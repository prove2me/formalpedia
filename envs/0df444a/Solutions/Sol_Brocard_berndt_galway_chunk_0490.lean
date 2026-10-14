-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:04:35.580223+00:00
-- url     : https://prove2.me/submissions/2913f5dd-6609-436a-ac10-fb485e68a425

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87949641 ≤ n < 88129497 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87950891 1250 87949641 87949691
    0xc010636020c0709050a18080306010e030109110105031b0d0204030b010e042d0204020708040503070b1314040e0a05010c030b01051c0216080a020708161d041509080409 74
    0x582251402c00213030714000c3c08004d000c403c4443d19600c05540500942685600c041e0251050584c1ca140000c000b409140d002401c45000707078940304050000c0340300131550044800c1d007440c03e2a620f480b248403000d0040c2c980c00b0140c2e810180040c0c44207032100720398020003c0ba4420f4002c02250382e661aa9402610340c110750181825095003c076203207a01d500140024142e002400401c040382c1d15802007000ca80006004540a20b000203040c401850100040380050145400052901307222b070f01c0c40c081c031844d07501c6000d24900c450003200f20155105d40010000242c043d040b45d050106509019028000038a40a40441e103802d03107400281d44280c04540c40414518080342c1c0a10340615258000d60180d00b00b03851030200d1231800740000354444000c6c1512070096000300400d50070109064100202c0740196030b50102508401c00c9100990a006041c1d6910106031903030660707513030a11a022900070324564418034640280c00081202e150064403d076003680c5030030840c1104124418020740c0300da0072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87952141 1250 87950891 87950893
    0x90708070314090d0c0303150b0403060b03060403140c010b09070201050703050c0910140702090405030403031409010f08040c03020402040609240e1c17030613140106050c010636020c 80
    0x54814112800740c05c0d2081d4951181c900000c1da030b8030741d81c04010403070880e4100c61000040000c0410600031280550f40300c2c038078102d000d01000c0c1060340d0b001e0105400b98456180d038840105c0d800a071500c00790f10200c0d20f03c50103412040b8610f440b080090082504580c00d0003c00e04d00000308240300c0412040e0b4007a0b030000703000512030140c5000c0c26a641440c004031801c8030b1004011000050b1281e000d0940107a10600040d43c5aa00b11b180150241760140b401c2c030082941400a2800c90380e000846071030000c840d0802072419107860030508089004c6400194100d400001c00103404d9a01c0040d51086480083e900c54184903e500c1c1800e0640e04a9042d9000680d011800101444e280e04c90b599801c0790f01c181310900155507528140c804d0389400c0c00810600c2c0c04010403982e81016070381801503035060f0310704014004c1c034502076581462041c01040700b00280450740d5030004009602150182000300d52000d19440a000c2428040305022801030143c2c022045178040c0d62003d0007a0798032a404c901c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87953391 1250 87952141 87952153
    0x6120e06010b0307050708160c0312020303130f062405010315030206041406130902030703060e040b07030c0e130903020f0303041203050c091306030209060307120b10030209070807031409 82
    0x1d40440d40c0d1b800c80383c0182e520000803c607445a10b0b41404208800310300c28182541400d05c8c41c10003100e000c03240482c0906540080003044240c00c58034100d5034859911224450041f09207040440081c10703507030001251007802600c071041c40d19200c8543c9045074000da07030620600c1c0c1c2e690941a10500c080c80001c2d0013403401d002c01e01130000f41d80d101e160400400760415080100c0b008402e040e0584650009065607400070a00030081ea15007e40b1019000b5100054103508080d07680d460842c0d0010014410141c0e654900790042d44525400980b803a0020805550307883c1241845004017038140e011401b52140c107040e544000d6021098074460b5410000540303404014010580103031000400407540844108030001550782c90354451301c1c0302100100000b5a590071481807045102c00680034038803c0d48041d0081125848001044030801d510011a00c01910341c580c003040e802000f500000d41c00041e4a0410005960202c1514490103441d075062051445101c446041124281c841c07000582000f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87954641 1250 87953391 87953401
    0x211801090519061112070e060705030714210315030604030804030f02071a03060f120703031d090705031603150b070309030819090f050603010e0406090c06120e06010b03 74
    0x280c0d4000c01030714054200030a130f0743d440400d2011a41e00a10019030380407841d0b07050041450380a80640c424002c02d6901524082e103d403a59956402066001040010310303082010503140700b40002c20b0100c8105449046103004069001103641040300c80e0002d140c540c0c02003c8082ca0b0015400340038a4050301d8031030325a1101d48080320f020b84132280b010190300c102e410000e811404c5810000d0320256508486480c3d01307100082204a203040381c003080c499407182da01c0300c2e41e40002240ea070301200d5140c1000ca500e041c0a5520b4040401d8010115a110102c01d003000140c0b40c00000540c440c00e03480000000800e41000154200d40000d42e44900140c02d00e60107105905801c0001d200260090815110309682c95803050801d03804011581d0300e80071558202518650040c6409003d092005400301c08181003402080440c0014440da41200c1426004034041c031006501c451301880d0085082c450064403810b01815140d2001070803e8014941001310101351404120241a2680842440d00d95151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87955891 1250 87954641 87954673
    0x204080312152101020909040c060e01230c01090501091b1e060e0112051501110f0c041d010c1d060a0e010e030f07030506090f0615152118010905 64
    0x500b0b0080f0750b5640c01c001d02c007003d9440c1c0060718402d503c20201000703400c0c2081802400e01018902d0a81440050741780021030510501101d8402c500c10b1001e00e48504c5134510007405440202c3d0054600c3d460821181c0174010720b02040020361411849102c2d0b2595103400c6480c1680b1070f8044d040d0314465605091003000c1c4a6440041e4010381450012015103041c0000e80854100390f80d800c0c00007d160243c0d640c1540c003c03145601c03000d203a074050803d003211180d0315030302c804070b02980510855032512035070300410b28019110129010b11008100003850b90343c1c0504a0480840074a80c10b0155640810705c40c0b030b011041700d402c01c0c8150b48000c135810f038000040d11800f001c801240e40c180110b07010048403800420401008501a60041030581081e5140a003485c01c582460301082d0080c6c4200b22809440e12501c3c03000030025580d50414a03d5003203802460b02a071050001d00c50164040d60810641e8a00c1440c0101a400c1810000380c2d188503140f0f0803585090f01c0200207030001d01c41785c0d1840d02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87957141 1250 87955891 87955939
    0xc01080702101509020c010b040c0302070804170a0c03081810020a020405151309060507030e0d18090c08180c0321070602070506040b010603050c1c060801020408031215 74
    0x14800075100346041d101d10341001646c02559644441e60340d00c031500e6030b051800303001d0928210002e00b000c6141210300d85a800e4070b0712560140502d54001c20200c00d0f0f09601c100606031241d90480e00a5000980342c1c685405c0130350040520141c049072042c005500703071030040000394501c040c40c0c0007090500119030034003000e0500280060002600c14405050541b598240700030f50034065400001d0083c92454410102c4101400e80c7c4105883d1042103041c22800046c0d904001c0c006003041c0c40b4400080c04da1408042e41604543e07000b0f41064200d10b0625004070a16003e180e40e240c00e0108844600140782c0d40716440001183d059002062215088480c0b0840c0c1400b10840c0000925104e802c0e240c101c140d034400142111303142d01501c03c21050040b124922400750959103810b01003400c00207404105c6004040d041c41c80c0903a01e03909900c41121030b90001001b44100340095465668400d0660703101c0d000003030789090201c02c0100007a480303c0310955064400074024080040d01d4000b542e2001c80c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87958391 1250 87957141 87957161
    0x10c05040e0f07090302190513050c0906071e1112010c0203030106030b011403010e042603010302010807020115030803012306040b0903100f02090a060201050402010804080309070b0705010e0c0108070210 89
    0x40a801804400350f22201d01414403400e01981f0404498a030034244080451400141180b80d484c08041c00381030f0900c05e048a008282c2240d10329280d02941c2030150110195960702c64180d520bc06500041052000d0f90050409044480000d184200c0501a00340c0d0003030021240140c108100501941c1d01a40c01501c21040c189171050103807074025820034580e4800c0e000414521400e008001c00c1004003164034545641030b10691800c200485030fa565140018007000341400803800020304424800d40c03190069162020b443e20545a507400d003c2640d40c000e0084c82c5680d5001c901e007010754251214020f26040c405056507250900d4012004010307000b40c0c0e4010703490700921000780146c0070a070042c500040700c2d07000016540d0420308108000303000a42d00860659041004010140c1e0b001903195910582210001795282d688118040c04c044082e0000c2000080209021050180551046050381c40050031030f02e003804010019116810b04561201c016807020051542002d800e4101281c60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87959641 1250 87958391 87958397
    0x60108090c12030702030a0515070212070f02010302071a15040b010207050906180709180605031011040b1b0d08041e05120c0c04060e15090405120a0f02010c05040e0f07 74
    0x10642545c0041e061801403c0240c400342c0c050890038490b09005504641c010055000030075003d0a0089030b004c0034041c001c8040d2100700c07600444030959000b80c0482c0c680d80e074403001c080d40350301c10f41c2290381203c4000d89401c3c40031038903a00821040d06052050480303104058000300242441d00d41002049a0000e1282d90064000200c078260059a14942802080951100408581041c4040c0c1c1c001300c03000380c43d86426041c0715040055453c00b0400424400315001c0104482a00f0071100307265200e00ea100d0030240500103031150750820340e0b003100d0396450344c410199003621140c08011a0390031410f03100680b0181c0c80180d0000c0e070714150252583c07200d100354284e410303d02d100b0280c000c1c0d1b6000305649c0301981e044100b00d448030f46454411280900200a04803216042c0700c4000c0d10300329000d039581e50107180d60001003001e2003410400858180d601130030340355890020131310040c80650040c070841d0141d82403100c5048150b000310300340c905a82c8404541840c950b94407207104904803015000000b8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87960891 1250 87959641 87959647
    0x40e19060305150703020304170310080706020309010306080309150a030e070609060f02011407030b0a03300503010803030705220602010203010f0509040f0b0603072309060108090c1203 81
    0x12051050156038010350290015203501c081034212841d4000c40184454100343c0304100b00000550040c030000c2906103070a0003030780c0700d030350711400c05020030200e4005180c1e91044c00ca00103400b5038000001c00301940700782e90901c0321603500d80c696960707070061700d00c4c8980c029550a00101072002d00d00142483ca0340a01d8046500010b0030082e50a089003074001d81d002804500c002c0c0501070f040032a00701c0c6600c03c1d1008100103001542d84200c2200c020b08000d040544911304846aa80c500031007601942c0c0100c5035182c0c880c5c0300180c1240455615820b84111480c22111031070040c040c1081d00d04950561024601d56902c041c1c048840d54841c1640d02500709060301407925075054006800081c08036600016a02d50412500c0f0090031044e0780142c0c400c1100c0c02c10000040e0704060303040300d00b6902455229454885600007414040c00e900024000c0e240e03510700340601e0340048142500301c00140c43e14034240d103442c40110f0381180200c544190562000444c07001c20b0901640e0310324401c030b0550541c2d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87962141 1250 87960891 87960931
    0x2010b031c32030411011803020f0a030b132303070b0406090618060605040603050705040203070504080a06091a01050d02090601050405030102130e060901081e120a0314010b040506040e 81
    0x304100d0b9440703145812060120404c0104809a5004a40803400342840d05102c1c92151504601541d10300009000c0d41c921b107829403030f58840954100c080c0d40e00002c261110f2510700d0507a03003500c021050544500e8460804c01500d1000c0c11511514606040d011f186005c03910344801c511003c0180040302d40760750302c40720503022462600c00c3c030035000d2001e40d18602070b26003410040c0070b03200c840e0401c2e031080340740800c1040060800540501155001c1d03901503200e41c0c030888283d0f403500075a48082414018104148200700065014030710071072146003459900c08041c3e00c1810022024001c3e1074000b50710f603485201514002144591018051400c2841c1c280c540020a0a80e007042441d5112000065418032940d220180303040d601003001e98a00c40950714010b003c3c1c0d510000110707003078200142103403180351940003400955600c10f05403641a0303135015080da005005044003005800c0800e16580040740c201d154804a40440d00300800d02814681802e802500c20391010b405d500340842020020030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87963391 1250 87962141 87962207
    0x10e070c1203050402011404080a1b09090f1a100303110f0304060903060518030306100903080a120b030c010f030b06220302150901090603050601020a05120a02010b031c 74
    0x5030501c4041c0d60104840c18644005450381d040000065407101c02840103008258001441803039590304010034a02845c809000d6031040b200781d0b040803a00b94104800d18061049480108001501c1858460358807060071a50401301c1f203007034030031400c5504101c03003c00c0482e1282c0440008110b00d9000e6400400c1051900c901e1507000d5030000c030101d0380000042007800020700c5419800b5000d080d00c0150900ca0303d0905e520b9100081506100360f8040407130a10542c41000c410001d103a11200380e030307625018202c014024032180c4200c58646828040800142e0401081e8240d90340745c181c40e460004030a0304400e9000e082541e02c595041013082c003582d0b8803044902c07070a03101e04045a0001a2150841c01803080010740208004186d42d000c120711529a40e00503400e2040b1401e91400103910344503240100c1c1490f00c04100a03280340f1540c0161000c2500da180200681c5880750000c100c424000c070b080c19140c12014804580d1300503800e001c0600380e030080200001441e0301a4000c060381e401481e0345 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87964641 1250 87963391 87963413
    0xf0e1513080c0415030b010303050705070308040603141e060402030a0b0402030a0c021501061b0303060806190506030d02031806130806011e15142109070501080f010e070c 75
    0x49441540107a05480083c2041c0c070036045800c001d100680d0b1180d0940e10b03005c2103403806110090401c60005001c030144007051201002850380300b10350969a541e2080014040c121070325216045001c4800410748075036003040c60102c2560b80b490784940d1a0744407800c21000b900700612400525171200c01074004c0e65503d01c0211f200b550310000002d0a811030a2000780341248681d881a401e030700190060040c00c0d00201d504910b14000f0303241e6003242e80c0c24a001c50241c0f019130701c011202d1051009022034240d40000c181d640c00040c0b002040566584010182d56058110790040982c00422410700d00f14200030720292031850151565290120505001c2e01006aaa1107020a50442e4005000f4284000588601010b15040ca1365209081810a2088540040f1000140050280000c210034019402d40d440ea286a07074560440310810302190200020889141c203c9009584c1d0208880d07001d00085402081c0e07500008101d40e0808035442029038015040c0014800d0310b09401000a403034000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87965891 1250 87964641 87964649
    0x3050403120e10050c09060f0702041509020d0c090b0d090515010b03070305060d11011b080d0b121203220813080f0705060d0b040209090c03160f0e1513 67
    0x3e000460028100ea011503801070021510038800f0440c103040f41d0364010903144c280b07601c8000380b40e4586051001400074803100340b4a4640b04100031000442c109250302901000c017010310f060111450700c04040702c05110a014148440c4400c0c081c442c5514001e62042e1243e910500803a40c040d4800070504083c1e82d0264003101d02c0c0e600000820024079850b000d82a003003101074494800c203444981d030700355541e10800c900a040010300701720410640003400c10600d296820080c22503483c0e03202920000500040c00c0d50074024541014940040400051240c1e03424014466050031500ca000d01c5440c21507900c000402501e00403030b0b0700001314410800514440011200a03400285090001810f024240400f00c40c00d0308204000c014503101e200c100d41350b03505079900002d0b070100041e00040090041094080d041040602046868241c820040d4028251400c60a1a0001a40c0c04843c1b1941c4031428000040c1c1c02010104a030038048070601030035400e650300f40d080c007144003004060100e403030384 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87967141 1250 87965891 87965893
    0x6091b0a05060c0a1505040b040b1e0c0d0c090f0e09030c01110406030e0d020d030506030708070f030b011e03030818030d05010608060618121e0c040b060304050c0103050403120e 78
    0x84c08508101c0d450141890400741030034240194901a1910009030a004002820b2000001d00041840000302c4542c20003456041c250b54507070901d400b110b88544c00640d40c01508514046640d00c44a01940303040e02103e0760055050035450030140c0501e0003410180180500344030074802404000d1081c01140120072104441e039440e1840c1450040c2a660600b11082d01d5030080764116050a85c04681c48411103920b04011405441c6c0b040820f1404105070302c041543d00490102040f0020342070300401c100da020b1119041c00f82d0702c2d450920115a0054001502400c1e5000100000b0340100c16480d80690031400d414014460794a0302d03030a540c4081510780c0740598a0005000d25038100c408983c001c0c0003540c64505158441040851405104127403d10070b1881d948410341e180c104100750303080704103440401c00a510b440102c65968000581c2d8040c4100d00700400c15800b4100581641d1103142c004d4014103c0700031032001076008040c061b01c10790800c490812100044030160184046d0110080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87968391 1250 87967141 87967153
    0x100504050a0618060c030c02040c0219030504090c02010c0207031101020a020405011707060503090304030b1005030d1d0d0b0a15090c0f020f06010518090f060a0c0e0306091b0a05060c 80
    0x2446490012180c1e801400900444802d40d2000c2503001f00c61010150341030701c0001d0050051031081c0d03d0503080701451030440900e50203040c02c056000010784101c0c1c00400c2c00740001002030307000384d017a07031050303c81000141e0201d0f0b002c101003010f4080011a072003041c01501c160910680208041e12001d070014002c036694040112500304040045030000c04061411905505000c156240c40344074620019044242d56404258120f1181c030741c403002480002c04480701051140c1002e864112120b0f408020199903910f411007605205010092140d84910034040542d110010100244650b40100c03950085114000c110500300e4031500420300065200e02d113016200280080c58040091042c201c2d40d0000b2004014a44807c0d0810040340f0003418000c5140c0e8401059901d003549500d99001144580c5040c000741c40416888404042c0c00b5907500c08840c4075004c24075603a13050540b0030725002d038040e08481c031402c03400302c80302103860350f0041c490303001e4543c1c1c0c0d0006600c540110081880580200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87969641 1250 87968391 87968417
    0x303010f080607020d09090e010e0d02160e010605030a021c06080c030c010c05030d053310020f10050604021b100b12030406051605060709030203060709080705100504050a06 76
    0x8001030781e07000c101d41c03001741902904840700402d04102441801d202c03544500241e501604290030030f01c0e850b070003001100c401c590500002540c035403c2054040392141c0c521000b0507902c01289526040c0c6406442c0c29286071108211ba1009501018895100260140c038051203007820b40605001445584024081001c1c0c5208241c20074024a00c3c6070f040c401046801b4000403008419210a402c01c4030000034030b69180100b2054070030815040d040f42440f942c100c4cbc0c8054503030b425822080b003400d42d10100d0300101c940003682d5581d0400d0700005503030321441c40d01180c20342540102ea8130490141c40503081c011225003442c90a0070009100107070790131010520410b844607206001e10818122212400040000364071600d070b109501075402088000100401d14403a4280d80c2da100c0341d4450221503107480c1000340103000300401d0104030b119000d0312010914840c400c00280040e1030105000d01151844e24003001740c044610306200c4180b0800303000c00900f40d030b2694481c0c0014003054540706071900391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87970891 1250 87969641 87969643
    0xf0c0609060207030332130e0106030203060f120712030806040e030702090109091109040f030201050a02033c07020d1b031b02040f0203010909020108010f03021c03110303010f08 78
    0xc40d0440011903003ca401000400d070700a4843c40d200389a001c04054512108401020581c0d503031326132440d142c10014020301c81e00401e4550100f100c0503180f090280d07988030702c4100e003a48000c2d9071142d800090b5004c414440d10b4854845421040194120740c10150740d01002000c0190a40042d004100302c5000c001c02401d01d0301910502ca00000003851520071254009040e19074180682c8005070355584102040050300001d0003078284005003000c0c80c5140600c0e1041071205407032030440c015420b141c00300309580040c0c000d4034000d900071744c04200d913007411980760703201d02005804048051844041442040d1081f10203540201440d81c00f4100080c0000030103000300c903000b02c02207141200c051f50f800200394010700a00c031181e41c0050400041c842800000c014040301d400b03849080e4070000c000120304815034044170065200f82c030342844503aa00c61265200c14498400079401010589042c580340044002c1542554440c2c108819580005944a86180c101b60800c1c4009405030f007049c042c10130 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87972141 1250 87970891 87970907
    0x1090506160807050d0213091b2c0f0405070f0f0804030801060c150507020102031f05030a020907121a0a3510090b0a1b0804020108060d0f0c06 63
    0x281c51a50740c0306440c01c80014400540103080c101000004605050700c100b4540455004180301d5000005072034440302e40d60000d2072034a07481942083d080407803e82d614080c0301c1c0d82e22020045180321006020040b000e0380021034400d40c0d01d07030200710f10762108155503451040c1e901442e0143e82e03082c207142c2c120401800d44042c4940441c14031050100b0480000c1c0d01490581c150391345468025580c000c81e140c119030300c07083c0800c00c801c900d05107803c0010899055010390703c503c0103149500c203591000c0540c0505080d0306d015954040d00b05614103009814004903440d0003400b1454400b071090007040c000c01c02c0ba004640e14018561078648001e0851902c006040081c007458921289408200305503500109445001c03502c6910b00300303201344640c090602408406050501003404940900e24091030001d00440c0d8030b06100c3e01c0c0c540f1440e00782030b0b000005441c9270802e403a2060310340c030b868005494807903004042640c08800fa0442000042d07025209803044c0d4426201c0021040c24000c0c0900510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87973391 1250 87972141 87972151
    0x4051314010803181504080a03020607020d0509010921050609010f050a020405090403230a0e1c0302061b0403020a06030209010806010e0d03030905210a09050a0e0c0c0106030b0901090506 82
    0x15005010f080181da0462454001140c3c04a07501c1c91085d00c2000011244d000743d0340240203038001e184c2001c1c01e05402090f120f2141102c0c3c0d0035650b48005804041c2ca0350700130100500c0c00100f02c04070500902034044006030240406030300c454800740742c41d42c903a4034068084507000590794690b08184440c0c0f5441c02141c0c3c0068898000350f0901d402c003404100d1a2400401c064200420b010702c2c0c0f15202008a102e020201d6142d1007680e94a007481030140048091040041c012210303041243c040b0082400e14101c01ca0b032550191180d9203454040c0e590014070007540107165501000004010b80d2004110002440c403500c0260f160a02c40002500410004003014113000035070481030503075940c130303418000303019894180040c0401e05402c10a140400307070a194420440302414040280b0701e0b100240401000e6075642c141211380f03032401d000c0011007502c81c0e0300c0b4900f0700034041102c000003800a408951110000000c605549441d8001a040c05903490000c2d40d64502e41e00043c00070a000300d80c2d00c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87974641 1250 87973391 87973393
    0x5030702210c070803041e1d04020f0603010f0311030a0b07050f0408030d06180506010e0d0302010f050f2409041e0c0b1b1f150e040c0918020f15040513140108 70
    0x4518100841100201e0341100c2450700012358005421503a41d80c80540300c03810098005a103d60311141002203c002c1030205444103c6c03044d01e128218a0001000d00e0b40980c007170321088a80d19003480645503a00644084131820005000105440c9420005030032020100d80000c92020b00d0610310080d100202c20301c5000b0641401d00304190f0b40d8121001d000d280500ba64407820504107070030128014203000003651003440c1000248008001a802418020170146040701843d1400500c1d016052003109412038000013406c0004000c01c9000040d908484a00c510700e060300c3d032144e81c07001c11013001c03600940c0c0c02c85404a21030a0220328a00c00ca46440710b001c00500e02803907207980104000c00c1c9091804041d1361224802c1029900900f0210000c2c049050380c0e08440c2010300d00840c6d811564020307110000d00c0d00c82d4021a5002022090f1811134000e0620a119550380e4140403e481e84e0b245070010004c010003002455071520144021a9003400720002400c051085101203240010790042a032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87975891 1250 87974641 87974699
    0x1201090507111b0a03050303040c0512061003020f060408030a020a051204060912020301020f0a081e150111010b03030a0e091501050f13030b040803040201030c05030702210c07080304 80
    0x60040040c403c0e080d09803201038025030035030400c0082c4d500a01500014254000030081c402040381c040030740415103e00300d5803107040302c00d002c1219075180c01c11225003041c0c10502c40d0400242c1020079044250f444050031651400c0c0d2600c54661a42d4000c40f40703003005901042d44001171020910510310550715040029107003c0c0342c0040180180014001c190300b134a49000d0380002c40d42d003581181c4a5100308507000ba201c01071480007601c40d000445044012450720709409585c8030403002110701c00c6020140d8000c07810042001104c10300d001c0c0d0440c02d01990396801030b035501c1e0760400c081e05031000b4075502e68040305242428040c004001504038680715183d403440244982e04141600d02504c0c1c003036516030b26192004111150b800269002912020443c0705000500184000071845117000382c806001d1190f9004040300d1a00c001c444d608010303008403660f1203c00305c01c011031034849006009524240342111031510700340042d603809900c59500014040000c0314441d1601404040d90000281d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87977141 1250 87975891 87975917
    0x20607020c0103110f09040207050a0f110a060f0f030f0e07030611030708010303050708070c0905090c0f100507050708120a08010806190e0a060603081803030f040e0405030f1201090507 81
    0x1130034043e140d548112807101040317880154907158140d801654001c402c50f80f2460b21402d188184c860326210603640b05050310f0011203c3c0c20142003d804442e4540d583c0c0042c1c1040c1d0300c044030700e0340c041c00c484800c054403510030741a00c0030a8040d4841050b24680940541841c600e00203044031580c4d01c403144103290034020400d12540000a150440c3c1e01030806039036035071481c41d0030b000500c41e0b2040240f1004021901080d0258181d100324495001c400c211640d0001320410407407240c0d40f664200b0f900c81417072000d6482d918850000791170341d503100304207c03103901d174542c034202c2e081c4400f22030500800e0b02d0100380390740015030001c245401081c5e1080682041e040c04404000c0c0c9400110058443c56100c150251054000708100148103400603020003a540d2245000c14069000e80e040784880f45402484014a15020ac00c590040030042c900d5131502e458400070b81c00143d0300901c06e40b00d900041c4040100c4022440c02445100c000089400d4198180340c0d80e68122007010b00500100050046805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87978391 1250 87977141 87977171
    0xa03091703060103151a0a02120408030405120a0f030302090411120402010306050904030210110910020f0105010609051c0302031c0c140405030607080a0f0e0a020a05040203190b030a0b010303020607020c0103 91
    0x9580ba5000821b21307914045203000f40d103400d508000d03802c10700400140008081c9000300c007a02c00d0315002c44100c841c0b4078030401e486690f02c05024003e000041d030320719640c1c0007900030b900034404190301802c0807450b0100700100030a5034102005850444840404000031982c0c0b43c07288030050070080360149400d007000d880083d0b840c03d070118098a01580c82c10802e000295110950390745400041c02d15021840c0c01c84025200c4481071204800303982030070004240c290140010805881000d868800310600600302025115480002030b010b6020401c80c669800782140129045440780329008604c0d00403035039004048a00d0815260090241840140000e550202e885c0d81c20101d10300c0c1015568503070f0b003690001011504d690360313400b928143d203170320b041071020641c1001e05000b1a4081c81e43da6640e03041c40240c0c48100c805859004500d05041540826a48104003840c40503040720a456400e94600c003000300288c0013035015070710010401024030b6041001c1d1079002070a103070901885103255805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87979641 1250 87978391 87978419
    0x70203030c0c010204120302030c060106051623060c03010f0e0f0403111f0906060b03010803071704090204030b09011802011d010e031002030709080f060103080a0309170306010315 79
    0x103030800c0070300040c640c550003100f5010340f4045d01c00310754a440780c60001d1501035541c1e40003041101d0316018a400000d150381c0a5425249440c2240e180c0c2200440242d950a01c8080b1103203400fa6400d11030080c0704000041048258404c64036200c080303a8a506080201010380f456601503110702410004001c11580b601120b20f0700543d240c14800c9002901e00e4016092000b03034080c000075110103c0358004451a03a070030050034540210300420489032501021142403009000d003906542c02042004001858080304a03640490744461504080e101e030718007010399100b58400e44410724548280941080300f032058400c0450b0064595109420302da001902e81d180000c142d0029103c001c10841480e400340300c90301041c410003001e4551502c09101d681009400c2904e01c00c0c00034680c841d021590b5000010600703030755241a402880260728660710b505069202c40403100405840310817000019044001013020b010400b0031182e01da140c0840010300b207032000e41f600014a01494420484a6058110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87980891 1250 87979641 87979651
    0x705060423030f240402090106080702070e0c040e0603010207020f3706020105060306010305061605190804050c0d0b060603060312130305070b19080907080118170307020303 76
    0x110310540e90748901040d44500401c103107030540070300e40003104000c0300800c64160b0344424014030240055000d035118151103003110003e41001c81c0800510810f409240b446501100d948125021030380c55a14000b034a010956091050700408241801005030041e912a40000c1c21303002141000c21540010b0107030324a51590501418401c0c80d14000150b501c6000d480c800b00f10030000444590500724001c0003421440703900019460300340440d94500c1c0c04140799040325085401080c403615241031203000716280324a820180001005440100c40c03046804a58108842c0c0b100c0340079103014102307a03042c1494541c8251080b1100d001050006058452450704000b0546106031030b82d80d420042031802c405460100d481d00000704605c0c081003070a48803003046d02d00c40c0b401d451809644030103204940c006d42c00e041c03c1c200d80c0175100d41e403054410408145d108201c141280c02d607940d2100340508590719098a0704110b41100039240600c6489200a5003900300113094030301d180703040c8d003009480e13002c0545 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87982141 1250 87980891 87980909
    0x50a0b01230d032307050106080102211509010b0705010c0e03030d02160b130c081203010501030c1707020d030e070302010e0d030306050303130509070207030c0501050f0417160807050604 82
    0x10710641818803c034504065103001c0e84001203490220041400b007600720b64002c1301c256080c118041388025045c000e071041800c204c0048440410330408031600c5082c0100b442d0400040403042c00540c0d030f600c501140c0200340d40c0d2921961440c140c00d155003502c0c2107002c0d280c00e0041107000140980c400100b280c0c3c00e44984000161038600e410101440e0500c44507010b40035021110500c601040d40c0114601303400d1090b0801d90f99595a0340c192911110b01c1c60703150ba0004d505000403c00355020341c10414045155103010401090340d9440215521b03001d0390b074000164000149000080d401d4070548685580400060401b1441c1d94002010403402d00c0307400e03015601c15031802d01054004e0300024080c12004003541c0d00d03030321102a004007508140c0300b05407042c460034022a4681340040341d400140c0303822000301d2507401c3c2403000565055001e00403540d000e107020040000c2c18012551112414400c280203000302c0b2485480745500340c02a9001000f040d004418200216a1044202c404465280e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87983391 1250 87982141 87982159
    0x90a0512070312110c2a060304050a02040e01060609050109081e0a060207050a110103150302090601020a0c140901050603090c040903030902030307060b0405010801090305030c090a12050a0b0123 85
    0x220b82201c1209400c02400d12140c201a84144c104030070a001d0404e80303c070359080b90f040c040c141d16584207100202d202003000d8040344c40489890b0600000450344a8005e0040b01c04804043d030100b011039404032140e0f0740036555420b040c0026980000014001c040074030f010160141020503039500c42c850004912000c1024884540f003802080c045190180c0e040881152100501d081403500c1d11400c0001300c03046060801c00300c040d98028842d185401103030444450b10241554240441d00b10040e00c000d0561107407130800e00001d1807a0b80101c01a00c442c0c1070040850001806000703000d001a00500d224030780034400c20995103400250569001404c503030115401d20b0038107042c1c0060201040c040e405000002d03207030050200c0780d0007140e01c060041c0c03030070000750f81d0b06d4540c0c41c08c0f070b108045c0003000920b00f040820000840c10001c3c0800207001032083d6211650340941d500d20300000c4504444540140c0b01007001c1c80071542900b401001031201d8500c0e03608080704d12429541c00c414013079200e03401c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87984641 1250 87983391 87983393
    0xd0207170703030204031a0c1603090b0408010e0d17040b0606040e0f0601020c0402041d0a0b090103030c0b0702070f15110106060c060e0c060307051b0a120206090a051207 75
    0x10308046544021506689a5400e140e050080296000b400161078101c2d10030200e407a0704043c00401c41c400d5104140c15818904000074005000d400610301303604101a15101094542c00500104020042400000354003503602c1003030b0341060200c04c541401c1c0306008030794070002c8981450080c4d00950003000040241d035044001040b40c002c540103014240c172800d00b04944003441544890085100743c0803200320b80141070400090b44551301880c1208200302c604044015a0840c50315000401c40101040050000002c0748142500741e00035400110074030360b860240440e54a50036000520351008d41001c9003400555568580d180c8214031005441c9a1170f210001d12400c1c0000704140c200c4003e12282d42d880100402280c092441540e00500d0039549042105001407005a1640c0180029040d40e44903201500e46800c003008100003480c4000d062481c0d90424032030070042e90321480343d000c844550060002e103070040003003009180b64000003003080481d10006510942903402140690341d9041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87985891 1250 87984641 87984653
    0xa090b0f121f18110708030703050f010302060f0d0204080a0807020a06030908030f0408070609050c01020705041a040e0f0f06010f0b090a030809040f061514030f01090908160605150d080d0207 84
    0x601d1314404155400130070450204a0f580c0000e41c0121044d40e800e0245450340403901c4a0b01c10b0a00c0020751001d802c1194800d60b4012a001c0c080042041c1d00c0107080598684000f8180030760113008540c818400100711003145044542600541118030341000307180d405503036900f07082c131014041602c1d50803443d000500b00240750302210078055001d442030103c0344891074259034444128103a14054044e81501046a061610600c2003a440989100f91007045c5401880000c0401c00c040c0529805001d20020003034004002a82e51400b0100041840f90f00d000c50300700500c0b071a40c00c002010141001120407503030718910010143c0e81c00c803040c69962040742c0009002490b560100e03103e9075050035800201010020211b12032880c2c0340e2500c1d007580840c0e0003400031034807084034000f00c2506014014008590158089054140704144091a11181143c0b0b50010600f6580443c0d100d5120000c10808585014002450000030355000105c500c003071340d40d01ca6501074100510519a4080758110500c0a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87987141 1250 87985891 87985901
    0x108060409080d0c080705070809040e0f0708030306030c040603020105030a0b06090a030305030115020109020306011404020706020f0c070632130303050d1a0f060a090b0f121f18 78
    0x2601201040c1e80f0008003224501905a030544840840d0300c0200185038180141d0490710050f520241161400c2805020440246480b6800c0200d1384501c0c0030780300b40c60101b0040080a0701140e4001c0da00c1c0d2400d801014035009052002e85e00450500f90200700607600f040036260000050070b030120307044107201c001c83d896000c3c5030070a513407041d02401c0000905410800440c140d81c0220302903120010741b844181d00345d82c0b919070000e40640c0180300402101c03451503a0300b24420307401071016141040541b2080140d07000442d042d001290000351ba0361152104100c2e43c8000c0c00107050035824481d1035840d42814904110321551002d21090b5034000305503080048070204040da0b046202e00da620b034140103160350048401240c005141c08612150004485101200610010300c0c45d01c50035002c10511030700b504404c0303024080c40310703503200070905c04849009000386600c5240d045485081040884018500182061030241d0f40c4a6020441c84034400c2d010069400914003000017400d84640314000382 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87988391 1250 87987141 87987143
    0xe010905010f0902030c0d0f02010503040503090d030f0f0801080d14090d030306030c0b07020f150721030f1107030f0203040b0304030815091501030b010201180501050103031806050403020108060409 87
    0x751900d400780900740142da010f000020300a038100c444150140040c09490302d03a003030020f0036a2040005901c010742c03250006552152051081d281000840800706008518040c000c801243c50b0300d01454403a42e001407580302d0000d070b518150b038080d450820b205803104054052001002082c0c00440780102c800c0007110a04d40c00030300684840103540c01d00800819040c0000c0743e5810cc07818000851483c40390948010035002003090988500b0360b0200041c011445240201c810418030540010586444085190100e030b83c0d00300018100c0100c000b002c0b20403800042d07544d18641b000601c14006103c0589000b6541030070b00c80c1c101403e646040e07186014650001c0c040c0d500000400040550000500c1d000308820107400b40c40071700e60720402800c00c00440c0c2c80440019180078000282d1311a8001500101040c00001800d1000c0c0f55a0f4a40d94543e03442600e02e85e4407a0300410415502a811020700c40d00b46000080d15400c01100a1052003140700203410443d42e6804100d0319075440c0e024089803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87989641 1250 87988391 87988393
    0x80601052b0215090a080c0a0b040e070806040905060a053315120705040501090501030c02061f0f1e0501020604020303120403050d050915060102010203010f120c03080a0215070207030c0303030e010905 88
    0x2c241e843d1000e503541c04c01d5901450207075023204000501006c0d1401660250b45c1c0700310b801080d0342d8562400702d40d5550001c100750307130094035410741d81d02094043c007100d40540c030000d102062a10b0b20074010390804415514142d4130010710790406410954601c110800c08008807440301450041c0c0f815905213001d103003000140c0300150380502030b5103504174006108980e03080c0c941c404031a980b000154210b400100240d07003d60040e00004403400d0b0415040710321a00e11f20361041a8a4aa00d500d0309801e0090700403800354010309140314a141c1900314440b0040c042403005041e5480d10358046602c034003800100d0b160803143c0b44049000c141c020000c0d900352100d0720300d0070400e62511400c01581c9900c10410300704d61102c040701256940d44103000300c03070513180400207903500c091030702c004101d6050841c40103880000903881c1c04400075021500408500c0d00d150f00500d000642c1c071009192940014240005640c0440002c0000580501404049a0301400c0004602c030a01c0c10180c050220100001c0c11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87990891 1250 87989641 87989659
    0x4020c161802040e010e090f03040605040f05030604050a02010f0504030b0708010315050106082a03010609031e050a03121b030615030e0c06070c0e01080601052b021509 74
    0x3100003403010040071195408000d00d504800301203000100e00c81c80c0145241e1006450040c8024100e2180c0380360040c2d40a4121018441a001e5450440e00140c001000194001a04101c416011390250000d404200c0141000d8180355990940d10703205400e00070705010b94a031005109501820030b880096401c0523403a80e00380f41222000f40300050900048440401c1c014000645190070700c100380c141c039540d031603400258450218816285d0851004001030760300048080b0701046c45640594001c0205480e0084824114900408407111a94680c22135541091808010850009212160b5900341c1450701000c1d21700419000a08413000c21000c03000e016491014400351f05a12140c111600441c00c1d40c05002c10107000c406444405014802c00d40c440c04980b40705142c0000100201407150b542000002d59441901211107800da0016000d508840010000b90610b90314006400d4620707a04480c10180c0d511003100300c11880700700a40548240010f0340244440d410031603007055001000000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87992141 1250 87990891 87990913
    0x50109060612050907140604090f0203150306160302130503030307020f06090f0303040605070306050a0303030c02060c032a0d110c010c11070e09010626120412030e04020c 75
    0x2000c0c100a100712000503030011a800c0000c10076108541c090940035002c1d001c207514000c00c8207603a6130241c1c0e00ca075000c0e90400c00000c00703540510503803c02c2014400f02688900e0400d0411800785001c66403030b03010303030003040400043c101c410050380c030b420300c85003801078541603a01c0068103017484941017039030544400014404d0f46074000403980301c3c1401c280c00f111100c0c0d41d20250a519260402440d51307899000f400441d0000d02070360040d9511000c140390004001c0d42d12000160020389c550720a03000319070b80e0f07510007513125070500c44640c0c440c0498440b00e165040105a00d0411841e4424100c100c2003000c100c204000ea099003220118280548107000d5103074145241140c640c44454011450340c030740506e04d11540e000d0007641030403140400251444c1c62600748107020a038030090001c0b00555899502256084050f464503900310740303130714101f100b05083c080d000b803030710350040041c40c2807100c203210401030040144603041485a1500c1c0c0000312608090205e8007034080c0c2020805d0034011001d4040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87993391 1250 87992141 87992159
    0x60f08010b09010f1a07260a08070206070c020d0c030209181b011e172401030504121407020904080324030c01030b06070c0b04050f0a0803030a0902010507060501 71
    0x541c00c4808403844092642d079001c1c0c2c050460b910740300300e620021402903101194005c07140540b030214099403040343c0a15000a580c01202e1703554001030302031304011030140009540501c20640c800c801c2c3c0018056400c204102401181082e80300911500000020204102c3d40c800d012004550103000b4887c107040c42400140351034944000c5021510a5901c01c0100e05c0d00c48820034100c400603151000f003208030340012026040104042000d101501243c0c3c525070b405010b034688901c220b20290312541c45c03031020745043d0380e0b6120f030340504050a240c1070201060440014101000741d9050a000151609190a940b4014a1400380d480350300101003106000c0090000c6101d090340c184180c0302600080e044076401944400704640540c401e600c1c2403000d500988c0840520316004080905143d004c0d0345820700c581d60385d0051f0340c0ca20000308080001e81405034401c0b01c040f01c00c884d11005203060080f030b503540e40401040c0c01e00c0c05441e20038980c2964000d0046905140d0490018060b80da1070329020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87994641 1250 87993391 87993401
    0x2190201021b030301030b01050603060d0f0308040605130c0e10050406080c01110601060c1704242006040b0c0418020a0f21050a0e1014060301062601060f0801 70
    0x118002007102c1030001d0780c0401200f228103032503000c48020416405d0005200468000410f4523410802d0703c1c6044001c2107408120350b100700e2183c0e850008c1031405250060542d00047c1056811154100411000030310f40140c1c5030581e4001100d004280c1d41e1030050045092503a030000750040d103040008142c821000c50a8416040b0070f80700c8901611043d9110b039690402441501c0004209503019000100d880403c0c00c00b0100c842402030809840300c802e102d4074190300c40100c1c5512148801c2540c650b8100065004090588246c01b280c0301400705480e880e0040100300502d985041800284019614010703140034050b0601054280d042c0050314200a600c5968254042059509200744a9110352000000342103d026203088404182008030064140a440c04403183e44401410310380200801030141018902c02000c01c42c0550494100d12031302c009884603001380d040000c10b0000c552007103940b120141424100b00c500501c10b203007003030041c07115400c6195012a4070b20001001c1405400c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87995891 1250 87994641 87994657
    0x1503070203031504391404140409020a121a0606070b09010e0307030f0809031c0506040617100f020306061611030307031205180d0c06090b070f080f15060d0219020102 73
    0x102c2d45c000900d142c426910705000311400c640b03800c01003000b8800742c44240d100d1500444007810229005030141e0004240740010742103c80480100c20000c0284803a0008480c542c1360721012100700d60525002051040c811500050400301c1144042101c1c14000d62001800d512900b081d0fa44414241c40e0042165030840c0d00200024004004918451b4010080320410811060901c070880d0320503c004000e800002d05c02a840303a646c000014402d10302c41102c0204200b1600640204c1d000e00440400b2110620a01101c840c418800c2002c684c4484084448040c201000d0326000700b03861803c19a118406e4040581600000c1a91300402d030300247d440300326040852040c05a40d41d40c1c0d01085040701c451591a034950710400103060310314010000c0b05007144c090000811a4407480e105da0700e181d03500703580b1200002d200c8038503610480d41c45070355640c012007101e00702c018600b00000c000000c003141d070030a0340c466180041c2c070127a0b080240e81280d04081600070300d00340e0800e501c0800f900039005254 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87997141 1250 87995891 87995981
    0x40b0a0f2d050102060106080405010209040c020304051c020904140a200406060509030703082d0c0d050708070809040f0f1b03090812270703021503070203031504 71
    0x60126542540d1646400c0c2c0d60103a0081107181e1800e0b2003100c5442d805030041e140c55508005c0a00d2a803076902031135208650310b400440c0c1e1a45491300b4889102a80f08d007051403404034070100c400594850b011280c001c0d410141200082c00362410050401d81417400c02001003c0ca030480481c01c041010314042c2c03006d0202c0301007144030365416059413280300702580c0980c960001d0500f400015006c82c041c04502c03140d003c040640703d01001d085000c40404c81000c03503a0f00d40100d0ba50410342010032041851190a2030503505000c0d0380d40e80c0c021180aa468000c1111102241c14400354a82d5440000d00d0885030310300b402340c6082440071500411090720b0303810504c042103005001003030082c051081c2c0264410400385c0b030041c513154640c0060303070301604044911180e01e11541128035100c0c001900c014000d00540503151840c0304020b800203090b0b00b021422070060040051940d004010307607901c91807030791045075058a00c50000d002844c0303204030b5014400e401c20f114641d103210410540da4030703140c40c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87998391 1250 87997141 87997199
    0xb040e06090601030912230a0201050405071403070603020c032503031a060706090c0305031210080111040509040f1704050312120711011512021e060405040b0a0f 71
    0xb00046040d00ea01c81409416002c6d40744625407150b105201e10b1500682d44448007911082c82e1604085c694010031075440140e4442c002d001c140442484880b000749940810701c040c409500001c00d07103501251080805159012030280e003201c0042c0700700d4010b0711142809003145040c48803034800350381100c4010790000c2e240400d4a210040520280c1e88400f100403c1ca606004540e41c0700005030000c4207040366400c00c6007000000048040001d490940c40ca81c0c8a0380140c906070140884020b100d030b00c5084168108200003000e00c50310811202070380c0d015180d00200341d4079400c1c00e159804410f10000c1807020841030a150220300d4002400035644202d066800c0c00b1f500e0300ba0750301d140c000c2035a400641c18035940480c0500340588011004034401200100c0c070001240c07a01c4a6000c540c0d840301c4000d0040c40c500ca800c525089000d241c043c10382000d0402031903281c50106102d8010341c0a42409503035520301e0311130281e66104408000b0b203500304491090603110107840803100c0588083c460080c01c80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87999641 1250 87998391 87998401
    0x14070c030f0c030e0402070203100e030712090302060a1103070203100204061202030c1218010c0306030c0e1603020a020703081903060e090307080906090d1b14090a090501060b040e0609 81
    0x503900c1410b00c03680507512035284c0840c4408000003903010344c2c000c070391501c50a581c442100d1054080c2000c0c500d142400345844641a081c8040c0200e0814060410401321100900041e40d403a402c1d41d03051442881c00754030300c0902a268901c0e5100f00346004c0d40c94450030040c06016100c0d60010419a09580d850004140015420805234081a81c0500803000e0a104000240d900d50b8003050340701d1500c0d1305100440342c001294034211049000ca8100180d01e036102807080c00350280301807004003070115000800345051440c030800e070000d25410004041d0001841d0200034401c00105005d9600007100940d207408410020b508413070308801c040301080c2407182c0059105401d0004900c82d0221001841c0f4051066488a4899111401d010b5012406000e03104150700d5280c3c0c5101c1451289922000c6019009108113120925a0000f4001c91080329035441507102d4803000d40d08900e2000020405415514003113000d8499a00050003650000c18001551000c0c0d0070700383d00421068403080f0658442c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88000891 1250 87999641 87999647
    0x1d0a030b091c1b3207031e08030417090307080f0d0302040f03060209010c14030a0201050901051605031312120b010305040c05060d090606170705100215090114070c030f 74
    0x10100c030100e405192040c00740490b60000000c941d00a4621307464403148070844580102e1207141e400c1845503400a0418402c010310245400e0703400c20401c11201d881d80712640c0e01000c51000400080445602141c3c09072110400b03000c0d190240402000d442e600394a0b1000c0710394420100c42030803d14841e8010540c3c81d03500071300c00c03502910b9186210184181c10341c1c48050181d840000020704000d000c140901c04103211140a105502068001e50354404100000900799100a0414412640b6140c188449110042038100c0382c0015402c0c80d548968420040307990304181e554016107444820a8801041c0d0381c465000c1c6000b0342403032000c009545101004404850003102d006261003820311007449103242a10203090f0b032825401022803a1038070340d070320032095a2103580300c16207001c101d05106001400c02d200c0e0700050f01096035800b0007007002d09002542c0b0080142400581c00601c00481c0c0780200a40008051443c808401c00181c14203200040c4600135440d0103030b000480b150502003120b84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88002141 1250 88000891 88000907
    0x50106140306010b0c0709090c03030e0108060604091e020c15010b0c060a11070c0803040501110a0b0a0929070f021c0e01050c0601090501080606010903031d0a030b091c 74
    0xc03016004003450381c03c3c00000e4410350301c24100000365120b030020008901e00180600700e4441e104e144207411240c950300d4090252820131900a0500c4410402c000da0764507290192812121100340100310042507451034a003501d41080d21400d030301c1c00090900410300380054100840881841244526179865141001e64015592001c446400280200d091154690007101c069146801c41c14507090655036410148400f0f503100301c9040d00301003810003c03581c100341d081e09180c2e03140c00544288078095032102d600303410003422080460390300d130b084c0800d01103c040141540781c100c1003c141c078102a0800003080c1e120444e03040c000545180030b1091480c0c8003150078000d00306000303050120100700f07110654840d07054045960411100f400b6800030540f0401840d4001d01c0d244400050301d5042034000c03818804001d01c058103202c40e100042000070b41c03041c5030b40c1c000165000d500c40c1100d01354000a9941c1d00b1a4000313000301c81700005000c032001001c10481c410039042852891080c010b82401c1e01c0384c0c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88003391 1250 88002141 88002179
    0x60204081218092e0f080c0108040818060705060604111204030c060e0304060c050c010801080304090506150a030209090106091203081b030c07060608031224060307020a050106 77
    0x2410102c2458018101110304640009800d04010414204181c501074000c1485807000e402c12004407040000d58600c041001c0504030880c0034040000d056000a066494003130002000e46800088410f500d200c0e5410040130004c0080240d982d44e60315040c450341d039460541d4214401c2d858480140f041c04070043c11108090b04121640010f50740703946040e141c18001c20002c2d11130680300c0d0045800c00e48180002d001a0040391508001c5024501348580703020490141c0505104904005101075640003060b0f60441d456024081116a10100400c044d0914040c200145071008540000f415416030054104120b041d41d0100300daa0303036820f00700c80e00364240c0b0441045000c64103910021070302c1307401c5080c1d00401200404c0343c0c40d01c2c0d120319800305034022a504042c104000c6400000c214050040c24010b00410009506201c10081c0d0450500d034040c100144001c0b80260b98001c110f0002401200b4501c020305050302d03031510140c081c2d01c0350031040040301c16500e001000305942054080c140350300717 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88004641 1250 88003391 88003417
    0x60e09010e0711120301080706020c060708090907020f10140901050402010f050c150702030405030d05040b0a0c03030b03010603060b03100203090a0b060d0f03170a09030c02100c0f0602040812 84
    0x1c0d031107240301540c0500d05028590580c0c0a08100404001d02d200c00a600070003d400040c05542c0c90700310300900304500381080034800c11041040b4408a5001d40030b0760044e0f082212a013020340c4443c80140e18103103d8026041243c0180859440e56194603400348a10f03070313149280b0400542e11400698200c030707003c9800031702040c03107a08440e40040c0315a0280924444900880d0f42280c1000300d80e5030361070821540d950040e84000790030711250505100004407a059030a01034140790030158013405030301940e045d810400078003407200b501f494400d070071692640101800800200741c40c0d050405c00340403184602c6010744521203171414010954402caa2142a0241c05088410465500e00102c1c2401602e00f0b039200540070542d00108402c0c12011039814071030b4a415000418243c1460080180200b54084061505411402198001c51102ca165138100d4618030400c4405100307581d034405001001d0300040503403103c0010007040b54014001d540c0684103c4070002c0c2101603010a52140380801c0900c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88005891 1250 88004641 88004669
    0x30601030615081c14071e06020409020d0509010c1d040203060303190e090105090112020112020c1015050603010b041202060702060a020a0c062f0a060e07060e0901 72
    0x41101544980002c8440da62080802660748032003918141144626080c01c1c0d070b0120030b90ba061900301202c8200308640103056810003625403185524401054031401d015031100c0e048508101499040324068501c5141c01c64940101405603c024801180e1281c115841e10303c8225499010700392480d500c2070388807a0f528810000605200207900050f1002f5014841848160f002c804681d441031000c24442d518000507095900c208210518180d05c1507001c1c1000800600a0600101e100d4250a030203090018100a03078020303200091098070645040790080c0030302c403a0444066040700703035212350200c0c0404107140c6131400c00541d48001e1188940c0d80000700700412070720140c0807428100c0d1340005c0c1528140070064011820a070300a0030a034006030012072a540c10000c040521030041e00d0f00346080444288088804101491400e1101c0c0b201035110309100c40f920801c00600003110350150040c00040000c1841c540c1d0b5105034065800819200c031202d120500b0441c60b030f61304950400600c600c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88007141 1250 88005891 88005893
    0x906040327140a0504050f0a0f0902130513051e06150306040215070213020d1d0606040e160e01060801060806030d082a040503010605030327120105010305031c0b03060103 75
    0x600c05580c12030181c0050b4000d100084543e100d1082d0707403103041f111126050500e0300d02200400c070303110303401f152401c0c03450400518050b841e0100703082e0344640c140c040054261142c0003015281c0780300020041072481038224101000c031400c400020300c0710140c800c60b011a103610144100c0144282d000c56003550004c8005000340c030300311b408451083d0b82d01c044a80707015055004500e00706c07942840c111009800041c0043ca011181c42413802c501d4600f80d001c600e0a0021a0090701c0d6503003e405548140e40301c1d0a225525031060004004045030b2514060742290f0f110a01c558400b001d21404001c240d0300400020058060701c075581c42003900030041c20301450003100644a51034044d11000c10081000b9041103031a0600f515030160714840448d50392240e2070310040500f0341d10f05400103800ba0b081445074034030218a10005400202e0301c09140c1d01c1c000b1040e00410f040380b01c411030742001d0358280000041800004070080492584140c00c0d039a0807a135012000c1d0030f4402c5001c48541691052380108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88008391 1250 88007141 88007159
    0x50a020607021201050106050714010903020a021302040f080a050708071212030204090f0b030c0d170a021207060e0111030402030a11030c0d030306091505180403030902090906040327 80
    0x404144010101104150483c403854211407003600004041600001d10000f44125101d00c03c40c00e4040200034410009150360003512005508002406541c200c01c0c3c0c0c40319606a0b405840145c030103c9071007001c05a03180041d9030b4440042c0401d9800e4060441d0206680e1320104002050b1495003051009001080d07071a4030303024440c0100801015407d000c0400c1c403001c0c1d401a030b0310b0418030030310204d266451413041604207081485010712a00006041c44002226007005006c280c00c0111115295151150142d0421a0400c08803404000008150302041184e91003003c140c4800c0c0001c00950442040840c44d501c42070310041e505a0000011400003205245140c055170005010b41d0070440034900414940801484200c002c030fa01c032003042c81a01c1e40da214408440b40700b11602c0c181c5514040101d051511002c0f116000004c903803000500381400307a00302c2c4803260b40c05000d0002910303201a80541b0380314159012000506d000000c3d03841d4009034160007030004d544c13068403440145080c0b850 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88009641 1250 88008391 88008397
    0x403030e010c0209040503130b04180209060412030c1412090402090d021918020906070201081e10091b02100b030f030403060b090c070308040b0c091201020c0d0507050a0206 76
    0x8181003022086030b06005884002401d0b0185109900031505d52058040348001c10400f60804602610184402c100300c001d4140b14028114a034000141c0d40c841040c00719482d4403c81d0408540701d40003818003020940e0001d03120b4049406280d9260550703142940d42d9440c0c4030090100b243c070440500c0300c60504e1900340c2c0101300d200307002021185184496408184402c004105052000002c000208150b4220443c01e554031045040304601e0110b11400090142c015200060304000300c040005180450049580b241e44507074240701041440c080306e0110b080401805602001810000c000c0b540350080c8182c1d01f8207541c2a006020130100405200004060454036507605108040201038000c0040c001003004d035005140103e6080200000d0054240b005408101807282c100b181c4004203500904613500a039110409040e5501d03150000b14050241c41070341540814100c21080070b5641c154018030040c15208250340d00c1e081380400907112402400350103130064008000000040c5414001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88010891 1250 88009641 88009667
    0x4060f0f05030727080d0e0109180510170709110901080c0f16080d0507090e0411010509030f070609090e030702040b060f04081f270c05040e01141308040303 69
    0xc220300341040b0f40b0480348030031300d684021407907000140807950480c1d225030f540000d0381c801e0070611626441c005c0c0903d040e080420a0f1007600e43d481020411503042d038400c0c0c800910660740d1102c00380000610485c3c80b11094419070400f81d1510200c041c0ccc2d20f14100540fa40803405031602c4400d551450b0714a5403e901034051a550600200040c500d082c1500c0c1c030b007403401c60080204c1511020140d03852002c0b00c502419000600058032410865070200e0020260300540c418a80c0606d4441b02005854a0080c205860fa05000c0c24008003000400040c44134100c0340c082d5250b80f00c46a8801400045442c000781e17071510340d00304001c0c91000d824190421a400000a00a40e03e00100c1004114040d00241c0005000f07800c01056008004a056000000010040400c10580700c0c596103260710010021490308031003d582e002c000521890190050090030007070010311500b194104d4490007841035819031040703100c0d03520110390b1140c4a2102421690f40c014841842c103411600d042d914030001c919 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88012141 1250 88010891 88010927
    0x9100608131e06021b03040b030c0a0c0b0c0d0b0603070e04050606043201020d08010510090e01060f18030507030b150319020f04050907060c0606030605090304060f0f050307 76
    0x8481084442c01009184110f01031400140c942c580000107005030703a016100961140d006110038401880040126904a01044c4503c0d40c0ca055012090700c0208841c0b0b07000d09070b0600c140c2003200c01d80512008042040c102c810130022280641c080068500050b83d10340000341c09613140c1091030030954082900b060300144407a06140d924100d003801000c05800282e04201c0d142c40404054582e552030410b030710b200740050810800131035401040d0031414882c480c0b107000010070403601240a030a00307002800310090a00340568503054003070035469040c00c02400251301001c2500c5000039050080302940e0744070b40a0400030f441c41e1201c1407611005858584040c56810112400d50b40822805150901040d41e0509010140c010130030a040008140d600030342c205410800e8140d0003040d03510686882c1d0800101c4200c103030030410024210340e000140b41c54980400d1090040c80000640111100b990701c080c040c0d498a1011651042032280003004201c05001089000f40a02c0c0000382181c0d65030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88013391 1250 88012141 88012163
    0x31314010c0906200a03020a02030f0312060f041407031b02060906010603050c0c10060e010608060d1707020303040e04020a080321070521040b01050f0d060207020d05070b04050910060813 82
    0x540170b0401130010b204501503440b001d45082141000d000203812020040301a5003040088140031401803001061148582400094040c3c0b17962564400c16081c2c0c00c100146685141100b40600188001d00d038007500d446040c10031031012440094030520403c88903014010316440c201d8246c000d00b030054680110390409020b01e4500e4441000f0785018041818400f140480c58140c1160301d54906030001410000b290040007140e454145210300e145500042d1401d50b0070307000078145403038060810000d40c0350100240004081c00c401e0500c9004a0003151640380007559501503d030340c1e106044180440c01841d0f031481c54550b189908240e4003030803504010745844032820078400366050f20304900d20001c1c1d594050009000f00508568050101a07400550030108000010740c10016800000d0603640c0005840c0f0454650380c081c8084c441d400012540311a44a0f203107240f0700c0d0001d000302401146510001505006298144021103096440ea00042e458004042840c1d542c041f600743c070100150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88014641 1250 88013391 88013447
    0x318150509040218120d08180c0d020102010b0406091401060302090307030b061c0303020315040b0102100f020c01020304030f140a080408030a20040501140304030503011205010f02031314010c0906 86
    0x1000c6010303405e54880702a0408040301d07138014100120207080354400078007406a1600214001510f039107000d00407a10003003030b064980700403405014903c1641d40c00500309200029030800d150061096020003500f45a5103a8035a5000c03000c80c003a003000c980e81544840e8003040418031030701d286c130b400c0704000d008940b03408445a8040b4040c41101022000a50b0010030884500c10611a0b4020014200c0b42401401c5889000075911302080ca0049820b907038907030034001c030008158119041400854000d6450f07203003d0401410282007446400081651801070300124890001194007400c910389a81149455035122543d4075000180f6454103c0d540e01400b81d07480013030025014154031025080b80e910b81c200000105420010200f8484184d0706005100c0043c7d0080c0c2502e0541d407108441c0d0b8604049070400c14050f002d0b02ea40101400e10020602c40921048141449103900900807900c500001032802400c8036440740f10040040e11511040c42601e01c188500e40c1080031807000c0d9400d0b4040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88015891 1250 88014641 88014649
    0x9030b0606160b04141203041e080d0e01090c09060e0c070812190516020c24070203160609030c05100c060e0a170307180e040f02040e06040318150509040218 69
    0x706c40c904101c99400070081004010150700440c0001034404c00c90061080655510000c600820f02c03241c1540c0d80ba440d4581e0600c0c025406601c0882d0030180d08003a0710b0b903c2602c40d00804450180c1a0868607000c001030319007100d4021101d001d40d010b0890b6107030104044d0b526000501c0949907242c0c411074404004204031941c000c0a018403181c078485400280d00b5500a850807a0144c0e841e4004c0030000380f510b451485080510000c543e01d03480140c1e45040e03620000e030400300b1a01700d54039090307103015000c140b00c0d81c401a103005480c424109140299101d900708a030098181c0c88c850001100302d900c601c0003c80d41e030841410101c0d0481241c41400459482e51801c00741580c640f240c845011081011440d44500c5444240765202d520516050811042060301c050062024003413a40d030030030400840d1281da01c0f400e00c10700d0040c03d44869083c27500c1c004000104080d03900340116000384000c5440309803101040d00042e5292078180c60300c1480002d12010790440d05074502000a42c0e0058a00c58803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88017141 1250 88015891 88015903
    0xf0f03110d0e1b01020a1e02060714010e060121240905030d0f020918100b0309010914060606220b030c07031101060b070609150c09030b0606160b0414 66
    0x803102425400f0480c942e030310400c05407045803038110742c810808000820544a02040101000d03c0c6070900d00c0c42c0b60021550a106014006060055404504011081c194041981503d80000303589032030741e03928008046003001d41d04010310011038211910009100b0144400151b04480c20f070500e80504540c07c1d4221514030a003a65240c10004841703050b40c0c0d0900c51134a41c400c01c04011800c2040c2140492070031003060000c286640414400325030f80d102e0701a86a002080c0c608066503032480c0140700383d8003074005000102d4000b001a406080345000100e206071180901601050424540c0503140000c40180d03050b580c080111400e010a204090800031403181401135015603440c5103903d40102001030400384014603914042e001d110703d1b400c0400b201d00c12078101501158181d124140301628000d043c0c40403542520f8441c0010006030000d2a00b8100e0340a404e800781d01d03964071024803d062040902c07001c1070f004030100800010b8100c0b40d8107a00300307000d011424026001050036a240007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88018391 1250 88017141 88017161
    0x70c05070b07170313140a0c060e010809070e060607020a0e0108010504140609072309070807021509030d090f05070b030a0b0409021005210f070905010f0f03110d 71
    0x440000381d040a11410001c3d89505038030910702c841c40e52500303030a01544c0214514008240d10100a40070381c0c5240d0400c174200380107410240341107070980c1d500c00140c0038101c1807803803d01045a0f4800100c0c4400f000c9600d10484104690350101d603a26034040180e01e90003e8401c0741d000c2c0d000038010410700b4080760743c00e010388110000001c6604150810034800049400b0610807a800241041212040840d480d01100d468807000b9551107030a00c07180c0d9103c04000001c0d5085014030040041403503000681e01d024403401e8007642c2200700003042185440c3c208880d8804164800c0041064a00c3c0650044192600400b40074002c00b1040d40c4071410411198803914007040084244481060140300386030481e0011039081211494a0340401e40000e42da02c42d00040c0000032a802c1064030f0039140d14514580c507507130b1400c402c0c42e04030441203021406403201c1c0d0000d00004c20100b82540035035a10301885900c7c0d00d4a0b007081240d090104c0180c035000c1c00c1c0c012840d10a1004214a52807401540010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88019641 1250 88018391 88018409
    0x80f0601090b060711010f0c020909060403110a0201140904021b0109030314090a02011107050301110c100b031002070501110403050f010c0e0105041e120506101e0e070c0507 76
    0x951401400300c095500391981e1603c1102c0801c8240d0000390956814641a0400c2c20704046004d0000c1040d19400f9607500042e41021801e07042103582d01d000325415215600c84e40701c1421000110a4455030350030306000007404107a03000c01c5480700032442c2c005088040b030300500151070b20411909640382c44080000340c20b22691030342900c0c800c25806000308031203c18a4403000c50b052804024059813081c8208000e030502c0200100084400000d1200c00003030000a0002c1c850346000b0411150b586d84070b24030113801802161140800d110a07030094071081c45004000700361881d00404860025440084c080302c0d03070740d65007038000d42c03001280d0041c200443c05400031780b00055020344100d003901c203544203040c200302300403070f41d0a141d83e00310003918184d4040c2d134100c00f007414054030b50b2040c4188541004840d54812404203007007000000c2c10318411003101c01d402003150740c3d4548801410001d401c00c1071122100c8241030020300e01d00020f40b90f001840d0720300b92208040680303c0c5030500c0c2c6542c00c032141c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88020891 1250 88019641 88019653
    0x7020303130f09020315040c030b0415030c050a030b011a1e0405040c02120d090201020c0301050a2418020a030b19060306080a1703130602040b0d0f0c0f0305060307080f 74
    0x39a18602c500000b00003000040d03140d40342030410894005a4810020300c1556514080e4013110310036484a03c01c0000908100030001169504d400401c4180c40111041440300c0340200c0c80d0b007000384034031003102e510004200d2a6400d242c90340020320040d100703590031403009201c606132400040e074440e01500d44110060303659030b00f0a400d1109540503400005c095600041070140c4184e00341c070864000803044000010010f04520040307050148200545074191308107801d10903200000d0b4007200480860301c000075140d8a09603004c5140512505c149075003c4201c1c001812081b0140e0001c10038403105240c0001d81c0700d400340000707101c00444070080e1031900018000344201c07074041c07155074050320340540103162029107551400015401d03013955070202040840400c0d11005030080200025034450303000e540325501c40710600710030380010000c4002182400d8403103020704042e210700e0710100c4239540d4020403521981419400f40c800a07140c203415108048002521100a1100301c068a50710000307008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88022141 1250 88020891 88020899
    0x12030c080a0504030206010303140c01050f01080c010c0b070804020a050916020d030921110f0307050d0f1205041e0308060a050102070510081003020402040305030c060705030c16080702030313 84
    0x30400300010300c0c02020303a15010034000404d400054460459074103150800403c160b0000b0b100d003d02504c07650000395800c010500508540365601785041c1d81c2d04a0844a002244000442e9000d0b103600019101c03614260120303107400d1013560a10340c0540050032203091145d54401050041e44100d8181000c0300448202035252941480302079045403030381ca018090f03a0070a4503090110500d074407500d0a400302c1c4140d070301d1602e805020214140c07400305003a01c0070740109240050b241d40c405c1c041103540340034031148003030300e503008184400f103016843ea10076900010112000005081c064030948411160b00002c4030204400030030a014248240e5812815091050510041001d5a0031060554101c0c0405012940b1480c8140d511240249008a030f04c0d118000c0c40401d203034064001039041400040c0100c1030100c000020683c1820700800c607609a5030381c00c0112541e01050f40c00080f42c8600b00130194040220b12100e503c1d41c0d0040407903914010b40e660020380703558848c850840c0000b4500d68200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88023391 1250 88022141 88022147
    0x8040605060303041809050f0105040b01060306080d0c0f0f021003020403020f1c080313050d05040815010b090d0809040921110709270309091104080604030302031312030c 75
    0x550011810b5000b1810242170500340800d2070ba480b404564002d98030040a005d005e010410803500c00c211100800c15070409041902000109004800102c0d06203200001c455800044200480c2c42554540000c2c58495803562641e036500304042d079a00078240700c1d83c0302603a100c000343c9400c5102920b00580c1c0d1031552041c0002d070780e11004071901c129464212018044c0e00139074038100f02da900440c829503a80d0788886155880e00e100901400b18030400318042200c1d50004028015501040c0859080c0214440a01e000903000d01810301c1e400400e0022512604041602c40443c91207480c0e239604120041010804a54189070180c4a840342c0542c5110f810a800003072000d041510700c1c100d00c69400c003860242d030b62103052089522142c0d03258200710900c40040840b8441d99442400e0a0b034070182410020701143c1d0074051913100b50f02d0202824041180c20040314100c80b04400900001e07955a2410f9000390001480845200c403140e65200020340b0750840c841d0101c0c1e40345c8001079078100710030000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88024641 1250 88023391 88023401
    0x2060a0b03060103020f0d0804030b0a0b09010905101502010609020309100509060106050711010c120e0306090703200102070302060a02070311010905061c0e0307061d03030c030c03091c080406 84
    0x30901030b800050050000d030302d90310040040d2000664a00394240140c1c50044d40798400c0b540090401104034041c09400c00582d0400c600c0d4030400c0303030090660790306c03900c3ca401104c8003500d000c031182c41288004c10001c02e0f8010702d44107c1e0204c0c0000284507580b9004501030303900850b480c3c20030342c1008030702c50842a0517100d1140c00ca407400000b03100540c10088050624861014003601e45400c8400c080d00c0c6030f2050f401341000c2d51380500c0300040901c113504040c00e06031101e260f040c0f00b8007461000504500c0b0001d2190304481e00403007541c0407a00c003200380d0311203448039009090442c001e100000c000340e114400100f00c108410350040c41e0b100e04d541032120902402c00c0c4502d04002001000300312030307030b100c07402d8401500720280d66043c0c0d840303246403020003849010141800e81c00041506003d0211550006010410719120031101e03000718001c035070f1039100803584401207100030700226100d00d400002959200c000071088a0690055601c0300c4026094050000c1c0021f01450412081005500034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88025891 1250 88024641 88024661
    0xe03030a0617030d0f060b07030305090f0c030c040207020a0308070c150c030e01110c0a0810050a05040b18070914090c150f090a030204050c07200109150201090b0702060a 75
    0x34880c03001d0b09101512441642101d440301615031000b615000c50035801039004011400300c0c5540c4d10310924019002e884200e40818103401480050071001c400402c4020384548020060590400d01030200402500607460a030380000014401000081e403081c02400076900800c203064000d07103050104080b041c0704800e468200040740045000294100340c08000b4200d090a081001c00b80600441e480d00601032150f5900c07080c0030200003602c5030003150041218440150501c081e0303403044584800d81e0303015174004201c59800f4001641400707904003240540101141031310013907503a039217518043c0e40b5284519010290b0340d50034008807960804c442d02c95440103542030100c0c40074002100d03160b4024030030702c02203000c3c000030383c9646542d80d1600b683c00346a0040c402c0102e0b0a0462000c542a04100c00844004071030020261003410364102e0144c400070165584d0100e40c1c14000b8008640500071461f0f420b640d00c600044002807001303e55140304c0c0030b6070381c001c3c00d03141340090501d03096800c9115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88027141 1250 88025891 88025909
    0x9150b100f090303030c0e0d0c080d080c1206010504080f0c0a1d01090c030f090507050102060c032203050c0a0609020306060a0b0315011e0906030506060a05030a15090e03030a06 78
    0x841c440400d41c200e10000200c83d0541000100c43c0d00c0d410054413403e0103980306582c0594500515010003082c00116003d40302c0d030b14201c0b42024011482503400b078a0a8801d04903c240c14042d00f036050751007203041640440c06241082c00c00780d43d20001881d10320b040746165026003207402005098101000c0c00350050404c0c2c2c0d520244114801d0801c11140010b0003070130300301c40e10755807240303a042d000e03401102c044030031003000300860110b90901d25203c5405001d140d0041c00f0300b00c046102030b8a840c00b646d00034031480c0f540944040b0818080c0a48e041d0340f031021028070000b4000020041001d000c507011540c080c950201c0c41900b2481090300b0500014000e61007006c041406000001140c402e5a61060f1030030264800003001d500142c031080700c1d054281e0040380c00305a641030400d0344040c4240445030140c80510003074950300c00300b05190103880409030028406000080c052081034218221140c0c03203140c8d82c600103490782d0300102130f5000700350b0840c150303071000051000302c1c50300780300e01e20050840392 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88028391 1250 88027141 88027157
    0x902030d05030408090405070905030f030408010501060c080d0509010f020c010912020105070914031221010603020414090a1410030201020615030601030b07140d0c110d02120c0109150b10 82
    0x44e803071144e6070050304003280c0540d91f5900040d020600844020003d03003001802c5585501a026105a5035403143c0038900165082c0000055442d008415941d101c0d82c0c82202c940c10020f9030b0140c41c0040c04020003030340e01c1d59200c141001000500d032005026030308049002080c1203440703003003240846200e00307112011685403d08000f8110383c4407405105580d10314081003d02c419240010746400e1a41d00035500c0030380005030b00320031031003801d0202404840d0381c5d000a0079aa0303500000e5003240a00c0c416440030300015010b010251801c203030030a81c041810000020010845009040c51413011200c011041c12110014400d540c2c041240c268840b419a0041800b290840d01180d140d83d81840002c000b60071a20125062901030f044000705040300b0a00c00b901c0e00302251503200500150a9000d005c14414903502c007401d980400d1a90130101650010441541e900c40b54410039407140300441078655070ba00c40c082c00103400100d203a10440d4200c43c04034050216104024000c0c80e0178440b05c042c400742c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88029641 1250 88028391 88028393
    0x10305100f0504110405060c0703020907050a05120604150306020a120902060409021605100b0906100206010b09030313080d200d0e1206040f031e020a1205040e0403030902030d050304 80
    0x41d412030010b07500103507404030f40341d981c180400790030b4021030300703c954000c1c2c02061440c1c04002c005800c03003c0b0b90086600580d651202d00c019590780c400c4031300c03410014004100500d90040d9140c2c80036009280900000b0380c01c82a0506010b6090315a04212111600000c1044034654029a4003111050740300003000010301e41e42c0026414411441089800f903008114200d00e04516090442c1d819040000c1d15140001400b070440100f03e12181d0f28443c008400101c0d005041c4822070b91500c0015030010140c603400c09040484a401c010081c40c0e05102c200f081c0d100c02c0044040340c2c002004404006c0c1042e80794500058014107001a5661404e100030710f00d010301080c0080d0100c1c03100d840707013082d0112100a03c04180c021020180c6070016209402c1407004200c0c4802e2868581303402982c80442000c0d0340010b21b41d0007109041c0d5507005a11201520021805158039400c074a440b50420341d1810340d03111220300905c08129000c0d00030942c3d030107402c810f40c24188200b05614000d840c1c020320b54546 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88030891 1250 88029641 88029659
    0xa05010501140303040e04020d0b090606010305010b07050a0605061201141006020a0f080307090b040605070201020d021c1b0c0b04030302010b0a0510110115170709050f070c0305220501030510 84
    0x10703512481040c42d865202241c2903442c0d0b00400d051440cac111511400510f4149040385c0d980707a0a44403e800a4984800003031480d803804207a410315540a0050f051042880e01c070744000e05000303000142e200440090781c04001a007446040301405041301c11040038907100065180d10b04d081d6000c80c0039908010300600008003051110907034180d021140326140d84070394004840ca08140c2d023043c80001800100420310301e07080f50140100074802d0342146c0650248035030403030321758440c8004054003400740c154050361039000b172031860681008c9102c00c11400780d0b6511040e84116540d030186981c41c0c000101801416828056400c100ea401d0750701c42c5040d45401c02007810103007042d42d403200f082500c04441e00180403e4000710703601c074400e404415000d81c80d80404074144a4203068070709103200b0b55400240c05180b45c01b560748a60243c9940081d00d031b50f07001040da0402d900344401c40422900f000302c4148900e09005804040d05480007001070181010000340840e00050020700010400c030604001101d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88032141 1250 88030891 88030897
    0x180303070e1e150a05091009080c0406030c1809050d090510030e100f020c070f06180f121b060c0b0c13170106050405041401200a052503020a05010501140303 69
    0x10300224031a564540d135440031100c41c0119070605500ca00c5c510391003001d1031350007001c041c15141c0341030685044801e03d00400088581620000f040d000f40800c04000c40c020603036600160070204c400c045148000340ea1038509100d0359403c00f13004902c0c41c01e002d104a09107903400d001404440d080402c200d4a544104030380c1d4000101d0b0344502d00380c40720030501c8441c40540640d520a000340c01129000390f1140d03901d0301d1081d100c0c0038400005540c400800071540074110440101d444803400c04d0006070400c07440f07190400e40d1460030b0f10b0169840310711460304884920018000d00440c4e0314500c0d807040d03d280c01c503600318010b803101002500038001040c80070402c2a4840c112114918681c81c0741d02884151809484154480ca41c800d103840c1c10002400400c004200d28600d0b010000c0210060b032001744c40f14058041e0f030224642c103045c0001c1303010500940081012050304803110030581d442924180d51459a20001c400503042031414104001c2c0c24082e890142090340b4104200e40071210210350740380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88033391 1250 88032141 88032169
    0x605180910030203010507030b01030507090b04050d08040b070c0509060a0602060f0a1104170f07080a030c0812040812060405011202090a2a0f030204120b180303070e1e 74
    0xc04030001044208002012540c010340d4058024409460901030240040c156007500d580842d085c8000074030103a110310040d406031480d2400040c00c00c0c0c1010280002e0022007035040307642c4402080701081c104203031009000300c04d1148100d00d502c2c3d818001407141c2444041e1101d401480400414848140c021906035480108540e180719641d6880c1c546c00d01400e10112102d1081c1c0000401080f0b80a002d0407981c16428540203ca00c0b500803184c4107940e628640c4102c0102ea0003203001c07140013034810030310350b01d0300380c0542c58560400fa10180c0c512041102601c040387c50345c83c009983c5660203229501c460703028030100c500f007181c1c0d0715000c038405407070b0306140b002840b1b17903001c07000030380d51103072079801030340f49041c0301d401c07103103d214006034101c0c008400b2100c40c00400d031313080480c200d014424001c540583c2e40d8000c216050603410703602c44207440409001c10b2010186890b810103030300400c1000d148176099582e10102d1700300c01b56082c800f4400e412240d22101006c210f03030910311903d039508910003007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88034641 1250 88033391 88033399
    0x9150b040203060a030b060112020a02011a090f180a08031302040509010504020102190305070605040f0b01090501050a17150a02031006020c15070201230a1202030402010c02010807021011070507060518 88
    0x1b5940c1c00004031030401180001c0c9800a01c0450b0b2600c040c2e50540c081d5502140030381000d90228004020448600411513590040030720b0703040000c00c411142084442d01103584411032354801d280f90358445030b541045544400200340b040307140c030940c9000c0c01145c1d003043c0c615008016905140d00005d450f10100c0d480c07000c99031040c0c0112420948541c0481d4000f6800400822a5060a14100645140d210001c0e40c0d40300d01c050011990741e0303070b40c401c090480c2d500408103240b29103800600b080001c0e6030315101942e030261040441030040d15a420900c12100e51000507500c0c5443d045028455107d40c10900856004030240062500d440074692080c603441e00140f5159071440c030040724018020180714410800c441114840c2120740400b521036030030203841b401291380b0350100c0c00c022030000b12406030014809807203c0026502030040c2981200301c0d40b058442600c0320f8003c01081c1c0f00c0440041200100002d40786091040521654015150602e0400e10346219100c0402c44503100307101030741c46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88035891 1250 88034641 88034663
    0x30c08010501051b1f050603061311060c061501021908120901060807030305030717070806010c060605030102070503041d25030b120607090501050405030304060e0a0909150b040203060a03 82
    0x60f10304d4042100d100e0048008a440c00710a902800e42007619071040000d01a0908012600c1460041122482002d5022529854101380c0d00c581c01142e03569260305400a000304a156007540c1c0c14040c040c481c0640f8201d55008051705800240b5010140c40454070044c0740c00019800200c941e01241d00801445011a810340c8498010034018181035100c0025441091000410103030004080c0d1700c02d1480d504c8021307410601c05c0001c02c4070541111002d0024a90fa000078440d580900180000315009140000e0742540328804030782268400310007640c0c5c0f03a101140c10081102d86440b001e0f16020700340f4262056040c803d81401f003100b2078900010010707d05c00c502e040200c2c401d074810305d26480002c0c60420322128048140c0d403220403d03654040043c400e16000710301540541d0455045402c09030083d840c0501d0b00a08580c118141d00d1450f03442524058005194400b03405941100e80c0200c0d01d494400540029440480310354551440c062401402001000c2d9102910601180d40001101e0f00e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88037141 1250 88035891 88035907
    0x90605071502040e0f060a060503040303090c030b07090302030f010e19050a02040606090513060e0a0f1d030301060206090105131103010f0e0609011a060915040e0c090a06030c0801050105 82
    0x40c0c4460040c484a41c5600c00720700098400000704a1078024180fa0050414039100e02c03003440441c0c12540192004144100086800a4843d41c0709084860090316010f10203504d0380d40d13241282400b0b8030024001203000c0424815494248098450001c3c010001c003e00c0ed00104120784502002880e400d40a82c684094028000c041c49801131166004208014144d102d4102504415440c0241d60040015460786140c2c021144951001e981115102c07844c02d0380c80c407045801070300d0040c1617501c7d003d0301c1e02d14082c081014210740d0420703042004042d6440398144403009203401030041000400303031306003400d02c400d5600091202d681d4940007249041406204408240500151940d548101c5e18100c0081100340380812072500880e901e40090018500b000c1da5403a4640b001a1280e0f03000c4030400882c8594a07020420901501d40840c4c0203061030380e10a001c0c1038624044800c109810000100701806261a0b290b00001c0c1c00c0f10b060420940711400c2d401030900905004660522400007040340d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88038391 1250 88037141 88037153
    0x140f0601050403060f02130e0906010e060f0301060b0c21030a15082a01020a020618010306031b0602070b1603110705120c03060c0717160204050f0403090b0a09060507 73
    0x203000f075900320405010700840000f00f0301c025400303080381c80440300043c0b8000c9900c0034218440c601401d4290000c114907400e00c90640018034000e001258015486200004991401e01a0400030802a076000741c84251110086090090a00c07504201e440200180c0d0104080901680d400c040b4840300002c0f01d140d10a140d215418094220501c02e22400f5a004845403280c2000d000074210900307642d21907a00180103a90707070084a100250300c4001170000302c266480003203014600307040c1450042400d0359030303440b02c03404541d4441000102030403020302448031980400c0300c40001c0c00e610303822901e03006111006040703c0503800780050030050030b030060040d010fa040007000050400146000180360944100c25500d1802d01c8403d4000e0103410005119119108140d0707840581042e00c01c20506a03003204020b881c0d20844080c003000c0300c01ba20300b00140e00c0d40d109103881069000000d4169040c83e0070094213500b0968803812114404010364000c241d07008480c0c03811030300107007441030f1a400b882c540343c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88039641 1250 88038391 88038397
    0x1206060418110417060a110a0e010c0606050414150102030702061602122a030706090e0a0f140103150c0f0c1e0c050907020a0c03020d02010302070510060810140f060105 74
    0x55200c00e032983c5402804030002107803690192050000820040f0401c440030085802036280500205108000e601270550040b501d5416070f61141d1400141581c5440004d03046032181c81a41d41d45648402c2000384464115035428010702c000d00065013801070940c0020304038850000f440251500131070500e001c41d1102d000940c4410041001da54103d4400d0100584941c0300c05072900b00780c007541000c4001800e001c2036090940d112607503803c03495410810b5080307440340090404501240d41d01c0b0000701c000140e01c250401c0d242103009003801945503080181d07010a1344c01d140d4100c00d141c901c8203080d41783c00486042c2c41095500b004040d544440c1131810074a50201c0f0034a062030240f0300e0751003c100c0140c0b0f004060359011102c41c0300c0b50311100b41c03c9958001031503009200512806003840985000c0c138182c110680b051401601e07196a5503500c1e03007018040c40300728040c1038869400788000341b41800710280c003984011342044940b90020320940c9104c000b42131400d150a4240204020342d00c500c0071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88040891 1250 88039641 88039649
    0xa1e0306020912011d071e1a0c0307030507030905010512220b0a05071403130b0a09200f04090206070204020904110c0c09010f06021b04180302010212060604181104 72
    0xc00590040704080c01040d139041300c00082500174190089802110040211a1152100c03030120880741130001d54081008e800085070f1044105024030024504100020030f2414403c2d69416164460f91070040c1c1105850b8000034188070050102104d181c440e0841e040d84000a84440301031a194044c2c40c130f0480c12a580050000c001a07070400102c0c60081d0005401b60344c1c00e5459110707000110f541d20810380400d4420307030010b1600849000110b030452100641064084800240c3c0002550f606c002104a01c0d05000001e1020940041c0501d060b101ca0360070a0342c19070b02400050300070b42c0041c0b070900c1213020003413080b0340c003042c100c0030380e00c2d551300454010214281d15591040032030303400d603030f40c7c0d80c0408824071032451900003003101c82c490180001128102c1c1c0041001640c041d500144c4004c00c00e0300260020b41d5000905003001482d100c4100e400c0c002d40005980f54000c0d82d40e98203036140108018000ca008103c1080b905030540b024021a1001d90b000040e540e004841000041c0301d652301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88042141 1250 88040891 88040893
    0xc02010e03010c030524030604030f02070b0c0604030e030609070603050a02121008010606261506040f09050105030c0f060a0c060606120e06220302030f0406050403020a1e0306020912 80
    0x207203c641c160700b540c0494014500b8070780d04503080b5441c1c803e09880180c0010703010b405400c8080400c3c000f9014403172600468841d80141e4244503190220303984280c2007042c004400341d0207841480103041c1c0106e134503c00103405802904840c034014100c2c3c3d5135401c0c503128080402d40c0c2c500c00115410030541c15620700c046003c82c1071483e400c1080b009515070700b103401804069403070004000b45040c000c1007001c00d09071440050051a504100d141400510000c2400d0382c00344c08001c8100c1242d444500401c040c0ca11402424020750800c030030a000c540050300700c680682c0c808180b9101c1d80c0e83d0105150b2218000301c40d0b851f5207600600c411120207442d44c01c01059a8104200422100d80002c00c440382400000c00c01c01805440218907582d40340255000d102d1400466410b43ca80e0003001c241401e0300d406801101d186c012070303040c18080c96200e6801080050004035040c401c500c2c0450f2004001c2900b05000320003461116011502c120b45440010503003507001440030f0b09a103030b224400c10401200300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88043391 1250 88042141 88042151
    0x909020705010204080616090909050f0d0f0201150815060102070305010c0206060f1801050f27090f0303041e0f06140105121506060903010e1605090c190c02010e0301 73
    0x11800601135002801414124094540015003880d06490310841c0318140d5520402c0c1c00307240c0050b600091141e240141c820f401041008440000f00300071400411030580e0f103202034449802e40090071180a41c0756072980003c0440d04004450000602d8202d400c0e840b040401c40d9110a40140c2c503000c6c1c10f5200500319420490100c030540c0e00820310a129040540d407410840c1411420408411040380ca55141546c2081c0180081d0906000c1c0080b800006840000b44043c050090b4600d6044005641c2c840c400720020800d118134103100c074241d010b140b07000950a40c207141d5a00545055200d00b80c00004854090310010310010107952182d140d001401008210341c603228502e845582401344600a689072020001000c40c0041c1907074071110b01a500034440d407190030411180b80c0c00740c4091a81903403166418020300e507040c0880184440c2c4624803501c49031820b401d02c140b02a00600c454003010b01400440c080f0a150481c3d001c2d03109041c54004c83c51040e17440141d58075611800400e030150301c2c0c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88044641 1250 88043391 88043393
    0x9150a030f0605070c020321090607060608070b0f1608090a09020306120706022e050708090c010203120606090406030c140f030106030203150a18030f1107030b0c070309090207 77
    0x4107800c01e1a10700841c41405156076114098903040c21810f00290903070b1084c0c1c02044036441448040c070368210403641c160f144c00c29510000f0a1900500000d4562664a81c02040b001e0310800c2480010228046628101580040118002e0040746a004041740388040da04013002007a004a5104500007401141065207540074000203405c1202d107180505242c056000e41d200f400100c0b24100c44659000748944000070080001d5035014107400c4c1c5001084400f000006083c030b001e0345105042998801c0c03c5440e001c201c1c10b00d01020310b05e2a0f0305542041000b00d0600b004814019880b100c1900d2243ea58107100000c60000c0542e40e0010300354891400000c2030380c001d5400003041c44407080310b07606220145401091301721903d84c40020750540c0032510032014247c0c5185980d83c0b02840c800005891081c202c600c105d0b0b100301d80c104400040041d40000c041c25000910345181c50910b44c001e003541400c558401d1a446005861b610511102041c030300304051040340400c1c098486090f00390744894403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88045891 1250 88044641 88044653
    0xf060a02101503120c15021b010c02030c060c0f04061110050f070207170c010c020d0c0602210307080703181b05120f0c061605010513060606051809150a03 68
    0x15003c212042c0500c030741440e9400303101d060311070401c6420052040324a80552100c070000d40c4042c1381201c0851010304003c03a048020302c41c0440240103500030f141d0b1003542440f005e0038030400421801406e0014031035240104680400e840a5594a04001010801c40340a071803800c403442d0303e081d00c0c3c0d90401040010080b00d4030a45c83c0101c83d19000c81e2042da4844203030355403411503d060088164022500080c2c00d40c0700d1500200b44030b001a11592001005488110748500e06070816005a4001d080e103a41c0c55400034100c489039228180c0140c258107000b1401400d00c94060070000405817215400e0342c503507405c0720782c00508942c0414826489484030327940b844441350b14402c1c184240c0b030b900241c114542000c61900a41007030b407005000c010001c081000029041368848440c8140c0c280051800500709220701d42c0509809030040964000e94030307102042d00c4058002800704442880a8807808408100d010f49a00e000c903000443c43d40e491407129001021005601e80c00100040004103000c3c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88047141 1250 88045891 88045931
    0x216140a03020c0111060a050717040303020c0d090305030d0f020c010606080a050901060323010f140a0c02010605030703021302092d01030b012007080105010f091503020f060a0210 79
    0x1c465001d540a104401d030042d1071880340c006040003141c0015000604000d0103901055021401d401c001c083c202905403180d58092013281c084010940c0007a54140c06402006210480310107481d1628840d800c5035101910703401000c0003030030038903110141d185405425405440818031104e0003041201d55482004000b00d40c2500c0340000c544c90a000310310499410302a42058942114054600b03200c0c0c03194140c5506001200703400155610300540001c10800e000e00c200106605d0310b0b40c0355034202007074117400703d03920284081c080d603151540403c0982ca0200759882265011225000e162030b04040e03c0001e031154241141d0302c20307a9180c0d041c031506040c12038801d005092140032201006001e006500b1030751601000c50109403500e070340d840d44481c1c0d0720700c1c3c40c0d0b10b408440544207000d64901103a402c0d94400c5e0001c001c181c114107818484501684652003100d00413040140e600b900c0c60300402d00710150006074a00500000504060440c020010740c110602c00c10801c10075801c0307602e42366075122 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88048391 1250 88047141 88047143
    0x30313050117010f03080714070e0601020c01080f130201050f04081609090c0506030402030c030109050f010c022a061201060905041404022206030b090a05010b0a06020c040216140a 79
    0x94a20884601001c03807401d12070f81a02c441c0c02c0788900440c116107595010f9086404101c84207140e000782d0420100003840410014140910a020303507050410000e8140340c0c0346140f0318100b1040d0f80422200360382140f20a500070302e12298411802d0000e0004072240d10405000070381e04840040d0010705103500040c048102c01e40000c4c402503071925a04c6020546003590005000b01102d14010b100500d407550056811903c02412550740501c0340002c213086d00e00c1c04005940e0b640019809035102c0c0400c2c02000002141072010303080400e0070044489040b41c0605003a40e080024a80d081d100e40c48090858003048a500c6d00d4640640e5a0300004098038458004c0750300031800c021404110f0035441c4602c50090364020304800b6040c604080194104105859444e801501d581d00000820290196280521004005450310503100e05081e8250344111815030b010b030b00103210803c04242e0100d02c100c6c91080488000d655101104034200300b10019144c09030407a0002d000e80b503500b410002d900001c403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88049641 1250 88048391 88048397
    0xa2309040b0130120512090c090606040f120201051315030b0d0206070201030b060d0c030504110111030d020c0c060409020a09090204061b06020c03070b0a1b050f0a020c0303130501 79
    0x11203003c540500d400106416082214116402102c0041c48480d413103c0c0000051402c00d007080c0c103d00c58900883c00581314400e00e038020054600076800c0503030180303900c0102950b02c0c071728107861303d0115641c803d49482000100300340707450781608680c45007048588040361011071200e51343d1640c40f801030b809400c1d11180c0220b46080400382150030030390200702c200b680003407503142400c5154005401902062040035030280f4104144050055184148149814165000102481c081c5007035060304444100c41030500102c0034010602c5030000044480041c03000e00096250344503109058984904981007540c0701001050115100d0129806842c2c005041e560b0015842c1d40c5030034501c124070627800745500240e00c5110100040d8a13062403801140c2c03094100621f8000900d40a0b03003940c100d003604a41c3c401b504400c0c4001c0c01c1d020302910b0205481541c040601d207082c108041c3caa44075507000626601c0340450400c518500030b0012441002019007a20fa80340302c030351510003904d1110f000751804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88050891 1250 88049641 88049669
    0x4030908070f06080105060d0905070b04050906040501080a082d09130506090c0c0703061109130501060503040f030e03120d060905011a071b030606090e010b0a2309040b01 75
    0x1040300020300c1e400849443d9140c010703041c0d09240520806a2001c007210000e60b40704c4450900190b000c11060004158252049454130b04141c10440c038044003500e005c0c07081d0b0030708005011030038002c0b502d2020941d0120141d40d461010180c3c95040d0030805e60300000200c84c041801c00d141a811004101034102102d0b40f050740f2601580c0e01d002c41c3d0302900c01c0f68008941d0000a07085c4108240103200c09600740c803c803460140d8a6444d4815a140130300d00c60416940411005498140403c1000281d500d816041c4030b9981080002402400000e03c054101c041100004007854050543c0424490019043c0e414a6035040316007452a13100889200700c044c5480c0000940e051075109182c10b84007503081c00c1e112034040c95001901034000b5941660402100903c01d05141c00c540005001540700d070720081001481c000e0f00c40d0440302440b0030200e40ea4104544108140c1c1e401c02e145080e102e221443c038010aa4058000d24045800781069400580c40000d1005000c502c0c20024120381840031a03040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88052141 1250 88050891 88050899
    0x510060509090a03020a03051e13080705060a020c06030a0204080307050f071707032a17061315050703020c0d020a0b010501022a0607020a150f03020c100504060b090403090807 77
    0x3d518a01480d015005811101c0b0680010388100c0c02001804c0c50903601e41c64142116040100ca9804a0141071540c070200b8030400250030240112401400211211400d181c15a000a5100c038070f071550241c81441b0000001d2001344580e07040e0781c0505014400c40e601d962192400b02c2c6d40c0c1a580355141950305c2240c80016503d10101c1000080c4030004000c0c0c02c0507440c55035510710200e0140c120540004001c2d030b0b050710117401300c3c0098000302410f40c0032404a0880809003400d0410203041000038030a50700380310b008194000c01041519586040000350359807800b800320024018030215620f54011228202281da500003000404507004011066103640d0320401a42eaa00320b00300300394015024400707040c003002e8420400300c00b0f40902912552504c000355000501c420b8440c0c004c40c03081404110b25450300c0d50700a00c05078600f002c9040462130200c3e0303281c15070b80c6c2d101d5403a292980182c0754030001e410000217803c02d604140d405410810a030034140b40251090156001d251311390f10421000013 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88053391 1250 88052141 88052143
    0xa1502030301121a0a1e02130504020c2803030c03020901050906092b0b09060411061e0f07060b0f0616050102160b06011715040515030f010209010e03070e010b0304020d051006050909 80
    0x50181000b2328034803241030718040910019402606c020b1a0500800c40c1d019006660744090002d65141d60ae01e1000c404860310303000d000c03501e00b16003038405c240c0305000d0515540d0300b0108803141180d040380e074507448001e00c0c6c1c0002c0b402d0f41100c20907041e100001c2d40e58607003180d840c68210002881080400b59a035a00b00d103496542c502254050031501d4541d280d104507003040c0d0000d10f0403103605035044c084139803035008610087e808a00d1180040100092003004c0c41240d100350703c0c98560445041c0e0b51726071544001009405030303503502c4410400d2080707000200301c0d096045800c81f1680e140384c410110715030300b00400908011680706021600742501494280700c5c00410510400e130048207036000042c2082848014135000f08101c80d41c0c0000c0c4801041030750200300b00507001100e400050b07a074004103000107250b1124080c8860080d4041c041c10f000074030306d00740c415064803012009141c0701e07500d900025002e48094440540140101c40ca0004000d03420f0f00300b8030982d20141d81e903c245d40c07103009440b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88054641 1250 88053391 88053397
    0xa1103060307140303040906030308060913050a02010f03020c07090204030302060609040b0c09210606041a060d021e04090608011415010804020f060a08060a1502030301121a0a1e02 79
    0x100d9410382203030b141441403103000030548001c220041c040f242800d480d14881c804544090b0829804203c0540c10821103182141c001c80d48040e1261141121040580c2e41c283ea0302c1d10000020f060101d82c00600000510a9056410085816040705d0740b4580e1000c81d036000b54401d00064005000f1180007510742e080884001d80603d40c817546800840c3d5482c10074501c150801b4000d1544801101032161880203000c40c4448900d00807809000715082090403c012a501220100c1d0a1032040e01b20070b000d80c2d940c005444401c1e031103490140c1c0d100f4580600c0007804802181c00c000a441c0402c01040e90903003a80700740b040d5111a402004001c0700c110501d010300c0b0341181c02204500d10031aa4081e2544164400d035001807000c0c1265102c0510b14000440719000300c2c04c0340c1c00103440141000002e02d019800400101040003c80400304180440251030744414003459a54803494604a402c200d0909050700c0c00d40656251040700341404424000500000190400c1c1c0742001d001800c0c0c804102d100f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88055891 1250 88054641 88054651
    0x10e03030106050315010507022808190b100308041d090a08070609030905150703031107050613050a02041a010e030d0801090b13150e0708010305060402060304021908060a1103 77
    0x945042da61846141016605a17131211070401c2014010a8010f845091101d5034918803a989080c0d240e9580040241c6450954401c000551003450009075070f51038080c0c0040042c2d0800b1545603503070788946440306c001d60a0f80c0000e0003070708001400502c0011140c00e000e880e031020030000c078540e1500c00d0102e5403202400300c0030700f041104120150004851741d0109017120b100341050726580399176000040d9041d081010600c1001000245841015454804e04540c04500300d441c0d0b04202c2d0307e80711280d03030f594001c2882e0a4002d2910464003402010002c407010107a0051051004003031036007154103031821018015010840d1113112100922300403c0101d245000ba50712103807103030700c2c0840c04005401900403058016a9003a03529292a881e80240c0c2c454001f09180035420a10301400125120307001442441082034038001400000c030049082c40d00650110b032942d440ea2034034000241071504400c0d03500451141b0040c0040c03010070206041e40f05c1c41e5448002c01c2580c241c180001c9242c841164 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88057141 1250 88055891 88055897
    0x201060605040504240603020a09050315060904080c0f0304050a050105030402130c03020d150524040b280206070f030608030d051e07020105040c140609010f180f0305010e03030106 79
    0x1c0b090020741800c0e40303c2c800f04014040841c0c0c3c0210303030000a160700c00d510303048100003940001e14854490b40000b4100020881580108800c8400840349480d10300080d051920950f50705001c6024001e12805a802102d004001d5410707045100da4034544d0303030340288a654010300c58040002040d40c060400d40384030f681c001e002d180040114050074802480c02c01717050f4040c1a82172140d582c411100b4810f0210000c1e00d41c80a00800381070804000c80b5002d01c3e4100c11078854102035214400b0400d401342c501300ca910304105038441c0000c00c20303039040300340895a0502417003c80c44000d900301e030b00240481c01201c55846500384401d0b18a4100c0940d4080d0007100850f510070450108480c115a05c041d52281c80c0030218900c070703015103030309400d0090240c46000060303446805020900554800c00001040c14501031000c000c01303c40400c3c8075000311009a4140201c00841c0400c09010343c1303031400e201602c034190f802c4e00c94a42000030f10302c1d504d0380405e4030650300e0514420156140001180d058402d551 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88058391 1250 88057141 88057147
    0x317040e010e04031209020102160f0e0903090307030b090312040501050a0f0e0a03111011040612090201140702011709030c15010806060904060603080d0e0f120301060c021809060609070201060605 86
    0x42c8845c02a111125080b4114880d030081034582201d404a200003520380100700740c9404d803410000f11a490740180c44180346405c20450070505987c0054150105ca5100c0c001e804103076a4030300ea890950042c49030554009070030600b044200441940058898084020104030b1421110041800c4bc1e81c1180000360a80c000302030000402e00909404801c50b60020407141c400140518038000d4800020130801d00110116040c011280c002d01c562224442c0e150b02004400c0710b54000804282405a02e1015240c001800b44150b906c00d150540010780c90551200c2c0d90704214041a50f81e600101d1200d489001e22055501010700f403a01185c1224000d8000b8482d03500c13502d081105010001d003080381c6050ba5613500200040e131000c003500121640d4100000c0710941c2040c4070342020001c40c00500b29402511101070f40c421420140c80c155001c6103420702402c4018801300300704401080d036085454546608028143c100010901e03c03601003070f070391b55402d5102d1010907400d0b10081d01400f00850814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88059641 1250 88058391 88058417
    0x305041701052403010608100c020607050a020604080903010228090b03090a06020c030c0105040c17030307020d05090111031c0b0a140409061404051005010f0b070f0c0317040e010e0403 81
    0x1c2c083d03d00141c50003400050380c03a548410003881c4c209014003c518407601c07040d03403108907034042c04030701d034070201340d0914600d4543d0850307000b511402d00520090070603c010070300c9112610254150b480144220145805000c1c510540f101821280050740c400607031030b4000864a41000e9041da402403c078000100121802580c80b40e000e90094815000c0a1100b804403a5102100b4000c05024074014034208403800d0904d410303218680403000300101d00e58801c00c01d001050b41d00040c1d801c40d0814034605982c8401e0158012a400045040c00504500c00400c0344403e0009151100200195541081052056000078400c44000758411100070071180f030301e0785600e1700381500102c5205100d00380000c4c2025200c01c0c69880d040043d501170710b0341c4d48100b49246104005104036409004007141100909140c400c55000601c03030090020024651440074508001e800c45a0001460340007441404d14000c00116a4254100d032069006201e05640001812460192018065505565220016540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88060891 1250 88059641 88059691
    0x100509070306150c08040b03130b0415061a030a090201120c050316020106080706050304030c08040b07020306060a120312020c150403090501030902010806010e0a030b010b1209010614010c060e0604030504170105 92
    0x1454814500c27000300041000900d85816544140d00c100504800310b0f01c10b80509040304c0c00364115124401681c06400034035a12942600d83c80003400d80b01040090035403004032103001210324221141ca090804100b155600f0034050352203441c61051100c0862101503040342600d18910410758160030116092003410301c901c5c020746d0b0040c02420310040d4020155107803078403944141d004100c80100401c0820443c5401d014580d0007c004a0713554042a0408030a02d80180b100350000b801c0c44900042c90f500409150195640c0030000710a82e41c00d00580002e2a14040c0308403003c40007e040c551000c5000d42c000d1103109000c98042e076480c6400d0313490500548840c40303030408003540121034540020004001a0825000e407404038103032512044004170010703414402400b03031851a4107058040c024100c002019120805d000d1030541c0c1d00705260f040c25401864207004200d454040e910401c020305400c0802042147c8018a40300706004100045900b00c4906462070000c130241c0542c1082103000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88062141 1250 88060891 88060897
    0x9070c03110304030c0f052107060c02031504030309031205040506011802070f030207050a0b090904080f130b121609050f03070909060e0105071e08100509070306150c08040b 76
    0x550742200e1030241c807610307101c041400a0f8010860001c1c1c004081c091420300c111440a800c0d003078020108290482c0424648800c124012001003010b190300d0302c025981c0810030a4200c07111580082154201401c0081c00341040010640106001040c1035201202c0e0f4030505101d1500080900466401c1c41040f0f00501d0f000d5a5041543d42c0074410000880e13442250645124469002400030901e0803040c8420b094441c0e101c04213401040c41151842c0d221440001da002d64404040caa40b002042180700140c090317901c1891400b00800c601003007000304c000082ca4000400c1c8400d0950340d880d802e0f01e450615a410b1443c0001d8189031041016060460100340200c0f00102642c5007242c50b12040b400b19101d03d9405e0313032040d484c1da480c4203030200280b003501d800c010149000b0403040003010711070f41c0072020f0034605010807071004001404074000762068800b402c8000c1500f0440c0c10325060050103031990b401003110141240480c5544c103400707a09440031181c1c0c0400180d0030189003c50b01c0b000c0f90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88063391 1250 88062141 88062167
    0x206040306020c0d030b010c08030a020706020c03030103050a11060a1e27051314040308040204020d05010e040201020106150c08031f230316050904030e03030d0209040b09070c03 78
    0x100180404000141e8034005840c600228000038202014103160040c2030b5074250090906100c030000c1007001140c03121084a601000b8660301503681e140c1030bd4241c0080c0304c0c41e83c140c2c1c103a006c00310000c800c02001141406074280540034605100203420104406131140c0c040c0440072480c01200a0700300402c0200c0c40c80080d80c0da00b0601060f01080803c500300c00c0101c2e9030015641c109031000d0105160503141303004c014940e503c04004a20f010424044043c401a10203000d00c059980010115034403030f011a01044800c0c1c10601c9156035660760301103030001c240c9017240903500f0501d004c039040005421140814410340c0e240000030340d554032450143c0d407002e80003001d400c00d0700000ba40d452074071140140050440001f20000e0402c2e09803041c400c4100c030002c2c0e0b0b12035000b50300803020404006182c0d5054417001c0320f96910644036894103441c002c484046040e0140008034101540c4801640540904d0324192000e1245010820401c0b170022000c440c0358010030045042c4c0c0000c01d2061501004030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88064641 1250 88063391 88063399
    0xd1a130b010c0606080d18060503011205120403080715050906130602090301050126060108030306060a05070219050a08060f0f040c080a0506010306180309170309060d0e1c0e010c02 79
    0x2c50807540300c0ba0143e0710950000c0340654001804001050b41c40040d01d4946200009600500f40c1404001403043c403043c40f400f840d8503000380c06c8005100080c8010740c03a400110040036620740d924500001103400c0450103480c0c2c1d03080750300149082c90722405040e01c15602000a020140e80b46400540c0e070050568046d2215a0b00b40444905500c0c248a01c0e0f000c0c0ca0540381190074010062441030500d0840418250240c002034010000e0090010650ba0020811a021501c0c0c40b9040740c03c44030380c003403500041d500611440d00304e80e10b14040e11108094070381c00d80b524518a81c4131086542e580300107817003400319914400002042827000641d4950424030961003240d02c0307903039405181e01d0840c103270300c6c02d030340f80e400001c010410001d007441a03d00c4059056130062013054a51070103824418144a039010741e6001202c0303103c4600044c002c6541e0380c440185416141d40c0e5000a00004189034095424540b162481c401c4485802c107003100c4600f0b00a55500d10402081c4004450482c1500401c03a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88065891 1250 88064641 88064657
    0x50105150703120c05090411070204050930071209030201031d15090c0307030b060907030902030d03050411040606020f0105010605040b030a0c02010603060f14010e010b180a0b0a02030d1a130b01 85
    0xd0b5444d4007078514040e00000c5802e4440d401401000120cc5002c1d0103400140d10085038241812a03095900c1c04100c0c4205010711100c0c0008000403507071040b810001d004c406500030b5078070215007080041003528000e81e0f0401084809070040c5001401c6c01c070f0004029803286101e003d18440e401c072401d9000c4200000d46841c0900b29001c40c0ca850015002181c41c6446501003040d282008000203600c8400b51400b440b00801c55008039031214050000c0e0010143ca8400280c28014900c0041c801320401074070030482c40e035032100002d444505840c0f51481d0703542010000a00c00b80710f0b9050390305460714500c002e40307141c80b030340d10707aa00900e1502920380541d502e404000002c42c585100318a40720b01c04100106800d0740301d00c0311031f14000313058200348296907141005105031264242a90301c1202c054086440c50030105002500007a882d0340845204100015288086907012001d401d6a1102010520131010a46500081010390250701c0da0896461400c4c890320f101185c00546129406041c0f543c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88067141 1250 88065891 88065907
    0xc030206030f07030b0906010c062c0a0213020903060610090305061509060405071b060902030313150e0d030516020d0602040609050108130611120a050105150703120c05 74
    0x4000c0d001114203003000c2c4101d00800000c00e4250184880301ca000300c1e030650313003840e0040019001529555001c0d05840c0c1d90030507055203003080258035004185a4500e422042d00014106a1b1884800012809402049a8007401d0f6404c0d000b9101c560302c000b006004c0301c0d601e080520545810306c60000c010000c0050000020840911031140640003040c9104014241a828441d01030000ba20b86401246400304101520f07600006d40b00c0294920a040e000190b59810708001030050707003134040d41c503000000706004051090341c2c04204641036804140880d05042100b40c03540102000b4040d00100c941a1071000284100010000c115461004c0c4014131500e4020940840c1440300844082d540014140a469002489500100003d01e40584140b8013034040d0100c004200ba4024095921103004140d00001d880c280c030308984510041805078600807140304064a005e20071103019040030b4294050a032420000c842c1d805030107444021030036208850700c000920040c0500e42c1000010f204a903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88068391 1250 88067141 88067149
    0x11e0e0702030301090b010804020a170a02040509010c0314070509220203040f0501060b041202150405030a03091a030103081b030c030a0e1903050d030b010302090a08010c0e0102120d090c0302 84
    0x50150000d40d00964a80d81051064030880300c0421150707051005845c00c1000503501c00e0500b1007940e01500030380131110075402030140740c2079039810000e40c45401d0004101000d40150b1103803142001d5070741c0c1402908410380a800381c5150560301c001c0000d20400c08109142041d070086203074900f55141c03604000c010320210000300c0e00283d030101e58086550404030b0501409000f0500908507d401c001e19051038112043c50710006108024010300c0c0e0000315080c2c4100d00d4040d2801040c015003a00d00c02d0590307240c0200081c2d03490207000781500104800c03031400001c400c00d4038180c80c1d0160803140f4040222542c0a602d4541c246244050b110400582131401ca0a001900d40c408160f1250320754003c44d1420489040310010440c8414240d40c1d0f401c0011800c0091101d03460140707805c000079840c01c071200403400b0b031044404c855046001d04500061070301c015409808055032035a42ca416031000880126154081030b410b810400b1414030401761240b190740d05c1260714600c50003504054694960100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88069641 1250 88068391 88068419
    0x904050103080c0d090f03060b030c0a1706090c0108270715020c04020304030e101b080a081b032202040c031509060503060a050613060801020306010e0301050609011e 73
    0x480d0410400f1943c205414003c00c0251922203080c2445d1003040d080c10340764959554a480003518042e20380f0b071900c0b541c0d141400101603485014240100941d201d464058580c220240c01140c188140000186941030200c1c02c0510b40405030340301c080750740b150210742004507600d0400100c4c0d5410400c1d41c1003460070401620f0001c101c500805954001355004c003070f06000c1c908507801e001c1d070f00400401000a9012242c045250400c440c1075100e2191840115250014640440c0c1071080a451036000d1006402c040c180554180c0d450310f6180e40c0340d9510304082c40b08800c10104107002440440d98101c4000c40c220980546042c40700008180703500058140d450a01200780487e0b80da50017440750b11590600e00c000b03890082c1050100301c5c0b4140100742d032100d006140e01551640c03013010566a5a07400600041100000c80030301c0b480792503000581c001c1d48140c4010f40442c4d003003407071426981018001c862107140d009207a01c5c00c5030b107001800c1d006554136041401c045081160007107440c50101c0f203c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88070891 1250 88069641 88069643
    0x3021905070237090504082b020f071707150e0c06070b0901050702070f03030305060f0d0312060603060e0a0504030509060d1a06030c030720030f07020f1005070303020702060904050103 81
    0x24203100306210146049034820700d40c004c0c4400c1400c06080101203400c140c2158204061103c0c0ca04102c881e0801d0007005030078410003103100d0b600010b0925050381c3c02e900600707402e43c02240c3e040e000f628848200e00c4c2c948991800140060180181103124030150b9014611898180c0140e80c00d041240c80003c10130750200e8002c80341800e0b401c0a04c2940b02d402d109440e4040042e0004000080c1407854195100a00d403200400f0541c903100084c5c49512030030220281480090200c0580400303900d400b5104010b0440344840f500c2c500343c400035500c0c0c802c1c09814101c404040d80e08180340c48010b1000041c1400410903028000304010803241a251170004244254004600151005110300000029445040850f00c9940140184004540c419084030f0b002800e0b41821a01b0b010481040d050150f040c0060340c2c5540808200c814402e6184401800b143d03108a594140701c4801c01b08000d41c03041032850880000703005118040000c7d0003036008088050008041f24280302a1000160503640c007608 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88072141 1250 88070891 88070959
    0x40f11040603060e0702070b18010e120f010b0907050a050d0207020603090303100608152202031e0606040308030f070e030607051801020d0e060a090b03010b0403020a06030219050702 80
    0x420000403c0c04203001741c020204d44080e05d03d1b01d03e080c90140060050343c1c0c000c50f1038203114401c4c2c00070b41c2c094000342214100103400c6030f410604018000342c0740c6049502d031041c1c95080810320445481c0103549148905159103030133007003040b00a011105a04480568a5244e900300301c0305025a5960001d1441148420029035403480c002c69580300c0100f50740c0c040c00a014a560034058a0f03d5040c2d411001044280c03401003010046580c0c508200d404c40d440042d2142c4008188039041600f101d13504200ca51200d110725440d1540300a020390740c1b00314880905880428000724060b1001164001d03000581841c00ca8050148040040e080120585a00c00811000141418030605034007000c541d51800740041c103400c840c00d2101030080341000440703a202d61000199290402d0044003040d001d4114804010745941d1c4941c03004416a02c81d01040e881000201c0c40018058482e0003210401d580350180c2004108400400351081d0f00702c035070700f280d00c0b185211041c40180800c00000e50b990080340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88073391 1250 88072141 88072151
    0x3060b0706020c0f01290105090411180d0c03110105130609030209010e100306020c121306110f0304091e0e0109060e010603030507020d0515040305030601090605090f040f11040603 79
    0x129a45203000c4c11600c00010590510058103406007a1894000b915600300001c2c8040b4400440126858841d00341c01c00e034411714140d07001242509250181c8580e4a1103044000c0c1036416030f04002d9241d20f0914000c080582c10442440059a940000c0e11212010b0408500b40306031030400b200f034016603401a60007d1800c513030070010351804d114a40d00501c0355034990796103818000c1000c08205114040a49000d03000521124481820008035150900350001e154840302ea180156aa500561207400300040e0303d0401804100c2022908008059503000114605031501308190007400c10202e54070080d0414800c0121607440c2801540a001005400020030401600d4003d049a50311039130100242c0c982003060000035040001c484040b5012a041d1040035114078081d494503909070300406102610718248810160050040c50144d02c0907260352124030b4503407000721054011042c40d95070007444210791810302d060540c058400c0401c07103200440c007505450aa03801580c4958007020000c0d64036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88074641 1250 88073391 88073407
    0x120807030605010309031b0c0911180102030a0c1b0e0106030507032a1b12020304091103060f010c030201150f060e03010c080f0a09021c0501050a0b010f03090303060b070602 76
    0x62007448003900d024241084a1416074600070860401a0a400c52500c1984081010b1042000c004c80003132070207440034040c3d980c2035103000040b40c100b003c507614413070721080c0740300c11560021096904203e129901d5115020807511140980d003240340a00c21100d42d8900c0100d030b030204495420b4041c0c003103034602140c60b00b800302004088401c20713200301c84c1030114004006010140000d00c0c42500c0030f0741c0f170145d0520740c84502c0c401c2141c0003a0802012501843c410111094001c000342c41252000b610030032003050104104002803004039007032540020343d20143c042640c02102c2d83c11642d402480000b0300380e0944540b8041540c1c460f004840c00d0007000e00200106036002c003140b44007007010383c002d000d4246d01100c09440450302900421107083c0307120000e480345019038010b881244c5c00400c1441d941ca400c81d4003090312545650306481c0d039420400003c0b0080700a019141e90700106a452a684540b0060100d009000c6004210105a00d80a00003003501003403000d072588d10300414005948901c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88075891 1250 88074641 88074647
    0x307050a08060a03051c0201110c0f071a0a030513020a0f080d030608030a080402031906021b2406040f05010b0a090f0f03020d020111030304030c020f0427030309120807 74
    0x70003000c0301d100e000043d009200188000c52840d290b507024178000320305144020001d81c05040c582a9012094a0100709031603025000195480552110025200c400742c80301154410580b00f0711400155010400006060910035800542d0007a0000b07c001802000c950000e00d4940c629840b4482e610504c800c180404102031001e4064004503046c10046140f030400025241d0003410708101c140040040005c0654030300f440000500c006034068200009270900e81a0000d4000610b03100f60b00804910103041c0041c001103d2000c0481c0d070094460104c5901619810303880c004042580240e20f90005100d6052103000302c0c0d005e00803001c00c0300c0d1101c00c540c0000b4445c54880c1e02240c181d50008030104100c224008000040d01e406517842021180300c1d00040c1d48640740c1080d00d20b8144000402c11061562000c1c0044046100310740d50252228180f040005480101c0000011202191184250051080140719096100b03040208a00400b91a81090030140c021101c0200d2181380c100f00390142c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88077141 1250 88075891 88075907
    0xd02150a060315050a0b0105090906040b01050906030106050a091220060d060803071202070f0e0402010309240e060118020d0e0f03120106020a211101110c1603030e090411060307050a 80
    0x100031b20b031440c1040107000c0000c84029014001ea0300503640c61440d48410b3f4420001c07101c6111000d0b215546c0d9513542c2000a00304d03400100f54070005080844085008244060110001d541041d40444501040c8107210148420a0301c40c0d80c3c0030800300001c108281d03841c041da40003840c10102540e2111410b09248120b824402031841c02c64004105c103011006840d451101a00c2428405060503600c034401a401010440c0001d450310304001d50710886483d50f01c01500100c450301c1024885c00411400c01555a0020b018048800f84409400d40340c04140d83c1c05040d509454100c00300e42844480f500d641801c8101107400b0341a080010071812a4050104c0e03540105031620080c2840c4040740c80344680c3c61a042500d01c50218440c03040d01255101ea45000c11042d118002044a24007040389041d07582d02580540d44a40a0b4180000401f11842c0c0900c040b86d415460729998207155004100d13010b03000400440f148040d424012602e03449420195129005c0c0340c81d210303500d10f040180500410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88078391 1250 88077141 88077161
    0x150307140f0402120106080a020c06040c1503050103030210150302060c0d091401051605031905040807080f0c0d081905070606170a151d031b0d02150a060315050a 71
    0x2070041004400044000c484d00303045a1031450040307400d44649040902134401e6100c2482c46109020520091040040c244005c40e107400d950040f032068440c00c1501541d50174030018000da00142518004841990007031002d0152045003410300585030f5000500c950401e000c080341d2a4030864004e4031683d080f401200c058460000b840110404480000345a881192010012400d01c20840820800e04000b0388040a00c000141c41280c4032404000f02990020322610074984181100001c0340c0c00080790511000100740082e0508aa0303150038803442a501c0c0e0000c5401040c00c00c005402d5413104000a044e45038140d445680d58005420404180c0d4116000fa00e102100c010341d41d013582c030000550403030b0241c0c0718500c10700180044105800412004102c41f000500102d41400c42c420048028a4206102c1104507000d8048030a0103a56020309404c00c005030b0312400303149ca1000b0610f9805540581c00140102c0d502d5207968413003404005c0414080562500d440c203100910340d603401042010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88079641 1250 88078391 88078399
    0x18031a0f09070b09011b020402120f06010306030323130b0a0e0a0506120a020c0d0c05070603051b0721030b01030f0c050f0309241e060612150307140f 66
    0x31505020001c03d182c40303900445418400e40030032038500040304420076013000d03400600440d00c03100565496041e0082c210307581e41c401c0c030040380010801d6009100b00d0301503a40590383c440c81088001083c0602105110810b2600d0f441400620f8401000c0e07540440900303c440003103900c40c9070742403010b00496403240c805840307001500710034091921404141c9200040c0f0814042407500c850070b5580c0280f2501400c2400f80c024010042d12040d04a00c0d00107660740725108582400d0b5603100c040f001c0380e0381035500400c403c60b0304400042a07001d2a01a0245902a002c2c185160080b0f1000801c1d0741e00c0d104010000c65210740314004a581c061240040f880c0070b010307050205203150344008089108103152703400344820100100e044103c08200c80182c4003656209090980004001a40c420307200302c84500010300382c442c08034502d5031800f18a50066402802060600300d4a11500c01c5060b402002c1010707400f0541e00026247d0f50401401006103c6000800c2a0542440c1441003001c84042d0690003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88080891 1250 88079641 88079653
    0x9020a050307051b1605091803030412020309090709030201110d02100c090f030f020a0602150c0703020a02150409060f050f190b070602040504060806040f020118031a0f09 75
    0x5540d000000c80358414803500c1c0480d40c500c501955280040b1000d400c101252183d13002c4040c2001c04440943d042d0b80d0200ca0007261036494140100780c0a400422501c21074109001060000381ca028412078120158010f03a0300700100c0d6801308107505e8003110140d00085561404005650b003050301c0c0c1564080d05405080780064490003c0e50780d01841c29505090b50303a0310300140340107100c0d21110015081201100e1f0400b5900d00702804640603540080c1e10030750320344500050550000494107102c0300b11500446090352261444000c0b038000d24429815405818500e20069a9441d0400a040c80f85c0c4000340d12a402c0c8280002260403039003200043c130400c840244a90f03550b4007042d404030582200c41c01181c083c1c200e550103038007180d644405220900890300208120040e0041c00954400f5142001199038410b002d40e91f5660698016003800c550300c030f11a0155101d0310891020100c2d020003010015aaa0745100c482c1c030b80401446094034544003800849036004e5a1603401504650003404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88082141 1250 88080891 88080907
    0x50109110f10141b01020412030e0a14060d060b120a0e190206030a0b060f1c02030402011b02010e1309060e0703031d0406380f0706050402060c060405070806010902 72
    0x10183ca1000c045501c0c8680100c0d925000305481c08500c5500f03151003000390b48403561000e034090f0717001c00c0a0381140400c3c881c0340c0d0f43c501800d01003401c200316110007442c190400041d070280041e541c080c00c60380741401d864041c0412543c110310018402981c40d20743c03040140c80c0070180c0ea4100d4a0b590481c0f036031a080081c00c400c1c0c0a8070b800c50721922070307012190b45550382c0b60401042c0c028112049003a42060000c141c076105032003880c02a00610106820300b03c0250900400d4808034072003107800a020900c0d1002c840c0e141e038484800312076514810304040410803038200c0003070076030200c2e6001915034030b8032001c9180c1085118000c2d01c0c406001c020040c018a811039034050031540441d0210500742c5a8850003c10a50701e03030700080d00400000100009206e160f80d171700e180d8030084000f43d841000b50b03002d4000042924070100d4402e5442694020708240f040e42d00d041c054000504140d030302c41c0d010301c0b10070106001031002c0b030301841c03081000740911803401d120507050000c140d01021003d417051090078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88083391 1250 88082141 88082147
    0x20d2a0b07030302030603030c06010b0a02010e070608040305070501090213020c0f030a021c0201061805040506130c0b0a030213170601090203070507060905030d1a011b020d02010e010c050109110f10 87
    0x104210b50504000d80c480c1c0e00d080100f032543c051a44880e0b00c0d88140d00001550702541c0c0020007000e810b990003440400d29503040d05544444a02c0380000041c2490005800b09100d400234003030703242c0315000101c0d1901d13907500040e018154000403403038000e0303000a407000710729010080401c8828410010314101221030320040e455240c10a4000880f010204801c241d640c401c0d070120021f007901810410419103110101c0c4000c000c02c40d03003255284100f00100e04140c20303941914034156444a1017105990420004240c0c1c1d4105010b280c0500d038007440b525140c22224065400600f40084815030f5102400038082d10307040060f405080d180b0f00c108107210b0301c5903000084032501608001c012070300c01051f280c650320718483c24100002040c43d094078148002d542030761840c030b207e400740d95600280006070b40e0b043c00722220b060001e52002d1003004800c0127500428240b60000c00505206541104c1619441d0075561200000c84030401442c0103680c0e14605000321030303a080d0080d9400342002821240c06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88084641 1250 88083391 88083397
    0x6080c0702010c0f050a060b1002010509120d02090904050a030311120109051005040507082a0d150f08070302090c190c080f0403030c0510050c04060806010507020d2a0b 74
    0x80e04000100d400300c400c3c004e100070724201c400d5001007191140400c07070502400400e03410380003900c00c03c034089852000078414000c0754001e1031114060070301c040100714401401d5100b0541011344580030f2000304800d50320101d502e80700e41c0c081c0002d00003030b0041d072a0060846206034202c0c5202c00041c803003421200b1284030f400341500d01720340300000d04c1d8072420b01c1000d165003542c1c0240d40c071604000c01c00407480d610103080350041e0150805445000d004001c400c480e4140580b031040200018440d800c05000c054110390600c020f0086061921525000d400c001071126400030015540304600030801c41c14110003e90f40f007a001402d01e410202e1070403842c2d818030351900744039041011a00140301070010250860760b04840070221141d845e40d6078900a4103c0828150646847c0903543c110380e604001406040c0c420769520003141d14050600c2821740342e400010b0b04050401505204640058035400c0040544900421802b03500b46001070f80004040e8458112050812205e42c0402100983c2e2051b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88085891 1250 88084641 88084643
    0x1140106020a03120b0405040f0507061b061503080301060206091006050a050402030709090515010806030a0317182407030b01140708090a09020a0f020303010f060c060e2506080c07 79
    0x280900c0c0c801d20442e18041e12851805c10f41c401e281809100410064004500d441392282094460440e925003040e0740b0344145000c2c41c403c3c14014210720001820360ba000c07450222880d9580c1014646a03105e0601039002608620050f9210406014642030100100014800b061506008240c2400080f03210107a080c485e0170b00440e004804a58114002d503041c3c0301900340420704000514040707079030000c0004010a070902103402e2801180c03132402c000c81c00c40552505034640d00ba944a40c2600220b080c0c0c00101507400e04001c10310407810700c850601035450004609424041a100400e0f21418120301c040c049106040c94403c10014a0340c10403c05060240c48070360854441e0303014200a101c1d072243d50790555004008030008100104141c0c081e000e0080302d96a0a000c400c0d0b401030603030341c901c828010003071034904070442000700c1071080c2c01d08090f8510070100400c1460880040900e40828150074210b03035440030864181c2c0064180c0e00303100030109460450642d0070100c2c0d04002038030949074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88087141 1250 88085891 88085897
    0x10050a05090c1902010b0a1a070f03020a0605070e010807080603150901020d14070201150f030816060f060e07020a0b010e0601030605060f0301030219030206030a05070e0a031401140106020a03 84
    0x4006080400107074141c41c50051216038080c0c820f005564002d009050702244903209100c03a80003c54820b9015500c0d100ca4100a5070b0149400b150b604c0e40c1300301c2480d092044045114180e09000042c1c0203000740750055900d0340f00c10f43c503440010005049488028402c40800c05c80908100c0140c0d00022464000c141d02001c0c0c1403207480b804520b1340680300d802481c0114500305030b50480e036441000100c51140c0d080b43d00800c424868180784642d040e10170f11421000d00e148203001e00104414100801190003280c1e909600d070f20031a170350a016a050b040080350600c0d51b520041000c03613004100e50b80e0185440c8060440c81c61a0b9481400f10f0301d041c01141c1140c42c4920004485900982c041070281000514481d12005404043e00d0258800d0100b28081e410050400300580380400c5400151395005003c035085645a251017001010014400e404001992280705003d440d42c1160310041e50061840311045072201c0c04107400d46140341c1c03104030300704103e100410400f98080b13a00345c08254145 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88088391 1250 88087141 88087159
    0x30312010f06140d05270601030b06030303090706030203060d06060902210601171f030b0118020f0301031b0308030a0204080f0f07032613060f0207060807030e01090507120b10050a05 80
    0x2800000013006c0e007001000d0101000d071030680300b40e21300040c2141264454902c20746180c4c1c0702c1c42070503281d01080d100051154800d88090120078002c1d006143c0c0004081c129442ca403a041d22000213844040c0c0c081c8003101d50014100410b00202d652410160210000407981030403d00c0000742103000c00c081c4903040308025808501c0c4120f0300340340b004032802c8480100d21107540b07070b0900c1b0074940c0080c45101d041c500810034079a03060006e40251341d4102e00031404142035a19544602d060f003850025225034403080440040b00052502c1c0c007841c0141542407005850b80d0802030341500e051805a201100d0b80c0c1702802c0810303084000684981a00d0303000e1280705504402d0000340307500441d10200198034200105403a045c0e840350035514000c0360340d1982c9a240e0040d040b0303402ea890b070199016501c000780d15140000d4034207000e038106522900070a03000043c4020181c41e07143c10210b40303400031520043e030b0414101c00e00458031429a004000410090042d6151800041082c0003510980f40110102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88089641 1250 88088391 88088401
    0x209060d02011b031e080f010e0702010f0e030901021603200112050106020604030f03020304030905040c05091c020a080714040f06030203012a02010c0206060d02040b030312010f06140d05 82
    0x744060040000300e101103c0c004880310700e400f40c410803108582c6007a84d0140c443c00c40c40b80c0d104400d03050007518401408001c590904082d071182e1480204400155900c544450020115078407031410044400c3c0d01550f00c1d60100000203092410047d1503180c0e500a0041c1800825558a140c7c2500d80003c0b48600c40d00c080715006031100e4002c120785007241440c180000410710780200710188101e00c290b5507507201003890341042c1d049000075200600003500700e40d0300703201d40d0a2030b6224080041260070020f044c054001c0004944140d1006489240d51041144000b1400c180000340c0c0035080c0030f0701a01165080c00821402500080d8443d44165200d0740504038280859010101039070300540240a012101485080d009503107200104804139401c1000940c1481842000300590480d400303811192280410000d02841e130b18820f9034070030f5031380b80e00e4015640c00b000207054039010080c0780d601d55072400c942880f100c0010342c0404140003a01032981880b0300d900d41107030010242194001180d441d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88090891 1250 88089641 88089647
    0x12070b07060b0603280903170702071a190201090f06051314030a0f0809071404140f011802070c03080c120d0902030601080a0b0103150b040908090405130209060d0201 73
    0x4000d4190f40c0041000050240c0c0460b0381c0203070f440a51301021180040c102c07182c1d00760f040b5000c0040c00b5000407500101041d01121054205422610a10441c0c0109454070b038070340c6c505400c2282030189440000740740302072120507a026190084032400208642200c9840ba040030100c41840203103080ea84c0c10001d2140000e09415101c0340740c1114a007103160354156202c5569030b22104901c030101d8005c900840d21130b0310510b0034621400020f00600f04080c6080011100013050311011a88151154a10704c010050b00c0c924030701c81c070101ca80003500d40d45800303202d080c0c1c0820390342030115080c0100009800304d10b652048000700c0390b005200036695a000120207041100d07503019540c00200c0000d07403051f01c42a640000c0d130124000c80544100d0f0f641c0b42c1c0c1e80d0f5514100201c0c01400101c50800410115483d010642c0e102d4500d0a0003041e1800c045000804550301c9803000c680003000840c54200d24201482000e500041000c00004101929000105d40c000005d125901c01ca48960300c13a411a44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88092141 1250 88090891 88090901
    0xd09080d02030403081305100f1e1b020102040803030f09010b09040606090b030c030a11010504030f0b0a0507050a0905040c020118060501080f0d0c0318120501061412070b0706 77
    0x904004195200c000816220020358000d807000e40c0040c0c04072001c51402c0a0040c1215141c9038060001c0c0301c000f04994500000e04605c03400821425940c2c1c03040c050120307115000c07840c40800360f500060306600e0050740354403000b00300c4180707011684144400d00c80d03002c0010031650002c0094041d40c002d40d0b501170300580540202803034150040402c200b440b0801c400c5400c0017007030f101380c5c0f4000e000886001c010303d9030307d179410b01d605a456800f0404407000308041c00c250f11280c00040c50301c0392a0585a4680e0034004102403001c03202101a030302040b002d00503911849402a20624003c2c4c41c01302410300003885c00d0001c0c040c0310301c907035603490034628414002d601c04208a210000482400e0019080a50051409102709951801988a0809440b00102c0c04611540c0144c481c800390040075107084640c0b005440c2500341a800c005800720f9004c29032000210603034420000801c140e1b003071030300480d0500081011280503001d1480e50440c1d0850110f81c00082d81d6a815a858446441d0306200001e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88093391 1250 88092141 88092143
    0x3010909020d06090615060f0203040e04030c050a05030a02160302010c0b1008120915040f0b0702040902040207140106050f010203040513020f040315050c0711060a0c0209160e03120307050d09 84
    0x1901c0d102050041003c00e0700071213400a09060310f2565071f9503c40b010760b0303011280040d20f070050708104001d110020080752010b421501a24207148800c42d140e1b0796901d00003400405131801d45c0046805d00d02580e04001500195140400080140b0300c0c503030010340714641d40c010003800d1031458000510702140070b0341484000c0c22030714100c074044494490340d0984c503070200345c040e4000d540300b2801c0d8209078600400c540c11078a452003500041480c05400038400e411424007260700984400100004d681c5a00244c24000d001d800c048036801034502d440e03800c41b5039035840140110410010810180e0700802035a04541064420060b004000e60340301c0002d104100d40e00300070244c0800c01205010003407211242d220500f0800304125203c4403c070122900a0420080a00052042007511828030740c0c0500310403803460518101c5600c16500082e031041d02100c0200d80021030a804401442d400342c491981001b040e000f82007483c0324165281041e00c8001c114005026000921109000c019440003403a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88094641 1250 88093391 88093403
    0x405060414070f02061003110d03020c0409060b1201060e070c0201110d08160801180b180c0d0b0913141212152e20030a090e07020303010909020d 64
    0x240c0380c03612016007202c00d40809031005203c1c0744002840409504022411f0b80d4200e40c541c0300c0781608008100014450202c00c404601615620902c035407580e004a400b124804e501c003051007239042090104032401e01c591038485a0500b58200000c2c0f21903c40150001d000e03180250081c0280c2c001a200c41d920181d21550b41d2040000f24200300340d0203108107010b20303005010000c89aa000f2022105010300307000380147c024ad003e04d01740f4000115800000001405896a41503505141000018070000c0740c100c8400040001d03020f000000600c50300c404008100e80c1c00841d81040301000703500106000c0c006203001800071501c1c820040411100f6808020131103c40e0782c1d014105012081070201b81c5004524242403003080c0040c3c6407500790440726502014044008c0c450040c1c000b210b480c8803041070f405210741c28801c0d0f041100e8500803810075220810041d03954020002d0003c1422159500c0406050a00000d2050070341e80401103034115000381c0306c00304d803401142c00050f00050b2030705001040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88095891 1250 88094641 88094681
    0x1b030c03060e090705040506090108280501021201090609060609090e0c120a02090f040203030d09030504120507080706021f0e03251101021603060e0705030102161e0f0204050604 78
    0x1266000108007094880a840522490715004284806440300307014488058104007000883d0030749290000d0703400c002c00d2440c580200350949650340fca03030200c071110032030844040061106c00c8017405010000c102c01402040101c2c43c1a01c010b01600c11401246c803600d0702e8101803042c000c410801001c80c60002094010110400d0f60499a20740034000c04902444156000404154a016090303100da07802502071803800e07110300000401803280f400118180101400003080500552140120780c5116500501c0401d081c08080e40c41c0002d141d100d072007154040c2c41e001550000c20402c052103844102804212181101802c82c21409486418209070444c411000b54080d05007401d030800b140114240b0342801c2400e03004903240c4291415903034080b0723400541000000c11580c0010300b42e482103401c0d1503203d92594006800e81e449080c05101541101102209200310704d1320a01d0144800c940e2101c09014555038801d01d100c41c1980a840b5a50350340005c5c05603107803a000b540a5480075204a85 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88097141 1250 88095891 88095901
    0x6181b1311030414010908040b030403031d07050315220503041a1b0616110a08030421020d120c1b06051b0c07120503070b090607080603011b030c03060e 67
    0x400342e00215429682d84a1000ea407881c0a401846013000454110240900d040d081102038100c650010704101c1c20142d49032801010034822403211641e8540f09000f800841d071030181010b2030041d5480902c4501c0321014140524072107100b0810305101c03022010808440d1440c01d1045c214020796024031f142500d10000342e181004500010310049151200c010380045912546d280e446400312508946a00c4100d040070707005014461011240080c0011103506100c80e582e81c0c48150010342d001c0b10140584000703c0f61454940072005299071541c801004d000310102002090030f0041e0f075090414a83d034081030f80343d4a20030b800510070001d10012140b1000504e00c0d0070001444201d444041c0340d5403040203050803121542c11540c2400c6040000d00d0000d0821084802240c184101110540300400c081400035a141c42042d00c65a00c0c5005000c00e0328000101500d99000108481d210b40d160130202480b40e482002005050304d201d1a0004011a0358101540201103a0304504802129030003008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88098391 1250 88097141 88097171
    0x112020d06050114071101031d071202040b100c0602250f021207180b01110f030301050907050a0f0f090f030c03021008010305070905041a041406181b13 67
    0x54201c44007071341c0f03180e14441c008040d0013281c040c02c03070010a07901c3ca91050100302e40c4280c009100c1205121100b180c0c41050f980301d03a14000799507101c3c595004000f401e40f0154a0207124101850600f6140c514028407401c0004101a841da00024101079000c039603000030040c201141c03030751a9060002200c40210908200860036840d1b2422886541d054200c0d1280c0c00c4003080d490125400c00c1e8501c010070603091401d802820f60903000380d041001840f822070b03000108024107a4415041c02c09981c2e40d506000503c0340d905801030140040c030078108200c5408a034040000c03c044036880c904400b00207600c4004489102e020b80c84000c8400920038040188068440c1a40449100301d07101e45003069201c0054501c44824440500300313400807441001050b500e40c0006500501c295180c83e88940080789440880409540c2540d117a5003030217000b28507030300030040329030450f08490342e141260030003448036642c0c2d00b440244d0f01d9134498a2854034082c1c0d16440060036005868000a11009448a0300d078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88099641 1250 88098391 88098401
    0xd120902041d0706031a01030f020706060e0a05060f09070c02011403010f210201090303080c0d09060c020c04110901030902030a0605041407090c0207060f0c0b1005030f0102030906060f0112020d 85
    0x84842800b5480e0b000882d40c0c001d12406c800b0b5260203840785014082034005400400d1045038200b60b1980803c1108005901c521880c0046c003c1c100b1a82d505040000c0c0300d404a502c004d007d24065011507107a42d4190f51805191030340507000386400012000c00d40f00484820b0b03900780c41031180340808000805d04016121a0b0000d88400030110500068440d81101442842041c041e020504989061010a1054480c241e1010801424614190011140d0012201d6407101500da0f0780c0d41e100c003054810341c141f0540c505510101e0b401c0c0903590b1484070b00040b03803050340725036410b040e40c481c10f004c1103403018050000c096400c29010095868141008900d000315005100c644d40a1a040419420300520500b0f05200700c5070b00824046003403030809c1e00d60310305200c03c407420701030042109000240360449546c41051000b40185d01c0602c0c0001341440d111051440a815034010301c2000440c410004159501020403101d5002c840c070100010f81d0b0f441d2685008481d102d0000450310300c1d2407210342203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 88100891 1250 88099641 88099691
    0x30b0c22091b02070302060306011412040309030309060804030801090b12030c01060905100e1f1203030f0c0c0b04081b030408010b310515040609060f0909050d12090204 74
    0x280d0010b450989400326129049400000d6020009002060442d4410911810104200c0401600e40700e1603a42c04520500f040b40c0c2100000e0019006000301030740148110010507141c101104c141c2003c1c0c8e000340650105000741c5009644c2c80d104804035580e49441503040348500c2c0c00b07407a134032402d0300c41c814040c0045000d8142d00c1400c0c5404520308541c000c400d84215151032111100b41d88034520031082c030200040055007280305007000466856141e00011421a110b91030018000808146200581e04904000014040c500078800d000c907103440540c030380c820f0707000703400540e42e4002180510b49014041c1804c01c40d4030003c1408240450b05600402c43e01c00206c81411075000112002610900d0282401600d28103d1041c500001441c0d001250040c0d480a550160038240c500480e04076801c075031090260f9901e40c001000002100c240d03c0b40946240f00c1e06105c2c2d0702043d11941d03601c00d0f10740c06206c100301690480005900050b488001040d500900600c6103403180242006485c6005030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 88102141 1250 88100891 88100921
    0x15090f0602151501020a02150a030f15050d06021218070b0702011715061903060b0f030408030406060305010f05040506060a06020705120304030606080618030301030b0c2209 76
    0x20021414a00018140c0041d1032141c40c2e10190f0795079240303e040b0705814078411505510445010100681e5020404003103450102070243d103400407054018143c03501141a2240c00e85410081c00309070301b8826051066550030795039080340300c04516201d002403080c0d00d001d2510135054410710003c80981c00810721245200002c442900e42c68020559040c032900100034042049003640d00044a4050442039114841c0e0300c400125070070300740201c1c420398000f0b2807050308550030040c08044a500762151b600600204200141800c0304d0380d0350788441e80303c05080640242c41c0440000c04004d51030b0880d60207594820020300401d09a05505000340005450841c0c59024420001d0500e00340b030340c2a0030407a4090703801003003064501411b1104241d03003401481c480303000402000c070116816002d1440200364a0008200b83c0c40e0410b8884401d01015032020400d800400042003c41d6824039059080340c030218419a81d200f10125440b005980c08112a6401d07580030740014000d0503076440340d080d07801400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 88103391 1250 88102141 88102169
    0xf041e09030915030203010501051606091a09010c1b031103040816030201031a0f040c111911090103050d0305060a090513030810030b0c0a020307020325060f0c1502041509 75
    0x2c042c4e050b40401d004050020342e00380019400c0c401c0b605c45004500e40280d80010746074010b40c981618199581e08140c90b00a07881040c0060010701344200542e528091401d020f05006400c2400051001c00310050100403800810917150785c010b104440007081d9800880d20410800710705003035103c01601c0180e0100b85001c040043d0500c80d140a111240750040101000c01d4018041100a003042c1502608200c50500400b481000c01c0218543d80500103010002c1d0004614141e00501114078105001c1d200c4200100009840007820044800540c100410180d03904400700d41c40c0c114035402540c00f14100400c1c46800c9201c1004100b0840c0650f4490381c1e00ea84000b00e9240d140b20601c4014442c2e0b024800250700b011030003010309060303c82c2c3e1068030715101054000074a0030410302c42850595100c900d00c003d1416228040324010300440c1048048074080f1140a400d140baa1178002c0c0000305201140f5052a516a04982c054010100b5890b844981c0746d500178580d1102c0d00512854201c85 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 88104641 1250 88103391 88103429
    0x3030206070f20031308010203010302090c1303060e0a0b010306020a020601080c0303070308150604180b04061d06010207030c2702031512070e040605150f0f041e090309 74
    0xe401012003600243c442c40614400e2501c0240c2a4848504403c1580011701c420040070000382c803080b0003403111000160b142c0d4154010401c8900e0302070a60712074520108015480c050220442c0d42c1102d420020002d407034069580c001e820f00c070740e060004000b00c416500100422020b5030142091800d82d500321a880d80c5c1380c06203956031b07d01c01c000b400c0d4154010301c2001c0c0000c0c407501003264020001002c03110403000440115185412a4021f101041e1180c14200e000d28502c0c8140401040e0841e414010300d4646004d00c81424940300d440000c214200d80000c1d2640d008028a000646e409550541065907804180c0a02d104104094100d4800c42c010103125801e6402600e000d01200d04019040c0540c00040081c0655040812021400350110000700f04425010541c460b60280401180e146400540c220100340344111292240f4107880d2181e003e9141d000844030003030320944000a1190000c440c0802c91140489120901e9040104100c00c142d40314941030210750790b42e86641d04241030b07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 88105891 1250 88104641 88104647
    0x19060b030f06150402190f0206070302070206030115030e160503070801020309030405010c03110307050102030103110d12050c01090b09030a02010e030301060c0f4206030b040803061c0c0303020607 86
    0xc20841c41000c0e60141c4085803860300305038800e00450100a100500e040c110303220414607000c00300c904801054130429210300154042c4811a440805481c04514007252580096003500042c0602030141c00c040e064014168000d81c48008501e0800044030b00041d640c0320002c003c40c203d070086600a025003100003a0507001402a1783c099a030300c40103141486c1c1000011964180401029820481080c480644042e4144000c20312607020340e0002da5298150704010360245074520310940110050341c3c588011a45c42c0741040d00e007954034948195101c20790108680034101c4960003402444002d0140012144000000c040d11081500284501200f40e5241500e030f0209202d6a00450701502c40c01000a03e102040c418403403080d1a12880c0c00c05007001400351003200700700300f08402030078006880495920b0100040721002c0e4002800403506565850f10b02c41800b810007421460040007240150343d0700e100c010f4101d084035405030603080c041e0401c000d038600355120650260280b8008a561144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 88107141 1250 88105891 88105903
    0x130905070605120609060609090c0d060b0a020303070c0c1703040e0709080d08100f081e060c040302040902030f1c091e061206050301021309060518010e0408070519060b03 75
    0x1420030001003da03284e40034130520180c010072155001004003e411f0140c1da9440100b4010905000000d072070f12800c0445008a400e01d80001e6003c0e14140004508564000101d83c3e00120301c0c90400c11112042c0703000194090f0540010f41e00e89403403e8180c81c4030000202510854981d803240040f503071034540050300c01e00c0181c010002c0b540c0000b8180301e0050302840b2540e400001610030034501d203a8a00c004960300d21281c002c05a190000014052180804e400c4040e1004840000e0a140c0c01d0800c0e10796224132540c030009014603200d445202c00e40d58240304500001e0706d400c06507812030b000c0c5481906074180c90782c00e280c00320310060008540c00007240808403007240400c003031800e070500340391040e90300c0e055460601158645446020035152030a00107480c194a40104040c0180e00300030060b810340c3c480350407040c000c04400c4d80e0320000000c2c5203220350445401f5402c220305034945003031200d032621031003201030401e2007a09030000800b0ba694200030f03079090041d20b0800a0405280405813581 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 88108391 1250 88107141 88107157
    0x3010f0b040f1104060507081c09020f03060f06040b0303091804020a15050306040b0613030c0f17032d12010e0a1a01050901030e0f06070f0c120c0f02130905070605 72
    0x1030f10500043c00a00d006a00a20703681740240c10490411050b100310f941403502c46110002400e03100c050040171420402040e681d900e00480141125142400c0e440c0518200201554400e588400380031503203880600454541c2180a000040b22030343d00c1000280c00036066400f00d002e286202c500040000c40c039241c0e0350000880e61340303040c03031a29160100005441c1c00c20390168464820804440d0710035840521000441c412000c110800f803900207185442e8035075500c1082202603483d40e8580b9108d01108483c040c552000985800d000408401a06508081c3d012401e6100004501425692038480705040f590018002c00090760fa081640d016100900c20b0080816403034030050f0f12039806040541003405041c500029038207030f03104a9510b442010503211510380c01040034007102d6039210b030407072801090500344880210015924510001056120744040050a00d8600c0030481201050102150001c0002d048403810028a200503e14040c0c00c80d40ca20400100050042c01002566105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 88109641 1250 88108391 88108421
    0x90506070506041b090f1b0f080103140115080601030203100e0d0305060609100c020a08070b04031203021c1b1b111201050408040f050a0302130c0c0203010f0b040f 72
    0x68032a1307aa03201e0050300c1c01e15001c0c400c4c20304080c0420001c0745842080c10b241c00152011448000c840103054003031a0145484007081410700d0000d50864120714182c0c11030341d00810740740848407000d82e038500610199081c500c81c4ea00d02030380010010800920141620700031025a12030000000e82c01c41103900c0c0602c80f2600d07030884101d41c071206000f03501c0154411009407000c0e1a044c00d50700091615100d00d107030b010104880c25010350650a0a6181001510b91030300240a900d08040c0d140d802801139210090440c0458555000034920a4041d101001d900000c600100d00c40c40c501c0c140648621351001c0c4000c904010316408481c418103403000b044502040611466000362988805141d5108205401c40c0c100081146440d109108442c0f040e801000f941d92950b0a14405a98089141e40306504c104480070003880541e0760488442c19400d100c0000140120349900b00366890000c0c0e00000e5031651038410616640031b09a0407400c04540c007100c4c10440302c5c2a50140c007045840390b104e0740c408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 88110891 1250 88109641 88109653
    0x9181c0212031005010e040609020a0f03060509040201080f0c160f0302010f06050616030e03070b0909010803031b0702030f07030b0a0b030a050715120203010803040f0b090102060a0c090801020d05070905060705 92
    0x180d54001c03070000c04031810160001c2415625210f254090364040d01d0781000163340005190401d030750501c50707000a400d0880c2d52560f5410300e0f4000030800c50300504030f0006191800e002c81c003058850700c21280381100c051820b0000300c0507824862204070301500d0950155003040040520b80c030f520311401c8103407400145280d082105a00b07001003400c0410504900b80310402251983c10703542041811300400c120001c242d07940c10300e036007400491041a801500d8a9200f032040c018030580304102d107110b42c0c821011301a243d11032800082e20309a403041610389280204a4040248001c0840e22882400e0b400c0091101d901c3d5201415035554443c0006000c43c0c02c9100107100d0341202d4440d629542500d49011943c07006004054000ca0303000781d0043c400b40e40002030802071034254541d55001400c040381c0e4a82820482400030b07403030b440000d090803011035940000d401d6840c0140f0b4010080d00d0018000c640f542c951811200041c841640c00c4800b00701e083c0000610351030000c0c0ac840e04070385d010b80a064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 88112141 1250 88110891 88110899
    0xf050f04030e0301020408010f09120f020d0c0206090405070c02010f021501050618090a091b050d1205040b0d0902180603100c0909020a12060e0603070509181c02120310 74
    0x3424985070b054059055408001c0010303140000d00800c0b0b4221554040000d000c001d51804004002400900c68180300340300281135201c1d84c000c10705141c01001400d24006000c0e641c4001400e600c101070003281e02a00c1c240c10300102c60381c41410310300212310170780344c01245a08056060b69035000d5a0711440d050021140103200e1420805c0243c494000c866446641d0706448400044129604543e04920241d41b003802e201030043c40c1d00c00c0d40700e80001c060076905590512011401084035102d020f0120602720b10842802481107046400030240902829118200311022802074450004164071500c941e000c103610070a0041c40990080600a004102e005d1040ca9032901a040e03040e2101c1c02d03c00021400241c081c100d00051941e002107030b4600e8842c242e6520300f60111940d0b50000048002c4100070032005880c005091000e94204449250045ea62a8001d0080502c484450009409010308460040c80c0214400900851540035030f446074294000310038482c00100d51282e207880c4281c1c0200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 88113391 1250 88112141 88112147
    0x9100203071b081b060403021215070504140d11041a0405090304150c06060f03031e080702100e010f230a02030903160201180f05040b0a0503060402041d07030c090f050f0403 76
    0x241001c00b421007410a0307a40d40018000027041a00180d00b40c10000080403000550031215500a64031308016041500f0b107403000801e4265002c24034000c038484c496050501c24a01d001c9003007258018814081101d42c40b240054a0890f03610150003281810081240c2a0011055070295030390341c02c19010080c0702400440e0060002202650b2855541c0c01c0800d511843e500300001850080e110314150503254136031840b042c1c9121050b90200715444081c4104d6590220f0075000d501c1d412000404c801c0d041c0130005005014849981712120700d41441c0001801048071508003038003500549400c0e6584441074141a031000b25002c02458004010350110303100840203010301c890062400310020740803062060041c0001d40c0007a5800b03d8030340b004001074540750003295201d94007580c40070901440d00c000b182d81c90310080e000a110b038ad01c805444400440303000022400913600e004440882d0b680c0e0400040b00780150003081070960511010303482000840c00b8a501505030042a40d42d20742c0c3e41d0f1800c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 88114641 1250 88113391 88113433
    0x503041a090c130b010206011701181415100909030c0206030f040c05010e01021515060a050c0601050a0509150301230f010e071202090609100203071b08 67
    0x22104655800e08800c40d190031200518418450000281104407141003005500d54801c2da56024141c2071210b48009660b01080c01c50442d81c409680c000b291410202d628054000d800c144200f400110300740e00140301004000d4018500c1d20390565045100d240e44450340d00e841211100a000c0c9500410010305031940c0c86001085d019242064040c4d0725503001545079402512503030f05031003c0c0304c280000d100c908081c4100030082424552684ea00c107000103901d0728a45a0090300300d203000000140110b0b00981000400d0600421160760307024444030140258203e03140300609446100008681da081840140054450040c50ba582660f41e0440e2110010100c2e014540c25541350f80c40a01512044819001042860500349040d03280401191450312016400303101c40c0070085c814894030540003140c00d071200000c00c0b805a9214020800701340c1e0340c03103400c4000da041581401d80890311b541c08000307410524030458640364401c100701c80f00300f0424140d0050f140d075a0019619280d801c0d40070512 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 88115891 1250 88114641 88114643
    0xa290a020a0c03030503040c08010203071d210307050705042a0e09090a03030506030d36090219090302060307030b0a0308040303050306010f03140408030405010e120c070614030601050304 82
    0x11540001510b564046011000307a100320b01289010083c03004001400c3d41103005420000021800d40c034000d48011b2000c01490200040020750960045941c0c03160502c0300c0d420403103950700b0700d40000c1c482801ea907664080c000c1030315280540503011691b4603040c00388038981a4400d544504031840d001d00003d01003030001c149018030560702d40c2243c0c1c5840e58a103841c0f048015401070207189103681130260a03101c0060186c2c3c80b0303401008811400b507400011001024000c00002010001085501000c0960a001004e0121506100014003400f00e800070000c03140e00041c1c500d1400f10142065640044901000358030032010b000098200348240e000b00030b9040c0c018180c40c4059601d80b1800b5841c3d115400c2500003440c000100f03e16540c020a420701419120318081150401c034a02c0415a40c034081c10081480c0e80000104041c0b003c01d4114244050f51201a0346840000f038210080981c415a000c0500b40942100003560034042c007940307024201c6c0340c19198650307035995004540307940c00100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 88117141 1250 88115891 88115893
    0x3050309100e210c010509060304060903050f0313030906080424090c080a020a06110607140f030a0b0a080d02030409020a0504030b0a02030a0b121e030918060a290a02 73
    0xc95141150b59101c1c0100740000c00440d41d0003e2071415407181e081c030b00062241c6040c44400c0040c00e01c55101d10003241c0c0e10a800440c00682c07003100b4502210b05116009903070380071100c044240600c0398081c1103150801e600c02c2c3c80784042c1940c4d503a82556990070403540500710018644054545000103070082d10250b8100e40c000603120b005560340088004d40e83c00c59561544441c12a60441c10309043d0300000c0c05050502418034013403030119981e5940d004080c3d40801c103c01c1001010705510005807404440c2800e8902c0e100d141c040c2d41c0c50004d200c4000e6103482018848000100c00782d020804082e06115075001d9481c060600c2c070b403240030703511149007001040800c20001010500c505481401500218005a944d003032090740c1d4800d0302d030844250340c4204080d995400c604000011008024031010141e603485d00403403402c4078154024083c00c50380080caa0a604101c481900040f1840341c41c044860994641d200c00c0801e41e82044000800c03c02448803803c840d4041106001e0605080244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 88118391 1250 88117141 88117157
    0x60708061806041b050c01050f100303030b01090308030109050702010c0e010512040f02040608031209030f04051e040507030905010f02090a06081b0a0908011d03031b07080c0319090305030910 84
    0x12010342e80400c45003080c6001a40c040f41d1043c406c0c0d001c0c01016000a8070071072803103650074400e8038001c115032a480001c0905940e102d034800d1507400307600003000464000d0001c940b0b030340e903503c8004003070b0a084404c000117500c2c0c4207841d5070b0f40e40074405c2400d52002c10303521541070400d25041c2d0305240d20094000e881c80c11610b45000016601c2d40100c00280c5840f0313000e107854600d0291400c1d00c00d2000340c0212416003042c8118440c951314041942d0403503d0440c0d90048541641c1c2151a011607000e1401c2d81050500d820482003039010341141e90014414402000a41151b0107810124007943c54810b030b21017a148000c211491180344000d4001030110009030502820302c241d44400c0d031085001d200424001e00007000242d01c207109640e1401c079031501c82100b0b10314500c0d50907243d00c0010445016680c509901c0d80c810b05012003611882c0e50311908541e6191005255541d4980040301605404c05c0410104401c4070710407007030381f02101c0c0d02000031400e0800e40410448550300c0300d280241001030381 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 88119641 1250 88118391 88118411
    0x904020705010e0d0f210b040603050c2704081e13170a0b06060c070e0c09040b030d09030803061c0c080615010806040c0c0b040803010806070806180604 67
    0x54401014098400c400000d001c0c90020800b500f040803403034400b02440035401c1440c81050b08400c0400084c40c03410407120040d004401070f4001899038a081a4110f0b150000100801070002544800c1e640300702c9580e44010300b01c945d20300c11200c18600285294150341c0109000442d00c070041c228a08104595141c3d03561485031070070054016a0b0b40310001c807030a4008020513918809131f0840c0103c0600500130784101a02c8540da0843d0141c56240281c0c00000c100301c40000c18801e82026000d81540071040e42403013214280746822003c1040e2280e031400340a080589000181c2c4600314400d0740f82e49515071303e0740c0c45103851600002c1c0419044003504280d81c500c41403015201c04080d11510502c075199050281da20f2a1400c01082d03010103c01c5040440d4080e0b80181c1c2c465480341049134081540c0d000c1500440d1444040100107041c01c00b06d20512040000f00d0700a1810307114081c0c112801991100d000701d070440000e851140d04003070135004071446040c400c182c0e107a2004000c1e0000c9080c09003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 88120891 1250 88119641 88119649
    0x11090405041a04080406170f131104060803120117060403030f0f090f110603060a0515071707111504090222080a030318080a1101060506030a020a02010b0a0605090d02010509 76
    0x402c58085903401c4c0005802d11841e60009413440c50031117072401c08a5540b4154251200302c01d40641600c901d50300c4203414404000380802404504003002e0000e2140c640e45200c03403652508411001035941c08030000220740060f140340740b400465513030001080243c545881c1a00149441d202069a080e103c0c1103c0c84c0652082c040c1651851044041514100c010700305880d044060400c034a118050070000c0c00090f641d9440b4203015545c0071100c3c0c550280c02030070700420b03a200c0e4944c010300503466091801c400354050000380c90058041d400c00130b800c0c2e0303415080200401c1daa142d0801c0c1c456041c0f00600c0481c490b175000d0900c58544c040ca0201c51000d0001001150102d80d01c00700b80b513400386060700105541805000007100000742d400d800403019644241c10381c02811180001c120700144c54030002d03182500414005c00700507042030364030300f00081403401941c0702d489214090342c2820f103451002d061020700b640844d01c05079142401d2600c40c1c0101304808024850981c104071041c8480b6a41d660303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 88122141 1250 88120891 88120943
    0xa090e0a02130605070b070804080d0b060c0d091a040f0b07020402160b010512010513030c0f0c03030203070308070f1e0e0418020a05010c0302031c09050604050a0c05041109040504 79
    0x7a00d0f101ca80d04c0c1c40d100e1802000e10b21b4000c2401c0108000e0600307110000c4c04202c2521241450b608020460107034100210f61540103e06400c80f45210791003001d24070a030041c4d200400d071280d5440c440c1103500030450001c2a803099100c1c0080340f05c0d94400400c0800c01003070240c42c405100401c0540b81290340b0b01240340b290462241a65420440c0004100c1490014601004070006a0091059207051001c0c09003030398000ca8041d00380700745403011604001442814400701d6234041c21505445849083c0299a50030441d8114042410000800c0d21035000740c0066500e1507165403010003050544508030400c42000340f050301031203144425244c841e91903000c1c05482d00b907218a5010111600d0040100c0303c0c205510443c18800119503150100303502000b2a4032407015410100d12990a0350607040061000310005001030040d041480200000480d0342c41455005000980d0381e01c2d1a10204400c0b08c1130309490f642c038030304100901045401c10303400c100d0b806401451040c603500341203840008041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 88123391 1250 88122141 88122149
    0xc1a0c030a1205101404020901031b0302030109110403020f102f0705040212010b0711060a03090c0603060b2209060b21010e0f060d2306010b0a090e0a0213 68
    0x4803600003000340c10382e003072084079400303503d0036007900e0f07807614050540c0c18500805440d02c3c011500000c00c0c070280d9010703400ca50742e0403044c4440e41400311240e040082c02904203004d4002d24038104404011100041410786041e6a001010700340d4460342e100c100003078840c01c00750560038041840f0782481c0384501400b40a00701c82200500140f00042100500d007048461f801041c030540c418003040780720003203010a10341503400e8800c00d6a0b0f81c119034201510315403103c8103481c1d4002d50000b24495100d80c10740044152906c12031800402c82e49590041d02600e540d801243d440840901401d041642e405490302c01c64039044507000007085e00ca20030001910000c0d003100701c441c24001100300d030030041b444d01c0d03107445058080d54120b01d50410503900450a0b01410110800000d00c0215080e5903948a116070202c0d4801d000c540c40100c140c1c414000300d003154007003c07201d0180d20000942c00c4180740403980084180c0d0b56070f00095040c1040c0086040000d0310034000545e080c094190081d61010f2088090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 88124641 1250 88123391 88123397
    0xa1a120d0206010e0705030f041410021b0106080d1404030b0108060906090c060703111f1a0102120d05130f0305040f05031903050a05070b04060e190c1a0c030a 70
    0x5803441090182c40c000c0103a1040851800340c0741000946075100c4260f94108039600c0c98410640c4503400e011203c440000849515401303040807640749004103900038144490500c59800c907010154a66a00300c414600c24201950001510050214404caa084010b1010340030610300f882d0700d94680c1c3c1d01d412403d81100c00540d1200050211040d41000200d43c04010007005100e000c590380d0219a041c00380b040010188100600607080e10007040c822881c0041c8540001c113407400344220010050128441c50401900300b195104045501c0881c00740196003d80300c440340303880c0c142800200108402041c401c52043c4404603280083c5405140040c2c0f83d0090340d8103a111410000c01212864142d40710b184280d20002c4028074074a40b10f818104c00caa094104661104d0b030807101039070181710302d0724010001080b031000c100410240303a0002d0b0030306040d0300c207d03030300e041070034070798010100c1030306405804642c054108001034803140503815030b01c00d600d07034485060441c2031038030514580246c43c121000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 88125891 1250 88124641 88124653
    0x703030e06070827031c230307090f1203170604180303090b01360e0a05070e010b04031e0501061703310b0306040905030714160506030a1a12 62
    0x11a010110304090313806000c8000d000b8a20964050301410f0419820703d8050007403c884043d044001940c1e80441040907007561aa03074503200a0041202c4058062000015a2100d0115003240c0501440c040582c0c140c66512002213038134080d81c040503004140c60b5009403516210031114110345400c2a550348a501c0106c0c0d241e405180c041c8411405800040680041150104178000c2084000302c600d507981c040181ca48421044200240420000341c03895485240141410018001080c0b01140d4149458079040c0c0d032034511981c103910072440007034100e0701081503407445a641d903c440881d0912440000804541e500000ca1040c1c0100ca400101504049005003207001103062a000320143e000141e46004441c4003004114440347c0966001801c02000040403901c0366444202070780e420004603916a04140b504001c50111011414800d028540002c0d40311803c0c600710105035100180440d04640c0c0d140300e10740003801401281402602d6202400c1c2d00794540025411100c0c450a001d003034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 88127141 1250 88125891 88125937
    0x30804031a010e070c030305060d060507120f0b01050a050a02010605040906020306030c0f03120703031401080601180920060904060e0a0b010c1a251d040b030703030e060708 76
    0x4a649059101480c0c00082c0f00c00c0000269026888010203941030500154603220000482e4800d4240e0000401c407520f880e00340986203400070340d0501c1d800007001092007500c81c2000c802003034030304904295001c1b40040c04051b81e407038054405480e00b0509031000142d010b550b4000038083d601103480c151075403940001800414101840500c141590a5030f4002030b030b1502c82c1c003203039807224030402500c0e81d51804142e40d03041620a820010b483e003100001506c0305e5031100c0700715441c0d520a221307040c164030801110307000619140c01820303003a80d00181c40300e840c50058401e41d40c82c10720001c0f4856005204002e0300d030042e560361083c100a407100b144008203c0c6448071a140c101c4902ca4889410302107440c0f400d000003540c03900d444030340c4134004154170310a07102e100b50068880c2d0828100b0f100003130408030805015074440c43d0440c10b0b4400a40300d1551110a0082c002101c1c0d03260161901500070007400d00c0480d000e03555000103040301034061845d00740c00e41c80780d110641042c9c3c8201a00100300340112 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 88128391 1250 88127141 88127183
    0x50f060a050105090321070f05030a020d02060f0c070c0504050a06030b0703060e060f0a03140102030a1401120311030c01110c1002040f0303080a02090a0909140106080d140403080403 80
    0x380501400e080140c40c102c032400000307540b503280711520022194036207000709908445100362039041d940300f03401c0b41d66104d01e490241d4032a085486031100510a00028a4400d440060800d000303905c064410001c5440b440e11480c4650b201e03400965103910702a20025890711280f103040d1180c00d8036000001c0c81811450070340c0340c855020b03101c24109400c00e0010f106980c6c01420940e008402240d075082c0e01ca980001203014020164000741c09822840380114400406400440c0b1a111000301040030b40089414029440d0080c0945031040312054180317800a809009002d0100e00360701d00700d070704020302c1303000b01e500b034a10038040403a50780c0010456040300b010410011409500b215015400c2c9428040d007800b030103600707100c06800c0003485004a07000f5000d50f03040f141c5824016025a82c410307110550b00d80949034a0b2011941c194091000440b5140f042c441e0000351010203014003d1102180412a0076078111801000d284804200000010b107a80d00103000035441f40350380c02c1e80e15520030144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 88129497 1106 88128391 88128409
    0xc0b0417010606020318010302030703140907180605100c0c031505090606090609070f02150a05090d02030c0a150e0d050c120c070e06010c06050f06 65
    0xc940c8540310031114240d00c50010090004941c1d80b04103d0303503031040d480d03014450b018082c075031109076100f50000d54001c0030700c0c0f6003c00c5025100e182d03040b8102c015030300191203500900d0200320041080d016902c046d4000041000f03c10702d000c01141d5540100500a010801800d500c40704100200c1d216034065500b010002089644800320175005080956003a03100d441404006807552410718040780c85001c0203401e00e0225161402d0544560789050310301419030003a01c00a140810680c8130152141d0125100401c0d10f081500e425070510354040d0365102150009c0000502041c0c0020b1603042460380101c010f140440e12803881c1c0000c0000703003403028050041e500441703007040d449405410404c9522050f251502c10501c0001c40318814030036610155008201c042094414460b4042c0d404101030600424412041e40c48004950003160802003031800481030180c1400c0140c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 87949641 88129497 := by
  have h0 := BRFrame.cov_init 87949641
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87949641 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87949641 ≤ n) (h2 : n < 88129497) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
