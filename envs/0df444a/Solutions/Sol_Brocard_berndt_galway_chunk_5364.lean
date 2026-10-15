-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:37:40.577264+00:00
-- url     : https://prove2.me/submissions/3ca3c52a-d209-463e-9d21-9424cd23449a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964568345 ≤ n < 964748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964569595 1250 964568345 964568351
    0x6222106050a0603080d06060305072a02030c03032205040510060f0e04020f07020f0f0609040b120d11010606080610030216020303030112150912050a031e0507171009 73
    0x202c8024800410140e00080c045a000140840b050f40380ca420050840303c81b9502000140e5541004940d442c0e01070b0940d4a440b00e00100c454070807280108441822400101901c0380544440000392031a0300c101c2c2e40a0050300d03030683c10600303c0c0c046501080100b2050310188000d26080c120140c03040c4990041d00b09000d000010325030074920540c818068000050011583c0303507071951100c55550413091049101c0d40400184121505203200380310104080a01141d081c50700d0311040102a081803080c081d001148a00c15202080041007001040741309600c2d039000c072040e0210f14500b50b410030342201040c4843c18040c02501d8550f6041009400158540182c40b580380c040c91040c01821058040c3d4144000310000c120482d0304250600c8161082c029004181012400d180a603001c00310054100b079082265854020301480040070903050900d00041c090b2180c0589070041c00740c0005000c410340e41e4604101001d900f03d10014105640c00000f003800345440030030101c1007009030291010580d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964570845 1250 964569595 964569601
    0x1150e090a0c060806041d071a0906070305040620060f0c12160e0a082805010e010902090f060904080a03020c07080a030305060613031b050622210605 66
    0x282400700d002100d0380007114507202c0c0d81e03400b8000e0a070542a510700b48560300c0c4c620400c001418810743c002d8404003c40143c041e0b036103000c213503c10b0711003442004040b0000822091540d65a04801040c255104e911110f407142c2c2449402403806c030300440e01008809503601018518180001c029521420426611025170307600207960100f03000308007001da008034400f400e01c031000e0502c05416000031119030b582504001c080d02000700c91035540c82081c62540140c40c5d91300c2c4825000745802003029158800010300e070015540d035401c6a40120400e0f810381d41d100c20714011031416aa0036504a2541d1702da2480740e0500d4000074907600e1020700002c040b100b0024469450301c2c0039405484080c0c035014103503841781c1e40c3d8640301c0382c60341030b041ca007140001e151800107215071030f064040d90207550603071008101460441d91481c001c0d42c4106190000343d074001000081c155142d00c01440201e80108800e8a200c41c0061001d52180c07081e0001012180e61085147c4101c204030004800c482e007200002c640c5803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964572095 1250 964570845 964570861
    0x21e070327090f0b03010e0106051207060516080717041d041211010617100c090b0d200301170c011d0607020a120813121a070905060309010e070801150e 67
    0x404444405d1300341d42401040741d640c21065000e2412900d05950441031480b51181b407544461181c0200c101107501171000e07a81003084c42c0d00c1890150301c1042c10501e0000c031500d40c0c104104244181e061900360001d030600451403002c1540e81012408403422845050990341e0b443d0601c64040a80208980c0e214400c80c0300d8000d41000b402003080000100244040c000620b0701c1e03035a4404c405449500b81741030000304030310440c0400100c4204140b42c6091600b9804044041e00c0f400000c980c80307030800441007038a000c40400540c003c009102c8440640c14400d80c05031304108076119100c0c1440017480ca8003001c0e590301941d02c0140340033114150b6554400e8400124401d40540000c02003204c005404c0d420402c84400500c0b0100010403c00c4603203541c0d00100420342840c400003081d208650382c403404441c602c0b03000caa07000703521130503c094081d8a4001152447c0c00884810742169140d5540d20000c040922400c0c000d0001000244100c901c007100c1c5c001c41070a00d2040350144043d41001070661 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964573345 1250 964572095 964572101
    0x20d05180a15030608010e0601030c1512110415080c1602040905030301030614011a04030303020a0e150d06050102010902060f0901120e03090901150c080d021e070327090f 75
    0x5041c401c0759490b03000103103000c01070052103140503020f110f43c40c12072610340451000070740314104c0c5d0380300c00401c0d4020b04188003c0040d85014a20310b06014140304164000c10440c029856400d22441c140c44d15103190210400c184114540c401d0b06015440c001c1c4010031543c40b08030ba4551742c0480f50000d180d4020301c0407c00904e180721015020f400040004410024190824050380321403500e0741049903201c01c0c00341000c5910405280d01c10000b0003003000020700980103000740c08450700f000602165500040348070f2011300e8a0611740c110700090581d80034903042c442d00021782400c0c402081143c0309940858610321851101d5180300c1d001050000d1540e00c41d00d40200c02c2e100c140000e2088098420b1143c2c1d484c0c12401059110711421400030640124000e06484208829500c415084441d40c4405000d41d2000030140d01d003d03000c1000d1958500207070f96600d000d01800c8009565a01141401449202c034074884500040000b16001e1407901548940c00584520150014030050950790311001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964574595 1250 964573345 964573349
    0x170c0c061b040503030705070603060f150e1305040318210204092d050c0409031704061d150f06011710091a1513030f02032401090c020d05180a 63
    0x2045c4400075400003040b10101d5100c0445204d500c05010154681c0c5241102c000f40d8050050211000c0c40130500b60340c41003000254210700688244a900075145100007640c0003204c083e000f2a85584000600c0c1c1c0123112040014110300c011054101180c4420320b60b0440d5007240a0311550300c5844050600481650070304180700108101c500c1a13a40c0d050391a4041c0002c2d600341e40c1402420449401410980074990f40c556240c0c0e200d04060310b2000900c2a030a00c0a042910400c0c2d84030055000043d003661103002c0e001d0b50b0310003404041b40c0084200e45a0310002c01100040d20060188602c0e80d820091100d400b02008200d07144e00c1d030f9584410b401254540d408000b42c603007090a01e4450000c10407512a103440b0030365406251000c0c0e01041038940c1702e00b003941c4008100e900d108201291035194003611080c0300030240c034a05068880ea0107020700305140003004440002004110040385813040c0340e1044058005060140111000680a4000d0001848044c2c8125090031490754481c146500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964575845 1250 964574595 964574599
    0x3030c0218091f090b0705030a0905030d0f0617030318160b0912010b09060d05070905040317160f0e010309170c0d031509020a021c170c0c061b0405 65
    0x42a460701e030850307680d140140f102d40c4048400c20072a48a850403c1e0181d0080d054000b03082c900381d5101d01c01c0031106944000c010302500ca40e50004080011001c1c0010601d400341000089007c05903160540110380d030a52040c0c1050498000540d0220400710070341358402c02d103410f00304201d100c6000d82e0b0701340381044428210348200e0711070105000c00480c2c00380c801141d050b1101d00142c9500401c07075080310316224003e6800100080000d041c1d140c114688060305205509480d00c50f6501d02861042ea8030a0310110007041e80c42101c01105c1071140d0007590303c081c80030f0a0408418000300042c068143c010303200310400a02c0d070244038441c4d00a80040e0b01407644040d040800c003602039030740e4469410a8400a1041c0529a03119403528401d00540682c0c01c80f000541045a1900340100020b5100404060540c09103800140140c1d008912841d00000a5142e07844071b0f03062180c414410b440001c00c3c14400310320030700c403d40e041040028510b0b480b04121811940200100c2c8081c007035030003a0ba000503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964577095 1250 964575845 964575889
    0x5090a0e071a040e150f1e0409080903012f09040612200f130902030a0f1a060103053904060e09161205060f040e030702120601050a03030c02 62
    0x10b031400300844000c0c030884a1a9040511503140c0d559844a00341c506080258020007000d403541d01481e240451100f1103005400f25520080c1060116040e03805484c81a2021500480d42d10078609007030258809100c00c07101d9039416031002c0043d0096000c0229201101201c01103150301140e00da03580000007404890020b852081d03c2450b040849029020341d4510f0380d400e0112003a0b0034184450141d1440c50014110003500c0d401a0501c001440304c3d58040e40e05104800010300421820200350070002d0044a0488081030344a06446503003c02910040c1094541410010103c400228418030008088020301920940184001c400381401c00c401c01c0c034190020b400038101e900090b4450b2164801d4074620200d544200102d015544000c0c901030101c1d14442c60f55034070820355408698490401055071b80600100340100e001c4542c581c18805050b0700006000b4294036100811800007030245006106541c141404625140b071107100090500800301d58050456035001c0c01081021303d440740c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964578345 1250 964577095 964577129
    0x807030314070c0e1f0b07261c060b04030816140319080105060c0627100e100b0a051212070b18030408060c0c03091e040e01050105090a0e07 62
    0x54015074030180d864060120b82d02400c010690200b2403003000300d581c1002d00b2410556503442d00e21403080050203035070701c00c1c1c0e48c0d020420070b40c0002409015104405803900038103500ca900880c0856119801590010340c1c14042000015144011a418040d1025210380b0b41d00075841c0c5040868440b0f83d400c1e100e80000f04041d82d034070b0050b20380d050b29423980c0c0d566404146d0703903074041c802c13103200700d0b1041110b0380c0102000610a010700100c60450000464074080c61400007910541010207940090381559144e1301190414041002051480b902c07540c0700f0040005044001242500304ac407403140200511615102d14640034060380200780710300d40c403245d44c50f0624500340170250790441d000c1000e00b90f8282501c8412000209403815038129a0041001f6243c2c250200307802d820400707414049100820012000e07494030284001c041c541c44c200118130264000411058a060704017602081e8074200041106030b840212098101251142c00134200e240395074203508181880d08480c400710b81c1d500350 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964579595 1250 964578345 964578359
    0xd081207080603240f040f08040f06030e06060d020f0f040603050a170304051b06090d03031407050a020709020f070c080705010318020108040209060301150f1401090807030314070c 79
    0x240b0402044041d01e205108000c01142100c0e1080254800307032240a0000e02d07070358855125240c100d8000c840e2130001c00c1c800e1346d506000354015001100c8280c0604002c12016805004500004590001078016480c080010034800040c4010291080b01d00080078019a215010f4107400345102030014000c60313407203081c00d0b540c50011075000c489a40d20003e501c5086415031040d64003a55200025040c82594000c8029a800040d5010765104008101c004003030365403025896070852090b140898100342078064a148507000030098030600c6410000c1b5110141d0104240c07066560221005850780c145240714105400ba1500090421980c140c0200300f284c400249502210001da81c103000c200d01c5040711011039818110300074046042c01007c00d006143c007907442d590010340035000058101c26040700c10360610840c0c0c000c0a02c0d84100c98244070120414810100254082c00c2240c6214134040005944e401d40c0d1002804016440d01d400c1448000242190400c41d048540311350b0351900d4086c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964580845 1250 964579595 964579607
    0xe030307081905040303050d09111f182718150c0c0b0f0910061202010e06030c1605010e060a1e0b01050a030c0315030f0210020c030703020d081207 65
    0x251165000082c80d50070201103110340102e40580c0c0d85960f8131403d00c041d10034002c2c090003001d0130840d46042c10805201054440030104c1e6003180d84002012a0105080e00203007403a00341e9803403400030703201d01103041c091209018600607030b14410301082c0c915100c010070010020811100b00191a0b1580c0c2000001c2c440045074895907503504a104001c4200074a03800c1d5400c0d40c0c40ba100230480441d003000104c25080d0520450351103104007094940781865907011301e045409540004256111142c010419960310100d00100d00f08240c42d618514245041c4800490150402e2039910581e800d003828200013080d0000004621084219009420300311815405000100c003d40084070403080d961125200c1401207280800041e101c661900f00400390880160940d20080b009143d190441059003064000d0000000c60082403009802d80081c8100448040201100700455005c4d9101c0c2c2c4543d43c01150460132130f40e04480c07181c01415146172401c0103006116814070032021304001c0101c1950490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964582095 1250 964580845 964580857
    0xf0306030b0c2113020103020306191e090b240f0d021b0d0905090604200c06070807080f2d0105011e0801090f0e060705070515060907030c0e03030708 66
    0x885600c26030094a2140f00b49404444246500605800704c8001d54003075402950081405000504440f80820031841007001e141d2003d03082200341480c0002e0a486000311101400c841c0105010010803c40090f040d002e1800f004101540106403030003907a155001121005100c0148294035100c1d2101c03810300a4124038003085001030401c00311a808403001c07601e00841c2c0340d6a00c030000d40313074100f0341444408000201b182d40c20641d10031443c403c2c04041c0340c100300a01d079442209d55a850711030341c000d402c02070301070302c5001407100880c14800065045284240e100c44100c80b190740d41c0e902c1c0d22014101c82018060b00e9000c2d00d200821542802102c0038403416664207885290f4002c035000a08403007540701c0d5940c0d00000e4068401823240d80b04035044070120840344180400d49810907000e40d410b02c442541c0090104000003803070b03030030804203101c09044001c020080391018030b8604003081c11420020078000806035200000080c40d80580941904910090100d035140ca030706290001c140d0303101c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964583345 1250 964582095 964582117
    0x1521010e0609010815101a0d060e0f040f051e01050411032419020c0d180f0b091201061502060921131e03060e0c100f0306030b0c 57
    0xa40009605070825220440c101c130300800040c00013030303a150701c0200b00d2a8058a69140c01c04040000038500050132080d54018081d005001d58454408000c40220b9080342d000400c0801c28408005205240c10681c035442034000c140d9009e07840036454001c0c141140c005821000d0810301950b180f10080540c006c1d4401d9100b03592640d04490381c07400301903031290f150300703050700a0308070000f0401645401e1015640100030124500181c1c0c0c0140c00d50001c1e0f030088680341c041588880b0903048941c1d4000304d00c0e00300e8031500d03405004040c00c05003154108003041c064004c91010000741c01c416910341881c04d00782c8226460082141c20b071108881e586818014019000612900c00420140d01e8049450001c100ca142500654200500d500459a8008510725124003103d11000102e288e8510340d408040901c1241e104500c505528000080329403a01010319254000b00840000307071aa4001066081c010707041003a5200780320f0380118068041c0e03420040880d010741d420700c00c070f020800020388806424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964584595 1250 964583345 964583369
    0x1060803270a0b271c030c050f030a0f0302180f010c1703011a090307210b15010f0518040e030702121b10140706020415021605030c0609152101 63
    0x4010f68101001c0100713800c0642c0f10004c064192200100203892410b0144242003104031031410b0788406080c65000110520396800c005a0140e0895101c1c2051400303041c1c41c1006c40c10418000c101d043d8818414498078010b0400c03040d02207143c7c0c0508152208a82c0c0044154090718150820312556002880b540400c14074444101c400250729005485c40c014015000302480707840d08550750040351035240c6501141801d80e041c040030600c0354100c103208000c8449542e80c03110b6803800042180705582e08a10400005101c00341c800280a103a4005501d811900031035080480c0102a085100700d02c0000d40c0503034500d90041d03034044089400504040c14030b040040f0030020b901030124010b2458803010000c0d941c07100e02000b084c011405880e10034054080142001e448250100d100d0b061542454007690000da000100c4c811880c1140707001c0c0000303401030075000035958041a0703030b80940350241c0e00c200820f6100b0f40b01611090b003640c284c115046240051307a10882610614810280110346005003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964585845 1250 964584595 964584637
    0x8130821010b0f07020609011107060207080618060a0e01060f030c0509010e040c030b0403020a170d150621321605031f0305030c07080f01060803270a0b 67
    0x482c000035a0110b500e042d103075902c1c2020580c208181580300e50916418090b07805051600034004200c1b64001c2c000c0d540083c02d50504058049180c218000c04203034581c5a80d601e44c03104003002088481c0c2101c0030840105800d00d00d03a01d07441c0508900e402c1010384000c1c10f84004144090707e0400780441e4015214600309036252508142030b80400c5030081d1010a00340710400001d00d80c60750780355010b4064415110314103010b030b4500c404a45440842c40703071054045030031540050b99100d4000d040d903809071901c0d121761524801402600c0e28401ea642c8112902c44200c5c40b40450380c100c4103d041e40281c0705d0f5140504515400b950200401001d2a80c4100c000000c45800061618440002442d2111405e40e51800050941e5245085840b00120404200040018010809040046041c50141c00310718200240309140111529203c0080c0c0c0c1490320030044180040211592801510341c04648094074882c1e142d0f07240181301d100c075000040180000340ca2031002c0e02400b4100c40072240c21900c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964587095 1250 964585845 964585859
    0x60307030b131404081e0f03150108160e04020408030c2121060f030106030605070224070c05120a0203040504060938041b0e0d030c030813082101 64
    0x2407040100d00380f0350290140070030b01180c07804002d00305000840e241094410b480340c100b580660800c40030080e0981000c81808800d02c0900c0e140c040614080c6080d0f015071904884817001c00740a00889014812410055070f02d9480b603804403000b510650080b20303502d100444225a0350110001c04403900010140102a25480ca00440748030f0600480341007e6110310840c58440e40b02c010748030561102c075882c20403885840078015513004600074000010a031070708002c080d0038180041c40a0748100110341061601d000b03004c00c8107810100c545030215450003503250107440c10074440040d030403100000c1080305d01c0b43d5000000300107884041c6c4e010304c069176440e90900d090324812141c68900001c01e04c8458601625103810401d40a101442c0182541c1000007250464110300c03a4050190300c101c9034012401d80001e250b00450070140c0318025607010b692402020001208402400c115150002c5188490340c188210255500b1603201c0c0d50b1a0749621501e01d2250700100031154940000000080794 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964588345 1250 964587095 964587101
    0x30b15090c090103020310080d09030212030a020a0b100e040f1203110901120b10030621050a140705300606060f2d0403060621030c020a05060307030b13 67
    0x6101e0140558146152400154013035000102140c4545542040004490908001c0110425140e40740e9000007401d6005100015281a040c000715030700030030407081b00c0d0303900140a030800c80d000300c0c804c6070b44c0e1211416009161081d0340214080745030002808144000d5103c1c54812038400c036905810204c042d0001e50542d008203040c0c28041030300b8030003104154004c02e90101041601440003070703010300380d1001a0102d8601d44440000941c0e900702444000380000041e94599650502d40d03808101590b1125a55407005500402850b480d0070b04881003107080000b040500001001c2071140d00d5284440c5011040200c2d950a41c55070742d03880c0a16031003000c11158080c5c50050085440c000702d02c0c1c9010a15809450564001510300d09100b1810540f20240d21804600d042c2c0c1c0b56465203142420401e6440c1c1d90007003101c04800d030010328a50780e40a04a207008580c5820710714048051760000030010071a55004a80140b0008100808190305034846000e440d01180d891001d0407220a0840032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964589595 1250 964588345 964588351
    0xc0102070f030308060409240614031e0a060c030c02150402010504060309050309040906150b2d090306100512070509072012070c0504090534030b1509 66
    0x84441c410080c008240f142c00d4503070740040040e2003ca010685581d501d848098460240c004115481c19640000c41940c003c0701c0007042e0b1015000c0100f100d840000b0748600a0000221701c8105882d803202c001c00d01400580ea2040d00304008009008100c84041e0280840c10103000041c020652814907030140a6485802207406a681030b04060a20b0003c0e030040c1040b14040d90503200500c00010f03107540c5e0340103610b0504d01c1001d011400d2400040c45085024054001d010803803400d006031f00d040d81c441541050011048182101c450140789039084161140c01c44850b0180510800c101802c52904000c41c212481500d1030700caa074140e61780f00c545414640c01071950040d100800b15454510540f58040c0754a200750040781d0543d14102041d11700380c40b4411700d0030085004103102082c881d002c90000001c180c00d443c01c1c07017086425551140c41c5c560040350a250086801303090300c0d6985591036101c5441c0c20348880c0301c0d681616824001d01c0d0305002c0f20b05c2002001000007180481c1000500701c0c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964590845 1250 964589595 964589609
    0x918010213090f0e0d0e01020f06090c040c170c0d09062a050f0d0207020a0b03010303030905070e190504150e1b04090807030807050f12060109060228020f0414090c010207 75
    0x30381c5c038043c500303c484000003c107445c11407080c256003074030b00c0d0804d004103409800240001c01701c55911905100c260345c08030050000780701106822903a410246220168001140c04485030380d9403180320001c004003906203025044502d00040d2154100341d01e140501c50340c060103410001d54a952400312014401c503d01c0040c0c0250038003240010340e4075074019246540c0300406520050b600c42c0d035040c038260426403040e00003d803a40c80340e20600000348900d0004e03091040041c00301e0b14100c401d8403030000720442040402980c41c000141802104158030480e41d80c819414030018901c0104541c6c1d4100c403c0c409003149c80ea00c1c03110021850f182c41081001580074114508013020303034400b9296a000100000d044c414100903005100103000f00038203140090b40481409400d02c4000108069a107800c440e003958403040503241110426810b0003ca07009150001d100c501151011400801401095581042c20803228400c9881c05c90031541c4100003032421144114804801203076a41454442c2c62 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964592095 1250 964590845 964590853
    0x310022b0b0d06110c030c0a1208041a071e0512090307020904080a050c0a1518020303030117070312090e0708060904030e010302190e0f0a0807050918010213090f0e 72
    0x80018125130490000411500d1216081420080e403645c103650084c40425666040000c80d0000c10400307141e03040c240140d901c0e00006901d09659840d800c10302412104002020b11000512820710940700b0030004076006111041080705604061f206800c00d01c80c040c1c419800e500090740c20300c0000141d480791a00140468615200c98072980004d87c410009501004020403040e80700346003c0020750398051195030a2401041c0b00200401243c0c103000c0c0701c0e03119007000d0310100c0c0035a40001c10340341582d0f604000035840c0001c80d00c0c068030300a81a4402404807841805c40046a03400844983c1107030907400000c135455988000880e0351280c100d506591100032403011401191240100c01540c02c4181030052811035417980c910308141d040303541240003544a051401003400c00c991803030300358441911811840b905080c103480d1200d100d4040c090041c0704c40000140048641d410000200c510170307000310764507199241d0156480d0190300a211455040100302c000d00c0c1c605101e09004004488050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964593345 1250 964592095 964592119
    0x1180e070306090203030c0109030e040e062403190b0702010507050a020d030c050d050a051012050309191706150f180a0f111c090c03110310022b0b 65
    0x5500100311903c0180d1301880141300e030b6118804244174900645009848425411249000700030680302c0d038040c40607454000070248140c41407034501032402001c07403c034403608030300c0c1880c0402c1c50300080c09010040e80d41c01c9031a18080c407040020450254146900034002995051001e69203031240160010040c0d100d84076031081e16109034443c5480d1406842c11601d0011010f102c1c1007078030819641031200c070ba5214207001c64000b00f41715003c01483c3e030100000035203090380c43c3c880c0c49004101c1c441c2d009507485010480c40c032032802c4035000540740348842100a8800701014070f43d12902221803603540b01c0111031f404428a031001c2038a4038400002d000359446090700401050031580541442c042075140c080704c0c0d41d82d80c00c6000c1c0f0208002d00071109621480702d01c401001c0c070003120841c8403400c6d1a046084002c1044c01d002c4805403500080b0000200c1080d402080ca05000c5000700c11009101184e40960030401c215501c070301c650a07003007800086400d044140c00f1607489003010340e07000c050440d01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964594595 1250 964593345 964593353
    0x1504020607080f040b0a020f0c030601051c020d080c0706030c050310150306051003020d0609051003140f030304210918091401061409010b03010f0e0901020d090b01180e0703 76
    0x10883c14640b4801c0130308081da2060b0080d21504400c0352a0007680000390118140c210400c025144000c0c21001011607500d010045503079030340b4840000104410f00700902c011f40d180c0100882509a2240f10b082e80d40e0060400c4035102ca902c0c0c020701e40041e0500021120140c450707400c3e280650000d0300c08088103440c0260b095245814000d660050640b2200c1c00a00c60b614040540d541c0c0900c2d17100036035030300410340420381200c0035504940720681ca0103041c000042540010b000540e03621918199a0b50341030b80d6014a40750b01101504210b20000080104000114105442c85502e1000e850350380b8201850071345180040c0e00a5044080085042c4a140001354100d0140e03503002b81d601e540c100e2221600142500c1094019900300c1201c111200403030300305500e5090041000102003801c5504081070b480059940e48103221942d04081c0101d80519004c0d81102c0f62940b0500013003101b103100341362580079464240301d8404500343c0300c4e00d103801d110668095049400102e01c09410b1090070341c1c0d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964595845 1250 964594595 964594597
    0x303060d060e060a1a030f03040e130c0b0a1407350f030105010e01170402010c060f0f09030e060a0c120201060b031810110a3905150402060708 63
    0x40c0035115a0789a1000c54980903081c0031203402030082c80c1021400d00700b46000054880802d01c0c0ca1030003940103501c1c03503686090210580d0251403802000d59140c0c2c4034080a5042e80409210191045185c05d10000d145c819800081081c220305131142126001001e000e2015130080e101c000c0e24041c1000e9444039990a84246200003a00700d85402003214520040c0303003126048a04021000c2600000601c40d07580c2100c92903840f10000d00e4800320400b80440c6000654202900c000d041c48060b04104080001a400605071072180420403c0301e40d405000910281055180c1940130174030803030030f401c0300d82032100868235262013545406103400050758500c0102032401c12418115540e480010810292250045005d109803040e00d035145203482139a91d0608240da0200e440341850407002d00c035400fa07002d0a40c2e00e10385007414045e00012895118540306e101c1c1c4c4610b408030680c140c50450143c11609e503035180e0036002d00112a92403401080d24000480f0550340a980b01e2410700c54140011603240c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964597095 1250 964595845 964595869
    0x5070c11011214010e01080307051005070e13020a180f06080613050f10270b0409050d05250305120c0c01050705210705090609040605031e0f0a05030306 67
    0x3151480c454a0120341620440f0a41c0505142c640c0595004002e1301089540303490150080c3d10107107241020540d09e05944804106850b04110746940c000340340309000d08844401d5020140038030b41030319001f42c9400300945c000100d60010410504004845050002901081c0d80c14030200e046520705050081e108003100600b100d070302c100310b42c01c203400382e40e034030300a0b035001e6141030309000c40c2400e007548203003503511844d00310715040780707080c15103075031180708500702e071030b0600d251000007601800d070700c0206000e45610000500700e0f20481c3d50700000741e54000010074680750b2171110001441c0d00300c40546499801c088002d00040c0b014009806e95180b54074400e41c21920f074041d03403440c1c9035800c145907080d203600b110403901040d0b021a0207400c3d00101c0c2c01081c0d03141c1d1861000c801c20f1802207c0a0b00d0b5020f1140e00500461010945a0b81c1f03403078036484003010b0700c0300034103c0d86045d455a00c01c440032140580100c3c1a0700500ca2140c4d11002c0c00640014a80d074060051400d51343d400e414001c403242c0031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964598345 1250 964597095 964597097
    0x120e030403021305041202030909011202030a0609050d0f05042d150e130c080c030c0403080417010606020a050a0807110d060902190608010e090c130207051005070c1101 74
    0x20040000140d803803c521034404104801c001c6410f242c1400c101881c20801070040055400820010f040c680d6421040740c15070304405e80d0405021058000f0904c2d21501c034000800c3d0511b010107c10902c9800916009030800c81d0b90f5010413251010400c45050250744140c1c0010b02e04c116882003144458014480d20001c60345280d80070075620645040000100c0e41c68002140046001c0390311400d0894100d06007520700d00040c8000756000d003004113407500051020690800202c0881c1c0c0082248003118011a0400075251f2221f0b01d4641000b82004033f004142e45541c41c3c0b14001911600200d0641c40f4140c100d00640350030b04150719080c0e555881281304541c0305018030156100c5658414a2070741044c094800040c002180d4410b001c502c01781e0009422001402c21410050507034004141360655140030040c000a40310464182d28201b1420700055010300352122040340b81d002503010f040064054012900c00c07801001440080720b0064a040d4001440c8401c401301140d14604000c101d2881 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964599595 1250 964598345 964598347
    0x1050703050d02030a180605190207081b1c0324180902011803110f1203040515210a050a020901052a160504050906011412010603020a060305070305070f120e03 70
    0x5048410b40304005101100d181d5940e07002c4c00b0040205007240c0c083c104542202b1031030800c031a103c0011a0052855a0340003d814040c0d81c10402c2040c450896003000d0149039070000043e5000280c00341007030801c1c0c25442600d41291050312034000c0c00c0641241c8920710140d120091204502001d400d24031400c3c3d061000e800b18541115002c114004001c2d802036841c940d075040c690742001041c0343c000c000103100391580c924140c1c1100c8040300300d82c111034040b1f072804894000c840181e4050300440010160540301014410001030700d00c0030b100d04c10750307082c401007205940310780c404001c03405420f405070b001880910054000c05030050b0300c21032821071420f403070401d281b2102516181c1b04500c1e00e01606580c0f030190070012401e00780540c5403c51070081c00783c1221340c1810903a04817a079145030307403c0c4104001d80d00ca800d12102944184055034003c0c041c0c50301c5585880b00500075010507902400000d10301000244d003a44684038800d0740e00510b64a156800890101c07400180140802d8140c2c2408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964600845 1250 964599595 964599611
    0x30f0d0e1014030c031f0506040918060e06061504080c0d1b080d02012a03020f040e0103060c120b010206040b10080f07050f0108070507170f030a06050f01050703050d02030a 76
    0x40b200a58440c01c0c0300c5103420b40e80e1400201020150600b18082e11500c0603100d4103005660b2118156400d580b00d0100000d52541c840083c00e4030f041e5944406400703945480b100070a240000b0400c00d204240648010010348a46504d4402034406d52140840903085004102d0745c915003c0c8000000034000c030501006284443e080400075000c41e480940380b9400141c0700745d802d5030280600440c00089000007800e440341e4000748184554403800c40400c05600103003500c0074111080a0714060420b5111103001903840c1d207044401440301c4e41046000c900020b0060a44400501074006a6041030f4064021502c0ba40d651440007003015000b000170a040711030204e0883d40400a4030580d03100d5100500c10385261109210706410401c1010781006958001c0200150f008070881e00c1032984541c0892000c28106401c420034042c500048000e0840001840403150254001d001510011226120072102040054417607101d41c0c40002c000c20028400742046542950144d83d000d03800b00001f1420034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964602095 1250 964600845 964600877
    0xa180209010e10021b0a1d0907080a1217040f11010e0d05030409060b2b090c030f0204050105040e0a060203090a0512071103010204030c0512010f06080a02030f0d0e10 73
    0x92103c00d40107005902c40d4071a00c1442c5040d4002e11425902580c0c1c0ca85080d003041000038030720644c0d1128002d80c1d070b0000c0103d0030603501048031000610051094416444591503e40c55040d0020748000001308800d10242c0000c17002d00085001d60380c0180c40d1561120107549500750307403902103011414003035881c0c054030b0951100c45413200800d214201440d0b0321400c141101003115074a030010060110240148400154402124412406050b4079140c0200301c901d4150042c0c00209001003a0380c1c0603a0000007008901c45c417094406100303c030103100b241e89803400d10088601464407114607502281090020512030b81c015904021103038203031402450309841e03140c40d0a2800001c031401c401b0020f00003003400b400d20300d00c1d2103401c03044000b5480c251a54440142920b2180240751244140442c0c070b5100c00d500758072401c1071000c0311030107122072035903030070350a4031000b00b00d400342d0103030152105210807001d002c285455a010700e52902d840506004040c00310525090f81d150040c000c0440c1940d00d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964603345 1250 964602095 964602109
    0x1c02120115091b021e030d0204090204060f020609030406050d15121406070e0907170711010e010203101203051608031806060108070f020a02060d1a0a180209010e 71
    0x79506100c06180641e251815034411035890040040b050540a08000741c000d601003080c0e0580084c41c1c0c00d0642d0025034040141c00c510075a510401018400100004d41100b150003500c11a0717901d841d440341d01803c02c0d50684e00c800088a2007000f07504100818450705000394043c244c040032441c0c00040032401400441200102600148402c1c0c020300305400c200f103c0c0c2804c0c10482c4482d6006014242400721000d0b040100750405207226030303401030014580b54401d04072042d50144840702c50b1200d0070a40c00c0039103080f02c0d05800c10083e500701006514101814000c690007040d41d10a41c017202490401c00148910868008504121042081a50010703810385000002030207a80115501d04003054007240361008409802c0e003d0701701c6810003405a0300015059880001810003030940841c03880202d00b04003602100940c00079001c500c0c2540c459981e40010240d42408070455035110907202003007403400b86440f40b00406d9189a4120703034824050340262441141c103050011100803100c0000303400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964604595 1250 964603345 964603361
    0x111030c15072a0b10180c030b100f0210021201170f0a1119030b0703091b0b0705010b040207020307030311031c09060b060c0a1b030b0106091509051c021201 69
    0x30f40240b000416052103840b0100c0c40d004006000401c2c4484c0c5012082c640e0309141071003560440780c0e904040c901c4507002e50884150382000400f8015201d00d2403902030880c001104020005122f000750190080c400c5108a5542c541100f00c4a600c0e0303840c01c6010310020712114181100341c01385240d1104e1000c03081080742030032482042c48540c0c0207245014008400203101810102e03903042c040c2080031440000c1d41e182c100f00d552401007840001c030708000c0844d2107007501040b01e882c1400320004401420b54050012144608000d002101d42e040c100001d0740a05400694540c2020b041040028040d00b00541ca1001180c1641c0c2059004654511499500d5170180b400b0380e1142041000c1007120f200321a030f1284205c40c1907041816620440c0e6680880c2d240c002e1452082c005288030342d000a84403600155480b1914045640e190b11004004020714400c08113610540700103402440e001d80714080c241d07071000e0400403901b1403001004418440c5d246040e41c020000c030300c1d40b0101d00001e000e002c50b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964605845 1250 964604595 964604657
    0x609060b04090c08041104021303020a080d020106080c0120010e0102030403030207020f01210207030c050604030207030c0b16150b030f070f120809040506120a0b060111030c1507 78
    0x7458510b040d40d6a020342d003940c20741e0350030030445104020004a66120041400342d05440050302c1e50960b07010789282646a80010b58060280c0d50006100170340024101c3c40740f05150700a008641c0e0f1260300d565030f40c003941d41d90f5011501c04e0081d2041c21040c01c100790007110080001098040043c00b019007241c1c020f4509400003500061580158280031689500a0ba0207181440d04104800401c007240c10801c100300910907000201002450710901c0c85d80b12864010003a2011810130340340207540c03025980f100701c0d2890300445000400340c260400380d541006051050b18940d07c55607468041004250261415190703036071080f00200e0706e080101200d003505080052180c0e5081400172103100e0f111380d02c00c0c9058000304400302d0020321030070203a5004036025a0041071070f80716a40028202080f096629410b0720030312030107070180f0140000e06070243e0300c03e807510f240081e80120929101e11843c60010066400301d518482203004441086078461054608444100050620000740c1181541c02403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964607095 1250 964605845 964605847
    0x81b0a1202070f081c1103040504060e040519050309060d11030a050f0c090a1809140604031403070507020f061909050f040c080708102714060d0b0405010609060b 71
    0x700415207660f9001c0c0c0a051000020088038414000c2150f804141c080950100a041c8045896102d0304000740d9009d45030041c010f004603515a02040d0707405008641c26910f900ca0421a12440d4810350b0301107464030342040146141c0b40002e01404819484013241e010504c0d0b0340c00389465071380100320107140151100398001c202820030034060704036404050410b4000c04000c00c13041c0e48554400402c4c908031000950f02d903081c00020b140c0c010080c881c0e4070f800340c98864030b002000800031011510a116034071076141c1054406100e203d240180c00111554000b00314100040400362600c040d032040700c218002c001520b8054403650340742c00300c1d102d207100c032001c15030300f440c2440300346400c01c0410800b038070070b0f40c04011528103000010200e072400340c01070342071005010206441d0102c2c9280301014001410300031111074590300110020701c1c550031010000502c0c203c0f41800d004840c9071141d0045d44020b000440c905d08a8490200984003c1c6c01100c1d590b59800d0b0015020384070303002d0310004200c0b01000c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964608345 1250 964607095 964607099
    0x708070801050916120e0109050a2f040504150c020c01030e1203191514010e12281a070219050d030504050c0901080c01110a081b0a120207 61
    0x6480309806800191207440701038100b1014644454080071007030410b1402880c20111a01d19100030f1150301701c4042254217003580d160070320000003030a10095108000301c42000d215a0740c28500725201d40301c070004180200a040b0050710307268110540044c040c0c1d450340c11041051649900301c0d0a080030702d20150b00300c40810b03862903070548036040c00d142c85100644507413001614440410b1000a082e10111071441d0000203826402c1d40c8203100013820ba0b0003400c81d80391550400c1d1245141c40000c1070004e2903a00c0c404000e03040104410240002d0030700140842c600620808680c5070803880341290a514000310034003c140307802072060b03043c4104105c6565508100320000e04200710009150001054110308800044000442100c0321466150010300c0f81c80d2071803ca809c2c0940c81403010342c056450b1001144180d000300e01d1030f1500b142602d0721145a20100f174400d40712010000060501403040c4403c02d101045400c03440011868441035408416565407030f80400b01c106007806005074416401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964609595 1250 964608345 964608347
    0x121810090311120913021b030403080706060501050c070605090607021c061404050a0f080f0714060a090b0103201009030b07090806161416020a050d03080a090c0e070807 74
    0xc3c0381003010245000c00c0c0f6010301d050214401900c1035224000c3d00d03a0004000005440d0070010808130798001041d00d07522543da05010886e9000068180c0d0441e20b030800c0043d0540c06102180c4030708818a0281c0034203840e000091300c664110b02c1a10341c0141d41041440010f80d104040400b104001300070b04e25400a46040c80f00071160511700d00c0c0d907405941414040440c41c0020941445d650043c40e4411203d054a06800f26002c0c1d18100070780030501107220710401c2541f003010400341c403108040358610303a1281116070a071001e0001c0501042c10b0100148003041e881d0714407118859020b1038900f00f01a44201180d55611041c10303c6000408240080c410811100c1d86180c00c82401d1900d419002c4c240040e040c0c0302d10010300345480400c480b5001200090040826100110800c1e1145440c0d405900034110200e0065000b288519041c8001003610314009410788440d64241d51b41c0d001c1943c407085210300030040250203070741017810040c0002d00301d512001c40034400d01ca036a41e0070060781802d1f08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964610845 1250 964609595 964609603
    0xe010506010e061e0706021809071b140708250605030f160e0a09060609090e06010e15030604240b0105030a180f050a0512121810090311 60
    0x111504006030510507040c10ba4955003601c0e420001e00a40c11800f41c4c41119000452140020090020f4000704150024009009109031102e1b015141c10344a80d0b9540021030301441c006541b081d1030090703031031800040b0ba1401400303071600c0e80e45004c81d50300e1929240e04070b180c181841d8030a0380240a203050034028141925200c80145240d0030301c00d01b5801d151100c1940324000514045039400e0703041c420b11070f00b403103000d4100800d040904040d10468030303030306540b000e40101d0050704080b032003a01c0c0010351110306115220204034450068035069007400102140c080014094084516040007440c1d22540c040c0401401a440390010842444104140305488d51079480301440262801e04032034181c0e40c00000316680589514000100c12044003c125a968032084014051480c01c0306183c0400c900040c3d8540301c00d004004a86c5c2800d80c254030f8189520555001c60807100d050b0022031183d0881490010a4461410644103104e00740050314084824800701540002c0380c415015000c000140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964612095 1250 964610845 964610851
    0x215150d1a190209060a0813170406030b0f0a0e0c0d06061206140306041203140a020c060906010f0b16081215011b020d0206090d1a06010c1122020c010e0105 69
    0xc1001d5092007258130005545002da2140ca6091122000018a4407011141611171859110713600034402c80d2002a402401c1e08240a0b6001203464040081d5031450010300034991000000c20082c0564204811500e5480003e07100000c001c0c0306220309021154030780070b4a000b60000d80c0d11f021039103002c11840350036140560300208150000c858000c842c2d8802099699006070031844620445481640460042500c400c42c45958170f21507051203c0018260001d2003954001411103101c3c1c4c032780e80c0349643c4941c020310550005400d4000c0c100144441c00c03003d07000b03806840d0709940c80e10000b5120101c980e0310440a840d075450f211001c02c042103000340e040407840b410a10380300c48e0440c680005903e0150080350003a1040d114002c0c4041150f070381d1002c990b1010b82c09042c0d000c0e10380301c0c1e2900440311001c440c6118083c81d22a400200ca0b0351003804c007034041503004140366800d0080c0d1414019440107a90000645c054070070b60705006400d041c001042603d000c0800000d5003002c070003200c1d08580001e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964613345 1250 964612095 964612141
    0x904060f06050132160c0503060f0903160302032107140f160609140706081b0909060f12030406022515020a050106060e040c0215150d1a 60
    0x2040d15030032010850054008459504d088207080c14401500c0049078020200b050902e0801221084100310f005002c0b1001c48806030115a800d45440c0907881c0004002c0782c8807415984140860048032030400f80c03400b0140c0c081c0c0192803500443d004c07103081519000680c00858560706042c0805940d0245010150410400c001414805c0b8003110045500c51b42c013900e44881103044404d414003070603501229109030f0203600810361003c1c40340301545981491040c98041184400000c9041d0101d918440002e51020302ca646882508004c11201410203071200313410410101d100f00d42600e03100d0403942142201e000440e1590b2401c14000d14212100440b22a0084446145070400c900600120b00359003083c10031003003032850400100d03e49166920050302d00e40c00d120000468030b41100c00ca031841c103800d8a05100320826008181d030740c2e216108041240c0d07440200010710508040c0d112042c0030740014000b10a00005840d5031070400ca800e10307007841c0380c1f1a400034009543d44a1107014425214 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964614595 1250 964613345 964613357
    0xa030b1e0405030a1404181b09060e0913050a06060816050d141002130f05010806100e03010603060929040519060f021803060703060e0a02180904060f060501 69
    0x55a511a1613000d106070f00ba081c0802d0b8941620081d62040a03100a0300c0c20440d24070400d00381798840d41c090105840d00c103125415054201141c02e01c620888800e45000340c0303c4049035602c83c1c0c00c1c8042e003c0010025004040c400b1501c00004000b4405c0300980f07030081034041821420907400300d040080f00c0017054010341d0030030000c225903203841070a055440d401c02c5504041c9540c007010340342403019520308964880d1002540e03503004554103201c14140c9440c0341c08207150740e032120300540b0904820307030f5442d130700c108070300e15445142d84682c103400400c3e00c000d400442d44070350741d079541c00598403803040031039403da00c0d40d544203031020700342501c1081c0381d0b4110709505940c20030713860b07880d120b05545130000c0e07444071a941880e041c440c15410120340041c1d00d0b10708540c0ca0035014038402010340c401d050b003407003801400e01245045d80300740207070f81c00d60311000881c104c15150000c1d140300a5115081c47c141c0d140d04406030301c5040d900e07500158812800b40300007044804551158000302e4095402c26414085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964615845 1250 964614595 964614601
    0x3101a0a03082502280f0509130501150f0e01060c0308060405100810050609250e0315070c020117190e010b09011706061005090609010c14010207140607141303020a030b1e 75
    0xf5072140107030703040142741d620810702180604115003d84001c58081e50040010b000c005000550078400104407204000c0d00240f698035a50129050199003c010340068501e8010400b1403402d903101c1038100d0440030321518001d03924001c1508001001c00c0d00021295184100a05070600131441c4d50b100c000d20308841481d0700d690b56200c005d58108c00b00801041428039034640c0c56102000301c0d861a100401d600791962424400c0202803078002030080f400581c6405400340b2030910401428010248605c1070b400c0440380600c603500401603120b20040a6488888002c52a145c00f802d01d4042c1100350356003919140d062340180c1c604200540150b0040444080c4504402d5222003611040c1d00d045a055513070b18804401202d1000780480094440f001c044001580346034150b004140d003600c68000141d42d09030031800c16448450490b040c00106404046001c4410311840081c800590314000c841151900c0f500420701c80c641d039030002c4580c008400e00b4400307444c01040a0082c011403a400f0281c140c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964617095 1250 964615845 964615849
    0x31c0207050d03140f040b04090605101d010f090f0807030201020f0303010819020f121e070b0a1103040e010909140d120507050903101a0a03082502280f05 68
    0x40112403280c058401701d1500d2035260100101c07001041c11014582e1240e8440c0c0d0400f00410680c480c40344034400022200381c41a003e0701310502a4400c843c06844000d001200544200a84120001c00c0040b954000314030081c440205002034500c5400611006081d0f2001900d00380e15040c062160398002c0c030040160800025a8a00010141c481800b02112501c00300f10007142e41c96010b0340c060002c0781c00c045621b000146913203070680e103046900d5803050724100540d1900110300581c009250300300f09003100d05010310241501001000100c910300b43d0707540101c0d0030100080e041040e0154580b444c00e001e002c200c40200642c100404090b101c40903000c040506030340c0400a4540b01651503a0000f85400c3c02082a00d0400c007000d0103403000c01940346004402840b44289103004000b0b424001a6241080b0f0410004d07280e212045c40e18003003003844c1c0f40343c80c2c00844035844019125810b00c000161145c40f42070f952154007180c407071242c0c029401c03145d0200040380c0182031082d581c840d04210301c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964618345 1250 964617095 964617107
    0x2041508091c030903051b101d03070809030712080301090507140915040b0f03010302100807200a1523060102070b07050a080f0406080a020f0a08090a02031c0207050d03 74
    0x50781003803c00141900441c9000d40741d17405110070300c80ca0802d1034a1015005134000c40c2260f14002c0c0c002c400c00c01000640016004020045110b0240b54418040c11380028032002c001e25400000604543c0c800f42e4404a940080011080458900801100400c80d11849000d41500070209007444801080d002e1803410180c040c42840e80e201c0c048012201c0c1078404c4103403c0780c01030f11640c0085640c3d0035011030345511950080c0300407401080001503888407580b16600c1207002c0d1410381d85540a44c0201e045819142900c40321091290050882c000001959440f0313003190700d5454138003c02c030900107100c242100d0b00800515003000c1407400400079aaa40840c00300d082d18050a0805d445081c00d0074041d161254403c00208922000120002074500d001c02030000c940071651642500d42e9506100380690298464180140c0350900441e0b00300e070b01451415601a0749030007110780c24021a000246019002c941c1120400e480c050468106941800180c000d080103903120204203555940050034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964619595 1250 964618345 964618393
    0x411070b1005330301090b0a1a07081b0303071707020a26120a06031e0807020d02060c06071808031e160c081506090411040c0c060204150809 62
    0x406950b08014400c2d410304500340880003c0c050201d030b182c0d0707120340344000140415819288280d4680d000051a444041600202046074690560a10b00c040d9078001c047e400c04201030301d0180d003c2d0151170703903084104040c51080a442d550a84d180740c0c0c80c110001e017420042c0c0b200c01150800c1c080440818820136a8810380c0120311245140540085c1124840c1e016043c07002406c51010b80034048031601c0c5030040360a403805410b48130318011865000340c0100d8400f86008060354014408030000d450200010790b0040d0000e018103140c070001c81001070804204580c50000328001c50f42d250444006003c803203000d801403500851074165100c0044c040610381118511b039002c400242c0c00c9005118100d00032203594044059440707a41c40703144640d1990008401000c034019058000340c0145441d640702400b07242c209810001c1d21000ca414800903040c0b2445200030300501140109c0042c1540c80104010700144018824074600c031100140300720405401c0a1543d03000201d141402400302d51a415 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964620845 1250 964619595 964619629
    0x207030b15090c09010809061b0706020d0f05101205031c0b0907020615011e030b0105090616021003020304030503071d0402040801020a090f30020411070b1005 70
    0xc51580d552015081070104105600d4020000360107100d0542c40200150190b520240c981058582c0c65a803003543d268000c84011902c8012000d41d280030a049500902c111402003502518100700c0a00001c00c1e2004c020258140960b6a400c00c000040007545050207001c2140a80384c0000f02034840547c3c07800f841c1d0189008040c0c005844094200781c0e8045000c6040181c2105d0382d624040310701a46034401140c055a41420034028804550711a2035000060700b4402d16200e4070b85060b035805c500400d0054031060500004024030345080e03603044040d1003500031210691002e19424418459a622607901e541c09141c014824000049c0c1c201c070940b40c0c409224500310007011811040350801044201d02e2581003480090007084010040d00180010000d036103c0100041d40d51040d8691940d6510030b40c1f0f042131503202e0b48000f020b22174042000383ca00a031000c1c0d0290200d50001b6088442c1c04810003218140000c0203010440751070542c0c1d0740010b4074082c0c550818070346400b0494003100c14848038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964622095 1250 964620845 964620863
    0x30f0507110f031e2d03070e090f07081e1303140304030c080309120a05030108160303090b0a02070801110910030501030f062a09050f090c0a030b010215040602030601080a0507020703 80
    0x40c0b0b802d424000c0c00f0b080c00c00040340304010010b01c485c115003640151440000200c4040188401d400e11090311406000794200c000b5480e03850080c11075510402a0842c040035004421100c040c001b002c030141e0043c03281d500040009640791501800b10b5400c000710000c908400e2080002094001741381440054210f02030319600d582e214205c5007004040c5c0300d1900c0c04400812502d0741d042d031040c00b441c16109041c085411380c4009010b124204d0b1030034400180001c03401841440200b61402c040d1134150050b004641c43e42342c5030b0340c41c40c0c00d64911801d65428142c005c18418014501141c000c089404c942c00e0401c02035055807180038505444900150049071940745000761b05140300340b001c031405403000c01e401c8864194503006108440d14130a1a12841c0315113001c03131840c40c08168150140310749200c0103280961005098020301181d000c01c0d030540c02071842c90601d40c01100c052903c00e80c4074000c0180c4d40d10702500050701d032a101400140e103440ca0304042100e42c030340004000050369007040c192 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964623345 1250 964622095 964622107
    0x1080309011b0b1015020105060904080a0e0a0b0a02120a050a050304030c021e040b0105090109050909070f0f290a080402060408030417190c0312030f0507110f031e 72
    0xd05008504003401429040e0540401c0b05103030042c41c841c0c082c0e03005030200b90080191714008071300307072402502c0a95000300d00c00080340025000740c00500c1d00307048c1401c010440451100c000b0703414005c1a800110302010001e40c108076603038184012500c0c818050050b60500340480c400a10b02e0090300442800d000002010605050042c04642000c0783d009004e00100c10880b41e411800a07080b881990049003009480d81131903000300c0946160b9001039550708a000d16000c01c101c0d402c030010708402c11900404002144041c0c401320b5880280000500c0500c0c8586011100c0085235400c84100d6801e031090081c070700751030762210704452001c21a450014035a440e540009401449150700c0219184400100020403d420f00400403034020140169552500e080a00450b1400060402080300034020030900000e0180e90207141d01c0e507058940054110340070742a0f017040300d60036a40b03140403c0d15440781c9458544200150071980380c144001e0b44c01d101d003042203240840003408020411400110318 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964624595 1250 964623345 964623377
    0x60c080a030209060408010b010207150e27090a0311030f0d050604061701090c0e0f0c071518021c15180c15110109052a1210060603050108030901 64
    0x10f946980b000100507540da541d442032614002d0010310a06400f40c012070381e0005e0160032031031010807140c1d1300340ca955500da40c0800c100a14458041800181d94001404e0100344000c60000b0501c00c0c0640001414130507428100a0a880f401103420100790703108200700a0f60380c0d811020780e803900c0325515010a1340e4036050300140c0036141d59040058003020f0031041300c141000541144040071301958100f80040e48400c000003100c80e0441e01c8030b5150070344002040f030841410f402411030900690350300301281c010700f2220050b200104070b00f2056820403104501980383c015107601d1502200d01481c043d04a0b01d40c2c030b011020072010700440145960b418903010502d400d80e4002016648456000707101030321521706124090040c420840050901c21580b902c45005100360b55580c0d410034018410b45002d040b021300006103070074100f4554075801c400a40592a1480a480081d5003034024000c4c00c198210040c044030010342c070640030503051000400c50b6007400710442e02d4217082071070191300c0e41d206080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964625845 1250 964624595 964624597
    0x1503060d02040e012406090e06060f0a02160e0609010504020a09140a03052d0a1e0c050d0c080c06180f03150f090c0f0303120a0e031b0115060c080a0302 67
    0x171485460022040d1008600c410720000c10a0ba01aa00e401c800c85448000e601c20088048070500c0c0c10110402c0054070341c91502020b4a1024158811900c044103c0a0a600211016405000d140648205000356440d1013600b0038050700d0243c60450a0a003030302e00c024101c803000d108000c00ca00110054400307035110250124007440c1c2000c2100d1007503042d100090b501c5203218056195005080b820044160b10201d0000b00382900020350300b400d99401424448080402481120f40046903400040c1c6621104688030005015807407640e00d113481c0208942c145100602d0341c0344107007010000d00c082c030111030000c0303d511041502c15058000c15900460300d0300303d210f10706404d01c00c0107600700a0454200c00820303100c3d0200000f80d5400c07010000502100341c0803403001c6075254005101c42d5218200b101c01059101d40c080c01d010481468032007602d82560321407141907043d812205c1c10150270704d07424006e100403104079001780c1c4025882c02000800e055080c01d8020881d410026038001d21500c6a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964627095 1250 964625845 964625861
    0xa11030613330f030b1906090c0203130519032d0c061106160c02010e09070210060e090304061101020909011701140c091009090510051503060d02040e01 67
    0xa82e240070b034860319440340369140700b200340c121599401901c0c0452401e0019840b40304503030b400703c255682c0d6296070f41909254212071904464440e0741d02c5000070145000d0090803511a4990080e641c0c43e2807400843c10107054a0b00035500030307807595401d184941c03841c80c604000c0ba5046420495890031403441641c80e0171501188459554a0584038024004234042120442c0d00342e45900703420035100807072651200b5003250070250710100000345100181c003800c88180003500c1450400101c903943c10005100711400d5913540e00692106d101c64a406a49219400140002d600c0b420640d24210b04140c0e540c0c4034501900081017020b8818088040d0250107481e00c0807401030800a0543c1c440240700e21420489041c8811507007840505140600e9a003580c60003540300b9007029240510940c10f1212042592000000300010400002190a124070a50b80a900d100030114846841c100411220b008400c00d100e583c140b082060024580d101004101420750544020443c0c01501c2001d5005100c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964628345 1250 964627095 964627121
    0x270206041205010b09010e0f0708130f0807020a060207060207090b0604210c080c1e0d0b13060f02040f06020d081f051f02010c03140604051f080a02090a11030613 71
    0x260b0000c5501f00c0b00c10368140c0b01c2d00e5106140394040d0740d4144112418002607410900101c1c1842030100845d0004050081c22070040b01c206240182c0e5078082a07180e0829441200144c0210809000e03050f41840709000522142d02d0a03c0070200d40c8001604900c100d20408208491111039400079140d07a40f0710032800d075000041d4006150752203340135220002d864a49200d0001d80550a02c010b90035489000002006000500805907035500d0440fa902c01070f045445240c10100c071040064458081d0a00782c03820712801580f40d0b81303422000c07900348020750024012f54005000d0001110ba000800507441440e0a13224469503081048504138285a9080650860308120390000119130298019484c147c1c20b50080150b28002001242103440b6141e91100030080c500211f452450309801070707034104c0a400300e007880042004c400c1c1540c09481e5400a80c0940115105005610780781d81600d034001000203060000d07601080e9145130602c0010401c500c2443d44902c00451802c07170342c1c022240c807503c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964629595 1250 964628345 964628359
    0x10021b03070308070e0616060f11070321020a1d190605030f0f010803090607080c01060e070f0e060304022e030603020a120f02121609270206041205010b 67
    0x11030400030002c0c0d004540140215405c1c0702c071a15a41409000c564090399003220207007000301140c0c0c0340000350070342d2051320901c1c0d901e07162410354501c161070003410458480d40303c1c55801002f00300220f03440d20000381c01980d403038410301200b203649801040c0e03150410020b42000d070311401e90710b00140c040d18018003610350343c000300c1c000032421a0700800110701400f454046103a00b41d40c0c03081d091440060034000c2d003500340c01c140a903d0b001d04000000c0c101182c45000744c6030405591450b03443c2100c0c490f5000c1c842c00030345081031144240d000b00b41c24206481914250030b00100c40404141c00b4030010f48000c0c020241da010303c01146103500e002c60f404040769100d0050601e41f00c0f000501a0819010aa114003611140000c900311403401054400350320007685400c01c2e51640800000b40060b00307900c3c190740902e4111000800342c3c200d0702c2010b030014035400102c0051254002d00a00140e422561201465206010150f50385070309460440d810385401c0c071300b1401c90340f41544c09846a89113090f00b00b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964630845 1250 964629595 964629607
    0x9020a020309101206141201060b0a0323090a1e02010e0111030c3403020307090509120406050a09080d080f0a2c0c01230702151908010f030510021b03 66
    0x103800046081d0100b41251447c020f0400410018206c0e6070610440b03800c204c04000642c0c6090107a0803101c4a20007010544240c108200d84030140d1020481e1810010341005944508002d412140007602c400c0c01003408542c56180c0e80042d007095100d074a158180f2041007000d110740e4004008848100115000352186500d0f52240381d0840c10180703042d40c0c440401040c50b2541c0900c0480c0c40e000b201c2e001002054802c1c50000c1041c000d01c0d0180c20701e100c43c0903d42c2a540039607142030042c0000c2c92545ea07107568032502d1650080c0011055000410a034124041580685900008440d0001428284003040ba12441d00910044c081c1d134a28003000c0b100c180c80729400c0c0000750340c40e09010300d603102a02c0288004000446139016940b001500e10000004016449056007024000c1c440c4007511032000d04070a1881d102c003540000400001c01440e1340c8040040b00c1c0e20400c064010104211b00e19006411599520b4a4184c0130050303010b980ea021880785050b400d54003d250407280c0502c1941e036100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964632095 1250 964630845 964630859
    0x83a08061512090d1103042904030c030209060409240b040e1f020a02031c06050d06020304060b0402030105062502060a0f02150103150c0207090e0309010909020a020309101206 77
    0x1841100d0070700e614001c104421343c0060041e100c0106506005d00550700e860708140c440326081c820450604114180281c030b8101c1088100c00400107103020307507a0107403044e155104120300e80e42c1c000c00c8140100e0424030080300003040b141d0200c801c3c103d28050355500c1d10329221400d00600c884074110741d00505161944154110101d086040703244045c0d4040425134840003882c2c140e01c209601407006a20810803594006e035107180401607803c0b07a0201085c19681d8600041d1074426404040d030b101d03503002092104104c891b20408410030760644080d4150341c90000014a40c0c0191841d03a45d24681d6003036038500514030f00c1060316110340c0c0204001d86480c04001e0091900a00401480c0503201d14282c141c20408201c1c1c400d1b048a138442038034001c4124410030710010f0700c1801c548109510a00c0c20106200f03440e40030b00440c501b6014011520f680748100010000e00c0290b00500c180317131041003421f00095010040350036040e02030b0303045022124655811a012102c0c1d4045500084c82c08402203454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964633345 1250 964632095 964632127
    0x1104030203120702030712240f0e060103020a050d1103010f020a09091b03110c0f1c0302040f031410050a0504030e0613210c083a080615 60
    0x528000d404555581c400a103840e0303000d00c42c00d0f001940c1070f84060410402c50012651441d40070b40708003100150316410016420b0401e4a90841c9100300d40c652561032a188006d2281e0400341ca0b1840007811554034640204000c202180946401290014940c20601000c400180d0108070060002c00c010091907603400300a40142c0080e40c001b40154500048552550180c19294001c680c84000554401301c2c007a00102181401c2d1094081c1c2442100000107040c4001d0502d07100c00406440c0d075985c01c3e204d68894040141302d51082c9841440144107515407814000240c0341d00c00042d1401c00c0035100307894580440325810610f800e00b00410000c840c24207401290007a0310a4039407402000c406c2041042034060100d0202d18502c81c0740e001c2051840360700074550f0700402c0020740540d2118036140c000b4000c0036500a00ca031360303014a1207000441590b00c280500c0c0c5030b400030949105080b503520b181c0b07815040d030000810020b10748040b6042d47d450f2000301082a980c40783d01c40d031324802c4981d00359071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964634595 1250 964633345 964633349
    0xd02160f1a040b0601030b18190510060e060705030405060d02040906150203220506130f051c03030509151f080102031012080f12090f0309010e0603130203011104 71
    0x6031141c000c01e040a1080c4503a0320602440d032060b4110060340c1c481004400502d00d1484d03569122000085894021403a040014080c91668001020410b4607010b55402d4400c0070f0140c48002e4440d034001c1081a0b84005042210602152400d0b903492840c18058614002c0c4e404c81907002c000041c80014018240e8001c10441c0e15001c0103100ca15610039281a050440064050168204000c05c1e010b1820041c43c2024500b0300310001d421054031100400c20781e4001003e240346000700d0640030f21111140701c0d400c40050004031054200503201480720705241d00380d0f64004044c03640354000301e038051a0520600400c084c0d40300c0d19150a18002e03140b00184241103805160b01c12030704c035010402080c107000300ca00c5030004007854030400d03244c02c0c004d040350401d0390340030349000c2c0302400521042c4d40c0c484000c014010b1072540c0b08881d810000d0110b428600c3c11000c10740a42e00400030070310340c1d0340c004007061007607041140c0c641e45940d00c94219038142854a400258954030304040c8141070f65103940a041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964635845 1250 964634595 964634603
    0xd050904060e13060b06090a0e0a09120f0801050f0a0e0403090b03190c2c0102030910090602070f0302031c0309060603060f0c1812080705191703100b0d02160f 70
    0x131040342c244090205910460300452340001c1021020b000321034100c0c021540100101900081844054440d814080c3c100c0d840032000666401080005647c029000e9000d40780445456001411540014180300064441c4002115a80740000c0c185070180125800030120000f082e552450000b0411107400400c40c0c2507590b8602e0100500038041c071510440041361150f03c05605003d0101552812075020000400e046101c10400311800351902c1aa29080750042c0d1140d0b1403403410302c40e002c0d0038002d007908441d0319118038940c10005a640041d20315030043c2072041000c5002049501180034000e01e000140215080080010030415268410085034081c04010402181d641800300c41103009001404095803c001c001d00001101c40300d4000b01501c2104100e01e0103841d03a417428201842c1081c09004591002c54040501a081d030f10064650142c0c265940ba52501d14034050300701d09e8a005581882501161074110301e0b07030a5040340d001001240320f6402c04002c0f45010007161f40060341c00c072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964637095 1250 964635845 964635851
    0x121050a0c14011d0915150711150f071506080303090d02070602070501020703021201020714070f122003030903120310091e05040809130207030e120d050904060e1306 73
    0x281324910718001345021000003008410141c440d0300550345102000b0852a0b0311a610905030400c4d85c0303440c2c004040300e520810781440ca40b03003500208540030000c10441c00c1d03030b10301c00c1050900e010040703811a405140d000c0d8400440329031000041000300081d03001000144400001d110741c0c1350b000100b0f054500b13a40e9086924440c0c58176000c0741c81c0d00d20b910901d40982d2240b0310038401861b0000f41640803560b0100010300b0f001041d00d41d9806005034500800c00d40c1c104000c24418611100010400340c007c640d02042403500507910802541d20080419a103624203ca481e18180d4060049a00259005044840b0034102ca0000203417540252031141c0c2c2500301c40d500194044040c01740203401c080c07514290b0b081a42c0014120041c2200500440b541c1100b000301110503600e0b24000603180d5201c04e00142c40d2111898003404610280038680d12034604105542c0b00c0010005140c0f203000d41c1450901d446441290210300a0000341d007082c91015420310810096803144014880301c2d9000d10801c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964638345 1250 964637095 964637117
    0x16081201081b010f170a021608040f0b0306090a0e0106170c1807050a0f03110a0c060f0b0603150609030a0501140109140f060616030f090801050121050a0c1401 70
    0x42d81d616444c40c1510001c07031204003030900180200c540082e40a40c0f442005403078560080100001c0b20800b55085500c10000318090140c02c02480081020b0700c040e0f0109859420480c0c00207a48840c0280903191940e260320711524001000e4020000406040c64420b4000c1300b031621440c1c946000b411694003900241c01c5460803180b003940001c2c000e0250380c4a291070615880000c60f40483c14a031107905143d00c0e0382002500b694084000c20042ca403a6607100071884445c900081510303a10f42d12540c0b0941000208200c0366604001c81c3c0c0c01182d2103c101e1181c01c500b10105a0501900350030b1075050049140f44000c0c48019007240c000e2040c4200511510380e00e400a100031915040d46002807110340c0c50006a04141040c032154028200802e42d40c00c0590101c0340341141a410340049000030900400751400c8c0d40c01c119400302030541007000340072030760502203180c40d846a00e9249115141a82103180f05011043c800c110f20140c204440701541d42c4c0b186030354500c60704251180c500242d600c0c080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964639595 1250 964638345 964638347
    0xf150306040c02014107020a1101030227190b0309060112080a18050d050708101419060506040902041508150907022415030105090316081201081b01 65
    0xf41040342641c00140002c1041e42250501c81c100156034040305d411500c00e4209811329054441d00d200b004158001c00c0795101c10714252117103048940440b4107160040c8a0070643d410321f10000100700d00080c40d488111270300c1000150071840d49554110000c802c00c000442c0301100340b0300a43c40f03145140101d030300c00e0b6601c02c601700491003104c1000d410094140212118944504841c015818040c0c00b42904103444d0030004a030921108000c071241d0340240c0c0100031410307040c8264196220a054208600201c28541c410002c2004143c2c0305041e22004007000b0300300c00380e80400052320000c0c00c05034a46441c0c0c03001c05c001358890300815095441c4844220540c0b4444c418041c07081c880040c52007003552440090103a0040f000e003500080d4010720181070b0042e441c41d00400c5240e10500b500d8130b542e080c48820303202c0d030b4002e084241b03001703905000401c4100f19000003280d502c1c42d2090380500340b01440f400c10088600403510039551246041d800000c2d04103001900034003408410035099031062140c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 964640845 1250 964639595 964639601
    0xe0a120507060806090f0604090212010c091a07080306120102070b040611090a050d060f180c050a030c05060309010b060301030804030209090c0a0605070501060807081e0102040b070609020f150306040c0201 90
    0x313000341d01400c1c0d80e000400c1c061900b819150404c0003e0030118002100750300240300e80000d076000a0a9a644a01512003607078000c1c440002004e000006c99821041c1050f40c2080e480b0321b1001a254010000c0450711644a03400081e4a00d01885c0003151902e803e480c140d400366805950a542050412407082081d205100c2102c498501c000c00c404140c0345009c090000344a92aa403c1d030742142e88280d555009401e90060300801c540944203104ca90030249410b4010303800c660862401491000c41c01c0c0300058214074050155141115032503142d5454500e0a0701400190083c9900460080000410011054080d101f07891080701d01074210b660349810580d0340d0b9440074880742e025041030000c00180d40150010041140500e00100792141c445c80d407035292035415071100c0c1c070030384c407a1504d12242c0d12850801d05121080e40f00035413400303242c9200c0386218012000c1c040c0090703076507406100455869070345034030048202a00c6051401d502500151182c0c1003102e880d40500d043c074824103850391041c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 964642095 1250 964640845 964640851
    0x20309030304180b18220c06200706080106030b0d0f02041a06040b12071d060901050d050f0108010e011806051509152e0c030e0a1205070608 62
    0x90025401c140c0341c00040c40f00e040144030303044920b640d92400b141036611211510007a41c0b14500c000308407401c044100d0740007490020b034003410300c1e01040840b500045003002c510341100c55a20300032001581000303400800c064103503244000c91180c0c0e100042e41581200002d41207601903101044072030140d81c00d2201c01c4460280090104c500c0c1c10030341b001461b25500c01c0b142c0104145248480390619808120f0343e502542042168030300106800d00764500040d101c13507202d4141d181903500107403983c281c0c400038000011164030031000420506040d9100c0c4040e21308051074058180980d04004620003d90031007805051115401e0800c0180c4152050091040c94051007401600200e0181ca402d1300402c00a0054000f2000b51070841c0216620010b099024285885898948106c0035040042d08003d2100c464400044501440d0048612a814820345049d50925008500c66444c2c219000395401c00000e81c0040110341c04a482d480e240324503e600c1e44a01c0444881e582c458000381c41c2c4072011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 964643345 1250 964642095 964642099
    0xf0c15010312111c11010606020102030a050604140703021e030420030d05180a08060c13050a03030e0603060102070e090a15150b070c03060203010306050901140c090f0102071d16020309 81
    0x40f030013500418922250300e4082822500d80f030b45018420014441c2541d41c0da50104005031340100c180949441e01c2d1045641000c0110f4080240c01c41c0061000c00d1040c1c003d00c40414164003003140001000f41c1c8944002100070a4086a9203281516042040c290300e0201c510b15140615082111800d0010b036922841c001c503202c60b4104908000e80d1044074603070604081e000307413401d00002070510040103298083c40710036074145e86944030741c6a10100c06101d0342c4494403c401d09002040070940010310070b000c0e130005507001070b0383c1d80e140030042c0c0c40e1190380d07403001c0c0f0300000704020400131840115040d0401072144208121201c007441e011410b803520005028a0880140410845040314000820041c2c2c4683e00a1000c1d55403501c4000490300309901c02c0c3c1c1c010b0385072000c02482d4242071280103200505680480740714101340e07001c03000500900703034a24011481e000000c030250303008010010040800009120301c91030b003e0010358290300c0507104d402182d10a0164075031014008400c0d1240d070880 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 964644595 1250 964643345 964643353
    0x20f010e0316080d02030466090e010b010302070b0711160906060f0f0c150b03030409020a0807020f0a02101106070e0f180c0f0c1501031211 62
    0xb4a448201107920205800c5860880400c9040c18010303040c0051449940070f41c41d0a8022007800d400c99000c0f1f000c1c040e1049503c000101c601c4800c4030110780da101b81001000e4010b0403d020720903020303070740070540500071004000c0a02c0041c40d017030141c0000c0380c10b10f4240001d0281d40c1c9000019002c1e8000d07528010700308070001c000189100e100340400c410940950341160400d81010503208050406500000b4801d91525004d01500341c00c40105513405c1103c0c5028030740040c007940c00810203486241c009008120140504c062800d03290401c1c690780710010300340e995855441c0707003c10095101e0300b0100081404031000074006400416207002018480c00036040c0c600d03240c1c0c00c000c24413003110040c8007070040c251005a04c00604110301480b0720066102c4280c2000d546e01084210700902410320302c21810b01354180c1b55004079404594224098039820354413400e44462840281c080c1c110080d00e54440c5881c0740c118403030340020440c1220b01500451600c0a40c60348222405000c000744100b079544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 964645845 1250 964644595 964644607
    0xf0705040f020f031518010608040209100e1506130801061404020c0706110a0b0106050a0201050a051902070206040504092603010501050715060b0a021e0109030c02091306050f0403020f010e03 84
    0xe440b8406185e40030003403d0803400001020454680e0030283c0260000030f891404020840c149540c45c2500a180c5800c0c00e10507078a000707070051614000402d0740b81513032882180d25901d5190700098420081031005091a010380f42c0c030b1014000c10030b134868621030084940d804c1180741401c0c800c8652504420300038004260500006545001d4241340103c2a40300f0051044081100c4100050280c212a42e500c2d81d903c61f1964000d0079a17802811a1402034a440b05011054001c09030f68155400000c03c0907850300010b000241d01405213038840e5800c603081c05229010070100c041001c8032a0101c80e0714681c001e8161180c9643c5000034050140814010084480441c0c01c050340e983d8018450400401c1c45510b03820002d050b41c000f0368081c3c002d40c2c050142c5042c040414650342480c4050707000208006009620000c1c4101407a40b00a8052240c400c04920f1f201300001196050580021041c40281010392103688122000c490a9005000701e214244405a06010740380341100c5020045080003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 964647095 1250 964645845 964645861
    0x115020c0f1011120d061508041e170927010501140706111e07021305092b0e0d02090f10090912170601300905030315010f050712030e0f0705040f020f03 67
    0x400d4131121054181c400081c4000064156241d02403041404292180c0b110904024000980c4000b9510f41201d0242101c9401c001083748010303044460918042d1829445003411402920031004041c00c0310b41044011801c0d4490a4002c0903545c10015a403003103000d1078940c99000b0f014001d1300a51101c1035843d43e4946580d60782101d900036050100f690310440c0441c00c0d00f040c090700301070709a00400031006610450380d0400c50680d090001030324456510262a8001881d00740000d003082030f1348910501185102d200080d000b8040c000000040000c880740b03080c115003000020b0030f0800000c40e4000700c43ca8007121021501d0107400103071203034848140d440c400d80304d102c0307400c0c44554641c0c50122181520481c20f4014000900d0007074015650302d040910400848004000e00d96050100307030203400380029400000c64038826040314500d0100540031008402908101c44013038024400d070b00003010351b488c011410a08031a011501000180000340c4e458060780519182a296980300b4400281c040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 964648345 1250 964647095 964647113
    0xa06080d050a210f0507080f151c140601060e090c04080a060b040e0d110105070804150c021504121116060311090a0e0115020c0f1011120d06150804 65
    0x2032040590b0104240200c82082002c03101d085510038001030b07c1409110002d02c94440858010101b400201802410800852800f0210840c1c0c16140f685251199061000211b50b61620b8031050f41030b119256035800d00144041060f1300405e224900200100303031b03d482180b0480342118182c6014091901213503c0e42d8004106186031282c100d620b600745a03001800074003ca0310203a0300382d1070300d03510040b40b900d10301e0840304014194000d00001c0c405000104d0385c502c82c0700c0e002080f14103010a845007440c80403418000c3d0417440c000b540416006100410030030a11102c2007541d59a1540f040030040c0c0b80459980c01c001c1d600441d00303040504c007072205510903044000040c03a51040c21745400c4803240450140354145d40588100c03a002c2005000c06c21464075402c0700ba10312840281620310014002402d400348840d2028415807441c011082c0c410f00802140410700c104038141d1b81d19806503614681756030b004052180c0320034a021300114a02040c503080300d11000e544d607914140c6940d01d0b981c403582 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 964649595 1250 964648345 964648397
    0x10b0d0b011214120a021014040206130f06030b12060f0129070c0611030703140a030f0c02030406030605030604120503060a030c030c030b070e0306061c06050a06080d050a 75
    0x500030740c14601c031401110030081c00e440413158901c256a150b08104c40207045c191103130307413903010300f4101400f02e800e20600c408003d400c181c046484596030200402810380c25a41540000f5900300e0400000501a405030301056130600140d480c80e50420403e041d66440c1e80c011220b110003040c03480c00501c05400703811800b0304420000f09003800f21071081c150b00782d45500000720032180030300005000e000c0706034800da103e900505402c2c001c5062100542d006400394800c2143d90003e141c2c08a1088000c2d8400e81003032000780401b5400304021030000b00001c1d100d5000d4050b50004c00d00b001c90003d1141000a0481d200f580c001421f0b1700c10f4031800100700e906900250280754060090003000c0081080c04106000441c465040c003500c9130329501c0c01100f0190004c0541050201045119070305c1e40b0007151155014a0403145031110248400c58202d119481c4ca40c00390640d46048100040883d4680c0000305a441c90001c50301e580080c43e0b03003101c3c180320f4440000c0c00101c400440e2030f002001320f040805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 964650845 1250 964649595 964649603
    0x8030604090f050a020a0803160201030c0504031208041e0b0c0306011709060f0c191101061e180c120b03071701020910140405211e010b0d0b0112 64
    0x207a8075032944811802c0e00148005071402c0c0c200c0c4084c0710440c5403480c0c084000304542d00c081d50506020305208510301c500448081d050503115106112002d1180049501071070380302c680c071480840e201c1001444800300f260704a503804090980e59031031a02038020700807455484820104d4039501d1407800c5007107400182150b410b01c00f090482080d42503255101c01d101c0e20092000704540d140c41040300a0b200c0c00a46204a0b908023045030111440c982c803078294411016007051024440282003250041000394001c2412481100104660241003410751003101c0caa80005191000450724002c101c1e00001030000120744405500108a140c1d5080070301405401004c2e0b500495480440304203903803107080c100035240d500103400000c0e49010300324204800541e1526505a00d018a101c01c1c051086000b0b09105640c0100c0c0080707000461030f685001300c001a0243c4109549401001c11500c40300c030503151145d400d150826145007000b03904801d030150460405000742c0d01c3c065a40c0400901e00d24195 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 964652095 1250 964650845 964650851
    0xa0b0903030903070b0315040c050904200a0302070308092e0e030d090209070908071a132403050402030703080706020d050114030c0406080d030b06040e0f07080f0403020a08030604 79
    0x1001c0741e40c0030311000009105545c2400d03641c1c0381025500f4802219010b10030701c603501d400754005117523038040d0555480c03c07800da03400124945408030062000c071611003400223510001032007480075503245c0c014150807032080c0c4665680303481d0420107540313958140754410b20480040300744a10880c038103001a1440c80e0b21510020340300b04208813803419036001070510050540c0303c10060b002c60506590301c0f640114545031009016060050342a207070307902e51040120032400000c83c0c0580c01e000038102da40960404111820082c0c0d2542100c042c54034050040d002c03170703103026501315002d4024040ea502ca5640100a8101035095940e4140f89402070030b0140c5095502b070289207140c120501c0354038064242052055994070008003050700d000d10b1081014040d50a040301044000000214002004003904001c1004480170000c43d04501459002c0700759030034420305000d00d00400304031050142500f1766901031107030380b204155850003100740c0d4010300581c0019002c6000c604150003a5420043c010008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 964653345 1250 964652095 964652107
    0x1e05071425050f10050409140411060a1d0a050a032d170d0b0402070b100b0703080a0903140f0a090609032a0911040521190501060f0e04200a0b090303 66
    0x25100310381c0036952600b00072236411306203c00c0c0421400306811503c02184c5852400d403102400a100c02c921400d2000d40d1403010001d05c24a40d90305044001070071000c0c2c00c141c480c0c0c0d03072030a001e0580160345001d100c10005079844402c060040f200c0d0034034401d030086c10b00208841d00080a078002d90106964012441e91042d030204c059541c1c0c002000b449005001c205818103180f4800042d4100c10361003402c10220403c01c0fa8006900840100d900c00120100050700001d10304003038940340c0c00404446280e060005e401046a4030403400783c00d544003181c0d140c207000c80d2942e00541c0d4441880c0030251690600e82034810081c000c42150052500410701c10881d529039032034020060302c0c044540403003481300108003444141004144102c4011900790340000b03004c0314000b01900e600741004d4001c0c0d500309100c0590705105094000800030050f00c4c1804034125600c0315020701c0e10350151000c4826100488a01c0250054034090740e1880c032000f0301c03401c1054a4442c500f25585c0c00040b0700394140c003091080c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 964654595 1250 964653345 964653359
    0xe0903040f090912050a1202030a2409060b090603041401060b0a050702030c06040e181507110d0f05092206030b0712020a1e05071425050f100504 64
    0x1244008003070315680400c812080d0f1030141c000600d114451310812030284125520340394040070641c01500760050050b40c03038076007150301e1000e4451415000c1098103891031140700c0c140740b41030b06021030324070400c00c0007926220303400010144074100c5078a6000c4810310107c3c01280d84050b04030001c0500b240005081c2d81e941e074000308240c0001c0e0260f004107001080340030a41c1024400c1066090040b80c03008e1500d81071004078240c80c040036085000d00c0801c840c054ae80c802040101039200301010016030101c2c50104401046100ca10001c401e030381c0100c154201495000340c03101c000750712143c1c072814208400783c02880090a8200110b244641003c07614060350812407080c80080d41c058900d5200c10700c3e10440c00381c01c000c1c10100f0340481c68810061209200d5100d04243c1032102031010104000c0079444040701e8900950700060a4042031143c0d56821035000030355001030181c0742d5103483e14003140c030310002c8d9010348520443d50000c1074070020541c24a0b00380702003e425100c1d03040c828203058541c09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 964655845 1250 964654595 964654619
    0x306060306240417030403050d0c08070b1f0501020307030c02041130281815060608090f1b01020102041d01032f0f040e1504060c0801050a0e090304 65
    0x2100740d01031000050b007406a84044c2c100100103400c480c00540c5843d1442d88c8895442c0100e015007401c000040742aa801c210303101d030031075144ac5d070403000c00307601410030301a140000d0580030b07022440c03c01e040c0c01c0080c10f54008030035a01000e070581c641081540541c0c0900c009008110101900313000100b1000d0003000d860550b81c420f0220b00c00317008416204994940560000140c0305407481d03144d03402c00c0c0c40d40620f140c4400c0741c5503060400202c1c4035085030125846445054100030004010088800e02d030700001d900200c215111540d0382c00315a01d8045500b80c4407030400201d50a984c01000700300000b440301000e140100750042c40010f1425036120004941ca205c3d082c0c034044000c519100400921a004405e0400c000c01c04458140b2807404662500c402e60445c1c80d594002c032103a811900c0907589e00d6000503911166a015140c0e5a01076400c1000c031070100711000c6807604e25140702410340c2440b941003541650005402801780500305103c08261102c0100902d5031480100804101c2e021030394 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 964657095 1250 964655845 964655899
    0xb18180a030e09090c0303030a110412030c1106090a030b0618040507080f15070804030207170d141e0d02070507141f2a0503070b100801110306060306 66
    0x141e10301800544000410000b50743c060324600603031380581c600703028030f580101c1101c0e0410010a00006d10300242202c01031301d07000b03943c0288036600142c80715106150300141880c05c600c2c031901d1700b80101c041c2c810800c0350f14002c1640c110713042181481c003800040c810800300c40e04031a008044041c0303c1410141c3c0c0e103000c00d04540880301038000714020001c031101080b50f80c01c5400c0a001a000c0c030186065101c0350300308005c04c2c80041254403804603060500038440c50011703109140220a251008101d065038540c60011980c0000b06032500e27498007070380700c6d1054130115099a0030100c500402080a10f52a80107003821003819a13082000200060041142c0c038020144000d83d0203290000f54100000202242e202140142509850301c101c1c503070021407141c502014020740208141c4460b10350900c003011030b40040583c40700281c1e003010700c0710140c8907510a404000e05409115200c000041c01d0b11030001e03100c00c40600c06c0c0301141d09450704c480690760044000d0b140c4c015034078a020306030f00c10400344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 964658345 1250 964657095 964657097
    0x10020c0409150f0212012304091b0303050315180f04020117070806091302090601141b0c030d0207030503040e0612010911011b0302070e1506030a0b0103050a0b18180a03 74
    0x1090031010100c03441150050490303541d403003e4410001c014a44029140c41f1181c40303543d44046c8030f010843d544030b1004584107882c00e107440d815124a8003501c03d600039114480460420700540030300d403170079a01007580b446200394100210313241d00545840a01c00548100e0511101c052010290110308001c2d92140d0580e42d19001581020b030107000950382c0c090024440c1140c1c0c22003d401603200e194005800000a2034902e135990078a1480b24030b84d00906800c4000704000c0121616883e100140c68000c1c06002c5040c1c031407044d20b4034426645c83c1d100388401050b58000340010008040c10300c00c225446000500f40c90f5281e0790b10705401742142c040001c21245010000f00c003000950b07010b01c0c040320314000411281048005038401940c0d03156103200c2c60509005200c0004c100702c9641c405800c00d02005440c1c2501d900349074a860000d85549415a800645405e00203048000d0a000b201c160440241030740410511900b80c0041111004001c4a03940003550396803460131004011083c074050003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 964659595 1250 964658345 964658347
    0x1a0f1204020901050a0b120423071502030403050d030c020102040902030c07030815130905011404050f0f011a0f24040807150f050c0106080d090e0610020c0409150f02 73
    0x42841000404801a0404c0b4064041c000003031000e12071040c2121a5100a01c910b0b41190780d0b46d203010b12403100000003c3e007842c01e020040b8006070b040060444142c1344403107501c2c2c0c0c9034000d02030103d0b0380740140d100c094159800fa40460031141d00941c4001940303042c520001d490541c072038003030340e05a9105581030281098001245400e041d400000250010403034030607000381e8030b5102d000170075103c0c40c400c035940700380d9441214104003c001d52200c001189503007205038140c64207040442c0c44803400019105540a00d141d0540b9841c41072144244080b1010041000d400c065000d100135420107410103608150503100c5a91000214411000301c071800070129a0741742c2c2000d00d0f1504001182c3e1100c00c2d0b001010340304103141500070801e40400820303031801279245e0b0307c00c2d0050740c00b5040d280d00ca48001d0094682d1001803940c04400d00e0140c80004040c012691284801d02440d181244030078401a040b004c841e0f20380c1d20b040e802c01511140108580c201d0241c01c0318156084901c0b60b41c951a01d658 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 964660845 1250 964659595 964659601
    0x405013209011b031d120105040503090907080439081b180604020f0d0f0c0f020a02150a0908010203180d0801120602030c12040c03030306080a02010203041a0f12 71
    0xa44403c1c501001c2c008800c0540340080c4a54000d0101c80c07403a00200c16941e01c0c0419a18a912118407400c0c0c081a000008c5c81a07040a08045480e5030225030300314080c00c41c0c0c500245600340030314541802240e00135140248404d12605002ca084089070268802c1c1c0784040340103654804004144001e0607113140076109000040780c0c0100041e8070103907258051090441080990042c442c05e040d03201c0c00964025176103d01c4403440e071049100d030000140b0594038151650003070307400640c000480c01089071168014013140103001c3e45c0e2071034100c1c002540401c40302c43c115011007500c4003078005d2440a0902e080b40985400d4000d0070381e041103e0079408085aa40340c40021041005401e030035203400d040520035541880d822420410a6400160001d900000407802020754282101c54144607c46903010368185807408000c140c0c2281f100b42c001074200348000c6088030020a000c40181d034160006c41c40e00e45020300c49002450318250030440308500b8481808080714503401403192a030003280301c2c00245 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 964662095 1250 964660845 964660847
    0x31e0201052a12090c06070b071404180908040f030b0a1a130905031309020c0601080303011d040204090218010303020d09030c0909051006170c15040501320901 70
    0x31034210030360200c8125907400049460b000b001101c80d09001e800c4008155a00c161601d0f14201d1048034460f04000b001a54a003400340344808107001d58410b5451541290808007442c0190103240a5078400840300c1c000d188059104d940607039021072107101202d080583c0c401401c03010662a034400d55000100d80104226040c0c80d21402c5d42c2070b07580b00c012540f1214000f000c51001c1600508002c030850742e80114a0034003000700143c40d0b00024030004400565114041200030b07400a07607001071148180c20001c11810804020341e81070b2180b18198982818130032400d0426280060700a80e041a1b80c1c0070040c0c050380714103640408401394044020b0555145280091030000784015401c04c009054900b800080c0000c9504c0017220000030f4007003201c00103801e24600f4500d0b01d03411245690f20b807920001d100c09181120145188650007520f218140d00024094260145800d02000c0f0104100034001c1d580100100c1100c041115012950410010300c0780c40403c0d15560030010310300c00882c6c052095 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 964663345 1250 964662095 964662121
    0x5041a011203181d09030c0717010c0c03050904020711120618070f03080c011407021b010206101502120c0a140f1005070e19080d0504080a0f031e020105 67
    0xf2961040ca0440d040e8030b0103203070802811804001030b894000807004a0074280d0100291030303100451405072100c065440d0300d030000c41213020080c24000d500384085403400701c0c041c2d198a1115905522207519009403c81040700a5220745000c81d500240f046000030940c42d0002400d4203008568002d01c0c403810b00035803101126880318468110b50f4001202030200d440485d402c0401c0303da0119443e91102c0e00440038501510750103800b00e8194640c00d0030850490b60000b104424020312140226001900d240126155042107548050340d44441074200401084035607098107284542c4165141400d2070001d9681c203501c03042c00114075902ca4400e180601c51f4044d0603946680400d40100b0600c141d42c001640c941c3d0710303e940d074000c01d503407800090755803802803d03140381c4490300400391494a03001803c90001541ca6001b1100c0300d10803014511010381c000c0b070494064503c1742d00240404d003107613a241032003d200e541007141000184082a8040a2801c01c0003606507243c0e00085164503106415200c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 964664595 1250 964663345 964663367
    0x200d050f061f060207030803060d0b041b060906050306060f070c0e0603070608040b160e0604120c090b0a030803090a06050c0a0201050a0b2d0a06051b0a030503010905041a011203 78
    0x41e0002e0403004102c02500024018120703940020b0341074032655141700042c1c0545041c3c030b0107080b10100104000400800391904080301311081858030341a1b80710030003265207084500030350000c10400c0012455030301d403040203803802054068141e494040645c0c3e4550401c0e6140d44440598000481170100d81d240600543d0041c0c8000d00d4451a42d1902d52100701c4410005020b03c0c005020804255201d01d21441c03088a00c068003818066546507100301038140c0c0e408040c0f055501c125401804200700b000780c000e402c9841402001c0365041e9080d602d40c1c040c00c0d8400342c0004120312600c598480040c1160044c5172040000c0d680e01c80c1c40301803050001e820341c4c800030b0404010038a00000e45056603180200d0b0301080404d2907280d0314050030001460380f115840c05240d0ba100a0f0020300041c81944140103208041401780c5100410414040550717031504c800000401040d010310051044181d0399000b5a8424092800c0890784d1020f00e004c0b0031003500a03044450b04e240c0d0002c1e03900906070070403e850a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 964665845 1250 964664595 964664641
    0xc0507081f0609050c044a090604080f0a030e07090f0b01020106180f020909100812030708070516021320070807020f0310020a02070e13200d050f06 65
    0x105500d425800c84ca2170780300314010400440401c450040d0841111030020699036080c61486600344020801058001e00c03e51184081205200003d950b604000c115a4000d0354003141c054101500410303ca0800e03046400b440c01050f0f915030703422034005010011000140b21600d40003c00120364007803941614003915095040d0ba0510104004001c07441000c000000004803001400495010707040020348201080c4130352040c100024408420060008002140c0b6090200c030310320750b00c513520300d5071038041124440c0114030850300103514980114010840280e0061100b059228035900107149185c2c055070425055070b031010305034086000d205100f82c0192004014a08182241d6280d4045100b110f2009000344510130b2200c8030398030b04000038207100520510079500e40001c03140003542c800092040c0000d29411a012070303002800e103810841400d0300409031032000d070031000e101850200c2d11008242c00c40320052048000c96010300030000601c14100107070100d0704040d01c8000401500c850200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 964667095 1250 964665845 964665851
    0xa1e290a0f183302030a150303080c180907080411030a08180d0c0905041203020f03070c0312020c1e03090a030f020604051c150209030c010c0507081f0609 68
    0x1001e8901c1ca145038416038418071400310380802020411400505415110040400d091890103043c450b40140d03110307030b4240b003003041b105803415065020303ca4280300107804035403018046039060144400600c0b501442882d902308901120000c02d04420040f2902d10014803810140704c1040340744040b80d20b104000302c00401650300a904c40109501c01d0750074124140040b06504030442d22400303990342000d86c00601c1c1e50300d09030342d41c804240a44800c480032208a0303451604082400c0c080d10135602441c02e0006d0345411075a851005a0300e0030384030301040d800d024140c107504820151900080c0144440710f8040c1c1604102070b16141c0020001040c0e605107138109101d014007035161803d601d021250044001d1040140d03e00204400d840341782c01c09034100105084a10700610840007000360180b08042d40444900101e000340100c0c010000025891723005011400041e43c4580712195016000301e09131003040d6a148041ca00c0d21070b0b10000c44e10300000000384005503003e81c0c8070710f8008050006d418 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 964668345 1250 964667095 964667111
    0x50a06021218030d050c101103010b13090c0c0b090c0108071404080d030608150108061527160906140a020309030609030301170a1e290a0f 61
    0xe91200d5074080c40c92015003000c1602c1440419040485000341000307000c1d250890031a45000305140c0c804007202e48540f0903070300c240c01703d01c000384900b01c0b0740550065000e0443c0d003403514586066004062168072401d0b490008070308022240701d0b840502d070507600c0d5410840c88a25040700b000c070005059010542017402ea0101076600720210940c4007807a843c000d00006c130a0000f107a114080c81e044040540b103054140d120b629015403011341580c003a8400c507000e0751607001441a1407002402905590340102c404500c0e1640d510400790034407400140301c00852940319084201001004140d00032440401302404000c0000e24010341006e8600e03d011a180c2c0d00b403400c060444c0058400c1a02c0d40c90000179041c0c1c04074030134800c1d100e07003440007429074109040c01560580c3d42e4100303003c1c00062078100018020000000981e1810903940401910401401944000c1d02d08004c000c05a0781e0141d0001440b003140c80c03c1640d48062002d000203801142000c0e0084000c0300d411100d1210300e00d01d41100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 964669595 1250 964668345 964668347
    0x20301030203030d05071803081c0b1e0301062d080303040302030a1b02091501140403021f0e09040b010303080609130222020c031c02040506040306050408090d05010f0501050a06 78
    0x4c540f254440003601180310f80f54000101d908814001c0c9404152404e1000481004410780040c02d584480260f205054403481d007601e811920402c45440d482007400112101c02c6800110820341008010000074506a507445134190b410300c51031035169202080e80403000c9005100c3d003100003600042000354214a032030398003e0354900c541603000c2c040c00400d603442c1c00322038466403550448981c060b00d146054204822880e4018200f000100d0100d095000d4425030640b0380029503040381c3c0c009011095504c0303400c0800308441d01100e840c1081020b0b0038040840c6440c2c02c1ca005005912038000d680043d851400e000706010005401140b003030344580140220709584000f0140c1094044690040d00d600b0f250306020b4022a48c800d01a2a60003c0b5400e42e20f10800302c003600c90425031588101740c0342d4805107400c007244901e005440c0e1040f024401440824030f00c0d40061b40c424131940081d41351019020000d50844100c40c02212207a440e10000c07144e40070107001e0b1a00400090f40d010782164145030b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 964670845 1250 964669595 964669597
    0xc03011401061715060703080f010b13030b1005120f0c010503060f01050d0e01150f0f0305030f0a030213121415150d02190e0f0c1602042c070501020102030103020303 73
    0x400c814018441c03c04070b00410b161007803c501030b5000803c01980ca0b075a0b0724010301014070494111000421120000070103201c080c0c01c4071030030307401241c010110078212350342c104400e80d02500f11900b05540c80c0011071917407102083d0050648030000140322544824070000d20300241c1ca8810707030400109105200d030307545481d003c140900509092840c2c48002c480b0030341c0b00401030f1404c0c1002c1c660804201880f6950416024400e544013000991309807900d1740101101c1d00c1c41840024070380e80c0100f204141ca55107800181039592024134000d8580451403039110718800342d9410503905505490044400c00848104005840d10084040c0c00c552480d0741e0611413000008006504d90190800520900d6480014080d16180d00400d480c1c1d050101c80050001c100d50360103903600c1000d80c540030a50ba2402c511f80d0501c183c0003202d0701ea14080411411002070403081000b2a00203403a15084840080c1e01d52414102548107151000d25a241d900800d00d400d03145d900032415640304000600141e20044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 964672095 1250 964670845 964670867
    0xc150f1b1106240609060d090c06020c1827060106030615031a01120b1302030601030e072d08100b010f1404090e030403140105040209010e06010c020111070f03050c0301140106 77
    0x13a0304903101c80210000c9100751188401c2d1600c41498000305404000d00040c4040a452466007151700600340780041c8007452440040900f180480000010581c07501c238402e900c0030000100ca244144902002d02c00d00c0c0560a03041a40807945504040c40702000e06980c5104010241c0b4007400784045e0080703408a41101c884840f0304006415041c03501c11545508070280030f41d8082c0503d0760105042d071105009400588595000034202405c20181003000036541c0251003c035041c0c2e0480b206901c140c842030a510410042079400c0041001507000c82c140101c0c4230340340001c0f90200d0450802c90004014400d51540003050245626440d440030003010161801d545e0643d00000741100512185460750140750303c0101081048004100301d0300d0190010303409284252104603550340c8451031401c0c2440100c5440f40014022840750000d58070880c5101c03420207850040d01c0314507031102d240190a846a800035a51640300c01c4a031a2141002d118952400c1c20400000340103504096000b0002c035251 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 964673345 1250 964672095 964672099
    0x1b010222120b0c190507060605040605100309030e0d051e2a0303040e0103032307030516020a0e0c0720030703080703110a0b040b070c150f1b110624 65
    0x30000080030f40402104883c640070241c401c01c00c402c0d01c03c1c1c00040040e8800705049074140e040c00c50020302820701c0d018a07819942c004080892600c00b0600440003000030002c16010440c1050032480c0c66120000c501e48200d0091003d0985200c40c01903c0f420108a0400d1003250381c00440d003d020300c86c103031840e03c0c0c02e020b24581c0d0300310b802c4810001030318501881d0041380000125000000401d60030200c5184141151555410040c2c1c4690703260301540281700001e8085201008894500c5020f4031240300100d100401d038a21003174aa403204203800c041166082c003c0030f00010800240900107211030312110030111480c80055034100403a850360b10901c030040c095040880d18404050141d1041d0729921042812a5002c501038240709005803030548040e95801541c20102e0041441400c084490540159045016030071081064004180c0d411030040d6440d510b40c0480385001c20f4401e01c41300c0c0c0320150786900700f0341c40482e03000d81420720190108000190808081c010302840c840080c00111f82 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 964674595 1250 964673345 964673363
    0x1061a0304151104030614040c090e1005010905061002070e0720070e070e061303080703050c15100608060a05010810030203011b0906080702100207030909150e012304020f1b01022212 80
    0x102f034540d645803485610024600b00e007088008151054241c1c40b0b18400c00d81110752000c058240b039400d07600e0b202680502400f60341c11b100040c01c11805090441c2138a0040c54141e020380305c9242646040081c0ca07001a22003401140501030100d60011a000756039104880340c52810301c174082d2980c010282803000500a1030049403c2007814015001d1703030840e00184050310006d80d503402c42c58004420444c0c070a000c0300b908200c04540355116800c0140318240207448503a43d9414140195003a0703000502101c14185102d0001c40161820f014034982b2010611308030013000e80d151809811011550421002c10417204108204c4660004201034624071790403006907294186d040454401e00740b5001503a038142082d2411039840340001d900001c0314804078180089036210b8820402c145041c04400e03071035540c1c4143c0c2071068901503004140b941105d09407285003260b0380d0351885011a80d10f1804050b84d50215642000084503082c6d203001e14821254681c8260074960f1403031035100f0301d61000e000500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 964675845 1250 964674595 964674611
    0x10e16080c0915030d0306050910142101140105090f041a0c041d16030506030a02011805150705010b03070303050708090103150f06090801061a0304151104030614040c09 74
    0x10b5201c00c06060f51030090b040e5480b06011300c0000e0040c02152050324003690440c0000b804010b44403141005840300141640032062a00d01001201540d0108100d42072112050200811009110300c04040c8081d00a01a00b50326210400010030030007800300424001540401c000030b00e103c091050428030102081005072911402200309020720b400a00451030741c102080c03518441140e0451085003035026880c1216007424080702075800c2526802d4065000610080042d030103006e1036041319004072150a44c150356040018803441c01d000c1000c100c52400601402480710a0091155808058004041280c03944c1d0f8000d1241c0308044003d885000e010607030150341c0e88280c00c6100c0302e41611402c0d58405450303000b090400e06091003510007080030081c0020326070394180030f0041102d41d0941900020161341c11298105d83c0300800403518052401300d51078048086101d802035246071003880305d45032415458044c040340d941e0b88050724205d046804100c0050801605441616440c45000c0340c040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 964677095 1250 964675845 964675861
    0xf0612090507260304060c110f1f1e03150b03090c04020d1d100e070506070f080c030d06141828050a0506192312030c010e16080c09 58
    0x58443d0051804a0000080020320107520442c1718902900480c1c11400f041440400c111928404c14965500521280762401a11a9500790004280054240354881c800e4139400d0942e0702071540c00e00004249d807440c1100781160200d004001500c1b80002d114074604000742d189030307680c0021040385d1107203400044140e040c0e0103e4000781c402d541000742d204842d02140a01711740352940c0c1e0380c180c0d40861030720040d0f800641001440a0450f00007500c010b203003074215141c54030030700b980800a841c0341008002c140d511303440400047c030b10004500c1c0d0020788581807100c0d1b4480340040c1705600d03118444401d542000b569000708601d80000c5009134004011284001c0242201c4039141c004841c549403034104550201c082d041184241ea088403030f800e60a160700a0040229842c0c0520140543d09101c1c110022100c00c000d003120301002800080b8140035810403900c3c65121a4900f07004d031b5112070340031003000001c000c1c0600303e40700e121015102a0812840c01c0d035031005030100c1881501c1850102e0050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 964678345 1250 964677095 964677149
    0x4030e0f0402070b190b06070f0206090a0f0305030c1501050f010f020c03011112060103021c02071b0308180306065401050405060f190b040f0612090507 67
    0x80d0340e0000c4407442c6460404903104208891036a00c00015051403400308152600030110303102300342e029218407001d10b001c1c1c0901c401b0740c0000c030403203412110b403d102154940c0301a10b024021480344c0011580c44a003054091304214224280945203a10000107208a5480302d800d24001c41c800c0c0f80c070507420548000200d190000c0300c240641c06510344880c3c1440020f82000406280a000c0c40310f10040e1100b40045080f8468000b05000106d6000c480c1004881c081d0000c0117480d0045c2010307201006140c11107505904980d03c11548604005080340c40c1100c189401444003404034040e250601c0d00e00007090a061552401d01186c03411102d48041a1548141d2140c04050890b00e040305011b030310b4020940304501c05580f0b06580c2e6020000503280c03406004651007440301400c04494440c1d03150500034000501303004111107a1805001003024503501014000074109050b440d10020b1611700041c018440302d18001c6a05030406420002081c40010510308485844401c81d60024031400140744c030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 964679595 1250 964678345 964678357
    0x16110109121103100f0606200c12030903120a0e030a08040b1e0c01020703081003031205130609110126152b02040506040216170f030a05160804030e0f0402 68
    0x251501d0024a90760b4019640c6c844020356910381c845404021342490b000d4201308800003010080d42c0858285142428040d4201c0d91800b0f10710212030900407001c00003410b1030304440b01018020404559811200d912807071406201d0380640c0509103425041c0c42d104624803942c002ca6066013000a842624122007000c041d00d00712007007146988500c00e1a004501035404204203074002071403030b0041088110000b1800781141d906894140d544c00401d907210024150041c004586030345003140c1400407580d180642032001d4415400740780c01440c05c1001402031251060400d1b10061000b403080f5680900d00e109613005011a003040d041d00c0c030300c940050103101140d4029040d00840c1088113145040300c00e030b02c0a81d9482140c01707101503600e035400e010880c046d08080e0402c02d8030010343c10003c02d41b158050441d000c6481252443d01d071004070910840e510039514003902d07a980b1001c120310b100b01c2c0c7c0390592003c00d241c5410003681c141510014010001090b801d441181280c0311135651360b03255030450301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 964680845 1250 964679595 964679623
    0x30212180406030f171617040801050a050f0108011103150f061b010f0e0d0f050421051002030708010e150d2f011d060d0216110109121103 61
    0x10041c0c0b28075090745288891344044542d80c2194280e6000789102d00255006241c0401c2107890400300e5032a01e1010900804030b40082da6020000482c50750021f01505100b00c200c5400410703141010304004031011f40c164003060059241c001c2c07007120301900b41d0880b41c10901034100e01012030030b588000b800d801c03c0a681a40d00840006401101c603164a45c1c64030a0780c1d00c54020428a0280c030b00305420b8039103040281400c2d402c64044100083d0203003140c182602c0092501c5414262100040c240e1850350b18a000f01a0000381401010020b0400c1800c0d20707450030050540c01c60514180241089006008018420840c400061440d000780b00d0134151289005250b140091400e0908007040104035088451204440c10702040c42c190f40f4000760f151007410383d11500d0103414052090f00084607501029401107082280454282460003e017044101c42d02040308800081c0c64100e0380b11864400c035905000600404100f2a80c14070080759580d134000c0314681c039a0f4103d5000030700701205807003114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 964682095 1250 964680845 964680851
    0xf0304120507050301180b04140f0f01050604061a07151b03150f0b0c1c0e03060703050123040222080d030207080d020a09030b1306050c070302121804 66
    0x50803240030158104060140c02520b0070076807550140741c245c03210342a000400c8020f03095010b000401c20a589a0f003d40070b09980903800c0100300d41d050416042889000d0030303034451810800f5901080c40740c580c0144040750204000c40ca44a00c0415030090f045c40f0b0030f502c00021880c0c909104000e4001201901001c10420404845040c803110641008401c030000a28201520790002d10900c01242550000c840124840c3d20301012421294042d03074810b00c2c0741c01a1543c0120343e401c62444090994160f440d07036403100c8421300501d86407540c004c1503142018106401001140c0c1504407101000104054801c40401480702140c0648200c02d415121000404203070000881c1703010a2000782c0d000d040540740c0c1040b8802d402c6059000301000501003d000700100c0c000020750754001e04410b403180c00e141120b155242c40300c42a206003114412031440d68400c20004004031407041c25807044076110001e0030f024054070000d40d500700710350701800031002c0013441040550401c3ca03900701080c0028014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 964683345 1250 964682095 964682099
    0xc0a0312021204122f1003063b041502030c16050703020a0915140f100206011a0f072a030303060311120d051c0e010e0708030a05090405090f0304 64
    0xa02d0001340d001c41503c4c00e2100c034515001c03504c0050000c2c10b05091080c0310032400309249041101c0c44043c5e1404000b4540d544000007607190422503034aa0412a002c060041c1000d400310b0761b4030b2924054840b600e104045c20401c0300280c3c40e010072900103184c4001c01a02c90f920600500500d220343c1540c2c540045001030040d08001c00005d11200356442a542200d10384e5580c007421041d0b4042040840c103003c0200010b100c050031a20001502c02c6c001071540b040804003902040907920b1a40b640340068020f240107200f0940310901d0024000200011145010724509a076056401010802044c854601c0c4001104901d40001d0340d0083c5550301c1083c00050b6030345805001001244800c580e4600d0700d11260580c0d02d8012008020040e015024040e0685400c1045906a04c8102c03039407a01004e4800f035140f0300c16544541c40301100803c0001611140c00070683d0324001c0142d1044240d6030041102c14850786d40681036074006c0d0016503000c212926440d10003401d0000c090013440013484003140c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 964684595 1250 964683345 964683359
    0xb09090613032c01031104061209170310090b060f0d0f090203100e07050f06030126010207061a03060c0a1409060c03091302030c1b0a020a030b16020c0a0312021204 72
    0x402c55290403d1700c04111606a101c020842c0740104d00ca0800810359040d117607021131400e80c00c0307031803814449e01100341d8047c1c24904001d55a007064905204e01e00000030705100d140d680307104011102500b1900302e4201840c880ca9044203114807008840f9554030343c08901d810170415000070103d29030080660300403000b12900c8070000d040400000e2414416180d000030305040c1803e000401c40d0014000c5c80c51030f03003070008504a98010346d041d1003111000b600c500481c03003002c0c4040c03e60184034410200d0682c8003d49580c1d0f00c02c91540c855031003600402e0601c00f68000c54022a40d6549803414211100281c03070451044a014595100742c0159001a044405030300101c02030050b01c1c2c3c00c40341840c0e81c09004440004034001201c0c000d0548000300b0000e51440603202014003038070912000c590380c0310f81c0c81d4003081141c03441ba4002c4070049005414071060b59441001e4200c800010320090551010f0310001400a040130301c0041c1800c095641e00c070b01480d200344504007210400e8407400c2e0f5940c0d99808 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 964685845 1250 964684595 964684667
    0x130f050118120201060f0b0a1107120503040608060924030a0204090506011e0f0308070804120c0e090c01080f310512120a0f1b030e010b0909061303 65
    0x50600652074205c001c140c41110b085a030081e40d02e4022040e040112a40b403d4503064618084c1c103006103d00000081c80300c6030290a4108944258041d40c0c4036880c0c000302034048403018061034480c40d07840b070030030010780300100002940112801c40b80c0d0f80403030200040380c00c2030006034010750460308205102c03060000004403c2d040340e00d02052145404280c1c3c800c55145d51160091604a900c0b9003010004035080401034816a070040415500c0c3c00e94030014000e600181c40c1040700c0030340350904200b00c6490340c100e503954001040000f6103d44240703180020012180140302d14200b4090310081682c2d6804000e4102d01410f5040c4e41e040c80c94001242244044c8003003804a400c0d01c5800c4146911420200986030074480b64002c40c10700340c544503600801360803c1085801d0b0341d507556024007a9503040c0c040341c40f03600c106030300c0004890b14580056429a090341c00614010701030442800021400003e0807a40300a054401203203545080ca01150001101d0050200186d055041040002c07149a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 964687095 1250 964685845 964685873
    0x30b101106070e03250f0603050601021203090703080319090318061805012304060c060e0106030c062a08210903190207030209040305030103050f06130f050118 70
    0x28201c1c0c58030354031204220b03a1a28106000768141d0800d1603204000c1e8240012a080c080c0f00d034a0011000d5140c620380015030f4240d9101000180d00e0b2420f000407540c041c064282000c0c600100d85145103801d20001c0c0d40e40c19248030003880018000009058070028106a900d04025088140418611070900501e0320310f2402c01c1000522040700c0c002481030051981440300b0380c1013105c52080300e291070300546491241c0c03451049840c060400e041380007190b0b07000070409083c0e00c0d1078030503030070395142091001c61701c034110004410fa01d890340c1840401d8540900004464852810560b18500c0244100340401d601094110550510040104100c400c4000c4c00280d544180c081011001100c2c20700c044c80301c1541c1c2c2c1c039580e4000700031480c08508401d002081900c85401180c4c800c503a01e80c00702d9480c3c0d04c01c450580000b04040010320421205105109d042c3c00004010099420001030800f10f210680500800510500e811841042020b412986240d9561600c01034000c280e410440224400c10b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 964688345 1250 964687095 964687127
    0x8030f10060e01020607030c0c050105190f0b090a020a05130e0412030c2312090120030408030a0915020712031503050304030206070515251b060c030b10 67
    0x41000803400c9807080352000ca800c0b10507070081038035845881058000b4418020385204009803d04840c02103070b003d010701405040031084000c61080e50f94151401c8420410341d0240003070800004400c15075900c2c808503040402e060300103a451021000545091281181b0051103188250340000c0940030340c129280700758050070004180c5034110030100c007110003000b0b0410114414400c009002d21800d100c40c1e140c4615500b142e40303060442c04a0410540302241c1e03189942c2e4481440d0500800748010740455844006069419402e0a0f5034442d2507000040c01d143c2c0640c1d8410520043c01200408074051b0001c04a00310341e03070710319411300400d104594041c510101e41404030000c004180c1010100840b40c1000145041a0640c0d01300304041d40601c100b6030740d52040405a00c403258006032401e004248550340c101551440d114000c9800d01d42105440a03c60000030040c064040c90740c14450f000c0e07120703100203a10740c20030b00180e005203a401d0740642c210842c00c011007901500400020415002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 964689595 1250 964688345 964688371
    0x9071d19050105061206040b06070506060a0602030415030b040f14040b1501050a050c161d0a0605091302191e0e0c090d03090302132f090d03050708030f 67
    0x100e40010250350007842419007191080200402185d410000260000c000400104030040d108000a0894002c01c105982d43e070003800501c00140341004c2ca2200601d40303030001d9420700f0f2404a107a0100c2e5510580b0b0414184c40380e00c07070b400304c2e0360703075805008500116401002580d1490707218554519080764110350480109002c01c62032401c03101e0121981905a44451800c25440c904983c01d80203030302214054404d03900802c02c0c0381d07603c19440014083c0c40841c1c844c0d00801c0d0f20740352003d04014146c03182d00c6207000c2c414011900c6089d40f060380503c0301411148c103001580f01280708008146507000b17021082c0d10010901c1c56042548150400c01620188011504d4100500d0394110682c6c10ba141c3c01d00070080601542460080d081d01c680c000d04000c0d203090350326004a244400c0400c81c1c509029958a080c0c194600c00340c00d0303529105d4541190b40002c002c602c40100303643c4901201311344148044041c1d9800c051044045a40d169030204225440341092002c0c504030800036030f119180020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 964690845 1250 964689595 964689631
    0x3010506120303071407080313050d031a0f060c07140f010305060303340b0a05090609060a27050307030e09130210030b1c0507050616060509071d 64
    0x40e19075003030100148008051451501d0300b007820307640010140440c82e00d2400034040d0b0000f2548041c0a5845020480d0500341440e540d032400500703010410b919181818600f032407031403801c120544e07041d042210070380700040803802000004516002e9101c2000082c0b18102010440301043c07140880603001c2a1516000d401070715005409854080390321541551060120350724101d980c07580400e141a03e00c44046035100384110440c0c030030100240540d52511302c00c0c02d200c0f13401c1c0b2600c902988120442c001e0046400c10b07481c07294403800050000554a920780d00c8502490110703000240c05100c1006901c0e840070803e00e00f130782d2039800180051b00800c1ca11403011101c1d04000844504c2030000c8072801801200550070042203030720f003e03512020190340d10380c411803036201c007070b1841c031580381d02c03482d008034145540b030407501c3c0c60b9064001600404c1c0602040505014940c50030b1016070748801c01094958448408618046180d400010b018400882c001f0b07107114010070b90f070b001e101c07541d8040e14682 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 964692095 1250 964690845 964690849
    0xb030609071a0307110a030201150504110a1103250209070206190c0203121314012016081c0f0207020622032405010504090b06090907090609060503010506 68
    0x801148108042070340d411100c4030340007080b48011603000b500c0d41048039101503102003140c03501c5155203040300540e643c1c0c1e4459007550414100600201000c4806004440002044004900540c1a001d091040d03800d1410100d01c41481903c1000c244d028407046500c015411040a00e04554400d074000c076000c2c0c02160000c4c0c404034106208038040c891652910100c0e05000b0b0042011000440c118003081c0000c1018045503807089020300000f0900740720205082c00c05800000c42202c00000c03da240400a4045d142c9062480e00308a06040c185511040c1208802d00e414466007002030a8900004052281d14104000c0003035503001d5190030051118055200001ca11500314043c2d400300c014043c0120107900c0c0d64007a4041c411070b8030305805142c1c0c0d07a920b64803402912203680903600348034079150040721228401c03a030040404070307030500c60000c4a48078941c45c40c201408070341c090541c440c00106030302c0c020407007040107008a8608010701541e424000004101d07900170588070b94200750100d41c0d98 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 964693345 1250 964692095 964692103
    0x1e0f0504031e12060e090d030606080705071505040b10090905070939021b0d06020304080f0c01050421080114031f2c19030c0f060b030609 61
    0x40da03815102c00b14030780000381c0b11100e400c1c02c00701c0401c200108103115071541d8650b4050000144112035082000e8141080002d0601c0d9a01c042c010030146468410010251f01c05420780e001041ba00704281d990003141480010060543c41d9110250b09020a0204210a034030300d00740300306c181c00e00070b01400c2c3c5c0380c1c00d04c80107841d074121007d0103650041d50284034042040d40300d0400c42d10300c1c0c0c80d030f484190400c0e40c5000000540c00c81e52400c8840724042d0041d8190144100c051500e042d01c000b0310b41d0802c80e400980a840e9601003e030030301d0780c04000602041214000c40e48107a285100c1c103903e5801c0000b955000c0c0000701c0d802c882603402c00502c0c1000a00041040303140c4c0308242c54121541e070814079242c44100004040c694540304c3c00e00000391015194418000b1006040c0c0007045102d00211200d6824103c0050030114104040440304020000308035242c44a19540421121210500f001c81e19803801c202c02410344c010080144040202540c480e03141c0c00c4050303090b01e00c1584c03041d400c2030311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 964694595 1250 964693345 964693351
    0x80312010f080a0f02060f0403060515091006140c15040f0507120b060415050d030804050c0307080a0f0201031d1b0910271d0f070f030803041103011e0f05 68
    0x4d20110800030b40051811070040c0c40c2070424031f0b4246060947d680c40c1d18041e0390055402000c201c0c504807400d220760805100c03056001c204d896039015401c0c68100020b20314102c072054007003052804905e180703080c0420302a407848601c05100321b00090820781488078a000c2501c8003101d507446910000164505096124600540c1020344165180c0d01c100500001d0280e55050701820041048007045603521240082000ca020350384900742d038900340c50300070300c0c09000d07045452080d400041c080101e441d0000302c0c0300b40c295000b00c1c101d489419a01c01a4090080c904a185401000b0865864401c10020b680000119807041c040c1c1050744ea02c050003603d00054900d101d0304041118103201084114a00078625040980c211070301c2d20955411400b25141e510282100b50103546c803180003040b0420110500c01d0780d05000c0c2801c0d5180c40c020700d02d222014803008090103000310000c0c09109000196050018001c0c00071f01840c5130210005440c07040c44031080e91181d1034500311115103800c0e4800c1c144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 964695845 1250 964694595 964694603
    0x150c10020a2715110718140f06220e0a06022d090d031103070318170a1e050f030301061d06031521070f0605071a10080312010f080a 58
    0x241440c0c0c0c00c3c60803900000030880d141000d105e100c60014107040310030003c50030300a8102000400081c14460448002d40140c120f00e0000c0912007402100d076225802004000801060f40800015000014001e8440c51480b80d4140c01040c1014051059a170005d0030195903001030002e5002d100801e800307401c00d1510040ca40d554085c842c000190900b502c03c02c0c4802d00904144c000410042010381c51680f03d1007003140002c401c0900c81d0300301454185604080d08040c4021180356400c503006030781c0c0c0d044d1088003420788040031845580d1140e100358a040c400d078200084d00d400b1103c2c2141d0a03079a91080c8a048001501980030b20341c00c0a015420240d002e200800140c60343d201c04070081e4080c000c14080540c4007111529200c0e964291340400c0c0d400010701000b0f04903185c5030015800040400d54400300038841d0030090034000900c0e002e2540c0c294081c0b4080040c00e502c4840801071000ca40b5003160b04223110008200031078400413503100d4101c500e25080310151944403134181d5103078400500014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 964697095 1250 964695845 964695869
    0x1d070e062e0e0a0b16060b12031801111c080903160b04060b0d0b060103110c0d030c050c071d0105030d09060e0d02040513020301050a0b150c10020a27 66
    0x601000c1c4221103005880000400340b840c0346491305560541540701006001c03804240c03955500802509000c2c0c1801401c00b04c6a00c1030110b210f20486880307108100b4140d80104e03e101c1840c21036800303a885517140364402021500034080300b01d046a0369103420011200452910000601c00b06800021104030362807110b50007220005940c0d6055041030040c2c01200e066459942080842e16041000100c1c507002d4850a521800d01740000341c01c65a8202d20070a001c8000c11120300310000000c0c241d002101c06e0328000420030007101044030340c0d0180743c9001680380140040011110110300c000e9011401d08a003015050341e030791041603911000c117131842d4045402c900003001030900944800d18166405403480c1144031b12980010221441210015003070000b1209090640c2800d200d165400710180c2d400300205800000040c4034903070595842041d0641c0000d0f808480d0f0018400002da0720006502551a030407000000780500119030760301806140c3c0079110024002488c01c0d044c080740c42c035500c0e117 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 964698345 1250 964697095 964697179
    0x311010507320a0c0b0c04031a040204110c0a0204110313080310080a121706031e0109050607090602060f0103150207021906200313091d070e06 63
    0x186403000004450b01c20041c9105600d204003520364000b8070110f007043d5a0040300759260303d88403c00c840003801c0314892803400d0000b800060060a020207491490280045080da59840018003500c41c24070a42000c6001141e0480d0b1a240024800070702e9100700c900740b1507841c150742050b07070a0004541c4618000d800b40e03e040f021504441c0110f801410020440a40365116042e1516102404c90200d410078400c20b0076461703c0c0d45c0210110b94802d0b28140c5081b11781481c000103035840c00880702150203400c40c902068083c9409500210a80c3d40c014103a074418540b180c2c0c042c244640a01c981d2026014480014843c0140c440c80b081c10381c0c0d4400c03000541c04054500b0720f402500070a00482c0c000c4400206844845064480c01006003c9551120541d0107003046060034a81010300c514607641c024060164015a205202400e844203810009a803c0d03038080c0181c01d200c0d80d0011402c0303c2c0601d0034049180700709201c03a03600c9500c0944a64544402000d0ac544280503810712640e036000c940540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 964699595 1250 964698345 964698377
    0x201030507112514030a030513030b1305010b0334090218010315080c0405070e06030f043011100e030304020f0102012c100e0105040311010507 63
    0x1115400100602d0181400340ca03020600e4074043d12002c00440c0700100e0403040011101c0a1084806041c600400103c0000e070388011a0f6030358008100181802408107054039104c1c8080001401590459182d1240341415020b0040410310004103451035400c0003404501411b001a50800a0b43c0b01002e00144401c40d10804480740c030165202034080107000c800040410190000d011012030928100c48400080e00001d0201d400d400c071490500504500100100c0501141c15003e0101c01d982c04685542d40c508101c6402ca500e4074140d5103c1400702c1842010380310b521919224900c5842e0711070500c06500301c40c00100744c00f42075400a82e0030003100d0b460002d01c200710003d03200400d0070031500b00c41c0e01c3d1b20b030071000ea800b0110000304031760002c8204015498445076544c80260280020400324251101c03425840e4101452502d807118054528200c1660810544684464030402005078114600e080d074040d00c3c1c1034506031f00103120344240303104455044c490130b8014146511248548041410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 964700845 1250 964699595 964699601
    0x60619120602120a0518060c04030b06240c0d080415020c1e1516080f090304150503150301060501080106030c030204080106170f070602030406120902030a0602040504060501030216020103 82
    0xa02110416000e000c0c02d0204000e030402c00303001c0c6400d4240402c01b86410100440350f06406c0f083c0c5250b6911103030038005600607034070890b030540f074005442030041e076903210116406c0d00042540c11004520f44e800ca050204210300540884000c540556451801d041c50460b08960252000303400f560240c00c00034010380e8168005c0201010207029542e0b0007482101a0340d040307042e44107114842d001424510100d105040b5801c1e40040240c00900411140f4003004054550003801040450b440ca030100f004481c0030015a0002e152101483d403640d8628440105140c0040d540104460780d0302c00f2034012407070107011307030010344506a440024507071070b011044025041161b0350a09043e408c02011540308428041d84010f04001c4003500e101c008401c05191403d850324031041c0c5147c00a0b04284000d41c2d01004072421030310180381040410b008480d450300180400003000350305218000e21501001150340241c01100c0086800f0010603698a0066040e8494091544007e52500301c2e940c0066000364 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 964702095 1250 964700845 964700879
    0x10501020d030b0f130204090c02030f0d18080a030623090a111204080909090304080604080703200609070b0705070b0f04030203101b0306030305161104061403060619 73
    0x1c0c02d610584c6403100c0420545514031003954041600010148100321b00360180a070100d40c2d610007145050b45100c1c400c00c01c1c0c0207002906400c581c0317404803032460003010b040100300250403201c207035501c109101e409001800c01b071180100000043d60750005180c031080c1b800d044104041c290351110795850041c0d034000c100101070040300c080c0a21000e146481000700d99481284111035040d9504018070402141c0c240c0106a100310764400c000a101044d4081766441d001980002d00039101c800d64641079039148807003c2c0540b41c01d0360340120300c22080b90000b54a80100c0c1d06506407915983c50325110380542c42002c00c090000e40c0701039020000707080340c0c000410280101d02c40890074a902c0f40d000908050f020102002c245440c0e075003203201d05002c2c04407040c04600906040050714170b180e50103810b40c000c00400041100e840b151440500021b00301051f86040000c00410945448511000709082d8070845540603100711400a141c130308103110004180c80f1101da81d00c148070703c0c10222440e210440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 964703345 1250 964702095 964702099
    0x90103030f080a021b1f0615080601020a060c0818010e03091201090f08070b010f0f050f0109031403070c0b0a140d02131d090715050c0f03030a05071403010501020d030b 74
    0x30070801c3c2203251480d00001105c2c02d400d0250000d6503405c00075880141c14004d8520f840b514040013046907100c070000720240383c1c0d8642022203096a550005034100f1001c54030180645041c00b101d03022442e07011103641e214051000750101111511071071079088614036441c460301035000708100178a030710304052205e2101a8400c0042043c2505070f445400e0980d03100011a030b0300a000c40c0c0c070030801ca00d140100707000d032000c40ba120b2180e51401c024203885030107502c2803e000e0300090320402c0181e4492070608019640040501b002d0b030f2803003a400b6940f0f601402043e6141501484c01040d0b60026074202d550f072900594450116030700d0040d84040c5903000314004008103500304a0700c48010700d80d6103080d00038142e0a159001d418508040702040c4a0020309200705a044045d0a012202c41548162101003030740c9007550f00c592021000500c5c0c075114032040c5002d0f10011081110415503034012600c00c098698030901410394007860385516000a0007268003503082400140b07c01ca1003035001504075000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 964704595 1250 964703345 964703347
    0x2105060714091908030a08060a0b1c020f070f08030109110702152a03030a060806130803090a05100b030f061006050304151d070f0b04090b041e020414090103030f080a02 74
    0x92416428174640c403440480000c42c1c0110f00b0000249040c205060003015004c2a0a141c418140d82c0d01c0784544c0c0c02112800500d0b40815810b002030082d00c266003d0302e6015141101c02c1c000c80c244801c584d0400d100384556503041903040b066105141081e80c02043e40601800100074013030f1807001454100601c404122060b04950915070f04244d0321b40c4072000451400385540e410660240301c02d44902e0f03002406194003030428441551a80000c1005070388d0044482910b035221502c04078103000c0102e0003d4460320030184030901d000180c1c0d0141e114454100c0456080382c0740790301101e448501c121200703000d4880588040000703038003c9004503030007441040d264254200030b40349581103460700c07100d02c8001020705d042c801c4940b1080124802604000ca00c0c982c4c40c03440c0864100c004c0c031860040b425115240e0389400d800b034955401400c402e501c8840a00681035980442070001c1d040340c441c0b80c0f2003803c2901612101e0501c0d0f0b039400d0580341c059030f500400180035501503130721201c042c0c990030080e54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 964705845 1250 964704595 964704599
    0x9070f1d0a23070e01080103121101060b1c240311060d0c0e040f050114060c0705040203011d0109051303180305030406170a0209061b0721050607140919 67
    0x200c0400030b00c10500081d01d001880342042e82000b008600b903490700318140700340d4500620118004580c0030188400501c0c00c0d481e05032402c0d600034050169540010540c000c08252640c54542640c0c0b145024250140c080146913a03a003100c1d030a0825514425003041c18214060003c00e80c1c1d001c4000d030000d00a00301381c0c500820750710354000315030103168408005440c43d01c1e01c01c204c0c60b003401080784400101038148240c4d4140302c0e501d50706040f4000d04902c50880094460f00207030017400003e0040ca00104115140d41c0d4429203014001c0c0e803a04035460701c101007400441c03409454401c0c41c1c0194800c86121401c020b6a03501501d4071000108182c0c2ca0396011000080040c000300018805418656903a0528117150102000f2220003d4070404e1003a0043c0002d4102c2e49508054130780062038020008481018010614140a0ba81c0c003c601c20f4040c02800111101c8281e5030092018800c0040302c040303079209501185e4580d0391800707a00203420b041041ca900341c94a801c030b00e0342040c40d492014828035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 964707095 1250 964705845 964705871
    0x5090609100f0e0106021e1c260613021905030405100c020c03010c140906222304090b1f081006060212120a020f071a09070f1d0a 57
    0x202160f0320482c0000350803030041c404158180641c01c4d002107040e42000500008030441502c403000030744211041b0b0b4001c080d80021a100e120128040030f607803010100401139500016107850000c4403454011076103115a025140403500c21a000d0140306000790422a208800841d5660301c00790041e9000e10800000103031104403071050708403548003500180104507800c024142034418007100b602c18401400c0702a151403d62804503110a001100c405954503603c0c80380048502080c09a00080540c80c03002040f034049500c20002c68650f8451488040d0720b03003000304000d80c1d055000060490b9001c0740411000401c0884180000d410086241010750300c40b5401032500034242d002421460315660100401c1b13405002000d9010390401c10355140c00f400038042c1980c0000605000e0140c2e50010300c0f28083d41a10017616841a80729059000c9280b030140d45c8240b1400940e00140b041c02000000584a500340c0411012100c0b0480305141c00704d001c101c0d400e00c0010003040c101041c0d4551414640407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 964708345 1250 964707095 964707119
    0x1b0301061409180105040e0705060910020f0a0b0901060b04051f0e030307060209090a09020904080702030c120109051c090311060d0501150311180405091606030204140a0509060910 79
    0x410b42c80114030f0158034150800c01a40d0540700c40340d1854110300e07424042610350310101c3d00d186c107040c0ca400b044031007840c00032032801c3d40b40c040540c681e000c1d0302c0b880003c0050f908041e40c01994440000c1c449242c80d068001c6d4036104601c2200d81c03110000051841003940d400440c64040054100f000343d250304080841d0031a8001803048408590000b004401403410400b4640c01916041c4204103110490b0b02244107103001900240c5014004280c3e0f00842d60108019022180044c0116014085003c1d21a0103404250f401722039030300408541000850752038103401076441440c1d90380030026181d03840710203110000d00703c1d164206000300402a503007980750107000e00070580c549508541d50b0503014000c1c00c4170140403c084903010b003080440c0311040b00c2900d8441e10700c401c0714002210348500d06003914045803507c048601742c8124000144140e0558080c20032203411a0101c1c00e0302c8101420080704110500442e83c0c00142880441d40f1801c0040c3c11560205405c0070090300c150b1101d15080c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 964709595 1250 964708345 964708369
    0x19090c080a02010908070503150c3f040302060a0c03060f0f0317030408031602031b0304050406050a030b0106051e0c0c0117130b0703090c08060403081b0301061409 72
    0x3160320580036038046580c48801a4000d004400c0504100f6090000081d251010302861400708401c00001c46c034030620040464545c441500004c8180c1d080c098403403e03840100e00403c031101a09051800034a40300c51040c10700c40e90745540038150b99560100780e1002000d43c5401c4408040d40d03400301150340615881000003420405904004240ca1460903005030380140d10748400302181401400005410703401038070380045d00a901756207000c400030400c82c035501642c100203242165408440300403900100c010029144107072804d001c056111000d200190113a80b000030924600900100503140c400c0001c3c0a8002c0c0005181e0740203180483d030800c1c1d541141d4204e03e400d070400e00b1080255a04040f2421040d603141040d81150303d0401050880c0ca1017400010b02208080350000d50700074429405118500d0f400300708000420344424400c0e80d2201c00302d42c00c0b80801c10000100d0401041c40204011070012515514517580c2450001c64100302003078180302ca1381105100841d41956040b1071008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 964710845 1250 964709595 964709609
    0x1f11120c1207050f030105060a030906020310050901062c0f090a0624021509010609020705100c08101203020a14030c010b0609030c1912050a060f060e19090c 69
    0x1031030310851580c000c0c1140002e0302c02414400100069040b10b07600a0540b411150129103150311058003040540c040c0c0350072400101300074400404c00c85024060b01c0400c050713a009541c06a041ea07203458003625600252403881580405411849140a03500030040c43c2071600580300e00142480400456290320066034050002900c440050068443c00c20003000000100b9500c030005440c542d001a450345001c4c40001c45030288280019800300c1d094005000400d0702c2a4119950401070501940710039000c000128403d040c83d84100190384208541360040000c220b80201c80d030700e401c4c442d280c0504050400c509500580362404085100665100c05071044400070316038402d8400700184c00c4410509007144070b003105201c14410340c0c0f0001442018072005031203401075400000d0034030151400f55849100003855603c40c00040090100d00e080185106180034012104c11941c460186c5286001c0c3e060603101c0c0000055152090038002e4240003c0e0b0030300028101d21030f442d800307030003413080e00645 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 964712095 1250 964710845 964710847
    0x120918010303020a33020d06081015080a02060427050c180316260d02010c080f0c030417090d0506150607170a0207081504020405091f11120c 62
    0x148500752041d0503080801a900c81503444410717403083c90f00c02c2000504c1c070f160380c2d0228201b40d04140707981c40f40020309440f2086071100044a40c0c1c48000d0b00003108000d1905440b5000001e4020300003407058006503004042d1403e142c03c22015480d0294030f1512401c540742520354024150300c040c41030600405a461040f41c3d03030a164940b5a8010060103041d03400303940460f094040c204a07001e4000d0039640c501c826a40580c0755801c0702c400c00341c25290840d416004500040c0c96040c0c0550081002602a84441e0302554078050035046001e8122030845164500b000007074005512013185410304481c0030711086c00c2285480120b00900c41c40b280c103c445074031140900281c442207000700014135a04a618074607042503030790764800360111103104010604021071040c0e0071340d00030f10000000c0d02c90b0a01b00d5190041c1e10070342c0b82da105420b82d0140e002d01e15000105200180200d40b10740c04001030180180c9407a2048403940040c02221542001e5041c10301c49459019a05286507010300304058100e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 964713345 1250 964712095 964712113
    0xf1603030b180702062406030f04050d090303020a030f17100f050409050703061d03030c25260f07030309120c2001090905190e010e12091801030302 65
    0x4028036000c10200d2440000340c0d070007080f65003540021055800800180d05c0c0111551040704009038008400325a070f88640301000b0000b5038030074910142e100f28020000c1781c15500d02c0b110103903202d614a000280c01a00701981d8140801e010380410980e0741d41030f2902d80d1860120000480800a00391496880c02070320442c1001503030044950f800c003521007120104146600c43c0c1e24550b40309514071008118035200c4d00071483c51155a05502170541c56501545d5032464005050384403940b000e083d00c7c22489810803180c1e49030340c0b0511014801c03940022107440800900321070701c4248454a032500982c03c0d04003e501c241004003005041a0380c4641c401243e8185d052810f1412a07010541a604100c0410840804a090b08070218410f1004002c050b02d1401420012140f4580513040308100c0703402d050611002d90306a40b01d20141d4a0054020003518043e840001c1c20b0780d1128081c1001c1d0343c041885c525034648001e0080120f2000100f01c005c6a180b01c01d4447c101c03007404da1082d00560040303445 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 964714595 1250 964713345 964713349
    0x3041701090b1b0d0b06040302120f0105090d1718030a02010903091d062202030114031501180c02010b03010926090604030305070312110d060b1c020f1603030b 70
    0x50702d50444111164400c045030031000e520010f018140e406081103071550b00807500390711800d040f10051a0080d040d001c0030b00c242d4849a0380c41c420184200748941c6000001600c0781000301c0c40c84102a125600c6c400401c14540c00419803c402502490700c0002c40381c1c0200942c5800c000600946400e90004030f054603490802410307025040c1c2c0420616480304c0b024110443e241240c032a8000030031224009410450b094811243c00a444250f0401d8800400401c2d4825a64400c0300340040440c2100c043c0400e000421150450030b204400514842d030708808190f40640d00b0004084216100000396401940002070943e0801101603804903036185090002c60582e2200544800b6281011403030039920002003400d51082e44809001c120000c50030700100340c41420106520800b044084c80314504001190f2030300d9000368081c5010b2031810b440007030122124025212451540d41c0121804141ba680b258060741c080030340c6c00ea19a80401c80781c140400034401110100b4081d940025906460f001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 964715845 1250 964714595 964714613
    0x50f07081605040506060409151e0e070e090105121207060c0306061107060302180d0606140f0a03141e0705181603090809060403080d06090603081204050304170109 72
    0x143c0210f04000402c40543c903400c00316000c507619030100081c629a462031001d4000d0864001d40d0851204d02d180410000780c034541801951600d03c08a882c40e1206481030703403108000003e40340c00554040041000d4a450144a02d941014400340e071015001c120150703d5607481180100c581075941d8a04805259051043d2005040c01d4180401c4100302260201d658001c0c41c030401d0f0405400043c0c2d0f034034818003900540f100310350207407080004090524050380501030300c1c0194110b001c640407201c1c0f000e151443c2e4541000101902c0035200508548800070406062110522742d8840d141c3c240d141140c0410440941d1348a25002c1d000160400d0100324142c0a10803000c030050b01c00d50188468000003a1a07074103120b1701070600144403642403511140c14010103443c203501400104001081c81a9140100182c1e4180e0038100861358892041d0b80481d82d0900001d400d00c1824000b03c040b0526540ea015000340c094412a804d00d96140034181c001c03250ba0801c00c040d651544981400c1080da15 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 964717095 1250 964715845 964715849
    0x1104090f140304031515050a0803072021011b0f020c0402032413050a02220803030610050c120406180b03070e0103020d0911030d02010615050304050f070816 69
    0x1c0c61070a0302d540c4071074000410045900303499607a03800403070400710b2100f00c1c0f0300007e0001405003a0303d160746511050312500580803c1e40d103103003a074040c001d0520030403541da1098880180300034030407240c039040302c4000c07a091803140c201596604e1243d03040841b010f81401c4d22120640e90040c00300304454000342403c09117031400b0b0055005006007c0310b000301c01641c03001c410410305010401c080e1007001860074240904000f603420700c2d083c00d1000001a9030001d2481c0081b511040607910700c01c500f401070604841c410814141c01c10b00c0800d03070310700c0c150340c89007411181c9241c01414820088040380c18030b019100ea080152900190800000f9008032030500741c00000499071707030007070301d84260b14040d48001000002000000c2c00000034030fa02a6041d2150300008180c204070024071403800c201003418140325180b19110303100d11403101c140b0500802d070a4074100611401050dc2d8940c00381d6854102030300880309409a041c2071209440c003084941e00a008580090850189034000022401c42e26 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 964718345 1250 964717095 964717133
    0x20904060f180504050d0e0f0901081e0703050613150606120c03140720060c04030201020c2d151210060f0903021917010e06311104090f 60
    0x400f00f0803002c1000414120041105810b2800c008010140020482c0c20803181d41580103484600114403c0c00000d1074660040138211490a8020140380350340ea100e11031300c0000e045500c00d0000540b13070322107080000c400900c00d080441181c00b1101c08401235031803030b8001d5400a40012000d0721b0001550050807070494079030408001c02d05551540c052141c1c030040100040c420664401c0c503004420f0303048150380201081c05e5503e14184600d15042070340c4240700907801403003074031442c842500d02001c11106000180000c1e684000386204004004006119420b5000004440c005040c51124000340207000000c0304980302440e0400c2a043d810b0000d400900400c5480304084100d1604510004144c94045a10109148600c2c080c41880c020355002844484194041d5101844054119440f40942c4905451413961807491040414110349100310000401e00c4861603050701c0034101c1100039010381c01d454022070048000c641030320104c035400c40e07110380e00245400a002c1e104141182603190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964719595 1250 964718345 964718351
    0x81903020d0504052413060320031006030f0b06042603031302010c0206070515040629010e040f3215130b1c05010e0727020904060f18 59
    0x2008045030120181c0e4003d2011250400352150100c42075600b905c00c400030004111046da0346801c2c00601424880416003076202c841d5100b4061910300b03e007920300c01d007420808080b03a5460058110301600e00c0242a40102e55500025805903e4600007400545004145000c452007259036034014410703507007107010964005009008106176071300d0685032966024030704a81e44c80d449000240c1d040c0b0420744010418800c444004c60b1a0110f0105148103078040d25040091240380e0008101e40d40c01909800e030014082c2031044210f40c018001d4490070040940300141e02021144017008850343c142c107540c2d1800b442d001c04510014a4840c104045d502840c035454103040490521102244030564184a11007003100304860401c2c9501400450000528210428200303800c0404400c00401050302e00e5400c0c0280c030311480c6c0c0700003200d40446111600e40141109182902e181120618002107121602080b0240c000d6842c1e029010113041031119a102261411a11501d1100351810005240d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964720845 1250 964719595 964719599
    0x120c0818091311010c141c260103170d05070206091603080904110f0f130501030e210c0639030c070305040306180302070b07200406081903020d0504 65
    0x451003e5540d1038a00a00713011681c0e81d4030b860300f115001180003d18120f845a03010010083c5201074020051b0411500c914100d003920014911032061102050402001100f004100080b0721035907a5540c100c88580040c103100c40c0030300c1402a02c406445140041e032142c014040c2c410720074000c482030344d4103980144954030320310344e180c1c0e0240c0210061f080c440c1d42d03515035111140100208643d050400703019819a02c5030409103542c2d00e03800044107140710000011012455500034819419113401180c010508411010490b070b004607296405a51981c0003400b03445100c903c00c01c0590302601e145602681e810168445001e03502c90244072100a151080301200c000e40e80640031243c110250010050ba42c90340c6007405d0340c41388141e910007084140380c5105d107040e020700c00010301819807296090780c0c00684d072a60742d403941d03000da818090030b40e4517070004d42c103c07000c680703086142c010030080e001165495407581410305050109070a480313078840310151841056818081189054680d04045007054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964722095 1250 964720845 964720853
    0x31e0501050906010e101a0f0408030a05031e070804020d02010e100e090a0203160e06070c0311090702120d02130f030c0806130c030305161b0905060402030403020604120c08180913 79
    0x790200700e003a10802400134688e0204503c200c221009040440103c0307903900c0140400405a91084034003603601904130280300b043e0010103010a0144401350b071070100300d03180c580800c20070440c00e440c22411303c81300c1c41250304240c490340c0440c10b42044548996403202000014050003a4008110402d003d00c10410000c0d001034100020380295240e14140c0fa10780202408104e0600c22020080c101c041070100c00010040e480e5180c4405900640700440a5200c7d0441030340c1c0d406002c07110951040f03040c0505a008841507014082d00122480d41000d040c0c1c0d1000c05451340d0940360401d4580710b200700c0c0148641e0900b000032507004035201198640701070241d203c940042c00d036800000c1c2004030004502c815000365410003050301c1c0e0040c580f10903221004610089aa180348503250f59242030100007075a518152084d80e1060317405070060003641c0d40d25640c0380c0c4800201884142800710000b440c1001c290600302503d280c0c98007510440303900322080200000024002c08030300d0a00110980e0100107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964723345 1250 964722095 964722119
    0x80c071a100b130303030f1109011202070c060e1e1311220614031e0403142205030f121b0a060f05180601031e0501050906010e10 57
    0xa0503849105942544500c8450040144203500c618030010000c202aa101c1c24a020b100f81101c2c401e440420040420045010558030840842c0d400c182c401d109140c1a940192130b041c1c04040c04507070040c40c207892603561141c01042d40d0000300004010054241d141e0400400405c207441d21001c1c1280d4840e82400011102088924040c4003161a884400540c0307001605540400300c0400c40300080da90300d404001010041c42c480c12002030b503002c00c00c4051038441ea04030b07070049802c1240c4100e956500d407604800c41c00098000c40400044603c00141c25038241d0290035010705124041307840030b44a030000c01300d0b016550031640c40703900200d4000d50620000a00640013014144076140c076140707540201740401101c4502d040d00c9009140c0d044041103400d074005017000201c0c0100b0081c40e200d212481d008da40c101840c0d0442c83e4004801400820800c0304051580d0700c81103421070303282c1e0132a0360300c03030070b403170060700c1d810201d6000b0401030280d0415a150260310607040000c844003135141000072800c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964724595 1250 964723345 964723373
    0xb0105120715030b030f0f100c080c0711060d152c0604060807060201150b07150905070302060c030901201504020f0d200303090a05010f0c14010c080c07 67
    0x8200c0e418000b0402c5240a038005200c40036009003a2401010b404803620b4907a900b0130b00c211004d0181e0714990907490b0302c600c02d002c030100c3c999031481d0580d5154103c0703a4460f80151801d940444d01a4913002ea90b94611000f0015600b0030031000c00c4000f03044180c803000d80c000e50046075000790400035200d1110f6540208515403103501c4d02d03d090079101c410101e8000c10140d008000c81e4020071001158035501500117900c4030507010704c403201e0b031951628040b046005007240146000b400003100d12400c0103036048034607a9802641034404007a581d90009030750354407a25034110705800208500c4280d60f0000541e040e042000070101c10b070744500403c00740c2c9800c0005009001403000300301040a54444081042c1750400c003401070207404250b0704102076003e85010708e148600440c1c1e04900d0305401e001c4251381c00120f000d0424a041c9041c40015104003051030802c0342000742000707154010901d80e001c00040021258000140c2140d400300040ca150401040e0b0701c5031110412003800002e00c007018080c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964725845 1250 964724595 964724609
    0x3010b0c0d1707120e010203090109020901050a0b03011a0d060f140109032109090c031b09120803061f0905030c0103060b031b0c0105070206071704050c011d0a03050a0b01051207 78
    0x10451051804100c010858021703410250f602c08000c0110b2010150300c88002d01d4021680700c68260fa885080240302074080c05065039922080c07004110144100d221908048080403000e41800348414000c81119859400301d50f291041180800c82001c501010480c50720081c40e20700601821616094141040d0400342038540380001e01c044846131103a007405010703008d0510b041c0404040e400c0003c002e0305421017203031030343d0040751100010140a00d000340c0c103e84480d18860b80b0300c5080c3d210311030b9940000b0803540d0800340036010342d10b201510744100f0307012000342d4852401c46410702041c1031600005103807140c1031514040c1c0c14001204094256940580074001400c0002134003441140e007401680c00c000744d29801d1405010900e81c020400ca0722440c0b0b036564031000d40e59400d42c1c0c0b90041c40241c901a002d600000c80c140c859510803a5801c040707021172a116002c00c1c00d02c07404900c0d0007038198401d5505800c2074042400b003240c5400b0b00c40c01004201e400940b441c0d4803040c01a1203448901c1510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964727095 1250 964725845 964725857
    0x30a050c0c06010b0f040f17160806130618050d0f020106030807110d0209180d050a0512180a0c080d030209090f060406030204230f070c0311011103010b0c0d1707 71
    0x8110303081c100c01b140d025104140d40c40615540e40c401190b4002d08400712211035010b1007207400b4104480510840c1100e05000042c07400307031140c0400a032a00c10b202415a031660326074404090030390404584210161180000784041740100d2001042034424107555411a410020308002140001701510001074001c60152040e01d8902e000030103001d16004001c1d0009613400030083d00c00b4140c502003c01d18a1030701a540c81c20620141100c2e244140c0f100f10700441d41c14444a2901078480804681c000030006007408400b489070402840c00201c07407021945105400c40c240304030401401300c001c0280d1141400e6007440369203000a007801d48002d19590310074405000040c019543d6030050401503070003410800002d200421107a9081305c0071500c2e0103022a40c0f4006c18200d00c100034280c0d1141c81c065550211401e10795070100d404d0010310a96425039902c0d98820410109044019802030080c40c49407a40c41566507038075800c14003009030010034804405140161040044880d5501c10340c5890b000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964728345 1250 964727095 964727107
    0x2010c0903021512090f060604020423010908122205011e1b030f1d03060a09060b12010902131506030504050115060801050f120a030f0207080a08030a050c0c06010b 72
    0x4003521380100d03106100910301250a0199030b60b00880e0080c4880a2982640c81c80e40d00e110a0000344c5c8190b1042c480750f0072218008180200140515000c4010140340121070603548203045445d0220900c11054a1800014528a1001c41006501441c00c903007031200200c0345424000703030000d114210080c0101c030480e06402e01c42c81c805d01e80d200b543c90038105202203244c05070900610a8040c030410780003040041c20003140c503140704c04071800f010000800030b1500e5073301e00c0c07100809410703e10f07811500c1030340340c0350840301d45d0340c802141e0320784a06110700004600c40140104000d81c610110b030000b102d45032420601e0072400204010083d160b582c18041056180c904c0c0c0a40101541250f00141e0a41c0000109282d507002c40294102c5030112241b2140407400e000300186000b451007000d40d958403241e401c800082c0102031361001c46201e40141c400403a40c4445680c20482c818204480d000e0b000002c200c40d010b824031440e40c01c0b42c0071499040c01d0a80702141107a80707080c1070059040d100008102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964729595 1250 964728345 964728379
    0x10c0e061605070e0108100b0f0f10030b06190912110d080d0207060b030c04151203170a06061229060d0204090522020a03171306170702010c090302 65
    0x5808004d0810070700050741903a40c0e11780c4076101c0309000c0c642508681440394119071854030100c00030b280c580050820b05012240702c2001481d04d29504840241901d4849840d00781d6601d00181c10b81d041d404402c03942018122500070103034500c0f030b00105002c095a00010002c5030442c5c02e90a0000d109035010004801182441a07047c0a03020300d48175107500000d81e02c4200085c90f001400580c01c03d404440d524050b003810007050768200c81c0002100c01c410502040341c03564007161225014000d0500508104010100f404161070403941c600642d41c59120400020354042004550780411203002c010078103040041403001b0240d601181e1000c00240f00302089079545800301c562004a0075011541d0755501c0242c00041c02d822111410790000c41c005100c00e251030043d4400300154001c0c071000160b81190b480621682200d4846d8146610501401018200342c02184001c0c122a488000d8075103403141c401d0102d00030042080c421641811001e031a403070b030442c50f07140a40368111080c07240314010300e507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964730845 1250 964729595 964729603
    0xc010305072c06030a02130503030307020a03180503010e03130f12022419020c1917010603060906020429030a02090105071b05012607050c15040311010c0e061605 71
    0x2c60603030140d000401c0c0300070104568001c129600d10702c05090f070b4150fa0303041015240d0100310b945c08056001150603d0001c0c0c4901d080c41d105031002c0321101d07035282d1204046802c507154002c0550b05a400000c4500b510550b441d101c00c0100180c40ca0f80c041030381415805e103241c2a5008cac000303004944912504014a0344034200c1014681081c0002c1c0d2541e030f400311045030460105903410058040d00e100300395107007021503080070545010a0b400d112249000880e020101040741c0448180d582e944000c00040c4603405025506401032034090f85035820000c03510ac8001405502c0c0c5c641e074142c0c0b041031880009000503294001c4240000685510504005130740c1ca2040010050401d928008078076544100d44003901e069800030390300c0032052080580095040c8840e58801206030303036032000140440d485840100101c0c040b03c401e480c581260340303044203c070f024180c3d4101d01049007480d01c040c0c0f0b0301d024450020101e0301407410188a1003074001181540c2700b00441d008160254117000018048100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964732095 1250 964730845 964730927
    0x80a0801090207080d022a0303160c0c0302010806060409020a031506030b010c02150403061e0c02030a090311120d080a0b0f0d2604030506040c050d050312090c1c050c01030507 77
    0x1800a50441f00701002407512684111103801c280070740c2c1409186a42c0c803510140328000d0b84a102c02e490720342150015945032400404503940000100030100e00480e450000d08075401081c0c1780441c42240010315000b400d40107401c040101450b01e401c0c0c0600d40ea011607484100f41d01510a0b55100141044042091180d500080c0c40c0a0504541d0b40c0310042c2140c50000c84410f1070020880b400144a080740c0780c1c4038080b02c1500290506005201203106c2103512362110500911001d44103825824941c104022020300c40b010841020800035214280c0c069102e5030f850846a040360301482d1000121903184100c00600302004072403402c40c580c881d044524021500c04030b14280c845680c0c1c40e0851b69a001154200c6030f05501e00d00001e401d09180c5a41c0c80180da00801550030035905101c100340c8080020001a1144101d2101a04070b441c0c00071148040c3c21007000301c040c544840d081641c17030607041d5801f8904040c80d110410042d5540304402808101d501a06180c00103401c1e00010060180c0c0b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964733345 1250 964732095 964732147
    0x2007080102120f010b16030f02241501050c07090e03090901030803010f080604110f130e030a02010e030c21041d0405060f0405060712060b07080a0801090207080d02 72
    0x405520b034101400007580700300c100d89129040d90303890b4014404540200d1090a9020b80741904c1600024081d80c510703840a0760600c1110402400103045907945600082002008101142401102004091900d040040a0070000d280041204580395108031501c0f40000d0703550b072280d14803022407040c0b0031074281501c01007051109507128100001642e20a102d245522252803c0024041e074000c2500c5200d207402080400e4119815000d0114001003a200a988003646400410709001c0303e101d02180c00c24150000c40c2c0b20400c0503000781c215034607003011460960041c0910800ca2a0005980d015030101d10a505010f03230001510107071a014a400c0304044071002c01058400341407400080384218020030450700755484454840641c0d80007a103001c3c2403600001c000801c2d10b4024400c89101403008040010205c1e070754081580c85801c404012652114001104002541e03c52056405002010400c503d40344217959503541c035114842c0301003085ca8011501c00700e014524816200d1810074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964734595 1250 964733345 964733347
    0xd1407060918061203140d0501090f0c0c171e03010b0d0b0d0b0619170c012a1b0509090a210503010e0612030a080109050105010804032007080102 64
    0x440901810000842c0a26001a1544031044411000341c0c042d080c101c3c0c5041d0402c00444038140c4041b10460f683c480058401d00c0200400c05050140d4450ba5000f46122100054004d0043c030000302541c0c10801079100300100000e00307030041090303103585e01c0e08005480d45a90380c4013201000034503000320302c06540c0302400020000082030190b65009100d961050082000340790041000c000541514410291448042e400001e030030313080c6842050003106880c5450604941c0c2c80358200644049080240900d070040d81c1042c1403541c101610018414043d019080100428844031070700d15a412030140091b40c203103031040d40c40c00400340004c000e00405401c8161034581000302c03d40d1100050001c9036000d6014840c400c03d003158882c0c6008400843d40e03540c0c650707441c01c3c408180b4880c001d4111507020f0400e88116090400420041500c0341c80c0d80c070ba440300741d071500151500300c4034160703c4641404040c008101c0001d921498455401c0003d046681e0034004c4034844d145082c1e0a504844202d40c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964735845 1250 964734595 964734599
    0x151d06040b060720060403030e280602160906120609060b09070206040b01152001020408032805040b030415060506030a021804110702091b03040f060f0510050d1407 72
    0x6001c42d00c0c00c06000135801d000200c06886040c40319511540c07102a00140141080f1002850030f00c9601030104c1d69a00036040c00701071542c7c41c1c103048100350b005e034000d83e210700700702c01800c142c01880c5c0c002400f00741800c0040a04d402c3c2450060b44c00000020051684c50302c088040cc02e03581e0000d03480384070180608001d440c01a50183d41c541007030b00c003600d5007040b141c00002c81d1803649104000c40300b0280d9030741c03080c100443c040d0100b011014450458a54080c800414400020000341507041c0091024210208000030004d190a6402840d4401c00404200c02d105046041c03089940281d805018075122146202a40f4024207440c1c01282c0e001c400082480001089600a0403110700b140000105a000c000300300f1003118401060f4044c129030921000c0050328101c83c4036903018140d4219a03254411162100280d40c0c012102103511000c084801018071003a8800e03503065900c140c0041105007407180380d5111200061040d00d01c50103444030703031108000d030102810303400401002c02c40e00095 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964737095 1250 964735845 964735853
    0x190507031110060302120105040507120f0602181f02030f07050c090a0b01020c09133309060e060609150f040213050301152301050724151d06040b0607 66
    0x101d501c8141d10451000e21b00c48150101031044600481d400801440d88500d40018065034860221080e10320382d09003172482020442ca4001486a4210303140810040707404401006401c0024201c400741c22101e41c0c10200100e80c00100301c0d904c010348020a01e440313169a160981c5455030b0b803c100b44d0031250210a0000014041d0080c000c251000d03004e4640420400d03080c003107551422560103003a81c80442d0740201040d051643c880e5100c0c034042c5281c40c40503041000d021018104803030100c3c060f5603419080140310320b074440d1901611216000d483c040c1010030005200c90406411941002e220340c060000907583e44c00410f109400141066440e6207404e561040d010703040f40b203281e00035400c1007210010568840780c000305844c0800041c0d060b50b48166040700c45030b06580390241c144042009054042507000003810b044c1d0041001c1c042c0c6400c80c00300224240c1c2c100d0b0764841005c1395001002d002101c5469004082001c0c0200354920030741c0e4680015010f004211b6007250040e10002c1c42400344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964738345 1250 964737095 964737101
    0x20d0212010501120209060306060c0703170406020714030c040b012109150204050d08070309051503150a080d030b03070b03040503120708060a15020a150b04060902190507031110 78
    0xd80098035071312042c1411200c4038040e48102035840f07038480b00410000b181071921802900419850404654111307441c0c2e036445c5401c1c0324444605e0080440464200300456040088002800840084001028400b400f10756920746914a03030f4441ca86654080b480b591081c1d4034030925141049900c445102448070b10310042284038007d644040019040c040f011003103008032801c0b40c0010300041844042074a6101194100040482c20450b0081c800107159468188010111128040d607580ea81030001810000c10399105e0024010300703002104100c12500400e4100200700c8904001c9094212100005c1c2002c055030452001940b01005010501c00000007410b043c180d171110100302a11900d8081d2a048d204440d529407040c09803200b031015843c1040e08080d030b40541d004a9044043c150f0b9095007202211522300c1341e182e45c0311a241e280d403806004003001481046421803400c2c02d03c80d00805414824403a04c81404000a889010944144441d500c040000406d850401c00000304034400f03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964739595 1250 964738345 964738349
    0xe072c03160b090f030a030207170c09040602030711010b0102070b1e0406020a03092102041a1002031305090105030a0b07021e0c04050c030f0411010c0501230108060103080418020d021201 82
    0xb01c0b0395504c6102541400180261641c2d01600101030152410f0201e00d00070045140c203404038000c00d0048603158580340700c494003641c403c031009612454031440040130b484078203d4048440c1e04044107644903036000f140340d00c2540c072903085040c3d6070303120090201441e0040c081002c0d54080c1c00136000030542d40c0410000000c9100366038160600b41d4800030f02c0d01c006012685110041d141e00341140042c6000e0380440b038007110003248140ca00004400050f00f0a00355030002000d07810014105207000f442c0e404038000b0f8141150403403200c1d418240401c1e55000d460f0740050011110002054800d4000c100e16500318000c0c1e168102c4068003036083c29160391804d800c80e8003d50610300411015200340c420b50b4440c01c42c10403128196900d94030b0760400e8454042401d1305100444141c0e4000c5003080c001c6170040680084800d4940041d071019420304041644102c40d03a03041500140001010a000c86d800c0343c0c6082c4040d070f003800900c85a24000e10400d0b800e0042c241c400074070b94262032001214241 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964740845 1250 964739595 964739599
    0x606040f03080a02060c134b1a0f030402041b0c060c0309020d150b060403110319031e05120906070908070f0b250b010e072c03160b09 59
    0x1095150349000084030301a03c00d102e04000e0071f0b108180091000340403180b40c41655003501140320556900d10660007804c45d140c11405403051140c12052121501000700140240d40f0035042c0c6140c1c9600ca0565405a07003003003005254000302103010f668658001c94121080440c40359809052030f900901055881031003101c44600740100c940c00340b4003a1265000c0303203801a10400d500c0c03000fa41c0d100241c50700041c201024070b40d1900007207815220b42014001840c0b02d0300f010440050b21130101464000c808002c07580019030264500006070f80240040c44602d200707a0561a40340342070a09441c40d004020368048480702000410003032260005104e401000e440d203401a210b51a40c03825034907040e00e80035500d446070701c4d60f100f04807080980e4010711494200440500700c50012160321103407401c00040545103004518010300c400408034842230f070410001d003000c0d100140e000b4454082a003034840030721500c91030110402100d0b181405189414a03c00030500e500302e458249003000364100300e260f54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964742095 1250 964740845 964740853
    0xa030c0204090803181c1209060f022d03100512010f05040b040201031436010603050a0201201b0d0c350601090b030a050a0b01050103050a02070c030b0606040f03080a02 74
    0x54030a03180c440c201742004002c1e80c0c45987d0803412440f03c3c006003040a0b800c44e5015612082152000160b00c06410f0742c9035030341c0d40d00911003900e60070103042407292040c0b002d5040081050007000208801d0200032100151000145030320604202401007120300080c0c1041c5090004000401c1804034bc07240c401c030303c00d03281004900402451030b680e01c40300715075a80130644541c46459100c40d041451841c80c0411121078005044803c181509684155000301c6546d44151036800840da004011030840840303032401c1500445190466030b94a1140803020100c415005844203115217400c1c0715201c240342c0060300032245583c2c81001050895a11a810740088084456600d00300902e40070840e40c10050002410242d082c0f030b0030000103041441480fa4188554410741c1d0010300107004841030940114007201540d0b14041c00501030750070041180c0c220a1041100200241030b4090000640c0d810020721000c5560390301c0800e21600c41c2d41c110a0f111000100c0c00001c0040902c002c224585080e400d43d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964743345 1250 964742095 964742113
    0xf0102120f010e130305181203070b06190909061119021e03071119030303020306010f0c05030304031206080703050a1a04170a0915121d0a030c020409080318 69
    0xa412060f07000d5034005900c0726050b80c24800701e441003010704400042510040320401007200000c14403140d440d00628290400301ea01c0040c803c0c0c280c00641e0042064404001d40c1601c540480d40c00c000c140100502295180c060f0010300c0300d01c0c1c0c0000c00c1c0426010174103542c3c0841214911102c0c10b03101e1060014801c0e5601e00e40c03051501e4916100250b071080041d42070100d40da40702115080e012503429040302c42c05040384040358542c00c09800030b5020381c400590302e050000004008108030700080042c00991030001001940c0001200c2d4401d400d0b20f40040310104400c0341201825a59005000d24862124003109000780492204d003800e1240c4c01000c401ca0340b01c001c11036501c0d0f0484000d40b041100711108108062000024101c0418601e07086100d21f888400211072034a02a00e0900050030030030240e00050320a01c21402c1c5801d4941c2c102462005202c0182c0c0e45141c012402000c002401d40c011085460355003116801f6a0b00c810310544900c1c1012001d80320007503c01c43e45180784680450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964744595 1250 964743345 964743359
    0x40f02040f021c0914010213080715050406030f0617010c23030f0a27030e010206011a071e03030c1404050120190c0801140c1b0f0102120f01 62
    0x8036624400e0784030003070220f50b808507001e4004010840c3d05607031366802c650102810800030f100401e0000940008401d020b030808145034a414807540080b14140d41c0b044501d5015070b004070603038007110700c1d5140100d401070b602c8213900c0113842d01e0340c840d0120720b00d200c0c01d545404106411800c2035140c16074031181c95501510442c01511014003aa05841c001040440c00500300e03600502d41c001d00b038120209082e00000403481062505005080000c0ca5132801c130000c260741b000826000d180d00b48001c20055060107401004210145201c14607003000040050410a52003100d11400303480020f170b42004140341c20054094007442c840c010000b084400070b001019a000c0558083d500f06941d841c0e5480d4041e1103031403000c03002c11180441d6104c2e022100100341e200070380040c030707041c403031f822400300d06262500f4242903070f00403008044204282800c11101c4420402a034840a4088540c01d0f801e610300c500a0782031041c0740d80c1c2c500d4154000943c0e04404c9a142e910640540b405142e1110a07a91741c2032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964745845 1250 964744595 964744597
    0x507030f110909090a1e1e0b150114180a06090e0f0c04081c02060606090d020d031106011e09060e040314090301020c011e090206070f050c040203040f02040f02 70
    0x400907500c607050101c0401801c194104562004105049034001c42260301c8410325004602203d00e440301c03900d85400d0400114144090070910500490a41d00a1507618443d6402c401080f01800342d19500c0d401e44030340e10807079041005088601c045640c030811449003115203100205100d002d80ca504c0300000d01c1034424201c050843c2c28803c600354071601c1c0d0071400d0003040000b4040300c9007510140000308500c03c0130b016001480705a604421004641c642000c0d0402000a05651207100b041c4180031040d02ca44110200203541111f03402600400c1703140941c3c441e01d41d145488840d1040d240003145a620000e0070301026102c0e07810740030b02190b03150310700401d960017405001c651002c0c04005c0b800090051401030754989040b0122400d101669000c603003207822107580100a1303911032804011512154010707a02423451b900c41882859250740105a06104550004020360009034054092050078003880d1801c081c010025962400e003800c0c8411207680e1410180d01c6680742c0a02e0702007803540b0388 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964747095 1250 964745845 964745861
    0x7060e06010302150c030405060d02031906081e10060303021b03030406140702030a0210020114090c0a0e07030e0a0c18050613020c03090310060f0605030702030702060306030f0703060507030f 84
    0x1444c0000d0b0581e18039070b00e0f0190704440d880c2e0701d1611040c040400c040c4d0311300029101182c0f80e1a030040e1a132404c00004900c404003181c0d5075010500e0000f081c03100e075101240318070f0b80d03040c00466007100c0031891361450b14250b5210051494585000c8000c0201a804588013607403000d20828901c111140d801095264401c0348150804501d02d403500c004190140b80c094207003c0d00040c1503440110303c0d0380211710103895a114060042c2d6446000c2da40034142d602c0c03841d0308000483c005010307910464020880f690244c2c0101e0560000c4880007440641c4030760040d00d01d50b01182c2c16524048140d1800410541c440d0041d507401020410741515181c050b841254481e2400608007060303041c030304000100940c44080d2503202408200075011041e01c04002c007910507454840005400c1e45024540700d0075502c0c0c0d81180c02040401c005100400d50300009880c18a40c04031500c40e035070713200c41c1c2c0000c2c64140d19070700d200b0890283c000000180030107507018510855627034406101e1100c4000001046500303031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964748201 1106 964747095 964747099
    0x30709080106030b0a021606090f150b210a08040e04022110050a2901030f2304030215041b0b04030222110f07060e06010302 55
    0x400140104041402040b145042d80ea40ca8030300e5002520303030900c040d0040780d01d500d200c3c81c2c40701700e490680d07204c0304c10806a2003a01d45511903084110f825980d1401080a020428480d401f90502c0382000804440c810902040c1100c06200f004110390054424008648002058080204051700841d1580d0481e86441c2c81049290030609400340701d08071301c0c80220020420002420100c2c580c895101007920b40c3c846080d04000d108801703d41400d03101a03490340b88050311108400b40002400e80e01401214001140071080d81c160003188105401920510780c402c0b14031000083e00580311b84141c8254000030703a0b5005a54206880c1038601c1c251050f2903904079004100000c00500508908905203461070700020880310010f84250400c910704040c030b0382488001d50003d28298030286c2a142c803005a803017840c1c019005458202c40d05481d00d440344a0301040051414100c070341c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 964568345 964748201 := by
  have h0 := BRFrame.cov_init 964568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964568345 ≤ n) (h2 : n < 964748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
