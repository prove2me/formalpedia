-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:28.751216+00:00
-- url     : https://prove2.me/submissions/1b499ec6-a8b1-4ee8-ab45-5bdfa7d8635c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925719424 ≤ n < 925899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925720674 1250 925719424 925719449
    0xa0f0815091902030a080a02070609120f020f04090602210f0c120601140a020105071407030206040f02040e06010f0e13020f0904081b0304080c03010606080f04050a02090a140a06 78
    0x8520141c4550421038203c1c3c01d07200703104d205c90005d603820300642148060703517009100061410038020680c200301d40c42000031260601070800425801900341d5140740e01510200c0d011031010000c500184640c40c4080c00e26031001c9401c031210210f8008141411144009001e070320f464803103c4180b007030000d036104c0130355200802c10342c6800788a0010b1b443d1301040506040a07000784600414080750310183d56080181d41d144c041080303581d04859002840030901428505043c02e076940a9a03440002d00050a00f10000d00c84104540c0c07603400c5458010b056400342c480b03550b55015401e000341454020140c0421403000003442403a0320700d0320803810b0740d0010240e80081d403224003030081c501c030090000d580c905420010f07554041e00290104403502d0a100c011b42d035440c0b40081040c140191582001c0c1300f0b904100041086507848100b95401c851150000c04894903145055840c01e245540c0c02900010404100400c004841d4002c40042901213000c40c07069880720500021031b1054000c00007071031030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925721924 1250 925720674 925720693
    0x1020d17060103020904110c15070f080a1808070c060305150123040f0f090923100507080414300c06090705030d0806030607050d09020a0f081509 64
    0x301008459000401810018644420103001c24255030000c640d1078041240022076814201003003040340c0390340d250700540500702e041c44072008100f100e40716889000c20a1310340c00328043d0032140e8041007204907441140b14080e426403034100c840d50001142034825055141000a03000e009000c0c3c1885401a0281211000504401562002c2401a806102290100c59801c404203000000c002419030048400a52840e0514600d1601d0322038200b0703030101c0d00345149040040d071040b01c4081401000c5000d92401000c040c85945444905066800b80b079003010144116590001c40c0f544c01039006000c1520301c0f51030b695107543c2da032107500002d403c00c50a8541c010700103801c1440040440c1e908500d00c41c45c0180c1400384901e0608280d40340c07030700364210b00d101308003501e820441d500349134645061100042c035041c00082c0d220310004140714180000010990016101d0394488860310340d0003440d50441a0300c89065012070035030390150310990321a10700d00d980e0354111480450b100b4030030803000303140450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925723174 1250 925721924 925721957
    0x807090506071e05100c0e0a050411070f1104050108030a020a230a081b0a031d1f03091101180b2203030809100504030c020d2301090b010501020d 64
    0x82c400c110a4581030101c540400c0584400e0061400070b44c0240c00605e041d40d801e9440c203088072003c442480c00e01c52007074120342c001d442d01420642100c004450004010f400080b4640952240c0d1000400c3d80001c41c0d030600800c030b034220150700c00113825203007085a40e8840f800c055a81c45080900400340c0d000800c0c0d200080c0910000e070311109640a400900b403000720400e02d1510341a900225001c500c04103400c090290320014440c03000b060240207040d208480d807000340c03e440d5480500c41c400c000954035804d003a1164100d445240d52908680c84281d400c4400080c010881c08104507081540d0544000b440e602c80c10b00680760100042d00d441143e89020384680701a40110180c040280305c40d00300d4503240300131408590045d40a9103981c0e24a280484105040080c0225900341035861b01d0f00340f0001c20f40c40700344044616070603902c0048169280c2800404000c0e09130341c01d040b0050f45c0c0407151903c20b064002c202e00510528000e0080e903260401603844101503034541c4005000114002e0458 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925724424 1250 925723174 925723177
    0x10020114010e0c07170c0102040602100b0f0604031e0b0106030506030d02060c040905040f0501060b070303061a22170c01031b0c03050d090204020307050421020108060111010617070807060807090506 87
    0x1c170404851500920b071020320f003a030f006a4000d00140c4c100001780f030792558a41c054000348a07000c44510f00b000c580d46e0001005401107010207000d1450000c20000f01c490001c440d2400c4980201015405694039000200585811a0301c14041c0c0a0305241100d03c43c00000c00c40d01a0034107003540c1d400c0504000041004000082007511480550034450012a00c20f01c1f94202500100c007205a6901c10741c18060300b0780340750794070000c4100044096030094141da5000d66003c12891800a101428856620b0703c48010541119402e4098155200b20f0706400080c40e034043c00302a201030003644525001d001540c80018411740110303a50f5a407000010b817081c3d008110102110ba40050b600c001d40c1c010401720b1700210303515804180005001d003c0000707901c03107a00a04000b0a02a2904d203003550000701041c00180696060001a040600104d0402e402003009441861291a2a060b150380ca1640d0f407141c030b1140301090b01034240086030a81c4603d110902ca0300c1641c80300d4030818a04024041217 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925725674 1250 925724424 925724453
    0x3090f0c100e030c0d232103060414010807060e03060103020f0d0312060e01031a06013509010c0e0910030f080c010f0f0e010c120c02030910020114010e0c07 69
    0x15000e440e441250a54071a085030781018062000800210010311b041841242d1071161032003540d010071046550303040101c3c109100740c1103050005850f40c40e20b40204d0081c0040c5848803203c031143c1e000100f00d450340000e40b0700c11505039a5980044204440905854846c20b00000e900030401c0128540f06092640c5441000c034881d290840001140d5521031b0129030300d5800c00c03a0f201520000420500140000014000e9100f0b48008110301f05800040e0036259010704e1040380d81b2000c0f1b580f032400381c41080d814520f150b00020000d524504812445e0081094100441c04101050802021402d01014280c4620300c4a148074000508684514100350415481188d60a20800c0000468402809a5a60381030f27040f8020490040b40b60900c0705550f182018078465071300d071004013803000b940141d46503016200020000780070710080130f080741188220064550401c00d120384000075682c0c1540510340c0d9090568159000380d032180f83c201c06415003a1f42d2510300070000d0040c0d601184045148444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925726924 1250 925725674 925725679
    0x30928020108010b1e1803152437171002030106020607030b0307090608070e13050703080906041a0310140303041e03060204120b090118060209041e0911040902030d1103070b040803090f0c100e 84
    0xa1807c0ad49280c903020002d9409c0f0400c15045c080002c40210020025081450000e94065003598144100255502001040c0804054440c3e2110003561024030080c405882c04140a1240035120304007259105500d01ca015652015600020710307008120340c40c840d141d60310002818449281d03480344046034105c59202e0303034800c83c2000001606014900e0b800c044030342c5851076584919210442c2d240c40481070b4801c16404000040042e9a550b000c0203c4003a145010000d425090320b00c0c4249810b0782841d04000e0400e440020f010441000c42d40410100d10300c99a003040203542d440c042d045c03d94100540f03262880144010110001d90990050451804003501c006000303603903440c0340030300e901c149140340c00750580d6421400184115800e403c031b00c4c000159801e004070030056000c42e59480d100c484000806c001d00001c48041d84091044401c0250040c5816050742080e0809c0c030080c0d401550200d110703105100e000e8809842c04a1081c52207040140b141c1a8500a80400d84018508a4440c0d0b07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925728174 1250 925726924 925726999
    0x41403012f12041103011425091a220815041a0106030506010f020f030a030903110d03020a0e01030902010c08030928020108010b1e18031524 62
    0x5031038035080007000d403150b03006103000c515500d403000a050840b00c0ca040d000041f401080100800c3c1455035071458604d000c0c004034041e0092070840300b00ca03541c04139003100071510724001030400d00f2020130015000039801e40c1803000720b0003200e2580a02104aa110701e07800e1b5000752150400c5209103014069005000f0350203100d491161200304129610f00b42c105001095481c0140031316941e011600c0307a4224914001000043c485440f0f01d5a41d009520040082503260088130041510078038580b417042924908407044003071800800f0780650082904000042c54408078440c0940c441e0140207031040c1c040e1a03d090001258030f8014480e44020400b402c280b04101361042059861a42540d00720505002806580d000f2310004060210603800400004400d000c10540d0341c84401c92211020811100ea40d0382704074110305540401030f4103814540c9030245608241e0305960b180401d03482140192500e0b40702c0307171503045500b100d09444007080740c10454034543d91440c00c880c4542d0000065100400c0b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925729424 1250 925728174 925728187
    0x60d02040e010207050d0306080c031e0c0a03030503070807050f27032a010e10110a080a021f0e0307030c050703020a0b36010e010c17041403012f 64
    0x2038261381c0300741d5045030242e20001c03a4122007a4140b02e45800b80c0320140c080c001c130b41d01c01e01c0029510150300d409880c0203144441007590b50001003003080103158001e050040310742d94a0802a205400842da0728000c00c919500140410b480b480c21201c116014070103ca042c0a5441c8810380b428040150718101c068030580003848a40e0100714900560240c0c01551101c40d085640002091500d00703020760610032800c0d030070041c9544070b00d1180c00880c82403610301c038503141c81c10300240b42585c0e00c01d000d0280d140000301ca540069010a001c0e0390040c0c20b20a0410910405585200312100b001e00e542d0300350424000b000002c1c1c42803040000840c05141102c540a07226000140035214650120700070881c0001c5001030741054498140b6440303405031a80d6494000003105641041c10240d100b0304205d9403040e40c1c14243c1c012084d00502c2508045211001005004007016941c464010780060201a0b2542e110a00d014021003040c0d44000900769055100003001d031010000185103070413640d0301486403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925730674 1250 925729424 925729451
    0x3030f0c2109010207020a0e010b03190b0a0b190809060a0903090801050a020712050301050a0317160503030a0e035d01051c0b070c02030a06091101050c06060d0204 72
    0x1d600416840000603525400b038410040040c0642d4040c00039000c1c24070040004100c00001d6a82c42504011584041280d1000581c020b14a4241d007590003203c0905c0443c1141080001e004450010468060480900402552203182c01c90b540c2526611202c0080d25207500780e040441c03003a100c0d0800c4044d05454241850a4a204594881e1701c2540810282c06008030300d41100040541400e105155504050108601020902020b8814440c042e92403024005000448000d4410000a4000c01d14949022030b200d600a0741c2440c0d20764103140081030404408000c80c2c1c0001448425001c0a528812402440e081104518103100f14141c0d200b8405000c0d00e460500e0880003c46da204c596051600507074041001a08030ac1d005030348504c0c2d42000741e0b820740b00110846400caa285100d030f0762a900f04507403100d014076000350035000303083d0010100002900007140042c49180c01080c3c803a004001100c540c000c80088082c651701c9103001c9420ba01f400c0c070100312030500103000403a4aa082415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925731924 1250 925730674 925730737
    0xf15010c1e050d0503012301050d02031302030f030414040e1e01060602150601050d27050604050606060306030304031e061e0615020a030509180c071403030f0c 70
    0x40c8462030008900c10101049001e0210b01c0f0200c1c40b03400e10b5429541444850314883c0d141d10205800090400741b091116030290096400d0520014410340d030301d00c0c000101801015841500704e01902c074030507102c4264040030040c5c9080d54424614000150f141c04100006010001443c0a080c080c00000b03101c10149030103201c1c9a00711807000865282c0c58814020b2403c240e07251092801a00407081c428140e9002040b00e900e106043c1000c11181050764181c0071024000c000702524900c1d02040008104020503260301c52802041518000e03074508040c4507641c40300719410b9034190400c000601c00038280c491000e622100441c3c2010040b5a44ea0b644c108072140c0c0d021060000e1180d02c5201240d07201070151704080c1c1205032400c0380041100c400a991035030b03071300c40c0141405070125848003581c944034003103140d88451030344242d21402d0490400040d07a000743c1e025110840002014001400c000040ba800740c5028000d000599451041d0407400d42c01c081c50b40300c0850004428440c10070716194 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925733174 1250 925731924 925731953
    0x2040b040e060f0f040f03030f0e070f09060909210309081605011a0105030c0a1b080a0215040c0b0c010207021806030d1e030b01021203010306060306050c030f15010c 73
    0x5000300040c0c18140200c100e10f0000400c0280c800050004010005440182180d81d840d41400d0218074800e043c1640f002520500104104903c20302100142c00081c070b02090089400c111001c100280d150710040003a181003030000f40009070703814040045003610b511183e01c02201841c0020740403806950f14403982d0f00030007803c1c0038214001490300600c070087c81202e841c000c0d8009036480d80d0041c040082d055000091580ca1b1809001c18901c481c94000c03101d0602d0341e1402c5044110025076440c0580082d0001d0a04000502c140b1f04c80440c1003146c5601c10380122740005010340c0c45c0b483c1032969580e9038005040000c2c255028083e650060700c0701c5030806e0204c20201711240d200d1030000f060529002c408841070040020402c0101c0b81240002c0c01042c9010b52480d01003005d0703a10b0300050303140ca031400740c0800c11310a00100000a201e01035101006503841a01c0a20941d01c1e8103114489070b000075074140034120005008965241e0070b644019030b03030710810304060711000c9440c1c40300110040d640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925734424 1250 925733174 925733201
    0x100b0301080309010f12051e3318010803030106081b19140d0504020f061c0c050c0706210618091704090b0906010906020d300903120501050f090402040b04 68
    0x50300243c01103030b84190b01507030001d078042108500030130103c4590742a41aa46a140700500c50001c01d20054403000124140b42d01a92b0003a0f02959455981594a600900c01c590010f40c20401140c1c501c815000c80401103c0070540c010704000340300a02003c2054090808018002c901d0001c2c1000448203003c1c103101ca02070f40e000611807a0600600038841c007040085845110b04101c0341d929202c0010844900300c40945000440c12a4070005072075510a40980c5101803041200c00141039600088044600440c05007500e02e031142c1c404000203940d41c601400310b015541003071284241c00941c0c04800c0160190740054a007100c0c140321f4460940c03041e000301c0c00c0903440f1301b1012a142040c04201e03030000300178030700406150301c1c0010081d100d10b04980711b1030402a04070500000700d840a516804101d80c460344a809088507203049900a0800c0101240420a11170b02011034208a01c1864100c0390302a28101ca03020901042140e02400280204d80c429541c644000443d2514130841407900800e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925735674 1250 925734424 925734451
    0x409050c0d0f060f09021c02280903021f020a080a0e03010515030312091c1707031b12020c06011d0c0903030a03020f0706090308100b0301080309010f1205 68
    0x1d0030421820b4803810000c5002d02030a00904002400349514203404543c2d83c25401600d8490f01c100e4901104001c04900c403800780041403007141c80410b030005050013440124201c1c40e0084800d0b0644280349148030107540010315203c200c41c40c0349049806000e284291046d41c040101b507540d1070350690031207240c500000f81c1c0d5107400141800c0900c50180c100ca901c000703040c80c0405040000c1d549201c4c28103c00807003403c1d1000b04068010070480c0c0302261080c6038039441c20041405004240b8001d4840504094204070049100a8024402c030340310130300c1c08645c10605a8560784191044c406901401c1c07442503003081007a10100081c000140079081c0800c401143c0140d0044010540c0030140c80102d0300b12080000d01702a5800004a8096050394180580c4400f41d031111100c050040380f4000d1f02007400d2484140030150f110082900c181c10b4648050310854440b9000e21240c002400344032880e51080000c0030896000d03200d08410114641f8219041540b40c0740d01c0c1040e9041564100002100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925736924 1250 925735674 925735687
    0xc020f090a091505011401020601180c140d05190e100c050f1305010908070e06130612030c1b030203070b131e030519051e010e0d050d140910110409050c 67
    0x440d49102c086c544403d1008101550400b2103c408590804c004425595900c50f4009030560142c07840d11100d60551141d503842d038856000e094054501200c200c21009400e002508a0703c080784650303204441c03031400a104003180300000c43c00420602c4902010700009210038081d080040c0001d021140d1080c0743c070740c1d41d1f62038100054182100c60f001102641c00c0b60340b00b80507511652428a6101204031040c1d107480740f0314a8940000c00881e00125043c01904481c90145500301100700030861003211039401e0f26040b150340c50307501c840c6400029410f40085408111385225800a4819030086260500603a0303910706213014004c1c0d482c4070a01c41801410300c20400d0100902000c0c50311500d081411030903c06550b1100e0300e90000401320400c50126007213009003440b096101c2a140341d25042152405540070318050030030703000074000c0100f0504003a42040c02c42100c003074007802010204000c0800c10b54514a8101034084140306100d0b075078090100180380d00090013501d0040c1e801c009650364420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925738174 1250 925736924 925736939
    0x10f0b0307080607020a0b1f0801090b0c04050f0405060f030f1e150606070c1a1b0a0506070c110a1202040509010b060901110a08040902190c020f090a09150501 70
    0x41c541c1c428101c0341c00034002c000c51a0b07008100034620070380c000721902e855507540a00904000c0400b03405c00d5844091b041c04201c1103815880032107014024000002c030b41d50f0b4042c541d4aa480707603000350b83e040078001e15044c10070f060035044503402440052a6100c4020a140424604043e0924018250303000c0030000c40100d000594180e04070019401510158980d04070810030006c000d00321a009041c0040d81d80c051019140b1400040c145074000160807030302080403904075400066000721981804800706401c61000034a03039001340e601001400183c0d0764103000f950300c0c1d6020324081c3c4000d03010b420010000d07030b11410924007504d0219103180d0b4000150040c481102c1005100e4041a85406499801c5694040548044403024030f046584204520350007420314860920003481e1140100c5c0124030101c4507009000b08591040c8905220040c442c8122042c140001c0c010390070004d5200c2d280c0446c281081c0b2154407810008010130041d800ba80d503e944100c031080d5200d91075548400510660 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925739424 1250 925738174 925738183
    0x17030708070f0e10110111090f031912091a12060616020f01030212150f0d0b010605160f03110c10140a090b1b01050a0515090612010f0b03 61
    0x4000e03031601c82003010101d58003404055108000740e2095122424295100744645d805980c8401104c0081c4149080c64540505030341011150320300c5800c0710540070100f802c0018140e000300300021002000415951290703070742a00004030500800000803c04039488000c250943c02c1400042006580c80315109109c400403207024103890321610080180841c945103608840c3e0788a0f40480b0f440d6901803082d00180c000f03216005a41603240400c20401880d00c000490f41c0c040f011082d10049000d08680741042035480c010000103110415000052003103e101d440a06400750030501c40880d0384245da00c42181c012010803049000035a8840c200517440400e0003c4004e60360143c442c000f20820140d0054414111803101a41069010800f0761511348502040c10042012140050780d801807072a42c2100e545222003080030320341c202004206e080750680326043c42011882c0c01c05c000250110100110390710094415070740304005002502d0014821302c41d40e1511f040005000030010395250605050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925740674 1250 925739424 925739431
    0x3080a0f1803050d082e08100e070b0307090f0315270204051306060f0e070e0a0303050c100203010617090a020d1e080703031a04050714070f17030708 66
    0x1c064105804000080c0001010650304445080c00212995401030720042c080c454800303c1c0c0018000c1c014014403032026a07415050710010026070710140e507140f0305030050700c1c003600d0010b28aa101c410104005840140990307040803c91400880c0e40c5d50750742044940d485950400e41e52904c01464180500140f8400c50078040a14036161481c1c0010440c1003d0011400364064007d54603000000c02e49903108010b009040da2110b0200501e40c1c54403280e1042e25400c0c000e02c00f6401c0010041510140070f80494405460000e04040d142411a5403c03245a001000118840d12a526001e0481d80450029502902c015900d684e1250310b500c095180601c4080c2416642d03030400407983c00981c40307074100c541141d0380091a4007040315078070f0f010082c0e0205803203025001c0d0310040f80140c00c0503410b404c401d80c1c400d50340d5084100396040200308021640d050350750303c4c086083c0030440d13807a41d140b01d03014068150040d240d45071040c00c43e45800803400e20200054039407800001c100000f16400141041c0c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925741924 1250 925740674 925740707
    0x1202060a09080a0f030209180615071212020d0c020c1c0b061c0c08010b04240314030d0e07030204051006090b0729060102010b0d0203030304060e010603080a0f 70
    0x1c480c4107884064162048040d280d080081c03461003450814040c0d0101c500e0300e40080c0c500b00c40b40c2c41a1103024030710700085c0e44503481200e0501e20050303101c2004054a802c1600300005100039210b8500586520f20b02e6400d015921b5028802d03108521254405c00e01c240c40203402510044086404200030b82d55540c008156031480c08181d4bc011841807044140c3c0a00c09075a01030640c207241d00154082c02c40d181008010703006c1a0f5011030006010b40100c4c242c48800c0c0c3e000e01c002080122251f40c5403249401e24645003140000400c0440c4564107402c1c2030000b0030341500c3c50b100c0c0340364803881a40e05100310104280e01c00d0754100304509052140d0340d0700c140300c0511000076a090503801400c8440c24030078039071045c10120f401d0301070200b180a61202c011000c684c0031040d103d141c1c0c04c8107542d4000c843c0070740594601100005c01d400d10a14a4480d40c2c5c2c0103000c2c511316a650f036030b00c4006241c06254203400d0341d61158048002200540100342250280c0c807081500e070b0103032100a00e4082e02100046 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925743174 1250 925741924 925741931
    0x40e0d0e1f0509062503050405040b090f0403080c090411030f0f010f03030f14041707270f1805030309070614090108190609020a02070803030c0406080915041202060a 73
    0x407010750220a0307990103e421207100d9500c981005800c200362030560440301c000300d07403649030fa802c242c0c004000b0030440d00d0070346041c40008000c1040018a170400c44144c403031000000d0000d800a8810720ba05030740314030071a942e20300b4007000307402040c201c2e03d64007000d50f0480800001c2c003640400e40717807000d50b0100c1c8680e216203140d81040f804500600300c0d80b00c02800d102d041c6034800566409001007164080f1410032040c0c40d80d0f9078620038006c000c2102d141107803d01410001003005401d0840600030001c10841c503190500e0206400001071000130241c0c519035540c1c0110700615104100d00c014241e010714000c44e140d0524101c11420a002503128406000c00040108000010740c01900c2280a003402e1003504ea0b603803030f80115032070204081d8858074075203008000b045888550f40030b89031581c100d50031504407a48030b0a51940d2488203a40000c1034080510040081601c03a1a0035940312080b42c044e1002e408002d0b484052448060f14216445540503409102035a41001170b6a8410001c1c6d4061 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925744424 1250 925743174 925743229
    0x7050f0406031113060306181202010e0d110106030503030906041b030c0603020c010f061707060912020411040b2802061b1b03180312030108120306040e0d0e 69
    0x9a070007000350500343d03000f5424031816145510155200380000c54009106000244010441c1c03407048003070b21802c683d142515004040c080d481407146800d1048031000510344900080c00540703201e10813010f0342c8010342d01c901003c000901c040c00514050346a40b4000c0843d407e0030300c1d01c04042140d20640d15000030780da910403c04150b441c0c2500040322050308005a45400f40301505001d0981c80312780c1950356040c001d0008040c0306d1045d00351503c0c403500d01641c01c42922584122050301c8240302c0d2098000c40d0028004c00f6280a07401070740b01042c141d40940c585075403500c00650a030080d049003500880755206a0051502c16040740000d0310b0b00e440a080c8500e044080300e1180100348000406501d4003281904003000e08903884148515103504036a2940340e0f813460004d00b1040360584901034010f01c0d02c903444c000010300959068500c554043c0441703201c80c02a000441d08001c00080c0e110f49c0312944460450010310142c0b0104201d0350394410402c0d0a001441044030417582e00c00758185080010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925745674 1250 925744424 925744433
    0x5070e281a10080106350f09150a0b120718050115022a03120304140609120a2a05210d090c0b0a090f0518070e0109030b0907050f040603 60
    0x54103481c140d0130620040f0200c03240c030541452500d0900000100b014100308280300406d05450b208510503440c0401e40c0d903408007983d46841050412121052130100400d92080f40394103d440c01c0d405c0030303048008188a11105914215495201350b0802c81042c40c6900d1149407401010b000d85118241e1064250f080072000703646890b080301542007603491000118054000e00c0366480812001001c54092039110082da940316482030b079048404103d2103107480d0f08a0404100e46206001100161408880f9850741000c258000e034000341c104031100f00c0d20f480c02c5d5070b10030048494040c5140f801510b960301c0d142052a1a01400b1003c18860b034000d84030494942040854404070440749010030303150140d00d40710750102d4035a0030480f00b903100070800be01c015a004059108a40380d44c80141c03101980c0f80140102d882d00c9103100c1c51840c130b18400044145000f030750851070550061400b03a2080b07a03692038000e44444282d40c80c4815030000181000705103000e20400c04000c804480401009196130f56 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925746924 1250 925745674 925745687
    0x30c0308031009020319180b0f0709050303131d06130903020304081c090b03070207060509060903010c031b0813141207052805070e281a10 61
    0x40c40380400000081030002a100c03003400070303c2e00703c40554582c24400b9501500c0c10840c0c00103103400c0e142141c0b2400b24803078101e000c00e0083e0411860145616602d2a05071034960044c0120103001d0075420000f03c41e20108024036000002c080340d50100350900c071150110744000780c0c4440c012070101e400c1c410b959079010314000d01f01c202910000b5120085103001d0b800c60150340d10446950082403491900d4101190311840324412958659480d140c0380c00c0000034502060358001c005074000c403028040c42c3e005100a2031407450040626040c03601c0d9800090075103d900104000190704c0341ca20341408044038800500310601814443c84501c1c0c9403c10340e05052940304080c100d01e00004010100d0641408141070041030f0b03000701c569541e114140160345854504061007a8002d1140c007203801200c0d4441c03180d26aa00a002c0e08519103084440c080652024021200740100394100300480940c06081828461000074080382041d01d50054074000201500c1007801503038114140c1e2141540b014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925748174 1250 925746924 925746929
    0x30e12250e190c0e04051009050f150603041a190e0a02030c0906060403080c071401031407080411100206010801061a0301061b0b07020606030d020d2f0706050316030204030c 76
    0x40c2c00036440c81d070900102c1e080c0ba41142c2684e0480d16002c240b119900790400241d007660107000c0c00340401e841e441c036111034030340c0100c030b0000545904c2c00144841d85040001190414000c0074a82601860304600003001c410a484500e5031030220071019480709110f0042103d40360405d4041d0003000c00c240c022980b42c05c0340003e164425208400050700554030142680c000c2d5400520340c50729107030068000c41d9500b1250181d2160103a00d108041c0340c0790710030b00440303e030701c0c040d054070a40c1d54540c00e20596110700d000d8001c85a0004641081c411a200c00001841c0e00340307141e0042102c0d514104a50b82114902e0f0803000164582a4200070101c0c0d1a10031a41121503518050801104045001c0c141004104008005003107460610a8840d40000d800c0c4c0503450850954014401c090403c0e03035281e007111311758000704003e001c90300840b41d500600d180c3d1803818005059050b17483c1c60109401c0100c6504460041203002c070920075100040d8408850403c80c900381140307000d046440d882d00c68181c52 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925749424 1250 925748174 925748221
    0xf010612032d020304030b010b040b04030b06010c1b030b010b0a050316030b031501080c0f030d140d0f0903020d171503010b040504080a180b0304030e12250e 69
    0x60b80300204011520110040705406100c1c48100710031100007500c0c1c0d8002d21081d1910040e01d8004140b0f01c2c10340c0100c9049130303074a480320385c030703281c0385035114130b543c01d00100369a050007141e0780100081402c0401c0d903007050503500120a0054154680540c0320041a000308000003400e101034412160020b044a80043e1180c603035500c58061200120068442c1020060305030140b4243d0f44c003070079a56120b45050310741d0783d401d407111495a402802480d40301c00710155810f40c404c1d12400a01d40c000c00c58040305c811b405034101d2a0100c00707650300003501c01c140309101c0181c0e40c910202c420b0540c1800310074034189003490300b206000d062940c0300d100000080e1029032400300400c40112999025031000203542c07400340c8280801d02e001c7c00c11002c507030424080302c0301040e4006a808050f03445290a182034600a01c101400e40d102e94404032002b40c0011041500305640d1100c220f240e09041001c0201c1c3c03001390250413650742101d41702e00005105030b4409111002c8080920641e039480140d80d05850208 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925750674 1250 925749424 925749437
    0x5060705162103050a0519110d060b04030c05011e18230909070b030415060e09060115090311010c02010513090203090f030307170c040b0a0c03020f01061203 69
    0x80d8045080c914040180061600700b155020b801000b11480d0050710000c2152400c100c0e940d60442002c0030b83d101214580c3c4a09100d0203210146403c0313902003550b081a4140860401905001041c111450758100d4079410304046800c0041001019038040603000c01e10340f10780c14203800c42c0e8160102c2ca484082d681800900035210401c5152425038400400341c04d039540c24001185013420ac00040c0e005155030281c22042c002525124000550104031075070004024915030721502c860078245803240e2000351a0740c07956000584001c00840300342c010359880002d0720f16545414800c0c81c03100c21200841c030a0142000041010800150f5000300c890f00a09102860340a2403004071541e100754010340c90a8040240f0100b2441e0003503010318451002442103410b400030f081403141c0e480c0421184140080c0380310000c1c030b54071700446400135048514000c00908090719602c014023aa0804000c44001441300004c44090540c10031000d041c01c3c1c3c60b05d0082103d0b50800c00402c0300d0807400780c1c002c1c1c2403240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925751924 1250 925750674 925750687
    0x61a0a05091003050718060c08031003050d02420a140a15171c020f070e0f1f1202030313060503010f0902040501020d1103130605031b040305060705 65
    0x400440d814207200410030450704520507006030081c030b42500c0d00400580058043c4205070742c022250030607102d0a4446601d21001603440d14000e0f80001c0103092500751048000000070301c10040030b0441c0499402505010b105821450080e000d0f2100041c040c4a6801d00203c8120820100c1007600b801651120410341c0c0e40c10300d84000c2e20900843c1001da0803240f0411482c001650b004828502e1200b055079034480e0b42d4148510b0032861102621081d0300042c0c04000004151485070300c100c269401912106076039250054102284d030b5204a01841d240000c008410400c2c14403a980b1294a0f0a4190b6460f02030080521a6100740580000404030240c1c2e0303410b5550800640d012400301d00101c4c042686c0b1900c005105800c00e00c2a5010b4006011010440420b14001c2d107042e1a010f03402042110810710017140d081c50840d0403207000d03000c10030029214410301c101d02e4001d44010344a241c0c0c1e908019002c07440101d020300c0d0004189205110500c0000ea022800075000419490655103545 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925753174 1250 925751924 925751927
    0x4080d05090a14030306040b0d0b07110a0f120e0103020c06010603050c0c031809311a0709080c0102160b0c010b0604090e0c100e130e0d0207140301061a0a 68
    0x4104002804118561a00f603000c100000001c1d44500d6050b54103100745541c203418401040da03100d50062491110400162129129034500c02d000d00284003116420b0351142c80b60005500405410f49a8404190110304d400b5004071201940c83c07070a00e011480c0c84038041c20316491304018052441050b880308041800001150180e42d100c10355141903039510a8410750400030006003001e014002c6070403200040b0030b903414090003c04045003a051009600d400001d50030110070544080b42c0034541c44048a9400e440f283c1000e11a11003600c0b031300b00031030400d081c0030702c1e0440903a0f8050455118984070b24920241041c0e441c00c0b140490056611010078040c1d0902621803407444940126020070000f850b04059007101190807030900039180d45003000300501080c6080e4080450200d0001035401c5a01d09000200c0344039080f141c00000350b0041d9850791603060100d40390f09940142e00089041c00321b802d40705450841c0e924224001c0100c1850004952544070704144840c40610004c1136421815 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925754424 1250 925753174 925753183
    0x80a0203280b03011404052a03030408010b090a200d1b020f060c03070207091109060c0a200a0e0411040c020a0501050a0203150607051908071a0f0c0c07181b050304080d0509 76
    0x8c00010140c0351142d0300c0d098401e0081019101c090b200d1020200401d454060f00d00c120355400d400c8540d2051104078008446100754030000c01d042d1021341d11840c5905261405c1c00402204a1960181c02051800e03030081c0d00d0070340080c0004101da4400c100384428580c001802d8411074041120118400001203160545405041c28103904603900151220031403e01281c40c030712003441540c60700c40ba190320450703281140e400e14860700c0e0800c04442c400d10096440310106a1301074800e142400b12401c812001c201680c080c00e403030101590000488208011080c000c0a03480174a0780303421401c600e09610300345090120000401d0040f0300010704003050140078403a69280904d80f00403140c0346555450130312400e5000c0c04e0141d580c0c81e00c4a017a1b4024544009070180501500e0154451540721821621030070303805809509510b01c940c100c006030141c00c0384c040c100b10340c00d2894002400415001c94a01c2441403c1001c4100305040040100084a0405880b509016000002500d0382e03170040080c42c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925755674 1250 925754424 925754503
    0x102304020403060c020f1606031d01150501170f04030e130c02072414030c09280f03030f05031b1b100c080a0203280b0301140405 57
    0x3400041c01105028880d04101049007541e821684030b043c040080a13140c4c0b50000340b154040344030981c100100c0f403090b0403d0205560b80c2c44403003030300071101d4107890071500c078540080c00c090f500340d038100255070b040640d850b91011803c850000502d080c149010300850028002000e1104010041156449035082c9c11500880c2002c1080a48a1107901941c2d030340291182046000e0507082c60904071400c07403051003480c03100c1e8072807840003c0000c5003140d45402c014a031a6902c501404181c5040e643c5103160320701400700b10b4942c010f100e00c40c00e1005451100e80c01c003148144408400300002684101496420074103841d10603107a44801d8080440c100745044000448100440c0c4080e2500f80c0d032115000706a1407031308680569407c0200f800c244c541002084c00410409030003e9070380c00d995002903a200c003ca20071103400c079034040c0030101640c400514040d4040e6480c00f405109050920840402c11030203c0451003d00d007554074556183c40c0100c2520b00c2e4881890020154460304040310341c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925756924 1250 925755674 925755679
    0x705070b3c060a053c060309011a0a0308183708070b0706050405071a13060305010620030c240f1303030c02010902030616021b010507081c110316081023 67
    0x542342400031840c1d0181810b0f00703140c12201d20600c0c43d50154940380e0010400c03290b101c4000e505040d0403d164918455841d080d168010090109a41c1012034803194482803042c1512107424692203102020803a42240c2c01c81c1e803c5074001802401100c07400010f543c0e0250344404080b640d541c80d80b50440c105229940044040c00c0c040c540d07000380d01c051002410400c0720074200264611750f184022002da48003071143c0e10216240007030366400e850300c0c80800c04d083c5105a040b0792805000800443c60140c90141080d118a07400c4940c1d9500008414881c2d040305071242b5041c42801d0034180f55101603202c10008082c103030342d25185440e4130700070741041880c0758005054900f03900d4610110000c00752600d42ca28014080c4a0f00b910034031070303215612203c1641c1030350b80700d017029529030f83c06e0410f0780712602c1441080401202c0768142c00136800750007514800707802c040383c0301c1c20072400c440800390040f646141884014810004440390b0a03d03070600f1100d030101d00300000901c04285c0140c2c50366504d000da4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925758174 1250 925756924 925756927
    0x20d0906020306040f09020109060f090e090d120207110d020301090204060329040b0115050c07090c09050117061306090207080702090705070b3c060a053c06 69
    0x80034400c89501840c81a00c080c3d50900400480000c4141100d003076610003400b0582100c4207100700d911860101500744481d091084c400c0b5203903042d281d0000f80071148071115901080c0c202182c030786d111070000e81c580482e0005609144c2c090b0740d0701200300b40380328206005580187c88030b82556825040308181640181c410400c00d42c807420000442e00540f580c0c062100c10360801c0c441002071341d0440070301c82d03070704070042260302d9007000c0d565106079030a0030b44042081000d0001030003132101130103010001c02501100007144151498042c20800550b4407550511041008811a031b0040d0001d0700d6200c0021640e86804445d05003101004007403540284102e80e20100b2140c0c01c102190005154184c021a200841940c0d0070500715220700ca02030380104282c0711880400c80c04900c91008106a2024036900500e40c5045181580d42020705070807a0000701c0110b060100a0405884001c050030054030464641134034107030350b2942040d4004060001281d4101d102c01c482d40781d4866031102c50b50040019 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925759424 1250 925758174 925758191
    0x810150b130905060f01020a02090c070507060e01230711151b0c03060115050a23030414030a02030f091c14010f1a121005270f030906070303020d 64
    0xc031900112400b644490034500004140ca03460800e000e400942d20507402080c00000d0355081c8107103040050840c400d1000148401c80006405100e040d01820340c955031840400c8a110004040c800300002407000c20030b0b1050240041c494040890700800d810203080582c0d070454001049000042507400d0760101008100703a550511001d10049802203410101c0708030982c0360382096180c030f900b84640703044403100742c210f81e2a0b24021805014009030505001200c80100700d001812420000607400319140c00000f00410003411040312031901030060002c509080141ca03001e07603070344200210b4052810012444181a949102c031184079045031650110790810036180c01410000044208071041d400c000c420391a08a01e0311031078031414450900c1b040d00740401070a2001000c8000070007040c90244062031203440d0102e02469000e540304a00c4038590350b07000c208010b03131180d04940c0117a151304181c1041e0081080081030720081c00d4204d820b5540e600907803606030000d20034102a5071907030742440c846 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925760674 1250 925759424 925759447
    0x7030207030b0c07060e152202040501060c0303050a1407120609091a0106020a0f06020a02030712020715091a0307180608040b15030703080a030b090f10050a0810150b 73
    0xa001d0384d600c01c1c882406010300c1050390b103480b810b400d101020358603c0c03080081c0c00e00c503070301d00b02d03c070203000d03003a8800d0940406401183c140d90090304001d01142400421104059052040541c400303e80e0808014049d010903402c2c02c840009400310f800c0015000c031240042520394462401080c240f40c0030400905245880090140d00000300202c00d0901000080d40a001140108a560340030303800c0300020126a540400a40010354101d04506c802e001500024a41032030761324070540d060f001400c0381c41c941003000d001d4480b0038410a042000c00b4000b009044030804540c1545411000c13603030b440fa603400c50101c0c0c1044100c3c00000c5444480d010000b1003c0e001004a03000324064205000280da404031040016407552500c29095800f050040000c260b011001d0a062403903403902203103e0b0300c84030000d001441c0c1920b420903100b1040060001700106144c28400a0000b964600e1460f0314054050351117841e0f0040d1502e0355625119010321340321b00502c1490242c5016040191250490f092 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925761924 1250 925760674 925760677
    0xc07120c061e021c030e01140901060b0f0d09060905060403050c0d05030103020d0201080402040f09050c0301060501030507050d0b0d020909031306140d270f030f0804020904020607030207030b0c 85
    0x4030408225615030a04281641c4040b00c200d40e20300b42c00130400420800360b0b200131040c00c004403404041c0d90b0b01c622040c0681c00c0c01225107260300006581401e04051103120300310b60b81365002c8844100100602d2903103503400c109803450700c07451a40c00039486440d8284540a4460800c0080290180c5d0042100b0503410002404224940780700700ea040c0100d10000307544600c02800042d5114442041b07a1005612811020b44e2141c0701a00101e0b10629592090056400c1084110703131076009a0541485420240304010083c00d091a0900007800c00c008094044c1c4640c4c03022030001c03511400c0c1600e40d916065111080d580e40a80044a9032074040c0c0c085840790803031515a8800011f1100001d00c051283c07442150580009140c985400321440c44440101195200506c0704062201d0380501d42031002a41010180101031001e804601c502c0c008011505e00426882444141c01c10320004d40c807010081c660065046d0b0b001d59850b0804c1c2000da2078916a580300600f040610400c11a40104580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925763174 1250 925761924 925761929
    0x2c04022d03070201050703091e11130f0b0f09040b070512040c0501020105161d01020a120c020a0929060904050405010617010908030f040c030b0901020a0915080109020c07120c 77
    0x5000f04210303141d58800320b0954219480182c0040c81d5005001800d16004000b142218422b503000d88009214001044068090f403d1603448180d40d80340d0403030912194018510345a20854021040030403010000300c0122011300040c181041042c0040c0c00305c2d000300c00711500c41000412601c510714140ca401190300c40c883c01194015401c09001c0b0344400c840b001406c160304540e40301c0d800c1c14082e440c070792083c5031607291009045100388810170000c901031801c000c2c5807988503a950b2005a9850060016004081e488500402d03d004d29003440c2d2021800304020203500302501c080d2130314402c0c000501b180650710610382d0081c03400c410300c0200300d815072140f000c0316401d0300805401d5040070820360032110b02c0c90010f04078550401c006481c1800066146034000e02c9803415650181e00d90310303000c1d10710400b00c03503025450f03500149103030840b50844540e40040140260060f4400c01c5c00c60000d00c0b108062040340060350b00800c18a00c40c00d0103020171405019450403099071803095040a0101642e9403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925764424 1250 925763174 925763177
    0x721060e010513080c1f0515091006030209061b101b080402042703050a03060f0b18040b04020a0203091002030a090b07051c02010c2c04022d0307 64
    0x30201a668841030044912500c02440c0a80078100c194560003201d911011140040c1c0c0218164590104d64920142064102401000500345000b9034056441e200c4100494400d07000c180070018182103040e000b03010b0343d800345005a00d0b035048602140c80d50051120b10b11828100c200300c01181c2c03000044000e00200c0c42c042c2480910f18003000e000e801c2806c082c0d0400040c5c1f43c3c100240250825420503070070b2000d00c4d006000304511207064500c00e0743c00c000e0201c1c001a00000e0308491203070305028485c0940b01f9940c5520403980b801001203640e101d40e10f541c01c40e45401500c1441281d980364040d0854120241c429981e8054180d0000e40f40d6220b0021203100750002c800400031b0501c00801c0d214100703004d4603040746590038454102180c0e040908c00315400d1080300002094000c02507411109016180c0010800002e4010050407a0294284541c0851003003411006c441002c00300500328441d060740c00513607411855003e110300d800301c24491140d120036a42d4680d0001c04801c000c52084005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925765674 1250 925764424 925764431
    0x80309130b130e0f030307050316020c09041e0c0b121e040f290601080a0507080601110c03121201210618050610050102010c02060603061305072106 65
    0x1804500c1100e510620058000d40150514085400950b0010b1142c0d07072004100c44100002a0b40e5503e103510890751400082c01c0032092100402902c80620291300d07050029004460042c0041211040006d0000e41a59424904c04174241ea80341c1071450110b030050340382c0d2403e0345c0318015040e45038011101184002500c0c00058a81c040300e1100b400c0035500304a40f90010b4036180c40707913400c800040c0c8040c3c8600d81c410030078010f08a0480c1803089515055401d0010900d000800540703424002000104651b003400304004509a116595540c084e0090a0825480003502c42c92482d282a000e1010303010f100c1c21895458020800020b003c08041d90550741009a8a80005583c042121800000107950070484100040d0700d0b500091a01240741d0320500000c1c01c1d41d1a2549840c00c181d810000d103a05080c410b0000356428040c2c054210348170300092520303081c1000466a9001d0050800f040124110709000030444140030010080c01441609090744011083c50a00760030922001c40e041d518 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925766924 1250 925765674 925765699
    0x90f0c1406131203091d0103020a0503010504020a23060403150510120303111215130c08060d0206041701020a1e0e15090d050a05010b04090b070c060213080309 70
    0x1800801c0b0382c2c40d4503403020426802d6181000400b4403402080c0228180040142c1c0481c0ca0350a138130302d002c55040c1d110f044202c039501d140144035647e100b076000703280243d06000030000581c4610b040e5030210340100444a03e0625464488040c4c0e007411300080303a001400160000c240403181081c0400104202810031045d15081c2e0100010080c2d4455505000201c1c000c1c0d0010900a5104041c18074015140c91b20300240d600e20034508100c119090180b460b50020120b6541c10403019042880510b11000c0059003a440b4000c0d01c1804018003041c4030f140002091001c540b01c08050701d004054458801202c1008046034034003030341041010000040e24142950440589002d07803403c0081c2548410140d1441c4200b8881c1103e041082040c2d140010031082c002601d922110b200c540780124060504112940790003803d41e20481030492250741072a5020000c203d00460440e0010702a0410100d840140d2810b40d020303000e6201100742020074020700140408010005110009049408040740e04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925768174 1250 925766924 925766929
    0xe030c010c091508100f030b09060c0f18120a0c03030f0504060504180908030c04170607020d0804031101050f0603010c140f0d0e010501060903020307060906080f0a090f0c14 76
    0x10703064414110300712070544601c4120b50042d513a15801003440c501400d609901c41c0035a0314495180d41c42240c0242c0400100032121106205403500030385d8080160f0720340f90f54240c1c10350301801104200e070303030740310a902060380a0741d66071800040c01c0e2a504241d60000d0100c5c180507812550501c010707000305650301902411140300350111030903603216850b8541400d01b442d0101d0450f01c01c04c1c440d10030321070340e0325201c0d00480c002c2809035101d00da4580c100c554541c00c02000381180d140d2841c451120f03610001c20321141c681c012a10382e180c00c50728030f8031440036a140d00382181c081783d08600c004500e51a00040c030513120445212035215207002d900070301494210050403034400c0302566580d200307c1c206104481070301d41d1481c02820903644202c6c001c1180c422140007c1c1c2119004c1c2e2111011845144c1c08000314241804034100031301c0c072400d00001041c0340c07501c040c03c18032004040480008900000541d0240168065a51560014013901d4490898541820008014020342d2009000c1c142c4c1009140f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925769424 1250 925768174 925768187
    0xf0f01050402091305151503070501050f121b0d0204170a0201090b0d02121005030712080306190314010b1212091021140105090c090d0303020d0e030c010c 68
    0x1264042c043d104103035912030380e9034043d000c103080481d070900448010178003444108000318000d0402c0c1010011002c102410180f52600725800541881018010308501c1c050003000d40d04515141102c00045d80c2d00e03240c03410803802002c3c0c8038260a00e0b02155040c040e0401d92f01920a1f260001e810b04201c0111100c0307540c0d07940c00c000c0e00034001100080c0900100c02a034000d0826690340030809810282210320f100d03107078107080700d40a02014184104002920b0100f03d68001000a500c894001001c2c981300d4000c641b000400c01c500401183d211202880b0303039409101c000b1508071442010a000d920080c43c0178100e11308075144959454504011550004590749007001d00f08441c03503180600b404113200903110100e04410a01c0600702d540f1004d070b481140e255040007036001d000101d6015204681455440c11307080340d40510303050010400c4c3c8505000403a002d101080768181d480183c2032404902910a03c0700715003000c3d0074401d000a50540000241400c50030031402401450f86102049850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925770674 1250 925769424 925769431
    0x204060201051b310801091122090c0905010308030a0f0509190c150507030314060a120203012403020901050301141f0510050c0d08100b13030f050f0f0105 68
    0x2800410041c40c4030510020140c1c0b155a040003400780c440c44004000c91510014031740c4115007994494134004204181e40d01c50248a0034200d8070000c1140124030700080410301c0d00300c3d07100c0e859920007140e814072498045c030f40000c249070b0806009560712482c00410980040c0c42a040b5203003841160303101c105807400b605100e038022074018010301129014960b00d4064041d800c1c2da600c04140408a50081110341c0307072004001d282c0710309640e0a00d0313280050440d08014503c00c0f41030320000a001180c0d0f0b4410003d41241c1d410007a4101d420346c2c03400000d0042500803a04003c8076841c41c42c1044200850041c40d08480c004c0340e1100f40c0e40ea031402414203907840ba2065450705d080000024007010260303484000c0b15081500f200740c1741510f60b80442c07c1c560415248030042040413a060310340120801c9804141c4440385890203a904000c1da00301e00600e540c1c000d095140c840802d4442c0c188028001d02c40003580c2110803884003040b141440e540701c1e9681c07040e00044d40034421910707102d0581405003500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925771924 1250 925770674 925770721
    0x150c020d08160521041e11060c011407080709080714091806150916080105120f1c08010509150f1f030f0e16090c0918020406020105 58
    0x310355032107145002c6210001c40341e100c00d121042c001e00001034861104601c4220800f078a041103403d203401c0c900f5601c140901409030012001702c0040025140c1002c000d41d039802600c407140c07144800b00c4694050f080c62440c00380302d02903c03020403074002d40c4096443d0180800d520365034026a00d032051681c440030540108400350448048107060b43c144040c00030750100d50201c455a0030b803801c00600d4108203081e02e690304070320511021641c00e890f00103c0c00d508030204001075584280c0c10000501500c50500c02c0910401e64080c906404070030034807041401d011100306903400d040c1c1c04903901790116400c49561000481c60000418103060880f00c41d0300500180840585150b00c00e0200000d180f002c0f070009030060345500c080d02d240c0a02001c03405a028268a000c1038849602200c1011140d08201e0340170345902902a0482c1084450340c000c0c2550701914020400080c100c40984440016900c01c580d2030200000401d0011070960103007080e600300768020710050312014550b140160031801e8280c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925773174 1250 925771924 925771937
    0x906020c0f01020c09040309051305070c0b0903160b01080f070503070b22060c0212190303020915040609090f0501060509060307090302060c0705043b0c060403150c020d 74
    0x288546820001644000c1c81441240c502d000c0c524042480707000c05031802c50206001420601413031030107034a001c0c090300008108200503c2c3c00b410040c140e00403080c02408050310240440c080c41824800c840d0b500c0c0c001d1b42c0c0102003024502d0440c400050900c40c0610702d0240004404500300007065450071200010b00400c445824402c030701c02135a00503040717007002082c42c0705041055150b170300d0a50020101c0742c0710040141814010300c04801a900d4102d40d0316000064400105517805140381046600362400589644d50f0802245d04400030320035556143d00f0216002500784da00c05074907c26036158107000c2c0040030780072044006441c42030145202041c42801021900e0404601455110030b00d03103045441e0315a43d401080726940403100e91141030300060800d0065041c03901a04d90840b003410440c04080c140f07a9816004545040010b00c1c42c56203644c55000e61000810650024550050410340d0b1543c0e00d2074020705c0180c0a980d006001414039007030042c424004200d4000080c229103505 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925774424 1250 925773174 925773193
    0x5090103030f120f0603150e0318060f180109080604050606040c03021614120405150a0909050c180316090513060e160506030c0403150b041a010e01090602 68
    0x41d6060000b004401c0100031001d4003070b4451030810701501d04901a10f40b4005001419414220504504995101c011034148007440c40c9080707000048805041036805502d24a60060700000c0d014418214100c0d07100d18003049111921001d0144008201c0d001d80300c6401030385d620b070072644d140d0508503400382c0a038010b10005142420140c01a0508466a03c0c0040c5040303c440081e500c0d071246c0e001c00307460304019490080c2502404008140c05c0c50410f0518034140b528142c006901c4010220302c400d071100c00030072601c020340e0003001d442e0041c10131100140940d2806c20905446a044801041d0350b503007a003150001d0303e0801103260b1550b014640038050344503080c403c2c00800781c480030300540e207481c20581501c00030845521503007103152209405400d0000141c00103904113101034003d140b00f16810410b1110422448044804480d07029a0030f55004115400707590040685010064100c0d04014a0f0340320445800c3c1c10266441c001d032100b1075203546880c011998100140144005a880f05220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925775674 1250 925774424 925774427
    0x30204060905182b030b030114040201200c040903091505210c0a1116081005070e014b030f0b010c02010e120d2a030507200333010509010303 62
    0x5500104c2ca081c200452421004008030742115001c0e880030000703c0030b48050100f15039100e6007004105540c2c0135078280322a50000c0b801d89941c08541c03680d1203a50788860100805000706c00100080047c502c880050440580e00640070740d000140024980100251301442500c03002901805002a008110b0501404030426a100212010540000d1040842c01c02d45941804c2d400406020600040c011803500801c0c080251217000d0a448140098149400850390b80a00c81c02d0380d1003c6800d100903e8443e24031040c6240c45e0000200b074404002041800c200d01c006066030303520f641c80e5a810440d0644245003801140c1d0000101787c0004c0c079401c0c004000d90702c180008164054004e204007030101a0303d0701107142a000d084264045804807420102041039110b009200c41168120000103d90300e540003401c40c8264103005207000300d1040701d4a12814080080000054041c085618040400c1511800d48038000142002940100d8003062000910440d050481d500a042d26070790b6401c60350b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925776924 1250 925775674 925775743
    0x1703040308040618081b0f01110703050a110610030201080a09080d0213051e09070207030308010303050a111510051203071103120d1a040e060f06010903020406090518 73
    0x482240c4500d580b980c802141d03a0304014178802d0f01b106283c2e0212041c44213858144015904801d1041c1d1400c4086981566141c0c115181158545806075545801c600243d030701246030420060079100b05400c000c20400b6030a509000d4030b000743c0300c3c503189a44420188040e80c43d08030009041d001d051000000080342e41c0c0141115072480b900035074240740c079500856002440c400c0749400103003034007a80400c03074107004246641046151019018fe1421500c0280100c401803000030104040090802c00c118031800c0144a000030620640303400c1001c1e03041d04444800c0c240d50420600301000c0f40007401c2e00e420500307201c164400401850070072140d45c56010328002c0da951117942602801c000c1e203240c510040002e009081c1c44c1040080c100c40580410b412810704000f9250080d483d12795201903840001604035841104480c4120310755440f180102c4031904660b0000350840d003001c2000c51503403016048503100e8800380d2201c20240844400c032507901d55804084614032650b118605d008202e074200c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925778174 1250 925776924 925776941
    0x60d02100311120a0608031e0901090302090406060303090b090a09090c050a091e11090907090503120c060601021906020906091003020d0507020339011817030403080406 74
    0x200000c0780b4004000800c0e00e070340441e02c11048000d030901001001a00c80c804c1c2806440c102c0000c50030b10016189202c15402e014084280c0300c1c00124003400543c0c81002c1c0d007000356602411071002d40c10180b030301d1005014a030008070b0215400c02000724001e00043c0941b58030803002000c0c008290f1500a0440080844240030740315208400404145038490800c184000e180d01c03480019a180c040b05900d850b40007840300240054280001084c04141841c2a5442d84c44200c2e14a0816142e174038050319030240d194001c03501030256042c3c20540c4071402026010380f41d4840152485a0380b003000481c2c8800380030a5100c02c80441140000209441d940500380e05030000e40407500d41014040024001c018400d868070001e80c0004050740c0b414154066076800458500085042649503905060340c882c04504140c4200d0703422290000f41d0544505200d128102d99008019205840e03100c0329604d00800410380361039107102154811100103e04884c4125019038400c1c0c2d030b5071242c3d6501c2c4007600101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925779424 1250 925778174 925778177
    0x80c031c0c0509130b0603071206090c050403020603133c0305030412110703060c020d1701090c0e04181a0103030818101e060801020f0a0f020f0f070603060e060d0210 73
    0xc2e02c117402c59450320700c01140103140c183c40b00b9100d004641200c1d0305403900c0d6040855100e092600c01d0300f001d6004402e40d001e407907046076002d44079500c44040a0b64501c12a00240c090203070494800a040f42c1d10100c0340c3d1080c00820007001504058000c031046442d0b0090060014400300000303004140c210303220f0645a621480c0c4038903220f0b0342e00b06d540e00e0607170907410642d003540e07548280c10a0280c0401000c20302c0f0145003080182000e071401c84403190401441455081d03a1148800007105104144807000000010700030407014031550344d0103e640c0130300c41c0203d440c02009800340000106101c40241265031641c0c0354441c43d0b46050390049000200e0511505510850910381e0b012072650050456119003c1c03900310142d0201030000003900c520703921821413640b04004402c9101050011a20350802d0b0341000da483c8030345410101d15100e101c45403d1407a0181218100d0182c8000c104003003116000d40d414001541c0301c90b80204d000c5015a0125400844c014994006040ca10018211011203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925780674 1250 925779424 925779431
    0xa20190c15080415240923061305090102070c0308040501030e0613230d030509010b0f0109050f0d1e02040b0a0503060f07090810020721020d1b080c031c0c050913 71
    0x303120900f0142858000c551040e440d021700e45441d142007080c405c207211042d031040f503090402e9008142780d42038251014074410b440d0340019048520075011100c940790711030b008010707841e0b03a824610031540190191078002810000c0c040c44150002502c24052013104a4200052810b60f03103807058032480a15140468100014903038030403038140001a0544219140401c0742d242a03295030303007101c3d030301d25410303101c0e82504994940d96640295400203442c0142c54082c00e240c0d40c1c00016040e11703900d000c003e040000041c43c3d00140c0071068401d02043c2d00c255030501011807801c0400101c482d103409129099800000014403c2d00c01b0824140c0000c02e90820152680d1141d481d41d0401240c488034000c91078001603000200050200803a5640c000c030b207260080c02c40801e0009466000d80200710080100113030710700c00066000040c1c01005076201406c15980c4407800b504a450b40c0015010a4680d04205104803101e16140180d1001140356501c0074540048001004113041800c140c49203110b0740c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925781924 1250 925780674 925780721
    0x702060f0a02071805091c05040918020418030e0105030112020d030e1f1806170406060e13140a051e010e0703260a20190c15080415 58
    0x280c0d040740b03030014419540205035890034086047c0380c220006001c40018110548903824954410140c030309449000c0d03004550f05591752001c601046551101950107403410002c2c0c604000c0c81449104241d01c04c0e103500303840980940042d03803d030009100f44c0284480088100005141c00400010040e03c2030414601240509010030de800560742e69075242665510030349200c0360b400c0300014200d0300090481444c3c3d5401d2240040031154496252710320583c00401090411401c1c1d0001d20180c84400c2840b00b051030004802d13680c0d0241e042c015103907219484520180800003044581940d604100141200524041042c81c40c4c9100950f1800035580d03100001c01113881404000011801007542c42e02400c48264440000404e0014078001174408200040800e50844a161044c02903070a0340f000039000020414203180c1c2c842e03580030304450a48142d600b0010514502004e5800c0140141d44120700300030140c550b107a040c1c40c060a00807801d142c01d50f82103507940051448610816045a1192 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925783174 1250 925781924 925781939
    0xa03110706060e1515040e0603030c010c0503010608160c0b060a0815060103152306070b07032c0c0409080c06090307020907030b0108060103050a0608030705031e0702060f0a0207 78
    0x507510f801102c07141c2c942c0c006018148074580000c50000c0c0d4221194901500d01c3d044035103c912551140c1501046007000103644e540e010700581700d42e0701164000780203e4100c4c40c4000c015502c00d01600b0301150b2074102042074010442c0d5000304a9641340c0f82d010000c40280c8450f03260303110081c001644164104004a5902020f10485903d904114900e017250f007003c800142c2901c1050016007820521b82c2c03401c00412150400405150111595030401084102c001c1100c92040d8100a4a0f409004040c4412943d0542c0500407080750403d003452a00121050381480813402c075003044490748030700140041407626900802c9540c0c45480104e2a04010501070307418680c04076410081900080740031070039420688003081d0f0203601480c04004c00742c01c0400182015a01900c924101655540002d0845d51a80e202d00040c0c20041e04032602c070350f2103180c4a81c0d280d0000581c20760300703401901d90201000b07080090351140303603000340440d04028403c0000c200d260024280b890451241c0100001c100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925784424 1250 925783174 925783181
    0x15170a0f090b0a06061b1103030f22081c05031306090f0b310309050a0b1e1801050c0703020a0905180f030306010302210906090706030605060a03110706 67
    0x944202d8400c4403a25001a90008030340c1158021001e000006103031080228003160180900340e0f10001528620b0a200c000c03900c2c50040c240c0040000e040003508107816000038818035000c0f55640d010f0f00e480c44d262900b0540301da0040c01201107015a02d80c002414501600c003a650040727841c9203044841c40c00c0d031076400684100013020f8505012180c101c1003481001256140d0191041960701011103511503015200f4099103250281d1091031507801041501c502441d000a20340145504a425220709042096500000c40d6000107100000410001240e080c251000005480d8503130070058054801522980d208440e413454a020300c03040480140d4821041d0400b5003201310000a0034a0900d14181c050380466100b80840c0d40b240700e09000595001048a520100c28030303000d40c0b1440388201007100d102886407503080c1514450b0070040c2d84503002030450710400e41001243e4045558460940455015000380c94000303104210010000c0e0090b08210401c1d80040252031600c40c2e81d498480c204c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925785674 1250 925784424 925784441
    0x1b0203190516260f0702040b1305010807081e07060804021216051c0b04061805060c0901570c0e060609061204020a08060a0e01050115170a0f 62
    0x210740c55508100b1000c800c005003e16000c0109100519101a0303224662030303405007074402889141c480520b20400c2d100c41d041c9020000b040d91050100c0d5844442c142d485190314003d0b03500521034541341c4000c3e50724042c0c849034840c42c080054030109040110072291100001e0041c0d801074000744512a900508010f03402100308555850044c83e81000100a5040103005103079865164440701d0794003048900013000e4007e0703803201e00000c00002000c15800d8554a8510140450080004000101004200808081100360b88501440c4201100040c150001907a00f00c101582d100141c90070240c848052203d89852005000340000300d001d000c80307225000b0f0310898207800c00b12010801d0200c24101c850300940c0446a15013403203043c001041c0640503225100c55224100d40205055466405114010708005019108240350854042e0090031a00024807400e40ca0500005901500301500180441e090707521200d00403080780e64818100e0000e016034402d41d075901c0fa00400043c15200b000b04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925786924 1250 925785674 925785683
    0x2120c01062c0609040204060801090305070b0a050c0304031407020a170715020d180b0304080315030109240b060a030e1c09210c0e0108011b0203190516 67
    0x440604020544070429500e0340071401c0325941c2c0719031070300c0c888085400c254045000d5884420b60742d5140000b80150456502100340d5519020000702403550202c01040c4140c011201c481440c0c591074034210850303d0455410411400610115000901c600c400d07004034051601c0312070600350f80e6000211983c01540c0031001411010511421840d001d001400003481c8e40380f688901c92588000c040d45428071800b424081000038103100010f10252001c8901400342500fa02e502da103002e01e0b10f020180d106445012000043c125440700c1d80c50305020381480a80c0c080a01086148440c80c0c0c0c0102c0407182c0442070880c0e459a12104590b219403010700a52489503801081040c44c860605041c4443d0381c94159040184500724850302e41c2101c4400304948086802000d90710302d0310050070300300c0c0820400030035500d140180000c100a0325802281a41c0648000b000310201042c070000c075040e2140c40c21b0015810601c80a815019040503a88a030000f500f01103203080c003000052228078280300b0003104c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925788174 1250 925786924 925786931
    0x810150c020310150b0d0e010510170c011409030f01090312150e0f041b030f02010905011803080306030a0f05030d0b06040e15060d0c32091002120c01 66
    0xd0540c9810800c20b10000039031103042201903c656582600e03182907000312410008000b50f04415501c10758004c80300f03007010f58020006c40c103124015468400e014810b04ac4983c0c405441401040380101b80c00404400503154440c207180e400a030002c5940048201ca603260140743c000c0302501a007805100c5001e84647e450032100c04103080d00d00200c0d060440d40c0c41c4c10400107507052205815044141d44c100040c0300300440c2a6480380740c05a0700c4481180030007000c01300d0131000810400140000449a80b00340c171111100ea880700011120201840d100c040105151081000403c1600c07000703507000400030b03003600e860b5205601c0300300380040103a40032543e03070f840010741f5021100300344502e008800c1d04990703191404c0e203040d644c105e078a2405800754580321200402c403451036642904450a01520b503a0501c44841710000291140c1003a5820b051815111403135083d030322050100d8102d4503016840e0302418188900144160300c101c5039020015840703060307000701003100c42402401c0315443c1c003000170 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925789424 1250 925788174 925788197
    0x60c070608090705010e060714240703050708041511121b0306032503020d12021002130e060f0402030108030a0e03011b08090715020d0e030d050a081015 67
    0x10280070004010191541215500b40711aa91200c3d481582c0b0104440300c54945025050615880c0c030000101ea031688a1002c0301d003102c00001e40011140071090103107c02c0c82d500d07043c041d801d450b8111070820008010380006400a4400340d8024011503001e20001410070b06104044c66aa00000003440418188030070000c0030f510000140e038910702e002c030040d401d60400c040400ea0300d600c4188010181c02050030001c160509840702c110055070010000107a14441e400d00c600d20340c54032221400140076000765208021f005008558000e03401202400e1402d240a014144500028004035032100e02c084540319181d403240080c50290410341e000c0c55840c18a0320000d82182000800b65000e6418a54481c07500506503403c82005409418400000e40c0d034003805505020082d040704401d416082c800e400e449034002007a03106074005403103d2075140003070b008140d0b0350b50043c0c04650003d0b0b010442e0200e13462085480c16084108110405400c03a1100c03a00052071034400d120304009004032021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925790674 1250 925789424 925789427
    0x1b031502091c02030d39030e04090b010b07080c01050103110306071704111c0803100602030403020918070b0f0a081302030c0f0118080a020f0a0e070c030e060c0706 72
    0x407101d1080d41c03000741d4003401440c1e000c00e8071151005d0700201880751340407400300c00e200b204608021410ba4808a0340111740281d81611038901d1030041940020101d140484540c00c062144025441c0c002c1160b480d107a2034501101c0c46903000040c110348801091248100303528090203014081c51141c00694042001310742031525002f001031801c4104101c501003990500440b4588640294120b144148103102400104015103401940d10710b100100d0300d020780c1072007800009940980c0501c0300955040e56a40d404996901035808081d500000800200d05038007020501c2035440030002050700c8003d5030b00c8840231015004418076190403140003030041d41d0036038004c1d60681c1c80244421074403104265500800d40d81d10812019500400c1202d002110507030150041020296003c0c180550f0142c5426038140c441010280480c0101401d4012820b1490402c0141c003e6854207800c031142555a0401110380400102e4141d0500803002e451004230f45541009103040034000e40200f030f100345000b10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925791924 1250 925790674 925790689
    0x10e030601030b061810090f020405060d0603050c22020c1c030c090605030910360b01090203071b020109120503090f0102032d0408010920030d08041b03150209 70
    0x3550962441781080620700a12034503100f82d4003034240c00280c43c4c04c1001c4880c002d00c00c0d50090b0307602840106400484030010f400080c242c0b842502681c540c050300c0000d021058114205000d000104441c81c280c001d182d960241c00386c010205c0441d0321140c180342c0110044610070309801c3c00261130b0911407000ea0b0b00003c144004020604e40745146141c10b020b0b9549485090180b10303812500c031072501006004511100c0c6c290792448005104124070740c99031103900c045074842140c14040541c00020032a0952083d00c0c820341840d20343c80359540c000c502007203030400070f500304038107000900101140105103440d0001300300780f040d0019541d031180c2108000f1007030442c10f200c03811503208109454052140d091507040c121041a1100c1ca01c0b903240203608803c2c051504155055880c14805806000900c0b81812904120519443d121240e000a0640302e90800600001080006010034005450325195010181d408403007a000d258907948d0b0041d244481d1038254540c00e402140018042c40c1069 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925793174 1250 925791924 925791949
    0x60b061213061b05090d1518060b03010209090613020408060406020a110c060d0e0f100203100f12020f01120507030b010f090f0e040f05011523031b010e030601030b06 73
    0x58003c4620f0803004001000c1d8444c00503140e00a8416160380c1003000074050705200c4010041d030080c481c0d5400e2300c80d28410007414a60680b6542d0070302c010400317241018400c8941464028100c0c0a03030b130742c4250600c40d0010303500c24a4a40d695082000240e406424000e147c0124454000580e0307826814030000c010b00030300d444100300d0343c02012103001c031076680c00200c3c0d480319040e010104004400d80740090030303c01c000714425000d005001000b44c58040c1940114441c000c0c00f108204841e44441c440c0c00c64400a0041009615600d5843c10142c648610a54550101450401d240c6202444810242ea0302a60600003203510740004c031070300c4d607080900e1400c1e40c40c1a28006030f0043c500814551181c156100f0680340301c1c0203a000c00d041c401c2c0d0410b031062058101e002880ae001c000101f447c00c04285204040148490b451880c6c80e40340616021604140c0c02401841203d18504900d62054900d2281d17606008000e02542941d80302840414000c500a01c2581030a240140074043d0388500303007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925794424 1250 925793174 925793201
    0x305040e09010513060f061703030405071a0f13121419030c0f020312030108100506010507030e0906060405030a03050c0105070f0c0807020301110c0105070e01020316060b06121306 79
    0x1c0200848040d003842c82e4003003281c00510100781c03121842c050900400098000c00c88e6002e601c803012003110030000080d8043c510442c22100125540c4c40c4d600942d000410465100c0681000001c3d2908507e07006440300321313001890b10306615620000d015a507080d03000215110891000818000c0906128514600201c40198100d40da040d6600a1880c520340380018005800c0075200025501e04018420103106039041e0250740c1c4d41c548418039950340c3c440740c11142031801c10002030029407254081c1ca210a034075031141914070b0080341c00c00c1041d03900203110340e070031141c01c2c0030020321075070200800c90155000741c5885540310455402d0f982502c100410b07420038400090910000e4a5001c100e1403500c94101842070b80369109480064050701ca405400f034001440410240081d803019031016005402580704c61034914006001a41c8902426680300301c01c1a46c01e0070700000c00c086822414250170000d000320300e81100b140894051180c00d80d24a009041c000c01c400080015a00c00c101030201c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925795674 1250 925794424 925794431
    0x50402040602300417010b06160c050f18060f1c0218090a0803071202041409062b0807020a08030a1101060f0302041d120d0f060b0403060c0207120305040e0901 70
    0x1e5062454810b40c0b14141820005c0243d01000820a40c403224481e10000d04d81941d03044c45d90b00740000030769480340995000c0c48520380003542d89040e5120982201000e0a440ca0b420200003004106600042000e600407150240e10b00d01d9544103c0d0105820940c0388206829000500511004860400c0c803440c03075449440500030f459000241041d19181e004011690302e82d582d04045031072500786105032000310f0000c50081440004d02c0282080c8a0007a101c452255441108000d400e44840300000405000c80800d51406820490342174023140c0901842440d00d01994081050010310f5801422260004030b4a14442c90340803042e09044e0b049580280f018034101009040104400c0c40700900c00c80c1d880c6001c0040c004c0000f0108281d03405030050b544040081c1d01604180e030300c0340344008107951a01c1e00043c04070b0001c2c450380b4203030342e94115407e04160079996502e00810f0701c1c941c0c030f02c154403d050002071180a26050840d956219030b8805031624600f03040380d03801c7e1a0103480c0d001203074107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925796924 1250 925795674 925795753
    0xf07030b061c02031317031605070b0619050909060601030e0d02120a1209050604120207060903120903170c0d0305013602070303090b0919031107050402040602 70
    0x3100342d90031140001c840e80181e0301c1d21008905114811094002026280780020a5460700e20143c05140709403c404c4c6903002d00c03600c00c0011034807449060300080c00b0100c0a404a51142050740c0c841540d42014562003101544071340025031401305c00c46d0700d001c050f0b200c0700c100000e559040c000c0401d404142001440700c01840b07903001c0d445502c4084680032403413010641140c4144504807030b4504030a48902005000340e5402c000c0d444000494007521081c40c0c05442c0f09410b880012307008110b54041d0340d484c00300c0742107696100c0da220701c07882d840c005c000d0640d0001c004101075036030300400b05640d8900140d68a940501c4281003680f203001c0c1200b40340c030b801d0040000c4c448003c4041d07a540c5450188004c000506901815681e49047d5041d900620129038142095090341c00318911b0350181d640c41e0b140d40e40b43c2000d15920071101c862816007002010940e00002c0c007544c4095101e580d2603083da0380c0d00d920341c0d0210f412a0010b9005100603440340480b81c04605854600c10309070f4201ca04c1c14181c845 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925798174 1250 925796924 925796947
    0x506270106050315180a0c090b04031709090f090607050a090504020307090806010902070209010e0106090e13020913021003060b090112140a0e100b01021b04090b0f07030b06 76
    0x24148a0403090080000000d196190708494119070240018038401d25003408034480507031140120303030100380300b482d20160708055401212500300312800301c205a81f80c60304540d900b00c2e0b071840e520701408001c2e90a220a1003150364504010b03105101801c5110018540004281e150000250069050040070045499510f5000380500140c62080e140541d407901d9803801110120b14540c00006103008050010840c101280c00808040d4000c03202501c07280d80b203100c441003440081c840c01e004038502140811490542c0300315583d008a071070840360180041a004200540e40454080308868078001e400d50441c034000300709440344001d0f8501002058188a000c1c21548a84801c3ea8148039544060700041c40c0319400482c0c0e0b0455801e10b0a416051480c0c055010700345400001c403841c040e1a0340c0710b440a04510940d00e49540c141c0c018200315002c00205816003245c1141d05030410348684480000c41c1c0040388003030180d00d8500c1c00c2c084510b4030480090480b41c40d0f4280520403072003040b0000011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925799424 1250 925798174 925798249
    0x120f030e0304030618060f0b040b04110a0311120106021c05030622020c031803120715050406020c1b19030506010b0a0215040303060302031506010c0f0507080109060506 74
    0x40790b00c1000002c1e900c1210005c01d4840000d4400203240340c0c203040083d0300c5050903030030201081c201a5424400c03040b43c0301c2040195000440c1070244e031101031207c282010b1203a001503c0080e000711034203140803d0300c1c44142c0c014509801070000342e80901104da503030740c801818200c0e10042c50700e01681107052860000c2c207401d01e49005100c40d80745155000c3c50042e2070798111036010b070540c422680d40d12040030500c50300d604440203c600c64011941c6224603110220304075030005a002442401d00342a2181e0f08000b484e02610540d4415820b01c5480d401400400c610b0502c45078418a030500d008429003000740f0740c0400115040466480141000041d43c00114141910b044e40040760b03e820a100d4103e00d80030501d85107039464a0110180001d040d0140e2000c001d4038000d90589000c0b20b040124002c40400a865140c001203600b200000070841130b840d08062144264160303581c243c1e0b90050300d8203541c003204080e52182d9440091012a241445c0400380720b0440e428042040c10301c0c0c14085494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925800674 1250 925799424 925799429
    0x1b0909050c130b03100911040c14070c030602040902030a0b100e060d021303080705070902090d1407090501090b0f0a03050c011b080a0c060c0822020406050d120f030e0304 75
    0x2c52041c0c60114102c1c0441e000b5841c1c501c0050102e90102940f40b0f064130162842c46820b441b60b50b4501e00d0010b840c2803d0050340b91a00840d21504140038024840c1a000d40c880c11302075603150010800440002c54600050008024001e0090317260304000f8030500c11140154102440790780500e15049120790000d0101030443c03821504075850700818212500030b0300c540e01c6402ca074500c20450210803c06d603d00640f090a009008440100d6100e44030b04089102e03204040d030f4044200d102c0c1100091601011003038541d520380684646550300c51708002a07a1b03082e004030100680b201940710340c50400c03190285444004841d6400114036541b200c1e03480c0c1c00380e02c0080341002101d05901c907944801c402031484450340124a00e81d2a0401c40c401031221140007421170f695801e0140d4002040e10500308175000d06100c41514110b4140c4540746006244440c030100c2c0c003d03450f403000052980c0e80d1490501d100340100306004e805500003200600040d050300c90781007818540300c012030310050000243c0e8103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925801924 1250 925800674 925800679
    0x9060106230315190e0a110405120a1739070e06040e0105010b041707030c030b16020d122c0304030c0609060518040b1201060e060a080a0b0c040f031b0909050c 70
    0x1f12286400f0002056100710703000130b504000440c01420f42080e001403212042805110300ca040400b22040c12101c1d44100203060813a0030801d0080b11141416070032400304482c80d0411440241d603100c03403082c286102c65001c0005460b11004010303ea003410301803058001203400080200d98104035003200c0c6030069003c1c0001c1000e100c4404455210200301e19009150450100302065603a440c00c4100210102d400300040507000b0700c046c070381a000084e990f5002c0840e0300c609411800c01c4c06010020700300c21611000400e004400c01d0800c000c0d2045000900c448030000c0e5680c0d50541c1002c5081400d40c1e84090100b002c510f07401c20400c5d078064140c40012241000741070b0141c80c5035000402500440300e015500c001d102c2c2c5100810681540300030304a800c0d440c2d24400e40e42c1d0303180411486540234400c000c800d401c400b24000008501005542c0d0014846c1d510904180d1940c500d00101e0a16070000c07507004286c070031106101c00c5601815402030500c01d40904ca4280c80da42d44c0c82d11041c607060100d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925803174 1250 925801924 925801931
    0x170601140d090f140304050a09051e0402041d10060b031b0a03060302090703050a110f160203120a090602160303091e21030306050909060106230315190e0a 68
    0x20030070001c40048030f90260841ca060409114403151325442e03502607c01c1522034401110009241d01c0076000e050b214840c00b0100e5000200501c4140c0900b8500820482c0d2140c0d481c0c81e4a07043d00502e050003107191214000800c02030b820f240b104011036a05401840d215001441005200c04041003141204019000040c0e10362001c80001d90192006402c000c0d441586c0b8020450030742e6150340000d1061102d040300788500c0c0b1202782c0f210941d1081240000700710000700509400240649009074007140301031304030742e42c4424002001070540c001039100750015110140400102d51304018501c1c81c00342c1c03031000040d6645140c0c0c000e8222000c600c1404070b00d44200101c2c8240d0320030b0341b00c00700060034403070400700055800483c82c12148103140c80c1240801e08e030000120301404c0040c030300740c070132001302d0000c040d00c0e400e2000a541030500d41c03440b60b02640107082d036010b400d1542c0d00958001c006180f00c160020040c0e030100b00c555542002201d0a000340d50108002c128000e0b4407260f0000c54021001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925804424 1250 925803174 925803191
    0x8040606050307180f2d110d0c02010c0c0809011b0203190209090f0705100512090f0f0a082a01020c0d080609071205070e040204030f060b180114010c02040c170601140d 74
    0xd000d01f580020341c02c04e80700003040300c85c03074103420b500300782010075055000300100d030310050302030b105042c04031005000a04144000b080b2135018481d0025400100d8007403858540540e40002c0c81c1ca4007030300003416000ea40d10f900c4007c504040700700c190000740020140104070000d0364640e42c0d8008034450b041c81103081c0c0503000c1c0c00030b00460454512504002c41d0040074070b030a0842e5a568a50641401d0a510810001060000d00032a49181c80d682c070586c400c0c9041c000580011680f40d41d9449030082e00b96849024040d18801d100030b004074442400a8041c40b1600c12001c1e2210750001d114a006040807405c100050b58000003800409801440004a80d10f03650021103101e01d005903965002480054040305100d159808460400d204a07001e0010080071828171800c8103c07042075002c8240c49100500100c103c04c0c00c00307000c281c010304d0020f40d000b54540009054400074102c48004ca001812240c1005007160b000b00c0e806082820180c241600c0d800481c111845090030150445640d41004c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925805674 1250 925804424 925804511
    0xa1404151b0218040506010803040f0312020f0d1115070e04090c080d020312060102030a09140d0605041a06010203090a1a07080f0a180b0403020108040606050307180f 73
    0x5454a40342c02500c001c803580c0300941c004102500035103080e242407162100000e4400c00010032a01540c101d0343c0a40b01c81440e644d6002d00e01030030304a02d44c00394000c8003c2002001010828050402c004d952001c542c00801d10825041207a0401d188007026802002c04c030110ba0001d1504003280c5040c3c40c001020019414202e2a0400c19000341c1100d0203402c240c901c038181e000016008200403000315501c1500c556006903522702c2030300341c0c82000c125084020002c0503502501c0310040f110190100b08841050b07501c81080340c4040750112806030120641c040c0b80c410b0141c2586d0322100a000451420744000005850710500d40b045a021004040c000701e481c3c2c095406841e03584c1d501001c1c442c0c4035007410301c00d041250080761380903000900301c0c41801540c643c10010342086038102d0400c0c500d45030444c1c00450300200000d00c180c1c1c486450343c5000420f0340f01001441c0040200d1b803800c1506141101d0b58100707a6a149610503c02420700141380c030a01700a501c614a03000c1c2c8502440c0010404204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925806924 1250 925805674 925805717
    0x41104050d021f02030a090e0403020c1e0d030507030f080615090d020607230724020f15010f1d2805040f021c032001060503010905030a140415 63
    0x40240403e81d00509003220650000060302042c000341d201c201500e91142c0d41c81140b881304480203001680241e1000707019090200d112107a83e016040d88104883d20000440c00710481d40768100c0020304000340d07102c140b65008000707481600c05032604440c541414000242140c00280b240140050000741000d01d96032981c01c03c40075198050402600c2d840785052a0722000401c14180c0c0d0401046d00c140d0030b03e4500442c00d1000d8800801d200e0f0a00413034a104c01d10804408429042036106046e180e107a021410000540f1030014808182225030500d80c0c0e600344000c807079000c4010101940303d52860446041815070b40151180c0d91710100d10780341c20114001942c4424003850705450304041c8428045040c44005a05009440000c1407031200d65561105d0600108003800180803c01101c001408801800000760350040010a22a451300000303821540c00d0b44040342e140d4400624000c105401024555004422900700d508040c03034000400700004020615504100031082e511a03407124000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925808174 1250 925806924 925806949
    0xf020102070b04060e011803020d081b190f03060807050d020406120503030403030b010e0603040f03050c0d09080f0d02030d020a0311031603141509060402121311041104050d02 77
    0x300600c02070400b41042001030910f440408001c6d428440c00180811070b0840d04040c1590581c014154015800307401c8504101c080d1189500c06000411100b14840c080d020304100389280f401005130400189019002045504031007080c51f0074950100010030000c0744400c02c4540c00e440320f041d0340000f48001001440030381c2202c840700656614807410702000201031071140c0d01c662000c00038140050010342d4803151100b94180c2c4000c0400005001581c801c48180301c0c14031900b0600c0c10901007107c8103041c00b1040103040c0010703010f40c0d005c0100780d80400c010000542d20300090100d008010710025160300c2000780b110382090300010441c4416110350f10992216602150780c40d12030424000d884011080c1c948004002130a090100b900d16500030302c60750143c0e02841c0c104034075020f884103120999000401c036a612640c00c1c000c0c0420700c20307090b01c401e02c280c10300c0515031500c020030f18007020782c03c00448000d13000b076290070740c62a441c1d020703401180c0030754600300c91040c4090a90302c0051640003030344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925809424 1250 925808174 925808183
    0x15050715020910020f0712021507060b130b011d21030906040b040e101404090819111011180409060608100e0109080f2212151404030f02010207 63
    0x80540319065a0200307440018546440c150746d0b9451395140f52034000c01c0900340c003075030082007015524440103800c0e00900c0c0c2e961040202040c03100c00c034800262640f08072541c030301c8115141c0d00340a0a0b5a0310000d1170b0322248070351700704022845103500031551400c080c0781d001440d02c0b600c44e20210120000c0060301d185030300050081c0c1d0f13101d03203603560740c41560410310407009100e146c48082919190b00140040a0b03078138504400b40b1001c200c00402026100f01c03c41518058020420805081d18045010802d00a142c0702c29107580c6256240500d09502d400c40b0344840c520b030101c440300c6084c49070225403107074411081c044002070607000018000c103010400100310610f05580000c620304081260b800420302214102300c10201c0014081c240d07420864010078113030f4100259004140c040006c1c060744200c09000074202075040e10380c0e560702025034124054024003204402c0030021030585281c200403020390188405105694803140423100a00000e00303102c80c18100300d0055100754180c0b0300e0550030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925810674 1250 925809424 925809439
    0x711060115080105010f020d050f041d010602120a09120c0504021803010606050f12150a121b0e2710050402030d0c080301090203060d02090c09010801150507150209 72
    0x64000640515919031030071808030342a03100015040d03001c0d02d4407a007078034542c0d0040c001d65103648408903500d600000108241201c1404046099410b4018501c22510240c950310259410103001901d000b4502c03048408500c0d0800c800f8448aa2064a0008690452400750a40ca88510300b00715606400d410483d0420300c085000300b10550320400c1022150801d5008000701034442c002150140301d01000c029500d0340801000360148120f01441e03900001000c00864900e0b12100040c4072025980d00c5056010102c60705a0140100c08144001040c038040c3d0300c0d070403030b0300d444004902c0d088010105040711405207000440001d02c5103881c04100c2c403840c00d4034202011103104100511b400e075030a0340284901003802c0308450082281030190341c3c0001c810380c250384c0790017000340c042d61001704000c2c0c102c1d0103000c4100060301c0d0484142e020320380d55120070751500751100c00105201d105900c406c8001c041800744149840c0c01c1000c035281c042c4c01040e528464440000904045d206c1c480344150031171792 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925811924 1250 925810674 925810679
    0x1401120903080f0f010803180301060911041409040f030305071103041e0f08031603020c060a03090b060405011811042312070b04170109020301110301051002012307110601 75
    0x307011a09520a1610301101d50013600c41040c00c8416600034016250642d004202c070002e09000c120004c4000203006002082540d21410740d03109484524114042500300803c007030010b2603203102215104481a5039443c414034064440d0018401240405414035070780741c0200d40d1480c8241d000018034018501149c0e500c982e41c0b09003030f21004401c2c0003811301c800b003440045a01c140d4004884112078011b1300542c10201880030f2504030321041c6000f24154400e040d4841b0441d01d809019000e0b204054400042141c0241010031105000030040c034030462070320005001250300c1d42a03600040c00001c8000402070303100030035001c1c188a00d070071200000010a4480c3c0b2050341400c520603071040251060113582c801d00c5020390740d414081c0070b0f1609205050105125604401c0403c11000003078400214058500d500443c1c21079040c42c0e110654020004010b10090500340300c40029040780f4070013080021607000c8055001006c900740e00c01e0206c0c0318008078981c1c51207074a004a00c20300c3c1c981981c0955a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925813174 1250 925811924 925811927
    0xc0311031314030c01030e0c10170109020a031d070b25080301031b030f1502040306020c07050406300804030b0901090b06010813022e02070e16091401120903 69
    0x1105240701e4442d11850f1302016055101c1d0041d11343c2004848002c20700924503d0800140f1170400c0309480030002c44080d40c091503010500e015009003001140182e80e08130b00100103040d680c00203200d00201500c48805085070400040b5581250003480c8500e07164186518441d81d40348405075805400c0c0e2515248e0400e00114900540c1200e00c94102ca00310303503a20300000000b0f4a0507100c00ba10316003078200aa40403541b10740c540d0900c02d440b42d50044c81d00e40c5940e950012030308100c0d9100f1403035025000074007150402e40300d01006000850003405c460100003800509100c0da2411406040844211000400c401d07c13043e140034641c0000800814500390070303024020080544261044600c0c3c1c0013080c61540507001d168000c82c60000d1003c801d040343d400740b20546c290305062000e0ba08100e001540305075140000b0b01c05203540356003e001d4a924100c2c00050707004000c0e001205110724000000113503500b0941c42000c88070202c2d04c1c0d5070846c600da40140c0302c04100c1200c1c0300300c4c2403d2940020406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925814424 1250 925813174 925813199
    0x5121504140114151b120d050403080105060c030a0c15021903050109060f0302092a0406112811040501174303050f0d120c0c03110313 59
    0x22510400f440804071a07503c10060f00890030b0784140c1500c0020401c6030310202445405040c0e00001e0400c40c0c0c5840c881342901512030b0301910100d4012582c1d038003400201940101c459005010031209503080c0f580324888581c49100d00328001c1d040c8001401034000300003c1130640c1d604400311035030841d04d40e440f040801211095803000310000900d0280041104140392007080309075000f00401e0180141151300f844917000c005004030550052444040400d12400040001c80f49400001c5c1342d1144e00c0c0c920b0150040403480c104800f2508101c040d200282d40071021034180300142e41600d4550405428a1146d01e41c04000f001e4105040c0300000ca45450004200103c50002104403100078401c80c40101c0c0020841144141c01c40b4900300409807001c0700540061174403a072202414480d40c2e20b9448501c0e00300c01340e180b60034981000c0341205415800006420f0103040c0301005110410310060b0041c10b081542c4002014081d00ca402802c1d50b1108101b56150b44c500c0030001149140c841e4200d0544 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925815674 1250 925814424 925814429
    0x1318060c09060212070302060106050a0c0c030c080c09061005090a0306020d0614090412080603010e1b031c0e1905030d0e030f03160204020714030d050901060b0a051215041401 77
    0x7501c684c081c4c40300394042d00c004481c600c58055001d0016a401e0040444d0940d0109943c0c904000f1445001004100720b5a00c0b20001e40c45031201440b0145000006030410a42501e101c2c41032141c0b4003040b01c1d984031710381c0000e1150740900d0135640d50640100081c1008519402c0a03080758408240300304c44104139800702080d01d94080707004a1440140b0204281d500048a006240d100c0c0070b110702d551140168405034129400400110f250740d070107118186000c1000050340400203a440000c1d000b81420700070941c004c3d040c0c0501c598407100301200a840340d4203040b41c0d03500031015440b01e0140085c8990440001d03150040c20f40781c080410704001041000c8441c0418400d001d020758080740103400000319209041071020111642c241d503000c101c001d420100301662840020801d05640d00410b000a1400c2d003050700740041e660410040c0703a400c44806030015040710908120a64200d60020b081c0c40c90092040540201996500001c4131041c5007524003d40081c00c0401d00c280c10b400f4444c1e01c506 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925816924 1250 925815674 925815677
    0x1c09032007061b150e0102041d10050d05150916060f03050f090a060f140c03040501061a091c050f100b06070305070209070c1514151318060c0906 64
    0x1180e80501d00c4200740803418030f0040c104591220340103c0c00c00c1c9600a01108407a00c2c00050034150740e001d100f0152180b1428082c40810a0f204001c0d0000126004034042c0c0410b0382c2041c0b41034141d0b61074980d030300d42c90440360300c2181e0103100280001004102061407481105d0417004056651780001d0008101d507500c1102080c05e100c000b0315024002882d5501c2a415100140740b005001e48503032000f0029507106091240d2560100c901c12403607000c48900401007007829644e02d181504010b401c40b0700c150812980545020207200200d88490140e90b0322038400c868201d0b2400c1084070a403900324010400419034012508100d00200300444c511030041401c0b0030520280341500100012807040c1c1400502041c4280481c2000d42021400e5035445296414038000c0404c4586a000740d01e410410850100c0f52a031103618000c0c0e0b1441c1c800f0360000810b05440070500c0300300b00081d21410420040c1c1c92100d50ba680c4102007091001c9013800001d40001041103103c101c8400142818042d02400d0b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925818174 1250 925816924 925816937
    0x240a0306050601110d08011206020705030a0206091009021503191e0b01020a170c07080f031306030207020904060c02070504150608010f0b1806220303080106051c0903200706 76
    0xb01c4c18a40800c00e4105d6020a030740c0d032146030f030a2240b071a244441084050307a00c15030a02400e4005041000141400c0080340c005181d00d00c1c002d00910302d022030b255a04042c0d2814130b42494010f807910450501c005561008076500c0c4e6480c03a0410340c4017520240880001410f080202c000040d580103a0300141c00030308424031901382000016a0b48460301000140202c20f00170802016010f48800b80068100b00c8050360429660b405c50f0919045040d0542c03d031603080080c3e600c40064110300c6040080c11242029820802180c00203603101c00d005001600c81600e4004c004030081c030a0202704003811000b0402c1041c1e003180c040f1101c044000c0c1c000c51000c03a000c81d00220f0104d008403c9001152043e00d006803070001000348400921011a0001c1d07005801441031603c210340301d015900f01c00402c031072588070062135814004e2080070103078030101c28007400f0081c45d2810900704105220f070240c6d10001054075102d90ad03084801145401c0725403504504860f08049804000c1741e03644c11150a680c809 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925819424 1250 925818174 925818197
    0x60901051612180807030b25080906150105191404061d180a0c03181b320d020603010b1b0606090f09120c01150803070b240a0306050601 60
    0xf110110401d000b84019a0f000703160420000304071042155208018203e20264400b12503100e015041070442d000000c41c0c2c001080200340b03002040785c540e204000d200e4000e44109010000381540c4070390805044000151004444107500442030241c0705880803540c99940c036600c400080c0004d034108408902c098074680a00b0044c5020750840424404403641c0456907242e1500080040c40171001080905840c2c0510100c5110f022940100950081c42d0004130004040741048190000f9009801006080c4508880d09140098a100c40300c040361035114424910750300003003140703810560003903000a0000000c54021084806050f05510110b001e91404503d5a0b0490f01d9803000c03100704d030f000f41d210b90014194070025400070f504581c041c41a101c100d11481b40e628420352007510f20000607034554081c04040c4444032165001801c10f18051401c1c40d440e42e4030006001000740c00d6890384040207840d04002842c040c80301201c00401400d01211907640d240540c042c1c01c0c121216804261100401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 925820674 1250 925819424 925819457
    0x1602010908031911070b0a030e10050903030601050703090b0f0405010906080438040506100b090a0b03180a0606061b02090403301407020d0509060901051612 69
    0x1030303501c01e120740d40c81d8200b40c80c240315040fa0f134844102038280092088440c0080c841c00301ca4002c0c400d410321039401080480a1869051030600e914485d05801d074a050304102414401100340ca0300500240b901503525445c2d4207045501c4000c03074018501c503480c0000c4083d00d030500b0400030401ca0354207032144044540d803074405880b6040e0486024000e18010030000002208811000780c010b2400c43d42c0003008a0b41540205801d4011101120b042d40a54140000342e490450440010524000304501c0e25040380042195224184502d280483e00400880c23503062040582e1100301103007a0803104c00400b103062920141c003140c41a54040b45c2e2072041c024125801c1d200760340741150050b100e12200d48550347c040342c840c041954001c44400034a034075203000c0c19455440a12501c1c003a800420002c003c400006c1c22118080c01039030655012006050b105500101a20b400d46011a007043d11484001e0040c0c41c0351080e03800080c03010b038030b11035054100032002c400d001e18142c81b9640c10446001d18041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 925821924 1250 925820674 925820677
    0xc090708070801050f0d050a1407090606140703020a0b0f04210f0c0c0f0308090f1804061e0f0c030b030c010e0d170304050a14060105100c050a0503160201090803 71
    0x706800096001d8006000c0381c2007800e0080c185d000050b02c2400e00c28891f4840070306004e01a242203070324410000360a0514442000184041c007000e4000300001c3e8504075001d0070f02d00c1051601411074a0106038030043c58002c0c0001d0a0080d0031810315039403407400e460a15070300d10040307404486c00c01d9000c14014900250080b102c0090071180c488030b0244440034001c4c2c4416003188401c6640190031400800e251038007420920040d84280c14068542800c80104180c0b41065010103000303111010a03649a88103802e5255045a00800001140b10003524000c039032a810110b01d20340c0e01d08050700c0802e403181541c0241700041469a0030010328202d0000c250f00c4500001c0814001491a00b00117000d01d044a1048003c911800003014241c840300603811854004076019500b80c0c02c03100349401800600c00c40403200201c0d540281641303604001c0001c0303e0018030414202041010f149410802c60100300d020325040e007140032a901c0300303101d4550b412804035002c402c03070004a02d66000a00041b0010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 925823174 1250 925821924 925821931
    0x42a1e09050103020c0f07121403093a08040e0610080114010207120f120305040506041202150103051b060403080a03020c150a0501260d0503060409050105090c090708 73
    0x240e810400c18904001140030703401104800282c0d002d404801c000e83c1d1020801100140894100158489070504008140d44152540c03240980c004101071a0944d450180b030a91142d208190030030411a0707070f503154010002ca6104e52111100921461061102c0c01001c0e1003102c80114036492180d58400501034550b00800c2510041480140180a000d485000700c803c0ca0f1812310440b407125658003200006c54142c614141c0300d00382441c01c418188000c180c2a0038401e02a410180680d080c035559140d0f660400800207800788000b1100b00d00c44074401d0242c91008075201d28608441c0d43c4a0500540310100b224104020388500e403110100342c02c1c040180d13400c69812912160801205000035006581710100c0c984150280c9a03110004000d85130240e80100018800064603604240d20b240542440031440c03582d011100c112240910800108081b440d6003600d000c036120b0301e4800c04500a41080c0400400075400c010400840c62000210f800c105c00c400c072041c0540d911044002c0e00e1554065 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 925824424 1250 925823174 925823177
    0xe0a09230c01320a0f0f09030308060a0302060309070503061f15090305240601050f073002100b010507050a171912060f050d0b0402042a1e 61
    0x1d2545164540c01069064401244805807650320400c0a00c1d4040325001d4002d801ca40500c08605440565800380e0100b00340e041908011b49403094070000901200d0291000400300101440082e115442c2c40078500c004550103480282c50307080005c2c43c16200e000740e01a140c068415030300081c03040d0364100240d01041c040d164903406842d08203281541500517000800d42806005079002001580c00c2100035030340c40c3e04840701c1d896070161200d507001c1d103000030704581d041043c1400021800d8800608941302107a0180114901c140d288031058a89100b00c1c54081c2265540101d0f0140d86801244007481c4c10907407141040180300351b1006542a00465001520590043c80c55500150b0301c020991300300c00e8010b0019080040011162400c004507038a01c0d80080d003054120784485841f401040c000c3d00c0d90f1409401c003142030201181c000200404068684c00c07462001c10195281e40d40031511940b200040700c00348010340701d1080300c2e0304401498440060440903041c0700800040700b0300203100b000da = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 925825674 1250 925824424 925824433
    0x1b1a09131a06130e09030705071d0f130501060f03230c010813050604030f0206130b07120e0312040c09050105011b1110020717010e1c090e0a0923 64
    0x2418107002d142e402480c2c0120140701d008a01094140c0500e8000c0d20072040c0c0e2005540c0c41c0600d162090034a601540611070458004000c0e4a4030504070140710761101030000d00005555429846081409400d60054903651800c030300403480980303955411050703074000e42020420507071100f50030a8854080c2c0007c1d0030b54000241c419400c0d8031414440360041c580700c1c00d081541046448180c2003013410b45045001c600e1380802c4940158040c06403540c081c00e00440000d034a00d4503160f517031401400034042010000f0086902d4540e513032640c0410210445102100e48038001d04860b80b40c0d08806a80a50700d07003090f01301c00a100c01c03550107264180c50040e55005105101d00404107001e000300081203c2000844818101caa00c0e004a00c220880171035009003070b900e02e852001d040000000a549541340d040104070811400001101000c045088100032018200365000319218141038100765500c0c403964042c403600511300d4110446241c090660140d01952009003001244001c00840a29402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 925826924 1250 925825674 925825721
    0x80405060c030f0d0609060504020a0801050f0a030b0109061a31090203041112070311060901020f0609030910030e0a060b040204050406030305070507061b1b1a0913 72
    0xa00e40c01811120640e1021207003000c402d40d009041c15001940801c034440e0f5154800c12295042e0f00450000b008159811031401d000c003200100350140502550380204104c217034030705c034545a012002009541004041d2036075619003e441c2d014001d5071180340e1200c071030050304458180041c0d0844070200d14a0740100c02d00210350b218882c46c2003848141ca4a4444403940000d0f00c110140010b51140f4841c00c11031105030b100c1c00401809544025680701680d10200040c0300142508413203821420049514540b540c2c2d480300100d2404680305100c2aa5024001c14049501000000740c0700f41c11089409103400102d00b1021411034074a0600c006440d84100070742004070312a41c0c019a040d000107000549400e49170301c040740c1a12404d0f4001c82c0051340001d941014000d0a01c0700c1000b503d0145000100802032a00540e404803072401e0191a59003094000601e0000c900d0ad203000414030031b0301440b14111050172090850304440d81c018040c6c807100b11000c41c15400d80c8a0103080c1e01c04094000030700395 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 925828174 1250 925826924 925826929
    0x40806060315011503021c0209130219110c0409030c031202030c0a12060312180b120403050307050706330609091a15030615030906070f0309120203030702010b0607080405 75
    0x481c100304d81021305074200540130000d408803202c0000708002d50b20140c2c0c0d42100700d040c880c40c51030801c1d5035100203205005031920910003a11002018486103080384400c9200002241131643c20441140c2c020310b4099100109030300040e05200080c081d407110f201140418080c070042e0b20041b6885052038504010201029000d195007403003c10125074001042074580c3d90740070003080c3c1940b01c500424102a00c00e02c49d500480110800b41500c80081802c2001920b401c69600d540604002c052020110004c0c3c0c02b40c0c0706105803903031950040780c14428408084c0082c0304000b20034000c0c0706507420105807824250b10182130b5400f00c800d40d0307a942d007005143c80c000e14018555a150358104c21030b40f078044003456980004400030702d80c00c840c1c4e0300c4e42c03402d01d13208004c1d120740035018941c07402c038040c41084902c40c0041619a480406410702c0250780035084c4c0110001e2a1498004140d421300100d285016980003018503c02c800b181c00030481c0170301180801c0210f0040680041510200f007200303000a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 925829424 1250 925828174 925828199
    0x1902071101031e150f060219030c240b0108090a0b0411060f030f1f21080405060c0c010201051506030c072409030305010f0b0d0b031f0204080606031501 67
    0x15840150303070301c03e2600322444603040d5801126000a010445401030028000039807010005258070b0004005510103080102080740100c0c4000c0c003408039030f01c070207800d10191a9138005642c0c0030420380145c0c2d801502c64200140702442c40c290000e41040001210b0110001d10303921600c2d00066601102d030f072f80365a0741112000c1d8110250700540c040c42200b0780022100095400b6003207241001e956460702510000f542030860007148072003044110708000d0445800a12a003000c44003d6500c0d481c110b9050203c000e00c103940c003143c0c00000000d00e0941401012441c40c20300c00090b0b0090009840e2480903043e0041000320070b644c8030030200003240c180c2c055100200b110390300ca00703840c12180a84c00c034180c80d005148001c040d5035640303c101c01d108050341071151034003500c46100300c1c01515003040c0418006019081d0446142e0350342d0205000599002c10020311076106402090942c001c81c43c141c0300c0a9040761142d8096403003880089400d9240100300c41840404600308001d0607840d2502101d8003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 925830674 1250 925829424 925829441
    0x303071d180414030a1706040c080a1a12012301182406020604030314160e04150906030507091a090a06030f0b0403020c01020a050d05090303040f0905190207110103 72
    0x1104840d050510030030051020340301d17103000c68036102100d549110441c240190000c00452141d0b01c0c119240c00c2e4940c1102105411401e910350000368104428615441030801c40c10407688182030101240b1054015000201d11041a02d24501c0201d222207014249420a009114000508421031206175002d40d000502e01c041883c4204881c418980c0021030051003500b01c0d0005800007001c200915806000e16284410f210360031701070780d241502840c14165154003800307003080004800ca00301580c07107402041c0d020f0907000c07000010507610b2800750020182440121602d0054010008001c0402e21900c11001040364041d40824511010002c03520b038000c0c00d036204107941d0350000c00400e03202007a88031014825140495076090508002e0f18141600c94010704550100842100150002c00e1101d80e104ca00e0520f1070303c401d03c400000e41103016a422052a070300440c0360014910182d50411401051740d41c0c0f03001d030510050b10b40c4009074442c070080031b050b18400303000c0c0003150351081d80007290 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 925831924 1250 925830674 925830683
    0x1803050405101716110a0c0510121b030e06010b041e030c03060b041a010915030618090303140f0613020415180b040501090e09031b0303071d1804 64
    0x114803090f9410b8a5200040d200c801ca030412400c40c805460350000c1c00c007441e400580008005142c02985d4403040030b405800f82c0c0d402014520601c0301141d01460000d03900018180f41480401454800106a000300141810000e81011840c04c89414049121410781e40c49150300c9103801c3c01e210008050340c000c80e10021b03152241030000000300e47c40042100155204441c0071440403451420441926031920282e803844440a0101748640e8200b003500b1704a07805e0011014070004901d00913001130000c0e90188600c241c034030410020b03512856010a014510a45042100d8040d0f0040b1024039082101e802e000c0700f5407800480d115140003541207000111001c80540340a490310a01c4400301107080307810000c520301e400c03040d82c0d0510203180761000e4041129100d0805140000081c01c081c468803c01407101e1719080402d800a1050044501c0701800c01301403030381d0010417004156298011a0111300155000071044205c6d98080500a841c440c010080204600740019080c03138160050300445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 925833174 1250 925831924 925831937
    0x1110f1612260903030f09191511030d0903020618010b09040816170909070305091015170307050705150f030a0f1d060903210403050c06010b0409180305040510 70
    0x4140d81c0d0410003801401e45040d903041d10b41011f401030000d2444100ca12101c010711091042c040180b601100d03110302481072801c0400c0c1000441d03402c0c1148a5503001c0030a00f4100703044042415000035800d402100c6002200c955540d400042508035407102a98981c4070500c2c42c049404240218090074100050100c0d8101501c4140e0b1262486400c10880e981c40600c041146600c80c903101860540c000c0060409004501c2c101a4440d00c0d13114141024046568520010700a0303080d0303210103405004c0d06071340d400703641c0e03a0b03110350f07036a2500000780480300c91103240340105031070401c1c0180513921308900c5001800c060218244c450b1542004021000c540d0380d49949003014400c60044007401c40b130040c0741541e0003a40a40050030520001c0506581c0e03401049004100076000c1003040c5c41034500000313041d081d1154603085409200301680544984101800415100b8080e4000d00488620074030400c4a4880b684042c2c10aa04000c800b501144060004001c0750814018240c0406042d2410b413 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 925834424 1250 925833174 925833187
    0x804080115080c19051e04050f04210e0409030e10030b0a08030f0d0b01090e0c0405011e022509090b060108010f0e0a0b01110f161226 59
    0x118212012440850001080300c40304210b9041d090012a02d02081690b82c04544a4014141a02600765204081c007a518800540980307400c1c014a10300e0400000300240800d0030410103001251005460503200e92102803121a01007407246055504140940c540140340809202040014010881c050703042c044a00c07039918160f0f480c581c00c14241030322500c0003d40b15400f101030148064945d003212130180c0c820010810b004040700251802c40d903243c10f011810340100310040b0f440b00c0280c3c1c402503400344141c081c460003c00e48070280007641c000f0b90ba440d110002c3c9407090650007100c1e018800143e040341645407000034901f8402d810341060110100b1f066035586a26000b1680540307825220031305480c040c441c0c0d569004025500500562482c0c801c000e0800c806c0c100c000801070f09101c0b0b003d50b0381480c008030b03900800282002011905c203465103038034104055611200c440400e01d07005980480e01042c100c610f103501c40c0741c0c0341c0c00150900d00348102d030000d01c24051003954085201401070107032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 925835674 1250 925834424 925834439
    0x2030c0403020316030314040e01030204090f08040e1b0f07030c02030c190f1410111005012304051003061508160f080114070e0a0308040f0305120304021005070804 72
    0x3122115115104c807110030600d5824001c00803a655907084001c10010041000300d44481000c940c10b583d0111800500411a03140112002c828641c000f0011a0040b600040050307403040038511880c2d81c0e01080b8051652050941c10b02d00c520b0225a12850041c410207000c64403d8441000c0c5a10182c00c42e4101d440d9a400100c0520317070f281809541e880c0d14401404040e000303036024002090351208c0c8030f40c414a070500080c80d604500c010041003022001540300d0285c1c1c2002507404c007504002d8100140d58494160741081680e1906030780401d60b03003480c28211800c0900c00c8174450011380405040d00b904594600014000d03150005200c06a4800089000e1f0024440ca030007065030fa03a940050246865222101140d2907840003495900d0107040944004000707075056404103480c609056a511900001403480600d50009003d2110100340450200c08403144001a80c0c001c00448601844200440d0480d10040b20004c3d08503070b4108065840500401c054003401c1c0c03143c800c4500702612030a2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 925836924 1250 925835674 925835683
    0xd0b0a0f05130c05030601081f0612034a01020114070504050a080a050d0f0c120e0118240c0503030702070f290c070306090c09051003050a020402030c04030203 70
    0xc05072403602010111600f00100300c90800b00801c070a81c06080a0340c9071a80081d00c81039030901c69490008031200c400ca060910303600000180c41308241c081403604090034010071812160440010b2a0380301d144c42c05140c1540d0421044001219550600c5201d01245507459050011a2241559290301d184c0d40018600c9408a20501c881c0d40c0c0c01d42c813240f408040040d003400c190b204e04065044002c2c0040821008211070109081c01d04208010034001c070011241118019005070400c0211a081624170754040003606642130240daa40040482000c00d04d1144052842030510b81c5107020028054456020241c089540080c24201405100e0341c0f1441d0840d0300444080c4010f8002c514107001914014000c04040d110180314105441a00c400c0210340720399a1151807060070001c601c80c1c0c906c0342c00700030000207160310850520110070301e4540305800304a5070203071150a5081800161008600e02000c0c0c01700ca42040003000c0307074a04c0c0d400303100c025030003d800c41214101c00c00010000d40c0f070422 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 925838174 1250 925836924 925836931
    0x129042706111e0a090510081f0501120504030c0b0405011514090f090f01090b09102a0504170307020306060f010e0105030a060e07020304060306080109020d0b0a0f05 73
    0x2522000d094103189080300896490798000101500103108600050190140c400a0001d204000a0f950f01400340d064030113800c96803141d43d10038032203001022000d5100044d103020700e148030b8110f80ea45112002c00b81d03040c3c4140c081c40b400520201c0c1c3c80c1d041301c03284d6008603070094003170308242e50720305081d0301c80c60340d2100101c0d001d407840e030f440304000c5800c0c181e20312a00780180741942c2c040018444010015482100c060280101c000460300894403440f42401400322024034240204041d40307540ca000240103074207d5401910f40039402101c0520b514500075903111505103440c80240c50520101d9810401c5465480e070204036003880013182e18400140383c82090414000150780700c40e030a104140c54035000500650007240300c074030000213598200d2121101c500c001d0a005860b543c41e03240c200000e141d9980050107040c500020b0000d03960300071005000303a41c42980c0600c81951202230751426680c44a01c002c0d00f0280340504840424203100030660004090301010075413036038501c0c01d0702c01d581d81035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 925839424 1250 925838174 925838231
    0x2030a18080624011706061812070f051804170c03160b07030e060115050d0f050f0f040c1a0c0d05131a03010338040212012904 56
    0x151001c00500818a168501d040c50034a0074250301c05d800e40340850f90800207890316018050118a800403004210444012018041d02e6480c980072103960701962115240304441d40701c0342e4008007081606140300d0703507010701c4080001c00f0065200c4d55521031001900b414007101c6824140403070713203036004240000d210f120382141003540260502e08005803803910103010101890b29101c08c0c403212079004126581101c52a00041015459008040e200e51188414840d403540c038044950100d1000c682c0064082d01c2e4510a40189503140c0740a50000001610080c182404031181000740c038003000119440c40c003864034901e04250300001031a25140e464101e0380e005c0303040401d0500101e615004450020b040c20350040380e02410b02d052104281c441800050000e107108060028459001c0c412140d545580040c240c07404c1d001d545004c03e002805a904921030007082c4c1c031103204078005009410a000ba44840004192070010780071001010b0005030f10340003600c42c09041d030b4405055100c0403240b146d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 925840674 1250 925839424 925839451
    0x108100f120b0c0702100809160b0712020a0f020f010c080a080901050c27150304030e0907050306031c021e0c0f0405071d060d020406050c150702030a180806 69
    0x842c038085506000040030602042000e10072035003d030b41c0f403201e440b0000000703060404003038840b440c895003851108501d410540340c61182c0040c218030b80e000145602409641c0500190030903203000c070384501c80c10b44c0260200044510f5440940b805024885081c9414140b1140b203401c43d5aa0121075085010b07288081800d01c410482107420a00909900241d03155102e86403e0030a01c0121040b001700c40410740300182e04141d502151600c0030012820102c00318450780b40e01d0985001000c1c1c00442c940d03a030254000901050010b07000e881924043c1d10000c010b0021005568211030780301100d0b00301d00c0f04602c2690b00320280005a5040003011140f244050440003401400f070000072015815403e004030328000401c04c109030700c24110310900002c000c0c100c5002074542c00050080c000d4001166006e440010000354180d00000188070100040d015508100e4040e071041c40480d204a4490f000340e0810046410000e2040c201ca010380e0282c540c400b90001d40b01c40041d45040b004030b036a60350400c00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 925841924 1250 925840674 925840709
    0x9030f12030c021c0302090301020705070b25080a0e0102100e0f07082d0a17030f0f04020105161e0507180e03070303110702130f0b1507020108100f 65
    0x30716010340103549403503000a1181e444a08041004c1141080000041581c00308080ca40c60f83c0a40444940b05c0e000012a103d8a0700c440c061201a81311145259800350200040203002900070300d12020740b60002e100f2801c0860100c000e0f24107244092041d81180210f190750103004226101e0141781070a00310007000c064176544281441c0c450302d50400f001310740c801c000d07013100114400d802043d4203070b00d2282c00410341e03244038800b45406d1221a0003480781c0e0341c0d040b901c00382006400145120340651560300015403a89201c40710035200a850280c0001c03010400038403c14040c600000c255803040030103c1501c00c0c4002c0c1c00244518441003200c880c1c011079020000035199070707100602d4000c031110410813003104044e0075642c3c0c410400000e040c152a54091007500502e282992840794000d04100c600346940100900100040880d50b0b021603d040c10108031418103144c001c1950160000b107615003602900159041003004014500f10301c2e440d900800c030300c201e02c140e610003408085c0d07031541c008a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 925843174 1250 925841924 925841927
    0x140601050a0902131e08010507051240060e06070e1f0c030903060c1206080c0d110d0206181e0f0409030e030d0207080f12031609030f12 60
    0x4407558003048006005000e0080c00680401d280811280e044484c690413880020580b4603a04540d4090002c41d4a00801c100c5000d800200078070003100c80318100305840da1800040c0380b002640c59102c1c800780c0c46101a05000841d004240d403409029001c144031410543d940d07450960701999403000c02a08810180604650410450444e15000300c07046c1221500281071500000701c1c4042060810650303071180d00906018500c070101840d00041c040c4006290400007402c200c00c280d0303c082c0400e240020000e01c010000c158a40307801c0c0003c0c01582000c0b2591511942d0040c110a02a03202c4040440b8000680e9440300500700c1001d05501c0d800c0e030051090800550481c407102d0840c0070007112003a1a0181e4501600c21060a0708440c0022142494181100d100e03030300c440e0300354040c401c032080d0b100c0d00c0350009109401c4411301412941c444400490103901d54071400e25040c1c4114080c03010644000c0188086000e01295190039540b955594607007403500c804c006800d4915502c020360456409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 925844424 1250 925843174 925843189
    0xe04060b0d0c0c0f0b0a020f030702010b0906060a020c0f03070e04030c0c0e130209090a050d090e0c0906070311030d0203010b1b07060e060a031128080108120304020d14060105 77
    0x41070600b800e000008007504d8541c121801402c1c0201020350b030743c0004100181d5a0306071005003a0f20022139451740b03050b54001e4000c1412005140c8290007030000a0400d2402c44222030020445a001d00143d01444013446034085444203c0340d41070003608004076404002e50455840786001396980c0448084c0390030507502070401030708140303407040100040102d103103031202c9001c69096050701d0650690707440d070840760308010070325200500d24001c4ca801101425440035003030043c1c400801201c0115183d503036195801c0d00c6044079081e0005d10501c900c1000c24020b01804e581621050300f542c1c41c2060744061201260300c01d8000c009c1103680420800341c540c580d0f01c00c1d4007a85e0f040d0030003811040d0500c00040d04003207050315914071803080003031510071140c425000b41500c0ca866442c2e0300d0700c915868008465108022041241420305600f00ca0303900d92240940c0c6d8102c408050141c9052040c1c050050100d500c010002c1c1d801070314442c0c0510000c0e801030512126400003d0162010754100001c0001d01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 925845674 1250 925844424 925844441
    0x20712080c09031504062c010b090402090f041403030f010f0503031815090604080c0315040f030f0509060a0f03060f050a0e0a0b0d05071401110a0b06010e04060b0d 72
    0x11010309000803603943d01c0020300f000b50b000c00d441d20f002040e510751402d02c002e044181344658028203072501800038191004401003000842d40300910035200150f00b4808010000c6070083d50141d40c96001c52040740c2d14078030454115029148140740070003840078080c80d6600903140c1c0e40e099103210004120181c124807102015100031405186031401056502c25080d6050001c14412410015248041030b0300c0c00886108050241035681c559603100c6801c0e840343c0b00c542019000340103648040549046810345141300d1684000c00c403113400800c1d18102e8000400c40c56803818810100b240d06001d54440000e000000d200f5070390104404000d41000b000c5d035100380d0100003901007050051296a40e06501c0302c0c2070b01c402501c05c801560318809040041e10b50800d010b90001c800c13840b00d2052000100300314080c0d0f09001075540314200d203038004444c0c40b00303680305290f11908012840030008040100305a00f00505260500c0d103078003141c0001e82102d849604c01440c0500018503050030101d5405044030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 925846924 1250 925845674 925845691
    0x17160203060a0207110f011b030504050f030f10110d05190609110a0c0203070504180b06030706080403120b0a09060603240e070909050a140901050603030423030102071208 75
    0x4207955a941d110792015240c03003246c80785085e184501000d034441d03031724006040d00345541c181c0c0320f04040c00d0141043e0f0050103102c0c000d071a90759541040d410005114141a070450307005209422461502c4030080c1a030842c080300d44001002900400303003841c09000d01507004805021800c0805990b01e00484180f0307440240c1207410800c0e14088070303842c0e4080c5c0701d50b120641070a11501b240351002a051904542016a101d072074081c1158082d0850503000b00868400e03840449581c0342d074010542c1c0c841440c030451300007403c500000342c0081c3c440c0103241981c600a640106542c0341c44400140864040d070018a1600e0303a9031000c004807039050080b00c1c0c44052130602e4020403050000039482c1c0c0003690003600040020b01000c41c0e40d080c41051000010000c45a08200f1810030b442c0d100b018010750700c4c00240740f00c2d0310b1340801e038002c006120302030103120b006008615061404540c50318002140720340c1400705100d01d84081490301c0a000814a2920540c000c4003041c070604c402924140c0080c3c2940c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 925848174 1250 925846924 925846927
    0x2a0307020d02010504170a021f02031f1a220e0601020c010c05070504050c04090f091a2e05060304050c10140f090f060703030b0310091e17160203060a02 67
    0x309160b45d80446e10303c021500616990004400c2c2030380703040040e410100740344007000c0345940b80c0d010a07406980030b02840c0c50100c00b0400c0ca81100d42041142c0d00481c001c521480008020207126071004006c10440c80c2107240000d000c0d040703903c02c1d0b0040c1c2d603c040100071b8010208846036030f042c080d00d080302c1e0f406d00300000429142e8031502d81d03c0c0068019070b40907030b1392100452081d01600b0180c070f00800300068188603501c602501c0401a2403002c20450318414100c140c091480b000055007072107000383d0840403c0b01c000008000706200c4840c4039184c10f0b184480e0020416468800046110b14000c1e030051149160680074001c0540520030700c0010440c4031908201e02c00070703540403185074082c0c2440680c5c0b50440d0b003000400301c88059200540c4070b480081c1c6c2004040e010f802c074030f9050500320156040c031504541c003d429104000b030b00402c0d00300314103611891000f00c184152506402a9200001d0000d41d00d10074146034040c4812015821050184504501d800c1100c207034171180c1c0740020b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 925849424 1250 925848174 925848181
    0x1050a0e011413020f09090a0c090605030303130c0f0617010902030402090a050618131a09030406032301080604050c010216060815060f090a12020d0b2a0307020d020105 74
    0x8803411400fa010202c0d004441c4000381c00d541e910f1100c0d86015100500a000d07038103100480710740d203c2000d18100c55a241c4600001804030070f42c0305501c00c0301c40c094044c41ca15580d409284141c5403590700211080400b081002c20781e0b41d482c08003000a0022501d892003440d2070051560200030050b80900079990040082100503291440225000510746002040340e849110010f00391502100e800f020880004080101240100c6a0203500a010b890000968030784d6107180544003400b202d00c040d00d584100070400c40c8902c02e41c03190440c1800c08804044603602c841100701c0042081c0d100901c5540300c18184030038480b05102081d40484240010180030441404c180c410032118400c0e841400b00d0400003403601d40c5100318100300c51900070140395585a01c940f504800790803640109000384184c12001c19070b18a0803280683c1c0a4005040c11000d00855481d41202d0302c009104c0746840450940f145250690102e01c080d4103494000d0f9161280303080c4900a107000c040c034014100b1603041c807003070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 925850674 1250 925849424 925849451
    0x6081002090a090612080d060e0403080402120706081f090204030807031206060e0d05032206090803120c0a11011505090717070f030905030c01090b0c04060e0f1804030201050a0e01 79
    0x1005c90310380d0114209445440d070300742c0c600042505034032400b8000345443c1000201035000d403040340705078405c50303000007081599884960748500034001d01c00400c1d48240420101e24041c80c540840b0340300180b41400d00c1d81c80d20a09010b90300180c0c4112500e50300892003808058100300d0303410398804259020415686045002000540354035030450140c112441d03154203001c8244116001800000c02c01021940ca001002c0503800281c851440010100700b004109964003004840c01c0b48403010854006031183c22500360541d00c12002141805041d1035a91803498080c012000b40b08903041e9120701c2245010107210030340030300400803006c0002c0c1c00f00ca1000c4110700104190005002d01d407003c0c8a044000080c0c008008280003c0d100340300200d104101b005054025201c140d00c10100804142c0314a00b1f9207210380118001c0a0124583c07101c0e00c0c0041c00d0215142d07500c280c009029001780722001c2d404030034540c41582d086d4010b03511041080078581007401191480713048180204800d01c0140c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 925851924 1250 925850674 925850699
    0x80609030f0409380f060f030406020a0e090c0a020622060b04022101030203010b01111507170406290d0213061e1508040c0b030a06081002090a0906 65
    0x42d000f400c981d50344000c4005034134543c0f11003c205800d00c40c00e038455130400ca4034000b500106921840b600c2524826040e80c2000001d44821b4800050300c0c07411915141c0d81e080c040e4101d40204010454000721481d2265540c4038660b009182014805544032940c01000707081071801410746c0c101f4010000d1807104800d801c001c80f003a458104600086040c0e0307600008010740300d8900314080c02c0c14246000c03548800c038110094100d0b44220020005c49108800555400c0c802d0386805502e5080020640010070081003840e40c044158613085500041c1d008112501e4603042d5002e40f0720351780d1254181c0364800e009160302c0104850001c82c00e0240047c4001407590784010360020300501c1c058001c01c46000c0c031a000000545400041d1070030301c03029442c00da080310829104002c1040d014501d0b13400b80c28081e90142d4004c9402440c1040128108403405000740d0003d031003445c003140d80300350000e1904070a00040411351008400503030380340700354401c0091940c4250400c840c61450810100808406e482 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 925853174 1250 925851924 925851929
    0x160e0f011509051207050619030b0315040212010f0f0f1d0d140f0a0201090b130c05010809030d0c180501030501080c042706060f1e0308030c160c080609030f04 70
    0x943d840e51106072134500c00c2c02c00f00e06501403a040760010916001c205c0d0480340424a1403420ba0313003081a8000d040030969190b621584220f005035900c000b041c0981015000000c004a0410001c1420200e1f18043c808540c0800c0b07084d80031598070504003c2c0030030b250044010002c841c0302007808580d4903001542c1c9440e00d9101442c240031b08007d8500c0c0d1010400c0039115135140c070312042a1242880d901c068040d0003240811100d505500000445145490b03211b40000368000c0486440c00c0c2c01c0800540d80c900c0040e1940c1d07072a100c18482c862120500380150b84001000d60365030751404000034000122401281c0040741410b0811005100c03c240010710781000308411580840d0144800504804510141841c0001e1180318428501884601d0b001141150896010a04500e036074a00c1d46c40d400395011020480c10001c11410400708a214000d0740d0005440280385181040a0900549420818004442151048504108028040c00b40356809481c007006503152400c07066984040e0312590 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 925854424 1250 925853174 925853179
    0x30402130c0c02090c040e090f030a050a170916060c020102030d05060a08030d0605100509010f031e0614120304031703040804030c0905100602031812160e0f01150905 73
    0x241d10041070039205403020080143c014044107074604000d8200780c1e650b4464051641c40410380c00c04100c4103000040d004034169440c0c0040d600344080404119990740c040d44041e001c0111006004901610305109113000f160351400526105501d070801e404807d1566000302c00f4080e10459440160b60040211182c015040700e00040a60b52800050000e00c034540120500b840042512010865a98007070300039100d00300e880d03280860325480201c2e814403e05060341e000442c102c01120b61180250406031841d40b07805e054500b81010101781e4401c5800301e80c800c0030030700903c0415020f6403c1202c00c0c507040c0c2c0c81c0c1601551400e41503803200600750b01d00f00888081d24000200090a00a00d4420380d006076901102003200c8a41c0d0750800c070080c220036546441d4000414000040050000048541d43c90f0703503084c9080c0a241286c10050110700c2c001d00e20b400703130052210340c210559400d0107107406032181106401c1c5d076060021102d8034041d0140c001086541c2d21074070100890340c003c1510000ca4508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 925855674 1250 925854424 925854431
    0x130525121401020708130f120308060103061a090114030112080715090308190603030e1311070803180a051e0a050f030c100605150703050c0a0b0a1103040213 69
    0x103107410918140c400848070080c1d4408101d02040000d054003c0010042038a2a007a40740e88074500d40ca87c590851041e5076036001d121121000003405000c200703502a01c1414006209541c4031140300c0030007080c00040403080300019060350150380240e40c410b0000c0740100342500b07640c100394540c008401083d102401155000c030b408405c02100c0798038810b003104004c0c03062110400758038015001d0842521440340480c044505000700e000503100d1101129059951032000440315021700158029030b844504081d9100c8100f4000d18130804000c16000d071280c1440740c1c2c0d0b45060349075920542c1c04c1008031040781e04a00100c41c00b007040040c22a00007518518100c04500400c0342d164038009500c1c0008200d401125010500780d0000300c0036102c0010310006490390070145904070411075115000c4e095124038510700154486034460042e0404512038280946451101c85c150f502d001180c00c01160050700c0c1d030017000313000310090281d21181c5095041150841c00e2582c0040c41221f109503280c03100781d58 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 925856924 1250 925855674 925855709
    0x1a040311220204090c081806040201081b03041a0105030f0c04021605010509070510030c1b050307081602030106090c08310605041101090b0f0d060e130525 68
    0x520a107510407024803542190b5580da80c901c824058522000500089059200007421140400208400386480c50018000c20380c2d440c1e00541d01c0400c0940030030000018800c444980301c91903001103010b0b0340a030701c1400c2c0700d5081b90104d40f0300550503007006000c1d0300601c0b808950b01c900055030f100781580c200c2d409a181c00c40ea240303007910560f003a40051300b00d41c240424000d6042c400b04032102074560580c2c54100d41d0500803c198140e9050328003220000d5541050020101c5521a0002a841c0701d801641e02e008240d464001c1c00b50000d006407868a030100c0c95900440c60240b14003401017501100c28028220402c00207406054002c0c6410122590710820040740940150b0920301a228501e280600683c0c5003014001000c0c01c5400f1a01070542201380c100c998014103400003103c0041200600d042224203a03501140c101c066404080c130384520001c50301c1c01030090082e10400d101c007442d151030b8015092041c90454081142c0307040c0145070000a049498445016007580c1000d81e4030340c0c4000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 925858174 1250 925856924 925856959
    0x3030103083406061a0409050a09050307030908102706090c1806090212010b0d0204051008040203011b1b050c03060423010203160e0301090212071a040311 68
    0x1141201c420001085100c203000e01e24402d03440d03403556401240104aa5501c1d03010850310740050490710000c4403c144402c001c2e8109035045281c3c0202c40c4200403a04900b2a552517146400c45841203000c903510820920929070108480000c1d10300090050112580721003202155000004600e001e401e070911008040c0115500445103e552009880c906159111410345411440001440314181000f000040f00b000d14001c0e1401c00b494034100300c4a030f03440c01d2103aa1103580205280c20825409000000700307136442c1c05084130031094a441e42101c0c6d103040d10416013121000c6032050407402e101845080741c0e0740d0080b10024940300751030450288186a00b011442c0c04807012040e581071051808000401024401e6161600a168003050003198040d20031400d03408112481c0382d00c44400350400d0380380717485406000405040500001030000e1036401158404829244000850340119401c0003040c2e5404a41c031403415904190b181024159580c22420b50242c890003840351242ca4101040785 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 925859424 1250 925858174 925858207
    0x7170306011b081e0a030e0318010c0f1718041b080702070f080a0302070e0702060a05182a10020c1e090109091b0e1602030d020a0207050906120303010308 68
    0xa00f95542c41030b070716040c4c0c1d582c16082e40c1c40314a064000a0403c003510b003140c58008161381e4001079070582007003421840070045544c008140800e031422208124510081090326403074112941803191030507900c20113500b2500c80c1e1412100064029071034506174007002400c89010208891440c80c00c0012038850346012407601c18549c001400c00000c280d03000807d2640003401e040d040303129030203a40c50a070381c2e0800a4402e400448891000d41c01440005440344002d500c000d6000d641d900e019a881421000000e241c40a01054841c03103010303106000c10034090341c203070b102d100441c01c441c03403030102050001c0207464611801056004030304030340c01e01c9101102007840c0e400e1a103003e04900401d6030740d28160009800c01080c1034820040c1c0c0314040c0c03001250540d10307000365000c00b103010f04a61111090f0400d0814000f1001d011030106004041c030095580c0014420240e0550040c00c65500300b1040289044c0c010303147c14815180c0e42e05d140d40650f808002d807030450b60040c042a407264110403015000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 925860674 1250 925859424 925859437
    0xf04030c140f0c0a0905011a09031e06041506060c030e040902180106110105010e0402010c150606030603022b031805030a030f080601030510051c0f0807170306011b08 73
    0x1402080d903605400180083c000b803140400b03c031140900f40d036404640c1c04a0b0428012003101d10205034920700d2000c0a5001040700d500c0140454108440307a054008241da161065001e141c1c22038414401408401c44541c400381160301020030415241100103030102100500060501100c0c0554444a40d101d50005200580103003811107124840028035149c2103090007040c010072030582441c0c2088a051086c54161020a43c80c0105510b480e001915001898042202c003010780f010500d920320b000e402250010150b54801050319401c520402507900c8800c00400304610340d203880d100d100010010180c40b040d8150402010500300c2c003141240e01c2c007168108d59003521500461004041e48400078948a410990b5921415260361004406076002070300e20301d030b01141c181c0b010310071880c00c2102044882c0c801400613a48203815500c40c03142d2075042400399031200c00031400d20217020840c1510350340e80c04a8031190785036140040002c0d1010390b20912a61011000c040710b00100000d60044800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 925861924 1250 925860674 925860713
    0x415050c0d05270d08093c01110d2616030f092f0405131412160f060e0c030106080309060d0c022415090f04030c 50
    0x1d88209844007400c20b5218125004245101ca60074003040d070f101c000c91121443c80204449080440b50310b50720001d802400244e036120020503054504031581c1da003c040340c041c41c1003803031300403072030a0329040980550068000d0603c107645a144045003008566821485168104400000e40300400d54a03280b404520f000e8560340c80600380f104102e130005026410001035602400241c2c9015049016200541c0c0000d0203a4041c3c22004030000e41616000c03203c402d080b008034180c0b1144400102a220b0940c0c02034824582c2100d0113080c410304116540c44412410014617017072500c1808401184500b008034008442034188003400c2000c020034081c4800c1e0826014880485146200e0307440701c00c0c076060540710750b00e4000c00040e40600481640c000350301c01468141040c860502070303006041c0c000e030506d04601811610004407070424200d510b44d09031506a040d071078640344202581c0f40002100c0d40307106500c03690800c40f040b038003210256070069062506018020719458404601c0c15007402c1c096 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 925863174 1250 925861924 925861933
    0xe15190915090504050c0405030c010804080d06170607050a0912021f080f0a20090f0a1206200403061e0f020903010b060a020303131b06051b120415050c 67
    0x1110766501140c4441030b920700f01c0d0304026030380781c0ca0014003d82c03040e13100383c0b0b4158000c140c00007520760050445607805400350303500710715282d8000509012078100e500204194460a4081541750204000895000000d4108140b41c28003201340580920003521450f00340341e4800300705104548031070842c440240541e0382c0303080b4545a03800c030141480404030340c02d9174200c081c000000d0100f4403d00400102d0211008403503070300b0f0b03400c007a00c0c80c081d800310201c550000104185120f1381e40743d60a01c1c100401c400e00d042c0000e85454a05401030301d421100303010318140242d090801a400107000c550481e035008070700264994900c440fa41410303128012081490345804800504202035400a0010301d004030f000700301d84050282040250b001c6d09078005c4c0140d00910016148241c2c0b20002e0b41040c0c01141410a5000a40001c3c4c40c000c00f6a000040010000b0070804400040301070700c20703100c1000ca00138102980000c96112041e020340c2c4611403480741920b144e42200b0380940200c420651403a030544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 925864424 1250 925863174 925863209
    0x303020d02031005040f0605241b0c0a09051033030609152907050604030210050903031603150308192d08041110020c010e151909 57
    0x503000c0c00aa4883c0303d01940c2000d06034034100c0c91900c00c1e98155440102000320031110001d540408805824081f810500104220212b0190740c4c0c0302d154080380c802c001001c2c01042d02003400303000f4005900104070036040c0400d228500303400c8103461041d10300c264503c850f2924100b031154240300b0b40a01c00c28004942e443c155030003d0303140d0042000c1c1e410381542030115150507100c610b80301a482c800c6540f420740a0704c1134550200070010360a0301194001c903650070148a61107107420700605460480240c0c0c0310500c860b400d50f245005041d400b28042010314118a083c070090341071540c901d4855020140e84203040c40705144a10120f4014640003518070342c0707070a80007210a2210030301e1813110012a034000b2140800754800c1c201c0034a4040e8400705030f035940100700010381c0c0c2004090700482c1c070b80200e1030303881c45280c071070300200781c455103090303005141c07480403000003606a0801d048964010007480c860b0856088107581100c0800e42100701c0b84041280d4010200c51001c4a030b004522004110b5101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 925865674 1250 925864424 925864441
    0x20702040b1806010f0f020c31050f07090e06010c1704081513030516050c091e01060e060711120a0506100816090c11060c0408010f0603021c0303020d0203 68
    0x143c4148000c3c0c0b14902d0b030342000e190075261120300b8038490300180c3c4a410980303803a0825079408103500300c94003802c91240c09111031000c0461036008070001c06039521810040c150a0390710782c181c0c00c000907080104003a414141c2d909002c9100800341810b100d07407038403031100b0001d0071b10030b248070140190b020350344803601c401d0404d0b1185900201c00a45000e004085102038080c3c203640c01c01c6980c1921414a012480100e010000850520036035480c000ca4048050580710360581c10700c0351044c1d42d25510704030700c02c030044408100183c104030204000d4a05a804035200e40c5c2c111044540c100c2c807500c040081c01000984c804207819100040f80c02811307908010410006405070042403400106464240c48108042e84c441c0160b901001410410300d04104c41c5909038400c080001c500e18110701000608445a45896800c0d502801013250025041048084c203101d050202c07007000d001801003600d1900000d00d4001444c01a51202c0c42c110281e01c2050700aa04680446880d404155200e143c0b1100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 925866924 1250 925865674 925865719
    0x120f2009030a2306091b13110a050409140118021e0d0501080d02060601021203061c0804050a05090c0f0a1e0207030b0702010203040b01230307030521030705070204020702040b 77
    0x81603045481008080780703410401240e4007000512411100c1031807164a8100401000500e5441d807ca903640c04c03110540d03c2011000302500c010580b0344940d654a405181003c031142640c036585032850031001030006501c15000003400b1220a100541c80c5d1700201c81c0403c421000c100703141288980050a01c2e04102d080c2c1000f8101c40480060760f4400000c3d0409907110300049910a0043c2c1210f04920404a11400a16001b00018100c101040f00c00a6000740319070380d852080c0e4a90b540070904000c2c03850711803400380143c54155a6001c29042a403082c5000d03000d02d0f1403400004c0760110780002250301c0703945100900c2445007690b02d0408000c1401035115a028001924a0b200b903d00060a0354014000c80340180e9004000c016980e2a00e403038880c01d4110121000341101d202c00c00481665010000301d000b0718062f86c007924000d2003a143d00240744440d0032003030020b48804d00c1080300443e04074054034001c0390182e2b03015940d4110392000070020096014041c0d804a81c46c0c4141050209400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 925868174 1250 925866924 925866983
    0x501030c08010e0d08190605030a1406060102190605060f06120106030b2b0201020c13050f06010903021c0807020612190e0d0e030715120f2009030a 65
    0x3c0140e01c60807a8469190a264011600032030304100100741500310381e8480d505030b2150250000713007003500c3d0030001c0e042030f080c0001618044000142148803640900560350000c0c0d09000501d482c400c00e4090b803a2018440c071024011070741c0c2c0d500068603920745805a00f200b01c03008103030720303650030010351104000c66082c019207000900d00f2102e001142068030070840503419568000581800c41c2088042c0c140348004101c2c1103005440c0d4544040e1180d9526103800e41050002040310318040c4e5011206400043c0b06a040000da070348108050380314511182803a4202030a13903840082c00e4100070380188100d08009403c1a0700140d150200c00418103910301a203001c458620310b18040d007109005aa0620304180303503c2e00b00c29200b04140c0e014121280540402a09480a03656546590402102107800c4200803d40f0305203030000d914403600c0340c41120008400c0c2000080d111540708840c800b0107030740f294003442000404450304e5501f040540440c661241031a072407500c0c6070b4074400382c003100f09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 925869424 1250 925868174 925868189
    0x7050618010e03160b0c032812180b0603120f0c0606061204080c0109050a08041e030b010909050a0804080a0b2406070f02090a0204092009060307111921020606040c0306090501030c 79
    0x303c3c541e49030b101490003900c58401218802005168051300c6251032040090b18155241c4507190ee400424043c00014203600355640588179154400c44e4502c5013440001419244185005c03ca1101628122484a40c00c2604407146035255a495880680103011082c40075000b48900540c040404c0b60010080056988420203c02610126120481d2484a600000700010342c480018014075040e5402110410b001f101120501c2011351108841d903801a04044010380003002201c0901410100c507a803c5901c1d240c1002c21080045034003051411140c0c0c0180c41a080011802c003803050b0640051803580d002403030540503041c0361031010b000303500c10310440c810241804d00c41c02640542041350000240c2c1d08075070501d0300d0b82840800006600c000d10340420301581e81504d60018904000040c040782407210481da65035058244030030038058900c20b43c83e003d800000000400c983c0070a03c20340100f0b0580d804070b2000b0b0f0a0400381c02501e40c5402200d0302d245088000014404515085012108103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 925870674 1250 925869424 925869437
    0x140415030f0c020703080d110d200a0203030a0504020a05130609110c030f0703170f010e0c03040f3002011e0b01050f070507050618010e03160b0c0328 66
    0x400ca204030590b1041640b58015801a000030804241407800038085010039440009a072080c40ca0800c0301a00201141d0319102c2c1e03076100001c03402d0040b240c400d6980b918050810b092240402000b56248801040c0d214841d0320340c0b000c0b5085488100d150400b03028005c00b241c620700112030284004192038070440d1300301420146050690861002251032400c0c15601440ca002d40f0040742c207a0540c000c12003201000100e50b001c03000b150100c540d5074000c18100541d03071a903501d0844520f0380e03504050102840800c0400502c00003d060a0b42c990a0320340c000f000001e4442000b111610b080c0038be4040d0118001c0c1c0c21110b6039030326410750104403100309100c0d040f080400814007010440f030001000a000c22010001c1e4a4a4500c2c04090001d891281c2c044032525500d074804100c080d0000a4030441c440c4a00009a43c95a0800f002200c0c002c0290001d002010b541403102c0003101c0d9510540c4144500098242d80200c8244210350a8007030700a03402040825580c43e016040135030760480f03000201b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 925871924 1250 925870674 925870691
    0x30506150a0c11060408030c100f0506090f1509090706090b031b03090f010f0203010320011e030e011803091707031e05150a06080303010305190314041503 68
    0x24098a07030900ca02e0b524005103085650380d02a0002c40c80143c25441942403200080700503080005011050001028204031402c0000c40340a446950281c41035080c104001c101c12925403c81ca07580c03100287c4000c4003991a100c10300d00d800d80c030401400750002100010419000700c001032081c1291768556503aa902a91500b40d00c01c83d000545d100040440f200b520100442443d40141d0340020141054441800095042a08488426402d2a41242c01000410501038104c0c0c1502c220150039145071041c12500b000286607203118120080001146030000c10702070f10992040e000c4815080007006036010400300c24004100072102180010003052022400300750300c91041103054a80c100416402c3c9c1541d17030b110000140400d6004410030050050000b0803001c1005607030511015650814038103051220314103881e0705030440d031f20940c82040104000303400051100e030082c40c046004602c0d200c2900d0220f0382510010050030b0f07541c03004107010440044001d070310250040303661800c201149 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 925873174 1250 925871924 925871959
    0x6090f01020c07030f2a060e01030b090f130204060f150906020d0f140d0507020d030915050a062313060308090114090d030203090a0603060b0711030c04020a030506 72
    0x440c0c60700b61030950308010802c0000131141c81d490b2481900c01d14026541501448400c4000f0a40a24018048410034010010140c008071050420b41084c03805100500303030354022415075a0041d0440b00116200700c00968a05040801c05140d80c0d8014014003140c2d43d1003022001103075031030042d102c1e15035003282c40c0501c1e28010003641c3c04541140d0041e005a102408058410380314280d1b6031010302c0300d0301c010640c1c2d1100400041c6020140980d0010b05070414000091074000044980c000389490810030101040c0c0c40b44441c040b51214a50208407640c2d4180d9403806851b840c4c2c449850420f40d842d40030306030480300200c0214800143c624606502d10403561505480e0503100c007030080201003001d1000c95100d10310b002020b80d1003510712850402c1c04c04c0031440d2004491826001a000411040d00354608941c2c800b00a0030039140c28010345041603c0c00c0810700c52054000c040514921403d56152814003031142c80402c02003003107484192122010b8040c00b011501140704140d0b800c24201d100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 925874424 1250 925873174 925873177
    0x213060305011d04031e180b030907140301060e072003090127030219090e120a050c070b040b0304061d1e011d01020c06010b040614031f0806090f0102 66
    0x21105400f00c641c0020401c2c104002036540a041902080f10101c48000c50b80f09400f00e01071000b800b42d5030b0300416455490b40e0304601c040c0c1d4010f00d590000030014001228000110003040e03590703982e401c00040400c14002801440030341e01c0003110000c2e0300b08015009410a03048031100b849071207264000b421504509440b441949103003170104540400320742501b201c44005080d640308160400d40015106e800040252600d80e810500d8954940804d02c8030501c02c0c01441200d0445400400e01071303001c0704c0e40080c103001e81c0c103110003081400321358000d8101c01003040c83d0003009a020400c1d600c3d034a45580c400140e01c125010342d0301504124942c640c0e41c3c80280701ca80701c000c80c0d0010780440003080310790b85030b803d100b02156200c41d900d5102c40032060180c040b840301c29030400000181d0342c0b100003031500c3c1071801c141e024403c03162082c041003050342d4014040f190090b8171141503550b42d555242e0a144007140801640300703078044d050703004101c101c400651640510b1074201280c40f80d21740c0d0320840d4241d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 925875674 1250 925874424 925874429
    0xf07030b010b030411030a061a0d0c03022404090204030309081605060c0c0303030c03040b010e0103080f1b010513060e0a03050403110324011406030609241003021306030501 76
    0x11040c404010032201c841e200145800a10504800c0080ea81840000f803410701030450980385d541d60b40c020802da1840c2032005403901d0005550300c102c0b09500c0d1701d07985040701c070781d210190242c1104115816443d52400700100c9400a01c40c0058540e40c503114504025001800220042001c010340801e01a00004d10615003400702c441521310b181c1000c0a0140c1500310704009241849550f0300c002e25a1744c00d101031445024100520ba440740340500381001c08403010f85c06204140c10100050008c103204c1021503541c28110b001a9564500e07000b4041911691946038840f40d51808003440410b05141445a500c0c0f0b000b403000344082407003100285d454449100340200410402c000400c0013a4454454045004000f01a28100100aa200d100c00d00140920b0400000c60f040148141030018000744044e40b02500e4190541c68400046074a040020701401d0140c04001c0c1c440c0450030881044503607103031010f4481302c0c0340d03081407601a010f07400009140c9000c803d180e40115480f4401e1103220304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 925876924 1250 925875674 925875683
    0x40c0f09060308033601140c07120c080712112104060e0d061d060907030b06060306041104080102042d0b0d09060515090610050904150503060a06080f0703 68
    0x4e10b4540d140d50200d04805044035805910040240c607842c4e0744903920600c01d1a2200b800811000b0013034241a43c1c40c00000c100c2a0061014880c0d14007203202d5070030b204038012890508410402c1d040c01c19081900420703000a10440340e061070762070940c1d84004414407403440c600441c1d0360039404c1e24182c0c689001c80003400e4519501848108095841510301c0c800d001d4020304414002d54207622500195507030703141d449000d030803001d0b56885402030401c1720692201c810000740485906691b1001c40018000d0401b5200b0f44001c804518590b48690046a03900003000510750f840f940c40100c903010307400910a0380304800c80510000e22001c2a202070b4000e9806100030074007204d0800300350711074030b42082010300c003c181c2c0c2d1212840001da1034480e19000d00456030203812914446010440401d0000340300c14000c0116481d2100456088410341e281840201e402268055034a9081e1026460360f9100395894411030f800e0042c40e200a0340f04400f079030ba0380e005407007500b6034071a8a199241c105100040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 925878174 1250 925876924 925876927
    0xc050405070f0e0d1e21020601051002010902060706050402180a0e07091107032007260307032c030a06140601050f27040903030e280b0a0b09040c0f09060308 69
    0x600190345030103101007a4886d030360340050b1001480082001c20b42007a900341c05a801000180160301d00360b01701d1741c0361494900c020301c00b20929a003c1007060083c07002c01403225031120042800c540c1d405441100102c420348441c4954074003503880e9805003000088210440c0501c80b400708010305c1d9400b03244405100c0c280c0b40c41c41c01107c1c1da4210b070084114003c0f8201307005a01391030b20168205002040003030080724012060b00594003000c0f19548505045000581c2c41001410f0000313401c480d9800411100304900c0c0340004503007440071400d0707a68426855241c05200c1c4880d04003d11070b44a40c00000350700414103013503075410f0015540781c4115000d5455501007407280c8441040801641c6203400007140d01c2d001d0707048820001c03a0a8611501c1308402103502c603900c0d01c00b04407082181c014568030500c101b1400b00c142e0054030030306842c060300182114881400094000480e5008003e06080207026401c1a04d03140c1421072a40500340510350308403030134090004012626015282c1565005144035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 925879424 1250 925878174 925878203
    0x2109010818010902090108030301150e01020a030e041803120501140121060b0f211e09070f08060108011b1d0a030b0c0d061a0a05070c050405070f0e0d 66
    0x241101500c10410074015922440c01d4030050300d42c1d600c1c0034020415000116100c1d414501c068517100d02d1583d1580030450f03100300c41403860fa40000d80b0010260036003400e2041b4040300011030040d0a180a0501d08960b5040c200c00030594002210080020403040821060343c8912000840c0307072101501c940000c4000c480380903103201664031007485501a02000400c142e4803501c2580e01e070005500524055400300309064005805070420034021070550050040740703071945213541d07a0b105200e07030302d500c404001c400511203000c10400314015003408103102100990301e0310040d43d03c0100340a031071030075401d00540c0003118640710b50319100c80c15031b43c840340280584a2440300e000383c951550668400401440040803421001c00d181c007405410f207141d40c2e83c500c224180800d480e815400115500c10b640e0038604120000800da540200c041d1401950311103103428070303c100749401e801096101d490007043c0602380b40c003c45161070310707281515294010009401000720b20404c040e0058155981e07024030b0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 925880674 1250 925879424 925879441
    0x50901050d08160c0e0703050a1e090312020d0903110d0804021509040c090603140412230a020a20030a020f030102120a06031b03110114091221090108 66
    0x1400407003c2d8200004115491034503603080c0300240d035010070185d00d03103402441031207607150041c60f81c40700207002c0900210000703120303e00510488114180742e490351401c0810415114244a07003c03440403903019500c5441c0d14020302c0061441010890114000010b0007441c0d29000c508801070521640b10082c05179103030f400b032060060041c1c0325000c020104100da507200d03aa651141d41ca80003429074610306c04a0a2010250880f0700e802c03000142e07103806604100000c0ea41d2880c2450080042c83c10306034210f10a110898120601c5c21480c0c0500320200b52001c000351b0000350103990398000d109a401c2d401880b4121800a06c004403c103800d900501c0070080581480c11131034205c860003500041ca8421074003601d00c003443c0b05682601d2525102d00c010410700c020303000382e44800016403010385007461a580c1d810300700030482d42c00241488124401800035017145401d881002c07602908100d1000d4140702d1840c1c44601010001c604c0348110b240c4c0d20150482482a107a9071032043c0c4074200503484180d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 925881924 1250 925880674 925880677
    0x19020103110904021605070909050c0409030311032a07261309090b1b1207090312020d020d020309010203120a020c03041d06011e0c0302010e01050916050901050d08 72
    0xc0400740d01c1000c00950145444502c010200c011815880803c40d540340e00c0e0850070017200c0d42c0000c6103281043c0c050008030350045070711a662041200c0015020403245002d6020b4407c2101c1c42d900500040104100b010030350201d91f0f2111003520300394400c1c100700c02e212600c0c1d0050000250500c001c440e1940541c00110003500d0580e01c905079001d00708204061111000d0800c0e4000780034103a00c0314151410400e41d050410f803c83d26078880c000da0301041c090700501c1e50150303c44001401d5101c4000c5a0345c94094003117000034541100700c1d0300c0d414040c4400a0b588040680c40e1000510401038040f504030320100540781d81400c1680a5450003a1640d01214241c401604032000d00e41d08114480003280100028402804981200348440044040305e00480c540100f4081c10b00510810301c0946040d22900030524518504100078101c030a07082c103c2c0100f4001d010160030b50310788030038810201400240d10749110088882c4d4158580c455082c13001100d0288030b91604682e01c1f01401e40014140750 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 925883174 1250 925881924 925881941
    0x3220f0611070504020d06030507230d080705030a08011e06050f180d030e090a050906160c0b0f191b03021b0a030507031d0d03050a02010f11091219020103 68
    0x40c2100c56154490f0001812640844a0702e01e0342d40d9200d01c20000c2000510214005141c481101844800107111001c00e90075149001803040800c0020042000414016243c0740d5410004803074a83c1c50a0704094120035080c02210030a4500e0900b02c0e8501e030100900700141c0710617a403680c1c10020107510203807664110000c0f0b038490106d00740841c800d2761100168141201c2c02030f65485603680d000070034041b04110241c04140268100010410044800200280c200c0c0000507581080038402e101244c0041c1d01e220010315540d642c0c001d10040b40c111305400f50284c005170840d5008040e5884d03c0c2400c451a0540c004942401c4428040d14180aa0701500c09849030300514113048500004041c20450081c400310082903003c0742210500d944800340407030440010740c0c40d681c2d6601300c10001d0070100c024900201040000181034415074400e402100e4180b013030390383c01c0c8000114005800f90315009003600c0ba0140c283c1005003a190000000c144940c1005458044400f4410b0b40045000d0000715 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 925884424 1250 925883174 925883207
    0x40b0f15010809010e12040f05090403021515041a1215011223060f0c0c0a022b0b04021002150103260a122417071703220f06 55
    0x440d003403e001c4900b0300c11321b00e01484420f02e40b42c1ea03608100c3c101050402a4001c5401003165004000020741c0000382040e45d440459041d121036a140d542c461194045005e0081e0002d06248026140142d180b0348664912412150100c0d0410f1200109555060f22110702c003414440100400560304120000190391340038581400488109034410120406030880410043c2d02a074100000c02c035004c0d0110760050340d120092440c0103241c0341c045a5440c1d00040c06481210014240c400c0d45c00d40192460b02000e104086038030905042c01e11180503002240c2c01d0340a50f0b048014803051a2000c545150511005a12070080d84d09503240c0c0700140b8900807503429440840c00c440000788803424040d00050095170340303801c100d0311000003941c00e0b195050310340b01d403500304c0d01c1c01410320030401c120b0907003550355070003481c0c04607004445240d01d400c48036070004414181050102c40c4445001c8001c2c103c03040003498001c107040f901d02049408450510071440c0302c4110b040306109507881044d00a000c2d45a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 925885674 1250 925884424 925884431
    0xc050706020f120c1803070501080c09040e07090c0201061a070312110d0c1803050c01050f07060203040c0302090115090e04061518060e09070b0f040b0304030503040b0f1501080901 79
    0x10b800f080c8401082c01d95107041100340c00f05e807070240c0b000203039a070450f0410281e01070f003946440c01c00007070507041c0c0290564440620114046015844642c00750364668411000c59501a50300c8900c44014650990844019420184007103032020000744107080d48411b0b052518501600d0741c40440308051040e160798580c0b0348a100160040c42c40e02e010b00300602502000003480b0340c03001c0300608103407a4014642d00b8510413001c10404a80302140c0343c8011402030802c140d81d80e0245454065078854404000d005a20120a02042c007001007000c1041e68426500d844803a45c07100704003005889034048400000b400000c017070010401c0007a4582c0c00c10f104d03010210f45101c4110b416510703000c0342c1d00700c8015217011704010710b403940190260400400758561158414102141d542c1d4649116000d0381e0f0358031034006192140481010101c41c02850f07000007141d201e0601b481c000f05603900a070340540e0341d204103c0210b080342000c0c03075020780030b030410103c1480c01413a45c500643c1e4606005260f03400300d540c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 925886924 1250 925885674 925885687
    0x2060a14070b0709080609150c0903120306031905100c0507060f0f051501080c0306011403010602030a0e040c021b040f09030203071a0609010b0d1d0a020a090c050706020f 75
    0x1003140a0706003148a501c284880d0b2800c10b00c000c01558556100c01d80c035602c08010321406e4100841c0c1000461481d400b14032040d41d032028900d00e144901542903415201e120301100681e02c1c00400341d8040d070002c40c207032095510078154400400030000c0c005071903504410314001d525886076100315201120760405505110641d2108801c690044064565040d1a911790400802c00c074840d481c0c0c02610700c02c86401040000303000801c070300e900400c0300c20719150000101e070040e806941c0c9441c201800104a5940350b1b1103000013903da030414000d034008940001d01c20152840c2501480540c002240c0c0107125440e409540d074034080c030380801560342260b41c50040b04407161248c013900403064002e4008668600c51450b214035002d48000124542007540000e0015581d102000d803411111000e40329030300d695100d129140240401c400782c41096103184002210020049041c5140a00131155105016070b2001e0301c000f5543d01e0510200021420090200003c1c0c890307010744201c40d80c0301d1041c0c0c140039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 925888174 1250 925886924 925886957
    0x316091b083903090c0105271503070917030a140313020316051f050301050613090c270f090c0504030506010f0312090501080a09110d0b070e04020f0702060a 69
    0x141210b07180d140100300200b006540f681c10441c1c620401e40a1a09629010100700f0340c4a00c04560450040c40c20280c2810031340664a24000c905149d21610809540c0e0a2440014201074001d1083c1540380d01307420300f500180d20001c8160f64291107030742c4569185810345541e054069000910143c0d03030b6084500c040000d030b10200304c0c80701c10b0181121114042030500c4200103c9040314692528608800d004400900f54098203490440c2c8044e83d541343c60707400f42c1e0030202070004540c0081584514050940c0134650f8403040c1c94100103103010107600803040042d127801040ca45409211403c0c449510100b00c40c1c01b999021510119251800e40d0a0585a50380e8a041c0b40382a80f0000c166589060b040c402c0c031a01483c0c540b0003544c40d00300110214070b480000b074400c20300142013002c0c0c5c0c0e0b170f52070b410002d0140c2007542e40e403260300041c03c40000c1e000515094940000995840002030b10b4800b1800c664102407007141c00d281400041c40d4100b0700941c0c200300c1d140d48000d11400400c17100d01131400d17a82 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 925889424 1250 925888174 925888261
    0x10309050a0f05030a030b0d020607060b060c0312192f04030c08070603060806090d1b02060d0f0b180109020a110a031106070512040609060b0316091b08 67
    0x1038880c3d00610394400c2e030200020f059400444075240f2541403544040016606c80c02210502a88568045094200c92000582074007540c07888080303900000800815020b04e884103131707202e04c0c1100000040342880d039491004603058176500d614819408030116018001541e102d0320795070050b1035414a869100d030380b10a100c4000741d01c11f840a50004030240074694250052801038480b520060007640f40214080c2c0d55812110601c0d418001301c580c032407240d034030342e10009035200e500039003450f548616098104e8014500000700d818801d2402c8a50f91603498420229181610b01c110140f4840c4d0030201844001c0d40504140014803424641c444108801400400140340c003d49a0a10f40c03400500102d003040402800d20080100402044a00c03100c8640c62a0300150041d1000501c20040e103400802020f040121031751602c12a6144481060f641001c941696003440040c48402c440c0e254404403040b041c5050004941c40d5800a8a10000740103805100010340f00c404072038802141c04802603 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 925890674 1250 925889424 925889453
    0xe0f150a0608090706050c06180109171201090e0709180516230918012408070e040b0f15100527060d0b01031d010c0f0c020906010309050a 61
    0x440c90301410050f05040a002ca040102414140316203804071100e4207a0300c0d4940240022280221a085500a50380952000214031341c010540380108030744a00384142c2d0303008100b80541d03592000c00041248001da00650342c000f151100201605418054980e01500d00c1e8071400b4800d00321014090082a4100000e4001d00c0d50482c45600041c00d029042d11034150b5226090501c2e0200c80454103541c03108600c0da58004d1150740e50301c0c804483e00c45864090b0001e90401603450110b603611050441c0c0700d40c50241126800011695015902c040d040e03d004003ca40103007400d40c1003400a8210102c6980c540e80c481c144d0443c080c8040010b41c0001c1c0c54030015020180095004030b4114411280114219a0380403c40482c100d44076034000090401d10980c08034140f05078552900340d584d41d0098000c1e080700b07000c556464210101804189000b0010404610006049200c10b0140c2600915070a0756403a006032412600e55544401034000d0145e40d001202c407445a42c0d80c0754045003c10144000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 925891924 1250 925890674 925890677
    0x1110307050d4104200316060305160e0303040e09030f0a03020a080711120d0f0204080c010201140712020304020d02041e0506180a05071e05040305160e0f150a06 71
    0x84608050b50000c40a80d080030484040300c0400381404086140214908410203504410140c85d01d031035004207042c84150aa11962182c24520104031680c258014034410b25010b0191951810f8505084540350810001e03990150410401440520b0800741c8031540071040004407842e110101141012580c0900d1940002941c04100d406d032050344858401e404c00e8040c50b0510651108640403030700c905455004201565000a0900300303100242c11045041c80361560031900d86a4a920b01c40d1941c20050001c0d00551074a4004901502c030440d8982c094842584c50340d407081e0008640302c000b5032000c0d00c2603034032841407051280140e81e103000c0c0c14110300319140303e08644240c07000030313609950010b2300240c41203c0d1114803d1f038100198502c1a80310300c20340000326150701c1d9a001980c56104103e4090300300c04110715001c8072940c01c20010800c032841603089551080c3e15418603000000e2600903908803501a00105905442521031580c206148043c1d08800082000000b000306489610000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 925893174 1250 925891924 925891991
    0x2070203100203061c0305090d05010b030f1c08090d031e0204031104050c09030a06090c1a0408070905010b09010f0e120a0b13050a0f030c02102001110307050d 70
    0x24130703428004074000d411180c64610316007441c4c4641c0c01804900900e81e1041c0952a0740400b034041c02001d4205000070340014040e945482c90b420300494030f81400d1a14032081a000f13880e040c1c0a10300c10942280300d800504060466a10303141c00444c05008610344810b081021901c5201402e00c3d2440100001c503c11441c010010350241c05110039038600800c50b805a0b90240300c8034400761008500c802c2055840f00000804007441d16103400c2034403079034000248203c024a1052000602c0c40c0c014800d4500c07501c00c450b512540da14031801038070400d008159040c00c061107452081d50080144101c2400700d4100f00030407088800108403000500c541c074072015400b2420003001d01849500302c50b0008156441503601d1410341d1901640d525050381c0c010202014078510f0000c0c90b12581c1170800c0543e00130072100030f814203030100804000200d055450aa92504807000481105104140341140d4050405045989201056465400170300202c1c0e05980c070303140d0180d0341031229404040c0c284440780446 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 925894424 1250 925893174 925893181
    0x7030908011407170601021b030304030605070206102304021c0c020309010e010e0d08030c041d0f0c0c25090e060f070c0b34030b0f030a08041802070203100203 70
    0x6215610705100b0711650046107085c0107250b68013140b00028200d0750301103084007030480d0300400d00d180300707582c00038010314078260900c0f03500c0d580460550700603c0c44810710086a81c6400f2240ca2036903a1a0700d000040f200401c0002c250300b480e4001d070440040000d24039100300000c03110402950b144400d0f000040c0c2001448540319a0040c4620007028028a0030307808002d1050702240c009100c0050140000a01000003a070108200007100c01500c14103d0301d00190500344000000e409041c0c0c0e0102850982e030001943c06450441507070001c2e48050010400d1021040380c1180581c0b11182024440107a1003021070820b0f03490240390324141d40080282414605078642030202d0300c0c00b500320f1080103401b5000307602281180c2035003908144c02c00c0c00c448080002a10840b115004050000580d20458496401c03481d0164401000c022013507842920b006100010151540702101c0d00504190040c8070900c00900500003d254003259810700601e080b4050b000a072070640305462086030f4903000004c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 925895674 1250 925894424 925894427
    0x12100f2a02010c110a1b05030304030f060b0904080306090a0b1c1203020a0207090c021f090201030b10170603100e071701021e07030306151112040e01060507030908011407 75
    0x2400d0050702c3c03501c0c0119000003c59015500c58088080c0a0040758501c280ca541c012400d0900b04003c00004040780e40d610b5592a022100d000c03902c0007918100d2a051000c6a035052807603086109503405001c5920b5903407500d00304948004060094805599200841062615902d1601242030303094480080d004082e460000d0803040083c400070201401070007808210382d00000d0758010b0794990213010500741c8480604a2810049481214051001d0062004000656404240b02d00d00030f0f40c0620078240f00c2800e102521500c104547d000a500c4400000c00c0c804070707056283c10200c0142034031a540318246c10b00082d100e480b6a81c007200e41040d00d04000c103c00002c281c94524444100947c286034400c0300100119038030340090030a0b148001041001c0611940c00003001d89020740241d9085010620014444910310078500b009205030a014500070300d0b084160f40446c2ca2910b01d1590a03820f0640c100e40d241c000e00b81c11414428088808a0302c40020302514000103416460141a0314191f00e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 925896924 1250 925895674 925895681
    0x712051006050f1e0301090f110f09190209030d090f08070e04060b010201020c1605270402010c0317090a230d1404090e0a02040b12100f2a0201 63
    0x4039440c03107803034044204207540b54510b01d41d80303c0e1021140458000341502c0c003920b4020541d90700c0d5030325528040e4914100210041d8110800c0c0c000c2440c810141015424401c000c8520740e0303281d40c848881400109180200b88002042040000b4050704041e0044041b070318248100c3c0300300c00460361515040c8403010708800c000000f0b012400041001a203000a1200f50380c1015002400e031503118450050140d0007501151032070700308802150b4155148040751101c44105000d0356101c0c0d8008410b280c0c02c080c129120b080c10407500400c580c0f464071039600660741020300351002c4003071000441c11043d1140041c41c070503200d0b100000c090000d0038100e142c00c100d03e1041d80c010002511071000402c000d40400203100e041c002050604130400900958480403c0c040c40c0d121020180c00e08c1f641d09203d040c04903041c103081d4404d483c14850380d4015001c20171202c1045141407503a5121030b41004030660f9035044818802420a0006944454a1140411203038001c02d4801c000401c502c0003040c0a03030912 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 925898174 1250 925896924 925896943
    0x3070803070f111e0607230601060807030b06220b04090e0138011209080c070909020306132102010912030605010e06030c22061409010903020120071205 67
    0x4600a48602c5603162141c1c2c00c4007454000d03401039030041746d20820000d00504e080360502c500c81c450306900400740d101c66039940c401d0140000103641d240100f042c42d80280a80c11890f00300908031402c05042240c0020078100407045900488503084c80000c1118030000100f0160101c910007180c100c0a481040703080d90182c070368001103003a103a42c50040c0c40e202031000880c850081114180c882c10000012a50440749660303210b07089141149110400c24480c00600002c8100d80035107040c2d6031340d603007840300b1140141e002079010342100c0001660b5410348010740118501c5030100c0c0c9081a070561086080c00310028014000d0713903450041d58140090320404440d482d006140900106040800080c06100f1548155000d04000700200e15080518001e4601103004800c43d00e0100786401001d030700e0100c00d80300d100d0218090400d00c9402100c504115011000107031582c0001c10f14650044601d80b80882964100c03000d14070001801a000f404000001c218902c04010000c0060420074282aa0803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925899280 1106 925898174 925898179
    0x705100f020a030b0a081203090106180e06130c05011b0503070c053309120a03270f0501080601021c21020310031103070803070f11 58
    0x15409450000401d0f5410320920b8100c00030b010074900305020b001502d030004490a09040d960350000d5401c648160000a40d00350f80d0956044800346942c040860540c8030554800c2d4242e04002e01500a520b48401c0d10302d5883c2076540c00c6031007145201e0300e41800b03441c05001c3c00d184440300e20ba45200d504101681c1e5030b003003185400303210080075005d2144203841000740740c58003101319012404958400303a4034203c40b40b50411041c240e5004081005d038030006801219900543c10702c01d0528040c402c0d290404110036400421100c0d0740325210301c0600740c407949420080041601c8000c070440c1c2003030800c2003150b114540101d00b81000c90040b0304460000e00358101c2001e83c0440c034101c2042e801440d02450b0800e64807070000f03a1000b03544640c0c04440c400804d00c003007290740a0702c00207510001d04039070311b0b01d0b07860f0405800d6810070301d0240d501000240250041c081c40594410400404 = true := by decide +kernel

theorem cover : BRFrame.Cov 925719424 925899280 := by
  have h0 := BRFrame.cov_init 925719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925719424 ≤ n) (h2 : n < 925899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
