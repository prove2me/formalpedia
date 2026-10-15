-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:04.272312+00:00
-- url     : https://prove2.me/submissions/723e6ce2-c12b-40d7-a164-e1f50ef81bd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 736151079 ≤ n < 736330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 736152329 1250 736151079 736151081
    0x609050f040f09151107170a170702031207032307231801030c022104090c020d39020f0604030506040b0609390a030903030b0a0e0c0c10 60
    0x40001142e90b2070384440303507130400841c5200369400c2500d02c1c21801d0420120750b455180107020329445507101d840100f41f24003c10300ca84081c00421752401c04c152083d0404400282da2904032182c0d01c50340c544610001111b1900c43d12407142c502201c8080d5070318801306100c285007101000342050381003001d807502d802850111402502541c5840c42c04550b900c001039080082035100000c08141007600340782112001680c0007480b800320291072007480a035038041e030709143c0311403295900010840e41001180b00707020b90007040341d000c00800d80d00c400c1919070050490516020010611540c8015001100724030746841452407200d181c03016204d8036015864000003092904131f9801290640e008008120030043d940316a6500404296000e10345814802d450344020616203501c06611844840103a50300300e00a04030001612015001d20350fa19100f2400a010b040b0164056010a00344185540303e400c0c0320074503404a0b050f070400620b8540391496a445181c1c041c8130030f203c80340b041030304000c18a030403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 736153579 1250 736152329 736152341
    0x30c0b16270b1b0c03010917031e0703050a1a01050d0b0112020c0a200a05010309020105070c06080702070e0c04090207080c0d08010f0503060906040212030d0e0a060e070609050f040f 80
    0x300f110065400e1540422645809400d044c1c0c0350090741400034881c001035203195110748521002e0714183c1c0326910300103030016041b0300500500000540405010b1440c2d019805240141c5014030103000120381c5200d0410302050044803076001030f0b02042544440c0569911092006a05151443c549454907000b030003a6040a813455800b074200481c074008200815181c003011802c2c04a000c200300030b18400188602569210310340c10f05448102c10400c5a103e18201c0d00003a0f40034120b060016203030140200805c01c00c607a980054450910042000c0d003108a01d0703449101e541000c01d14003070070030807094007035041a80203d880c907100f0b202c1c1208402050106078520a4561b031840c150b903250100c20304000809603c0103010350004010702100c10008201c2640c00b54050b01d2149000000720500e5103188110400010b02514244003035000e500c002c600c90314058085c11040c02101d040e50f4405444840030f10406002c0f4000314010407035800d04000300b100c0c41000801c00914896080068030554030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 736154829 1250 736153579 736153597
    0x1031409010e0c120705060a09030b040c08060105180402040c17010b0d0b060c1c0e0301060f08120c06070e0301110f34060203040c03020d030c0b16270b 67
    0x5110001000e02e04810400c4050040046038000340c1e80300c00400003502d44200d0f0240c14018000000c0503200d4600a210b8100150380c031122034452440d040c02c04401d82081401421407a02078200009034600d00320001d129840001e01c84144551115400c00000700603c40d45042841010800c2201e24080340c003046008140c404612540c4100641c0c0c220700b1142100080c61040030280007607244d0410008040946149803506200701410b03185091704d5500d42441299803542c03e0200200b4042d0705213640400312070080c0c2c1180c4150031032034920182c50181c801410b0f0143e016000040186110b0407040e0700701b00010f4000102d020380d0b00600001c90b40b050100c036001d42400207034031850a40c4060b5140400400d041c2501a09144081e0783d0903080b000311000c1d014a402002107000e1044080f10500290b074014001903040106103005803025003020400d075a030ad6041c4c000943d0807800302d881030040484a584140d51101604045c0d1708600c0c445201102462014a0201e01d80300ca450090141131 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 736156079 1250 736154829 736154831
    0x1b0309071e030506071b0b100b04080a020a170a0215071208060306070f1d010315080c091303091a090d050c1504080a2303040b0d230408090103140901 66
    0xd821410583d00c0d0404c003601c50404c01800d0400f07a5150f030701e0703a03201608403a44100c1d403c255071229006124081c05a800501e200c203000034001030b141900103031403900310f84250340d00c1450b01e944421010300c1a44442c041c61450300440d1101c4014a050160b950141d031071144890308029181c1c8905c002801d000407440d002c0303a420400e2001615040042030b40c400298900381d042131907081c400818010031103c59030030400f00d90408102e0790b03003e03801c5180100a101100001503954a00f500d035108024008a8080c290400c04980110081c00010703000640684512949901d4042c0c0700c030300e00340c1541072880b0048042c0314500c40740c2d50792184aa803c0303020720010b0a2904096040000c8a500364440584400d0100700c20068584003041e6034051981142c0d100d06952901044801c03a0a0620091200350000040126411400c10090000f400d0034075800c01040c194445209428002644420b0440c2000c00c00034000030580401020261818940414070482401040b68004007d13035003000e0517 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 736157329 1250 736156079 736156139
    0x8070f0c0501090e060a030323030f07202503061e0b031908030601050c06250503060102191103070803070203010b0409030504060c0302120a0309020f091b030907 71
    0xc0d81d03ca01282c0c00703400861042c000710300f0090300148001449100082c2485081c1c00141e07070304107240c049611032120960001c4d69910301952068101c2c0c404a0305080810650255520540600140d200c1c008213070714014103aa070244c854200302c001c89000d080d40d200441c80c00c00f10000703116000d00e08450480600b0445002111840c1700c054030800e040e00c42c00b0707900c0890900c0304000044000414580c200020342d40ea91124401283c10380b1a5016103202440381006000c000101d0000203130890800f0900703560343d011001c204840a110580340207005a2107011000100300403c036500d81c1440c0b080250b0100125100c011170f05241701c88d0f001c03045907000441c040095040070701806200000c111810050129a540c024003940564080c3c030003000210f101d401c1c100750080040505404100185a0311035100d01c0d070050162000342d001702c0c007a01101000d6985070804c0580b0a000d40f1b011400317055048150b148194054000070034a01031486030b070b04002001ca10034452030640380c0b0514100000307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 736158579 1250 736157329 736157339
    0x1b0a260705010e03100504021216060e0301020f27030d020c0a0504270c0f0b0318160b090307030602131d4503181c03050708070f0c 58
    0x80c000e40358041414411030500c0c4000ca40e4010a070900502ea5001002510340c44500101d01d0903c08103406030024400c0c8144441c040100107002c01c00c80b1a81d80d07800008440c0e02e001d0600342c0c010405e03c003404d01424440f540720701d254241c00b840000c0b031120740301c0b1040f05120006072030300d940f00e02d50700003503000000038003603d05001c1c41410140c203007a1000d00800d41c0f40042041100c032052440d8036860801c185032003c01c10b84d0145800101a003003481030071152600d41c0a41c0c2940299500020b0f007200c1600c4110041020404002c0c02c8090b0902000051801080002c0c6600890368282c1c58000c0003400310000d90341f071000d01000c02680c0d05940c4454103051144c959480c0b803c06810b5008216030801400c40d0f50401c07080a80c10b001600140307021800500c3c1c2802d80854800a07440c10303059070b601c2c075003000e00001800560144148180d0080641c20622200c0c86c011201258408105980480401e00070740043c400303284180c0070b180c9000c590b07864068031100c0700d800c05c030b03000314550f401000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 736159829 1250 736158579 736158583
    0x1d040f03121d072103080721140a091703130813090c020703080d0b041b020c210307021509031f1506120506010210090b010f0b0307021b0a26 62
    0x10b07050801310042c0c00c14490f0140c486508a402c4000c040040110002c6c998500c152400f5180e850780805001c0d0028074a00c0c080068440c203144030a40800d40000a54111103034003601e207000c0d03040070207448203013400881c54080b5072004014031b1010030250a40b00000300385800606c0030442e40a1644901c608044c1c1003815655909200340840d8403607002030001c030340c807001101c02021842000244901c800c8011501a0001c03911840c0601d99500c0c7d00d01c1e510350041112484181c0c1142d000194182d9450315207503d54883e81c40e441140d10a0006c000181040884946030a4075007601d1030030440324100080ca40401c00c4440481070381040c014840c1c1d03108500581491540b541244003a05007040d00040c00c50342c680000182c0f160301e820118049034000d01800d00005010304044c48150b801c0d0130000c820040038810528001e2100b4000950040340754143c0f0300a0296501401c0300c103120f07640c0014054080c1c00815032049020390001408010071000754012880820000b9806100240350340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 736161079 1250 736159829 736159843
    0xf060e0411013506030102040e010e37111903021b0703050f070902180d02040b03030307090e090303061f02010b0d20010c0c1802091e0a1d040f03121d 66
    0x10717010341c0c0140000c0c0410b0044540e0300b810344250b000a11915520703291003d404e950b65840b04c0f407a940c0d802e4958102c050034554080d92000d801103040c04080201c0741040c509200300d4180305149030342452502d0440744a81c0043c558044010340109614422082032400c4c15003582c012078080d44000c581119110051000b1001030503c0d540860500704005580e00400c542c000103107104507003180301d1104540e625170045201c0742014048030703124541320303d002d01909080d0182101030109080000c4480798008200c9104074005414100c07520325100060b002030311030031b034100b0940d5220584101c4030346034001010455802032102e000400d10f00303280c81072050355000519040281c1c841c032000229412800d06801ca0b0200c0700000194225801d20340024040c860000c2e60025112030074032000200076602103414030040f01c1482040d650381030300070810055903110110300c10b10840001c0100d0020b810818402d4041d0801000110010130168112010f540f541ca244407031412491200f0301c0300304601 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 736162329 1250 736161079 736161091
    0x15041a19050702090c0c0115080c010207080c0d0b060a090f0c0f080601080f0c0c07030c050a0b360d052d07090c0507050f010504060f060e04110135 65
    0x1d40e1402600ba0007140d2401c1e40101603410b092800100513054010075030000b401a0058a0b40340a41d0b515a4840350f1034490000220380184603180b40450002004507210302c103010020811540441d1959641d00499001004154401c01e58040000c11404a000382e4142d6040307814001403013401d00c4d030040c0000c1c00c80342d40d002c1048484000c10010340d8000007a96005540c0b1400c060640ea945082000540704058001d2000d001d549000420003401c0c0402c6c07400c0e114100e800514480d2103140c070070b40030300602c8001402013501012032066085c42110242810482c0701d0580401113296020640b442941035088078a5400f80400040307400d0100201381d4254400a400e44030103900b800e0850751001a40100d541403a600e40501c0b40c6580030b00c08496046602805880c08100c800c0784240c001d0504607001d0700c44d5030170b0068104501109101d10300a586000209035029207564603901090040c0b071680c1c0d414040e003452500a40c2902e005140c20780600b140040482450520302020101d001500b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 736163579 1250 736162329 736162337
    0xf041a04050c0423040f05070f0305060906091603030e0a030b191a030a060e01140106050301060305090a030906050c12040b1305040b01020303040b0907090f0203160f050915041a19 79
    0xc4c001900c0c8010a6650300143c100b0f0301c1d01c01c0d101c2c0d0380c2400b43c102140d81e4403a03a101c0310140000010400d001c21924030603039100c8145e4881d03a4071011717055114120214071112043c0718440500009000c1e0786002249400a0150002540c49a480c100a1541908da0346404440d0b80b8408680c2c0c50140264581a00004e81c000030040304000401c0d82e40c08104002000e1a07100d40300989000f409500658400e462802c9045003035035a0312001e0901c1d4401c4c001e80e000030f81040009840c81c1c1c4000340102c4c4c881d80c56940c2003003580c600b41e411076507500000c011a54500034203070800c0c8402d0454002c1e00207005018030b41559400010010000c010343c950280d400ba906000030060130740e0b00402900c0e401a0080180c11060303681055641c1000130761707005440581e150159408507601c0643c0030b58403d80420841907000103070603005840c8100b5131062440040c104200f025014180340702d120902905807803007642060f4036000031400748410140031070078a500100e00d43d0240d4a80700d45072030450902d410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 736164829 1250 736163579 736163621
    0x1807030c0927030819020d02031e0a0e031e0c01050405010e010b01140d1d0f06010510081018110d02091005030408070b041716030816080f041a04050c04 67
    0x141c05403020400410414a01c0d40307602c005c000000c41c0742c044540518820b20119940c2c034010500482e10304041c45c180907131b05804000107139007200b5885040400d010a5001350300300340d8540902c442c0d8010560468800b280c0a0141d081003e03424000c8034003c1e071261001203241d20200f8800341c00c441e04200200c0c10812411101d80040c0850001c950740511140001308038130741d550000c183c05040c42401c0c282c10b4031960380c200320221000710340f05040c1c0308100d86000061a203000e00f15106401034034041d0741c401c1c1e6400100420f192101d00720165040d080c8010648480f082c070f8090054119113840d2450350380004010a0f54640003294911112083c00c000d40ad501301078841d50321034001c100004044140c0b03030b00403c00f1700c84400080a045511944c44c0c580c0c540d41c81c442c2c007601d111403c0003100819401c4000c200c003203007200d10000079036200b40e54940740e685e940e0703d500c1100000a081510022400204400805490450284160b0042c001440b136626500240001c03682094201512050450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 736166079 1250 736164829 736164833
    0x420030f101a1c08040b0304150f060b0315010e100810080703080f0a1403090a020102010605010302030c1e1902030c0f120d02090a0f08010902090c0702091807030c0927 74
    0x20f58914000000801110410202860540d41511983d00000d08180e808410041000640c1400500e680507582c828041400c40040301d81c240c8601e4000d0ba80158018030015102e8014400c840c011464145010b42418050b1004165000700d0059284001008002005064082407540b40020502c11006090b80d6246841e90711180c0070f003880e84000e07490300059401c0d50510404250141303805040d0303e00e5480c240003541e1035940d0040e4004030301550800d100010690f001c0d1081c3e9206030360816280d860031781d043c43d420070840c501c0c20040010750001c0c441e00124181c24a54075101c940b2326002150b0b51101c18030418504907002194052640c0120103544100c03580784150764900051210140e26103680400040b80400b00d074104403000d48810400082185c070542014003098020707100c10070b06480314640480c0c94800c0400107508150440080f90f010015420b042180307403a80c03c25070b01d015403681e54040f40c08015501c01c1c2c00a0f038460307101d01d03640b101042c0c6d07c0310034060500001600048070b03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 736167329 1250 736166079 736166089
    0x190602160f080c010503090319030e0f010b06040b0a0309050a080c15040305040b0a21020910050301080601030b040f060216034d1203010e01120b0420030f101a 70
    0x400c3e080c0d04000c00400880d0441c0301c1001034440361140b034603540c40400b050080080042c00000e00c081c009200e80062584a1981031182400078080508514139145c1418a40c00c0594000000c0030105a80c40001c04041042404000080ca1040d00c002c0d59035100c681e0454500319800d400c0d508908885818000080d4100c421030301140d5000c0c1000340c03103510503801600c00301c2034070900a0044040710115840708540d40d00401d0044030454400c2e030b2245034444110395601090182410690202d0018070114400c010190740c041d109030454842600d407542c1d4441070307802c03c080100082440c000f00300c003015000885a0306440140c0449100784070400c0c81605208041c09044417000c00c603414444150803400c0e503095100050a048504401d01c0d2508610194000d00c62400c580f000b800000c140321f2000e0707540f400d0054008041c0030054559840700070070022003405003c10b43c070107080313400040e49003481440c0b400603441028051120080441200340d4040c204070341200c8a116981498940d12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736168579 1250 736167329 736167343
    0x40605040c080d0813020a2c100b12040203010b181014182e142707261e130f06111204051c090e06190602160f08 50
    0x1440f58502c04041140c00800d008a482d0740084000b002020701149818402446e0003140030480c88ea004016034035040107290355005c0c0c1c01003030000d4400300b080201100c00610560b0304280002d0000450150205c000381d940940004980c525000481c10082541411900d540c011b01c0d82004009070034133090002000181d1032034421104c4200000403468850720b40d02e04200075030840500200b8030390b0392000c01910030341c14498070200080c00300044550717003040d2400c0140c0704114000030b4141440c1402601d0610002402d500400460307190900085400c1c01075100020780b010f860340c00030301f0202c0c014121007025400d240f405000c0c0384140100103078101081d41c1001d81080c80100e40305007901d001c2c000703001010058120070b4804901403981803400c2251601407440781040301c2844605031045d0090045a964450200d85211010818038980829480d0300c40e400074000c45800b0594180b002c2402c0c0c140d081000180c0c13044c0c1103040c5814a11710084007030a003a102024501303182040b91366903405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 736169829 1250 736168579 736168591
    0xa08040e070c02030d18140102030417030c0a08031909050715030b060711090a06061d010c0c0801051017030409150905070f080a021e0c07030b040605040c080d08 71
    0x1005000041c0210b202d034000c00c0d041540201598003008801034018844c89040302a100f2035491154005808048801d1082c1c403550103801841c207080c0351101c00750001c4801d880d0003910780010441d20075150018403001098a01c00c2459586905000c81002c1c0c0e83c04007210004809490300b0900c1002c240002481803c82e42414818100d85900c0f0b80110090034007170300d149800c4000403c0350b00070080c41071205440418161545089030350740703e8042003541c6c890301c550303004160141820080030200290742d02e143c89060621540300304042e950084a500c0a0f4400c4500780d550f242072000340307608202c803200101061321100907400ca0300084c03030ba100e04c02d40c07150f0205250b40c1c2c0c0d0500707200c2440720b0303c40004006a15041256141502c0e010380b214826044180000e03203114001100145c02c0d00c241c03020756040c01083c000070300681e6028030303803644030b07000601091280e030100000044881107014440d03441940302141c0c6040600e00b6a4000c6440c1d00b0003012900130100807003c1d15407200810703a00203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 736171079 1250 736169829 736169849
    0x307030e0f030309060d05180a0f0209042a050f15030f0402010903120806130522030917100b03010b01140708070f080909010501030b0f04020c0304080601170f0a0804 73
    0x899600c006855407040c6a07141c0d801141c085040020120310b03a1103588980b0380c91b10701441d009188c8807602d4a03071000b51070003421114410030300f2015041c408a030641c054800c44002001071504417a541807104149078017550304421100900c11400c00441c1207032544816200e03400301d01c042d44102002800300400705518241441c0020301568854a4000000c507000004914075000500d0010704966049402c01d00940b038072040343c0c4040b4200d10880c2c3c400e030b4600c09100d84e6415804252040b407280c1d42c0d0b0580c00c03c50b070400c011400348000070080d0341e0158000020000303200400c19000580f00a01c46151180e40f6221032444680d821100e9035160185c101800c40d510780c11850301d12140d016040c0c018110b5000000b4003010000428020003540a0443c1c4200c00ca0780e035600110251030100c0c0381103800c10480d842100b414100b80d00034090f01041002600c1c00c0584801580f440e001c1b00340e1003070300036080c001242110103205100f0302000e000b13480040d00714180d150702d42524034420b03481020001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 736172329 1250 736171079 736171099
    0x80d030f09061803090e0408030402270702010606080105031c081009021c0e010b150a02150709031a01060f050901020c101d010e1003021621030506030307030e 70
    0x200c4a54031024100303038001c10410030090800580c3c180e41650400c101d0106482e808086003420b514400765110300c1c1d02401c1980307582d0301c03642030140e0140c420004a00c40c2125800103194140941c140c5846580ba42c0d000041062421034000d1a0601c103070b0086009030011442214100100303404040b100142e410114960388078020844461078455128a26183c408100c0802400741200002d9400c00d4810701030002c0c400500c1280d00321100750001c41c0d44002000b45219240440c0c002238040081180141c50030f003042c1d204400325200d400c43d15130300050f0341244180100505c240300f00085c070a07540c03620b0703074258100340703015040034505810380c42884004185071103c2c0c1c0c800c10005d501440041d1040c41d202120320b002800c1000d010326644050703002c1c110b1002c10b40d40b00c2d04980354180d0b0b00820400c150311148806a000354454201c103170302100703030860650200d12424031a00c003040452102010158141000a04860018022038403e410810102e0007103035010700c0511206008039014401c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 736173579 1250 736172329 736172351
    0x702040e0316110f12071e080f03040305010c112d010e0115060f0206060607110a0602030903061e1b090a030c1d040c0e19020c1c0207080d03 62
    0x6103016000d00d00440741820b103815010484981460040300c00c0c03d640d10030009404104018984400485000c00369005a004020040070041180c6504111007c0440720903240d486a81c24441005e0260155610006042080110034403443c0884001864030101810445c040c050329052502c3c40141c44c10040104001c50507843c0c031880c50980c20520003000305128250805028000c00005824120508400080c5481c0501c1c050228000f00341d02601d004d81c7c2d500b00b00545900724440c01e9480d981e00104100301500c0d100b1000c07000c3c1106400a50322441040b041602d003200042c0f200d03c02c000b640581c40711015080600b550010030200101d007400b030f90755110f410140a800c07000c07644440303502e00000501c01c5044109007078448030100c1c1440640e0040d1007001c000c03801e48009060b181201020000e01075034000d1282c110b40001116084801586458001c3e0303000300b41543c3c0d068004d076001c1f0344103000300050104158054009480304a240440890301d5281882151060586810380303400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 736174829 1250 736173579 736173583
    0x507150506060904061e05030601060e040509101103150604060f0c062403140304050913030e04020a03060503061311120c0a06080412020a02060a03023007030b150702040e 75
    0x5540f400540308002155aa036031450a5906500c0700c1c04103259812000320781420041246030690b0120740b90b000c120400c1348240402484020204d0015019140034600c10844501504c1c0060070341040154480c10200c11101820030001c41152203401e00b00300801165411a040220091082c10301e448000e4450501e1009044d24503151181902e52480100c00070402c00701c81703000d503405507181803e0440050301c242e07903d104900071143c0c060a500f0001c2e4400441d401030703001c02c2d440313403402c85113040075080803409a030070086100b008079403203c101340140e0808001c1c860b0b214415501180b00c030085a200c42c1000e40c940b100d0640242210034156154950400540301c0b4010302800034116550f960030700400031003041d81d00b125511189030340c98124500c002040c280154005044070314124001c0415802075110304c1e0071020490010720301800170702c403040c070b090001050344180c01c010b0f10b0300590003800c8030144e01910b0301c11404646804600190311007035030005641a41c00003201c030003100c480384c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 736176079 1250 736174829 736174837
    0x6010c08091008070f05090f102a031b020108061c02060d0504140a030801180f090c030605010f0308070611072411040503031e0f1303050607050715050606 68
    0x241c2249507600741c0d84050740c0c01410781e4480d030303d44c3c0ea1320b555000c1c00c841c0c1203980b41f2500d01480e9116821000c1c2d0725945c5401242800800c100d42802400f840209a004000c100282041c1c3c012030540c031103100515402001d0b0b10705100d22086800e40c0b0704802e0f40081c0164034050000390150403d20f80200a04100c0201116202c0d00206543d440c0d041310312194016000464003210701c2c101e4007008800002001840214495040d110f81215a0a040161080c0c0000f24038003a02581c980898143d1a01c2e80c1c03060030401030080c0580302d403041c118102402920410b90140361200046501000400e409000340c3d9032140d80107801141c25040c3c1061082c03a40101040075103a8024280485003001c110b40f103461190f00f070940180034603c605040010103004520400d41c040d0020441408210300b4001a007455030b400980203414914503600e401c00795007118620450006140d00180180300781003040701d92140161601625240c1182d4641c2c0c41011000303007000040e5101c00c08618175569420a031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 736177329 1250 736176079 736176097
    0x1b0406050d050102030118090503040308090d0f080304020108150307050411040312120b04020a050a0806010908160e090604030c1506180b0f03011a0d14070305071e05010806010c08 79
    0x40c0a044800d801c02c14000c0d0310130321035100c5011404080001d00041800780b10350306600034002d07508103481c40c1c441404a0740304415003580600c910100030700140101940c941750030300541c50603072030f86000c0c8005060004042d05050510203001e900d100a40c1d00064944103441055402043c1140d04200384a02d9000b44c0c0c000501004250030749411b103076440060607030501000e5805210140c0d10740c7c1400100e100e607601a10000d1000c20032490707200c0c05403500940202e07042c500303071400903940d69a460510b00d01c40003058084800c1e9404001c1010703000e0360f15411003403080c0074020070704080d680a040404c0c000001402a07a11000c1d101c8001c241b03134094402006420103c4105400c104038000080c070381505001e20440000e01c0f890598201445992031714090300010f1420340c0c0c880320402681c1c810140080311a00750406001c41c030788000b400030000651203200102041803c014104140c906120349004030140b641d0410880303603a0180701e0682000081c20702c18466001d40c14120940d104150003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 736178579 1250 736177329 736177339
    0xb1c03110d021615050d0504050a050d0521010819051c020c100f08150d02040219080121060c0c080c0f010501050402040308040b0c0c031e0d030e1b040605 68
    0x1001242e004100d1900f02035800b003445000c561503010910a91103035040142c0069401e001954812010b90b00c229002405502115203000b05076480030300d801c04180904000a80c0800c2503280c0340051400c00854800b107a404005560402c0c40e2103540d000d0043c4200c2c800b02d0704034050403c0c4002404903080d50700440030400040d0300d11000180d81e942908400700d00404200310450b40c40c0b40b00b410503115507031890362640c280c0e403074281c4201244619081c0301c690140041082c0b80042ea1140b00600c0c030f600007843d102174040101940030b004094141c4c440c08141d075070349455110f0742945010a50803e540194001040080710074104c903030040c060b03401020400d002842442c024000140203209420354002400560b0b202c2003803209a0045210051882d038090109120500544d80035080003040b000468803501c1903680028584400800c11072a650030180b1840d1000e0701c14402c1245034440c500b02400700825001525946020102508501507001d00142d1940d588542159004080c000d00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 736179829 1250 736178579 736178593
    0x506150d020a1202010f0e0609040c05090604030b0603100c1b030e090c0706052a0f22030605060d020607020103051503010c020304090b0312091504080a081c0b1c0311 73
    0x107140f410072494070002d90102d84011100000c6501c901001c134201f10024000070700304030407030084c44054014030502005001e804d00c04124541c03103010160000b907004808075444ac2c2089800c1c58208000d0800d800700b45030402004040f801e4008680b6611410440b104d068071851a04040b03411540b03102c0e031903a00005031030a1101c1d0041b05009400e010380117070401c110316141c4600b901c052008800e4580c0c021215003505001a101c5800a05202c3d40e4401c081d520f403009181c1e500c00c0543c2c15104500b5a40804070701070040c40003e00c01d45501050030b45400300d448403d60009403990007880030003810107449500081031204c88420030007400c00007034020700c5014410382000e500c9400c43d0040b0842940343c000000300d103140c0010306680712684418294a090b0049041c400d800180244036020520100800a8000030400c00310382d1050144400e1911a00240c0d400446481444006034030f0b5410407002940581c0c071582c1003122a6041017110700c2a42c1e841c60309a416110b010000725071030003042c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736181079 1250 736179829 736179839
    0x3010303090b1c140702190b06010c060605121c0203121902070b090d020c0f24070f08040906170601090b040e100c090b040806010b1b030d09030e06070506150d020a 72
    0x44000d0045c80903400703440f0500e140d28030180e20103040410180c0300300c4031040800c030b45500030303151001c8890065402203121501c0e0004203051504000e07261031903510101c040203c180300744294080d412041e102541c40c1c156502d10105070148003600100a484c100038584803159903d078101c0d084aa03001904640e00c0c5011806030b6101c07224102084090f0084c0c905104c100c0c60325201c1c001c403208004241d5081d10800440b0088001030f503c20f0039100c50401c102400100d80365000c40306034280f0072075200c2d83d00d504200f0040151409980007800204c00d00c10180c0c11300e240441c0703590549280e403400184113000c0b1400200a400c41c001c101c0c800d40a5000310160b041a1a040300c0d000030340035240c20207030b107030f1f00c840c404020300c1984117064240c1c024000520105030607a000304000500861300c40b401c060415019402d680c07004024030200d0790780b204020101600039442000a0008555943c18401c20f5110203488100081202d1001d0343c0d542d0341100183d6072031541c44c42007600540508066503c2d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736182329 1250 736181079 736181111
    0xd110d030c2c040605010201060617060f060705161221030b13060302101407030f1205070e0405060a080a1112070e040303111303080901270f080303010303090b1c 71
    0x441c65019070b0504c000851554014098541140e040b41c0e40d0101c580a468002402c3e020041e180b0f581c004104002d0613900e0341e4070381c041c10901b4003850151080d01013803944440c2c07140c1c10394040d0f10101d2548201c03030702140454840c0d8441390415010000150303212107080300100751020446502800a00895a08012644c80f8009680c82620112488981d000c401e0b58201d0503082500c500f0307242000380700b00191180c0e00c11260b003012828030dc983c05030404104016607030211100c00001e42c981e40a0718403803074039010700ca80112090b115400d007207080040b100c0c1c032158460000f60001c00300d40760740929a1290208040e48e071040d0803c0e00c0e803098803103c0000304030500750b4043e40003d0070301040810116009045844455580c00c152544500c0c5680341107468202002850500c034404407810501000c140e0b00c410205140c0c48207160030750500c4081c40000070701c2e400c1b038001c0783d00a02c01407000130b4206028034161508c030ba40352078689400d50218070403c0051080d0b0301d240350610605141c0e2610b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736183579 1250 736182329 736182407
    0x1802063a020705010b1806060a0e06030406020702031c0906050a0908031603080f06030303040b06031926030f010902090a08072702090a0302040506030f0604080405030d110d030c 78
    0x403c0d0000d1203110102010418094860899030000f00d6505e00858460700d0700c90f004081e0300c9070f14207110084450010010306030350012101910603c2c1c00254041c210f00c0c0500100142d201c051104030034604001d00001c1504031503004c3c038000e1000014842c40043d019441100007414010101c3e50785000c0d070b9240b22004110340e10110f0102c0c04d6a0041030f030082010303d9480c4902030180066085546036110203d0707032800604116014044d800e10f458520800c4031607061070718052020340c0c00c0e9030000c8000f8801214800001c0d40c00c440c045c4280090281281c0c0d01504490707031600096151074030b07000040e1000d00e10740d00c1915544581007000a5051004502d28041050394880031032501d4080800020381c03080e8640560310285032101031006280550005400ca44003404507460018018195468002d0998055400b000d0202d0100002c0c9400c2024842003400f0349006450810003141d03969999409028200501d80c441c0e21410845102c2c0c0202d85a0811603c014800031440c445603403a4220 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736184829 1250 736183579 736183583
    0xb0705060603070b071b030f11091303020304093305030c150a0f2a290f040512120405070501090f0501200102030106121802063a0207 59
    0x10030002886034900403c8203001c881003000d0320b510306681703962000c400c51003603258084101c01c0d4010100c0451003141d01ca1907a244120345103590060f44100b08030b4070090040c8841d1121708107200740c00000703a01000b91800c45405000101d02104554076074980d1580c900042001c20040c2017078410900006214202201d40607815138041c0302c20311041c07000381204400076018048003000003641a51281c101003120200702d00e8039810102c800c007001c1c2450109080f00591212a4099480c140880c540c402070448404038680c180040040271a849402d40041040703074584107081c0003805100e024030000d940c032081004100d03565101e085400b41024420380b070641d55403140000100e402e50103101910152491207000503501071a203001140d103085412100c920004020304940c407490130074000340d4060722080c0c540107040440300e4206021a605c10070b40d525900c01c00a0b0304c00140c0c5901c02100d0807598050800d5654403808000d0b202140324842c01c0f885000b14410b035010350100c00340e0103004454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736186079 1250 736184829 736184833
    0x50d0f030c020307021e0a1e05090f0906240303070b041103060714071502030a0603031d0a0b0304111527030d050705190c052d01030c030b0a0b0705 65
    0x601041d800ca81d80e0146000007500202c0d2501c0752110034800f01e002d510500c0c0010001d1080b16150300160f09078000f103011140c4030219048050009260280442c4d5001e41d403000d425201c2d04d048407103644d88840c0906105401100782c410301c401c0900324000c100201c01d001c0d00b02c07035540700640341600c0c0d018002c603004c0c2d450624074942034055207800b02d075444c000c04042e95040c101112142400b0090780c020b4100f244d0400307014120043c500500e0000e0340c46150700500006030685982030150414441c07804081d1000d03203140031151560343c3c8030900c01c20388003200d4941b900d0b030741c80d031510f44200380808015a9009004000d410002c0c00900e0041c54054001143c03010f800c00d07254084d90604400a00d401d601d0b40001040c84c445611500181442c0c0e400f4070220744015600b0540d100c4400000c45098802a407604c2c800c0c012403c10500c02c020510324030b00036905d007800400c000d040404103103a400c2d04140d107038001031010034071a07000002c13000d400418580a09a0722401d0b0740301503204c04400c941d54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736187329 1250 736186079 736186091
    0x1603150c0503091506010c060614150703120c0c0203031306030b03071d0901090816050d09140405181002090a120203060a020c0102040f060c06060e0123030a050d0f03 73
    0x21a00c680c0640e40070388000f5008094140b10094903a5400600500b00c50400070036241709000703c0c00b5805508001c01a000014400346000703018017034100020014290141410052030000031781c40080d0f800d4951043c0000203148444200031201c40210a40c060340c036200c0801e100c2609118844040111003968030308114800d400c074185a203a0a49109203440e044003101421004044038a4440c1d11161850000620741515503501c10103401009c401c40000c6d5108041c1407c10100300407140d1604000d040c00150580b821001585036800a07045a00454441001c91400b400403040103040501210035940361031052407081000750010b0b00d84501c56101007000054003106900c0446001d500503020b06500d640714001540650b014840c4401150340c204400141c0b40c61210750b41c000303044140c1d20b14205022a04060f0140c41311f40e044680e5441400c0c004003e5a840ca0b104002c0c00c4c0c003402a1107205800e0200042d0404900c600041c0c154080e8040c2031070065800b91002a428031241c50420030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736188579 1250 736187329 736187351
    0xa0306020a0206011a090f0607020a080703030e010c110103180210030903080f042607024c030b03030f1b0d08010509181e07090c050327160315 63
    0x200e04d200208114170301030f0800140c40b82d03007001d59a8950684015000d42d1800b41d032a40402d001c90215403107501d60350031261042c01050b81c014040c0030b459000b40b90040026885403500160030035850203090505030354100d15242c000030344000328a515001400d4126a0600030000303000361404413400c400181c1c5500000e01400031100d101070160340c1180d070f0800381010000340681d0b5203a5040d8001107040091010f000103994409603442c00c80d14103903030600c0c000c0000c40741600c0d0303241d10129040c0007618600584d4070201070301c0c6407685000052901080700d038021400f1034254401c505910111001c00240003600032241c0e171003204074450000449103200030303c0301e04030784c503071420b0041c0daa000d88900045034282c641c06001e00c040301e403500b0554500c40500c840e103242e103165065600815400080b0104800c02d005d100d49803900d6850304040e49180340580000100900582000a201064002c3c00109400400004014210110080032016180d05180944840c1c04a05062180c200008100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736189829 1250 736188579 736188599
    0x3060605070f230f0a03030e0a02030c10050f0c2d0a0b151c05010e0a0320070b0706060906151b060e150603010c0509100f020c0a0306020a020601 64
    0x10201d0307008800803034101119907840e0444954004506854545400325103030012042c4090f55400320581c00800e4020b00c0ca2401030161000000d0480c10360f0002c40c100000751b100400c80040d00e01c8200d0754006519003848003510a40a0f846c041d9901640101c1c02304014440040c03c2d02a008216944402450310110208607403072960442980c66008208400700082e9216902904104400e02d003051400c200008118180c010744203200c081c0054480350428041d080c4521008004107101415103071050781c40107881d801c038080c10b0392407a00104243e0142c80c07038180840c2002e082d014148950307520302c6c0d05201c0d001c0c00e243d00620310300c14604080004d000025454a65040072551548180d0f0641c2c008035003034502d403240c070a0300c1d920349400000d42292024009194401d500d016851601d090400a260841320200039540621008122884030b950724041610700368192482c0240300122a42001c0382801d600400301904851000d0010041159640145c800b044180d400c030f0302c160b80c1e1005621 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736191079 1250 736189829 736189837
    0xb041502070302030406050901030b040e0124050102030a12060510110708011e0902010909020a05040801060504060e060607060908030f010306150501051b0a020a0b1201080627160b0a03060605 84
    0x50151388100f2040003442d0059001d03002c2802c05060002c0d907001e040001c80d0a49440710407601c070300d95588409100c00c50300180c02255241c822036025a001d414000003030342d2480340241d100144844007007140300f07420316074010300040c1070040c007288441200094080c08101a010344501075024004020903071800520690740c40840140c0d804184680001c48440248104c50043e810000c0078000411a01403900081c21210b056070b8071140d41e103160051705800c480480d04070a2003241810010458603e07130820720307a04120201c0f600c030b036030351444d242005c010b00c040c200042008501004200c2049074036800d940c100d0340925414811407404400c520710002041c05954080780c81840806245943e00d4001c0d80800c0310302048510a13041900014000005507220b614050307000200803030500c5070281c44034014174201c4000e200d1811300c071076481e084440020400400d02441e2803030f03038560a000c00c005003a03064449402210182c07940d60b180c210f0b0380204001c2c00400d0034035000003803a0313100b40d04503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736192329 1250 736191079 736191083
    0xf120a02150a200f0d09050a0f05090f090703050f0a12170a020a02100f0902180705090405061f1206080312040b0a020f1b1501120b0903160b04150207 66
    0xc0004050941c14922004441190f01c2c08038031400040d40001c030820460311018441c181c4561640516141c00c10200103010b41207040070000c0301c0c400f00181e8581da51059003002c1142e161a5550760385000891921001d5440a0510310984202c1c0005000c04100c0e050702c01d00900004c401c400304c1d03050540b0a100061007590403818590002500c0c40c0e1303903a01400008900344160784496080c400600196200f9440460103a42e4440481c02103140000c15100da802d10ba5141000900d00200702800c1e038003480c19024001c58686000600580d162000d5500714003112040000303400501d6801010341008848006d044ca20701030307010a41751400000e8549140302c006407d4400d0359680d4520704480d80213884c1c1041c294007407220301d01800011028200000780d003003003e2103040171044843d00e00000041a00381e400c50210050161083d41d03645220301640220b424401c0b071b200c14030441d1651040424006110001c0b0f00107001f0410380580300d0b8000c41c000d4a000c80c03d5042148450308910400c480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736193579 1250 736192329 736192337
    0xe0402040602100c091a040914060907030f1e050a0c02030309031b010e03041e0609150305070e0a1502121204020121050411120115050f0f120a02150a 66
    0xd40c43c203049094000d02c80100851400115860741c4200c000342c0d2403403400300c14241c900d004c50240182a018801d1040c03011005d000190142802e001040c440d01c4003400f03503810940c68403c41c25801c40590002c00d9070b20204c1c40d200d5030100b06d0b25061b01c000c100960f901424a070502c0a003c0c102d520000a5034040c4da00c1c000554030700f078811501401c103800a10340f0480c1e1035417501030003001100140058001011740c1340c03600c9803240441e00d0420031a90360307400c0791061040e040da0500c1b0084201c401d641880156080009a98484100c1512015041070f09240c2c00782d00d202011820942202808054001e1502152446084480d0480d4075005107109020304403112000600075601c10050894002d022402081c241810f244401d415901c04403020b179010b080e031001140c0642407482505229030910002000b1142c034110301444a06c0e1140b141c14882c5083c070103656030355230740c0c2c5500881c0d080004068038541d08483c0b1005446400c0b040c4148d209114603c0c000c45502d202104441c400011955 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736194829 1250 736193579 736193593
    0x31a0c04090207060b1305101a030103080d1d010b011205010b070206091f050a14030912030709120b07090608161d1e030f0f100207080f0315010e0402040602 69
    0x80074000d401880d030a40e1900d4440621441540702c0504101a00d0111203000c26145401103c40d4011789039039000c2282e0800a01290900340e06040942c4d05407a80b01c2e8005503550408440303100030340840e884500f8066500724038490490f6055000c1220ba02c42030300c034010049050303451181281c00921030000c03000d900304400401882e18000a0944e040c00510030300c06d0100a41e86000b0704408210703014082000002ca007040c2541262010b26024000c81c401c616516103118555221542c4805a401400d00440443c81c10383c091038142c4041d020329042000310680b1390402080d0410203542e40c00100350704840118400d0322520006101d2101090700c50094a02c0450031628011814002c0d901a00c00c81040010780d0380d143d00c3ea00f0110050400107000c50307074400c2098140104013103c541c0d20384c400b5010000215020a80381d00312084d0700b030700507190a03240c20722010f07910400741201018003001003004014121514205000d510130307a01e400b074014801041c402284510b01894025900c58a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736196079 1250 736194829 736194839
    0x11d06070609030201060e07080108070b070f06090236090c0d0b04080f0f0d0e19030c02030c1009090f0207020a05090a0603240f0c08061011030a03020301031a0c04 72
    0x28002d050100e2091000049460b03442e030000b070703200b00140c1d00c0c2c60010310f501c0010043c8100400102003d0141c4984241c40d0031541d07a1441345000300540014181030f2501f4004055540e00b004005010034903e1051030b14a4100c0c2101440d43e2400c250680c14411200125071540070000f4080c0c00510080c0c5008135158654540044000c030060045958817800c006001e15101010302900e003e51740c000100f9229810740c0a0401a10f0003504070101e10f5108030040082d40207010100e00c00d064160070b0031740800010f07001090800000068090300284081107161040358804d46003000c40d910410108506000030401d04180e104004029502c41c0200006028916202034601c0c2c21000348031000403402d50381d90317407000400400403501003482c50615404c01c2120701400750b03011204d283c2404002e2030000724005070401c0c81c0500303440e000d6141c100080c140346014410160404424600b00c6e6210040020700138080c0d802400109c400800c160000c0700c200c0c0c0c5c1d00101074003803400505640c0c1414104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736197329 1250 736196079 736196081
    0x30501151b0c1a1213030503130602040815070818070e060d050d032322030c05010213050f010527061201090b01080c0a090e0a02190806011d060706 65
    0x5010255608000540002501550610f0381e6980361503012503603031110890300506125010003028480052981c0320001c2c0003907032040c116035219040381d5007040c16600d1428400002e000e030380c000c030340603104040e04030011514129031284192450f40e96225955660003004204807400c6c00c140c10141d00861080c4102c950030100a60301003009000e002c18242c1d0364035405c2c80d1000c0c50442c1c0c2e001c00c0ea507003c40c8004980504a2007500c40612034901d982d070800700b42200d103a44440240c0c0c1c404410010141d800c0522031000c11a000c1e0b0004000c3d915088540c000410383d885038425244a50701c1d0401040d02c95000e49d05483c0c040c050042031401d0440e114068001d108450495194050301c1040031000c0c007103d00d6102c1d4040c03c01c4d89000510500241d001506e0280050060b0380211400e10400d80709035407012050064840d0740104034043d8865803030b0703030019008810441e0380d9a180b500d104000d0301e9021908034420f00090380c400024154010a03149180f90700c11005802103004c0041101040362 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736198579 1250 736197329 736197377
    0xa030b06101d010e1c03030606020d0c02031009030c1b150311070f0215040314010e0304080a03050d1401120b06061e070f0c06080108100203060f0d050c03010612020103050115 77
    0x6803503c0f81c0d614503140c05d18020a4031160071000300750707220000c0c400154100b051001091f514100009001c8542c2c00195507030707004504042800c0d803182c0403141094410903400a00c180d0110b0546010381d03400030f04d1805e200407402140f03205039002030300000031031180c09450300e540a03121200b843c209803600c401085030814101a60420b003c2c200c00ea0b40030032000000c0c4025801401c511922003102c03160399080d03401d181001e588641c800d01052251144c0480c41e0781000764582043c1c0d1341c9d940441c0d08100544820103052410b0a07602d00006200703500ca140400103e4030401a280e941d59808040203400d000380400841d601407503009546648104800a0038114020007940e488004a82c0d58510b54081a800510001d61003400402841e0b000700030000c500b400f0070005600754501040482c2c0070500d10020b061060390007280b803405005003445400c120100c007030024130a8a0f04c8000305a1605014202203001174502000014405902500e26482c0381c1c55941e080351511780c1c01c00d40c1003a00a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736199829 1250 736198579 736198607
    0xe120703230609100f2a0e031c030b0909031b0118080a3216020a08070e0a09120305270615030106080604020d03111501031a0f0a11090a030b06101d01 66
    0x40f00321f200c0e04140d9806c1004101d00300c0441040560014040300050588418180d0a80123601c000240255044041b040c0c0d01e0b0780c464020180c41e188000d001041c05481078002802c1820000c000c04002c1c0560754005144800181d21003400b8504140c00c226507981400c165080c10401c2c40b0f8840070a4007404009100c20550382c0d420852100d0305400003a0300040540c026036142c2d100c10000c00103401c0005015600110010007044012010b40720404405407000341344042603502c60004680d04143e01e0440301008400c54401445460100e01d6682c8400903100800e50044200d688181443d0500a560a0b1003025002c1c0920391a141c2c00e10000184c06801101409403043c480c03140c5d828200150780070716402c05d4940030b840d49541088500802c07091420214503004008001c0e00d00618108a40c02410b20880007c01425244110b82c0d50f0180414503a80035800b1a4000180801d04a02902a000c2141d030309408003207443e0241e41d060340b9140c0780c1c000d101403920300d0710266000f103905030700d500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736201079 1250 736199829 736199837
    0xf08060702101a1f020607050c151815101401090902070303090215071a0402091306021b071502010207052107080703030c0e120703230609100f2a 64
    0x11103100083c61107002050394400e113903180e840c038040c035540c10894a5008001814200c0c81c0459a09000c2c0d11103e04044000803560341c0000701740c0288180c024107200c000801d00351050301c001c1d81c14040c011141902c0000d0284610a000702c3c01f01110003031040e00d400141c40b02c46445107030654030400f039000f5031416018141d5038820007001d41c6906e0807002c1101c80094146684800c5071800d20407030103c0c4034184030510881410000103031103826001d41c11050402c1520f89448640c82c11101038450400307501101d0b5002d010342040141c00013158001d44515843c44c000400d0226412402c0340500da00280c0540d02c969064072a115554004100443e101643c0618000b01c0791100c0392103038031078181100025511264294070680c84031945a1f1050708961060444100405045d9034580a00010b01102c1d5415a150090018002d501034094103603029a0f505143c03540c441520b4040c40c440b0340301728609140210782104114407407850321061500d03e14425036148981702034aa500e81940d14184 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736202329 1250 736201079 736201121
    0x15010906142a010606050f0405130e010609060e010909170c010e0105070e040506040b100e0307030c0e01170303010803040b0a020c0405042102030f160326010f0806070210 75
    0x42c8a814040c0115051003400d00c0b11000c07a05400c0c0e400c507140c503448041009810f0103202e401200001c12142100d10880305440c8185a4031428001007002e0002c0d00f0096281010000f03002015410240403203400790206a081d80c0c1e5001c024080d01c24402000301000605202030030b800c031181010f0711b84a01d0a03000054210404680d081c01c40301c003a100400070802c22078419a95203081c5c02070303a610482c20364090141c41c0c04003000c07440450101c5d600a0500210f0400504030b41c50400c04d507002107800038032206099030f0302ca18000c20181e0a000d02e200c4146603203480071034403000000f1241202c201e00d00842c94031717103046610b10341500244800310840c061541a608580c2e200d01645000c1c03400340d040d001c1c3c0c801d10b841d000d41e009907450f50a4400e40d0020300c41584050788030010b486014200603c0d1300d003464214a000c88500d01c403040444006004110001104400003041e641a40c5107110000c01640d12400c83c19503403602241c00400503480040400ca01c0c0000f5040f040d884842d5207000d001c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736203579 1250 736202329 736202347
    0x903140406020c0a090e060c090402070606090603050c011d060f0d05070f02240f0402040b030f010c020705090c03061306090e030d060605040f030b090a0f03171501090614 75
    0x19035005078444801a40900303022002883d201c82120010000201c007008000140140c498454400a141240c01c80021230842c1603503c0382d03011a01000d90140d010004e190b01c5501120050295002c11794052145421402c030a50082140d840c0c503005000d140207090046a0411805c2e0b031140d588500c0310340c0b080c0444050142c0b039014850140041d612650700110390076400900c0d040780d402c7d00c210b400140700d24000c90409030000c0341d504440391810100c50b0b6520342c0080b03006030001e44c1c081500751242e581082044a410f50150702800181d03401d0742c041c5569482046200702080e5a144040c800400210f9460701d881490342131b005012010109902e5503030341181c4110b075036044003038410b900700040b000b403034614902c107050141140307061960410303040c855041060445400020060000304002c94001e500410407048420b9102142c1510851181303402400722018142607800d540700c100105400001e0700581030346980e0107a5074070442d285003440459100c600000101c889900c10000070b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736204829 1250 736203579 736203617
    0x130908070f0f0212070b0a03021e030907030b15090a090f0c08101b050405010c0f02090c180904050c130605090a02040e07141c141f0501080610030903 66
    0x5900d9000b40003a901100c0580140041030f65016074040103900002400d0048906041c03d68064503050b140040c2c40d8880081c104c0d1200743c2c9031603d402032040c04005c00c0b00e4031b0000100002900c0c407a801028007a112070405515a5905420072540b095081000891385178090f803241101d80c1c000c0075440f6120300c0d152640c0c0c028180641203c02650400d4261807550111801038909104541c40c420451440c1c0c808000d140340260300034981001450003043d8140015840c1540803107800504800040c10400440c0e04036070b0009095a030074a416076202e144918001200c03621075074210740904086a040c800300252814600d00d030301c0601e59201008107454507041c4050307202c4c210714000180c2da070703003401214038050000030000010855103850f424084000300d0700b0789070404260500420030300040744050300034103441a01c042a01d018401005450712049806041c103003401501010a582c4441c01100c3c050401c42e4015002074800184890070380c801e03407000058030b00a03d00a4031020301d44003100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736206079 1250 736204829 736204853
    0x60a1a1801080c030c0901050906032802010e0d02010207030611070503070f031e05040b0a03020c0313030c0b0f1c090b070210050f040b150111010e1b0a030213090807 73
    0x200e108221900601140c00c041001c0b02004030118010265004103100040205c1c90500410740211550004103a1603181081344510611000e18480403a088031a220400400303030f101c4c1a4001251484100a18104001c04d00f54054060780a00142030030740d1141c001805104072501401c0c82d04104120128209101400e5401d10a01409111000e1814018081d09040303030b07003404074040000902009500001150100ca00145440b07842d9602c02001350000d00a44000c80b01c0e034000005c511440d90035100100094034403800040c0e40c03030358841c944418940a24017080d40d13080801c000b0303080c6002c1e081048010b15401d55601144c45686a552518001029150300c0d001da4810f0b1217003104580c42d03000e51a80089170038400300c2d591070710ba150030150603006021004005044a4040c106910400d10b510403400e103000203004200000b01001d503600789507017825001e1658825080554546082214202c980003810340c2c280307007440f01c401001054134810440d4219410000040041c0f82102e0300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736207329 1250 736206079 736206109
    0x316110d021006080c101206030b01080a0312020c03160c0b070305070c060206060d0b100e0c070c080d0207060809010f05040606090b090601081506041703040f0603020c060a1a 77
    0x1801d1400000342d00e00094491642004032240c01c40c400309216506c0f240340c50810510781d4946421310512082c40b0b07100424171904050804e880590010842020002c0c4405d003462007551030001c1084212200300403801416000f440d640c20070081350340a1442c28080311001d1340184880e03032025681c2d16000e2004d90220600720007241012850b1400c0c08440f440360030060105001800031480c1c8140000d024180c802c500411814200b004510356441c00c0700500080c0c5a007940c1c103446410300054048598110f0007045440201386180411400400304602c405964640c0041503001c0c1000c10513150320000400804481d9030f146004c0e07500d144180203032401107008803400543d840c105180c03031007503542c2098120700400800091010a90384801010780c02003001c0044007400aa10000413800c0c07285600000312084c0d0b04025004000c001300c002c1c412241d204c4140c054441c1c2d611000d030289d000315415150321350411400150440c00541150f1500f860781f24440c002094403400007030004900041d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736208579 1250 736207329 736207333
    0x15171f05060111060103031407060b09040302010b03070602070503070e310212060f040210020118120809070b0f1308030a02070609050a0305061501140a03051b0c030316110d02 77
    0x51120782d582100c2e0521249401c100031341459070544e00c02404081c0e42645c925440440080d000051000d6070b8060300890400404e01411400c040c10028041d04840da042c03031180c0241c010004405000155040454a018001c3e03c041850581d2201c5100c5006010b004c1006007024801440001000c401b00400021241e104001c0310038010b00a22210285079070040c3d5100d0401e11407504085100c0300d60142d411100040e00071401c070022809000c0340ca2440b04c105000210f00d1041005000d0344080080c0d1656070b100c000d6448800003035403100680300e500401241041181852130622004007504002c5a881c040c0c5035a58000e0189503512031900c1d0302c01a040102c050103016070000550008003000c60341500118103544441d5140c49028003922541c10000c0c0f20b400c5545d010b52000349100243c50b0340103807201003640028015041c01c950b900390909030464492000080141a07800e8004d0210095056075034450404980c2070b50b880448040c0000c24141c10840c140400615a61100680c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736209829 1250 736208579 736208581
    0x40e1608011401061b02030c1c02030c0d080a0e0a12051507020c03030427090b0405060f0f011e03080301080c09060d0512030403031b0e100315171f05 66
    0x111003400c4860302c0c9140540808441c1c010000c0c03540c0800403001d040c1041d80340b44c0041c10f651001901e0181e40808090b0803400074000000302031031140c04c118490b03000b41c05458402004c28104556031190000041c8406d2050122003031162096494510764640602038499143d114100100f0003c9100c00071221a4007403040d158844035220746d015000050f5000404d031083c2030200281d281d008074040c1c0e800c000003c204000082d1101c0c00071240002400030b08221068190038082041e144c116419105880b070100410f4015aa01e01090f200b1401503901c0b2060b84d0804c511201d01c8520b01c80701e41f02e0f203142801c1c044041610203004500030541c0c040149800d504803405d1000307080000b40801e10450309d000c62035000c80c00116640400e0b58040e04115600c0e520b6141c01d600918900400c00322152068080c4400c20350400001203109004035913180740801d8601e021015a10f803503142e2440c0140e2540100700d10000086c4045507104510152110301c11800f118004000ca100000d00070681c8683c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736211079 1250 736209829 736209839
    0x1091e03111204060c030e040f06080f06060112020d0b130e1e0303010e06010210020a0503062107030201030209010311030f070f05041d041118010911040f0e06040e16 73
    0x4040320440310010700107000d600c0c0d00c104a4810314061481070109011700d100d602010140300342000d00032040300801c204040d90010844c14000c02c5140641c21030f6218410001c40c41405c005482c07407041e03005941d0040b0420040800780c0c0a07400421042081507210f42d00041290341d0344015203105145204d0010300d40081122040ca001482216441d0040c18000b00c1710b00441e02004403411b54280e0ba4181074236442e580c00403443c03c0c0910061250b030b184081a296800b80e8058000c1d0b02650007254900340625500a0f42e40310900c83d81c80b01d60712513210100404c01540250050000750605050010b00c50301c0801007200c1540c42141e040703100088c1882007105160b0400b10080315260946402ca080500b46020300c560311450b41c000103c15480c00c80018200020300c2c0c1440c10828025001455040449000401d0103100b03001c0d02980b01e0620601c0900d090148040d10215540c062a01c2103840c80d010b8000c2001d50041c1007a504a41c0301c4141c462503039810807014092401007904028564607003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736212329 1250 736211079 736211087
    0x3021803010c0e1c030c020f1908010507030501090b01120f1508100c0507051504152301060e010c02010e0a050405010e010e062d01020f070f140a0503031b01091e03 72
    0xa01904e2401c4c041c040c180310046580000c80641040c2d06407a100440314106000980c8280c181c640b40c000203601c0b00c00460421419007159000ba94952804d00c0349980300ca2600d41a10800c3c0e88290014042c00c105407255103031600400341e803010312400003a4018040c8000024500c030340c0c1107081283e0007443c504802030440d21400030b0351201803901d10706100e09503031007586170f003210b60482201c540380302d002c02e0034040c2184034003102980d04c0408101811019031141e07502002c0d800c80c8a4a03420110000070840d0040790a0b56038214160360741c40340c0c200c4540c015105460642103a54010043c0100890035441c0c0b0f00c10070f40038124140c0203074801e40c50302c500c140700c60900914031405810003000b001346e04858400c8020601c9000c0041041035204003004034a00703440a4005100d51040034000610100d0059002080c0c60030000d0004007040442c041c841321300d40500c662a05603108000e030607081d0003214240100d1000400000c2200c6a03140c481141c00302401ca940381c03144c6805140d02d001c040d08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736213579 1250 736212329 736212349
    0x18041a1507020d020d0501110703030b010305062413030f0b090d181404140a0e0c01020f0304091d0a0506221203021c090821010f050103021803010c0e 66
    0x14624a80c90201c00340d001c01c0034115540c800074050307420081404100202900400c0341550380a4405407500403500b002400f80c41004155808640f401011452504040011090040c00c01240510311158071450900640c042101a000003680c840302200180c40307894100200c41c0521010025800c000b00e00e075090052401d582d0040c4640002c5030502440450443c1c3d0450702c00080c0590520100f401243c090a40108005240d074000010080a01d480d580035424289449003110541450030005a0350740420007030944540e8800d0004004d501a10742001c40d2030f002d2050240d640135103250100e4030f009004c000c100c0c0e80e50020001c00c100312000080d41d81300c44800310801015079460707840c0e658641b00070f4800c220030545c00280c0c0344d80d01d6035800c0c0d001d1342142c09030a04108d02c0060342004015a08004001194144d1400810001c102c1c0c05040d18141c9254a900c800402e182400540c000e40c403c250340303d0346070481c802c009041d0b40c0a11991421413000c3d1143d804044885041001c0030349 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736214829 1250 736213579 736213609
    0x11d03030103062a080a0f140a060b0c1b1c03030c23120a020c0307030e1e031b1504180e010c17040203030f0f0c01061203120218041a 59
    0x4c001c100080d50305900d50307400300c1e9280c80c20301e941192284980307030001d481d5803c10b088002d4100f2001c26041220049014402c01c03100d90108141d0341c9401d00700c4546e00c907030242c424880e8002400e000e0210203141d08140a480c00401e0302c003009115015081424441d6481540885e0741e0344d912480962b040702030702039100300341540c41c01c1210581e080c0d084203002c0c0c00c1350401842c40500c002240144150b04542180d07880000b00c0c0c3c0c9804082c580101b14100148443c0c0c040e414152a0a84000309600c0c011070101004010b0b00298640a2024840501d5890300d564040c3d201c008410121040340003c1020381001c135030260404030305140010544400c0c0c01c003110715070301d02028264003e5000c421491a1114a0201046c907215400000d03d580036111000c21028030010f07260150107039120051094180701c00090200c680c0e03581e030003140c003105a1300140110312082e401a035004843d5005050300710001c6425000c0c440d4040c0031030200c0304145a0b09000d221142a049680d181c9400d51040143d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736216079 1250 736214829 736214861
    0x903010c0207032d060c180b0c2119030f1a092a07020103020409050901230403020c06030703020c060108160902031314120d1a03010207020f0111011d0303010306 71
    0x11002e50000e00c4d5440c200c0005010a03946164440c922881040800c2600c1d003040313810303d41d064582111590300d03880f24201c04e605204a4425103844807041440a501c1706900e4903250030304060b00c07000a569602d080401e020103591f6a1800b10443c004d2140c068146c8001010f50b4040024105011740588041c0c8402d821451400c00090402c843e04200000d5030914803501e5164149440141c01900407500041e40d000d00307003c10042c20020541c4910b802d02c04c5218000072050a030500c0d0440c0701000d481c0a00140c00070f003a4904903084c0000156001000d62400500e8a0313044c140d860f0900d1020381050500740c002d2404052002a96003960016000220045186080c0b40002128070703400501d0061000d907000881807080c080c00d00146448000300c4012a5031a9403e9550000600100356500d0b580301e8089400503141c00e0502c00e440300c5c90782c05041035080218800054925940940e618007003903484003445801001e034880384413070700c510040080d5120f50443c94590242c80025272009003007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736217329 1250 736216079 736216133
    0x40b010b1611060f040305010c090f0b0307030207020f190302040e010606201509010b190b07020108041704060c020306060d030801060809070b0408150709050f150903010c020703 78
    0x144441204050744603400500c00030504140b0000c10038a0007001034500e01020081400000d011042d0400701c160103441d900d05022a4a1308081c08881e5094010b80010f04018400600200c4c0241c0c01003040d10b0004180361600c8000e50b0000352410201304043c01149482c610030400c5080c1405040a10300701c3c40020b01ca5241000d070024540d68981402940e40b0860f9122081229018000d42c00e404240341d502144a10305608454040d03e41111070501a09681210080144040e010b580545009407502c61920100e40c00440310001e0140041d02c06040d007003007903041c141021000748010640e544825400d12100c0c01010b0420320300601c01401001d004504200181c0c3c40794406055412504003030341c181e101d500c0701c9443c0030741503048407680c5040040e01040d2500300103403140c04030900c0702c1704070503980c0c0d0310704101c401120610800b9004103940c07803004d400b443c258050340c102800103c1200e040200d0000007070b0a48031006c0d132000240e08035100038024000c0c41c1d400b021b9840c0340000b0342404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736218579 1250 736217329 736217347
    0x1b09090b031009060e15040506160f0c1a070c150b09010509090a0512040503162106090203060103030908120a020d031a0315010f0e15060a050d0204030b040b010b 71
    0xc030710b060061032803116581e1824030100030181e401808403400c0902201c554460003448010071900980b4107480b03520409000400c04504407030b450301c00c084144e854003010600d400050b50004003118044404001c0b2101e000121848202801d205160541d00d0052060441c140b0b001089091117650a4403420045d11001540300d0605407030464905a03040211070b61403180040c144540e024004241d4024440c1580a032540074001c0c00640704120191005811900030041240405200f007001030303034007680c50861204c0300d40c40840000f40500d001245820550380000c5c20240c00b43c10440124054410a204544080200001149001114070320300301244102030740c0c807051204000101502d1300658501c1610b00e84250024107000740c100d4811408070004d4444401090260081c00341035500d00007940a05021014001c0f0403c0e51f441c2c01e015801018081d180d80003006200c02e01c5070030810079000035a00d2004100071405030449511600f802d241c00741084106a21050000c032040c010300ca0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736219829 1250 736218579 736218583
    0x1903020a0e0a0e0408030601093210140a03140f0106020d08010803090d06060e040b0405061b0d1113060f02011401050906210d0203030a060503061e0604020d1b09090b03 74
    0x207002174011107107644035512000100c44550450300040703030341e030706c2e87da0410254051100c02c03400d000c0d003c070f9080481d07504130030500c007901c00c25101980000d40c00844a8000d00c0e1910014007003040c56140c08100d1004004403c018070200b61117140750048020300401142d83c2c10b018115220701c2c2880c00341c4055140100c0c1503502e024200c80e6511403002103840c142005061b41c4003070000c0c04c0f158820151440c250616412003142264251868041c44000440800031105020300c01511142d80b14205001001c194004106000f69011030460402c440701d0824403240b401c030b004154607643c0200b0108659002800c2d1040350503010f42c1c4100c40c200500c65a80c4e212810366020703038191503a02003117441e40306905d0304c07850f0b80f00e19143c940501e00b2200d002580c0030005501c20344000c502448201c0d611024565540d00031600c00140908103c0e401091500c5059144d410160042c8098201020040c50314101c421804d001c11809034011400140b054129030a00c0c010810060108010f00400001ca0303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736221079 1250 736219829 736219831
    0x80c0f0403030e360702210703110c03070905150414040c080106050d030e0102160b09031203040f0b1807091a030a020f014e0b130c051903020a0e0a0e 66
    0x1201201d1400041a1034420480c064110304c80e01411494082e10045000072940142c0054002500c0c01c2c07140ae0742d0890008003204001c0300600205485803500100d18000c010281c9480c0000301303810031035082a90742d8003039401c0007501c91115445504041c9400900703030034558001c01c50b41c1d05084d4204000c5da1181500000b5641609002c0b502050180040703040c03944c40d2500e0802c2801c2544042101d0b245540a000e1012040c0c0842e00127095034414140c00307000844006240110900903034000501440546800caa400c8182c5003003889804a42402c2c900150041102c0580d0b42e0380341020360100c112107955050064001d0040d0003081c0d0042410042000c00403414004485111500c60300d0541d00081d8040100200011060845038800c42e4409060b441140c903100c40440d0712501d0714644522205013000416070142d40c4108610000178043d020040c01c2800001c2c007491000c0000d40b8800304004034643c0d40143c1d45c1051183c090700c0c960f80b94102c4c80c028800c0c2e2006102d026021003442d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736222329 1250 736221079 736221169
    0x4032a021806031608100e06040c120f141c111038010f05030c0301030b0415181403040f03060209061c1a0916080c0f0403030e 56
    0x911803035910000400c1c603041c90114204e110300c80c109000200c2600210f0382c450b0f55030b141241130004c071511110f61944c5010a40d0701a048104400003002002881880c80300d0b254821650700107040f15944910140c001c0d150414225608944181c2060385410b030415104124242041c3c203000c044445015607504c0c0790307081003c8560741d0340f002c038003d41250244800400c0c20211304045d5544d01c1c40100c41d54003401040b260100300c03101d002d01e002c507000d80e00303980c41003189100403070460b0b19603110108400409081540d0f07000c010140741d034612080e40100343c2c034000c84180559419002d860440c029680c0d01c54610441e400920007031010a51528a02c2d040360382000b00541c440e901000040c42503c500e5000e0703c21000b208148409141040d001009402000071501c403480c000d92083c450700396012141c02c1e80740e04131390a885041c640910561038200d8101c001e9141010b8018503100c09640c0190000d5001c10712a10303080c1d8507882d1070243c01a080e02e440c04044403084070141e071903104030205040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736223579 1250 736222329 736222369
    0x50a080318180a0f060f030c0f170307150908070605040b0a0203060f090603070506072103180f060f02040801140c0a051207050c1b041a09070318050604032a02 70
    0x410008080c4d0340003880500000300340046c00e150350303107012106d54169205504001c0040200082c02c4d1034602c00100c0c0781d142d1000598a410841d6545100060385204000d201e90790350b000240c045080d10018080942c40b075400080c0c5400c107402d1198010340f0040440d00da9600400400c5041d8070341040028400714240c850301c48036100d03000004d05040d025003010383c01c20804039021080c04404101600c011401c65180c1c1c8100345040790031002d44608009003d030817540082c1c01c00000c0e030340c940f903400014001c17030000071444552520542a680300d5405500a6034492034912160084c6452807900941e1103000c1d103150200441c006819406510341d0802201b07602000140030328052401c0b0f994801d0040b00341c4101d9100c0c2008070310700e074034a510418001c4c1e252410030002c0e15400c0348030314070030500101106610b0340e803c08200c010703100041203d802c41607101002c00010b002001580d01a500c0b07511000f8444442c000c0002801180150110022400340d0074480540c80e44c00c03a0000000080c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736224829 1250 736223579 736223591
    0x31b02031b0607050607050a08071409121005090c030c0d020f062d1b150a051b0c030a0e01090e010306090807021906080903040b031f050a080318180a 66
    0x10020740701c0e00410f14003030003602882e0100075280364401c00030721003d4440d0311102c80755100c08a0481d03160140952940c10148100105181440c100c0141c101401c140401c403100e6001c1c20030a982039031010f44e02e00295501520100c6d402c1c1c80c0a0041d00303483c81040e101040d00c00307401c1d00054240e15060700454001c0f500065880c07150b50404003204034021000c64080305005c200158050f140d80b10b0300034054040c0d4240300585003d03001003200880b8a00441134507900e900c0e83c1083c08005e0070050803003501c5100318956404031441e00c801404140710402e01440d02e0f0424000007406107808510902e04001200f002440400208030155065a803c03400c0000c0641151400c000644103402020b58443c400319140310100c1c8040c004001030301c49983d150821900d07459a0a80d07240a02c2c02101c14641081c80020a81040058203020b901c1e005910340620651790070100c1c5480c4140d4100c04002e8200250b013016842e070700d001e40100480140c91030007401300402c200540c240c4004c0c00d6035401d151501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736226079 1250 736224829 736224883
    0xd0203040b0708090d20060901172806030b090106081b19180e0d0c060b210f010c0e0a091a04020d0c17360613031b0203 53
    0x40f041e912030301009081201403d00600f07146e031600001c070310300300c46403918003801300f0301403e01005031080018107848290280c03180550365004400300501403101115030350002c0341004581c1c1c2c0700500b00f03041d64600003141411340c02d01000f0004000d0448003241e040280403c4119000681d9400e030449401c03403000d41410030740003e102048601d80f44080081046004a4070f85c0d00610035801c032600244040118a030342c2640181c40321180030f0800c0200f080003440b40040380403a0009411b115009020300212410400d1402401d60803040780d0450fa8040c0005888080003481407400302101801c3c80b45002c01c481c1c0020710618041d001c0c2298550326072200c0410340c080b50701000c034000070052040d51900d118a8080005104042c00c0300700003401000c8600403105650365550064100d480007900300041146511106002e0405c0e105d0f00003d0b20928a00700c06050016a000780c0244136001460b60782c2c2e05005088440c000a0081c00030b5200c030f40d47d80141c0d0b000521201c01c4140310340c4501808609 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736227329 1250 736226079 736226093
    0x3010b0c0114010603060e24040c0c05030d050624030103080f0903250611030906070314030108010615050c0705190308030c13120b0c03040804091d0f0d0203040b07 72
    0x5400c000d201d030b400d8600003081c10b94041c3c0040007a600b00742120794959079400c0e120042c0c0300ca010040c503c0865080402009424140c2204440155030b0900d0400d0710b075aa500c19145500035000d240c0320940da081880f1603850480582040741e0700500408003081d00e00c40b01c8c28814441844010000503000440c10400c500042c2680ca4110b8010107483e060304803242c504e54401c0340181680281911000041043da00800200418034131420045007052010001e025241e80080d40035014080c4542481045d403410340700440c040d00c598000800c4240c03402842ea01c0c00900030b25107000b81319040c0600a01d1a50011341d6008590742200ca88074064180a0f00c8240ca0b0b030380b03400140c0924000000c0107041c168040c001c0c60403281c80c4042504103580c0d505a0450100040e000605201d0a03101041c040c08050001d140c100f805141e09501c0c0a99031680d500c1121f124040103451458a01b42d020a202801c0c800400007041c2c1801a040082a0000017501ca114034014980a2007002c40c1c550284881c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736228579 1250 736227329 736227341
    0x60f03150305030c070312020f07050d02040209190302040506011103090103051b0d020909070c1203020a050f031e0609130320070609080d091206020702131109040e0703030503010b0c01 81
    0x444156551050850801c2d03448003031a0001f80c400607020041c082c0198400100e002d04082014080d100950400b0200a5806000700090782d125400384001c50303055444017210000c420340121600795a0b0700e1071051005850300100841d0503c400710740b00203c03500001c000c5403e400030074640003d15680c3c001444a0451452104081144006c2001e00c1184003d0b402403d000400b100c0b0079684d99038030070040354800394202e0002d02c60b083c88020805003d029401a2103070345001c3c100030f4185807841e60200101c0d0012500e154410f10704201e40e03c01000010074240e0090b5043d44c4807041803820360b00c01101010410b500404101c0344558010343e141c5c56540031075082c50750b0020b5030b0381d80f5075034480108480c22900a00c55180103414174401e43c18004c951540c00c6413200c0f001c0402c04038183e03d40c0d5009400c0071005a811007012801d0540c000c802e07100e444441c0403180f142c1751b21103002c2400c1c0802c45025084151641d4401001880403039041010f603811641c07140c0045a841c0840c2d29100d02410f1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736229829 1250 736228579 736228583
    0x515040c090806070f091202012705032a0d05210f0304060c1e090b07110a0b0a09080705030307112805040515100e0604051309050115060f031503 64
    0x900000d0281140c0d00540400c17100c50030703075a201034445d200d0300d00d41c00380b1240040007801b05082000701e60f08080425010028151101408620301c1d9480c0046403d003201014107141400142079020200c203081c0401ca06240420b598017009201d15036107095403284081c2000b0000b8040d0040140d164881c4000c81b0304685502002c25142c0c02e01340f41c41d0000c0c00846c80e1a50215040310b201d1891240d966001c00c40c00202507603100ea100c2d150045042050303221030020342e0b90001c0301c403803800d10740c550301b01110041003001c41643da84d149840008000100caa0442c40060700144030411050380e00100343c0d13500a402241d0307812040085000600e100c1c2070301c044000304144800c4003400d80020307080c250301100d40a807001d0040e81c0c2c0d0f403040c1c25035120007030898070351007010005441c401921a0100140f040c2000d0b00e40391800c1c0e00c41c000a64503403002c01160b1109a250703030003402017250a006254103008090001c0d000c2d00e040420107403120000c054468101680c500b81444221041442100199 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736231079 1250 736229829 736229833
    0x130c06050c19050a061431080a020d1107060206370507020c181305010f0e0321090a24380a03020909120406020d03050702010515040c0908 61
    0x507035450309a885045403513080d580949090100700d00801d0301d90f2070510440c29100005480f40303245030b00c1403030107a405001d0240700000042e81400114039100400f400c4000b5001040c80141c4108010250400c100100295402c1b006082048980009078079422400303003903071403080c0b000d07080305100441ca90031003040701c92082407800b1114000b56441503000741903650942d0588a21503043c402070030528400b0440311034985c000204152042100c4002451098001050004040c6040e0094136400d24825240340c00000d40030109402030314580e1200500401e0101c007500e07001395180d03242e00c900d400c0606000705150b11031241a141c0c083c1040c6039000e0040400464510030a140070f800c8130740501d04a54402c2c5403c01010303080b1480050b416140091804401c24215070038080110130140c0700000074400c00e900d103984044214090000340110340c0c01800f170b04c00c42281c01402c0e200094544401d592401d0140642c1514031403804420380c1e0300b1390300441c8500096000721208501031b0310494841c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736232329 1250 736231079 736231123
    0xb04091d0a08120109020f0307121506090f080610050d03021609050703050a050411040209130c020a0308070f080c070f1203050105040f05011d1f030317130c06050c 72
    0xc690310252074141c48070000a910f681c3c0321903451049228182000c403d100341440010b2020303110708140185000580e402042c0c9103031050009081c140c0a40105e0003140ca040b0b03041c0b02241d498500d0500030710b9114020907103800c0000c1151014103003400764a0241e90150251410315000300010349400c080f0762850038281d82e940c046140201070070317031300103000a081001040c078020381c50081500587d000210300c0c0c03045001d0380c1000001c0d4032055040c0d42040270000305d0341e071010046c171500c2001034660f0054000a16185401400198001c0c190380034050f11899800d41305174000c00c0c80364045003595045a40d00c203c2d06102d00e044815220040010105004000301980d154124034101c2d4400e4800344500b403101c00c01401694003d0003000c500500341e0798080c540d0940000c55541000198031503608040c1861300711028048190401e0b80817400c0155080c1c5842107104400c2d510081010008000c84000d95036080c035800710b880b1b05002c1200100d49001451400c4c4195070440080050743da0348 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736233579 1250 736232329 736232333
    0x2007090c0e0d03080c1b0a0602091002060906060108040c030605150a060e1e040608030c011505010903021f1e020a060c050f1914032403070b04091d0a 66
    0x340400308009000108020001c80386410401924516154140ca4007145541d0301801d030400c43c0c0024103051092031020003c0031071080140704100500e80601005640d4031107072814050503525480d039500c115800101003108a00001c2010b0b03800820903c0d00342803503240c034109215010080d41000d44104c0c60f0000f444003440f00b8480400345c40ea02030b01d0b480c0d1720665444040d18441005160543c0140111a03003130010210b2220109000600801c009516500c0751240e61460700b24a880091a1f0b644421050a030703220f4115103030023000f007403800d0906a4251341c080f519040030031006240c0c084003000c6440380c1034001e1442c841241c0520a039503c030440001d070025621400440107642c1c60380762170640459140304400320303168030078091044c1c4d00c3e01c44ca0081004403240802210400c002081003200c550450500040d40a50440b40324803402018144c0c20740311200120307186078429400301400b00401000c00701981c0c200c5e64421030001c1c0420006e1628107040c01c500d02c00c1c00e00740c01125150340c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736234829 1250 736233579 736233581
    0xb0403081f0e100602121b0a060c09032d060e0a0204051e01150509011214010605190e090a020a020109020a031a0a05090a0807030203090a0906060f0c0b07200709 71
    0x44201802008202001d84e42c0340d00b42d031103142111220504c20010403a5002241103020501a000e4000c1e08441c1a100309486900880f0b8820500100240310400d0400030300100341e01042c104a000582c004200010010140c05003c4044006040d5070b01c0300115005088280100080340760040c0050000d842c03c00c0110550b24403038604a01e40300c04140010400c401c00e035400c06070790011034980310b140140d00700055564812140b41001010b44900585d910440040313075145c024402a115540c44c0c4114100180c48044001f0300c0d02c1c100300c04c0014041c015550303107480d01d4001c0004c9000607521500d0140490150802100c003a412910f800f4001040200c96860090761110f4501c1c80100c68035049210f100361402680d0700e6006521003401e0f8000f0440b01d9008000040c824012603203086101c0022810305515984080c4500307903100010405513410140c20b00742d1103041d14116203440c1d026922402020009130840e02005a81c092650062007100103500f41007042c881180e020a5030b1341a120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736236079 1250 736234829 736234831
    0x1c08060f241e041202060f04150c02132c0c09150301180f15020415030b0102120a1b060b1203090a0f030201020a03080901020f0706050912070b0403081f0e 68
    0x226440b07910750980a400d0041030203441c1500d81d404041e409916a82c5c00704081074100c5801450601020040007030180e5001c010f040c7c42850030f803156010f21040c1d0042110360314259504003c043c2c02d14074001e00322480707150480107052001d540c0f260a0b400b4035950514041416041d1074201103010700340014078103802043d400700141140244003204203089000c040c0c6caa01480107020420350650302002035001c4c3c5c2c0e035280382034802c1c00c01414507580f9407440411031941000070000c66592054104503582c148000304680040c1d084042ca080c40c119401090246035401c111145034501d0400c0382040b10039000034195041c01000d2011207400c01154640320b0340034030030647c41224080c10000720801c0c90b003c684201e1350142c014155940190f2010784000310000d08031002e0303540c01c01140811034045006423503014080c4200203541d02d003105100b4601021080142d8100c0c40900480780000d0050140c0e80d0b0155040c500400a500c2d042c00003c1c0882e1044030603003940074280000b10f59080500111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736237329 1250 736236079 736236097
    0x2c0d120e010903120608010b01050a08251e05040f030204020d02070203060f0a0b03010b010509120c0a1508060303190c0f0c030f110405071b020a03231c08060f24 71
    0x1000511b58035030300203088450082015001c500f050000c0316140740108012544103c0c0140c1502c10454040f04101d2910340e440f90200100d1907407005070000300d03000d02d40c400071154507050080c6410700f4070344036407188951880024415600001c0080e0141c00340e805035444aa805003c641c00c42c1810f4a0b0f202d90f6000880c1e402c50303058a004003900803807a0502800014690684890303141c500c01d0750a1086401c10090b0310741c1c207407041c00c003580d503c0e03141d00e9040b4000b4480380c1180704660070001c400038014040500380074171079807003444400410a032402041c0080c084600300074031030420034904010f20300013258000e020f11524003c0041407050140519600b680b08440304d0148036041e000b0001122800d451501c0051102e002c00842c40756503042216600e80002d2401c0040c99481d558103101d4100c81d8086001c00c03003604940003070130340c0410201a801c0d450305101e00c00650084c1004104240041500f032041c40c0145640c541c0c3e480340003140c821901406074801c1410f03c200c00b078078400c4e8425511 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736238579 1250 736237329 736237331
    0x130236101d010609030b1302030f0f160f050d0c080109030507020f011b020405060609060d020a02070803070302060a021309090b010816050612090f0a062c0d120e01090312 75
    0x348085210282034603050700c3d0142c840800d41419a1281c11004800a101aa007100c012000b00003580d010468072482516203001840000407500a803130401d04000e040f40e2400040450500c042101c040c4490140c85058030010052455800c10804003202e5500c500c2a551821000600b407551090040c5100c42c0241d032182e017118441c3c801154506540e84040680c7d010300007010006207802d07040f0710741007400203003a42e04009140c80096090b43c40a003c0c0740c044c0b0f50014a90032627603014003416005041c070102450802102e03807400f944517003008212103407496002904070a094454401a000b402c0740c814200f18022041c982003d200b0380038001c08016100b11604211b85042ca2403058082e910080d03c15400c01c465100380c0601c0c00350141c00d00340c0b0f6000c1c1202c224909001000000807040c05a1008030302580d50105072041000f8071611041e49103401584896080c100260b14922031480d407800c83e030b0500403010440010040034103040260750902405105142e4403105800c1c1e803240100c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736239829 1250 736238579 736238609
    0x31b0c0901150801060809100f061d0603010e01060b0d0207030207030b0a021e0331080c060a0b0402090a03030e031c090503010b03071a030406020f071a13023610 71
    0x4070540d50381b80101c800c00740c04d601ca1075000200e05402d0300700658540305108040303030043d11200380c007202da00030502c0301c1e910341c484400300891841d090040b00031090850303000700072203420312002a0346880b407142c52404191300041c1d0881018800c1085030300440d08070018044e10305211a600d80a54820036000c400c6800480480d07220300f103800100c030701030000d40000c551009400407448503003501c10509071b07481c0000c081e0004041550b64000740000d261940190401d4602800c116048680a2201038021441840180c0490311075031075103000d5940605082c912800c00000083c500aa164a0110429840b8030140302c034603004602030381900c204600a202048003d412315a44030300900c81c4e564a4000d21041520b440d551000a6030002e00840000d490017610389034000e03040e401110b044849014800d50900031600c9444900e81000b002c0c443c00000c0c00e01c0e500050580640065020010001c142120810b1106031940c030907603010480300d680c190324058944d5140f41d0a1842a54a8510141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736241079 1250 736239829 736239839
    0x1050703050c0405010309031b05010204050a09140f1909031107121a10120b1b072d0519030e03030316030b04020d09060f1a03031b0c0901150801 64
    0x10241c5031150000c0d4403200d04181c68200114041d1100d81010380502821880000303803660350300d604010717840c0558005695180b801041c4003140c0030703d5000741c1c05c6510f0f1080f05030100902c146400d030070607042e40000c41140c850382c800d44807182e180241075808500e4040c7d1081003580001c0b0102e58a01401f09130343d02c4669a00c40c41210090340600141204444a0b5043c044441440c481d80c1140403520f4008000343c80b4680151640110542070711662000000c001d40d103c0c0c01945204880110904541003500950741c00d500c0b100055401079a1000950102640c1200c01c1484030304140c0100c00c8407168000138223009035a542c442030a40000e1022450301120f4200041241e000780071000d516452210550703c100d008150480f11264002e4080240d1915041a402402c56060143c0000a840b00c10b148a60040b186009410911128a07034405401560b000c802d41d049100c2c425061442411000f480300e080c0799001c15900c0d0f10200d40c20011404a203912040801c0e1202501c1d4101140d80350 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736242329 1250 736241079 736241081
    0x41b050607170a02011503052a010c12030b0a0b040906060809060a050c04090c03020a031b020a170f1b10060f03081b011b1b08220f1701050703 63
    0x810180004200018260026680c50010f03c0b030000306200000320101400c0e003614628003160b000b43e80940c021005038040c4148003225207040b200030b1318503e602000800020301003115042007d00f06907407500c0b0400c3c00d02d010350041e00010350014150844a600c0703482c0c0402e983c101d4000c0340d12845c501100491214010f110792400313803161400401e078a9903081420005420005e10502120009010000c2c50f81c1c82400b82041d00e0307015031409600c0d0000e03001c00404030340c0038042003000c035a00ca54042540b40c0e008a1402da81c1c41d0005105150f01501426141d694403501c00901c0e60a940050a09081942c80e175041c2041042a0241d1740074511500c040703020794000f8007a00c4002d902219013000040c141c01d0041c1450301d001035110804951908041e421941c005000c1e1000303045c00c0c8501c0f04503540c040e100d5030440c03000d64034101d0700400644406015000d6800039411200740c102d200500800c0043d1004000c1c61174440e038480349900d5502d00600c00440310205c035500e6080078080ba03a80c9010b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736243579 1250 736242329 736242337
    0x3010b1206030601121421030a05100b03070e15070302060609010b0301030503090909100906061404060f090908120a06061103070b160509030a0b040201020f0d0c020d02040b0306041b0506 82
    0x800b10100d6a03817892510342d81c514071480c0c00750350b05c0c5200b182100301110310f106c0d4400c00c092a20121035030310391070800c0810341590801440714050803a400300500564840400f582d800007c5440c20745a881d01c2d8401054024504007045a0100b0000c81c1407801c0560028145220340b6069584010590f6a5640322076a804280070041c200c0d00b0034009a20a41015004c85510030140411121030034008055042140c20988080e01d44541360542071041d0160940038050108042c4c5041007001c2c50030071480320080300341c0644515952a00608030601103030006a800c06944140b0101d01820059283e000a2a4074800d59021411103040b0300d0f2568804016109443e402210f0030040e0756801c03840c095860700810340d41e001d000041c004258a40c5040041e242140c6c0700b5048001a42001d0002a2038041082000c1c5040d60001c0c40c60340100340d0001e0001481030b41508c152903c00d12510000d00070344060301c1415010300c80c1008010601014100b00c9e034000440c426000306050311a802e205062213 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736244829 1250 736243579 736243589
    0x1505150f030a02160605060a120f020409081c0c02160602030a2d0512060306070c17120c0702041a01050906030903130303020a060b0406051008071403010b1206030601 73
    0x2052001a9484111a00656001c9100400103103040d202c2c510b003c1100324040426034a00c2c1da6a81005541c0c00c04000f0003018040180368802520300781d0340c6100c40f0442c1030310000e0050752660360b00340070803030303107805031107803c24441d00b40b28207440e241c0864030092403a5280c410051080700186290059968183c01c240d845c15400b41d0316000b5107204c199404a68510405905006401d02c0c002e1031031240387c0301021070302c50345d00d81d5501c40003647c00c081081005421f1501c039800c1601482806500488040e41869118078070300542003544000c0c032030b64015014444085041001045018600c410013040d04510896040000c1c1541c0600c118a18a6202002c1d0101e4010032410605240ca0005180c3c042d80381011203250a82040303035000c81d03000030b0384110096400311521030104001400b40d1613a00c4030a0300c007086480d01d0301001409054100364007030300b84002c0c2408100903a10802000000ca4485041d031540c81d6550f0801410683c440d505052005501901094040c6008111581258 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736246079 1250 736244829 736244869
    0x4120306120818030c10020106061805030d0f1e0c14120409021612030203060a090504050705150d09150c110a032604061d0c0108070813151505 63
    0x180b551410795203001d2040d020b0300d60500c55142018141c0d40c1c0d01b0a140d00945081d800420803a1404071702909405440300005100c0c100f80c04103112644001070002165036881c50042c11450311140c1c2503d5180c80061044d04200015134030022240c1c0201041078010310404a002034044180c1c585915420700b04946001824104010003103000c1a801821051007944145080e041541e038500e8429549001c0e0440482c3d00407041082d1403808a104200070700040200340301500d05603580310340303660f69409000c0c0304401e18403c00b03244004440030385483e004021010006c0c080f060902129100c54282a042c000c0e00f060300e002d0040344030702742487c0310556000c024041066103a0301aa0001805135a500302a650541d1210042d8030600050340581d004400001d80c2d00618104010590421a102c400e141d0000e03c06002d1640d0040815902040d9890100407588030704221014030840403001404948502d52030000000b40d5900100c42520300780011102c00e40d56000744042001100140e01181d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736247329 1250 736246079 736246087
    0x60b0a11030c1b0105120915090f0a0611040302100206150402040509040b0711460f11060a030e0d0201050c03070c05070b031e07080c04170a0b041203061208 69
    0x21001840c1a00c43c42e001414080c1c00e01e0111010038002a008658010031540800001c4502d995030342c6865401c1343e00080900f96000081d8000359560402400082000340d607400741e09240b201080941e00030755070003001080c00d100078640007035035850141c0e001d2100524060b020255850980708a80403030341c0c0988944060703070b00d40c0c499120301c11005240340240a00d80c1240380ca201c1c424090007082611070001c5c00e049000304641c10203940203441d087c4130000307190020b0864881030107080220a651001c10307220039400c946084c0c02c580350f5007181c8681140d0081186c0240941640021445814400450701000e40b400e508a003a12801d9480c0b00d02e40d64100300ac034042c1d9100319031403041c1501030411514407030f96506e00100550b01c2261181680402c16020300440810750101d03d4100d1510b20305000c49007081074026400d4415441451000754440896a00d403c9051017203102a94101400006618090030012010b0484e18211000a403428102180907011040a41c4032640c20092150130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736248579 1250 736247329 736247353
    0x2010f0e15030903190c050d0807050d09110303040807140405010e010510021c0522060203090d11030615090a0204080606090703090c170f06220f06060b0a11030c 71
    0x4294005011203d5a01040112045020408400310a14600390380c403580745445a081103410300c0368000070741c2c04102c071000034010303050307170100aa4003504803400000031400d809242c210b24955508407200e8250002280000341c404c070104c5c800342101c10340041009185184010002240d40c00d014040031032500300b0040c411400c1c240c1840440344428012110071040d2006569405002501ca5000140d0002070724004400c0342e40b070b4044440c0b21a100e2030522400c0020103522402652803990065840a00c2c9205002c5800401040400301a0640780e4500308034004480c510236441c01c2e20b000d25210804209111240d108640884480c600900071686800c0100708031010058410805c2540301c592600104224114010007040500400c0040520940000d400c0041c40c0003e04855085541040220840018000440c2c0440030666084000f9841e00c5049000700c0000580201d1034424041101d08946000b05103c80c800d031100341c50385030302c00040c598074814400c2c0b00490b9008500c107511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736249829 1250 736248579 736248619
    0x30305070309030605010b0415020609070b1c0e06040218040f020d14030a02010b0a1a04090510080322091e090203100f0b090c0a050a0e0303070f03030902010f0e 71
    0x840c0d5031191801c0c5003201d903291034520540c1c10a0704942c000400004080100800b1444000e01664241c0064086490145901c60302c828492117030800451002881c81c04e056021450100420b880c02410029400c86006580e0f40c0c003400c45040340a000792030b603082c698090b0005910301c61503109514171180c103007039424000e490151050840b42010041701056180a0900242905004039400014403000721401c11000b4222036001c0d0aa00d410095001c0c40d04030000300311826180c07440d0300030495272075485014681c03c0031980007503641e000108082c0720078066400c11030040c01a1444404806841c1c86118088070a2020100c0e0110382a090720190082d198201110450000301610090b43c1900a000c0540f2084140e012045076a00c200080518182d40803a4014003810f4040d4280401100050024403d0f02d001406100503450142c00c503070f90410480b00300326440003544902008514028015110041c803c070b010581040511035410f1041c20004d0304810014101c40328809060b02140b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736251079 1250 736249829 736249837
    0x161b1421030f0a0c140604020f0a0510050c03090d0803010e0c0310050f0a091d0724110a1203050a0b12031b03040b180306011d041101020a050708060106020c06090a030305 75
    0x243c148008070702440c0c003144032240e46405886155000c1c0c42c0d03502d0035204014511404140407407190010710000c0c456070320341452864a04280d41410b540d100d01c8140d48903c1c5005204030154440d502e151000c00700154400a14100d41013010118107580f00e801284c3c8107400201d400d4080076610103000c005a2a08800104404102800d00700e41c5644070203021060742e20204801c00803184240710b40c02030910801c62070300109003050308000c600203030904440703161808001e140b0412074128015006180d0900c070400c500340e486a120301001b1906100038018000465900002c1441c2101850403410b0109000d00c28044000146190880009041c1c80d6404907503240405484203000214440205500821400d0380c4500d0007c84102400109480c16905800c010f404500c11000d011a820312544215049517010645109010b54000101e2802d0350202001e04a0710407030740002804a0040b403043d05079201603003a50700c0c0819120074046a885080000303074000c035042c0401c00c0400c3c07040002d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736252329 1250 736251079 736251097
    0x1e07050d080604240f0b04080303010611190b0f0a1b0311040512030c010b0d0b040f030302074b0b0604180b07020706080c161b1421030f 60
    0x1d18426136025401907820814200302c00007405080030300074050f0410f0010018a00d0740b030000c0c98941822400c58813400188200d005112803866468003120080c8000f049101a184064415240b603091401800e44160b4021041114000104549040b540501c5480803588400c9202c910441030341280108142c0b00d280300704a00c03c0c00085a9035543c03c07546202000018021a02c6404880806003162441e501d000d2049208011510004040c50082a80190014441e40401202c0d04055010384074203140100103401804107a291100f000c6040c0017240b8882c4501c500c1220991a80007201c9a182900c50b0100900d00c01c2100062101d15403d0b0f00c010b010703101282d003080c2080c00c038140c42c2c08054212a804c1801382040083c0b41e0401000001344190700e031100300c40c100002c208005105424051510503007801c2400140603a0829141ca03222400814548075555880c40860308076031480e207075200309503e42070016682c41107880c0113018400300740614580b007010306040040382d000c0c5c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736253579 1250 736252329 736252331
    0x120c04051f11190c0b030709031212050106030906060b0a122a08010303030c0915030c020a0206031504051302060a080403020c0307170105280c170c1e07050d080604 72
    0x3010000c07803018020409000b441e40024104140c0c940380500084d4155005140e810070188100140a030748140303100120303a0001c00240b0480c14042085074404001003e0496aa00306000082c0e40750b80360740180d07051070040404001e400d032207680b42c044a1141060746000190f41d10703805040904030794040b00c90107100c11403078191448442c112866005290481c01d0115003030400410a141e01170140811380c0409140810340f080c01c1003d49001c80c0c0d10346503050700f016504d0b07181d10740c018002c20040b2680781d0018050380e2070780b400c1ca10031103429042180b200d025a050401044100c02c5611581c18259401030100c0c1c1040803d00040b1307903c0328010003d404620030816200400d031814020400502015200c403030341c1c0c43ca02c2c3c00540c00d5403005400c0184103d102045c2c00c00201e00f00d80c0102e4095044000801c40c200410001c44040d08c0c80314516188161400034402c0720880c036001000d035400c6443c3e5204400c010507004070151f006895020f000c50700700c10f11b44420031384501d0445500c003800400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736254829 1250 736253579 736253597
    0xf1315030c0323060702060708071107082103010b07020d0c030f0b010311010507020306010303231204050105062b02010309150501080f07180b04060b030408120c04051f 74
    0x781c00c40621525030040e07821000200320540c0c41d000795803488a044441000a14107400c091000a41d00c50b4018085001c01c00148003080301d280c4182b0004178220303d80030881e00c0c95511040340340d0702c0d2200b03940c80c1010040790b101000321038a01d41e02940d040350700742c0700b405003040d0260f0240001d8910400c012901010324410100000d499100340400641c007410b0b5000e450742c19840e0031080c0070507540440b811f1200c144500e000507500001c03000d054030f13131500c0c0c9821903003000f1501c4148614480e200001500f00800c51503020304644000310301c601e000c0c2009000e2921140700b409407641c410400c0444001e118000d00721150010407548510f0f602c1032400041d02405034071032103108940c200209410984031001000b6a45041200e1a081c40d00340014000841c6015100040928010612004681c40e8000c0600c3ca41d601d9000000070030780300c40101e1ba84d15240c9401d0a03145d010202041060303043c40045600002520190703025180040c2419105824441e9444036400d0740440c400300b0092006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736256079 1250 736254829 736254833
    0x90c180b191706011805211605030d030209030709140601020c090c09192d091406090402040b150d0e030711120f01290f131503 56
    0x10224001000305084031521a0914220449000a414a0a070400c60864541e041450b66200199049102420300010f9a0701500c911003140403036a00440d8403d0103050291152000f9241041415099005a8519051078103103c22208002d02030309030994041042c9080d2140240e0092540d05030003000c8680907980e0f48070300002d0310100b050030000006508280612941c040003a0341c2d00da0f400312294000d906d4410356108440c0200349900b8441d01d611001505442e078000d0b078400241101d80030a00784101030000d50b03101c00c41c0380c0c0303581703400c070000c60340001008212403103209038074000f4445000701a1035a40821855807000341050381d02c00d41e510840c2e0855910041d2013a464282d95150360f44400301c01050344111084440b807540240c02c02c00c40d03140041d1020707041c122100b6003242d08005048100c0d420b90700c0c1c9080b0001001b8650300e0315115162000c0107280556240034188040780b0303103000e6842400381d12000e1625443d04a0b144101c6142d201306540c00078140e41c03c1501c0100782d401d0b43c030703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736257329 1250 736256079 736256117
    0x81612060b03061311090f0c0f160501092a030305030702012c07050d0809060c030d060e0412210e0f0a060501060810060f18090912111501090c 63
    0x9a0752206184d07a4880c281c010402c01c58211614040b04445441041c41d08001941e2003580040c103115000070005005030380786807984c0a54101c120280d1050895003c82d280c01c0c3d00038241480706a4040040c008014143c95904c0943c18408102802c0015514070b1a81c0603251a04007410520640d52110040103030442c691a02c0c1601030090b202c0603240844006205040c21800d1704464004c0c441501182e011420340e10171100ba0758020f4130303c960350315114cd004c241540111140c11003000d09150002503001c100c0615140502d0040300964a40307068144181c0e00c80e0b00b0b485140305030780100304003004c1c060350940c0300381c4e0b641100c070050f03441d21a4003004081c100200f1400031215035070b6400c018400564424110b56100345154044107a80d41429005020a00c10b02025410800101a900079111142c030345900142000d000c1484049802d1401072066140c1a80e10070019a0f181c580300407050b00003400c10a0029503400c18065a4207201041c005000c940c3c0c55030050014a060341711580c241 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736258579 1250 736257329 736257331
    0x2a0f080a0b1201051b040506090f0d0f2001051c0e390102030702030a2409050c0906060316050c010e030f0318030301050108130c090c0315081612060b0306 68
    0x14200002d1a4600300c0360b6161030405c104500225007005210030711894903020b00701c0310400c404850070400342850034001100c13000400002000f0f24074001605080216121500802c6000710711000030112003000119941e00440c0804020417050040f1108a6081503120110b05140242502c0c80ca4200d000c400100541251500c2e800c900c0c1501103504181007a01c81c120700040900c080d6140038440e800280c6c2c2d94000460141c00e90100e004007041c3e00024414508c07180300114001d12000030382c1c0c10003c1c0c4030b6540a541c40c0c01610318000041035464002c007140d10410551403640d02c1401000c0c4125100d0b00a8030a1071041d640e5a40c08481201007040503110f082401d0291655034640700705011380b401000b0301d80303041c0d5a10600052000d0780c3c00c034013203607440400079101c03070030340c040ca41000d02034010a54002c11016280900401d07200303506030421201d03e6040c40c03141002680c1d62591960b03484400c00c00852180030134106024625070000c1e1101d03400c0c09003038041507000144001a0034490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736259829 1250 736258579 736258609
    0x160501240608010812030f070207031a0106080a060803030c09040213140a0f0602030909131a1503060603120a090815011a0c06070302090409050a062a0f080a0b 70
    0x41003403040040650090031a4050486074001d4540828124864581804082c0c292480020640d00003101e80303100b002501c00a64000002c8034500390040c8146425483c203000e00800203030747d000024050402409441c0455215800070740c6540e442001d03040842e040305094544c410340030044030740e8428103014000b0180040400d1003601c0030340d20003002152246540031710811503080404102c0707150044142c45642d441a68240d020742e80d4541c1d03941c04a4444207009100b41004c00d40c0c03048a514041001e441800551b581244040b45d12042650310340c000c40d10b1660681c4510034644c0c0000750340300035201300440c5041843d056500c49040700c0c145190f4042a041c0d020b045001004011040c041c15101d0415141c281c614012012081075154040102002c09046e0001031180041c1c4450b03002c480d01c02d4210003a80c441002c203151100142c0802c2001c84803c0344151400c0c1c84160030015901d48040f43c688030340440600c889401d450005006062101c4559556440703941516605a4404461 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736261079 1250 736259829 736259891
    0x120b06040e040b06180c04060f0e030a1103010c1110110909070e0103050a02090d0b093d060506270603071823090405030c0109080a0908030a05160501 66
    0x215125052040398802221014004000c2d0024006c02002d25030480d03040d07804900e03010350301d0540c126081d41c0d11914039583c0368040c80781c402d580062129201d0b02c80e01009080f8028030501210100448079400d03545009501d0303401c042040d05185009510041c2c0f000c4c280440d503428080c2050004489000c102c0711107000c02d00d0307031407010115170340b520582e030b4096982c140442c241403145000c05c040107411a00107180c07140e0880840c0c4142c04c04c01c940c40d4204401c0b07401c2148040c24004101121b0940120b444100260180b0707015103c04034054030056940140a00d4105003914540701c290041c4903500a051808450401c49180c444200544c41501d40e505c030300d42601d03001c1000340003c030030300c2e800394041d0b60310281a203e1038070001c014040d99140894100215858900f083d41c1144904904a15998030307000d860400c2081c4035015168003210780e03c910390310340d0ba5901c2ea070b600c03841000803030306c0002c4080000c40000806e14000c40001430098000084160010142c40c80109242030301914407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736262329 1250 736261079 736261081
    0x207080307020601090204120b04051507020a0506160e1909090c0618150f17130b01170d0309030e1909060902070b0403201f0608030a120b06040e040b 66
    0x5901000f00d94010410340701c04615080c54070400d180701c110142c50040c096074528010406015042000d4021101d071b900c40d40a2a081054000e59030720040c110444050042c50b00045601d803d01660364131040c0d141c0c4a41088aa01d40c041062040d40c0c03400d40c2810b000344240100320000d1a00ca5162440e2140f07034100032050402c83d0140c815400045140017000d2076071400c0c0180e52620104a0301c41005040564900d5001c08056501d0308050340300120310b410b15400c21084103131b07411000c1d580500440d0290040d076202e69000e0604520805101d500c2d9002c2c85c41012218429806664458000e16100144800440000b00039011149000110200b501d00c1031109110512842004043d46001145003504613501c1e00201400200094240000b90120a00115111601f12181300010302625100700c140d610820103581649201d4070307180d1600d000800c131503400104903911008e890b11303140c0003103460311400005410751041d501d030029014003001a014400c1e01049005500c40c0103401d0f61 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736263579 1250 736262329 736262341
    0x50114070b1f09201e130302040e1c0c0305040e09010b190f0e1e07030f0b1206040204050907090903021c020a0807060e07030812091b01050a2102070803 67
    0x14084030b411a0100b64505102c000708210b088801391070400c03540d9259034869000b21503640310ba14401215013840b000000b24040c415002205103810b880c804c480800082c9820008659281024880440c201d440307a50518403030350085a40840551084c40d20a01d06600ca120107068004291020b4a5603034480702d4030780480c608206c1385c0c1040703000d20006620303180c07400c0103c002110b00c81c440d000341030300a04046440100e506841162650402184944a04040c04010001c2041701507001d00245001c894025078900900b000a04c01c1d5040020041c540b1180c00300001402d01624100c40da01c102580026840c501307004021f5001e0180d0080c01d000018488861580b1034148030324400c44d002408010001000d51341034401c0250402ea00003480580c81d60a54030702226134002400306a004960302080085030843d031407061b8001c0e020f4510720035146541d4405d200703c00c14110301083d018000794015900c1010b118860281104448942d11242001801264059001610920800000c002d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736264829 1250 736263579 736263631
    0x20408060f0105120c330a03050c070f030534031e05031f23041b08191b03020a110c0a0b0a052106010207060804020a050114070b 57
    0x1004000c144c50059805241880c001c1c0c80c1c030000080c00d40705e85440c1c1d0000c2e8110382d103000c0071040a0fa041e1000440c108042c403090b50707150083c42c81c1200003400c020000304140012400e80d000340390300544809500c4c56650381178401e038101e4803d8105100349039000d50003421100c1030f4032403800d0039a10083c4041c1524103005000d00c2151042848000c41c6501c00600540d0240032254425a41c0c94040c118070381c510b00203040c00c0c005034044900d140390741e101c000920b090a1103203003101604850800450041100d2030000f0668040c4600208201100141401178406440c00c2c02c0f0000c4c000004000310f01020650034004051300340382c0004d60102d401003400340c2000080002c01c1120004101c44854a000604034207014003554001030030204030b40e856103019034150340054100c45100b0100c0c120003880031540700300480e10b180c0103118210001860302d002d0144103000f290050061007920f810400150303000e4400000c00c3c00d40307003010020070000c41c542842040c0100720404d4018000140c1c00c0b0310403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736266079 1250 736264829 736264831
    0x1110114220b040209040c1805102103051605060109020a0807090b0304060221090115050409020f0402130b0a050306091e07030c0905030307050a0b01061103030c0f0706020408060f 79
    0x5030702611a80111002c03036415461107a100d6811200c2e100c0f13903078446c41c04603032101d80c40e0300c00020043c440f0907108910060b500890311500c1032203030f461861560303401480900c41c00140100b04500d24800b1401c0480d00c164010010413421f0500d840b801f00316036031807030301d0414264410109980d01154001c0d0455005608640010b10b500c0c10302891414050205d200340700140c4003d004030f40c0060310046104901800000c030f0840c07006010300381e25109035840d02819043e04150050310040b032000c24989054421600103a0300a020a4001d4002d1000d2000950203d9040c1245003285000040d9020b20300001384100340741981d44680305d040c45001d01850040140c039250003000d021801c07007885019004902d07071216062401080c3c0701e4440405440038409504100e8050100080c4201409000a4480f0800e0701c5031103d04126aa01c2900302c4981b0050002c54205420070008100f80c5c0660710054400c0c8036041d2030341303450074803c1c0d82c0d003000300c0e0f11540c481c3c003158022004000d0f07054043c100785 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736267329 1250 736266079 736266121
    0x180906030d021c1205090303100e190b0d0609240513020103020a0e1504030515090a08030405030d02070b0412110d2a05010605030706030606120203040201110114 71
    0x20500e01d00310760030180d1a00c1404030004001d040450200908601c214100700f01c01c0070030712082280e81410b008941d02c0ba8000c90351000b00c000380d903c00062410001c0c1d101807048603060101210208000c000b100a00701e05010740707a100c1604040040460614481c0000c0c6603c203031080c566603656100f82c038030950002020310359031918010420049481500e1801680d590918006940c2d0074082801d681d42c18042e0b42c0301c0c0d000400c00b544100900b00307030300040c02900e0040d4100e500c000d50301880041c0142048500134819080000000d00064894002c0c0da0003500c204203417400e14242c0c8111104a03042a0030503110b60080f0701c00c2c0801d00c00c406800e12900c00b95483d045070311b155950302c140d035a00300221400b02048086901810140c10200c0001004604d0f840c110340d030111503091650203007407903010f103038420b020b0324800288140c024428207080b5100341d21a8840c0f00c0c03d0541460080d00000c209170306200c02e43d049804011400e1040440c00740019004100b182042651202c0c10005071000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736268579 1250 736267329 736267333
    0x8070f201501081e0604030c1403071515090603081210120c030b011d010312110a1a071107060f110a0311280b06031c0801031b15030506041118090603 66
    0x60102007540140c40b4511143c20270b41d680d00c0003041c00c0b40729142d407040300c1000d4000b401007540e41414a00b5900218040c0c0000811038007110b481c0c5031000100c55040c40014040701c810400d00a010601042d6150f10241c04082c0c407410613901da040c140703a0440d0039011600810710850034400c01c84441441400343c40024048103c101031405000a2000e040c00302801801f440140030340f5207407142006164645c030380700c1a00c003030703035118500b9480550a079004800c2c40b00340c540c0000c4003144100c06a010620180d4014080c0c145000015902d004d614480c0c00304000e0700000500c1c4400c1c0401c000d4951038400d5130340c2c1400c925600e04d29401e0880c162a120885c41040e001d0349271503e18000f18036806600000480d596450b803000091421260401407401444211001400a45c05c0f00003241200e00a411081b140f200104141c0056007050240d8019161900c920300a1140b01e0b601c03080e8054009880000c000c09040c8290505410464443d21400c0c0d91400c041308600301100c10580250781030300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736269829 1250 736268579 736268581
    0x81e0d0306120f02040b041401050a0905060d060203060109053303100303050c011503120e010201020304020d1b1a0c120403050303010b0708040b160308070f201501081e06 75
    0x2e0103402c420074200050103a141e1000c0c030b08155640c0381d21640c001600100100503011480c0504079802509100c0c1ca131080308440750002e00c602040c010389204d03a00c0144844900c5000b0307074030309009400c0645a18108100c0100114a82d00e030040030f040003001150030941c2c46221404210304000424030901480101402030044855204040406580e85400c0403611400c1d1015014010024118003441700200b5201c0003041c0680107501c840510b10654800a4840702d0318016403c0c2c1c44144da0007034001170089040c1011404020052510008440010400356030301c1150210501100240841400002802c0c0400c40820065080c02120000700c1c1c600381441c1d910341e29202c0c00144610506104000341d00c000704803000013150044d00d41c0b03000d096164000b1203a010101c00342c1280440c003180488010401c01802410700e015802d9260b51110014801002120010b0211200000c0c0750702c200e1340b00140035034264130010b01819041005000c00e580800e00c1c8646004000761030b00007130300150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736271079 1250 736269829 736269839
    0xc0c03050a03021b070914091f0c020f060a0f0b27092a150c07031202240402090601080403080105010507080d02070c0e061903060f06081e0d0306 64
    0x4060301d0001501d4240182c4580581c0d54510711880d84485034030150040150226004e00c041d488507080346450390040d041c03645e60014940ea2240c2d0314092103017104030305035020004072640e0400030361a000782c810f4900e002441400b162a0401c1901c4c5400c50341d89074490085401c544c0d10544114040464800070710180d00c96090600b400b500c18504420816000051142c0e04200441c0020204445190b52016121201100011503548803140700d02c90880b480d154a81c02c44066913055024074000d40003d62469907030b0349000a5010b1b0603820742c0190074003041c6110300803208856214000b5404002c070f1410348104a00301000070403880c14400e080c810f10000c280c0c4900000e042d1182800d000d69035601a05120b6101c1c044d1810940c0c0d403500014865040000c3c0d01c2d80d1404079145002640c405031544401c0003a0000c40b02c55504076002d90303000410110b0f41540041000d01c0c48603100043c159104c0112600f04882891000d00b100103e00b02d449040c00d041041401800310f030b01e02003000a00346 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736272329 1250 736271079 736271087
    0xa11150609070c11060c0a02030601080a060f0207050309010c020325030c150903030f140309010e0d020f0d030b0a0f060504150206011a070309170709060e04050c010c11041409010c0c03 81
    0x80c0072801540e022481b10201c44081000c03540007038004088440c690307594540d1a65800303061000300c80b01402c005050384905254000d413503d165200010b181405440001140c00392000c1c0301c00e03603061107070132a030005403400c00038600c0c010b81483c81c03810881d5007103003040981c1010310b510007101840700c43c1d110140700b6404000042660b5041c80d2810320105001012511600c642c8000d003811440082480012001544200007110300716007540e2510340100e5042c1e03214030700001035458a820400540300010b100c2e6010344105a80100601522130311070381e0300c600d40c003030341d401040c0414070019040c009280c5035401d04036105580c0c0300401c0e007581041b441d0b00b01500d0b6143c2402206501062a404060140b04900040c00116103105c1c900030305100010b1341c81c41d0701d11880c404180740210104204208082091180d500440280031007100c4000440c1e02d00d644c0101590708540b041003050882d07485004450800314607001c981a941840d14a250031507a050688100340130001001800103500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736273579 1250 736272329 736272353
    0xd0b0f060906042702030a0e0f060c040b0c0f0706020102030f0f09102c061e161808032b02120105060a031508100c080114060a11150609070c 62
    0x5854015a41c041403030380c48512100313090494501d150000c01080000402035101403140c103640b50480e441c0080c5142c0f07144d141c4c4070a440c8000d8034032080109101100c0031900508004d541c840c00c9900c01007407028040c0c02c02d90180c0203100140d4000052285041d521421075800c070754411050366050034800031640d80e410807210f440f009580c07a540310031003400e0303400b28144c1650003112806000e80d107200107070ba0f19071800311071a88642035100310600031100c2400e0703130758800c0c039090800440105640c50152a05000d42002d080706606001d00030404080500140c0940039102c10000c011140040c000310041d4001500708140920500c00c0c1c003510307101c0411480c11203005940c0c0ca41c0c0c0b02c145085c11000b4200c04002c0c000303008544200010749000000300da000e090b040743c504008114108900301d540b100207218452030b1480b1000c1610742880c10300b000703200240c0242840e220107104991700c42d08003191a88501d00c0a100c0c4400c0201e00d0400000030f980c000014540321121200650300c199905034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736274829 1250 736273579 736273589
    0x31b0504060806010c02180901051503030d09140a030504090605010509090f07030e0313030605151005030a0f110702040c0212070b0c071a07031b0903061a060d0b0f06090604 76
    0x8201c0002c00e8a6901072015004117a801070720000c1140460b02c3d82c2075403407a054584081d250729200000d0362089900300120040400240510f00c4d00c8120101d0b0009481002c1080c0c034044200c50224140b40307010070216544501c2030300c42c0c544640c54a004d160880d501607120742d0510404000348000d0769281034050b540302044c0c1d41101c940e6200d00008a000f4030550307601481c1407000180e9501408600381032941140d20811051190355182c1c00c07440e000c101d84000c4140c1000103010955800d50207180034543c0109803c100040803081130702c821090b94051403181d0039000d000164142542054000d69074884428001099013085580002c40b4034401c400c4090704c0d54401c800443c0348c0b051300004558034542c000c00c418a220220f000d030441420010742c0c1c00c1c0d011034541026000804103090400e5007606480e104c071000649140c9451000d89280040c08450501c03090000009540e03034805090707c81441e150005248081030300344800e003c002182184510000e0080c0103195446208682c1550b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736276079 1250 736274829 736274837
    0x314030c030708130c080c1309110d060b06030f180106150e03010914064003031b05030105010908060c04050d050f01020a031505091605031b0403050d031b050406 71
    0x15941e04000e2444403600c0340001c1c2a2401030703600180085002850359100b00c000c488c0c5011a1035500845422244d8a0800815132038803a1a002c4e15440c03c0e9040e4011a4096000840c003040c20300c001900b958400c0394070b100160006020300480d0149001449070702a0001c000b08140b6046c6030164036010350010092041054401600034180ca082d0011984558031114200c9000c1454802544072041160b60507442500d442c80c0c20203011100c10a100c2c3c0f900711400940802d1281c0d4808100440140001d03424151111420321325564442034028008541d41e40e00b54a9505213400107200251a81c002440c0d80d10450502013401d444404131821102c003201c1c0a11120032600d032450434050300b84580e5425510200f002c030509509500070039000c0300400c03140c0040e1070720380c020801d07482c900703856070b01c4827120202800c0a0b03140180c00442c0c100b81c500a048001030411028400b00354000d4004440d250003102d00584016018054001240c0c00c291109040c3c6084000040560046100d100208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736277329 1250 736276079 736276081
    0x1a030601120b03160e15030a080301090507033213031407050f030d020403120c08030a0504110d0302010b13050705270a030303020a0e01090513110408010e0a0314030c030708 76
    0x155000c101c010030444c0d40e030510190311075031202030104002c411208070304541102c2c140d1080d5441c010401070801703544403102c0c604503400d02400b00c00a2900426060074503544141040d20305c20b0002881c1500b100c6010b04203114200007004140b12400500390001c0c01c04038203490390000313401c0b40840003590380c45101da903101c41032400c000b0308d8500528061001c0c0d010001d080d20351a0a80c0e0001d0083ea8029840144503501c050002c031a02035902c0c4c070240c0031003418004a220b4102d04e0700078941083c011000045103408480005440c82c0c20140100c0161795110303510411401c043d02c4640316106000c0082007240b8009201904a100311010240d003864800a440c4000b0010306074203034469000307070011900ca80c980c035001d80207500c401d9000d0041f4607035088171800c640c4140314501c11b6a034082e0038820120300c0903a142d8080d064084030380010807000d20001c901c0c020240300301d070310800808000f04605041800c000e05150300600c44444e095008100300f1440b054000700b2030390449640d25004103e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736278579 1250 736277329 736277351
    0x503071404150f080f0d0e0d0f08030718090204030201020a0311030d0c081e01050f1021140130390806011503020705031606061a03060112 61
    0x200340102c182807598920b80b0b0081024881c41c2101d20a4607215001c907000c00a070700c001d1690341c0c00399480c408002401c2c00710025540c20302011034140c9a1081c2e41c560040c007020382c1c030918603400031200c440c0000da03290310114019001c00352070002016004421450a0700703640000351030314942000607041c0114407084041c44401002211140c06540741c2c00c000c4204a14402051044251040d0084c03081000090400c00761842e03156040300e42c0188602c039881000c43c03d00841e486414440b1091051507018035458840d401c2c410313210814050800211800540205100060107820480200348044203400120b010769a4030402c031181c180c2c58191640c3d4078600501007403000320405020321166103000f88415000036001c025023440805940c0040c3d19000400c1d901d20b001d2260302501c04140700c080307000c90300a84c01442454015001e61f8076100481c400d8500d011a9030000f00c4440c2c0d910101045201c030b2840038500d040351000d42851443c100940000c000c450a0104001025501ea1882034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736279829 1250 736278579 736278581
    0x309050a0615080f0102030a0e0f150c0409050f0103031701140906040605120d08010510080115050c1f1503020f040b01020102270423010e0903070c03200a0503071404 73
    0x2004010f080308a030740183c0c079401401d020390001e80d002c0c4485401c004a0641320840802d88240800c80080100100c201091900e411017a0280116422000802012030020100d0007494030a03030364607003103480c25455848d0041a403103800141403242d40480c1c2c014000c6858065041065010403240800241c0313070390f0001001440349620251703000c01610321103900c04901048c032241000f8240c5603046980c0c0d032031060241e00a1003407810000070749a0310061020304000c0104c0f603401400b901d0032030304084588031140d00c0d1018060040c842e8900601e01051700b8190b501604c0c002480d0f41d000a440603195a0100c0c0c020601c01c441c0718402c50b10ba4401d040703964070075410388103070703d6203c44005020f0b25151950560008580e88481c010703400c060001c0001110a0050b10124140d0362014105a1902c0140740c5442d2024001c03606900082114401040c04640030b00061409812101414000a0008070140d0070409015004041c0c104040045070b501283c1c0c1001c446c0070702451903401c43d00c80000f034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 736281079 1250 736279829 736279871
    0xe04080d050103300c0609081b0604060510051e0d20030f0a110d030306030c0b271e04110706022508250501090303050709060309050a06 60
    0xc02a140000000600c03084d16501d08001d1440b04c0d00c200f00e030740350000c81c5003504100780c49080850310003110040050b5180d80608000c80c0907820785800d0030f070b02d582660080e8140500304d0f4402d511020038801400203510a442c0c12904140083c11218680400308002c0170a41d0210319407401100c0c1c20b50650f490742c1c103803a00a19442860000c903070100e140c0384010020400d0506029100f806103003440350000140b0107540680101c4040303101d4114000f0411490441c443c200e00301511000000001071440003510041e00e24110708940301c540807400c2d0207402c542a03000040800080880310b240d074850740c82c14404100f114804001d600c07000c60205014014401c10449021000901001400f2155025058248c101950192020700185030001c0441140c0070140120a040044c182010701c01080084002480c2c060790450300031a858850855240d5a02900800c3c1c50703400300100710343e20045500c00b9054a0804100d944055100d01d5901c888030030000344026500d4101942d0032441300c900c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 736282329 1250 736281079 736281097
    0x20c0c010e1324090b0a0308031e0103050607031a0d1202010216080d06081b240a0c110612010e130c0f03030825200d030b0307090203100e0408 63
    0xa003c0c400c40a03185401c60300c0c404014145a40d00c1c0c80c808201d15050740140e40c20100e009201844260464803a10101d900203440d4220740750000d103880452001940c8000d0081d07009501408052801c4140641690082428039810b08201e614003c0700340d6a00840c13040060300400440301c00d98011502b40e0091240d404110030310313107010030f500f8100400000140303034514591006004441c0d603a04d11558401c603180c440507480403d05505001400d0054641110080720f281c20001c003c0840c80d603c40591001a013103000800c0103d00c0b40c14083c011800304030301c060940700a0702e001a40c0f1504010301d1018001c43d04009544004100803040700601c1d0444244c2102d104828030359a0b9115001140403440201c02103103802002800100003917005d020703d0403103110b4400000b2260070040381e9444840030146880c00c11000c0f507076410003082114060400460310f0018240c00f0400400d0303d031400039400381c3d03001401001003040e1400101e81c9442100c4000c10b41c00b2007504d0383e00d4000410f004a9000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 736283579 1250 736282329 736282331
    0x16020f0418060606141c091218050307211103060f0108070509010b0d0c0c0b090a021c03020a02010f0c050102030c0d05071d0f0111010504030201050613020c0c010e13 73
    0x7001c507098589801103404148100810000603a503250142c2e5007400008070a468200184000d035144001d4403d022842d174091640066811440e9543c50208905841c05000040c00c90340745002c22600c4043d602c000d044c2c21001808240d2414455021030840b00384403626181f440300c03c00c01001014100041c0034507000b010380d41c1c5450b101a041402402c2480380d4100c0307115401c0001080e052043d4039605840340e036000e40c0d2a000c03903114100f020740321090b82182003100b840032601c042a40d04006900a400c08000b80c2070f007840301e004001000e0400f508203184c0948864109000070780001e0341c0300d1b0b402d90a082034807040f00d50781c0068940c03010060000d40796500020402642c0600140244080003006a04120315147c10b8021901d00d00150400048151051403202c124644403008a6200e60b0500d40b00306181a104c0340182519401d59007100542e44601c14800c2615002d031010700052410700017141000a050356030b0359210078a0710301c0f80c14881d07070482034900c035100c81514446400c217900d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 736284829 1250 736283579 736283591
    0x180e06120309131e0c0203120903090915040c021f05190c020304060f020c0a1a25030905010813060b0f09150a12080906030c040f090b0405011a16020f04 67
    0x90450041e0590004c0d00e4848800300780700405400c054440c42c1c540c41602c1d40258180500c0d807103078034119030010304544400c0c407080c02081480da80b0b4007803451081c0c03800300c1000d9031140404184001d60b4084400f51040d90043c6d460f848000c410881c05e018102c940840106254403040ca40740310700080d141060988908002201032040c1d0004000d000301c0d0f10300d0b0340b440d0211410110807600d41d40c0396400568030040141003046141541c60080b1000840d5200c910f2034907103402203042c80b0080ca074940e0b140315030741031001006142e040100f46005190a00305880b080c68801854010985543c0d0010701d4540d03204281c0d096a2920507024440840240441c0c0072400c00c54040c4a0000040d0805881160f1041c40811107044607001c04036141d074403d00444c2811074080420510342c000801c684006402070100103071205c003001a001c01040740140020701402407005110640b98140c000c20306400c10704003035a154403148402c5900b03000c85140250300342400e48c400102002c80121a65074010f0a00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 736286079 1250 736284829 736284859
    0xc0f0105040b070f12030501080316050c10021b0603060102070e0408070c0905060916090608040f050303040b070e030127030306080105090c010206091513170f03010501180e06120309 80
    0x4145814090042022518803c5c40380012400e8890034000c000035034000740148010350500d1142c40960381c0c41741e0191007200c1b4000c80030900c54030010f142c080c01a0300c0440b035410401c00410380141d94580643e41145103141000c00030750303110403601c6440c1005040c00001014402000f0a40d4030095214014000055844a2420140c41d0558203240f08400503408205005d45080280805019170f445135803400785041401c2e00c8c08000100152484000e100080c00000d01c01c1c801540310701d1049007401018140290002c100c068580852800390785098020304002007051100342c1d80012000c0c07000d84010192500f01d019028542c40320460b50309120620482000205001090035000e82c00c403003195035180c1140ba9186404c024552044d581100401d2000301d400b01c1c2e00c01060f02445164190b13035201149000c16078441a0074510840780400180265070f0f0003500b25080c0d11a0030348800c0d0081c14107510200d1540c0103800184a03503070651060101c003106006403496810024000e6070910031607 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 736287329 1250 736286079 736286093
    0x403080901080a0c08061207380906040e070309051f1107020f120f0304031a0105010804031e030e030304060203041a0903223c080c0f0105040b07 64
    0x1400ca880c08181a040003401e0341406120322448010169904507040d20381c40d051040928540c1c441d4a2140507860b80490801103200852071020500c000d21102040075012402000030b0611050242d0841041100c140307035106c0f000d840035650f40e0705c0c12610b2615505415401482e07a12801006801a00148036900200501c440301c440703d4020309100f01080840e010440c0c0c0724808000b5884100d201100040b42084280c80c030250305030100316000c0604e50755400e8515082544219018440ca0070401d08100c01f10041c903004040c2800d103904c007800d141d50060001c0d510900c1803202840da050055030500c0c4280c1103c4109410002540d50700d003414201180658400c4606460010741c2450902000b041d15460301e103d140054050b6040c5480070314103442801240c0c1102c8101e001d080000700c2e540c01d600d600c00d154141a280c04404041c0d0401081000102e1450204c00c4041d1400040140b01c3d00841d10a480703050445001e410400070720b005944a0150303820100200700c020807504c0401c211 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 736288579 1250 736287329 736287337
    0x20a0606050409031407081608030910020304030f0e061611040b330f0a030b100f090b0309030f040f06020f06040f0b040c03080a030b0f18040f030311040308 69
    0x5010602005071036400380426500d03d600000c0c0000e1040c955a02508600c1014110740383c480c41d44507140030500d0b0f031208d46e41d00d17480c441691843d600100341701c41c4400030811511100596401582180313400d46018042084841032a024419142100199a0b54401c11545100f00360803d1461071030483c00e01d000c1c5a1b6980031058050ae20b02071601c441c4d480c00100794008101200c602e00c014405000d1154a0400d549007084408081880104108010b1102070100015180d40c0054014002410040d0710182c0520b10018004400000f40c8081e42c000030741020f0300c000c1044075a0b82c1d119905114a03603c1201d8400111460128011130045001c9801c401141e50aa00b183c140d0703080705040301d80b1441d05a40c0200030400c03081d40003001070310509406a1090041200d0007103255662110b2205a1110300550002030b92001d010304180380440d050062500284e404101207807186200e5442600d0152019110b00ca0f9030782c1c0d10b000c0522941081e45007001d07202d14141c9031070366460700d0241500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 736289829 1250 736288579 736288583
    0x270b0c01020d051302090106140405031903021e0601090902151329031b1210090609050f04020105090a09060609061106100b0f0f0f180105070b0a051510020a 69
    0x205010220b181340300e10b80e024400b120340041c09240c0c00d03440c00c8420303644149252403050350717880309100c001210b41d018400c00e03240444500b000404c41180785802401c1c841d0703000c903440101e48074450138480790309d0010708ad6064901e21403000501c403c1a00010300c4195189031030303c0b034000c070004a03102c40c44221281c0d02d0848000b500d02d511070604c0250054603035031541444e40048042880011050170194000003031b42d0440e0710b1610b14246018180c0c0960820449005007030000e00360b41000900c03070f03038422a0010140043c1c00c00c803505000350f005000007070240c4081e042060106151049658004880000f000b07030040800005958102c0a4a00c40b8540b00701e5000c01d12003900b0000b14200410f0940c4211061400d140189040c0b0309000f5440d08103c3c103480e5800c805100c08048a0f0300e903c0202480811003181c00d4507060020755a26882c14003400c4541040818410507000400040000382c00c664003803000b0030395581d80c44000e10720301400d081c1c00da1302c1591958030a000c0740e001b103008540700b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 736291079 1250 736289829 736289831
    0x809191704052706090412030c11060a1b0504140906040b030709270b060904060f0c080108011a130911040c080411010801050d030c0501020f030c120106030c270b0c01020d 75
    0x1e9104c108000c540c500c200d50181c952a9004180644c0d0740c42584a554201050708000b401c2010349540546016411a03914440e259130386555003400d1170702c00341c041c10801c151030310780d103010b00348061803d000310b0030064680546d24076004100513560ba50403402950fa0301408030b078500742c0c1c0d0751038400280c1302009007403007442469402c921400c1300d082d150480c825007241e042001070b2110310a015154100400544480f41c0c4c400010b1040c1d40c10380a2048485c0b0161354590103541001481402c40d0a4418480c240035908a40003c1d40d4071101c0c0c108421080c11703134000038000c0c0c25007080d280040000c1c4800c2e81c058505004d1200c0d4540101c202d038007440c01170000214481c0030400550703075110203000e9a503020385000314600c00a44550181c4100714898030000d400d00c0721821440320940c1040c1ca000801070004036401405104e803000305401824280b0301071000d1403580394060440001841d00c0701e84003030f4002400c103a03110103151040003400e400f4852540c60035400300300d9000350010440c1c090301c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 736292329 1250 736291079 736291081
    0xb1c050d0f0c0f02120c060d09020909070e01210206070606061211030c0f07050a080702011106060a0504020f09090106031506030b09071b0804030305030708091917040527 75
    0x1d03480b80b10b03040d40465020320700e404620700079020043ca80022002403441071090910200d03450f16050b015001c869107041022035120411720402103407540c010016002c1c3c0d4003d10040045d000e80d444854112088056458400c1107000711815043ca440070010350001000074034401084455030041c0d00b100c1c241c2c0c0e690541e9804c0c414051050f1418010030100c1030f2000c0c004a0028240785000341444145000542d04e41001691110b0030030b03c6030101502d40300f5000c00c580c400e40d40c12940b50b00c0903078036003c041e10311480d100340010804e007050b01400f070203280c1c0404c80f5800c000c6c1a00032289a00001015001a581d6401c401005800d5038110f04460720407221001512902a02500b10814002450200142e941000460340591141c0c001c4011030700221000011500c50402000654080d0356120b95a1900d818003406c1c0345805000103006038080003d80c002d200c1c0340d10507a20641d50111205610036481c1c91001c01c1405a0340040c0d80c482d81d00050080b451403c540c410043c020058454001c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 736293579 1250 736292329 736292357
    0xc09060b0d0b0f031c090515180306040f171b0c040b03010b030c0603060402070209011503060608090a031d0319050d05070c0b09180f0f0f190b1c050d 66
    0x490036a0071810742685c8101031030401000c419802c0c4480c0010341c9400500140c1d10000034907810307a2000c1e040140ca01c0041c8001090701501c14003902c81d4015401890103003007a65a00c2c582849441e4042c007d400041032014500d640c2504640d4805003441d81105c2003a40c83c14501c5d25201025984c5100e2850118403a665003418024080d8995009002c1c000c2010b0710814000c160b0300003003e05521990802403400140d48078a8041d010340070030000d0192004c545d48020301251507541002081c0004042008030580b8001a8801c606615140c281c0f2210919040f600410048140300c41d854042d04081c0752440c01a929100d9415001303008441c1070300200c0070155482d2248080250401060317200c180054081c1900030400200c010b44034404464a07111480c1001c18140e8800b410210f0b28410300c0030301d80111000a8204d040c180b00b140b030508055540d686021009400501038075101c0312078001c01e5a4040c1c1950f5003609081c00ea89000c0d8882ca003850302d0310070714040400440c04030280b0f112 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 736294829 1250 736293579 736293589
    0xf0809030307200906010833090712180c050f040b0312130f050105040b1303081215090105010203090f010c051c110606220b041a0307060e0306060d0c09060b0d0b 71
    0x1c002c8800c3c0480c4840a00c8811194000440c4400500308010702c100c03a0604540349d5080f038034803d9449070b4800300c103101240240d0301a0741c00340c1d40b011800700b040c1004002040070300083c4800c81e1400c840c0004820385500c00700f000b40c4000300302c8507810300900c02d201e1a000005d5000b084500160440042265101c0d81c0066014a880c081d40b400204e040c4010302c503d6901000402900c480e07500e001429035607075912050039600c41980d030b284003c012010300880342040c05d0140300000048500b00800e40c14000002c0d40c174010706035002c0c41251050701170411030340540c81e6180d01e0390b00903080d5103008040c4940f10b006101c16036951000074101d5203402601d00e40100f12640917407802444600600c2207641c204004001e04204a0401566241d039075640d5079883c410f0b41d9403100e070080307050382d03149034a0109814801240d000314207100318200d644149540101d0280ea001208480c40c40c066409810510549262500000b81003460201e012644140c0c00000d00304c5071104910a20803520380005000f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 736296079 1250 736294829 736294831
    0xb09100206150f12121e03151e120307020906150a122702030115140907020307020d051b06070b04260a051801030204030f08090303072009060108 64
    0x3001641007100c04688034540a07070f0610784010001d1104608001400a20781080402510b03032002c03c6000420401c40e00c2500700404020032401c80c56070851a20121425074065520b52461048203a400030b21000c0c90703058030b4054024000303041d04000121245180d603480d8041c0b1030a9106003540030007d9028a8403070140003c1000d14500d03981000c01d40141520960f40c0c0c0e40c0c403440d003031761990a503c00549140e40c007035074485080d010b81d90380e055160042c18216503da01880a40c10034240c000d02111106e484c030940c04140607915101581c2d1110700c102e00314081c400000350721213038148008007404000115450000100803a2140c2c601408041103010b11842c2c2000f04001e00d01c400080124440320074035030441c0d103141110003200f00c640c40001c8065000d074000c6c0340841c40200d2140301c0940b580d1490780f103840d400c2c2411481c06080d51030303090b8413901c281001450b800d000281003096440501c1a43d0540354403020f2074525400005840d03507401a0401a0f0703014002c004009005584681002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 736297329 1250 736296079 736296091
    0x1506090612110301200910080c040b070602130b192c01201605040605180403022805060a0c091203090b04030606060801060309020a05011b0c0b09100206 67
    0x1203039205141e40d0b0350100300c490140a60350555840008201d000b502c00030035000c1c2e400d19101c555558290034100301c0c501c1350404841c0304000c0d80108011200c4036540c110f0f015039080703c0c00c071034541c209071820502a100340c150300c10011403020000201018004082c1a032610714000484000d118200c00300c0384890308000100c02d1100d01c110040c1c0e139043d000343d443c11014040c0351002200058603500105400316048910b603a43c044603403000340001021014005e09400c43c0c0034404a403400000a500a03c01c0380548007603104000440e00b0180200325100c000700e2501c4c02c03a02c001e000d8036510381c01b0305014003041c3c40500460300081c0300308051344901c2e00345084985809812a0904009003a200d528917000c40612049500104039802103102520080d4825030010401905000005091a606a11540500d401c0c1080400141e0740c48004801340d0b0400c0c039000d10103014202050741c1d803101c540005080c020512402041c509c004034000c1c68819400e60759000081801c0100700c0c1c1c0e964007110380f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 736298579 1250 736297329 736297349
    0x2030c1e0a030e190602030913052502210d0f09020112110f030c090103060e0915150d03030510050a03021e0105120f2703031315060315060906 63
    0x1c2840003900031107642500e074102801d00442041c40d68401ca0100c10a038018030f002d6800411055428548014440d0740015003940610007130400603204500c05040d900090b99010b960241c0e032038251f01c200000140c55400d0740203000d201d1054030f50202603500802e01091072070b00304180700c104001e0a0103007011055043e968000112808070381348004002c1c510040305220420400451458903036406107000d001c00d030b40781954480780d0400140c1111980d42c05007100c0e09800003084061400856116082c1c0e4107503040003540d42d1034102c54918801c001c1081c030f6000960380c4a18050661503404207100d036802d601e03d0a00d541c1c07510208942d024042c80029172000365038050150a401c0c59100031400601810b140d400c00c88484e00503e00103200b01c0301291070360584070070044401c2d01c146104180d01d007090b003d1800250b200e980161a40300040829109140d40c1e52400b041140034400640000e610040c1004015241e14140c5d00404c109900550402d080c03460124054140c0e110b201d04640307089103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 736299829 1250 736298579 736298593
    0x15030708042010030204080c030f031b0c0604090534030b150408060403091a0415020a15140a0204060203121906030c08010e0c0102060c0d150602030c1e 67
    0x140d0245860a102c03244402c0c2c0b0082007000100307803104440100c894450ba1400760b2507e040c80059480c080700d542100313110b03500c100c0d02d40070080c401004651180c440011000c003510a6215041d1030300b094510100c0d08424001800502c042d0f00740c0c0120f020f524030440264021500503054440c1c2c5880d81c488125400300f06041c46e0845000740d219011404000c1e08170f00d14040b40d03400d103000c1f5801c81e91000301c04e81c110000b0001055844400380014090b03001902c2c3d0f080541c600420341c503001d24003c2c140858422510071301a030b40200101d01c095a031081700ba00c04420003c030458080c050791003994003031107103034000f140005002d80281d80a44603607174011801d002e0488440055000045c0c104140070080c1003440c3c0d000307107140c09040040d5001d5131201c95102d292402c42c5084924490b1a8042500002d60340c0d0311680e4085410b54000340c5400d40c0680310007850450310028500740c0f0121107001144000040c0c44c54002c0060070a150300301c0192800c0020301070701961203000e6442c0030401c98101e81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 736301079 1250 736299829 736299833
    0x306070f03091502030408040302181b16060e010b010e060c0d0e120f160b07020a1701180506010519080c010302030c07050d0903020a090b060d0c0c0f030804021503070804 75
    0x90b0001840500a558504a9000804110040b0b9109403015180e811000800703001758182042111604001c0c1f1001041500e4100c06156151034012959416950006400b41c641401200080c0e21590401c41c05c01c50a204084494003d18082e06c3c0c00c1c1c0460840d2110f92101d140c03203826560340700b0002016000b116102c050888042c1320103840345500880b82c1d0084222441d0410185c101298100c0040c00d20800814070a400c1d9442035021030714504042005100503194211120100e03400348148440e4040d001a40301d0140c840d0030144140d502641c04003e080c00381c00603880f4101c1e10306451540c0ea02020030182100f807240d43c000c000c441e52102c2c08143c195407080e4001c690180b0540d60207800d01c1d10668a10b418110501d801500091854a0600551901c86520030040c1003501c0304020380100710001c03400c10301030b1140f824001036550100c1c8408902948145034050303813224103040102c80030b26000c1c2064400f074034180c3c000d50125440030324581c090000c0701e0085001c0c1e141c1310100d5450b9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 736302329 1250 736301079 736301081
    0xd0c050d050a0e060706090f0f0c0b0901050d0e01231801050c0301230a06020c0a0501050901020c04050a0905030f0307020609030304200307090c120e07210606051008090c0306070f03 80
    0xc2c401c121840c645c7c0307892002c04280e009248261151061001d42d405071038500b0001c1c11400c0b5500004581070040045030241d1781c10200300d03800582c600e00d012810201c0e14890600402815100c000140303840e1801c400f081140c0d002851044005c15481e5662920180200d400c13250203e503110441c50b01040140546041d60741c000d040607111a880c00d00164a07640800c00880450780004c0150b0b20206c1040b809243c52039003880602020f1070800c0c10131a480d00000e540343e8184820318000c4ad80d42d00411525181074100d039101581040442c3e660725a006d2001e02c00da8000c5a0203c014000d072400300b82500310100131280602c1d00071002085d07000d02c0034106200c405602051030f80c14490302000090b00400c41c0540c000491494450140d0000b400c460a81660b181084080060f00854400e0200380203082910301d44044030a00c101424a480c64820010401078004980c40785020130014425903010320031904c101c4003031050341c884202000a0603035448043e9840303008a403480000c00d01d07091003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 736303579 1250 736302329 736302337
    0x20a17101703040312031a03151902070819080106050c0a0b060f040f060f0608092e0509070504110a0807030c0207050d12020d1103041e080d0c050d050a0e06 69
    0x1d080640e403a0a0b82c9580d10079110118401000c042030b1a840d81154410820004030200f150035005480c1c0020b642110700e00f4544003c220140403410000d05200c54905603060320440c0b5409403030301d9641c4480211840403030010811500019810341c0000c50818803030303010303031380c140c0b200f140288644041d695a0f8403480b07000500356a00702c03069007001c1c81d265844d03009040d10348560704c400250082c2480c2207600503d000e60040000c0c004250280074403914002605100c004919031002c0c024500c04018119041803040e014071014240310034440340c110080340c860304442c4102c9040251903560b0050301d031705001e560799034008128208001210540a500f104079000074910640c1d0215840e00300003940c00c06188000e488658605840100590701085824003d05072400d14240312031070100c03041d640e8803c40c000c40b0294100307101400b00f115400d00d11107000c0c0800c1c00545c0c0b50041c0b203120051401c0180281942c0a101d42c441d50400c01c0d01400807684059040c0e500c0c0880c2c5102c60f401d00c1603d0380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 736304829 1250 736303579 736303619
    0x1803170d0c3f0207110a08010b01020303060405070203090a03141006050f2112250b130503070c06031b0e01020c010c05030f2205010905091311030d03020a1710 70
    0x200710712680b50440d030144000c110721885028007012030300141d8248a0200b01c07e03000721301c442e031608506d8041ea0380c000054a50205c000c440202e40c0d9654840c040b800d49c0200494240c104c080c00740040200140c140403c1003450000e411180c030030040080b1402074030150302c1040c1e042510000158120b0400880c40406008298002c90003142c1c841f8029150114592902c4490704011854501403280a40720500b200300c030b410414100001611107050b0b422001d0421804090307030b803001710100401032081c2c49125030480c025595a50340d40340050003400002000c04102c078000160984503d000d64200307400842c0c180d0043c48156441001554503001040060390144070134061303180340c2c888420052108070030b011000c000e80c040c00f0a2200e0f000700560401418402111020300050311000d001c0c03907010044a0100b03c22002a007000360401d115140042c1e01406008002104240c264004281804c555902c01281994403c0701c0196054207681161840207506410840c41080f040c4085d1000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 736306079 1250 736304829 736304927
    0x1404080a030209012a03120207050c13110a0e011803210c0b04032001180b070507050601062111030103020d0203030d230a05060108071803170d0c 64
    0x81440404402c414030024007480300da429640007070100347e8003450013090001045010b5042422940d80e1a0b1510009940a4040c43c08540c62a4034802c01c0c1c0c104410b0031007400a060f40e990140c0c48010b189402c1d9487d00c6000c01c0540d86160142c0003291005030440386c0050f10206081c218111103e0b145620690010810059007144800b00300c0201b103031401580b10b51210001c0650b154210791580440811031285a40f601018181440c418006c000c4650382c0254454078603174403420b064840f40105440906944220300003c5882ca400c4007902802d041c6c42007555001d000d161564000f43ca1495440c021505402c0c401080141480c22007212200d1008094074204440010104202c03203890600301e5010301402d24291018030f030451075036000304101c10140b000e484c0100c00a0846d0f00c000e40305804028650708040740200100748210080e6a0010b12030384140c1a81c0c0c0b070051039411042419070850314043c03282007004d010703c80d0b60750199004001e210200342d10b17880d000e188902580310030042c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 736307329 1250 736306079 736306097
    0xa0b1f0f051b0106080601060504062f030a020a02040f0b01090b0f070b070306060f080705071506080106060507050601081504081c0507120b0a06051206040902040c0504091404080a03020901 83
    0x400010070348410984110000040c003515200c0c1c17280c544107040c4c2c450000c1c841d04010a01c402d40d8084080b12900b01c40407640c090aa864030942c0c10328900c945072021140c000032542b11845a40402d66000b80b41c0200ca090042085088068084614000030140032a0300d10000b080386840040c05010050400081c2500300401a04c0703070002c2d00b000b1102038000076078039101804855048a228100400546840805842c201001038010310a1040241c150090226421038014554120344c026041d02802404425a50900074000390804107044519001e400c001041845001501d8050000d1408201481c2c2c1c48546480102d5880b5062640201c0b07049685101e206c181400760320301998866651141401500c0c8101e41141c5a03c044548541e0b00c1100070019143d128040e28201c01801b54114003a03224032000a00411000b01e00a4016045c010280d05803034005000c0c0c0f00f01d904062050040d1204400c0d404003256044800811102050000b240ba00e40f0a07070107020b0610040c1000c03141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 736308579 1250 736307329 736307347
    0x60409020d0b07021c120203040c0515091807020c2704030f031506050d0b0102031e03010302180f190e2b05130608060d0602120a0b1f0f05 61
    0x140300060802030b2080d81c036220500c92410781c10404092400b182c082081000b8140c2c0c28020801c0c18210000f2500076004000305c0c05214282199034000c003c002d1501d80401c0d1807158a21280e048001c00911a030300811a03080c0000b414062507100c1d40e440e50142c05030034046020420664000f140c140c0a0741804940c101000425040c600d018074040c2e103030f0001d030344901c06000b41035481d40d1840182003101d01a0422a0075085001c2ea0030a034120840420102e04540c0101d14500030150300160b80742903400c030324400541c01c800031410b89000ba62204485000300500c00b81004041e1201e400180850340014038015403c880d0414008410030302080390b5012440d00c3d480c200000c0b40304403c0006440160000010030050414890190300b842c41c10496542807a0b24190440d110741024019204e000a0250781c1d04034054500070350040c011500c90704001c500400d10390085440309442890200d011060340f43c4181401410000c4164030b000f0044d41007000c65810020340584410320006101d1140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 736309829 1250 736308579 736308589
    0x1005030c150405091305010608060a0e160b090d0c09270b0106030203060f040203040321060609290c01021908430c17030402090a02030c1303082205100806040902 71
    0x2007000b0270080c89141040c000c01c2c0b0445010481d0300d0b15642c048110f00c5507c00700020303000c0c11158035030441519052a10081445e4030507540009240000040020861083c554054044000d500c00b416140d6881511b8400d4401e5200201500030000c0c07a0040042d9480b0b80c0055138400800703001d01c40310a5120001c2800c0e40c00683d0120042801d001e41149102000355100c0ca00101580341804080c0c5041000b8100d43c0c100d02851040c1d0419031a0075500740003540c1230207084e80b605800d180d0380c7c1840c0b24003e4001d4100b01d01e2002c0f00664000740d03440d164840c6071501e005040c2001058802c181c070075108240d40d0b2600050a080c81020031840418005032980d900c401502d684a00101e2411854210400c8903019a8103a00100c18810f0002507200c1500181c1d01650700440141ea07030b04d8021405185002d40008a181402190350201c104501c078005020301c2418002500c0c5109850010b21030107100d54000d10740c01035007080581c0703002c0d84a2060342d41c01640207403000a0048454002c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 736311079 1250 736309829 736309841
    0x130503040b07111503101a0415021c02031c09020102011e06080105252709020406030b010e100c111f080c07050a06090213051005030c15040509130501 66
    0x1440c50000c100c144011410301c80342e01100c0300e10660f42d503441d518081c4002220113001f80544041044140081c190132140d174421140a003002840034012200d5a01e00255145454072184072440c1c0c0b84031214000b18000015500082c40101da210311b11401078405000070000401c3c00e904640d01d0b962044d203155100c52403801840703007240c40422900c2c00d1842c61030940d007024005034240c0407a201d00e030301d061003032803111300410310b661a103001215404803000d180780300071080c0c1d031400304000100080c1e2140658010812503845071070900800c0014001910719041c0142215000180c108132010110310031203d1080681c0b242441e202020030b80c6020544412880d10920340c542a119400c41c00243c01691880c2d100c064142298a440c00940e5040c1e01c448507400000c001580310a81c00c1c0c00c56454959211040d00841410001450304000c101d2030343e410751150600034052010803000b241085181040c00384000c4e402545401d25060500800000c010650b50b814142101c12400140d400c0c0166 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 736312329 1250 736311079 736311083
    0x1031e0b160f05070203070b030417190e030109020306040b0a020d050112020a0506041d07200715020a05061602011d0d031a090601120b120a0c05040903020303130503040b07 76
    0x24001407400301c0c50240c40403402c0700442050000600c41080103950004980c8150b1718180e142c5500d903100d601c9c01005c00348107001d240c04003000c0403030030203800032000707202c006080320980d1107213582402202810301300c41c5000000b03501504a14002070104207004031040e0821644040103240c038011400c090100e8800381c01c01c22016000d41c10403c06d43c07920445040260004840740c6160500d880403c01400311402c40700d80c80516914001399021307004603203000b03403019142c2d03112555016040d0010b44481c42405440e0140e0704800d00f07400700a10010340b01d810f99070b101c002002207448903548039010062086c00c0104644d2960202d81480e52140500c2010b00c050200801d4903100111016007695400c040100030309201d001007034602e64840120a0b0021420f003050103042c40c3c507448450250005a140d19005030300f605c0d1968014800040251a2078000c11100310009c0c2c95004103c1aa040c02c0d00140041c1d00510104602010a04501000c0da1260301220300c2c0540d55030f41503080750094141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 736313579 1250 736312329 736312351
    0x150a06121116300503010317090406060c15202802030c060a110406030504060605090c0c060a020a0e19030c09240303020304060c0602090a0306051b0a0801031e0b 71
    0x101407201c2c11110101250100c94200c0c02c3e40341c81c41240c0c0100796000501c00501001c200354407200380300001e04125030300c1420240013400340c107407a40030281c0a1020000203e90030801000101c80760000b92190303452048800c0300d406010f5031007c4132540107810120404030441c1c11041a2104803101c0d5000c1d817040f6400d80c000d151640910701c41135040140007415510f005003020010380041d455a030860b000e450440c100020103441e1400c090780100050b4120320303003180c001c60030300c43c41000d06805080050350420441d40344d83d41c0c110309541a070040d20401c601168001ca5410a585408071207200d0391000d5005441a980e40d80c0c64441d0409010350107030100307503983d6020b010300303112004412048840c40315604a4030f03842e6903402075523446180319040c00c001448031036604028041d0121074000b40014101042c40c1d407681841c0740100019548103004030150074200e0100308440303059480c5540a03403101c08003a13180d0b44890f41c0160649401603440c0c1ca000d010f4000190184801601501060f10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 736314829 1250 736313579 736313603
    0xb0309010c02150402010818150403180b07020f0d240605011116030b090c0303190905011404090f0e0321100b0f07060b0a0e150a06121116 61
    0x701a0802c1402c1401144075802c000030040980d030050b0407180c00181043c2010180700f580d0600c281840c901500032203e05a00001f0300c0140342c0c1c0000b180d01255002d40700400d131680d4508d207a40d12441080b800a40009420343c0340d14062910705e0622100c1e6000380124200090303244080480c0340c0d010281e2607600c0d42c1e10b030018005542d00c00c130581030800003840240090000d1003804100318010f44402070260b0203081c0060f0014205000780709640002404483e2540426807a20200445425141d400079600d0074001403c0c0d8414411042d29038822056507107080c0c24052188041d1011003c200d02c030a0700d410813503102610400003081c840c0d070702010001d02420305030540e280460380078000c0c05007410b00410a2048144013421108810740500a0680e521103d16004000d006a050364a83c401d101900000c0e00c014040c4030140303e8464910700c241c601f440d080c1000702944040c0034010014420808004c02c0c8012a0b00094080c40014800ca04001255614604200b0b14020850311081d40003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 736316079 1250 736314829 736314851
    0x130204030506011a030f0718030503030118050c19140412060b1e091005090903040801060609060f03020d0b06041206050618040206030c0c03030c041d060f060c03040b030901 76
    0x440100e0251032802c4d20381040d40c85205103c0c141d4007000c0c0038001041000000305400b41d02070b10200c0c4401251030a0f124840e50380342020f1b038907030300300b4401e04600c141d050f4500554180984240f0780710b449010501030500000d00da418208180d40c882c01400c0c00410000103008040c44000303007005242c40400001020030619111003901d025511041c014801d095210710007451060140040d6a01903840c00600e544090064400141d01c1d400290002d10400c188144040b0210090041d200c3d240001e1003100e0340ca1500f1240b01019115034030018000c446c003200040c0c42074000b032085030710f00078001c1001d44140c170004c0c82da50b00a901c00e00c0c403d8a000380220030060540034146e4001011150402d00300081d03969a4988080144000d11402001001600038000b441c2603440790b000f524102c03912481c09101c503000796031107070281110740748202c400488205280d120702817107141c010305650030b1180504280141900301c200000308038003040c413002c80c00c5000e51001e5840741038810000710700c0b03540c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 736317329 1250 736316079 736316083
    0x1509010f051e092802070303020301030b01150518040f111905040e0103020d0311160501110d0207061101020403060531080f0904020c1516020c0f060708091302040305 73
    0xb20101c145400401e440c28095555035881d01c0e03501810b1003034984c801441d41d41185122000d03007140c200c460b030b2000c0b50000c141035141c0d01850580707224040303c40e4245d803140f405407004080240c411000504c2000b014811803101296030f442d926001c0c0c0045010107100c85240142e0301900306910105401042400c8901500d403c81d20040b02d280c1040340c90b19040c42c4003109404d01c1404003a004140380390140c400c152141922000d80c04010041e101e294400c07489200a0706032038860280010007120141d610150082103030545815680c00800d2118a00315080c0c406150700701d0b100300035560074840000802c40900550740700b81e081d85041c90312180c611059059091252001040d0004100e40e00380000e00b02c2811640c10f860010001521088158001806441001c17910384040c02080c4030034100540c3d554507540260074121012109008040003203940c1e2007460907442d4001041da01c813180c681000f030010543d03140600c0c82603151060001c04913041c0c0044400b0448030541c0000d00300140030741 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 736318579 1250 736317329 736317349
    0xd03060501051602040b0f061902010f0e030a030e0705060c07180207050a03050d09170c0c040213210c0807090609020306150309070509011805012103081509010f05 72
    0x242000380c00d0050b18060600040080c21000340196661106c1c49078650310844115200c260042000f0b564811100c00c1e080c030740040d01c04880141d800e0074500c8560b5080c2e4001d000080304480000c6080a00e5540b0032405000d00c0c0c20b681069000d010408030300e54a0700d01c02002005075074002080401d2500c0c0e0700fa403800d414000170742c0c05103106001c4080040d50224200c101a501460040d0319006001076040080c02c08010040c02000141c00114481e0038840203090340e080310740d0070394451082d8001400180c4c030641c4590481c101000300c060000500c030040688148110144560300c41c0321540d03810440e00341503005250b00381d0101000b001788101301e0240c0400751004c40b01c15030031420a000030900b607035090130f580c0188440100014000768420001d460043c4001000440c9a581d1003181020100100d5010fa40442c2490300100c1d8226014100b484001800c2d09140c038008a41d441c00c0312003540242500c2c6084800500810f41030340c0c0c1501590292441c1601207004601d09002c2060b0359103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 736319829 1250 736318579 736318589
    0x130509010b030c0a030e070306090501050a1a150c0601140910080606090a0f05040305090f0409110906011701140a080c030c0613030c14120a0503030a09060e0303090d0306 75
    0x10800180101c0801c44241ca81110307812100c9a00c0f01c0030b4410540180619404805061040741d00000a1108a030051005940908000c0101e5124810340f0340544016010a81c1b9140c083d009030381880c108041c082030821801041c0e00e0030015147c1c01a41000c02c01c3e8801c20984c1c24403990784501d0b10303040d00b10302d8205280c0c04090030ba140c64800901d840d0340006102503c1002c5010004070340c602190813000c095910780c44204003e00c1d06203006009508464800d83c01440c078802d800115080034850034001c207800c2580500300c184810104203032240020803181c10404c03807403416450b200702c44007041e0107001d043c100300c14101d1a11041c0008030318254002c5405911503180000d075601d010030542c940c0031040d503145503510402100451010002e0b8401084001301c003e00141e040b26092100c11101d4089502d5182200ca602c4216621a0b0140003d4082d0f0000c00200b0040b603020343c4076620080c8610004524080c60346010703400c44d001226070564540214050300d103425450312800d4007600c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 736321079 1250 736319829 736319839
    0x1090911010518190806041a071d090717010807060212070b060f061b0a0204060f0e13020a0509012402010e19080d0608030a020c010302090d020907030905010e031305 73
    0x19800e0f85800c10309807541404a8061842c1d90898110703410780c010000c001c0d14031503003110003a040a14000340d00005d01004c1c150b0b080388450110b14078030700c900b030100441c100340707481000d0210084080088000d0064400f100b40003102210004901c001b0031080d00a0140c0e40c00f0b4543e45240400107400c103002c90094800c294020071043c400124200d2019170003190580d480070001c00c20030081040c510441c220011203844800d0042d507104ad0000301004598030a98060001598038041e58113140050700800d07004000c1400010200c291040b400107003240010b09a102d5140d96801040c0584030a810085070380301d80319000c1e5141400c041080079480654402000082060100380c1d1f01c0c0c103184103160584a00e116600f04c02d00441d0805c1e194400004441004082c2d41c42d00717155580e030300c40308220300036010360f00c0c110603a58040d02c255008040701400104e10581c080d401c004000e50020b0800003416680c000e03034000300e030092040099000c0c0100055a4601c41c1e003000c841800c1b40d0b076201502c19 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 736322329 1250 736321079 736321087
    0x207050d0c1b0b0a1b05030c0c1c050d050f04091806140601020c0f0d1403030f1018020714010614040605040228090315150e060307180b0405010909110105 68
    0x34442c10030440304d501002d0314000405d1460341e425000d007011320f044080c10a11020441c0d04404d039000c01c0305141400211460903d40301e6004040f1031240c0300d0b2102070190341005d0540314035103000f00e0042800b0f260440c0c14030716240d11003e188003103031002151010194081e41d02d01081000503c1003450740c03035205822aa8070318101d80000d503101003828880d8011554000c1b50706072341d01c0c1e13449002030f170b260301500408014140c01c4101e07584e41c0089443c100000c0050f0045031022801d4800d6605564081c0c144c2007501d00621034480180d03120303c13022a1519000c10454001a40a20410000e410708012a9240c103440d41c081005a94194205500c01c520400c20b11040c10141c503c03010751700f18000722400703503080382e8a4140c508044c19070014040710039006115010038480c0e4444040c0d842035034014400180c845003d98000e980c1101e0070340e055441a80c1c04e00004800b00b40a104010310360701c1c04242e010200c40414152042a40002d10b001d484141180803c44c580076880f028035020310b401428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 736323579 1250 736322329 736322339
    0x901050a110c0c01050f040305120316080912030601050403060c030501091b0206010302090a09050f160f050102032703010207030210050601080c0403061806020a050a02012a030f0207050d0c1b 84
    0x4a000150003d818400e00044c9a03c01c0c100c0c00082d10015600403040e903540c86058002c103040b0303500498104480118826010640318051200715028643c1d500003010020000c80308110b0640c0302400b01814007000b40030000025071907000b40c8095042c280d401040b00d505d066145e505035900b0038150a0b00c4041001e103111696070000d1168112a0110f0b058800ca031241d4590b6401445d4001000d4054020040004821480010f001610400c500480c10121380d43d40d03045c6945800c0da0042034016082042800c0039909804480c80042203c80d4802e1054000c420000c1d0899200c020100c026802441140301c400d4514896240c1c040e6007130030718149e10b1501c0080e0b4101440b45002c002c01c1c140d03641081840ca0030011078040c51441c0e100404640d906254070300602542c02c9402804010360800e07100141412104c0100140150740b078020f0082281d2100c8240c01130611481c0c0e140d03035691709000040100310104024000b1a000e9162650a4495802c00a90f2005046410fa0080b0115441004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 736324829 1250 736323579 736323583
    0x4170a020c01020f011b2106150809030a0905090a06090c0e01021b010f0c030c061d060a090b180c060a0f080f13060c0e1906030e0a0c03031b0b0901050a110c 69
    0x41c082c03e1890544030002441c001c7c580c10b29040c0e0030540070245452000700340240496000240076220b078491007201d0391020703090b036524440d40b255074000890a600811035801c00b05040b5403c6440d00c00301240542d1a66800c8007207031402c0e46007600180340b02d451b940d074658040c0020080310f0340400e8440c0d4510059000a03000c14480f01075481040441e2104009140c440c0306000481940000c007805010320301c801c00d48500740000000d0580d4040c86c4040742c0c0b1020503200301c01045078406211356165407059031412200003410402101c50060020301c1a403507541e003001700108030554a51070084071100744001d0074200001c01e004403c6549505201401591942c0d02132540c8d4400400326558100e54001c0b6001621446c1c140c2d0003010400760491002c0d1021540c005962280e0340c20401e41c200542030b160b0f21a0f2075900a4081c4000d8042440400d110325010040340c103100c1d1a0720070b04803159a45c80c0f03d04c08211070004059540e80188118183d607402001890307040003140c0c6041c2900e17200055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 736326079 1250 736324829 736324871
    0x921090f052103160c120506060f03030903032101081b04020f0f0d0606110a0b01090c02030c0d0504030203150c1903060f030302030d0606031509020304170a020c01020f01 75
    0x140c424a01182000b85042402500700b20084001c0d064a886800e282600400404101001c031000520190702044d540c0180306455034140d00f044c0101038584a4005101c6c0c1160800b2110340c041c0020820440c5c80d4400704002c007211002c035003400d5007501c09818000405503041c1c00010540c0c110300400c013403484541141d0410b0340d0089400503620303648a001c9a04611486c00c1a1910303c001088050b690581c5900180132601036450b42407104902c550360302d4491030002002003e080401006000f07103c0c1c150300869022481c1d0044a00e0806820040c4d4034100541c8000800101d001030709004506042c00001400b007401c0741c074040e07a42031461101c1800e010700020341d8020304010004554852180c0c100d4002002a80040c0309029105d082c000d480794060081001d49030300301080019039521903c10b522070f84030034640f561001c50400000c00065403026100381c940d10103000048005000c100010a003450860300144601c030310010000e42007040c00040740380c0c01e07403400c56103078200201d80c2c10074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 736327329 1250 736326079 736326089
    0x1218090e06041b0509071115070e040510120318030813080c010c20180a06081903200709061d07080906151f080601120c0c0221010921090f 61
    0x3c84c0c801f0000881c01403500720b0b019611106d004ca5801441603480c0c0142c5c102c0b00040003550300307002603a40d1a840d0304000400e441060007040c2d1020070000031034070a40080c0c541c500004464882150741b034a42c0001504038440e4004a2000c0c44810400700342c0401c0b04406240080c00c041c102049140c407016003010544c0c2140240761516500c82000d0340c3c0c0d42c21900350010407100407a107182030166644004200600036400a80700380110f88a5090203084002161907241d83e89003074051020942c0031084071541185a524809c4003008511145103006100241c0a10104401d4200440005407120304000d4100c1c0c082c071007105c003400052100880c0b150f9011140420500400300300078089040c1c00840ba190b0307442c440d0500d5851000603844600140112426a2400c0d220a000e2802c641100e640c4d17214500032802030302068006040c00054040c01a2a076212202c1c1038000d07904803402c0d103a05003070840300c603101012019480403003003402e1800ca00c00d5140c42012503041c0110665650102c0c022 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 736328579 1250 736327329 736327337
    0x106080601060804020d0b070f0e0f2112071a01060e1305181006030b061804030e040207120c0b0a150302060d0902030f1b04091218090e06041b050907 66
    0x78055481700046c00c00040c1d4406600181c510b09004000c1400001c036010000081003103003100c00714a4141101812000300519000a01d54040c07058408600c0b00c640c215200c0c02581070203004585070001900800d070107000607007040d0b013014825070001d500c1600510305110258904008a842c2d180130307940d4012001e1400901c2e80c0361182a130405001e000c0346960750b8480c0003400b2144003c2608510200e81c45035013030784010384605040110b03810324030007100104100c050000e008070f80705400c07210000d8005003005150a0440c4c8400019804140515005c2454054040200020001d101e030b400030001400f00111460001c60303d0b04400742e0f2202134802ca0000c40c015140008d10b0784900b0819500404440c4008c01d00443c1d903450b40c020341092480c0b210142d01e030709805d0605000d04691302d60700201c0c40c500b43e0520b00307041c0d0300d240c154400c0230b044040003040454204068407404000076100360051030316160a2411080d044050f442240d5802d0503240100f00b00d0f01c4441445400c0305e01030070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 736329829 1250 736328579 736328581
    0x6080a060903110109030e030c01020c36070f02060f0c0d0b0a0e010e0703061a0409090c0f080f01050114030619020915191e0c0305040b040816060201060806010608 72
    0x142190704001180784408154606080305c0d04040e0005484005082c00b6001d68117030620640c016600c8046900955410014404103400c540c401030300b4034500c240010034202c20070909a0603212408100f15030290100c0c01c0758611580307094041001d180d1010362200b046070585024003415101b800750042cac00f8000e584a0203c61040d544440904000e014503d482e0110b45da500c00d40d030250041c055550030046441e105001c5041c4a000d5122494a80000344042ca005c0c0303020380b040000c01c080341c400d883d4980d00f0f50003c02c10044154402c0700070034051004012000c441212a42180c6040c0d018048a11013a04a01020303200420074940c06000e101c00c0c03004c00d500d2075401c1c90103840386070012580700202021480798540200080c0403c4c890485032070000c001e81200c1641c260305048440d40703154003061071402c102c1e03104041081c002c910900c1c5c00e505042d0b85020b10b0080b074001d03401044031500710384050200c894030169580c00078031180c8020300000346021201506d565041c000d000400041da4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 736330935 1106 736329829 736329833
    0xe100308040b03191b0e180703020306061903050420030705060a0e03060a091115160609350903030417010e0607050d0f06080a0609 58
    0x4035040d25090914980d51801d4000034105a02c44410510700700d0702503100c0c05190744000c00e041401d03003104070205000c0c115000300d07800c0c14002d00380c08041d01100000f6200712074118440d4100142e0340e0b140c0310b02003543ca01c262810a01c0405c00b40c050495059815808248640c0c00740110030034079014503c0042c0d1344020060103940c9581b1010f014403051600000804030000035042507459100e20034040b0382800d60488008160303c0e621000c01040c070400c2066600c0483c4103d90104040b01170448a51700c1d4000d400503100c01011a200c6082008603a134090104950417194081c2000610708180351121800402c1c15003d250600c0da08091040702c2082c1c07520450020061403d080c01d14400c0c0ba001d00104070302183c03030340d285d098580307006000f402610300405079542d80c81c1d911000c44110100380c03110043c280c0f811500d000010010305201092650750154402d10101d183c1d2814 = true := by decide +kernel

theorem cover : BRFrame.Cov 736151079 736330935 := by
  have h0 := BRFrame.cov_init 736151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 736151079 ≤ n) (h2 : n < 736330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
