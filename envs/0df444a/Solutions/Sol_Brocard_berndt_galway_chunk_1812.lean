-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1812
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:46:05.012884+00:00
-- url     : https://prove2.me/submissions/0df02f66-cfee-4a43-9b98-29e7a989e4f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325719424 ≤ n < 325899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325720674 1250 325719424 325719431
    0x1403180a09090f060507091a04090507110c30060a0b090115210207061d0c280f08070e10060e040f09083007020604031211040f0503010f 60
    0xb151209014140c0300c20700501020303103590004076800e0081d001d18004015608400c00d103400400c011516236041070141111003420714010813000c40c0305249500060b0303011000b40c030000e46200200011120459010000130200300e14601890b00c00b0030b08035029181107000781015141c410300413402c840c940108503210300110401400044050101454420182d050007481d4400b60112600c0040315040384101080c00000c4035410090246c00100c0302c0c4900340c1d8415a050b081030321264076401076151190304451070641024034441c07000c1e010b41c07680042c0942c2412481c3c641210b80700340c1016402401c3c4592003034004016090b071100c641c590110040100050050500780000d000c0410007600360b10407074507034a102410707000c1580111441d0398130595a9990352030b24081140d030207031501c0001c02d07103192240030300007800b5604119521540803a07014001c2030b60303aa5020f6070000241a00595959603491181940c0c8031100c0040000c1c2008060300d010b580c1c5004101803e488205e010b01d00c1e001e08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325721924 1250 325720674 325720691
    0x80d08160801050d080c06040c03110f10050a170c0a0206010b040b04120201020c1011150f0601230313061d1005092a04050f090a0204091403180a09 65
    0x10701c10061415524100c0d4400742424150520003110b010b0742c0c00c158103d005130340500c410043e001c00e0080c1106d00ca0f061040304403000c4000c0040481201650300c1e002902c00e42140c0c00d140c070440040c00e180003203003050706c014481e82c60ae403103003400304a0340d0164441000440c0b40685804110003070052410025142c94a0305003002000140214411240c400c6505000001107a000384030005060703002401049900004620003420882c1401038100c20340034040d051075000003540342c803c1c402c0d841005070441c540c59000044982c00c49240b03000e10421207491003003820010f20002540030b1101c0301540c1d10040c2160512804646050500c601c00c1c43d40c030355101c8140e0001140c0b43e034441e01c0202000807180d032100f00283c18042502e000705c22890195001d1903640944100e605040901030f42c04028903595100d118a2480d42a60314520552000c000300c0014506070704200031042c4a030300440720b5614021502c40c0b03542c0200d80210798802c603031110034080381081200e490040c060b03042d084c080c500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325723174 1250 325721924 325721927
    0x30f0309151302090a06091a01031d03031305010e0a03020124051f030632010c0201050d02070c0302061603030e0309010f12060803070c0608060d020916140301080d0816 74
    0x42c07408009029140e4440080c200407129801a030080880c0281404104091720154140c20910304039a400301c1d1a080441ba0035481c5d032010b8030a818503050046241d9112900e040034860548002142e1964031420300c002c16078810301c8406106446600040b419055000740e12a1800080d240c040085800100411140d0380349005401b180b5280640d1050320075035414101c01408558200300d90f0a00c400c08803204030862102c2c101d00400c41c0361081400550b04000460f20364031007010182c009802440305099843d034550040203650301c200e99a0f20342035907990124020750802c0440f60b1440280124074000c0c5078041c09000200b0407200302071803400301908000b03032807462a11100c600308280130003541070030301031584084003800f03900046a450303240c5842e000140c0720b070340d0060b03170001240080419141d060000c107140c07445034020005c01855440e0011441e044a10714041e41c10000f180f616108150000e2006501801410340505040340d02507101808540e400703816161024031440c0c6101005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325724424 1250 325723174 325723201
    0x1141e220b030c10080717011214061006050c0a020409030302030603010b152208060a1b090810020d141819020a060305060112020a1809150303030b12030f030915 71
    0x204d42d41400b02803500d80010032103000480142100c0750810720400420144150000ea0082034400d100c030102030b1804641182d21b4400035034042010b40404141844418028406032081d0003003002261045c85242d0001029944030f07550641c042a800014003069013020300410221000988054401c6c9a01d10b10002c064400d4181000c8070300300f1507031500904c2d90b0440e1218020f00020003107900b141808244a8014521112100384449080e409041c801e40500118400c0310034040203418100509100b010181d400280f034400003d0741c441454548075100000c0c0c2d4000c2801c0047c070a964a003801c030380c529210020304448198280d2000c1c54006a641c075200f10103980441c60040303100d464640040e582d441105141442d07941c00402c1d105e40340c6a0002d00c0070040d04209a214103519507448281c0100c9141450b6042a02d80c135490034000f00b4045e401c03100d4000000703040b8085000bc090700b52402c641000340340d03000c81ca00000a11248200400186a01801c203441c604a07904100007600c590 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325725674 1250 325724424 325724449
    0x190e040209280f06061d1203040e0109020315010f05120c0c0a03020d08010902072003010e0d020307020f0f034206040f021312030e130507021501141e220b030c 70
    0x54101f10340035030020751003442600c0042203903015903001c5584a0008801941040310018a21051403019115541c816118207841c900c0b140c031014546054810000c0c0304e41801880d049101c5800c21080d4941c050130444e2003075890081d40607009510340058018140101a8820700c1c51900500c024808034050300503081d1404001e140d01c00f00f0030181e4010a004d0013589803c03450030702034001c1d00544d141c0c0100080034407a1080f40d403007880030500c80801000c90071048850340c050740a4070914130030004000102c15403c0301d42c411000c0e03555090641428a80340e5040741c0c0380031800f40c410b06c00c0314103250060141c05d020b5180c2c158203144501c07548ca030b49000e1620030100440040e846070700515004420000950901500b0100c03001ea10000d0340024000030340d1144014810f40d00340058012003101240d05a4032001d4244d030b40388541c10b0400c40c800c21078120b00b445030303840d4007840360342c1d96140407204543c2d840035159850800e100144440880d2101c615150180c3c028040054466032440d446806 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325726924 1250 325725674 325725679
    0x603191a0709181e0c083102040b040e10020a02100b060f03041106030a0203180607081609120501060501020d031509020313050703030e190e040209280f06061d 70
    0x6a40244502c1841300001c42d600d01c40380c00385400c9104406030752022420344142e003501d220050030004070000302400300b400c1074500e041c0108400400d00501e05500002c400c232400900101e4241d600590700b5051480b101c5002e40e03115400501032981d580c060003c1c1d80c02c4c400b82d0208106402541d40400c001e4070644806400c14280000002c04014082c807098210000c040e0100c1c1d00c929090010304029030080c0e070140480d0009108031914a580000c11900c50403041e5104030154030366200c4280e5501d005036a0b403080c0084800301040c074856126807071040c0c83c02f400002c1003051a0500190a01e20407900342c00400d030802060382c072010503c4170004110707145024016a00d03501d076854084469401c0000401900a1010000501d9400082e2042c4014200d5019200100300030388009485420710038502c003d49083c0c00207000d13140c612192a40007110140e01d8041140841c2101c44255075100c003114520745d03414000203101210302c200e0018181505140f407510780c070306904003440d0040204852 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325728174 1250 325726924 325726931
    0xf01032304080c070902070c0e04020a03170c030d09171201031101030204080a0b0f18070905041406010905011e08060a1505040e100f110307080603191a070918 70
    0x1c041140700c00031580f0b02c07040380040c0e80d10b05032034103802006903120b840140d400462488010804041480040b03004541c0104041e04661440e690004100c14940c080050480c052014000200040c801890241200ba0000030700c4111813501d10b035200c2201c00340320f0b144041802842101d840070042d050649800c90100d80361441c000c2d00480183c03089802002c003e0051082210401a1241006014140c4003107280080c1d601c000c2c10740301a8045211419030303640880c0b01000440c202d81d000c2a0420b024100c09a031005486a00c036280000a81c0808041582c440041000072841201c407042c0c4141c6400d075841007454200c40300d5480c10090f0003040782643d6003c08d80c20501c80c42c9015402484007400501c000c0401da108662110785c0c41400798080e40c01e220340014012481c2c8100d2942c048040003460a5880e10079007141c0001006180a0305403082c0201e80d445080503100d855040d80c440c40c000000c03400d581d000d5000c2081c02900c22001d00c044a070050240380500014040c4c00c040780c05000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325729424 1250 325728174 325728181
    0x1060215180c0d0818040b0a0512010603080c0d020601051509120a052a0409020307120c120804030201020d030509071403031207020a12020604051005041b0605090f010323 75
    0x190704212200c80700c0741d44420403182950400008a01500d445c08000c42c243d0021140d00f414031080e5403400007620f03442124140c1c1842076181000207007600b00302090001904c9610ba503a0942d2035440750007001070581c01480c3c500c0f58240e04002c081e0140605481d01c4200c2c00302e0300c1500109000e81524244548600404420941801c118100003035410500311040d5003586065901107401001c0201d0000c0b0900615481c60f08080c00342c4441d0b1b0f94082c0040071030300e1500400d5046070010120446204007012400240d40b0003186400c0152401681c01c184d413a072840c0700180ca010f9109036048241400e0a0811030150000b00750881156440300056600b01c16590000341544190b0a0b04070b80d040c0042d050050160b4005404c3d400584a01ca0300400562100d50590351103408403001420350b4401c500000d804140c540085e0f801a01c1800c0240145480c2416045201021340092002450100b804d018601d002c07251741c0340254003803c0402031851200801820300c2124200c119040b204c94010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325730674 1250 325729424 325729471
    0x11224061503060e010e070c0506070f020d0c0506040303050c0408010f0605090f040b15130204090507020f0604080307051c0f0f052208070809150a03110910030f0b031902040501060215 81
    0x1008c1c40c5a0140c2030359864039200c1d80240400c20311034600310040c8142030fa941403041c02429140c40c1c0c1904100200550345d1030340c3d811405004000e1191503402c0c4c0c24000010300140902810f04440c480c3c3c3ca004c11100d0800d0180121003400402440d0b0b0100c408040c800401c00709082160400041c000b130f074101c111603102140983e544110302d02e240e030340300042c0010724107800d0340072500510450b425552107500810340c030b680d58401035801400b00c0c0340070004540401d00483c0180443d40d02c1c14140715003848000e1502003240c54410f144403455444201c00c3c10248014403440b0741c0182c0d1000e4a0309020424040d00382c61110034603000300301020022b8140c080c800040309486d40464020b000300310060207500c0442c0e45402402100000c01d00340b4541400307a5055200ba00c50a07100503004204801d850b5408901a1204501504000f6942c51483c0c60300e4909004048451981244080a0b02040c1c0706100c21680141d2050701190040d0304c00a4055641c480c2454000015850148011841d042c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325731924 1250 325730674 325730687
    0x31303030c050913050105030105070c03021b0a0504050702010f24031709121b0603071706120d020a0302101103270601170c0d0506011224061503060e010e07 69
    0x10030701d9004100c0d5018040d241c200e504064182c4009230001c2c000d603202c0700d07010f0b242010420001000b581103241c001040a480c400d01e03600744140101381005956444000c6000c84405460010041c0d449076684004003010b4090720f51402c0c040c1040c0c42c40345880f9081c2c0010405c95000082c051110380815150340c154540c140c1e4501680140440c28000c42d4088140d910341c01e500f8001040061315507107008a141040c19079104500740c0c0c45600c0c404d42d140d01030000d040c030000c28003235001c08510f070b12442d500b0301008041c81c11441600101801c445a04000c0c0c5448150781120045030708040404828000d06415603400c1444850108984000816480119021004072440d40e210720000026413601482001620b40003a8003594001e0741c5040c280082c4070315408001c1e01d00d60040004204000950303880716580c3e401036003d4440b5101c000d040054018904101c8800c0e242c031000144240c401d00001000510451700b0108055031810b09024181d1405100c3e440c00c0540e48400200d10a00448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325733174 1250 325731924 325731937
    0x3022107021512070c0203030d0c020f0a0b06120109170a3f0e0c1504050312030a140f040303021602130e010509071a07030c0f050604050c06031303030c05 68
    0x3003442c01100040c66040ba442d8001265007030040700d8800c04607801d9406220203405158010b009140b501c02d18040240150200c2000402148a1107400100d012800e002c84401540700c0d0300803c42a003405030420000c1ca00311005c420031645810784500000d00c0482c1c00b5051030710007141141d10b030444620207a8690300348140304020000b03441000e8101128000c3e0070002c806448403160984d04251040c001259800c500340841940500000011454030140032400002c4003a0b40503d0a51030700c0102c0c0c20700805c124840600c04010061011010450007903808040d40e251001c4400d1400b4a0000d00c00c000192001d000e0590000c0c2c6914010310055014514070707000703002e405098001281c0a00201018241d01c1c03481d510303140101d41030326000b00e0500e0803502d41c07110140c0400c865002c000c1240d4040103084062240030741f550000070740c1c8004480070030790049019147c145041d04146003800c000f5403141303216450401c20004003e4010034807501c0503406107000100c038600d0b00806e030341500c01c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325734424 1250 325733174 325733179
    0x30303010e06190f06091202010e01030b0a15020a02030d0e01140a181715190f0b040924090b0718080105091014070e150d050c0307020f0a0302210702 66
    0x1c41000ca1603100344c0d022807007100c243d80e50783c03048280d880c00255202c0f202e03060300a00140b0112801e49007588240c11841c80c0110050070004103a95034001c12461103034141001c805a0060303140c100c158079003441218043e40090512142014440000a15480e1010107445010001160144480b0b200c1e1441f10503481404602d11001505d03046a55000d1a4030503203851144201030301a04900400c15a41e80903203000a18003a13a1681c0c0300f9544040c10010111046565981c5034103402c5039640c4c015610f00318080c00035064201c26843d09108a00f0015407981d0351142040ea00100040d00011256440f240a00d044004c55130411b5018a5510007640b008250750300b0b040610410500c081010040d00203241410417048a100440d0001038104603502800300c2c400000a100c0c070300f480c0c038100c101b2546040d150341c07810004419030400c0720002d03501c4200c51070010041019880e0100a001680614800141207160003550001d41d5105d450641840307000881e0f038900101c56000c4103a52805500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325735674 1250 325734424 325734469
    0x51c0f080d05041101110309060a020c03060126030f040306090614070e01020d091a090114040b0d0e01021611031e0f060f04050d080c090904060504150209030303010e06 74
    0x21001010701a1100ba01d00340c9208030012101d511560181590b0b4440703848100140d801e18000004021042d00128041025801190b011a0483d40d040c0506402380c04005828100c41c1c4c0c0c1e4007005000b44284000d501d599074805c0081c840450502825641121b920440108101109242c080c01500c0b00100c48490b01004009008402e504080c14030032808003a03086500e40300c0400400c4494020500ca89101000300300c0d200001c60300043c0050442c0760041c100700a105040f87d000311410341c0650720880d0f004202003482c2d4083e9040e0b00030758404007030ba18000d42c00c00a5229032030404d100c2404000302805242d080041090710306216020b60145e85500c6c1181c0d194509140b140c5034120320034054024052600002d20788406c0314a400d0250744c0020003051180412901a100d540010389604440941408245500ea4a07040710910581c401e07d404102e50906141c0082c0c803028943c80b2040b4140180701e024501d84000054a0441d00e51002106039600c84d0404500c40550404080f11245d16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325736924 1250 325735674 325735687
    0xa02090405190c17010e090109120e0103150302093c1006020a03050703051c02030c1b191b0e0403080411010212040603020a2c0108060406051c0f08 65
    0x8075100b00b00c040c111500b4060090551540040310f0322450301207400c0c450020700c0d0051081c0d82d07041d0305440c1e00445130310001489000355111003e5070084850343c13200255040c00c050405581c03500543d405041420f0300088018115800030341da04000500b406c80c011003034821a12520301050202d1903200b041408040001610b40401c603809404071009516080a000000b940d98800121603090a405607070311030411f8803d980482d8103a0003c20102c031121005140269140c03010320055001d80380c2e1222041c0e072040100d01040e5456a03150140c08950040c26901000d6074100c004204903560111180125030080d140f200920103850f00541c14a01c110803c001c20160040c1c0780500507030050b9000100d128480004999a0b140181d034440c3c41142484108000c1d030094019142a07074203410036080c02c40b0000c0c5902522161888040240500341624500035600b0501d1980c01c4030003614203100a504010218500040c43c030403d43e000040c171034800342840044082d9541c0c4aa101d901c01d0343e1f405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325738174 1250 325736924 325736941
    0x1006080706030b0303090603010509040c154e560d03020a05060a0f270f05100603050303190e0705010e0a09050103080a020c0a0605120a02090405 64
    0x1640c41c094076000c00d00d00821a0f01d186000410b0702c48104000300b0a40c0b8603030800c5c1c10300a0110000d8400c1355206c10840c000724201d181d2102c98a40d44902d41c1d24242c87d8100040120078040383d007501041c4100a0b404400810306288800c40e468110220170024662080360b8040d004001910301c0940f00301c038621a080c011120358084174000c031310300807603200035082c0e10524110034210080c040c41d030a12803a80c04215414240c0261000c203009006481c01c0c02010b4650074100902210701c8203419542e0844c61a8481991140c4c0d402a02e6090200b030b0b0400e01c0303024501a01d558204040e08001c40c410303542041010400981144404a000c1071107c0e590764508180c6d6608142c0d00c00b055020300d95100b15401c4c0f11845804c100c142c02d034000f81086494000103640246c1d41d00d00e0590000c0d40c030280402d1084c414000c81c1e0003180316032204c640d80d120610703000b403e08030920125803040003010001c01000d5804010b0318441c0795601140c6c00141c9844420000903c00c012a4a0b0018100010082d186 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325739424 1250 325738174 325738183
    0x909030409060b041509120b150d1109010909050a02090a0e0a080a020c06090618010203041e05030105010e090a06020a032306030c0402090a171e0601061101050412030905100608 78
    0x5d81c800390b0003c0084040110a071341015040c0a041641d901e00d90480000c06e1100701c116802502c1031004010030030584021941200d0060019145180b1081c1d9860b050309060010600420052008004d0300e030060341c425403a007404003c040d1141d0f1008012a007132100503030042c0f03003014103002250803041c0c80d483c046165410410700074015000c2c1e000340d0103c2c0e00740201220a1140001e285038034103450001900200c004040520303045200c180404a02504101c0400004140c603110804038241380030304050a40d10140c000103c40000f910a2000300340d000514100f02d164080e40c05a2100c400070700c00c0340181710702103940c3c080305265070006500703038078400480d4066802a015905109030721018081a8410029250b400c0b9640071020400c0e4000e140030008015104000d0b900c0040001d11b4a080d0380c01c000d02e0090709038102c40300410211f904681045c401c400d02d40000d06c00fa2409880d01e290100449003404181500ca038682d03801c0110034400440c00c1007651000b00016615040c41c0c1c0e40c0c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325740674 1250 325739424 325739429
    0x703050d0b1f1d09010b1e0a09031407031a15091003030f1e0f0e060c1609051003060b0303070219080c010c0b01060e0a080105161d0d020909030409060b04 68
    0xca40c007070154042d007000355404203551850252180700f00c2d91806880300c8050340b002c47e0405420416030503890407140408020042c09002d966244002030440c2803081201c184c061228110b41d1001c2c0c030030800107543e8140000800880d0300c07400c40301da85112a100b080ea031007901c102d5000a422042043c4009a10040802c0c0d9012782c0e10014100c1c182c03841a104540e01401c00c4201100080d404d0702494071411100e110308103c2d02c2c00001000c00c04003c03541c660401c49020946400c400aa83d100c8030700241141c00402d141c00080c402800d00015503810039001e800003402c2e403a2190007411003a10100202c40405034081c0c41284840d000200c4101d1580c100d00400300c041c094031801d502550322501d20f0402d00b0b90401e664020592a1400950708280380e41c801d02d4003c02c14600000d500d070000c0c4920383c4501180742c1c08440030840346030000c04a0a1400040d49445503444e0701d2409901c0d8070940301c0b08698181e07218009078503500c0c080b500d9805a64016240d10703003007600c0402c00b510840f01a004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325741924 1250 325740674 325740677
    0x120f030825050d0c020d0804080f0405041e0b180609061c0308060a0614030117010e0a050102030403091703031302060c0307062c1908090a030503120108120703050d0b1f 74
    0x60b541c120075049860385003400c58000041d0a040201380407481c249d000308881c4000c50b901516155507980480e0603114840c40f00d40b038003c4104800e0a4200340d0b4060340e1814141100c0180c1402010b44810542c010040c4c01c640c00384010100080090f2210600c1208220504040301d00750000303468002d1a02e075045a00b68010224039400242040c011410900b00003044c100c02404c581c00c112041c08400c88a4160811b190349030001c2d105e8401087c0541c03507045004000140c0d132440c1604015000000307c0c3e104981003400020a0b441c00040031090325084291064625025552800010348600078981d0310f40b024000003481c00d042041c21f034001c5144c00d07107415000520381c503481c1c1184650b1142c61039602142e0001d103004450386645c1800709003090700c22100c240c01d0640440103d035600c0b409400444e01a0b00005548100383d43c031420060040011400400e10201c02c00740900300c900034007000034213000001c1540b00840c0ba10703400140d444c3d0000303171080c2495002141c1103140d02c01c424400c0d90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325743174 1250 325741924 325741931
    0xc0903060f021c05130308040f17040801060e0106050f070f14010b0f030c0f011803120908061005060412020f060307080714090d0201111c0504060207120f030825050d 73
    0x1000e0042c3e8003801d84685103075414030602201702e1b2000d480d4090020300844810740c0800d29100001c05003400f038480008110f0783c5503100c03070419441c54215022070b0040000002c583d00100096644181100c14007520141425122070291410039a60741d60306100800208000142c440780050550040c440c0d10000c882c0b0707a105903200000d25441c1c001140446c3d40017080d00803e0001da5005044030070030000c0b46440710650b40e50ba03443e5825030741885603e0000040c034420040050138020801d1580000e440c8150038609850400000c0141c881c5200b2900350b0315100b41130906550702d1985503501a0000381c400c1e6a00d2403c690000d1030050121203580100b1a020b03400504c002084044e074400600252041455a07541c0c4c00540d41000803e40c894201d20070038860206040032407130070b103642d4095a190240c40b18240340b006424110543c205c00401030089241c080402d00182e03c5800301501418000d030151645c1d0500d8020403c0250300c9800d8150044404826962040040c581103c0b030b0003041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325744424 1250 325743174 325743217
    0xe030a1805060313021323010501170f060a0305010f0902031510060503190e0604050c0d05100911030a050d03140c030a0b010203040801111b030c100c0903060f02 71
    0x4034121129001d40c0350407031001e0000603682d88008511860303003400240345400c001c3d00161030100351040c0801207140034801d1521204d072008910185405440c0c242000304244060244044502c1c200610784401000c0d9100072940700d849075039003407001d160410028010318ec0c5010429000e861211002c07802881001c540080500d0155400c030b0180342040405460716103040002c441c0c82d08041d124a6509803000140850489544201e501c03081c151400f03480c040c40c16061440c2002a5580c042e40100c980b65020400102d010840035042d600140000990303140318185000d40340c150a507140c0d0103108640083c4140f10740000c24030000c0000d80d50503c0603144030480303860001810340d1001c00c5030f074003400401c55400c2982c00001d0070302018410aca080079078880b100d600b510400506110605d00000305100d0b401c1600e9149400c03106400c00541c6060400f0f54002d030345403002c481c81d4880716915901c076090b181c0f040c00c41800440e0054401d1050040d4025000025072046c0c1c0d074008844070013440c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325745674 1250 325744424 325744457
    0x5040c140604090b040b040f0b01030b1507060e0a05060907080c060a0909050a09080313210818030c03040f1d01060e060d02040e0406050610090506030103080a11010e030a 75
    0x180e0a5140c00350085090501d800d02200c06480c080e110a82c0c800c1d11446d84003559100c3e48a852504030203c84007140044581c800541200c0c54015802d00559485500b4443d001c3c00700c1c200e4041a5000d1800615a80e0301d14640781003d1104d1801401400740c0d03400d01c010301c8000940c1400740c85901003601c82c1c42e41c0302404c102c914401e080700040411400350080102e800e056004581c0103940e00404121320440740d5684074990300480f80e01620b0342000010100b4810b05083c602028503010040e00200c520030400031306001001440c200c1d000c0c4401c010312041c81c0080c01651900702e24a030403680c80301c0d1141200c0d2910f82c02d502940d070035400c03d202130307600c9000303a0300103181207400320785800810a0503001842116801034901c4c000450b002c02000945140d44a580c0f407046000e410005003a003400420484641c2203408610100001d0807404c0c407a0343c2d188021241120b038400c80795030ba02d01c001401130b2200200084c5250380c1c7d51900a402a404c01e0200043c0340c000480d0b81d40201c0414200e00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325746924 1250 325745674 325745699
    0xe0d02031b060402030615012d0e0a0503060105040e0a0f4d03120c1e030a0e060912061f090e07030f020103060b030717100e07030504141005040c 64
    0x10045c1d4103620440100311020402c24035910200410700d06151000201e5041c04c81c82580e075900f0702c9035240342c03028130088168032180d09812240f0032a0690911460400001e649960602406114590700c000010030508104801040c071a407000b0441800b03401802c042e001211300b1244181d441e487c0361a41c030618040c00415540101c1342103403401640c2e600c060002e048a0310080b0458041c8603015100841c58010009801002400c000402103001c480d504c0c03101810900040301031035403040c400c8050300d42d04881c1208581c03c1c1615115200c9540301c00168041503500c103445410b0080c40c050041c1d2100c07540e1491841581c01200d041800e5480c0b078071004885004421622a411034074086c270000342c40ca400c00c140640140b4020030419251100301100790f005880e0300c0040781402a41011050032688116840000e12589803195454004087c40300e003002000da004241c1d846000900708003804590070b0345040e004080700c4a841840c404600207040c19107080d24007d001c55000244d0008030031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325748174 1250 325746924 325746931
    0xc15070605060103141b0c01060e0a06060f09180f05040501050604050f06030705090c0c0601060503100e010605160c03080307120b0f030a030f14181305040201091203030e0d02031b06 80
    0x1404805c269124003900d0340d00ca51050383c0342d0f60190208501e41043c2c00c00d01800010b01110a1000124103105010500f02c0304d651740b020307040c0024510b081c01819000443c6404603a0000f0f415000d02080740d0a010083c101a03c0804440303181c00140000d10005512031842840103440400a42c0c44895446040305800c4072126807560001c007003488942030058a0a40007001d40e45094101500082d4150400c4d109800a0f400290044200589080f42c04020401818484c0e018103980d410160700500610036910303072080d03000c0b44038180703410803503010074042c0210b40140c8201d8580c20301200080c0740c0580c5a0020004500b44900d010240c58405500c50358004002c00520b110032065030242c5144050038402d0003801124460034540340c20002c0240456842a80b03444521a04801000400c140c50505408520320340820440140d0300110390005031a4032507030060340520185409c6010b0161051556202d0050490003011641c000005c0c0000c4007422030342c0c4681d032002101c0c2c55600d4200301e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325749424 1250 325748174 325748201
    0xc060406110712060c02060f012304020c06040f0510020403031209140f010b0f040e06150117070807120506010c061104050a0f0e07021b13091a040507120213020a020c15070605060103 80
    0x8080d01e10740e400902b0082007100e0160000d0f040542c03643da440c0c20840119801e03264034000e10850001c03c0402c0c030178141a401e400504508003420354800502043e10b45503400304280e0388044501c02d200c2e812030f4404103030402804603407054880b51041b07030203008400c009038006c43c1c1c40c1000a889140901a010b0b0184060000f040c2607030f00c41e044070113030300b071081c810505101441e00011440c0c8083c203080b910403960f40d00c4045d50381c202a04001c05500c020b0220185003440d00c0240015a0380c400340c1801310741c0d003050012459825900750720b00a841245c0c4125880403840c640040c1c034602c017501c0403080343e107200c04440700c0381d40b868401d90301c1e00d5252010081e4030381001c076030401da40b07804015071116a0b0b04160000341d03e01655a500544804a40c40e0000180c502e0100002c120080200e803020700002007002c50a8141c0d030b402310750101070749040d07086130540200e03004074014401c014103c8110001807181e86041c1c1080407941d0540d0140c04250380701c500306400103620354064000c1a081000c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325750674 1250 325749424 325749449
    0x20118021c0c060302180603040b070c020102101a120604050d050d062111270a0b031906061a03040f020f040f021b0c060406110712060c02060f01 64
    0x10340d08109480301c0c20500ca58500100381018008201001d40d01000741a15840060341e03400380b400c0122802501c4d00c4028800c3c0c41c10800c1000150035140102d402900a0400880780080303840107074103004050700f03040811444e00d944002c04549a02e0b980402d0714080da001c851000325034094580390f4200b120301407c290b104c08040d981c0184900c006008c0b003054401b0024000341c4490b0207210441c030101900b618600001c0210080c4404e107e03a4040121003100d141d4881ca400740e0600c010465406516528041c0160014551304415040080d180300c004080e9001c101210250720035000000c10161499850004080703003c0d2500514440310100d4054040e0842d555952148407a014a0390202c1e000902d040c00389441d0380761401a49070a80100c0700150b11000811201e511014158030414450b501003040822262141c1307044905a641a1405280f40700711104071a02e4042240c1c4000b5a000c1e84824120a01200e40c1c40340800901d42d50940f101d82d15003960080c992030007800f0b03c10b0300030340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325751924 1250 325750674 325750721
    0x5030a050c070305060a05010914010503071e0e011508010b0c030702210706080a0c08060f0415080303090703030e040c140d090609080703030e0303091911032b0201 72
    0x60024001c181e0804040310b01d11600d0755100d60800a050314204816a1100c0c018001c42e2034070b0092540d89102d41010340c450b589042c00003030f602c00321440391540c42402025080c5415840d006004082d0542d04032510040d42c1d100c2c00703002c0700700c000071140001400e40f0300007041159400c001c03070b00031004040055061841640800c0f07000b48003a41d2150650054440040e0000310502a0300c0007014140c071491003500c1c000c1c4803001a58281c041d00003c0002d00001c111059031014003441603c60107583c001201d01d000004403003510741c2070b00308207914400401044000b503000141c24041d24480d964221041c0070301c40030701c0251540b0010960102c5c22401003958445120800313894850200300e00820711005d2038403800c1c21641820810b40e001d0400189010a15415006403010203139020300442ca185030010800352190041250180815058015003003031000780c1024000d5514028244c0381260071070400e624006034040b110504032051803a08070a110300600c98400340d2001c40030151210710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325753174 1250 325751924 325751927
    0x20f04050117092515030903030c0f021b03010914010209010e0a03030e13110a09030b1b0f07020307150507061b050f09040213031202010510031208060d05010e07050f0d05030a 77
    0xc155458942001d18521002400d00d00c0e0440510300f4011030b4800040d03000a60170300400f60303100549002b05005900245140c9964001581209000c001845c160800350100020b400340005d420060a1050b0f40001403510311010b600400e8041402d0721900b0001c211032042c00160b880911001d804149607198034009418401d1162051000001d000281d05502da0b145e00c0c003a40043d903640c00003034034010b828001c11151092464010542c800000f0140c041c0c0f0229512500c03d03003041c1d07038403080c0c04a11340045440c104031076006080071042c3c580e42c60f0704d03500008000307800001c0d040c0c44143c140044404002c3e000701601181c400143d480038076040702c1e40e1070204903601140215800c0f079802c00c1000480c50301c002a00020310f200e50100c5082449044c4000d0940e10085c201c03c034203e28441042001070810b0020301000303915404d0192440d9510000540d004022610142082d42481a181203400001c80e030300307090f5442222207445404181092004041c010240100300358000c0060b1a0500d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325754424 1250 325753174 325753213
    0x50124110a05121e040510110f0106060302030f060d110d031704060603150b030304060c0f020a152007091119031d030a090306020d0e01020f0405011709 67
    0x10619803084805074200e03a80d455143ca081c4082ca164142004200384031100c0c070303d08540744100003208070a4105801d040000f500781c582c0ca00c0c0e810a20450501c030300d13201441844000c2d96040b101000704030450b84d484000e4060741c42240d58004000e099000a08a8581103112101c7c00c0c0c0c0041d08a00b015441c1c4c028451700529009040c0c0034030800d00801e24245d003201020714400c500c5110302040c981d1542c9815070400d000342009604503810324048006544001099500b00c91261034500ea481209040850703440e2100c00011b9000503805201040083c0340d40d210155002c260380d104200c407800120b0a01c5002d00f0081e48090503004400104220240c68200101d81c20320b18107140c0c0340040c1c440101044201081443c80426298204814200092583c40c50800b911002451030a461280014182ba6843c0001064582e02081c500554803490740042c032241031060085540c1d12019240072525005413159a000070700070055003000000700007541e4092003502c8010300400e81c15005c4032008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325755674 1250 325754424 325754447
    0xa0308180307140f0d09060f085214070203013317030703230a051c02090a0909020105070807200406140114090402070305030703050124 60
    0x340d200500408020031804070038403031421518070052140c103803145030031800c013005c90342d02c2c3d010b010110904000c05c64102d0086124180d6514011b40241d84854074014010016400c1610000c545240001c92803141010111003c40f0411518441089145802d00d0315040300007050004014202009106c14407502800200f40300a00105a200e02419031171850700321208038800c98803081d40644003444c10303403000c0b4000e08010100100c1071045481d800d542c0780f061500040030406140c1d074044841e00c1d5482c81c10110b03101c031429182c1d288402c8900411542205030440ea0940d0158a0a8020301041c402c60340300140c050b0051829500c0c1c1ba00160003010f130004117a06100c8204080300001c1e040300002c2814500c210060800206d07100f2804c04075401910f40140a41d181007020300404072842c4044400341ea0134a0090f07001b1003156281429401041440740d0000d0001c1050010990407202851140c04c1c140d070208a00c1e070742c9184141d06402d803080300415000364002081803403442583c0f400702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325756924 1250 325755674 325755721
    0xf07030212030c2b0504032102010b03030c0f0c0a030f02060a03090602041502241b040506070302060108100903080103021005130602010f1404020a0e1308042301020a0308 75
    0x8000450b04650b08201ca241507034120b0392034512044282410300450721104d0002c0c0d1804506080c2503544500342442a424015550302c48104540f080c3c074030075000f5902c005400b07070542c0c5c0c03101c1d03000d0032044d982c229141c0c10900d640034070500f0324440e0800f0b0450104981c0c0142800050f040d4035000d00040b030317100550101c20151500041c0000c5042d5000800062015001114100e079041e80b00a042c01c02c00c529200850000240c2c4284c6c04000248079500710025032007401345280300405ca00c14a10655101e07036045007000c80c00d4801d050b004580741c0d040701c0310081510181c9400500c6042194404034008003c604540300610150400740012503900580742465071505000c5070500c42911880e500100050b0b459240111148800b8001d42e01c118110f2070280c0040c0c01c040e80020321410540c05402e5440701d6640000d02050810080e40d8081038006050b10ba0719034440949c004146100c0980b90104601200d204500354030003d141c0350743c59015582c01d501500d507200c04058212410a030023a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325758174 1250 325756924 325756927
    0xd02150a14040b0405101b021507020d050a03140a0f050d0906020c0d0210060311090a1404050604030806090c1905190c0c0b13030b040f0b0112060501080f0703021203 73
    0x20003441e00040019180e00414152524904010071200411440c4036004010507502d4110307072140001c224800c02c50781250344001e0700714640b65400c668044c04002030b5101911001600500c60003090610400d40680d464599410400c0440c1190348a0020640002500980d03213080941c41803000c0d200c1e01c018600c0208000c00300c0d480e550180e820480f0017001c1741d0402c0d0010048990100000314007582d6004040c05024515250003658041450090307002d6006440000c298500c190702658003d2030708946910681440c2c00c1850b034504c801c40d4201c0100b80908081080d500d084c1d403e4511480144201c1440c010384060121200c1121032450800e00405001c414405090804441419900c0c0d0351892035407c40d50130401e5541100b58000c103a407900401404109102a843d000700f40e83e000561320130a034072507150840e0354a800d000c002d42510181d0002041840000d480d0a4240e40a00300500c62662200070164603482c501c160b00030a40d01000d0200b005041095031041c2d00c80e03074801540d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325759424 1250 325758174 325758197
    0xc06200301080d0e0301180b0a06030803040506100e0c0d200c100f02070201052d0d1b030b0901270c08040311030a0801030807110d0311010b0d02150a 66
    0x400803a0030a80186009802150410f040e403540000c801010790300890092281c01a98441403010b80010b034400361642d25008001101086a900700c10001d681c8254a15524680360606940381c5200b0384022800e40e10442c80082c000c91030344102401180c002076050300d040319040549009049090350750700312100e5000407c165182d000043d240340c004040c040d2010211409107003040f00d40f100b2003101c3d0140706010305c42c00b50341c0c09811368207602c800140d100d00c1d84216a000c035040480038144291f00c0364000641154403951600038140000588030700328806803001400f5002d43e040102c0031900554000c0040110500d0800d40c0500d565141e500040700000400d050016140600d19080100c3e0301071042c00101a0702401481c0c0d12031030180614100b62041c2c0c001880c640040c032020b00107503008941807060207100c403041c0480803002410000300e9000c0d440d010340b40042e401b59413006940b92195045d242e05000c0c03088058260300400f51001035240c030841e0546600000d40510401001c05240b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325760674 1250 325759424 325759481
    0x2503090210030c0f0c05060c0f0c0102040b04091812080703020f0c06150a03030e10120e06010306050c07030903022b030c061b02030d090302190c031109070c06 70
    0x2119540e000d542c000c548a644081d02400c00d4440c0311440d0f0070000b42400c001d010410104101c0e410030000c0e490180d84d001c2102202c01c0c04c2c080c403d07811080d03520010740000c0001c1000c00a104403901030f03d003440300c46400c466092685d148840b000e000881e150540035480c5228a0320181d01000504006060054400e4095215040a800301055a0080341840b50b4150000c46880e4170b0300d022500620f4044c11903400401a800c184038241c06001101c082c3e03041c1c80c0c00358900c603640e032102c90404c03c80040e103100410b0740c450080c0301c15100707075107024041039000b4001021508055010307214241400e20315800e104031061445158403c1c0710050031140c00c0e51500b50701c8440c06501030b95828450b007240e414035100700c2e6100c8010300940700315205c2c401d10543d00441071f030307503407840c0d8840c00074010b0202d040581c01c00b852035100240540011140c0001c000d00740b20301a003a00d02944c403040c08040c40a080c419400010758031140070030340040d82c45000031415004040c00020310102b030704600703e00002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325761924 1250 325760674 325760689
    0x506041d030d0e030a02100c020c09041b090b010e1e04060b0315060702011d0a08061609090b0d1403040b07060209040b0301110307030f02090607060606140325030902 73
    0x8485003a040054000b10b80301c2540104203410200002440c60704560b068040c0d80c80c11606203200105440309030039a8624000d00102448a2015100d80340310314040c40e00480e600304008150b00c4034500340c1e9010840000c284100040203806031500002004ca010801c007161044850707a00c862905007900304540e4603140a040000c101c7d250704152a803c0030412070608000180c1c07080c1c0203000034001c00c0007503070307100c0c00d6591482d45007046003060241c0003010406000d400d802000c11445400c060100b20740b081030800c03109194994401c65080e0702e034948403051340c0110101c190b0126078081700001040c440d00200c5200e04014044a00d025962680409607411481c4161000b40e804202c1d0000c0742400e001d188500202240200700c081c0c40c81250034440c0c0000344c460002c040d80c50484051040659046424002000b0704654030741d5481e01e0306074060480303030150200044414480d9505040180280d900842b030820000326040382e10448085600c054501c400c0400d6241d92448d130240c0c45198 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325763174 1250 325761924 325761971
    0x703150207050d0e1507080d15061202040e15010203070507060f0e030d1403070210050411030d181401090302040c030e07080d020604020f0a050310050a060e0603030d050604 76
    0x2a009038489a842c285103042c50b11090811003802070590031000c065a4003c0442c882d200c42042c82034403010745d400e04031458095000301c010501e10b41b0600911002225111800f15009903a8445215011b11b010000364051840f804642d07141d0701000c56081100f04041c01803a00e81803048a05107a010349403a842e220306a8440c40c04902000d96a480311644051459207540c401e40040c80303800f82c13290b8010102428042011049076000c0082030341540b003880380301c1d0007042c02001404981000d003407082e0010002c5030b2851080c0300707003060426140d000c1d0002020207441074080c0e1400900e0300251000d500c0d00000118100700040340b001c00145e5462040501c0010719590020304105c00781c1a00746080d0132a001013026522400040c09240d6000848560155040d0754000110183ca070204901f4911030304243da05015184001c6c09110f001d90089101d8090714200780243c0f03684045401348400c00343d0b501038141e0020004007051050507000305411200c040e0001801e0661509070f140400c441c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325764424 1250 325763174 325763213
    0xf060c03030709180c081f12031716020a0b060612010b1b1c0e0414130506060d12030207151e110a090302090a020c010f05011e0b0a0e030703 62
    0x4103001d01840546024580c448544e9420402c0320070b8803e43e01034021103009000c180c0e0183c0f1a0b042d0844030300040c0f091402448107400f40000c40b070303003441c010b0804940d0101588440003090001490303075010345c24880d02041290050540c040c803c4e12401c10044004040503003000d400c0100300e542c2162641030728002c12040c01c1060303d0f002c083c11084241e4084c505145441e1b882182c2449140490b000e45114000081c100174004550b8840420b01505211508086250040c1d0070030004803404081048840d00c201c0640d40c03191381711001c0088031105020050490643c289046969a002e40e005003151400342c0e06801c41081d9400b01401502e0176480b05446110105200b09030b002014020b1190803171080c00303440c0c10450003080007080006a0b10000e8800c0031b885012030740c801c0300759045606a80e00103000340310308001590795602401c2d0070b1080c6001288402c12035442401e41d00a40010791310240c00c8945080c103102000c650704943d900001c1d62600580800000180b00c08402811185a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325765674 1250 325764424 325764437
    0x702011416120c02100c09030c0603021e130504050702010b0d0302070f0f080d03091707060912050c060a24080106090c0f0f0f03090206130306060b070209060f060c030307 75
    0x80e00001e14001c4084a100200c41c00c00d10694000ca4022618040b017210b00040011074014810f011100800154400707014501159000f00700c480c0c0c9a0000c3c90350384194080e80f4403691800e01c1c010310303501c40c410f00d110041d04010420f000301d2a10b90407507600100a880080f9040307441e203002500c80000f01c2004c402681c0701002c00c0090700a00038454000b043c10807440c2c10a41d1a0030442501c501c40d4504990406681342d60383e400300003400045141d10f17600c203004203840d03207100d1902d100182800001514540648884c1d005114400d2086501107080c0d02c2c007400d015142c00c3c1d401409011141e80c251a00040000d42910541070710703200000410300c0c400041440d601e4888100300f1292000e4001c0c04018005040c106405c1c0c0080040060524500d04407000c81c02c41e1800700e00509640c04000c0d4800800070b10031444003072a02072203090b03d015040c200807c80d551007850156200c1c941d0025000051140056003a1034076030030f000c00700c400c081d00440ca0700300c3c00c00c0d0746400c0d0751080320410080b0380d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325766924 1250 325765674 325765711
    0x11808031b060703020703080c072402031f080c0103270b0406050604090b0426041508150f0d020301110a11071e0b0313020307060e010210020702150307020114 70
    0x70040c450700103643d81811458400c050310020007540b0005c264842207080003484404100c4481d14034090f00614a109810240907280102c000c1e41c02600d44100710800d01d95801980c5508000398021103d1b10300c02801400c28050054014020307140c545031402c21800c461884140c64034940114040c031a014501c0c1c42d14003031806004540000e41400e008500d44815400056554103060703802a402c442441c1c00449500a0001e449040e4050004104d101280010f40c540c05071000b144e07103040715100c52216690305916041211200520268000f00c40414000b0900300840740884180c005800850310f01900002103c1540c40352140d00300103401d6200c800325845052080d0405802e81c01d016510311401c07800c04e0805444c0c13038000c1031101c40d000800b082e0f00d01d00d09081c40035041d03409001c0da03014a43d9604083d10b541c4a18428a0140c000c2c01400c269040161086484050303004210501c0140030703084035030164100a048405565032052a4401220035200c0140700f41281e0b6009040c140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325768174 1250 325766924 325766977
    0x803100303110604050703020d05010e01091a0a050c04140d0b130210030c020303071d0d0b01170307050709020702031f0204050103060e0708070f1209050705031903090501180803 78
    0x10042c2030504032a00b10301c003440300040022a4282c212a012641e0100145c000c0c185180100f009c018042055071070b03c110b80c0200032460001d00c1c40c5030300080c46924140e68140c401420345008455a0741001c10030002840840900c654410340c040c4007a08001c0c02e4040b90361090191a019249188101301800d450011440c0c0900d50726007844540c07070b06100181c01e44001a41d28003001e0184403e01240c03802002c1c10044c0340c1c4c03040701c40c0040242407141011803400d1030441c008003030040500d0036070441e0000c50041800000c4980c5254480010329080e450010107400a400580d01240d15004000301141d011400c00d40808101c441548010303600c0c2e01d4503002408542580d48480b0b0380000c144108405c15801c00300d215441500f03820800c540c0648100d0440301a1800c0119120903440c211020090200000d030b04415514254225400061a10700340c001c5914a003500a0002780f90341010300995202d06c100445444411801101c40c5460b041661704540100c40140040640000e0501840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325769424 1250 325768174 325768187
    0x909060b0c12040f0b16150b010206090c0d06200a0306080c0d03080609071101020a05090415030b070f0912060c08060105030907030303020c0307061d10060e06010c020a030803100303 80
    0x140002d9805403505140800032030040f00c1511980c0e0782c0d50800306052580b1100c0b91120350195074000d60b0000070701c030005034040c028807526181a005115180009426020004043c14a900024015512044070b583e4650281034105540007030a924041307142d241405140c040c040241580d00d0204a40c0d0070710116501c0c3c108412440341c480c0301141c924401194000c40d080790010001d46090b034440d80da002d0305458841c001c0e046084290310004895643c00d604c5800380402000481d42800392401010703240220300075500010340100c84140c0820801401070504803030303000359030038004c81080d0740e41000c22044003140b00944452b03442c1d50034807030132603070150320660712101c2403c3c0740303040d400c0600465650720f2841c0002024550300148580355207004006441599510035810700180c0000800c40d0a00014206544110f1107000038003002c0244c1c50040505541c285d041079015907942c3d00c01155400f5010350203030f82140b00e0310360100100c1c1c1101e00461040e55451552070a503403441c41c009100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325770674 1250 325769424 325769443
    0x1e05030c10020a0e010c0c180b030105010503070303140307170c070b0a050408040b0f0d020d320601031e06080105160c02030d0509211b010c0c0509070909060b0c 71
    0x51078410010002ea144e0070190840121100380f80c540309540e100d00d00038480b5040c680048003e510343d910700002d0011580c11040d00310009400030310859a9a809040d41c4d80141e020003000704d00c840b8140000904100051a8805c0345071402141d4400c81040840194000f6143d10030203200c0040c240c400c5c0031402e4030060f04840702520402c540d14180d143e182c400d0096005803c4030100c0054034601c00103098040d100b00442c4458115510320840181b4402485d1818104600c171403c00c5994919a002ca19110107069064800c0c4000f540d904004600501d102c120248006117402c0e00751034040c14520451000c2c145000000070141080d0500c040082c40340b01c40c1c0c000f00300100d40c0c02c0e00162804642c0701c0420900b42041e945483c103c1c1c0000c1e494446524040c401703460f0036101c0c00203180300065520540911160a01d000c0010783c2c004640506400c0c201a000c1c500c241c0b81009603003800000e0301e074071658070315001e004240c0311070000f03098809a07400000dd400b80071589585072101441802c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325771924 1250 325770674 325770703
    0xf0618150c06050705040b0309071401091202040216060e0109200a030b07020a020d150b01080606091e18040c0905190b03070e1f050604061205041e05030c 68
    0xc2500d155401000316580c040e00400550b140c201203500035001d40c0c190303800341103a51102070b202d00e2304402c1c15944900e80e114040710000f001d07a074001d01e54000c2c4000801e407400caa0ba0240d5280c020303000c0c440650702260742c40707107031500c014113100204480e4455010500d280c0b80020036040030508100700e40154071000a034601341380900c0c0c20f88581d5420004000c4a91150002d00c00744e6801c0c2080e403d02c40c480711701a420a111400b800100540c01605860b000e10003102088085c1d12100111000401118241d80051040260b20024504000c603d80d030310b4800b081d448400606000401c0151118401004d4002041024030017082500343d107440c080e101c0c1080401841c5808003600103011884180ca090300c41c0e2721102d9210711f1b00e09208490142040003800021420180d081c42c2c41c400e10086605c45002d012100806c05251007000c48084909564500303e0080500d04240d0041c82e019108642981d2001e0b814400d40e1000301d04200110b000740061526840480e520908000d040000510b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325773174 1250 325771924 325771949
    0x5070515070f020a0803030126010234020604140a0b030f01030b0c090d030e0f0a0b0901120f0e0307030f0f020607111e010510080102030423070f0618 66
    0xa04030103400948140580181d0256002051400400d09542c500d8010180c107010000010410503030109030030715010350541c480361070709514030401d0b8201d004404a00031040010303843c0da8030000e09000c2100b4101130b5518074502100c180d500041481c3d000780e07c9036501e89104280c1c000c075440c0610681006040c43c01c1c0c514694a440c0a0010030440140801400404114041001080300c00c0644600d10000b6119074000740040c00c0c050164030a940050348501400300e004803107030504450080071641d60454581c04c0c5400c803c0107540d0802c820a4008000783d4549500324542100d002d03ca820501a4001c2e5a41e0612400d004006203800c0c000ea106110090807107680190703002805039884601c604d06406d40995850f089420010b81e54822042c8440e00349249a00c4001075100744d0003411500800544030f80e503a0300580c01c0c3d000803907019150a0000304c4a84582000740203a200c003a001718203445040c2d4564141115181c0c1d41d801400025041d41110010404490110000b8008041388007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325774424 1250 325773174 325773199
    0x302010c11041e0c02061b0715110306150901080a0e030c0109060c090506070507030f02130c1e090e06151608091504080615010306150e090717041103071809050705 72
    0xc000f80410490300907046400042e2365014040c01401210401209440500082e2120058620300b504250341039841403c110540041741940b02c8121441c1100603100c03404181d6909156000410f031035581078403180820803a1030140341c400c1c1b00b2072514501c07800b40001d50015107a0024230325249508003d02501c0d0807c510300c08518002807060032690300c0b08844c149652184003081c1c0e984441c020722030216040c841d0b110603441d040810001c601c0e441905a078a0b00d410240e084072110124806d01d544424000d0114000e410040c061955400007002c41c50301d002088400380c0e4000d03400580503500441d001c01d070184185445158000b03440f02c50900581040e017024290398980c4409480c080c000b90340c046001002ea406500f00380c000303183c0380b04844501710700c20001070507002812000500ca03084800016450364081c0010290840026040002680d2640d03030704a52203c1e01c022095241c8074422000450603a0110340c0c031011801e283c8003086000d810f1034400e1529115803c035507c6000c8010b80c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325775674 1250 325774424 325774441
    0x903030903060e070f0902073804020d020d080301080106060203040e070302030402120d02030a021002030106080718080d09090b030d120f060506040608090d080108070302010c11041e0c0206 83
    0x111015650010000510a05600384544c40c00d2020781c001c2e01500c07046000001c00d00d07030031b0380074008172030080c0c0415040c14092201002c4101c0e00c041c088519800c9040e64010a0341c845c40c07210b5000344054403000e452806600050b03803140082d44100c1d18240c0020040c0f060000a0146100529041c001541080d080c41c20002c1c07510070041c0311b28101a40400004c06542e1240c000065050462003074545004010303000a440b5032003561110701500c550f180c40d028160191003124100c40b29655078135229180c905040760100c0d000110180312400d085008a01c900c014800320704500c11644420503c507240804d000150f51555404a2081c0c110708018a0802d805c4444600c07078460b032120004449050600f010018051504240d8203e00041404070358140c003d40380078010b448060848000d400040b40445d0290024068040c5941040c00108015409640e607811281d204508026948484e203020401711058014040b50402900e4103103691402c952040410001151003e00841d2030604c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325776924 1250 325775674 325775687
    0x1615020601060f0203070609081801080f06010c05151e1311010e0103061703070b0612100207060204030605040b0a0c030e030f16120801030204110901170a0605061c0c090303 76
    0x742c0c8007402034444004922a10a00c200d84606510040800400b03004d4104035106400103075103a011640b14081f00d0031690302a2003050b10420009240c541503565000c01100d0740ca0142c0000c407414403401000b00800342800310440c0c45003103907540c12030b000580e54091008028001e004082c40c980d2044040003ca0700c1130702c1814040c20300382080c078950800f00d801240140303060b500208101040b485a40d6004c0c0c0044000c108940c001d038000c0401e07880701005c102003056402485030f1b1617400030011400116480e0040c00d03290780285001405c1a540c0d48400d01030305d0301110212101c801040070008031031083e120780a880305a40c502005206900c001c055520311070006494511000420180035400003001c11202c140d6000798030003a1200d0045028241034020301040344514202110010950010b4050f0381d4801c1e4142e4442c0c10600911220707100f8002d01800a562031030b00c4075000b0030152503880050a20450f40707480c44202005100042d022100c0d50041c0c0c0c41000840031042004c6948841c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325778174 1250 325776924 325776929
    0x5070c11010504050301090c0905061c0b0601030f02070302030306151e0c01060801020c07140402070c05040207020a08060702030702031009030c02090901060e04081209070e0a0b03120c1615020601 86
    0x50400640c1280c800050382e4900881d800190300d907003404070728000c0024450080d401c4607a40c4405100c2600c528041020203002030011203809107802107048003107410b8804550300114181400501c8008a4070391205981c09401d00390056800041806498101030f801c00a184646465980c104010b240c0c486038200004c400c0c100031600f01050110b1588030030f610580041280390000c66990307010ee105c003a21000c152240c1d00b1200c007a2a90000281810f000b1280c00c240c2c0311158401940c107000805c4000d40103903c042ea04110443c50208165004120f9540160820b070015500c900b0389104240c40c040c800c00c07004200740d080603240000280c100c84070030007035a412200c16882d030f640e001c00540107010661000360382c00d40e08000d10061000c42c1000340420611a01c03030300a00e81d10310f041d443d5150030034030a0800e80100e030000107800c400d145e8400580c260000f0f0036120071a402601141c0940c200c04040141600541c01c02c1c000d41d038002c05850f000708005224020906444007019481c1d00c41403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325779424 1250 325778174 325778183
    0x141f030206031501050903010203130c0e0c16030210050a0515150a080403020307061803030c031e020a0507080d0e0706020708100c030b2e02010b03030403060c0509090f040c0905070c 80
    0x4000b28a0380c00f9501b03503000301c00080c0c002c644a15001010703955000c0c044174180c0b0350603050030300803030501e0040341341c10b21071950501366a14082940c105019101c40b005415011030040c003450614401030f501880e406500c600401141c1ea0406c600180707402019003980074840d00e43e10100c0c4010340100819200c0d00822800c0049265456080a07825840f40010052000d443c0c1150410680c00e075036524640c00c0d01940d4100f16011084800342e00302c0f40c1000e0601ca25100c1c4144140d03940340306400030700540788a0b00c0c0850511b011581d440825420403031420318415168007104407518020000c51000784540d00c0104009458002c0b2a40c842000f03844091030740303407a4940e4805103802038010040c001c0000e401000e21952004c600048010b82804998441042402d00c4240d244140500d5401150007405140780c146903980d0740006203040c1d81c0e25814800c00f84422600c541d90003070224420080c845100100340341c40e281c10186001c554000b8400c0c64074240034480b061b94440881d000c4507501c0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325780674 1250 325779424 325779451
    0x610050a0f030204150e04140c04060e0402090423030403111005030c25030509010305070f050909090c03011107050c03030708090f1809010905120306150d0609141f03020603 76
    0x511285c4075001c0c0e007039003112112080a000303201c104203035a80903d8814000c2415038140040180030407056450078442d84401000620218000d4070f0706610454105110303208098030080705940030340e038101a40c0400501608049010401d01007600c0e09018405001c44402041407100340000e00540006020000d41e2540455248ce900507071308100000b10490300c121900b0b15200740f03070041080d40a2041180003074180310200e07075a180103500d460200415615a1424540382c08148094a440100719080a01c034104403c026511f00303210315951150820401540c4c1d5159042541c98411004d042c81e00a900403c14080420101030658450f2107044070407a41c0101440000341e5541c2c007600f9802d15042c0c80c0810700ca0580030540c045c0440903c074030240e50001030076161603070071070004452464000c7e6007640d0303080404070340e80020440086084000500d6a0b1642e821204a4289424413000740301b40506010b507000d00c5040e001803104541504040c114191343c0401e00a0202600b0540c84002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325781924 1250 325780674 325780691
    0xd0503031b070b010902041e050f130b0a0b03100618170109051e0708010207020609090919030201060e090105150603090a14070611060c0702010e0f040c020610050a0f030204 76
    0xd04115141c454028040e0f98055844080d0350009500900c21000c0300361414000c800c15802818000b400c030340004241da0414000c05007800300c0d82e41000141894640ea0f01e60700300940d038072004038a014100c0550079079280d01d0a424901d4540c9c581d81c000380c0c03c1c008008000c000c003000e11808841130718014844080ca01d0700250b100380c050304c1c400d0320003041c4d4000c148052a02c0c60000210384400e01201c400c1364080c90382c0d034404508078402c400001e500500104025041030412402e090b412030b03040e41c00c85509580300c0d4840c40c13280f800300743c0c202e0050351151070801000d002900c0040e08039115000030401402e0040c3d455140c4c00c01d4500c581d0049101100017119500103121f8000403542040c600074017070781c08940740780e02c0d40e03c41d0051402248000302d241200100024a6170b20131800d00036400d2800c481c0740c00544261806c090002d6010711802e101c280d20b40c45030300601ca507400d40c9400a03c02410034a250104034422900010f001e16503d0708200105c0740c509004c80112130301910000b4030580c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325783174 1250 325781924 325781971
    0x4020f0c0706181a0717222312031209060a0c08060906040c050c010e15070513120c05100c050105060f0d03030213091d01050c0301050904060209030f100b0f0d050303 73
    0x2d9030000d440c050950007180c4010a6140800d4103100055000c03034104c01541c540380108030343c3d002c400708c8a5a8410481700c9180506200130403a480f90718440840e803d00f00540c254075401c480480d07200a86400601c14070100d84010b0098103010a411b0412103c1032414501194004800501a13846951200442000c1c1401101207840c0039200200a004a41c441128607a07501c58017480b8080d0f82d00b0210003e504503200340d090343d44010704903c0080380340745080c02c10100782400c10003e0300e2041030081c0000c0c2c20f0f5100120419410840d4440e40c8256819040860031a0344c010280340c00b800c01c402c5d84144d03a99a906102d0f0300f06605040c01a1158030064841c1c0c00c003c040c0d0000d9030000c0c0b800c0c1c440904600c945103c15031801143c0001e2040d40c1d0346003d25070143c0003c0c454039811900103000b00e40000d40039005403440305e0700501107407000006030812514203d0b15544c0711841d15610001e500850501091088002200fa14090b21414041e910720343d4900c0300070013400608400414516071503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325784424 1250 325783174 325783193
    0x140109021302130f140102060a0b0d03050f0d050103230d0e10020f030409090b010b0910082d061c0f0210020f03030c030a05060f01021b04020f0c0706181a07 69
    0x1440c441c03010303601340c980750b0b400080045a001d00041c00b620541000130401311440c018050310356806001c142404000350341c01d80d11f50300800e0801c034565409100704200c8107968030617240203602a903502c1d64483d034580300c0301041200444c90420590000001080503580110f41d121440c0d0050310380580000000404905101c010300b00d00b60640000500040c4001c0c4c1d54101d1182d2501030f846088159982c0c00c0300352018481e181c0360700c0d0412800404100082d000e8410158004c424502d00d09120300c0e030b104110200d2080c2454220040c1d203c0040c00481d040c90080780c481604800030940000c030b05515405110025410000d00c9100b20440d040b4203036100b44525207140350094116030702c904000c0e0800c1050b400803207107a060603190000045841c60400c4100a5031041a005407800341c24114030071800c11040e04440d50015020020045822801c0d8024070343d0001d544064200f0700d040940040c503030110316002c2c030709245200c0030502803100c10741c00e1a0301c00307c14042c0c601e0751240285400e01301c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325785674 1250 325784424 325784429
    0x140115180507080f0c12090d021e1507170a0e16060e04020f0c0d1115040f200a0f0315060f06080403020c060d1a010503070906030905070807060c14010902130213 71
    0x224a560418884e4554000a03015040105a000d440750a01060031307098500c107850f074620400342e008464440503058001c2001e500335a0624008a10101108101088400039180346c400c2e51360320040317910320320010712000711080c40084081c486c0515000e07002304042e8610101c40c1c4500c0e80011200d03032542400f0212440151054160b44034002090070107001c21200c1c900040c51401020980303090b5545030b80406100303a07445649402e0220300b03a11040e4000040c0d121091468918004040455035428800301c0149480071001072164250701d8400000f520101e0000401c5040c1a41803204115041012041c0e138500e14040c4201d64460074124607007000c3c40296600130400203a1135911403615007140410680c00b495100e113040d030b0400111000d120480e80e50000071f40145042c03144074481c0c2c00c00c00a2600a2040311265515044400c0c100552580300b400800c1644804004002204071481d40c0641461b00811035006150086048203403841041d01e54a5400240045031000c00050f0001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325786924 1250 325785674 325785697
    0x60209130c0c0501180b0c03090a05031309060b0a020c1e040609020702010e01020c0a060c030c060203070f0809010204031203090204020d2904020313020d140115180507080f0c 77
    0x207800280020b841d105000e031040e5907a50030055921008240d81c80c0c1600c2a6912680d80070895031081090842c941010b040b01c0101c0c0645065103001c24002c101030107500020b0041e0300307aa136140c0710314141100d039140e000c0c4062040601445420726000308940e03115050a4800d8414021000b564507820441540810b901c10b25100001c0b9442c038140c1e004e8028103100380c0303c1804250240c0010b984da854903100c900d078003000305032007400041c0c46480c08580c0c02d4031a0030301c00e040c1c2819559000503a04116405000180203241c0c40802d194005803885c1c100241000851505082d512120f40e50900119800d05140d1146c044c1d034110349a41d81224200a200c5004000801038007001e001c0a41c2c00b0181072041c15541e04126a41c0d01d080d10880c3d009603100c500002c1c501040c1d07401d110001c0c3ca03114003a02c4030383d000700100c0310b0103e080c000d003500050300d220f445001900300080707154402801050b84410034034107070400a00940140c0350301c2e0440440201000039039036188030301e0b55030300c181c554115 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325788174 1250 325786924 325786931
    0xc04050114100504230103050c18060c0109020d050303043806060d090c05100e2b0209130b0c03010602060601110102040902070302060109060e060d0803091009120906050301060c06020913 82
    0x2483c158005d90000c03000400740e0b001d2106840f05100d43d2001c2c0654a06010042040911a90741c2d190050003443d002d10f0060000c0346d035005540000e1403801c020141a950fa810000420040014901030540703034103c10144140d09010540b440460b451800b2b140ac018082140085881695240c0682e104100c80c010103000c606080e10700480c0b00a0315208441c0143c0c14003110341c903142c2c000d0040c1207030401c02500712109001c4120f0040000c500d60407140000c0c40141580b000561118240f06203e00c0c0b04800100d410324003840d01954010006260b071000760018001802404c3c1e022404a070000001d190601943e441034030514024451b40d84203c0da03151000408408264011800c10304980e402941000b00ea50798903074415103190104e501c1a0f01c03000e40100040041e5541001c0d540191210b4212402519081140d8046a01c84003084e2000701c103140c40d148005500115110285c5018a003441c21949403070300182007041c403094001c2010f074000c20743c41c1c01501c3e242004010f00040c1881030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325789424 1250 325788174 325788209
    0x2c0603070f091b0305060d0602130b0301031b0806040809011116150813120f03020c01090303050a15051f0c08030106090501091202060301030602030c0910110c04050114100504 77
    0x40340142400c3c2068034405080c0340d80402281d000e44100340c0320b40c0340500003030340d001c4442d41d48500941c00302c0c03002c1c0260720041001007115070041020f54007952203803500307407107429042d11002c3c0d20310010b071b20205141d4001020400020100c40640b111081b007824400004105103140b1410200501152514075855910004c0c0510b1555404141285030b616250300e50f4403495403403240c1c1102c03a90064014004142c013100304512401c46108072601e18900142031030b20385c100c907900313440b004981a00040d0719441804101c00052203548014001480d005100d00c1c07400c00824072601c818070514802c484245038070801d00d0701500094010707560083c030b41513682d07131518001b40282003540119400140468000320301c0303003e0040e51805032900201228250303880c50340c901010b98001419820041002e01c21440a0b85512685010b511042c3d00c40844010400c2c0b81075203811a910300d030340d2065007094010050381c50100401c84010000b500d042014040403907080e100d91190380e101c801c00340d001e810003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325790674 1250 325789424 325789439
    0xe06070f050a05030a0315121101230d0f140f130203060f012111060706110304050109020f150306040b121903030c0503010b16050c0301020d020403020306012c0603070f 74
    0x204807100302901c01f0494808100c00444884845004002c50f4000200020000c142c80c03000409508105151103003615111180b114060846002c039102e80c42d41c04600c001036000e00d405000132a00e0740c001d08000c403080004415502d004060000c07952440c500740801e83e51080305020728805500941240c0d0a801d061755454250307142441035003261115080060300381100075201d2010319030031501100341c0c8400401046129030061104441040d07540840a2050f616280518440c5014000004240c0264014081168490000d41380302d6007188070b508000142450075690844010b0703a001403100c02000201d1081222456501580d00c0361421100085940c00b00c000c076040e10a0344d0601180340d071003c2c00c2e19180428082c1c2c1d4400c4009100d4202c000201188200d00c01e80608200c8203021203c2020a089070b101d40034003a0466000181801582400c100705130040000e48882c04018019900c0c2d4158079480c031032390246100086011407003554082110a01402e0320301104d801d0941c0d21b4a5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325791924 1250 325790674 325790677
    0xa0603411b040b130509101703130303031407030b0321070803040b01090b01020a02090106080702100e0a03020705090705041e03080d090203010c03110405060d0608010504110112020a0e06070f050a0503 88
    0x540f134490359403514085210b0810f468441c1c01907201222141d460b41c14401c0107400c40c0a0705d00c3c1d002c05880300740302c109003042c5004400e400031030190b01d00103107001d40192038400c00e2600504203030074141018502a0b2035240086d50715010301c0d0b11800e518221514018451061040d00d901400300d46002c01880144806409014102c07070981c1c104100c0b100d40318005903202e25071104046e52245894004005031401105910f600c85c0c3c0f14414ac0f07602d42da444051004807005224a10825886031a0400416404201081c0909011902041c1074903000ca80280350303200d640148080c0e9209a800703009991039100000c1c000e5984081210707207803000440c205000340041d40c01640309600b400d03c4440308a02a224a0b60248205a0070528150a007014401158040511020003030b688001c0015254800c2c4505401640f140b00702404285101c0001002641c01c210b40d070b00c820384100055a8800e400c10040e00001100f40c5404e40ca0765038505001ca104610a0800b030428000c01001c181000404070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325793174 1250 325791924 325791937
    0xc080414011b0507050a060306030b0112060f09030201060501020f0f0d1b0c08010902040f0c020c04020c0312010b0d05010b0f090d080c16050307080a020f0d050c0a0603411b040b 78
    0x80b1b100144e01c1e40d03210114140e5880b840050f00410400d0b0041c801070f410f0754045104c060007a440410304003004582c5100300c4141500035001070755a40024005581d040c0082495000c501d0010501c600048008a0311081c401c4548018880c0c500420505481d0a1150040c80e80c0c00444980c4c10380d81c0d47c00c4242c003070194180b040340310358507041e0300c80b00c104034a00c81c041c0010700c25401825021101c4051100039401344641d02182c1c402805001c40f9003814249075406070a60b2007086440c0c44041074074400381c60042c3c00249198070280469100540007906a03207480c00e088070120207039805400e000714644a0924141024066aa4140116409a048481250010341c1114440d90365040c000d900e82180c440c00a6001010325142c40f0545003580e000c0c03807078900450690b1140d40403d00012600089540403101080d100c50182c0388034440780d40f0007580d102c0001c04004040a4141e1000da0018070700b400005908003803400309002c040d01b000c000c0d03c014140da809542da191107000f006440c2d0800e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325794424 1250 325793174 325793179
    0x50702060c0c03070b070909060902120609010e2805090619020a0504060c08041502060412090b0d0c0905060301080c090a02040303051c0f14090c010c080414011b050705 74
    0x101145000d1000c800302d8403054405805181044042e82e00c50040a9020b040a0100720303158402080510151007148000d014070f50f80142d07600240e04100111f40d90090245201319407500c0100401b003420310840360302c24401031a00840c541102c002142540c41d040c00703411400d02d003100308079078070b0300009030540209181d4120001c1000d988a10109034401c500711000044c20500003086424021540c59031618814801142002d8540e100c41800849015050006912a41c1844140700b204c44440e1880812440d00a268500303000084032544110013403407210a81c2d803582c00d01c10501c10340c5203102500000b094540d582d6968000d00c0e81d903520249103075125100380c1020a80c0301e01e01744221001c4951580700c207030070010710000c5440406000d8080826040e100c001c00c4203c180c0d64030807500d0020b00c0056460f1582402014039260107980603407a810b1000786442c03040031030800d82c00c2d101103038000156030280e203c00400407207480608202e541c81504803544040f040200124440c81512401e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325795674 1250 325794424 325794433
    0x10181203120504080f07210f26010e04050a050109051e03030f010504090515040c150e010c11010215040503221406070c120b151008060d0212070603050702 68
    0x40194120b840c242c40050401c2410012401c0c0d00170b020001d0890280181c4482c241c2c00e8900c660048840030181e0417000003030404140d6042940c01c00c4d10480c0e00600e445800640c018030703008540f441c0302c06000b442d0311002400002030420070b080225a03200d40d8403030000e000c01c400030300d400b540e5503c141380c02103007540c030b102d2031098880f8001050743e1242c18403100340c42d00e50b46010b00340070041441c00c80a031010300801410000501d04c600445001e07610902d01c120520b4500500e809903180b808565a042205e00c0090346a04e1b03900c4460000203a400201400143ca00b86005034036101510460880d40e1110b801003105000010010f400d200203046941d8040e5060b88810342030709502c0c1d0240042c00950300c0c01d4040e15040500241140a11400e503501190303489070103001c000710006004440e6840f690302080900b01c185800b4810000c025110072030601c0180001500345070006200c1401170711079055110541da04c86050032443d03118203040d6480c498450600601805040b292180580706 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325796924 1250 325795674 325795697
    0x6080607030c0206040b04061119140c0d030e03091e12010509030d02030714031303030c140d110403120f030b0a0b07080307030f060b070b0c040f0510181203 69
    0x42e008200c580c5080b03601800d142d0380c2c2c960b504c628004000e0f2003910180ea0b1102040c1155811200a1207500714a8818091158481344010080030004520501d86142804440350103800010602141c0400d0f040200d900000a42c8080c038500504c240f89901050400901100401d03080f100440c0ca902030f40c541c0041c0254600306826142d0983e80001154000c01c070020425445901454114040b450030a0500f1140d402107841608180d0302c50103c12150040402010307014400c0d902ca2a4560601d200061252040c2d04181d01484012102c81c03621900102c000110400880d0003031540b0903940c091100a18800803c012310407080d04003c81c2c6030162802ca0341c40d2013511102121020401e003858042561788003100c40e00098070a106040d126a0481782a00f81e9008140150401c001c9903034940c0142c2c1402103d0325400707040708880300001c01003405440f0b08980e02d0000c4e40c40588040c0000460800c041b59209040b8018509204405001007001d80c40d01c1c1000340300c14025601c01c0c0d9602d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325798174 1250 325796924 325796927
    0x121002130e0105090112060e121b0c0a0b0d0b040507080906090f030f090418060f0f09020f040504050a06051e01090203061f020c06030a02033718080a0306080607 71
    0x1d10a008882d400000c5400400c24003989020041d111841040c01190801c0e070504903134030f04510301c2103c03a0014000b00c0c42c103101e007085621807451810741000401e500d10005010520303106080c019008088400100101000702c2c3d2380006011000c050720800a52401000041400d0300030380b55440036003e40804920900000516035900041c2e1001035450140128007000c0f25a0000c880540c01c1615001c05125407034220885006141c081d840100d8205a28400d0710111103008445000151404402101688403c03a02c9040d001e020f840002e45a119800d00b1403038100307003100040405050004203e64440c00000c81120000e029000c4c94950340c8a002000c26400f003103558540202c04400c2c1d1001c50802e2007c08892000369006032404500c0c0300003c0f510583c4200c03510102c45030000f003030100b07201905d0700c01140c01c0c401c511031140c6c50788001c83c000d04e00d1000321994a8100d4440c6c50418200ba0305480960300c00740c0c842d000a0361040382c000058090255032081103120700030000010381c620f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325799424 1250 325798174 325798199
    0x230d0b09040b010501030f0b060d0b030721080c010e030a0e0301060506041212091a0711010c08031503010209060a0315051f050d14011d01050a0f06050912100213 71
    0x242d500c09001030b00d0b6800c001c0110010011030424050721516a048441d2584030b4400600b1480066100402c0a40c03048060520301080c9900c213424045007421240030841d07100b050000c0c0d880d4410340c403a0356070740342141050241580d00078401e800d00001505011040c0c0000d071022521405400034491255241c0c2000030038052403203034841755070441d002c102c000380030800e1a2103450030038108142c030941c0751002c102e0404c1d02c0100c00e070a26500050218203000c00c03e0b030811203000091810903800100c1e641c50304030030700000e48024a2208440e48000d21603034290199485400040e041c00e071038400c0400000c6c0588000b08070141140304051001c501c5091120601c0171001c4043d40a41001901a0f411a015400520158081a07580101000c03081080c03400f58001d0403402442d00c00c80b8a1145402101001a4461807290021410404c001041c0b41012001c5030030f5401c000d61a00690740208803501c0740001070b2521405801c9018417a90100d6000d00001581401c880c40403a440762140a41d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325800674 1250 325799424 325799431
    0x12090c080a170307050d0c021c0908010b03010e0307030f020a0812181b101715030706080f042910150507020f15130e0a112701230d0b09 60
    0x80c00400080c0d030803903000d4001f404025200c0c411074004140c1030240030349030350001c1d05450000300140f00412114000340141d10240384100c000700230944030800e0a903600e100e104002020b000e15034159001349070007440309854041c4c00825456444400c4c00020303480c4502200e42980f68481510004014400020810a003114808a9851012021080050211140c00d0850400c2b807412802d404100d5000307a03440c000c41c0040300200c40d203030783d0b04101820005c1903040341c402c00010804101800341c02e00c0c0d40700c1e00aa0016249c92541c20140c405000c45561080c00c207030400b20080602030202d080042144c1215009000e82c1c0e9581c2d41481c080f44e47d07118152020750300c204251100ea6a51a00c00b100c00071001e640030015190600c0040780d46412401684210415500901004013004180c0202400300403a410150f1030100c40c28001c0f41d285c07100142d01c80d400138a41000c0754059016402c00322100e0603014840c1705c078002c006100c2c11036501442840c442030b402d00b00d442025003043e9034035601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325801924 1250 325800674 325800677
    0x307030525020703080d0b0303040906050301143616090e0706080f090c0d030807030b04090b0a0903051309090c0905090601120609060501180b0306060d0312090c080a170307 76
    0x2081c13560b22440740b40d8002120444c4800e503503181d070082c15034080000b01300078500c0d9030020400b00e181274100b6086840407520f0781c103007a0310081000b01801c075040c4054913102c1c010356040e40d484000903c045a24051000c440e865100300640d07400344c2c13140030f4449800ca40300900c040c02010031400140d603d5110034826000484da40740d011a40c40f60301c032501c07580c0c4101d07c4022668a4500c010000d2031640380d018040d8003084064041c44203544e0305004041e42d50b4015107080c84483c84940d1a16800c2c0d0300140203054860380d50614004042c45030040300c801d5440003000d00d01841e1104014002000c440404444c6032054480000d40801d050242a1282036071001a021580c40c0450490074049202030490340030340e442e5600f0f800103000748600e9010b00258840f207400942d000c14135404032003058286900c80e601000400003145d444654000b0f07001c1c1d05107868403011000b480601c019240c5800024107144480001007000440040c034981514040c01c60786d1200100300301c4054075407000f540c4000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325803174 1250 325801924 325801933
    0x1030b030a0b042603090714100509010c0b0c0c100908040510050d02070b06040c020a0c05060a09030f080c060a060e0f0618070302030a1a0307050f15030703052502 72
    0x2c1200b000000da0f102d070060f900348500c0c050212500c1001c104082c80c2c01241c0c0710100a00c40703131420401c1002e020b01581c101504003905418005040905484481c00402c80000b136075a480b64860a02c03121031650008020325207007064006407003039800c06010002e0b64410740c59400004007207406421412600700300c1c2640390909100500c034841c441450403006010042001c2d42c8000202c2c8000c0260300c1c0501001425410700e0b07030400c015110410b40420466020071108004039010512030801c440c01114440e54490b03e0340d10649807801541e102410032014480003c09205202008000e01c1040d0003d540542d034404c407851040740e55034080c40b162030300b42d80300150301070026611050700050010840c011013180101111101c000071119440081d401006001881109001c4c5511a0702c1c003408106600e070340340e0086a510202442079502c05c8524401d1031380b8546444001c280160301c01c0e100d5075600c2ca0484000380280c030068801c0c202c0d0005015008000400b0143c400178000459400b0b007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325804424 1250 325803174 325803193
    0x50603040206030601020a150c0318050d030209011211040311090c030403120b04150e07022b030204030b0a0603110f0310050402010203090a061e050c0a081303060f091101030b03 78
    0x8402d80c0c00c01030225055129403508200032521640d441e000c201e0710500b0101d0103401290005066840c20300c2c1072484595030300c855200164020030640c0070705120385401a00c903501a03004940c0207401d04051545036181c40e12a01108076070000400640340104030200c8018203030424448151400c582840b6032100a20110340060300c01c0c0f06030040c5000e1b16802040b441d0b40240020b044440c55188040c4010a40e04208210b540c84460036500000c02d0024016807241e203051100e12940246002902507141340400b4a098004d0b4103450141d074210b665069103140c00b660043c0101017501054a41c5440c10003035124600d010007480d014004090040d003400c51220324680007400014204a0650205001700c40140c1c41d518038000060030140d88036800b8008401c0e501c1105040007811408001d01044114294070000585441e0320758070681586d503982090080680f91307402904014402030038003a030300c2c91a8505401042e50a03005851a0080b1074400005500300c43c0c2231030040d9050340004011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325805674 1250 325804424 325804429
    0x1203060301022a07151d12010e0f0601090902061c0608010e150c04050a0605160b01090f0b120723120102070c0915050607050c120c0f0a0506030402 65
    0x5150014005000541481e028156101100030300c0710b225145022021552a60210b041194000400310141d1311000d1140c0114010f02c820105014680751018682c50600a502c41c03412441c00b50003204020015550b04561094407031043d03400d84011840343c4400411003c0b03941c416003554550041250303140078035464510440300071110340e1440403039440000054017003083c0214801002d244020f012a50110388401040000150440140c0380c000d01c07060016071585014071060301c400381080c0d03480d03c0a244440c0541445460001c258400c40000000e01005681040380350041d0440d0a01071110401c0034455003c5040885103210b61005008001c2080c80641d20030030041400f15501506403103501154101e0344100003000c85139030004611007405041080c4a020700b20070300d4103104244401f0b0b80705115082074012031b480340704005121800c000c02000311001e030710000341650f00c8200700207002d6074455203065030603070083c3e919644104403460070f05600015104001c0c04207080d034071a83c00703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325806924 1250 325805674 325805677
    0x70207060e0303210a0c08010803040504020717040603060f05011806030b030c220b09071d01090305011803090803120a0c020f060a0b0310020f07030305060a121a010b0c12 75
    0x1841601804108803e01360b2492401c2c0815000090701100d54050030224045401c440a00445804116000e4014032281d0360200c200c404446084401684070b210900b00101c83c041d1031640300d04502d80000b070005103280c054000c0d10845052400304c1411036071700c0c40191001440c654882400d100141030078050107001c0c2d40840c03070410000e000c555040241501003031202100011194100c11184100403071810700d8024120343c01c80566440c5414100500094142651a01c40100f040b03080400151b0f03d07440b90034804000c64000c0000d000d00d0b1003030b9038180155000e002003640013031007407140410080000003c40e58001c901c0c041041056650520b004010400c54202d2411800f603001e0004107103208100150103035441010000e106440030041510341090155502c0030302d4014406402e040190b5801d623048223400d0305012030725031303134460001d1404030241d006000d40c10b0b0180d42e54804d001003000d140040105103180c00c2c8403641c84010400641c01124100d5074280c2c082890300259002000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325808174 1250 325806924 325806947
    0xd0e090601120c051b030309010510080d050304080d06030b16030c21020705070f150201140a0b0f03190c0e090705010c050106090612030f0f09121e030201050103120807020706 77
    0x113085030600f14044658900c1c1c03400344031007103401e074004410310418250070f105468003c2c1c0050060342a0628020205031038802c44500c42041c403001000141c18804010b046071034812a9aa00308245a00c03482c0284c801d071429540c86448820205a00c03a05502a00c43c500c10a0620b841d10303c2c1090221480c0e00d00540c165400400c400d40921195002900c1007280001904240403659081d500b4810000080301c0310402c034004580c185100d110f1811507160b041074003c0c0340004007042803000e0b540401c1d0003c003c440d0301d940512540750814484011440c1c00f4181c1131298580c00c1c0c00c02d035200c80308540002e05640c0c003a87c0c2e402055013045030b1340c020340703040e085107105000104500b5900e00c030760811902ea5600c490156090500c0c0c0104055000d07401959038501c070b05100c22540d0510f0001000c100d05801840c040000042c40311045c065001d51001c0302d07404a003503a10902c1118030b80280079100a206c2100d5820f20300898040a50080d06030a1040c0c469600414a251420500301d4400180c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325809424 1250 325808174 325808177
    0x140c27071416150606030504030f02030f030712090b04110a0f0f0b03061339080114030a020402040b1b06010e0601050307090b030703090b01060c1502090118080d0e090601120c 77
    0x80c5070f1180d011424010f20700100901d03100002c16151600703000c1c1c1410300042e141011908208800000d500382c1d03d09507500310907285840c002c2b41d11100031003c000c0500b850054440e055050800c410021017038034403456420241d8032000040e64890740c00c1e08c100514010a0f10fa0035a0b03120a2104d01a800042e40d802032004103440f0504000c100d80500b2105188002c50507105034401c85918900316100f0580460842d42d140d142018614000504800060052480c4505007100348182030340c04021914070650020000c543d240c4da41d014602407948601000004908000130540c4010400305215049030441b4200007816500c4200440d09944020007031030a12400b1b1a010400402401c09075100d40b0311624005603480107401e024951803416408441002140c0041c0b00008140741c5a0300004101d140d405601d0329460001a80c8007034946c03101d11691940e04c8070000d42d000c1c0004030380c0c4005411342c07184440034884000f403212507d41255214007051818004c6003103c81c0070741c414201401385 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325810674 1250 325809424 325809443
    0x9060311040b07110a0807095a051806010501320412020108060f0d080711030a03091d060109050d03230703020106080a0b04140c27071416 61
    0x4036000a18000c1742e50480207407503201c25400c1c042c20807a485a6110304210310020744020200395540c008c60701030304c0210b1200d100c107091301080c0c80120711901001c0c2e131141071480503071507a000c0100c2d00507c012138800c01001a010108030f50b0030000318042d8103032001a516808190f0010303441070310440328001000b442121034043ca07124980c800001d0006032600301013019410843e03000042c01c01d54060030b27251240d4a0204580c0c1507540c0c0300d0011500ca98082046070710b0345541e0810041960240d080c036a01801440d00e0f2004041d40a4081c030140c5808038030000c054240c009400911440403900207002c26880310051000d4a819010741e02e00c40d2091802c081a0780350003403020490f0404101c402400074010408504040e0280201c2c0c02a00c15138005000c0141c2d15103521181d8030000e44080d182ca444031b240c0d0880248203001b0b410b80910301400b445224005458039440440803e20168080c2200b0030110740b14a02c20400d208010074a0141141806030b04420250640d45400c0211256840d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325811924 1250 325810674 325810703
    0x8040302031222150311040e01030b0402100201050114040e01091520090303030c0901020f030f040312020d0e10020709090510060b0c1c11031909060311040b07 70
    0x1020401e4980502c41000120340310800403550054440d04841c039050004403c0e4030034803030340c03001440543c00d85000b460003103025043c44540981a101310380000c84480d0b4007000100900c02802c0916000380d10070340d0300122a94010340e0407805c03900b0a01801c410100c2d0341100c01ca0928103500502ca030704000c03a000144800069690094044107401845603c5d038403220b0550001704140340d590503a900b25410b0601e00030481000a4903403000170061442a034010030500c41c5a4030030040d5900f80000d0710110f81d582c03a002c001489181d009440201c9064139141c0c0b0b40c032012480400c0141d4600050b407034082072906010108685040c04162070004c500c00c0070710000d00d60b4514000c13101c072140280c014100800d2414603030f8040d00c1c039a0f00b0010038080308200c81203140d200054202c0b0086e16880f0705003074070000348804458000b00c000c040200c42c4400303d603568003605107070441c060b0b4008944803405415504c91060302540d544c14481c14800805100030003000a140008000081c031410b981d004c06031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325813174 1250 325811924 325811929
    0x8070c030c080927060111030a020601090e03070c03032a05150a380405060d080f1204111827030d0608070e0a050105060a2d180509071b08040302 64
    0x108208810307280c003a130003000d1083d156003000d9890032403074001000d1440c1080140b00695038000601c1044a126604c0c041c0c0d0030703041c0c81841640c5805502c0441e60058542e030341002020200c01c81d260cd4114140010b00e000140070300c0311003060f1039501102404040b0f0b28102002c41c5040d00414642606444480c0b0003c2e82d0480c0300340c41ca42c00e80c00328499002c592032030320411151a00641c81d50150789000140011903944541120403130b030b0701158265a421081111410342e01030045400d00b584050000c0c0b10400c01d500c502c80103501d6081e204440c800c4400780310500c94410959480c018091559911110440d020030050381c0100004101e13807802d80c0300044802150344540c00514941c0000e034050240d0a011650345400c000342100c18041941424001501d52050b54241d41c02d20003e1081c0c130281c030a084000d00b01418000c1250340b450925000c007e0402c280c14245079941007550301c00860185842c0d201c0714098403266542640003c00c9414081003031100c0d007401d545e107010902002005a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325814424 1250 325813174 325813219
    0x10b1e0d0c080f1f0e07020703120c1b080307080c0c060a0806131b03020a090f06050705060a1a0108041b08030915030910050615040306060e091c0f05160f0308070c030c0809 76
    0x8a005032f9600c59490307000c0c1481c0b10b080e810b25100341d02810b000381d000c01a40d2000800e8940407500140500d555111910307101d40f801e80d0003012190006400b1419519041d0000b01c641d104000c01d0301e11030245005580001c086075040e005c8002c070080300b60441c0c20158440c1c0d015081041441c03e00e6440c1944400c00500ba414099014900003280014080d080100030301415030400d60114083c8892446a9010007145c13500054441c10000044002820f002070440f00d850159150000d0610290f1607058040c4c403a031200040038050001003e00c0c0030030140705011207200d803070004040c155400c06221508007a000143c05282e00040c21240ca004110408000300003e40c41118006541c070300c2c00c083c1c581040300c001d0815216410501d4502c01c007001090854405020520300710f0842801b2040598403801450b0100c0000504c41c0401c204210b4004401d9110707602030b85510039565100c510440b0140718a000080c000307900c0706c0d04400010042000b41c0008030004041d00c080414410080204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325815674 1250 325814424 325814453
    0x8030f04110d1a0408040909050703030e1503010e0405010605030609060702160b1c1d06060f04091203020a050d0c020a0311010203010b1e0d0c080f1f0e07020703 71
    0x610041040c0010090002000d104050040d11189544011a2186050040e0012042d0382441c2020b00060810000c0c0d0300b1540600b0400c1000c12410003a800c0c56903030f886590000b20007050030444000707105d181a460103503031405000180340c550b82c00c1c400081d0078580b0242089a1301c1d922880040750035501031147e41d03c500401e03001003140d80b61001000b0b244c40300140d210054007880035014800c205540040f9000d1442d08a610079425519840800040031015031030005291300141c00010f20101003444c41c0114001c448140008008408020440b406018018410240001d072a507015000760041d0010070740310b003405030a0410751580c0c9005e845241076103c0043e0002410b41c000c16410401d5040e000860034021421581407418801d0103100e49103002c421148a145600030f440f0906013118002c400243c42400413000455015007040d100341c0741c00e02c0000c0301000140d10303d03d00c4c084c054201c2c00315a05803943c691626a0f00024040b010700a8002c40c060481c0c0403000ca548140d09401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325816924 1250 325815674 325815691
    0x2040801060605190801030305121302030f0312060f01200712080903011a030c01140706230a1404060b06090d03080a0b010503010f0b0c0708010c03060f0b0304051213030803 76
    0x82c4c4513440d003030103001440100201003d110201c001880825404015100c2a41d4060741840154480407248201d8680501d0004d515200b1036030015482c0c82c012000e41803035900c09100200c4c903100c035010041742c89aa03142c8103001502d42c0d42603030030496003000c8a4200f42004005c0e94003860710b500749c606c480f040343d000170b8820020000f00b400b441e0800340f0402c10480100304403100843c40c1940001c3e15003042d8bc8a080c108454241c1d01c1190010f81d40c01c942c201c59000908100680200b4110a00718000c4101e010b581c109044c00182000e150780540e0750600b0202211030580e0707841e552058000c00c3d0030080ba6030020b078188510307205500e6007540801c99a009450398022854441c2c0400c0584005400c0c060400038180010005440c01104000981d03a200282c0d5444208840d04281303030814507407001d002c2d9820b0442030007070213806501c1a4155000c04800c04c180c5621071610035a0340c40280c030000d049a0100c2500c0c2c0421030010b000c0e100348210800c0000703400341d4940701d0391601d030000d031040103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325818174 1250 325816924 325816927
    0x3062811071a27100e0106030326190e0f0a0b01140a0e09010b030a0605040209070c051005040309080a06150e04020d0605060d0215030f0c180f030102040801060605 72
    0x5000403050702e02da000400440840e160f2800340a4200101c240400c860051815a601d04a440d1001d00c070844004800440400c156908600b14502801d2a40700c207070040303626004e1000c03040450b900d01c1200006150145013850f1540d154641c070741c40501e0105540e80b95140c20220003000e042c080d00aa9100d000d0080c4503050007400c180e200c00320b060b48043c40c10580f4081e40d916544804a5880c01ca07214080701072000e03541d14800f180504009011a5030500401e08507108000c0b0540c80540070f540280d4a000a56940d40c8042c0d030709070801000604150710506104541e8091074100b01c2d403152191502e41000359803241843d18240e40744030205c500a4940002c04c814003c904401d03402403841110481c5c4030b00741034010403c0042d003404041d00302600c440000e0000d803100c1c41d0080360258064003012802201301d401da05079400940b50000340e1030369a80415203030080202a10502100c050044510700d0b80a0100042464020100d54155409020005e0148401e00c0303050010001506d0b582d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325819424 1250 325818174 325818187
    0xd0810050a080d0207170c011206030606081006060203090f1909050c040614070201050a20150a0e0c0306192318010501030b06061b1f06120203062811 66
    0x40e05042a07074102206d40400442a100d1840c00000c0401c1c13407c42c00c1c2807110010b15411551800b03809140c00c050103450410100141c503030b20004242c400c403411103c00f007043c80d885600490b200d10813002115440028100900120318000c04120840d810b90302c01c3c0003002d540c540c4030405440c0d04030340c07200031818003040030881e01d83c1100301517010783c0c100e04540c0d00d8a003e030360000c0c0450149a103040304001100341603103148040c824800d500c0002560072616101c0618802c1d408900c03040300d121450780e050443e480f1075084002010200300d88020082c081030303a26110250680b0003c100c0158445449030440c000980800c1306211075021041d90760212498640700510425414030310040c83c6030316101c010408940125072098114001b110200d541d1840c10b00010025001d05d42c060000d400345010702d01c0b841c98803c050603040141500d0600c540d60307407400c07400030322040484044d4141c1c0040000a21440c05c0c050101c40c3c1e2050150454005000081c070802100c1d84d4900030466080000b942c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 325820674 1250 325819424 325819427
    0x2030d08100f050a1e08030409201620190608090604111309081c150e061306150207030b150d060f0f020a090918050d0810050a080d 58
    0x19800a044500501c100c2c403482c14000c941e0600d5079100d4114000d0018240d40c0586200d0800341e402400b540048a0f1200c1d286c80c50400140100081081007032104c4098800305150401a116404040410401402555151100005121483d003800f804c0f03e80b1620b03440343d4840d5121450202407030b401856030381c20b003503001d4005600a8004101d60340030780204000900705001610902c8000d448850b1800000182d400c0900b420030401400c803140450309500e000c2ca410306600b800c080119060048001c0c0e03260250b204c85260181102008505002540e141020b9041d203e02d0300e000040002d00c2503403640080100071010000d000180c1080c2c00c10400d11200421543e042011a60f0b0f0701d0a405030b400c000f40d440368030b22030010601500c880c1e2039034006e46160300806004000000c1036585141c0080010640303074041c001d1002017490304d00b44100d80341c0e8000c0040d592035401001445043c1d4451411703202c1c00401000140c4030020618003203082e4946250081c02404000000c0111500d4100c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 325821924 1250 325820674 325820701
    0x1504090c0c15111207030509010510080d14040b210c040e160327020103060801050f0402010c0c05031504020907020109030f050c0c1f020d170a110702030d08 69
    0xc0345003009124076240011811000789101d411020b0500054006400c0e1600042402035829240c1269904002c01a40c15010340100d440750344413500811442c0d9580f00843e411508900420845a100800280016015000c0b0304540d4011404640c109503a841501c6025030040c0c0201031013100080751410740c2a0b42c9007449070400d40d9803901034241424041c1c0a0806140100076107144a815100741380524002c0d40b0004c11501e9180003908403c40010142c07652a80d0103800328006490300b0000142850180700b282c0c086c01d45641040c240d6115a0011982c5680001d8152130140c181030300010940d5042020800c5070a10840640c180e1401d80104080204010844070543e41841401c00c0021b60000c44002c0006140c10110f0310380c10740079040b61400300c00c140c030a604050710840f080700c400d1449800c2d5409541c183d00300e42d494540000c00701c4601d042051600c1c219580d18010481001064000044011101e00c91604001060b00080d1810582010b00030100d03413084240188941d01e800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 325823174 1250 325821924 325821941
    0x8040317040b030703020a0e03060708010f0906230111010e0c0a09090224042612181003020f070b01080601050406180510051f0e0a05030c01110c150409 67
    0x190340c10546004604146480020145401c2550015480e21014000c1021252391507001d000c46055240aa10140003001e003070144521100c55040b00141c03540d014014542511000c81911b050303501d10000c58a4a4480c52807250305001a0064403074000d0070074800c451002d003060008007044c90120b028404803030030b00e03040344207024240440d50001d07072200008071a020004071082203c0e401c408510414a000b00c0d047214601500041050040d8034444201d00e68202c10a000e90320221036042003010240302c0e411002d81a400b45841c81c01d000c1c41c1040d8140512032240c24054078162444c80039070400d6011100c1140c00e074150b00300500040782d0412074540513090542d820441541080c4418a4101144115440b40b43c1c85e10001401c0543c4060600d0052001030f00304443c803866109480c8891004c2c06504000031041c80c9440b41920300410300d84101c5201401030300403440300100468a4008000b041e40380c62181004011107038031105031004074900c00c20241502c0d10b0a044840e01a42c1816 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 325824424 1250 325823174 325823213
    0x2240304050303150d050a030f03110d0603021801050d0b091002121e0903040302191512050a06050114030907050a0603090303110406050405090912030708071b0c1a0c0a080403 77
    0x20380b0703500002030001812030748494150270134599800e20100c04138081e09414110403401240400c40d80454160f54100c1c0c0c040e80e00c02c0b02c540920300000400319a05c01ca09118070f03940140d401010790080355007415041d40100d176100c1680e10343d00035154041e003a688400c402801c080c03002e00c00c01c8135002000107a054002c6844201c01a941003100602e42c0d24015804042d200351411610b00d02030010140f0400001c00c001b014004032490320842c058003400920f00240c850a06000020744005090f126003400d44e46c05865581030507660603c42e1049030001020088903101d0654045a01d613500050080145000e84e404651a000c0f49002415241d01c0014030041074003d00013440095000717003c1d50305481080e11080754607078030300c0c0c8100d1508051801c43c604490001040c80881680611034030301c10390050305e584550640c046109441c65205e0000944100c010707030018040d41c0319003016101c000701c040c10841d0812103541c902d941840f88841040ba8082c1002404204000120207d1061744000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 325825674 1250 325824424 325824439
    0x90417040312110111040603020a23250203031803031605060a06060e0d060c17070e210604030e0a05190906120c09051e0f01030c15020a0224030405030315 68
    0x1700c4500490285024850505401040c0d000c400d5100f0194141560181003203a410f500200d045881164450282c040c080015035040d640700c4002c40c088117190f40d0303014006615248104941c220043c81c0200c00c25490f010401101e0105000c84041200701c901403006407016040c001d202c5012180c680d440700d0180447c2c3d20801e03501e50b96048184165540011010840225890302120310700340b60000c40e170b007a4450314240310031b282c0d22442800001c201924203503580340340c2441070043c01d641840c0c809c241c0d50041b400580060b11800000002070000f400d02c8006546800c002084002e0b250002601070160041c100506090741c002c800080c0107185202c4080c2e156502d03480904890303401048261600e40c00400c0c640341c01d00316a41e071a0034960001034100d0825420030f1410000070f00c001da44200e1414408a4940022602e21415615540040032030040d0360342171200c0311a001070070068180410407004820104040114490344c410350103141da92400000b00d06c0211400c503890381c0142c48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 325826924 1250 325825674 325825691
    0xf0105240102060606070206040e0708100f030f15060801020c010203190b030618070e040311061506120408120705131a2710050702040b060c0c0904170403121101 71
    0xb0003048068110030b040e07070030795a146014008901c1503c40c5074000b42511094004014645511041007030003030f110000c4800415a440c0c0d42040d145071030340800b0b04451003000103980021030300300c0c030000103a5038004003141c030990350300840d0308903001000b559140d65000000c00c211070302c4140b0030440c00303c030a0104002c0c2c0005040403035548c078030007066a0540300907070000d01256581000140c00615080d0501310441c5054a0000c12000300d40c990070f0b14500c070300b0000c100d0145080c410848110409002e131821f04044400c4050405c602900a40740100d0400c50040e411a00061051140126480d096034500300f0364140e078610800c540c003540560b80d004a548020110750011984410b118a41d80b2550400da60b2402038407904404070254000d9180c8510102d41e41c04c00d000e4003044e0f000b16420010041501e0601c1024450141001c00d240c1011b078120040e49402800c1c0c40d000f9008000495a00d54005603424550b4420340090380d01003403517401809101d6001401205180d5040300900100a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 325828174 1250 325826924 325826927
    0x1060e010e0d050a080f120c07120906141804090c1809080702101b05060106030b030a051c090909210c11042007060c02010606051603120e0f01052401 66
    0xc0010b5801001720900098015400307000000fa2000414074151407031403070a011120403050761005104071480c0540d40c60101c01c040c0140500411100c040e02c1300c40880f40c013080d400d49a50300203d00300642100e40c6038101042d0b01c941c8241082203104141c0c54202909124400b96040b44520945111500781540b0f0b400041c40d032407c8e56a101c0e41910040011002d403942a038082000c202c81c800f160441c81e401905020000400364100c43c016241084001c280c0c0080c1511015251001751507a804188007001e41c0050071048150494949442038400d074840b076103001a28140c03041641d0000d04142c9000c51b0f0380d2141036504032202682032400c491070b2190380b640c81c000c3c07407940001e00c6199a0203d41c42c00424003040300380c0151160381d5991b907400d00d40c42c024000341848103244005610301a0040b410500400440300500c01e86220300741100d400390340484828150300041000141c03915460000040c08002681c425240c85002207001d03d080c0318050100055111141014a501c000514099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 325829424 1250 325828174 325828183
    0x151f080a17070204020c01050f0f0604060e011a0c1e0d09270e0a030306032a180f0f0b09070e220e0f0a030905030a080a08060d080301060e010e0d05 65
    0x801d00c0c440065150101c07800020b00038000e4011060482d42001c04201c10750320b90800007841209100c41c180c20503200e40301840100d818500800710b80880c10700050080d00185140200b0b401124440c840c501100781c8012420581c0610142442c10180004000f00a01c20b010200c21104680b80140260b80791005000710b510090304210108918100250401d014981101040d40d005100303c07101c0d2442071a00030010704071484240c0e103d800c2c03040b00000f155103142c1407145031880c1d5030241c0c050604010b03111501e4005200c012084582d200000e00a81c42c0328050742c010100c8406000075034a04181c00c0c05140480200240200109407440300e0b850350707410b5000c58118450307040392009a50780301d0f250b40007440b0701c1c1c1150205104280309036908400000700c0c1c00200d8405c0e0345e00e9112a82e0341c014944e6405442c2d0004020b0042400014411882040026403200c07004082e402c1c80c01958841d80c0c041e038420380028002816501a5100c80d5820038202d0342c10300c00585000a0510b081d44945859 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 325830674 1250 325829424 325829453
    0x30d0c05030a11280c0501020414091602060f09070f030606030b130309061407060207050601081c02030403240c0302090a1a030c07080708041215020a090501050a02151f080a 76
    0x84c0407141c0d40b184809442480c0107099194000000c55407903407280941154820b440da80184240039002c000f440c94103d038640c045050718103400034041c0752142884041607100040c0701004600c00d08500103244800e07883c00600444c0501000100b86044d828000c40c12140104008441d21080d041c20700040c0d484405401180c1c41e61503c062007040c401c600341c0642c45811000303040d0314008140c1905008000c47c12504a400000031170740083c840f00d08070f403140c0c00d21400010158000344000c00c00704402c1000001002c00b22192104910500702441045800400b10301000a03030200349102e0b40c0c100051030801808240c00c2c1c607020007180340200355071403000501980d5400404140c00e801c00a244c1c3c191064a580040007540722901c566614403541e48148098403900403450000f10384c00c85610031140295003940e00d8010450505005596035441880c440c411441a6040117500c4a401550140107040c1e05006000003001208041c100d61050782241d00180c000310f06144c005400c51105062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 325831924 1250 325830674 325830727
    0x61c091e03200708060a0b0909160e06011b031119051f020702060703020d030b09010311041109030304140a170d0e030c040903210b060901050309030d0c05030a11 71
    0x280301a80d0b0540a041103416400045248200ba046c000c601721035810415980d141910407480968404818994904200319201803031035509009112600a01c003020364040c1c410704008240b0f0360010022003007003c100340c2c19800101c000d603519070420018803a0341d02e090410700e40350104405a849640d00c3e08024404c1001d1240c0c1c001c200031000445405880d4850b40003005603881d0256404d0180d03d8111450324000024a04220300f406450400c2589041c0c0c2d410be00e00514424403a8180001807080f0091000e51038414003600c00c8565080000340080d1400b40c0e050106981a8820704c0306410b081c0d0449107107400480340e82d40d40b050303002034001e80d4003005207402c0300320850070000720741020b240c004680d03041800c0480b070605241e00724603445c5422010340341c202c2c010b2368a42001b004545c0d11100003540f003c01000080040d40c400e402854000c10101d064928024404401ca4212040c0081d0310012a00100030865106100d21403504007c01c145d5040e071600e0b0342403100c4150b0700920000240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 325833174 1250 325831924 325831967
    0x20711011e0c0c030f0507080606012a020f04050a0f0b030c01081b1e031f083304050718050610120f05071d030f030d0902061c091e03 59
    0x14203002c3c2d0814600c0055800400804d142005420204c0c1c441d50a8020180d5500c115404642c282d4031440b9440000c030400c00c0780711429400b4422006044401e240f0a0342e218102e0380b400407441c0d42e144605409002802c2c0005000000d208a2406540140c4e411a2090300501001050f41c2d03002407280394045200b0150b40020701d00c1c5034040025005050310031034900418049110020840e0380194014855402d10b012007030b80c6001c0141e080e40c0d140c000d101c1c05400c20042910480c0860a030300d0050040ca071500400d03046664101c00194000302d40656607940a42410407604064a080c00a0380381469400d004501d882004a00e1a03101c8098903010481000c08210030244c665000b5654600c95000500050921820042400b2246010781c40584e082c81c00081031460300082600100c048003000d1750604101104c80380c0184414403050741c000380c1c100f00728460b60950882c800010f0098202c001002c68803030402e13030a81104240c880030284500030607480821b4100314144000c00c001c43c2c030034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 325834424 1250 325833174 325833197
    0x31e0403150915020319060b07150b0d0510060518010803090f1f0201090c150e0616020d0302150a06240207210203061b0f210a020711011e 61
    0x7164048000d54101d0412407001c401c3c0320961020f003182a51503030204000740b0020303440b4400c81105102d0100018003654ad40004180380c00699041581c11440081030b0240c038000f151503060401c00303102014005036640d08010b100c6480d042807003500c00d10540d003e40000d5810a040c26a0b244990080c2601c0349004281652043d07075140f50464040b1080c40c1920114545d8103c0a030190041010807586007048010201d040c1c49118070201c1c0e40d20072541c7e40046040c0d48014000507902460340029090001007003040981c94011070449d5151099000701a8402541115494040003401c105440703814180d00b040000240400c1041c1d840306c00c0b11400420b6190300d01640362042d02e9114039000144190110391b03103c0c0170854000d0b003600a03400d80340b41d981c4030702d000840d005002500b0710401100340040000c246c040b1000d0b0020000c082d1503903034080e01d800c40301056402c040711400852600041e21104001340c00c0d0354620382c1070f020308090811080c5108070395601c0e06205890003c018805603034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 325835674 1250 325834424 325834433
    0xc100b030109080d05040b07021b090402030705040903200703080403061508010609240e040b040302010915061d011503020f13080303040b07020a08040902070809030f031e04031509 79
    0x710001c0c0c0c3e20000c540d5490f0007400b000c10103000200e5040e10800d0780030700000c503458004036203d08590300003d6962503031015441000f105843c094070603a090f10840d80d02240a846510402d44098080d4441d559030780d0f0310b0100001c480b00003031740d50095074110800c10400180e80c901503030241c80c2d03c194003042880403101660b0070703600c10ba07001314800d6080007400038038008036a00a2031003540c1c000c09656501c41e2003c103a03450a50342d1107846404150140001c0c0802e100c803590315013052180c800850f586856458254040a030752542050107951103204120906084c0c00300305403400ca505d54840658507000d11041404141034640082c03680000c0c00e00c0d00c80c2540401c0703075000c0c0c50304000d1041c0341d51550181c80d1b03690003c5a04503256104039010415071400014036600301030340503840318a01410035000d00080d42007414212040700084c070002e0080d82c6c050028420101124008603203d920254401e0354150030112500401e010410090011804d40d81240b460003803804401301d8004800d00e0b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 325836924 1250 325835674 325835681
    0x406020d020922060e010803091203161a090604150e0708030408010b01170c0301030f0c0e281a0d170d0e0607081e04050c03030a0c0b0106050c100b0301 67
    0x91030340c2d0000348404480c00b580c0c02683c1480d50710341030490810400e41c50b800d103168170030020b0207001c0c6598014807107209240741142c11404064211002d036400c0076188240e40b81000b00c0b42108a480600422090350100c4910408a5010100000504040c14180c40c1e0200300f012202c030201c040b40d26645010034481041001d0001084200102d03030380c840da180c400394020160300f00c0c42c03030028403002040c010320b940f10480305001c2c4031005040b500e5039180d0349e2004a46032000e8070854040000140018501200000e030342d102d00c60007441ca060720503407000b0040c2040e4000c440450391a1409009681c410034000e407208004c2030a50300c1804400041c20400348900038000380d000100c10001c5c5005103100240c001d4110075918404884141d10f035590705460801084a0728803a4a44042c2c49940c0101b80602d23954000c1e00030b000740c400071582617001c6410346d40006a03a001242c0814055810040c03461009401000d07649450b81c04c004d0000074103500e44c0101405c241c070f416210582801603903021b50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 325838174 1250 325836924 325836937
    0x30807030905070807081e0102070314090f1804030e330408010606050a0f0f05070602161e1e120807030f0618050a051005130b030d030912050a05030406020d02 70
    0x445640039550700301070b0b5441f906050724203828200d244045071440014000d0760210f07175040d00d440c003408541140582142c9c204040241d44681c00d4090604581c036030600f9800e11403404824100c1c986410b00340680020002c2036081d000769a2405400345440d8200b503001440120550041601d801e00301d0705120754051a041601154079145000420f260410001c1400014030788032001d000481c09800d0b11000590012800816410403280c80040e9a035401445186500d01d10b50701040f055841d0300c03080d1800d00c0c0301074003242410300040040c0281012440c0c180300d03005040c0d104040e0300c0e5403429207540c400c01d01038040c07110105c08540b5450003030b04000003815101d0030401207180d0301c00520b44020104075042d030100e40342c00c000c03861410350350003050311400d24021040313441032130078041c8410071841601c1200d6066880c0700c4240940d40a002c01501d02c000c9580c04a041900c1d81002e44480c81d900030441c00b070050070003241c0c6407941c101e404c1d25071041c0c00820060b00d9400b00e10401003e071080c0c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 325839424 1250 325838174 325838189
    0x9030313020301021b0a0b09070b0a03091b06090f08030c03040b071a1302100518060901110102030415060506160b04030e0303070c3002060309160f140d03080703090507 74
    0x217207903415100380081e0000015000d440d421605840d0521402e0f00c842190003103031210141000851200c0380240c000e4000d0911460410391400c0320805c228404035025000301c0d000561803802088003525668500014100040181d840c003030104200da5540d100314451825844c0001c038800c3d05100701c1541142c10f20000c4490701b1500d24100780401e66010001c0d900302d10a13902415000d0180e0f2140080d500c0c00c020441d40043c000100104010050300078041d8a4100000d0b6100080c5500080c00550b000b01d110300c104500000d855046d0b20b09480d090f4000601890341441401c00c1c03400b18000204243d500404000d506859900b02196031500941400d0f4244c800017640c4001c00c03443c4440c00e800c0300c0b0200d8001000b03801c200c001c0072950413030002124440da02e0103036034805031401200560300420400308840d80c5019812420140c034545030300001c030039000d0719070800903d409407c40910700f0b0003c840c4ea081203d07166402400b0807102509000405549680c801c041120402504001d414030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 325840674 1250 325839424 325839457
    0x12070608040201080a27230102031005090c03130602040b030f061e030309060d0b121509030f071101020106182f19120c030608150903031302030102 65
    0x84100191468105640c2240001d0800000503010200c512072480b40c0c02c81c03055141d0f409426580c00048042005406803400c1a40041c0106107a00da001690400748104c8000342c1c80e440c044401c40e409a400e6400f1301d004203041c204201164070f4000890303501480800c01034030600854101800240680e400c03001e80a0000810301021110941000c1d100740380890301049042013039442034a5050300c0d0180075405501c24041c4881d585001006481d80c42140b01c6c0000e01c0006c0b900000e11220076400c0780c1509a00030902140c00640700c0d5003038a88c070000440042d0702d0902050041c1c0b80900c9120400740c60710104c41c9010000742c7c401e4104400500c0e085a02400340740044402c000185003130095100c0d41c11084582c510000100c10401d8901c2407030a414504001d0340d252034132000880e0b204503030f00704009501003c01d665410b1042c01904052580c00041d01400e080107149024810302d403040d401120b550803c003a0382c50000c1141d52118035500c2110082c2e401c0d1020a029025440c8000404880c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 325841924 1250 325840674 325840679
    0x301020a0818150c07020117010303080612060603030307110307020409081c1e02090307170a0c1202130b040f0614030607050a020307170d050406201201141207 70
    0x1d01584680c09090507250110590000308002551040d1101c000740d01290070f02c00040004c1e00a502600301640181058084449003081c1d0802c4004260011404906020148425402d00e07400c000b05059036000100300728109280001d03628040181814100015842a100d8030001402910301803540039000340103090f983e142201c5aa0800440c1c0d090804100b1160f00740385419004040381c1ca403034940102910b034551200c00300654003194416030180f02e50304000943c035a100c02050780301544100a810242c4080c90315001407541944000c0d5101d42d00003000d005a41c03100c140740c160300120309000038031170f58210202c0c018100060006821f41d02d01180083d0391503803105680403100b0210290f034807130b81d14200e00fa40c9130f0040d001c0002c0143e009210449c0054a460036103848101d0544060b8102034401d06042d05a403c110740865008d03440300c030001c032584e65100983c950b2030301040b0003508020712172000d401c1d8810144a1000e9080c503031260b00c1c5090311118100083c1401c2041031310302c00c0344c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 325843174 1250 325841924 325841927
    0xc0b0705041e08120412140a02030616020c0906130914070305100b0117040b04050106050d03050a080c09130b0a1d01060912022110020c07141504150504050301020a 72
    0x51a105003c040e0145a440e01e030442c2c1100202c03800d407100c44580003d0300850b83c4641c030701101500d406640781d01c45c102c0400056a030411405200360348a098264031035034030b5440282851000d01d6100d001300f03208010300c0100d03520800803005181303070703540000341c1c0000c2402e101000610038503404200340500c41c0088188800801c0034404070102ea0344c00e11228418400459000041030320000da1502107801160006155204940c3c100c1e0148001158440d2108002071495140860450200d00005910301c440742c1c01440059012604981d600d0502001d0300100f40911400d48901082c50303a01d22a6481c15174800648801034408501420450304280000b40400d80c0c0a000f05008110074010001e1065004240f4138040c40c1e002d044540b184500845041450340f00e0300c00040640204038000441c80031a1000e0300c08032900c4230090030024a0880c00441c2c0702130380484280602e100c0c1d541103514008400032030b400ca521546001c0c15140c0c400e00211501d0240341c00056065000064010388113 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 325844424 1250 325843174 325843229
    0x1a070e010206010f050a12050f0613120206070203161704030605100f0b040e090a0209040b0a0e060402060711030a0516060e0303160809040204050a0e250c0b070504 72
    0x929003a000c865041c0d032141130b030048445240c13180c5d40c1c0c0420810f0090101c55440c000001d2501e1082c803c0f41c0101c2e088a9449041c0780080342c0340020710100c0d60140b002c4c4202c1c00120720103000e00d400a44401e081140c0700948a116207140100c81c0d82c0000c0d072042c2080040c0384030070903c55078011041e40390b0b6181e107841d2015002c1520102c2d1440b04d4128085500c0303200324440e90803507042400c036900c0c1c00e103000d4000525500c001c09107502c50080307500c4070300961141d5121a11441c800c500009192920210300b008071040c1d52000741043e440707581000010703110780c0101c40c1c9254111100c0404106601d00291400628038802041030181d048441d060860194076103040d140640c4601040796600410b05590f8001c03100380114504500740c045004c035580700d0042804c500043c0c800751800b5102c4020441104140c1d200c442c420030081d00300b01070218542d5002c000d1030300e6190003400807c40400010700d016060000580403080d203c001c0381000d401842141c0040c1940700100420240348190407115 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 325845674 1250 325844424 325844447
    0x81503030418051609060c0c080102160c0609140603090c15070308060108071205060303161b060c1a09100504060c02060105010311120a27060b0609010c020103091a07 73
    0x4141c10300c8085101101c0040c18030380401c030580d45d444c082e2460b051044440501c0214195814003a00c2000b00796010b081c0000e01d100e07040041d44841d0750100d480e003040384034040d511003804c000500d14184442d8a100070059080c0b001212056129114100c1075814001700910195120b07013034045071045c1c00b50120280c440c0303038003c0e01c580b0541e82e2894019202c4040445400000962002034800d805a855201d15000b850140407a0b04100c4002c000660702c5100c24029030b0480d0040a0310948401e46408103406030032985416502941d042d91080d40c2d1850384c501c0c807100644c2c1000003e5554404024601881c030b0f8000c024000c60415040c210010043e4000c044018010f14001040650080c06200c100100d65648546050f0029100c4016090040d202c0c0c0c0900e500c8014100701c030000f01040e5000c0c0703c42c0e400300d204207884502d8407404407034030081c800f80190814000192260b0f0010b00c5007013032580a08021402c503986150480001522844a894054442090056496110404185 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 325846924 1250 325845674 325845719
    0xe0705090f100b030c090103151a1803190b090a0f06063f020f10090611010c0c060c11010516021204081b15180414060904030815030304 60
    0x10410f03220f8006901500c001c480403c2c0700c00007000707214119480f0354088600340c00080d11101d03200c3d46810782100c461031004001000e0350404a12209458503080f03001e141004102d005200d00552500c40385c6030408030701c43c00b41903071420b50b001942ca81001d1160b00001d542c01103c5250040b19071504a00405003801034100c510310f480042c0b070040d0b04542078544515000c4c4a81d0030342e0010740a06a240c41c04804049070411014031058010340c4074001e00d42d8103045980c9503c11090700748040207100c040d1019050307499a041008440001e80c20801c405036654002102050075100c04400390750a00564004480c55880c090410000709001c40c0310b00d4102096509031070803001d0444501c0c0581c0240e00580b0f00a800c4000500c0d8000009070384c0707803d44640a0b004603811940360000c0c01304c41c0c1181d4840c000360501c540d200b051925003442210000740448645410300d0901001160b04543c0040c0014180203581009c0390b030211210083c140003a0b801411203039103603140e100f015000c4a00d410800c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 325848174 1250 325846924 325846951
    0x105010b190c030c0809040207140c040e0303010e0c0d110a030905012409020313020603070903050c010302030115080405010f0213030b13030c0303050415050c130e1005040e0705090f 80
    0x700366485145680302503a010f655070b5043d070155880301d0071203520106100754041d07420080d1310005807c80e1500d000804601000d803c5014801007444140c909a9006401e142c0040005008201040007055003115140c2d015030384031020150041c0007041590115104448049181402960706810085181d40700e0002808500c035010001c51240d40c0011500b60101ca200800340700c00405540034641c826030b007001c08024041d8035004190b0350341c000d031006400106440401d000b403040c10040d1111081e801c0c6001c500e1585804103a0314000040003c0c001045501e00c04a400d01000350800321a50100447c11551820b26030201072426010784003c0300c42021b80000103e41101d241c4083c0145500350b12b45001c100529030f8210700505c4000d100302c507400403c1746c601d28501540e1041034403070720351001d440342c0d98258412008030440c0c042d88200006042c103001c001e4841e4070300c40d1200882d0030545001c100341e1031024171542029207a40001e6044480c10080000d61480d00c90a02d004410410040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 325849424 1250 325848174 325848217
    0x207050a0f0b0c030d06030f05010b1804023003090a0801061a0319051005120703030f121118010f02070e0c2208030a1803051005090f0105010b 63
    0x508503424801c022001403200010030020800c1d000074510988001e003aa403811154242c00000c0b108180c10940d01e460380c10405408009007407040030b44904003218200450f81e03038064075012091700244000c0c05150009101c0281c40300c03800440c4d45520010031b9180101c0070403055580e580d08040c1c03660344583c090700c100103040d00040c030070401a00c1300380c50031200d0050403808050a517400a0180d18081e44425000c950740e48030b40c07007000c0c040d102c50038041d42584c0c40c04041203c21030148000d13841940140f202040000e0b0415030403035891100d0306044403011092100d803c02030244038002d5030301d520000344c1d90f07082e0107802e94590178a03032003600d80182c00d1020100403662900030b8001e181c804509407003ca84214101400b03408845040c20f49041440d410801842050f1703a113500c0000c16601c01308807660b480b50041051481d254440c103600024034a140c55882c1d46590181e0303500c6401c5d039640045940114140500180080074000a2191f569241606420383c3d000009807588910305000c007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 325850674 1250 325849424 325849429
    0xd031503020303180607050706031a190e1302031006170a1716021207050a05040209031002070201030e0604031206060305060f130209040603030509030118050a0f020f1807020705 78
    0x81505503600a0000c1d0705000ba1030354041c45000904034150340c0010144807020001c2e0041040d00082d2039166404111151541a000c505010440c0d40512035665401d00414400c0c50350342c00c204640c61109801d2482d16a0f10200400303011107134002e50135000d908041600903c16030400c4003102c8620917155840095480c0c0c8640b5281c20300c800601c40943c110392182402d02c120003401c1031500d403000000005603a54001407420301a006074803000e80041c00f08000740c0c50b08100c00e500800090b141580380c8006200003d4440c0d900519026001d0350214402c410742e446540071108060101003140e205041505010300980302e411800f1201d03505200700852081e100f4010940a81005081c0c9035102d040c240811003449038410425510580c2070081c28081e81c0d0324000e003002117000761561035580121000b410300351801c0905034102e0703241c8281c0c3c00e00090000071f40140c1ca1358005451010507607486c40040e0f280d00303d404215030310201d08240c507448840141d01c62800341445400321804140c0e504207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 325851924 1250 325850674 325850711
    0x6010e0408040e0c040b0c060603010c0f05040603150b04181a09010506090409050106121106030103020a030206031914091501050312070c0b07110901140d12050c0604050d03 76
    0x5004140301c0050004100001d01c003011550414140000b49041a44514861200781c0200c1402c1140e5800071b414002241070038803a10700406c107246030110a020161201030114869072081c602050313644c01001c1d0364005e14428080c00303042282c92503a0703210b40e1240051004560822040c0c1201c0c82c242610703101401101081104480250045405030320388800c0101e41c2e041502825040354481c83c040000803000e100381d5010700711011520070300c26040d01707241050910a09205016510410040c009a55100007800c1120707070450300c2076135903552007040d0b00b508401752070749803010341c00c08071240d01d1b030401c17045420b2068540d002115407862903208540d81c1e6003802e224841e01031700404090000c074800d9400601c1040d00451400d00550b513540e01c03404655004480503075405104490580032880c007041c03140e00401d941c0107000700c04045c10000440003440d40d140100b07100c0008140142d10b902900a036004580403000303956007441c0a0810b95258501c40c5803400010f4508103104c01c09410101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 325853174 1250 325851924 325851931
    0x2090a050d11040606020706141c11070b0702010b12010212040b0601180b03060405010e010605030703090c0518150109080a15060e09010e211c060902040f0806010e 72
    0x80410200515020a101c1c6425001c0c900b9500d100503810340c814640c450b8059500148600c1d402021018075000307000348120840890011907171070130400a561940400603800303500d2001280003803401d19990b26401e582c0301d520380c02003600043d40100414103406601001440c0307000d40f80c0100002044400a080303102d4450150725440900c40800c001c078118025080c0d01a4042c180480041480c681da00703650b1308264804200e15500204002403804c040c096280181080080322645504000c4042e0090100400e20340c201562010110144090211084010200641150400c108401c8503400c008030440c0d2420405041100c1a00594400c0034040100d0b40c140e0054800704201d43d407031700003103615651580d104a41766080400c80c1c9090480c076a01440442000190745840304da20541800350715904400f40f40d07034208610680f50510422584414820a0460544945542700d08010400c58000f03016481c804200820038070b191002c0d00302a144050122241681d0703806041d040c0300c0044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 325854424 1250 325853174 325853179
    0x6060c0317060105090307090b0415030b1305031b030a0212040807180b120609060106020c180709271407051207020a0203162103051801020c130207030807030209 71
    0xe54080038080e00740408150418414075220789010740344000640741031540c1e00308400311070781e8080091546ca418803034110100d00001900115916546403c1011030b00100015000780095064104210f400d000b214034000e416010302a0403a602c84010390360b40c00c600e200c03070b02500c25015840442010070080e1022240603000074901241085504460580d91102060714681c69007041c1c001540c3e003046000c0f1804110004003400d1400382002864200181d02210a42d04881581d52075521641c0d140b00007070345400d02d164565211420202c40101e0f01e0390005825406000c0e0740da040e91005a0380c00b0464403600c0c01440450900a40315600c1e0b14140e500c4408285c042142d643c0700390100d0304040e88260507005440c001e281c03680100342072800d17a00311100560502482032000760a428210390b9004400d5a003101041000d69000e01240f0034580c42004c0380300d20205005c1c6aa2081080000000015100d80c018090700980040a50060202200810052000225000c1c403074803e03254003ca00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 325855674 1250 325854424 325854437
    0xf0a1101120207140d1206030b010911070c0807151b060b0604090c030209100302030708070503060f0d08031501080c070f0602072010020c01080f070507170d06060c03 73
    0x4580040d2a94800c2001e9401001e07020f005480104002c040218036014040000d88007002e01080c006003420044440c842c9075502e0050b062010404108500d4103490a080c400034480d011028507d010f401758840090890740c1e1044040790000003ca60803044501104a01c1d01e5028005429141c0d020700903203144025001031310520200d095900521913424000e010700b032078980c6500d1144141c4025a071041c1c0407039000104e00a1a052200403230810019901d011402c43c2070500d401401c050029010104000020010070781c80e82d00c01500710f04506009010041000c84c61410741d10342c0d0400c5030110600405451071603a254000d24906114000e00440ba529240140d9a0300000e42580102610115070034802500010300c1d44615100060300301c1e04181d6489010010080712810480e010320441d04190001310307050760400b1006030040c100100d01c14a9941e9490100d8407030003041c00c040c0c4020180da00d904d40d00c980c00700040124004580e01400007503110402640d0050704a01f006000503503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 325856924 1250 325855674 325855703
    0x3030e010e01020a23100902030d0c02012003130914100305150703110d09060605061e0d0b04020a050301030506070207060f0e010c1407050f040e0304120512070b01080f0a 75
    0x50007101d421100114001c1005e1211241e0a20762070b0040c00303000ca215055407802014103505d403c00503d010100700340340042035452113a0009103403120407064140000c814800c403260286050080d20700d000800c400c4001d4865407241071101419542201039aa01d40e282d0203c1e40800501080300181c980000081291118101213800c1a41c4c0042c5903d04150355030b0a089000900743d0010500d91107040e0000c1600d5030b1a080040c04c9a106a0240d4824401040031251885060b031402820642800c41291030704602c9841c076010717101500096a0142c40010404c600c16048000f03181070b240503404681407a514030b0f0303050343d660759140500004520381d000310801c03241c414959409441418508035902c8885076403401810b039501d01c2c49260b1500070074018801410030511078810064116020b020038000d01d400e10703071030344102ccc0a000c03a2021190080014002d00704423400300c540000b000541d0300c0302c0c54240402d00c028203005007040d1b80130340c2c14680796504d030018080103c10b030019444641c4c0320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 325858174 1250 325856924 325856933
    0x106061b050304030b010f03031d0916020304120602030118020c060412030905060108010203090d1b110a1d0103060c0e03060106031e1d010e07060c0b071709010603030e010e01020a 79
    0x2a0445048507a4802000080005a09451410300808456001c90301a605524024046288804e600094a2807065203185550345650101e500840031002001508442c580220b003548110b0b0080b41d01e101141441d1010003440742d009504071822155071006608580318014240d208001d05481207a001d1070104000c40c44000f0fa141141e001d60a0019980500c0d55849007031880036480300950380d60200070800c0071079043c0b0550500d20442d00e441c50b120000780000c07110381100d1010140041d1242660209507031156402c0c0005010b003459010039071061002e0030301e003840090008440f0b8a00300382020900314001d0400d0040d9990003000b50000380e0a207201100140b10300e4480e0b954001400c0214803c9400e0ba00c502d07e09001001100d80342a40c1f0b2844507401d403203400c04072000329841300340100001c60b405600680c0c0b843d40004003802d01e848450b4210354045a943c0500351201c0d011090003900c0005622540440b4800e8850146040350700f0011340e000300c0c0840905000d600425003100019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 325859424 1250 325858174 325858217
    0x12061211030307030905042a020f0c030f0703060203071106010b040807062a060b061305041107170f040f0b0918010803040302060309010e01020c060712090c0b07060b03030a030c11010606 82
    0x11400322040001140e4232010921051403440311100941c100080041000c4030038080c9001280098006101040c845040340b507544005102c0a04100d601202203809148a0383c03105004403e00ea04844440d61102d10045803030b80035115101031446240c00005001e805000303409081080c100e000144e102a4100d0000e40e9100480d049030714170365914010480c0d42c5d404010700500352507810003191080c00c010a00c8110f40034204005442203081c0501e00009006110390100c0401080b50f0b10345410703444000c1001130165800c0f82d0504108400c0c04101418030002401400c07104540c0b142110000100300d4808146c2802800c81c0ea8004100030710240c10070200940c0c102c900e80b000000c070740031010040c40c00c9800010304019170b50030803005d010303409901012a81c2001d00000040007590305981d00c0079614101032041c4c081200c1b0200d400814403100b44ccc0004000403015090303d54403032026500500a201e07240354500441e100c082d40a01201c1d0500c104016100325448810b07100040d40d0505d0040e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 325860674 1250 325859424 325859441
    0x1d060106020d0818010908030118112b060503061e0f1005010c1106040905090d0206090c0111150a0b1c0b060f1201020d021b06071403071206121103030703090504 71
    0xb03540d26541b802000403440d82c002c40c004e080300031003d0420f03000010f001065401c40302100c1801507007407254030100141c1c042c009001100040e80d000c0820300070305070303400034180756880160b160141400b0400e0301d206201007600210f1041c9241c1001d0b03643e1108503001140c05981a0507008640a0184459405041c1d0342111134007401096821002410004900b070703009420140b07089450f0014043d00b03a00030407000d141160240003928461804181032565195940d0782c0d0790400c04103da020304088828003000310540100800d000301c6d46491124040a0590300004034000e4001090703000d2941c64041c0d030300c43c2c0d0507400003012105480d840101300301c100c1803100480c2e0140341c6c03181d030401e8200248000e20070081c204102585039940004500e4645035012503403d1540c101d0010817003066448800c1c2040300c07080b0300d0500d8882c0c03268801211808040c02300400500c2ca0400c001c148031079150540413240740f00b004061091405941450349a020f45039004010483d0464180864580ba4120910 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 325861924 1250 325860674 325860721
    0x506010915050d080a020c180a1d0303070e0a060509060f03060114070b040b13080a11030d06090516050403080a0e0102010f0903051803030405060d050604020705011d060106020d08 79
    0x411612030700003039064480704104a408100c00222042403079018003001714203000c2114a09407050b60070019450554000300009e940a80d1428029a41c0030795440585852031100101c94491500840240480c0d54201440b4820400d0140015000d44280105c41c030a19001e4120750828a10310420403e0b41c2010740401d0502003078007064440c000c80d18015020190082c8070b82401d9040604102c900d00b1006400c104030501c1082007400800d03070000880392050b805241c42102c0c10b490b02d80702400c1d40076a100000603141001e034000740c51002c030703080039018296207c2109031204044005582e507205038800100003013424445d001040d4090074403c1d50295041c000401e440b515910380c0c000703d818240e0100d01185010504411400560031103650b00701c0d007074004514241c1010009021030145810030030310340e522940080e949407269015592201e40c050001e00c402e07404c06907a0082c6031800d407880641803050030000034400e40300083c040103000c125120702010303403103600703081c0b5411646114101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 325863174 1250 325861924 325861961
    0xf06291b06103f0f06020309150a0c0e101e0f020c01030e1c0e03030705010615080103030c0209040525050a0b09030d050c0f0706030911030a05060109 66
    0x61440424070034184207400c4001e070300c8009401c1510760403220782414201c00d00c110750030780088008002942680a01c0040d02c2c05001d00b801145842400f8000d04800202903a001209100c01e15800084843c1c2c8842600d170b40c0e00080c2e54000004003112030005183c070000d04801620000c9042860b0740750003417511841c060856000d0f002c0c48803e4003602000e4500000c90400f6100130792a4103200030f00c8251400d2905101c008240c207030450f602d51040400c900221455882101c2e80d038050201c41394079072800350950751291150f007081d034000c01c400e118024502c08074810801c022031003a40c002d81070f60780c10b07103c000e0b0401a9800780107000300000d00c11a803d00c20014042c3d01c4640b2468612a400701103244411104c1c241014013a14601a0707116600c0781c4010f12060226603404034031156031070b52070301c2c225840350b01c0450154581280d01d00001003501507460b0104040c1c0c0c1c16046038035803c0c010340b1020010b00030b103810700d80e445280e514051b00c541c1020300140700500f441c2c7c0003050840034602c03000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 325864424 1250 325863174 325863217
    0x309030c030703020a03030c08090a110301020714010501030b22030305070509040203041b0603020a05180105040f06051e041211210606030114160e060706060303030f0629 75
    0x103256a0202e00143c02603802080d5180805525008250131101c443c64070036260b0030040066642d4610300d00c0006d000a0003901107010b203403030135810b54200541103034041d0301070313041444000d00800003801306490004d800b81c0000c3e40c3c1070b8041c030602c09045203e10303c024a094241c030104d0003000060590f00800504001ca1080c035170f11800950300803030150400403c00c480004801b413003c0c0c2603500c81018140140012000c80da0400180c544410703400552038490f00000740100c070b03184260307000a03043c000390850108000381cbc4400608040b0612100c03000e00c8800c4400ca040c61409203200c0c000c101c00d80b030140c02000401240c1811110100a0400711601448060b1500325940c140306000c1c45a100b030042009500d400d01414440112943e0004002d0814040d140031100d480040001031004201c2c14000580711501114802900300c1001c00585071245401030141540c07011200f95907041400124002c1d6201d0200d06401c41042507001c61420800040c669070b070841c1158242085101d903d6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 325865674 1250 325864424 325864447
    0x16030513090615030e0c030a060b0609030102031801200405060a09051005070302121204020d170d0501030201170f071b0605180f0a12030905030c0d0210060e0417030903 74
    0x1200e01520501200c0c9815031554000141103507102640c903551780d4010000300515440c041444140203401ca2804240e1a17020f20208a051080c104500c0c0c15610000810075821480d5a16072800700191000780710382c801c803a80010703803800545580411981d00300b00c204414a1b00900411031072600c0c0c04c00c81441d0f075035440002c920500726540170f40031501c0002c0c001d00709075040c052410202c510301c1c0198100601e510000004000c014030080c0603225070000002481003e56220b00d41c02c0301078a0848d81d4440d060311b01c0025103428031049000c13030807440d0041d03503800b0312072121403080b62540c41c8419260745111040716444549041c0740b100c0c01d4240384000108515004141c0300f8141150b80c85003a0856107842490141c2d640d03800b20f4903401c004000800601c01e018600c188450038a004502c1ea04075082c03103170071442900301d1403c00380719420040b241c5070380200740041682940d00701044141d54030044030a840c0c07c202c40c01031141030491440421654100051a0041440c0b800c80c3d00b044d010444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 325866924 1250 325865674 325865681
    0xd03110f0610140109330201050603100510030204050402030a0b04120824092a0414120607030203070504090c0801060801060f021213150e030601050f010c0f021504030c0f0801021603051309 83
    0xd06d000181d444004200c12401c00300036250034520302140811480c90103824138005103000780402842991600045415507a00b04078401840e03400c181001500c0c1894035220880c6400c019080c1d010030074540000b4444880c1941c8240c05c2c0c040444191003110b0003c080001050b0300805588210100d25031522002c03c50b944103203c0452240c8241c1d5645007003c5540090070105008a8400c40300b0310008050600c0c003180858115510f4140075890b500c03410300c250364501540c2c00020030b091070040d2054070701c1e80c00142c20b4101d81c0241c64099080c1d0b00e425007103c034100b0010500025034040009444120b900d040241a0780203010b103035000f00b40d11380c001a02da0070b41e0041840009070081d541c80d03041d0329052041e0b81c0181030488011402014020000c0c102e0280b81401501c06400a03071705400350345520340c5c000380e40c081d00185c84d43e44075140d04e805200e01d00c0074000e00c40f52803030310000440c65000510032102d08100003000f4209052003507030110b405512014460b40802400c410010b04400c87c1c1c007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 325868174 1250 325866924 325867019
    0x90c020102090a0512100c03090b0c1c0203130b04020d120c0507060813200a26070f0b030702030c03040b07061401060e0d03110f0610140109 62
    0x6001690b079510203000c2000006494000d03030b2007141c1200b0360f0218508009000010008048404546910101c20580007010400c402900d4007560000b004181c3c10700000402e2040c2e20305e240f0041001b42c00ca11a01240022160050440e000e81c042c0e60100d2455511207900c244001c01c071680004581e950781404a4400e0820000b0640c0e81981e541040307800d000c0c0701d02074081c51401032005d10305109241981914a20060400e0700804102606501110400844c2038002342544000c2c41e40c81d42d04004d00240c076007030349022a4855845600850300400c955041700d11030081440341c01c0c28080c06c030310310f0390001d0591801e5100810200790340910500c0500001d00b449100c4503101d81581c2400381c242c600003003005038400f40c031100600c40c142c0c000c00e207a0a00341c000c0d0362040a42030940340c00e891007207011035140b10f14825188070100c002030006100b4440c409030041442c0003542c0300ac000010151038001c3e1800300e02d020809009020302114101030030015078078a00368015044410418800000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 325869424 1250 325868174 325868177
    0x2040212010807151713050106140411040e010b130f0602070510050a09060302130902040b0415020d020a0b060409150c0305100f05190b03161202121b04090c 69
    0xd900410100205000c818000c045a00c100080d0195032100100b5034250b00e0782c2ca054411020b004a03404403c01d8107440c09075941300000f04049512000f048032a680c00f280f17124459030400b038195021540c148161411a064560742d900140d091034a020f2070390308246103820500c004901c5c0080e44208a0b50131500401c1d15401618106007080244580c0e140c6c412080b9040c01420050100090381c0540b6620448126140050301c0e0b00302e1224081c40c01c0c0899200d48030307050001c40e000c5050740c04900248101e40220138940b00c0c10b07184010998403204155807034400b40c1c20203080344001c1204404c40300c1d4402001400081c50b4aa2070f500c2c01c0f0010030744040c0240b00e0b9601c8105240994041c800c8541241d60300e40004c0c030040c0707440e002d000d8402c06405800c1c040c00914105140c81c00d45820184040d01381c4414680c3c036490040c1d100e040740b0000c40004400950b00d8102d08821440d5403088800024141120842d19513562200455070405002c003010615804c010008000000307124545003920036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 325870674 1250 325869424 325869457
    0x30408030405100525051b1006080d080f1509070e0f0114040306020711060f0706050112020f0f03100e0c03071a0301030b2208030f0a0504052107020402 67
    0x28281a80f80c1008040c403452010301c0c00b81802540c50b90301090b03070000303002101c0044004105910490341802100c251000314640d06080c080b002c00085082030302005504c008200e4181e03102d0900f966182341d1854070000c500300001180c0f00400041940d5880101454200c52282c1d4000101e102018111011000140601280302c00c915165000c115600c4003440c00d0100d040b001c0765200d010b072186210007010b1a41c0080d4131020407400000702208003800800c0a40c4600031106449841d62104404075100c5250800104081a00d4408a9644c03a0054403406800c1c5a01042c441e4001182510300c0d89440703040030720700d01409140158009a040d810203804030700d26030014145040a45e800c00a00d211019046081c40342c2d01206490449402c0058040540c503915024089119080201d05084045070030000501c0208001980204003505410f1101d523500d4a44d80200d6070b065500405030380155440842e0000d012001c095422801e43e0902c0c03802805500050407070b8400180480380f40350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 325871924 1250 325870674 325870681
    0x3070b0703021213050d1805040e03070b0901050108030414031f06150e0306071808070f0323100c030225060e030a020d0305101203020c0901050105090d0210031103040803 75
    0x80c94500d254000c0d81195a6150281e02552003a441b586400380100800240070790004a80404203041001044013410030081920b050343c12944a900c040c1c000d60780710740007401183c46110140329583c12940c0305000345042505001e042007186602404d041d9141c40b0f04160078000740c1585a890583e108401c00024906103050001c5505240d080c07a030109200920806e800d85480c0400c0940c1c0c000a41e207801505190444100b101d145015003125043d40702d001004610001100505800d6030700585c04079544135412103220162800c12444031100e1341000c90161110f0010782c00604905100741000740c07c0818548480d40e1074440081740c140084243d8215105111661242c02500407000001d1803800d5049070019554241d65281c03042015a00c00001d40c50003002000d0b43d0182586039000070195486040096490600112a070310451160000040660142048030100711001c0e2556032028040c0d02040103240e010091602890b032a048801d508815540007184128450b980158407400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 325873174 1250 325871924 325871947
    0xd080a0b01090303090302090406021c020a1209081605070503010e1c02070f03170f03040516050a081e0304030807031d040204120209070c0b0a0b0f0d08091203070b070302 75
    0x9003800141414404148424004030740c1c012400d80999030142c4040303045840354503101c80240b1680409190500411000c2441d0641c1038000b00f003c42d03c980e95000b81d070404c0c94003050482b006600e00800121040010801c41d40300000d05040e035034028000d9030300e119540c0c0042820f64a903401290b10035080004404604c43c86980e490703110441510081a50500f440b40103580d031070481c00041c1502d504c44078020802e600c080c003190354a07410400f04a03100e0800f846d240c0e64803102c03c84030104440143d000810541008041c0500302c42c0070318001e090b400071040d08004451000300c00d001140c001008040040390401c001040403034440d0341c421494150700314202006402102c3d620744201d004000c03c0048903c4c104e4100380e02501140c0041d03054560b81000c1d511071a540b040200020010f40801034244182e500102c40c244007030f2800c007115141d840402680300c500c00001481044107120500341800c0588440e1154400700044074038020054580460007a000c841c070360300281d000600c08001346d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 325874424 1250 325873174 325873181
    0x40b0a06050c0f2d0a0204060609030209060d02090a0e0c0a0b030907090203070903080a170114030c061908130c0801050a0e0c0112050601051204050102040302010f022803110d080a 79
    0x160b520f00a020412844415010002c0c0c01c10042d0840080e2000104031421044c400c0700c0303607581c1c02001041015075031603024006108512042e8403450305c45002640300d06150b1400500382d07030300034151182580c42900c1c0070010700710131181103074910030400351064a49546001c9030141c0000c2c01d49980324502100a03501d08242900528045401402400700241d0080c0c0b2240980394030480e402c4d100e00000ca03044510458508070b41c0f03240100040000b40a0250509030f481c5900203605894012241d80280b0000b4440c50795422941072100700c04401c881d00c00c12819802050310001e07484141815240c00c10740d007500d50440d0580b6503544c8180030308891544075540c504283c01010f04900003140001803e08218807801c080c02d16100c50014a0a82c800c9040303a94080c45507064902c241000c0c14442d0003908a404101d0115811170703102c030300090002443c400044084400d0000d01c0301000b000024900d4581d4048007440429601c06929140c28040e0b0f0605520603510100d00d031510303250060a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 325875674 1250 325874424 325874443
    0xf09040513050c041e0507030c110c0d02040903020f060a020a08060a15180807090e0d0315140301110a030e0607030e070501051303050a08071a0c041202040b0a06050c 73
    0x2200791030a2180300150011a006110002c02c4400280c075a800c44202d000e5069900d00c41c4c000d007440c0908200d030245d00340e4001f811016043d9910350103100203d08807582c0e043c0d41c4160781d03807142d21700c3c0072880140b6164101c0d00905101e44141e82c0c600000070b03c0a03207040c9050740d160070150340200c3d580c0900e95008404a40c000011116861124580300d1140485210400c035442003009640c04040b4521803140018010302a000071038041c13994440c01031008001c010b1540d8150300a03116820a11446409031003e1100c144201c901110324103860035900000c0fa0142c9501552a490701500c0b07035080c40d014040716440c84d1008107010a03035409280c00c0c107100800e0b0341d050600d45144504120300005218007929000c1c200b1a03940d00e8010010003030a000c07640024014800c00d00d0044c100455030024110061081e0410303c0e02480c4440704040207a8112904850b402c401d100401483c082e501400c11303135500107000020401c0da1000810003a01454205001244c40001c5142c40c22004010300100b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 325876924 1250 325875674 325875691
    0x3090c030d0e01110c09090307050c060703020c010f0c0b0115030f090b0624030a020a08100b09062802010b1207051014040905070c060b060a0f080c0408030f090405 72
    0x1e081a85140604015107801c0c01c1c5041042c0502e8100f0164001c00080000707000041850419140c079221440e904c0e800003070704454034003500c1e0005240341410b4066405083d415005012040d0954004540c00610310011201700540b0f05036040105013000750030350280c401800c810540c1140144081c00740d0705451040c0c0c0105180460300000f01d07070010303011500100c080380d8145020601e0f2414601d104450554441a000d00100b0312003171319195801003c0f90705071900c800c0003079034503070240c442100301c01e03c500c40c200102081444001e240403c0103120400c0726280303281103e03903034103e052800a0000a81400f50791f403490700c03081c545028410300d0108074042c00101140360606001c41c441546040404081c0090075550b070786104c4030001600c1c054a00c000d41001580340103403004160001445054407501d1030312007000c00c1c60600400311540c4011680340e0070005002d544e4202d61003030000300100c1c92114180302c0403620b40010f10050400385a8840703281d8684299404000843d240a0b10342103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 325878174 1250 325876924 325876933
    0x25060212062d060d0203100503120406090311060f0d06080106120c0302040f09020613030b0c030c0901180f0e040b0a09050706081036020406050d021303080304030503090c03 76
    0x1001901403440b4600b03a41600d03110280782c18480200320035014010f20050580c1c0084200494501541150b100b1160200d00700c038120a8206984041403145025680008107040030920200c0c241d14041c0350840e0340034040629008098882a00a400040310b01c078501c2e44400c003c00507000d003401020060400004040b540b915180d4a50210848a00c4000c0c06191503804035580000c007580150300c17958014148640c1c6e100709109192008056008c00c94905007001e010602ea9040201503a20614051320a0761608a40800541e407030031350304a07a44001c80010002041e810417401d41c0b0340c014000030131228884e040501d0b1074080d006000f03003030407a514503152182e404500001044030480d0b08508000da035588600d490382c0d0801040d0342001e400315907059090b01c1485406464140192182004000ca004100e144076080c0c2c41a44240000180140081d0760020042d0f030007858898040b13024004c103159656600c014580045509802141c804010003120100601c1703a52a0708104a0142 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 325879424 1250 325878174 325878199
    0x1020309030d05060a030b100603110f0904180501020f0a09090209180a090b1519030506070f02010615020c100302030702030f0702060c0a1103010c0206100302062506021206 76
    0x1668030b0041d10404031129440d48040342d2103489211154000e107401142c0d1031500d10345518100f4800307905219071030004c0e103480781c4881085038510030f54850303000044036645030412420810010b0004e010141244040b4a01c500c40054001d10060140500c8208029102e690120001e4540390141d031040d0310803801044050269954400c50188045255506441039155900f200d80207160100008000300c6201042c40700c5502c0c00c500d294041d00c401c031410341c4441484841d030031010101c8c2c400280651310502c0804d07151401440c40a04c10f911610000401c00d650781560120040b2040321040543c200b60b119455074100443d03821240d00d03003401e055186040030b110080da80c0c400e0001e00c01c81031707002048180855840e5411a854825100200e6051040d2030802c0c212803603c1480c01482586048050f410381c0340046019803281000c0b0101846aa10b0358080c4a10307644820410507a03880400701d44018161040081e9071060300402d00180c590300c10300c0a1403019400580360621620402c4a01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 325880674 1250 325879424 325879441
    0x61d0309060304061d0a060515040b0a05120c030618070501052502011e02070f080a02090c07060b0d050d0305010902042103050f0d050a06060801081507020703140604060e010203 78
    0x882c0e401035440000018413144404e4200342c03188150301d4418503405402500028082e098000394041d4502003440c200900b0b9080401003150451880e143e000f01608004020518021400075007610b480000c2c2e80706a40202e000a050040443d071402c4806401ca460200c50003040201501520082c20520300c0c0c061301c0030440c08200c4140e00c3c50b03100352103e82540c0d03045910500080ca0b000455270f031281252071100724042e458400d2030040b02103240940d01c0024044000042c0b41900a4014010719141e4954610301c821070742c0080340c26904591500407040164860000a201c5e00c4c0c01500600201f9091217001001e0302d4040c0d000e140c0b4a401400284007040d40048520072495445c1d5040d03c90034544c0ca410f0b40c01e401200140130a241011411408005154000e14030402d08036008209840e2500b0060f61041804e004003103040d07100108000a015021861a80100032401114241c540d40d9a8590100c80c440705507411301d801030010301080005c03034080c0b40da50442490080d401c42c9444081d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 325881924 1250 325880674 325880677
    0xb070804120503040b0304120305070e06180604080a12140901080c0a11100b010e03010c0503010605070507080a03050901080708160507080d0603030309031205040209150f0904061d030906 82
    0x90640d88070994280404100c81003040710004c001845c0392a0f16858142005003032040c2001e081000f090400c40040c3c1024490090500d2002000b0700b1141808091040d8124400d02e00c070180341c00400070040031030034a030100166003000b480303a4410441d0410458000b00000d0402d9007005901d4424440343e41d00341e8100004503848866001d83c0c949400d00124221007803e04d421030a1054000c030300130800402c0c0c107a04442a901000c0c0c840c02150b600311701c03d140c00c0751030000c0c0305000a4030510051090030300ca00c008001041c002d200719000d054031280020709204404c002200860b00024040031fa6581003100705030f101c091400d03d45218500450700de02c1c00c249a020b000c00b003050008a4400b080038600035211079000c40441000341d42e88a1a01600504001c98150042030954072040c5c51000c40340500381c40785501401c0b058441d11109032400c140108550115409007024070006103c3d202c3c101c16034800c1d80038010200d482d01c2407042000a1040000302c220030341d00204846060754481c1d50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 325883174 1250 325881924 325881929
    0xe040510090609020a030c05030d051810020708030d02031b070309030206090a0924150c020d08071a180a0b0609070306050a0906091109180403021221010b070804 71
    0x8101c803541c91030300800804803208001d601c004520000300c2441a580c0804056131010360880b4000748a05070140c038507008003448082410011180f01c20503040010302124400200c0c01107605c19030b00d0b0824682190000c05010b0526580030040103d82201c404480311031007100e501c0e0a24181c11524024440081404081d00850002611050307a403a0140404000d0060450030844c0c1d911f00c02c1c00418140c050101544901d0f200780300400d5141300ca4410101032010750702c1d404600421a4240700c40326880745425900e02800340030190101d80300c100f04c14040041044490707650320341448841c501c4081c901c11801c0960140000f40c0019243d402141e070040c00803140700741c5a95400310128060181078000503005624903100181b00c1400c0e4000106540c080002448180700c035103c00b240301d02038517000390361111600c2c0304000c80020381c0c1d4a80340c12500034070541c0d10086042c40c00614036442060081842a40320300036240c400040301070280500100c1c1106131134186183c842c0d1500380030750b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 325884424 1250 325883174 325883203
    0xe0102060f10050d03020105061216031b09020a030e0d02060c0f0309010609140f010e04030e0d060f062d12120306030b13050d0c0b150103020c03070b010f0e0405 71
    0x300450b0b0000c0c0348904200050000518148214082d441d00030b0103020251146800b071980f007000790b0303100c000105201440400c084a000100740c035589861030034080c0b004120410305100140415500381e01d000030103e102840d100401c0d1031001c880410702d000103084003071085400c10230910141c01281c1040b2031400c6a003c842c580c894803840301c03e50042c40b0b280d001d07910315490700e1441c0c0a40001100d890b031003403e011500412507071381c8041c3e8400c1c904007110300400248014101014074900100744c901c000b40100c4d400942e10744c0f0300440400f01d4a140c0c01214241e0b08860800000703402540c81243c0344840520024200f80c50480b8020004444210061800f940b1198a2110521070707841900110307002201c074a481d05000c4107080c0054400e103402d85141c05a2411100c115000320b001c169003550180c04408603644860070900039402029582d810540c08200807074101000b04041c0141601516155503294034080c0c015400805550140d4507031310400e41000013080022420381c0c0040140c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 325885674 1250 325884424 325884451
    0x3010f0e0f101a0f03010e040317040b0f0903131419050f0f01180e1501020a150c030b090c0a08091204140f04021305010306050103021215061303110f010e010206 71
    0x2c9a4140c980605025000344c41d03c00720002800800402c5114000c50003515000d81258070b100d5035035100e50040b58064510040440443c50f003816500149501c000784c0700c2940d080c40c6540326400e40c1c2c0ca81c40d5020b400032025402c014034442c07401c0a64403100401d9032540000a601d00340205400c0c9200c0c5158030300c100884003040610340d005440c10b04449200d441c1f10071446131910960105513800b9110751001d52071200111840354000107660820f260000d288260516003604140041e1041c803642404050715100b60a00c07a40f603413a82d150103041d82d450142d40b51704008400902070300c0000c001d0103682d4010a06004010204001c0f034007a10f41003c01c18004100e1200843d100440002400d0740040c400110200080d150450501c2a580240c1c0c0034440035588000440a80c004c141c95860f15620600c0410002e04c440114404203060141406040c40e070903c00c070a42c03d100a600948004002c004500a24078010007052920710007424098080e060041c0001d5451000406115101d903a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 325886924 1250 325885674 325885709
    0xd0c020d0c1a0304120806182a03040506070f050d0c021218100806151303060212011502071220031603050106090506032e0203010f0e0f10 61
    0x407a07046000d000e202041c20080a490010300c00b2076801154244d400c10010000307003042a1041c2500703805510020003200d03621200500117510242d000c0c01400c59038078141074009500900f503201c0980c6a40700620161203103868246a0b0a220f00205000100521910100107940d0090261001c44040c0a400150030300c0442083e407900c58500300a90414074082000480c200044c048814185400e40d1100b9a00951004c02d88032880c0555103d03030700c03172144d0f0700490044520740007038031403400c400c0c54a014079507072921014100d07400024032078404a2841c3c0144038002a448101700440e000b440107200080c038090694103842d2031001d00803d4020b49482c030203801c07198079410390203c000003029603281c0325044200d005403107105c0c403041b1920b500b48200003500456510503a03110380000380140c1200c19041d42122101c8003882d030000c1d001f0705402e8200d80452020720285000e8150304022070005414000d190001407401484075000d24042810051a032544400f007908030f0b01000d020700304500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 325888174 1250 325886924 325886933
    0x1401030c15020a1e3302090d0209010303030203010e0c0708030f092103010807060c3809060f0c1606180f0c0e070207030305070209060406030506091b01020d0c020d 72
    0x3c1c08000a000d0742c42c0d40803111401182880380061a900c581d54a140c0182c0c02182d00120840b0010056110080000c8203804441940c00501d50718200038414401240302c4e50004c0e560540a030001d0b40000d5001c001803281c6103000c2659500700103500d1941e0b082c0b40140c0e45808035440021f200c002d914000c44040b440158041001c3c0782d0000c141400941088452034002e00c07181c1091090741c0b02c44c8910340001440d98025103c00004540040d0f0b07200d100e6850b60403405800c3c02e62a000c4140c0b001d21306650090500f9042c1180c011950000030305603a0512a449401900010341004030040e03080203c0700d0030030b40e220f01041e031045c0d1040000c650030703403100c03540e103051045150b01500f280c149200e144100550660302c08161101c8000324581038035061400c9035545124000240400e0003041080e0162402034040e540c0480020800310302e440c0c07642e8070141014400e0783c5030725450b8000300d580515180000c0c0340c0c1c800c61074288010140e4170140d200082000140c48406401010003002203018003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 325889424 1250 325888174 325888183
    0x1104031e0501050a06081009081306180509060d02090c0d09060b1c03121e0603030f200c090c09100807090806040b0105010810050a0801020403061401030c1502 70
    0xa40d00404029400e12a1455961100c25035100440303103540b8040020389806524420391081e00c40c44802401c0715034031402e11714000d0285400565648000780320003010040309030314400140905540b61049540284050070307e0b1681d9403c0075100d0b030219010011152600a10b11001640490b034203050341e110610030045500c61b100301005441e0400010105112090b0850910040c0079144190441c050303155a9441a4084030020000b42e102000c0385107403c199041521401a14101068402d8014010f00c08465003648100c0125858818180365150081d00010011520b42960300508881e100300a84603298410242e100b81543d81c007181101036000d065610400000e0400c000c01b0500000140410908841560000c0c880d584081084500840c1c19030056034003851710500750b4213010040d200480d0042c4880030100c0192800101581e030002c1003070040031030030001a07480d8154108901540c41c0c82a0058281060100420000360b0140819084450800710400c258507580340403400c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 325890674 1250 325889424 325889429
    0xc03160e0c1e07060906181103031e030a110a09060f0206010510030905031215100f0f08040809041a0f0604080303010603090312020d1d0c01021f140a050711070308030105041104 78
    0x103d18141c0c8007500b0500300421561f0785401a00d072000200340d924100b690302d108042c2daa030f021605660300c50b0900c0d01007002070741c2c0004003c81d0101e541c0080c1c00302104d8940042d1074100015000381b07010000680c00c50f1920109038210302c003401140d810540862400c10968403003504142c0d481e44820700740300041c0241c900102c5820a00d07441390130581485100b034100300741c103144108031a0b54041d0485025462030201a201c640f507402a4400b040c40555803003070b000300309540b103160422a503040c55446110381c10030700c40e903004180c00c6540d08001b44000ba07117480c030100b4020030741044184600a000000c0da41103821900c1d02207030f125594a400c503012242641c0c0e5081c0c80c0d001080300060403401e17411203800c2e4800c540300f1846140c00301d807143e40d541c101c03014010f0150700418000841450064254041203210b01d001064090300008004003010b811035000119542e41ea040c0035034a64040d80d40390041c0a0140145403150968668924501c010300c00d5522942e0364440f505a16003941041c2e600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 325891924 1250 325890674 325890683
    0x210201140f04030c150c030903020603061309030801140a0602210f0c0607080a0603110f060f040f080f0d050d0902030c091504060f0b0406110c03160e0c1e070609 71
    0x200c1c2c503036918081400003070f180180c0f260710300c58aa40c80e07101d61241c80800c00c90b903050790351504040e2441c2c0130700c121503101501c141e410914890302100340210500903402070a20980c0c0301c180c1580350010411450000b2001ea0380300d10042e4508001666000415541b002e242e441c0e801c601c40d05032143e0601501c1510b03000c000b00440442d03814941c90001c10503a114120a4a40d00b40035030f591710410302100c1c50350000501100c000d500c0100d075401d00c260b42852a0002904187c80d0510341902d091081c0c1007617100c0c149600b8804414000c0d0a02400038411400b2003000401b094440d800c0060403500481e400300d82c9140e510a014001d641d820810a102c03648050918104c900304400b68400c002640402c83c0d02917420880e00180d50044a00c60f0b40032104201d00d03090038203050a504032005407544481c2802440342000c3ca00c0d05035003d00400e40310f011400342c20b03d10586444080a80c0d9000103004038001c03181400000c41541541c05002051055420210b69030400e900c3c2ca0001004140409032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 325893174 1250 325891924 325891927
    0xf0e03070825060c080a1101064e0b090c0a060e011b08090409080f0a0302030642190f030b0a050d020607020315070c0606210201140f 59
    0x412020461a001d5201c000e5040c50004107444007426500440081c8006024400c1003140c060345034807d240ea203480b03681403c00861119695a01070b604c81040f032114084040c007542c110b84607003445c00800391040c0500e40d4218102c4138011038980c1d6181240c4c0c1d0142407042d0b403500050b80f105090000104400d00102042c200c50707101c01c00182185017442c0310a0101e440c1c2c001c4022001417104584905541c01880b00e440d0a40400602014180014003114402e82c02e02103c01504400000b80c101a5560307500142c603450102d08121418100780d03404104260140800c4800500415a904810700541c4481d10064040d008a0300d191180c0103030b80c0c210b86040c140f20705103650b00104603100c08207259014800c10514200b04040468030b1b108540d841495660060010b007000e03c05410380b64001810f8804841c1c4140780200303e050211210800110500300030401c018842c8584406001c10008201901c05546102406901d9a02001e4140042c4004600b03102c00344204440b507a4002c0d00285 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 325894424 1250 325893174 325893193
    0x110307050c1c0f120207080109060e06010501262203090314070e13030207080d180e15130e0106030b160807020a030c0201121e050a0b010f0e030708 65
    0x103030384540d000100907115800c0305075102004442040c44903490b03a007004204243c03041c1a518182c1070580c404404c0c0541c02901c0740090b9401081c401d2203100c42c003441000c038451582c95005818170794142c0006040c000010a00e58403141c40b4460b40f20b10784812074100c5826110080c000c000600c0f602d00c071080d04085080010100340c1c0c0600c52004680c810500000b440391101d043c6625512103010b000d008480c118001442110301108c0021624064015507041944550788107041010f0401844042106c003034101031074403030425142c00100f80c035021820080c18840101e420303605c60402d1440c4500b014406140c20311446038450103084c4400790080040c1652407401001c0c0c3d110844011003000303408540303010012b004228481c419004e65000d406541003e0303070240c9a61452450580c10010002100030100a1500c44c80100580444d007524040750f45c084000140c3c1c0009100d410000d0070100c5410503a60000c484504030316030360400d03000c48000d000101c3c0c070b03000c40f55019465600c43d02043d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 325895674 1250 325894424 325894433
    0x1905040501021e0f0a0825020d02060901020708070b10080f010f05090c091909120e03010c020c010206062101140f011a030c030c1201030804090c030501030c0306020a110307 76
    0xe0000042c0f4103040c03400c21200e084601014041c0405a0590f40e80400c80c3d1000c40380b1600c0103c1d4070170400064100d5034843c3c5500f80403a0032004200b9400b6a00c600c090200f400c1d01044003503486100314009602d0720b49a41d171085014054180010400c0c410603000c00e0f481d1300340314500b0700581316010480f04500c580f0024103000e0001760400e0240c1c01e16010110319101c1010842c1140450041c0085880d0b445800fa07c00b1031301c00444175800500da89a84039000260421820351140c5100e80d9413541c4058440209800c40e45401c0d0241c05550003030503030806d140d030081044ca61004c0e040b00d80103070051442250b20f0b103405a0000825007546401800142000300f801054081d1501c15504d10701030703032250038880c002802d040c0003a02c186003d00004908040b6400115806044500c0302d90034000100b9070070700968020380044030180070209007442000501c0c03003018206a200e14040c005c5515503203c0d482030a48600001d0700d0300e0340002d400710b80d40303028071000740c140b141c0f0300100e0343e0b6460315051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 325896924 1250 325895674 325895677
    0x30b130c09170712020303071202070f050301020315011b0807291e040303060512060103020301050903131809020603010f050405010f08100b0102120d1b0203041a03190504050102 78
    0x500340071409012001c100c2e408103480000150241100401805003840150f0601c000c580d5804c1360306200401440c0002491501128245400c81d00141744240c10041000d150361410703041240a68414010020443c20344140500b48910030f00b0180300d81403004080075202004148050040480051208104101d0310b0300350b0b14030f0716548008000c1003a8100b503091010b5042c1c407a024201049607031101458070004400742c015200341000280395070350f040441c00c0305038000c0c4421600d030040d03401007041d420b003030084d1980125248007462504e2009914103c110f006400340000ca4184850120314041481d0b21400c001500100880d4903980e64544c61180d828240c0150350140e07092600004610b880503051f041941c1081c0d0140c4220f199801a900081407c904101e046125004061074854904002405180c28800f40807030341140c0d00d0110542400321010070300440d030040000700480411290345182c142446003030659a5110400b0781d1018824a40c03038288118500828407080003c150f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 325898174 1250 325896924 325896941
    0x3120409061a040303030b01090e040303020a021209011421190c1d060904090606090905011410150504080115031b060503060402070201020307050a050d140a09090b01030b13 76
    0x340c10320241c0e03210500341c4150101d250510580312000d01040c070000b0f009130414403200f4010f00d00b40c40041d030f072600414807110042da81503012a50001c0c403083c245d40d06114500613850b80548107450311045000003819040c516941c000e01180c007155030750122070b54519102161426512080c00d034100315800c440d841e005010714801d100d00e00010b010402c0e000d032801200000c640c60030000c00859400134000350354041e00100ea401540c500c0040d00060740303072040f00054102928001589800341c5002400c648200545001c080ca5242c20480101c01880300c4009a1f5601601500a80208181520503020307a4000c00599400e08803c1100c0c81d03520034160003101e00035107400c3e120404508804840f490305016220005804100003121424241c000384261841031044a00c0c0c692591182824140d2001080701c80c0d030803c8540c50045035100b80c4401c4403041214065207003070f0340d500010700384240901c1543c024646940380542582c0c0694480e1180007405003c3c01070a50354a0006c0c0300505006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325899280 1106 325898174 325898189
    0x10317091c08210114150c07030b06130218011d0306040804050315010b0d0906060e100602060c07080706020c0102040320131413030e031204 62
    0x31500041c04a0160000300e0b15031510665400e00740505416031000c4075074040060141c0c1802c2c02104001d10b10407204000c0006105403095041d00031022a800c4a008000c00041400f01c00c400e8107104110481c0c140c0621310f0064900d400701c0c001d902d0808007071b08910003a40415405160160030000d03121602120301c488107030009141c0340085504403000040403608000c1810b0811484c03072700c038040c00c04480c065814990f61550303d01401e102c410200c0e4851003158240b00c400c0c0e220300c01a1450414160306483c000d50710400c0340505108040051054500007038150f90003006507200564030044d01417030700d8080d88502019400541c6041050f540c00c02001001505c4142030341400f40e408040048541c0c80082007162a20041c48902081424012800c20103005c81c94480d5121128401e1014041c81d42d0504907081801000e840e03400d13101d54101c48500c1c0da10903014000311a181c = true := by decide +kernel

theorem cover : BRFrame.Cov 325719424 325899280 := by
  have h0 := BRFrame.cov_init 325719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325719424 ≤ n) (h2 : n < 325899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
