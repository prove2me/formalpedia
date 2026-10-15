-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4781
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:34.433527+00:00
-- url     : https://prove2.me/submissions/a4a21fe8-6363-4fe3-8cbc-9fc3e4b79f62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 859712230 ≤ n < 859892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 859713480 1250 859712230 859712237
    0xf03090105030a0f090302160e010e0402190308030c09150405220905010c09081902060301260105010608090d081009020a0333050301050f061215010617070807 70
    0x2064010054540b900010000703da60750361030a01850000c2a40122211284640c0c05014405e4510301c0d540307003a43c52500004800c08400c80140042d0720080b5065410540460b20101c002d0507440f58100300000716000100038603804424170400c0c1c01544060020884203c400a1858060356183d41d1a80503610031160301620b0402241448001c14070652103460802e07402092107071480d210070b400d650000185200041d80d000040000400c00d10078424803000c90144102046055000200d007030006006604010900400514006146004507401074180000070700c51503a4500000d08010004c4960a509014086000c841e003031040c42d030070b0701c80c00c02800042d41480c00c10b50440020b40181c00208107040d034840201c400801955928403203200c4800a244058020b0103404082c00c51913400365010f43e040400f07203c0300903550954203600c900285c1d168024982002030652500c034984241d40041d07001980041000c50f44007101c2c881e0211350400c10300c2d0b1a2103000049480c20012076003840003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 859714730 1250 859713480 859713487
    0x4260f070f091a031506012303010e0604020306030c131401030b01030b1e0a180803090c0a12030e040902010c21020d09150e0111100b040c02070803070b0c1c1406030f03 74
    0x2081e90005036406c030f50180b5201840040c01d0410b000c032045481c000c00408a03002c0010003d24070b00e40100b40d07100c07501f60341c19030540c02c20501095030ba14801049500c94214444001d12054513a40412503481d8880c040c9022540e607410300e14281102800280e40801c010780c0000c000300e0032410000c43c1d55041580152a55403803061007c01880c1101d0004a1035101c00b41c04008529018007441c0500c00341c1e8054405d9481080c00c220003149254031040c500c14081c9120800b081c1c2042e094100700609a40105015035941300495081d0451100105a88a9240c840a07848a5445598015006a003c03203829280b1141f00343c40c11b02040c40344108500c800d0050709045e61245103a00c141d02818103000d0300d90902d04041c01d05020311030104c0c001c0c2d80c0d0b070307032140c20080c1c60603002c1c800300110345001400340070707040c42241516882031420103400404440c0108400703a064604642d04034040040c0e02d00801100d41d5041e01520f160309607000700280c410b0104d069441d001c1544064240b03100003c518 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 859715980 1250 859714730 859714753
    0x702030f0a03081914090d08070809030d0218150a03180b010501030b01020c030304090e06060d0b16020304090f0906050f010b09120307060e031201060504260f070f091a03 75
    0x10f9034140303200b42c400c005444900300b21481d003c42050a002d4031b0b030f00000c0c00148150302002400044020110710812001d0f0040c402c11361004021610b44050154015a45e03980042e0007810ba01440c00280b9007201c0410303c107128203a01c241c060800283e074ce0b0b4013403240002e01040101200306001700030b401d03039140d4001044158000e50005298801c10300542d00c0c1e420540c000242540c000b9804142a01e0f1103000f980c100310700600c9119071040301102c0710f40c094506e603100c0b070f1660003008040c4854100590003000040307008005490080110030024007040004501040c0030b41005581141c2141c00d180226001c806038141d114140d401040303c86003001400030401c204180f43c00d40045050204100b540c0100d01c1300e028803c1944404401943e841050100da14034000050340031404024081c8030a0100b601d0200000282084112159201505c2840c04c80d040541b1030400c0c0c0002d1250304000500d0500c40510407085515020b02005408000512803408071010a441545504440c3c2c2000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 859717230 1250 859715980 859716001
    0x1080d0305060409170408011d0703060507020a0f1a06120c0103020307121a03060f070e060d061e180606080f1b1602030c011b06051503120702030f0a0308 68
    0x591042c0014000304146140303803510311211801c1d0205480000000505000000090080132404202000b8141000030113043c81c0d5152a00c0f40801020640c89801180c400c40c0f081003201401500015032a419160314600003c01e2482c4500d903c900000c140002055850a0107a411003260760101a003000001c03240118025840107091100b40450102000d4003c0f0301f510408440c1640340e6600c5102602c00400c1502d04407004080482005600341042891680a44000c1080602b540c1803a100d04004189101500240d0819488519004403c41d07442012052082c115000040c8d0001c210b0b00d411010300a80d20240520710101d0b1000300410a00c15001c41c44c19400800400c1d50030b6a03103276210700743e0340c9540003998207070741e1110290f03508040d4941807000000307207842400c10454110200c2845100d40343c40d0003000e00700c1a65900000c500081004000c180e8a01c018142c40c0100c1d1040900c005a81020509901920450380d9010141c4400100c00c0e080c190181c42d09d030019620f00281c4e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 859718480 1250 859717230 859717241
    0x3f030a0b0916021507031121150d11010c020402120402010905010f020c0d110d05070f08032502190602070801060e0c040b18060d0f051e0720060c031602030301080d03 73
    0x20006c0554403c002548400c2c0d2201505181d2884000240c00490740b0803c190b4440c005000d014001c181e42409170340940d240400d840380c0a90054082e10a00c680d2801a95824002c0704040c0d00140005401c0103001c2e0380c1c4045601c52f1b4801d0b01e80005ca1611030004507004e0a80c945550050b0303100221003a5285040000712085a1103280d00401d200425000302d002c40e0b003040411101c80c1c0c03150500380540004640403c0140c009480150300f4a214030280c420180148943d800700200b4802c54101075403146601e012540c11007003c1c0081c07241c0d50744070080d5114110311903007800707500c2c000c3c2c085030000300c041895004510080c03a80b818181040d40035082540070700310155501d26040d2546c80302ea00d03058040d001d08180403200041c10040c0764001d10948e44020300d910800c3c42031042041c0f180c0383c0d21004c160003042038034140300720388112031040f620300301d0b80c40711326410740304800800c040c1c070341e0500007984910100c244800c40702507202c100340c0e9070f8042030184001581083e406420240d00c00e5021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859719730 1250 859718480 859718491
    0x3031d060d0e0f01092d080a02010c02190206030109020f0d06080706020c03010b0f06030603100612060e150703020c01110c0109031b030f0c111309030e033f030a0b09160215 76
    0x488000d12080d65501c1e01c50784240d040c000540d448bc0014000c150b014800b6000400341d007009203840514942c00500148414040c4c40940c59010905841e01c00324201030320350003a580d090400949485c2d10b00c084e0b80d5101031103004010b10070703244800003070309043c010000ca94001418003004803410908000441c5c0000340281d03010b2284000c030801014060240a004007049a091081c200c180c0c100707502511626043d0040300d50146000030b01c41020680b286a112801d80f40041e19030003e1341c2c5090240c2415941402c2c8500e020a0109000703c0651003070580a00c213071141d0710f02060781825003d510b582c0c450050085000c940041e00501c0c003440817044030a108104800c00d80c041000010111100240c84c0d519682d9191003a4080541005503203036501c00880003440300030005880f41c9024180003038821158054010b00040034510340852640210540c3d1402c0d0303c3c9e28141c1d4815004104600300c0c14441c00104010640090140744042a1400c90b9806008140f2032450b001020030360103001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859720980 1250 859719730 859719803
    0x20901020c09040609020108061806010c083001090608030d02030723120a2702120a0b16080105150a2d030e07050a03031d060d0e0f0109 60
    0xa9008540e2040c1100e0f01c00d602c51a800a00e40310a40001403a000005049501503456841c00c04215030a03091125403040007441c02400998092800b51070601410030078240410104d442525003c03041c0e00381d4a00c041078030300403901e545e90725050401070b180d1901c5490082d4104110064a4160316002150320544600b04110a2684d20031082e200c00003000001442140100f07440011012a03201c080e042410900300f423165055400b1015030350088090b8000c00407550540700b10840d1039a04075500742600c0301c01078a228000c1030034100181101151020488007481d4400341c45d5a015000c0d0318140c07400a09803c0c0c0e420441c41c1c100e03511b0740c0202840790502c0110543c074414100c030aa008040c80310703080d940c28500c90417060064103542c00c051562045410a40d800c0c0700c203480704159042180e8043c503050355810103104100001c1e850a50007035402c03000014a115404440d0b40010101c410581c0444110780c071082002400c0b10b18603040100316001c91490b40c0c888003200d01c0c00540031011300c40d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859722230 1250 859720980 859720993
    0x412080a030917190f0f0e150313020a06020f0613020d0c141801121b0e09010605270f071b06050906010e0c1c09051506040b1c020402090102 62
    0x71644404030040075011492a640044c1c9220118040500d001506595050001100c0c00007003018086601c2c4075482020050b03800403198059440c10314824080201c4001c1903520b05101050000000716404260301401c0c0031400010014400540314011320f0b42c03c8003400064841d4040180c00b654006401d07644644000070380c07001300c0c1c505204003000b0315000701e0b00954600e0070804d2002c0000507107059009020f241d40100803480000140b0a40d480e8000f000544c4a50048448107200c64990400c0030084c0003082040b81c038807415030003041a200115134140400b045801050201d030b0000111400408514010a005090480ea1280c0040b5207040100550001d054104031003002d030070060f6002c98540c428010104001c4c400217024160701c003002d140e00e107480710801415106000c0d591000441000d100390031114240d210450059000c400d1300e6840700c80e46030040514106540c01803003245000c404000c2c034a440070a48844014003d045e15400d1255001c1000a402c02d98007207066007d080b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859723480 1250 859722230 859722233
    0x313030e0913020103051503060115090e070c1a06060a031a04150e181b0a030b13060c08010819051509100b01050a052d0f0406080a020412080a0309 65
    0x1001020310030812000036140c400103c0c00018140c41000d0007554600903141d04c440010348000c05d10b03a0640715110559025003520400031074800f50b82e6840141d0301640c00040c400841e42c40307107640e441c4078050b07101c071810749030041d50741450620243c60041d4440c2d0200011b2401324044e8100c2c204640c010455500d8200421000c5002e8400da0b0082c0c004602c4c0210301130001c2c01d011006150000700010f1500e0240d840d092005665a031680c40d000500e0146030f00c004115a0f644440c50007650b480030a04216003014181001c0d606581d260072103456013003e04400c0c00030701c9051018100c03080b14005200440c0109004080c181e80c0e003500355802d000c2c50000b01401181005a0350240c801d0400428050821030f600e5003c6034840342e100c9040080401c034400001d50300c0300a54482c035020300c1c2c5800000226842c4035032066600c10904240900201300000d450200501038811907049488850a560f60b011880c0100d03c554025030906d40580d080e00808100c059001c3c0ca8144414100000c034013245 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859724730 1250 859723480 859723489
    0x12060f030f0d0c03030f020a05041e0302030a0305030702011a0a060309150c05220e0c090d150b1801051e0604080a060218060306032808031f08120313030e 68
    0x400c10840114181c00f8250042581c14411048a048480303011030500c46000ca0040440c4168842c041c5540c90744002c1c00d58030344409604100442d0700a00f201e029074050300e4040e090707400480308103000d07500c0e2440c03441c600c108a100b882100325005100714001810184250018840d940e0203035401c49808501c074881031150721aa40042281e5207549450300b042c2c01805041850301429240510441e80d410821109001519904114001d1080e031700d428400011600414000314040e2488421002081024110380d00658030342105641c10300e010740f0311070703620b100c40c200a02c03402d90009070504800030340c0300034800c1c80d03085088020000c9103080d82d20014940340c109a10b40035a1825400615134062545110780c00121140c15106a41145004000039482d000c2c0b8501103200481c19085034a8404a0006044084da038000c0c4095141c0c109140740d541810380b440203203404090100b03800303e90300e2400107102c0d0301103081c0304400e440e50b5900140b8400305114a01d04a060107a540f04031040e5966 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859725980 1250 859724730 859724743
    0x60306051008070815041e02100c0b2d15060a090612050403020a03030504020a05060706020304050618030d0e1603050d18080c010305250507150212060f030f 69
    0x11450703410721460406194508020403a88030080a51000c8125400c5a84411544d580a41c0000004402030046d540d841011a40380c0002503000c10404c9010307424541002031400001c0c0601101551039441012030102d0100300c0b180c08003418241042541340c1142d010745a0ba010224202c1d907000144010003040142c0c002d25840d0380030600c03209050004680c0000c84041050a40c0e80501c502d0070142c80c0a91120350302c840280805440ea40000c0654854001c4400100b8010f80794554405503424070b10020340042e80c0455181c0601c0d80440d014921181d0910300301000b02014628020380000c03940c006084200130740903580554a2540c0c4d0044031111800700540c0206c0203013800c1102120018036811000c400742d528240001001d004010300062002017005081c2000142501ca031000c060400000c00600b6035888880e40306804000e9129010309149481000140589010103107408107a00a0300c55060070100000001005850031010f44103907024054150780d21014412901c034180030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859727230 1250 859725980 859725991
    0x15230408011d0105071d0108091c03090308130b0c1c0c0c110d050d030f0b040e0d12050105090a0c030212040b100801061a0a11010f090c080109050a0308090106030605 73
    0x10a982d00c5051006000e004140d0700c544503280107881042c0c03a030340114010f00504a240e04106540300041c40c840010011003d001c40c120340480c000d00072410008001d807518020442c0016000c10100345402202e2201c01001e0383e11034190101940c2e000c401240c07039000164100c0c1c410030307541c02c41d45071130307a05100c0c3d28035041c005c1d0b513503000c004d10a040000700306001042d117500a000c0d80d0209004501c011492008070452460042003103d00421140301415402c07000503400352500508c6c007a03080c1c0004808460364800e407140403035805103201450440344244101c540008807440040d42d81d0b0040d82c440104944681001810490612155070b640e10086508913043d44406c4103006c458490201000c0c01070005a00901285060070b0b078190400c200d80b904090035050105400130054010042d0004281e40c0390300030404103000c043c03004041e120f041010303245441022070205001406020b8002400c0c0c00c44002d2420031000e40c2c084070b895a0051022171a55a0740d8000301c0001c0090041a0044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859728480 1250 859727230 859727261
    0x306011a19031a100e010e0a0518221203110d0f0b03100b0307030f0507050d0b072c01081807080a050f0d020a03080a0618151523040801 60
    0x7415080340d280000d410b004000381c8240611401000c6003179004018608034002841c040c690751000c000811604202d540251364801e00000c9010444c00c2260b025510a41f801c1443c0c81e002c0090300e5010300310603e900005405075808007805101c60340039401c4000085071003200b0314030300724021b908002203c195601f508042d607241d44502c801407600b00002c56024107501c104001c1042c034000000e82d80c1c02148401070142d800c2412280c184002481f4083c020300c40601007800c0c548051410075051081240d100c0301046103e003160003903845030340c0907a002c4ca80f10441900409103075401910b02c40001061a00707201f03601c1d00c92454260050061030000d0041d4401400e15502d1858118100015902041c005902c14911f10031041c0d800100b4001a90700350415803065205c150381100542850740000c2c2c40794200000c0540110060b62000000d40c90101d200c4103150303220140740b0412400c1c004400300040d1404c03903900103208ca1016010080d03000058003494a41d0b42ea180701e094815032510520388 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859729730 1250 859728480 859728491
    0x62405210703150e15040f091a0108011107020901060806030f07060c11060313080f090607140f060708010b0a1209060203040308150607140f06011415090306011a1903 73
    0x41000c204900000b074010300400000034a0840c0840700c11300002a54284100d0302c07030300c0c0704101c7d40c0a60f100881c0b09404c05030070512481520f2003148002400c0c80f03603001c0c82d0b1820301071404150043e0240c030390b07855005101901c1640307010000c883c1440c01408240e414014120b1585003a9410040440202640d4440e40256405800c0100c0c4101004100b1401540c08104010210f404542040c1c8010351000515842e002d00681007042030007000d00c0260081e400042c610244160400d51848030710714a0101d031441481c1d09010354a800e01030391410041001c090050100b101da00000c1c100d41c41d401d291810007051004401d200743c4102e1942a0b407802d40c000140424140d1040e40143d200100424040342e004180700480c00f50700ca61203009d00580400d032100303060100c042c810b14458402d000200c0d60300756107518a040300021480705103032240038840c0c10000604107540035560152402000703000305a04e001384105d00b03a0b45007040c100b68100100030f0080d03010022107600ea00c01e025036400055 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859730980 1250 859729730 859729751
    0x105060d030c420506060904110f030c04090c0215181002070605071b05070e1312090612061a0706090506090703060c03140a09020a1215062405210703 66
    0x8964080b42c141480f8241003070708000554480c1411034070030000030b0320300068056a00300710544078040d51a00310070f2241e000040c800c044192001401c19984552420000300303004100590f500c0c0201c2c16a0b0300b4606140d40080c1034890f0f05000e03500c001c00e116085d280d04102c0300800000f280d000500464855985006003c510f41c0d210b00202652aa12529030802e803500f0344919543d009280300b940c4551200500052011000500d0803d015a0144503c07903000000d02e005071521805000d1540069492601c0c844018000e01500e4112900d81140603880c0b003c3c400d9900c41c1c0e03440b901d0280d80c030703a88640c0300c200000c10400c05248240d0002002e0310b521070843c6000015102515101d00c20503080030012441c00c5000c0d60354036040f803250000015201082d01c0810014006a800000c900d0803041ca003105004441d200203100645003581004019126004200124401d41100400381054060040c0c0c003805030004040d601d509107080c8600340320f80000c02d0500b1004440d00300010f6101e603a11074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859732230 1250 859730980 859731083
    0x627030816080601020a1e061e0f02031611031303030807020f0111040b131e050420070f0804091802210d1809050106051b0105060d030c 60
    0x101050190b15115415060a000007940d40c0c1610202400300d1100044940041c014104100f91050340448240001c1080807103401c050301c0c88401900702c03181028141310041640b0f100b20785c46002c20740d005031103400c00480e04807001e400e101d01c51402480200014441c1040d0307083c41e0070041d80300c0c1c2e460b4411450504402410302510541c1f42640e82e040c0b0300c0000f59840c10b101942c00fa80c000c003982980b10150310b6000c0c03106070000e5001300c1c45a484108610301004031242c0031000d680041d1070a11901412001c021201009602c0c00b04110100f0300500c00011003051071003d1840c05401da0074100350702c0d954030908880389941340c1c01c0b00001e054280c50850412075200d00c030202032904a45150101c0d0800a500d901a48030310300f08025940b2465209508041d1482d400b4204c034105c100103a603102d4501400952211042981400505072003c3c1094014005c0c1c6105440150020b900c60b103560781d0039074a500303280d40c04855000112007016901394241400160080e0410745890106a007154243d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859733480 1250 859732230 859732261
    0x1918030b160309080d09051c1101060b07022b051b10030209030619060e0c090301061a0406032307020a0b090c0315070516080901020d031806270308 65
    0x20040c10f040110304000301d804032081d640304103850540483d12452501d0b020f07007494580e1001d009000d0010403040030584e803000c0b03594a01e08016000304111516805840981c0c082d41304025486240d002c00380d02e0741003500004400c51902885180c2c950800c0c2e81d6200d050015010030340d14100c1c00c019409032186031207a07110043d515981000c5181000100100e62074010081c2440d4101c9480d6044840107410390b80102d0040c0f96454011005042c54140b00c9465400051514865800c004010540d4401026054a040c1c032140c11030b40b0341032038040150058086115810602c075001c08060016840f07150784544592029406050342140e10b2808130741c41d05024100e52801e074071003468a425070b1000648180f9003510754100c2c0545540b9810200d03154460f076029140302000c1422640104558100130f0401c10b0026029940b0a501046089048030078000c540d070615000e580703040000c601d03203920603480041c03c008070295000130541c2044401e62050000c600040380c071003c1103849070240070078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859734730 1250 859733480 859733521
    0x3010e071d070306030b040b04080c0a0c050a0906060f0f020a0f050d030f020309070e062407030f0806010e0f13060b1317031209070e010b03091b01051918030b 70
    0x10060b035805c6844910b1184c1c0001c20082c00e0602d55030104007845008406c1d100d06201150499001500b946402c20803010b0302d2040500400c080b500100e11500c40d4010f00c0196501541c3d80502039120301801c548a4840031014001d5006004a10b80450000b0009403c2503004074010915014003100041c00c851203440502c04a500c14014403100c01c0303000c201c070f104031101d50a8064254032a00c0016003600300b039051960384601c17038000b08003100512901518160b4041c0c1c89a189111802c8010354500d00c08542c080d0014903d1003007001c251070040f4030b0314918030020b0600058040c12800301c070100c030b141b42c210001c6450f012810b00f103c8480d48944c07001508513070b5401d9100031074845c501541c1740211028000e5008401000071003a100822002e0000d0240380603501440d40e4960001526510964000300a4011035507010107032030601c01c1c50254070780306a480b50715102d83d68031184c0c40a01031000b0141044543c109013a000c0201c40c50300700155015050b80a5513080c0f036980320610600c02c0c060b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859735980 1250 859734730 859734737
    0x9060605030123010e1509040504060504210903080a1707020601170114040605130c18230610050c010e1c0c0b0c0306041409010b10050c031803010e071d07 68
    0x1501c01644e40d0040920001e12820303102203542d02200310b0149a00d0184040050300203282108020a10401d5000386000b03500546a184440c072018110440c51300201d040d038000704403032440c10000103146000500b144201032410003500d000000200340307076a00170b0300d180c00141e10440c01480700c0f030341c0030002c2240648031310001c0089408101e04414134200080c406032449999400080301000c6441e40b2148456101020130142510b40d03820507401c0740a505a4940189000d4144101000c00031401c0803000b55441c0303548183c0c1e60346041201040c600400e10741000800d1004580c4074609000c1c99000380e0b400000380100c03418600c5421a000001000b840400c4882e11281012400ca01030382600150140030143c3e4907620000443c024045001518070400c5143d4104494600198402d1140301d0702103a03078030b1841802e19011120f44c0680b0707000801d950020400e0300550140e102050314801c00c0500085040c1042120160404d00c4683c800c0525404400c1c280a82c2003810741503d602003980c2c01d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859737230 1250 859735980 859736039
    0x30d090311012c0312030f1005061204120306080d08042a030f03090e040807150e031c0b0d05030c0d02072612160b01080102030402011710090606050301 67
    0x44040103205040c0daa0100c40500d03e060403426840900c0720750225045030750480da803814000024643e00e10111101540d080c1c0f40e02c00031a10386071400448442e030b450f85484091310744981e1120b00d414000028204c0504d55182000501b40d007040c090550019603c0d2035154051602e41407188041c0708c14003040a504401003503559114956004150680e41c002c46c5200c401c86551806076200c00d584d801100c42c2061000c108001c11030902c000f0000780f03205030b0316003802e210800715100590300100c0300401e10381c005000390b02c450745d8007288180844100c00b0703003c0340801c1c5000118a0116000c0c078261810703040003800a00223003040080e02219003282c07004110b100c0c600800866140d003807402c10010380d0030032102b017800898100600300e0540b12080110b0383e14a40c2c0e6000c12078600c001d1400300c4801d40c0e24000003a4190044c030036a8403894044e119540340c1d410b907101c80350444000034100364408030000300c0803500d00841e02c05e03030015203202d0300c80c036a80394145001a000c460385220850042e02c03400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859738480 1250 859737230 859737257
    0xf0b0402090315090102040305120304031106151905040609090c0e040b04080307021e072d0b1605010c120b0d0309090f0f021c18080306100e030d09031101 68
    0x80b105880d80350020040425144c6a440c14060300c520303880a40b080c840c1c000034442400480f401140a41e200b0707104c507080d0b0f50703020401d0f68884204494450070000d80040c880c0381401c0142d114048203115107880890181c4800005084468907084180002c4e0384021309000c002035042c480000c2c20101d040381d0020301d46036403180c901244c0103200800090b40480803030101e07802045101c41041c0020312520440e8868020282e40f807080d0321400c0c0044c64503840c9100e0a2801480300c100003a41d103600204628104844201241e01c0003da942d400320208844001288003842182140655030340d50003040d407440d8104074151403401da1181d11038459501c1141c0041e1304041e10340c0846511460210f10f842c10312036800010b01e040b400c80302005000040440148004440440003641440340800c0f90017564031710400399102505004081e003004102103000340c42c2500d00000c980500e071809803a501c840c3c4002c0780c02c1c4140010f41601080d0012000c1c8100310f140480d4180300312083c0791482900c2c0c542e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859739730 1250 859738480 859738483
    0xa0323160302040b0109081e390f03060a020306040b0a0e07080601030b0307090905060115051b071206020315030303070c0303090f0f12020c0d0c031e0b01090f0b04020903 75
    0x300d1100a100e01d55030700f00989664024800303403005080410039500090f04a941c1d86400420040b0301d01e0481c065810149140c5840780c8c0b209071010308800054250040071041c0c03d10400c100c0745d203554403041401d46450159410452a44112000500580c40f402c00d42d041c08151507003807481c6845542a48010300002103e414a02d80c441154a00420943c55100041c2e000301014500c007500b5000b600d0002c150f11800341c0040030104e1140c1c088a9061380d0b5070003c6e4a0700a2008203141c00030350100700120120148040348000c28199505407540d450361078040700e1408402c184100c03000341d004404c000301f440c806c8480d038000c40d07002c1c0c014500c2c5140032200102881310480c0010141991500d0362000d00c0140200030400c0c83d8840f407001c19001003400c2041c01c284803890000c1c0144074200e60352090341004001c80c1c0d04241e0003038000d4031040c216078482c0c1150014801850a510041d000e074000720b05402c11250003803804607400a1040704003c584008d446900c0390b050300490041240c000c0b1900c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859740980 1250 859739730 859739773
    0x70b090112051902160302060a090506040b07030e160e0601031505040e030717030912130303030b010203191206170d0c0201050f210105040e0607120b0a0323 69
    0x41c40500260315034520340110090b180c0800e4001e8034600c00300c4c0707034021220740080f400c602c00c1c0070340c086411650ba0404038200b46c0d243d403240149a6041140890700003040694176640186140c2070210320a54510640e61030300c000305031080c90000c1c4220b020044c110030b001c030a50b0443c4080c038041c014001c046215134a00c04943c0300e8240600d0341d600c9248004c9030705206481c0401d6200c21056041c24500303010b1012600180c40c1c1341458007501038880144803c1710200c075901c0c2e841414a07103443c2c1c0365072400e500501c03000d90240e0660001b000180b4004a003200304408000e21511a0300300307080c1903103800f0300301ca90755003020034080040e0354003105202002074850300d803c800b454101e0000d0720b0392004032400d019084190700c00701000309209000710302201200d072110f40e0407101120244c0e031b190200410b40e403005106160702d0304980e01291100380f0460441a42c19200390300450311600386800300e240c80340994002e0311000412020207840a850381d82007440150703800b00034480000c600302c0a003803801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859742230 1250 859740980 859741007
    0x80d0f0e1f0207200f0d200d230d0f0504031515030b0118050411091b040f08060c0f04060c02130e030304030212042912011502070b0901 60
    0x280541120020344080c2d0111256154030164560082c040300103400032000070892064420081002015107500f09000403542640d0000e00c04680698080310f8018204450f00c00160014001c11042001c511900c10402c0c2030001d0003d4000090110300429050910200c070300c0041000312441d0900f465885401c2c0d41c10b076900844860400c0c1c0c10b2020715001001e0382c8449000d800c1c80a5000810705c1320f0b40034550304032008019241002d8540c104c21208440048400820302d83d01800745965500b088400b80c0e80c010480a9000652002085040d2898000e030384801902031501310b040c00016020b00004e07800c684101c034002e0401d1929082844240998081c420401c42034001d50000e40d80c80c05901c01915140e528200078494480605a440e0340c0201d03401c1d0094070500700040c3c00c210760745080740c003110380c40140341da03030500c010034400101c8203409a820080c0006014000f540700000c1c024500a0103051000444401c800001078200000d41d0700002c0885011704c18142680d17000031481e40102c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859743480 1250 859742230 859742263
    0x62808010f2d05120a05010506010309151503021518060f120c130f051008010f0b070f0b07030e1c0906210e0607030e01270507030f080d0f0e 62
    0x300b4200200003086481e80f29541c0032042d0070205462010205165400d64020402403065650f031000541c103562000400400081002c035044505002e26030084100c034010000311000350380d403a000141a0054a203115064440000c0c1d0703214820140960b503042c409045d905175081c10104003800e43d2a0184442d98039000c0903040024013100c040400700c0b0152801b0301d00401a464442d02c11405d0b00805004480c02585012048241c0c80d00403104181200d030750000c0ca0b912281804842d103615004079004540104541d200e0800051001c0e00441c461040d0740c2e40005d100768043c3c2680c0c0343c01c0c40d0780300c0b400c0c0d803110300003080d210681d00206040c00d076003490900d8005c40500038810030180d4a5030f640001c4641c605140311002c04c0c80418201d020b5556540c007444040c9030140210700b01c41403544c40300a5a81c0000c9240a002d403d000301e228a82e0044d000c0d2110b06650751200000c014000e40102e42c007000c002031a03c0c0c03000243c800c42c001c070741e80e84008100344180301665594600180c0201e1001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859744730 1250 859743480 859743539
    0xb0a0506121e040309090609090507090c0201090206071b06050304050a033515040b1f0903150f0f0b0d030c0c0b0f0414090c03070806062808010f 64
    0x203890010b4001c9403075002c102c80c2c031014030706030900402c00309060044000c0706040c41c3d00040d24291034044e8901d07103031308074000d09005884c11036228000c1042100e0740701595200c035004005607440b40081c2103400d00803100c4407202028078041400034222a00590140081031040c0008540d00103030105081d0b41c1f5003045003540617a10a0b403107000e40e04100101d010540c011280300035041c034100060080e2800c1050300e4205004000700000d540224001c01d0304174000c503a40740341200c40e80140c100910a1030030100c0c0490b03101d0301c0d00308860171945200e0710702684a11000d40c3c0c4003000d01c21a510314103c0320081003d1031140c030024a80551441010742041940040c0c1360500040007285c43c000c0c001800d465a80303683c4480c0036103440d081841500c0f042c5c582d000c000002801c280c050107102c0d043c00010139140d95290001500c0c102c10181040c0e4000383c040c0910086030900c03112444600c402100a0800704090910061004205030080b203851908050100080c0702c4003507034581c1891504413200324 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859745980 1250 859744730 859744741
    0x30120070201020c04110d051815060604030c0b0c070b040b0a260a0e0f160509040f020d0312180b010b090102011401141806010813030e03150a0b0a050612 68
    0xd444d01c4030410070351152401e0b5440c09000b81c98001410003410f2034205000c2c580c0c40000314070900c42c0c459920b0500d40c010484600d03081d00c04034440741e8001001002c0c141055141e071150169440c240d000000018400140481e2003002000790b00700601c00c0482c140c1c070b4241401880c1c2d00a000b0403192805214603030110150b02c40070000030088580c8002c0c00d51485280004040c0f010700b10080c00e0400e02d00824040d00640007001c2215020018a4008402c49030b01d804248041c04c000144103860300d40d40d2201c0200169680b4024100040c003980d030b03001c011035401c2703000c00403100f408013070345050820945442e0008000b030302014111903981040c940c4452450b00182d0241504040b0510030003c0400042404583e1100400c20b03254103450182e4402214050303030b48441400c0d220701d40402c8030080062410010510700e43c030b40364800d19020041c1102c6202003071a080055450301303c01c2461004014400c0c8480c8107005600e00d040f03400034122407400b070200b003192141d460100d043d08a524000751 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859747230 1250 859745980 859745983
    0x50a09020d080a030e010b0d03260106030b090903130303030f020702042306010521070311030a320126030703030c0912021c0302010b191403012007020102 68
    0x45098001d0200040000c25141c041c949500c00d040c03501c00700346051405681030005106400c00058041d11140300c0680b07903101501c2c400365614030718106103400d0940103d60740d5000c0000e40206210f46002c5556401e1500f00034080c0c100a0607091980c0c01440b41c9003034802c0300700d030303013000c1b241c060400007180400040000f01900c600c03603010b5006030400e80304c1c1e00c040d281b01182900050042c82e00400a440710b00c011034440c821959044007060700f00ba54400300c0320800d00e90503000b6005080018491085a5600c6a80e820459071019490b50b100d540c059600b1015110380440780c1860900303410030241490900d000e40c818082d00c00003801da032110542845056401c1c8811180780c47c101c944903401c9160040150070340b12501d2001422520b0005240d007541c6004424a1f82c0c0280b0000d002d060011802c0c5c828944840c0550441d9298003828030903031541c4162140b81c1400301c1030607103c24207181d84400209511500c00d40268036103404100110741800d0200728500c1c1d80800180c1d290000c0c00101d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859748480 1250 859747230 859747241
    0x81603110708031902040509280527030c030a080408040803040824160c03121803200a080f040b030106210504020102061f1707081009080d050a 63
    0x58803140030018405040c8442140070314820510440800b070355001428000c002d9000d580b051580040d030107404591042c90724040004105000c0410b0410320304210703110425900e043e10161030074915440d08643d28407281403031850000e01d0303800035071404151640307803680d0388603213030300344013081191004901000034450485005144070b001703c03911107455001d0180c407500041021a40b5101d141001e40c0c06201c04c4030207901c41d0302002c2c150300e000030b07a0000a0b030344005041422010050048491000c0c110140f0803100e4603030000b02002d814200c0c81c60b000d007018004150b002d07501003100034903800001e40010681e4209511400f159107a250f100400035241c0119000b189102c007000c800450b180c0c0d8400518808445005510780e601d41c0c07030740c0d030384012039400351800380c0141c110600103059085800044040c2c010247c4e010420a40d40e8000c07455411b810030200710b11a00b01450070094200d0400440001881415041150b0219551446d8603440740c0308520f0400364446001901801750350703000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859749730 1250 859748480 859748501
    0x110105071e0c0c03110a06110c010e010e1003061805060d110a030b0106031b050a0e0603060a090207120e03061009330503012405040504020423071e081603 68
    0x20b14480c11380380d1a001e2410890380b409a40500c00c18000040c420b80315602ea44004408003010f40360204002004484006040ea055811301680030341486582c2c451344681c03040f000b41d56400041082c20408409074581e400d0342c2120000c0e0401c010300141e40d40c2d00b07078038854481e4880303240c90700c5003110710100b08102c0d06640060711a120300c5000040e07454150300078a20034540c40102130510003480105071198012901020001040c21f0072506403818024010b40c2c0000300203154241c072964582c001c0d4142d911064003100d895507a0b10003800e1b066000b060107400c004013100070740f403946440075100380e032504c45200d6003101d29291ba69040c441410b000380010088001d01a07807040e00b03401742a0b00c468068900c105806980790184501c250515501d25810071520050b280d54034514150420000c1e00000e001642d0050703031126006886000150030003862070345241c0050701d5280046010307065100701c1341e1108440302d01c00b003c65005a032104a40d61700c4140400400f1784522440811402028852030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859750980 1250 859749730 859749743
    0x3081e161b0606030302190b0703050a0f020c071406040b1806190c2604030201050f1201060c0512030c07020613180212060f0f01050a050f0301090606110105071e0c 72
    0x90780c024021550825010b80740a9000c80d0107800ca13510504103042c00c2c1c8000540380001d03107008034600a110350072040e08080145c0c5d002c00d0b109002c0011004030381c0004031010851340030040130080303550f11003841d04c1024805c449039401c2c2440d003000b428461180f00020300107681c401841818550700c0909942d0300c641c0040d0308a0341c0c40221000071300310f070180f5442980e400540b00340d00084100c01e00c07400e544080d110254242003500d10741c0103440c1d40d009030702d82100e0344509004405046407001c4405000f0281d07035070740c5160f80d4568100903040490030521030401c0c01c0200104a0511001021500100d074103440d030760381d03c14403041049541280f58100c0240c1c0c0180c900c6404030b1b41c8090b0064180040310341c900c6c0c601034440104001c029561410110b4020758085078a0f01d217907015002174060340440b818024a0104189030389022548241c100c1c004081e5075038814031485034030075003624607074180b4802080641413003d006090b00151820784014131505c0c241d540e0006d849988442c2c4039590080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859752230 1250 859750980 859751027
    0xf1918020307110601030507140d05030d020901091505030c1b12130e04120c03090803031017190209070c02030a05070512032d1b010903081e16 63
    0x2050040a940281c41910015948200c0f00d03661001c0850300074101c940c040001c0c03030524603101d05201c01104880b0390f141d10a520740f084102003201030009101280c0414030044e60341400e070002500859980c1c214440501a465a0012207500141144c5d01301440e000c202d900eaa4404c8000c00d405003ca42a28200f40a4108100c140070034280180c01c0c03050802180c00140c5480d90b107220541c0000710790240c2500c0280c007514141e5401403d91610250080c5001e180041d1600170f242d02d5907006962440f0f10821a0000f040b4521503100940c200c140c2510241034092010a6842c01c00c061640300640f085400c1740124205a0180d0b48015040b603000d0305130350b8010000d04007075071602110302c0342178040c04500b800340e01800d0700802100d400c944c110849600c0200600f42d52044014018000c030452a400c00c50b9041c0c002c1d05803c129804100c40c400410165051b00d00100102c80c0a030508949401d01a51a01020000c10f00c6e0359003d08001c2c0207a1280c401d24004031a6500c201010390110765451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859753480 1250 859752230 859752269
    0xb04030c0e06420a050403080d021603020f0706050c06071d0409150e030c06150307030f08030907140a030b0604060f03120801080a0c030605100b0a03020c01060f050f19 74
    0x1d0660b6600c1d010b41454100d000541007403d042c15102c0d480404001440400060001505180180c070403045000001400c003d213101d4849000300450700290301682c410142070302048400c000482c0a40440c0c80c20604045890000c00d0359000040c00c40401e000d510403503014020000d40e2040c0d00f0000c0280180f100b0480b42c202050440101d0f5411021581840002041d03d1400411921210703003950003490195584102401d040b0720032440241d15000303401c80000410b071181180030705e850080010759034a00f0046102e038a4582d443d0720100103190172003144000f9940c1e40c10440d04607500580c408645036521000100100019000044980c0c010103020042c40709460301d0559001e01d0392580d07070b07560b602c0e070f5a0a80c0d2425100401058207040c41c6003880020780315045260845c0c000c190407880310b900c0380344009441e0004101c400001ea40410352503540103090195400401765849055009402c040204002801090302e183c0250801c0c61010036500c2c800850f0401000d00501d10302a14102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859754730 1250 859753480 859753549
    0x12030310170a020a03140a02130b130e0705190f0605120901060521030c060a0c0f0e0303071202030f0f0307030c08100e06030c280b04030c0e06 63
    0x40c0070308803031005140c201d1440550005414010207800400c0c03005028619900e0f00c40401010412410a00035240c10000503299400d007504510702441c404604140d0300018010084a100d04007141c0c40d0404240c0c0464071004100c8001342d58003500c0d0804840703006d0381c080b00d03c0c0b035050340140c0030040100740000e041030b17020028004464030342840c1c0d1940e40310290760302d00f82c0c4c42c20b0280f10303400f15081c0c560100d40c61000d1540114020300300c041c0c908018195010a052407004c9420409081d04c0720130f58404c503a8803005a11000300c1505220540381002d2001c69074034012014018500c400e44101111450300030401d450270740a685030b01907074134201c0446813002c9400948512010a042100a40d1042e0107004868030500b44460580c020398903141c64400003030005000a17030103000300b903a0040740d9101d00700181c4241e03007105800c054141040c2c801c0e03528042c2d10351106c80c80c01000e100c02d200080c1c54010100c221501d825810002e07031191000242018038046030b2600040c85001c5206241c0071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859755980 1250 859754730 859754761
    0x4032009010f1503091406390f03040f0506070c03030f09030512060f0a0e090f0a051e030d0e0d02010b030304060c031202040f30110f120303 62
    0x202034800c2034181c0d0b42d48480003540001400307030f403d80c010740e09542e80703500d4070940c0400c01850045904003483c2c46c407480d5441c1007800c1076404034802d03a484a69070000040e00c260320544881286c400003000120080b144060340190b03144955070f003034000041404c0c013840240a02d00d480d0420261205030a100d20050118458000102c0209083c200900e00c1103400f489800542c0350592a600c1c83e0032060b4103203030203200004005551001004c2c98000d596107420481c03501906801c04941c185040c5000751034604144100120180d512110070b281c005074000c40c1003031200c0c00c2d0340701139130007000600d54035800c5000390b912200c00c0328030300000510a050005062076481c15990005c020400c0e1348418503880344100e0180700701054208100d2000240b10b51070018182140b803200604140d2900049080c100d480c1e07201000c40004051110a240110ba040d010201e520741c80d48600e40c0c8042c0c0d581c542e000c080d41643d6110f44041a003100035511942d150f0f40c1c1e00e11100042c0c944d0f91401098410792181e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859757230 1250 859755980 859756043
    0x9060503370507080112061d0105070908010f02030106090b0c101104060320040b0c100c0203090114041a0306030c0a030308010807060306080615031501030f02010e1c030f050403 78
    0x2e0800300492640c50152100c42d044c2c511208801c41d9800300360720740744003902e103145003900d0049810224400496082c812940074000695a50020134901000242562054007001065a20410040002580207800c9170708444000005585407400c2c5c0021504101d40d464510150383c0c00d0601480886404500410907144c190300e080003030001070101d540c40c54641ca0f84100e8814000c1100744007501809001e0a1a0722031001251000c0c080340842000f5100380a40110140c4d0010542d035840e50307000089580ca4a462102c131904161511200c41c0c1800c03050340c0640f40920000021640c140c0781480440440e02c40a80b804460a0362480d000f40703c100c0902c00d50096001c4c0703e00c0818018480d00400084034014070040c54107407961522503107540000c3c100315505101c0e0b24194200c05e0300d511001030085000f60820000c0341058000036201c5407880141e54070404051403982041c60050b482c51802d640c0502d016203222010003020f88291140d50400b91003070700e0075203844080100b00e6140c02d2180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859758480 1250 859757230 859757341
    0x2a060a0506090c090d021212040801060f0501110a3f0905030a050c1c0c0f090c050c031206151303050c0409020102120a0c152003010609060503 63
    0x1e6407600031660041c0140a511913201e0308802145c0090303d801c80001448441507810f541c0c005d400300d2040700d031a510540c0300b00302c1070751201c100b08480c06402e080b090003040c081c281340845550001a254a61100410003048003540400c080d00c501482d6071040c000300b049003c080018a480030040904042c0034160000041000401042c1c508002c02d05901340c41d407000c01410000e00d00e1041000d400d4645140c1d44801c1762490010011840750803c0200825107607040c104414240260001030300c509201c01014848100460b60798240000212a00754103610211441d0351101800117610750380d0085101c050b0f880204c2da190450140001c04e000f02c03407007001120b6036916884284802d4603404480a800350b00107100743d000c98040340006105010341440c0c080402c0b420380d924502c441900c1c840403c01d40c3e98078003021b8030940d02c4915555100100c030100343d04540c0b51602c01802540140944001c200002c40458001d41450408140499540c07050905400042035450b41d00386c01201e442000c1d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859759730 1250 859758480 859758499
    0x4060e011127010e012f0109030c05010c05040f090203060f1e011b05120d0e070e19050f060d020411030103030206040312020304030905150702040617150c2a060a0506 73
    0x407980034110304242c002c010b0312200e200c21366124403d030f6140c003c04240003142c84007081c0d601c0f0746e02003031140c0070076288030f526442c0b0603079414248103085032048034801c0c050000c100001d0191145a0700300000b1504a81c8001d0703a42d45c0c449012a03802000721101c01d400941c000d031440030200081c840c205003018280e030740540d180885400c40b00d00d030081000207407940e000702c0c0e0074408115205005040390341410300041507140c0550301300b0346000740a50204041912400c00d0160b054a0b1008255003208440001d0115007400c001c40316020f14050309203440b03810710524040464540350042010500184180364413503030741c0e04010707440305411542140041c001c1d10000c51202114400c1d0380c01190141c0c1c80d408a14104428091120308203058000c0074a000c1c0000d80041c0d07207500804000d080d03215002c0b0081c0040312501e5242608180d40c0f02c1101102500b00304210f140325094540085004201143c1a10101c2444410509280316048140129002c1190915103504590b0003050107462442c07a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859760980 1250 859759730 859759807
    0x703030809010e1902012f01050402102c011106100614120c070606080307060b030d02070e0c07020a0f0608040512070506150307090c0c0212070303020604060e0111 72
    0x443d144d242243c3c22803e0b840c1903a840c00b42d445070003440200e50318072441020303c60891040c80c6100604282000b4640c5d143c4040104508200c10241a40c449506000c0e01d90241d07a050446161803401c0740030001e22044002d405a070303104842c1b4600f40781140c0192601418402400c240c28105405901c0c0410049492700094003442e40403190030050503038440450761910f00c10030545520900d019618642c80714070205801c4014030051540d64421030000441c001081c0525041c515001020815504149030801c41d4200e130003078855000c00f00044040e030711f8003a8030006440d0350f25604a00000a100000401e94940183d0014051b034003c80844800614495654810384074412004049400600c003040541440d01c40262086c0c60081c1aa8000e035141c8403003004075184043c1010005043c0c03484142541403014041040803804800f0780400c0d415918069503581c0c000e8001010715645202d02c01100c1820b50040b202c0c8012201e11503920810310030014100440b001c1c0110000415400072107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859762230 1250 859760980 859760983
    0xf04090b120604060203130212100501090506030c0f041401060807020709060617060f040f0603150615050307090e04030c050d032705070b130e0106080601020c10110703030809010e 79
    0x400c1071440100074007160307455582d41c038040e410291105c2aa848955034240050351000f904e032441c2c1007110010140d148010b81000700b80e4106078403c008051403d000d2051684020640000440301501c4c01001100c02801103001407002410605250743d8150012038220b500048080c00f60000d0350072074141d65101c844000454015200f40004a01c101104044005900314002d5000a00a00b18240e101440b408a800c0d80c0750101c1400006030350704018410045803040e51008420011001c004040c1090b840d1038a122082c8100001c0c45400b0001820b524072070440400680a0704100c03951a0400e0314018001388054582112075000703201c48003406c0c501ca40700340109103146000761075244446040842c10300c132101000751094001e241c40401c2d64426280201403103000d050382d01046038902a00482e0a00c0103800c100c0070030000e501400041d070b0780000d008807440e4080ba200c00c98000d0103541941c1242c03104415001e580590b940000c00e01d0f81000d0f5040c81112118024010301c8945000f06 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859763480 1250 859762230 859762249
    0x2031609080c090a1d1b0307080a080301060305060d05010f1e090209010311030109080c2508060402060d0e010e0a11010215130305092e05090105121b0f04090b 70
    0x6500001040d001890460140e0051a00b50303840b0144000c040070171454942c03c060300d4011601144481a2000720b89040402c407020040040340064000e0440d81e903600005840306214803020143c584001c90450340d1801d08103ca11a8010003c010010703008a040010300310f8800100b9900c00807d07403038094000d20340a0307c03128a0f80144850541d07801d595038400d01016a05280d6055940d03400c0c4c2c00d00003600c54004146132040c1c580200350311150140e0004200c030750100c2c3e0b504070055000c020042d0340700020b842504154110b54058842c0c8007100b021004040101032001a5030070400e254865020102c0e802d03401c2401490f000c0c2c5440d520a00690751034041c2c2206c8510a43c800000a24101031100216010f505c246030080c50804507400185021427140050074a98800400450b000c0c0550081414418914100581070044840c006012030084907080f00d841d058800010b10307a20040201740082d0580c9005c000e8403480714205030300c101c0c2c006000d12030030130b4030f8400050722500e4111702d807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859764730 1250 859763480 859763503
    0x23010906030902090601080711030a080103020f010309150b13020706050703110313060b130606080a051b0d0c0c02040609020702150301080c010c0507081203070201140402010f210203160908 83
    0x20b10150f4640302e00454524000400c20323810005840c0a411819905200a1003a00c960759517150095045004009006e101103803018141450410804002400c0300080c41c0c54041c1c0c04c0d000904504050b012825840d0703d440e0140c40c1500c0045d1b40700800845078052402644151350030011154040907100c0d940c031044d14040d5031100d1850300c400004580f90803000c5844405044103a41140102d03842d000e503a9182c02c25004a01a0333410440b044220b80f1665900003d05070480c0312511841c100380455100790011900344c00e4940218150140c0503140e4170b0611980079004001c01551041c51000035040750310101c0c4114262039141e10b05180200075030381600c4440c006810810000700044d15068039107101207950f070265000c00294841d00384a00c401507030311403d54559902e801d16000f0300715005003500c1c0320b04c81080c10900000d42da1008082015039000d05206201c0c0d0f00110040d0400c0e001441c1c00007035a0b00000c1084461072403004090030000b6251508400c840d160a030340c607100e8045d0280e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859765980 1250 859764730 859764739
    0x3040507050d172b0e12070c0308040e06030d0503160c050a0c090623060a180b0415030c0201140f0c040503060a020a41040302040e250501090311030723010906030902 73
    0x140d0b801440b070751b980100045072040d00d030074104507a60382e201801d5401c95800301d610300d0319080c1005094241400b803201c548883c1c0c0f90852451a00f400c280035154940035401c010400050f80001c2040360411030501074035000b04c200c004455840d0030040250a141c00b035501c10020601415a41d000c04d00c890600010300117182074200001c0120484001110140040c0c061100b01b00018580c04000c00074805000b24902c01c0c3d40094011070040c0c15918090516000c5a2410300f81e0802004484985034010620249101c02c540310903000000324000c0744c0010740e140c050f04080c030405082a500602c82020103446242012030a00d48000020424011070303802080d6031505084020401400280c000c1507611945041584980108040f22252080c0400647c00301c0507044480800020005030081d808110184040c10400000e0980826120041c10703006146000800c0d581c2c188082006004031030214800201c01085001c44100c440301441e02040c9419000306442c0d03c24050001034a8000e072 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859767230 1250 859765980 859765993
    0x90c0613090213030f0305030601081501230c011505090a051b0c0a08030a0207060f0c0e040e010e030c030322030504050d030212040b07061103040507050d172b0e 71
    0x700c5900c0654000c00c038a50009a0400c404000100075a011413031040c06030382d40319145e2400c1c40014209482c082d0510b40040c0c5100305602d6503a90094600503458080d074046801d203418420000b50728083c07500301c05140d50819016407039114412002c481151800c4503210029100e1007800002c440090301c240c01c60400c01011209020321000040c00281c0381101101d0141401d0384a084683d08251404001da50700003440700241302e030900500c0000d0300c2d22a070030012a211b03c7c9014101c6039003404058000c03a212108a280707100c0a41c01aa81c0c04001e00c141c0c0c0e07407183c100640d2922548119002540300403002e014400184481c4489501141d050b20f581d03160500785010000903015503c411411813243c03000224000324420060302c024010510007548a10700d03860603409640c8484003040411805004201c0031510000301c41c021140c1c01da40744000f1014604108600c8210f01d80c030b200c0c0e084800200001504050080365203458400b24440c0010741e0f0201444003601c035020791180d1540e1286 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859768480 1250 859767230 859767239
    0x2d0114010e270705191d030c0a17190f020316030c0e0c161203180b011406210601030605030a0f170403020316060801060503130b0711010e0105090c0613 67
    0x22100d45800c044907041517030414040c00c0c40c015070003094141c0480001c59000c5c1030711802442e100c04c0030750f41004401900700780e003450003c0341040c500c5220740c0590b402011074090501d9000d0080000c4812074030341c01c2228040500b002145401c8000d0700300e0080c46090800b80e14443d6a41240c3c064aa20a0000030040d00d401e000d0540c05902070503100001100f0070414801030210741001000fa807140703100321314410035410301400322000020010303466144420030800186640322000d05460b007001030002906d807000c1c0405d41c0c80c0511140d9001d10b488051070a103407003600100083c4a040d099906009150711601456224000060020540300800c502032002034035140942c40e0f0541c00c0030350107040a1356a00081c1c036100d0707842e0201094aa2101041c009544d00440d42c5014140509180d451030030004130341c4180e84040c14020344440700c11800701c0c0102d40b142101e0100071441c440203000000300300d103e01d8002e0600780d0b0221a41e118059150189040c018159946407510507400354415180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859769730 1250 859768480 859768549
    0x20a0503030c061b160f05070906060527030d0e040b0402040302060d051506040306021308060907060c0602090406080318090907061b0503072103060b032d0114010e 72
    0x440e8240413000080c0011040364007000442e811903405045440b00c000b0550503c2414070b0000e0300441d000d64103080c02072050a8000e0206d07440c005d05c4010f0089500382074804c0c0154086800d00881e414004c8442d02000954445101003e441013114104002c0c5480c1080004a100364031000750030000a00c00340301040216403140d58407038441e400c501c0042030400006251540950022988a40e02248040c018450f41e07882d98040c118240040c40142800c0000c0c66a03180c4a00c6204104480054800100141d80e01070f500d0424010b0821300c11503886004007a1203400101c09942a000c000200d600c0758584204c02e140074034000b0010340340440c1400003c40d04c070724042411000c03002c103051201c000901e081000b404002e00a04003240101600303292030f0103540311810342804040c24410248540c070700c188112600090900c4402a49094240d85042a281d81c00d018542d032941a00000030f1103040c4030311068440800b42c1c0c030050400913403400c01007a11300c0b1854542c28043e04030010304502c4030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859770980 1250 859769730 859769761
    0x801120813090f02070b0a05060928020406031a030106060e2b05060612120a031802030f0601140108040b0c09060c160f090516050d0f020c0109020a0503030c06 70
    0x55445203010140c94074540070070340390f80545401e103050f030002c2e265080c080d58025041e0042d00042040c846030403c05d000440540001d41303003003007400000b900d04030100d000481e001094117210b51b0964445a823080081e00509581480380710100d04190b041b0400d1a040c46502c0640b012500c0d100c4400d5000c105118802841d400488864100c900e40d480141f015640b0600f95140305100078101860428240071201010101c5a01c203640701d521591015000101500c040c0c0c00e0f60701e00096440300d0345140d0650070581050180d014090140314040c11007021a01030f050740c602c5000e10034070f007840380011038085004640280141020300007046110440c280241800600200200d081518081000b400c10b400c01410861152310510104190105a01c1400040200c917108000d40e02d40225012000b0041d84100c80805c8000140c1c2740d8156500d030711080e03020004040c2113446d40d10440c1c1c490700802084c00160700c5a503c3c031400140b245000011152000c001602a00c06a01c078000d1400c4900c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859772230 1250 859770980 859770997
    0x13110301090b0109060302040b060c0a0605060f0904122a080c15010e070206070f0518150417070803070f121b050303040209061e09250f090608011208 66
    0x1501e80724128040303008102514082d09440303400280d0300d8614070400c811100440507060007030078244581c0c0408031002c00c107034510a41040c1c003c43d2940d25400080d8102d4407100c0b42d039601030b44410a000501120407540e03410160592961404500508030b100500103902604082200034058801c0005403094050b01400031110100c07004840b61404142c0c4110742600044440e200b00c6081200310365041040541040031420150f07403888071100010400d114200c04c0d80840604000c5515054940b001100c0301c800700d4203561911240c507118689550304013040c1c010390038441e104000c22001c0c0003104403804c081c2c0c4100d540890f41865134544d02c0c0c001603a41003406200320210303034000000d9141d10700341c0c825105d200038507601d282c284100640050302604003800341084400800f85447c5280f1000380c28442110b000a00f0740d5208110003028286410782d6000540c0684119489c64111205e118030001075201c1c014090303128482203441c1c902c03d04c030710301c1c5880300058200301003001c4400400303500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859773480 1250 859772230 859772233
    0x3050a06083c06011508061c020f0111030d0f0e071d07091a0324030c04020c010920130c09061b050d0207060905040504110f01090306090305030709060206131103 71
    0x1840340c0010b190a2103000d0740029102041c0802801d11140d114103002da128408070380134202d00540c0c820100c1090507002d8024002d00a071507a801031740c1e010301818001c0403045400c403983c030001c0078a0007000d815003900c01c600c040d0800c40c00326030010780406c07014242c841d82040c42e1500070340d40c0b03c90804000080c10131014400000c00c04240080c00c51440111070b50f1620320a41d0328202200030144540545a07060038081c2da00711180074590b004100f601d14407904541c00750300c0e08102041d540c0108916040100503685d5040d2084c01644082c01c1840011012110420707500b154000c041d00744d034401104c69001840b200400c0c4a003e00440c030071031f0213081009040c49105040e903545e600c0c0c03c05000340c0030b0142c0d000c0c500401801d0343c06808600a02416101408641001c0e42c40b4462100c0d180b1540d84a00c080d5084180f140e446188803500854000d01c0600607109242030141c1030780d20540f105000945000d401084460002030301031b0003885126281d840440300760b25801c4a041d040740d8100d40c903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859774730 1250 859773480 859773583
    0xf0f12030c1e03020706091e05010819050a050403080c0c061f05060c010501050a1a042c0114091005240409020d051e0903180d060501030303050a0608 66
    0xc0d542c42a07200030a291003a00100b6900e030034104080c206150030307400b000d000c94868146101e141d80c61150a000c440c020b003400c903600e458440c807415042040d01115410549003c0c1001003049654000074061406501c4010140e00c540035407024500c98000f0407061503003c1000300d80c050341910b4065080c7c0030004408011240c4510018196a00c43d104842c0719a46a2005100c41d16240f0b030000d00a003180701507044103400400021026004030b10074880300d03210303030240b09007841c018800c031941603030b04001c204056684448086105141a08001c2c0c010b4034200d00040101c106204c1410179500300400007099a481d80c840004400750b0307075505c0c04280b81c05000011b2503004a0000d0664070890200104003072515100390f107010717040340a82d04d1614401c00c003403040c44000802110303401008003014400307020b8402c1c0416101c010150000742024a40000013050651680c480c501540b41c0304000d00ca141d5981c000c0342d075501d840f5803607600100e41107206040b80102400ca58110000401443d0a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859775980 1250 859774730 859774763
    0x804170415030b0f0609220209030a080c06070e060711180709030b0a02030c03070c080403320d09091d0a05030a0216060e04090f0f03090f0f12030c 65
    0x1100c8901c04101203511451641918a0000d0040d40303581c5054411505000c035480015029050b41d07400000d03d8144103194800d07844050301200c0361004040e0490300c04e09150718210f02e642c1d00c099124010740c001d41b00400c0c072142c45000c141c0d04000c0024886800c1c6059a254203c40d2403512800c15800f6401d48041000d900ca0100031a20501c5503480f01001245503060002c20446e0007000307002c10503c10420030180c07c2c041e0080d250071012910300300d9004031951400b1121841290000740c4450740c1c0c10b40003210100e8006c13a0210904c104900c0f0440881c0ca10b03013141c1e43e00103e003001c2020a003403150a0100b00b14580c0081d003202d802c10465003884103003180d000d081a1040d042540c0701e4100007208603034aa01001400312429800010640e51850b0140041202920039640d902c5642c8420300754013030180c403140d41c40c080b640040390b50312208840d113009008600280f240c0f42550041e141e00049911b02d0300000011181011444102004565411940002d0550301150001c40b1002e0b01003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859777230 1250 859775980 859775999
    0xc020102120901062306180a03080408010c121802060a090b160201140703080601120e1c030e0106030f0803060a320d1e060605130f0507030203040308041704 69
    0x24060340290b000060801e051010a5205610a00749040000150b00400e5110f07229101218511000b912080c1c202e40303c1e04001a4036400584e202402c14900031402140c004410750000c00c6003040f54440c1641705130000790203019900c000b40a4220110003241d50310250800400909400d1401d1810914a980710801300d0807a810650a040401c00c00e9a020801c5581020969822a4022800d241451943d80d0010601d4800911607410009441118108800180c03c141d01400c041c0b000d442800b01e031b0a60450f004810224514000b034103103c45140320000601c2000f0540780c220782d0806c2c21100700c4d1101d090070362001e00703900c0c0c00c8130710303200f0010b8002000074178620300c441c0e44a0505101401d03110700100240509080910425a080f008000581c42c403114110f03c0c84e03003000e8100c0e10b40301424144010211030388629040341071149504016400356002e60081400101304005c15100c940d401c4040f40000c0f580100401c549078040707404128900021a211084951a1454940c4600c1e402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859778480 1250 859777230 859777267
    0xf06040f06030b04060506040207261c200c0d0e0f0405070503040b25081005100f0801080111030601050d06032f120c010f0c020319050d03060b040303030c020102 71
    0x60f00c6841d070000034401088494011190801e03401c980540c00e0007110f07214131001c0c3d1010f014074150a1141d00a00d107181c0341c00410b841408a5900a0400c142104da48080c0074200e0190100340d04640141405081003803c000c0c0c1e40c15001d504020000030001e00c2007560110012000141d1094108803213244da0740c1c40d8001c01d881030605603101500c1c0d04051914090440015140343e0450011034203102404580020819050750300d840c15100070740301c4070464140c110590b003007140c019101c480d243c04407a800420b00c0004104a40d0703540304581e6910394207030890740124501401100d04002003829980710320080d20800c005554001a00c130b599a80d02c020303a000c850b08607440401d6510320b0a0310150000d0b0010ba08000c15034454904050007002c070f540b2400e020040c1030520240008035186180326000040e180340d070180450b5020070302c140795203210541d16001100d09116801000060034424003601085030340891503a030906055607001d038060301180d1981802c565080c42020041403003a26030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859779730 1250 859778480 859778483
    0x503090907030608060a0b010c2d08040512010605090708040309080318011d280e090a11031606051e03130201180302060f0706061701020c060f06090f06040f0603 71
    0x410300d140c940d00c50b0170f000004080241191500b120b082c0d190740c05c520300f000300f1540681050410700c469042c410307903a1030300c0c60351030505122651030307000b00440c2c00700400c260f40e01200c03134200d41c500210b915400d07106c3d140100c2c1d030400e001c00003081c880b50040c0c0c440390304a44203042c5900000d89a1080c06d1550304542c1d1100c40c04440701142517581d5070845c0c22001c0e0b0300e120700b14080044940801051000700804800503010110392444030013072038000c0b00f0038060210290217080300d00701080789650310041e511017540d251540781031480e80c500c1c0014124030b11003c0140038a076141c1c540710040d80c558105c5002c1e0103120242c404030350400c880e02001180305400c3c080c07070b0b8404100079000042c04c18000b1414104c00ca5130280c001d202681d2560103444e1183c021f04a01076546a85281c40e001410041d849401c0254001d030704c150400e40190060006c5143d840c040310100c1d5110071408400c0281903415a0b048902c040100f00110f01e52440c00b5440f40c800340010640d00d02043d585c000b202c425500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859780980 1250 859779730 859779737
    0x307020307080c07050a0e2202120102070c1a04030309060c0f0f0515150f041503081b0c010201020702090a0207030c0b18060c0931090c03031704050309010c0503090907 74
    0x1c06025920380902c001c8007907c101500c103c040c1c903041c0c4c10310354102c0d03038660f0b030300b00300200b0702d404508540e01c0d1205101031a007800000d40d200c1a0354a80f907003201540d40105003282d0381140c400f24428141c00240c60440703805542e170030b031050300c3c1c640c0c152910309144009a5092406461100c00704002c03031a2030006500c24001020b4681900200d0781201e10b014105000c41080c83d1034000c0c1c0c40d030b504400f0710840801228000b40403444816690410b00719584018440713074011941403031403000c4604003000d03000c100042c1c0e490550782c000120f01303d100d075000080d48041080c0124003c44560741c05080401d01c24188241d080c0e487d40c80d04910941d049480c035000e04d00e04181d05c40c405409201094000a280c240b00e4100b052000000e01c00304120b000c02210700c0845583c00018210508071407898800340c20040003a00d2050820000341d0201d40410b401203070402c80c8551801402c09482d030300c141d4205020314180307000078004490280103140f041c4c42c1032001303011184060341d444007090f0003203032581c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859782230 1250 859780980 859780993
    0x4030302090d150b09040b012619021201050103030f0305061c05030c0c04060e070c081902100c08191e14010503010b0a030c1401050f0d0606081302030a06020307020307080c 76
    0xc45000513903400c4600c0394010709503d800d210000701c0d800c12182c107480d80551904074240000005d115102d5035411704510034030070340c0c840c0b8402291421000010500903503587c1002e18003200503e0981d002844000d001034810254240300f28840e0741324a4000000409090340c8460b0751542d403010009200058074150000550300b41024800c0043c040e80c0c100070b40d001d10106241550103020380f68010401d10a01c05141401d100700f00106041b21030f2904070341c00300c008030440c81074020b60300c1115075986204546000860b2004902411100380301d10f6840840300041d0f0004200080500020200701002559601a03844110b40c07a000d0b100c601100703042a242c039589083d080500b0b480c45034040d01d01039452000c0900105d005140f0788002c4e0781d10390304040020084400100e5051096400400c5416000708003200100d100341c00990072603000d03a0740e480d101d481e151803046c010a005040254181e00c8510000c0c0002e560f41c02540d8441d480c1e00690741071a0464658176569805000200801d40181c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859783480 1250 859782230 859782263
    0x10510080d050313320709060b03070e03101103100605031e090c1003140a0510030f111216090207081204110a140f031903050304030302090d 62
    0x20198001040c0c940000c00d4054800e03a00030741184400b43c500e220802c10b0301c0e00041031207504c03400050407800c0210304440420310001071202410b200200300d000c40c0640d6000055140361401080e00303482d25140541d103192901c1409030f81020301c0020fa5a0180034404040040b08e0306803190a03104c80c1c0f614071055881c503200038482c2d0700b0f0800da005141031007010f00a00c03a2440030f00e5418440604a03c03031003010364a4402031107103030041c0c0806c102d0303001169660440ba25070381900410742484504141c2d15464540824400c00d9a078102c416041c00440748804002040c800b0507070b020b006009610500120311040082050400c01d00d408100941c03000d1607016000d1140c01c3e03c0c2d0002c21a41e5403c60a04003203540b2240d07203229030791958800801160100b4240310001c1582c0350007010041c00100b0195072a00c0000b140703081a69940e1140301c01c40781c0005242030208000010700306820811414200580e410344454101601c00c0e4105942400031100316181c0c0405101d80c103001c4e003c05500c40801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859784730 1250 859783480 859783501
    0x406170703020310050412051b01020406121b0e150c010c0f1b0f0b19140604060509131e050106080601030c09020c071710090b090c06030f0f040f140105 67
    0x4d103001241c006241c14104000f01d84011442d100c0d4902a1601e66620010b40104074445a201000340006520000300024a20340125051045100062091200400b2244c00c080e406406070b000c100032540c40340c0001c10b20303e0050040300c8403048075040b040c200007000c4010307400c5640900d06c00c0d01081c1f1601c1c0500c110360b000012120302c4e40c084044460b2003059170355200304c02032100740002d01c1c1c8610030002c220440c039502240505500034400412041c40d03403180307560000d601600c07018000d625008000c40c5a00384110410712031145641d903800602807030b941d4a801c0c3c2c0c0304940e000d0f80d00250b07002d403400003030002c2c0525401004400c0080c80c0d10b50450030424561442c81d401585c000c1d104100102180c4004510321003200c05000300b081010b040741e079a1508141031010b03410007080c60002810204901b0b0241c56001c0d400078411115900010014000e841c4000e9402c0b50300750306001d000500d2140340215860340a072103407041a00b20701c40c656442d075054000c0440750582e65126001c02007a4070b00c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859785980 1250 859784730 859784743
    0x609060e0a051012020d0201050f030708040b10061b0f08071a0a0203060d0209070e040609091703040804090902010216082505010906080a02040b0a1d100801060e04061707030203 78
    0x1c01540c8042d03a50320b040d4032001040c628000090040900b1b80c000010740e0300640c02e5a0255a03081c68059481c0303001080200030313420448040b00d55100560215403080f085588080c2600e00fa0b881b02c0d8454001c00b01101850050a24215130707115045800d03100040014000d0306000e80725680030401d001c81118542d506150007010224254410b0040100540e0340d0155030b43c0e816010b66100780a51580c1104944251614400580003418000002000c2d150742d0302c1345403580e016130302d04c8000078075680d660603240c03000b038502515048003480b0038450740d80290300c814003813481401105c45014014104140155855003c3ca055070468400403070050910710038181ea14000e034901c800c0700350070040041c0035400540116030030820900c0c0043d080c00c40030f50441d0054a0300c05140c0b42c842280c80401400c01c41241e40b1820b161001e9420750380c6070b00344084080300ba14004d46031548070b40c0c2070550445400d801d0f840c01660158454000050109000c038000540d495a040604001411130050514001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859787230 1250 859785980 859785991
    0x1a0106021f05041a150a0b0f19030902041803080601080123060403170a02070b04050604090c020a0c080c1011060c130b04090f11090d0b0a0609060e0a05 67
    0x10080203940140160809a001c1803074409840001c490b255803c207924058122140710081c00c600070240840d845943e5001c51030184c00725800800c8070b40ba0020301051780650220781000e010240111560758400410059054150b40b0b8002048945a0002002e8410740a1010400e50740c0442602c14140c4c000981c42d80004207080c1403045501d004550411062080202044000c034420740c080240e540e40101d600460700302d846a44048083d20855403642c0c407101a58007d4402c080c00054060074613002d9500301e0b40700070025810586441c8003800a009030f045150304500454a05d040011502c048190150814500419100580348240240041c540480303034103100250b10300c5414120b0028166130f00c120150855502d40300780030082c0070213041039000340b910400040380129860480f603224021203820210700717001c1c511140000b00750074810841c46a41081d1342d0300045e40400c1c1d40b00c03d0550400c503182000541075580d4071a0000b200c280703801180b0340200c1003050007902c0446000d40e54000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859788480 1250 859787230 859787233
    0x1e080f03100819022404030605010e0609011a0901050f22050612150d0807030221040308070327030302010506041113031203020403080301091515020304121403071a010602 75
    0x1400c0c0c00c68031400b080400000a1140f01841c0c0748101118600c1c5c95203559005101c100c603210303a12442c11401a100c24018400242c1c0340800182d00c0c0d00d80303011424104d599904005078000d45600b99510180c1c0116000d50520508100799001d19258800400200307401c6000c81a00d51407080788114104010340c0014450700c8240401507803c014440e281e40c02c0a0f40500e46a8045205d06c00f0440744072042d24040d02c1c03000041044420b0640100700c1c28803080752002c08401d00501c55080b600180030f5800058044101848401c001900403290402d60085000b0144007282d068000c21200005a42045006035110390601c00b490070680264681c60549142c018280320b91040c100c1c081c50904d00c00505100ca205038607070b0456020f0341c1118061900401c1982d660b68561100030090308180b12718a0043d40d04107000914030521225100c5e45541ca9405980340902e082d90201d0103443da0907003602d0000740c0301c940100740d910401c000c0050a1046018088110300961000d02c01d0780140d2000d03065 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859789730 1250 859788480 859788493
    0x30105160e0d050f12040e010803040609060f1e11060f0f0f0c0f0409060e13030e120c06040906030c0f0e06040911030a0c052106041e080f031008 64
    0x101c0d04040300d1500c4900641e4807810701c030781d64108103280c010300d403041a099014030106643c0f5034100c1c1000300240d442c400808680799a0700c41000343c1d00e116501c10840003410030301051001d00c0c801e0f01040c408081c185481c2d070204546145148681003c0c89200011882c404c0408410410a100066205210144494030340c90150015000c00c80c0c002e202c000f40040c8000040d41c07800403036082e0f4002c3c1140001c1251501d4540319003800030070550040e9610107001500084c03101c0c910b100940d620341e5040d5603449180d8400420b1050b0a00c8107480c6009074092a080310038a9160400a0001001100d03c04078801e49503041000d2003003490340101000c25068030051107004540080c241d0451400d80740040c02000e02c1c00c041d83c8081d465000d19515020b200e404205010400700000182e840845200d900502001203548400883c01096070650300300d8800140860504c011018840c0002c003d0030309002c0165880710040d038051440000d00390004000c1c07120059071109080054030340360004011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859790980 1250 859789730 859789771
    0x307030e06163605010e0d030f11192d031b02040902040f1406010905090117070e090d0e06071e051606031d01050c0f0315060a020a02030105 62
    0x1c6010225180b1000c0c4038850500d11403c3d441c40f0691900600c48140d14025900a9040340060410f00c0c07203100d0002d02c150410700c0b810b240c80386248030a01e130316032076040064400da201541c0501c1209007110352801014a9030010307224441a2805040c2f03da84000b200410015052030380a103064550300505a800c1928000a9001501e02e1108442401d001d204d40a03988005000740a186500039041401d0000e0b0a10070182e0f504500080242418020039560340c0d200110f03151011840b85036800444d80300104640031602500900542030002900c10880d115550600c4517002580c9225495004005940e0340075404100d0b0110000100d505a2600565454065200c0040503a05002d040080342e00010041c080014005003050f540f5660415507588001500402c000d000c2410103800710059510b0000041c801c540c8945540b480c584d0801800102c140d1320382d00010309030200004010b121074010f0b558400509040002079005022240041c4145820341c0c101410043c0c0b42c00c1c003c00d1184 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859792230 1250 859790980 859791001
    0xd11010c230f0d020a030f050604150311120105010f030b0105220b120f0a02040506040507021f140115030f05011410020109020612090f0c18070c0b0703020307030e06 73
    0x10501da00009240b03031140c2802c45054124030405020320092880050001d008980540045502c0703580000c041203280e41e03803414002a102d14689803414407240318014000143e030345111034081c8902508040322881c5404e0907500b11078080e08190a2903410700c00800400211201c11070142000ba00c841044860141c04040c1989581002c0440c064440b1150707016034a502141c0b05114440d001211128060894403640f11890f03001700782d01a5042100140d82803e01b40211402109a5401454500c081c04111500d4042a005c0b10706c0c050744032505d031268038054400e614060a60854030080303001181401030f04452855518105035403d10004014144c01d000e00c24070300b0398065926503980d140c0e50034128010249400002e50090000c1100700054041010540c4600100c1c4120340c60f01d2035440c05155202c100c1c083d40b6030b0042120307403a00d1400c8620307121560008000d081c500032842d05540c031003540050481d00400040d60100401000380c0e4540602d075203040d840c902400d0075007441c00c0b03c00e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859793480 1250 859792230 859792277
    0x203120c03120c07050a0606061407050d140c0109080a0f08060d03110708101a090f13020d1401050708101a0f040b04080a061b0c02120c030d11010c 65
    0x42c81c00303008140002d11021845003103d80c0c00d503106007a82c210215500e86400100141c0c0a89000030780540042c400301c40700c0d9411141c12540100042000004415086400c0e64444e42484104001402a100418001d0207030980080c820f5000c075031525540d09000b41424501001c0100304500c410a224150326505c8138800c9080e05407826010342e03003801403c83d20740801039104c00ca252180c80381e0b6840348032040e07000308110100302428400c2810587d04103d0321001c140c600c403074021168030206990400000324000c0311403019000b8241c503415138131550021241e0400142c4965190000c0121659000c1c00040c0e01614405900c40524204544c8020b03401e900300e01d00010b03041c0000c529101100e103000344c40040c2001424503603503945501c0c200e500c0d410702820450300c845c14200c0c0300600402e224a8440b000b00d0f160740c0c00341180302c65001c02c4885c03000300c03c9131455409540b00c1d142694806014440a030603582c1c84824842c1031013411142100c1d6820304241c00c010100f1010202d4030301d9500301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859794730 1250 859793480 859793497
    0x506090a0b041104030f020a0602070f2d0608060405090f030d0207110a1d01081209280605070b010806010b122e03260405010c061107050a0203120c03 66
    0x6981c50340202060060860b8100380c00f4280000c40c0000c10072950900a050311442902c112041d070783c0c0e8440c140c1e69420b40d070241a0040c2611b250502480311030200705a40c41b801c4040b07011207110344e295802c45140090b0030890000b221038041044c00d0500c0d000e681e42040c0d243c8001c200e1402e08405a070f0701c0c4d0160a1551402d42e400084080900192005082024000174070584541c0d58442040a0542031000340b03204052000000240c820b00100d400c0c820710001d83c49092800c46460108174860f0020f05028001200405445590900300c400c20005410241c1b01e095459006090144520105a1000c549684982d0041c000200c118003034800c6440c03150405003040d10f402ca10740311001c80c400000c04c00500b030701100c41d003603840202050088030b0054408080405149403842002044280e0010049100f0403041296500c100004c504140c040d190003e00340d000f21400101d0780e072190f482030b42c03658010f900c400e040d85400e00011081d603040c4040945010b81c1f1021042e00d90281441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859795980 1250 859794730 859794751
    0x61409010507020f0d0315050a060203040617010e0c07080d0f0c09211716050c0901211205040e010305030c19030909021b06071e05040605041401030e240604050609 72
    0x840070040101f03050000940002040c4180450700c804009640c1e41092160f080002d040756440b07c0c801d844c80380070701d040c2c400f0007000709901c1d034800411041d10b030300c242e0f07003190985006c1103504030240d514851500006401000412403040305500100741d00d40b281c2204941840141c40311244c0d03080358188205090b4060040b100c1020800d003e081503002d0b0600e003107035809004402c0c804103e000b080d40081003808407405c030315590300c40d416000c41001e4260f50184540071079408801040c08032100300360441c0b403440d02515064440d921514000303800c5c0c0c003c4502d944042080b00125005015560b841c68101d61140000c54642d1001010210f04e442400c903902e03800034409010b021a0010345540c400e40004640c4c40e8180070b50000c12010f0040c03a044106038903203240b003101501c0b580c103ea08171042c0f9602e2508080c100b0b152001c1590349a40c80034145a41c54070380300d01441040c0a80c204142110344c00001101403054080c80240300181000c0c49285000100807965540d5900306800c05940103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859797230 1250 859795980 859795991
    0x609010e10150308030403030c1701050108070309061d0708010608160603020a1209110a050603060d020103020d1503050a03090503070f03080a0329040f020711010f0c061409010507020f0d03 83
    0x1c00341e0b42029036040500103800c0041080103164041d0086000c0706100e80c0c95013102640340d10400007842003030052034005205400492074551103074014151160080c4800151039020142c40c401e082003440102907182c002d12803c103c01c010030700c184001021000302420484006850f0710b48406440d011300018194003241c041c0c040e0b44a2a4109842d4990003420440c0c00e0540c02c1020941203a00c1034180318208988000c00d140c1080c00a0f6802204064420802c800d03e5500540c00b0350460603848881540d20f031040c05800000e050340c00e000b94081da000c1c192690950500034803594054002600a03405401c2c100482e4600c0401441140d030420041c50703d0b2094954201c020f40355000720f100c242040300312602800070091560742c401b40c000b103c0c10005000c01443d44410703801348480181c84184004aa04c059502440c00e49000c540306241c030803001d4481e507880e10200c50400c42000e2080281c401003210481c024860507800c1040b43c00108401d40d50300000590740e1040051020800d0b8540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859798480 1250 859797230 859797251
    0x60a060c05010f050123030a020306060402160525061805060f0c1b010f140304060207080706020309012c1c020709021c0b0d080414150307080402030609010e10 70
    0xb940000300300d401c0b2070000c4c41196580c5091108220341008006902040c03040c1e04c46040c600000e00440d5190f0160280c241e50791840308010081d0043d580c40301c0e00d42202c0d8401000100240400d008601d00480810260b8480d8500031302505c84c0c64000c4400d10241000304501e10122035a03450442c4c404440140d0b40e0883c0803040c80c1c0c94041c1d0300380d444840c400d03400826120103056458042c026030030380c0c410b982503205041c110340d180708288090750a40c1082020a01085068006211107401107001034a44402552440d00b01d0340110303903030012a5940c15441035020300c00305020462441e200e0107261040d000c8052103448801c0b100601460002c0304490780001070084c80180020200d50400f151581071007140c4242861503c014031402602c0d207810003c8a00d0030b201c2e0300740314540104405050a05000401034814079a0700841d40c005008488000c00540f81c000070b6102c2c2141c0d03925605103040c244141840c01d08080c1c05c1070403a9042c85410510610b0018a141614403070360008100107004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859799730 1250 859798480 859798483
    0x120103171603080601140a2703020a14091e06040f0b060f1b0321130f12080114062709071d01090b0a0c060b0402130815060a060c05 58
    0x50660340346035075000e0305503182415080341d5000c1c81400c3c01e0301c1c0e0168088680341852003a01c01c07003107141c0c080340400b9550802c1d812816a40798543c80060303000031020381c40f030b00000c0c40305009500200c046094000034040d1411300c15410b60704401e101c0c0071000c802101851034102844000e014034011603454282e510700b10031030741040640513000381101c9d41e00d00d24010140316a0f40240c442d46140c40b0000b24a4042900c004103ea8406440840b0008000071042040030081c4002c1d201c200f44049a00b01c100118400400c5d842c8803d00c0b540784451801940b96014007050416401140390b051818194030700350310740a0882325582c040d20744d2042c110511020300b84610444e40d2245406c80c0008042000007500324810f220140700c0a45042d00c202c105000448440c0d180d030060a00c081c20901414030194016110035035111701c00c00021540108050104040782c006d1041002e18101006040200c0701080c403d030304445c0c2c100c0302c0c15411850000c1c003103900d0741024855181044032a80b58a01403210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859800980 1250 859799730 859799737
    0x6090204110a180e0c042304020a050a0305060109060816020111121b0c07090509100c030b1302071a07050c0601060f0e06070512090d050703230312010317 68
    0x4404010748032046414010540060b2010660040b19820b40100b10b6505801c031072480740b10510a1780340b074039082544640d40d054a49002011000701452868010360703507400a840400216500c164890840c082c000303090300c0c0b015000c103042c8003103800244032141c3c0c400390040e4030070103d10180ba4000c0103c64103d005100d44048030441c103101003540e282d020101c46110340640c3c00c07544244a0140264040d0070326100b918524900c1d0b62109100f0048254031741c000e254008406030541d410a00031034031100940d46046445800070344c0d603d41201d50742c03900001000720200c0f05902182400711503034603690920140208600141080f10005079003a215004940daa1240d100644090b941d46034001340090a0400c1c42c4400b0549980f5601c0c102d0408209030391020b90000e008118444100203842d1540d0700852007550801c40305a018008120208468001944500390304601e500078141c90041c98002100304003103d420801c5600c6090b201c482059040d25001031911980d07040d00b40030a80b2a10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859802230 1250 859800980 859801001
    0x2f0a081b030706050a0c0801150e0a080d1806020d020a0605040215041203031103041a090c27070c0f1203021219140105281a0304050c061606090204 65
    0x2100185000802109802103809807070704440038081c4101e90b2034107980c07c850900070311900e031085224400b0203e21500900715901c00140410101e035441e200e145e8240388100050b040419403000ca42c0e80905040407200c4c004000d02d1024111303000405d0300082d11807404410142c0969240e00124041d580c5410a40001c04051140745664690b02d01804a00041d200401c0d00841d1821a0342620103c2020407207119682c4092516164103440329580c02e91407014111600522400756215a99127030b150207100c120500c09a9080508819005007110001c001c200e40104082e024801c1e00142000c11050380c480d80c4001112415000070100300c0003070051101941807184e040d0180020b15103440d007081040c000d00d40b402d01944425800b104100c0c1c100b03106080c1c100d11141071415211004007850a5161804036100c5032640d611301d60f50740c0b0000d89950700301c54208004148020030400f04626400f8030310681303016003450440d110314055420403c1024001940341c07281b560031561176500151011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859803480 1250 859802230 859802233
    0x1011101e09030207030302010e07050d0b2e0f15020304061407060f091506180f090b0106030b0a170c0f040f15050f0f030601050d0516062f0a081b 64
    0xc03541e0b03060007036031501c1911064002d0751a00d1140250b024021821809a030300c058a0303d9404a1a49e4500c40301e8a001811580e40000812840106410b8195004180c0180c162461104c41c10840c40e511544441c2e0302c28160b01e6011960210400d4020007278404488542c200381185026407620310805100e8101c2c0205030714641600345940075400c0c1d0204500900030002250380072109209402200e000c0e0240c00b56405104200104076029604061450b426482c0040390707071000741c0c1c2c40308030500084c0c1000020035181c0d001d01034141421041030b4003e060003140000ca61440120701030f103c0c4001e040d010f02070b920320281550141c0383c0c1d801c00051081ca80f9810003415146207500c007500c2c507030703400343c0c900c62a0b581d032041d20707103140c00c1407009030002d2b0003006810164038110811262010034001110280508001d05140705041a4110010140c54580b0102c82480070003a0300e0598406002d003c0c080b0a42c544880d2503c1e000960b40c002c281d01000303075643c0d419605400c101c03040e1030100c0000103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859804730 1250 859803480 859803491
    0x61b0a170916062c060d09050a0b330604230a0602010209130c27090513031704054801020307060b0406090f02091011101e 54
    0xa4000000340c0701010201c80c0d5950065607103552085030201c203006103610382d0192101c2c43e82228801521301c080340300c1008204a02e40600c4034084819168040341c01d03501500100180000e020610810b1a881200c1c240d00200348902da0311314640101c200803441c200408031314654006c60711403d0071a00a0b0000d805c00441c1c44100d40000200620030b032050501503d0041d030b000807940c1c014002e882c001d02e00242040346551080616100818130441d000c0708200e03c5014040c00032150001d0309145a00162450942c0c900707090340b0909407039024054540719a4464800780c0440c2c3d00c4440800340300c0a81243d15280d440702c1c1022894403402c2c07090790100084c1158010440201400c11885403c07000314020710704030020000c0042c5441c854121409030300200502400241240e000031050000104006008c5031a00b032220304880c0c18002411046600041501003484d02003072680002d038440ca4203051500c8031513a02a152041b0300070700500c15840300c0c0c00307061001a201c810025824640c07004c010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859805980 1250 859804730 859804741
    0xc090a020d0c1103070605270d08010f030b0f092a15070309051c0f06050411150409020a02030c0d021e03030f04021003021c051008061b0a17 62
    0x354401241000402c0c0b8061102c507049003d42000c5001541d1035000d54140084e40e241c44000d804000c140200d0500d00d124455600c0350603035005d5004881d100014816200508000b60500c00180c21030380b81e00355000b000f0000513842e0114141d10042140c447c19280d11841101440c002084010300c0b14062040748901010030b010300c0c1d0100c5690704031031140c451400302d25800024455620b015000030381c003600510040c14450250340e07082c900c003041481c1d00702490b00c0700c034240d01400c041110b126450f4000e000921000e08038021a10004862310390300a222241c2101440c8901c0c0b041d8502c050300403402ca182d01e402401030b60f0720311000500350f400984040b000292140d10a44000d100101e100325100b080350320001c03c1d64840c480307601d60b061458803a41c013005008030400569808040d020001c40312001040c0e0100501d00c900307070f10003103500d0800c00d0700711822070100e030404082a40210100000c8420034030801d070020a0440300c44e9515440074800300c070803100d400c0c4e01103200103807031085c0603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859807230 1250 859805980 859806001
    0x607060b0a031506050f031b01231c02090a0504050a0e0a0c061b0b13021f09140102010c0504032a23040b031507020f07061e02070f0909050c09 63
    0x1044540f40110810000d40c41d40100141c081d82691242d030036900a42c0070716850f1070440800d43c030259050402c0da81c2a801485c1d090035941413166010980100483c200583c1d04520200c40c035803144c0d0100c15403c100e89107001c10b052040300d124a40c404c5446401180f00640a0341c400618a0404000d8410441a50400c83e0603070a42c0c0c0325180024031030718030303007001000c948800f940301c0b41d070245e03104c601e54944d04900d600640401c94241d0344903803000c80204c81c0d0460b08480c0c045206598540e0200c15107000c1c602404400300f8042d19041d64146a01c00300342035032050446040c0c92703004550401020500c098102c80c1020000030303d0031140078410100e02c10046070200165210200c042440d00350300102404259801030380815050b51000081900d44510046130710303030010040c41111030a06070060894500980d85d48084041043c03440391505030000100350200d041400d000800c5528504403070310700751000612500400076903400306101017080520800301c0c045401401d00d94103040039400d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859808480 1250 859807230 859807253
    0x1208040e0f0402090c18040c20032d0d140f0a060506070b130605190f0b01020613060b2e031103070c06110403060203070207060504140607060b0a03 65
    0x3000020000750000700318095184035581c013030316650715500c0e1070240d0002908807100c45808060b5401d100c07081a22140300d604522111f0341c1d101d05a110400e0032034044c1c480f0b01c10808519030810003905401d135400e400107914484601a1800300c03181108460440d50190080f0110140e080c040000d2a243e1101d0b410b038018820400e038202240c03220006501151750901c100c03904254184410381c0402c1c220511144e00c40110410003090198544c5ca000c11543c045480480b0b842000c6002c0e010345019205000102d00c2a01c400c010503448680040d5555000400c4a88500c800204000c10040150001c5041e400f014000750251040002d041d00084801c00122601d07020520f9107103034462003802018047c00ca417500079450f5803a001d2003254800030552041d80c0d910b448000803103603030210800602c0154020b03007005031203041038480203080c64640e0b80041308101040c0000e00010182020815000304100d038180d5440009150000291011a0030b00e41c0c4460741410000c14014200c4c4003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859809730 1250 859808480 859808489
    0x1080102040e130f0f03050d0c05031f03020d0809120d030c1403100b18030f030d0b10080a020a030b0d060b040c051c1a03030703020309030c0a0806070e010504120804 73
    0x8000d42c030b0b56424001c07000380386200c02c064000400f803003281d40890000b820071a0f01c24000d10b40f0600c0c0036803064420050f10540f44403080041c1d8004200f10807843c0841403104840c183c0000c40e01b0716440d6400040350800c1481028000c4032000034580001d64400c072500644226400a4406e0f0100d03949000c1c0080518020f102e0100c0c03442500044c003c408031080301e03c1403403080d8000e07078060708010000c0080d40024040a800144004001819950402c442c2d800c4591a20003903a03912156800c102c1601d080001090141d8403c83d4840060307904004202e51142614600680706c640d01c18085003e07015615000342c1041c643c0c902c820602c00075401151030310005950500440600d030004450301c0c4512645500001c82480366010004a503402c03e81c0086401c01e03000094400303400009086900028045016034000100141d20381420b0040e003050390300c212070314140c0a251804c2561a120700422070003c00c4408905c0710002d82c080c0003680d000c5c055038007040324405282e20780341c2c6007a4001d019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859810980 1250 859809730 859809749
    0x9061c09051006260718090c08030a0804030e041d0a2609120f03040e01210305030a090c0f06051b010605030a0b0c0d0f0504060b01020c01020c0f0d0b0108010204 71
    0x1107000c00d84099000300f000b116400310300344010f5450101281c88118642c55010201d01900740001901030000c0760b01c01c008020640001520030380c9291003001a0310742d9029412a41042c008400700c5038001c0e81156116400d401d1041c40b900f507440c0020028290030394001c08070f40000411038032090000884129092140002d40050b504030f601c4200d40365003491150302c00c4803040210003c54103190000f901c941000c241250b0541072500307111402c1d03801c150005003019a490b00100510842e6406811141f8801d0300000903401c3d560310010658800184280c241a8440080b0310400c03621a41010003040040a41d900c030b50344413440102154080c403d45128142800e601062403d418821103048a0008000307084d116655a82c440713055100408a00000b201441080c40c846014000c20084140c845000902850140b03000e90444020031030490440d40030100340406a40c00042c902e42010044445002d61103480c0f0028080034440b00d00185804060000014980015000707002a07034072104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859812230 1250 859810980 859810993
    0xc0e1515120f010311011b05100504020a0605070201021b0f0315070201201b0709050c0d0606030b091f05031006050a0e0c030a02090f0d0b010e0a02130b09061c0905 72
    0x902d440b074540000e010192101c83c0d9a5415181503014003150703024810b11100210380301180b6110203041101c2c0c40030b902d5006480c3c0081004500d00345d01184050101420010f042400c00d0300000c6d540d012241c0f101c0302200380c0810701040b80e070750020070741a550001012a4880901045040e448400644a4401540c00d0000030700c0c5540700381c1d010101c04440884494181030f401300441d0301c5080303400021061030041840102d900280707402150310a40c0c3c000c20311641c9001699880e0301310740b070340d6010404040c070349440720484d43d580810217a0060081c01c1451001c80c120110b0000380f680c1544600da051182c0004c00c0c0b002e032129007000d400c541d000c0302c4000025503a503c00b200c0c1071108030f4031445610300030000602c1110496014084181d400b421009511fa4408017044c1d01120309001544c00c03401c20001013003c81c171101d0106a011041c20402c0d410f00b03c110403846070f090018003402031380c09008107050304140c45850540c1d050305600000c6089048203110154010035151000b55007501414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859813480 1250 859812230 859812241
    0xd0b09090a0c0b0702030c040b010504170705100801080309012001061205060c0309190f02060a02060a0c0f02030a05032d09152518151101090c0e151512 67
    0x83c4181c40d42250042c000e801c03064000401c2000078001051242d0521200b44008122581c02c103450300b401c3c511400003080200c0c101010440d400d0b00c3c0024103410080c00200500c000d51003c0141e500f401d0003800c0201d60320509070344070340800801456030b846642c80c1280c0083c81110010401d240e0a01039029540c3e43d883c0d4680034012403108442c0300d0490f038480710580c0707585071021401101035809101d694000000942c0000c01c1030380000b01e4038005074401010300216004074868114004460b04246001d08d251000c080d44070301414024805020022002400b41c00c0c007410560300e58500d140b954516261240b0326035030014000d540e54401031040c000b9070500c01c03501c1005103000d02100c40758000388081c8940100c18041c1810f0f40c0004004010101d151010385a01c8024054611150b0a0810907002c6030000e2070705400319035000c9281c0c1030500c0d520204088003410000e45410900ea258980c3c1c0d21000c0394521071740b10300c02c6504401c550265a5004019801400c03c0c42001070150350070381c658 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859814730 1250 859813480 859813499
    0x10e060a0b0127181b1d0915010c03120c02032101030209060411090909030a02010b031f0e030417030304060c0305091005060d0b0109140601020a0b06060d0b09090a0c 73
    0x544464000f1805a4091144216440000610300c1c50b120012a120002c001e00e603440340068140344010541d620501c0d0058041640a00c2e4151002c0d29200c41e01c1ca01003c0d190200c0c040031956905001c840325042080c50f02c581d005521000401405000c42c8441d2000250360b5400b005451000b4000c0c0c985c0000c0305410303000541d0480350014000807064941104000042030f082c142044640c07410030090402c0e4981d40700300d40c4a014414003868a65617615030213400c0d5440b40c03010740c4c425004001d46e10702964568645000b458804200029440b01035070b00750380b07544240c0c3c00c00158284003000e80142c140c8000025172281d841060248014011018240c0c04c0d580d054a0361941d070b030030070440f09040e1340742d0f0384c0702d981c1c4540010310b00717420442e164039400f280c09401c0c2c00519546807550700514620709108071080e0010700a00c014044860b06440c1c0407078010024000d14880c6c40d00041c00c0c0c2699595800044204100801110303460800348801592030700b03c0c0d542103a0b800864100010035103803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859815980 1250 859814730 859814777
    0xd050115230a1d0d140f03072121020301140d050307020d02042007140a12030905070b21011e05010818120d2417010e060a0b01 56
    0x1980c403a01c5080201081d07080e20f01e98424001d14840d02d16a000320500c594441c1024001c0e14040c550066040c210500502e090a41c808064110b0b41e004000b42000907141c41d8080c2d40c240c8082480541006c11f10f0300446030049081d131903490010055044c00303802c20305035004504807210000784c6074010b03c00d00e09000f16a00c2d442c8018005400074858100981885448054924401400015181c4c0c0c0098007421906400b4801414580042103190410604145601485054100601048280343d0398030494040104070303c8101070320b5000500402400300406c1c0050952a00019103550800c1960070f50315004102401c002641c0c603000150024000440c4071406400f402488e101c2c2c0e0a100041d14a482d000d001c821405006611101040d8020710654001e006250880c0d641d80f04000c03940426200002c1c50900388040e80900369040c0c4a0654802048030800c88081d440f800307805034898014507201003490b07614000d51040040e40225580200d1420800362141101000b45a440d403440e45c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859817230 1250 859815980 859816037
    0x20106030201090b21100801050c0f040b160602070b0601021506010207060e010c0503120402030723040906020c01091124161401090317060d050a0b0a020d050115 71
    0x198489403e0010030729410081c4000e035820b0206819107440c0d85e103145200d1808681c2c8a049582d1542c091040c080207005840c3c21090203405207080002041844006105500c5260444040003540304100d002642e40e066546400c500c08540b41e0000342426620100101e607080e0050046a451020074421414428000e8206a000f4070780a0706160302560788500d142000d174144588511013100051081004181c1d00c030100c0d007c0c2045091900c1410720308032446c1c201006030107a4021754507070f0301074000b14070311240c0381140c000c40d0b54607a0f42000c500a220b030600c1c1100f2542080381d07480c1400706d1100c1c009512402900c0c20030300c7da101c1009070221101445066005203504000c2040030803a402d402012145c0103400c1080c054070414802070031940703959000c402181b0400d1503102d0403645c0c01240b50340010195881405103150b9039500da2110b002000c014001032000c00410076505559060712000c450541007084503503102c10400c18070006074000e000003c0c10160b00b092000d003d103d00d2040301c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859818480 1250 859817230 859817237
    0xc06031404140a0506010f14031b040c0504181d03070203101a0604170c12060a05070e0a09020c01150e0106080a1b08090c0301021606021b011e0b01020106030201 71
    0x9494940e00d540340c1d00c1618102c0c0c40c0314802e80c000500031503c1071200070300815820640700340c5685044065503184200c43c8080c0d1081d0000300c2962194900341c242c0b40780c0c80c9404c0b54000f43c070180440054a1078095a0002d1400710104290005000300c02da00c000d2251401001c41115581504940e59030f83c843c40c440250141c01c00b0940c2503040300d09030401078101003c9884150040d24840115a00c4d40190b804806560303004c1140500e09407003401303110304403c819104070003c003012698059490802030a1051010b64450000325803038801e203050040144020031000006a5030151580650040301c1e040a5035443d01d082213201c0038210545808541d00c1160f403001c1c507841d245c0182c1d0b84c81c1c00140000601922600e141403601e080f00c1001080070b480b61118103860078a11348040c68002c034411041e000f1782c4100040d003c0001e810001080d40c80d4891405030b505c0e848071170030f5001c0d0340a0458241c05907007002148111000854000740c0b16194000040002c070240360012400d07607078035100280c0403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859819730 1250 859818480 859818521
    0x5060609040207171603030e0a03080c03180d02070504050a05090604030f02030f0409060611070303050d0903090305060903210105010f0804051c020309030d081005040924090c0603 79
    0x5080503005804400e00512480c00c0030b420107040140180c5c0080d45010810103910304181c00c06400d803060426103c41140201180412958082c1c816840075003075600440c0c0c00310008460860110791044224000e00546100c481c082c1000381d030303030342d224025980308909000004240d419640b040520a501503002413500d038603582c070701356103030003903c0300240440c04108088507416111030000c200a000a4500081e00740c03a090008003c28588054082d4a41000b0802c00100394000e064a0041c03400c1080021040d016140c203440645a41e4001005c5d80142000c000040350044080c0c1314413500c0307002c086654509244000da00306400d01030306002c03c10800c0900c48040c032400300c180e8800d106500b100c540c480c40e042c0c0c0145c220703138100140d0700581c0009803140c4581001c4c0207071000d100c42810315888600700a40d24408046080c051980101d40c2c6050210034802c0c507138001c07541d00c041040302c003010b217000e00d9280010340086034095401c844c107c000010101d100f031160540003a51030144191 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 859820980 1250 859819730 859819747
    0x8190807080a0504031403091203163203030f011a070b060402160b010311011107030b0a111201051f02100f02191e020a0305031303120207080913050606 67
    0x10075070440082e010810109000101c00940c802c80ca40780c554100000039600c8420f103104202e510f07052800802c1081e0414401c10005002482c055510542d002006070800c401c521081110f550b042070542c415071860b00c1c4000c5903090080025405103100454028a0360b03201c00e10000d1070b41c0b146910249000e41000540d000c03502040c0d8154000400410240c40d240d80c0b030307002e0000c0d802205000d1701c996011724010402c025141005030b0303c0324802c4c2002004024a850503503110041031101500c042c40c81070000d10b56003941d500c0382c07104c003816100b601d0712a610516080e402210901a03607016a86050740041e0303030b800341c200c2c0c4685081c00d540104540400300c1d00d060b01070411500d030302015903024440145800c01518212a0581c03540e5103089113203407010840f41004290101c0e040554000c450960040f1740e00c401142c0c0d00800101d06240d0303c01051804540060f070040e03410f80703594408900c40c03080000680c028200c104044034003038001026401100101ea0041d00c035142d000780104801c0c0e9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 859822230 1250 859820980 859820993
    0x12070b01030c06020c0d1506180e0c010305130609170c0703030e03011a01032406030b0a0f0f150e03060708010509070f0914040e100608060c0304080306011b020d080408190807 77
    0x40040d54401f070104010782c0d07800f0500198503e614144031003544400c541c00750140100545242e44038240f800340524105810620401d4190100141449407074010700d0007401242d000a8107003002500700f4555441c00d01042a484041c240030403070005a1269035051503180500400c0340f0ba02140c100c980301c582d51072006400400340c007442e06101c1142454052102c0d29015005e40050485440100f00308041604200c0c40e85140c1d040b0010500b514581441881002820002a01c0e102045000184202d800c140c0720800c3c007074011989441000c0400410b26030000d2040e04a41041e5040c2c0626250540c007515010450040703071002451205040210300185000200c00301c4028200141440355507081f9403c0c41d0b460014410740c3c13512086d04004a410410206900c1515100300c6400d40c02d01c0c0d5210031707041c0f00c050a82d50401011840010400c40d8101700ca03844690f0080031442020558030b400c2100c0e800a101c1e401180c0116020448141c05001190715125806070400340307031441503903e41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 859823480 1250 859822230 859822253
    0x9092107020a120f020a1403070906030f080a090e040807110609100513030501110a0207060f0e0d0804120b070912030c0f061b0201140c040b03040b0912070b01030c06020c0d 76
    0xe40b44c84140e0040c00d00035885010101000c2c16800b81e2228000c420101454508490390b840348003118035155007040071559591034001c20071360000c0415a60014101c0442c6d00c81c11980248849407904401e120030001d191004102c102e100d89240b000d10200641000480c2c040e0000350b44d0007410340040c904c21548100002c1c401240010041c64115840780c07112400c591120b40034241e10800060168519038040008100030405458101c008129401c00101000341c08038249005d0100700d42c05104000c64076041c0c40291500c4035031078020400361300742240440016140307680403030100c480c0414202d034841c10310506560161a88590481d4035502c03044c540003000429102560344200c51048060419010a08070300c25a00214600e42e4084400c5254030b4050f102c5041c210007040208810480f0340c050307a91150b04001c09114540d1400324030340c141413216414140400d00000c90b0810444803c103a241070f43c1c051681d44c0801d5854100a0f03968100c1700c2903299010752441c0c01000019140980c9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 859824730 1250 859823480 859823483
    0x82212030504021843110606060708040e0618130b0c090f09130f03020f0d0302180103230703091103010c0206131a01090501090b0901030c0b09030c09092107020a12 72
    0x1280d4862a81181700724a00050358020000610015004900000401205400c1801120081d04e0300003c1c2c1e6400409100710300c00c1c2c00714021103800260090742c4003014540220704e503041c8400c031442c2c108241c50145c0a200700c21074a4501d11130114018020341d0041c0c0302c00d1400502080e18407503240301044800c05009010203052100511500300081000d840040f645c0d2090700280080c200714010182006030042c118400c2501c10310451340b080345215842c40b13003080b0030300b0001040314060880c071038150185200035114903035100521501c1a4103500660b116401450041e040c601c5860405003a02e201851000c0140e0005000c1a162042400d0800400384107584d915000c14003080c0080464000340c0c0003060300d550310001045080e105014204601d10210356400c0e0642c1590b45a18100daa10701602d0203100d00440c00301040c3d101040703821035001c001451403080c0c0c41c00f0564240c1c0c0e014030700b0840a0403401d40394070000300300c1c1c8a820703200c840d5401454018120b0600d001e15503600b40c928030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 859825980 1250 859824730 859824811
    0x15030f020702060a030501030209070201140712021215010f0203040b0a08180a06050a0c020606180a11040311120a110f0a180f06060e010822120305040218 68
    0x40c500060f50386000501d9070041685000c103282d071441c01080310400c0014402010340e4100a18900f402d10305910160b400001d90410140384030f01c09015000034014003040c0141c01910308244002c10b82c20095a07610710509a0b103003581441d10a50403610fa00452084012288051004100c4c0f1070041c450705602c010b480340c3c000c0c040a0088013252400b026040c0658a1940e10707407d1200e481e40e6802600b110601c030b80020a4913080040c045031a54014880307840300e901420000c2451680b4541000c0f91070f00c04586c600b40c0742d030307201e0030491699029200090f10032400080c0c0704d0910701c03002c40e500b4203654000710401c1c41e4001507800e00c026801900000340e480100c1820104070301c8000f0ba020407c44050390320000e06507189044640461b61643c02980c18010a0408601180e9008180c81d5109405043c0c0c00e543c40085c1c4080120030402e09401440e10300c5443c0c074929480d50541c0b11500c2640200c4824800408041d0b0070600e003c801d13528419030044602d400301c03801140240c5c04d10409100300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 859827230 1250 859825980 859825987
    0x120703020c1203060a170c10031d060a060906210f02181f30080f0d050109091a070c0204020409020a080a05060102060412050702061b0d02010615030f02 67
    0xd01c201d040c20200740300d00c41040004401c0c001e0b117003482c00c601c1c8054407803681c03aaa88805240074503542d03101040001881642e0541c032040009210b60011f000d2900100b101e8040740314a5100180c50315412107580f1009841c101d000141d00c1110300842c1c0840300ca10300b0700d000300941941110318010690000b5a580303420a0005801030321064015640039140038590b84a41c03c207508210f002c0240c9000c0b02210701c0d80d49134244040404410340100f06207090b059146007003c0100c2c103111054181001400d040317030108000340b5002e8550003e003605020742c80308000903a20f030710201c82115460702010b0900710201140b5411042c01580c0c464210b90203003401040400260f0000b03050340d1050300017130b0520b900804e940b0b9580d6040302046401c810701311070600041c944200000d684580040015003110207400100700d42d00d006508451080da00035103156a00e2251054044075480d41e01002002885041000f200092040c0308030f20a417480c04e15200c03034100383c0c040f048014144a495a003400341e401c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 859828480 1250 859827230 859827247
    0x1112130314120406150e060409020a03060603050d17090604030518040f0204140402070f060b1c0f0b01080c01080712150e0709061706041112180d031112070302 70
    0xc1000d00114a0035070210442c500c0c062030644240d0710000443d040d10300c480d00e170502581c00c020304c0a5074004401d07100050034200c1800000c440342d199a0024100f0742c134108010091140104200c1c481400340e8981103900c4420f036070300d2104890308803031814807900168007040019128400910103942401e09042502ca004000a0200c6520111107402194000380030480200b02d0344502031120011201142044d00039141c803020001c01c460010002d0b9500c050b480400d580f1078030580490444c00c3e10340c0f103100c0390030302d4004030070403411a069400314180350000503a0340d400281c1e200d40d41c2d41a920414241c4940f001a2203a080d1401c2d0510383d581c03580412440507084c00301440c010142800c421a0500b031042d0050305803646504000100540c103031a04c6213040c1c2210402e43c000710203540008d18007103901c9942c402030042c401d4440201c0c11040900c181d651030b5a28805034000e03a5000e41e00d0810b410002582240c580c94400843c03036400744010181901c1250b950b80c1e000c00315090162070700042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 859829730 1250 859828480 859828517
    0xa052b020d1a07090b040e180f03031821092e0918060f0b130b0c0a03080106110a060902030705040518160b0409020901030e030c030a020111121303 65
    0x100880c03002c00940c0d410410503802c0e80020840010300e58480c032203141c1420180030b4030020307c00910503003040c0003901130a440140d04010820070210048181ca46030308192004401d19a048404002c00348a442e54400701400c40b180c2d10440004960b8455290025200a000c10048001c10501104010300e920a511440c00c0401010f01c40b5940d5840c5034a50810000300070101e8006141d080c0a032504005200b081e111030034010507125015a0207407500000c8100380040c0c040c5420004c039011000c13404a441c01c1e4001203004220303109880d484e0f1240e80718402122030103400d019104295000c590350301c0104485a121680050014041d21000d035111000709064580c144c9204003004009a2104400d100a0003800040405001e1a0740410705c1e01032402c1c0140500d004800f00c1c154006151511680640d03c81044013008406032070311010b0106509450350402c64000003d9428200d04519048460044418014880e08556082e0311071101c20001710900c2541141030000c81050494003400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 859830980 1250 859829730 859829753
    0x32009281a0319030e090a060f0902091201112a010203090d02060c04060c11061b061f1a0714060906010315140a110702090907050a052b020d 62
    0xe00c006020030001c0d04082c186401030022a2001101d039107084800026030001212104c520200c1d410021a15503000c1360004044a9100b40c0f421054001d0005100c1e00f1600601040103088500c81c0700c00b41100f644600361148070001c500702c001d04110071030021a52000d2912045500d0504101c0070f0407a52407035089038410354800b0030a41c0301d082c100c84511303410000d05601101c04903040d4145450048084c0100c84110002080780c840e41402c42c2180c0c0701e82e0280c44030040300c80610f0078189004500750b900c8000c20b8400c0c9000c00301894510b4601c0c03001801d000100c41a42404034075260b406011350320b594001480840d1414040380e0492070401003002050b010700207481c05410194036620b000464610629462100c25003000c2c2d6000804070b04241095100d4070144e00030860310790800110501e4803d100d030003540691024107200e0101c10016900050303030b0050b50200700454642042028240301414000c8604000c440c101031280c102000140c041840507001000e00111075540004c0c458 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 859832230 1250 859830980 859831001
    0x2a0307030c050909030c0604020904110621011e150507020d060510150806012a03030209120a0b0106030207080d060803091504050a27050c0403200928 66
    0x18011081c0302600d031040e40190444c00c0200103600c0c10b106c900e60702c0d490f00f10040002e0300c14243c1d5400242800010301010b981084002c04d22035071442d114000b4480102d03034180504003004544000700e021850611070242501440303003200000d1b803605080205002c14001c403002040405d201450050303e41908001126100744c5020983e49000c9204030b40040c210fa100755002c7c034646001d514075580050810360440001c1c60a04048405440704400517100c0307e5945860402e01110f06090660680c007400e04204115031554003241c2c0d00055940d64400180003504203d0f02100400845000364001e086142c4980312241c01c1125010284007100c4044e40b050215800000b034005252030300f18488416040d59121440c00d260402c0046068801c940c040c16050352802e0f6150308410151400c508807042030130605001514004544601c03941041c4000c503414034201c22540545c02c6255600030445c0c0c0d0103031410314240c0d18a20044070415088000e42445c4511100380304285225000304520306 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 859833480 1250 859832230 859832243
    0x160521040e130c050f301e030a1803060f2c071a0708070c05130c0f0302030414061006090506030f010509060307120b04140c01022a030703 61
    0x481ca46400c12404800003080842520048101c41c0c0c0010350303101000d010f68070140e0b2141c40c1d4400301404a2141c818040901840005560340e801c1c42201c44542090801030080a49006445403044100090302c9400c100c140380c2c000303200700701c0d42034842c203811701c85003581040c0c0c45004c42e0b881d1074040171140c12052000d144c270b8403106c1ca503592710220b0903401e444a5403844204d51042c05443c0c101c0c0c980c440341c02440e100510808041d0080540801564101d0303800c0000c083d50380301c0c2440c0485060307903584a1603003c1c3c0d00740313003009440822074403d15601c001662190002112113001c22402913000600c100c0c0d00850540003182440317410045135100e115008400b85141d8207004000d04801200c2e402103104802c00c0042109080310319910a04542c010350b400d503515215040064181840740d0413038046038101c03100768005d00c0181d0700c6803030145010b180190000300b5203076001600d402500c07002c0c9015170f20807184c4120f070040c50310180c020500010750101100140d07400003030500b519a803041c3c422 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 859834730 1250 859833480 859833487
    0xa080403031805010c020f09090307060216060c08040c141f02100f0e190303090b040308160306050d0f060608030d0522122d05031f0605160521 63
    0x15a4104100c0c00d0180909003417584070f152060740010b4080d1b00c03291409000300104000325146400c00c00540300c001e83e000c0415906c0740341d0401c2104c0e5103501620b0545440f4180b00706d1102c11800752900c58007981c1c20210354149a0f05141181d189201400d100903000714083c000c0e52100e1a2108400c420810564040c00c070054040381d03c603003502c0002c0d4010303103078920b40350751603200070400505100c0003c481610804d05040d0b80c01c0c20390050404c140e001d010000c0368404c00c41015480006640725504942c402c020212404100301c044030014040c06801451200743d200118100180b1710400500ca5900402c0704c0b031316a00510304640141c146c04074095185c4003401840074181410700d03212110340d0524883c0130b1540e01c54010345c441c2d010281003400760031a883c00c06441c090300315880340b5054020003080c1c9544081c008210f544229240d41c0da264200101c81080750310300002d6800c4030301a6881904110300c014107001c55005000b8200c135030303100343da56600c1540400d10609441c0051102d90546 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 859835980 1250 859834730 859834757
    0x90d060e010509030f22090e1015210203100615080105091b0d1803090303030e0f1c05090312031b0c070b0c0c090a05060f04090b04020f030a08040303 66
    0x1c1d0340003d0303c0ca00950b0014480441d802d40454103858401c0a088803107403101d1a092008028204d864012038a03090604034400b001d2080050b05001c0f40d51180c10402043d0274031000c114031007405020b0144800e0142c0c0c01d42c055600341d0131580056a00040544042c0030000304a0f804540d215400700c02104c2070902c0b90010b164206080c1c500410082d84c10040914000548941005101c000d06508100c0820340b09051003041d408001600003140c004402c07403007207003005810403c0d1848105c0010b8100718018040c0080402c5c45040103240708000d06054900d40301c90201d4281c40196101049000d01001c0300c2d83d5020011070520362183d0308200e130fa9003401c02da44003068030b09190240b1007a60800c10004c20780c80c0000c240040f9030310f4610050300d80403016462802c10600e4a80d55034040c0700c1d102841a01d2a0a604c668000da4089407074581c50131904d0140300c15141c918034040d003503c1a0707100050250030b01c01c007040400c0f80002d040c0d81c000e040c02ea440100c181c015030000c0d0006984401c0219 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 859837230 1250 859835980 859835983
    0x31e0412020c01020c0904030c05070308031e130c06120f1407111c080a1b09050f15040905060a081209030105010f050325180e010f05040f1205090d060e 67
    0x4612440030304c003a004014619020078103c8502910080c1000801503054091110500c4050702650f404a4842d9407414a904c3d9240700d8029100070003c00f03142580031440c418070031001140510b40c024000b120300da1520368140c070005694920f00c4501c503150000c2c401a000c041c4141070107c1c44501c01c3c800b031810900c0000f0008201044840766035032102031803000110f0f0f4031580340c141c1c204602d051250b5a4034107500320040c10040000f00d00c00010344250121903900a06090309440080d0740c0c56040c0000a010007440780d0762801e001c404180d04000500600e61746800896101c203010309031051322540d89003032510388101401c1c150609003011810007468602801040c0c010b12501e84460903041c20706000070303240e1307030030480a0f419114800342e241030b100c1000510000421001d502c0c6000c40f072468003c07601801c4036400c00c5241c0e519008030307040c4524140c03041600594200c0b20b59140c41034559581c61065081a01e00e100f401021310022003c7d503a200d2000c0c140c0c503c1800003041e02a200c80a46 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 859838480 1250 859837230 859837243
    0xf1505060c060411031501090c0f0f090611120a09140a0506030609090a021513080105091f0b040504031106131e0204060302031005160c110105031e041202 68
    0x80d205190410507400c0c0c108001401036041600003803840c10011a20000920309007100d21030000c40854040000340c0d80107107038014482e820103a00c80b000c0b1a076040c8822a81c00d0808824000829044801030041a104401444910843e802221003650000900a82d650809a48031000a034003203400e0010001071144121101019100c0840650070310300081c0700d6002c01031125000307000c5000007802c004010800100319a40103850ba09000710040300b4182254001c80d074058188940c0d100000d804a4144038881c401c642d454007411880c05c1d4140f0071307104110b03209026010ba0343c071010501103a940d54440d182c0582d2203a2180b000c0703490304996071410b01000820380030000038002c4e024000314204118024179140d003010240c00d1213409100203401884142c00103034052080210800200c1c06561020703002d80c0d1314030716500c0d01c1c0401050440340c40c66410401007825081c49418410365002e0740296400240d2080030302c0c62007201c03821b1031035020000c440a403021003011406000f103030b40601c1710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 859839730 1250 859838480 859838489
    0x3241a0f07240e0304180b0a09060602010c020f12070309231c0201020c041806061202030105060a0f050d0303020c1b013903020307020d0606080d0504060f120b040f15 73
    0x600a1400c65040e103900c030b010314496080180004946c01086a01d26400b542c05860300400c80400e054413400e1000081100b805800c0c007640c07030300c000a001c203400028100e184040703140c0203042c481d0300b2100d051880c0e00304a100710140900d03003102003100d588501441062030690000c01c0c0312080d80100f080804527400c1c0e140c810310007015810b038000d40d0340807034804400c48041e40c0c003081240d451000d0070b0040f4181080549290715043c00414964020145210031310b000320002c6c895501c0342030030020139084500c030b03819112038088010000c50910540925466009040041c201100e84e90054100310b012481c0040d1040e813401c230114590381100f5655810403e1042d1030240407a07421003142e0956000f002407000c203001502000c1014420411503100c2075001d840c08849040c40c1c94050302074070880c00303104528014001c0c0c81680921400c1641c0489801da41e414011421400003520001d00425801200c5629102d0501031529540a96a030341d19a0b0000050001045442095446081c1d0032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 859840980 1250 859839730 859839803
    0xf030302091c170f030711030c010c090f0902090616030215130b010f051309020a030c0b0c0c03060f0613110c07090e07050d0314090405010306060603241a0f07 70
    0x4c4200c841c1c8140640f9071003006406d0204940c5442c08041e40f03180039894501d04990f007403070509400c080e4003480c0d1108403a00304585403101c0307440380132070010b0780100548c0c150062000d2000c05503d1051110a8040310701a0050b0381d905028586e1030010144203e82c00d6200c11542c448100411115100755801050b014844d05066401c0c10000f4044c2e0007201c0160f4032040e1280d1202c0103640e140a5100002d59100ca984041c1c565151101c0c103094001c0b0400070f0f15400b419155004904000c900e1601c6020a030311580f80359566101007000580d50180b1340c0ca421650356003158280741400c001001c010a2070401050181e16110404d802d4a5580700440704541111004122585034078178110503c0703900d070512840920440c0398400c501c0c015400382e0355015007800c00020600c0141e511900a0303640307558041c0702004a0580840b0740d120f008034503001055010204110702e114003420b00d65110084440170b49054854040300b0400d0304003a500751070801e05c0a00007510360920120f030344600d030701c90074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 859842230 1250 859840980 859840987
    0x309031206050a0b071a16090f030c09051306050702011d0705060703031e020d090c0b071a06030304090218090f01081203250c03180b070f030302091c17 67
    0x10040740000c0e200d413186580350480400e0310801c101c840150640001c0c25440c2030740862a110001e42d0b02204840031401c04500422408214040b03000c034038509803070b0030a480c200190300c0e10403000001e0000a105862016441038000300050301401100d0050100f07600100322a500650a2102c0019582034512a0b0b40403803002c018640321081a101c8090300b50a0015035071943c1000200e0315a11205041e01680c80003411900540c59a0f20a1090b203014404110103d611042021064070a501002d4809c07109503005014044048100c1607004c1c00103020750707042036651503000040e82c02140c00d10110b0b001060400a2600301603c2a560011003031602801651414940729200d2801080b0f40804410020000c0c4902d142013100c000e01e1030750b000c0707148407030b03180031100405010040c80201c00142c80c58258120080c2e50280741d4054a15605d04145001c48035951500400000e910803014141c00b40060562540c611051041c00c408040f0000c180c2d030514501490807425045420303118090a1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 859843480 1250 859842230 859842239
    0xd110c1f140103081b0609100507110a122601031b0b220e0703020c1614010305040215070f0507090c0e2107080c0102120f092803030309031206 63
    0x160081c504480c0c01401080d0b031a4040d0800c070809130721908440344c182c4225414050108400607108000c414180c00400098480300c9086942582c45c2c01811015030100308410302040302031100218561003070801c4199854594a085005040c3c000700c032060f142008010821310070795401d500c85911a03924000d4045003010f045003000d001e03002c118103010700d00103025890014081450f4000d810806014042881d081000401961000d807003410580200c1001c21106900020468150303400b00301c0c00440d5013100401107004010080003a03030300c861002c03814a08501180f0040143d42c0c0103016642c0328210500740301c0d18001a0354000c8807404d14007112042c1c5241e11191550500f030003101c015014050703405a6030021010301608010502803568005441032001030040f12141081e0250f8501c44842d0703406400d14050500240901c100401018641c4d147c000c01801d2080b400308070702030303001d19a0303007442ca80740710103420450100ba902c500b58000c7c141c10884403407010510f0041030140e503051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 859844730 1250 859843480 859843511
    0x211806030f1f050d1212060602030a0f02030d02130509091f0b030309120d09051801030816060219031107020a06110309090f011a0c120d110c1f 63
    0x10045040d501d01900e6122802c0503064520000b0030f0000c062460803000780c140484078051410402001c03c00b00c25940301461080c2c0a0102100d240b50003950a15001540c19200005080da180c0b04601040000c0d460f094420310150105058042e6000787d220f007040280000e280002d09208419404540095140407000702450411203411002041d104040d8011038a5806803c0c03d06a000007002d50300e640c1c80e00005801a246486969a40d62059a6100f8024401e41280320000d120760520014008510b0001c002c03e045000c940112490302d0085c0c4440e400c83c1c00c0100c001c003041035000d02d990703070480e814003030182048500b6a10740d00d0b05040d43d0000e518101d00344140001d004003040199404c08060080d81c41c1d0210107803500f00e43d85084120714403030007001d008008504001940c5510507811200c140c4054500f40402424852190380090613160001c0c07003903800b07050304d81d5000d000c1c00301c0f541c002c3c1000c012200000d141d909401c1418100d04a0009050320660349010f5418000581 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 859845980 1250 859844730 859844761
    0x60402040903050421020f15030a240e0a050c041514040b0c010b031b0325050a0e0a1109010909090c050303030c0c01050c070b0105100221180603 64
    0x904840001d000380591400341c5003805158400c0070f24070801e40c05a90400d10005010f040244219225034203513160004114074481850458001e010090000482d60150743e80840e120002c040100c10301c00148484200d45442c0c20342100790708914040910060400718090b49801101c141500e606040c2072081d602c3c0000c0340460130b074041114200c0d42a55480000341281c001e0040c0d902030030350344c40300c0c45000ca018007500e00e15607000b8461680311001000140160144076403006001d0320019140b42e800c0c4840d035000c0c05914a10400703003000029180c1d0b44094050003000300b00c00c0c000040c1340c654079160883e00300c1c1c2c45510700c01404120300b0056a80c80960380c019140306030700028180c1503900b02105260b4003900040e405100000621943c0d10200c0d0207807a040e000c400c000d20040d640c01070800121701130484003c00c4420b283c0010f00252030148440150f4104510403100c20102e082900d0903508440c5010140e589800200c2d06041c880381c500c034414002094462600c0d50800030441e00130308070f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 859847230 1250 859845980 859845983
    0xc1308010b090c1b030414010905060405150307021c0806030c09040309150c020303040f290d050405150748051006080c011116030b0c09031e0d110604 66
    0xd0b0010707540344080d0350103251594104d00a822a0385498590301412060300403d0a2140403c0380100c1c0001c00c0d2820108880555402500c11002031601c0700340c051540d04040c6c184000c0d805001c41d0741c6111060200c007001d11052507507540c0c80c00d0500038140740c10b00300440003a13401200c00108001c04030b0382010100c403c542240d41c24964101c0400c00880f50b60410394402075043c0000100010400542c003004800d0703450607500b125145088800001032048280303241090030b03009105503c2e4120707941d0300c9982d02500031000e80f840c44e840d5001001500b2803c0701c0280104140c0440200c4135a8452600b940d02411104c1008078504403449a210f521000d00c886104501c21211803010040e003440701e1400340d80c00200500074a0f031607406458031010458074290000312001c448450f1100f0005115100d0201c0d016404c84250540c0c03078021000c140144858031500301085240129141008000c2103e500884c8005035040c0c00d50101d41442d0182c0c00b11000c10070400740400d800c5202152681d00603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 859848480 1250 859847230 859847251
    0x1c05031009051b1e160501050f01180903030b13050a0b030a0201081b0408031206031903171506120f0a0905071202011728020c2a0303030c1308010b09 66
    0x131084085100c04821000d403a1a01c13140000c1000f10182c1c13259809018024403d40c024090395842e14001d0020f01c00034071858a060b01613020442d10503202e80d00045500f402881d010a85801c4c110100d4032141002e803460a81568800801003d11820711502c1200c0c0801c5001d44401402ca400091003520060490318455004030307454090750800700100d400510360902a00d889510070300d444030b14090201c500602a001b15848010b1140030030427111a0103516440300450102400004021440300400c0011290800711804803203030344006c082d050001803134a0702c2c0e9280c0340160004070a039001030401010356080c000d2450015002003500c1c02902c0020b03070018840800d600040f0b6140d045241d44c84402c003a0b01040c0f18030501c08140600c26030036140d20042000117004104401c82c80780b2400010640c024624901c0e03511020f1807044104a000310181c000e031081c15000908660003640c40100040380081c0151403556507000441c014406080200030381e440c1c078004103101020040c03040091 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 859849730 1250 859848480 859848487
    0xf0b130b0a031a09060601090b030f0601020a0510020c21070b0c1c0504021903050c120102070515010e160903030305040201031b050c01060e011503020c1c05031009051b 74
    0x80c1c0d00c81000389401150007048281000041c0880d4482071502070f02d0780d10540c090000051400d500030b031070440c11104220952407540d9144001082c9010001d0310583c114000c611420b00031030001c1100b88111a42c01200590b10415070308035924108400100c6a035000010318024048001310065410079078000621207041c6c0e0712000e14905030b100d901c00c609400100d1454406200c0d009900452003580b080da10b10390782c0d500c8885000d41118042c8402010340d4010100c00d24982031154200b2050f0f080440054200312855664900348008400b4500310000c9040040000b100d4481c0004d800500d11460340f00c044c000324500400b2540f640c00080d06041c1c492020500310792113980124850001509404a803402c114001011a03000b001c0304d10f0290709052001c124030207404101d03030480c0c250300c800d081c0341341e905001a0080e4000100c64581801201c0c8448030340714514013000e0064089948541e602c0c942030014041100490f08560052480c0c101040f2422015081d160f40d01c40320000700310f44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 859850980 1250 859849730 859849751
    0x2709020f04090305073c1511071401150f0b031506040e0403030e1b030a0b070302120a050106090b041203030e0f19140c09190f0203070c0201030f0b13 66
    0x1413510849400401ca031003c0304401d401e4211501030004080c035640c5921503c1021710715110324208917248060b1000450b6403e0725a09015030f40064081d00c159801075080c5080340d01c541d80c0c40e03a000b030860101651255041d1602850440803c006420056004011641041800852400b00414108170144245201081e07942c40c14150780c000c00e4407103100509071a00d854020068064030140154501c0f40c1c5030350a0181465408a0380f4600d4044d000382000b03403007600c40200c070450140400c81403550070040c1c802c0c0d0101d460840b912614034600042059490250001e12044065011141210b03040c0024800d06d10031741d000010403505481c0110301d1442900981d41030501155410142c8e100d40141125401d60210602c505079010b042c040e8400f44519030060b856520a107840d03580111108002201c03900424410000803003012000034168010b0050541240e00640e107100209035810807130004c40da814040c2540e09404181d007400060465000f25117512844e41038080040e40f82e079204035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859852230 1250 859850980 859850987
    0x191b0b07080c03070c060e03010c030501080a0305180d030f0e06120c090a05060a02010f0e070806010618051e030f011e090201050906070b10080c1c030c0b012709020f040903 76
    0x62201d6004881da075000e41d41e4250190044100740400d234020b50a14850a0240d07001c1c0c49594126201c40c0064840c2c42c019075030072541f9034011040c60702c02e596031341046100d036114a2000707134880d40f00362161924401c7d02c43d80940600201a0401c1c40f928081100040c01d44881a506030080b4001c9440340d101c1d10843e001494441464100340d8015002140c05543c1690540093751801c51a0004008915964500d0368480003c0d00900d03040c0e52210b001080740300c0c42140d12001154a11600c29406030715078002501207003d04800ca20411000301d81914186810300510103140081c5c0000c104004003424600d481c441c03007008086d00e0369030714a0300c041564080c100311801d501006108a03a221601d02c0e000d0b03101d41c1c0030754030a0000c00600c24082a10800010143d103003030401031400c04e21070003281003001d030403604090490801005e81600400034041c008aa07018060075903552441d88074400ca00b40d260000210810180350602110a001d40c80b1705100741486681560045035040e41070030180d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 859853480 1250 859852230 859852237
    0xc0c071a160302070519050a0e220f11030a0b01141219031e0512040f0812040203010b01020c01080f0915040615090507080a0b12191b0b07080c03 64
    0x1050740c807402901001010f80c0481e4040c26130b0030071100c4c8501103103220418402540d150003081e400420100c0140086942c4413070341a481004880041d15100c5141030481c285003106c03100300c5071540f074120180208110403403142d02c4400250000c010f02e621640b05d00c150420184681c0075945860320f0361030410385411340f00c20008111882100c1601e1031114141c1038200c0f02c0d64040d00080c014902c503035410701030001c03521010303c51641ca20781402c1000104a2030441e0107001107611590125418001072001d5014017400007110011801d070b4500b5005040c2540e141c00200e50441d0002031890502da80c01c5164035803c0399803200e840307c0c2d0342c0d50344c0002850102000500003020b044002048100b20803600b203001001c0d120b42584904580d9580c00d002958030564086012519140025a0b030b060694042c2c14441c5005201281d0600581c0d05942070112502180c0011141110900c0900140300b04a041800500ca2000e10a51501103505214081d10364018100040081c142039440000c0040c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 859854730 1250 859853480 859853497
    0x604092a241d180912130e10090e0a0209011a121314100f021207050d061511070b0c0c01180807061d092a1606090b0c0c071a 55
    0xa40c3c1d80004076032612412480101c820b212984124000d03203024000b1841650140600c0307802d0040c5a070b040c0030600341c0c1050000d1990040d04580c0c100082c2000c41401000090803082010700100509401400002101608001c00c11038041c0540c24000466100302c800c0342ca05914180541d441e507040d03250b90100c01c110060400e8009080d080f480110118120f4009404848104a03010030384101c88180d010b6404205094415000080c1e40240100700510024450f0900041c0c03560b220a969a00204524040000a074100d5042294103034200480005444640d484500b080f40c90707000f0315034903000d0b0083d990420210740f450101c2c40e00b49810300030107011143c0590b0051526818010250a17039001001c446154a103080e240e241080d2109a00440f541110244000800b040303c034042e203c0003104000010081000d00300030b62341c0e43e4640d080e0a120303c801081700c207030034242600c95542c06489444513280800c00c0d120710742800503008080312080091801c440d1420602440c06c0e0050420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 859855980 1250 859854730 859854739
    0x316030209160e0a03060e4c0e01020d060f0803071410230f0f161106090102070c080303010e130303141f08030a02030f030604092a241d 60
    0x60210130840c03950002412a03903014200d5842c030b404010b42440e000640446507204c1c00b00c83e080040c003c3c11107200c5a422300d14030080c2c0049090703103540780400c4420f100007494080e54007150b00000341009006c0d11005210b4a20076406103800c1c120030302e0b100c0c805c0c040000c010500304050000c01071030903c0f0850241c01c0326a0b0400c90042054000485000d4190104c04030400c40ca001542400f4044001e9003d608074044140700e5583d80901c12150b18000403419081c840000312008140e0001c0010610a0300c607417002680b90919803a244000c583d041d00220744607041400140040d050540206521010840782808507030f065080590041000e14a900101440f00080080e520402ca441845e00c00890304200031007591103108a40b6801900611360058104010384580a200ca5000e1034000b80020400078130928603a452004421084109490500e03a24a03542646412595404010003080c0c6071351649040d15030a096074844a02e64200c180028403003440950010102d0340d540c610030140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 859857230 1250 859855980 859855999
    0xf27070e15030d0c060b06040315090201030b0411070606080303070c03030c09050a030f050c030105360604050d020c0603010605042c1f09020f0304120c08040e01050316030209160e 79
    0x20802065103a1049050b6445070030822804e41b6401d000b82103d040381d0304100d01c0c12610314a11110009007001441c241d0401d900e8110580940e034840c07180c0380c54200041305050f80c4100d50700d807060030703030b40c16900c4001d19400c1030040007142038012015680310b0381e15141c0080d511100380000ea4042001d40c1046810821180c00801048280b0b1031545c01c3c0c50081d4202e0381c85c00f00e188101400d80310111111801c541d80ba408401a0340101440c040a90020b5080141c0d9440c0c503000280c54030a045409075182d520040c0b04035a041d4040c8110365001105441d114950340c1044405440c5108900c50000c0d001d41d1031001c00302c000131f1040e0380c240e048048244140c440c00c118003400c150402c1071140e07150000114030005018506482124155450300480324250f0703a85803110030a501c03150b084071052151045e0800c00040f9084001d0014080c1080c4084075941080140340c0340c4080495481c418000c10304c0d052000daa00e0394801988540d40035215440c0701641201150300c0b44c4a00c6c46250443c00c1c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 859858480 1250 859857230 859857253
    0x4022a070f0f03140106081e01020c151602010b06091318051f1404060209031c050a260a0e0a080c07140118050d03050c060f27070e1503 60
    0x82d001c20480c3d0043c50034070000c0c3d1035207403d1401c031205441503d080340d01210460524010300039410000c40c042400041c108910551344600f4900400d2044850400b80300c10001c5034844154002e9802c41d41c0e05c000c128a00f40034000c00c41c5c030710503261480d224405604145040d00b85580217080030241102484003c0d4220b45402c40d82c0d4a80902c011a05044400107806034003098440c060303014003074000245803600c540d10f4070b4000350311014110787c1500a5031076034034000200329048044602280d0310140e4a140d0010010010700d000c50082400030040341c0e0821001d0142515103030080340c10030001802d05015a105803801401050003007080340007040d64042c2000c00b04200c07045408402c40c16070410880c40045601c00c0703400031441c24110160009000c0741c00c0400d214007000c0d1280c200306241c461000c0f1010b1814504542540148180004114480f10030310450758039651540102c81c8444549500c0d039032a040e840c060203a20b2030030100090320041064a000d01c00c00b00c0070f001d4441a0901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 859859730 1250 859858480 859858499
    0x40212161a04171f18170c06070c170a0e010e040e15090d022b0903080309030c07060e010203180607020d12090506040b160c0905090706020c04022a070f 67
    0x301c01310440d810f60150b030360040d05580c601807101c4034140b0500741c00299805503102050810400c1005011300001c2c08042c0840c8030802c1114025180b40d141c400700c001407403500002009402a6100013554184801c8102507008042243e000c0c109083c081114081c490209009114240300e29180384112603013044180803000c0c40074001c4240310162130942c220618180c0c0d807020080c0b40c1c040d8088100c2050320800d04020380d0782d081d942117440c3c0050780765a2600d0342206600140ca14038800d07040001c01c1d0b00d0031082048030a00500590421642c00a4200d00103520f034003800e400c032821088581d4141c0341c80c1e9180400c40d443c07203900900c401901c01560900780c040508030010a4045210000042601d14202e81640d04450828840616140c0a115491400308041e08101e0301208540800305020702a400381e40d10a016100003001c031940703042d000a142072100d08810740990300c104002011001d42600c9042c000484c200303480703070f000c2244504602e0910980c0c040e800d40903503240c01150541c0e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 859860980 1250 859859730 859859743
    0xa03090b060a140111030405040911030d08061c060b030105070c020306010b031303050903160b340609050a1a01060f020f0c090603010221040212161a0417 68
    0x11011001140c1e00c001c14000041c42c54011102d20031042036102609610540c030803d02100d0800a49080654a0300420250782840c40215504503c980780e426550408102242c1200b0042c0782440c91070030054080780c0c3c40d03074004c8814a1075513555400c403c18801e964001c4451890060000c21070303031170b04d54002030103c0c00c0040105c0c842d02031040009510a012801e59000e001c101d4200301c5610a542d40035145907020300d854642601407a08494a446d03c00181107008101d900503080e52034a02481d070703050700014200542c0810410b02d4411011115502951045981c002c4000806c4004e034105135181c8000200b000704100112440c1103040e44000e000e8904a41032602c40303007c04c5800c1034080c2c1e2103c80000385014903074008034600302c50345419160250818400380005141040c102014901c0c9103400655884402102040c4011401c160381f01102c1400343c0006421800307103101059529140740d00c00c800a4140b2030120444803c1304108440043c500428a08103042110000546541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 859862230 1250 859860980 859860983
    0x15051509090c040f0608070f030f0e03030405010903030b031207170403020604171e250909030201020309070512071503060e0108010f0f051b0d0608061015031b0c170a0309 75
    0x5814800007440342c6c01040018021441c03515484407419132800304078010000e456072407504984440c60080d00001c2400218001e0340210300204461a050401038203440481c00000e010b40c1c01140d003c0c107800391810075500b100c2d9103c90f00d4684800c03400c02c4919180103503000650f010500140008010303032009012039110b0203003415254203840d145110610445204980d00307850b08000d03410354200c3d150200d51150684942101110b040d11020840129201c41e01c0441c0582c1d40081482404501080b0740c80042a00700d8030076040044c00c400142d181c55903032080102980221540c0010f00340a40c0025014203c0004001c4c410761756000042c1c06085815044281036150001d9801c5126442c05005c2c8508012648040181c5019040307000c2d9034072643d03050800542d15540030440020521103039002e264141703140703080e090034840703040004d01c0612090030503d8980005407851480c43d8071141c115114030705008074010510b0074141105020180f210341340d880001495100a81c26030300c400e403640d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 859863480 1250 859862230 859862249
    0x30f0301150806180a020a0903060515180402030a140307020319060b0409050c060d09020405070f0813120509030f0708031804020913051e090d1215051509090c04 71
    0x2a2903c409004803414040d1580f40c502e606070000a4640c601c0b07800030503e0910910b80700440d04c0c0d503901c421040300c0041d603aa44d9039079044d806011107480c20700000c40d80007000041c00d941c203080582c0020b542d81c04c0004000c10214160501b440020011300545c0ca8894010307080e29024405845c1c0c08040b140540000c03100c0c0c03031415001c04403904182c440c50700690350040007000c201421340100705140d040140a810026207600003000140c840e400303860b0080e02941c481c0090f400d28514090000080104201184100e640240e0046a850211444a081541807040e43c544100d400720f41031580045071220307144103400001800b8038001000703104200940f8401c15110b42c602c01000700342c8c03041880b2030b64061101c1c0c0750b039841f03005203a0209801c0000400140c43d000c1d4400c0041c140f003c41201d9032250b030f1301300d0354260416942003000b283c041807506404004541c03089c100d00d016030308140034850103400e00082c000c84201c0d000d07040314080f000083c04000607140101180317074030b5409809080d162 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 859864730 1250 859863480 859863497
    0xa02010623031f09081303061407050415051207021506030d0234091a0a0302010c0b100f09021c1e051003170309011d07030212030f030115 61
    0x41086185a0142034500a002d00300784820300e03d22203000d1801c004000e003030683e0b55410000092203803000f0001d544903102200400f5245040c031004071080c0081c1070651280c040c08001b1603aa0001c1150103071241c40b19110a4100c0030ba608640e1030196444421185c0d10980602c44803940003e10200e5069000c1e103482815501c40e024180c45a409881d00d0003d6072003101003041c46403040400e601d1261150741a011180080c2c003003003251103002c1d4070404446585801a48a6280304280100c09440a42c0d1075251246544c0c0020103007803100030003406c00b41da047c020a501c0806c010828004007030381c04032110010785400d41000258040ca16030300c000b03641c1c0380100140727100c28041c0c2c006a40e0800e10240322900302e020314030082c5c40000e000e01c0340d40c50750180100000b4500403441e4603404149030f181d5201e02d8299040d9084444018cc69011900c03030207011102640c1c00519001581d0741911206502601d08001c10b2071030203030803c06280d00c5004400450720102c07503018150380c1119a55440d06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 859865980 1250 859864730 859864769
    0x90518090705270a0f020406120b01030902060f0c0a33201b06010603090605061e040e0c0405070806150903060a09020d0f150e12120403140a020106 65
    0x22030658007a00f801040c00002c0c0004003514000c10b403181c1c058030244010541903d80750700c603402c17a4040d40003040132071071620111510720f61611480d03141210030b0804001c60709464000481c2c901580d442c030300141000041c070000200003806401c07040c0d0743c0807850340b4101749200e050100d0126002c440790840c0d404410f414100c030800d401120a010080d000c1c1c0101011460710302c001c13a0707000e001c0078000391490083d0100c4044082244a0082801d41d070000b030b00e9511407410400b607510291089200f201c80e00d03400d045c041c2c021812024414000c0300d000410702d000000c200d003000703249551598494505010001d0168021415600c1400d00b112407020514000080e045640500c20b00c4941551008001500051041c2d20031005680002e144c1035090a2a80e5403c0c0c26510040f0121207040505440790602c0d207442c02071142820010300038001c00410341e400c0425031302882240b50160006140403d00f0f00d8001d90205000e416018586907039000c849031301a01800b1284122409080c00d03908445 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 859867230 1250 859865980 859865989
    0x21033050102190b04020f0312040305010b040b040b010f0e0d0b0c0c0609160b03070c0602030a090c1403120706060b0409150614120403140c0a0c150c060507090518090705 75
    0x1c091644418400ba44e07494640034017102074040c00140344c2620442100e11659545c880242002718401c400101c0d60782d0308402800107030785100c0301580c0614140048200981e8020808070403541003441d200c640c03145007200007003022841e5a800b40c400a08801800034030301502c8010010f00d074101c000c032425616000d40b0130b60360700801903520800e060401c10a1000b420f01c0b000441d08100c0c980b403da04458281e442e900e00b240e006840c03d00f035040c2d0300c550000401c4030446203003009084412210202807101d401080e207035803a200d8000c0c0b0400740000c0e904104405c0d680580041c4c0350405895480d65191000c25000b03192182c04111140c0202d00005001486040020700f1007055410300c41c00c0001640100e40c1610380a4401c03420310840760311040300c603040342d009892040441e100904141c1c04c0ba08010341c0f00c00051304081001071700c1c16607085030107800c42c00c001e41003903207e180003c00e50307039501003102c19048030340000c0d0f8426070721b904c035044070000400794034011003241041d00d928a60703550402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 859868480 1250 859867230 859867273
    0x2a070503091924021e06042f0402030402040f0c1701080102041511211222030f020a0b040606080105090d0f0e030106050d05030418020307021033050102 67
    0xc1422078162603c3c411096050245901d154000d004075014500359070014010f1017280c2030303000b00e00d602183c20001404502800502c1d11643c1584180404c00c0c0c8000581c6c102c120300c000c4038001c5400202007021500c03568442c0700e500e5140301c010040c0d1060304100401084e160007504240c0000c05d000070668070818400c58089400a201e1007015594405054038040344a0720307039030b501c1d0040184580000c42e0980f044120318580300c1005956045540a010f03602d04080c6c280625803c150f030721a01603040d4810049004d07505420440300c030105c2035400320301c2c01007201c0d00101418061010702042186982002e025101c2c1c41c402840035a90b140c0c012030350790515000c0300001916290150b91514002c03152050710034006800426110344540100d01141d028520480d80c07903100040c20011014561880000402204000e5295041c2918000d690b44952418540c2c003d44d00c0040f0070702c0c1c100b4210031b41c8801c82140e107500003044889080503550041031150501500581982c0e500480004144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 859869730 1250 859868480 859868489
    0x60603070602192907030507020f01020403230f07060503010312112a2e020703030e0103111b010606020105010501090302011e0201022b1a03062a0705030919 69
    0x2409142c0d0300c4d50001c2d00c000c0391050703569103c2c07003202c0d82c007070700c1050b02680c032890345c0d40c070040351506001600900c0e1481a1b90102d4070f51348180b000303000041d040040d0500041c5186844400c1c0d88250003c80e05081c1942440881445070440004000b500040554100c070701404801800f00b00d818400e4500030282c9045402a40200444e504082d0f5503c0303192048540c3d0300400212800032601140b1a10786588a0840440030f21101207180d22284001150301d1b0b80c0da1000d090250314696020300047c1c00c0300402410316484005000044c0c062900751014104180700d0f55038006071000c01c00d4000c00c00c5014020055081c030001048550150811340d0480f42d0680d02ca5003e000c00d5000c551286407803440c08400c55408010050101801c903484198070203c03030303c10341518500c0070140360840d440002805104a280c02c5262341c150b50208850350711040000140c0c4100c0740000d800c01c2014812840314046c00340c0070600d6800c1c481d00001505584d00c01b40d9000004280c0045101c80f2100a80304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 859870980 1250 859869730 859869763
    0x7050708030a0c020319050702120118031202070c03080304050d02030f07020105090d0501150e06030a03080703050a090b1e0109060b090d1106031603140f1620060603070602 76
    0x8940c0b4054907a111420021007441076038100600f0f409030848084000610000080001c140304055140224a6951032588000204152071310500003081e880050f407030203000d102b14400c0418501e03030190111800c0c2a40680903450498403458031070f200703030801d8a040e1100d01c10041001e10381400001201c0a0504d020b03030903801c041c600d9004641d182d01c80c031003258001c40a00080c00009200b406a0000d2040012445001c90704000e41c814460310020043c5209030722004442e40802e4000d0103a50f04510240380c0030840740d4802484502600070b0040042c0030b00358110405c810200c0e4030300300401018180e0907005081c0da8440280c020f85015000300d60286004100c885001c0c60700780701500c0814480c40c80c0319400a00b0000041164200f140c4000c1c1282a00706d9503001181c0c944144c000110b0340406001031418046828042114001d084109141e16020301440f168041c10322480035403007110000404400d49a401d0f0b80302c1400741c40860091003003d0012071501e0010511800d4403002d40d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 859872230 1250 859870980 859870987
    0x180609060c1303050304060e120105100b03040816031806111005070908030a18050d0f11131107110d20010c020303070311070f030b06060f0f190807050708 68
    0x16010305480d84010b40200b10020140750000020b0014409800201000d0311002c92180c21982440b040040b040400b001591400c010800da0076103014049040c0c80d0740105040c0c495a440c81c103070056100319140c0590009021412a00701507002202000045800e951390301c40d140d17120001d50344262003c113800035540140384c0042140380154804d951018861606140035550390740c0c03042c01c660001c54581d00141d00c1415460b4800f143c03900440c014041540c5207407500265888403507000c000c420009103510b4560b02424140d55400551100880b229601002600400499190b481c0c3c4414400c031050341c031251030094145050084200019001540c0e03194080d000d251080382d00350300410f414140b21800c81580c001d07883c1040a400741620a450b201c0e0400030700d9031518a0162203501c00c00040c03508480c148005130000d18800d8009000b035820310b0701d07140f030540040400d0003072000725102d210b400b04036446182801e6890047c480b400740c0303c00c1e000c3d803200c07401210b86200e407141c00740c81d044040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 859873480 1250 859872230 859872241
    0x30f14060a230603060d02100c050d0e220e07090e1207020112241206060b0a0c08070c030605040b0103060e010b0a230405180c040b0a150302071a18060906 68
    0x4004c5601030782c014001078882205500003004034110003c01070003e4450b4145c5401c0000405c041030403040c003410b100340b6582080d000200c09051084604151040d088442041d52805802c500040c00161041d9441c541d102c004040c01020300d01601c00a89c841d40896041400c001e01c00c440002c5c0d0180d6560070f0041029003d4000380035110100c41d005058425a034440e5807000d58000b0140104555030704842e0800c0c10690151002d5422181c11280208070401d80140c000390341459913030b4401030207501c840040c2400212035095602c00b8061038217260420040000c861440d5069038401c04040244440c118030441c222039111040c03d030004d10f81141401016400f48040710022104030001e108000301d100814141c8030144c900b00c020002c4483d8a003e041000d01000081c48001c3d81d040180c00a4200010300d021150f202d2942c00e00145d650724940c00d486501191031050304400303442920800c1d0b481d09031444100b2603901c8990b50381010000e0840c0d902003201c1d401106094020209038946 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 859874730 1250 859873480 859873489
    0x406150504030215130e060102210a11100e0d0807020c0108060409020f04090b0714070503030a0c09120507031e0b0c031503060a06080d0903030203030f07030f14060a23 74
    0x2090440741c084400d011382c0f004c01701030501000c0580b001009078202403d0420004e490b00d0544040c003004209298030802c0007111706410340740101003034505208032015600070300e420035120b28103a0444a040c208644d00c002c50010740c0c4d0080c0c5410340d49286c55030380e41c460106d0b1200510030f8040d00140c1600c0100b00580717019044500618001810b00403151101400107080322a8648101d6651744030404002c002c640054200515540203103650385010101d030b03a1280c50344030041105402e142c1e00c4400085640c810300c0601c028080c5642412084d0401d0308200303949800d548030403584040f40d5414900300d0200240b482c0c20780303507120b6104086500c41514170600341d00010700044c410b00075401c007824203a400700543d501960700312074006421400e0101403030501e00440c0c2e0810a01120110800c0021784c000100d0358404440da601444a88403007004401406150b50080c0d000340c14070407081c02c0150b061581a006160480d42d14400c0750b80e82d40000c10035502c01e40300c00109030303044054030b006040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 859875980 1250 859874730 859874749
    0x141f0608070309140102122d0c1303080403060e0606040623191403060601110d03090f1203052502030702130f020408490c060c030b04061505040302 65
    0x115451581c6050204130300e503404c981107410110383c2c600c3c5400510002e841e010700c14440c600f042480b103041d000840018046021005800074a08401c00184006050400062000915804100f090351541d070b0342005c030080c148001d0088182d0080c0000b04a89146c40d00c241c0e003c0303412681e500d188001002c036001c0c03841d415a40f1040d8000c03842a4409501d5442c015402c400703482c042000d0b0340c040c80f485007851300c1c0100c0100014140b116000c030031500c24400145203803040c0d01e1803501080c040190b20302241e2112800200808000c0e9100e5030507000754042c0c02442c41810010361145070320b007800e440d030160204103600160260308100021005401e064030010000381c40813101240c24000102288200d038003e51102100d508100c0307600034503e04c001c00c0188120304040d2805290184801c00e400c120000c1100c040700e11180340c00c11000d29001740500c11905400c00700030811811128000380282c100e110000384141e103403060218034203216010191400c54030365603160600741180c3c01e1124101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 859877230 1250 859875980 859875983
    0x30d050f041a090f03030a0e06090c01080105131e0207140d0504090c0e12071a131205010e011407020c0901081903050705070807050117060d24141f0608070309 70
    0x260201d40303c0c1340642000114068803008200040d032400b04540c4504200018000b04040d4004040640a03603038441c2e0441c2c15200e08a82080c0042c0c50b120800004144901c086800d039038802d1155040314180d5406014182d003d050044400d40d0314103401034450450401c80c0000c12028402484a00115071000078400820b0522054503082080082c1680d038003110179030301a80c48100d0a10048512844450238620101e103400e0400b5029103412018060301e020790004d440030703d0032040510000350000f00344403a0749002000603041480c11500c084000329440030161091081d100418140340a18504a0310032030060305022201e00e011000c0080d848000340e00b0414207101050208a0900600c0c00a0103501e000b04000ba00e40000035000040d1903800d02c10001084d4104091510b504a00c510030642c003061000d966035603c203414003054009034902c103481d4a0205016501c92040c1040740c050040c400e4440c1c1c0c0c0055007281c080524029018100000340300d040420708440c0660070200085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 859878480 1250 859877230 859877233
    0x80903120705030a030605090c07030c1104090b01030303061a0313110a060203040603050a0605060304260408010b03011503020d030f03020d0f02091f050f0706020702090405030d050f041a09 83
    0x15140040032001600a008142c030603030800a80302c03500a0b0140b05500c01400305540c0340c50b140c6881c090813070341030254181c00b40c00c0c005860080750400034681c441c2054000c00910801c010f00d0701341020f181e800070901048021030b103402e501040300c1e14215003c02611074070705407003841c40d651004c124900c8840d140d011100c1034030703182102645690301300106016103070590003192150302d045401410344002900d00b070030040c9020340a200540741e410440340d0046e000112011440741e200c18a0292a8000200c01040f0070b0215001c00c484c9810740282070a250110001e0101f4030481d81103c8005070144030095000d0403040000000a025140c201480c002500300103081c460713980794900c19264000000d070941e80c0d00041d464414030701281c01444400400d072280e030004c00b000c3d002516520580880444601c004224001003004540403629010790181c9040d1150800d803420035a40d030000d0044041150904000400d64050801c0380ca12035a00142c854000c02119601a9440701e40a0310f0803116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 859879730 1250 859878480 859878493
    0x22a0310020c1011030f04060b030f0321010b0f03131a041101020607080c0d09020402070c09091e03020c0f04090f08090a082109010908010501060509100c0b04080903 73
    0x440000d10281007500e0303104010f41602c0e510140c031642100c1d44248034000d041e07424000d010280070124070142c0d001d94003004c001031103264000000c0c80c1c59418803031006203100000b4820980d813a50003860049182804451100e07980750742d1003581901401a07003c25480060001483c4944210f5101c2a4640a000e4420313107100c00321008000d20808480554201182410400455078100704440c3c0c8030840f0b00c0c2a560354144000d403c512485504000d55070261200c80c00d5056584682c115091903610840d040c111301c0c0d650035104007800c4130308000d440c040b0030160300c4480540c903601050031b2158554090811440d5100c10004984d142e080525005552024860005940c4030b030018406805500d810352900f0101041050400c115000860790780c000e852400e241074259845c1480c0384104000840c0c81c0c40810b00120740710085503001e518550b0034440001501da0300000104515002548c000b25050303860b690a407080c0807054002000101c1810004020901220190202100040070b0380c0d01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 859880980 1250 859879730 859879753
    0x1e051c060803030121020a0618050d050c0a06020706050a08040c120b1b1611270103120e01170414031c0605010906120c092102040b01022a03 62
    0x4a80c0340c0e802030101680000300602c6195296600707242003e40ea0030b414600d9150a9000c90087d803118881e18003402404807101c1100307201920407501500c0082e2101c094440700e4240b143d901d8659008081c02502c80301c0300400c03000c0c40400c2100a80725640c030f5044c5407070180c0d2000c6903000401407064a2000c46501c01141c07110341c4207c1e40c500a030094080c0d04142c102840504500d2401d61111600c0007401c1100d50320389a50381d81c0200310650000340c1c0c2d50f1140f201d0404919240c0c6038500c50700c0003500f41600016680a00d140d401d040e40e01501d0712071940303803008109036864201000d59034041002e803840d0101803941c20260725030161140c900015039140d880055450750308041c0c0e03601240b10307038a0301101c40c1c502d062084030000c14007440d00505007860244094802103c1c494a0185103031a40001c480e16401501c4820040210550624000004101600c41184407030412842242031034080d21081d0304c0018900c061800c0c5c071150900181002c0c408070500414290501c0c1c15000b0080c0721103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 859882230 1250 859880980 859881037
    0x403030e03122d0414011116030b18061b0901090302030d0e01031401030b0601051818040b0a14150406090f05040c090603030c060e16061e1e05 63
    0x3c1c0842a076411103141d501d0960700c0c1c040481d01c80141d0180c0c1d0f0800d0200b005803e2011040005404003802c092070f44c1405003407000d0604160070000880c50070402000420044644d150714801c42402d40700403c101c685030030309134641205503820101007690221210040c400710f4010400c2c08014141081d101e41d490340480d0a14207600320b040003162582d800043c0c1c03540c05000c0c4000603612410711510030341c11a03640f03103200384014050904001c2c010030984803c038820420b810701d4a5000b003a501042e0840b405c4440350000496048802e00102c03404903900c4100c5004070015041c4042c44990940d80300c00382020b03942c512141680d031240d1980b80010b20b84a0511400e130a0440c01309021810b49400d00b480300c0384c003101e41d00210406140900c1040403c0d072000d0b5030032200f40c1c030500c00b0902100f0864250715003d000c0a0118040840581c000351058001401803000c200c2034441d21700c07030b1880f1301050b03c0000641d1a941c688003a510005c2200501c0b500c01010794003240c001c0303000004000c0304000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 859883480 1250 859882230 859882237
    0xd0e01020c0307080715020109050d0f0909141b0c0a02090c0403061103012606010b03040c03140c040509071208030405030c0601090b090f0c0702040e0c03030f040f0501020c0102030403030e0312 85
    0xc03100d030810705c0144011560081e44515031070180c0001c0c070107041c450391f549654070007010300902040941c1102001e040d118144110007001c42e40310500074402200e9142d8500201900e40c0e481c0c0c156116032004901c24108141c951006400f009000c20703070490703000d0040e1000c00038140039803440104000710010b0064480c520105402d0341115840e503052100c100c110143d80007424111882100c4600218100001c40318156001c4e8004161203484a00d44240c0c14401ea0300001d20341f545e500035445002000080100c2010b20440701444291209042962114014000d851001c2d0015881001066009000b503400500c600c00310f9140c10742c410360080c00c00c075081e0824040c01d40c491070440740d075260134a0a1500001c010100e0032103030500d03040028091180306802800380303460301c0820031b242ca42480138820101c0080c0c1520350355030907030300418102c1e8480d02800500022251020505510000e501103c81c44180c00451920741161001e83d4011103490f00141c3c1031203032140d00d50400070f000020303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 859884730 1250 859883480 859883489
    0x1050a2a1223100905010b040603020a0918050a1109030705060906040305010e0f0105070e010c0f03030605060417060a0b0312031f0f0311030d200a0605010803031008030703020d0e01020c0307 84
    0xb060300c541041c40d00c9800415075980300f0820300c1c4c2050018031925140404440c110780f020300300141c0c1c860804a058444441950006101815003210b03210900e2180c3c000c00d10860503000b007000504565559100c1034014501040d8156002540503c011b09200f0024041c0300c10082007642072075070365a01c1500355184111307619000d40000540305c000d072109000f85500030001c0c0c20070000d039806842c0002d1031617410b4200501401c2c1628130300014107000b079021070058131010b044140d0355130300d4140c0745c0c0341400c051418500a114000028010941390301ca1802902c900401428a03c000d400c86c20010760006801440c500c0540f81204d1001c0c801c3d40b0035840102103560b0704060580c55810025400592141c44038001d812100c0813642e81d0b5400318002801c0c100302601301061002c1c0043c1e0511b403a40c038640c000c000526087c0049078840d800800b651140650b50500d09200d51161002c584030700400000901590048460000650040d80703410500b003010f10481c0d12050301000000d00d40200c0b60712 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 859885980 1250 859884730 859884791
    0x1906150e10020f0c060703030f0c020c030705180f06150c100516140d0b030703060209190b0d1d1b090907060903080d09020d0501050a2a12 61
    0x42000c280e0400c5001c00c0c5002032140050055408180321580d151550610b02921900300000c00c1020075010354001200c3e1210040100000c0b02800da02a41da18003243c6030314402e11400c40c1c001402d04e1301c070145099032040300c90400210b866044001030700715809490640c1c04442c06a41c0c9800201d068068881203281000a100b64481c40f07201c0012540c020340750040e5041020031000f811500103051218950b4180e008541d82d080c1c0d4690304003f08034072528198140038142d00081031007180d4018126001049507550405a184411459601e11610034a10080c0003480002240550341e80125400058040d1002d0340e1041c284070b183c00e28000714110141d4038215180902182006a920341c2d1060040d4010f1801c2400c044000e000741d8403503c001070101a00040310f000c3c1d1100c0ba0800c0b5202c41d0301910408486001c2c0c5000760280c0812510407070900d190100e402d038001807080000481450001c040f20012501040441d040e5064819608041d0303111401c6002d820032180072926020450407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 859887230 1250 859885980 859885997
    0xd020c2b0809011202180906010504120b061002030406080a09020607021008041b05011b020f090f070f210207060605130e06090c090112110a03060c110a0506190615 72
    0x40002d0103410103040009944c03441801400250f100701c004004941004076150301482ea00c1000480b180d2285402030080808911401810040410710490160000315030664000d0442101203a490141d07104980014201e00302040d04c1407640e600c80c1c1262400070b4141450950142c000c03030b80c079240101d00000002c4c5c64000300710a111101e8400d80d00c10307228001c41070106203040b00092410210b40b482541d07175604240d02c5c0c0f08540d01d0086d01e0f0030401001d400a200d515200f108d103c40ca030f030115158404a0342c21421441c07040e10880d601c44030708000803550031011101d102c0360720003500846012668107507103144c041001d0342c0f81502000d001e82c0006000c260098040f190a080c000c0280c184505030744031094180d015500c0548450550745c03152840001c000107070a0010340503c07850909500301c0329442c0701005000c0a500050b0305010183c9074000b075011500300f5160368845124000d00940c00c03e030003155201c81c440c0080b82c0798614003100407503000d4581000d0100c003544140200017040000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 859888480 1250 859887230 859887247
    0x909070b0f07060f0605010203040614040905010b0304022103030a0e010e07090605100e0a0504020901050706021207270b0a0c021f020c0a180c120510170d020c2b08 72
    0x28000c1e81c014110040041c000071b4034240c0080e690b40200d0040b001403024108520507403480b19804c3d60300815040340180400d595480c242121a0b2064600380d0146250159403446001a1502d07080044140e0300110710b15136440a0440c01056065a10300c9295280d50919440d032000300410409444074880014029180108000c101d8010319448010310001c1000c42d0920355640c1841c0084038004d441c00750303445d400480121058460b142e40182400d10101e10b0300e80c810400152544261103540f15111040700001031841000704290250b02800322503c42404003a001c807002d4100d40d0030b54201400300340d0041c3c0c0090416100701c0c0c14a10240020003412015550401c0500c030081000d40314141000d0518810901c49954501c0802c012a00d40540c08e000ca885060081501c0e515034108001703170f050481c4461400d0300309124036903014080303a0664108060120b0481c1070884503400414440030054241301c1c046414400c500801c00d00340548046000800b0001c03070300716104d02d41440d5100c45c032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 859889730 1250 859888480 859888493
    0xa09032406060e0904060c02010908070c0e0c032403070510080f0106090317030c1308010c020c030102160201030b03030f041d40120302040303170709050909070b0f07 73
    0x6503444002082018440f406180e11007009040d00181c1044020405030000c060990242100303010082031040d000030300005110311002e1500955003040b01c007140d40d84508688042034001a20718034060342c0c1c010070302c0e000c40d4010403203607440341d10140507540c0c041d03610340001e1302e5203448010142c007080480c01000b100329101400741c3e007d81600c0c2800600542540c4440c03000c40501c0203034189054000011400e249107a0003503e200c0d62400c540342180b26101c01c0a28081d008103018400948a84144010b06243c10700941c0c06107542e000e0544558503a6400440240c00d200c90380075090700080110401c0460307034400900c050704410340740304c1c132072030428096803a00080202405c480d0100307480d40c0780340c4007001014440110403105000c52034401001c1c00480c26194401d00400c544c01000c498041d854042d00544100c84c082c2d1504048480311070f040a011202c1241c8083c001908030205205928254a20a4004140104585000d9242d0f4134111640d03100361240500d18401144840c10080c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 859890980 1250 859889730 859889741
    0x307050d09021302180310060f0b0f360a360510030c08070303020304330f02010c08060a050904170c0a0b0106020a051c0e0a0f090b0307080607050a090324 68
    0x116040c08003d50b274581113200c2140074841c0510983c260300007448003019907801c01580c20340080360f0542c252030040851402d80141d680300f0541d0bc0103280f011003616a1902c0c0142208491020001e414912100000e41c84c070080098400c288c0051015543c501788001e0740b00d498862400485103592160460a01c07140300c41159100d10010b6100b02d10900009030701005450894005d14555211b980c1c0c40c1d82a00b42da0000c0c0213064440407541944d08041a0b440682c201150314150020030181450140c00c0b0f0f0000b8040b1400790300214000d604106504104250350782c0607000d8035030210000b200000d010350b20b90000c82009416481000544103022003c3c068500402180c002440d41e120260f8429848108403009900500c2c030440039800d0440c01800d071140c84140c01012000c545840ea00d2200201340b85003d200d801910b8210850720740d003800901ea00545001d000208170710358130200c040f0354551100c079140b810030100c40f038000001562113004440e061420b02d0b0141c407461881112804030f64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 859892086 1106 859890980 859891003
    0xc0c120a0b040c0b130e100620031303080306030606100f0311040b1c1508060406240612051f0e041a010608070f03020307050d090213021803 62
    0x1859500c40d4001d031046c1c005404010f40715400d284000d42054040c40b40483c869242d040000e40344401250741d1a03026004880c5002c00740b851404150b03c842d0b1048401c130300c011003071001618041c01056030025007500c466904002805000701090207400f584018103130350340e070b558507032200100444000d403441d490070b5944d0b6096050500425209222481d80403460304500541c038400701e0291404480707846000340555104ca0300c4110040003030000d00000310300c464103025040c2b10196a50002489030b51120700c882c000c403013009000e03124000d11100e603404007d41ca0349060644400c000042d200000c1e4280415900d61a0031001404001c072120040c05110000044541e0b01c0000b0b00d209006555604010300c54140b4194281d000c182c440d034011540501200030b143c3c0f4190300c6403540705d00040c60080007004809450040ba413000700f0325030005450b00000015400d08001c0d002003075 = true := by decide +kernel

theorem cover : BRFrame.Cov 859712230 859892086 := by
  have h0 := BRFrame.cov_init 859712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 859712230 ≤ n) (h2 : n < 859892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
