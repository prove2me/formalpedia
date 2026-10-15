-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:28.187757+00:00
-- url     : https://prove2.me/submissions/d28ff284-456a-400f-b86b-fcba6c9310ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 799640287 ≤ n < 799820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 799641537 1250 799640287 799640293
    0x5011106010803030606031302030105070c0201030507090b031902090a0306060524092b0605071b0c09240b0d0506040b030c12100f02030601110f0d0804021c03020c1002 74
    0x10031071810b001c400c0d00c0e04910100c2c1c0031a0750340c403448508079074046800c002a51652070502802003480c0c0107020030b00414400e8a06015a546250040d50781e01c0c10742c41034450500b81000040e103c40b0200030f8101e444041654018244804c1c400410f4254814ad04216a55503a5100170b000f145000043c50700c524860001284411400361014446801030100850007040f44644107048240c801c008048100d101c03850301ca0780c480d05401d008019100990780d54000c1030208041c040c032244800360412005412415000c0b50502d0301c00214018204901c0e44a0351010090740306031031a81070f00d44c083c02801c0710302c811074844517240044000c071360014020a1055180003c82022624081114140410126018040041190011400c1150003003070710055905c0c04040b22002c07410f0707502035030203400203984400310000f801000381c1d640c0d00d0301c000202c042e07030200b500320b00510300ca454101e611070700c040e10032840c4c42600c400c0000c0f0107500e40f07000c0700980c0106404001c1810180c8070030004440600c02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 799642787 1250 799641537 799641539
    0xe1012110c12031620011b0905030106081905070b0403141506010e040903030b040c050705011a030a110402090a0e0703050c040f180b10022401150518030102040f0501110601 76
    0x500901341c40f1682c0300c03803c1c440c41c4c40c1e51580c1e0600d03c0e11100c0500b0818802400f981103900307604e2995070411082d803800300e0041312010a090034144a01400c1d10b07042c6004100d0605036a955604001400c4c600302c603a80304140001c6079000450b0050401540704040207a01101122980e50828602e03000c5038480780d5051042102c1d45e07a010b200b0040d020800d4400007100b01b00f509044001e08948007503940c129040c80c001c02d09140e401002032040500400c000c00032800000142002d1582d141c0086925900c80303200c000104441c07910110301204001c0c00145001e0941c40814101000341d4130071440b400c0c030321040103109a00360003040e6001902c51845403030541488082c03c403038507050082c00c4c6288000c002001010380d4682c40b005c00020300401c240c1a8400026000b0368aa40e400316491500f2a00124581d41c28099108203059900962082c032030070486410481e200e42028803070039246405550700504039102840200302a200c9030404d0f454003424100050822080200f47c82d01c07a0380300c840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 799644037 1250 799642787 799642801
    0x3020906041d011802190e01021c0c050715050910030b030607050a02010b0901150c110603090f15070813020d0b010b090114040503071203121104090b030604030e1012110c1203 77
    0x146c2c943d00782028140110305e20544030040b49800104015034166440109134207007070320f400c002180ea8441c482c00407036060b5500c9150b2100704048a2181c0c0e4003054013400382c0b030518941200c0c0141d03c01c1151800003000310000c0c00003450640c0075a03015001c0307440010355018866081c000e0a0000c10203a4284074154507000c04054a20394500d001c80410204125503030810500300c00d01d200740c030320007010140c481c149030296988540c0340c000503500910030944890003454920981c02e05c210003584581c0400c0d84c0e0203041ea2215405940c0482e442800200e03e40d000440305c00c4454003805c044004103440781d0a103030015104040700441c08500d080d080c842080b095a0015440055445956480314854214038041d500705201c0c503001c54546042c010b2044198071280b028004680c44248144960042c0d03200b49600d81c80296009000100769a03001e0355a81800f00c074492000395140352544810040860300701c100c1d012501d00c0c102c95100051030a9000004210324000d01e48580382c0c25141d428a08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 799645287 1250 799644037 799644067
    0x5121213020a060f031104030515100e0a150302030a0b06211e0717030702010e0d08030426070501050103260a18050d0b06090f07020d03020906041d011802 68
    0x80f040702d0400243d5035604c25034921079000303002c1001040528903191605c9191607a11410390240310444141604002407900074070058030303000c60b040d50f03010507020f88418443c0d2026102c400c8600524a030426070000050b2800c1002c451080d00448460b00740c1e08000080102c1d0004601000303d03106072106900701e130000f0218001002c40002040c5902d180c0c00c66858500304240c941c070043e85400e589880ea0366a01c8040010825580700741d03291560760300c00c001000002048100050403942c01840054001803900b900420f0361208400724115581c0000d0002030154031081c011102079450b08010002c00c0a607500e03000454500c50f07030f6018a01101c0700c6056045c06111074417010000505901040342c40c1c0081100301610b030182451120344440d017071510307207010280e45060003030b042d42000030340001401450a004030025406842114406841103000c3d4110041882d4401c00800c000103407000300c8481c0c2280a006920041c200390b00d05440050400700a000a0011074010014000c440f07400c1c07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 799646537 1250 799645287 799645289
    0x417090f010c0606350115060e0f0a15030f0e0a03140c0601242a1103010609090203060a020a0905130e010507051e090d030c050a05121213020a 63
    0xe00e400400400d0a050660280c201c0342d05c05a05a04800c280c034900c0155400c43d4213617070801028051010b141c1140d0142295031540712050701d40106074082c440f15115410004140900505402c200466003000517281c42e282c0d448910081280c002d8070021a8041c02000c000c18a00941082004e80c11b80040c2c1e250703000c8030001001c200c15070a2014030000d01e10300b643c41143c0948103c035001d44c3c6540352440c0a58038480b000412001511140315510b00c02c04005048184031010080c1d480803003c54800b0301ea040800850309210903190045c116103092003128003c2005920100e00b0007041c3c014541403480c09403aa00002c2c0c01008960701d0340385c00141c10412a1402d40d144640d00e085034641400034a00c401040149500f00f1090010341a80200502003a031080c20183c10410650b1460044e24450380c1040390f085000d0110b6980800d004d010701e810302c1401503064840f20443e5944040c140355201c0382e20040c4c04000b084924601c86600503042c1d00c0021120101141412a000614a0115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 799647787 1250 799646537 799646539
    0x30615051303020904080403050109050d17100608090712050c09070c050a0b06040207060c02060702070807060905060c030708040e1b071a0a0e1203040212070501080106030903050405180417090f 85
    0x1321401107010403404600312401190400001c002008141c5456074480e84102d404000081c3c006a020106596002049008041000907000f58600e00501600e0b40c000040808449000d01c01000074503591001a00d900030340324402610310907030000100003501c0740113401581004080300310300d0001140040d05408403900311440100680d68030700018042d108103480101790741d081016011407541c00103102c3c1e0261020b0303003d40b00081d8844016680e40d0600f84203100004442c0103042043c0d00701800204181010f40701500d241240e02d4aa85020354410352009030900626410002c1c4d0f08021a04001c4001c480f03048603180c42d49980350003038071400d60001030300c54a030400300ac28005116680000c050344010415603014000c10225088560001c48050307018070401552030398052004520382d010707107005865541d49a42003076821801044002411014408100f20200301da80d5a50400d1007802d441d054085404c0c0f620385468400038402c0d40c08808400010701584140343d6841e0582401d244c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 799649037 1250 799647787 799647799
    0xc0e0415091b030b0910020f040504051003050d050408070f03200d0c0902040e09010903090612200301090b10050d0b030709020406020604030f0f14181003061505130302 74
    0x18481c00c0604070074400401000d94500651800010000072a01a600c81d101980035074040d0340441c6c000d04107902c106481d80c2400042044144605e140a80c032050300803400e2408030b08901c0d12503446c0ea18200c20042d0b04004900041820080100d042041001400000219072a5180795544603800d030800d04040000e0b13410407524506180e1145c020501c08a42c000c41d030b00556683e02c14400d0021350082c014031214920150020384040b805005102d2100d500d55140c40741d442c41c0010454900320b16001d07481c10140c6a091340a92100f1640304121050b09034030712140e403540341c10007050485100c0018203008010034081804c07141d4100050b642d0400381030740702140b1101c1400c0043c0c2012800c0d00714030899407002c540450210f9001809a00c0b452190f2102000c55014034025140004003070820301c0003506131880c0050542210b0003400201d01410030503000c1502c94000203010030907d41200780080e070307501c400700700303000c1040f40507150001607050003440c1401e0350440b0a4a09018040640904 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 799650287 1250 799649037 799649051
    0x30403080a050d0c0819020403050705090415091209080f0c120a02040501031101080606121909140f0d110a060209030309101110020306030c040515030708010204030c0e0415 76
    0x140c01182242c246401240d410040844e8204000e00019419221229030414079002031641c100729108840580303400034003c1444134542020008034100040044412000d2a884002c0003081402441c0c04a032184c00b0110f070000117400010540026540560741c03580c402e0040d2100c1400114030a1f84442083d07076000141c40d4240e00c014505444080001c1d003141c41c11000205000c80c40c1103001d4410000da98010b8240c42c1d404c2000310314001d1510742e4803102ca0107004102000303409854488104402d04000c100390801e522a400914044800100c468100710500ca44201c01886286034002050800304412003260700c107142d40b90318a01000300003d070b00180410340c6940800c250341c110700004102c188001c5046400030135402807a24541d51501c00c20300900d2411845000380c9101c2c0b01d01800070040180700d50308000107040041d02c00a0013503020f5100034041c1c0c40520400015109120001d40d0740d03461482c01260546036070303000f041e0000e6070105200c0003410300c0c242e8907554155400081210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 799651537 1250 799650287 799650307
    0xe0904023007140103060302090a0c0c060e030a11030406020a02060912030c10060518040816020405010b1b060f1305070519140d02010e040c090b12040b150303040308 73
    0x1800c0100c5260100009525a15245400000b440ca0580c0c04542d01c40c01c0b1080721100640642d0900d0000039070100c0c0c401e0020344078090a622451411509160a5070210100d0300c840080711800c07000a0916000010b0b02000550444810111080000010f500d0035203000740c000d40341d00d948e2100070701c101400103510243c1e55401080365606022802501c1e41c41e0700220460740e851700c2c14070080071150300f070043c0000c5d00e10348694259080d0281000c29400756907a503840d001a5480035807219030f42d0900c610700d40050b071201d120302d5003e0803203c200c07160769500110203410891041c0001c0f03800d84d4801400c0100f80c00d1150380f2540c00a60020414420285625000742881000c0d0001608801c2103004801010480e0544000b00c031714443c030000c0d062042c1001d0104204d080d000c00b0780072400c1940c405560341019400384071001010300d482003405884400168407540501d20158a24211400f8030090040006003147c11074034240c5000190100740c00420345900691001618101004c1944c1c116 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 799652787 1250 799651537 799651579
    0x3030412080909010f0312081e07020a1a06192d03120203120a1b0e0d05191202060919060603020603070c0605070e03071403030f0706060302030d0e090402 68
    0x1000c0307000304158869038417130026218180b014401582c6200700c010741c981020780540c2140c0d01031400103400002858903944010025070006c2c1111017140f041d076403502c1c00304540350140c410048800d20000c0203410101d0400c10700305141012064641d5426104008051074915806184d1481d595031520600111b44000301a61b05139001801c806091160400c4041d4080010700300d5065080c0e00714080c4e1502d1002400f03c542001000c086114003c00d82c50009006401c1c1c104605401030100041c1d07105d60ba5510b04119000d05030700d000c0383d1946040000c1050124029501c1c030001c0c030060500f441d14032211b6a455140d100b9581400104008803010f000a5400c00c2e0095500580380642d070303040c54a8010050315408c4016180203240102040300b8520841200d01e48440080081041c2400c0c95031180c8858000303005154144803c0010f01144134001014142d400d02506001030901d00e9030041c035040007051043e00b000c01c030003407814130b210343d444991035a00240c040e252645252001303194854 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 799654037 1250 799652787 799652797
    0x110315040213030501050a0507050c1905030d06170f0d170a0f14090c031b0111010b0306010b040f06031404060c020c130923030f0a0207030804060e01030b0f0303041208 74
    0x421a041182c01200384030b0705402140c01201ca0b010204500d60310500300300d509000302e01d5100c0c016044404901c0003ca00089550390150060f07054030301d0171005048142c21151303244d020400021401c0004280720030140500d8800c2d20051001c0c005201035038100424030060450343e0244c2d25071030800301d040507181c0d40c0301c4001c1d144200c03000c114882c49100c80090800701122610f103207100300e01d1000700c2ca007008102d40c0c0d43d074600c2d10803c0301e1140501c0019560702000d150341e409a076684485c26000c0f550200401b80c000c0c6690080c0030b60f03a07404c003e90a0550010354011405060921004044104200c0c070410b52058002500080f1b02032648002c07814509003286c0c1c0d5500014508403c01200c4a542c06400058440c0c0450410b990300c40940c11468400401205801d40050010510510b41070000700002d08451060365040c58613640e03040190f4000360010000910101e034645200d58151062541004d000c8910104035184100060360302d11a500507210101c42c41031030300d030420800d0401c1c0c2e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 799655287 1250 799654037 799654057
    0x705070b0408090906030a05071a0c071d07030b01022107020d08131d16170103030206070306081b15090d05010b0a060c0b010e1312170108011103150402 67
    0x12000e42840e0400a182d9081070011600c0350800304081056440c0000360210960b0b4004050b002c41e03440e00c00ca01600c015001c5c6d0f003e81c3d601c82000141c0d6645010700181d0068805c01900250a04815081e031002c00f0300141440c040c1440c18061240a80e0001480c0500d1f070300102c034002c9400792010104000e030203282d90080d088000030300c2010030000c140d0040c042c0c2802418210240c143e0350070710130790b81850300005a001d10f8000300c041000c5242c0c0741e150102410040c02d00c81c910f0500540428001502640b0a40058110405000311142d150080e0001409190020044c221880714203072600300c4441e0618ac46101092800f0380c8a07076403041900d00340c0000402c031050300411810300c14068141c9928143c81340ea0784240c042100b80c02903055003202c40d040014855160b09007802000c40f004003504107040c0c0880c064992000605141000c1c10040039543c03066080000030b090041c1c2c884060300061042d03410030301c481401d107000c41c041ea50b20070391510310b40380c0c031600d00390100c4c0003841405008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 799656537 1250 799655287 799655303
    0x130121202030a05160c0804030206031e0c0c1605181b160b06150d0207111c030311161713030f1a1603050a270c120803010b03070507 59
    0x43c10005940c0110304c203003030700324520700360a100392422143c0b04e0390721000500c2c1c0701d0140001c1c00581840c00107164801c2104400401c00c40c5210140b07410840e045664034ac0d01e11001505001d40318080c0840245880040001c84407542003800055101101c030011540385801d18000660586481c0212800030300c0040300b2035592251103800034124904150305440b07544000340400c4150400c1c80d504001000c1a030103140c00d1619210040000c0d5100440a135040035010603050580e55403260301c95408842c2030707000080d2100514000e82034800701d00008034402c0088c0400c008080890010901c40340d8446500d108150380c0148005a5000d49158030341c10001c04000481007102e0a0030100b9254041c0814840c100103003100054042000c44414181c01d0300c550340942038900941101d80c000d00c0640011441440b40d0244260158030079400b01070580f04401084284040608040040d04050907070310078000c016105d04405100c18400c408400e40004005452684520705807001c060f03216400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 799657787 1250 799656537 799656541
    0xc1e0c060906070f120c05011a0f120f0303010e010312030b091512030d0603050f01050601090302040b060904050f01140402070b071b0c03080a0f1b031202090303030f013012120203 79
    0xd007406e0708100115081e61816030b4048a00030f110550480380c203c010401c0d03104440c1d101c1032021001354031820a031188a06110302d051001c0034070145001c1d09084510300a0747d03140d8144450185199a4660245840c02c824542d003500c0308100d2961080b48000003644c00c1c00c4a074045100788140b074441aa03a40400303d18181340352840e800030407c9901032403c0f5055010303036200480c22900107881c41030108000c80010001820b1603081003210f031000400d881e090030054004a0180e070030407510b0f265407456450051000324120402e0603074122080e6011410888075030349520755294050046010b00583d07c510413000404054008036071036003c118211a03680d80d10300342000d030300060007481c042040901c03202035492203035890700c80001c007007110070038500e909490a954000043c00d00200312a002c000c840c03805d4802300700442c001c041c0c894a40034603600d05081544042068003a10303208284117407020384940e1842c0705052800390000c503c125070107040b000640c1c90002c1600380003c12400481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 799659037 1250 799657787 799657823
    0x30708070b07181512020409090c0303110c0d08131203020312010510020a110307080706210e031c0b04050411181b03040f02060c1e0c060906070f 64
    0x3081c1409801ca80e02d94040c50015102c0030004402240a80480359210084002c042c40c03091050550440e80707080018541600c61780300d60b042d904900415184400c80e05010070400d40d10843d506151060507000e0060707a05010006105d40b0000c4d2005010380a000c1480383d8030f15503a001b00001007000b21001446100c0500c0d000c1e40340d810111074004091018400080e01f03003000b41013012075014070b13405804141c44076500c51143d591030840e1907415200308400810f06040400104015040d2038a455000b500da22612503a80100401c180d0b81017810b11040c0102201c00005a800c420301c2040c01940f5a411110030200602e020080740c0c1c0d0060502c005e0006002c4955214140f4510984102c5199641d1080701a10440d0541c1c80c0000341d1905030010a0f008007400c081d41d0014071401c1d01d0450082071f90009103403134129003003c041c242c0103041c0c08446500b58003210b5041c103810401a02c0000b6400001800c10301943c62a140561700001d0500c0070001c08020740c100301a80b00109841002c4404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 799660287 1250 799659037 799659053
    0xf040b0c070e010609090c08061f0309080301090e011107020a063c02010b12060115020c030102040603020306131505010804140a0b1909051903091d070e01030b0901140303070807 78
    0x6c828038219a1602c4030100c1290320403070f40c2600c80ca5000d00959219010102ea04202c4030f0f80d00200d00070140c2d40c3c070709500090301007002107008050344800411502246900325003182d400d00000e1495001c2003103c50010389590740c4100c210340542c1090039100c4011110f401020030408071a1646140762030704038060301481c000b10085107449038001c011b5085070b4003d10000ba41c845240f2009680402c004100c01004420161000f403610b1041d200013220b01c201003400c0e80c0054201e200401d8000c400c02c110341c203104410740c141155076002485050a141c407040a01012030044a04200241d0b00050a0000101795050346540400841d80f4400079402e001c000c0d41c0e800d6601560710065141e003200f941c800c1d03010b455a0980c11001030034000641c482141d111030070b90581141440b070001c1e40000c06c0041c44a0000316040500d040038600e1400703060040031803268842840c10b0618041d0101d10a49030001d210f03054a4954038400c40c42190000001c1c6580030724000241110000520742040101503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 799661537 1250 799660287 799660289
    0x17060918030d15081b150d1d010513031d040b1314070e06030105240c060415091e02010203040803130e06030f100b011b05031e0f040b0c070e010609 65
    0x1980506921307102ca0310103460b814280910111814841c22610392803a10644030014000c0000f40c8030b19244030300b1050002d680f2030300c10401ca001d0580c150391041840a0040316070108082982c116140d400d03560103482c0e138240098221994602070003c034066200d69111100c8100c005040b8010081c0a07500e05002e4458000c0d21192042200081001e03107025107651500c440c8028a001c0c1580c0c2041c2c00d00c90408240118003c0b480f800c5180e04a07450500b10051103205101c07000f0702218640350808120a0a001e04115446031501d1010130100e01e60880e507190380c01150038807a402c100b036800102e146000360381000080f80000661100c5040e00d01d18860100e40000c1038281559451302e04140e20303a10380303000d025215080482c00801440380744d4480360400b0414100210011469184201604c001420458640d400003a07040c1e4a034604500605031b00e503190402070320f4543c1140c4840800d0003a8450244541c2000ca00c07180c0f15030060081101070045041c41849640e95401c0007005640d031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 799662787 1250 799661537 799661561
    0x40509151f0b18010305010f060c020303090d0b0108210405041d121b0a0b1303050f0d020409050a0614010c0c0306020309160b090603070e04090506190c17060918030d 73
    0x1042a0f03442c0c3c994001e0080e60304079111003c0c0001c0e03070303440d0140c10b0f00c00c40c0038210105d9050204224400041c6da03010702d03d80c0c00d1030080e41c28640c02d40c1030840052502602406400c1c84861901c00180c0414900d0101c500f550700c207645c0485c00011481032450040c000c0e01e40c040e5580a1040c4a4820070f8019000d81229809400300f0220081501401900d60113250b1000d003424907403c0c000359440719240e03202c00e1514842d02c3d0079407030503400d4921b030403454200f040303101c2c0d840f9000542040400794a010b040e400c4010003000b001720b5441d02180602032041c585519040c0000150b82c1c2c0c0a21203000e02340710055400c8003040d5603a140500c85161a140798110f9120207000c5c051021544019400c01d4540d45072000e802c452841d181c142040e200c0c1c501807150183d000e5142d20203800040c4085c0102406903c005808100500034940b02d20107a030b0002404c1c03010005044d8a0203079441e44101c4090304258241d6480c4070301e448a4003001c09502100503001c0e40751000050300601806998424001920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 799664037 1250 799662787 799662817
    0xb0a200727290103141015050c03040801061d09070e07050721020d08070f20030c01060303030518211e0d0609050f04140304080d050903010b040509151f0b 68
    0x2c5e1500260700307103d03025112001d107040c900409119155106c43d00034103501c06c40c18958184180c14216600d55130158000e0138680c6d441d203000b08640c402c400750146240e21810a641040d2400040007503840c0c0355442010200c203c40c802041506015100b258111600310f94903440065440c11a80d1201d911031244000500c00c00f0008102580b144958501030800c0d40c3c1c52983c55103a01904035881305041161011544960b1401002103d082004203c240708510010a0b10791030360801404542c00281a11040000d491000045400c085003500101c25081386041105803007041c408024015140c0d0318400b10510304101c2c500b007140d80b02825641081031424003443c0c3c0c0310040c060540d581945d900c4810a00100030400186003071034402454070b260700440382815035031114a840d189680441d00045600010500d840d41000c0c082c900b20780106840500684c00c110b6209503507000c4080c04052a40d201a002c6051010b15a500f034418428188101d510103850b155030060b654041692404254 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 799665287 1250 799664037 799664051
    0x18090614120c0102101e020408100f0c050d0f110c03120726071403010902040603061a03060d050c06040e160207030c0513060b0a200727290103 63
    0x142c403004425040c2c1c0a010000d11002190000d0040680c04803094071004080c3c0c800780c40b03544090002050040d00034407040001908002c1158011121030600504004524080d182c1100444184843d60840014020701805001c002080d2060150950007000280c0ca84115400000392290441000140386140c0300e401080e60a01110442099113410340d88801c044464984d140315800002400c0921030501100c40c43c0e01194402d801603600c0d0751b40410148900f6034144204009465801c6918071402405008d16820740001090305108004055102d42040340c00d12100d401010007802c42501c46841e40010280c00701f040300c00e40708000e9012042c41c0c0c6d1901c00110503088075005400302001034203107024409040c0902c0c0d540c0b03085645070540001c2a100740c00041c0800b20007075841d20382050594207404d800340c0f501c0400740380c3d56100320001c1c03000702c2d44040e03525180e0050501070501040c6401e44c45001d4818441d1041a044103a4600400744083c0c0c90b00038030004090360100810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 799666537 1250 799665287 799665319
    0xa120215040c03060903020f0f010c11010e060f100b03040c230f040e0a0c0312080106090b0d020d0609090605040b06040207170c010b03030703051e04120318090614 72
    0x18604940240541e20b0161080021402c180d03c0559504e02a206450190707203000000c1d0300e85102e610b2442240e81d07444411061840e40a40480d84a1030808020300169403c1454a9926007000e00084055000000400c14080c1410724110041c11044034103074491070181010b890b00d0005114500d02c504030040035100842c0429600100d803000144400d841d80454000d1200504800c04c180b0603d114481084001c500750854502c011072040e03001c00414004508014140007040c0e11090030300004080901c40e29501400b5100f82600021005880e03c05604200c40a000644d100b015202c2c40c0c06010000d0048079040588110b000740f4110900b9207461007070004030321400802500840501c201c0c218400034000c010f00d5031901c404000301d103031520703100040e0841c1e002c2c090803404076600040c2d21010a45160344050800311000023036041a18129940f0b0010312442c50080400019040003080071114a001c0070280c104490100406034032210007011080d41c1c42049481b07a43c0c46280c800320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 799667787 1250 799666537 799666573
    0xa0506120a060f020c01060b0d0f150b0304020102011d1c050a0c08090303120708072a0f06240509060a050d0803070309050d0807080f040206190903050a1202 69
    0x60164803002400d041941da00d0300c0c0010000030030030942041c0c08001c10071440000b40030381c2025181040c01a50b44414540d050f03c00c60307060401c02c844007030030003c0140d091144003048800300d039560031017282d403a80e992004030300506c0030340c401040302c0c0c03480201b05a240900145145015402c0300301d5510903034800c80306550301d00482c0002d82c0010140100d070030005588002030300c641603011f4222800c1c0303c0c25409064030700e00c088910800117200001040041c687c040715030007901040c84e0b001c2003440411311561400d50325024010300705030450844641001816070049199a200708030021400040c3c41d94054000054403a092007101c0b44008901903203007403d154000c0340ca00a004030980d07259590f03051030603000101250b003890b40c0c032043c07034011603410701454400004540d25010302c1d18080c4000341c01c8403405000001c111828500300001610f4a8040f64000d1f0066a81c204441c4c0880300d0840301c28403c2d800042041c001c10700781804011140344045008045034098540c00320102c078141c16 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 799669037 1250 799667787 799667809
    0x90a02190e120609071707120602130e0c04030b070c0c0e1017061810050c0409060801051e1003020303040b04030c060507110f012a030f0c051b030f12030a0506 70
    0x4600c1d0460001007022501b5244000d8403c1104000d448000f503851814012400d554507040c1c80303486d00007818030040f02c1e40018940c06849408a01000c9041104000c070540c043d03404020450301c02c01012070402400356811002c15039000d014961403544448815501c2c6205841400c1c490800310004101c0b0000c0b410080c8420004000902c202c0e43c800c0d41c910340300030011401d5410303801085602e522000c05802118480c4203110401980c562800300080200d4450364410005a49040d0a2100c40c1a60882e20a0000380403182003000b0b8a809101810301900c50744000c0d032500c00020b0001d451450b00014000b16405a102c1401380c80c0e982000380c0b40c0c0e2003100c0008084420201440265181000c01040c8911f8113141808a022004020882050502c9050400d010600c0045400c041e4400b803415403910f101d240007480140d06a48407503403803100015519030482405528a06031318208540166000300000b2502c204000403501d010551040e82c040500c070341840e0004909041c00b1030004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 799670287 1250 799669037 799669051
    0x621070c0b0606070308150a1508090d0305040f02041d0703060504020301050601181a12130b01292104080310060207030c060e040b06040602011a0d02030a02090a02190e1206 76
    0x61050384d1100410520490048a1f030396001501000204001c0002a025100601d039515a0f402c5414880e500c2843e1414400400c1c0815041808010001b810308440702c909642c10b482c04a244c01000101c3d020711016070135151078610980900005200d030580019000c2c07030080d0000c000075100c1c400111444914490300303003c40e401501c810000f0801c0c480c80c00c4d080f55030f054086070411402c641e5150742070005403640d00140003040c5403074081c04080d00d0071b58010240c11940800034100321110801401d1400303002074030b42038003080d03200340321401e2010811100b503500390003a1240340c40d01c1d0840d56030700195900040c1844035100441d80d80c2c000140c00041d01d40200c109512a4900b40d012240503002040c401c2d00b140d16960311002d50703110030b030180014060b241c002160191f0ba0002c81c869030031100482900c6980e00c4490709001da01d000c201d6130102c0740c0541320744a10381d03550380c006000780c070400c441003130100000c00521148a0b44480c00701142501111910081100500d03400e0743c42d00155044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 799671537 1250 799670287 799670297
    0xb250501110a17070503060919180203010c030b151b01060f08060c04051509012718180f0f0b1005040605040e100e0c03030301150e1e0621070c0b06060703 68
    0x400d07ca0b15090201c0d503849581c07181c607085005000609902a00c240c00252505000c095001c441146001c0c058030f144501e04d4601004071604000006400b400c0365089c0d54030f0010006403032405181100c400c0c551070b01e03240000784105a03a84420b07110084035446504042d0042001150700d40b440e2074102d50840320010183c0352051420b4000b1045640805c09103410311240101d448948501c40400000d50000c1e1004241c02c107103003140c401e00700f0302c440d2403503c80359141c140c000000000e4114000c0105800c03100f045510140c038646000383c140c10f01d5010b8020340c0c1207030400504041c01c00100060766400d9509109040e61181400155200e0081c000071f01d400100030b01ca05044164060200340318a641143d080401c0c010100b41541d20a8002c40241807442d03120300856500045170386100311054038040080c02c0021a540310160020785454402c803000940f546d40050b844000c1840070310701062214003420310880180c210f0043c83c1d001c40e810580382c00001c0030751a22505a424954064a074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 799672787 1250 799671537 799671541
    0x301120204111b010b120703050a08030406060b0309010b0103060f062c1206090d142b02040e060108071103070303091a010e10050a0b250501110a17070503 68
    0x1c20024000c02000c100c01c603403060100d1039042400c55001c030441901c110002030300f60f11000034031080602d4003205200c240e202c50000c00010701c2c00034100102ca5049202c240d00d903191440d1004c050859543710380c0c40d4210100074089120019444190408401d80303040000956660841d02442441d110380c0021405003e140f800d04290031020840c12806000020707082900d02d4002048038200d240d42400d2075010704104094904200308503031301700b4100d06141101c1210011148800c0c4200d50010319200040794610321801c0b4a0031040340d070f0501403001592100d886021206090400320b48082c006540e11010a81c0381e0b0080b00d00125401540d4040e51900940d42c40c1940500400c2c1c0313044410000070520f00040c09a20501d0a001c4c00d6034035848003560400f145c82c0180d48500e40c00c51480f5024040003040510303409000c803080e0300041404104808002c0e40c000c102c00004c10400b42103542021900045007011742c0050445201c0d589070b940044047c0f0700501c82c0c07070f40c080300c040c4045042000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 799674037 1250 799672787 799672789
    0x8010c080f06061b010501260106030803070f0908070905090c0d03050a032d06030b07050a020a03031802040c0909150f05042c0a1103010c080414120c07081203011202 73
    0x30071000c80702c0d030f0384005501c4d0011449802c60700242d110b030a085006404514100c41000c41a003a00f0307805034000c0c00b16505580790350059101c050114024891717201200c2c07600314001c0000c40020054071064411086e0341b0050302001e040e04a40c00401e5020750704806100340b42c4821000410381e015650241004c44980060b07000700010920482c0ca115098130941c00c140601000541c03007003403c5800f04001e461880e01c51021903000c0c20000502c0801d000c0703055159030004042c0001c135098640440c0300107414882484450310b90030702039005400c0034800241203400142003c211014214100700f40300c454400c4080c5411240120806180f6060b020012480c06400004d07003a54000a845903603000705110034445481110f00c580f1315044503541506115400e580d41c907152400390028030060101e140000c0a04400500007440021500c0245034440c00811040120b02043c20b1030b0769840e510120342c1c6030340d0748072841b6449544c4241050050100b441000b560304a6007044540b60000600ba4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 799675287 1250 799674037 799674049
    0x61502100f020408030c07060e0102061915090c02010b09091f0b04022502030105010b0327030f0c01052a0f07020f0406090f0501080d05040605030a0b04110408010c080f06 75
    0x60110007980a01020501180510040002c03a90440080c07441e2031030f0040c06004413104e881d0036070654200800708409581c1b036090506c00300c0c180c8503000030303c41c40c100041171b00c52801ea0403d0069510341031400140075015407040d280a4400c541c0503025030b0320840d03e00e0f5103400c51560240292401c8294040440054001200c0c0c0303280104054200104079024400075040210b14402c03030002c0c2580c0b01c0c02c0d81420320645c2d01400b81c1807081032461501000500c03140e40c007a80e5401e0841110030480c01410414810f617100006020086a603500c01481b1450190800f0358119005545900c0c060701888421009049441b13001c1072804e04044607001408036a80140501307a0f0082e0388a06a0840c541c2d5922030580a44400c00002440010310b041400469105030840e9426500c0b0b0b803003580d803c0c1d80200035242107804503d007460b66540c8006400000d0601440d0580e0020304110400ea400302c451800740043d941c5041c000c0214454111040799088002d544480da110005004a0207904182c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 799676537 1250 799675287 799675301
    0x150c0b011d180114070302070b061c02010e0f060708040e060613060c0606091509050f10170f0109031716080c071505072307021804231605040b060d0b12030c1006150210 74
    0x900307071400701c040074010a200d5444030608861607900002c1c14440e000203400350359006032040c2c45857c241001403a070000b0020b018026502409142d80b80c107002c00c0003640200c4e000d480401010302041480660344a5540c26a001e004116420a000951003140207815584a5071000c10f09040e85850142d4004802000d48846156405a05151078a003082405548011403281c2e807400c1a0704201c07101c1c40240300010f0f144a07504984c0480c008a00c0703030700024076034100300001c004945e100c1c003524048002c034450755802c00603141480100240d040d00b024042e6150107580384a40404801e02c40345080e81d100b140310017540032104100c00c61000e10301222040d8800e10900480b4110700d441c00c200468040e200c0403181b002d0740b180e030b1800707000141c101c0804d000304003e60303080c4007140e450000103074240550942a04903d584103100c90700c580c0c03200c425080d03d00450007030b00d580d8140026950385a086041c0e984c42210b081c1980051300d0149140003542c035a00300c0e40070b4915015201c1c1d00b5000303800d007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 799677787 1250 799676537 799676539
    0xf1a10021609050919050c090105030c010f05030601020f250e1003060b0d0501180201090902040e13050a150c08160c031107150c0b011d180114070302070b061c02010e 73
    0x81c21759407a050701d03da5a84140c298050310041848032254030800482c2d406c16040399011f034003d010300552a03600858000210b0010342000c680f00d0344d480380108c0c0f500140e80b654403120710600200d010105040d180514030ba4901070318070503083d502c4141c0604000d4094070b1100c00a41c2000d010008119141c2c0100746800703000f001141240c0007030300c50a00751071041c03c8610312070b04440c014104641e0070000a0000f00b810780030a50070180703084c20f021682c0c50300400d03003058400160212340420a00b4040351140540c4465424200401d03003548a0040000700c00200204042c3c90200b000d0781012207880e030310301140e40d5900c80080324550702110400280f000242e11482504804540c8503140c0000411020480d078810320400d4003420000050003069210810059490030803259000045400c194802404a6060039640e001c0314020b0040c285010000d034190070110074408020f42c550000d140d140d0180e003c840240c0c444e00c08100c40c2400c0c0c0400d01e203020340c0c03482d0b0100040d400f030b0404071800f102c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 799679037 1250 799677787 799677793
    0xf0306030123191a010e1513230d110a180c030b1806150415030c20250e01260a0c0302010804060f1a100216090509 51
    0xe010642c0340d00380e1644603805200e240040100007081150401c1e81c9400c941d080303000c0c03107003078050074480040d504080c801d80e0420101301025a8591500c0c0781c00d5091000100c5490350314513100c6020500d04a26000e030344a00701a0499440458140f1040404100001004071003a0703045503903000c0d04008405003281d0404003120000488070300383d042c0101400c1a95102046800c61048020215a40b030514148180000e4184041c6100d18548030380c2d00071030650303a08060802d054030224042c00386030301401442c400d01c2462484117616402c410411115a160a18808580d450fa45010290300540400c207500001a81201c1e9144854101203003c1c02c5103034500c1aa00d800c6d030302541c11000d81113080e41507012180441c40104030121001b05d0140348000c0c0880034003075a01d0110040c4030b880040e041050100201b4280046580071042329020b0000c20491707030060b070410303402e881241e10280f8428950340e111801c0c070754000f18418114415000c19140760500703024480700101006000d0306990f01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 799680287 1250 799679037 799679051
    0x3180708120a110709061d0903070204020913090f150212060405070c060609060618030b06010815120c030708150406020a0c05060c0705010f06150c03110d0c05010e030703050f03060301 81
    0x20340140450710141c040c585000c46d4143c1810000850000d80d5a1302c18040501c1104120003083d002c4151403800c0c0d0304179030150760759042e0000138240341c1b0307807903484103040345080b41e19002c108442d0070f1800b0151041c41103464858072107001400b02d001d00c4560000c81440f000029015280079401598480218140901c8403101500e40d10300311800780d0410805031381d489000380308040c2c00c06000c1b520380081701d42d400180d504685e40c2c080800e402612950501090f040401c403041005840c107044924090305100e202e02500e2b820542d03450305860441d00034041c109021030815400725000800111101d180c503000c1e01e403550341e00002d600401008007040050741000c0009001403003003e0007050701c0f00300e2944036102403c15508550740d142005c0354562070038000b04450460400c90100210350350a2030817241c1007504055980d07182d0005a819a8014040c13605005a0840e440484180c020002000354400010b2490303502d1046c2180500481c000340b10b40789111164200441e80444064004240342c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 799681537 1250 799680287 799680317
    0x203040b180a12021507081b03180303040f1403210406121b0c0620070309080a0812090309030601090c02010e010c1209060b06070803180708120a 64
    0xa80012000721940c0c088450000303500d1405201180203040c0e00d0074031182e4201d1607400104403001038800714500040100d052000d00040d4815107460360b0201e0022041c0d11110503050707440c1c0e409801301c1801d01040100c0a2400e080000c1a14152031081900d0b4442d64104807100d1800000710076459414410342c1841440b9441100000e010b0991104030701d5111070030040040c01e202203265603503c00302d20340b03001c82ca42540301c814116858640d45c10500c0e107080d010704103400a003000c4603410042c0070707a18070500c2ca0f0301c0d8042c0c02400e1082c040e603038030000e99889000c519110802d807000035091090070300144907000810b84541d900160785000301ca18045104d03012a003040000d0340311141860352000d02070003280e0280141d80f610607032030000700518036403204082c0001c0d99078140840c24980c0d5034038100800a8a51145c07036820f20081c00329458001c907141602c51640210348990300300c0001c4000c00401e00f40015141d003a1646074014187e003031110500e644841c0c2180c4100800c128441d5424030744 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 799682787 1250 799681537 799681559
    0x1060507211709060408030a0504020f030715030b15030c09030709181502030708041203060914060a080601031101080a1410030b070f05120a0603140d0807050a050702010e01020304 79
    0x3071101152200c55501100b6084003a90b490000d140f04000e40101d403c1100080000c421641e2051071001c0000d216203640c0041141d000c070300401e054040c400d80314003180d040c0d50100003800d0130a91380d17070511000e101c910520103100b281c1100080502400d0001c105c100007010040e111500020b0f08032605503a50754464415a1203865466210101028440b4244404100441c0c051900204150300d1400e05540041c15650005e0001e41000d0986030184580c6100303401020062035039080600640740e010355081001c05056030b485100b00044500050700010100c2d1442c101d03900000ca100c40800b040b8010744850500030a260344082c1e4aa608460403805040390501910101141e01c2445041d0701d8140c124101c090200010310040400e44082c0a0340b1400300e0b02c2c00e091842c40202d00303485260f40c40c0041d1885030801056a1010b08141846880016810405050301ea603500441cae111158266150304c40e481c0000c000a400300f1020b030140d40280003000d906101841181d10742135480c01d00e5a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 799684037 1250 799682787 799682843
    0x1a0102010204050a031118250e0f1018062607170603030d022b061a0d061203050c070f0b03010509090a080a0c0323040e0709080a11100e0901060507 65
    0xc1c80700340ea01c0310250840c0e18502c0310311052308a003080f500a09101000900d10190b109481e40300d03588030600742650a107d08020914003501280d00c500b030a48030100070700304050810140c0c04c1c58004064503000c141c10074030b0704c40c01a08140c031000c1c5c0561b81d890400c41c3c000c0300248069011f101c104981d1400c950316100030003408400521010380b801034000c2d0700007401024451904840d05202080c4024102113103000002072409203a02d681d0014000700078050013880c2c2c4407400c1002010140d0042c540c01c140101464042c500660701c0f215258111400d42c00614003954158000c1440144813600f000545950040142c01c1107d04596259880ca6a6a44240d841c000045c05d55070420007010740251440690641c01c100f28041d07400c214281e60a035004030321401e105000c00e20081055140126140d102501159068420408250515030182d4003404205801180c44049006503984200740c030b01c4440c44000e20700004e6920700001124950414481900d11042d0505051048900315070808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 799685287 1250 799684037 799684051
    0xf0e0c0408190b0f1009090f05010c09290a030905150a02091804050c092d1005030c010c030518130b01020105010605030906070f0507060c031a0102010204050a031118 73
    0x81100b03121450108400800580401103168540d005d000382403070750403001016942000301c006105502030400072007660340c1c00c10181180d403030b0100c005820b943c0050850203858000046000386401c140b2581e2515080080c507803103074603080c4590700c1c0b164441d8009106840c0144202c9441300d600c11201812210192440040a680040e1081a07030a02441444101d03001095411483c40d003601e42507102c2150b401d0541c4540c0440000035500c0c22014840030084064a4417480c04c0c40d001c0c840410941c0f0195043e82c0a0017085100050b940303800a03044e198424180c1d00c81d00c5101c030315a8161500d8000003500e22000112442240135512500c5403200d6400c403004020807030304020780000e4211901070b000f440401a00304200075441c540003c0d01038110681d498803611010001c242102c0034012040c000f803c0c00d0409a1408180350316030042810f480d560b64810710020412001a402c074480c92007034903045030701d0440800100d4443c0414000c5100003619040b82c1031004c545107262540112110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 799686537 1250 799685287 799685323
    0xf14130f0603060b0f01120e0f0304030b06011e020c09180f070f0b03040305032a0f03040302060105030708070905190e0312060a0f03240509011e060f0e0c0408 70
    0x81052107014001c0050900d4250ba00da0211700c41c000008298140c11808182031985a0703840c1c9a082ea0100010407042840d9002d036500d941e168680101132803410703202a8001403011606104607443d071030402000e079003141c0007402001d1528040c0b2054000c010000c824a080e02c028031090b5540c14810825a600180050240da60900e08081030112403900201c2400b0302c240204070000350030904480c6c02c05d888078909480c0c000640328140214132f001d0142d100c002c00200e0009801c56110010f503006603c240c09403411680c8034800e05503161224400d001d038942c090001081002416802a42c01c11a4140562101e802c0301e00b070002079601c0303141c483c0318690000407030b2403400260000c100e03000f400031590700e4405464185825005000d5000c0030301000100304ad000c40c98992424480003021142c030040c00701c3e2078140300e6580203180b021b404030070752050844601240c40b854400e2505481605c2d42c44407005007030bc0040210a8001071168034294010400451046001c01c42454003144a401c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 799687787 1250 799686537 799686539
    0xb0702010806010909050c04031403090a0302120c060f0304050f010b030c120118080301061d0109030215071a090d0c08040909080f2209020a080606030601031811030114010f14130f06 80
    0x10a03070382c00d01503014514907001801204103c1d652040e180040781d3f0111074401000310b010f8020b50078200003c481e00c0d8004c10002d1580c1d501c060b040c2c080e5115174011030581d0168911510071500340d0380d007070100942c160849103d100f250300d0309030f0180f0300f001d90000c0000b60560006011030030300321030a4012b81d1000340101c010000b440e0320254403640e580f01480c2e15101108075400180074012103001c02071107880c000014018a11941003502d0580b5013028500c0120296000007003800c04090b903803404140602e030011035125000701942141d4075402100f0307614142c50111030200918100c0030854401030b007007041d804c0003c500005000f100049501043e46800c845404c0f088402899201580483c01403003000b00720b07500495015403040c0c0540d0115501d5844034012001010184030380d103440c01084540f030040c403041d4100308000c524103500821048a249419034000c503000d2081e074401c404524018449041f480c01048180e00e8054000e41026503208400025908510f1341041015980c0700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 799689037 1250 799687787 799687793
    0x30406090605100b03073014061507020f030715030e0c09010524040f03030c0501050c1213080d0203090a05060a05150103110c030a02250b0702010806010909050c0403 73
    0x4202d0341c10400714480621450f28081d8180d000e800010600000c1c0242e841d50f00350764244901440c2d1000082c007440f20880c0e0350820310b070002003208040d14640ca0004c1c100203007040c14260000741000003480080740c2029016400c11040201100300c468060190315400100111802c202031910b5059032008034283c0c105034901403030401e040000d40c0c40346005030f004000b5030b251400c52891411592420b800013200f0003c21007a04c0c401c503404030907104a00c00f000028103900070b507044080c61040c802030206442e1102c104185008408042030740383c02003808074011116400901184612403c1d503141000c6800c888181207130411280c40190790401c5d1104002c00c4400c0c0316156006ca2000300810031800d11007103a0340d0440c04a400f00c0d050507035400c032141d510102a0142c0c2c1c0241b0801003200d544100e1803070025141ca40740307000d100400400001c922182c50f00894907a0981e00300d200001d00341405600110351010b0050000c5c0d05024031510041049003a500807948600b2507a0105640d681c5103203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 799690287 1250 799689037 799689041
    0xb090403050316080c07080d0e06070f0207080f120705012901020f280c0302090411011101020403030804020d15050c0a0e060408300c1b03061302091b0304060906 71
    0x20210300701300700700c2004200400429000f03580d001500f007182c2c00d890f0b42090840d08014400404950b465104540811200990004c0e4541c1750040356403e0354035440c0d580f08243d40e999500b02ca51445508804081940305280401400320130303015100204540a505210403d000080d0802c8598900080203c20040d43c0421980c00102e0300400200030540d011a4400c1301d4011200f107200008840c2008442071150030301d0070001440d001442c1c001c65007083d2914100840a22140602141786100c142c1441d041c1807082d01c003144d0b059100c101141e07441e0740c00c001d0100c91054040f0b0309480d00038034071000b5140511885d0f02c142840320541e6500d07004284061b2003451282da07414032a5070100428000c410004c00e481c252565010081c0250018001c440301c81403404c0040d01d52611800705240036810000235221301e805075808004180c40902e84181500d5050880303a089006411000200050900c03803510350748a11b10b44803624841c0030611066800d50310a44040d60700c0d64440381d402080c82058 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 799691537 1250 799690287 799690321
    0xc0f130f050a081501050f12010e01090b1e0c0904110a0f030b0f0a03150e0312190504050615040f0f0b1c030903030c030e0901060f0908010e07050d060b0904030503 72
    0x2600013041c90405403981d014044105001791030180c0034500d40e80c0050f8035280c15980c3e03c3e0010b4802440a202240300040c02464052000e546111054012440c4400070148a8400e0724050020007041d0303032541ba60300350aa114105490300950349112201c030060046020b0700452002d541e840c4202500c1c40300041c1030710302d08800e507482405c21034122070700c40e501d20718000122079004c09405147d0b4505c548010080000a4503009107000004041e051138210f90011032080c1a040d81c00d51114280c140c1c0041101c40444009008d40d002002180ca42c001840d9008400a00108082a0880046591401d403920100070000c3d4070748400228501e49044001c2c09048244044000c03011420343c1c41c0108030418a01c8040e042c40042c2700b0910a01d8450074240e02c030700344064500300240d40d40700d40080156840246040020f03543c0350000c20300c500107006404400c22400000c10226003006c3c1000351500c024401101c5155613420400061340b02c99802600c25402511130310784a1a01e040440b03540c1c480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 799692787 1250 799691537 799691549
    0xd1103060a050d0807061d0615010c061a190501090803071205070303060506040324060f05010509040204090c0c1b06120e01020d0504080a030605090c030c0f130f050a 73
    0x50003080001d03261905203000300d070011546280080d40604085400d489801009032005081503405000c008030785c43c08482440c0650111401e694440d44000081171140c0410b03800200d413003207014085001600090f40c10150008109009080302c80021103450070b03001001214030030072404105c1507801010f000d006220401c051403034003070b403079030784142c50805214070300c06221022031410305062013036014901821029003029a0f45481e418014802000c94041c114803122646048421a10500940b003c985070320f24113120b06410200190340c150800503216802903402d10001441c40e80301c1c010382c1d4603503a03a5141e500713508680d42045000101003d032140d07615586050100070fa241c1c085200e81d00c50100280006400301024519800785c4900c0c61488035081c2000c080c00180580c11009041060182d1404c0050179500d10074098040412100c480d4844820300002c0e004256180007008070301d816090071454150034001c01d80d4000c40310f4006032038a1845074018002810204080720290007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 799694037 1250 799692787 799692821
    0x1e05101401080d2001020d052d0127091103070e07050d0207030306150e1306050d0b04051509070f060503012403020d1103041506151107050904080d 65
    0x1c1480480350342d4002c541c140004004102c4d816050141c009014015102640e00080d592543c9138000d050290900751500d2180c2c03106070b903501001001040d20084540c24a04142c1c0d0301e45e183c0001c0d420441c0084008160141d001e52000031034510511a8240040c46140001d0a00800303c090600d8818580c22480390700011105000c2c11540240c151a4017000300310000d0382e2100305140882c09060317140c1c00f051107100d43d42c0b45018229007095111a0790380c4150707001d510744141c808400702624424032a041c0c024802c1c04810700801d9411040035401030045080703444800c406c5101c1200c42404458101903900510000d2000d1300707100381a40001c1c510347ca046401c55041401d0744102628070002382281040c1024809095030094051342c44658140c46c1c20400701e0064070191517594000c071030842d15800a40d901540b208214407440c03090b034130141c0040c0800040860240c0e40000891908500c40c4981480000c00e513492011151140d88111040d0ba184c401c603000c0c0b01c050310385059103c10298 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 799695287 1250 799694037 799694039
    0x9060b12060108191a06010c0f1110020111041e0807030503190f090605071b0605070c08010917030c0f0f09030c04050402030c01140919031505040c030b041e05101401 73
    0xc5c4041c196000c1301410401000c2c443d80707560005032454080036800814003480c9405200521201624090319414243c5188421f519404401c900f00d0b01504442c046090040c80244007080300b043c00c02c0c4420305601d074210342460f210744e10185030142c69401280c041e03000081c0d0703c80e0810100002d050030031144c20700081004800c40007601d10b0b44507005840800002040003414082c2c3e19182048070180c1d822180304094950313000070050742c000304c02030758041065480026000310512070404c600b03030004001c0306070781455898402a6480038114801d102018488551a400880000c01c2c020600e0b00d80c041e0703206100f00a250800381c0182205201b03a00d008100700c0541c6021070404001642403a1440740c4101c501c004000f68007c00c4801c5d60018150444001041c8403070074180103481c0070340910103000c14910401b20640380300701ca00801e05100e031907003000010302a0350519089881281c000c4400000d05452002001c0380590945441d80400d09801c0c000a00707200341c508180d00840904495 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 799696537 1250 799695287 799695293
    0x406080105091e1011090d0302060915090d1107031e020a05060a0207061b0c0e091e0d0507080705010227030d021203040512030408130b0a0c0609060b1206010819 71
    0x14080400701010440e2031742030044004c0703052030856418413801070542c10826946d040080d5a110101d40c0990300e40300f2800c0c4042c20190344041d0324420303480c60004103148002801c0442e41c0015030203101c0868400c110010000448440d00303031410100624900151318402d0041082d410140e034403460141c5c008101c00101c0740c0d408640d41c02030310402d0a100704010100c9468070003041e101c040140044020580c04500c607006003616600400303c4000320380504002141e01c0c0c014138402d44001c0c409074030031001c103400140601c014001040c0039108003428084140c544e1800ea82c0211200c0d549400e402e407040c030141403540b1b80c080070654160b00400100c098020080c0d900c13000d03101680c400000101c002000c020f000c22401c59401d03030009070152682441d0dd882421600012030240c0c00a40d000c101098448108080e03a40744950381d6075045d02140300c0d8903520004d252101c000d485850301c2e1700d2041496115001c00c400b01f44503030300c0105003941c542311020b818400b08200c604000e2a000d0041008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 799697787 1250 799696537 799696543
    0x30609011b2d2001020c0d0e011710090e031b01060503030715090c0b1b0606060a030504030e0402130617010b07021002150f070e0108010e0c0906090406080105091e 72
    0x1d01c0c00b4540107640d402d115018150360406070360070710060968545054019040042d000340c451803a03007508a60b105a201e100603901746100c3c203003480c0043d0100300c9030b201149100e01a0b40e00608509002c0c0400d41e102d00c800c6c000e403034110b001c44e02039520000318005800c018001c400900c40c40000208501400c0200080c0c9920604102402c0840110342e400c2000c030503640846581640300a1000c0c0d1999615800c20035a04080fa81c00b0940038070b080324890003100410660720880c0020002c0f481c014141e1010b60007020050001d404104000300e5107125500c3d24401040311441c0d00100948052402e40014030202d62205c8114031041140010042054130201b030b075075656412640144850400c130802c914112800309103103039550202c000d01411060120003035000b144a50b50b20703200d141c11b041c01907035010020310135509901810340008050308882405031524440041606103451046400142592010381110580d40d642d24144448003808001801000e034800c002e6401c07044045440340c6d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 799699037 1250 799697787 799697837
    0x70224210601020d2c15130501120b010806060f0c0d1808071203031e0f0501170c03062e0305060a050105010c080f0d02390a210c02030609011b 63
    0x3c0408a04104803030705075215011080c80318810f02446e07440702c406581c62440c0035141d11904e4007040710030b800803051905078014804c442e40306031141c503095100d1809004107580314802415401d0700038410901030381d4040c892030480c1100c40c0d8a0045000c0109042d0250390040c0c0c0c000000b0350300105003001026920140b40f400d45130141000141c600e55480c81d1441514141002d00c80a0b14260304035810659551149058800c4003c041007101f42441c03980e550340c80ca0500e80c1d0740c103a0200740059502e028043c24022840036030003049110766100c06404000d1061a001101c0c0c3c0d4101800b0400c14000620070940140307400d00e02111240c41c540c072044101e1142d010071200050340018500d0307139010300342c044503101400110442d10b203104120200d180e074502218400c0b1600303241c00340c00481caa40011609030b000e030840d1001c0e150240c0c0c030302c90302c03010941c80004a0600080c020400c01596040c0802072094103143e00100e50396201161b22295400400500001d21141030007120503031a1500180d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 799700287 1250 799699037 799699097
    0x807110c1201020f0a0903061b120b031903201f0507140d0906050c040612020306120a030207080f12040e10051509090c070224210601020d 61
    0x1d0718a1403000000d0282c410980e04200d50907000800c0359142c1e5102018804a030300500301040040030030105d201c0d01c840040c08a90010755030849420001010754440c6000b040028220ba41e92507440601c284401909141036000c01e0182e00c1e00f8040003402c0c1c144110181c030610242c440c4800c04103585121010b00c2c5401201603a80b079001405d0f81e4056021900440881c05100c0e1b05d44241d416004050601c10400301c035000d042c075002c00e03100d00e03806040e07a09a0321192500c0c0788000f04c0e501454000d400042903140d001c0440d00190628400610040e49030314040e81c050101c041c20640c66524090824581c810503900101e0a150017842c02d800303540a0720846014851f1076100d19112900240c45500420341c00303003d0800c14541d5403000d00050060790b0094841120b11b0380c42c030120201302c3c000d100d000794108094090960001d0110101115065101e01c045070401c0e010f280d00d544114003101095000310105000c0c004150303010841c4114003005403500000a1070300c60900c0d4060300f2020391203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 799701537 1250 799700287 799700299
    0x605091e090c13090908040302101809180f03260105060306010e01020a05060a02030a1d033405030301031e020f090907051504050108160c02010c061d0a02010807110c 73
    0x3526544802d011180003004c5180d01072104407603500341030710140d100e80700407441122640700c800c0a403409410039081e0408a40304048020f860000004003a098888006070315002c4c86a00c44001002c08040c003507210700903a2000e0380e000e0307800584041c035148425428911146a001040349c2d90340d09003240d074031000a00e01080031400c52001030b8640760740a5401003e5000d160300300315441c105980070394490b0b40061030902401e00010103109000e0381c41180c00565400c100096114040d44640c180e070188180419a40d40b0b00445501c1103101100003012030f480d4000000400078007586010359400e0410901601c040310925600103041d0302003440c0241e01801c01d450008811b144140100002010041e1144003a0b500c480c1203180c4a5220b805490b01081c05a00881c102c40e40d82c204212070000c0343d40304c02e101d203299a0010b6a071000f11007000c40d1515110541251003410034900c545400e40705100612403495980b0000d481d4101c028500e0042003011844003040d16030001e841501140d0540d04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 799702787 1250 799701537 799701547
    0x30b0306240a09290d0b0c03070e06191202030609060d11041d1c0c17090d06020309010507031b140f04120c05061206100306080105010605091e090c 65
    0x3159905100d0351101d0005842d00381c0c2901c84185044c01e000c95400807109400b8104c02030420006445c1c880c5074050560500e00f00005c0040d03000600035604240f2606040c1007000310100000c1003640307d4841000c0000c803414035156a250802e510340c40c1400b1090055045260080108518002c010255442011102502e000b404628112000705510240c414001500740181400e071140d003050301341f80288560410212400c4220540754914407540c2d5800341c4050741d0341c442d581e002c100c00142d001c401e24104000d03600c0f652018000c0184521458025849141c0b40009600b180c41c010300041c00c0c1400c1c42c0410100f0907a0280ca00203148041c02d0640b070407104112106843c1c090001704440d028800200811841e10000c0095090340c811421204a591204140a42030103010300700e0f070140481c640805c002e850f1031110071840c4011454002041a990813045007503400c00e900131004a100001c0c8503406003403480800031004032138811149114a04800315414004c002e02d414050b46001c12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 799704037 1250 799702787 799702789
    0x1c020f190e0901140f031903050c1c030504030e030a02010e040c0903081317011107120e09160906030e19020a031407091406090f19020d0606030b030624 67
    0x350504103007020705000010360f103848040d908071012494240c45003021000d0748000d0324000070302c01c10540d4071101c6496202e1300340c1c3d01514190442d8500c00d00364010f001c9040c005003ea405046852255541d001c5098141790402625042c0040031076030094001e501c0791000350340c0142c2850040c080c180d40015400c0c840450032580720001d600004e20303403036002901740015003290b218107059880100d0301c0700500b0f0145011b43e00b00c1c0c010010300b001404051200320045081e40c810980c0100c028100024000c4034140082c1c90b509045a40392402e400e0048a841c05507031100042d0f0280c81581001c109200c505800d442c0d50303090a8580561801c081c0c10710b8411500c41402c040015540a8185c1440302054a00aa102c407014060346c041c841c94040103041c030544e05801d8500400c07000d824466030303480c1c20a100303103040e80040815241192058501c1032804661004000c901100364000806078280304d0010191446d46e6807a0b842a4012400d20103061b00310707808490600b40c803140c03109140031294 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 799705287 1250 799704037 799704047
    0x6120f192d0e0601030503090102480301090c14010e03060a20070c060f0306030206090f15040905041209061202032203020102130e010602070515070203060c1c020f19 73
    0x12030721640b14041c40380000304020000014040301d0100340c092720400e4480101604502d107075445803d0750400005450032203070090040c0900050300001d40001c00c02107060201e070030361311640c1c0104c1e041641c5000070048000c4140c002c01600c542440c00c581d075008000c0002e40e40344006801188140d54911000910f00c0d520310608440784082c502a039202c92250070140c1e10b040301c500c1810041801010a40c64540c0b003841143d058950040c901420402e0308018031040780c620644c40c942020500b00324500700c410010180004043cac896021503580f0701403520070f0402804040780424880b0340e03081030120310381200255007000c0400e040162170b5640c48440c6900076520502440a20380520740c4d01c0c041c568190020407070b11414400d0031449566602017100704280921a503001600305034000d000b03518100000c141d9076050810074500b0680140c0020703003003070020345005580c00c8001800c0c4c1d180c4940140d035035141c3c2c0344c510011804c10801e1420716219200e00c04400c2c5d06d1510703c19031815494021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 799706537 1250 799705287 799705301
    0x50f0c0627030d0906170103200a0f290304020913031b0308010603150f0501032004090209120f0d0818060a050703110f04120206120f192d 61
    0xc00f00d410300098444050700e0303004c80b40600400601014a040f001d0400f9864050480c0c0d0703c000081e001f0403405180e1401140f9503c50113a100285c07100005040012006181c05005410310103010030400c10000d94010300900b00d021810a010300c100400750b510071010340d40c405204c08080901d03416600d000c40c1c00f03032009001c04204000740c10821047c1640140d40f503041e100c0356202080118021802081d02420300c4c440d4480902c00840c1c24031841d4465009440000f6108121040421840014051541180e04644002a40468242018948602c02c0111441041c2c00703440321f0800a01c800b41c4610008070000b0510000101250484116030009001c02c00d204060325503d0810030320010240605403640c00000c0e040c040c204420559040840300b294414454461405240060904602c030244034282d0703202100b80300c60000322812104441c441d050001609070245072100018203074941c1000c2003d0401e14064541c451003102c0d0b80101140300c0004a241c1485007100c0580e0054a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 799707787 1250 799706537 799706539
    0x60a0507060507020715082701200304061d030f16020316180e070e0604022b11030c27030a15060b0901080c1303020d0f050f0c0627 58
    0x2d44000c202d0943da01107100c030151501c6400380750329619601ca00319803214003179503a6014200c0e541303102d40b156960217903c600e50b0709800002040040c1c40d80c00d2036801c001c0605c451019031030000100030270402c0d40d1240300d504030040c00682c000000c01d600c0c515aa80600c104500a1a200040c180c11400140c187c4208207540201191500d8819001e20140c110203845402424030804070700e0b019503082c5000e1020405e1901000b001070700c2c034184e4001507500e000303050507401660800c81c1e00c0200ca851007800c0042c00c2000100400c8104e00c0c0050012550f10550070121100c0501c240f004032540072040300e0080c0405001c48640e560061141c68600ba12031304401d81c50312401c04402c0400c860355048200010300b1800820003503503107503081041445074000050004030b050b00012a03829108000c0d01d113003615000700c8000d1300d8896012640398681c04005940414040c0e4403a810030100f000300046a410359406030030040003007c040b40c014011004032000700d080a00401c1800d200b55480c00340350b410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 799709037 1250 799707787 799707791
    0xb04060906230c0901020d350108060108070f0303050304170d1a0405010303020c0112140c09031c0207051e060703050712020a05030927070f170f0105060a050706 71
    0x5080d0800794100145240e01001d904140b00c00965100b0200c02a180905010303005000e07030042002044171941a8910f4800928140c0d10413540c80303035444902d8264900048aa00110303506150704180707002c0301640700ba0401e0b803048409000750000c055451085a40c907051141d22500c0303e142c02e0303c00b880c00210f0303078554480100381c02009101c107400054820042e040c00b503401c100d12600740f000b80c0d10240405030150b803003800445419403186018041c421041000050203012130312000c1920b032020b503443c00d00c005021546100d20714040c406070902000200f071600702c0f40a82c00d000394440720203205480c400d904035481d03400e01092450300c06010420040c05165688181c1c60098099001924150703404501080d042c0441400042e40694a9800000442c00c00c2101020006903502001101c1d407824020b501030f6407882d41c09040300380140070640720380d41d10f02030062000b00200b00c52140c4ae006e140c40c40051201106603889024151001540e55030764039a1600000d448074882c122000f02114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 799710287 1250 799709037 799709051
    0x10f151103190f030c0309020a0b0a0c050102030103030f1b11090a020405041b20120d0905011406040509010b01050418020405030d03020c06280504020f101e050403050a0b04060906 79
    0xba8040ba000e50030f208035031010030180c4181402241111301c2d03900000e4200329011001c1c480c4034040c17400740801a4092500002e101030b282c0e261800e9030800c1c0e1003200460092015283d9554200d5040c44a51740c128106903200c00740740d141ca1021618803110b0030b00451a60000c18461038042e01200c001d4100941b0a00c03498090560480d400c42002c0391040c009404050f00031003410003020040c1506200c0001000103125604074401d40e6030015000b8614203a5410800f00080c0c0203004403c803128054807891001c0c50310b04284000c1d50002807481420307914000202229a81000558060341c2c0c594046c10711610900f46024003d03c20350300002c0e4175214070f803a00442c840c0d141d001040390074103030800e481c615200c05140c0743c1c010909070382060b8900c6902c4119202184c0301d90280f41c0c070500081001d142901c400c030201d082c003903136500140002410301050301a00858560036102103a40d62030050314041c50b5454240c3c442d502d0343d01c001c0010100c68042001d0010390340205000c140c02983c108825 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 799711537 1250 799710287 799710337
    0xb040c08010204230102031903180f12031d1e01020f031335221508010e070816030e24130213020c071703070b010f151103 54
    0x12444d040320466941035080140245500c08010340d144001e0704041d0074294108928290060017242540508504140c400d40340400c004078528820315005407107041c0216000c0701c00605580c4013500c00740180d10a00071038144424009034003036207041d04840003000c5c2e1219590260180c4940288404190404400d00c142102c02000d2442050310500141d0000c0203088401902090021011100c0c0c0110390a02450f4103034484c002e01100b80282da03490301d10700ea00300c1c00d07000100343ca8000e1950015001076240300140c101889501500c0c104510f1000da14052000404017031004058821250042808011070760080e0400c0c0c1850000300f0030340f04c03000e54188a031000207098000c14041c0f801000e02180c8030a81d0808144002500584005540c60b840750075480658071291140c1598400e2003000510701851801c03034041485048061079541d261030402144518041c1c024080c0004140d00070040140200700101070100642841030452158805450440c00f5040340c1c0d50045050038110070361 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 799712787 1250 799711537 799711559
    0x90105210901271e02030a1704140301061802090d17300711030903070902030a050c030702030d0b040e0604321b0409020d06140105100206040b040c08010204 69
    0x14411042900c180540240c050440f022150180100d80c001d52200c0031a40041d40c8540380074009800c80d03440c08500e070b0380d002e9000c2d44c00c1d240f0446d0310b201050a000c01300440303002030341e0140124020304c6018105080f051401201d00c541294030742c0d00103142401078458950f50480700d0f4002c01501d451a58464aa031080d6101d40c0c034140c0712038900340148840f0740d0402c20ba030035426081505210380342d9800001395540084030400c8006403005110410369907904000e12070141c035404801585a0401c071460344103803007000c1d0046c0c55144d414010407011a0b40001900c48442040c5400710f40a20145c0200b801845412030035082070094004000a110300f10b010031001442d0019404681540024500b01e04049290700d09820b130030400340507007070105107211940c1440c2c006100140c40c0c0416400a41c0441a01001701d0b4600d44944083c8050311240c890b440c01801c00ba28841c1800704105002511544000c0c8003d000b0b0b0115400f0074180301c800c1c40b41d80003030706c0510001c56641c5c0c0c88181c4424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 799714037 1250 799712787 799712801
    0xa0c050d09080d090806130615080c150c06070309020406050a060e010f0201180807060e1e060105010e01080a0e01090212010617030a082403010c050d0b0d0503090105210901 76
    0x103150b10640740c20380f1040f0b208140c0d040071241c0b03100261425440314001e8860395030206106840040e156405c003c0c2c0c01401d80096001801210010a2265054800d00145201003007065080300c0d0140042340d130103000450a60b0f0300245034580003449030542c0c070000f8010903d58100341d4000b00c4503d4007180c1da5030490425402d00109032510504400408012401c0c0c42c440a5941000d21104003010002810180134013030403886541e001c103a90600025141c50a01a0081e43d24000340507481c150000c40c0510401d80908000c0c64078140301c82040002804018014010b00c8125a9030203240407490020340c81030000540c02030071001c0030301d00e00702030a0103008540140750640440e041d02c4100c06100000301ca880480d00d4803680000c3d42d0712035440c0200410054480c20082e0110a00708450783c086c03089081c040c00944a19071074005100108088030440d00e2054062705514005d003020440001c241d564451007441d005ea41d54610302c03a03207140811141901e50b0075800040a00070a02d80c1900300c51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 799715287 1250 799714037 799714049
    0x41a0c0a150c120603080d020d020c0109050703020a0b0a0203040b1804060303080907050108010e16110a060f05010504021303060b06040302060d0c03051e07140405031b01020105060d0b06060a0c050d09 88
    0x1a80101c00f1030070b442252801d110042000c9400c010300c1c1d02400d81034014007104070001e240182400c10311450785081d100500e400b1030302508403540034400c41c580313038144002808c0086801402d0911011000c0c0da03034482c80c02041503803003001c200c18480403107620700d1020b1001d0151044c440c0550b42d1601034141d4900b030ba0707236103d940103040c0046015441008480d040310252840107641c0d8a07031200103124502180b1051082145031103c14800580c02c0144030022445104000380164411458404841060b00305a105a0041021a1000004104910503213801c120300099100710000020b0707051103550f00082d005003000c10990841d0f4082da100011076003030b0362000c2c82159141194865005406c50b54000400d0b0007002282e0501d1040d42d03401a0841c0300841c4e2442c01da06c54000034a0840300070302c001a010307180c81d00840310307580c203000e40c0b0380000e825074a440c0301c8941c80e43d4400c40200024540c0340a00c0b40400c0320100644a01942000b02e0340023010b0707650000003500d00038888140c0340601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 799716537 1250 799715287 799715297
    0x106030203210f130e0c0306030d0801030803240d0807110a180209010201020d05040b090c240d2003090705150f0a110f071703041a0c0a150c 62
    0x40300002c501106010b00481c070350501d5180940700c40441c0410f070807060311100c3d6107001850119400341010102801401d03109445501e900e0b0030401c040c03030100c0864041c001c21000000400000381405c0989803c001b280c0712000c0c10743e000f00c0307001c0e06848188800302c1e804800e14a01000b40050f0a008104c41c2e4043c00a120100350004d080c402d115459105800803249903140320010305540d17a001e01b00601e0144005803510642208000c15240152004e4802d01010030902400c08410080400506420345141080820f44694400c0302900c1c0c1c0202c0b190010005014102c007405d541c000d01c0b00c080010302c12107046002c41f5a04185070000c407003e2070244115800411640790000030900101d0034010418604004411440f50a820502008040c8030583c0c031b2054030715005000c001c0035828030070014546280342c00b170399001341080428107a4942c4c108000a120721500b02801d0403058515824407aa1940340e81101e52624942880103084214550312840c40f800316500035214840d00c075994 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 799717787 1250 799716537 799716553
    0x1503061305100e0705150c0d0512060121090f0203070314070b07020d03030e010b090c090a0605090307051002030c01020408031308030a021513020904150e070e0f19020c0106030203 79
    0x100008840c40355a4034103c1d548584801c001903e000080c083c0c44448110b491414280000e21070780c6440c101c1007907000811008200624441420381259030701c20400d1030100c001d00318000f01b034203005142c101416881034903000c01e0410300c40e203107807215480c607409011500042d40c3d90030444525038010740d44000d42d008100c00098039210b44400d4450301500200464612545590158020403941290001a5488100c0038040307584039000c40d48605c0e403441d4940d036203024030410080496801d8100009001c0140303d00d82058a00144440c1a070f80203451b18038440d0b18001c0c081c0d123507003e0081044d50b59800010085201a00403000d4280c55880281e10341c09203407103101e11526030251014020040c0e000490a480138520038021541020130010415108000798011501c91074040700e0503189068105054440c400452007aa5400121400603001e00e0f818820b654160070005030040013001c403010302240320201031405101001c048000e0843d61038941c110014060305151100768070034010440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 799719037 1250 799717787 799717813
    0x3094e0f11030306090a0f020c0d121503171606060f120201080f1012050601031a0f0a020901050909090d0806040e03040603022101060206041e0201050901081503061305 74
    0x1c6000310224500019506680d02c2c202803120180006142c0400c26480341800300704201c10748020501468100050301d49030142000c040e01c0e003900c070000030002d03c0c900f205203111141944603c5003501e83c40000c2c01c00c103503035003444c10a041c00b444002c50045c0801900e0501045070035070101017200c030805000002203541300e2010300c2d4080c0743c200c06404100d10400080540081441d0b0b0365002e80350702c012001054540790964152100401e040302d050b440f01005009001c00305100f04800079884101550500d8105000501d190014011101b0360b0303004503000c42144c0c020010744002e0240503160f0b0440d49801c243e0b6641d0f40d5201c17034100f008070318000c0101c0c1a0b0700701070003100c0c013044804005520f8145000e200b00e0003035000601e05040e10721011488640d11f4a5424800c2c001e11144c5d0040c045401d203810880010700c80c042c03000e012440e07940c0d41c48006036040300c241c4e41040d01c2420030581d542c2d6580070321a80700d840c0040c1e0716414041c0034104035250409880511030140030310119141e024600d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799720287 1250 799719037 799719047
    0x8120406080619030c06030e0609120922091a0a0e03091203070c0321020a150c18150e01020609060c0a020a08030708011503094e0f 58
    0x40180d1001a45600010b502810040845020242c0900d0f150440e03a51301d441e0107500d15090742250340060b480d260702c1e9912250030030090f5041013254003d00582540584203241e02c4c810000d103e0701440c10b40000b034525004003400031001c540135038000e20038040946440e403c107192454800704403000c4200401c156140d0b82c032a000748003107040002d500c0c04803d41c04000340d18000c00c00c0501c0d81d110402044c000903c1c4451850021840341032595868540005021824585e01d484001194481d8000c100482e140044210242d0110000043c0c1d60181c00790440d4081071282d40050505060300001a40182501c5140700034641c50fa120710862a819004903103555080d9007045035944044049100980008010b1100824500455091b03210682c0d50744140c4d0011510000401c88650040041c558102896100c004a901c0c04110302c03825980e40130071180043c0c44070031401103030040c0300140850420b985074052074442068000e83c0c0b508002e10604010101148002600700344840811501803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799721537 1250 799720287 799720289
    0x30a110604031205062707090b12070813050d0c0302010f02161203021605010b01170903030f0703060503070e01050a08010e0a152019020c030c150d06060801081204 72
    0x150307281c02c0f04108401da11400360038090101644654144002400c0e00031485451520f0900541101010711b041c0002805082465005480402040200703200205182084541c41201130412100988030181d21914400410200802c907204004000c103540b500b098811003440e00c40d0307000340b2114001c40031220a0340501102613003682d414072000d0000a51640144110704000c0c80d0040c1043c030150610000c3c145040400d98050350350b4101141c00c0d503800709044802c1007880143d9250b0b400c1081a0300d0307507448020312101000c841040072824080c4030360400c0c0010310000381100c6044d0344950a0340c040705020300c2518856501e030403001405070810301410306c80b034403c00c1c040c10084900e40c8440c15501c00c40310607006601e641d000071141000c4000d151000d030100c2080e00036220b888465012055017a408042000d40d8055800c0034495500015030440e1004291045101343c0310240b802901401010740443c030603800c1040104407968040c6050f41211348101c22241e00000c041000b001e81e10403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799722787 1250 799721537 799721543
    0x70323070501111e0c0405010f240801030b060a030605010b090306150a12150204060c0212010b0306070c060e0f03030907060306150c140f030a0324091104080f030a110604 75
    0xf01800d107580180031942c903466892032082c103617516880407400042c112035090b000864121102070042c01442000b9218a0245e964030080d035100341800b0300054041501440014078000c2c0d41c90001e8220f031212900003000f540d00c83c030240210350b15200d001c3c0954104905281c024842e0400044000301310300d4486486840103080301c3d0400303003800d060030300658000b1015182401d40c60305400240c121440208002c15441c2e5920710002d10320710401520014400050794560304002c10000f0035603001c01c515401841c0350400c00481c10341c1d4500030018010320b0040780705a00449000034a1558013000a500c21503c107020b5412003a2100c0c07060303003101c8642c040d034007440c001002c4050700075004040c200201401604403070fa6220700c400c01d0310719102100615034040d80011030f44215444c1c042c0511030707640385001000100710750010702d00c1414082901c28a5600c0b622203182c440c0c2c07194284110b5010b0004101510100c0c030f100300c04542c0e243e024440000000f10203040b41107441c013010900342c1c020b0b030f4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799724037 1250 799722787 799722793
    0x1c020d0c0801150305060105071e110d0b0f1906030b07020c0604061e0c1520120f04061404080901091a0a03150f06170a05060616030207032307050111 66
    0x3d81e00c0300440050100400840c18400c08000f6400420050443c01c05402c4940d402400320503144c0c90300e00084400e142945004140380342d9400006130500102560003001424032000355a1030072800d072202d004000052840500e000408800c0c4020f03e1541e031301c642584d03002c4070540a0004203010342d61142d84034090002d0684010740304000e04200210308681d0b02407401e1408030080d9103504640030301940d405407000c0d0351960000318008508000032001100401110f003000c3c10f038110000d9850f0010844032444d0501c40004042008a41c884c180010014110b410289842e2030071000c40ea01200c0c4490200380e43c0d06001030030141244d00c3c40008124031707403440d00304660000c040e40079050031016081500414480401c0184200009400a10295481e41082c2c0d00c1c0c02000141c1d03d502070b140100e8503003000308004080d141c500807204104d01ca0040b000003074034181012030420b042c541005024914894154004000c0107401c00a810007981c00e45100aa60710015500003510801d800d010350 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799725287 1250 799724037 799724069
    0x3070209011e0b04081b0a0810110c12030a0f2c0a12020a0c09060f0b031003120c03020d0806150c07330206012601021c020d0c0801 58
    0x220454516103a040d01c0e14403050481c1c0c6400a4210603005500701000c0c50340861b06a0700c0800e50303017031180c2c00d605007039030b414003401e0410b2103203512256441a0ba0513030360740301c00c61a40f2078108103040300c0c1807030107a0741918040c84281d040c03240d66500c213a035420070450802c40b4040d188071991142c454418900164a80c0c0d01c512002d280210100441c45402c5074020920054042080b6040030362000000e9405000502d03038074640303000c030700c20b00781c0280b8100c80c0742c00418010f0040e907100c03900940e980c02c1c20840c3c59036a01815000b220802c0d40008082200507109101c036590412655947c1e0751281d001da400200d100c06041b111020103d410960258002e07a25006c44118040100b003c19815406e849c0103a40720b4170054900c0c0c1d0003410901c4602a28400100981d0482c50f4078200c41900e480034001551602564040700c8200e0042c07110210355122204040103001d50440e22001222032207500c0503141d20304000000c2d0030810a15505a00700840010154818810315040e61908a59030b5100c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799726537 1250 799725287 799725299
    0x905070f05060d1a040501062a0c2603040603060e090a05070b13030b0c0a090f0614160b1305010f020406120504050c1f0e0103181b1e050907020307020901 68
    0x3815020040d0340b800751a4001d1302e615515180078542c040d007216101c5503207168080414207c08440c3c2042a00c412107840c0314280010200e86842080381c000b030b075045d00e44030140b100501421030721088524651000090010b0001e4241c1c010108039a11440c1451840d502c2000b01521061581c00c010400c0e006440706102c0241040090803003519410904140b182e126521124840815100032074021008a428144241d00429140140007021140d0300c0041c40c00c240603000300520b50488454120124080c681d0a00c0d0007147c0308031640003e41140141818032003541c00300041c61055506d9421710b02100c1e42c0d0706913402214201c2d6003030768a400751343c040381603c00000c240c040c000b11001e010b204106465035a800c1e0341101d0a060200c4040a0f0300c561120140c003e55050025a062500f03245c1185049001002c0d0308010f0740d000301881c040011031140600541c1507903088020850742c05c1085060520303010b5450700c180c90041d240360b403164031901000d2b6528002c80d01d00a40c80001d0320011301003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799727787 1250 799726537 799726541
    0x9060e0616030804240225030906080603030f180f030d050a03020c100903080f060a1a0a1707050d0e01050103080403150f11090915130c020a0c090905070f05060d 71
    0x40300c3c2c00b400c0c071007611007a19240008504501108107a05c660042088419040708509001d80c0309100085100455000d6070b0240c8046294400c060501280100133200350b2070920894500907610702215503a001c4546060749442024410603010380860601103005040014041110001c1e0351a090706103070541d0003c038042d41c0204c1d941c1445002d10b40007840307a4402c034000c6c0412948030343c90fa840c051030302c5a50282c00710001400c0d94403640e540f0700c0801141d950032400d4200b003450202c1d210f958513007001c004c2e1412610101c100100075a0130781000316060344440901664401a981444000802c0903001e007660300c04e020141032403000b08410000181203501c1c4801662440f00040f5445200316941003c40d4101d442e84a140000016015071600d440d8a840d41d205582c0ea2400c4102c400d01d8020500001c0841101795040c3d07951074000c44024000c109160320943e1100c404402661680c030040003903c11210121010300c141280400d4004500da000390a43e88050190750820002e0307290500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799729037 1250 799727787 799727791
    0x50d0f08070f1b0213090b06191a0a0e090c0310080f03040510480f151d151815060105160c0e0604090f020f0a050d0309060e06160308 59
    0x6403081143c0c645c022224042c0c0910b01440b0302a5505c1d201f00d1602d1814030101074003074110100326a0038141c09000400b0034000c41c101e08484039000c203071100425181a80c982403103508060344615a2800c10240c1210100210700c10700000141c1d0550b90342d1048010b43d103a1102101005a40040c0801d005a05155003000150f9685140181c1d240c4901012a000f2020818800e00e40c0340c805c1000608000303103422841c400c004800c030300c0d00c000c1c1c5581c0c80c4d1100c1c41e010081d00030f00d806c400076400c01f605501e5400615a081c41311135200e001400004905980d6581591005a40c944000005046500c0d014610107010b96600241c0340314580e10030f140c603500100504590500509228041d884181c20283d581e505103d04004164a41804481c2c0da50680c001c000b51712075410042502d0001e000308994828165060b00c18203110403070b0070005541000140c12071034100030303000d0381c1034140340e40305c59002c0071590300b5100c40001422503801e000c41886800744030001c24204441d00700c0002d100700881a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799730287 1250 799729037 799729039
    0x406090b22090b031905060403140c15040203060a0e030a111005090d080a1a091003021203030a0e0d09031b0504060f180212060d0609050d0f08070f1b02 67
    0xc1400c0c201455100600149504600b11080c1d8401d040740c000d04003008201029202c109201048aa580d075030956a000010f00081c200800c0e0910580c80d50300301800e54021141e0502511130720116422030708402e034401c560076480391007070070082810b80c03480380700360000d60121402031450041210016030b109900702d44207111030322a00c049850312142130300c50f55000d0b00002c0058000d42e809a0401020100050845c035882454060540c040017030300a028581c10400361030032102980e900c40c2080480d1425070000e07400c0303010302e840002101d401100851140c0d02c0142c00301f004000800c1029901c00b0400381000101c4d041d143d05101250f080c0c0480908030b101000000c00303403515040400c040c1c07040c50340128003041d628001030001c5030911016000c05c80e5280011814100b04403101c00841c1c0f0040d2003640140e011800800600101750805400d454101c0100e130f17070391075031180002d085d881c50f42910700028000c58007240045d44541c0c4440351000003603031441c900c01c401e00303100300c1e109076204812 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799731537 1250 799730287 799730317
    0x90312020705090f1f060e012312100605070b151f0f0e03060c040504110721080708040f120e19050f01050705060c1602040e0615060406090b 62
    0x502c3e40d0385107280c600c58038135030740320a48034203003240c2d8030f08840301da00802a40c8043c01c0f4000e1001e198065046086004240b90020503809415900c0703078165411003003984101000599400024078801c1aa030280d1854404103410b42d90700c1404071032134082c04074000c10a2904c000070542e00c14050403030081c0c02800501c601105c08204420350041c0300111a50004a10b0079407403203480542102c02c2e06407000341038015040c00c0c68240516542803180d800703414461907681042c144a61341c134200f60382009a20001030040300c402c1440100001048c1220b9a0026980707000107282c0318841c0e86102d010706d52026500303950300c02c01d690340500c0d081c800e00c0320420007000c04844412559450026103075640641c207001c00303890400c0d062007050f00400707c0c8581409410030145001940004003d94024442800300383c5844004c050616881c07007008020390700c9030820700c12001d07081e00801c002e4005c0700a51103410a0414520038480180158401d00011401041c0c0800120088000600c00c86401000c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799732787 1250 799731537 799731539
    0x4030809130b031c0f170c0304060b060c0a0209010501031e0902010e180405060106052107030603060903030b04151a0306041b0f0809011b030e010b0a0909060614010903120207 77
    0x824546139805650a4140d041c0f10f10078255103401c4400303083c62441514110030700d81550312540c0202200500b0300400740e034000000800344445907200048842000340f540c0c0c0c0c0c82050b10344c05942c030112460f00f40d2040215000001e0f0560092065200f0700c44181c04d03441c1c0360400b03007450b1001071004190590510424814031303030066480200301d100d40782418804003264140b50800c10f00c3c3c030307405820a0b4107001027004620007400165400550300b0101d01e4004187e82c0d17030380808401821140d40014510303420f08100c04100354154000904501e000c1c0c500b00300002c40703420034460030380303007481491610710b1400d101c01014102c0f070004642c007910152011074100d481031240403110700600104000a0100180030001c80d601801a903003105004000b804504448415080402030307083c2d03000705040c1d5a000300104400d00390000802280024103941d0555a244003140141c210100215900e13031500801045000303002c09040810441a0b440918550840c0c1d01c04030ba00c001d8400d100294491000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799734037 1250 799732787 799732789
    0x30e150a200301060c0b0a0c140a11061006020f120d0e07030b0916090908190e040501061809020f0702010c15020c1f0504050a150e0114040c0b04030809130b 69
    0x1140201002e559240201040d420f00a039109001390481440b20304110401c40150f0388100c1001c1d2404250350a5962b9a460749002e44107034495800c064114083c42e402c20010514418072401254034640139600c80c0f403480c140058842c0c6d8800d50303007151035400380440c00703964480d507012001203180c4200710742ca095100d4030748194110084030130040c1c507800a00d031000b01100d103500388001803410120600c144001c0c0d07690000340f070191010942c031280c0152040b45d142031041c5004880d058001d0010045d07940c407940014012107252040252210070034070000341038000ea200300d540c1540201d4045052542e0b036801110820f80d902d04c1a100d401c02c04e20a000d0040052000b856861b40f124001c2c4504000c110030441c102100d08400c10105180400304130200c1c20110700d215483d98408403140039a40842e41050007060100c540118561030301c01c415042220181b1401e0040d40a105101342c0590346940c1c1208034460750000070420f05e810701010055051000601404140c0c1c480045440356180c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799735287 1250 799734037 799734101
    0x9181b05190305070b0a09050d0f08130f06050408070312050408030a0306050306010e01030f02040b0103020f040609050901091b050903030f0d020a0e090c040512070509090706030e150a 81
    0xd052090754012030204000b0004200803140040403014562030924108500181400a4520896004040c1003203440100806140d400c18525440101e00c0c0c0c54107100040c460301d00200340030710414030610726004185140105c2c255422190540001c20605065984000340b41031910851000c1c41020b20000c1480310060010b4413010301e4035500010321920b0a8201460201c0c1a070160001c420110010310104982c0040c052605c1d0301a980400c41481d080700489c005e1241004040d1041c001050105c0c1c1c09611540705811101c0c103d81d10040ca03600e40c3c051400712882d81d01d0150031280c0f11001324000c1405007025014404009090300e00b081d00c0c10070408100c1c1d0211001803460b550001ea0406500d81044104881c01000e48452926140c0244541038911440c0117840c42200080c8aa03000040c0030000500030304809001400d0381d08120943c0d0b43d85005030300070000443e041c00000c00084800181c0500500707a804040301e4181c840f40c1d8030100824080c102e0b100c0b03070f0484148440c01c0301801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799736537 1250 799735287 799735309
    0xd0f0914030a020c011e050307020a0206041e0b0a0c0f05160308090405150303090f1f02070312080717191b111504021504090e031309181b05 62
    0x81806035945070301c282c034024200a9484091418014640301081c021b0b404018003000d001c95500703140b69241c980d04d0060380b130f0802100c1c000754802400240414400303000e0802c440040c420b0049080c0f90b90b100c9404400350702507084410006038285500c3e0010800c0c0021035a0080d024000b9100c00031030441c02d0501501140d0819074007940001005000c5062921810703a0044135800301020011032400025160b10880045a10507100100c00e1441903403503241c072281940d0428003141040e42100406905e8120310321054030104181c441c002e003050f001e07003007040c822150f42d80c61040001d0703146543c2905150191802c41030243c00706840c99211800c0c401d4009442c2c445010fa07246030300d99400104210380c0410b02003034503001442d3b0b1085400322050000d030030680c1224100880c01c1180707e0f0703119900903503101d000e9444c14003c04881902c3d0120003054842020075201030710315115074500741500c10200c141c0d035068102c41c80d0768022810030036004c0e44d0a03c0800642d440d180c2d58000041c007031005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799737787 1250 799736537 799736573
    0x10c2c0d2405041110080c091903050a06150b2505060a14090a051203041109040f020f0d110f01020f12030f01080106050307170a0807110f060f0d0f09 66
    0xd21000c0c0000d20501134690151010201e034690740303c0494010003044440050b288903c2d108007c1061078066a8038034041c41d0383c800713172002ca1100d5681ca00f08190b07628444101503440500c2e00284003c0300b2503290301401a5007503441d04a142a60500034480100b00034800c18054040030340441d000a10148084c90060401510200d81e80600c8000c0645840001d415504194003560001000500100c0c10076078440450506c503480c0e990341d00304600740c2c400051a0503440341c0c1c150100010881044460710905009030b80c82503036808400d0601211000440380940042600010340c0401c0c900301c00c0954101c403040c8140d40810800341215446d08c20003480c0f501c4000004800c000110190800c5503004002c034000a1141c41e2929010070384441690145c80060148000310344c2502c8802c100c0c081110fa0703c140c03200d42c0e0b481c1c1c0e81005204100b00401c8030384140b116800f0301040d0f107004000c0c0c44a80710624a09890310726144503803401411004080d944068440500350041045845940c2080305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799739037 1250 799737787 799737791
    0x204030f080a09050102030c070e0402030f0706110c0d0c050402030403090302030709020a03050f1b0f040e16021b01080c0c011e09021315030b180708010c2c0d24 71
    0x42d0ba58040c0c9204025002181194000e100080c203000002030940e0444082c1c2c848400301c0c1e00c403800031030709100800d6012481c52082000004686a101c0100440d030118003040d550312120728030030800400d040c200090311511640c00180140c1c5410b900031604a44641044858075603207501103410102d1590003400da995000c2815000250140903007a8010705e9120800d00e0b5192880481001c036800404607004210081552140d40d40f0301021100942481840d039445440c00c0311200f2130a002d0081c1c003030700602903c602c2c11340510082c10070009400d416110141c641c0d507601ea1054241e04104444002c0e50348600954030080d0105407420b00700c004481d80815110550b00510100c0b01e40c1500340316500703242540100c10040070104030b105882d44600359000c681c44000810300415040400c201490180f00800900c004055000607981032f25034464002c92071255000e4201d104644140524502c80c141c20000a031802558a115842c8500c038484511000c0607483d180c0300048400200c81a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799740287 1250 799739037 799739047
    0xd0b0a141003022508072a0509090d050a0c240506030f03070209040f350c0304090207061b0909142701110a0302041a0702061204060204030f08 63
    0x41040354110381c0010031400d09628000785401d0b400c102001c410aa0340249a02ca810b45041000400c111480341e50080c111711b011002d000c0399901c4401c19659886a07010181e0f000040b10300b040fa08161180315504090031180511250135205030b0b100c0001c0100f0800c02c0340440000903980400107025500b1100100101b403224000ca0303080300d1005d0540f81c408c1d4041160031103c51000011201c565030b0581da0711000f85c030303649005c0000e01d200d01c0c401007010b8055010114418008001d00118044449540350b00c5050050710f100300c2e2190400c010200d403c100014802400c4940060146500c02c18000403108442074042c2140001d14100d840001c1c40e8010410900955000380c80100b030041c00114041d041c1050881118421349202c062640c0020840300c1030858203502548651603c000000d030795090b8041e0041c002d6029008282c480902e8000070b28207c0700340c00640d9155035028203c24549498030103034400c0403400401c2200c415800b000040000740070781c81d5204246109a113401e44803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799741537 1250 799740287 799740289
    0x1050d051f060e040c1803120917010203060306070518010c0512040f1401020d0c061d0304080a020a0e07142d07060b01080f1513050709051c0807080d0b0a14 69
    0x40c401c5103513850300f003000303100031a00304896106c074050480741c3c04461f00c10020850282929500c00720351081500c030725900056200716806400030741c8070300e90440594513141c1d180b4105840c18007c1d9050640150315544146005500031860610458010412120140f049002c06030310345d4400d802895909404000400000e1501c01c40c010030394809001038501c00070441401071843c5940d840c0900055160598800300118100041d80b000d00d1410980755115111600f20741c1d10b24205000324050000b42100003a160941c490482c090b1b0140c0c0d0b9541d41001c9229041c00c11074100344a21006000c0c002c0c0b000e05030b4503901e203c0c1003411020350145510f40480d030030b000c011038014500180c18401010100a9022007190b815036000f18801d0100c0201035244011500c0c60320803004407138040b854541400030b82e5801c500d0100444a0859490341d80c4440e54a40054042d98008024100d502c240030810025102002074074200e151500000742e090344800010f02d04041039403000d121340d13201985117030301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799742787 1250 799741537 799741541
    0x81b010e190806100e060f010c0b0403051c050115030b03031207080a110c060604110405031506030c1c0605071b03170c04050d020d232a01050d051f060e04 68
    0x2008808004d1410268a81701c00c035400c03008010300701e5100f02001482101141c1c0164401c5000641080118117286440d203400741030f9600c402013032540e1041d6850190740031002c40c0100740c140c9038000303004030300c00344a650181d014005090b00c5580c140003e000c08607494010030f80607841a04640d4400c0c01d82c1c20103d0043d000c0b11070614103c40100e5040241c08840c80d000070b8202d40049041c0c600040003da071081d078940c00e020700e800065041c06000d11052420050503c12402074104034140c501c02082c07801000001c0100712688808200c0c202c50305004508070b1380c09a5442074032410800304041e104061628643c504000480100f00030040e0b00b02c0c100c082d408019031000c080b807805864282404009010100e0701100244140c0c1c15400300400c000307140c1014424803000020110300c182c0405d4420783c90f0070b0b1030309891003d00101a10404c0403a50403081c20502c0d0f4041c0c64003442e01c0041c084c160054403004202c403000c2205601c401000800075140c400080a02d546e8412010010100b0801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799744037 1250 799742787 799742791
    0xa0203010e07030c170613020a110c09101a09060d0507090501140405060c01020d0e030c010e010b1503040203120f0901030b0f03031c0905011b030c0801081b010e190806 74
    0x2c100b40c03400031100000354006840d100b00640b440c000360071603940d81001035000000802040703002030000c00c0c03407808660800155014201800300350340741d10081c0403e01a10180c2210070383d094108000042000220781c50000c004016614410f40c0b626251402241f81c69105070785200d9519503903001c01080341d600c07000c25000341c5800d203032803404a81003000e603141e940264044c1078030610001403a8007049a0950443e0749105542038184030041d84001025140c1e0071040001e034a42d420840c1c000d24403101886000107900c80180f0b40110818120911409500700420072601842400700005000174144060546410080459951100c40d90001020b40d40141981d9000e0342081c119414213940101c01c0d500c04190b0600e619480b04400b2803303001a01c2d0021340608194030700a1402c2c0400c1404071070714494262a01c0901140944880c1162141c070240b0424620760815880401e0310416241003031404081454011018820040000c50084405e90f40040c4840d44885c2080301036001e1094a13 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799745287 1250 799744037 799744051
    0x804140604170d0f09080406111f0b13050123010302070206091215010305010207030806190504230a05041101021516050d0e01061811040b0703090803030a0203010e 72
    0x362801c16646100e5605481c0000b0342c0d5400003c01c03075a0468081d40d110191100c01c6641c10b2100280342d041841059105008060024404141c154031040001138202c4440103480304001c4c0060780440c1a900402e01d41075810740c011825889148840160700606001e0914400111540740e40c1d942c40303417080031042d82c01d40c2c180b60061020a0150703407041d041c1ca100b04000e81302c801c900490b0103212414400d1241c420885154038000100501c0340c15400b411500c1d20030f45550f80c0c0ea888100420070200c110303510241c0168240c0c8002c1c08141000d81040f1300c0d0700d1024102c1c03404003054030303110b120b8150700721400c2c2d5102da80c2d0700c1000180041c60620080e440c4080c00603141e601e040c00d07003406041e84c00a040140350700f00d808c0761300e0180f84207a049980f06e213403c501c100a042140c0d210b10b4041c101c02d10450584030401101d000c905605ca1180158602c0341020803854240340840d001c071550071171102a02030140206002640050500003035204407454200169250f04201000421403409040c078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799746537 1250 799745287 799745293
    0x90b07030f0e0f1506060903060f040b0609040803131115090301060b0901120b010c02121e0c01020d0810050d0b01090c210209040e1b01080c07030e0112090f03080414 73
    0x1558500c00440d408000f05030b0040484ca003641d0305008140340380b05402056401d48283c800300001e400f48000f40038040d81c4034010f0344080e91545410007111290a680103040e2607801c03c04510f820f0b91108545880e070348541411541180c449001544030601408445481800010310112505d03080c401c40c0c001d08800501c16082c6416140002e20041c0c00e00410104d4554500c882c01040c1c0c01000312041c4994002c20f40305040d04501c1544d919030b09602c00842c1c48070003845000c049041c02040401842d00b040c0d00428010441100031510060090711840148e090b10501003241d888124013080414014004400b49515082041080b140c0d000c00f200108111801a1420100c82d005040e4007025142400340c1c440c059000040d0080818801151280c03040700040c0f034404016a480400402e026213a4541c2c564030030451143c280700e4120002c0008010101c1d44102d0340c05034107490b0071411241400190005259621440d01a13001816804660002d0410003001003140040070701e6030440d07005e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799747787 1250 799746537 799746553
    0x90302120c210d050a0302040f03060204152a02040e10020a02210738100e040b071103040308040315060b12040213090204021818040c050112090b07030f0e 68
    0x4141d8694018183c51020800c0002d48288210701ca50180c5024244a0385074100c259620b00d0402d000f075010340701d051761800c064488a03800501500c0180d15045011a148802e80c0301942020b10791540c400d01241d02560302e403208118104100104501070468a00059403055030880103442e0045811711000b0309070440801d03036001403800c001c0c1c600c0a9032080410107a0f16121001d29505448109441d000d1104010f43c5e920300c5822003030183c0917001e0b80d026140300ca9140c400102c554042244c01070321607c0001e0200d450140704203226411254518292810251644c1d5105040da001c0c0c1e1068641000c06140c10900980358401c1c3c9000380744401d03c00e464480a04081d1164460051000c0d1090450500401500e103081d04901d24a56000300110f54840714892441d4000540119480c01b07003150075035a40b4044680344056005603041281d1442d082d25000044603840a41c1d000e0b520100e86900300300b030004d111444018058080d035113000c200d2011038004a01107803c048006803490b070144007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799749037 1250 799747787 799747849
    0x901031101030c14071b0f0b09191802070308013c080106080307151118030a0204020d090201020c01050a050a1b080307080f01081f0b01090302120c 65
    0x10621450031000e09012410000800c4103841140c4100c0d046401204006030710303410040c50003004001d05190101903420280c6408000303000c1d0842d4062050aa241001402c50340c1c41c000c00d40910340c0b000704016061060711259036603072a010f0b0790750f0081c04ca0380104116041542086260340900220140325061401c403d030b4000440c0000c091074908400300030b090280c400ca00f60340002c0640510130081c000107640d14100e941c3d907032040d5420f0b15100300000c460a00b0f030b0002d0280401c4142d034650140d0802000c04661700c01005904152980351090080d40c000607180c900140c952071201d131200040c140c1490001a09240c0311000c0d040c10410300b0011054440d400406464140029140440c028020311506c6012040300c200040c10104000c42007101003035011114501c03070307548c08400c45601c1e40e0711455907544d810118107614080c0702d40c4000201702041c55205040c4240140342440116640b50003052400016085036411038001c0403908400b4280008a00c1300021150790101058101407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799750287 1250 799749037 799749053
    0x1609060506090603060d050f160911030705120705071a0601030f14012102060304060b0a06090b040b0d1508010c030b030610060e01050c060a020301060906030506130b12011a0a05090103 81
    0x3008a4801e040203801081448810448230244100c69412190a9241251400c01d00315a620a00880318144010307549080c0340c88042ea4082c1550b03440d410b08101207420030500e800c0009045504001d0306000380c00c04100002e0004000d010303c14210911800c145000406a800f140034800d2410306100466500c581110720043c1111200d03811401680c0030441c0300341000e55110006907100501005000900419038818a041182103802141c00381c0d9803001501c0c0380c0021b200b00002064140420030400c0741040c0106402c1143c10b0300080d00d900015031148043c419504082c16580d95101d000714160381620030080c05540031030003403100c0d02c0d14048002c00d0500d5802140b0400c000b04040a1f80c0b07900480079141c010040358151030103450a81c1882001350024803401c800a2140341000541501174440d15001d0500038041c0c281c0f03102c2c00403594020740045592283c122101149050280f0000cbc45411a000c1e5640f40c4400c41c01400004c000248010f5004148039420074001000011020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799751537 1250 799750287 799750291
    0x4151d0108150112050a060f0f0b0a030513020d05061f0b07110118120302120403051009240f0605040b011209050c041404020108010b0c1e0703051609060506090603 72
    0x4030300b0500c086494200483d00001c4c0802c01548003420901408103078000da40200007910a0b030000c0c40f03a0320381d98031800300310b046041c03080d001c00500410100800c40c0c8a6005541c4c860025103000e101130300a5404980c3d444452207003030f207980d00024248840301007942c01c0c1d040d070002045200c013000d506100c01c1d402144603041004240e00011800401c0c140d0050f00320710181c0d0545e910b20080540d1b107250014041b046058100c2c0140100e1491a00c800c01200a40d41561740090061115013000c403003280c02000d4540058a14811071130b01c0c03201300403101501c400c08502c3c491010509100103002242079801c142c010078400e0741003200d0f6031640c2e680222485446101048041a8400701d4141541042c0095000710b03001414445100c0350003507540c501c58002c9200782c1c0c030603641d607a0740c4090b4041070080c040000142c0d00700c44540340f00d00308000140158241c0c1c91090741c0d040c0355a6590715182c110180c16010345031324030360741c10081102e10b07100741002000d06072001d078a4600b2200000300c2340c1c800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799752787 1250 799751537 799751551
    0x2090c130801050106090e150d080408060105010516021c020a060f0e040b0105030c18100801031407031e080408010e011b051801081504090b16020c060405101404151d0108 75
    0x3004001903c90802034a804a4208d400b0301100380300d102909010305240c0c410b000d00300742e0b03214000000441c0d520074021107000140803031007007890305072035800c01c00c0983c000400700b400d10000002000c0580c2d1181400700081c2186e0712880d401e107017900005003c00b0704c01682c40e48103503d00729044030645d03000022030b81d000c4101c8400640e9102441c0750806c00a81c1d0501d0190409105143c00c010345400c162024140c070b0040e04960081e803040c00e80b00340d40785040e0100401020fa02041480c2c4c405000c8000b8a5051041310828149500d8000041c21100c2d403101d03c02690b91506080110445850500c000401e020700d40603181541404461914a80081c08103040000610000d00306e003075000307106003090000070014400100380341420b20362410151402c03031216a8070004000024000102110301c0d020103490170341014a04000c01c000540c681e100b07407040c00403403885140c200045100601c00740c00802d0245100b000107840080c4400e90000c1103035041c240404a81925a800003282548040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799754037 1250 799752787 799752809
    0x6090d060e061f0b1215060706090501050103030909020315120f030c15090f07140f030d02011413020904020f0406170d08011505030a0e16090f0f1812030902090c13080105010609 78
    0x1b4a0021944c14460440041c10700ea14103110602046010741006049a01a564442c216a00d4900040881c4801c1d00d03640b25802090704160010b05020000e11080240401a90b00d90002d8010302400c5912000c000c28180e081507440300500c04d400d031141900082c0d07640c001c1462040140c0000c0da103c045006194010015003c04051956440400101042c0150070b841c0c8410301254082c0c081c04411542500c244002c3c80051000c0d40018110000250001c00c81c0490b62100e409110001040b14035441d003040d16a0f41c0400c204108200c41d01c2442a080c0c010700c0d88089070040140410b606030882c10085c40480300c201180b0764070509582d046540b00f0030026003007840070b056070320305192004801242d034008070700044c2e401c445034492032010a5014007840300312100703600d242c21682c1400c120301d414a040b15030b04000c02c0312002c2c20780c07069005090006880ca440c2e00001e0050004036a203107103010000070250b80444140d0001001418040d000344440d506054020340210800c0c00380c0b0603011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799755287 1250 799754037 799754071
    0xe0601181b030e0a06110309060a0e0709020d140108030d230f190e031b030301030c03140a021804050c010c020303220509041103070f0506090d060e061f0b12 69
    0xc04240441d02155178428803c12401d0f4600d039aa8485400440740d007a40e6009040000c0c4100305a80504203900f00202e0203000c030141054000b80094104000000c4d070141c1d2401c168100d000d100c0b00341c5018101c2880250785404c4030b4041d000561301d554440502d48889103030160b407200c0080070402d1308840d848a403242035540b04140802104269400c00c14a5801e040d6500038444000c0001c00007030f0300e85087c00ca02c0300040c030001a42c901c02880700030031010710752004002061185000050600e885800d0f10000300c01c0380c0002c1c152042d50060003e500d0449418882040810400c280ca02d0200b82000310707040c20716400181d164001d407070b001c02d0315054082e203501e403114601c003402000d084000c10001d1241001d0401c805200c07910321446001c1d01c208000401c2d4241303000101d80c119100142641d151150351814088908017444044448507114019101c84038400e02c141c52240d41402c10441c0300941c8900e149540241d15845158440c404008118019046d0303404140d010101520501c00c003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799756537 1250 799755287 799755311
    0x1140604030f032f0c1215091204180b030604030c030e040f06080c191a131d04150218280303020a05010c1d040902030705040e0601181b03 61
    0x4500c42c0710121040700110341001d80691841070209520035010707040340c0a0321104002d2104540c810341180c03010346d2100c0e07102100205241d04503a800703030756202035603140341c2404190134894000b2f410040c440c1c0e981001802c05c071500e038400d00d602d207081100204013604064401414002441e80c0143c00c024890328805229140c64020301e040e8a0b818008006455445589503203444281901909c02d4a201d85018036800b0b0315113801e0240c0300124030303104c500c81000c14001900d9003c0030783c00c1d03011200442d0014400e0078a00d0a0025602454040a154641880d11103540643d404104468601c184681d00c8800c0d01240d03000481d00068030744e01c120103005915840c0c0c100b480c5c3e4030000300e48103607000401099808100707150b03d98800c0d4001e100840802e00c00751400f04c89008084003400f107000c00c01d4042d140c250819180f60f400a0241c420b06a2034502003000c0d500c64503d20380856114600412180d00aa001c0340f0100807500b40400a100c01c0c80a00105003924600700010140c441030f5029003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799757787 1250 799756537 799756547
    0x7120f03020408160302040b04090525030c080c190f060c0f0c0b0715060302130f0f020c1b040212010509070e0402071208060306060a0b1605100b030601140604030f03 73
    0xe0f1010320201c800700c0648980c07000703104003075000403805907007001090040c90409028a1002ca648400030b0b00f421100b58a10700d441e038031000c1d0840f04031150101c002000c41e64801e5140d02801007000a4803075051079606214610300201488078100780c081c081000540312022540c03042d10390750314042c81d0b0340c105402c10050f0140210406888480840c200041044040300101403151080c01d41c9454600c0541da08811210703244000b0350401c40d8640e1070713074440085074080002840800c4000980340d00c91f002142c100c2e04450039004441c3e20a9211401580740c40a1400c41c101d0300b29429854080f83c03054039100b514040c0302c1d090180000201140e9641e010b002003d0808401030700031522942c5d5814038014040e007100c4000086048000800c0403800c003c100c0520420000e0244080e10345440007071083c50f4050003c42d51040b209032101c0d000100c061210401400c42d030000801e00a181134209428040c06034440304148240e20003108803519003c040d6011690051071414400529080030750f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799759037 1250 799757787 799757789
    0x2d0806240f0927011a04060503040b0a1506090f090b0a05040c0203070512191704030f110703060e06011e060c030306051f02010b010201090302070509100305060a050105011407120f030204 82
    0xc520000015443c0000070032141c03241226030160340c510151184003400358407803103503000e010001402080000c01103503d19010321f030006410a80000c4800740c0c0d0f0304444807050b0755080386001a6102c0e000300315460140304013402400034810200a22500b4070002241d41e0100c1c86001e02882d00e6100c64600640240159911645c1000603948400252100e04605500c0003014585038000c1d48080c0702c050348607002c9030000c5c08030803c541d0116191a00c0c00d407042c0082c1a80102084803100020301c29100034400c5e4002984101e102103850307000d815000d4103010301604180c1c2142074030f00750b001c0b80062510250703046400c2402c200b00c0120781800c1c114043c041640217036400c070101001070550200c0d8000c030490300300890390013041900716000c012800d030364111901038010303440048280b00307602d0075041403070300f2001d01d654501e0160380d03a60703170181403050440b05408859500c1c0010022540c1003a4800c804a140d240a07a2502007166282421417540c224020208020420380010b41402075040750 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799760287 1250 799759037 799759069
    0x20102130906030507060503040807170f0f0c07080a02060a0f090504090f0203010c02030a0e0603090a1a010e060907090303051303021f0201140f04032d0806240f09 72
    0x60303241601c61800c1ca001e403031140702c00c079030512955070009036040c03058040d603005682c044c400b0340c5010010380390391240800400410042c0141001400d04000004009245484010310320640359480c0c45615401c02c603081c0e2045445811910604005907600009c0791007a03d01420300c24a0018942402c03545844c440d0001074010f46841d0000052100b943d00a04c2518400c9000f40440009484200d03100e0092050039004942ea2000076085483d1000156900c0f042140840b03410312820b0322281c4110001100c4000d00158410040c8668004140540d41c820000d80b851811030070600e000504080c2284006400c108001c501d00c0100c8145011000085070000e11102ea441002c4005c240b021803d411000059880c20403030100c1d5041c0381340300501c41c2407081e078104200e85c0e4548040c1c4005a107038420140810441001003001074a51000900c0d0040700d688a00d800d180200178840000303d00b40c501044040005245c00d5043c001c1422038502c00c25401c00a03440d029004003260ba1080190300391 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799761537 1250 799760287 799760317
    0x6060b0316110c2b050a08030603210a051c05150306010b0406020c0105090f0a151206050607030c0807060f0203010f0503151b0c120307090f03051b0f04050a09020906010f1d01020102 80
    0x144041c00642c1d00130f18009d540031029038440c0a0380009418002007089600d000b42c0409010456096015a018040519000e0700070360501d00031401034803c0300c000311000009550000d119010900b0300300442e6014100407c03a581c5024100900a540c4070402200681000740008111107540c441c0042d00441840c0904042c00427030322022000d404002d052400d1000800c20b42c070b0009030b03c0c2c0d180152801c0710005010745241140c81e8808035045000307031909580600040000a00095540c400c00a00d074003616001a00d82d41001c6943c1184086035000340e110781e00103400c42811070342c4c0d682d40325009440c8007a444040800305601c0c0e5000d004109011556001e1012580030020445000b94401c460b00e03626000c00302c1d15002101000103079030102502c290f114020fa14004400d001804440c800300810b0703038a01402035000181910001c5405041194442c2c0400045040900e001c94110f0424206a071602d688540d000380400980c0003038002083e405e010b9040a64001e50445803035089036004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799762787 1250 799761537 799761553
    0xa110d02030a060f0c020109020108010b0d02130b04051e2107080d03091a190c050d020a030b03010f050606070201050d11030f01170312060d06060b0316110c2b05 71
    0x1c50801013000003114078079182070981140c003640c0306100b030444465058503800896424150846541d4025200c41c000321030b401c00014800b11062886c10005003820210a5a102c6c02c2c2005d12021600038203030f40c084880b180e804917485a4a81415420394682c413a2a1310103204021040c0b850718090351311400250144580c4400d00c258141c20468030a030203100c07907041c0411081503007281401c0490306440480b05064080800d00400d0f00b2081c0300c80d0291600500b00440c45952404a030312240c20040400e9a07400000e1340c50a0a0052803000c2400160800071072a12201040710341c81144800bd0402100069003c0151030710313441f1003602648415026200d140081361051420400e00480301000c03c105048241308000100f00e81a041c00c40510300d820b03868a9003401081c1000f070b20101e81d07107900c41001058030400100550312a40c0301800d061907071462824064200720080740205078503080b0780400314598451200c0c001119a09240c411080340c03000d604140880303640e001c010414003400700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799764037 1250 799762787 799762793
    0x2190e03120a0504140907020d0f0c0209100303110c01090512070e040803070206090f03040e071101050f070905061305010c031b0303052514130305010e0a0c0506030103050a110d02030a 81
    0x13078001d444040400b44d180003240b5040001c6201300302c0d01c2c000140d004a400044480c030807040d40f0145242c5003040d00d07103e012603001840d11071040b6580c58034041d2030007041003030584c08140404e04c41ea064001c0c3c908201d103240000d01c1c0c00d0b000c4c002c03140640c0d981400d91209500801003040100702040d40d45107a4106490080c2055005454440051082e07601280c0f0342400441d104802d1007800300118a0a842c18180131010403008210a007400010fa190880329482030040030b00c03486080f01340030094907094002900742d21903a04528013550061210307148640417008034205552007400d0042c003140c0146011158904d0031882e0300451424003548030f08040d0142c0101d401080c24103600f001e02c050580b112402c0405040050000a420040b41030440d20b00c9030090045000d620202d40c02540c6a80b0341c10700359102c00384280042c0e4401c0d0700303640c14440c207510004041c0c00c04076600340c615451074568603910001d0360005484d425406401d81842c2d90ba50346d440152541c06415134103d003040703007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799765287 1250 799764037 799764047
    0xc1501031a070216050409020a05060c01090303061e2d060f08060121090503221502061006050a0e092e0503030a030f020405040905100c0302190e03120a 67
    0x1c880c01400c030000750042800b050010503007000004401305074003d03a07890007040002901080302c069030401004440070a10b501d801004002c115040b50002c180c070200e03413400400f120050762203424140d032403900d24003074030306852a954106c800707140d0080c0d01800c0348441c655504589801c548150341400c480014034507044a050078110340300342c6a03003140355600001511421801d419102d08141a00c1c9040245c0255612504815001e00112404c00340962210020321100071200940c580d030b0001c0c2000701107489203c900c0015154800307064107023455a0009113810050144605002000c00c05a8042c1d2044141e080b81980040c00800c0c00d04104402e5845c560121480340c5450040b40c41a9114881b4001d000c402c440c03000d0021868112800821802040201d60702e502560b02004009115580ca00996009a0060002d40034104444180300c0403030710a051302000340340c01404a240d00e11240c00700040c264556040058541d09808000fa007002e0007006031540442c00030a28001565001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799766537 1250 799765287 799765313
    0x3120901270b191704121107030c0807031419260706060503012f09040f060e06090f060d030c080d1406040b04111b0f0d0305071b0b010b0c150103 64
    0xb136124005008007452100b01c00301d500300e5014100c1c4150540c524559407040801840c21443d00302a925441e4581d40ea075100300100d54040201075004060500520914600c0c03002a40304003c01809002413550541c40403407200c01c1d0281012038540304942c550003c20701003480001154400070381d10f0250389030010003000707140580c40c0290310709001c0740e500301d0402c1c400310b50610704001700c040884081e00d090202c1782e01001d48107400644518004588004034011a80900b01c4044d2050380352a207841030000c0182d0042c4210004031880b405d00034142c07118018894820307010300d003a4500c04403600b0300c01c4030b61080313041d1070010030328140c00c482d201010f041c00b980c0100003c503810701c0b0202010080000f0766001240d4100d0101007001200c441c0c050030090f1502c41c040b504242d9131010715038207240382031410705400e490120b07448004002c0c99540c4074440c051040901064400c031452543c498020800c414026400c1d5a2800590400e41e410100f0041c10309000d0b9502030303035542d03841b407a10001440c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799767787 1250 799766537 799766587
    0xa03170708030a1d0303190209030106050604080703030e060f031306021603080601110d0801090b0109081b0f0406060f030504051606020a1a07140f0f1803120901270b 73
    0x2c00e066031030f0f01310000302c200d034000c507541401091b0301c00c21403460400a5011003d5590305641e2001d0000305510340702d014000411801d8040c000385417660401503c2c11408103d141d119076020415014482c0982c2c0980b50010009103691b4040d440700d241c80c42c001d01c10a02280d001030f810f03200351410036500055181c803507030342a0380d5550b131a1201c0c210310355240300c808403150105a49100501c01011942d12040200005240065025039150304480c140014004d142c2151000007580c1781b00c0c0c0c00d040d80d078000c6521003030394104500ea02e020710007046401012890b0003056100d5001c2814481e007000342c18022201c4001405190380d40c1c00300a13540307507444c000031250903540740c04201044554240261058000303445000103210405400c001c10340c00040d03000c0e0102014001103812100c0d8502902c0c1c010040310617140c02007060f400301450b0100403011070001080c100034209090340c1c080c015420280c0500a82d10054549000300d10228400703401c650380c00100070481d410200b400b070380703001c40000c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799769037 1250 799767787 799767821
    0x190203190c030b0a230901150f02070e0a1d0f0c2e0f14040f03150b010f1206050607050c0a0e0106200313060306090b0604050a03170708030a 62
    0x4207001055055546484105a1110314034104109111000c075850781081062503224034405000c1000400408003030704100340d010424401c940400360054500032035140b0500040c041c951804a040b104074100401d8004041e0700ca04041c1c42420312101c011442c21822002d8400c010300129034140d507075005003001440f50348000d84014041c88a61003925991400054110030340008140c1595541c403428848000c03c0510b41c50401c180444c00080c1025103403402c810107003246142484010400300c202018012880c140d5003289980c3c0040380c002c402c40707003810220214000350b076440c0005d045650019410200015681007009004101040c2ca4101186c103c103d441e01d0743d41d0810100000d0084d400031944a000040c2c0c0000791080701e090504200044a00d003010680c40641e050401e0341c07000e00800e40f107140c240100c080500500f02e0805095800a081c84d290200203420340103180700140c2500750030400d000c1c0214481048400f460740180045541e0300300100b1460040040444600c0508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799770287 1250 799769037 799769051
    0xe0a051e100b22030b0601091a090409170a031d0105070e1005090306010f0611162714010f1a1e070b01060e0a05090114040b0a080f030309060c0702060a0819020319 72
    0xa0300c1740c15080b49ca80c00e10340c010350030900300e0301c00e0000601004100f40c40f0401e860051080c80e215000c002c020010b003e03907004c1222503c1c0da5410201c4003c2c41000c0e481e90341840200200680d01084070f900c0d204c002c4402c003641c1034248105540c2440740481058050180c1c9001145250900150b0011901e0075641c00c160078080c02091a01d03130894403000c0340d0941d214041003101d443c05050710703500c02c5400c2400f0080300a60403007050445100200300d05d00c101c8100d00408c01214507290130002015114100d8005c1600e0410a10180c4500d00090300e10444c0149004102d1a1031015600741c01c0e84000f07060304558540b04094218003005130b480e840751481c854049564100749080c00e048907111286400915030910401014044944e131042d0465a03c240000e141c040400001682003240c1c006140c0ea4140000301504000700189940001c03801040410016101c040031280d03098154a04424a03481d81681c540319030002110103c11b0600110a11065902d410000e0b114800c044008001c03103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799771537 1250 799770287 799770299
    0xc0313060903050604060506060d0212090d030e1510090c11160501050307050702030a05030406170a140412110703110f03010917070305040e0a051e100b22030b060109 73
    0x614141c04010f040307802132000b040015105401003608401c00411540c1001502e5004500702d802c0800314032003000024050000040d0b0074041f4070240919860240040080b00511550b03a031130300c5419403249201c60b07000811000da0710503458081c0407801d800340918510080010813140800c4c030440024047d85482a042c01d00c1c0341540d008030f6006844031030030755035526030580d4a40c00058090f81c241c00782e01c3e91000051014401480a802c050b1550030301c1c002160040d03010b400000b070000007028030385000002d000d40e0101c0219445a84181c0307081c81c1e2072003050300311140007211000e0845481011001f104120360100c10341000102541c1201c41d8009002c10036082c1c40c44240040c05941c50100344240c40b48144d0010a20381303000e828001d103050b90f22980c14511100c02c68040c40101da4a42c140a505c0c00048500c0380101d0899080000360b0400c0c14190700010441e00c00d00030300340000510702e10b161f80c0103890078190b01e00d89c044490742142e4a042802c034030fa400703c9441c0c2c001000f820f03002c0b40d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799772787 1250 799771537 799771547
    0x2d13060f09051603050a0e0706120e030405030a0f020d050d0e0907030513060f1e02090301110c03121e0403020f0d090602030d05060a030f05010f1d03180f03030c031306 74
    0x208105030f0012050b55007802d0020380040c00003511001c203880c0c40c0c51219411030030400003840141070350341c2e6481a408552220300b040700d88880b002505900b04000c104555900050400d0b40381e904407054240b0f510182c4000307103540311542002082d40c0182402ca244841c1c0000e6246c50341103050b14012500d94422408030300f00d8070211103c44d03017a91442300318004149150300c000e5004840181c0069001c1400360f040e544122030480380c2d11000d4001504040e03c3c1030a000b2407200d1140902000d0806e901c0aa04a80320f024420420714080e40503030003d41d0300c4121401e8100144115010005c203410b01d824000d445a820360701c442c02d584180146000182d2160b4255412034401e58041c41c24405030003070581c0603010140400f036100f06040c030080042492601c100c003165205500009611542c11f01c284140c0c1da907200d10300400000000001c0f0190000300440e440380d52250180081510203100052110b01c5451503d034041c40301286c60200344070000300908084408580701850203030b83d584119a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799774037 1250 799772787 799772791
    0xa03020a1131020c0102120402031b060409020304020f0a03050d020105071d0607111f080a05040320011407020a171614070317040608070c022d13060f0905 68
    0x800340002c912151094881c0e5550001e0008003400b0141c90440410071403402c3e41c00041624444004071014441186002c02080c403480305142d905091501c40036001440901991290703c1c1e1a80d00000001c1c1103682e03618013180030b07074802000a03490701e88a060055840c4080f00b103c01c0950329041c0071903507050140041c50000300c401444036400720b4405050085517080f400c0c007142c80e01a40b4117003a1040d55001400c4c407002081c0013031b405804c444440b00a042039800740c003101c5401e00e010244000700f1b5004010b03005200d03002003211410500c40305054018204180c0c0c04440d52102c0048c80140b0780c3c0840e460101c14080c0c1c0c200c038140f19400c44061014403510b41402070301301044203620005078100410005048001d000e4409842d56038442003100b00711241c130b8800303804000405108803a0402681c58104196241c0400071000313641c04600c1c401d000306240d14281c00c3c015407160181d55003070308400a01030080e02c04c2480304070ba100c50001a22140c003644102d000d0341040491000e0f45031003054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799775287 1250 799774037 799774069
    0x7140c0604050d14010c050309151632090f06090906120a080a0314090609070915050612151207060305040309120c060219030e060d0e0a03020a11 64
    0x303103014074020803c450810002402c4a281c2c812080c1d62400500a01c00c1d0807988080da200ea66480c500120a20309000c0350485c00444507151307400740314214801c44c54000941e00142403d269217014100507a044030b1501000d0802c4050481c02d6a0541c1c00040240c203c00c4010b54038900c4000070b6004001e500d000340c0507555041904140003985d24980141d0000350080e0050544000621035103030010b10381d000390220804240c03581d2104128005030712965600c10150f00150400e428045c509d551190030038440c6909580e104c98841c9415889001a01d0040200400e981e9031542484c88140c0200411201e00b920360003450703190103480c10000e440c0062505000080c000240c1043d405a0080002038020b4040043c10700300400d00a002081c0d80031403c0c0260b21a00943e0b01d45040245130540407486c25500320303040c60880002030b40080c04403031523640445140e078581403c00c0c9828004d145031881c02907503100e0404020145900403402c0850300740180d0036011040005c10070300031094041080a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799776537 1250 799775287 799775299
    0x16050f07050315060f101106010e0c030412030b0d030e04060b070f1202010f050a0510060f1d1c140c010e090106200f070f1208031f0504020f07140c 65
    0x9040c250302c500060030381c420b000400310350840c00001d001c2006c000d041035a8201088102c071240000e00006c00c403013401071401d80c2c25500035240069403103003140030142c0000c01089007103600c465901d010740c2101c1901280a401303804000040d0600401103030b01a50a21700483c94503a01042003c66482141c10490700580b0030b84a180441d0340703114105594614030307401c40d540c41140349000081230050b40d015000f44140400c0d5401c0118030076610940d40c2e80300000b84405032440180c0244c000c03142c2920205010f03019107401c0c0108010030000441d0000c1c00a040b0154101075042001c08a103c46001c50310303904440310707661102d00668091440c0c040741540f00400c1c00040010350301ca040c103480d1102d601c80320382003407242c2904c02528100040d070880b8555005100c040c08400c01e00c205810080506020550240c02d50f51100003491201805095203403940b030140207032a04400020030010300d4090001c540d00e240d0080c0009031a040600c04a0343c0c0c100781c0c81400014000000d02c0310b003aa0b001845 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799777787 1250 799776537 799776553
    0x45061802150906070311190c090e0c03100228030519020a090b03040305090a0f05010f02120409091b030312050a09021012140903030609100f151416050f070503 70
    0xa0362200e00d50651b8004600c10400b030703a062100800070a00b0b08604ca42c0e10300d5142d40c101076085083d0b4804640920003076024017007800e0142d600061881000c0c80203100142d584005454507285002d040c0c03420000c2019035441e894855034141d001303910a08049140a00008140441d103050744240418040042c007800340900201d034103d0300850700140b003800d1046c0341000031004940300c1e04181c1e22015098807180c004201a50b0030010000da0742c45148003078041c01c2803200d0981045d00850003081030300388d610410f0200b0804040716011075540101a240d09060f501c1c83c0c000e11214507240040f030f91904000104010302024052103061650081c5078015101c4000340444101c03000902d0800e205803281100c65440b20101d070070382e0103800d811020703540d02d1808034103020407240f02406182049100e04c4040045489050708241510090700500c0302500350354a0403595800e07400210728190b040000d5420300d03030840b038600b0042c0b5407050060310780c0321000d0b01e031407070711108184a4590190000d0413 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799779037 1250 799777787 799777793
    0x61407140307090e160809010603031b0807051005160c0f031202190519090f03110f041802090f01061b06020c150a4506180215090607 59
    0x20140d64010700c9464940002540d502d804c0c0e4032441d040d01c111202c8807007403c00b40d4196500205031a480714090009102e1030740381d0b070350003050680b0b11983d81001e02660140710b4208035040c6e04480000b9000801c85513820b85084c1c10740001d010903034803c20760015410000c16143d0040080144160f00f1070030400c1525580d890541d8821400c04409580f40d5003040072028120324441221207840c00381c0d8469882c0c011190f184008048280845030500c818520100b20301e00e8500d02a00541ea448041c502518102e20003161b00704c01c020803403542c020f040c4404406064a40000007107014001c4880e504544c0b241096540b105100380558030000780c013000c1c00b044890306900c00d401242e01c14a401480c01c007200b0101424030311222030101400013181c0900040804901038410700000c104040f03407203d800c04002d81260081c0540c41601849220881c200058454005060180d08681c0900c9081858480c000d03507291103031001c0b13100d2009040ca80312000804401d6485c038100c0600450f00e08140c41e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799780287 1250 799779037 799779077
    0x12110d020a030f03051e0c120615071403130905040501050708160f0203090402031503120901082404060602030c1203060913081905030109060509060a0b1605010e030304061407 77
    0x149100c110b01c134003101b2030084000510300103105001d803818403a2104500d61041040100c0a003850303102e00c1142e901c414103070f1a56400c5840066100d4400c0c1e18000710900641e05501402d51803850300f0010344000a1802c2daa034120301d114038844c9008002d40e039a03905068034401d8060700c450000e045029104034104e401001d80f0100c00b2031500440341000d07c21000281660300481d03490094a891400b0f440007400c042041d8444510504480360400f40f84000080078442c0050002c010340c0f1006c52003440481d1106441c003000380000d80107220322034850b40003965aa001c100705030318610071140648260103032242902e00804006040f1800c40c4c0701d01145110f14945540140d50100f802c208400d030a4580c0c0d2804a11000b0580340d0a4803903140013400011201181d0041c0d0251000100b0072241c0d9403048083d0095038403141c00c80c1d03110144030110008104c4d01c0840105590700c0c041081041410001c0038611581c403c00d003c1c00101d0303640c030011003490350580701c500114102124040c01d808443c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799781537 1250 799780287 799780291
    0x1e0203060418060f060b0a1403060609030f060402090c040e0627100302150301141003110408071e0e1311091509180a03050903070312110d020a030f0305 67
    0x10004208507101448011400c10304800444205541c4c03488030440c1d5001e4000c0700d00411070f0303035441d9040000d202d00180404003a00080d10101d480007001a045554080a940301040301404540c0101c0c4107408140d40c0d0201500c007680308222241c001190708005c4000c80d0305032041c241e40a01b032034403800c0901c203800d00c0c440030b0441122140ca0254800c01c51a01e8160300c1551500c0140582c0c03480c4d8014020f10041000008000740c50410050000c000242604031004205646400c00d55240e00d800720001c10740400e10710481600007034002856400001c0380425103007160f4550000d0900304100728422480382c8581d0740700300c02500002d4000c100e031b003440101f042d0117003089086012107840066480c10089a0003640800b4407518000942441011203a001e001700d40723442c0100903004d4100c0d40c2e4a01e4100000c04001c2c000400414a407401d025907001545d001c102400c5643c95900040d200703994802c4c1e040e41c18814a0f8945141c00d01c002502101ca5070141c6920000c1519801c084029100c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799782787 1250 799781537 799781539
    0x1e061508190c0915140d121b0228080a03080121060f09110a0807050d03031e050103170702090705090609090405010b041a09013f0204050a1e020306 65
    0x8403072030000750f2420754000c110440324084c00006001d03050082d5681080c0001c12180e000d016540c20600c0003035016280300c01b100450b400c001d29500c0e185062040191440d4100070342082c0c821281d040035240042c07a500d43da607082007071034460b29110248a951202e0340c981c05000190130000400c240d08110210784100030454003886a040c0d07403900c5070f03803d407100c400001c09080da0b1003200106010000400ca040e03204111130003940700d841c141416075940303424002ca82c07040304081108010140660300c00c80d440d401e9050307900c600005c1e50700100c006103403d200075100d101d0721030754404c0740c82034180490342d001e03500038880c07581611804000c80d5190811448290441020419141603035506a081441944075a0000c20702d4800602803000f591454103040b61f01094a80741022590380d41d03e81c0710306403000440c41c80483c58291041455201c42c0307401d0003002301404180030316030070300d601c0c06024040d000781e40510050b00c5118071481103e42e0303808010112020485c2601c0102074680055802c510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799784037 1250 799782787 799782803
    0x70f08090316141e0d0b07030f06030c05090912030a0213050d0605100b040303080c0c030702090903090a060e100c0302010e0102160b07080103170304030c1e06150819 73
    0x9036840d14140107010381d41012040c00d025010516181c80d282c0e07060541c0c04550600fa04c005007404000c500911014031004203401010000101c0103403080d0320450310010b810b4000c0c06500d68078201292810150b00440d4010f14011b000a00360340400120109840da200c4005480c50751200744020080d0041002000904452500018650303601400c1408250207103800069a00304240c54000d40176665001c2c070a02c1005000820100344c209038103640c0140d103500026914014295150304521503004025031021950050210f007000002c05040100010b40d024050f050f1200006d54010076101c1200c0d40c4995850413508165125030180d400c214413900000c20007100c0c03113038900e099030051003100c07480c2040303213081000348135680c00c003142c0181c00c6090000700c43d41591101840d040500340c0002c0c201c20008041010984038800107115641c100c0f103844884c144140b42c0c070000c600ba04105940309420300c260301c0040560f110360003045481260040c440641103002c0402d10580c0d4400c10340e1103030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799785287 1250 799784037 799784053
    0x50117010e0c12071d030f070513180309030302060703052401032a03061203020a0b1b0301090221150411040503010e01152709022106011a070f080903 66
    0x42079418007540180700b582c603003140c00907051100c0d030350503005420324a01c60351140c2842040f40c000031403c0d100ba01c80903032b042d02c01a0140400e10010740003400240344580850000f0a00b810381c485c028505407403083c0d0030b60b129602c0b01c1104400b681d809803080c0300c1d92200e10021992461003a03a980022403010b04000c180b04182403450900d81e905d05043c5440305450a00051000341d16220708809041000c41d91030b041405900c00a40d903041a2000038a0369814502140c000c1c900c0b6840100e001c040504091340d20361b124848070019401018160900050f41e1100d09040711208001c4ae1052030440407001c0d00d9440d00307013000043c2001081140e65041700b0000071178243c80070300480540c003d0800000c01d00c1010308240303405030318217a4070090661030b000a0300c0031542c12034171022804100c8040c0124952219000103101d01024402c0c501102c82c1d21000701d030070f10001080d418100c1e44141041565008070701c00202841c896118020081103416a4800010300200050420002d0190881d0300403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799786537 1250 799785287 799785307
    0x603050705091e040b060f0126070c170a17060108040312150b190203030c1903020c160e01061422030503030406060906050609130507030f06030f050106050117010e0c 73
    0x3c403415a000c2d12450092003c004103820501580d200c02c0e0000c0c40c01040451585a025900da003d409a4141c101e041341d0100e106d45100303071450581e06400c140c0641d124003800008824540c4040016030104502041052030b01540c0070300e41d40300d40710684031208559610398040301c0400e18060300c0010b89586a8a4040b1046030101c0d0401400542d444e8a43d80e4004010305826903169207189001c6500410400507440d00ca0000d03569050745120389840d000d103a185040d0013074010380752410344030702c6205074031100003040020081c100c54906045c480d0698032048201c03407046864411412811040002c5041c281c4030070130750801405ca0805a24031140c0b2952201d007103a0085d1000e82d030071901c0c0c1000307001464041c0300346001450101c4159203025480300114200040030b0798110880c6940702c0008108501039008901c150a02030340803c442c6403603140c4035810700c005080644a17503103000b40101e0594003413481c8000240d01c400890302c10360301c0c00c02c0d40c05001500070803620b4060740500c010140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799787787 1250 799786537 799786591
    0x10f112a010603050105040212160b030405030d02030906101703040611070b03090307050c0a0e0103030807120203100f0e060a03020d0606090c0908010e061b0a11070605030603060703060305070509 86
    0x2440c464400451941020700400210b5940080c3e27070340d525007120f070007600300503544400581120942c072400c64403542c8900f00f003411350040c1c035441c1c4270140c00041001110500460103d22840d03000343e910030f02c16140e131503580c201a0130a001c840d441c1c1c01080300b03101690081d05c0c1c0b50b0203186d28030101c1342c205d5190811200d40d6081a2104541584003203421070401c02c042c010356107200010340c0c12078100c3d071034410f12600c0c050041c4009403e0090800104251500c500e030b0b109080c404114040d5624241100c2424079000b49101c5ca0010014210300820700410a40520380a1030005254010b51815074081014805400100b1502103940703002c00902c103c01d90103035050403601c81e1500400c80385800d403000c1c01c0d602110281c0354a50440b03002c101d0701c4550b01c0442490344e503813210202d40741c40d1040c4096400445040403410244949400010210740c0500114402c210607010766090780c0780c0c3c00c0c080c3d00b5504e803800018859000814240060300703240520962103030850b014944c42000d038018000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799789037 1250 799787787 799787789
    0x17030d0c09031a07050d0506040e0a050d03110909041415071e0507150c03140a0608010612030f051c05040506040507080a1109070c08040801050108010f112a0106 71
    0x1040341d41104106002a503031007007406185120030b9032114a08048010060703c03618070740220050391440030440c80e484070340c003a10780c401c03032034007150300741001d81c20955034407200e4014075000030b410314844155610300340c1d060b5010351501424406060b10f465451048880135030002054601c552604180b00c1040707945d031715014011a03216040761101066007040741e4048401c41d0760600004002010015050988a240301d10f032401c00040d25072000c04041b4003510300041220010082e90040c0000203040d03901100403519800020005a5520707603800c10007070404171001d40420410b00403149441d0180e0b0091902060f03600f054101e400380514400125442518152400d0307014408200c20803030100300782c03409400c03000000d00c00c5003840c0e51200d03d8580410380903402040c2070400b00306e0b160302a0b01c008116035440070215403956154a80b4900a00091082e55490340c2042403442d81d480382c6210304564441803642c410720b0035528046999110284000070003200c040e144016008140a02c9458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799790287 1250 799789037 799789061
    0xa18090504020112060506090f04021308010b040c031b0c0c090204120b09070b0d11070512070b07050f0301170a02040c1d18040b040303090206160506070206010b0417030d 75
    0x282a0610307000041002003081d600c9013805140040521056403580c05840300b03010b045500340302840800c40880d019001d0301c44080c035105250800858241410340000c1d040d117005850411807600040300440c05e0395000b5500d8040d866003c000032480901c11002c4984041c0558882078015603143c0d0310204070390069015030b01c40e294801403841001441031901d82c1009180b8000c0c0505800c0000058088c07095003840c1c11a25525001d07010012844d0f0151060301d81c000c8207483d03429200c071031507420382c0d48008400c691401c075240000d18103902070380a4030300c1d4506030303407039181180e0030900095165085180702d0310041c0b1131030240d100140d03154003845800d50851750f6400c0c070f05114102440f1070101300d03444080c40744100c003519803048408000c8030f91b0f0154010201d070845440e1414141d0082103254006501701304000b803641c0c0040e8100109441c03240c40381e402c481180e514130340201d03103903002802040c40a280411040ac1a0b407a40d514802c651000c0e40300352072a0150000c400c004640100640b8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799791537 1250 799790287 799790291
    0x140607030225081606020303061c02090403230a050706020928090c0c0510020a1b0c0303110c0a050411090a1d060a140112090203031206040c11120a1809 67
    0x203215000d0240000b1036800e04d41c8010916844c10420065140d000c002e10b998040d8000484282c40c480d0b460070941d0005030041c090300654202400d0040503400340882c0052803042548012100200d460120ba004603800d9072140d05200066550101075808440030690207110031006c41588100301c9000c04410320170005146101d40380c140e501003507600344080c000a000004004001090001c29100481009148016a00d1940590640744102c002c81c0c000d6134490408018420001503400c4081500d003c1d86521204000c10000070340d60b141c0c2400903581000c507010080190341802d4108200d001c441b031944609040c1d02c0c0e800b081180d50b065112110361100200304200842d01030780749540051041d20b9580c05941842c00d20180460b40420a034100a054812061050141d41c0719074074865004098075602c242d80c0119a0404106448a621441c5003e20100c10a800381c10041041002ca00c09040c03d0382906001100781e411401d2668140b01e40c3c40741040c003040074103003d0701c007428070301d680 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799792787 1250 799791537 799791539
    0x70c08071208182103040503040e01060f02011406061e0405030d02010b330904020d140619270209040501031b0b0a120c110105070f08090304140607030225 68
    0x10228451a1080a041c05a0800455003813404030307040c0c240303207804003484005607240c0300d500e0034528510603070780172075120702182d000030071802d83c4440348003441680e039402407084450310038094200000a982e09a8005400c1100c08500300844009008080703120918500300b80d52440803d0810135001000c0d00180d540b200002441c0c94032800001c5c1804610445000510788980450340b00c0810881c004800c0e40d0104032000d0994071501100c0703d00340d080380180558503030008401034595081d190a480750b4003a603110514400c0405d054822602542e507101460b5403040100c880b50312040c22266a0940c00300019101c076211400369038025072051081d6003c0c0c980014039070b46c125907103410101d40c9000800420455503032203038010007201860140001d040c08450400d64140c484030f50907000d1f6508000c00c21881d43e42280007a9407000080e21140e0441e6a244049502d91060380070751268446400340723410150030905d000c0c1c07078511703c24012580c00d100111240c101030260101d003503401d1841090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799794037 1250 799792787 799792801
    0x6100c030311030c09030105090c06070f06151203120c0e0d060609050c070c060c380412030b04021204080f0d18140102070f110a0902041707050603090303070c08071208 74
    0x2083d02e034020270381307006020617422000001e90300d4416060050700109001c1141428020f030341d403103407511819488018284a5070380c0010482c0700f44030340044d000304481070010140001103000c1c11080700b200eaa90084200200710402107080e0034000c0a540e081d82d202c07002b01d4022054440c2038000c04034052800e0302e5000c00e29248145890541060701003003407648194001441c641d082c82c2607031040010681c0301c280450014060200d00d52665001445041e040c80207105403403052a0340f60340e05560900050300c1c0b040610090b07115002c440c1c12071a84031000500443ca010001e0810940c000e50150f20304540c41c00450300b520060060300f400181c004405800304a603800e214002060998002d60400d07000e5100d40c08a007510180103401d00080b6180381c4502d540348421b00014040d1010f0440d00d454842d80000c41c13031041004928800d2064001c007103102d1902c032007664852081c40c80154074550b14a601140d00f000405c0044410030014020500000d4006500d0a416581503850301606d143c40e00f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799795287 1250 799794037 799794041
    0x50a03030f0b0649050a0e010c09080d050a021506011e0f030b090103021c0206160302071404150b0d020d02030a0902010e0a060f0c08130f1a0306100c030311030c090301 74
    0x110100240080c0d00191399841101001c4c180c03c00c0301d105000036056035106480009803030f1051135070319903500e48580083c4441e04241c42c0010343d2000780c225100c005400c0c0054903c4d101c0c2c0007001025900c90f20a400f030306280c40003034580c00031040c94500250255034840038441941080040003048800c5107040099606204450700701c1ca0881d1044841d514540100e9801e1007103240b402030041c0c030494204155180c1000704c40e680c0d002c0720310842191000f403c0c005d4a4203460700848015042d2400014000e00e01030086520444085c0d1340b10b01800d103400a41a50340d40100d6949184503020302c40c3d086540d16500c003a40c4241810000410b503248188001485000c2c4500a64443c00301070109000d040d0b48090b415500c1810360038054080081e03402c0009003409041880c1040003030050300880c490500350b003000c00b00c07203d100c41a116030754180004580c1e40000c443e4940c021035039254055101d486900c0014196000c1d00300080c4500609001d0b80e0b141c1d01c2101c610704a044000742d0342d25281024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799796537 1250 799795287 799795357
    0x10608031606150f05091513020d1a0f090411040207030e0415080714120604051c020c030d201b030c0307120f080c060f070905030604050a03030f0b06 66
    0x1c3d203c40c6018205008a42c4081007800307420301074600c0c000083c04942189104607180140108607c50b06c1020001d90006548003442c007126180c04d0010510704842c0a50014501c80c1004240a0710028030700300b400040140200140c2d02031000c00c2440791551114030082825a009503130f090848a1a0800d21003a940b40019a1808192004007001005004264074003902e810310f9041c040c2c01c8140b030010701070b002e0100a990450003040309000400ca80001c030311064800ca503030182d5803680d9201d4140d80b5032402da41d92680540207803c0020060384545028016031511764584005021000703002d07407030714000e2002031502d5100b80d0480c0000e440e003001518040217040740100903060800c90303025401c100c001c00050800303810300016000c0200b11401d603000044810105c4955190000351035501e64010b8541602003101038130042254180860032a1040703030000024000b002041e6030481c0245800740d1070b0040c050361005074482d10359a10f8001d0070980b950007a807603d2020000042c03200079600d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799797787 1250 799796537 799796561
    0x2040302091302030721050312270304120f0f03080919150b040608030c0d1d0102250510020c0406081903030c0c02040f150905011a0c010608031606 65
    0x62a1840b100581d8001080c1d0199011400c0305010a0700060006511015694005203503000120700c0c6c00450103a015418410601d1340140e245200c0441c880c60740d030704521214080a07420070041801940c9010b510701d0f1042d8801e528040c009051031700c0303480984101038000c40005049805100350b8903802c00201d00034000810b111100e24829035205644418400d00c5c4039140f0751106025a8180d0319903111600a004010a5070398035060318034000e0700e40440800841c0480c0f090007020882400048801e6581e000c10307001041d015150009c0c0d45020548031b400075202d8020031a0225007500c404044550301c00c1d55400401107041c110041000b0f50f50b158114034950340c880050140d55200d031020f01200c3c20b40505002480341e41790741084031111010079019400500344040004a0b81032a03000d40c10703004500750768103d00c9854400080039640c0a00c2500b0b81d8031b407039500da4031406440d5002051400100000010310f56511b407001c07821500310a80118103660b10080c03e03000d114441c0928440300b50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799799037 1250 799797787 799797811
    0x1716050118030f0203120c060117010209010905040f090501020c070914040b13030c0b0106050306040b04090b011707122a05010207061110050c040f050102120d110417010204030209 79
    0x800010741c16954148009003031655903080d010300f991401c4c0a0220180c0c51207000319560f0200f104240c2e501c403400c0c4184114044100c0390074a40380010f2003907031301c4224141c0d2519880b5280100b00001741c0b0003515402d40e0f1a556100280000300d0901c001c04500141101900c00e051070b0013001000c139032503030b5503402d04890307141d00b044000303400c08201f95845141c2d00410640216241011a0b04001511008240d4403031a80042445c03600100650321440e0215414001a030b50750040c0420b072841c21100500c4540d0f40c00060028401d00c0301c41c400d40180d01000c80300c025641e240e905a4000c00c2c5007041e104c002c3c0380d0280c00030240c0308175002506180c40d000d40d100349515150000f0b56503038a500c214403c1160254007981c03420814460481141c4540b1820f10060410303052030505940640b0428002a001c598006941c0d4004070704174000e207004006d0701d400c16005003d010080c1500300b09001c0500300400010800a092058040038121301c3c2c000140c43c3c5085106024542d200901105040d0b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799800287 1250 799799037 799799057
    0x30c1f0905010c38010f030c061701180209030312011a0f0403060b210c011101111c0e03070c09180b060f150714100c200717160501 58
    0x20b914040c4c00024400c200f5100d500411400050749551004003003002c4c5a9100d110000030b0a628200445099a0246001c00c0c1810303694042540c180284501c1100c0360901900100240c0301c0c203014010700000607400161620300320b00300083c1103500103c0302c1000c9090140052100e010004042e5801c00000e0030818903003801038080f41d000f401544001070032182c8500c1144547d840d80d0102d620700f00810864000710401151150352102d01b0700070800c0c00a12007d10151101205001e0304004ca02c21041985c50003d03071188aa42c08801215411340064690b0b80c0d039400c000c0300300300502d80700380540741d950001400e0a58100c140c85c56403080b40c003291504002e110100b0151030b40181c20810480d00e03042c6228401d404900000b15074180812442404100007060050008252001110800076a0000d01038003201c1000c4440055039500010395640b14204108415046001450350f802c2c125006240c0d100030424103070301d44075a0380c4016001100d910000c9004023045001500c400d0030700d01014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799801537 1250 799800287 799800293
    0x180106030506130812040807021009153501180524040b03070b071e0f2306190c0e090a02160506040804031a010503030315030c1f0905010c 61
    0x2035440034008903d05061410000c080211203400c40b2010140340c000d529052400341450811508039810580c080d9804030710f120011885030030321509440b4481808103030050901402c998010402d034900540702d400c04800043c00e11000d4002c1c1280440d010361445a42c1400204020014200111020942021305106110042608801507451201c145122021196000038041e00c1d001e1221a094041c1e85d10108070160840c00821503103024404485419603800502041c0030714109026043d03414100e200400282540e44060303103c4e40301200d01c41d0b00c1c140031404508100c416249041d01482030b400340c0c04080d0090142c282c02500350b042a0355101107220200d8450000103024451069001514140b240d04404111502d40c0d00700003110344902d130916240e0181d911900050b580e10081103500f55841e550340070660705030340d0003902950464840c0e0208002207034003040a507915009840100308036441e81e90000c2000329490711a1000c4648092004d0b01142803a01b2030350401004144207004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799802787 1250 799801537 799801543
    0x32502010213090c05090406090203012c071110051303030f05190b0a030f060b090f0108030a0302071a132102190c0f09020306042d0c021e061801060305 67
    0x103c404803a40030600d42d42281044400d84a0a03030207690261904030046000300c5241d01540c140c03040303450a00c0c05127071402e40035881c01185550007640000e441c000a0b03400f9204001081e40e41021038125220703a0041504241503030402c03070b042c1c0c001419076982241030590500a02c0c002d02a4180200018202009295040a404174030762007419210b40360301c40e654036030698002c000c0d07812241c0140c5400d1207180000142030520740302c2e80300b6000840400c00b44641c85a6080c120ba54202c0114a0030b20780c07000c190f0103504402e6080e20040c6800303103081ca242c1e1903a482e66204d410450360a0f00f1041c02c1e031a00345000584600c01440d4964105445512660005411414030000100032522000103181c54446004550064981910003c0002820107039030b40185015110407602488105004600718001c0c0700600440c00302480980e424801981c056481049441c401c1d10544000030041c010340011039030300405101f070301d500020411004041c1c251158608842c00d1000717010303091454840941d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799804037 1250 799802787 799802789
    0x30708180d0c0201090902160210080105210102041508040b0708070c03030e031e1b03031021060e0708010b0307050d1407080d03092a14010c08032502010213 69
    0xc0c0710100b800e0106682c0a600e0038002003050001c199aa44810201c0d280000007941c0102e025888941204021f28001d05126041c1c5401803d01780c001050104894103445a10341c0f00207040d5420080480d1008050b03c603450782910325100c07070410f42024504042c283c0001800c09040110900500401a0f403000d912941c00744c0500c0c003c03d145040301140c5055100358980c1000080f011003803808006410360241820305150300150748842c0100034150b803207100444518110b0400b0590a00403e8080d01641c42328009042c1d051590081c0c580d40e40040700d0300501c5c2580304c1d9200c8402040710020034014460301390400d03806417240500d0440070a4580039042d9000b007036030003c9040c29016410401540c0014074081c2c04a41c1000c00500001d0000c3c500c688050300c41c800b1051601d0501d03074170f410b500c1c80c08800c841414000c0902c0c5c80c00004c96850901002c80c1003095005d461380110b1303036030800303140109888500032240110018007280c0c41c1c04242e0f051401d690040c464501700030440140300c1c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799805287 1250 799804037 799804063
    0x607150609240e010b090316030c050a06030614061b0105180c1e0d050a0b0103030816030504030207060f14030f070908060c0d1104030b090c0102010c2109060612030503070818 77
    0x5d86601881b0f0019007840310681c42e18a401d0900c400002c24440d8507100c00080b80c1c001d85144450355160790040f410340d101d0340208060369405548082950600600501400400ca04400700055450202c2829030354184c4220184040c1001d902c000c900302480080f6941c1030444207042801c40310102007074031000041ca50780c0708803140d00f000c0b818414248600e0164a5124103074100642c1c5030b00d00a058284151201c10a041c81002c112081c1c5002e403250703601513070f010340080c075032140b4000b01200c0e00704852000b0402c00a8400c07500c0d000d68040300c003450182d0102c3d48403044a180c041c03030081c40f40c08c05912580c038540c414818810412010011644024090b5101180480214103010075500c01c940c0010601010707042001b481c428042404000e00e01c007640288240c6483d207500f1981500a90249640c44259806810541d01594072078101d40d4819000440c8a40e51030800300d240c2e18030750009402042e000000c205409620158496000e400341d825200e1000036160740603a50041c1500d1a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799806537 1250 799805287 799805309
    0x31e0207051e031b032407120e03120702030f0d320c25030203090a2c130206040e0f01210803041a01120308060d0305090607150609240e01 61
    0x140740c0c17000d100c2044111821808480c401e035400700c0303031040001c045840d000023940407403071502c1c07421003405201d85403404000210700b0070603945a10410310304060030003c154402082050400e0140b0000b8080c1040203050014892500d588694a0850102c17981c8444920044820183c010b01000b034540004a44051036110740c285030000d0041210030300040750006401d04500209030f40000240ba00840691749814a1903481aa500482e184102c1d002c0b08150030b0f8820920315034010701503680c008801080401450a1900420110741c059040027071a0b010100800100042d5a02110300409220892660400c0301d010580c0c3c810803108001400004000045400c0c441c10391605110a646821012210f580d00c030403180c003040c132044048000c1040388c000142180b03032101c40501c8003a095114585028400300400003035522450046450880b00200c25018410030320600001c1c00a00300b00085100c02203c4080c01c04401c030150080741189002e091101c0c500e0602403904403140c003040c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799807787 1250 799806537 799806583
    0x120d02030705070f300c0e01030203160302150c010b190f061e140d0e0607020f010b090402010c021309050106060e331e091503070813031e0207051e03 66
    0x24111490405d90010b884092200404281c42d5508100c00b4102e84c422002c84414000c0307007001400c003c82c0340c40065032219a07910b440c009003040c0d500800342060600300020b204500c00d00044c0ca0005043c0c08012082c400440c18440089010840c10240a041c14090300c42440c3c410000c51108000201e1000c1007010301740b24480203002c0c0103507498045607000600c84104807104d0300e9035507030045450300c00503c41c01c5a54401001c041c403d01203140805450035003c1c0d9260380040d1583c1c03035901000c07030300080e00d220101441e046500c601c1c000d9500c280004a0702924141300100110022071071340b413152035803a50148260281c0ca40101000101070704c107188085003002c020200c0d000e0300d080700d15410700025080b50368644a100420824a00700e07008840c103403005421b06031502040b03d0030800310b91105c010441c040d9400000e03554091281c908044004071070407030031464080c1040b0703040c050b0303000840c01c2c046031030410000200030416090101000741658006943c52507002d41303003c20b04040c0d0380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799809037 1250 799807787 799807859
    0x1109040c180b0607060c0912020a0e1812210f0a0e010605030a03090e0f04020604030602180406060314070201200c10020406020d03061a18120d02030705070f 69
    0xb040a00020041066844030000e013003000c06000c0740a078040000b4826000421020895a0034a02c03c0d9000780000002a0030b1180344c42102c0000342040c0d0401e4400700b44003111050070000c032408030381c6804e9240c0d00c0f902c503142160000000103c10783da944403c48200101015900700a0754010441900424404035041020f401401590000780d0140100e159030b00070b050300803c034030381110381003072040315140d0340c2e05440c40d8410001d4800035403050040000b00086122900601505000072028803545030201000804480003644070101081e02c1d01c0800302e030703600054003803507001500380000e0050410b6081c5800b000e0f05c038030146690010020600d60098a4104041c00f40c407441240115501c6403188400707569020800b65101c0040c1c00c103200450315413400c2c10000040401c010505007020400e20500c0e5030740e45d1102071141c20084068941c0c540c082c01700a460005800d0341c02859036142e45041460800100e900013510010000d903040201100e440d880c0301c4003485454000a000d072841c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799810287 1250 799809037 799809041
    0x30606050d1802031c080901050c0906130f1508070305070207060c140f1510050f01030b0103150f063b030708010e100b041b1d1c1109040c18 62
    0x2c0040e402d0b00c03174110010b04452508251078a24603c50325902d04503901c1e0035441c0d0036901e00321220311100005000141309418600c01500f00d02014040108040d526188201003844465008841d1140030280c00f10445070002035464110700285402d1003646441e00010b56226002c0c07203201d0810072101d502c4400c0c04580400c042e000b0840ca81510041032081001e05e0351410341155551940130464045800002d0126a0f00c08a840181460b0154540500103600420010b07035141d040c1500c0e404c1d00c03031940000798a00720180c001c0007990810310382402001007003106913001034108142045080050b00c0111092586a51201c41120761040a14004241852015480580a0b600700070360f039280d240000c903000e01c07109121201005031141c3c10003000284c03507680fa401c4100d0303945002d2503504180b0a07242e40d848071984124528400d4848008074146518001c100c0d01e20424200541c1c0c100704015100d100441003c482c04036035810581c0740d412001010344103943d010390107505c14103d00b10f441d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799811537 1250 799810287 799810331
    0xa02131503020f06210907050607030207090c05160506041b051503071106150f0904121103040b0c060f090c011b0309051f0f02060907061d0303041e06030606050d 71
    0x2081084100701c5c1c4070003248000c684255240d01243c010038001207540e09001060701e140682550052556034900b0660f4001005124181410400100700280040301c0c011050034445100340300400c15883c090500c00c1c04440c10050b103001503c40580c3c100007580e42d5110700050314800b1107044c5e907030b5121610309075000d42c0c1c4241c80301c507940102010048002040348941524142c10746c0c1f01201d00d41c4132010016242800c807401020320316000340341c4444502ca19130040020084100312480e050710b0704121805134120051300c8032503a20820821081c0d81001c002607030403010400051803c2010240080c0080b00000c0007c44e08940c00d50718402814407406040004000190414249540700704c03c035460021003848007000704503038000400c041c51001404510403403441c0080c100b540c1c140350003102c06d02440c00a2280c2c0c04d00c1d00d2820300700e55806000038001021101001480c039080d8484500c03c1c01086c2e440f00f0141450024100034081e001030481d16144201c80c0c0010340310303039146c002d02c03541c0c080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799812787 1250 799811537 799811557
    0x12090d0c06052205060103030e060f07030c1a090f010f020c1f1113140102060114010c03030f0c03020903120a1b060e060411030f01060305070308030915090a02131503020f06 76
    0x41101188140113012400398140d90095480d108224206018000c440c41747e2101c0c0d802c586e008101203c003003886000860b644034881e43c40164000110b2017940c07030a54054034086100e40117100f409444100901c14115041c0c140300040d4245400c5010300c68803444240403507006296000c4601d03044041310760001114144190040d619202005417100c04403070f603800303020480d0740014050140c4e50300000710302e8121010312030b8034030303012a4400046842c1007078806d088003416225901110035115901406d000344481340e0740142c944d495001050300c0d1603940110f103081e1703e07010480024035a40c032110040c4216040c0e00b10f0b0408140f1481d2500c01050043d0000c24540640c60030f0008100b400c118201c4882421011601c405c8191030000c0c1c00c0f00d20510008025900040c1c081002980103c09554856094400d41d903060703203c0786c40100024822501d060341c0c0d8000d814060b08604e803410100b00d00c2e50030160208460070750b402950780305d142240070181c460f0b000c0107441d40190756090216290140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799814037 1250 799812787 799812841
    0x18011a1b07080705040b010302034b06010212180603062b020901051e0d06023010211401090602070203061b0a2f0312090d0c0605 57
    0x1036140e88441d03d07040a800b03034138460350810710340c030145601c24002d481c0510031500d07901c1d60300940f03600910300440710b40c558050b683e0703070030b60081508980500100200c00820010780310140f40200009003003511715854441881c2c010301000030100c10f101c01d080b500d003205443c000d80d40d4450b900054640c502e00d2040d8400c42103c1c0c1e01c22110482600141e4001c0e920a0ba11803640b640c81708100143c00441c844201c0329000b00c800788004521308030f100c1e905114040d00740140762140107407002c074103031119156810518251480da00c4a82c03614149940d40004400c050032940c0342072241d86001c00c070030700031140c0700c0075110300c0c0000a0114084418109450560081220070500e04d419000381d000100241d2003405003100040001c55009050300a0881621405190010711401503608814501d61200c0d00507201452091041d41414607140b44204600119142e50b055140144a030f1402452003515400142c0c200407450f0704100c240340401d5000c071012509582d0a48034451070f020011a0b460b0401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799815287 1250 799814037 799814039
    0x70308150406030303021b1b040f0605090903040303120603020906060c07081e010614010c200312120a060807090c050c0d030c020d030b09150d0f06020918011a1b07 72
    0x10b4140d8000d00800c0c2450081000c0d034181c5003101c0b9111494440498400008440d00c0c1c1e2842c030b4a079229022b4110f842400040254540c40400d100002c11240e15550b50f00018083c1700340340c2c1210070340d5803407060b041c8180001421079011484001d0041c1003036004110100701000b1881c2c0520000300076120000c101c81a850001c0c280800e003050403044001c0652900c0c10102d0303500c488003040c5101000607160060740d05e00b5030355402132401031304c040b46014050040f0240413070381e02484811000e14031262240e807118015038003007607881c00152000450903d409006c120300e810215030300d000c40709480e90014441c1d80004040c1c44500c90302421b13299900602c190441d000b0b070194400c020403c0e40741e00301d850b58000c0c41070aa044030712880328940c3c0b00c030034503000030700c0d40042c3c8840808481d00030f00310190100c02d5945850050020301c0e0102e48181d00450380c2d40e120304100101d070342d1064240150b040c0551505960b4038207003082102007101034100240034514030b400b00e459880d5007071010040b01c64603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799816537 1250 799815287 799815293
    0x2060a051602030a120e0108040b0f1801051e060d050d0e04060e0108030703030509070e010b091810180603030c020f03011b031e020319050621030301080f1207030815040603 76
    0x3150302c00441001c96410440011294441c514061286a00c2b42e18950036480d045180703502914028404840c810390f054581c01012030a01816004101449040c04000190b40c442005050020b01640c05149641c040c6004180005000a5500c60341e040080350005000041806482240c0008640840e600e000191480c00000104844e5009650030002d0b41c0355008031a4407081c00740308511100541000501c8103c1c241e000400c145d40d801082e800188207101030701d0140305022125004198062481040100741e0b0194100c145000190208541400d6075400b41c070f4002e00d46000b83c050705000c001101d0b162030960250420484581c4509500043c040b4020b0140856020181d40c000d140d10903131854242c207000341c90081501000e88800541644416001807600500d2580d022894a144035841e403403034400124001d100101070f542d00e40c10310351060320300580300380700d03060341c0d8409051000c089e403514007940c0e141503040c0380136102a01c0d0030050640003083d0280450344a40351007400010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799817787 1250 799816537 799816553
    0x70209250e03010509010203060a210b15040f0c05040b090307030c1e08010c0806130605090c04050909030f0412080c010216140604030801060318051005010e0a050402060a051602030a 80
    0x4480c01c218000d010310b0360f481d040c4509034003050ba08590001c0580d101881898442d03035040c03a015000c041034000344085910b0316a42110280c038100040c4a40c030071442c042d414140210150060012014031418018200c01003503480b0358466080c6064010520481d113980c00c0c0700c90700003960094901c40032030b070b202c4a140394800320001c15808000f4030002c00160800c418058501d1907621501c0b807852a6582d40306022485c449046403da585940c0c1e00d010503030b075458607841070191841c00c841688817400c01080c4030410301c3c0070704250304540c020b00900319400d0f4034004403000d68000403618400710a06150650035400b416414071000e500101d040c1491740c0038015907a07170b050b01a48614034034542c640e1440c0e031100000e0f074024000900807001402194005e801c1080000c5000b852a260a2499140e050034440580200703c00c4070b8032000100400740300d1443d4150002e130b55107010001d600786540041c441c1d104598080d41803050204401c80491204d0380c40e40d41840d009000da5040c2e25061030444c1d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799819037 1250 799817787 799817807
    0x10020a020102091c0206070f03020f06040b090114100b0913020720060309061614030408070506091f1808030f010f15080411061308060a050601030e0307020925 70
    0x3001e81951507800141c8500c0c10829400c0c1500540047e290082d25256143c0404041d901035065200b03000c603984c03c8035030070091123100e50300030100b090160804050ba0307825201c8900080d0340031184480ad204000700d0280040302154134980030070ba500c1411402003841d0305003200651002910100c1c03c2d07000d010003441e440308681841001c0b02d60340c1c01150308204d11800300f80e44420b019881080003130f00195103d070440c00b5140703584c1020740800010600e081680d9000f1907040707a01c4d200208403441013040811200c1d030004114400391010040c010010402200034545020300140c8450740c103101840a07050043c541030300300301c00b196a4a80001c0040d0000c00a1180c0c00c4880310345640011015100342c0040c03a102c4040d81d8200141e00c1d1610390150401d0340100c410b610103010071141b1844c0d5101d030031080c020043d00000d041540ba0500b9403c00310b82000b02418103045c01c0c08540401e100d40881101d10181d4116160084d54aa2401d960070200f22540007021620900180080307480d04182006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 799820143 1106 799819037 799819039
    0x41b1401030f0b0a06020a020f0d0b040b0720030702120c01120f0b040c090602160b030718090c030204080606240f190e031005090d030e10020a02010209 67
    0x613081500c0750300150150381b000010fa021030910218204220008403410400c403200c6403911183d8010040c030040908104e9030006140c1401918185404600a1803045c1780e55200d20200d9a0f81e409001d083e4490243c0303403419218060b0001d4460130705e180694401c0e10080c403804100c4094680000d1510400c7d890b07809140030354896114a80444105698100700140340101c080e0a00c0c451111428500031604402d1004100c640200c0ea08641c0902d059003a00005034000e0058902682200c0c003014180540134001a80c140c0260040d59401c0741603441365210601040807804514401458048000c00c040410000351006001d112101c50382e050f02e05407000e2301441c2134188500e06400864103d01c000921070508100383e07150390006210401480c14082c207426910704000300c1e500704054031003c0d221240c03103003400380d84840c40c20300400350344403102c01c0c0019002c0e400442c044c2e = true := by decide +kernel

theorem cover : BRFrame.Cov 799640287 799820143 := by
  have h0 := BRFrame.cov_init 799640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 799640287 ≤ n) (h2 : n < 799820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
