-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4581
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:56.790136+00:00
-- url     : https://prove2.me/submissions/46f37238-e4cb-44ea-8b01-a7d9fc198333

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823741007 ≤ n < 823920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823742257 1250 823741007 823741031
    0xf1215060f0e2211030c030304060e040e120a02030a0909091203050a0b0301060807030605010e1312110a11090711060610090e010617011a07020f010c061518050906060d0510 76
    0xb035560081398080d200d20084040d05040000803101902c2041c0c6600750404006010000039007040c0707041c010180115907804c1261035451000d8441089030781c004e10b031107001142004125484541c0031003084c1d400c2c202c252010800344000c01310b4107611445c01060b13654510200501808004090540640ca0100e000400d480f001c079240003621b12400e03090002e07998503090f10340d1492090b2460704103150000c001c9000520030812607900070140c1e0400c40210030400560608080a041c01920160b021038a18569442c0c0000650703808102802d100034000c500c0c6d1940da554020041c030300750141d000418070b0b04020b4040c1103032500030210040b440358650386801d4000c040c40090248860380c42c0c915400461208804402c112542205041c0304c2e090102c580c003000b6607510518000d9042c07003001d84a68002c1040c9000300b0782d0003c840e0401d801c21901d0040c0c0081d02c0c0c8072500c09256414602020b02050401c0070918942000c03080fa00c0342035151450400320b042608030358105061501e40b01c503218503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823743507 1250 823742257 823742273
    0x160e040b04060e06040b16110606010c050f0d080403031407021f18060902011806080601050f28020606030a0f06050601020102160b06102105100f1215060f0e22 70
    0x4240483d040385241e07187c40607002d8030f5410082c0c505404a8001c80c1c0010842d504c650b48942c585400f400c215800241380210b2107040010304140d034000115000104414540c050141300304000759003070025821300e48501c0003900c07600d00c940750000c0c00760382c154020391440f4150010a80d4a80c2c20b89141058149031801c00c004005000f000c03408079502690540d980403041c0001c1c2c0880d40f640d00c440003140e40340c0c0011100c66104200c41e006004051100301400b0042c444054944012010508880542c4000191400c070005180911a501001100700010000c07540d00c42042d40c062030104081d244c00380140d004e8052010541000c21442004106010b403000e0351500403181502c442e8a0100e00000442d451081020b807098041030701c0701102d0100541c0d5004951155401c1c1c2c00d500d40b00d4465030840f280441684c840114400d83d409c111003481440165180d614400440400500d8075145541111005038822100007140c920b0002d0360401511005400a81203a90343c507602a0301e030315207508 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823744757 1250 823743507 823743511
    0x609021803010203040512070c0f12030206100b0904020708040305240105040605090c090d020a08011409010213120302010b09042d110f030c10030e160e040b04060e06040b 75
    0x480001108110500d5080c107200b100c4c010b9030404003400e09510120603001c49940291000c669205040c2400131309400072828007070240844110700d04625040c2c0c200289098000b90a1090510880008201c4d05464200b1540e40c2c41040c0e6025031181902d007806582406590b10140242c001c121058050030b0f05545a1400d0284803008818030381d07254428402228041e0040c140c200c0c24207000b0945070084c40700500694000140741416480c0182d010800021066100c0d4025030746612119145400303d9629a50100f0250004c6017071240c0d802d5081c0c0c0c8036101e80b04443c00000d1001c110740a040c070079048040e1078500a080c0707100320704081c0785c9511101c4405000842d1a10305680d0110100700010152140541245044109405a10802002000d003604140d0300d48240701c0d00b4813007500c82000306603000d038054500156900e40c1041282c10072224005100c01c41818141c20f00c0b401c110b0b80035090700306820000b50645c950340d030714201d0010161000309402c0f91164408008c10000c0a0342034074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823746007 1250 823744757 823744777
    0x50d1505101a03060d030c23030a020f0a080a14130803070c05220203100503010e031905030106080403211508100207020a0e1308030103051516020613030e04060902 72
    0x10b80c8401ca1414805010301064a80c0b69108012035052804640f041c00c000307500300e001713407902c0c80d92840f10343d41c1614445000841c100713030f82c10209106182d140c05001c1032491214040180500034141c0d80e920300c45105162241c1c040c4a6009020302c402d1a1a5040c2e503002e200094600d10116224004550340380c00045003160407a06941011946040c01410110000d007022841684c034031143c607000c4003941000340800e40107284100005683e5600f4040c01c91944850405969940003d80c07509004c4024420200203105007040100506680000c110340e0042d09458088400d8134040349032120b007070210069405140c200083c1c000b14001c2003200b181200d000c501160318100c01500f6507000c2c3d008814000c0c2d0702407034504042028208010500c0c0e0b010100500c1e140c10352025a0751159150002e030801d83d43d036401032462600d8075a52807086500911044c06444564481d090000d544050040500042c1c4081b410a9400c060140c2840940722200410521001e0303124070381031000b508070420f85 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823747257 1250 823746007 823746029
    0xc0d0302100c05090105031303030e0a0f0c06050724181505090105100311060d0617012901031a0405071107050a1a07110d06091505010e01050d150510 66
    0x4502c80b8058030445190301410303140d99080d9940d001d0490110600c004007582415240d400003c11401c0a02180f0501032054400349103419603820000411103443e0480820b010040143c08082a6080c040f0300e019000c203204031400c2141c13441b900016001c03080744440c512f4101c29043d0100302c4021301d21259500c0581041080d959071910341c50a030b070001d8a100c4000800042d0034000708170243e107003401828005d0034551500c00b031302d400081107401c6076000d400482e4100c008244000000c1c02202801e032042c1500d5000810000342000008840c0344105050503640c1c0e01c0b507507000140195102407654000c10410081c50031100103441e100080740c0c846441d001d03100c3c0102d014645511504141c1c0d100d132441e002100d410862140c0c50b50b0003d40140c640d1040d00c05010055502c031010030318914440c02e000f007003198441ca040c0020384110703410555170b242840010300c02c00c519028403504550b4211203244080b40d43d4100341c0607100d00100c000030762600b03200130000000648030b80d4204480351702e411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823748507 1250 823747257 823747271
    0xa0b0904140f1b1e0a0906052d060d1d0304080f0304030512090102070902040b0706051302150921150705030106121e020d09030e06120c0307020c0d030210 68
    0x186031200a014401c02d00ea520b02211000c150401e005011803010b002a0b09030700e00c41301c08002403800d807100e0388100b21080d00c4500a000310304100c00c4c40450851000903020498030705c904c0c0f168260003040060313801807001007683e02c15006242c00c0303101070301d0900c0410381c071503c0c03841c2c402d40d00c0b54003d00541145103e0120b40843d00b000000481702140c1e0803101070f06040b081509000c1c0241c0c031900780181144034202010804644500c010b100510044213001d60f074110b14607084081d10070003400c81007006601c0c14640b025071901c8402807040e10311215500c0e91101c0b0300c00081d46055800030a0100f04000314505c00301030900103450303100c2c02d0340c194442645641d240300c2100c1611007401120002080540c4021466200b0740041d8240c0000c00a00b10040d0754400c1c80000b01c0c0c20603002030050640b41e066103420b06030002c0303801d01100801c0d9002450f0101c82c40d2846002d41019044482074400000003a403c0c510070700c403440c1002c3e0010071002010f80701e0f080095648244400703005507149400701d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823749757 1250 823748507 823748533
    0x3013f05061e04020f0a031406010e100b120402060409060305030d060b160b3312010b010f050702040f02030c0403153c0e031b0109030509090a0b090414 67
    0xc0d498142c1d016003103184100d640d407a42407084c210201c1030b003260054001d850101c002501e0440c12007821841500510350340d890004441c41265000d00007901c11040c50600b8000e071600442240d00d600c94a9966111648440c40420514812a0b201ca04080d203440030120412101100130000000400c1040c000706440304294411072040b60f040c1c0700141041d161420028400441e0554401e0b00f8400740140a0002c0100c5070300c419401d400101482402c05070303d4520b10f0f0400c40c0d001580d2404008104448400300083c120612844900e0240100030600400715079898000ba4100310148905540342d0a107005424031540003808101c2e014052040781d001243d801c1d100303800d0b04264440350511512074002240c51128100709600da0348013048120f1030340703c0d2038a010305055640400c00560b0786000790150540700c400d044500918070703410f01404d0004694440242c613004001282d1058190712114800740c010140d200c0c00d603412045050800003802854640d1130007a25003002a46e0344c10041036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823751007 1250 823749757 823749781
    0x1f0b010e310f1104030b0f0705370810060e0906010509010201180c0f0e04050d0e0a120602030f060d0308071d0307083003013f0506 58
    0x1a205180222815903030818103115a41004001e001d012000107400c0054400304003500c1202000588580b00001d0800800c0003441186a20031010407030701101d410031040c020401d1180d82003018010701c041c401c02039100140c00411b45101401d001c0c0c0c1c40c690105031005060250212074410b540202a080040c01d0750240030f030b580383c000c401400e9900503030710907005607850b400c00302c0e45904540d41c42c602c91b082008801e502c20b46180c0642002c0340d0321850102c401404030041d810860708610064240000510f00007420b00d0b8032801418015001080c06000c41c07002005079110000c8031088007501d4042c015698011409a14138181071501596100244012069618402030000d0199000280d8480c4900e001040b010018440c82811400650004e40380c00c07500d070030003409900204002c0420580201d1303100b950b01002240d00c044900d0b20700c01214640070511803242c040381c41118170703440d03012006400480122134801070100702000640545000490500c100c60300e109880c0401d804680c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823752257 1250 823751007 823751029
    0x50c04020c07330801060212180607050606030609032104140607090513060602151005030f0c090a060e0c0f041a0d140105030a20090705070302010c030507051204051f0b010e 76
    0x64000740021072301c40300649030a900c0f64281c03101c4450504003070501c50b03803808000d1040c0da004000034001800c01c0c10030907040c0302016010300c86039401000746128107400c0b030303c3d002420b515500e038056050351241403141100815078900c2200d401028104038101d60450281d0f020350320107490450246142c41901002ca5406014001c05680400d1001c0c080b448902c0c02c1c5030340880006140301e000740e9034102003854804003d0040286422030840c1004078204101c29550101455400340010303460507000100c0400c6c0900500c072841c40000f684504032130883c4c112030003044069080ca40311a80e103800c0d803005401c0486002504c5007021000314540702c2d14043d681c16160010094918443c0702d50700c1c6040b04001c0c0085895400a60040c0103095490204039885400640c440030b6603a01549002402c41e0700418001080c94604014403482d941d01100391008030555000380d802c10384442c18090b2030102c400c07109429144801c4840504201a500400700441d42038845520305600841000910018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823753507 1250 823752257 823752269
    0x726011d100b0d020a0b1602030d020d0810030b070c0f021f11011401050409021804060606110f030d05070203070609030f0f0221161a04020a0b07050c04020c07330801 73
    0x1504000d00031b0100e100c0080212103041a0208042031a0740d011070b0609002591a0300560013221038031503d260030680603540101c1c0030070040314850442d0b0b6201201c102c0a0460000c006d08120b03035004202c41d0004510350703160001d0040c1403000c440406440d1522516800500041c0c00394071160030040c050282c00b103400080c46190045a007001c040c40003c00300d49c48241d900404000103480042c6984085a00860190310040f40311401c110028003085605030700e071031460384405507120b002e80303001c026641141e8441c0c0300850992603500301207145000e124805025a881c0031425020103070042c03007460400da416116507003100d19440007661034072062442c1040700300000c511080c103280d0b0301d03000b070859080382484a0400001c0303880380c401c08a00040403403000d2913060107001c290720b81400404003c26014010030b1405c8c649980e084c2e10307003403694407a900503a00814a4005200103000e070f00701a141b01140c40070301514081008141455024419440e252007205c0c0d44101d0b40300f42c0f1043e068600d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823754757 1250 823753507 823753519
    0x90317160f020a1a090a141513110603060105040503010c1d240702010917010b010201060e330d0303020711030606060a050d021603020c03010501080726011d100b0d02 73
    0x70316081d6190642400408028003170080c1401000062400c803000707d01c81038400001c0c0300c0580c003c0401c601d41030002d008420072150809558000070300204040f50940c201b42d60850316a10b5000059416010b140c0145925500384681d00c1c1030941d00c200b0312000e1030010500941c5440740300e07091100c003034040541361400c45103000412460222035401005124170624013070460a548002c4100b0502e0100f881600994407854200055079090081c64082e11a41e104031005080c00c030141403290a03030b00001c21148504004416000d24800110007080c600645a94450105850f008001394022082119824030811502c0302e103007400038000780314800281140f80307000b0b42c4410550ba1500107881c41c3d003082d502080080b070f44a018640c0c1581d120310940040841c540030724105400d54905030002c0e4159070040000f000b00480382d4081080c0c0b48446102ca82110000507c414050500c43c0070945040a11600c152001040051035110f42c41030705500b044102000c0e810003100c0044820b010394052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823756007 1250 823754757 823754783
    0x120a0203190c0c06030e19080d020a2003181306030803130314030403090b03041b030305030a0c170703020f0d0501140a0e010e07110109050a0b01060e040209060409090317160f020a 79
    0x461501c0c203d030742c0399005601c8c00d41440c10a0150701c060303a00c81101e01d00003411030a41c80310900f009403900720080c20302401560800d900c0e845020b40038022038810920540c00b19010b0040f20a04d41e001c80c004e950000029075403403401c150300b066154a10102140011180e4019000319040401640e01a507070641c0e500d03242514000c1501d416810240068901100304595030740e002d89201c50150007107209450741500da103080041f042c225070b5083c6429042c003004503141c28010500f840503a901142d01d00f0016143c0c00a2140041d0602a0070555818030b440e040000c1388080c04149024000c4004031860220b80d5142e21803506c000c01d0a101da00360075034450002c00d0040d40144490202d030120140000782c42c2046459052801c00e001c50156031b007600e05001400381c6980408044403203e001c2d501036152000ca680400c0c00c612482c820159195903668028081511400f170801460814001080715800c0000020303070400d903075002000c045918402044040703400403501d03103174154202c41001da40d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823757257 1250 823756007 823756033
    0x30c0504020306060d061d06060a090b031b04090912090602030703030b1c03080612010605130e03090a0902040509071b020906060c16210203120a0203190c0c06030e 72
    0x3942003c2c0a0640c0004c042c00400b40c0f00030180710b1040202100456100d405d030910002044c0c05401505e141c0c0250010800400c03080e41000384901103d0400502942e0307a80c070103180e400f4486428541802841002400090038000c0b0b0b000560101d02403e00c1300c3c0c00e0200c0c0101591040d102e80f2444001d60801d104002c0840d000350302106100300b000e041c16040d4041c00c0c2145003100c4840400b140450501e1046c000541030810341040c0e01080180200069400c0c040050303400c0311034900d040403141d120784100b02d181000b80161218040003600b0302028944856904000c1d402c28000c46002d510344200060380c0718400c81c102919164401071903140510300b5020301003008001802c064000d0001c10007050241410008184804440b52040c62041c0c02d100340024420904504007441080114803032001da5004134070406030101c0111520b1355a001008240d09501400307403180354480d0703029481c0f02450b0700000c0c03041000d131003150090300a945500042d8100d0300ca4100326015980055620b60b88 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823758507 1250 823757257 823757261
    0x150510080a0903050702041415031216050a060c0804031103090f010c03140f07021201110a08040f021804031b0519030e040f1b020c06090405040201180e0702070f030c0504 75
    0x102d40c040d20b80645442225000f02e0191020004217000c801c4101d4104000c2c03039001000580000030031800b6142c46072007000c003004e0764003c0120201e880c0d1041d250081c1040340070440b074140343d68041c03000c1c461403590722405411050122410ba012a036000441441600c01004403480c06400401d01c02d81d140569004589140ca242021010301940c5544a440081440c0150482003000302209a8800c0d40d1f2050240f601c040500104c201da040048800030b0044200603141d0940d080d00c0d01d0041c591f9a03060801c1d25502000c40a504031b82420031003406982030042c030600c00d41c02511442c55590600090f0584c01e5505000a041031304042100a45c4003000041010010300915008200c40324400c009021690b184008120440c0d8034a581764406181405119008101c1e0010780907410100700800c82d54860700c0300080c410780d600e00005046a019110000074080042c0c00070528030b441c2d00c0860f4840d0307001d580c40780142c401c0c400005100c05182100f2800da80d031181421307132101c1ca40000c0c040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823759757 1250 823758507 823758521
    0x120d140d02070c170c0d05070308210a140f091518060c0a030b0901121b031a0405011a010210050a0e0a03080a0605010801082a03030c01150510080a 65
    0x40d04940800c0300d1000f28a04144000182241011881d003078000c1c00340c4103140034264002c035802110446504808540701003104003c0301d40045840f030b43e039103075900c1c905130031110b21070a0504409070301c1c184022280a90302000641d000c22281520b151501103203103d00290849190040f54060203048601c003039401800c540003414010710944030407407083c3d040c0c2000c004540d40000e40c507002c5022049680d040c050b103880c21005480d00c1546504000c1101c180803081d52010344100c041c0c9620600c8000320483c050b0040d0781005851300c41c2c24280341078803862082a2025941582041c0361003031400303011000001700c100160020040407015000c0301010b080c3c020400c803c3c043d0350f10107107855080141303c4a018144240e075000f00a04d404001038080741c20301c1c0c01a604204040d4010320260400003000d882c0c1d00141007034640c4548554000c25440507403604250340500002c139209140440540002585101d0200031041c2c2d80e8680080c401d403120b02000e400c000410a20110325031058540c0010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823761007 1250 823759757 823759777
    0x807032406050f190812132403203006060a081b120106030f02041a07050703021e120c0f091509010b09040c020a03050306101107030f02120d14 63
    0x740c43e45c1e69607034080e050a041032a007000401c800079040c1c02950800000728054044110203040c10400e15950103604c0c1413603011581403550710360301c048003024100919198603030409010760b5604ca0141c010300305409004115141d04000710750f5244298000b11034203100700b0300a41030342e040801419040f246407001a140b110001080242c1c183c09510120081103010100b00d5002020f524101c0c0007070440300000083c04841b0b106103c1408080c0c440010204034a5070840002d44030794a5042c11810100250700c02035115034501054040030698100000c4032000071288446a0160b0368019034a9038015801158001040981501280b81600d130b2540c020401580e01c00c40c2898000c0454072528081c0c120203800310020580108520b0b25029440e5100f00c988090071214603541e4020303002d0300020309158422a04100142c01151003030582e446c070101c001e011250040c3d9242001f08444114100603030241a800c1442c0820907400035401400385003540d0780c48450350051400c102c0310b8005900107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823762257 1250 823761007 823761049
    0x5010e102f0f031b060601020a0201050a020f010617010b030604020922120503161107090f0f09081e040807060e120f0d021917130807032406050f 64
    0x4070703540000c00c2280c2daa0304031600c001035683c0c580620030700100d03c074402c00101841e40300b0405c0200a980c00304130040c810760b0a080c0584c690b49055026401d2002c403604480f9251700c0e0003400100c1c40040044110002881030081240424600c01c4c5500d03000300b120007a4003d5290f00c0843c8150503d40314407801070495040d041c2e50755000d540d03510050041100082c00107540801844216900861a04041c49990810341a04591140d801c1e484044030702c1800c0702c00d540d41e4a0911100780b56081404211040da80c100090b0741070f840e02d504075400182d4042006003405d0410b0042890b60403c039010350b25800010403496182c00002c440c1d031620f8102040d000f90f01000402d2102001308210641d075415000035120170020b01c0c9000b4980302070801e18601c403502446561010810a0811f0760025417030350f0b4480da0300c1c401c001c000c07a80005194042d40d81c0f03110743c207000000e209206403580d00c40a0348802c0401c0b07e02c04032034418141c80303550091540c000400c640000440c903042a1003082c0300c0d990761301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823763507 1250 823762257 823762337
    0x7080307140c090403020c130e031b010b0a060203041724060102061b16050f06010b0a030507030903170601210204090e0703031403041506060905010e10 67
    0x5045400c060310840c0d49a0540c031907912440c4003400b000011101c10364007600c1528003034400030369494018100314012007034202041c0d041c0e031340d42d0000b800003d448001c9a90b40c400c2100d50b45007404142d0b0079140f5952030080350703040604d02035040703070106c66159005604240c1440b80e030142c40d20074160602124811040e0000380943c0e00c003606082d608403011503580600d803070700000e030030020300030840551138082e05d4051000c03180c244103031508006500b01c01004c08a01e85419454542c503d42c00805a104480000a5101078070000340010200350341c0611807902c0c0c200054041c0c0e103040030028003145008030b01106034a110f064241d8070880c1403421380c2c1c0e51444d503500b0b6511500c00400742000c182d000903007400701000358002e894980246030004c002d220300d10f0f2402420fa190550001a00f488000082018402d2314540e40d40b40c2402c141041101c0c075690b520140010005110380e60110b82403004469903480c00c4081107640d50603a03241e84403070310400a910041d884801098419200d45031103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823764757 1250 823763507 823763519
    0x2b05040506281104090c09180c0207081e1e06011505071203050105031b0d080f070c080703020a0e161110050c070b09030c120d02160f0201080703020f04050609010207 73
    0x10700c21140c0f00d40c1c03c42d99a99040c84440f205072020074100c00c1c10b01000040c1080044800c001c59550589210ba0025a01c041007404078240032040d84400840d2045400c0c0034808010502c0c0c000360107031004200c44170005900e1000701c00e90b0040d01742d45841c0c0c2224004002c0c01107041c441f5144081c080c9010361900720300e6680c3c508140140400000003903a104010700c00e6040400500c607524582e6181c0d0130b00602a600080c0400c1a8600d00600c034000216001c2ea581b4420010780310b2080d1701c108541c450517181c0101f14ac0d200c809110680c0b04500b0710000013035981031210300c0c502440000029441d00000e0130703803d1301c7c401c3c05913004036154426406440c005491a2199900590100b01e100d96680303005d04100010000c0902144901e400070007903510a2100010511842070440c030354035460310030241c0b0460090103044148191280c1e40b860b0101001030035070000703840d64400d0721401010b441f0040c0c12400ca01a40030700c00302c000c00800043c80503141c8000504109801441211041500c8203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823766007 1250 823764757 823764761
    0x5190e03060709090b011103180604030b090a0b15060d0b0102160b0c010e0d05030a0c05071a0405060903090a0e100f1514030f2a2b0504050628 63
    0x40707202000038410f01e41401440614012070300204401d02e044901055801c41d929140d01c50841000500c0786030203c13020094071444196002960881300346a40e9281c070807a40307070315042451404c680071a840300c0011610001048990107540f000f41515082540b08042079000305414a0890b0552180301c00081c44200001065000303007482c042201e80b02c002c11643c1a0940f044001001e21542004c1c7c0803940040d030000a50390301842100002c41d10000d0002d041d01d03680b04101e0081c051180c3c00c0d8042c0003030044403201d02d0017940304004460307017551020103c90f100e004104240317034070217022032040000741e00c0c0413070890300301d00d01d0315031500c0c800c0c3d4840700c620344034103d43d001244004400301c090ba51035800041c10342110b03d821f82400c1c514946603003420400700c2c0080041c000d6105030303411000c104607a041021381d4048401500c0d69a400c203100c0150306400c0e100c04090285005210800a40240d40101c50082c8d5000c0c009100b140c0764603084801162001081d80c02c650000841c40401d410b070742c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823767257 1250 823766007 823766011
    0x3020603100609082b1214010305101a0f011202030108071a0a021207110a03320618240f1e150a1d01080c0a030305190e0306 55
    0x1907115030640c518008014005404651010300b40350420a03005000c1d40b8400c00084150088a00030210703200250f1054540003045114000e542e443e1040c010082002140501c0c141c80c003c41c04c55200d0301c1d06125450588144100c05400128035140c0c4031640c4c1444031841d880c044050504074072900525a03014100c1e0000d0b40310a40b6580088c00070051214030100030040b03280b00310000343c50b15483e564040d54689400c4030845540c00000f810300140030141180c100c0034140100b091580355a0307824030984800e40f01a104c0d000c410740f0808070303440307030750460303803240c8188a0402070407103584c4d00d101825100c10714044100e81400b880c0300f000f1001e0403071101c1500d84a020098031405003031055008107200c000401d0b140a00104c2d50300e0700381e0050004070071544680c03a00f02c0410300c50321000102e18000c00982c403e42c40c81c40308002c1540402070441c1c00314181c42010f070881d0018103070b40d01000f692a249200290104034208140503d810345219030300c040c0c07021400c1054052945c2c80200b0324080702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823768507 1250 823767257 823767271
    0xb1314070302100815010804020105210121021c020a050d030302070302010b0616020904020102120a02031c060501050d02030907051201051e072f0604050a110307060806040b0a03020603 81
    0x200080c811071400c40500814a600c0b4508001c8500e400c074034170b0004107030248510781070144010018085a21450480e075049980c1c01d0800012072240190f441941401e011383d81584562020001e00c8010ba00740c05108150001e01694006140c902c40c04011204400d0a07600210081b07800300e555181c40d502c5c03001080c403e5400507a00d84032070a0084c21162406021841110200030405d52141d000d25001b1003650101c440d80a243c071544010307850700c042c100300208440700c0446c103440426004400f6007900441450200c0c01e00c2b10300815501140c49901540740810070a100309d0703001c0000303507020751390200203d02250401c644442c0050040c1d2044007000ca0207030744030b00400c030095154071a0500001e2070035400303411078140160003404049940c0e00f007154200040855000c03502c1c5401180070150702e16001c0d280315040034149130351540103503001030740d03440e021482c0c14940f03040c002246c2c82241d41e180d03a18030460b141c1508000260854562a550044280c42e0120140e0360b400000e50084203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823769757 1250 823768507 823768513
    0x61a04020c0304080d0302070206040e151c030e040207230703170a0320092701120b10080d12020c0618010605040b09040b041403040305010f050606090a030b1314 71
    0x41380c000c2d540d01c0c2600c0700600600700360040c45040d0040c0c94120580b4140c031030f24030446ca8950340b12886401d001410051079640079251041140050f0b100c078844048440c025601d6401120071740702408280c0c412150000c01d0041181c05154200c0d80540328208884541000e9440880c3e50307450711503001082031102d81c14030f0000246000c4c0705400d489000150000c48260303104220042205040501419031098040c044902081c06d5083c3d840a100c914100da01c2103040b01961100c000c11381d030380c248181c100c92585c80740000c13840c0511155601011206003400074010802d0106044950b132515211000016409001042d4050010702606200703609441c0e140000140d4400c01900755080c950200780581c0c94202412516110304441c00e5001c1d0300720303032071070702c03640f50392401124003107a000c5030701b101d8040030401004002041d006280c6e08600160140010380342d550400949114080705140c0c0000d8295040001942a1000550160409060f64091117081d101d880a4a50010401c1c400e50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823771007 1250 823769757 823769759
    0x3130b130b04080a0e01030b01020606040f020403201504081f06261b010e0d020f222a0804080405060c0f060a0c0801031b18050601080601020309010c061a04020c0304 73
    0x16038032100b1080c56085c2480c050145001c00d80010f515100050305183c040d640750001c020810704180c04840045501000064000c0c9002803403c440c90780c0510207038441d14600010810100600040e1005da860410140000d0400c2003107010710201600c8203084d41c6611500005840c1010030340c2e52510082480002d95011152070b0400e05040d070903c0918425030107020a1851a60310201d21408044241d032100e480c50b610340002240c51003103072076040e80301d40c602c440d0700304420f502c1c4042081c1540e0f08005024a0444120005028409080c06e90711441248a0300c54100d104907a0950480d00802c07500345842d131283d0100f9966070041c0f075955942e60200307c200442c003004000f0168800d1080108101034502610010004403040c8006810849001c515201c44021201140014586040c0058a201d000c030541d078051300044a10501140e0428009500c950020040710b0240b0300581d1100b07420406560b9600080003c0417140d440740782201d041d4250f503161440107046030340044009507121 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823772257 1250 823771007 823771027
    0x109060c02013908091618180f03051605160e010e070e010f0302090301020a031d15131412040e0c070812040204020d060f090b0603130b130b0408 64
    0x10a090200102104040d00c12150741c9001c0320714100c0f4081100d142400d2103494280915291103610507480c442081c01410002c1ea10b05071a4411080800002060212540c00da07880000d03540b040d81c0c040d2506826201c0c5400080c440c01c001e000c0750710207550070b8140e81c0c80c03510390303038500720341c1d600b51485443c00394006000004590030064018912840295000c0c6024040108000051403603a814044054803211009000b50180d40c41618040c00841d01ca154525000300a001c0011400703c50240c028402c00704044085408841544829a408260348030495400812a6a110181d450420071001d480103180140300040d00065014181911907043c114943d1080c04060661520a00c0c20881440040d000c0340554030345c00015900c0084580d240d001050180c0701c0d045030142603500c3c0010200d00e00b0201440c08058468036503082051490380da062041f240301c01c1e01c1200040c205070320424001194002140d41c0000560f0004440580c135643e4881440c0069904070ba200c4000724605803a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823773507 1250 823772257 823772291
    0x20a022d0709020d0f23130b0906060a0501020a1112030f0c0a02030d02060f060607060222030b10030b01030f060219050a0e060703080f07050405120105010302041d061302030109060c0201 82
    0x41500008102c02c40d850340d4500314411032880d10141ea102e03c2c06c001040741500c0d058680b030164000300e240e21a480e2103010039807200400c440c6d03203100d104450404541075200003880d1030004c1c4d100042150150300001042083d42d40450301d2449444104500c002d401d0213040623005440d2460000c0a01050901c10142081181900141158426402c00450104400c00c094016900342c500e160344a50909000d4041d120340200350300300000016900603901c25000070a01100d00403140d0741d680d41c032003c4014240386420711001c0c2c21790403c03100501c04603a551111588031845408014a4070321040c084070700f43c0e49000d51510208001107040c0c0001604841c0305014110204d030f180d80703409803079a000303405288040c01c03000001e2410030015030078034000d50484004d4507000700074802c1e95002d4003115011703020900040f8001d41c1030101803c411600491000501e00e5090090021583c03011204c1440200030281039a2640d00c502d0040042505c034803840b0360451699001144400410507800b0f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823774757 1250 823773507 823773521
    0x30103020a0806040305040e22080307020d2c0d020904150b030111030a0b010c0c15170103110607290103021f091505070204052701020a022d0709020d 66
    0x2036504083c04000010360710004540c20703100e086400d0301403511099405200c0a07000d18001c111041c42403111303410b10145078040c0d4403c241560032248105401c50084580808217520544000011404801d404107150000d03088824043d1152800c140d0503000511038203020b48040d00c00c40040d440901080e000c6010f05d90210300305078001e11091143c2d017002401484014080c450076580e5081002d2680e10500d8034950700380d0803104004489485056001c0300407035a00301e000c00304020820340307150400c80507a070074122500013844d0281a40c40b54140003d0764404031b0211010241282411100d5103540f100ca41081d031004004a21507045105014280001440c0103404140200c41c00c141a544500090300752800d09210000a107a401c406a42e240100900258020708090070402080170744207109602c594510740c44092100e031003903000e00303e105000516006800508012900e225040c01c503800001c52451451001031201c100a4200503907900000180c039000034892440ca2050b0240403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823776007 1250 823774757 823774769
    0xc0304050f0312010608060310112205150c070b04030f0b0903070c03021309051f0c0503100303051308010e06013f060e1b0a0909030806010e061e030103020a 69
    0x1481d0945580c0000c143d200144901c0d001c00910000003001e94606201955140110402c14401c580d500d0b405208103030400104050070741d4900103001a02407030226a40d00311803000d42046464480074034604820f600002c100c0407540718201001076803104400007000150301444034040742200390310b80070f5020640a030410a0310b6009203c00b401284210f00e100003101d0b8101c5603c4c84807090a02d108015020004010f40603016045190f031071510803000d1040c04d124801c5042264101d6400c09444a000954440000b41c0c40b6140c2480000d01590082005655202e00713201c41d15a942d02903425100889000c9255411a000401a64400841f1285841d81d440a03850700405442c068201004404030740c50030001d00092194140001c1c0c2d0310140780100c910094a4500c01980c0540d11001d00800c0142c1c0110401c54001511074180c0c032410720019815038400c040c40d00c1d0407004503607200c11116150390103841080803250047c41d00102c8814040c00d000210344a61443c01009102e94040c0e20103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823777257 1250 823776007 823776013
    0x60c03061f1b02130f0212060108010e04110411030a0e0115050319060b06070b04030e0114090d03090b030a0f050c040b0703141e070516061d0103020d050c0304050f 72
    0x41d4260304a0300381c1100e080c1c100100002241c550001a85000030555224145803611148441003821900185900030f402100c01d440c3e5180c0000440300110240b0840b40c0b003e4554012500181031215051007030f2400604c04103082406c409040b0a0b83e0040e521030215030340c1e4014040305110280207a022600d204d0300304204903841c1c4404a91680722120100d600288039030708040030005039134880355045002426040e02d031022891f05004803a81a00c0580101c4d031062a5502258850002d104840401409482c1407185140600003ca464503070110b0a2105c0408040385608002001e18402c07070b4400d0000c200050000d002c0c1040b03400107440318a00e040d04000901200715040e080719000355261070304d0706030845a80300f00012401802d856000003c0304413040d4800c002100080c01d4058010f40a480c2074150211504c026203503039100d1140455848a610b40ca040100c0d11004c100040c10704016181640142c0064111030342120500c4004101009010901c503003000040c810400400007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823778507 1250 823777257 823777309
    0x1c05090d20010e010612021906051204020d05010908031b07080406140d0e0d08010b120c0307030e0703061506020a0b06100912050c19181508060c0306 66
    0x40140380c8580d5032141d103500c00c1030307444800885a0035441480e0010001c00204510703a1148441c0003110200e0354103070b2042a08031442c402800b41c03c20318400302d599036242d0918002049164070640c6000900503680003c0b40408080400e80170f002e80c045680c400e00c1c42c10b50b1b92905035000641c00c0d121402c3c13203121407004d018000001d80c9000c1101d09840039400d11004000b00903216020034460500c0b11003021703060121150380d0100c000307040030441c0144d4450303a80310fa072121400e04507030151500314a0800e80000110b51000003490007150050325905d00411400c0c580c4c40c10780d00e8040c05900c11a442a0354032100b0084080e0301486c0c0014102a101611111145071075440c00d95601a0403240720f2421010382c0c00003140034540e590020443d4003107a030031680050504079260b0403480a164010b05507440c4011384210b4078076140c01901c286090001d02070894502003801441c0600716842c6000d108100403a00e50303c1004958032440794000070603540d2809500f0300c14906600c4085140ca03020740c0c84 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823779757 1250 823778507 823778533
    0x9010c030b060909151305010801050708190b0103020f1b0114060a06030b01090302121606031b0302030414030325030510060f0221070c080c1507171c0509 68
    0x10855081001c00c440c0591306032124000c0022090013000d0195114880b8440030400c1c0c081c0da0440d60403121048020030207980c2d1404142c401010448180002d02c54017401c0f0005c095281d4403015071840e06140c010b050658042c3c0d110301c1c95100e0400c0d4403107091030b01801d0180d00024040c4d084e075140c0d23401c4820300c2e6080c400d01061003049540100000e0684500c1102c42c9a4411000003005680082814808092411b02c05440c0c4001589e007260084c40303110302003429070207406403405140c151101e0056501001e141103009402c054003c0303039001200c4540761001101000a1406204400c150071203951280c20034013169004c2d0100c803000e041c284020009095070640041084507423074105580c10016000c0100c0c200040414200d59602c1e00c0c050604401c4000c13005070105500c5101507101ca5919406001d030368035070080d4603030703031001221540100041015001c3c06046104044607400040a00e01f81e5441e40c000349a103801440c00340709c044c61240c0daa402402c5d08450944007901000780d11503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823781007 1250 823779757 823779769
    0x1707090e1e1003020612090a05100c18030203030a110c040606020303060a12053711121203011502070e0108060f1503060a0222030f03031401081908041d09010c030b 72
    0x1031044404c14010f03c0007501000d130903c20100d5076a0710205940c2c10700ac0c05000d030401800821401c0c40010300002d19010503198904140d07003940d030024000c50404a01e100200c41e1030800012030075042c06042c0b18005251900d000f480007518258014645034500070042c491014030552048885414808100020440102d946950b115066941076251180012144070810300c00c00c2690000c07039920181000c1c40300080d102088501c0440d054855501c41c440780e250f0300e8401851b1026025803c200400c82c40c0c904450000b001301c81801070340c0001d40e40d43c25000841c10240c1c0590400d8001100308880d2142030426503a001d03011b441721016120044010035500da90050900d10000e1b030001c3c007500c0028201e80c1c149030f81403116081504490301c03442c044501b030701048421004203050188a0b0101d1400ca00c141d816200d1240007002071140e80c403a0b91058607484001912013850411000c105120800300d4608801d01004480802d41015140706007124800b4503c5c0e0b007014900206181207668070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823782257 1250 823781007 823781017
    0x1050c13030b070c0206031503191104150b130602010b0103090809010810080a060605100302120c0306210102090a0803040b041802040e0f040302100501061707090e1e10030206 77
    0x2c0b41000b04241e550110640e4440420800650b100b5404410040200400010085d50b19003c0d003e643c546c50b101c0415145e02c4060b0f200060486000010180e028200380d407018400c503000d002c0420065546c0c0e0040c3c0030320741c81090400c020041d824014049290240510030f0300c64003e2908001c010040d40300c0541d24020056280e04025100010a002025039007219000d46003403030035109041c08925000d0000c2c0361500c01d260003244c024035003c0845010784207a0b0015407084c120031038035982e41c4014100c00c0d0700081c011944626036090b01031001403480c0010804101c6140010307034074901c5404020341e10b0019480a45280d204000601100c20440b0079581254040010001500b0911002034040d001c1ca82109007540b00307203000c0241c50705c15118258001c900036025603141e00c569208002c141e810900465001c241e103800744140c42074582445d80da1114240c501140e2207901e0318400b202980e01507405101c01d0681030f040b640c0e5228604112b50300a40e0500245021034034650100b1164011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823783507 1250 823782257 823782263
    0xc031106031009020a0c05010c02010207030815030a033b030f06011401030b030a05010f0207150203060a030809120610060f02011a0d02010203041220120a02060d180c0801050c1303 79
    0x105d080344003d030003003004808583c6c3c000000c3c46401c0030820028000e42000e6000e40000f018180400d480541010307a0300034141c3e002d805021354800c907840039950104c8004000e9640b0580c01c1074610310081070141c1e42001c2c0780354103032044c02041c2c103400c00d0319142040168100d503030071190041100500895494445103400c7c200492103446100000c3d0504d418680040c1613542801d6489031417038020744c0140fa400b44102000e0705000c04010b0258100e00044603001e400c4514a039092010415200180c00588030041103503102401b00d08a5600300001500c040f0210a5207000910460341c20282e100d035181d80310303c005c1011201c0c4100c42240000d1401416006821200340a01503903c00d000b01c4001e05040c811501520303c251030050701e28045080c001c3c20382c0c2390300020710300e0781e01d0000700c1c07940d03840b01c508014003030241c5980802110343d100061344003045a660124000d000351106844004a004900000d4564a000e18850035104014000008110f04220540f0000240401001680e030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823784757 1250 823783507 823783511
    0xe0709090b01050c0307050114160e0405040c051e04110705060c0a090803040b180109290d06091a04060605040b0304150608030c0c092a04120c031106031009 69
    0x9040801a20f05103d40c07a412091400001142e80c244070741500141ca0341400c034442c44540d55500116074a41c8002c1c01c04c040d0008170145c4807181c81c0d1030142c01c10350f00240280c80440e4540d0340e0301d001480c03100b8815032001c40045041503c1c021031805201c0c1981810054051030305d0444250345031038403840d000b00014500314011407003400c07445c8200c004d24050b0513080103c0e035645841e80640c0d11142c05c04003600c07042514030200020154801d00c03400341150041d140c07000c41054594100c407091030b54072803408450744083c072655100c403040c1e000380002032011640006140c544024045098400d400b4031a02680c102001000707090b60080842c0c0454146000b100e0700c0342c07110301c1c084059081c2100c00407003040c00c00e54007103840c0c034001c401003610408250444000d002004284800d100b011600c6a1124030030f848080311002c40e04c0d00c4d40a54408080c0900d01d070a84401d404108483c00c0c20050b140e89689010504c2001605020a03449240454929045161034107008d28401103d020300707403d940e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823786007 1250 823784757 823784771
    0x1050a0b0f180315090c01050a170a0e0706051b03120f07020102070c0e06030d02010e06130c05040612051b2b021f090b070f11060d0e01020901090e070909 68
    0x3501c1070a1440b00d01000509440c0c60485045258910010945031034003140030f040c55622031503000780e049540500b22603d410003070080b841d0680001c4800200050300041e202c1c01310580f610303400e0080a018145a440c0c0c035864503407005880120a0080100c11202d1f4400c10a814a9444400c0e01079406401c1d20428440303a5185401240603025200004040700480f400c045035034521715007010300c82e03075080d0211003405840c454100d0a0303400c0c10040340340a41005c0049450119400040c04c20356001d1708500b43d9007650f40740410304807441540100f141404d61a4076608000050005150441e0341d0f00049940f00304040c0058126600b550306460408982c19605c0e4400b03120010002c480c5400408410208007403040324000002d0703490020000500803d00401d20030b2000041e5141c85170480041d40c040c0b2180e50310000201ca00404495014805003c000c2c000c3c003460140b60510142c101c00076803108030090003d00544034607000300840144407800c1101d9030354040b61400490707140b00d201003114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823787257 1250 823786007 823786027
    0x403080702060a050d060e0402040e0118020f0406080316061404120804170c06041401060f090e011107030905013c05091314010b16241a01030501050a0b0f 68
    0x24172641203c1c1034610f060100001d00c0501c01c410036440345009039401c0c04a820061066401c80d464555400c1c503546c02a903440c03016081c041249000494054000034803039481d4403003145140c0110001040c032181184e0414201304030340c05105079103043d0b14285482e40c145a07503403d16442e41d40c81c0200c02c00c000040080e040c0141c09a00c054070030740e090003070b0b42e841382d41d07070645521410704a40c00e0391070111310000603500541c14801e080444030b1000b07009000c14200082c00001d400d0804501c80c5542d201c3c12a542000c0512004040c000d1294450b000d0076443e280000d031a014495007034034071400089031605c80c0c51212841402d0315046e80e070882c183d01040210b064640b40175039204113070000e080c0300302000c01c03007223075031140f1001c03c030141c0c07000d20907a61182e210580340304a0b040461400d502030000e4000512214100740540c860079804a030701018540400c084a034440000c091300d0b88241034180255130107224040c05003d00b40d0780058804e0800001e49203074429403841b0120003070006000c40c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823788507 1250 823787257 823787267
    0xa0b130b210c070201110f1203131703100f0e0c0a0c0b010b040806090304140105070f050a0b0a0507031a13091b03021005031905071e0906030b060403080702060a 71
    0x1101d00307101181d001506007502c0001282e00001000c81c0840c00d54048071800b4400041ca80342c40f400608000c3c54401240c40780140e60ba00094040c0c507103a0310042680c00003c458649101114803580358594580c0740001182d41d13030703441960026908496284003400591031700c10000e9030000c02e0030315265070b601c2018030846a2042c05036001e0888150a000400e41d80c08000003882141d0701d43c0708032035454560b24941a100d11440c0b00706486021003540b000003a5001d83c0c0680041ca020303582c20320241d4070365141e003414254000381c12628040768008102202d03485206154000d4803a2504200c00c2800c0e0101140c02c0000d408800e110b40d0b0381c0741c1d21804209454010090301035006161144146140a0480c0c400001f80400c80c0b180f406c1e40b58080300c0d54898030543e40b0480f090103040d42100c0c5c03a10604002410081e0400041015444000a2141004144150300402d550b55140e0262806000408550340890800d2250408000800205580d001034030302c00d070340440da620b694000c2900c1c1910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823789757 1250 823788507 823788547
    0x2010509130614010207080106050d06051008010203090a03111c03020c0c041b02010605030303190c1202121501090b03150d050706170c16030c0503090604140a0b130b 73
    0x705241030160209241001c01c4200b2901c00d000c0e02160340280d00d404200e070980d02c2c9070241caa00019a0a0711002160703e58210580098480d19004601c940345c1c8069401e82c1d00855003c010b07076000c3e9030300e00d01305640704c22070441a00449000c0c201003241754010984203940404030404040e004180c1c100560018004043c1c004402041084180103001100c049201501c0480002d5442c01000084900340441200c1c422003440740e158594100825034100200740b40b0b40080100704180d13214262103200c610040c101c42d1a0044c8458840c64002d440d283da40d90800384d4541003000c2c04104001d10482d0006494229050b101c0708803d040b01d01021a56082c00c12034013820030320a428000810340e420500d4202010044c44a021203540e85d5042c105151185403404c1c07648104481c0d2000101e803007001d01c094054840d205903807030002c4010001d1341030f4201d42c214090b01c054180b255a0145451600c1000130030001c0f55031801c0450042d100310840c0c02500c10748418410014030040b00301d9111007201c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823791007 1250 823789757 823789789
    0x1e0203031f26060106030c05070f08070f200a0b18030f0d0807030606092106110f09030f12070b0921041e08030412080906030a09021f0c02010509 64
    0x4000c846030a4880400d0040200d0501c0050083d0000441c0403442402014901745e1a0f440b13840c40e2160642d5480341c4a89140025181c2c2c203418010400055452050001e909001d6441080c991403499a0b020300c0c58030030343c0c0d4944240d00c1c0084c104000002501a91144075010415900c90f05010020900b00801803a10000301d0150158545860350030104003070180b0400d55042051030f48130101a00d05214600850300c0c9080c50a11107400180c49890060b0264030503140440e51203421800c51265030000e41202e058a0300100d645105030030100400c4105204480061141440ca007149010310700c1071480203002a1108030000342c44d407008019218041e032601049121282c11800020440d810500401c00070329000340d001d4034402a4503820b1415115400c2c0510b103400d2406010800c40f049100c400c4641315424000042d4076900c0d00e001e144140980d0034007140412030b078410001d0140c42d16046c681209505007003040d0003a0321100782ea254941c2801c1155a0314501000102800390383d42d801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823792257 1250 823791007 823791029
    0x806011e0b0a18120305070b1e0c1b06010b030c03070203161b0506091f0311070b072a02100c0501090f0507080d0e0d0204090b090a031e0203031f 64
    0x10420303240c3c0a41201610410801260501920303848008441c85040c68007a000582c184014804191603540e0320380c0010700201001e203aa2034010210312403010441d82c0f41c5000350085001022905c006020400c200b08540250016604201400529000c00362800d26882008000200402d008000300e83c4249102c1502038151f00e0a171520007003030310306110700c0407103003011130300008030390418905903071080c00000d00c6000399000683c40c81c69180c0416400b0401c2503181c070000c1e07850111050041a00c2406010b04042620b4854005010788020004c0ca83c0305400f0302c110044001000d6141e5181345038112200303e002c41841000701c0d006e46160001400551070b04580d034080007180085c03484894441c1c003c3d50f41080da41d000c002e48400194540c0d20205000140c0d84080e881d0440651004a1000f00001980809030b101c81903048421034030381c10b20342d00c03480045007070542001c10b4052850500340c403a051000500002900e034003000d84408103d881c80c0d03411040102d0340d400d0300b20243c0041e80380c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823793507 1250 823792257 823792267
    0x1d030f1501031101050c0309010e01180e04060501060801271e0515010e1c0503130f08061f051e03031801030e0105090601030f0f0b0a02041404060806011e0b 69
    0x501a1100020b20084070000c030365500d001d030154014029200d15030004805541043d034548010344451500480c8941040039001060a0540c1c07001207803005000480c840462074902032408400b120410b811490906c15031000412040714549003095292503080810038410441d03180100103010030b03808590181d400700344001013a01042c0d00107482041c4421803076200d240701c0380c01919075040035805240c000300341000010f842c2003e0307a00201020720490489280041c243e1404101c201a900400c1c9000712201c8204840041040150741056090012a211009880c203020541300203203d50f600608010b0603c000d4440d400e004680c00d03900c081e083d295103401c1c00e0407040b824642c1c1c5008a0120f482d000c09210720307030014410f01d80f003400d51000822160b403d507180c1c03076070703008503c2000c0b140200841200c070002000300340d070180100d8400c24090385550038020400e50348482841800d0140e407800d8010400400000384042c115480038480001041d19801052010b24007604100c01c8140d00182c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823794757 1250 823793507 823793533
    0x50c1903061521060e060d0c03051e161203030506010e031b150c0d030b12010213030b06030604030e0f030f030708030604050606031504050c070b04050f0d09061d030f 73
    0x244806501100e48543c02d00301484062140c102e030258003c14204c07501c00b034005040c03402c05083c43c042e103030f020720500c00960780c0e607070b4606184c001440d1800e02c0301d040210400145000030403080c03921040c81039040306520b050141122801c0c080d55070203000c06485002080440c0d00884140e18109006400c0c2c0d0f04500c1e4050620341004002a039030b40c058004001006062a404402e13241c101d000d06001e0004801000d40c1103028281ca200050b502106400c02552125000d1009040d01ca081c00582007049185061085a02d04000c00941c000d810160800000030340c084250043c255040300c144081216180109140c503554112807440c80c400052200b0070311246002030351140c0300c21541030090303503038803c2444210f000a03220501c40c01c1c0a43e901a08a00e025081365600980820380c3c2c2d030600c0c6058481c00640c030002d850941c0e43c0d4000004090890380c040c00068846006400c00860007880c1a000a10f0031103981186103080131000c40d507031805e136006d11080040702070081c00c032294018842 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823796007 1250 823794757 823794767
    0x10c0210020d02060703150b0903070e090a050d1b02040518100e0609010603120e0402070609031112090d03080915090d0306140a030308060a0b0a030e10050c19030615 73
    0x80502003d4400c50300040c0ca41072180c040e544200e03028018000300d2901d400d00780b125503000039400f19418001c9010115008261000c09845444440010070100c442800c11a040001810100007040192402c5541c1c000b41d06c02e9684209170f05560000312a910b9101c6004100031505041c5c0c003600401900302c80a48081e00814200e69001043e10840c2d15681d2166080701d00501c030041c040e60111542204081c049c42c00389030130100141015141a100e55280390495007019000c901040d420b80003540000c10400442c2c884409040c1034514284044000480101801c2c60040411130090001907403c42c3c10f2003004c19200f01902c0010b220b041c2007401075240d008030441d0708006460078000251065905500c44036045014140b590481d09644041380e803048018480c603005581ca000008880703200780d0081220100b01e075000186088071803849801c280142c0104107015007410107100140300d0450489240d40043e10700540e09000080095014220700d44c06040402000514000c0c078a8101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823797257 1250 823796007 823796023
    0x1020a1e06050c04061707050f0a080708070e060d09060905010c0e030d05030412080601030b09010b0406090b0405092205060702100e19030f02030d1d07060c030804060b010c021002 79
    0x600070900042d5101e00b09a0180e005511413000050407149903100d49136400944250002a41d02c3d10b146419030010181c1c1090b48501000b8001801c0300c000c0203c81036103d50502c0d00054103141008400c011040000c144c0d024544a4020b21030b680c0100d0b10400081790701c01d40406610034024000d070b000c01c160241a82c80d618501900a001e850094515517105d4400c8038030540e4000f02c5080c129034070400844468400400480c141542c5d41680e05043c0c2d1402283c41c006c1000d01192036a07941080c4004080081759800304182c42024401844251799000088bd4000d140100d4246072107140b0780500d1643d220040c014000e40a10400d00c4070040d40442d0007207125540c04000e000d0204141c1150b56200324100130011403240784000000041d20907801e1650000c11441120704022203030142c02c0c00c40c1d00f0120040c0c0c80c08000203090705403d80c203200100042c40c0904019030940c1450320040c01c02600100024801660344550342d255a00445140703080a4000d481e42910429a56010b9a10401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823798507 1250 823797257 823797263
    0xc040608031309050403050918100506121b07120c1a04030815270105040c02061b0d0204030c0806070201050a231803130f06020109170901020a1e 64
    0x40800200e2400c03000022aa0242e84040e600010305280c10600002440050012410448200010304003a0789002600c07a504e0114404c008803030411404038505440c642e4440b6000b143c003840380194800c41d0b656042d07172290080008003815002010b001e0018801d0030001002e81e07030131400b0703d040e1903030000240c0d81030f92060f800c4145060705213846541d0000200c80c010001090800020a1651001100119208040d215481800390411308a480c01000302c0e40b8124901c0101c0100481e2070140507a040b0b0842a00141556041002c0203030010040b020480140707003400100094000100d030b048400031034200c4e5845505035166a50b4030f4590f241a01e180006609120100e440c881c2d29220760780e060074509040511042a02800d915400c0c0c0040c4151030001d4081040388007241c09100401240d18444495000241030a13809071851300d281d042101160701d007240c80d0b00003694101d00c40304a4016841c10319165198280100d180c1b035001c0b0300081a2104290020a29034034288203038074020b02c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823799757 1250 823798507 823798511
    0x50f1006060801180b030f0709090218010303051b0c06040306020a20030409181b050a081603060b0d02211009020906011b0f0507150e010e10021e0c04 66
    0x41d603800c00301e0740311200380100000401c99440c024800b0a03154000c404848010303060700c0007c46c6e0307400190300304241541700c8a04903880e403128030114600111318084c640c00e02c800c04e6000c0e504540340140b840c010145e05440602d1a81018844400104a10302d9030010060589a070365481340750040280d08100200c90201b00b42e80d520b4200d00840c440e0b40341d00111003100450a05103801c04110281c03000d600d014400034411040d07440449c502c0701824004a401c0b44078488117078030345030501c01c21086541c40718406800586900340f5100764040c0c0300f4102c0f07801c91340c0807458840c1040042d0b0144403000009500003200c1d0255824290003003641d0481d400b00d8000c1c0c2d206440c821820006442c1988002540090315400060442d03001d420f001c002c00d04d0b0440c0748580f2440a46ea041136980e0700450a4407a40d002102c2004040c004043c44600d145d420725200356400f070540e0029005804c50300c038607032080f0205054500154800c03c4030440910098400702c11200c6a4507203180c84149004055001d01c3c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823801007 1250 823799757 823799759
    0xa0207051c050d080a060e01140f01180612020f0315040605040b01140f09030d0e03060105040905101109060d02072913050c090f0601030501050306130816050f1006 72
    0x10303072100d071907045290000301030500038900c80c004a5132036000400e9500002d80e98400032800c0c29001c404540640345040541e04540e61440821071015190b07a91141080001c1525441c40c44120310380034201c3e40241020708240030b04143e1007010b4040c0415004195001004024014080325041207102800752020000c8a49840c01d10007510381110300315000c10003040c1f041601107041001084064042c04096080080d0000000e040c003849121060000303050343c07182100b502e024400b260041901711000c02c14031700070f552202d131218a01c404003800c06a440408265024010f011078103075080c02042190b075458005a0f0300004d4100d4a0b060720708840c0d100210407401408208820070700201e080c681140d64070b204440300a011070450032038980c041c2075810411903c0311642140100007000000d00580f0b01b01000400300c50051780300d14030036803051342408140c08405142140182d0845030180c1e03991050143e02c8909150804014940d00c580c1200b02000c800124050b000e51800d95001c0c0205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823802257 1250 823801007 823801039
    0x20918070f11010507053001080d08060a0311210607050a0306140108161103070c05030115030b0705090406080303100614190e03012c0c09040b0103020907020a05030a020705 76
    0x8a50131950381002c28400c00042d8440030910061070001011b001d007c00303090b01c01d9074182000c0103017031717000c24400c0d40100e070848001030f00104034560284003075900f14051031550711b0340000f40320b4009100d40900c509e41d40c841c002d542860140410349640d1800c550f04c0b414809030080443c3c2c00400c140740020315021000c03401c064810104128110305940f20989920b402c04000445000c03403901e08240035035040c0410340f000b0184041c02416000d490031710001d92600c000e060945090000c000e80c9001c007071109100150038049510307001500303450000c4d21010584e001c20000c1421760000c1c9524031003c0108890108183d41c06070542c3c1031a550300340303010401e0302e8a02150007000103280c02c20b000c0c0502120041d101c1d01d882d02600c0780080020585003100100250100f5100340c1032802d410b4203603028041031034208010481140d06490780100d0303180c80d440703000315100180402446000100701150240348200002e00b000c2e904441505d40e54840050065a149894415240a41c0e1461f84881003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823803507 1250 823802257 823802261
    0xa0f17010b090c090607061113061715030304090608010209030d091404050a1d0a0605160909150e070e01020607170412091701141018020918070f1101 66
    0x10400640344400b1502c5804105606800c8025050b8000c04203200201c0401c00c10b004200313500141c400215581c40c4154042007404509070848000d200a501800340c60500382058298440030318030352011201800c400207411803055a2141c2d240d00d00b03014000c500e43c0010750040480c614201c0840c0c125411840381620081c02604c9101e12801d0a03403034038215420550440b944c4a14030f1040007511702a10b00d20f810395011402048491a402800ca800822080703200b00d6411252070b40c002c0703075900c2d10b0410042c0320341403034000d80c0b00480c0c1700c3c841c04c0103009803218070401074004130b4402a200e1400744c0c0000e080440e0840414014403c0130b000c1500b003401407a1000303040c0c05401403100700d50380e5602d903003102d604052417110411040d9007000462007210110019050685400410104582200d280c01480060811451842600303020042d049030f10084007a68040342c2c6001d61601c00f2540018501c00301103504041d5401e05404200c0240c0c1c0c801802500000715842d07a030200f812880b58142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823804757 1250 823803507 823803521
    0x13050d05030403240c0c0611031009020c03042624040f050703050304080f06160203091203070204021306030c0309032c0a0311100513061d0a0f1701 65
    0x81140c00400041c0f003ca09043c2d02c44000c10842e10702c0d06031480c2078002e8581100d0302c00d500a800240d0b00c040b6002044070500614800492a080b03403070441c1407500e10071400c0402c45c414140030960028003040000300a1042d40c0003050910040441c1c8012040c200755000d804a010078000d0240e4500b0700000c074041e82030040d984162114032105640d40c0c0d0341c2c4214a60348260159480c1c8115203000001810030801007014041100142c000350055000580c0fa00f9000342c00c1c1082a07040003489411249d001041d1001268119015480c005010071820700714031400001035003050000442c0141c440041102004656150f0f070b080081142140c402c500f202c0b1020801400103052208041d41e03c00094403c0030001c01c01143c2c52500300004002514011040e40100e941c1700d0a80c17680d421034900b5000740000121607040181c54004101407414100086000701414010013002109420b14030200d0002200c0c0081d00000145031180d15181414a5901c143c162034075140d002039800000c180600c00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823806007 1250 823804757 823804763
    0x1305010602100914010603080a12180b071101050c1b06040f06050c0c100906060f0303081909050a050a11011b0209040809091303090b030f191506020313050d 69
    0x6844802d1103000d009411a80d009a8940003034101104001c0300a00c550402035110340c081c19601d1541c1c06010307100d070301101c989000c0c2c1c0b0b02d03141c8000c0320094003c1c20760303815030b5100091b103105668107102900e420340c02900d03600d0300e98600410881644105002000611100e0b001c20114100c0b54501c00da070b8131004c4500070480720b8120181d5001171015003146400c0b00058002074100300c800481186420303258604601d482d920b4200c001c0901026100c0c0ca0040c041800c01e420b0f4503801c646014100c50409040f031800b15403507101e00b010310031561340210b600941c01410740d0051203040c00c1c4280d4459603000c00b65848543c10a00c2c0c00d40f58025101243d1000250410249802142d000c00400e090020400e403036443c01003100f41b030390f0f0356006130092080e03400c125114903100d594240200100c2070741d000314800c04c004006000785060180121984110660f20744401c041c01c0001c8200603243c1081d0080c903010050001045098020010302007a400310100c41010550390020070458480310300f806 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823807257 1250 823806007 823806013
    0x8100f140709030317090a200d0c0314010204051f0c151a0901150503100e0f09060a0902060d0e07090c03240608011a040806040605010311040b03060c0703020f16051305010602 77
    0x5000003018423128281c40005109006d055500c060b010490801110508840245a44030140100b059445003102d500481c0700c0214102824000850400303a9810130942c10317801d903024040a03051050480740c81859018205810a000e030011041c068143d00000d1141040100000203203400e00f0103660f1f040300c000f101d180d08004d550300029034040d031024050380f6250508c218040b500091151023a070140202c40c07180102454640409030130081c0180c0603041e000e040c90b0410003d6a151003d550071a003c0080014000c0111001c161030158503078484480c0c039041008024009815903c04850b00408840c0e102c8458a0800c1c486c240450300c2c0110740200e08000014031840d1041170188600000b02191140f61944402d401880c180080324200c550940b030727a006204101200440b420001c0040d035041c0f0842031140c00003901c4500041803440095004508841450320070044480304000783c40c15100c65041030709880301119054001e150003246008031106007422180f0605040319081d6000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823808507 1250 823807257 823807273
    0xf05100501030e030c0d020706091202090f0601030b09070e01030e0f030708160c0b0a03140f190207020603100509090a0302030a052b0609050c0408100f14070903031709 74
    0x56000f4494119610712500c011301900d50310f04c50402030810120300303a800034500030f4900400204151115000b034800a444201044016242c080c3e00d075030045001000015a42d9400e40100c0080c0441c142040e4031442d04814030207000d41000f6001b500d00020b1f07074240241c041038001c2e55a6001eaa10318074000c0d82c41080404042451000900958829080d8028520829848600b2140510b4104040f255000102d40c91140d0705849071281100c450700c0501c41e10725100c15884002c1c840145101c0d4142d42c008001209807070700780c0c1160350040e4000c00054481c1410203006800003014003a0600802c076000125444040014100e046203605600171890030f8540001100d4980000005284d001d14a101010801018907042c0003a0100c00300002001440c05070030100740c803400340074820044070410084c810807202040c00c41170040008000f0500e40d6076600344000401441e0400000300c2c01d03000c00e00c20700c503038842081000c40b40030341c3e104030792142c2e440e00801402c502980c00740e41c11b41c04214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823809757 1250 823808507 823808509
    0x309080909060a030b0702070f060e0d030c1509060501050420160507150206161b0b13080408030307110102031005191e0611030a0206060904080f1c0f051005 69
    0x7901c2948640040c000c076100503600d81d02c10007130035015940302d000768004003004e004031149130702603400606040c9414206e110710700700840c4540310300000141c02c0003d45828041031210108854a0b0214803034820855082c442c20048004c0c242800361900c10780c1031070b80103e122000c80707046d04040110406494542802c007200d04000303a40c604401c80782c601591000145010840b0f07188c00724022503070080e00301403421030a0302c042e9458130b059010902242012950500305260480c69415901144042c88c9071075038180c1c0070701002004001032a11030005000714207128088055070023200191038501070403807481d860b2800d03070104a540b0030040d15503007010000e40c0f4280b00144010020b07403c4502000740c403102400c49600e12802501c4407034204035420088240e01c20760403500c40c0c031000003550a001100b00000e49803900075044600c55a0403501040500440c00210390320404024041c0703688894070041c03112440c5400f0440b21250389440800c41210804e4041c00780304030641500320750041d0500c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823811007 1250 823809757 823809769
    0x3030e0a06052a060709060e220f0f0603050a0b131703062d01020d18060e0a0e01090c1b0c0b0c0304050d0f061d0d031d160f050103090809 61
    0x54406040846814038802c041c28140001d45c050304031952032403041414031402901c070000e03442d036880c05800d0190407001d84030072956401110112030f0201052009843e0a07241c01340401c4005088e543d407500c07100100b08200001e88001307551086011410301d55a44050f440d806540001c0a00081d500700300ca0f00840da08080210341c0b21800512948400310002130362b800708e00680021150311050000151155038042040c14500030043c0b4003050007461000c40002d07200464801e60051209915490000d66104a10b000c054144001d03030110540e9510a4134000c0c0140c3d142070380c041108488108a00a85030583d8803005402c03242110100d454400035108940c402821044603001c03d0101144555a2110301802180034000d84d081840c01400c058084603603044881600c5400403030300000b0100c01013044901120a401c1c001041140721517900c585001c2c0462148007401b0700c2086a03031071041010814180d429078265034903429120f80040d0215240700e0340103403014400340800c1485190078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823812257 1250 823811007 823811047
    0x260a0f06090c0b030a0507120b0d110105040b0c0706080705040e0f040303020c01020703080406110c071814010602010905011407020316020301090803010e04110d0206090603040c1503020403030e0a0605 88
    0x145120448183d8400700c039500e81d0415542030107207544400502c40d489038022508548510741d41000c020320311404000840c44800524024002983e50248090a80c0a0001c0c0c4004100302c50b845a540d10310b03841c6407038880480740140706c08160500c001c94400c51007142610281d035101001a0100c0c0c541030b90701e55240e000140200c040603001c00c0740028014082c005401c16034842e858100150801e45401815100b40016000001030240040c4a1070000003a01c00e0480d00742030404074007486800a4000900b44070480500f04001c000000990039074154006440b1901800003004080101c0c280e24a01510680d40800182d00900440015041d0301010b0b0a0041c0300a000041d108040d40e0b4480039a0003d80c05094024051001c02c402c0c08400100304030803900071121400000030650000d0040d000e40700845000f060003000181c02c21150900301c0c0043c05d02440821001d00d84404000c0c043e500a00007203001948100f03280c8280c1c103008080c03005460741c680302c0314141107248041e00e90a0b100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823813507 1250 823812257 823812263
    0x5040f0b130b1b031318090b06060c01020d06030b0613060e01050f061209010c140313140c0d140d02070b090d150c0c21020c09091204260a0f0609 64
    0x1920300343c040b0300300014401c1c000710b103054001e42880d020b402c240d0540304645900645040500c20f0700007502580403145d1001e0100d6440f40c40b042c80f5000340380240502e01800c20040c0c58840003005001c0d100032900d200d03071000c0342d13075440c0c1c00c881c54a060140c0b1a0343c8582c1c0c01403201d4500502070f0340750004000207400b001429050404a00721350a440c003103003c0c0c0f07108455941d180e40b040b102e40c0d4404544d5249800c25075a0a2440c1002d00124111000d80100030b00301007400350740c07481054420700810b00406001011400b148409050007207405491003074102e580e1240e1300b032018100e4000301311103044608203820181007008860038070a1802c094041105c880c1e8400500b24042d01107172247d240050070346c0d5104a5902254942050740020039001e0b5090aa07060f5028040d495001030101809001900c1e8202c0940313540c24060710304004c0452164070082d0100b00460320100e55a900200042c0307000f400c001300510700d461540c60300c0c2c1c0002c01030b0000c58409030b0342004c034845400c13554503944 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823814757 1250 823813507 823813537
    0xb0603030d09110f030d02030412060e160e1305150402190609050112050c0a0c0221030306040f090807060c17010308071502030c070f06090b0705040f0b130b 69
    0x15450016021240b000c0d004881c1181c0300454003900e4101000b00c04c601c494107400601281740282030182d90390290384900c8c1d80641c00d400b00101005001e80084617042122401c450008181c6081c068401246014820140c8180340004a0003130701075001c00000c5400402414200075552407000d03540c04020401c1c2c0c6c010010300d904001c1c0f1150209490000c0c1f42030340d10301040c142800c000600300b01e882e11280f5559810b213002d10400c2d4016800b1912205200c2c1007280c200f0b9854400700e80d40e6510050300707104040420403061340b1404088025032244400b180c007040030010150300c0400f200d60f032031005000c42d0400d20441c00000c005a210020035000741c01c003861041e04101d0801e1410509030800c481600700030451104100c2008407011612000c0c4000394158501143c6803103241c0512400a40301103007810241040c0003140d4403140c2132036081481340a4a1900038005419580b082c41000110200d8180002b090403044081d1400c0c148000420340341185440752840e030340d42140103606101d42c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823816007 1250 823814757 823814767
    0x801050f0603220b0711033f010803040e090102040f03142806050f07021b0f10091706010506070308071e1e050c070303030e070b121506070507030b060303 68
    0xb900c030540341d048840c440d0440d0f411178601041c008000c0851414426007075801440902074044400d07124005c40d22101003040c0840b000d58140c03a074441200032031038215060480c00424050404070050085d60011a4998455282d01c03440500301c0c81a40700c0d4841003444001d003400094040102c5440703280303649003120526552a2059480301c1a843e04143e4070066800c542002c000150292a5221296003006101403410703c401031b440c0c4582c9004440c0f100e071450f83c0e00e4a1651480d90403803009801a11240a14840560180082d00389000303400301c1445550000305e03002400030b000c6060b0359010b8001130406001d41e82c02e80d0905809800d001c1406800268681034500445111150071151b5407920b001c05620b680f00a90010b03161000d0b400c10000f0480c00300c0511000a150084030390505e4000b4031791491004c807604140c12070b003005170340400001d013810518070f1040803a8020109182510707800c040701c07410040144903400005003541c00040040000c03075008902e2541c8202c024098031f10f00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823817257 1250 823816007 823816051
    0xb090619020c0411070b0609070210050109090c150c030309020609220f090f0210180b090907030b1c03020106052808070e0a0b0402040b040806160801050f0603 70
    0x406424102500682c4108448070042c505409002141844900c6081c9041d9032510385007000e110041040d80111003881c08074101900c00c001400d00602c2e014000c0003035584981c0e0b42c42c00ba203a0420b05a82d01e500d480408071710340c0701c44a082c00080722151600030018200f0342e0140c016000c1910103076484a401d00503080c8c291500a0102780d01c6040c09001007003012404c11000443d070304441411103d80c035251b90140043e58450540120903011184402c0e004005941261040d41d01600380802c692004400207044200d0700c00b802c02481c0c03c490040499840f80310850032554402d031180e600c10101c0012085500012004000c030501030303c00410683d0f2a6408510126803903c00c61394035a805907000d44040304050b1070704000e070107602c021f4032050340f07000782b610041c000161003000c0e102d40e20080301d80c1646e202d9045038004c00000f038100c0e44880d80c40f0041a262401228400540c034100d40049030070034070881245040c0e8000400c0c001c8000041002e1100700e82000f81149600c5008000504c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823818507 1250 823817257 823817287
    0x40b0607150509210304020604050301090b01061103090109030807051005010f030b0903090906060c150408030f0619060302071e06020c0f1b012703080a1d03070b0906 73
    0x351601a041d9003502040700c4000000b00d032070052070303242d0300e803c500c141004a0300074108400c1000740020301203841e0b0304d46000180c0c061007a0b9004552541c6080e004c0020400c0c00014503040320101d44540250710303d1070030302d030b0b449100b0b050b643c50020340015002d100080e0603030041c100541c050b4080324034805000a1040458000381c20220014884d20300820410981100540e400040880514240320041003c40c2a100015028500ca0840800c040350300307101c02c018480d0305441c0714031218070900f042e0600c902a6481a980642c07510301d01c030001070050410511403c0000b150b0800304102c1e51030034404a00035085003030229070100000034140460b6502c2582c903e00ca070702540c401a564208060030303900c4c09207401d517200105d809c0a4004c203504101c2c0c0c0d4040b000c91a0a0820030310300c18800000d01223501c449040c01d00c860148500c044280190703174000c2e0810080540381c4003010f0030440c0352031081c0444801c0b05907256100e18020301103110040040c1001480250000341404030703100b0f440034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823819757 1250 823818507 823818517
    0x30f050703051f27150e10060302090a0504021b060421020a02031f0b0d201503010b0a030b043b06010314011b02010b0306010e190c050d06030f0b0a020f030f06040b06 73
    0x20014106007d2001300c0408180f201d005101d80c0c10304614002040700400e41d07035880d9101d564403c0d0381c081103d500c000c80b03d400c000c2015082c04203603581803030140741c80611500c0c01c42c030110f00001e5111000b00d01c640001486401583c00600074091800c801d01c00c650210050400605119256400d194403074540c50100f100161050240d03215044030080c10768048900d407074a0508c03e0701809100810024104101c81c1510030010082c1d81d206d10842046d405000c0700020540c02c10300c0c10880740c0c140715041c144954076160106000c4510110340e50302c074000211242400d5542c1e00700200400009078104001d5544140c1c6200110300881caa00c2c04441c7c5a0080348800051b035142d60784000d0314502031000501420441401e9030a5081c404802c1000c0d4608540344099503550b5401c1115460050b001e80b03820380340210013408955180c1c50b052000c1103140720212040d04003030000c28003030074450095031544400d440000b800e681e6440d0500e040c001c0094070a6030484e036520700c5c20320300d0348400000300303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 823821007 1250 823819757 823819769
    0x90705120c1806091b040b0304030c0204050907140108060d05070b03042a030b1b1b01050606072112110309061602120a030f050703051f2715 62
    0x10254451070140007103204542105654110030341d040001c0c960301c1c5100075401422961007841d040052400700c900e0f070b00c180c0c2c000c9040d8401c0030040000b0540e01c0008080c1e040e100b550203000b03d4076108000e1341d0f5190030340145001c405510600076000d520400083d640b00000030072a0072040a1078444d181071141c0c6400005c3d41030070020401c81844007509807020a4000c40c8140340c0b89100d144904101000140002003510300342c2c001041c5425208401603101c0300c0f2003070000356903005003200400d80740c01410540c00c1d25400c19000070164640300068070b05540d084071095101440700030741054481c01503400c0b0402d000140b0408030941c0d04078400c1800060036405040d58074180b00b02224507080c402485180340b5404002d11050a50307001c51921188080500703059105d100502042d00a0841c0a80098805140804200800f40e050308254080c5c10b92000660000d1b104d2850f40484c85410f00800391045100310302082038281c4d001d20350400310b5134460700198207209001c0509030b40b02c10358800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 823822257 1250 823821007 823821013
    0x902100507020108100e1815150112110d090317130c081906021c110301050a17150a110304050a17121305010204030203070801090605010e04030e0909070512 69
    0x603100b15600300d080942c03c542103a180406451420041710b100c038800074002c4055152401c080c1e102d400d8100a082c5414002d015600e10910b003200034010300d500f0480c00c45000459042020500140c00c1c4107048103508401c4001d03103020303e0381c040701000e00a80c4204500704139400d0501d001085003108050301406410300c030151000c2590170110300c541b6035074000ba4800d8211401804a80e1151844001c90903402400503869060740020404400b0782212019140360600c10000304c400c0030080110305850045824410254032803a0559004000314950306490b400048080c0c1d00303005401c4c1441c0d00c4000000e012503c2c281c1051242c110b9001a41c0c1107417940c2c00080f0305d00c10010801103081c02c0e14158a0f13140d05041040c0200112508051b00b141c54925004400038240f10084d0100c2c0d010395006000c441026540e5003030310f4020480c403101a40d14910300000400c0b984440c64000d8010358141da944604540e0100400c03190200c0a40613140c584074220000549403540c020055600000d6406 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 823823507 1250 823822257 823822267
    0x1021b01020f151509070c06050a0b0604060302030417030c1b120f1c0b281e140a12060b010c1b08100506010207031202071a041e05130f09021005 64
    0x1071180b504213a50ba0076489608868100705e61998406a00000325802c014081480c3d240d0306010001000c10500450f007169000030089801ea82540065006e94885c0d104030900c40c41c086200340d01804180c40138a020082040201c42000000b50300000303c1d4a0351081d18003262404a460000d40c0c408118109848400304a4203c0304210110a03140100a0700091140c000480002180040030140e01400400c0700c4030800941000c419205000d003080301002240b40101d884403074441c4103148120b412a074014055014181442d9901c641110603169041d104200c2c10b940e00c0c1301034501041f001d4100b12902040301e0100e401c0114a04070302243c002c00034603076402d0034040d41c14540088000e40361a81400180440c590340090907204036a000440d01c49285070248080703003170070b0003640070711401860b51803181c1500d04401c5c010001c4446603080c103101c1404540c02d66090000b24864694041c51440075054080703000d0b0812215020316440c0021541204c2c2e0018012644c9180088006600410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 823824757 1250 823823507 823823521
    0x8090f01091103010c1805040e0f0a032a0308181f020a091d010e09122116020c0108060d150501030605100317090f10080a0c090501021b01020f15 64
    0x205240000405e450a5460401d61078020b0208004921034940550ba581c1e9541526000500c00c103581c565180c4260f4011084a08008200b0101000502a204902940c0003035038050b4903003015055505031101c5400342e0710052018444011007000035483d02034005804414014201d040461064900005803141c0c2e0004005120518903040b52121040c581c092085250710703803079050304560311211201f03042d50743c0f0b0143c0c3d41003140d016000342416101050b4601440300240100c00d04582c0034000c01c80e503603070303608030f07a4a6501170380c6881c409604041340d80035095204140a0b43d001c0700c05010f0081240e1145c5e6030200d8040d81d54101e030034145d07483e0300500802c9640d02503290000d003210302400d1080e0450f1141004851800105c8000100002d00e9051945814566021118004000810140e20030901900c0821b044880440c285d29002d440f2031841d005484050a88030706a00810b104150075080004285031603102e24194401c0001200c10310714200130601186042d0140c003084c03030030100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 823826007 1250 823824757 823824761
    0x10f09020702031002070c0b040312030f0513030f300c030905030d09030e04050f1503010615111006180c0c02090f130c170c04150608090f0109110301 66
    0x500084891401004414007583d07000545070460241c803240142d4440070f51424003055511580321120340d01005ca000410b0200145002886076207503101445900c10f8409403408403501211500a140020000040404d103e2001d0703c01d1464181404c0080300c900c0013200c03402070b5400c5040800540b142c40507000c000c00300e000d03c011034001800e091101d040d6650351a1707104d0084842c03000a46030342c0d0459605041c460f1899030b8181002500800c1181404170709070368202c404480d441c1c954023818252500714101482503d08a900c2000c0d84c0c191079242080498600c0080b03810515940b02d034410840080586125000042c1090b4902c50790b040812910003082d03802c2a10b1039014400581000b0000d600d8000140d42e01c0404510b0040140d90786102d0880e002898103005003a1441d138810103e0071800c4c00c000248496080d00403180d52500c0c080800c0706843c440381092401401c12802004803900454026420410800c02c0c0c8000d00b41d400170b01c03401c552030290241c480380e2500c1c2e0651520b080c28 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 823827257 1250 823826007 823826009
    0x7060902150d140606120a060b07031115060a0b09130c09031a15120f010e06150a082d0f0304050406060809060402130906050a1409060103030c0f1109070305010f 71
    0x6501c030f400c40d142440004c1d0480c0038000e11000201c4010001030000b40180d4002e201426110590b103480c0c4440b824020044031030b0342c03103507002841040090b000c07600b8100c00da1886210014112075505083c004825841c0e0020030a060700a05000f800c10b020a6150013041c5000189035940e4120741d03d1810329641c143e0003026030140094a000a110102841d81d4155010744410340b80b40e500a86020042c505d0003400381343e1041c0a51038955000c0703400001285150255425611035813504c4550010030590780c64502c9a5000ca40c031201c140e04800c03992054403a481204030301070256641100741441d00742044045043c0040d00000713010f02043c5003500c5024003620301481c00c0d28591902d1400d440e514540540040d10071510b00e03000b40000c0d221600f0100720a98000014055130800d0902d150181c00d001c0300002b9446100340000b41801000901d05040301d03010b83c4c3c5c4030315a130843d072a56803003a0120f51082c3c40028446220703007007039241d00071218001c1c1a150360018a2b0741c941a040c295050791 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 823828507 1250 823827257 823827281
    0xc010c140304030804060c09050d0c0e0105010203040e15120706090303031803020c0f040f020a030603150903051b0a060203010b07020a06020105060102070603110c010e150601050307050f07060902150d 88
    0x10038818080801e910a104c60380c0554888400076000c200f1013816078040005921a9030f101d40b11254800410000e034141f0b074100c5844070240d00d0a80d0f20b0340d00590b281d010750b00072400c0840040b0001075030520310002c00005890050f0182c600040701d100b41c030b800e100094204801103041c04004004040c0e01d4841c00041c0d01945540650004145d0340007907d030400f1001440c89080b0544040c1210741e50b55010f00100d640c402400c40d5074821146014020b031495205c19100003200c0801c031800030303040d8000e04083d140e065a40c0d41c5000500c0c010005403c40e003034001003103885116071501c006500752004501800c07070402065207070103040c0304018841b400360b0060380440e4180818046640d0300014104256485410040390807281c0114041d0540220340080c0450b40c200b20006081d040702059029041509456213a800c0c1c2d10301c4010b49280c48207070b60041c0022020420345160110240260040070300c40c04e03011031040380d00c1d00043c00b60080c0796000900c0d00700014144403402158480c40c00490302c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 823829757 1250 823828507 823828547
    0x40c020a2006070f020f09070201141008120309010e0304030c0315140a0b0409051e0d03110306100509040c03021b0a23282307150c02060c010c 63
    0xc1c8100821003500508000074920240c03030800c401107640e4402d03003441080303003d4860845458400030090107445641328840d24031140801282c48900d03918900c10544110000411000006c1400d1003443c0c1e00007066621b06541c0c3e4403000540350802d200820086008180c40d40b02e060450400c1a0032212002d041364015182c00110801c801c81e01d40031541c040001c101c0021a2003c05022401900e04038000a0081c00b6405550074100701d40311007181407020003411107012590199003501181c00c0040c02c03100200050002401a00e010444500000d80914040342000c01d2080070400755698004807902280d00858003140c00c4140308050811a1640c00007404009015101c41040c148010082a00d640742c1c8641d01003142d4007040000e07070810001c4080c0401480c0041780c0e09100d04103200460304d082071607103c60a0000154040701710520907201810f4484d1502d1aa480d290903101900814480560440400360391341001410b41205100d00200c1c0c511410341005105009a905840342d4403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 823831007 1250 823829757 823829813
    0x210150f090209010909050601120509032208070308030402180f06010e06040b030f040f0c0e0a140103031e1101060612050c03070c06094403280209040c020a 69
    0x70381c0c000307020b0041b40c40075207000404d0b80f40d103001207540502450f01d04810605107400d0040c020390000060030040c0e00e1582101d101c50f0030921a0b006281584034420309603100b0304080c8081044c480056410510041c120001d0701030031025012170600c00c0300c0d50301c0078510040400c000b95070400e4001c1d54004d41252400e00d0103041c0480060755000140c03104032264403400006040108106009040c260041c0c18054280e0303450254200240c000c03075407a08101e007480b6240540701d48001940d0705903689500c50062031a40c0541480c4c0042d030350641c41c810003080ba401103c0f450700a00c50303100a080b881c5c0e03070718200c00e44070032080c01507400160001100d4581001084201d83c0d11a0500300d9055108070041515102414820ba070701540c20050384441035442e0080c2c42c055010b07030654145000701500064859504030300310300c440c001101c48450340118003214092100784218085049001c2d00c0c0c0041c1445803c00105080b148460300407005a4840700034601805018038030314507a0120358101e10201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 823832257 1250 823831007 823831009
    0x160513113f090d1e081305030c060106120b150702300f030301080307140c090a1a01030c020c060d271b080a021c140106060e030f060402010f0210150f090209 69
    0x40c2d0100b01031081091840c080b94041c0c00c004258010240c0000489462700c0c4c4582c0e0320350300c5010a22450340032581d00d425001c20350602d40681261140010f2052000c0804050344c2049a80080c400326030060b80b01c80314050b4188122404002d0640d07800103c00241c0d540020070b40b80150911041c8095403041c00100305500000046400c0140e00c56001d420010f51740600c0ea1500b400111000d43c09010f620410000c034040f039200e440007405581c1001600045a001035088a00414220006030444101d490780c0b410060003c000c02c501156000440850f019090710a0541d40d091454903c2c40f211a0031040c4205542080039001c00000c2801a0703e180284241d5a8110048002c1c01480b610204600000c50b0152450b040350300404102c10302810050254021716060191748040740401480d22090304001515104580603c00104910b486540064030300030f205054410840c03095142c4480035029034010354000c440000c40c100034250418018920014068100741d040314030601c403c00003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 823833507 1250 823832257 823832297
    0x50a03020d02060f04081c0c05060a1a03010908130f0b04050d11040903032f0f09210709060605030403050d0b030f160513113f090d 58
    0x89035412541036901e6407030791010950a01a0900c502c24070500440c00080300000424848000c4400701040c0d06c44028203042030b20805140200a00380b41d00c01d000264500001da40407041212801810401401e28003000900b0b543e40e104044400c0c0c10085140c003200c4009003d090007030100942d00452043c10700400c0c0b1000c0c01a840740d1441200402c845d5000d01403100402292004090001c2c8448040d505025015080c40760200c070704401c5143c040704044461190450940e85001692031411400c1e80000400307070040001e0341d901076104c5c00400200940c0152141c0d843d40c100700500304452900f0090000c68545900c10000d0040400c02c000009a0104c01c8807a2a2240b4100088022158020a24084a8150549562060802c0011804ac2001040c070496000312220658410b0030380111084e6400c0f507030013601c52442400b40d8403110320035003d15500c00c0b5615807005a012407000480014101545001c400c0b00b404405014110b14144050091f0544505206600784959464800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 823834757 1250 823833507 823833509
    0x1a130c050a030b1305070503100e430801180203041106030a20070b090a03050403330c021b0f1e0406150801080c010828050c0405040c0504050a 63
    0x701543c0c3d48145400d9034a000041100607075043c001c0140b03243c4440c01810503442a140c43e1404441210001004104102d810780301e680c160403014811114811100166510801c1814090030240c00c1c100c095071a090301c1c4401c1c40715a03500c1000952504203030f52006804500e410300328034010810400410719080110050340c50642e00705903250395146480b03005105031007100c101d81d07184103003072040c25034848041d01400d07014071540000da4603142ca086544200909004001c10000c0c00104007040050401007004196416001c042c10701500c20f0000041c58032038606c0c55180e856006007002641080040340c42c603890a81c11220b211745000083c550b08950180d980305800302d1384020b01040482188401a04010300103000f2107440d030307844001000c030078845040000d601400019116400003268900383c18103868684803034071040d12840c2c10001c1c0c1c0c005c1c03680b02100510368580c940145d11555100b41e2540c41480d4569007803c080000382c410f45c2c0302080c00c000c001d02040c070281c1e6034011924 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 823836007 1250 823834757 823834777
    0x9120c0f0212010f14060102161a0a14040b13050405070914060714060a0b030601230f12010501060813020609130b0907111e0d1206091a130c05 63
    0x2402c00080c2c0d00d00c440c09400c503030b800c042e8018145480c800e1030f42c0743c0509060013581c09800303684c441042c42050900358103182c4107103440c52031243c150142610b100c81c01413401c858607140c6884480b0b0b1070b0030036001c180d025078440e0010900004100c4a4482c9440700c3c60090002150b0038003840c200158001c200d6145401051810311210814443c995506c90032241015880140350611410f101c48003034a40c0b1003180c00d034440500303207503034600306160101e0058180e842c500b855078015500f440703400e03d143e040002c04940001d83c16402000030390782c0700c6c0030b084401105000404e8546c1030030b200410b2a007000d052a040100340088000060742c0b03001c10380e80c2410096545240060109102c040545205202a90010001014440000e038441c0401d001490660200e44400344228a480540080c0003940c18082d00300544141d512849403001808808220030080347c03a40e1108150750445a2000260180035551841910f440c01c201c00394899002580e03e0410021952000140c040d1041612003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 823837257 1250 823836007 823836019
    0x70b01181a0f3105040c0b0a0804060b0d1e14030f040317070602160605070203030606030a180b0c1201091103041e0803040614091c0e03070b0a0309120c0f02 69
    0x800d0383c042c50690410b00040107803414203158907120102c200400e4141c80130780300c0380c141c1700c00821109295000c42d4480c00c85035540c201c4550302c5403600d10003850300c21000b5500c5925800841c01180740c8403c10580f95146e07112030641020985451007410f020400801c0080d0002d1040388a0409003c0580f4101c9400c080c00ca580ba0900c4903900060303201e41031004009034400702e10312448040440e003c42525215090800864640e05416079503800122a180d41c0200704000003403040c0106d4012020f00002006050036581141d591400d00da42c040340c424002040c00308040c800851201e9086004100f014030402c01c9104850500c410340c0700c02003000c0e22030355444200c0728044841c400b038442981e4011764070719180d04040c40c0110141c0741c05030340000d800c08039a01003401c4080114115100c40120311185800d10b07003081d41519501e160700c080941c035005521000030072858406c001c2c88030100d203a400146400b0705252141381103c0c4e02d00080c1c10010003101c0d03480003a000e460041c948580494807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 823838507 1250 823837257 823837279
    0xd1503030e130e010c02011508010b13111204112715011b030918021306120e0a050a0201140708090904170c0106030201112803020102070b01181a0f 65
    0x240540300c01c0c0d03d040625840c00e000c1d01c00140d4103601c0045940c0c005080c000d00c140e034515203030b802c3c0c41c1706480040c2e010070030000200d04080070b0b40c0001c400380e14480c0c5050030a0300754588500c06e0481140c00703850b410f1005805103114581100c0300c0b00200100c4464040807041002108900303a001802801c6195004040c05103580c0079240b006414842e10700d00703000c81d440e01d1400a2000c5520301c20341050350482050010f4ac201103000381c85407000c03c1c601003503031145050000c80c1e000004012501307a55545000810200300180300c0c002c0803e002e2001070815003181c1c40014058000c4280100303d00805000032000202c561045660b0f1010489403007115480764104114140b800c40440e2203503610004a1071071100c419080321048034000d0705c03512a8450b503d00810b0700c9800000280c0c1d0119444c0e002108034088800310002154003d10005042000c00d696606844100380c0042004240e000c44a811200e07050040790000b9030218803e03815076072140041040c81100c441c02912810500d86 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 823839757 1250 823838507 823838539
    0x14190605030d09080616021f1514030c060a02300307121b0c080f0c07030b0a0b01020d08010506071a070e031b01140d0906060303050d1503030e 63
    0x1100028080040a490b9285000c88001d80004018800c1494a0090400041400e4542e42c204541040f0740d40140c0342081e141e4092085a48020074501e21150351084e0015455903540c9064020b0300165170221468220b90003010300d01500242c0341e45c0700d00410003014074120b0380800c22412020b030040c0100c002159202c4003032016151840310308105c09000c0200710070340340e01050140e00c0c404101c41c02c1011842541c01101040d51411020012600c03540040c130018440034001c0c214402200400f9041802c08848582011120b0f4401e8070340d903038810180141080a8810984031510034001080e0103142000080c005000500c00c0e540b1a03e0082924403c1c040500d0f41c0c1300300240c91100b45ea544d0b281000010380281864000c0c035010340704000e4031b00384a40c0c02105411b441c1a058407140c01d00040c500d00c4044951104c00d41c54185070b00d820b0130300c00244050050102551203500c03082d4403416a8625002246c5070210500e60840d904402003000c284c001503111240c0340150f4645258a600107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 823841007 1250 823839757 823839761
    0x100b0c0111030708010302010e0a0e19091415010b030103020907140c010c021f05042d0503071a060d020901030201030506060c120c0708070b0d02131e15031419 70
    0x701860301100340000c20004a9035000c02050b050324401d03255071141c01c0748c0700300b440303410b0403140101024100c084000c03d801e40d1440c02c58103a42814014040f5074003805690b124400001804019101d511503424100780f030501c074601030702606814445034210342c03458001a80d141d501900c94014450b4403135075800002502e00c00c849549256000a016108035218001c4d5030b850084407500c00360000e5004d240c3c10782c1450050b640529000b02c181180094600286005050320440d040b241100204400000603028009010458011103021404a200c9403400001c00001000e4500c2940071544040040e0307582106035040d01c0c2c0a1a000a40703a481d0b10201e42d003441810104002c2d0321a1a481140b620350b10401030110f18003000940748025030764000c440d600c461078020740594200c10300c9207a000d80d066a002d0034110900d45800d051a80c1d4842d141c00c450a03800c0c0303807801b4241c002c14083c8020108102040710078100f41c501049035401c20043c0360801c5402502421882d04940c5803050402040c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 823842257 1250 823841007 823841021
    0x319083708042a05010f260c04120b010f050d081804150902031b0a02120d0609020f090109170c0d050c04020f0a0f02121c06080601120303060509100b0c01 68
    0x100035003848016070200b0000003c224810140003a0400c6042c04c4107910808401011902501c0406600d1040344003203001c3c3c11009208080c4144107200c0003860500c81b0900c0035042c0c1c02004c8a40c1c03294104048401409481d4002d203000e19800042d00c0300280c6010126014400000b010103d405c0c3d49000090141144e40c48042c0f64020140c070104d00f00109a00441c0200e049911860b490402800d070139034980640c00030140540c00080001080040c00d10082c94912840c5000041a03510b030652982240c228080d8800d08050109080c5a5560040d0414002d00240c80c40e005070b449003019403e0740e8000c05074074140602d51f99000081004030802400c44000b100800542d280c07604070b46804e1007034014000a01c00119010f5030800c040d070011848207401540100b282d49840c1e154480107800000c403421007058030b5580c6400090f6010705010380c5010300005280700401903241c0c20000d050b500b068101c01e12440c03c0d034007403240003074a08403050219405202d8440e140c0707800e40350b558018028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 823843507 1250 823842257 823842293
    0x60f012d270506040b0a0e090a0f0609050c0a030c05010e0f0301020a0831030507260a0201061d0610050403060c2f100b031908370804 59
    0x315158441e08800800c108508401e10307400100900d548440400050340c50142e21190081c203008400e00c8100351210328540d0181106088401050042c0e0791524151503d0505031a8143d83d856002c0070040705000080c114101150001d000c0f07829070b15890780c1760095100d00f40c1070048500c56002c0135120250321110040c0010021501d5501e0002e01404500c0c04030350144941050300da80c0c1d02130600c20b034010071111242e00304807411200c0300d95081d140c6a01081c0141d5070b06c0c00e80f14013420b50591120008a512400000b615120702031144041d00792203054000b86261365411903030101d0051807024480d888401240d41501180d1390400945141c4102e4002514140c10400c0c070790340703990f04601003102280c007800c800402501e03010f54520701c076a41200041f0043d0003000300c01c02c1a1100c0d400c95151064000d040c0c61420060b8820001d015a10304e034110750000d40403550700b007400d0210003480a1149441c03269080b050103524800c881010389114903080c0822800070400f4070411845010034610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823844757 1250 823843507 823843529
    0x102031923040507050f01110c1302120702100c110a08030a0603140d0e1c030e0406052806020c03061b0d0203042307290702061b060f012d 61
    0xa003403e000d501e0303103032a01400d4081c4c51030361201200d55120701c00181d2903107045006400e41501d0300c01041031b10078550664009094003440008090f0b030300302441e20701070740b0243c004100c03905c000903402c6c056480d1085403905101544107000780e8084082007044a09502c00c504503542d031b56400c1000000d203034a40024103503100e14580158003401c00260483c0c25070b003949400c0c80000141080082c0d00f0a41007061030418502c00c40f4a0010f0300030395802d681c0003002440400c1c02521035000c602c1d07121441101850b030603c494410128201140c40e40800340c180f03071020704404a907400c0860356070305028140128403030b8085c9040080704102c2d41610050542880195038905041c1040c0c09240010311712040c03049203102840c8a410030005074001210340d240c01c4024501000b1751030b0142e4170501511401004010428940103964910080c0204c070218001ca190130440c0304013003454440018400400f40001c0c0700140320454505a07141144c004280030b0301c0d01060000f00f041082041743c2e00424400d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 823846007 1250 823844757 823844761
    0xf0c0403030e0d0b10030b0c13060518060a0306030c140307031e06060329010f090c020f07120b0c0c06133f0c08040308070f21110102031923 62
    0x1440d408180170440b0700410302458140c41d00e6a60b20301e0b511403000300705401c51036130704200040780c0510040c0941e0507400301e803200014409400f0908035030101240d600000d95404060082083c0120000c1c00b81c0920304100161940030340100340e441f941804094256150014181500d0b42d160542420955102005002c100d07500c1c1740044842140300c1c0300500300c00c0c2c200b50f01c1385060303040081d15040307510200006d0206072420350500c0090401d004000b086018002e80d262012504100940040c4191081c1141c8a2124100101b640381c01800c90341076840100315031130301180001919901308404103980c2881040c146051244100400044180300340407200c0170341d55444c000040c0d20411403d0310f00021154030340d102112680c1d0411001000c11006000c180b0206500d10f014007005032150800c200740714002d4891002400d00c001804692070709001001071800e9005140b00e441130410b60080d401c41c1000e000141140400341c5040aa050b0344d041c1300304c1007420200c0760484460000b00b00216034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 823847257 1250 823846007 823846021
    0x506070f14031e0a090b030601021216210e0105091305041505100308040306020a05041a0405041406010e0f0f0612060901050603070804110303130e09060f0c0403030e0d0b 75
    0x1035000421803030f0100400c030403500c041c201c1103c12070307004594036a6603101460801090001d20740001e881941103102c2c40010410a43e01c0800034a40c445a800b601d11108182e481c101141252002c2c43d02d980c000c110840700540754000c4200c9030029001d0070801e031255070b410041030038075090091038203800b4142000d01c8140007010741d500818800f01b10040c000e907a0f500d410045106180c1c0310050002c0c10400c81000407404c02ea003d0b01d610021032510030303e016640d010f26543c06800500c16440b0200010b010443d82c500786c03240c039a00440300039401c4054581340e0000382c20000c9041d0950300035618420240c6442c2c0d20b42099129030500104803584580618256071003c1e4000c680e4031707010b0314040d03002003490706d89841500d2080030b07503503500b000554483da10044101d40b80f236042501848140b102040c00d4481403082405404020301c6801e1500e0310074891403410001a001d40e440c11030306010701110910a10031682680d4050620211b641c9000380425821280400040d02e140b4080c0d041c4006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 823848507 1250 823847257 823847263
    0x3020703090f050102120f040e09032d0405010c0302010b09010f08012919030b13150507050906131e080f0d0e0405151f0f050909010506070f14 63
    0x11150096560a4505854601950b8038403018080d00303002d03a01c12083c0175000c0e840080101243c0c001e586441e03062980d40c0392a104240402d403501e8015801c007041485c001c03803200200c82910f4412080b0040d1801c6100004441da01c298014141040f41c1114070702c00b454000d400292003410094001507066942c0c000c050300c04941406080c480e075083c220040b54000840d9515442e0030050b103a078488540f0400100400748100201104282c145008004040f50140e01c8440c41a01c1c055103024030b483c0d41c5d00d403840040300f003030040f00740300d61400c014001100e07840b10035a87c0d60f9600303403440b641d80c6507411124060004140d101041e2213040041949060000080d00030032203040300107e0b41090000d491039074030389800600b10000a01500c140780910302c0d1a4201e60381103056103a540d10340040c100302003920382001c0d0071900c0050000139061040254010b48010841400746411420603580340001391011506108152003106c001c5401d03420701504c524003080f45a48240f100e01c281c00c00c0c52440361 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 823849757 1250 823848507 823848517
    0x1519030e0106050402070503040506031f08010203041a0f2415090102060603030708031b0c1009110109050a0306020c0708031215011409010305181015060302040806340302 75
    0x1119424402c00080c142414001d8801150b0b00c04091030601c5e09190a20015401c01070500e03c1500004441070301e251098001800901220800982e90f4900f0b814507480c0c0301201001c0c564901400340402100d1110441d0080d000420b500144200d90004502d0703c0b00d0040200c0703020340c400c14100040350010081c00050035400802c1e000c0e61080c1e96032400f05a224029018064140d40c41003001a01400080044070013050401c1c2c0401e0800c003039106842d00d41003075101030fa01c146548260308010f00c42c1101c400f0014101c00d00e0140d4141e4100703004a5012b81c40c0340710052a03207070041104100500706028100c0038000031402c5940701c2e0010b40c2c8d01d12000b001902d1300d00301d8040906401442d94416120042e0010a112010346841e0644004600500f0000d007e003c6000c7c100d008001400c0062042c0c440c0817161040c0440c42d080d114000d80d082d690154496000d140c0f0400080024440c040340050744107410082c1800d036010f14024030b00c1070050907104540d000348240d2400d6940303501507010381 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 823851007 1250 823849757 823849781
    0x190507050106061701060c0203100f201c020c010603050a0b010911030601170a0f021c060b16030c110907080108060601092301170c0c0f0d0e151903 65
    0x4031455595410584200904d10700f5805901080300040c07040600402d044084688060102c0798028120b101d414110703801424518002500c03442c200f140c203090100c031010b40900c4901410300c1e2609500025944030a004d10014915402240b00581c1c00d0307084d80180001c41d040415204200070b00d00d401c1012141c24083e0f040300b00c1c60000c58681c00c90310041030300c0c851941a19045c001410207004107030302c41c40091040300070316181c80d0300d40341c00d5040f40040c20052400c130100c0d0f1108120000d4040030b036042504144051307001884406c072600010941c03020240e0301418120000e54940c10318078135a502c0030400e241c100702450140a01d00c0d5000003258100c2d800c2e80c040e1a0241c541e4001110342d00c0d002c0c81821a046c424031540c10302c0e66541c0d1003040030724105041038260382ca1600b01210010340c00707c0d080040820302207040300c001c200c207202511800301904080c01424a0b40e541c060b000100542180d13001d50b2840e000c140c030302e220003400c4070103a010030b0890742454101032500030f001e464840010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 823852257 1250 823851007 823851011
    0xe0304030206031510031127130b01031817030601090e07020606010306080a230a050106030b01050312072d0503030907062c040905010207021314060a0b0304060c051905070501 77
    0x200625200380b0078140108411f810346458090b0403008000454a1040b000100752002e1256803015030701d250500703415a01d10b030f101041000d01c10b0005021200d00c0310a40305949014001e810000703d040030000340d0030072041c6525072240c660100481d0041c1031074003c01c4410020b001400b811640002d1041c3c407491090380c050000ca43c65204683e100d0784150002089110f44c001c498541d560a6045c8040f0450001d045441120442d1182c0e0b0030b5400981c01038408111b00350041c0304a0400703102a0250440c80783d0321a2401c0c0059a40d000140301c2890340e5042070002407550a45240da40c00d2480311190843c046079201e0400d144e0986c2c03501c92601c01d07040850b0380c40020721286402900c42c600da207203030750f1403803002e138080d10043c4000b5050014003102d480d5820420b80300165140140b02107036203400440001c41603883c21000010718005004240b05140940c03080101c00c1c105d104a0b0340c02030f0702001c00308010811103400e5926010313580160144202921240e80504e40c04000303400650300400c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 823853507 1250 823852257 823852279
    0x905030f0706111207030905010b0a0b030108070801020a091205030426010f0b0f0405040206120115080106022a12060a140a06031a0c0f1201091b0e040e03040302060315 74
    0x11064500c10003e8030044426a1130001d281c45000740e01020400b4010030002c1400000800040e142c40443e40207801c41d804003000510246408012910242103040c000f146040d500d40400b514034003141c42100d440c1001d45944904001c0c0c1401510018020500302d440c4920b40803500c00c400d86450340070940c41d5031810111008000b840c2c056805060000785c0035101114148043c40041c000040040ea08044204004500311a4281d1205c3c020601c9131520740c9940d03403014006003030f10300603032180c0110b500026140a42441441103450107101e0140140b4400b0040004961140b83c80000109035014070001c1240c440c82507007100100d10172201c030000e000d6a8400c9000111000c90102030060700390590b01c83c0d00680c2c00c89500b50480c032141c12460502d44110b009882903402543c424240000c0300c0c004010b0f0072400e0003154150105a00d40d4410ba0700e200c1801005803100c000040e100d543c55054500b252074060040720003864000d45615a24031704504a0752074503c03024081405805031000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 823854757 1250 823853507 823853531
    0x627080a1e1d04090b01050d0f17040509070203030f0c0c0f1006051305100b0901181409010801140c130503030d02030403080c0a02030f09060415020a052a10030905030f0706 76
    0x800d41301c030103600070b030707175200c141d00307101c28840602c06000c2e0854002550789004004259150316400d80c038028100170303070703915801c1605114224401a0110b0107540c400d00c00d000c002c0051074850360744031000c510455207506441c0d01c0d19142484090b0f826155000f00c66410301c1b00641900402d064400a840001c00c010f0400c485000b01c82040340c01c80100c00350620280045c880e003400400c030820b01450f00008843c4181000414a01184c2c00115480c2c21040441d08609000d080240149a40d100800c02d240704401e00030052200180036014810700040c6044001139400600f801800000e4102c3e5107690724010b4020003036000f0f983c254042002c20002900d070844a004580d06024140c2c017131400c010b484d002e40411a0490002c82da4081c005000114000d41a0f809000c000c0e40107038020000c00700d03d41486ca040c02c0a00e04014101551082c00032000c101c0c401c80940c0c20b20068902d59070094021078210000c3c503160100401d540800a400e582500d5400003912030030340118003c02800304008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 823856007 1250 823854757 823854761
    0x60d0f062106050714030a0501060206010b0720210c0f12030708030a0609050702011a1f11160602160b090f120109050f01090627080a1e1d04 62
    0x72851141d1500e26462000074415800c015000072050608028200c101c0d501141036420840b02440381c03654940c0108401681000f80358014492001d80910300342290300c500c007461005014102e1000da0101840b52070380c82c1c41d000500c03011103004034847c80300510085183c03a503200040b010701c110124110711009250083c8581881030100c0011480c056050343e94103003503040204005403166075903100143c00d80d41406800e12580056000140175200010078411580410000501412145552070b10300c2400000790f01d0000c010741407031406051170021361444c010f03913507003003c001d140030030f900049494000406000d64030b14800c1c80108140c5590305254079000b038528840d07100c400d83e00d49401a0802c1c40c4001040000d00c000407440b80d14a480340c620304080100f03006d04613990380400c3c0b820301a00344208a40d00007a500a4424007040b42d88036403003085000e00141c23880360009040c464160144032110003400500b0410300314090b0341c40b000352103400c00c900052024145009025421310b068 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 823857257 1250 823856007 823856039
    0x90509070e070f0302070507060c150912050c0c10020f0607081009050c0d05070909141303080606190801030b0a020a0f120905060406020306030f3702060d0f06 70
    0x1075514502540d4a2a1040b00c00c245110a09000e16a0801c40b103c0814401e206080c0505140d0711072030201c0c20b492801c1000c2d2070b845101618440d144c441c1200008039991070344106140b80345001e42d01c40d0350100a0030309200c004a05103070301440d0301d1441e82c507180e000b18518503080e015205480c090b591b9040c003550521400c403031303400b100005541c0501849080d5401282c1140018410504041d8910090300c1111401d546006c04103200381402c03c02c03080303a4024480c2d007040f000085107090400d01a40c02c0c1580c44014001c081c42902d1000502548802081d04d03a260394108440c030340514081409005104203000c03d490154840d00056001c0080e402192410300e480c1d0b4070341d03c030381b50b840f681101d03018a03c0140b103568545070b207204030200b0010060980181d004410041e56410240c041614107010307001c0d2802d07030350040320007a25854201104100325801c03145111f02c6014440700c0300042d450780c0c80c40007940120041045400c042c1f080d4046901003000c2c8004000340ca481c1c00c10b44104801d0703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 823858507 1250 823857257 823857269
    0x3160e0111030306190302060a081005101e05090d081e0c0a030f11011118040b0a090905030412060b010806040e0a03030f1803111504030903021e030102031009050907 73
    0x10400104d14203050040040000d9962840c10030005600e0b81c0c00280e00f54801c1c041d00d070004050f5800d1201050180f00d055005203011241041c1502c0c108601030225007150909151401d054183c0ca0940380c040d00441e143d825008201d4042c8014903e46404141c110000202403010700040c13414a0b0100e0604030b0b85005090300050110790020307a400c0320510400801e10040082c1d1208401f43c0303150900891500f2924062405d44038a010300380341c030000e03043c41e43c11803081d0b0404041d144503480e031200000548450560100e88807201d0300f010381c610b10850b400507510141c2d000e013000901c032003a0300404082400b642d85203e540c0f10b041c20842a10f18501c14014681c00850800c000a0f020380d0003401d03e801d10010114279295010001020b210403600c00f42c000c00c8908000341d480190502c105080031440910292032400e1a0321b0052000c00180030081c06074001e00c1c50440004002e0a03000f5802000030020340d904c1c80d090580c54030442d0144070b0401c08a0519004c6441150301160240c00e4803c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 823859757 1250 823858507 823858513
    0x311090f010b0d090c09060815040c0b160b0f0619051f03090c03032303010803090f0103020705060a02040f05030309031c090305030f040e07030b3303160e0111 70
    0x401c10b00d41114540c0404241076038a43c0e2440d100b000101c8128015000b0910b842001899a180c4a40181000d01e1104070100c04070000f020080003c549040c00015100310600d01901d9241100a0310280046a90090400c0b0030020412203400248000a8440c0d5026601a60303104001000300d140d21f40d6500640f81e01c50040e83c0c9040b1001d01009032030420107001e00e40814001d4a0340c5850380104981d41041d4001102540c0e27000c0011140c88100180402c10b8204a2444d0f150a860301d4590082d00b5600c1e203d0013420805034800d80c42034054030800364102c0141c132120305220001900079441445441141540154009581c1c68044140e581610015003d1b041c610b07014403201241444002d420030a1014805001c000320700c0400203003010204c41e80100341da544c100701280ca4110070081c002800c16080ca005000103032920380281001b1002d03580400203c60407640c2200880b22124441c0d0540903020080081d07030030380c01a00b010f58804944490325002e030000d004440c4000651542107586d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 823861007 1250 823859757 823859759
    0x7020a050103020a210b0f0a080a0b0606120709060921020f0409050a06021809010b22080a0821040f0803060a0b0d0c0801080d0f030f110406090311090f01 68
    0x540640c00525080e90300740f502e846610171541503081701e403804004a4019559841941c031003410f154880c0409840d04482c00c0052600d0070050603614030304180003e00301d1100e140822401c1c0c48020a03030340c43d00800d0540e1001440d00040043c4405000e1090b01c1c0002e6280c100011070500504410008400d2406000a03024440e02880888400002c0c115003150f07640304bc180c0070a10510525007090311911000d6903e004040a549040b0b40c08240d4511480e501e90040040f040040200c0e020180108a20b00c088445618040007200c4c03158842c00d01402a041504104002c00780144040031b218165035114448822041c0c1205808a400403c0d000118400c4000716080c0e5010f03660082000307020780340c1a901d410700381d40c45030040c01d01030300c9194440c1d440002c00c6d03070000d181c180036000110042080054100004140170901e2840006150750f030054400e254145811106500e510000711303540d075560b10300c40100b5582c02e620042d01c00e0b5813007551809a80c9800c0002d80d00800e0152400c44c01e903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 823862257 1250 823861007 823861009
    0x110f1f03050408072406080601121101172d13031826370309031e1506050303180402091206180c03060a090519060f060b07020a05 57
    0x3004040c1041d00e05003c14802c041c00160000003507085000400c00310141100c00241c201c1c2030382c82039003215416400840050112203020101e0148840c0c2100008295140c0c11f40140d941491241010112281020070412407084010001003205500070003080040050482c50b848420240d40d0300310340c80d21104c030f0b00e0b001c0303407040c05e80c034000b101071000003070710aa5a01c3c0744425000203806a0b04804141c000310000e010400e001468400c0340e030030000c0f03150000345202d46869414042111048941840c172070005d040c4a07c1d01d40005d0359014080c3d5141603505280003a0244c00a00c04944135480012035848600550160104480c0050300840c1080d03c022070152141100d00400c90b04268284224000341d50b070803030540ca5003c0d0701d03005007070300f4101021b101c40d005140001154444d80900e01104858400268050740320f90403800010301e19905d881e120b802c2104c000d0041c43c020301c140c1610340501003194401300401c0031040302007021503501c48408031140030700c0502941c4401c0a03e010442 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 823863507 1250 823862257 823862261
    0xb07210608073311030d020a2105091e1204090504050c100e010c03030b04091202010c030c0504030b07021f05060108010501090305032a010213081009021f0309060207110f1f03 77
    0x224201e02c90030b45c2c2c10864480c40d44070481c1c000901c1d001c00181c1404c80c0d818440ea50700c10000caa55443c00041c0324929010704800d60f14201c4030039000c06111840c1942440c180300b480102298040d0b0070b0b08540d225aa00b69010240c042598151b410380564044c041807803800e940000c0480090b038603142241c40b852001901e0f002411401a002d06480d599032445554803445035100c440d00c500c4041c40f5284403030500a0844032012112000d02d85030600d1180004e41060030348049907844503407440c280d541d0520803820030480c0700303007a103034002516507506223100345400843c4112800c0e42c49080d542c1c1c2e50401141d440c2010700c030160443d0800c00801c041904103c40c902050754440c4052144440d80400585c02c982c007003d4004020917000c1c03001d02086009120b013103603007044072000303128200464001510065940c105a25880400007001d1641802a02f060310702e1500320704c04644410090500c3d01c040d01044003a00c1c0324142e11441480a440c01e0343c0018600c01032149040e01c5030411a100b900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 823864757 1250 823863507 823863527
    0x804060513020a03080a020d030e100b040e0d1e0801051c141905010e0102040f0623120702150411010c03090f060e03190b072106080733 60
    0x198a0704090754400962142d0203038100441c0b00310050f81d07841c000041c00034106010321040404250074540624801c0d24005202070b10300e02d1a1500007041c20b1322000081c0144003591840c40e180c020211444441c2e50050f2012956200c0c56047d1060309031580d100f00d0764913001340915a4020000110104040202c64400110781d101d005400070410a40c07a01f5490301304d0b2219203001103091900b400c002c0010038092841e0340e40d00b51000f0f40c182405c09481400c40c904d1801101d04200c40ca860703088034000820b00061104c200603000f1545c0f041403c46046850b002110100c0261003011210309407424031143c0d00e885103401850182c260301e00f0000454418006131000e80070080b1900020031005083d4030345800800751030301c5020340e04076010149810f002030030550900c5a02488030000106500083c49a44520039160081c00e541c00345800d10500d0380d01c1c0d0603c444540c40c21201141001c0f000603024107850100912107140c0c40c0f500701f94101d4200f401e0381220f024a102101d5414523002e038020784 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 823866007 1250 823864757 823864771
    0x61518010b0a1b140c030c0306010b090409030513090603110f0d020f0103020c010f270c1809060905070603051305030f0307030b030604030f080105010807050a1202042c0f040308040605 81
    0x180c1d040c03c081c3c071641090f860031100381546400566024445140c02c01403520705440c01d8003d41800c0d807402e200c90359a4003440711102e01894403464000c04041c81203041316041e1910b215509c0d075061301d5498980c01416240411142a400d581c4031a0f041e14081c4a450513088005140f0301c4041c4482e803e00545520800c2c595050640911201782d540c1005e02032501c4843d1103540008200740000b842107900f03005a00c0c416907a0003107180900110b1040e00d0f2074015126607051512000e0327a10f07400d4900400c2031003009446585804216820444007040840840700255009d1140f0303102c8403100c041e20025010003d0190b40100700c04410810340802a45c1d00c40e94a080015407140c80d8408030382003100882d4210300081c01c4d0710030204203581110010b40034100a00c2e19002624160002620364802d2914100c20b00c1141400c002003201160100c50140102e071400c031030000b84040c00b0701d08000c51140543c0e81482c81c0c00000d040940b00c048100e1240d42c03d030307840200c1511036032200e10003018090128 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 823867257 1250 823866007 823866047
    0x11060711030f0d0207060c050a0807081e1f0501030b030a0b0a060e04081e090603012904080c0102010e0102090d0b191d0c0108040209150a08061518010b0a 68
    0x40b0b200c4101e40380c05450003c55429016030341c0d603410b02d012000c40c0d4000030300c4400d0280074081c044e06070307501803451035000000303060401903078031423111101c0c40070302c034101a2180c060540300f00405d5803021401d51440c00c040d6101c0503180740e100c10040d400d41e422160f02c075806920508598010485018000e500054050000903d5035141c0039081c0010000310303825600e040c00040d02e4031030201c0503234000710800800c007a82802e140d403a000090b4588018400c440c1aa106507050544504509203242d401c0c0d0343e039807107842d030b52039584d04803540b940f004042d45800365103010b00301c102803081070084131886c410050007803909079529502c50107070006c043e0404420501c2032640d140b01c601d2610690248103802d4a05150003c2d01490841c502429501c0b0641000032480c01d120045e2111078500c0d4000744d1101c1100300d1031001c080400c0e840300705513110039298441e410900c04124091009030646490030703100e9138011040c42c03508828246003882030302030002e010008000d102d0300c240c10a09500c00e1000760 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 823868507 1250 823867257 823867267
    0x5030a1d07030323070f02040e010209030a2901081005100810361202010f02040f080f0604170a0903050f010506210709020f0910021c1106071103 64
    0x4001e2034046660422000b181800240000800001124070040e221300d144070341c981440e5641e1000005002030000b80241d40350031001c0400c2da020f4041d102c540340054120b0317500e111a400c000407070000c03001e120081c007513945207020b900b51070700066141071b01c094074010191803008841036002020010032a074540c1d01c0d0070300f021900f48828090704a0a80308000003107440300d14403061a51130240c00d8100002d080c00340042c60700c40ba001c07292a00c034240d0001080002d01c413850505034003401d0210180ca078824400603000c0344113041864090103544040040f214000040c0400540c3c0e0710040e1030152044081690380502c0144003002032001e1241864140780b0b4584d00c0d5503192a0000605407046c042e510740381001214185814030700842c0340d00a609080d21000307841d00d40d41307d40782c50040180040d00012050305600c400c40441c0c00703080e0040c00c4140500c25a1a0003901d803a4210701514810011040140a2512510390404010940300240a054a0300001502c02d0442581042664041808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 823869757 1250 823868507 823868561
    0x30402060702120d031a01050901212301030506090a03050318150a050a0c05090f063405060c070308070807030905060901150801060308041a0c0106030609020108061005030a 76
    0x300c400c610130300c03546011a80c261440484284c1050b000c140a0400000307000b0480140c0c1d000840404191190200c52aa1304046008801a1042071864440d05d00032041207904100c003915078074100c034001d0050703644d99240c21000d0740d01d900340014081c00003441480414244170f508101c447d000c1c048901140ea160408081203550800200c4a40040c076940e0300400102d41014001c0c0c4911105074546146040c00680002c1d40020040c55003e01481010030381e140c3c90003004c000082c08045c004440c07030700001c26a5000c0d03000011000c044885002d15800b19a407500c0e11300550713001c241d0645680d043d6036200304040b1074919004100104042d1035441c5c8a01140003800103034029800c0000101d43e0900100608982142d560f009400580c54001c0400204881c103090300c05a03034078184942540fa01031051101140680d00c1c19154551900700000104540c561081603d44e1003a04c0b502c805940d46000c002076144a07840c40d00100b441080050901039180d808101c01525804950001c00e0501d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 823871007 1250 823869757 823869763
    0xb0c03090c03060c030105010e011e032f030403020d11060403081f08060108150103170903030403051b090a0e0601060513090501140405011a0415110d1812050303040206070212 77
    0x42c0300d0884d14500000113010a590000901d80014003e00f0444e83d9034156452081e01010450017103810150b039a00402408001c088007581280f02c0340005072100030142c8443c241551043d42c8c210054800c03614400603185c050700d502240c0c1003180e00035184a0743d03291001c0d5502d500c001c024500c003c021514030108424039003c0c141c003504031080107000b19030603c02083e1411145420f10541007008400400004901a1402c0786060ba0101c1c11a15001e28001082c654029030304010814010b01c00e81c030004106488540350310003001c940000c400c4c3c640d001c41c10121a001c640d50441500308400500410380184000c0c003080d2401451072041a40d2a514001122002c0c0c0054084452902e040b8145191500407180544415009005182c1002c040c000c16031080e8410f03a0308103080000b4210640e030081e80c441100c013007450190f82c512240c000000b00450014042c8805180303041201180d0220040c08040e062584007004528649031f44c0c00308140b039009104100c0e40005c6001816480101c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 823872257 1250 823871007 823871011
    0xc030504030f0c091a0a12050a0804090b040b121506010e1005030f0a020307091406040e090604020a06090f03020402030c07020d0f051009080306091009020406110f0304030b0c03090c0306 82
    0x2039182c007401c00d8141402e0313000b0340704600310140e914002000c0400701c030b0752100e0b01070301102c0c2c40751a038030303400000d03803800c0341c100300320b000c0c025155020104001441c00500c1d0000011440211801c221480d5142c003044105d0441d407c000390070784d00c00003035909103941401e5a550001f0050500390b8405d125240023904030107515503441c001620100038003003c40366096215400c5101403100703500718980a200201009120b02c03800c410303074030800008600e50b16580116001b504200c0034220040c900700e500e0310368035401901d0882c000c24a240001607402c1c0701c0c081000640c0c010020380580c6518603020403029410191201c0c42c101c000300100001691200d40210b00c1a100e680440b0b485401410000c0c11300741e0f204508031007281054445000281030200716035000d0800c07220319502d0349444041d981080741a030000384070b580c030004010540079040600072020035014011604000840400d140e2240100e03c002008a9103010228a030400c20740040c6034031520003000c990744900580f00282c80c141e01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 823873507 1250 823872257 823872263
    0x7110a03140a0b150619030f060f150c031e1106041112010203071e0324050a140303030732040e0610020a1104090b091c020615010c030504030f 63
    0x112440d07020400c000169104e5110740d0f1580310224802000010510f00d200d4002c0fa01d14200d45444000c0c207445c00780c0c0c451034411080031001c00c8400d07181c1102081c3c401050140e441c01c035895043c110380e1a8810280707452016030503500e0400607081462400c100044d690450401e1040d5040c810510f41e8080001074402c0b800740d03c000d441c80e0840130030f1142400300c641d41c20340142d00410411404940081c0c1d035110400b00815080407024040030214020304020015001000d807801c50320319200446050b000070743d0030031540c81c100c05036986180402c569400c107419402d80c106100155a540c01048004807071800b02c40c200300d40da080484205e00700b00582e1802c00c01060041014400d181c2d04800c0180d0004042c0e824240244220030040c2d5503058180000f026442d50341c2000107542c541e6004444a142d004400d1800343c1018525207458440854803280d18051060f04051120b1001900e5030040d40e8070804030354203284001c01100c060ba01c000c8240c0600070204030000005102c03149091040340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 823874757 1250 823873507 823873513
    0xd030f1101150920070f020607051606080901020a080c0306030a1406014401060b042303010507080115141b0c0f0a050d0c080a032303040807110a0314 66
    0x41021001d0f070072245056450806000c1085500340802810000c8a400a030490a0034480700d170103200003907142c4186d0703600800501584501040c4603082c1085181a54119240e1150303d07610071551034201d014030303180c0000041c10b10000c12a406000002107401400203010303218060100e80b10107008443d820311440d050360040c00100500c0200c010a03030506c0da54000207109204043c14032852905c80c8040440d5484940080c001d5210070941c0a02c4c02441c004000e0b40d01d8940d2070503480f80c5850b040c0c0050112440001101c0201d19040c07044500c00d00c0c0d15281c2648990a161111200e050126003030f2040c0301055409052900ca03e84c050040410000c0000180191001e002420000007140560103410080d110820780d03074481802c40280e400580e03409981080ca41002820744400e50700030005070064421080a00da4080300c8c1b0a241403442c03182010103080550aa03980c2d10048901800030941402441c000901040d5508000c86005060800c00e58617916408100c40c1c041c0a01403440d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 823876007 1250 823874757 823874759
    0x180308010f0e070509240702040608030f070b0703090b0f06030f1204090c020106051309050f0c010c0305220f060906020c030d050c03070b01090507090b03060d030f110115 75
    0x5a40a108140904400030101c500301d4989040c0420020024000300d003070020209424082c1d45a000709603a10640c005103283d075448282c0102c0107940d0080768182d0090b801c202c2c0101d0b032078000004031420b102d03000507140c1c0341144c651101d05203003401034000c0b401c040e220305840300401c0ba00b0414601844074101c0c041c40703900784442014608120540e01b020705800036105100492003080030785045803401c6001280c001c0041c90106d00400e0240c01240d4442c1c58094013241c003d240da40030b03071205440f03881183d0889a4009040743c3d9014045c001600107045400c00303d0000744100041c100c403d00c143c1c400d4000c4004440d0f4080300c02c15036000791201c103810310400c000d6541e210483c8001024140080e009a1b64441d02180d00d840d4060018030522078000385100030041c08004880d4440c0d04400f102c407403541c6034a160800b601c1e05aa21301e00160203800045500510ba40442c4c2c090b01004004100c5c940c881d65080e01e08540a0040205001c00d10101c80f18410003802042000d100d0900384803091 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 823877257 1250 823876007 823876013
    0x7051513080304170d0801060e0d20190e0a0b040b030109030f0e0a030201051204050c0907050a1206050f0d0501020d0e0106150908030d021e0d02070606051c0b180118 73
    0x448412042c0a542d603001e06031700b00d45141c02184d15415158145050414441a640481d00052821000800c84c01d10440032100b01c8290840781c0402010489030b50212034448a1240d01c407440d82e01407443c0081c6014013042c004401030b841003101e020082c00c0840c07940c55040009027141c11405007500843d40403a0710140b41584455040000203040703400e10310460443e0002042801404420b1050014810216080c000104a09030210f0340090000c01603280c045001405e40d00403030403c1012076000f03070200c00540c05500814095500142040c420035070f00c0c000304620300040810276205550300300800c000d00420703802400c0390000440c0001c5550340c503203556404400b0076a407924040151600341400f8080001c0704940c01c2002d00100136840d8480c440038079003c103a00d240101041500025100c0b1503500700d0300071300262400352004200b02640c480074064240b041e0110801c00d100e07464003050001d80810b400e00e4225010140d081d54030051414024211100400b110080c80f00b02003a160030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 823878507 1250 823877257 823877279
    0x70909060b040b030c040f0f0614160602130911041409010605031f180606110a0503040504020a030204120506091e0c0108070c0b330307051513080304 66
    0x411000800300005403501100c140e9034000c5006040030004004080760381040042c0940340548600d4003900e61a5076a0b6108800011061240c000803070b031000900d2078400d240d0000e03a4140109815a40b251281550b81c020081d4031089900300700c0d4035003c001045084043c444c2e04000e01000d48030540c0c2d10308140c4174051240e03010b401c5078403038042107005022680d400b40c140e0360040f82195401010211750b01c2c04500190407a04140b034000c03003051040e41800d12580100c0100ca0b100c0d01c42c1c1800f442480c2040707031030340031011000c1e01c80d80c4100810861424254000d08461203640380c0142401c1c0c4a503000f0104020641c02510107034080b005010384203006100201c0000090342981d83e030b0761001c00c1055101d4000143c514140004200060b58a0303006480516402da40200220400d2526400750b00f5007542c00c40e800b15032285010b00d83d0030390f404840502e410a51008009000031881c20007040751f118200901c541001c4010312001d610303807441003080700242c0010740c0695215414113860b10f034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 823879757 1250 823878507 823878509
    0x20f0106051906140409050c0909011e0605030901110c0a030f050a0801030b040218040c030507080f03040b090d0519030e0402031612110a0e03120705070605070224030709 75
    0x12140e40c00124204a510442c40440c08648242c2042c1150034500003694a039030065501507100b031070904c0d08200e11880c2400c010302d0003d108566054050740c90359a116040c5005042003d4032024084051103c02d00500140d41d000c8480d174004599103280f4500328489800200c0c51002e107070b209860400405800402003400c403071640c41c00c0c504007001c000004040031810720001e4541201170b400301d03043d912041c030609068410b41c80422002e041501d450b007a518241d1000b502c0e1401480c8000c5190000454070301080391281c1c00443c00c00d424a699034505c0e911054541da80110310755004000200b051106960401000c5807500c2090042e04000e0416455080c0301031056104004000424a1005c5242c019908901d0817184003070761104443c001303114501800740400c401087d8080000d50068441041420070380544030780c9415510707080901e00603024000c1c0240c0001c101440044e00c0b0b0005400d403036000604005045d102014075072a6202c540040300c0c02241d0000c10420001d8014510300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 823881007 1250 823879757 823879759
    0x1915170133050d0501060806030609030f07080c0f0607120507020c01091401121509110307081303051216020c180c0d0605060f03040308130203060601051c0507020f010605 75
    0x140d01101c0700003118030481044100d2440000c40120303414045031150702681e514407000c420401055859000241009404485042c401e115001c0010f0a031107011065500703290103001c42d2400c0581a40e51452140c04c0140e44a4141c825520600d007011402c00400c0c0c00f411300d9840c0c069030a41080304070300c1680c6008000700199804030303900c03034490707603100c4c0100040721480c1303035260000d00880d00100d5003d0002c0740340134140b90a21840189a410703003140c4200300c4d58296010003248492a9180103203000031122140811366030310004441c502902106060f0502c240b400ca4a040495020101c0124096940882c10203d600210100b81e404104900094030201d442240d45207103600d1000d10076200408852440340c0110791161160030603085100508801000d8907103a04003400b8000094004440c15800268480007044c0e48520844000440c42e8001d0080c20141d0344050041d9580c3d071244d0100c000d0744039401e900d0a03240b43e107485002c0c004c500d03aa01400b010300c214069182501c401d0b800003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 823882257 1250 823881007 823881029
    0x424080601060f14090406140f03010b0a0e072001020d051f031b080109080903010b090f0708040809130902011e080a0b060c0714190501020c19151701 66
    0x103101c03071504a0070504480e1180c0c602003941c550f84407113040244c020480c0c15900a810544045464034507580d0b4043d080200303507001306140503894201426a00000081d43e0400e4865605200d114100101e036644010349007010110900035480d45049038040072421086a5400300740c00541e40030900074140c000485200014100340444599051b148052100906c185020301280303032101c888034040070042c5500c000030002680d05040103400c40d03010038003941c031075403819020124074a8103165490007039a465007440318654807981c083d504550041c1c015200c80e001441140101d07603500301c2014001e030454201060080b07441c800500511092504812507a114540c0e6142180e40a1002540310741040300204414440d4808030304948a0981060198001c200020900e18220ba480c1070b100039050b141324120442c10310403480c050010f4003c1030b00681010421154500d0003519891150154202e000d0030325aa50895072401500b44a012b07000c101c105d000410f9007120345c89410700501e010101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 823883507 1250 823882257 823882259
    0x1006080402330c07030b0a060303020304060e0103200c060105270c04030c080d091a0307200d030905150411010804050f2d0106060905060f090424080601 67
    0x1418101c41c02c808001081d4400c0381007100401001e526064a0100500d01c9690300c84400400752503010600040d0f03580c41d92003000c107079035044521071042103030b070154055401d0504169080303406a8840c01100c1c10580c175500d12650b032003010242c5092601030300d03c0da80d59174010828564106001640414030074004c815600d07451081c40000210310b044200036114031340c3d82c1d40380340358028066500013800c40c615058001c651181d000070060040c00c40e44d1180c00d2042e58850908003180481d40d0b5918450b241440455001800f500140e9a55200704c004602107600b01101245480c41c0d030243c1e040002d44801b010014442c05110309040c1805240c55004a46001d4584416211041c112181048400c00002d0f05100d820301030001e081300180103031100301c0c00790b440c0303c141949505021072854440b145040b2075100b0520840302150308035210250150329080403c90135403c030102ca20a262020080c010030b50741e80f072041e40d0001d1072407100c1c130060014103e0503400019a41d0480c0c4115401400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 823884757 1250 823883507 823883509
    0x901081006050d090f0f0825020d0b06030a2109060c021c140d0c12080906060402030c09060408061e0c09040c050423040e150408301006080402 63
    0x800c40d03440800c03d0030040b506084d07620b00074442c1984444054400da402403008070811900d10003c000c12641c0034017001d01c1d003904080d00d41021100e828000d50000d260310b02c031000901d0342001182c2c8408000c095818202040d11540c04a2074058100c5c0390075541000c65110340381d001074905000d0404c40c82c000304452380c15804640c0c031009220400184161581041080080a6110200e40bc0c1c6180c1a01e071110601c41014003100ca400c070781145c843c021007140d002e056210f09030061040c40c2000041590b5100d2005000003540302410fa1b42c40e041d001c0222000d10380707540008100030121400140142d10300709985000032521180d0903450600b004052140c02c10350310055959143c0c0c100e400180c410048081a580f0384247da1140501d85500c2c038820401800c00380520f080200103480c01e20942510200f0280c446c0000503c200711413801c480468007180302000071f460f10700416441250002d06003000c01000c44003804000700301c09506000c1080c1504000c01d148010507407810301c03080c1030805034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 823886007 1250 823884757 823884767
    0x2e0c0b130b0c1309052211030105061e040e160b0306131506210c0c0302061f120f051c1101061809020d0606061805030729040e010603020901081006 65
    0xc42081c10139611600031420b4032040c92030f448000d920105c2c0161844203103103010944014018a650700c40c1d444c3c00300141444c20002c400e070442190314200c5182694130350702007000400352604841d00c18031508903c4040740c01c0030b400a10140140b641a07039140d01d41300003000f00380340d1144000b003c864144010004c0384143ca14140303081e5505420400b18039800e652030f403001404030b4036180503014146010b0b4034040b40c1200c0070a00e900d000307600742c8545075240750f04440c4c04c0c001c01034a0300e03011070640780c10015050341e80f000309111032140c40301400d01d18041c1c079224030308a01c0c00360382c2d00d001d09050895403c0030f0700302d90b03259065054036000b130100358580041c400d2000c642d045108102034940d4200411507446044520f19940c0c0303e1410820700d42c41e40001025a41400e40d404400d042010340030500740340004001045500300242d40c80172101075039040c01e0014408030389851200741448045807000d50300764075901900243d038005071600518000144040c50141001c00c154442240502c01b1940c0301c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 823887257 1250 823886007 823886009
    0x20f100212031e18122b0204061701030b060103020702040b180106120c080114130c08071205041e08070b090c04140601090311011b0b10052e0c0b130b0c13 68
    0x48a02e16201e00b42004610005110407401090480c20b17403602c002c4051b0143d002c1c006650741035030794241c9040d01a140c8075107480e0a00024007010810b00c000303100c0f98801e80041a60601c003810106980700342002040280904510410443d070b030300c82c0144102c0d540140300311154bc440307203030501004035000009031075502c060182a40f0305405800c19400760300c0340307286282c0c5244068403c001716040f0210003481402c059502c440000c026040020181c6010b0003003500440e005070300b03100c0c81c4d40e500444106100c40712a003162990b1052000d803022415511001d4441c0d00d110021384140c00c0d0390350810084400004080448041d900140031807643e00080035000d580d408404080341b28040c50060742e41c03510040100240c6d1014501c2c280810100040302802a60f5043e0703541d4004d900d68040040c4450b20140310007100400d1031002d00c400581452081c11000c541c1801284500b082d00c94180c2958119001d81595130310301841000c200540c008131ba480003082c41c1d07050524612004007480d0300c1c06 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 823888507 1250 823887257 823887283
    0x150f0f08010303030b150705160519050613120b04052404030c020102010e01061403010c020601080a03051c020c011b0f0c150204050a1e080604020f100212031e18 71
    0x5d20071001071107858480c00504085a4041c00d40e890b034210303140c219500c0008080c900c1c01041c01240028150414074460441c1d0003000da410b001c03e6040c503060040c5500207501c111015455420005440307910b20030920103803030082d440c480c9140b80c03900b011850a40509000384908261600743c01c0181342095000f500103606282000003600c290004034090845076140025652070800c1c0041c001c600c030501d034202d400d42500244074a01c18480140e031241400d11802c000c1390410f2b050000041d1245c0b0003402d00204444543e2201c00300308007403030203d0700321017148081c50f90740d2485803041c200d603101601d18a01c84c0d854217071189046003500130013089800c000100080c2004406080011058056902411001d0940b103180c40d0744c1c00101c10480c00c0e018030740c1c42c051000c0c6404592884040b030301c40d21440c7c0242000041400c928240f140600103c82d210b000c600942110051955039000103500420f13802c10000c3c04010320781e0301008526000b0b404d58082240001c00b4458a05020440c1ca96000e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 823889757 1250 823888507 823888511
    0x302010b0d0b1512030414150f0a0c03050f070c0e0916050105090103090b130b100e060d030221090414160f090e04030206041101020c0d0b13020a150f0f0801030303 72
    0x290501003130a07403541c2c0e003203140d40e07000201d404120105095400c1e501100112034141001442843c484441c3c031990000e61440941000904185401030481541e03551080c40c03d1841c2803401001c540c0550000403045030541200201042080c8190800c2070700101024003a00c2c2e08514120f894145c550b407845800d062040100d643c403a43e038042d901c0128100c1e00f0040404044c50000040072032016042e800322904281080031070b0413185d1240c40035099801c0c0c1701c42c490f180c0d00d5207001c01100d2401e1140480851281e0000192034040130241200c62414030602580c45140c0301c3e003003105880365001c01707461400c4031004003c19640003c07034100c01220281011204040c1c0c10000f190000b8990b0811403182e1540f0080c0300403da80015100c1c411b88c0528403800322a000c84d0012a1100fa1442e80d2a40c0280c01000e00c0020514540c03440f5007141c101c032401113042c00c4907401305248070120ba201c61000c0c21010302e4400e00503042180468030742603500e400c18190030604000351204d4018040981015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 823891007 1250 823889757 823889791
    0x507110309031c030f02070c06022a061e0c010b040b0d0308040602070c0e16080105010e0105030414102408071a090307030818210a080f160308040302010b0d0b 70
    0x15000c0e9100c4a9170002c0382d441950349485034149a846200188600b000501c149143c0c0c03824004c81c00c084500340c8900a030a006c8694190040003415040301246808440d080e03448000c1d1454810014101e041ea81800411039140c12010441158400c2c44030b54001d0f40302c10120360002e0f034000c8502e039005501c1500140c44100030b0a2440c0e9400396034003c09080d00300881840210b8140e5080d078458002965280141603895070300441c2d4a024801034580412070070f0010400140d0210400d546282620b000c46032940303048051442603402001d04810306c0d0704106246456201d5104002c005804034100030710005240440130309600882c8040315001c18404680e4098980e02408003000131500091425140e5260b062050203074403c0b0190144500400384860303506c9030303070004100c500c8500e901c00f80c100703030503540c844156a500540321203d0a210410184850354465840c02d1a010f02a60301d520036440c0c107203806400c460503902d0603442150300e01200340024a910995a901503208141a41d001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 823892257 1250 823891007 823891063
    0x1309060c0e0a0812160803010806041106040302150a032703020709050c031303030b060f0d0b0a03110f010309050601030501140c03150105160f11130e06040b10090f050711030903 78
    0x20300005ca100608512000000054014002444074045c602078203440041c02c8a0070200035040c8120310000b50032a0f4000c240e4a1411404000703440c0080960a0103d017100348802c03010300741031484a1042d0a04c1e41410000d092590400c1440007902800e80108441d04141c5920825800300400090000300e00500700341c105482a0465001c5c000060035403a2100f8010400078105d81050100360f422a00e8007001c1592450070b140a0811243c0144041c142072005a042c4501040362000310341c14591038807244030000300d081040500a5009000005070480741d1602510450405002180d80f11414411320454150382d0b00b2004200009090070340c0d8034012400108991802c0405c003424406139940301e07105000e214a43c1d0150b5410803100652030702080c0e010b10341115003400d440e242640c880e00000300050a4900f05a0704198141d207000361a580c0d84000e50706a4908000d441d01c4242c0b00ca00b40105160400580e80c4002e00307280155040c008600080380d900c00d80b0f000e40101b0340c0580e220540359 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 823893507 1250 823892257 823892287
    0x40c1e181a0c031c0c0c020f04020c0712060b0f0d08160614090c03061e0c03060f09070f090b03010608040b0a1b030e120310060e1309060c0e0a0812 65
    0x207403842e45419261a002048102c0d4800002e510403071034a01d08101010405034810310f00340c4d07801c903402400a8018002d0406120083d085040109c2080c4100c4201003100102d420100000782d00c1100c01061150141080c040048079a803015070203030801c40020000204000c003550404401403e04041c3c660303c81c10280e0140c0f41c00707032012448072028400c0c084000300101d1103403142c000c02e5084941546a9030101c0a15940300300308107007808082004100101303001c10003503070402c0000707185d54a4001400000b0b0781d2075200340c6020020510400d078280d2516003050a00009014106109003550b24000028000d8400100020000c00d00980000e85124042d0b012102160003d444818000d18240014005104903d99900345110b88200f240c4200c0b4000105e0b442105100103021031645804001e9408615149880c0d0340701e0880c00d017004060045100300c620043c00b070180420410400900a002c3c06000003549004034007041003404410000940790144410103145075035500500f10801c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 823894757 1250 823893507 823893517
    0x902090f1804060b1309050607090f080712150c050c010e010203010e0a020922150f060c0f260403112d031c021e031e09040b040c1e181a 60
    0x1101450004100d01f88040000c00520441040d12200b060a4480014600813400341c8111340da00e174441082030080d103149403505c1039040e01c03400b8059904064100160b0a03612880c0013080016804100301c00004024040c071803840e1b0880000f1481d55042402c43c00b10640000c0c200502e160f00044d0000762074403040b01c280c5881107081d40b40d45100140b00c803440d014000c401507803460000c600d040455a441d40444d010b0440713a0716101e4078074500e029601e04003000200c038410340700558500800c4006464000a011002c1083c0010f9030303846043d8a40701c003c22000fa6410f074020810401814003104a40700320040d1084511038400500781c0b40c80009103091112242c80c060060280c9014140c0e54002480301641c07041700c000100a281c059400c10350303034007035130600c2403108c4c2c9042d0890341000710100060203c0c00c000340c0b0100703200c10071102043c02d48140e0280d14002505101c1019078a44041300380c480c01a00b24505860780d40009003240740603000c540280c49040700c2041d04401c160035000c04440c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 823896007 1250 823894757 823894789
    0x4020702121c0e01030b0f0d1502041e1d041e17030f06011b110d06022106010c0b0f060d0c0801150609032001020f01060902090f1804060b 61
    0x90814001e424602050b07004051400701207118030b42c02030306942c0640100440a68090011241a40c13441c00b04a41040910001d94036200d0791042c00310071b22083d000801c054071035903112650140758560a841e0b240c4040c0d200f0350034982c89248030141080015959a00a90001a40c144005110034152902c400070b007801045030000c451040c4414003c2d40103584a00b1200078050800d0361044015149071050a00d002e00012450850000082012020301503040015242c01400790041e55240c0807684100103412140d0003140034548500c00101c038030741c0c0c040030070310b8406405003095880d002001c5015101e0102241c0c80d000141680d00c03100396490701d80d900f020b003d625232503071103030443d000b002d20b5452a009050085004140503002d0100751084a500141c850342451007120080c06038003170402054114011003080440c0c5007802d0050728090301c410000140e44008a0301000403000300341e0b020502580509014205100300004000d42c0540c0100010502c4154540024040703103070340100d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 823897257 1250 823896007 823896013
    0x150624020f011505041d03030718030f2006090a090f0213030812010509060a090b0a080f010c0318020f01080c0705160e090705090c0a091502010203040203070b03150402070212 77
    0x218120b400f80107070702c1c2c085407010f95007008101e41255a005024295500300b0348682d10030400b00d44518031070310322580380e82c3e02c0c0c0d14100c406035201c2e03031001891844002c3c103880320001c00e814041030800c3c24101d50303481901220134901d000401c3c004250000600c0c850443c144e0b0359102d201955507100c0e01110002080015601c2d803103500c91509a020380c1100d0701c1c2c8001444030b100089440d0408000301070080000401c402d401b03c5ca841c001c00040c00ca95818141c014862800c0001d030000108540d415480c01707000007003940c6500c5640101100c4a15002280d801c0304e8000e40c002580761411080203145080c600000e040d40c1b10f402201c0d00f8031035000e00820341c0c07207401000140c54200e981c051054402000403a03a480d1a0040e100d646c549141c040c840d48060218040740800e075006008141c0001c0e20f0924400c0c00740c1d1010880d0b070002c2d0141c209005070f50004100006c600c4e0501a20300503200c0111000d0546c100039168041c48030051a920303005550000ba40010765035a00c4500f44800340705812 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 823898507 1250 823897257 823897271
    0x603050c1314070c051605010c0b070e1201020a110718020c0a1208060a060e2d090a0c11122205040e07090506030309030312070c0b070903150624020f01 67
    0x5000100860041c1d4980c050342440a802d044500c0b05c04085400527500d00b00c900300b180c0c65071b40d8080c0d40a0505014412070140b001d42d141c1340c610b00b0b1071242d144c200c00181c031340207002005450300408501d03c034029001810203010503010007a00300c3c144449144010b0b01c500885031401c0c501806000c024107100c5104480da1035031540082481d100c0c81098621f010f20342e84d00d11341542e40100080c840b0358805107a0702c20300420f9001410060410301e40a0701c1480d0302c20342c3c0001c2014072605440360309a290b02d4845140703413590401e5101d11140602c0b00100541e400810603081c017400f4841c4400038400105c0206610048034aa2030006818018802c000d44883c58035203580da182c10f8801e0030b09076800d10300003488524001c01035669030070307014014602c1d15003c00d040c00040c0c40000c0108060103000c1d041d034000710f5804a4640d01c540481e0300c5072403040b4214105503240c2d011004241c89101c0c10a5814080e45034885014813624580141ea07418249420200342c1c1400c44078034040a2075868604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823899757 1250 823898507 823898521
    0x1060614030621012025020613032111031206030c0a1d090f030711040906022709070914010207081002041a0307140705010f090605190603050c1314 65
    0x1000f00c226103080d1030098440c0001300201c892500400d00500c0070502400106d141968010400c5050390348018042c0b0701e0000d40080362000d4080311f40041d9911001d00300c40c1c0f04154500711520312000303611b0821a14241c4440480342d40c9200c2d07000e80381581c401c8400400c5c004e40f42000300e011420b0000300514900b544801100740500d50100c00d01084a2044001c2000084003140201450300090081c61400016031180c8400800800b001504a030381c401011020030030310700c050800b128542c0b484500001415100051111180440d14442c442c2c030700c103001e00340342c00035001c0d000c844482003846031009003c0010b0381001d01640c071006950084428071340c441c08080e4020400d88280ca4454580142d210205271440d0200715032107004100e1021601d18124010b002601d01c0700d108030000b107001c81c0140e84400c10b41e0341c54507088524503210000c0c4000f8a100e583d0002e00f0001038101044824559201c807070740d031a40e01e2071141c06007880c0c100d48100e003000d0380c00c40320700d1006080c69000c007428551 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823901007 1250 823899757 823899761
    0x4110a0e2b0f1a0603160e070e1201020415021002040513050a0b090106230705030405012109060203010513090201020a0201120b180406141605180924030106061403062101 75
    0x64544d803203030080b00003080003000f0f403481036000d0302d90b081c3c4407184e00e50303800d081980d202c074590b50543e600490303c2030301e04107901007400104058022040400c001010052000e8035044400d920ba00600d8010b0100744910740b182c03848505001585100400d140d00c41f55800c0d00104002e2008580040b1408000308846070030183d60a5090180501c0b104c410600303140030940d5011f4080d0080c0250030400081015601c00d0039420608601d403080d84140001d103000c160121103d0b00f10440380180c0100c010461460030031400c01d98034404546c14403100e10f45a000079191220120b00905002030074105140081c05541300b0040b408020342036400007500d400048003c80e00c110b07011103165040901c8040c0c40b44102a40c94020070705500442c0054030000c205640c65080000c68011014000c104104e4076500c114000d8020150b03e550343c407035803606c030303180707909074048000080c4c081d80c1411020020103a01541002000060512554894507000300107075401d401e5180c1704124240c000f4003420400d4040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823902257 1250 823901007 823901011
    0x73623010e07020a05072c01030b060306010b0a12090c0801090302060603010b06131203052104030201141902030a06120b1f060804080c0c04110a0e2b0f1a 68
    0x10000c0c40142d914076004076900e44d803100b030092964000180400c000140f080e070074500786414031040da20a0301c01c4901048503030030983c070507550035080c98140255428148443d0740540008030b5001d142040152000d0000b58065034124200340e680c0c1540c40030720900d0041d04002d000c2c290003d10104080d414020b55940043e80d159200c1e511300400c4178142d1510401700ca403000d841c640c0b0f14010358900700110094412480e02038060000811010302440c4000d00c544940901031412102503050504009003158190f92249880300c041c1c00502c0550401c0c042c104505204030240545d490b590550182c026001d1a03200558145102280c4800c00254940360b51040070354140607101108032510301c1c6504c105d01d205040214454101081c040303240c0c44018510018001d0031122960110340100781200c2080c10f04400300500407402000b030550201a0500070a02101c9600d03070184c0c1c9c03442d00d000307981e07102184c4481010b00c0701406041050607416101c1c09d6820440750100c5144d001e080c0d4484c0541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823903507 1250 823902257 823902269
    0x180308031531090c03020918031201080f0601063504060204170601060e010806030c220608010605060f0a0c050d0801150816110a050303011707362301 66
    0x120b4903000120110711449003201c0d0050b120712a068615000e100714440e01815103a403500e12072030741000d940c0c000c00092030004c0b13448614124541c5040c0059080c040000c002c0c020700d8004030010411260310101c8003880050604015200d00092601c103450361200d2038007121000b41c0780e030401043c402c282e8060400c5039488900c0700c0d002900310003120f807544030900541c0d0218022541e0810154400c2d04200da1100020701207078261542c80b80040c4c42d0102c0804502265480c0f81b0640e403001941c2c4c00390070000c0c40003400a0003045c2c2044000381203400303040d00d540d03c0d5410105100c9103161044005000c06504081902c80618021800030003000c4240142e00c2041c056540102c8028460001c3c0fa00c1929004601c130703014100e84c9001c03101409051814030182c41000c24482c08154140001d5000b050802e03429994041c602e9103083c10324000754081e171216950349800c03540d14880d03024189050074980b694841c000404034800da0003403c45801d00c2000c0c2c40e500203031840b10885501000e0607030300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823904757 1250 823903507 823903579
    0xa030203060a02130503030c03040e0604090503030a3602100c0b1f060806090f091c030504060e060609040305030a020421020f0f0d020906060f2106011803080315 71
    0x51078105050381d07423040d0a49180958810401017008000800c0f145410480040c0003103109080e41d01c1ea00c0c60b50300141c4111000729628682c030139000f0180203808080304840a5206445e40c1c41c280a03400c07091401d080a8010034410011001c814030940a503201c15078800c0300d002032818119915881015180300274940d03049400808900300c2d0107440001c2c801c65008200d004195540700400c0701c1c051010342005001e218403400070030343c5180e94489489540e1150760005162401d0b040c100192100a0030443d003d420500030f01541e42c0302c0c03004660744590135050003603403070711a4852003000340b06d103034080a0000c400b441c04100c500c041481e100381003402125648010940c2c10200003002c0c40e2982c0c1d007544a110344040350014282803145075070065004000c28200191000c214510f90311a8280101ca41c02d0161407010100c0300340540d5411500a01c2e120300f1004002c0c41c54019445c6a010150100101000240071440d40c0708105501c0c1e800680000c541003007031890300c0c085000d01c0c1c80044c0521 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823906007 1250 823904757 823904759
    0xa08010e0601090320010c020402030703020a0909020414060a170403051207020d05190905040c091d0f06090a090c0e22260d051510020d08150a030203060a0213 70
    0x140c4584418000d80c3e41040c040052000104450340365005200354686c140030100300ea800140c1d84a2003e14443c05254402507a100b15500e001000d000c00f94024441d42417044c0001e00092a40d000442c40880c010f83c0c6440d42e070404101c040da03506200220003c03064000030208410941e0200c041c0c078840c0054415180d0b20f031909082640c03110300500c000d4000510a000c2c2c28200d0700c41c0140c0c10160329050030403109d01600e03040800e00740c40e40d000c0741c5404205521001c0080c81c104903c030150842020713541d418a0301705000021441a406480c0791300c01c8043c3c00100d03202c16260342c410326100703500110520b81c01d40c1c1ca0a004e08984400c035214081407061b0f04044446260600c00500002d0344800042c10a0103030300c2c00303c00503910284d4203001c0300d4814030a2032160b08a40c861640138040711460031001178882c06c100301088034902d00e148115009440176942450f0000041030f0441001d0044080780c0e14150042900b111706584041c8d4584100c40601241c10101d9000b004000c6404691458007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823907257 1250 823906007 823906009
    0xd0c02240f04170d05240d0305070201141606050403120c02072606190c090302010c110420030405010b0307030510050601120204090e060f132301020a08010e06 70
    0x22842215845901d140100004000a018485030000403044490ba079003003160308202c410481d4000c5460200d500306128041340d00d583c2d941486000840708035a42409a40039030342c01030041c095614024140480c062162000c2120603080d01d20002140c1541010203c503420498080c000944d41a004660382903015040c0091a018000300034286400603d40c10745882c003285845844024004514451920001d03c1c07040d091000c94040d0307005844000c4545c00644062041b04c10328a108002e20040fa0b004200607600183e9051841d0b81009401c445410a9004900508070351000c2e8215100180c0425080c03100600c040c5000c0c0780903000800082c0403103014550b6403805400043d029030300c000e800301d40e010340c20341100350301c00c4040c90210403580b0220b00303100c00c0e604140c010741103090300c036030300700e065002d04128190b07101410720003180850034003000065404901d0b850180c8500458000c8400c0c02c2181d01807045144601002190796401c01c0138020b00b02072082c042d41c001c0b861b0700c0f000304d10741d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823908507 1250 823907257 823907323
    0x50c040b0f010219080c011b0906050a090302122112090105041e050f0d0c05010b090624090904062c03032e0f18060b0a030b060d0c02 59
    0xd16078040c2c0040c5142600008003422000002604403142c140c1000740c44040381d03007170180030000d00b0000c020309100c0814000140541c83c903030b0000d0080080078030140d081c540d0300c80b1400e022207806640842e91001c135869128102004c00e4440410100104079540e25414854000c080e40c08081d2400e5a4035101d007c02c280c00d070385007542e0203002c00650244030f011055141c16002c08503403048045a1100c08460002c604004800c44400e0100390821850342c10f0002c20700801c40d10314411554141d9503e40540001c0c0c1039405031164510606003240c10340e490184440032100c00c03a8008101c02018501450240c0140240020000d0051080000010035151109806243d403101001031410b564a840c0c08503a9144814520303035132450303005185985c4000d164115006030948072131189003d410302e00c000030b005085c3c8004040c200d241080400042d4689001d50300d6a050b203141c00710340d901c40500003605038020700c5100c09010703142c82d400c01240b5070002000314502e0001d6901c01c10080c0d0440c00d15070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823909757 1250 823908507 823908529
    0xf071202040209120718051303140a050f030901061e0e01030b060a0e1303020c01050c1b06070212030c010f05011401082d0f010f08031c090b04050c040b 67
    0x5240504566800051801c2e402401c101c5402503d030000b4000309070b908a1600150307a0010901044100781400b0152190145a074812001040302600952170f9800500341001600c40300d61949001c524000c0641c802c0c0c044a0340c3c0314440684d2a100e040c0380a805000b00264418540350074800364418180348010343c5500220341d00301c0f44400c8140c0ca103442e0040f1801004040e19030021003000086011a4100c0445010380725800034069282c2c00c51401902d01042490580d0500a05226404800e54001400340242c5080030010f0030b280032110201d1340b640207101000b0340c040c1078124000d541d400004080e02d21140340000a0140e5a600032212040340ca0a004616280045440c2d050455005510302c68001c1d142d40d0100c6a00000e9650327a400588000310302d1540340b9011428441c42d1004c00156601401a00d4401300c10ba9141501e10f907030700d00c18070300c05031b8050300184040c50f052482984000741d450f030407100a860074989440c1c07290310741a0030607071640715601e030540d4000c1c2c600304000441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823911007 1250 823909757 823909769
    0x40c051b1609020d0b1003020304061505031020070f0606050d1223041824031205070f080406120905071206020403020d1103060c072310051006020f07 66
    0x101800c0c141000c400107036020113100c400321a04d4840714819512000540b2a954080b6a00141c072400c25180100503144052082494121070071018011a940450003e1508a40d150005024001d0742082c101c0c6201d050b080034000c0c5000306400c41031008424402d2801803086000f0044940c449007041685d00100801030612402c1169134107509010b800c50518000704034122007803c0307143c0040410703141d02035003141210954404440450100c00c1c080d1200064902d400d11400c5801c524007044030004a201c082d000c0d07801803040c201d103d40100308584080350403546601e400300982c1401100b40e07006200d040c001800541151066138420711501038456803050150146614008842040200540c0140c9200c0da003003000000503661400618986c3e40714141caa6140483c040403d828072900030018440114104503920001d40030315140307425070003d105140d000800402010303140c081250962004245044107015445138405024000c0315250307401c58001e03d04608a05445414500c1a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823912257 1250 823911007 823911043
    0x30702153103020f070801020405270c09060c010c05040303091d31050a1208160f030b1905030c191401030e030301091a040b060a030c020309040c051b 66
    0x481400304112503240c50080c4104e4540c2c0e000d00340524101400d0350320049140c1c0d80007404121078100341c1c1c001c00140b52138030407400340704950381840011000300801400000400141c90340303042d983d420981e41b00e040603c00800c8a40b81e580707009071050340503020540110b108003078001001c0c10242003030040c00d482c03529072001e80d8403000c1d441540e100c0c01520141040e4101c0d100e440b18640854840c00026001d800103094503942070a12140f009003004d410010404c0d50000c10881041c1c0051450044845207466012042110002c600400d80c0c400384a600a00d000a60060b038031040410301c041d074208030241e94400003404100615540c0c82403240c41c240020b0b605c00c01c02180508402d03840507034103041c0814070b500304242d96421035000360003c0c0141540c4075240e0a0519014184c03030303d030310400e4508102251901c0c0c009801801a00707421020591a9000c1c02c86680c03091055170b01b0030030080c0050100f03003040c40f805401c50b0484400da120310300e2074010f100d0a01c00000307010512055200d400b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823913507 1250 823912257 823912321
    0x3020405010902190f031107050303040c09060f03111c0503030402030d1805010c0f05011d07060f0905190902161a010e060d0c08030d0c030c030506010207230603070215 74
    0x9035511040c111103041810b41d01d030300c0c1c240c0c0f40c03d001c00140141403049c40650303507900c0c040c81d08244080d0240c00c0003884a00e41a024048058030385444003d1700c2d0801500002d5800c2c40002508403401c0c1c020396003414075000d400604102c8000007850150741300701c042c2c480000650714222011078244080501c85502c0e62410001940191f07040d503000c074010600c07010045100d8442074251010070348403000c0221080100340c800c94040c403c00d40907120618040201003020340d0020a020001c1c00382c42c0c440c0003200400715015401c041c565004152070002591114600c00e4003103000c1c03540c18400e81701b80c804601c1290800003c2d4a005040c0c0c0c0040d803880d000c589880c01070112065010b141111039401221000c10034403002c101500751490640d1010400340e0603038030300400790340d400100f10041c10b0600090050300da07004540d80c0c0079106101441221585000300544984100e0302031250410800000d000c40682e02041d4280c4800e80c000c00da0000f603d864050035a20b078480700fa649404240c10712 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823914757 1250 823913507 823913557
    0xf2f060d0b0303030c13150207260d050904060e0f0109180c080d270605030a09020d0813171005041104230901020a390602030103020405010902 63
    0x201420034150214400500c08071001d0200707145038000e6410030440314000c00c0d22209601010392010281526490300384440d8048440a5940c001c1d038001e42d0048012a81d40c0c003240041121a412980111000c6036170540007408058160341c800742c00307140200d0800f0000300b0390400c030761102805450050310041a41c0e103005400801406c80310001c0f002c40000100031030210b1806040340380600003060250401240c640b4010305100f40903520101080845601500540c58505000044030340500780540d80303075900e000041c002c002001d0001d600c50301c580c1c154014800d0304000381071115800d40c0d641c00c010740ca4038102c0140000468550002d0340c40036072144452801c0c1d0304038682103441200c508503100d1040c0001020b581c54402d1180711084801c0f500e5a100058940e04c03034016100700c00031442d00d981c0c11310040801400210203e0301000094220080c408841059105001030300c41390300701c224040c60000301960003844264481e0341030400225200c0d880348201c4010700c1d400b1001d03404042c0001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823916007 1250 823914757 823914769
    0xc090403020a08040b030603060a1404060b06130b030a0605182208030702060405010c03023a05070804050c0105090d02040b03010605211b01051b0111070f2f 69
    0x8004a0450054900c0d0300300180b056400f410142680032001e9881e407514805141c6043e80c000c10105686081c03001040103d0220720403030b50041e8101c0400f0032461902d46c04a01248107101d07140070250480311000a0001131040a1806250000400e01c0610741d25410406c0607400c1d4100150100c0129001c1010181445130001005241880d880b01c0c0700e4843d143c1c140560400c450340c0001d07030404410081005800c1c814200300e1070f8181021030506620582e2400c4958165444c000b030190310416408610702a4003105078040c0e07840d82c06000038980307800010600403064408581500c500001010381e58010000c0d00c1e0b2403400500113a45503c216020071018009011811b50155642e03000450561500141500040700781c0d0f90301044141c829140c64540b00e00c00104039050341d22188802030303d030b0b030140841c1e0083d0819404084076052190b0403a00600b40c4c80803002444400040c130070104082001c688101d140500101c0305800c85078001da080e0544031440c0022124000386160301d107403420f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823917257 1250 823916007 823916011
    0x3061801050c042711071101030c170711031204030c03020d02010507140901110a0b011406030903070305070c0f03120306092c0c04061d220204020307170a0e0c01020f0c09 75
    0x490000709050909880c1560700e58046d86081ea619102c004852200b56010f0140c65008607451a0a068000624942d03521250000c1c0c15a800c2003000740f07541166601c1002a640601c01000c040030190526207405030050141c000d0880160003400740c00c040140c010700c91988078454613117035801c80700104880d43c01243e000300711700c90620503228000300c1007100420107441c60520800d01070f400c07941000e42c03400d0020384e6041401d215420800c00c0051301d4070041b059039041d0b03038982040c0751900c503035140c190340c00702158001100ba140c1010f800424003502c001c151f48041c02c070f40c030300300b1255444540c507400f1ba0781c0c0e00390b944d40102404c2070264004082418003154550412040d01d60380e00203403000800b55001c560105120140785091504a1080100707501c1d044010600c0d154091102c08012841884080b03101a12665001c00002c2545005005071003d00c0081c00c00100c440ca410103408000f0143c40412503414480c2841000581d40001410340300786000200504400c0000c008000c007850700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823918507 1250 823917257 823917329
    0xe0f070605120a051017060615071106130b0706021c02031e0406020408071707050604060c110f040612050708011104270c02031c020304031e0e03061801050c04 70
    0x410b45d400150550301000407440030320402c01410303050400c581000414201e0360703590140c60004016900c001a00184070281030102503403003540b01c1e254240c45442c009820760021707410400000ba03890401c0801d03030007031120740c0c04540030ba4249204031a14a040380005c8a40b404058000304034098495468048141e202c1e118000c00b40c6070680750707001d4038144041c50340903441c0743c6101c813115901050180280406000c00f43c542c4c0b42850b1a000d0018122441c030003000d071080003005480340d05611062500040d5501c09402030003800e40d15005290070a008010542e40f50180b000f0109425006000e1101f0700c040d21101c40f41000c2c00c000180700010ba000c04502d0461b004401c10084c840c0c0640114040b400c542e03006035071140500d122841280700318141c0d503603c06104104010000343c0001006200c07440341440d8804c20504180c054854019014030154144107c00c20030554151868229010000d110024811900d648074040d05030b0203030b406881d082d0895120790a1113810a80c58030011411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823919757 1250 823918507 823918531
    0xc190e040921022e181506060e0d030806011b0803150405090a02060d1508011b080718170102120c130b0c0c1002120313060c110a020103051005040e0f070605120a05 72
    0x20b0ba0b43c40c01c0d03642108503c280b06c42c40e142e01c0200502c40c0c03c80340740400c1c400241e4403c08042d0b800c0c0c0d00104180c00081c12035050045001051640410a001000c081030b44035030741684e00c4c2000c0181000c09600b00400f80c0c440d81c00c0c1400a0445040440d50246540d800303081c41e0b003000c0000c60103070702500082c41130124400342c452000079501403d00130081105900d07990201c001c011a0780060042c2001404030b0240090b020406c1e03a421000c62807042110b1140b40c445401c400080701c07290283c0301704640c0348150b519440512004c107424000501105400600b010102541d68001c0461f90241c01c0d024065904507214580711801d1003100da03055012540705440b140b410805403812560010f540d603004d03000c1841a4141000814410280c04980504201c40309907407901c00d1075910805510002e04050300c0e4000310341d1000c02040c0c40c1c0c02a040040080c0070402c100e50135541e9401c070340c06e190102072180e80c0c3c00203145130058046604011a201664196079a80000d26024080280030642c2d529 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823920863 1106 823919757 823919801
    0x81b06070e1504180b03160302010905190e13052812140a0c1703130602030403022a04050c190e040921022e 48
    0x14221041e11000b0b075200c00c0c8401501071644126100044150300c000c03040c1c25900308251100042e01161010007800021000484491001901140f00c2030810310040c100502640170b000c017001c0081c00f4003a50740e0104a00601e044074523601c0e50b01d40281020411001344102e401805560f040a0070b140181101c0f201c9140e9440001081000e12400ca180c1b01030190b415928070210221140303444000017034000c1c01410b10708004584000140300c1c3c10540420385c0c070650b40200740c11024511030705029650b42009510140c000d5055208000418a51414502c0c2c03101441c0c1007109034083c00f83d02c403c2408160f60380600240302c2c041d400d0154100840d20010811000059441d00641c00030b000804a4001e0450304c00140000188403000c24288044400c80102504150300b00d808014800110400c200b4031480702140c08076591444590035a401d4008010390b90036214040507207 = true := by decide +kernel

theorem cover : BRFrame.Cov 823741007 823920863 := by
  have h0 := BRFrame.cov_init 823741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823741007 ≤ n) (h2 : n < 823920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
