-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:54:57.618034+00:00
-- url     : https://prove2.me/submissions/9438eab6-7e54-44b4-bcb7-64a288fdf74c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392446043 ≤ n < 392625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392447293 1250 392446043 392446049
    0x3140d0b040c05130e0606040519140906010c020d1b060203030402030f010e071e03062301090e0a0212100e300316030b2101060f0303090605130b07120f11030301 71
    0x82c040c0106e03504d04000c100d0600031640b0144e04440090001d00640c01a0791000e007e660015180040c0107500310304210711480181e800364040f400701500e42c005820098186000180514052184041c012503403500c000c2407503016800580000c030a200031441d0a06c039000030030070341000911808541c078000b10780b9540f40d4821404d201c0c074444681e041c6540b540329420011500041e040002c1c0400c0d8006a0405441740108034900da80c42002043c209401c0c0f0501d031192524a0040061003400c0d4280301422013004c500090303074494a082074081a50601914500681c1c81c8007422101581200c44035001c440740b034480055001c0e40040c03400c041c0307480065907400f0142050b5004d1850864600f60000d1049100c2c0a0308400440444068035822102c140c8400360800020030a035680e544400110508500004000801c0f4a008014951094000d8092480c25002d07540f8402c1e9201080c4919a1190800b2600c5000d03410400c00641d4024265000d03040b4241032010f950303070362034030029103a02c0140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392448543 1250 392447293 392447309
    0x4080c0d031101050c121e0a0c09080d11150f070f0c061104050f0a0b072d1511031314010209120606030715080406050403140d0b040c0513 61
    0x41a4106142c81220203140e003100200c003c200c20704010700b405405034800c0504541c207815010204080381c03100240000c11180e00c1ca071206840d00d541c04070344042d200101d084800c1185828001c109040148040384411307425860301524002e5041c01e05050042c0d46a5030300504030340c50308124010041d03001c0d8943c41607952070161740da04807078501070f9400300c1c0c5c2c8a00a40400d00d444051654a62000700030000ea410440d40341c3e030b02520301420042d02da6040d00808804400a20030300c1d0020b03103105042d903200c490b8140401510b2042d45145860280214019112002c5045040c00c1106581c41000d440b00b200c0e0100915520340f04113441d410081041000b080a00068240c8101407400e6040c1d0f4000d803801045519610000c242c0d1580d582d41c1500d829100c0d00501c180094031380c945845214000003161104003ea5586031030780c1c0000c7c100104154140280d40411001038503220b002040b07190041e200010380305c0361180511007110101e680c2c070803c0c007008205e06030110100f41c5500080b110342e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392449793 1250 392448543 392448559
    0x406020d1b031b080a020a02190b09040504080c0607030207120305010815090f1902040b010903022818090c0506131a0f0f04290702010e15160201080a0204080c 70
    0x403c00c1400c24005040c054407100020584203107a90b07010910a0201d4000c03038020020110981507140751304560701c13400041c60b0b010441c03c449400c0a03001964014020200702e41400368600f112400c001c1c04458010002e540003451504120403c590030041001d140b6042100f981444a0140da4415548800070116294000200006010005000b46101c807034140d50640d981019000b085040001080380310350b0422018044551080d00719504483d002022620743c010240f04002040c21400e016121824984002040c0402440d2400803481911100090b61828a007450703208a0401d400c51441030341c0400882c450f81c540e4020b607006841c000c512030701500380010008180c030b2180d601c0c001d82c1d041002c0b84d061684481c7c00b001d002100c10700d4003400801d14900b0f0391641d800349496030801315020300b80010700140d440b510003040541000b1784040f03000040c02c0b10b50360490300119002c10b01070307440410500840d45d1040c20b00c1d4100000000c158240f5041c803030365580711111000742c44d0085203a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392451043 1250 392449793 392449817
    0x913020307081204062a020d031101050408030a0f09020603150301060f151d1503060319060e21090f03030d06061701060509030c2101050c0406020d1b03 67
    0x9001010051603510300700c400240182050201d190424072480c5c01003030120f000500c40300c0c0501813003041030355010500a0302410075401c0040140404c1c07410f80130843c5060001081c001c00344101c50240380640803894603450001440c1041c0c6895400745120181007480c1c0c100143c80360b07802d907074004a00c000a52001900103010038018a002c6d4031507000810b01200000e1315181a03051210741c0103403039585440e405080350011000752050951550020440d041c0501141a41c1014603080394004060b145a1600300700f01c0a00004404c1d41551071b0341d0f555200031401003040000c0311a0b00c5405405a640301040e0303442075094041e04614a003e00401c00c03c010003a13a0910441d03299040640c010003019031110302c02000c203047d14031108211040c02d0000b0131454011015101007403002801031405005800512407400c5071a0440c0900c01098a41d0030f5001100380030300d510030700340c804030540c88502e4110000e1034013410707442890920035081f00080c0c4101013070401650182e0541480250561 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392452293 1250 392451043 392451049
    0x12050d080a0902150c07170307030c03300c17010b0901110d020c03070506120a0e0304081b0418050714190608160f0210051b070c090608010b091302 65
    0xc180b009511035100d40c60100c6901c4113134007502201c81540122400e003070b00d40050045882c42c1d07081c2d141565100b4481400024800d80148007103500c68940070240700045124120000311502e4800340c0b154554141c2c01e1801220300c1444030b1241c00d498207030310340b0156070000d8007551811b000704440704d0000589680380b82d010380021800082e450040307c1c1c900e083c14034004d444652220000384203000e00e100c001064030301501a9940d100816030400d010391101044003009012030030b003031680b0307000a0000141000003031042d03621803402d01d04108180d51208040201702c030300030610709142e01c10703c6040704042080040d100050310f443c8003103080c004182c000084e01c0520041c59100e10203030b41083c0440d4950380441c5040c0500720800500700c03d1042d0107400d6900c1c01c2c0040c00074006070710400301001002540c0d0005508094401d1111054400b84410020580d010000030307248600c00500c1006030441e01c0c400c0e1001426208001c0144618100000d84500d40280900300708144600d1240e007955 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392453543 1250 392452293 392452301
    0x9090e0a020607080d050c190f2d03050108010903020c060a05070606030f050c030a051c050403020a0617011205150a020903010e010605040c0203070506040206070503040e071812050d080a 82
    0x1e8004005644800861030a1509540034414010715141040080b402c4014500c0958500741d050030721103000d07d0301024044031180a0548a141004010b10404908900b80040d0340380c84400105414881340c050603015050301c4060f805010141c3c5480081c0010036404200c001014404a44c070507903412a5003821201c9000380c0102034402c0745003880000400072559601035900c3e00c154143d8000c950040d00b09611181c641c04054003640020700f65240507012803030700060b01d03030680c10aa82040e440e500890795030417050304400049111201410840d80f2440b0042c4d00402c0e141d802e410a00754542c0c1e865454011250300000d030381c5038003404520003c08076010350310103c034041c00810814010740c444502803d40352140c2c40c012894054501c215920100880b801190040c1c01009103450b50350034446168002401606d141c00144008260700b210b2070700c941d000e54000c1e40d1312194000d601c1c9400400040c06d9001903115041036031a6800078001007043c001c00a103900b080b048a640344030006001d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392454793 1250 392453543 392453563
    0x80f0402062d040302120a0b010e091905030403020418051b06090d050a1b03020a030809030c100306081e1005100906092c061504090c0e0610030c09090e 67
    0x1050400e1201000030002c803020b08100d82c000c0300c03c04961381c07038488019103d8210380070180c98400c030440113001c20a108214590814100004c860040c04800400c500c49901e81100301c443c0e0f007001074100306614042c01980c514502a2030030f4820304e030140d40c030665103030440c002003c0351620003001c14500d640d0388400d6400c02c40c0040c00d10a0036072441e02d03206841e2114910b04490341325106901d80449400c50081405490340a003900d558035003151035010315034001c41c40f0a58540701c3c01350b68446ca0b03150801d1f031215011468030049241c40c10102d0035803c2031416201080c009401e41d142c80c0c44088005511a000d1341d11420004031502e030200d501100740c02e00d41100360002d080400000b5503050543c00903045c00024a814124607004443c158088200301d0040e8405030f02032404034091000034008088035800003032001139124216950100701c00380700d910081d030340c0007900100802824000000e034986482840d04005201e0520805003c1440da8050645516641d214402d44288100030001da6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392456043 1250 392454793 392454847
    0x3071203110307030e10051501030f180c03110405060d0b040f12170c041d0a060807141c051902060403050102040f08070b07020f010e04140702010b10080f040206 71
    0x601c3c503200340003601400f80382c0440446445011540701e402410380c8501401412010320035000109410700440140600b9051500791941e120b491400700b403906c20321700250610440e01e100c07a861840c03c0004c0c402d92000d620343d000d00d05213004c008459544103038480d51a07030b111140d04143c1c6c031542442c04140802000c010440045015621140c41c1c10580b0072680918440c4030320519a600704640b00380303010703d1048010300541c2c545881542141e100015501c100402d0300003405550305c03060306c0e140c08000d601607200c03030b6a03075840d81c00103040c002c051080519152003681100c0206590f8942d0700c03800505010246010b240100c000c65448204a80c01550494025516640c0b603001692440060307200321a003030300c00c0100c005030600c141c000750340882e50020818034040d5042c4005458134504c0d24842c551107541e9000caa42c280c080d842400c0d0160342c5c1a070000a10481c541c0a008884103510043c2d024032080070100071070102080840340c2c4c050741c107661a60712507000e070300c988400703610506503011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392457293 1250 392456043 392456047
    0x1518180f0c0504091d0d1119063305010f020109080c060609011203050913090f231209040e0106050a081510060e1002100207210f020307120311 63
    0xd0305a849400740c41501c4c0920010000c0220108245640c4c0d1810100b503240e54005002c110043c5d0f02540c5d52080e2291400160380c140700f40e91142d0701d501c681c0d4210803903440b6541d010800381d0510300c0750102c1d810100003901d610070540c0c581c10344103451120f200c5c40341040001603595611a10130b411207000c80744d10641e2251620400c08115460312401c0700c00c00d00804c180000010400c00d00f003281c0c1d0308550144c540c00c1ca0506580d003809040c020510490f40082c0e2280c00c0140000c0410080340360b114011035041001c20810080c440ba0140a03024040d010b0b4804a0f01c000404044000c84403603500840b000200c1c6200c00001601400050380300d298490380d02080000d000001081d0000c0001b8102c000382d24586d41c2031128849030364a4010311000501040010440c0d05010b40da4210242c0180121156032056842c000260b0784928003c4601e10f8001d02c08403101c3c82c40e034030461700841540c20008155055200020b50b030f07014455010b40b502e45007e28070071540f070295007c41290a48010039603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392458543 1250 392457293 392457311
    0x60102070909150b0105091e1801031410060b04050d060605041103090c0306130803130c12030201110f0a140f0f03070f021605040e03040807030c1518180f 68
    0x100c800364802d00d11070b003d50800400d180f00e5032040b0200c03600028010301c0da49040b403003c40b07039110b1001003500b0b05403c17690345424041c2000850b0941c0380254410302031150924140510386c0e0600601f68040034800f81051018080380103010140da0136281d0a850106e100030300c60078034802030459940a29002071500796100501c84a201c000e41c0320781d64503021074000c0c1d1100000e25954120071150452040441220080018401c2c402513400c03510140c4441503403100b54a48074545a515400165841c1400040f1001c1603028022078070700d05806a501c80c185103031809181103d00c2515554130401ca100c81052011100d9001962904c04900c5003003a00c0304241401500c1c90350054429502040714001d0381c0c58460320000d4001c1180d0180c1200e050642d10345000d010180c541d80300702c0403160000b448040341ca0a0108030420045024200701040207180088038107042c00c402d08807408000440f84000400c00d2192003401c219001c41d07098a50b51404ea104460081000224090300750b0302385282e503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392459793 1250 392458543 392458553
    0x1501171902041d060a0608060901210c0f14060310092712080c03130b060607050a05030d0608070b040b090619090e010602010209031903110607050a0f030e0312060102070909 76
    0x958800c80040e05c44e1105c05448810580782c40c807048413101c0c4d00111700001400034240e590100030640841500904c84000c1a03514480c02e1002d64000c4500d81e1101e034420408846811200c640c0c09a080d5183c2c3d00e0350034030a006007580042c6001d4255095140e40e0009251804425140d20f100c01166191000b200c0c10310700100f0030b42c0b03c004440001145d40000c10307a01040c120442c0e0040c2c8040c0d60341d5480d90b00036596111108001800c156000d1002d0000ca008140d00717119280712980b00f4005513030b482e044c400c2d0303107401c075815a007140c6020b9210304400e22040c40d20360200c905843c1c40c10401074940d8151270005005218180d010340c0110101c41e54255900e8200c0342d080f06941007410f81e00300360ba0f00c40704220300b01d0161120b55549548054440300140a1003500d85014a000385000c500c1a0100e8610341d180031415660304c400540000380614940b54403a620507917072411450b080c0041258600f141d65640103112003900c1d003039464804240280e0081080800034034106600b4440c0406d24104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 392461043 1250 392459793 392459849
    0x90a0b09030a080a0c050a0c030e030102070b0405100c0f0e0402041d06040f020c190203010e010e060a0510050f04050a0b040e07080f0c01170411040212150117190204 73
    0x3802d0080303840354010403040b204d64000d08681421690b40d01d4200314032103100726507050800e2029800d06c08801903028098500b80004c1c01c0040c00303280071203000d007071a2404500d018107510041044620f4030400d81c00482e0b001c2d82c100c026508503d040105040305000140003480385a02501c2c0c1c400081a0940c844807210a4643c85540c08035070420048d60307050203000c2a889403426050082c1c00016034440010301c50a00c00a10324000b9000050044c1041005403c64024001a00c2d42d80e0000003001148140c07805803661001d4100c42ca848441d16200204000008142c03000348108e0300d400000d41e0300e2407181e0055104080c010818404540311000381902c440c0140240c0c14540105025445134040010b0243d4031803206a541c5825603007880442500d541001d003003102c07000f0403c4c4889800344d9035400503081901d921a80c0840e5410031940300c1b01c11401c41922641485503081c07000b1803007003041c04507503400300132031691000100c03408400400a00c030b1900001003000e60001c00c50483c0f042600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 392462293 1250 392461043 392461057
    0x12061b090a1418220320010525021005040614010b09040609020306060d0b0d050d0305160c0b04081318090506060307081b0f091602070603091505090a0b0903 69
    0x25043d0a030110700e43c0000c8a010044030040100c1e9103841c40c0e410a000d0f011041c140103402840e1a003c2d6021449950f00c5960032031804032046ea469406000101d03030368045c0c00c00068081c85072080100c1404402a4170f410300992880c0c50280e44000280c1801040d41004a0129000001072419a11403061940503008010150b000c0c0d440c01d280031618080364400c1f00c4c0a0340d07004001c1c03030421a1b14054140544a080017083d0090080300343d10001460800101c468008952008941c0780780180c1e6180b00c05041d01c8040c4200010680c81e0004124140304087d003068014100701d5644103030703242015828070315070300c10804109513441a820800042e80320b01d48652040b02903d8954030341404140c0e88010500440409400c081400031215070f00c109001e11604002d0503008400c82000700142d50030504844000e00204002c05075080a60b0600c01c0e00017034900c0d800c0404c2450361946651007020407071102c65881c03550340c101150161808201064030103900075041c68a518065110548a4110003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 392463543 1250 392462293 392462299
    0xd02120708090309011b0302150a050403030b061204110a1701020711041b0f0e040207060f0501063b0d0f03030615080a1505121b12061b090a14 63
    0x100402c00e04500071044a16031001655800e01352200e8030b04044003a03840240850a500c90032541c4400e200c00005420b10410002400103001e2030306060103005c0d240b2059110740b091504018107650710121042098105812078003034010b032890800819601e118079008903100d0204420105041e41e030540007408401c0c841c451a0751403903032803010300c01551031040846102c00d00c4600d4282c4d0a51052211188240c0c00e494851409010400454226806110140c41d03107615a0050850764600e4003800c2c0c01804c01d85420850007802a1060b00b01d05016032203601d003015510111180e10500d0705115481400c0100b41e12103003545032a000b0001c401000d81140030904003c0e0000717080d60ba442910f00f0030445030310385070f06941e10319840304002c0007090455181d41007403480200305529080002241c0614030401003101e03041001c00e001005c00302c0030140b0f20440341c0070f11030010040c01007002c0f60030407030341000c0308024000103015400038018040c0c4a81c104540d1071002556108080082421140907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 392464793 1250 392463543 392463557
    0x5090718060302010509010f0504030b0f06010f0801050603150609040507090e07170c0a1107030501021308010b0d120909020c0102090108070e090103120c0c0803040504180312050c0d021207 83
    0x41900c000d40340c01e440042d02060044c80403404a501a1000b0b200071000380c41e0403850961241d41d9081c0020003642d03030000342100402000107a50f008003100c0c5005a05080c40318140d85000001011444024030030f80c0300c03603e0416032420b40c1d2600c000703072103c520b0001d00c1403083e4540307a080144000c000744030342400c0c08a4100811a494080c696084036000d205905a82694a03408480f41c070707501c510070341030821521320907050741e4035014031101001d036100700000b40e5584c94424418130300b07142d51b4010310456454034021100035900c0104038030981e84d0107082c03046a0a41c004096402520b290300ca900758a00000351001080c0040d07000f002200e03800d807640a041c0e110401c040351000e45824585400c409908010700200e848642c902c02c001e101c6281462403114030790396045000c140340c0e20110303085d4800f050900c124601070041554812190800c0007180303849803070080c100b407821300b400706c2c0d241c1c3d44002040302c003074441080712414000503500399680c41150b01d1505030741d84115003550000f408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 392466043 1250 392464793 392464829
    0x6050d0e15092a0f0a05030616120c0207051e2701060c02011b052406040b310605060a02151b070308150907090806130c180f050907 58
    0x4074114100070b0380c50344900c4031040300703e91007445140d2030644070240e41309440100000d9955400c009451040c3c45455958080c1e41104a01410000400790b154001e241004040f001c0c0c3d079030000c0c0c0f900807107500702c600c01c1074100c211480400c601008201c5e960001c0d1000040074440001103c40c41c6442c1c110350044905a0381c0340403c94580c40e035018001d00056111241c480581103444100001501520598400c1c2001440c1c1211603208041c070803c2840148041241501d030030301c81c1003502c0d002645c503e20304042e05038040c040201423180c200608a07100c122209141e1280d0f02c0207000e00000341070982e40320b481e1a0003030f54510001e000340000202c4840022040c0d241e00c4a8203025146814105080c490316540a0394602c40051040c2e248014511511040e03a5a03034500501a581076151902c0503803c2c56111030038154001e00c01c19104000e0080c50000a6100d070b4144211160610709100420410310410098050f4550103020103062900b846120180410a83c1c1298042c102549030920 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 392467293 1250 392466043 392466073
    0x62412020609040207060c05280807030c0e0a0f0e0a060302150c010b03160323190314030a1506031b080702030c011515110c21070603020a030c1806050d0e1509 70
    0x124601c2c600740060400ac02107009a8066040102078079810304007001110b0b4050045240746003558410010f20b69134041c10020508041c8950344c0003400100306000250458000c0784542c182e4840f0304210780350000380101803000a502180004070000d0a03202c0f0011021000d4120003444c1c0410b130b0f5516081c0030152401110101c062161400c6038015202e0804069111150841c22550030340c1803240d104400811440e2400056101e5416898001544200030225a54500b0b8640000c8149440c04040c1000b00b5490700007554000c8952620118607503602004030b0542c0205180500301d50300f0500503000c0c038064800990191001240c10399056034007084219003101c280b00c0038880c00d40007001c1c1c101c081c1c01e0011030880e2682001e09042215480401502c1c074085042e40047c00003540030902d1010b4591500940e03500700e01602d00780c034041d40b03001301d060280c1005124500510200240791b280031586600040030100144080d00c05442040d944540f00902c02c90f4000e003240210014040ba1003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 392468543 1250 392467293 392467357
    0x8010f0c0e15031b04030c03050120030a0b040204090c0c02030c1008010306051003050d0203030919050d0c02011b141c0801171603062412020609040207060c05 70
    0x401c4000c404007000340b80101544003620801030812211288521803410400420080d88628000da41c03562642c01d041d401c60710b11a0648081c030380440c950361161035035001502c2d0003014401c0005100400400054001e00ca0f690107001d205080410700c1c1c3d01c440d006140c045880b0700034ad0580320000c3d0048200301c402e039180c3c14904c0105458a00500c0403400344d07130003d0f500c08ca5001a4450076a12a103803140340c003001048180060303000004000d1510707014401a1003818110801200100c5555101c0761501d94841c3c3c210200444445414250381c0300e02d100300103141c400c50649031600d1300f43c10b010200c0804034102d069284900240019000604140d404d140c2e1030540d980540c59081202010280980c003181c12443e100300301990b00001508800c0c000154418540002d091140424000c00000f0083c0130728072190000000300070980c10304520368052507044900d180e5404445c80042e0003401280006080301d480c021400d46015081001010620078000c0d800d0414070080b003820b9004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 392469793 1250 392468543 392468567
    0x4030509130c0e210a0f1e0b04030f020607050403020d0c03080415030e0c0d0311030f0f030a0b0d02030c240313021804030905010e041b020c040624050c030705060108010f0c 76
    0x1540090041030100303006042d9417822030b104a007c1c1c0c1c05500c443ea00c0c0e40d05c1120703010301074500c90710b520b09000c1015002981200c520302140081c0402e0f01c1c101602501da07000d5440301901940800010004000001d051030018590000d030711b90300d81c2d07100c0391202c1900900030b503248042440c0645100c51894000b03184d903031070703000140482070008840e5130441d080b6142c3c0408000a103c10300c8441883c14010313000e0300080386002051512031412003000410ba89c008081a400b07018800c1050001d601c0115040040020903203e4640d1890544400c4405415120744141c09200100500c5000b0046408070130b10a40202e440d04030300b01d10a22194001039050301c004010910010bc100f086502408400c42c0c082d500030400074224003924450600d0b00d40b40b943c070f200180c00036445071070503141620481c0c0161021040c44024289400c8071084442e03c86404003042c8070340458590000c000800884117419030000c19030352070703583d1004518040c0020aa81102e03c03814404400c007101d2145010742e1311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 392471043 1250 392469793 392469859
    0xb0402070b010302060a050d020a052109151003020301060807060206071d010806010c0213050f01061119050106080d0507110f0906040f0605300102090904030509130c0e 74
    0x741d41d2075682080080c1d03100301400b005101050011030710854451000d13141507001d5403204c42d9214049401c0450b521503840821914000c15010b01c111014005441c0081007035010400c000350700c0709621012042d0455100960560a00c0f0003c5180b00d4040340010841d55a40c0850f20f90b5242d44a050317450000030300014403800890100350605e980300356012500710301d041c100340303100340c200d5004242d01c0b404101d001c05d4100e40f500280b00b07a881c801c8071940d0040c003061500741c00030b00142120329250f41c00c002c00780704103511802d50501445000e6000c5001417048808803141140c2d081000f82c00c54124001c00d860f03500c46130400e50300c00d060820f0303141020030340103220040b15510350041100400c03204402040e001d58442c40803800392a8180d102070702c14114554800c0d4801d1740740142c2c1d41301203c800b0104031030740180014030403a106c0018142e085581410202d841d40d0380c030008169070340c94005042c01c055080901c40140320b038002d02141340c285000da48040076030300480d00b40700c03900d00c2a00303030000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 392472293 1250 392471043 392471063
    0xd0f030203060d06090803151504120c0e10090b01050405060a0305131707200916021c080108250902091206070302030603160609030f050c04110d0b040207 68
    0x15052096004541c03010005010680480300c5440341c030300300c810b2a10100c551400c00001c0c88a80328040350301d202034200499903201900042c0e0513400d10f600440c40740c10a0307201c0400d50001000184180c40300a004c0c40c04044480e0b00c0c00e0b080b1468040a1031040c3c00381c40f032403d14481c4c6076500c5002114241d41001d840b461805041240803001800000c04c40d81020b400c040c1484002400c6880c0e101760b55600180710394480610341449181c1c860300c10b0380d19080e080c060359030008a847d04403250380e029044d01d00300b40300e03000c07000c0d01681081c1e1031032110302500941424404001e508000084d040c0e070340c1c01041720140c948040b5800b210300100010044c2c4005000e0301042081040d80050120030700142015141d5146519554035002c000c1d42c50101007034020080040f5030808201000b9111000e142030001580342030005400d248080c00041c0c030303c4a0b4007191405002c4204441480703040c01a000708010070401c85c2c1002c80c0d4000d040c0c031003543c1e81070481b40309032031600b4002e44040c00c0c0c001001032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 392473543 1250 392472293 392472317
    0x3080c07081e130609050a050406290c060112030f021f0209040f02040306090314040b040302091510200f0c060c010e07141f050a030f0b030307050109060506030d 71
    0x800b484600011210719040810074940d2010010728000001c209a4841854a50908040068403051500498000d03442e0078010010b4904a40700d9a0040c0054540c0c10721800daa05d092800c14802c80030384103500e00c1030400029a509104440900d050700a6803682c000f4405403d08a8a47e400401d44000c00c8201c003440a45040701a4010041c080c070051001038002402d008100590304140c0c8155402039030340f5030380d02c107058001001910302400940b041c1d203020300b0180c1c2a0103a01407800040e0089003804005544103440400c40051310740001e1042c0031200d0100380c01406075650300b030740312017804080044040b02a80001c4022000d10707140003403d034114681307041c005140c02c07070000407269648400e1035403000e03141804928054100c1030310054000d0000d0080c0060280c0c5e080c40c1c1c91114440a1603250101c0d441002d40c0d900380383c685404610395650741c2c00000500f2a60a949915000001d254010440b0540c4402c41d494031683e01803042d9500c2004240d00e9080010400001c1003200480d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 392474793 1250 392473543 392473567
    0x40807020118180f0608030408030315040f0212041403090109050607080d0501080a03030e0601140108060a0503061e0a0b0321130f06080a0515100e0607030302040303080c0708 77
    0x42000b50b09050000d1080716518074101d140440290080100250380ba81405880002c42c0980d00150030224002e5113800c1c5000e8400c0e1f03403840000d00c60740000207200d94900041d51290081d404030051008255142c1001c80c207480c944000546084611210100300b000d4031550210a8800440c0c05841d150111031600017070010b81c1c0c0c8074075000c1703da4800030411206900c2036032068038040e1801200401d41250507107000b50840304030300c84a0605a0051004008041076521103022510b02842c02400c3c40c0c80340000b180814032160410781e4140110380c00c10508812480c082c0c5010071100850309c2664884014443c1251003800c49150943c01002c1162003220b01d4400303048050032f0705070142e8540b200b050316250681401c2d0708000002590b40a0402c0142e61010b80e050300503800e98000c00c45070038281060201140348a066601542c6042c3c2400d9900c0c1c025000c5000302d40015220503a00c0c0f000e850005c0003903003d4003040300490403090224100075070045c05d44540a80c03000029250034100440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 392476043 1250 392474793 392474807
    0xb060405040f111206011202030c18060c0a080d1103041109041b0312140a080402040b0406030f06050906310215070506010e0a0b01020712020123040603050c030408070201 75
    0x41202e22910303030703010000c81008400100004000e02d10380004d50305101c000142040300505444c802e00d801401030141c402800d108075004c154000700400440c0f0000d0000c034480380100700d0041103600500e030701030b010312050b0401025401131481080002000140c2c0b180081e000560300540501034400f881c140d24200100c0d0a41c00c14041c1360303412154806c90807609441080d41d0821200203403481c056400d155040307100265010b00c884c01d6142007440350350300100003940040000c0d210315100c0e403140405171a503900135005107810241092507c000307800e00c007024141c144c1e40c4d100c0e14802c4100080801c2200041229540c410f100c41038441c00c00c10304843c0010700f0a0030180da202d4501c0c400e203588030076038070001c10030184114040c0c409580341c654880d00c6800014104001d5900302004000740b03a034041550002e44032008401002c0b04401d000403075144480840110313065600040b8445101c407000d002e801101d06659043c080340d5548584007409010540d8003c3c10040c051011100542c007607a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 392477293 1250 392476043 392476061
    0x60103060902180a060504050a06051f050f131d090304140315040b090706020c010507031103090901030c090c0504051804060b03120c07080309090c03091006030803090c040b06040504 80
    0x40c040c841c0a001d0200180f4400940d1000401e0390b48241c1003215013407c2c0203083c0d000900c01c504010582c50803001c5000c0c24220b804402c0081080032b06100040d000350195000181101885600d6049424078680e401409002e800903211940f40d0110350f50260b038024074400d81044020794205481e00000f05200c00b8065001989400b40240300c3e0040210042c0091180c0d0007190780c0040e07801c3c100c4040e0305020701900002c0454200c5024105242d8020040b01d40081d07046c1307010090103c81342e04290660080c21046a40b004030340c8000000d00005031403080c10707503820041c104400ca40e4150306580324400c0784183c1d50403240c00e0000d2110350000b9541309038414000c50340440d4181803000002e0810781c5190300c004003c0b001064149200d901040b0000c0901039000045250025900000d100c0a07002011050401000000515040e50a00c8121031010100009100e866228900b08981c0d0b082150b01c140288601c0f089071005140030b0154140b040e0700642500e00e40307030034102404081c0600c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392478543 1250 392477293 392477299
    0x40e0907080115051c030203042601050106021609050f16050705152a12090a0b10090b030105040f021216080a0611030403050d150b0a020709060b0c060103060902 71
    0xc24001000740c001c0c0a0070004001140d00d81855900380400c00c01d542036000300784060050800240e100003178001048505030b428010300e070168140b041c400c01200c4009611031031040d500b03240002880c6500000ca0b0001c102d0040c00f410807183d11001e8890031078508989146010a01c1c07408260356403200006032070340144500d80035207809003d881d520714094108804014002c0c1031020080c82c80810201e1815040203081e00008411071002c2d4038040c2c0c01001503050f22070a411001c1090100200a0381b00c40d154812100d412030329000c5000e20700508a4480c2520341030030110b400c040741c40c3c10301c50288102d40c005004440e42951342c01340101d40d0740c413101c0110607104501c1e1311051603501900ba40000d103203141c003e0002011900e0704c03000350380b0605510b403000d24007403040c4000a50054241c60382030b14441d0000440b085241403c41071160030342d101d0307480a80300060400b4038960200b880700c03c2d20210076003440070b140e440d0035281c0d907407240b11080341040d00035000620028203180c004000407030000f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 392479793 1250 392478543 392478553
    0xb090f04110105070615030201020123040b0a0b0d21112512080415030c05070f170d021314010f030b0301060f0602070303020d1803082a070e0c040605040e09 69
    0x55641700121100d000c5124460442e0110810442d81e0900500c4413031018454a09100c00c11502e01920864000d0302c0201200c00302e01c0003800003030259012000308080284030030f0f000c1109013089100700900081c5d1a0620310048425040280200c4240b00d5043c40f91008040d201e52420f1040076910140780402c40340000345000245000a0050310440c080c0105a40f650310391404200d90180c00700c00d22042c06060a03c20300343c40d415042815110042e8014000540c2d00f41b983c40e04222403ca0341d1b08100ca41100030600f10005078665000c3c05100c000032149124154607001d860810000015113240020440364411036071502c85d4001000c1890050700102e44941c44654aa41180c0c8a402070001a40105d80400038194100603a00500f07500703041410f40502c0b420401d22130b40060740005080451700003200340380c0b08140142d582e8065000281c15100c511600703900350300c51581d8800c00c201c4002c1d00780032480c000d201508a80c2242d41d2522030925140c600344000b03a00150080c01d43c0200c0c001c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 392481043 1250 392479793 392479807
    0x2060a0c03020a170418060b0304030c08070803100e0f0108100c0c020a032108060109093b010c170f1f03030e0a06030b0a090b0a18050106030b090f04110105 69
    0x14809450b8041c107440d00c0e65121400e01d0360160985c402d484e0082206c40c2802c00c1045406a003d0803a60410b81510302205410400e00b0129868441c1c00d00003011444c00004001d4003005624903401954410484c0503000d44807031840c0701c0248028006c00c40c00c0c0c0c001c1d144610144611780c2c07242c807481e15036052a0740f00c00c03d140c0004402c000340741e006441030040c0c441901c45a004680000600420a0030058001c0c101000000d08400c000d0251800c0d59a0341c011121034001d0208084040036150010035a1901c80394940400c035100402240240c4c1d030800086e4120b07507000322402c0402aa0f00c04002c112a918014030114040001d801064042c03003c0010205141100722140040c1d400b035200d5042c00c0c00c2100070b1203156500c40d8020800c00d442c25410061943c0c440072180d0440303c492201050118000e80000c08440241c0d026540540c5950004c4510040341d800c128102c0b0f0840e20100181142d0005200686038200c48014941d5030290010307000400c2c0301e200c0001326070107141042c10516 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 392482293 1250 392481043 392481053
    0x30c011d030c030a08032a040b07080c0604030906091a071e121e05070506151f0e040606090b0d020c0307020a0611060615091c0b010f031b0302060a0c03020a 69
    0x480d0641030340c02650000410001150b584e28842241d00b400300c0f154180f001c1f80954a80a00803030058640c0741600090719801d105103282918804c42c4000c2c2914a94246440c01410a19407440b4030700200e10310030b400284400352041c04103128007055100620706034030b42e60b9502c4280c070030a021540c61440e5101803004a0503480c07142c800e4851540703500c6049141904501c038451094004a001c011040010000140c00842c020f034200d03001001c0e103803001110f500016540f0b4260300d104030000090707000706030341d0a07400b2051290054054070100100c6440300022500c0103414007500008440401c4951618929580140780d62400c034000d0324200041a400100600216440580099101c0c25504440e1606005182c0c01c5a4100c40e00d00102c1d051046a88403400b038200c02a10810802491544140c50340c076285009a41c80301040140e903031542d401d010410a140019980b680280c0583d076240c2001c56198030980b03400404040c2002e00500d81280e034468582022021402003586404c0040c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 392483543 1250 392482293 392482303
    0xc06160507060209060d153b13020907030f0e0106060f180302060f04081c0807111005040c180b0303070206030a09020d0c1e0e06280e010f05030c011d030c03 69
    0xd4035400920440c524100e60000c200400001c900b00230484101d050840700250081991a0349140401c4043c036074035509808a8a07010740340203900a4508401c014003c1d07031591103209600b800010400008840007029801c071481400b0348800b00d00240c0002000501580d40f500c010951400c40d07a207075940b240c1c0420416005406200c0d08241c1c04034040c000000c044c0101d40050460001c2c20080c04101000202105c2c2c001e068001800302806a010030388070140207940000007101c0041c04141030524024110041c3c91040003901c8008a5180450101500815500c104003d00441c20310010741c00300101940041c00003201c0c15514a007442c010b80b6110500401c1c0d0340070300646c80c0160300d03004103c07c0c000c035210360f0301c1032144180b1424009802c8102c045900321805075800000503415018074030501c1500d50406660810b480000144400071703034109810303075111030a040c656590740c109240d55401c40d072019134003291442c03030403403d031040d04403c0c4c083c03c1800600f103910036021880030900300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 392484793 1250 392483543 392483561
    0x2131502071a121803070609110405040c090b121f050c04060f0e1f0201060e010b04030c1203020309030708010c0909061503090534051002060106030b01030207170c06160507060209060d 81
    0x6500c23842c0003010300003000305a214100c0141d805112500d03003552001405042c038000d04403901d94680c1d03d440c0302c0c1c40780740b2026041102076084034403004902144d0080440d400e0f8200040e10309110010380f401c030205080d00d08503107150b21554174801406c00c041c0c038080e031290031140d0807407a405c0d40409410203803000c41400d410075400000c0c0660820f40581c1910005800182c030b03d0808200800000b0310455494046800c0e1038000c00105a0518007241544a4542d003994103100e1580c001c01c2a86065200010345081611070590003aaa5103002c01511164414500c90300000181040b80500940250130386601c9202a03450300343c1a452041c1d048050007036800140d00d0200c0742002040c0002410002030401161000c2042c00c039010300a50740e4034140515820580c03501001a01c590181d01a100c032241e10034200d50840c80030102d0383e070711900503107143c2c43c0e50711a500100e03102c1440b020341901d00c145a80d0b501480c1c00401d403264000b07580a04000d542203041045500f6040c90306128103000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 392486043 1250 392484793 392484803
    0x901031803031b020f0a26040828080d0923010209010801080705061603030608120c0c18150a1802031f060e0d050102131502071a12180307 61
    0x20b15540f058501001c9805a64200e055602c900e02c030000400f00095040c041590001c07590750b0410101c0c0c02c5218aa007140c00105200001003000300389003402194030581516480400b4150503030404101c030505020001c0548800000c0120b0079290b1940e0300100201400b50030120881c80b0f07908545400c292100c1c9142c00d05950200e01303c0815a40541c10a0040c844a00200078441c01d14000801c1072194200d007070207480141d41c0010426000e500300c071000740156020749503564003481036024940d01084d0440600d005002004d1001c1c40e19002401011210700c440c915a079403040d0b1700c00c0c0842080079509074041040880018000d0316184400888a1951400351b1a420900d0029003c0c041217621506454101c040a0107095444540d0480c07110045030f5211000840e81403d500a00c6105203202200105c2c01c0042034003240c4560003c00152550f00301d0f00b005a50f00c28240306041c0400c40c851500c00104000c40ea00d0341c2014506401a8405507072000880011500c41c1c51540b21200c02c41e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 392487293 1250 392486043 392486051
    0x2210c07051f0b0f03030406030c090b07030e04050c191412040c06020601081c050a0c0f0507051201140112050f0a0b0103150209010f1116061e23090103180303 70
    0x1051440d01540340107200913501d102c8168400d0000a450340214080c2c0020165902d0b910804e0612038580c6100070300d00c4a1140303554400e641002028803e8400e0001d0095003003002103040903105100312034000f48002c640240310010501300311407090131020307600b00d07600c4107005806880e0520503155002d40c0c81050580c101c0c61034094040e05104050b880600582c100c2c0700504c0f40c1400e80444158103c489291803691000013800c255560402d903800a8003083c544480c0b10704010b0300103044010340701e007114001d2003501c1d40803186003650140500d4072400e00d2031000410140d04050f5050f901d6521640a0350181c2e441504914500303180d0b40d40a891400c2c00200400610000701000c034030601c0f00010642c03914002c140085d1520b120411008200500c0c484110a111010301080c43c548000c14450850141d03520070040400b0350280d0071f40780300c070445003159241074011503a07603481880081d041440304e9240c03603503100c442d04104241da06041d22100c44101052444003070044480c07294438001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 392488543 1250 392487293 392487343
    0x2091206010302031203090604060908071a07080114030703020114040b031023010921080d02070302100506030601030206070c08030f07030807210213170c120102210c0705 75
    0x505d48034900c1341403010203004006100c40c01501048a0364001c3e04803001080402440c94808000d10070540060844130a07030781c1002d1038000201d4201d004060340d0b9286101640c9880174000d0002c0c1546040303515620401c010801940203080c0310742c41400c0d0030307001d40c01c00f613940d016200356500484130700c83c502c001c0d8a81481021010703600401004c0f1460044641000010006000c00240e0300030f828090042c1102540c408800341514001594802281c54880c1130301440344010f500a11022400b42c06040c1042c0c103d04400d01c20580704070402801448140d02c0d507020b0084951108034142d55030481c0c0d68010880c84000c00080050040c500c4a50341e5a4440c1d00b402084038002500c000708020507a544180d1601b0320303a03406408800c0c103080059071110080c1c0074039450502640800e0301c000c03800089100c08007012464050034030042d201c0d001e52141c01c0c4e803018200d11038114218200c0c90030640c01074800800003d641c1e804040482c444c0e00d480d80c240ca84a24080030392186000c2140340542c2d070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 392489793 1250 392488543 392488549
    0x2107090e0102070c1403060f060d060c0815180a0207170c0601093213140606031c050f090a030f060504060c05040308070809010e0d0506010306061202060a08090102091206010302 78
    0x102c0280170201c1c0d0b0704004000c42c4002515000c000d02441c0f050304070503002c915140e03075865080c024181e00100c104008031504201401f030500444004600c604a01e8004e60346050440640350807844d1020f084406564052082e0000e4024140940c0c41c152000740d0010700d01c80b144003c01800c81c406000344078542c9005803010503140358032a60444e488122010b416403000e14500000d5000d900700c3d00c803290340c0c1c03140030076072980e14141e0024056800554207154000404600c19010322001e03000d482081e4940b01608401000000900d00012400c120700741e4504000d8001d03180d5903100412040640b82e490b1980a01c4034620002a21980d0ba070707406010420081d03202e0245811710170700b045424680b4589442031580910b002c00741c442c0c1c00c0060092800c0e071007078002e0b1901d6500285011114042c80c206139940f040c0c240011130740e082c6003c00101f103440119514900b4240c3c0200010f151000c5403908480341e54000c1e11413041590240580285552100c500000740c07420000280710540c918010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 392491043 1250 392489793 392489813
    0x7030e0307330531030c060b0a0308030105031216030c021305070f0207080c011d0d23101116050718090c0b0a0e060a0203120a060305060f062107090e010207 69
    0x130400040580003052014040b10503442210f0640505000c00c0d400d025050407400340403200e41c101c1c3d010b42211404801c1007110750113141a41e82c26005c40310001900e0410599a2181510b40c41c0d04000d0441c4100009100300b9844060f0351010f81100e0f505040060b0760310664009075a400c02080b0030034803060400c1c1e410080e0000416120009000c003141c44800600f80c070920350450b10300344030342c0b0301d4400ca16103071942e40b10f0000e0b42c020030f1119040d07134004040300e42003101c0c130514000c0c1c044d95141000b804401d00a071514100c840f440c071403924100d16100c40c1d003103209900c1100c00c0d02403c0800182540c101240794038007140c3c00000305a184052030300410302d1105400c803501030340d000d103c419041c44d8890245101d6172020745d00160b40d002285c10607443e5000c3d80c44d048280c00c00250401007421702d1a0050000c4134414001c03a800b54a40e45a1103040440803500c0a400c803407012582a884d6820080d107080449807101a11030721501c410107081510180c06041802da034000401104101c84445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 392492293 1250 392491043 392491081
    0x501060e22080a0c030c0215130b031605030601170f0718080a080726040e0a020703020a0209060a1e0e1f06050d0204051c030807030e03073305 63
    0x64007052030703007180c0e60381c0d00c0c50180410a001300000c1400700010940294450030382e40d07400402020b94251814500c0f502d83c4d0003840c1200001e0f0b80558001039030403041d0203aa006088200ba042228400701000311404d4000401d40c0f0704100c90f003005003e02900002c00709014060002308002e4038038140c80090315040c0f81c0c03d5504104612048204031003880414004400c6a008010039510512824100c0e00382c0014040d502c0d03034082101c1c0e40f042402102c801802100c03801803201d595a50303040418000c90140110240240c0c1100700450014645421a0384d4031600c014a803a1002340c0b10f905d00e81e18089102038640c00d60020070003c1c422810019195a400040c404004000c2d2500000c000c58500092041105103c0086140a0806003a80684002e02005051040c51020707100452042804640080d004110ba02020890940c864000e400807010040000c46c6000030f40c0d65581501c1e241843c1c032889400f40741c1c0c151801d00d22400150140e0070900c00c00860541001004d817810354004070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 392493543 1250 392492293 392492341
    0x3110102070501020703020d230102030103030906030b0f0f060f0a0c0c080a02030307060e070e13061104060504050603040c05120f0d08040201140a09090608010f0b040b15160501060e 80
    0x410402c41a0390000321131080c2d0b507058601d45c003090394624040c0072040b009180032164140128414104010540c0558104ca000ea0b0f20210803541d038900c10703001c80e40007541d447c0e00603035803a601001e030b4100010f0803c1080781c0034140a00e041600006003a907500116407002c00140c0ca0004502401001075400c03000d02000b001604440d599a800280d076480741820080030280c5840400e041400e0500c002002044d105070151024582400c0b45012040c00340000c59520740f07410403210068102c0803d6a05030f41c2c2c0c40d2150f83c60103003064200700b501c1c2c0004100b10343c0030354240c0c400301e0261605006001d003117090b03000805400d031034100e88a0802004590741400c02c04200c0802001d070f07910038058484480210141e43e5603003e00c0404492584e01a0000304501e41400c000181c0c0e40015806040400010311041000d01c1000e01000107481c010780e0200d0b480301841c400c80390030b1441030000f040000f08140d04910340c0842c03079542c01d09440c07060b8042c60b0525044c404001e00d0070756016240e20f80740404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 392494793 1250 392493543 392493553
    0x705130209011d090f13120e090f0609060105090a0b070f120e0f040c0e0d05030a0314061503090a1502030615030f0a2c0d020f0706050703030c210603110102 69
    0xa003c00c6040800400301075640da0305c0700200351301c10718492032030301803503040b003003503010591810740140a01001c05c00b002c0c020040b170400280c060050049807401048000d165850949811004407126003061100b0796114801020016226a4600003400040d106000c0d695200c08181001d54141003016001070501100841c1e245159841d442ea40c0d507030400440340001d0722282207404550210b45c4c41e440542207143c4c0c031042c40c140140080a441500d0103a5014003603211554400002c10f07605070382c0160403500c400c0020750401c00000166522441a104a900c0c1c2601c68a070111000500811203240941c008148060350414400b48807881c032407054090314506282c1064400800014500b140d2165644440710721200d000710a010140f0118032955802c2d80e0010001e030b01c1d200b00342c10f030030054810b64a03035000c041c2e0007055000031503805860301ca0825919171015000342001c02080c1c001c104000040c04542c0404074070b1090241030049001640c00d0552404203092005400c0c4c450544d070003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 392496043 1250 392494793 392494847
    0xf03040e0a021c0c02010905010612030504050d06020f0406050405190b1902010609020705100615080a0b060403060f1a0604050d03110c03010509060f0a02070b0c0705070513020901 79
    0x601103540c0c122409840050b99541e1039840000300524020710441d6141c02d010540460503815000040f101c0d000d00001c1040030360b200010007260100010090108800740000c11540c540030034a1101c070341c01050003620b01070043c1c0485400368025041381000c901c01260a00107170502410307001000921a040e0881d0600308012041d030781c040c9803143c0500c40301c440c50f280703012071003074100c3d2000700172002d41503460704000d00c0d0182d21201a402002d05251404d034000441500c681c000310f8486c04141c803218000c0c5c6641060001800c001340980b508210b08100010000d4224842c000c99040c07502c500241c80788507421404034450740e8160031845000288420f001507612000e0030b03020b50343d140c02ccc281c0c00c07814003011142c1011440c4034202c1c0c2c15440d010030800300315400b007240c1c0c7c495951903045420590300d0842c6107080b8011402c02510004403840010000e500c02401405414022001c9034400d036030300c0000840010007004030402c44c540115000c1810350b00562008008480c0f10302c15009248 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 392497293 1250 392496043 392496059
    0xf0303060f0b07020d05070f06110114010e0c0310031703071b0305041509030c03050102090a0618260109050106080c0d1104020702060708120117031612020f0f0c030f0304 75
    0x1c3c041000c0e1184032110042020000100600f41c0203012119035011900e56038034019010051201c0004034650811010038400f000c45100181030755020030400d2955203541740c5e80c40494200130302c85d0b0301310b800190011000c51300d0310611460b0950503c4100d41e480c07034003005c001c010744e44517540050b0032601c170140344002a8000d01620281d4101c1c038002c07440020b0f1000121a080900e61015000e039401a00200c01d201d411340051818120540b400c1c0c01c0c1e20741c2d5074401c4a03414204050392104824031042402418408041511410440d201494401841c948564211204100200c072203a40d180410058401d06201b040c13503051003120680d8031407543d52200c0c1c00c2c0b0403078221000c0c800c95000512000315a07400064a0000d60803007009511007201440d03001014200380620440f510300345102c0310981500000b100c0a1511426030800005610794401c0640107150718a0720560181480312080c3c1c134020000780e0704141c17244004003510342c4100c00385802c00042c0b2440c1001d54004000500c8482 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 392498543 1250 392497293 392497297
    0x3061206040f03080718181b0815040615020a1101050a090b03101203090303080f041a0901020d0207061a0603091506010203090604150e06030105100c1e0f0303060f0b 73
    0x1501404c1602c0117940c0c1d02c400315104002a6040e442c4c0040103900070a04410640858050114a280400a220840c0300030020340f15a13140c0040095001400030b440d0344030341d00951100700e4000e400031507469243c080501c40c400300616a200140c0c099001030081c00951032203d600d010b002e0811603c0c00010b81c40041c07503080180507424405000201180c801c0d540300b4002401408071080c0102400003d10340185002c01610059000510140100c2c440000500f0203034051940401500814010303450741660718803000f05060b181c0d55003481000c1c8468070500080c150640300d40e034001001d00f208144250802100e00107540910000e000b0001c01040000311494041f81c040d2100d44280e0302d4031f0040b823544c03060b41c0340d01c0c3e0840c801240000c1e41c6003da00303420034180184d4540c02100340f01c070030902c4524042441542e601222910440d40003601400d80c038210140203008256090080f0b040c00d059040251b03600f19681c2d88100595020b00d40d240c461030340a000c5104562400d240b07050511003082c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 392499793 1250 392498543 392498573
    0x5160e010503060a170609120405010c060c0c06060b2107020c010c080f120105120a0b0a0209060d06080a020910080606150d060905070e0f0310090f0b0a020306120604 73
    0x1c0040000400d0881c1c1e1100961002401e8006030204019522190162150707015542d591940c4500d58001d03200b52041803c0d10141e8074103a42c1d00d100e0036002c0d01e0320800781050034040020700980345003513804241d241c01290050800c42c3d80c015660148001641c0460051701020001c2d00e40180c00d0000b40c5078041203048003641c09180c1220100110b0074055030340d10480355405004100003825020515a4042c528100e0780c0c100c62502615285d9118185c4522032000020002a401d600140041810307601800202c60b01800860901c501c0340d10b460210380d181d8008200344d51014000c002145000101e0b60b50100740c9190382018245811000c55803440003030b10301d40c07040c0c0c03500c06a50003900c82c40050f2490030751000030a108440e918410310b80102000e41e200d600041c1b1018030000c850400101e4a0722804003d001801e070f040b4010106070090840c4038088640c0c2c080880300300d01250305114218015440034000690300e0400e002045000070041000e07407242e4102d401004045640c0c42201200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 392501043 1250 392499793 392499797
    0x3020c100c2a08090a0909050106030c0524180411030a050c0c070303080c07060c0309050609070b03010b1605030c0d0e0d030e10110d0909061a0711041e0b0405160e01 73
    0x40380c4c0c80760b001410761003042c0c0001d4201403a0000d01001c0c044150004004c8074064040141883d03110003d0110038000c01c801065498004021180c00d60011402051510030a483d030413007040d081c000040a4600e910b0149407401c030b002c02400303d0800755119294016031450741d042e00e44100000030a0301da000920016092101140000d0324000f0300c4001c41c0e0406604c0f000c01c2050300740360310000d8004c061250040d40e040c85090f001441020300042d100043d41d2614040030f003580e00c0c2500e0014035604c090010040d0704214500c980002e0000c00c09840142101c4001e0070804c4c000040080c5034548174110184105400c0c40d040d004250050060030004409981c442c04103c1c0d461800c0e0f510010003401e064003031094110703500d849580444040c05075a00a80240001599068800c0704000c480121100407041042842c000540c01c1103070300003011024001041a007a01104c000c00e1240c0401281012a290000c8440c1c2d171800303100f402c4d807155550148004148181c24000c0031100c008540c681 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 392502293 1250 392501043 392501047
    0x703030219020105120a0c080903090d0b061c03051b0c0105030a0f09021f0809010b1804031806081503010e031c060b0316170603190303020c100c2a08 66
    0x643e40700da0111000180319814000d554100b00380c0000007071010090400001e0203990103c1c041c0700b0007108580b103680008280c604a81c4040e120003401850184c41035610109041c03444440d000b2410602c3c860f140a5107910783c80340084000c2d010100c94261088400307400c40212040d5a0380c124007945d403c106d1354640003481c140c21034841e90040c01c200c0006548040c2195080c05a03e908520020548500d580d030044191102c90700c0600385d4880548580e40003500b0504403042c11154a042e41e4094020f00d8205101100402003103011400c68028100042007802007061303a410300f44018400001c140d000300940d01c02d50640546a0041d423407800c803ca4559407c417109030b46150410000b0742061205e0305e55a050419402d82c20700c038540c20f4000840c0004e0381c50103031659805801880b4060240107050103a00004150243c1c0400b58412800d00d80e003032101c1c0b1011902003103068180390540200191030740e4510005083c507440c031220108002100021030000052805a404602d944807100329 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 392503543 1250 392502293 392502343
    0xd060c030902120303070215010305060708071e1806080403090b16080d0603020109050307080601050103020a1b0b0621030919050306040602030a06060f0f0c05011d0303010e0907030302 81
    0x18090320180e60065804800c3c1401240340c3d0300088020b500424107502100c0f240f540c40000812461024480030302250803620000d86414051100b06911081500c3c0080300b006048401400302143c440a4400280340d800503058034490080d0b111001d043c0c0c2e81440401440d01e03030b80003006c18540b40506030308201c0100301100e40104904061516503409400e0343d4845d0b01d85418940180118801a80081d02134600028075040108514040c1c680102c0a400280c0c00c004c0198081c5d8051415002006021300307007014948003051400907500d10070803c0d01c0301d504120081007504a280d0211004908090080c22800c07000001140e5107001d080c0d8058844030600c40c03a9014014086c3d00a0b905802030000b0401040744640c015441800e006900304100d9845a001708ca80007040b0b50040003007003c015801000c0f501402c804c129443c03240c0d0020806481106103510304d480541003c1249500200041c0305100b202484560701c950380705c0003000c4075491500c00959400d0041e40746070103413030241200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 392504793 1250 392503543 392503547
    0x80c011e1d040e01020c16030201140a09230f01030e0c1203040801060f060f0c0807080c211b1209010f090e1510030c0905040c0306120b060a140d060c 66
    0x940305030750004104000a5500012150203075001210f40759031805060041000c0f2000c00e0405804c2c0c0e601070303440000903001c8007540800c03913001031409801c0c8914140000703011180e0710401170000d060b4060b80c10103124508203100420200807032032030515040a00140007110b00280304454454101c451308520038417001c81c60709510a0b500300501c1c039402c0c4103011504441d01e44102e0100d682c00d90300c08000b4801404125040a90841c00804801c2c08018a0000c02d100307002070f080d4008000e0580d40340c0005203001c050762010b100ca8543d82040041104c1c981944c012540005200340c0b0700141006828102031481c4c24440c0742100b80c1480880f40d1a0083c09108403a0320000c1c2c00d110f00612800d0401c8400c00000318581c81c00944644400d514001e80144640100d12030102e50341c465444090801c001c000250018010207000c01d0b542c0c100024070041200f0940d84485c1c000c080d042d216003000028040c2d200c8440e08500f080d00e107a040c201c0e08640702c0301034180da8183c10034800501c0300d07420481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 392506043 1250 392504793 392504837
    0xf0307243507030b09280c17091c03050a0e0a060b01140301030c0e041b0f090507020115181503110901060503091510030515090c010c020105120408040b0c030301080c011e 75
    0x7140b501b18908035140360707620b030400d0380d240008002070381c045c02590310282015550061800c0500e4a81032105800140c80c4c043d81100c1d401c0b4040f044081030380900c158000b40b0f0310710241c4040e81d46948a000c0c00d06696003041003007070300f081c0c044c2c1503d195604541b108040100d50340704bd20020030300c24002805110110b5581c4150440220341c0b07909140d56001403c0050a1500800031080c0c03900c0c0110b5412401413051103402d05d6030b0a100c086451a10245a041e550081102003909488654901e201c0959240c104007a40c801c0c00403a0002010b40107202000e8416000003062003420820710005041c0026102229a4050b100c80303150754410000070000c007015400117089200f40741000c1031001c00500800e200389241811a02c1c1d5090031001100c01d0301e542a00607011a00410200c224520841c1c504d60b8880e005075000340c03030309030750702d1a0400d40e900143c0700184a0b000400140301d500403c0c404080954801d18100c040314003866030b00707903040e84440400c806000f444907000d000c0001081c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 392507293 1250 392506043 392506111
    0x90b0f071e2304030f0b06060d0204090f060b07052509060602060a0507140403150b03060106120c0c11040507030902031b0f0307243507030b09 63
    0x107550005501c0400c40601a00b14440207441c6042c00008906078001a84080c0c804917a04a60515035400702d03030711440407041e40a40700503081a010003003800b00b81101e000500c01000c43c00c50000380d0101982050044821a030000b41c0d802d0410481803012903000038640a03103d0301c805287e00b1034036400c500c075445104294022091141000800903c017600402d80d603116541c2010103011658402d6404c0b80c21081240b514900d0000034070007400480c99030320710385178400350480c0d00003070b4465008002454507200368015000a0410410201e8201c1c0394096928141410b0070403035407c403c241d03620400140600c1286e8001c50360303000080c06c3ca51003500441c28164024003600c04d050100c0c0d42c007155200c10307240b0060103542142c1c594a024200041c02400300c400681c90350711000c41441080340d048140c1c0068000b0449140c04041d260000341c500b0850b1010701413034503e2800220f516044040394001d20080516152110714609502d82081166000d00e114801d594418a502004045510201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 392508543 1250 392507293 392507327
    0x127020c031c0e10060501080f06011d0f040516110601050105040302061c0c030e010b0901080606010309141006091b0f2609060901060b1c05060109092904090b0f07 72
    0x303900c0032405103074044d00c10780360282c0e2341d000c0e29910620041503c40d41590400e00041040325005440341c1c289501c10500500140b84c0d00d0301500c800c2c00181a92401c2c1d80d00c290f4460000a00ba0b00182c102c00d140e8900b078076500c0a002558903000c00a892409a0310020780641d82c001032410003400c05034500e0310780f04410351007004a00340081700100103214641c1112460740ca401c2c9a8245840c0241d0350a040381c400f40c0090640b507a03900d0045024045880d802ca0f039006610901d150b0b41c030b0090010b060000c1d1050800203840b4a000c510500365080707840e03144100c0e00480c2050325407690180444c4075415060902103044808910a08400b540b106202203103140242c0034005091008100c05020720f810300c0c002d000e40d0b51241800f9040348101340100c01807240301003242d00061500d421442d80100b050508a140c0c5070340e4191007040c1c940c0c40c00030601c410390a43d9a02c1816207403000c0c21800600c140e0341049200700c50380c1c503238807158400f501e043d01d4108108006003d5501c1031544104cc01c14172 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 392509793 1250 392508543 392508553
    0x2d060d150b120106050d061d03030a091a06030a03110712050f0d020606090415110a0201140708070f0503060a0f08060a0b0d0b0609061302030127020c031c0e 69
    0x1650680d0010700e10045880d01ca03100002c07040c0208a014000c850a4800040c000000c1c030f0083d036a0700000300400c1c0c84440d880002035900e25421903041c0040d40c45005103500100b6094024600030510741d503055840c0d000402c1c604203100e05620002507502840b91305040408000811000041c5004204d03809a07080611302c40c019410007202045002c0d41024801c110342d40c0181d000000e0361540d008071045c5402600407400107012403140f0b480f2801d0005c05410005003036041608034100d56100781000c80c003503074490f2014003c0a02480e4074a901190b1031400100340e04012000070326150400722460100f00340800496810394943ca044401070030300018944800da580d1100c5ca0b280c031030444002004030b2500c41001c5071400c190306030250b41c035400808405241e99207800c0150203034028055a8120010603d80070031802c80340300441c0600071300410300d00e0103030303400c805550740066024224200c42d0040c4801052042e001003540c40207100405010350a20303403091980300074010003901600911075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 392511043 1250 392509793 392509823
    0x50d020a05060a0e0606010c03051c020304120806030d0f1115011a04081c030f050a15080a0804050405070512010b130602010c0807050a0504030204020f040501082d060d 74
    0x19250000d184540d0980d5060342d6503018910031950701a0142441d9002400000c8007503104203005041ea5120b03040007420455a6107031041000034540c2c179007a540d85d000080c481840440c0c1540740d82c03150a403401c16001c2c50480f000c070b81c46e4510004000f040c0010341a076002c0e0140581c001280e41006001240c203001080058410750103420303c915818200000c0c00d1410340d8020b502100d05a038a03050040c80b150b40d1010078171108a030360398a03180c101a96100d21031480011405014000c1126070004900e030025081c600440160341e601c1012591321044812000410707410560301140c90446002902d5a00c0c03003002d4607144107801d201c000005e407000c004210300d0525005442c40f2098580218441d5403200c00c241d08840c0380160f1640801c0740300000030551032140b0000d1042e006203107000c50400d80c1d2580031a051382c0091210100c400c030049414461942d00800a643c804100b038040e10f600c5030f002140d0310080c03420300036400c5a1110307440011007a0b1100248401c3c0540d00000003042f0103a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 392512293 1250 392511043 392511047
    0x1905060a06050c030c3a050909041e03021011040509150f030a080a02061333060311190e0a0207021f081e01060e01030906060321090902070b0c09030703050d 69
    0x11240d04403030020800c9024068000d404501c000320310780096290303249008035120270085038800c010000c40340c4e2405c02072801c42141241415600251003038004240078003510040b1825141003103000940d021041c0b04c1080141e50310802c191700b00080845103507840502c10042800c120301000700a030188a4040d01e2030410240100030300c50400300780e00741c40081e2100c031005640d050400700d0181529186405240120b2610000c482d0983c40f00e000c2454010480b19011050b151241d106588410b1000c41c0b1003618100202c0d13102d509081a00d8034000c19041c45007101208002030002c0a4940e4003203081760441d2144852039801c000243c0c5411150326000c01c1c004d0a58108440e020800e02c4a100c00b2002401500b0a15060301c11945581c10703004003d50044009061404003926441c1c2c48640c0040800d8100e50b000d10b0040d9040e62070419284480c2c070250614400754440d17281e45204001010216544018098100d5512800390380e4451805000901d0b0440035040600240545203036060126 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 392513543 1250 392512293 392512333
    0xc0e03030d201210050d0209040204240f030611030907060f020a021507050d111009210f0801230126091c03061d070207031401051905060a06050c030c 66
    0x1841c2c04c140c2130b1031a48074030600c1303040700d0300c1100250032040160116006240a402106031042894003030300d1803e140300c0070800140d08551098901c84d9150b01c041c01405824024002c041c0c0e12646000e245007004039155940c0d2049128180801c4002d4070441103a5109000d5100d40a400030030b01900602d1200040150340d020f40c004032064881d0301c2080010900540c072600c0090b90302e0028040e0282e00981d004060a00103000301c0c2c2e44440c80240c0f800c002654104003000e54030729a11440d50b0340020b44080c0840c40103810a002e02021100074207840c825619281003410f00030b1806031500d00311800a02110301070a07143d080d080c0c40329410056400310009130001042d1042d54405600702601c081681112918010808500c0340401801003400d4402480ca41008440c030440e06003039030f41c0d1944002000b048458107066510340041c005e2440100112608864803000100b040742040c2001403070302c6045214820031f00c1804240d20000410a0003910001e050f80e02c261a81013038002c042011007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 392514793 1250 392513543 392513551
    0x1c02011409150a02031801051015110619021c0b0321041401020a020a031b061419030e0a03020a021206040804090f02130314010c0e03030d2012 63
    0x188020300c0008151420000b000a070703034036442800758107588030120014080c0d40002e00843c078141c1200442c6c442e640c030900c1001c4c4602604803602950a0134500100304138108903043e04100254820f1742c00d58144007207a41504940c0130a026010491506458000b134058115140420450301c080005007031425003086801d00e8040702520408102c00c0700c6000145460991111400018002803114503411300c9075048200e0140100e038201c80079503001403002c180c42c4d081122100251459085000ea40c410b010300904814245885510074a0046090074040e104e90400c032400018802002503029a101030000e601c041c0c01c0d5a25845035040103544e540030002c0c01c9018a8001810001c0c40c8004150540907035400404280381c1071034030903400013500d20140304103040d583c00c0081442600414010304015403044e82e6a05103c2c2051000d2421502000d2108042c040b03c00103402d465a000f0045400388904010005000103106900d0191113428404410316010000340e020101d035056801c0c00c5c81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 392516043 1250 392514793 392514821
    0x10303031b0206151c0602160c05060306011e180b0901081006140d150e0109050f04020a050d05012003100b0c0307060203150307030303020c0f06040503090409051c0201 74
    0x11080080c0c10803651550100c03041c240540392001d4503075a900d40302c1521791031002422403044200c8220f80b98941281c0c03180c61815040344009008404100b2021410b81c01094100c070340c2d0342140b41c148000303402d1110018604c8000350b100342d8102d45e03040c0270300c80d082d00341c00480f60103490301900c03060400d031542d1210316128089000d90f000255007240107000801541e52036a142007107042e68101d000c0c03060f040000600c0d0840d4030b5410302d00490002d081960002d0040d50264251945000c00000854001a014015030a044000c110150322030b4007404084a409a480415040003400e015006142c150303d50904a500b9007010414481c1800c0134500640c1c0c0350501030307152644d0350000c0d009131080e0f600c0038940d60024456880801c1155020319448956401603040303041061001900b8254160412804031780c2c0420500f1080da0100603040c4010900c10003000b1508081d200c20341c0e0b901551040d0340c401d984a080c00c40400c50184030703012500003280519214481c9003000a03001c0d007160790b55030b41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 392517293 1250 392516043 392516081
    0x40b100806010302060f0307050712080f0708150f010216080c120d14070311030333010512180f061608010b0d0b060c0d050d0c0801150509030c0901030303 68
    0x1080803001c41d08604a030350080a05207410300030440d001041c4c000824040c14440207001c0d480114107840750345003903e0306607503402c0b040d45040f1140b2110443c0285c030a0301084100c40411170341d41640316403071045000440e07445444404600040f8034000107900007115a2100d084005008100007440168100f0110f407091565240c8801c19591a0307044294440003401e51840300541001603030040034254024903000301080c0c3c520405516560095445028410206c0541c1454923450541c0c80c2d81e809004a04082a0488000091082c0205070007000b030b041c0c1c050041418141d42801c8218102da007c4c00b95801ca400044007030b900c0f402c0c101d0b19401d207200c50410345040302c1c2c07252503450706aa0040440500341030318540b440c4003d0161f04086508064108192560321508200c00f040c544802e0340c0c0c2c15075407081000c294040e0741e140b8500c1001d10604000500c4103806c4c4004e2080d040442e4078041ea2621b2070040024613010803205450341040d600c500100505505d904054070301d0401c2d030902e003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 392518543 1250 392517293 392517299
    0xe0d0309020a0f081f0c0207030308040c03020604030b07090602011a27010b0a0f02010605090103230613110607050a0818061819080303061e060c15010905010f2c040b10 74
    0x17019180f005142d0300c0103812404040c00060300584225402c135004a0660001e10303102e80c0400c0f41c60380540c2041d11800803005c10040040e90007164100a0146407000b40150140b070780100d080082e034800c1092043d269440501c042010300e254065641c000306030407010319603450003a03407a182d000441c020000b0f0582d22000c42c25500501035602203034000342103d03200d40c1ca0368032151107100c90701071a218480c035550304020101c2c3d0f08010721405040070180d0b91b0011036040c80c280150010406e041d41c0251400d120800126002003280804143c1000d40c20369691101c800c00c0e04a0140c0d21380e03e55002101145102e0442841607000035400f005807100c0d1b81d100c2c12003a0b0103801c0c002c680720b200c0956200708001212800e05d401c12880908c04003c0103004541c07414000303100d5030040021002c481d4014100d84103880d60001e0700c6401445d002d0001c100380e50402c40783c0c6003202d51601401d52034648440300010226142107410503080b900020380c085900303042c9400c02039004107554241c08001c50440c08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 392519793 1250 392518543 392518603
    0xe1204050915100804140a03021f050c09040e0f0d12050c0306030703080c190f020114030907151403040b040c080d0e100905030a0506040507090e0d0309020a0f08 71
    0x41c0c4454000500c40005650f51000441e441e06004004a40d24a9190100d5031002c004001c2e22401078400e40180c0404a19145041800c46601034561009410700c000d1102c809611000c540002e1403e48000c2210000c0e80041441e04501100341691071040c501c10b81882a448407808600c1c003030341d46003480f070b545404c6203080b001c0c001031f21b0407581a04604010000125100018000c042da03880540e8103c410b03d510803040b060465900351500d8508407500c108541c0d0040d650003005c5520784951b811400c00c4100340d542d0302000d008201c58108154035017034605000e5040d100f01d007200d00c90015920710705454840c451030800c1e1000c48c0c070310540f91004038004c800454001d204481d030341d071a9500c44001504001b0081034030401881404023601c1c010501b5101440b24801d401e01903401450f00c3c0c1018034202d481c0066990001d0201484d0400c0c800c42003001060303a1044920521f0003081440181c00065070030241503210694020403450300280d004000300d02d40200390003940c1c09907000d502e030f071440c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 392521043 1250 392519793 392519821
    0x30513030e04050a06090204061d0105032815060519080c0a03180c03050a1101030c210b030f01090b060f09011208070b0a06050415150e01030e12040509 67
    0x180810781041e0611601c0c00c0035801103504c0884154081219640e425a81c030807a031187d0482d030005044181c10814401198105040c14482840c2a41c5103240407c56054101c1209200e0009207482c000300d45000c904a030402c4c0410142c14070a5004103071341c1c4a002d0419406171000d0b10144101c00700d0504c890b40201901449a0845503400b441c148623008100d005004a9403c0795042a00d80142c03070200d14164a6040603501c56002019500610309080f82403400d6004031904045c14140d0090146031700c014050301e24000801c040f01c56100c4903141c000504a0309281c079406110380804074400f5041504040c50080c004c0c1c11151042c0c41c0c00c024005a034145032407054000e1202d40040180c03501034031041c100503000300556428200c0a540c0e0300c00c0c40c2000d440a1802c0c40e250340c404d02c454502449940000681c4106000c401c51400c0710105890407030078003030380902c21040001c0c01035034002d0304103441c2d0a40034400e03607000400710180c04001e50002d000b014042c0240743c00103240e4410b5080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 392522293 1250 392521043 392521081
    0x20102160b09061605010504031710050f0d02131a0a21080c030706021612080708060f010e0a030602030103170301080309130204030206120f091501031b0f150305 71
    0x501c003032030005890148005a80248000b104040c0c1c0107180710003043d802c0c41801d0045100743c0c2c40d007459011459035940b85044c040c1640c0c540400c5040304006a40d42c81c0c03030805070304d40140c607100380b131070b4490000468480102c41c04440c0c2c6414000391407000c0e07800c091004264142141c3c06d141c190b4840c2245841c0381001f0a022000b4201c41c480d0002203030782072014001541e03c100c201ca15141c0282c0c1c812060343c1082030802c3c540f0031081d01705410400400101c03d42c5003110302e400c5207580340c00d0000412000d0043d00150044080c15994040350f407044500c000005000f86c01d5880096aa140800c003c0d4003d1205940004c00c001078440300d440d0540460381240c102e90020760030f181c510400c0100d1203540d00107015002d5820080000181c031070310068040880400a84041e81ca04409041c05007040203007640340a82001c0d00782c00320001603c6160741560b0700030281d08180c0c4000300d1a03004201540d0402c0050007401d8800103254144000914050942c1d03035418403058840180003400900601 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 392523543 1250 392522293 392522309
    0x1110a02090114030a120906020c0907080a0b0415030b0402040506030610062111090a0509070912050304090207211809050601120f02040f0f05060f0d0906140402010216 74
    0x40100640c00f68015001202c0a000702580c2c14003c0654402440401c0e052440001c2174501004000c03894042c40307038505060003071704c2858223441c0071030b4000c148910041c84250401d03a10081e140d45915280e00100d48038000e1080105000c0d12401d1010b0080c0044904070700c11030425000940300c1c10003080c40360040050b1007803110030030f08040f016620340c0c951004e4000342c4070858903012440100d41c00340702d04425902100d2a42e49103500240100c0c8205900303d00d0080d0f03400e9048c00000c50740156400200c807000901c810800c452441d00c0340c194800c50344490362481c00030030711101740461582da509140d203d03040d940390302001801c0282c0d06840b403554200c0041083d4042041030321400c1d0081584800e05140c8118840e0a0070240d40c00c5900c00e0392807640155001c10148a041d03002d07081000580600e910794443c030b91034030300060050f02c0750724202c0038150400300b11207842002c10303040441c45582c40384051080055024007100c00071401c940a90052042c6800014403d01d50220201038610036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 392524793 1250 392523543 392523559
    0x8010b0909120a0c051005010b0306040c02010e0c10050f03040c15030504020102060c0703020f25062a030c0c030b160f020c010f0c0218010e0601110303061512040b040201110a02 78
    0x401061300c00340f12004040e80c5500546011705160b03083c034450280a0f00400e55482e441c1e040a1091108451110700f400065a14108807220350040000e059034114030210b03800c42045005031b00c12149402016041070f100707400071080c0700c1004600342000d8260f6641301c031090031490102008400f80d4000351b501070f01580061010440340c03e200401803d01078042e004039503c114000081c01d03e492455241040d40f02d414070a10140c281c85d91140c0402000d4901e0140b1824150110160498200c11100841e100134203005c8000c16002d07401074480d0a81101c0841c0c062981d074102142104011640030301780d058601c45140882e0700540a82d4011422a8028041121200010354900042c5150a428803003a404010010b035280c0451001307041842804100300e51401500080501001e4403450600c840c1e209d2070403003010b0020640f6800001280c408200c90414040204c080c070030400c0d0218080041c40030001400052960f6a003d42e200380d071402032003020601865115001454002d6101d075074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 392526043 1250 392524793 392524807
    0x7170c0d09020d0812060f0d2319050102071e0305120411040e1b01050a021510030c080114010e060303070201030504050c0307060801031b0b0f070303060f08010b090912 74
    0x181d80710407421840034003000815851a21040c906800809005122032072110801505080808501810a5060721180000e00042c1d40d4200110502e41031708400145070080c8545c0032074100038201c1203010480000c8228042824124040e52007403900381c420031000e080c0c001121a034845540919030300755481324100300c0c2c0a0448140703034001a106489541603100f40001688c0d407031140c0130b040712000d0002d00c0401d82c00042525a65441e00849044c0f02c1c0501403060301c290041210203081c0102a490005682c0d0b0402c4456a05035030741014140104190340803403c042c055000c0c20150302e03042004000c581e40d07040602d10709a030440c0d0041d0950024020b8034015402504581c3d0002e1207241510b1500c80d080010a184c40c0c616031006000a0749500108188645040c0384000170000780c84010103d820010603075070a2140b40190b00040000041c8501450711a502140290654020700034125650b8043d0030302920f80114014400c0c090304d40490000c070800501c0300c4000b02150f50441c14604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 392527293 1250 392526043 392526067
    0xc18030f030e0907030b030105130506070c1b030311010b300c060d15060206040209062b15060b070512090a0e010806071b050c090a022107170c 63
    0x10044011400d0010000da0400183c0d103182c000c03482403070070756800079504080d0004c2500f07464014217426010049080d4a401050002c41d1700e80c0d00071390350309010003072900078a0b00510f00d504410300c8049480e44041c3c04000c255210000c03544510f085802403281145000030400442a16118080b861081d10800552401030020700c400c1607824400785c0c2e080029003008603941d0351207100d2200310941c1d01c5040300c3c02c0340e1010728401c000d810bc40c801081c840c54941d0100e003000c040074002c0da2282c0144a8910344042e940c0c0d642c00781c1031080a4024040e2221403a0402a030340c440360b02c4207005030800e1004a41c2c07203103103825560001e4210004103540d007000e0550301181e90007413506035003240c50074001051500820745084d00900c065002082c5901e0044002401c4008c074500c81c001e400100c61220011a0000540015001d0121520101501c40b1600c4070002d100f85801d400400c20f40f1380e14003020444a40705148280800d449006a03900f03142e243e40321100342281c018404441c14031602048007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 392528543 1250 392527293 392527313
    0x12040603020d1a0f04110c061006142104020d0f0302010e0d140d150317030103020321091228050607050c1c091d100819080f0706110d0c1803 62
    0x48400785110311f40304004042d036040000803104040c84031903074442080156802000380913030b124404645420103e40c814041d07d200741804900d400f51804602060a654540410b110b1041d8010041811280a4074001e1702a001d616090036143c015841804281401208812080103c0720105880d120180003510b0081035070806c00031030303095903140100c0060700c00b0070700c02458050010850340740d40c554410585801c042c8440d188181d0070181e00450400042015550105021a44607502100c206101883c00404110401031010000281600c2c002c01000c00c200d400c0c013480a8030380640d1000801c1d6610b2041c4850041b0507405411960098001c0184801903803890b071401c101440e558441038031203500214501c211181400b002e0044a82c48441c00d04020f08030000a072001c010130341c81070b0300c121405900181a10f40300150030a010140c050407070700203942c0040708000c140050404000b00d0b803c1440c1113080103240040e210520b0780241075010405101c845184034041c115515003481c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 392529793 1250 392528543 392528561
    0x20a05030615060d0e0d121109010e040b13020d0207060609090308070f170406020406080912040501030b060403120509100207121401150e0709090e03030606030912040603020d1a0f04 80
    0x100d03658120b201c95504280540c2d100781e1816514401c00187c22100c00c0300300d40c0014610f41d50b060041180d0226a40c10017025544c55030120740000314141c403880854001e150b00d001d2801403500c00591700c0714111050b4098808107010744401c1080c41c2e15044510102c0e070130710310050b010036840c1000502d854818030014076400d0342454030b48400259030850001213002039808075129500407505020320351b40403e082d9407081030403000741a40c03200d0030100406403013903001d2281090703111102d141d019120311044400440c2d0005a9803101e50410300010865081080402d1280440c4d5103a545c071984001080320990749001c002d0203c1b99043c1d6206406c80f50314401180700d035501c031140140c0d5602e98400078001410580c1c1c44401900d01100010212440d5800540c0042e02d01062110700d40e0740041a07942c44881540d546640c0d440c0c031040c00e450706484042c100b00d81d40d0000380210b41194107402a056580c1c0c1e090043c84003070314145148820505039100b080e04010841e04504c680d01e07054110340c0b04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 392531043 1250 392529793 392529817
    0xb0112031103160b06100f030b0103060b0c03030601020105010614030c0315040510081c050301090b191503050606210a060f03111008010501301404020a0503061506 72
    0x100701d080d0000c081c159041190b200504900c10380c00b6505001e00310303000c01e5000108036142c2d50444020b02c40a012441700101006c205076a40d16a090282d000740d2042d4050881d4005a980b542c500c64691a569481100d0540c01075003001c1c000500c250140c1c00380325903409401d4002d0f080da0380c0c2070308801c6550401401c07220080d00c41038400025813900c0c4101c500a60103242c40300b25090070000094a0003251180105404200180328000c0c194003105403419183d64041c00f08191011000103129070480c1e17180182072500c0c80a00250070300405da4040500c90880d1014406540e800c407c03c00d1600904100d00407211a410200c04211250040c86900010313126000814940301c468071800e5960b250030840f5400483d08050308075180070003000c0c009600c149010385541d818800020140000d85c141d0410603203441d1000110310140f049040044420404200982000440c1d9089070301410380d000d80c003907511080b011596040201e46503124503800741c856140c4c02d4100080c00f820364848265120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 392532293 1250 392531043 392531057
    0x11b17070c0e0f010e0720070b041514120f040c1539080a112a041103011e032003060f010305120f0c0109060c11010203040b011203 58
    0x80c44019450000d0142c4401d400b40c1c1e483e00400111035544181c210342c908203415010000d909511001d250000c0841c2c44110032148111103910b4030701030480c1c0241080300c0c000320380400d410680b203000c240f2401d2140e0361900e4446200011648911a110790054886080c100103801082d10310b03070780e0350041d21030902204c550707940300860300c0e81c1010f0038213900028000c1c0a82103c224900c075914404400c0e401d1000c541070b5070644240320030310003100c0000e005020218082c0b4800307014600504c0d80b24622420b0300e40390180ca031821404804a691510140c1d0540c403a1000541081c0c0300f1070010b240c811a040345140d007400514400c29075100101c04039003001180210000d08620403414011003145074134110341c80e22808150810800921440a0b052440c0041010078400111805110300d40d10005a640c1c03603105104c1c081d4400e81c00342c001a98245240c00e003c121040e40540c0301250180d4400c418041923030304141c280c0c801940c4c094a00b100c2c01c001842205501d40301c101000e886824a11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 392533543 1250 392532293 392532307
    0xe06060c0d050a1d130917030a06062c01030e01020d020c0102040321080403031104030618120314011404021306120b040b0102030d1d070f0311011b17 66
    0x340c5406601002600018008610702c00d80c160014825156840700c0741042c8541e4228002144043c210303952034290041d204c0649100744812500c40142440700080405e80d68502010348102800d020720664000440070711164100c1101500800b02c03900460b03401c0304940c1c40394001100600b41c1d00c0b12482e0103560030419203e003207110b40b0003060110400c90025890b58034508100d030b0005098443d510341c0d4005850680ca10603070200e10158480e9142c1070000b403001105030b0300a03240c091608002e107024070b01200b801c021220030b807200d60030750b22031102c0b40720070b20403880101d00b03440f10f011a5100304030401c0c005001d08880070021119000c0040c0005042800c010780801000c05998882c4001c00c0741c1034000c450541550181c5a80040107803024170000b010f200001799244216040c40030f125a86040c9030142e045c00318550f03004041081300321841036484109284400003c1d1200701e50800a803080d81c042540100030310958030241a00512810100d07441d004c00b10071310010241c10030340c1c04101c84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 392534793 1250 392533543 392533567
    0x31b0d11061c1b0c211404081e0c010c020f18130309050a26151503071a0a05070501060b030406091509021c020301060803070305130e010f0e0606 64
    0x2c10301808010021442ca4141801500c034164641641400c1060075840d020120316200302150030706290200301d00391301c0c00c007420403100c201110010040d011800180010710700d10014045d8035600542282c84c481c0ea250300c0096076a484d0840c9aa40440d8060740801d0140c070309241c3c09904940094082c03506281249500c8403580c4c0c0c2141c01040315251455290709159000c0d00110241c035007030754203100050400846400d024002a03a954080310048a880340c040b4040c003541c0881020404900058104031443d0301d03501c8012030300e0030301a1040c1b500000b80008400f07000c4441a610500c0c440c81d085420a0448540d070110300103032150b640350080019105000c5009500c501d00404000808400301c1c07824444410580707058007a034908100800300941e64803401031190a000b41d03405800142300c2d102090160032181c0c040a82c9000c003080da403003455000f8004225804910240c0d01605444420340044000700303005103002c0b1200e140003440000c000200f0190031090003000d09040811741805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 392536043 1250 392534793 392534827
    0x51c050c10060f06090803040b03090c09040302010519090b040206071a0903030a050718170c040f020c010605100c020f040902030a030306090b040e19030e0a14031b0d1106 75
    0x72000000e5940380d003000082208150f05025000900d010905107103885030f144e0b0ba86c041c074060402540341c0080444c0c1818002c00402603610800f408074440e41c509410301038000c0000300c071002c4c041070f1800d05050b4200181d22600c40300640c010400300058aa0ba000c0c8100c6800c03560044540043d8098821541c06d400f1442520a80100c00155541c1c40e0960f0420142c80000d0181c1080c815200c04101904201e01300c02c406071100c0300102445a80d00804c0f07d4541140c040c0c840390030624201d221210089035030028200c202d8070800a1008540c2c032010f2010541803040c0d803078006541e0700c08080c010324141200343e1500100030b1001c504d80c1410340000b802c1c910007200481c08699540410040d0400300e0054844550085808004199a515035640c944400b0a40c0402542c0d21075540c80415000c2c60440043c2c410150524101c25180c0e030a03040f0041011800920a00c04c0340e5040310012001805a0180c03030001d004072801d4160350f074549540f44c20500d056607000301c09200d100d031107801c9501c0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 392537293 1250 392536043 392536063
    0x9020a1809090215040311091906060503041407030210110109020a0914091c0c14030a050403050705090c0f0306031e1005090f0a0b09010906060608040302010513051c050c 75
    0x10001d000002d520400420f070446040d200c4c8001c10a00007040456010784801600c5142604d002010741d55038842c450031160040102d680c80d52400c080440c90550002c041c511982c0b05d9a96000c4507003604030f54a99030400761100a600c15808900c00c1a9a40700b22a084d910903102c3c0d00125071501e003940015261042070300f00745600355403086c1060404140003c601d81060034003000d07007258044044503017001007e4190380d00900018a03094010090101c41c1c8a203040000016241c075a40c101c500104180d0182c482960340e44148040410700d481c201d507046010350741412109280401c880302c2c12600381c20050056501d4014400c644620f408100030148031407410902403e203401e90300c0c19120407140040c2104400d58051395019449050009006109582204445031199a01c2d12000d0141080100041c1040d08104000600941102803240103d2080d0001d00c02684c4044e001e0881c4840b40340c01504a038090310480111126000741444468500d181c0300b49000900d034411807802e012a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 392538543 1250 392537293 392537309
    0x70201090332180928090302060a11090301051302011419030b06091003020d140606070209041e050303010612020924070c080a0201170c0a1b0209071206060c050709020a18 75
    0x45d46501340c0212070003061605111800c100041c11aa407402540e4030b5000301260310450b95094050103250242c0d080c0d8102c044018003d009030b1600340810012840c0c40403080f80031642480880580d0706401c4140c4a80c0442129807107038248803583c0c11400b810a2181c0c00b07400040420400359180c45040159038400229100566210480c0080100701c0f40c080640000c00442401804180d60311801103030f12a40c2c049030404055122810250725204103c86c51804086417100c200b4104003002c0b014604a681a0311491241903115845c0402d0748100550315034030412400c1c080b1030098040b0980c004202016030f840c3d04040480d038076204508180c0d009405aa030108410b5003c541e400701d0380c129503000e000b07003101c4181400c10389100c0501441c99148140316a510f0403110702548084007031580e5400400031905400c01034000b80000b25000d0001e030b111400c014005c10094091003140c50346590007001801030600d40b03030007540207422480d0301004001400e410840c000d5400070300c280286c01d1074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392539793 1250 392538543 392538571
    0x90106050a1409010b0306060408030a08100f060c06091e0302070e01050a0e180a06051807060203040f2105011e050f0105150a0e04050702010903321809 67
    0x40c04001100794240c0c4100b419504540c1d940400741c9811581c0c038112560400c006441b604c40030005040d40c02150011007062002007034100032941d0000a542c010703a4210240706400b43c640301408841070850054201003900281500700040702d42e404840480e00512410f00004401c85180e03c1600c20b6141c20740c010ba01104050001c0d142001d03c46005000c2180c020941c00d00c2c0c490080740401c0c004042ca240302c0c0c10021011011a001c0c0050354165a1040007017140d443d18243c4109031100c802140ba01c54800c0303240100700540008112004c0c3c607884030300481c0c0c5500c0c10050843c09401d0041441403141c240761500d0000b1024091280001c1d40046111201d449042d590380480b803004011580a5440400400942d02d40c00c00c000e042e08003201010b07503916202c240c1690100d03107000c1007d8005290004110031030b039040d405600090b20a0342d40094110203090100d0001101803510130a1203c2800c9840200c54a50000c00200c102644840c80b145505c0c000114070020484801081c0609 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392541043 1250 392539793 392539799
    0x90414011401021c1b0c0302060a050418050106051c06050a080f1504031d030309090405010f2405210a05071406120103060b13050c09010f0f0c02130f05090106 70
    0x1031240442d0005440e000380c07003032280c0704001424400c0c03003c5000340c500b9405081701c081c058190300c2c0501540e0040d25140d5141c200380f070010400d80c02407284000a0318403450780c8021980c80c0c02258121901665401c0c00d041303407900700320958180a0461030480380e44481c0040c03951500c90f0254002c000c02000340c2000036054070707104d0901009000e0300482422000410000a070421442440e020086100d12012804080440e2561003003d00003a4820001c008010800c001500718606140c00400144141035103403c011081d070781e800b02c00004500c0c621034240710500f0b01c8109440203000700404180300c00424540c8900744988804103070740c41e0300815400d0000030582558901001f06c20b80c0c5052420010701d0b041380e601c80060000070005901e60704100301940c3c5502085148540403003041046041284039040d0f2035000e4041140845c21003a24060300c64003c3c941c02e0240c211079140e0800707110b0b00c0e07403c0041801d08211031414541d030340ea880f03404e0300b9114800c55109a440c08000152942 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392542293 1250 392541043 392541047
    0x105090c030a0c09020304140f1b030a020913060605190f120201020a20031615030b03030307030509010908030703201318060302090705070b0108060615090414011401 73
    0x800811101d000707038403280048001551403401c0300101c50710000016247e845518081819002030852202c403880b4030024007481c076002080b81c002212910600480500da00001c1c16140e4240c2680a58880105c2d00012540038120444084440c0320354000281144c80d100000d015101c01d400c0c80303a444082050511000101e001444040d0540000545032001c499000070340d15025050010805070b80c6900d02d100305940c0081450110714001e05940455001c0b4004028624052040c00080e40194003500310b11400707403081c400451400341c042d516683d41c0301000c0d0050440a40400c000707658952031900860304200156005400c6a580401c0d164030850f01001c104100c05410350a8010802c00c6006820a0856040c100c6100f5080146540c00120025009004070703440a034214050070104000305a00c50010410248180703400d0f901d60340c03603607a2551303280000c5170816004054200b1941446408501a15a844005201140c80c9165440031040c004003a0700c94604207040c544030004560b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392543543 1250 392542293 392542303
    0x50c07110109030209130c03080d020d05181c020304030b0a0903230a030e2419060b0426010615020d0201090f0b040212070b1e0c1f02040f0305010509 66
    0x4424070b02503114906640004404280107810003114200c0c0000d041c080009804d1000011500940900e03185c000d1200c080c13000c0c2d4005409110720b1403600c4001017058180030642c1b00c04036401001007503101c00404041d04c401614041b044250b1005200020008040c038040500c01c0610320341c0494142c5083c82c0180c5204e00300307a1001400119170600c2102d80c40d469081e40d58040162502188246501041a08240310a94000c4116807500c1c2c107884030742c51320003441d4003c40c1c0705081c8a00c1d001400040304101c80d075501480d00d0400c410082040505032241011500090038405034140da180325025908440c1c9035448000403510000c81e1400c100d805011600450000380001e20100d00d0b10b9803004401b03550790900a04540d0200c01180554540d401402d4103858190100c400d0951150400420354110580c00c460000818400c04848480c01058aa00c6016031005001032322010301c10703600e10800d0341107038030129500340400100c0c850b0a40394880114020400001c09040c2608528100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392544793 1250 392543543 392543573
    0xf01020a15092a1505030f150d021c0515040c15050f180102061503030d021b0601090e1911010804030201020903030f1c05010509040303020901021912080109060803041202060409050c07 81
    0x205c14280104000c3d0b04c3c1513040c0035032095218000b941922266400289001d25805010707401c04070f201030120007a4a80070b000980385000384100d03494100045c0350030040340c07030444009040c842c4040040041c208444c030201811451418654141158604020502e0304400c40d0342074109a5160706114550b01030011503080b4450440420307240c404040460356030b1007483c622840050b400200007940d031036003c05c43c000141c124020348080b9651040320801130041091158914020450204031044482e9401d6540d568003408010030a101800155406500200b003030b400c1d0354080000d130049a4041c03006240d00c482c851071a40d00c80d185000945c10309455000c00d2800e5502e041c00501450b9181c422032355105a0501c0d0140e0388040d00380040b0b0034403100b10180c084039012051580b081000d181c3e000410b0b02080d940d401400d07030380c038040f41c0140c0303a007485807002640041000344014510301c1e5011941c42e0000d01030074a096980d403511021128101c4d070700c081034140854502c040200100751003000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392546043 1250 392544793 392544797
    0x27010510080d05041a0433050a080a0504151508010f0c0c0210030b090406050a0507020604021012140106030221090721120203090f01020a15092a15 65
    0x507a039410b107002c1c0440c41107019200180d51001146003181c2d01c1002103402800040c03540300d43c5a101c8030503600e0119554000440c8885103600030840981c812400d5511014a59803014010b46861060f0320041c1405001a01c40c80b031518503000c4000b0031405105440c002c00b404210702249800121803c4079001c000800081c0d0420200d04002c1c0e521845002d40346804440400c0f00040081050700200041d1404d142c004c500441080140003140e48031500c580c00c0400c042c056961001401c0ba20350004030790081d44640e202d90b2401101e442290715035030f1510702c98000180c00c1c0050403507401c516070076072040000a800190341c8620452040d40c4107a0070800c0c400442560800c1402c55480c0da40320301445910704440d40d9140102104209004002c50300182d00a16400b62854029102d51081c041c3e20300804c1000b600034110352001034680f840c1c2c0d030004020303209038050700030300d902034010903400343c42080c0e0120900e148a2826051451141600c401c403080143c40d001700004151580c680c5081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392547293 1250 392546043 392546053
    0x4061107080601140604240807111b030c0a0f0f1e15050d0e010603021c0209151f0e150906090f03011e02120a020702182701051008 58
    0x4100d070400900325042d03d400b900c5075070401d0300b0071010840a0155038813441805003281041c0c0100390300c2c101c9042d280c80f2281e0381c1a146c3d641d0001c0c203803600c200050062190340d20000c0c01c100c1882c91010b000d10000e800900b5509001d038070303100188045205400845007050325a074100540c90489141000401c007001c40042c1016101080078011041403051400d400d103404101c000d0f40740308401301c4c2c43d02220200c04005000d20141024028010f07030008030301840b0b1038410f01c2190945103450700d0407241e000300821903558807180c40da0b162045106020350014101603046001c001884001d0450302900d507145040403076104c3c1006a113041c00950081110000c02591800e9103840086482504066400c1e50080d510000030034018100001c1440303881102010081804404e40c000741002c40300d20115034070136100c0c0c0507840220700c2040d00096001003049410504c07016403801680d400080603610a0541b0300d1010b2042c0c41d90200850b402e001d940d540300300801d01944c51600b00240005d000281 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392548543 1250 392547293 392547299
    0x90a0e091b0607020904210e1c0c0e040506240117040c03080a03150801061202010c06180b070f08091e010f11130e07050301090903020a05010c0504061107 68
    0x10380740e103070880720801011108040a600d50310350034100c038042030340506605001d01e4a800c2403084a00c01c0c3d4007134080c68254600d401d4119104203090b07000070308010300700e00c50140c10326103902400c50f482600325240b0302001c400140010301551b03814460383c041e0001e80000c0c50000d81d5602c80102800030074465095501802e04c059030f00038081e41071840100d54082580d121402c200c80b000440c3e620084c011200050041c01d0b29516820884801000d56140c2c0744158417090f01c6400c1c4c84403801600803104850060501543c451268100054004d240009054a50302e00418100d0f045120980c3c003d4084000c0c070064503072041080b030302c04040740703407000960901a03415502ca4032910303801030741c0c1d5040c0458946400390070b501c26111005076480070002802c2c3c6010b604441e800107403460ba520900268000307085c07001d003900117200e41440c0c0c0c0c03aa4a903030700f460039403002400e04d60019000c5108804020000400900c074011a041187c4c607110b03102c601e00b004c0101003469100e482e03e601c2c1c2002c1820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392549793 1250 392548543 392548561
    0x2a08030d1b1b1103010f1d120f1e0d0f02031902120105010513051e01090f08030f1602060310030b070c0503030a0e0c0901230109060c020906130f02090a0e 68
    0x102c40b569030064036a280624402d0000e409444400880d80590340307444264400400f200f14a000039814084c280c0e0326504080e211403030580100c48450f40c0300c4608000584410000402000c042c07a50740d0092030407c4900c00252040398a4010390141c1c082c1e000003401241022507202061503c183c04003546020328142000ea0500070600c2502d0600102242000f42c552030400d1b0003000d040090074404601d00561840901504240c20060200d1522200420700503501801241690800d0004510349015003404807020350000d0f902c25441d0810700c0301d1a0040c1d44440c02103005602c4c162812100701d0039424048510308004d030101c1d0900081c82000300025902100f6254003d150800000b190143c3c03816850422510140311a40b1081c01350000c103000540d03425520503694201e101805c061034940041d02d2561040c0038800c04a50058070303800052a0007050554440b001404821642e81510305c003400740c5105100064100d078001c19030a82908040407400000d00c802c034007d103e541050040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392551043 1250 392549793 392549837
    0x1704060201051518150d0c0512030c0601030f151803020c030d020c010503040204020f0a050d060807060c0b0703150803220b030f090a0b07030b19032a08030d1b 70
    0x1124000c460006042ca040001d41700040301c0004c0c0c4240c0e50720003203260150b004411801814818200344060b000c4e14000041501d4047c1d541c00000c020a034219201c0c0110700d407254404460038071306014919210300e098050ba0f41603108284244040c1c100d54035000c0e04119040b11068000c1e0300103980ea9500359070020740c4004020080c24100d90366200d5001040103445101d8000e100e40400148000407198094000c04001e205948104109900c4064041e112441c2c0d108990010b4a0ba03910000820044a010b540190380c9080006a40c07800602c0034814884903403060101e0740001c02e5101c1d50070091610010002420714504240300d04051009405000c060b000034880300c21803001400108041200d0352801c0d4011500810303910342140020003030302440c040741d03004080240b07100d000101e00a00c50700c29240d022009003a00388040100c0d0900034107040c582e607030800c1140c0c40041d2998040c0020440284400004613402415040907a00720351180c8074507080159120303100408826061b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392552293 1250 392551043 392551069
    0xf061005010e010903020301090c030b0c0f0403030f11010608030d060602010203060a174801020606060904111314090702030409020a0e04140108070602030703020a110102030717040602010515 84
    0x8001242c21410707801220104210b0700000d41561805409900340300c1002d081d01d080701e200e00b00d031100942c1d6265410007113010340c0264030f0b00f0440034002403000074000c01c00b00e0032620300c6282c81c0450b034508030107203403e5543c650700c13484484d080001c41712000040d1340540000307000c2e42c0c0000d42c07a509203580400c01c586d40c14030400e03400c0160012100644002804001c80410241c03501e81c601070150304603820fa0131200051507214078980d8074100fa64490301016400710385016000b074900c6645100901105502c41402e580d0700c43c0d50795000e52043c8459030050007800344030020011000d070030080d50948482c0d007084010f00c1b9040c1e290800580e542d0020454050700c0038510050b0300d5100900d4265a1444c07581b030300a0f4400c0c1459404070310b00030111b400724102c6040307200f20740d00256a2a420783c2c9a108202d000740041e0041c240b00000300304107080b001c0c140c08040c411a8034107481c0d900d950000400340744186142180024080280036824000c035904080c964900441d0100b0302e00006500041c80701c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392553543 1250 392552293 392552297
    0xf100e1302070803072c01171503070305030d05060a0305030d02390d080c1b10020a02030c060c1204030f09170c090109050c040302130902040c09080f06100501 70
    0xc2404140d5009070159051076511000d00c0da03e90030f000d000071701034801c0c40307902c40c051003820001148500141148101e1407101a103030400e4030754151440d90010000200700c00040780c11813140a505840c100000310041d8010400345440d4607803030700d1002c00d81e00060040c07442140040e5041c008240084112101c01480100041e543d02d448000d000e5003d002c0141c003241283d2041da0440840d030101c4400725070040010640f41c091045a60907182083c060300d101c0e0302c07a075003407011180c050b54200c0c1402e01d50221400f05d640b09040000749000ba40d00141d102001a0008903420b40b040000304034494021050300191810200c030a960305081d04c00050001e402c110400160505543c0900a0400a00048132250344e0307182c080d1f880b0a9031260b00200307450041000e0400000c0300d49031031007614000c85002c030010385000d1654080048002c43c5403198061940d40e180c1080040c2d44501c00d802004490b80c0740c8031600d42c6460419418000303403d6010701e80383c01500410014002d26070082d02038440074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392554793 1250 392553543 392553559
    0x1204031109043201050712050912040504111c0905120708070f0f0f060501060e041a012703061a010203070c03290c041e06020d0c061b0306050f100e 65
    0x466968540b412904406006519045c01c0c0024142e2100d15401d03002c41c403e03014020350b1101c007421503031110018500c101403141480240010f02d0560031011001162403170032401c0401007004c0c4000d600720150b04000c020360f01c0e0789180401100340508408001800c0706142020541d0311400c98034400da107001032a40e5655040102041880c1440014a0744c0111900054040600d40400148401c2c0207880214525003400d09040c50180614007001d40b407801201148117603c40103444905550b00c004542d1403005502d2000c140b80b0b1418240150700518011428440d106096216250030344e901504541080007182d0109100541c070071304136070303014091440200204030310b692000240c48a00440e090b00109000302c440302c04001c1c00c269a07024221001d590090218284000c6940c81200096081680802d9002d03029901a02035140100c00128241420242040c01d0b084980100000310740e450100780300f581441004080c80d0303441507407803400c1e0300701c0c01a018001400c0782c91050b12079010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392556043 1250 392554793 392554853
    0x90c1103030a021605150405100606020703020d06180302030702040b0a0b091003020f18100f1202030606070c060216061d091503031b0f1609050711120403110904 71
    0x3240010704c1e00360000d00b55801c44160105c07008803030000356030039101e6201c5c00c115400314001a10170341e0200c4003a50010240c05145900380414210b4107001901d41540d100f203800c6001903619481080148280d02659a070f44641c810031040307589241c41240103000c8200103100d0f508904007260040750742169081c0416010000890107841000c03074003884100c2c0403447c648529a901000110210215026980d40c240e0400803190324282d490207900141ca001d003050036036241980195002480034020610b00115900c50707140704229580308200680c032801c10030740d82e408022510720283c2841d10303203801a6070145000840c051034100c4038500c1004081c01203001d000949041c1410513202800342c9072640c80e4003010342c030341d1184500d6500590003007440351200d5140200e802d44120944da90700f1445181000580c00061000130700c8032040c030401c0840340420550401400c03116988a0702c115546500f10701c1c00c503c45080091030740d80510100014403001944000003403800c000f0940d003041c04441c0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392557293 1250 392556043 392556067
    0xb04090b13060f15031127150d05060402030402060702060a0201090b07051c050105030d050904060e0406090b1b16020607060504140f0705061e0d09030807030b061207080711010510090c1103030a02 86
    0x12000d28207650081c1c04e20706161b00c8c06445005444040522041046182da0b00000c0c0800da01c011100254010740802c07030240140b0300040500100545880006611007182d90f407031b500300100f0360399480030960210300c0c0744200d030804031415440c034a04a000d0126500d4040801e61b144d03444040c1405204000c0ba1190164580764458802449a140362842c40d04184c10328800404101500b03984040f4120000f5410003400c2420041110645481910f465000601500303000d86148080343e100038104600404a48103000701405240111140d0440041c172494241c64040d5890100200360030261040015540e1281a41d1004985a03c14040d940300250000001e205041044501c0d03850800c0321024554414047c0c1e00c05d03e000d4600300300100f400740070172510b40100001210208034020004480c94810040146c200c7e11500b003200710070b404891503600759002101d5a0f603031305407080010032410020f4002d01e040301c002410072455041c4450b034529107130b10000741110612a00041c0810300342e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392558543 1250 392557293 392557357
    0x402040b1c0b150a090603021203180405060111031206010305011401080f0a0e0d08040201121109151603080402090c030705040e1005041a01180b04090b13060f150311 73
    0x82401800c0a1301135480c0c40e95200104603500060340642420100b0380b800704000400c607200740d400c26060110140f003c0f8100000740100414050401087c44c15a00441034100003800c0b001e40300d86801c6407036181142c0010204c6005070300010040030400000002642c00c0b91a00380c000a40e02c5a10500d0350f2401070b107502034109124106100e20070f0700c018034225644040c009010354400d980c2c114001e40c0d41001001640c42c0b01140c2c241d80841001040b010740781c50040b0b04d5105e10803140c20b03070034180031126002040800e160709a022515403c10001145008690640d101050010090071130500392001400d034041e60003004282a8100007003021a8554442c2c100100001041031000c06048801030342c03a403540c2c071409800304440780c140c0341074200f41c500074900303039070541e003145040c1840c102c51040a40b0410400c00c0c1c003c00c42c0514600700e80c4950207003401a003840745400f10201c0c40c1c17914102c0d5500046814000301840e04004000c01c60003402215001c1804641440343c070030387c0c0c003900101d070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392559793 1250 392558543 392558581
    0xa17040501060b0f04030611130b07150501080f010509030313140a060c0504050906040905061303050f0706090506070503240612070f02010605040e210f030c030402040b1c0b 76
    0x1801d0013107032400d1403896441c01041500c2c0b0610342409106d09009840e2114003030322003c8480b04c00042010b0003442d0001001e81200e6028110b00c6220400f500000b42c202c46007030700701010300d8000020703902035103800340900f42d00001d803007000310315603d03090405150813803805000400003140759001d800248030401144100c50303080710b810415502040341c003800a912604c5603d00480c404070001d0540c0c50107106440460703400c00c0c06420140c2d02c40300310104489440000301c1c00d0060038024404000d01020140141c01c0c86480300142d0904181070243c50002d009089408120007041003244404444011900c03100781200c0c00381d903000c26403000030201d010300400b851001590350104881c1503440000d100940c0b0b06600204030345a00c0304c0502080c0c828000d00c100791035012101507014000060340d5003c80101c0760043d24288100307600c5a01d81540141c400d901300a001209000540c03034148540d007a60003040b40c0480e45000c5a8000c040359494140d0045c0075a11048002a4000350305c601c41065 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392561043 1250 392559793 392559809
    0x130312110105160801050d0b0c0904110c01150b0301080a080702040908030a1d01020403050304150c0b09010522030e040903050c12030a450602040b030a0b0103020a1704050106 77
    0x19526050101c1c450f8861140c1d000000503883c6000021700e4141042c04500082d0407880710440c2e5034440d1000511603006200c603a0300541e0b40d40d03101002d4050240600f4036900800b00208412002c0c40001005002c260010712140204000401042e200007404009031588460443d89441c00d13400014010181d01c800074041700c0300003080020656a950041c440c0304229941c06070403031202c0032058200d014a000003042980108418003a280c1d2070400f00011b92990324040700385005955813100b00300000c2d2600c4005a444800788010381d0101441d41c0c4441300c2c0480140182042524010410100e101c000344c05180d0300d84a181c2418440e008450418049804036640000d0011950b09181d104607510034003980b4113400d4451450030469400d61035408481c1291214503814034482e41c0030b8001082081c0700307071a02803150014403240007810013080e424005540320701d00202d4850950f403000c0344260401d4030400000d41c080313400100d80315401508070b11b020259915894824010034090f040050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392562293 1250 392561043 392561051
    0x7060e0c0d110109090c050d0504150606081602190308150a060c15060f170f1006080d090b0406110307060501080109020111011802090c0909070915051303121101 71
    0x424886500190701c0e0010382a42c481130090740d070b15480000c9801a80503040003d00c10040e01801010381d810081e0028056140340014050b861007103000c03514a50b100c1d10100f4004802c0054110644644002d108505e00181a2f01c0c5050310340421428030200000f8240404800400c0060144005000e0f8447d4080c21070000151500d602a00399115010308486168841804980101182c05010110b5500100d2540c109082c40280034060744640c080c800c6600c45d41c440e801c01204100701403c119001020006401e504004a10742841c6110041009204d015401001b1150f150011101141d04601d8a0820328034024189030031485078102c0034148604000020506100650002400e54400d032a400a00c1e0400c04c0c245082e5a0003400fa1020300601f60003200160401c9090642d00040100405207048000c00c00030300030650998011002170b000709002e00c101e441660035040042e5282c20306030b04112a4040d000c5001c4100c1c00005d00c0e4221043c4201a041e0103590300700041280b020080c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392563543 1250 392562293 392562319
    0x6120203220302030d0b0414041e05070e0609132303070203070f0603061203050d0b0a080a050d180b030103150605061b010b1507030810120302060f1b07060e0c 70
    0x29602e410030317070b40603405500d054011509407030301d8402d8141040c3c4030340701c10441c0e0b56191a0413040a00f90b4070441480e030b0750001e428001440c140301c4100030708084000c001460401906011f00c520f0000e104078107028940c88040003140070010098070b460140545014041d10324170f08ad9003180111840250944980c003001b04085046000001c1564030030750303041001d40c4e40c400400003888420100a80810010445000c66202c0350b0003450300440080e14885a02e96501029454168095010f50312a0171261400f4003182d0b2100955030b0081c0e44602580b90f00c0c0c106001c0c242d0620061000806004000c04034140902040c5c00a41c02404c00411103502c070b00108200c8602001080031050040d440c0110040e0180f80030008054242ea00070002820310b0103d5a0540c2d0300e80e800380000000e5602c01c0c81c0050b08521400f0307800e042c144a64007902d81820410301405c0d040310082d101076120035544284402c41c14545094501080d00480080340641c1010078080c14542d41d0314107903400c500911460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392564793 1250 392563543 392563547
    0x2120c0d05010b041b1e05191707020105150f0a031421040609090e01110c010221040807120909060303050c0f0606060f18090a0b19061202032203 64
    0x6030f2240c81600c06024508850301c9030880c10820034800e0020510191011101c3d4603948004000448907041031440c242031007940f40b0300d8150608034800003802d1114030080e101d17401000c01d81c020502e80003c2c4402c2c2450499505a800481d000c24041e0b240d0002c0d504c0c040d41e038015410002c54100da60706066008100d2056114840b0f98240c1c115a58040b00981c4e03010410402c9600316080c903511104400c0c28059a00b02400e58095844030564907010407050408007000100440c1b0142400103a4171030b91811941c404403908501e8284207800c5104101c086000c040403a64000d0307003e44514a080d40942c1c0170359000403e508054201454694040201038018006181c0c0900b00c80c1250345544400707860550f14002110313203e070001c106200d103c1c4c00d5241d900182020416060304684030094032000f0501148046074400142034550080880c141801c40c82c00114011201c00c58608070704008001d40740d07202d203010380c1a925030b0000c00552000d001c22603414904041c0b8030142c1018544d4200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392566043 1250 392564793 392564801
    0x4150303030b1206040b0106050903010b0a090501050a210f05033016021c110a081201050604060c12090506070609060606230307180f06030506010c0b0402120c0d0501 73
    0xb110b406484200124140944005105486030b40e011402e1092682000c10407181038004004581e01503407926480d210300d9550401820203044001000505903140c0420400300107484c0d88000e0006840c0301c0610010340b482c281000c2c08540103800b402864142d450301d146036106061304010000d0b02740c4581a5005ca05080340c0e100840301e40410151911038946819240100380502c4001d60f0019010640907034040c600c60035522341d581012210001c8218406040c1400c12a048400c1d80000440318001224403090502421054600a08090a1041c0502500985c0001030085001c40c8503c00580d4451410500605009444651201e0782460800050065088200c4855040c1180030442a1242d00030440c2c02480100030600c603403c445004856600162800013084140f540c01103440d06248100700040007030300700403820180350040090440b0005407806041240d020424400705119446003a0442d804645960310202c0c103440e1540780c4007031391507816000a0b0020705c00b401c0c00010742c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392567293 1250 392566043 392566061
    0x80303010317041721040e18100c050c0f0303070503130c120b040605060f21160f060e01050304111306030210030207021c08041e080318040b01030e07060302090415030303 75
    0xe40c05017802006000d0400d00c0c0103500454110008034000506130f500b07690904040b4011001c161006901003014a07400e0b0f070030b119a0100480c0380011402c0c00c50b0001c200e001c00075440d00300610704604091400504030712001e4484840d083c40240b059041c0480c003851100200f050160030700603a1072512f004070303107440121415101186000300003049400d24601c035849441c00100034910b007400220302c450300500500d003094241e01c1010814a02d2041a0401c0c80190508081900c0c40c549000e038018a036140d00d1081310f0400200740280000220414410a400b00003100c50140944200161200078890740c0d0000e9406000301140e10380c0c0741d4050f40103011903402a50044c41d51a5980c014902c0e200c07068a005004e00c904102c05c02450100c3d80303145004400d82c0c00c1d4405002e5a480c400f914640003d50b0603004540d50f500d104989281511400550180a080034054600000d04203611202548500024540c002800c03c03040d5849501c000000d406805d040c4200d540c0740e0034000c004164040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392568543 1250 392567293 392567323
    0x250c110a0f090b0f01020d260405060402151801050a0507050601060801080d0804020303030705160b0703020d06140d1e060f0501080607050c1914011d07050402040803030103170417 79
    0x280e0324040f50a00d08181111614103030000c00650b000d80d0000c40f0041c0c076854518812403446050681500c001d4070525020ba0b000c2d1004142c1800d250040002c5000c0c902c0b99000d6101781040300e002c0c0d03500c0c43c4010348403156007420816102c44003804141c61500c41c901008140b8028100082142d40c0c001112605a4400008440e2604031403802a502c8030001e890182d8940d01c10300004040034031420050405890b80c040300f56144025035240d0310300080540d1a030010a402160359105016035101d54030040403400090150714041c2808190700c1da48030340c80a0481e1064039490f0b00d020607034041824003158004403c0281c1500c80302a50700419081c007a120142c080c10020603500c84c800d0064402d5a40864041c001455004894248501c00c03040129041100b100c20200640d4080c46514036422001094150201c02c86c01820f0403c111600440c1c481d81c0305001c00e100501e000070507281900c3d803104078460240903c0101001d0b50089a019100f8088850803140c14080041000c5a001c402d10f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392569793 1250 392568543 392568551
    0x303070309110a05011b02030304150309021816030905010e03040b120604060506120421170105010912030e06071202070914010e06040c0309140a0308250c110a0f09 72
    0x2541084038110f900e11071140051205c81651195400d20300d90804a9071004041b24680360340c0e83c0f0403050b0050003215040110303945031030120a5080c504c944066500780c0380710070381c0203281041121070b400da50105198105a40e5440d21400c00900754804ca00d560301002c212a00d45503116609070b5654024030030100004400f801043c207604140c0100010340e42c000300759070701b0302e0403100020003412001002500c261a200051451107403c41c500307000014026034498401202c4003154218003071060b07010504101400c141081030590600c0000e0100394103280040c1044042000103055004841e005003440c803041016040060700040d42c0310071220384038014010505005602e00c0801c009229074030400e15658000741403450a58400c50345030b4540d080029448001d41c4520a090610150a00e5141d210714569000e064000004030b51080001802e00c8003c059981104120720b03d490348201440040c01c0c2e4007003000700c0c0c031081d00f00403140982800720541c0d803100400340790403051144551852038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392571043 1250 392569793 392569823
    0x4180c080c01080c130e04060504050114060603130c0b130608070c0314030c12090102040609120807060e12031612360f0b0402010e06040f060e01030e0303070309 71
    0x80400c49540715841610307122103540e41e04410a0403039205090012103062080d0300450216001d0343c409005601440000403103280914041d42110900c01d4000b21040c010401c1011503a00c0c1001c8a51203610f0010340c0c043d600c150300c5c080d8070300007154100b40502c602c08680702c1c09825030b4031072000844040da5181c90b15070315020f005a40c1c0e621840d4014000428420801000340c00c107100079600705441000b0180350140c1e413100110222000e03585254180d4001504000903a442541c03071001d407051140301495003109036940269403190441c01000030740c0f0f41000580000c020311034074425100c1c040070306a0300e20b080040050300f001300c0407206001c560501c015408003041e51283d0b803000c0380f100b04040801303200345004000b103284a21701c0d222214100300030800050241105031302d18901c44c00f9030301d845080030320001d000c120f1225000750181d40c0600080040e108003843c5041203410509203001c50340e4921004801400d44201c641505100000c03c0c400c80d294198407118080b4044c41c4110315200c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392572293 1250 392571043 392571059
    0x2010e0111061f120c080d0f0801090b060f120402041d060a0e240f07180303050a0309120c05060f011d0c040f0612050a05040201080f100504180c 64
    0x11800e04264455803111001800460038401000306140404401200c2e841d42d4284138005200148421942d0600013101000080010800c01900800d942400c8140e10210343d0010f1980390f0512070306100c55183c0900810645072081162141c0f4217210140d035503580ba82080040c0c490090344d08a02407403030f00d000810002048050b10041030b14201c040c100d01d07110300555101034249022811f1960143c0c4031420480100c0c045c005c1c41564401c03108800f20714003070b84443c402c5180100302405205500300140314080b41c400198098951509110343c441525200840084c24103c000030041c0f4180e0038114862a0400d841d80900d40c480c2c001c03070390141d452003d240c4030b42c1d0702880340002d00f120786200092802d40300120316900c1800220f00c030381441d03070b5040560b0759a41142d00020126415100f684401040b0f0300420740d000c0d1900c01d081c485820b06070f0001789005001010001f40701202c401040051404040da2001404020804d0248465555016030424801d100886d11071800da040060307042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392573543 1250 392572293 392572307
    0x40f0c0c1502090f121507120509030a0f0f050906070b0105040b03011104090b061201170d030c0e0112021306020609010b12122208010b0f03011b03270b0402010e01 72
    0x71401904904c074900b01c58040c000340f070008603c400c6150081101d4480c4020713480d00c101e44202a6130b50b540e500240c1e42c040c1c0310200d6002800c0c54030380d40c0040000324241500041d82c101510818900002183e42500003201c481c0603400d41d882d841000001c11500f170040280010341030360001c403410003016444d4420542200c01c1045010041e0806000c104044516580180c03240000541010301e080080c2c1c50341d41340795109070400c0110b00702044040845510421800145518030304041142610b2808090500a07210b00c10904001c103018805005040070780640d00380c86030084e4201c0100c4d460342c0010b9200d8408480c041c0241d03182050000861a140c3c000c5c1d2164804280580340c9074884203d15102035204100c0c0540c5a01200c014402c80f003c0405e1060052000c0340000451092440030000c2d42140c27290051b00c00c0c0e042030321b4200031a9000300c02410088ac14140040d61040b40e10340c05060603e10190070f03042e4100d132041901072100c0124081c0c440c40c402d982d40c260005081005650300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392574793 1250 392573543 392573557
    0x1080a02011e1407050105071e020601140f031504031202040302090a02030c07020a1512020c0d08090c0a0902030f10030b041205041a0a0206070503130201030b040f0c0c1502 76
    0x1010100c4103000c030721849a00d001c207401d003031400c0d05107111150340a03041a40071200c111006d81d5544200040540d00240d0101d42040c400c0c0307210300700e041050f4021b6580c90180204180701c00440d100080c5640d5140321070811b00310103025948003d01d0003260040202080b20260f010607880b02455580c1c0c0294800c44065942c01090704402e174a8818610f0f0003504001c0454101010030020000565981d100d81d1004140340b4850895125049100038400408070510070700b401c5c010f1010003007620000c50704100640d81c03490201c07080d55540806625000000700da5a4110303003828030200b051445500214410803110000d0744903a03c0e100c00040250b91984005051088401c3c003003800142c1904222094100f10300c1e1032410543c941001d5491100700481c0c2403420003001808000d01174043c032030315502c4001800c1050a5103801e40d00400b22a0329207800904251759400d0f044e64a544541c4100380d085040c2d0800c000352502c09102400d40c20390642c00b40c0b1840741307d4107000b51280c0240210307000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392576043 1250 392574793 392574797
    0x190506071106060a0b03040203070f0803180102120d0510030213061a0711060d06091508010c020a24020d06080102090111010605030a11060706240905040803040b180703060c030501080a0201 83
    0x24003031505d2020700341074201410481c0d0500401d0000184400307403604c40006060500083c3d5079406281074405034041a0610aa0542d00614140309080e1440815074481c00c1d081c01010800b640e50454410301e0001c2504000c1d4040140c20403e130030160958031100c1500c0c6041d49420001c00150000300190180090007054090326012400e818105a405400b4240740d16801281039603c5403881400d940300342c1c80c9210320381904002001902d800740116008990b150018003407403010354503940b50501d0f419040d4041c40f9510703110711807690b00c140d0440d00c1e1158080c504100840d12501102d010358000302300c550004180880e02001140184550801c40700020000d01103030341655074101c0618102c0d0b40c8241c2c03181c407d1290001141d10390042c801840c00001a2140c2c010071280c0491205c84183c018420880c034040c10031000400711422030360410707008880420a540c0d2071070300e02c0303210700c41200034001409410b80c00010000780f60800024210291401e200c02d030b0700c820101e0f95654241070040c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392577293 1250 392576043 392576059
    0x605010e0d1e050d0e0414090c0103050601050c0714240a0c03030204050d2d080405090402040e1f050106081303030e07150e04150302030d08070219050607110606 71
    0x180407500009082400b06440c1c542080d00b540ba503504040c030541020010400c40c0c80c481c0c210349428403e03200c14480c42c1070002d4142c1885180765556510305400b180c140f40e0f0300c070046921a030007401582e044403180400c4903003294aa0750210065941148404c0c01101e1070186410714112207103442e1031442c1c402561604000d0307594400c4584804080080d41031550802001c146030701e8003026124400c0c000c4000b101d00c040c417428000c40c000d0000c0c801807038018202d940f40c400951040100c8049880496000030703117854a00001d002800c05601d50129407182554098401d0450450000d6000301110100083c0c0c0c0c0c0c81d41d0a03640c0c028111002007010740340214400000303010358042c00f080d900380c104440c2c6641e1107104e105220ba841c803584402013241d600c5030380341c4d920705801113a00503640c01044894032413031035021a81d1134003200c440106001924002810f03041c400c0081c0364494024088010256150341070450f02c4683c283d80550018002c00300e00329181c0341c0000e405000313502c081c0c2020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392578543 1250 392577293 392577319
    0x6030c0c0605040c0b030f061504050307050f0a1205150703150e270c0a050d030503240301090326040332031e010e04151109041e0605010e 61
    0x300040c04010000c0f9144810b0403000300305e0142000c01b440c4500001e40040301039040540c200100c031600030108401d05202000280440e440110300d060031510140c880900304090017000a001c814590001e46411032464404014400c00260124a61018408480950311102e00803402da9248505058044c04200020800120a2209150b1004600c04240c0c100c000301011006035520072845084c039584004178160061404008841c010082110030382100c250307940c2d01803c05e000c010684d8180000a60358440701c800c181c0070510320883c00034003c0214424502d405490b018050401d86940e001d10069070381291282100c1d50b0060b905500d4141808a00700303882c031481265007a0341c41d44c0b2001d911480407078205000107140101034001c020013100b4078012984801b444140e0011900a0522003800b0114500c01c10001c43d500c400740d40443d0201058606800d580b040b0b8001c0da810034500340c0000201700304c5202085d484110304009200741545d0700c0044441c85070405101d9400380f1070303800301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392579793 1250 392578543 392578553
    0xb1509090114010e031020120705071707080703030b090403022a220c02030412020d0f0b181b010203180307030506040602070b0f090a02040c1817010606030c0c 70
    0x1c202c0052051401003046103074480400d003040102c4100e40d10701502c0300700e41c0080d2405c0c05282d40b4880b0790300c01e04501f00700d03800190201c8684050a480d040c1b001c00a0000280003c0602c1000e02032507415459544401510300340c12142c1c04582d056000078a4460704091070b1500f5801980034030781690042c030301c030882560122405103500003904246110002d0b00002a250b800141001070710f41c0315507014ac0a200c020394000d49040b5000e00086400400040c000d80c05010498249540c056404607070b13980107440c006d044940440000303400d400503030f8200081098003421040c0340c44408815180e0390411a080b00d00c51f2003212a603640581c1041c40042c1c4854903070b440309069030000400702d41c0455078989409040040a8030103440282c1c00040210510207001c41440d0000600c071006951441c182000e140c4400441c2d0001748916115220180401c2c8540d129160071454203000041d078565600300001201c80f20300715026554208500002e0440c064810b110000b074541c1c441c0240f040b500e9650f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392581043 1250 392579793 392579819
    0x601110c102001051806160c020406170303060103200405010c060b0603070c0c050a050a0905100b0301060e03191703250906170c0406110709020703030b15090901 71
    0x60020022000070001c0c0d5040302d44480e00302a980d8600000391401d00440724031040c030700017015624941c8a5014020105d005a10201240b41c0c00e1601210284251000a002d4001c0b54882001a0054a44e202c410f50001c0015801000c2c243c80c00c0028103641c0144160080c500400c1c07401c1814144020071083d4010700b0030b0040180f0071000003d01030312070070002c0d03656081034441c000040c00702c4224400b004034000385500038150807141c00c1c000c5403411000942c60340a5001c2e02102e280c03030704081a1000a0000c0000c041d0035a480050f480b9a1501802020001300c002a04d20038812050440d000b00c50706c0540e0400340e40c0001d043c4506400c1c01d1144d4030b2990015140000c14000740c50784000001315210500b01c181140c0e6980303c01c2500e0094001c020724100d00c5101c0c03040440c4c2c0144011040a0003c50381140d280c0d0074013052200a0014050401c585d0b0b44c8611480d5000285d14020103615a102203101c00048a108401005800c1142d45a00a6051050f000503c090051011400c4114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392582293 1250 392581043 392581069
    0x14122712031612060905060a0f08070b0904090203060106050a0f051303030c0f06060e04020907020f1513050708030a171608042307050103050705071a0718080c04050601110c 76
    0x41c0403074880c0203d05620704440766a400740c00650383d64000c0c8102803034610b031902d00074203840e2400201e03542082c00d0151a28a540b046c0080d80400003000311031910340e5006040040d40007001c1d180344c0e6948010140c0340e40d0200d00d080740041d1050100244aa01400684aa00460304104110b150850b901603d07607a80e02c84064031a45501e003a000f0001c1c129000e005d02800c8017100202c2c841c1040e205000034640007421040554100d01d60207480b41c00002110070201c5418554101251a6800e02c0030b40180d2014001e810b03030090718404500018008002d0401d0710107540d40d11209500807444c181000e8040e55160401a00d41c0b0705108014030038090190003c1c081c5c1e542c1d07a02c1000240100340c4c22151039a9880403034019420400166800d442142ea03c81902c1c101245482501d0f0390702c60f00144a003120481030740380800030414152061f10b041d900218990b850b00807041c0c0719594503580380300d0300c0c1c001c1d4480c609003c00200194411030402000085a800170500d6901500401028141e00380c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392583543 1250 392582293 392582297
    0x302030c0d090609050f010806040f18060e1b10140f04090b0f0108010f0e190c0206010e130c030620181c0503030106141227120316 58
    0x1100d52010000240035030071114840c1d031142e44000340b03414800351141d200d43d8081446400c141c0c02c0600c2e103907003044034168418001c07100024000340411a44c00208a0140030981d8110076035103120401c00a58840d5000410640880300e00041c00c00c05c009901c5026400d11303810550980013000043c0c0203000d02c0d40c2e6108107481d85414a0038072510031050350816848030344110340301d0104c000d01d403c04003001c8644507000c0c6043c40312581404682c885030380ea14402d50b214164080001610b10b100b001e589040031040d10300c14002d40c0070200009503203500a001300c060311000c42e400308141c0100c1c5450700b0042c640c4440d81da0211844d580700c5000070304003140325400e1083c070700407021303031640d1000000c00072003001941d4070780c0400d003850500c0035085c1802c9010000d442024403403404100c0000989045a01920740204080303401d00102580e4012441100d10b501851018004040300308203000c224070900d90315682e9100f50541419a1700c842008105401e10390800111399000072442840903c02018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392584793 1250 392583543 392583547
    0x6060f080703091b090c020706020c010518061218010b010c030e0f09091f02180603040f0602040b181906110a0b04050105011a0c10020d09060914010c0c1707030203 72
    0x10340701e1044c601682e941c0a205180b10640a0143d0b10030307131003440c80346c0202c0d2004081c030908002e406541ca544500c4041d051040110714419850301e95080303131040407006402d10740c60303950300000c5004900c405d803031002040844038100034250505116940310350405a4401401c000310f41c4069071107110443c1000e40010781d0b10345401355921041e5001d03000d07251070002403504440034406020f4180120519009060040049490603514005c034855120300454441d0794a0701e481c5804580182000d5004215034000303e4000b800205d004054501c95215880c0d24441c00000f0042003c1e120100c400100003c04141080c040c05108600c1d0544042c8600220b0b4607940a50303d802c08441011030302180d071a9103800044c403e54110380e9819560b80c0c1c80490302414051061005611112006aa80041a400b046600080f101e035008504400d80100d010003c0c030b07103e41017002102100f100444925800c10620003d540d206e1003031a08410f8000c403070741c0102d042c010100c144035440340d2010b504500c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392586043 1250 392584793 392584811
    0x10020a0c05130207120c0302071401050702090a060f080c0901051518030718230402100e0d1a070905060405031024060206150315010e10030503030c07060b0406060f080703 75
    0x204d00e010a445d800a07440d00b4507030710004c0c078000740b8045040c2c22151584c000064032041998020050700c0706103a04950030185503544001100080003e03070700141c0003007a098000100000007003040080c01c02306503100442a0b0320380d03003807181c8400c0c0101e07e281c054104100804907842c414401754101c0c00010240c560541c1d0318000d1070050240d4407800b40c2020f649485450a400f04d90601443c0d04d40c075038008036007924140c1c0014041c80481d20300102481900b000041c100d9560120014000741e01929042c0d00045480c4000e00900c01101d00e903011803003412003c280da14102c82030703804440004006080d11000c0c50050400b4041c000c3c0100da00785c0807060108404100d0802001c050070407030b0300600c41440c1915810044504194005000b07400c00d0300e66070154036465034400d0641300143c441d031903151580e002c400c0595406a10207000b600020040c0300600c420301000345125801071400340300c260602c80811089648038271400000c5a8484078445409010723140c450b07071240b1030b81000106040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392587293 1250 392586043 392586053
    0x1103151e041a0406080f0a030c03110709060603151a07080904050a0b0a09050c0301091a030a050607090602011116081611010f050c060105190b04120210020a0c05130207 74
    0x2d030300780e80754400500d55560140a0401d842418003c080110043c07001c12a0703503000d1911703005814005010031403003102c4036043c1400740280c0e90b44000c4400885101d107546034074000c0108118082c040020707042c40b201544540440d000f400c00e481410801c8941422460310700c402d50783c84448100c0e9580014001d00307000366514402d00748102d1828102203940100c503401c000c842c071303441d411001c074a510b45010711a07003c8400c0d0a980c10740e00e40728000507121441c1d5464000171b018080b045903140c4101051002040070115400d40a4a0152070750202a0346642040e13003070300c003c026461401c11062080c0301c40303030031600512003505011300708040c600f01c00289580300322001c0d030380180c840c0c41001036117180300d580c00030b142c401c040c0e01031a02c0c0f8140101040e040342c41e010107105440c402c0700245101039180e0040595140100050740d09244c0d62580c60030350b901104044141a4072810250040101450010a0f84071000b80d0181c0922025802d24042200310301c6d0243c010701c1c07101e83c28087c0000080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392588543 1250 392587293 392587301
    0xe061b0106170105072d0e03011803030b0a050904060b0f03070605042918060903010e0a02030f011506180513021c11070f0501020c0717011103151e04 66
    0x10100820408011035034042d01030940d10084c10714803c11800d01070030904068106144a40d00c4402c5540300d020000c4084101d59039061084540d40c503501e0312003401100e140410300b00148501c0b030b07181404010101d104010706030055200e0f0540110001c7c0002c2c1c006069548540c8201c0340080a8042002ea10004a40f40c001140c00c06008600002021310140c050034203240c40d0244c42c0358a00d1415110207003181c09a014080e40524070a02c2d41062481e16500c900039189401000f900030040c5e84c11003a8169640c1140f0b03407041e0301034013494156520070b0406020b1071001d4411a9600c2c0300c0d844c94000101c2d542c86944141e07903590884124041025034401120105c3c48002000251f01e038100303d840203001c0c6006605071040785140c010400f940644245c182e5140341e8010601140000280c103050b0b01904c603002c00b85020340a07654012403400494140044082d65040c020400100403000f2012188070540e10000b0070040c90074140580d20340204030341081030340c015840f2a01c55412011405803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392589793 1250 392588543 392588549
    0x15010309060908031303021c0504090203091e07032f0111120a0302090f0d0b071404050315070210060f170a12021e060c070b100b0f280e061b0106 64
    0xc5e8032a03034010800e140d4100310754000003405940707804c031568000d68043c081e8031607440383d80da20030b4000c0001740c0030307070014051001410500b003482c0c0107400310600c1490310f40403140000c07551220041c2c0e40415690301c074146031a8078070b000070b5041c90840740c100064920b4440c0c5070740d0b410300c0e10520005100c14088003003e010102c2041e2030168450030303098100315458161100b000d0181442c44846808540c01c985800d0308001c440c14107880a101d1501002c41d40c0c815900060b03018481c480700c481d902d00c0c885002601c19002c0c6d9083d42c01c02c81d011502041a03074905c4c42040441c0e403a1035005d01c260400200540c0c402e80000b800c1f03c090003001d90710b07007440f50002e09030100560080c01e403c100c04460300100b20640c07080300300a03010354903098500c4501d6010f2104081c280d4207035200007540400e50307044508084c010100486031100b880284840050b4400c000b4040c1440448101c02480d4210341121081d8075907944030a040b030382209062101a82091000302035090503100c40c2000090203219240107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392591043 1250 392589793 392589811
    0x60d050a060603031b02010c060203070909090c030c0e040c0308091804050a0b0c13140607020910050109151709011508030d0516090b07020303090a090b03010f051501030906090803 79
    0x2e10340395007006400b803405001c03112034a501c070024a01c010703a80044440a01c07944502d0040e241d0b15000f500301d80d403042d950040c1401030310300101c140070300c1075034403004007100d10607405007620395250026440c4451301070318014516005207000f0b1000803444005002e11210103004100340c01d0f440714100300d02810560307080d117881d000b8400d403c00740b00b202e005e2940d000e20000500361506070030a03046409444207200304001d159041030101e0055884200b240c03601900140140f1090401000c1031071020400e2088038045501c0480004110a00441480c0e46620540f07500348440c46000b480c00d0324120007066550300e5561100040d04c0b4800d0309074043c0180c445c81c001551980001d5000d8000c03a1000ba05442034803000000043e02c240d48100c0c000140c03540c80c8016500c906461001c28554041c0c03200090b80301c108142c005c40c0720003556101d6005224218000d12071140303c0c480b104d044540c1074403080610362280381590f441c0c1d4000e410140c40c5911400303002441414580710818150403d0b40c08542d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392592293 1250 392591043 392591051
    0xe0c09061b0d03020c030d1802090103050f01060501020a17030a110315150414060d0e010513050c01090e06010c1a040318080c03100c02010f1d0d020c0a0e060d050a06 73
    0x141c4041c04001d00407000c1c0d8203060441c81c00e60103110842d643c2c01031070781940c04030351140c1058141081c00242d06101075405440d00c6243e5849203030042d150007070700c6490f0002d9841c00b01c00040662000440050b040d81162074142e03c0301d0340d000c00c0c120380e5000500c4d290655895200d030801c500400f200941c4510b403035640b48480c0d18100d800b04480daa0035a400340512300d005010a2000a5a0340002c140391401141c40c40d6455810505110240000c088024219441c100400540245948442d6251482401a120740440c60001900c280700c460084501101081002442550164040e18000d600640004220002c60088400324034011a001c0340040d6000c50848584882c2d80442005008040094040d541c10a00402c0e501d0341144001d60310b8a4542034a103094074004e5119960444001605000f0000042a2040040d0056101c2005071003104c00d840d1405102144a080320707200100510b410910b05140840c030b618005c0d003ea0f5114004a80440c0003860411404110612590001c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392593543 1250 392592293 392592337
    0x15031c020c090f0a0b180f010e06010c030915030e0f030a0e1203070609030512180714060313050c22060e040302190c050612040507050a0605040e0c0906 67
    0x241070040c0c19005078060700440c024020402030600603681d0080a8100c005420352035480083d034101c091a07907510600c041141405041700300c0c10f0034141078503d01021480c440e1503c1c801183c0307483c03800030060002134005a080c00503503402c80203410a04c1c100d1502042e08904880c21a007826540780c80740d14035074400070b542002240c00c4039114900d290201c1b0320020282c05035114580724820311000401c182d96803d88034041500070429078100c0e46800488240300e00d052519120103a54989800b101c034072034008005000e42c5411102c0d40c00c0b000c054a001d086890300b0a03000150400414112498050404010816151603002240306507a0910280d840c503190325102e01161134075001a04c84882440420003c281c002490000445125808558aa1709403c002e506a001900050780c0300400007802410f1014030425a4041c5004030261114503586000300910742d813140c07080c01c0c003155051004019100c5081d0750994010031401030b45103450701d070500240c8554041c2500d091042003081d100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392594793 1250 392593543 392593547
    0x904030e0f31020a090605070c0b030a09151b0c080d0c080a1404020d020d020f060c0f0712020102060613020903191a0106271d2d0a020315031c 63
    0x2c1d40e010521110110b1820b1855040100300703c0300c5000318411300500041c03a2003004004d04c0510002c002207030b011a183d0808519610242c046000f05444114141c10f001600312014400d00b4203820301e04c00700462100f142d500c1658900305003c1c0680d82018103000c00304040c03120340a10080c01c803590350f03000928500405e59400f19540d26408016415500c0204001030b11117500c5442400d4040320030780300c80c8000b0701c0041c803e02000c9245580211010554000c038407800240d80640030982c0e420b80e1700e0aa00c40801d200c204009140190060340203401050060074072003810900d08501060240c640046000030070710f401c909208002031f15040880344802e00061030418030b10095070041806481d4500b0000428a02c0d192180c0c00c507840381d100d04000d110761032402c840000d1000e0008094455084ca0320000c503100115441c0c03c4410700f9240498140e2048489143d00400300300c51118981c4035510803400030740000f0310006103090710030007400ca1a90b0400010042d404194917445081001c0303500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392596043 1250 392594793 392594869
    0x20c280608091902190602060a1a090703090f0f030503010f0902030609150d0f0c090b0303030903030c0a0c2a0b0a02070e04050a0b0408090f0f0904030e0f 68
    0x40041040c00024822140000320b0a01c0c1c4040b025007801010070f07201d000107074112046a41180c00384911100018805401048040c443d000c9200c08000da5002110100d03944000946400e40c0b00d41c0c00030001e00c1503030080d889299810300840011509900e81d03030740e80218450302c0d881540418004001044044070203c01d94001e401507400a6041d410301201040940300d0103009002e02d9004500d000030103858440144c0c0d00c00e60440509a8001598104051314075000c0c021444441d0800c0b80c1c4554034140001124000c5100e0002145190380351078042c030103a00402407210400c80c0c0c0c50290b50120300030081d1105903c9041482490900408244811001c00303513000385082102884458003084d00841c040045480c04440c244459545213801414a1000f2000070301d29804401440140700d20103010f0140a601619806480301514080241d5900d11507011a408000d02c000070300068401c00086c00380c900090003600c5120503050000d040883c010f40513109803c04030b2454210010f034114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392597293 1250 392596043 392596049
    0xf02150715020405040f1a0d033b0402190c0c0b04060e0102010b01091a0f130f0e090a0c031401200d060b0403050d0f050705070312031a091303020c28 66
    0x10030050300c0c880d60410003c0c0f0f0303046480c1c68807070000c09031101c092500a203080c00c1092b0a24010320740c1c071620400040070500800000304050900702d103401c80542400c0c4200d44640e50350001d05c0100d0f8a1055044980f1b020f080c030111040c1c22418400602c1d52144405003000e0406902c85401001034035000a0031103400c507d4080c100000340c60b041002e640c04002c441c42a00700c895180b51b030740e51510079520b00791084007901b00e00c1c1100f00200040e01d20722003422006581480c18400180e8581c100900e0b542d030140d40f0040d011108800d8104002405900400001c0d8040f60000ca5100c2c050001600300600e00e00c00452519800182c1005041c0350344500760103445030207442c50406003191286541c4403c21003130724085c00001c2050f007400602980030380c1c1c1c0b09a40711080350502922841c0111510182001c550302207818108070424081c01203040703182924003e4004001999030540003100d05984000c1502940255005000c140e00c48050102c9401d00000c0030400d1480c11190100550801d94 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392598543 1250 392597293 392597321
    0x1501030b04090804151e09150201021c020c0a0c0e01150309051002090a0f120c05041b1202040e010905040515070207141203070606170a0f0215071502040504 69
    0x640c020000600c84410358082e1754000860742011180140155010000034585503d24250301e00003950151340040040183d6080311185d000d2208022000c0e8242d0043d080a1100031440100780404c0e110160301a1441216040071205074003940c0d11407000000c8142c00c0749148010410060060094440c1010308000c07051504224411143c3c84e03490321107019034800c4c0c048580004040000342e441066603000307880409200d00071540e0b600f07400c4410700300030041103030244d0840c400040d407440c051040c020b1150403085038a9404079000c0003290041c1034001061aa42c0d402d00c00403602c4168070102c0c0b8064403004500254908080c1003603440d192800b403076610612100c5080001160f0b022600008441448085031400307403608000644442d9a02d42e80b800d1480041002010f001161300030b40100c0e0703600100280c40140f98400d85407107006070340000c3c0290fa404c200030b1006081c042145d484040c0c071010247d0030030000b55603e00104c0000403525002d26000301e014000ca141c64420b68100329000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392599793 1250 392598543 392598551
    0x15030906101509050d02120f0c0301060501080403080412121a041a01090e070905120309010314091e010605150307030b010905150c100c09081203040503190302040e1501030b04 77
    0x280b801428200c243c0036070707401340303810162003011902c402000114442c854002d83d0b1840c2c03200c4000d19582c40340100302d07038481d60174040002a29401082401c2c052505942c80044a80d11510382000300f81c0c2c0130401c0381c20846020740c121a080e006d481260801a94a0704800b00000f074a001c00060b940d080d40c03a150f00107040c1e5454603150382c00406850444055411000a650365050107032100c0b04964406a08080d038040700c0c840601011004200e0380c3d9090f00c0030130109107542102c100400d8100c6500096a1050704880001c90200d8070b018260b00041c000840c0d03003a22400818450074184404003200d1101105000b60310f50036002c0e010b202c03031080c80c00078000da00d400001403e242095034009602800052a42c00b20b800a1019415140c0d41007000c0c012441d50345c100805801191243e020140a925a501c0c100310110044a00894000c0001c1d030910741d080491105030840e005090082c2340e42008006825151203014072b200701100c100030108016810005010345d448000d001d07104031b00d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392601043 1250 392599793 392599829
    0xa02030f01060c0f0c0f03122307020f13050103050d030e030f0903032703011805100510170106050f010f0f08060604030501060803071e0c12021503090610 68
    0xc09204941124140c2c6890700000300c0070304207035844a21040000c0d0911007200f2002c100c0010b0103080b401101d100c0c48101350041c440c001c040f2041015140a88602c2162007513520b8200400c401a000050009110541c0000007000060354921a440d605010030748800c0100240002881105001009810203015003000842071940381d2040144001c0d002c0d8001c200c21681c1e441c100191460038a9115010740d00000540c00344d189012a107c01c0340c0710f58201100c94501001f070450a064040c0d01900070010814030603c900040c000060629080b02d50401000458240c41c13142482d11105040001480c04d00380b0090048101c00f0010050610802c0030748500c4a65201d081c8042c1c0300705903d06400e080c0c80d080300007033a0348110381c8090180d41c00c05e0b4011070070460100052520a1064420000003640201da601c1042d12840020705114a084030402c15104a0400210806e100500300410010030488602541e00242c43d42859580a20300704000b4080d0102c45102510000b070b101401594 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392602293 1250 392601043 392601061
    0xa0905010e1b0d03051c090204050603010b13022104150b1512060301020405060a030608071a040e090312010618050406080c13140702061b031003020d050c09011401080a0203 76
    0x14403407111800f4161401c0c41c1028584904203031109040d45505200e40098494040409480700c101309030710035031070b180c049601031805100d070000c1982c01800c2c244840003d0303c0642e0082d0004a5960700d64115442c0307400040001007032551103684144121a040e0b0403e078860300449001c00b8809000c0c03d0b400c2541098020040291a001c44100d01c0c049066134811000c80e000e80580e41c00380c0d4201101150f81080c80390140c0146040ea6007401c100c0301459a01e003440d296180c0d0002804880d210100014440c00d0303c0d84901d82e80c007148210483e85007071401352449400e188240d004000280d152010b0b807d0000c0000401c50040c80203c0302400f8150910041a4803001c606c40018401c000b2a40b900309690020740110203e4548001e00652529000002a41794042118100e5590200031001c26070b0b03044100650340102162410a61100c1c00d5609000300c0e60504001541c452040300012000c940d5020340b078034040d000044042d02e141c01860009403100304050040480c841c014401c01500070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392603543 1250 392602293 392602333
    0x305060904020d0641100e040501090f060c020606090712090219030803090f0111040603020a110601031112010b092d010e040c050102060609060f060c03030a0905010e 73
    0x54044034004580081440e0400c010065001100ca840300181c07440b0800302650004240c41d41700304c10b40b440c20b43c050307001d10304a820011500d202201007403001c00c0c411983d414248035803141c0f00d1000011100940d494070b450507001c980044401a807990010b810042d814496107401c55000d5503a0111400d00440140010140307004000f5119900c1d5204030555444d4102290103080c40210803c1e01c1380c803410120559030040350000000e01c5002d40d0569100700501c1821104143d000300e0742d00f072070700b403c0046003e58003009454040100c02001c0070040002845118000c62144100903942e51981d418800c0d40345094961500c2c1c1e0349404a1030b036050304c92000059100e079041000b0385106070482d980c1540383c1801c080b60602c259520f0008244c0500d41c0300311038043c038024601e00d08001e5461004a0381c1307a000b114501d8100101c40007041060070302000000e0509401010907040c60000040c0ba032175500304031043e0725419101e10b800b2041c003200713100e1800404020b10191030035816402d040c0341c1365 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392604793 1250 392603543 392603551
    0xa17040f08090616060605030105010f06051905040b0a0809010501060507050a0b07020a050d020106050f060a2316080d050903070503040303080a090606031101021b0d14070803030c0409050703050609 87
    0x950310000b8101c03019a144021643d0a00140f41440f0750001d140c100380700100f01c00c0c06880d00035032070000042030301d042c1400008102c6040382d41d1070340f805d40d6022040412014520500e0300f441410b001c040707044c00312304e8090b1000218940d510b10341894004806400d50348103074089818810100805030214102013040c6525517082207600155894180301203240c010300103c081c0c142d010303107000f400120341d0642000c001c45004448030401c2d922a001088100c2c450701c1c503040003140b80e0f44403151181c4600b40051a4071006160300c1400c1c505500030780c2c450029400d408030b0b19410005034400c0b101465110700b40d007006810009500b010420750314540c1d41e208a0102905200c1708000081e0308002e144c0088001950100f07003800f050366207103802c0d030403502c7c6c00400341c1c05802041c1172400150803c0314000c0e80d040000302002540b5006072200d000c0a145c003520300700035000340c181c0442e031144200010340c028201110030507580d52404401604459015244400b01420102406485e0b51350000c21070300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392606043 1250 392604793 392604803
    0x3070c0b040b0901052a0d0e101b020111030307030606020f010608060f0a0e01090311010f0b0a060c0204090812010303090902090303040b0309030903060114010e01021609051801110a17040f 83
    0x2580200c07080e50b46c2c00100302c1901c042c0a81a0844c5c0900501020805049000ca5501e9042c0c16408030f104101180b03407140545000242015062401c0e074003d0b0040c0d41300c40c0d0040c100802082500e010003419a4030846030040420340380e45040042d10f904118417802c42451200820815050000c01d0317403640c40240070280001100004100c403400158040b03005410210001c122601c11490b01a0080071100a184e56035441c0c91201c510700c2900340220426035100608800d4210300300303502070f20713043e882010503a0041c1d0780d001c20384000f880200040c4027000b0144240c1c099036156183c024084500f64210342703010350041c03007031440c00d480c0041501d050f50b00c1061682d0305d03035856200c2546140112030040d0760520802c000020320070307854201c0b40346004084e44c0719182030701d075030005aa84070100705100d01010004442040039047e01d501c45900281000e10000c1c20700c02884043d420341c0c40c0c90004103020400010001132668010b06d140d8149c94140d40038403014549604c0d84910204e0100019003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392607293 1250 392606043 392606047
    0x10e0c0f0102150a110f04080105160305040f02101106040b090d0f02190311010c0e0a08120301050402090a0f0605040504060e06090703150b0703180605030606030705161403070c0b040b090105 84
    0x8a108982090f02c00c15180d1b00c00c0e00d911655507540c424080c0c40c041d110400d1f40c60100d41c0404049101c0d015480c840c51f00038522030707004001582844500781c058101501006203202c0c4a4403151000d020b107074020341c051413403400281828007055081401c8049081c0512180000c47d076415030b00811102e0207000116280703c2c001001d4101070394003c0b0050030001c0694a4500d00304916900f1078082100b00300156810541c40341c0303500c8140ea031042180320100b801281800104054039041e0000c1c04442c00190000d054195521031401e01c03001550041c80c0401d5000c03500340194142445110010004401411558244140418050500944184101912900070f04028034090743d4a400910815503001eaa801c0e00d4140240b03048008a1848100489440f0001e101881001030328022840240030526603215010280d6940e44080c2248000034403948040d404101000d800f08240c12400f4043e590343c0f84a8034150100548a4012070741c000410b00003407005a0108050302c000c6042800c0c115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392608543 1250 392607293 392607311
    0x23040206040513020d06141e060903030304030f080f0708040f020301150602030403060b121e0f07060c111207091e11120a140a1d010e0c0f0102150a 65
    0x900680704a800054000742a0254044080341c1e5034014140314203035803805c2108a44503d43c0002e0518820221580720000d4081d10300000e00d00481050640001000c0c5850940d0380340c0401e00b180c0040b141a40800d40101142140e00d03007120282d648403c8c0c90306801070f5490030690142110b0700140020380000c1c0000542e0046440c01d5003e20000718000031385210f280d507034500c029907a91050104940c07407801d0290418035410300602e004211449000070300b11381d0141c21008050001070701c04a00f10b070700c101c503c0181401c8040c41000050040c1da51054230060071810a455001c01c000c01d018011441c0c51103840b00203401060303443c2030740c2d03003d0710100d100b000d400402220550030003002c038103851a2000580b4032103510001480201c131060b01c040da0964400d46490216009042020201014140001d011500aa21021242443d5000320900d04c00c90202242115000344450015510450340503115181a4184503122402440180a284051800310020f002c01802c1c2c031045c00d881c0d100c07030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392609793 1250 392608543 392608549
    0x807050f07090b12030403050705061e0c070603110a020c09070210050f04020103050f010f0504110c06040f02040e011e05060109050303030901060f050114070f0215130e0109230402 79
    0xa00300803251441203494554988242500400d403a0f9030640c4100e40d03207050b500714200d011003954102c0303030450f01400c11140380c103081c06055403002d01e060203144208007002503002c094102400405440320010010b40b41003080180850310b08480070541130500384140c44055900060b50503c11100b42d6040c407694885c14010b0f842c1005442d0318032400350030a02001010841e40701e0062003075000340c2c0d05021a455465075645451404c1c05010500b810000c000e10403820300d03030000c54842040001c414500341c1c4502609061410503901202d03202c1c00a000d038000d51a103801011120b41044000f040304a030701c00715a00101904d031240c4d10f05d480c0c640700001d44980c0500c20300801808050180d0f175a07441c01a00d0300703000380000d01602034103003414400480d0551040440c1d00c5c6001c03946000f0340c641201030700c5410310b08100700400c0b603102048542d0075540a60b650042d203102250821002501800c2030301001a04005030820f5046031b260820743d100e00d42029540d00c2c0070256400852480c0e0710380d4008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392611043 1250 392609793 392609803
    0x1805150619180911070519120f021f0509010605040204050a061202120412080703180b1504021b1b06030402060d020702300d05040b0d0605040c020c090c0403020d080705 74
    0x540f00705480c05040040e40f000c0d4500512070f40d0300c00d40580c3d520700403c0850182c55081a18090640990040f845600900402046502c8815401159103284003000e00040f03440003031180340c0b00d030303501c4503740b001d003040900a420203810300b11070a5060604000102d03814844501c81c48040051000c3d00a0b94040e00c0e034101c0d060907030141c00144580c0303070504168024000e10000000082d0912000501940c0310348280301c8403000000703800440300416261081e449030050000087c040080130302002e99500c47c80200055510741c0000d15a400c01079110904100021008034164100c0036901c548942d504822603a019a044906d02c2e12500d451070ba080c024091110029000b0f11040004240703c0d040c0004000e15034540740c040c3e40c888041c1219581c4802c004806080403890511040c0721b22aa0440602a10208404001021542c510000e000c4d501907084680158002c0010710046082407070a0540c404020740c7d400c0e20301440c40c0c0c0401c0740109100c40c0500131103004a4030004210301801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392612293 1250 392611043 392611049
    0x6100e06090f0a0608041401110703031d010c0206010914010e06060c0307050307150b041802060307020a020d060e120304080a0305070c140705040b030109020108011a04180515061918 80
    0x44401c80513294032000d4400e01081d2015241d4600348140791003465014010141200700d140841400d01c3c0c050769003030380904408981c0c0c3d485590981244036110750300b44110104002ca507801480c170303549000142c0b0704649144011070310460200c401448400c851241003504240180d070410354903414001c41c039056020303010b0020040e01000404030240002e000c40006940350006081180c21560002c03c0111a500c5150190400f2050412009840c10201541d800800ba0064031000015076001480082d404401121003550701c0d281512030f164100881a2811448000c09186007000d494081c041d0041d490408200350301c0d980082c50b0144101031400c41c2691152049403d02e151030640b41c4c541243d03000e8603018514009c5903654500d814000d001480e50181c440e00072a03400c00040041640903950741005006040200040d01d03d60108901403009021100151504041c26184490300f0b0980240d441014140200300c544600300b030000311000746a08150303072283c2c0c036080c4560f00200303264 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392613543 1250 392612293 392612299
    0x609041b06022506020a0b041b1d07090501050301090c02010b060c010207031218060e15090708210a050c0a080a050403030323010b180310090b06100e06090f 69
    0x610005001c58002402001c8041d0355524503034040901038218416540e2032060b980107901c080d011102040b404824150054011601902c0010b8400d0358048840d0310741c0e010354190f811401c00c1d8012031601599164220030146440351826140200090040c00180102005e09a6450160040da07000f540042400900541050388648422910318000d400c1040103a0114202c8541403420030018801ca000b050140da00c1c050141409480b86002800d001620780260f00c64074008040303001600e01036178880c4181d80010b00440b802c0c90103050034080444118180d1282c1c004c00b00c00b0780b00c1c0d56000e0783c801f2001440d01a845581280c038007450035041d0400500704640019040f030950780d1083c000e0046c0d038001c0e04d0911000040c001e41090b0340d001007040d402c81200d2040140540c0e620b0500800c0b200403003200b196105805600000c3c101552180780840030340d074540c52201003100000382c0e294082d82c21200100c560001030342c06800c0d60800d030202071090600103600242ca56440f104500848006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392614793 1250 392613543 392613593
    0x601171504080405010305090c030d030c0201020c070308030108150402060906090103180819050c07031202120f0a09090b03071403070801060902031012030c0209180102070302012c06060904 83
    0x40c2000c20b055032242c0203640c0080e06110001700340071000101c10140460240041c2648404c640046009204050903101155000c04c400410707110104501000b5600030501e0580d2945010011440d01e00c80707040062548414804000240c0d0b83d1000ba5101c403801500e40b1541c1d401e0840040b030041080c91a5030451102d021209c005108003000034000004013070400c4c40301d2070703207154082d11076000c0c280815080b03600450051000581c8240e84a4030418980111030003032094001e4402e40b82c205140c0107034115008208241078541c000c2c05070300104040c5008001245444020a407562034078050b201140d00341c20f2200816813410003555000342080c8001b0401c841d1a260548065030050307640d0041c20701018000700f0011800c1030442605541521480440f1000794240014018002d100c800344036450007e44545a00c20700060900074404e03030000400008001c150110b00360b038149035445100c000100c00e00b070044005012504001c1c200c8503103101d65560300d002c0a9401040301510001980 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392616043 1250 392614793 392614801
    0x30807150501080a1e052d21180109080a03050c010b120a111903080a0212040f09050405010f090c080d020a030e0603130c0f0311030106030506011715 66
    0x208810890844554080c0001c0e41d03030700c050542d9480400001303031803070b944000d404900c8080e045c0e002030414418826141540000078045540e06034049042d004000301080c07888030218140400c5000641880480c4458802805584828015040e0340c012102c90251800b1440e03004500300c0c001480703800100e903410b032080d18008100b5000070350080d40c15800d02800290b0b5160200d1030b4a030000b5071000a05296085854a081c0c000602041c02d4000280c18601140e507210b90302994061801012981d5491220a030007d2908165124101074081d0611051014002d9401803000b00c1d5005940891a604e450401a004007205107188a42514100c0c0c140d082252448000c401c560700301040c0d03018084403181c16621340a689100900251f0340501401440c41c002c005075810640f200e030002c0c1410303031554885000c0c6580c0d411101c0010020380c400c20400c041181c01162054054000f80b000c6403a56556554450f4103004c0d9004880360b4082506019004000b54030b250b14201c2c2108100d420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392617293 1250 392616043 392616053
    0x71d1201020301091e050c0a08150907200604020f010e011403010f050a08060621030d050106020102130801140105151615110c1b0109082b020f0d18030807 68
    0xf00115009030302d0445c1d000500c1c04050b69105a43c400c84010794a5850803140141c1114200c40040000c070514554500c40806500c0d107200705840b0309202d8841c00d5149107845c1d51251848a500100c0c0c1440e849070041200503181c182c20400900030070b00303240e5801e40d41d10700141e452014100510354030071400700c000580b241201c1d1140c8100d40041d981c01131b0070340c0c841c011240c80302c4003110300701d0f008102e1842c0c04250342443c41d2207281c0480044203490400303072060080302c103680080e4040d600507900400e54070f44041000c14144000d0003603034001c20030000321040300c100b0707900144a064071030402103010306100400d0f20101c601d144802d040c050102c004030303c0c0440308089007003c1503c915203003032486d901c61401041141ca2050210f0014a410320f551410024040d2058583c2410801184030024000204101e000d2020f001a5031040d04034a004040b2042c40e2148000d0340c013198014112000302000c0460100070782101c03407801000ca21035805103100c19070f6150780002c20101000402805001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392618543 1250 392617293 392617301
    0x90e01090b0c0a0c0803100302060307020106090e1f020a090b1b100b0603060f011209211e0302070501140103030825020309010c15060b0a1205071d120102030109 71
    0x40c1c810762588a9549804a50458034043c00ca8641c0106200b03216410118010002851b0320240110410000b03a4482e808241140c00035164040541c1d15584240400c02c040d00a44108600e50001044465010120342030f0001001161000e055800224851224864482031010b020203e6640365150403029018000c01d020241c404e29502030a14501d6024107917016002110780020511802c54a8503c200080240b000710480e0520160340c0340841c5105032801802d4516002c0d540101d42d00728015130003c6003003c01c0c80f00604004c1d6081c00c62002d180891500c500d014114680182c4074003c0d071400c00e00410682c4104c05081c140c0343d00010825510441541c03144100c51040c0c0c1c0f03601c41310072a00c0b111164200d83c01001d83c10500000e10710354411700300c42c1c0990b40a80700c200c01c52134903030305400c045907440e030800c0e40000c50001d81d183c2c5403900000f2460450f8040d0008000e18600110300030402d502505035811840c4145010308240e649900c800189a84910001c55a03945e540c0040d00c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392619793 1250 392618543 392618561
    0x6030a0210110733091707030302010b06070308040f0305070c030b0601022a060a0e04060801020307260415020d050705090118050d08070c180f0506030a030c0615090e01 74
    0x94400c40c0000f040e54020300e9a2040c25030441e0844c0ca144844582c2c0d088511500912068204840280002201101591030003054184a005442424214200282502c148464040c01340e8000c20003030000a50103141554066007000001d883c0070341500e4201c4551080c0c3e070000d000886290404001e0106840720103015040036001caa005406c4c905010085e107103805140c0d4030320709455040340010b0401da0001d000300011450b180440c480b074240003034201e48050b00314003090b0f90b003c410000c600b50051a50700403012124804410607806400c28024040001d0000701b00002c0229000060410b5030159a0014580c1105020314030706007000800c1900700340c0d20f00c4d000803942c0c03040c2100c85554503000c00aa90028000a0780581c00342c1f286030040d8000241100c0d600c070103141c0018100a880c10b103d812014407800032a51304503e85415089e550045d2400703102c0c0d00801000b030300184c1c0000400c000143d0040d004902561003281400180140342d105564290810081207404a0306520107200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392621043 1250 392619793 392619827
    0x11100207052b0b16030b090f190b0301020f090102070512120f0d0e0a020f18241201060e0a0506100f051306022505060a03090804181a09130b06030a0210 67
    0x8008006c04109030200c081c2e403407072410051207010a050040c82d0765900d6a000e54844041404103520011074220b034040706d89140c0016010912980541e4184000001058102c40700040100703005903080e150948241e800d458103034000740301190601c0e10400e85e01c25021207401000000c0740e20765960348841c001c1c8000c80c4a0b18036507190b6982d624046814940b501c070a22680307151a502e041c0c2c43c4a218440e50000d02c0d5492a4a402d00c0043d5502100498403244400010440c1454544621503030400a8422049a41003008002070754880d148802c298140c0d51410b500040342c0301c801500d46d88201d081d1320991000e071003404111960000340d00065002043c000c441440405038160820344c646008080d07109000300a071184807840303a04402d20090140d1540b0b0b1400b80e441a421a62140300784040a03c16101e03081180400b83e01c50080c082e9280a42e80015070b8070303020800300c0482c2c4201000420b550465400b00e8800c0e01c0c10441d0715002035002e000d03000c1c1c013010320902420f44a0714030080d4070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392622293 1250 392621043 392621051
    0x90609140708030a050a0c02030f1c030b0d1518064d0d0e07091a0405060a050d05070801020d02070b070c021f17010311100207052b0b1603 61
    0x2100e102c0001110199007003561818240300780a41d0460350316107640c60507a03061040b040090240082401a010070300821b400d1240074561507400681501ca0008880d441545d0020320000072070850a03130320102d40d20010002800e4211000081c8603103800e0500501003c0c1b501d412100c03101d0022005c1045901013907501c94003032030460001c0850103840b01020a00307032140b6002410710908100900070740240722101003400c51a00030709600d1300003e40e00076030755641c4800c0010015410b900986250860555092006260080110b100e14505104c1c0c1401440303212050010310005010321000713081c00d50000c1d0b6484600383c0c481000f9401c2a0405e903294400f84011a640302e008500c2c2c2c003041d81c1e0143c44100303004403d0710042a140c000610f00310500001401058581c1400080036010b18400c0c0c070010300ea640c000d81400044e441d95040300040d075008640901480c1e4400c040803486540c00112081801c100d2a401f440500c0480c400404600c0c100741031104c0c9800250510b4000000c13658104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392623543 1250 392622293 392622299
    0x60f1b140d0e04290102031b0717060702060f06010311070b06040b19030b060105190903122a05120d050901050f060f0d140f0f0708120409020307030906091407 70
    0x41100d0309000c2414a040f480c2e80041300400f1800030350204a10140152030507c1110000c410401841c203407030f0300d1550080c42c01032000400c0300d00d038841c103480c12400400fa50300e045d5801179903940003d80051541c600c0c0e130000400c9a8402d401543d00d1540b071482041e00d421a03441d104030607180981b0300340c1c46141001198030150411103402000e00003884030b0311170b299103103840700c00f55010b020b0700280c100001040740c07165803e010444800404160b683d0403c2d407030300d5030805d40c0446603a41001d108000301c01c1003d14120895880ea00a0f80703a040c0c03c9903800000916186240c1a03003103024100104c400700350002c21038800e5202c217100f07050040090090f603035a00310144a13140100c82d0f03070b580005410340c2c004c1241001005135100342d22424051500301c0804224902d0000c0380c200300c8244d030b0720641448150820920081c0010b1080d84010588007d083c10024043c0c0074500501c40c03d07550200000c1d00c240d01c0b1f5001710801d9030b08002c08105a01c0b042c01c0254954640610200341c610840d2400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392624793 1250 392623543 392623549
    0x9031219020c0603040809010c060e0307031715090c07050607090918150e120318100c0219060f09080d0e0a020901090906020405031203010f0b04060f1b140d0e 70
    0x1405800e8001c1c4110304e50b030b440340d940c1c0c03204d6045440404d0410907034501d0100000d205100d00405c2c0142c42000319255601d41c5802010143c1d046e0386178010103500c8050085407142292500c06051048138410520303541c00c0000452401540005042c40c441d5006022903150400c07420381c2519040c18043c04401080c0725148401001c04500801d00c441400b9510b03148405603029521582c0888255075032041061002405900161021140d60251280b8148c4040c0104072507404032007030030814000006095406521049600c000b4210340311440d91a00c1001441e50220000c1c2d0304441d82049142c07920708007821150009004080c1080c07034511480360703042e00011a50030640d8014030084040c1e080c01c0c40f14020703264030303603044070703229000e11004c1203d079000d110022410b0706081960391698544942d2205e041075940c0a030090301000c00080c02010340c4070245500b1141d103800c0c02043c110a5844400c1200003030036001d4041401020310544c41c200109030380b601d0b604203a40f040c0c0800c82003010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392625899 1106 392624793 392624803
    0x10509040e0c120616030b0315040b0f0a0212070e040b09240109030809102d120c05120c041e08060109050c031305030903121902 57
    0x580d214181500d0800050518000031300b01c500302405440c00c0001d002050208050300c0c1c40310003419032400c018507840c04080001d404200c4c6403a0804000d01c20080d16002244059540030071280c0d907a60080d2900e202c10501a640561140f0505868169041e22855041600e0700c040305a1943c1e40c0803100c2c494000d855500c5001260060550088134440101505112007000d0a0010540480c15240540c8003a0b544001c1c20601c45010382e100075040c424001c000c01508030001c014100c1c0b44a4404c04000f607202c0c460031900e94100b410541789140359200005806002d407d00c800100f005544d08596207040561505440316200001030085980c0001c8a203880082000b009008002a030300400d50700b10308020508114900000ea440701500000a14482020700e2092210a000701c038030000005080b81e040144011180768150852070740030100c024242840710b4800d00200d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 392446043 392625899 := by
  have h0 := BRFrame.cov_init 392446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392446043 ≤ n) (h2 : n < 392625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
