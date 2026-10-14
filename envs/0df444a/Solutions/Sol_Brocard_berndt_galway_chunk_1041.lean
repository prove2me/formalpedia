-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:58:16.685981+00:00
-- url     : https://prove2.me/submissions/84dc4151-1c16-4f84-b412-3b01a1ed915b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187050359 ≤ n < 187230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187051609 1250 187050359 187050397
    0x50706020304030312050604020c0f0105010509090c01080105090c161a0c09130903140a030209030d05040810052d0405100209010c06050901090b090a0303110f04090b0a030c080102 79
    0x2890000049a05aa03010b45442d001c3c0c0c0c0b10b4207070040150400a01c2daa8015809200041600d0410060107600381d03490340010030342d90705020034080c6110004200c13103107a91080070f541815980000d82581520710a03241251650b49074030603144d0901c91307568519403000105074000144444041c00380740c08221405010a43e84940c48140307054000c0c4c1c4509a809440d840f800200341e0000d81c00518001c4c442d0a0818a034010140c41c0f1029800404860300401c0d0001003480352464244803612480c1454140107090500340700485590b00c0310610912085691000441c121040300c03001c10f200c07400e0140300b0340003001c40c5541800b0300303140541c0d0440307040c80b80c030000398014001070007501d100d15810307556180112600d441d240090817019201429a550b100c4107900030410401c0300e40e02c01c0038820300901001c812480c00600702c0b0000340c0309001001c1e080c8510035408508030120b504803a0201004203210300202c0005903001c04903400100540a210030009003940d040d009000c0003441e0001180035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187052859 1250 187051609 187051619
    0x180a0b1e031611010e06090109020a080105071b15230601030c0806041d0609030a0801060302040308040302150c0d0306090e0f1c0c1e0b010b2b0f060306090507 70
    0x514081a5280c4a1001c0d2803210340b15068031580610000203800c2001140071510262403a003000801d4034458541e944130240300c010350031700c9000d80c8001c0000d58000c00ca1417030207100c0200501c0b1100f0405c164080044146014444034546e40c0e46000302c0c44400b00004060441c4a0712400308030425402a291524001545580a4864050704010607200c080316a5140002c110062003001c03540300d8442109030580c41481da00f0000188104840c00040d40e440c640c00c8005030009105902100070580104020b100056440d0103607000c0766070589180341003001444010305203014050030701040d4415841010103180d8540c0194003240c4150804202e10190045002e07103405141d22a0105503000c2102c22004500e01148000b441c52075150003241d010f0305544907209502100c80203400300c6000c4220005110340e180b1082d00600c009000d1520303061076500c1e140346140c0c10f1180310904005c03007013014001d000300c1d40240070315590310042080003544a281c40d0005088035402510310303110300200415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187054109 1250 187052859 187052917
    0x6090302120c09010b030705040806010b0703170114041e0203040f020f010e01020a080703110303042a120f02031006030f0b060301270c030c06030b012d0302180a0b 72
    0x1911406401d03c48103a0a01c484112039070f0015040da030401404000005e030025047c8000e034060140118106d9440303c003420003c02d5801c9030790400e0a00004000104031940005010f1040e0782c0c42a20081040c0e41b888065058511001c02041c040d00c1c0000b00700010445001441d00501d4070888941c2c102c001e0000046a40b401203c00b11800350341304046590101c0c1800024000c142c1c131078500050310840080041e4107541050383c0403240c041c46901808202800300b058a011420000041000940b404001181401545401504024a529903003043d920309200301d011007010b03501c05000c45036a0f460700d960002280724090b2240d000e40b00200c1d8462506005080e0f40381d10100000f5148134070022088100b824044046584106401e030000005101c2a5054001c02035501d0009400351503100240ca00200c0504801201102d08030f0b6000d00051500034640442d5240b900580390088100715008007110f00c0340360ba80c401c0d021400001c0034121300006054400103050050406544071248032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187055359 1250 187054109 187054123
    0x30e01050910020d02090303190306140d0b0405010b100e0a210209091504060b010e0d0b0109110705071e210605060d14061503030c06010b071b0609030212 68
    0x16038103030401c030082000982d6030b401030280c00c004840010b180200c0c0000003891680240030f107c0c603200c141036400300d0054143c4140740052005070486114181ca14000030203449141c0b200901044004002c075061000035400b0030300c03294026159201e007650280313000d0418075035180602c3c070580030000c0100c0d1003c0c0c8085039010074802d03104c9215142e241c5500f040355480000b40040490b2240400c04019101c1e14002da501590040c1c1300001d4001c0300a0004202c5d01908601a000c0e0190400890006070f4540010b41100d400b140002004400c0140c02c0c1803610a20501420340d105030000810000c0304100f00c0ca11081242040064556035110311145119084080b040030350401d0030b240d00456950381115501090040c284003072480da940e2100382480308038a04440c03e90000d01003007417010030a030b040800d550007200114113141452242e203944450500a0a04500703000c10b5070030030080200d04010410581407001c000c460389500009103d00c10501c070a0b88034204c10041514126400300d4a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187056609 1250 187055359 187055371
    0xf06090803030a0e030c0304030803270d0302160b0109020a03050f01141e06030a0606020f010b0306060d0305041805070e0103021828170c03030405031c02160e07030e0105 75
    0x2440c2150385860381d203c02428000b040d030046000130010480c0420381840100050f61107950600d4903400e01c0c03002d050304c0d4012158400f280c13002c440b100400c0f0420000b9104140580c0d0700d00980d880c000d2101c0900743d141070034802004007541c0000401c6080d0395030003415240300203603006c100c696a44101c02c902803d00384a5010090108460a6014104608440f41030a20400d4030307807070841d50002180c0e5036401120400c0180c0d81c1c8000c24000c05e036040c0941620b013030941c0c00a000e030480c018002900c0d0031003d80a0340c820300d502041c51741014050400d43c1e00605d0704200700044071f1040750004002d0802151030000003441444602e07a0741d03011780b0942d511034940308110750120a2140070301019514080c7d071650701501401030081200c0e2146600c801810329010309101940e80301242c20b190030011090140701c0d8206100500c40e07600c0c0010003041c11010010340d4403c2304002c2c0800d90030100509081c903003004441202103075040c1c00080c5a030058410b50b8042048103102c0011900f211000d49070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187057859 1250 187056609 187056613
    0x5060d0b0406022104050313090b06040504150801141f12080c0f010213080105010909050d05183001110414011e0206040b0f04021503150d03090f060908 67
    0x8074000c542c0c59406003480c42d104584864182600002c4250700101c210341c100d465a01c002036616007100f144002500500490030184540f080c0840007400038007aa000d0540602e540b50b0000b4140300d0408502c0005004200003008200c801c10300020b604030080711010b8902c410110201090444a080d12c07040318880a41900c090700346a490080390340c4950075100052040c40c01d0003a62072000c0c8001c00b400b01400c01100d503a039141118540c00d5810581c080c0c3c01d00c510f01122034002c00d10204187c522000c15140144d80d440328912200e003c1061b140c0b849800000090221074031843d0780b03082003200300310b01da42e1210002100400c9070aa4101c9850740000700c8051004001c0050382800902c10103030141041007050113142d0788000b00c1b0300060400b00042e40600709000c2800b140e001402c0d04070a11640000d41441d00d60049200e201005001c1c0302d61190010008010588480441900b11001040c5440007406400d0041821a26018040420100d00400127559015211030401c5443c2440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187059109 1250 187057859 187057861
    0xe070207060219020f19140303030c04060e031002071a1302030c12030409050906010e010f060905060a0e0301020a172a07020103061e0906060302030103080331080c0105060d0b 77
    0x1030802490f03a10b4036040703030081041009203540366180c48003441d0b598130100c01a49400d20304014650441c000c407444600036003042081c0089ca001d200100d07400c2d60001d052040382c80316034802103440c1020448038490850320224402c0d08120240801220901a00140e19880c2d1920800c11801d41c0030303d03100035030580c0214048505818020382c00c003607810003103050300d040c2a41c43c01280d064440072a40098240c1003d03005110040040b0342c002c0c09408100c401070713410740c1410005000b09a003405031f50f00c03801004c200414054440c0019070040c0c14007078000e6440c5d00f00b028014104140c00d04c4c042080511640004058036845a813104120b0f007455610201030100035045859079202500a07410191201030125103005c594038054080085801d40108080c40c01c200807040365255000b00d010540108010000b0443d603c0969401211442006403940042a41c40305142c56043d09030b144a004400440148134000000d88003d00e03130341000380042d580d500304004070043c0c00b040007440012401c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187060359 1250 187059109 187059133
    0x302120105043b030c0618212d07050d080903120a020729090105070905060904060e010b210403050a0f020a02041404151b0309030504030206130e0702070602 69
    0x2016144044402e9880c690010702140034184c110b901810743c03150b03298040c005000c0f503c0d805050000304600b019014002603605e105203800000410b1503140020b8001140c0316030300310054400c10a8181c5414041030303040507000740014194101501c252000e002e002075030031000d070190300424070406d18100550b00e82038a012602e40e5040c0040c0031080c1060342030141c4000a8100c0c081a804429140204082403000080d0300d016400000c28028041e410007061040e441d41119006041d00c004580240e2621142004240101481e9020800403070003007000080ea5070300c05004105140090b100c0000c44911540c507a030b03d070041610000e0004504000502d80a4414074a02d403104e0580d1045e5039031074480382c0008040c0d03490f49003001020351030242400200001c2c01d01805402c1c41401c400e2155154103c5204200ca002940d90b805160702c810000041502c900c0c02c032005564020501500c52245580102849029004003809008180c0220b40710600004414080390303030a60003042004408 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187061609 1250 187060359 187060421
    0xf1209150c050405041d0607020a0206040306110d050a0c090f0b0426070e0717070c0201080c07081303110105040803030c0d0207230d030b010e09040311030406030212010504 76
    0x30400d1004201c1c0a00000c901030ba44c0c1d01620300c0713941e003d80b034803802e0034441b180c41030400c04080d005105560060001d00700603100d04081e50704030398104c1400a448100c0040349400c0d88220050884054a0b02d0200b1020104613803001c1960003aa1f6070305040c864503034046880611207406049404c402c20301c02006545d12282c1c3c03001850901d030103100005070060504070b00c1e000745078001c0d07540c83c1d00303500410803026480414500440c84c54241500641441f58000d02001c00d2090047e042140910002e909070200c0c2c0219550386e03a1088401f6580c049140c01c81c0121009030004680040400903403523440d41c400c4050701c042d5050040514599241c03000001d1403030740301501e4241c4c0c040c1c00307020b8100031445c40103880100e00041d4480c81d402e007101c15090382c00e010b403c01046003403500d0000c220045903402f4801400d8000141c440300c0141c1c9540c101900c02c599038141c182002e1100150118015905030054005064402510341280c3d880720b0800081d83c409503c2c1d80c40b0f000d03418081f400f1003c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187062859 1250 187061609 187061621
    0x180106020d05040b07110307120606080606092511150402030d0c080301090c03091505060f06160605060414070504030c0605090108040f021f052203030f27060f120915 73
    0x34100e62406685090340c0300049e01c0c424081d544150f0b06c2c24100500341050000c0c0fa8043c00031035055165190040180c0d60081003400c2e281490044c0e00410b0b41010300448030360300f00b044034108a4801500d8203817030021b25081103070101e0180c001c1c1400c0d15012401100804443c9a00c0701c1010f042da800c0a1250004010f503d0681c002c258035000c0f00c40108403440901c40e0000f00381c01340403038940303007607801e010000c1c16090700e842c0510741c2001100035000c07090681341400c80e4003604c04102902c5440c0001c000c2c006401107072201a55003400e022011350040010000c80784144000d1100c0c41d41c1c0c0f1000e58060054400d1907001c202d030348000900190042ca04001e110384001e00c2c00c10380d04454000950b21620040003640440e0307000030003900140554040e00d0b40000140e29910b440750550380c00800160b8205814000e009420b450b559842c1c1d0b060805120350701e5004202d50b001552130300020b00070f031042100400401c08a0560780c2c403a58480c0100c13000c1d1394004818886007855008103400800c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187064109 1250 187062859 187062893
    0x190209090a06020a08090606010e0102100b010e060a02010e0d090303091a070c2603092107090f0516110607050a02160f060201060f030b01090b0a0302180106020d05040b07 75
    0x41d80c0c031550005025407000e40084c3c007941d910f07002c0901c0c0c000d5019140034809000c2c581445000082014030360f9001910707901025990748042002142940180c03010311800d10199400900030680103c019030560025a00d41c0c0320504850030720b030760a4030585460702d8500014002070140c010030302c0036603c10300050804d445003034100c078504440c544403164141005c1e0454403904080200d2541014003034100740c1c031205612009185860311880000e4902050800d00e41d01106140600b154030990901a120081c100c110042c4039110050365039600a050407035189402c5806804000c0060384911000c0c8841c0c4035510040545031076080f01511070b41c005410003000c61041c040301204410181100200900207854025141c5040180190a540581d00012800414940b00b040440c1286004504507004481c1c000b4242900d0350110384840d035150070194001d64095210b200001c03603980d800d81256099429208540522401102c940c8600e20400344541c400b8003a40022503620f41d8080c0c0407036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187065359 1250 187064109 187064113
    0xf0318140603150612010f050406140d0c08060103121d011d040605100203070b011502100f0603200901050108091b030109140601030b0105011e0507030e1f1119020909 73
    0x4082c3e0b00003810a62010a064602480d042c3c010414820518200c402520080740d042c0141d506200369800c0034610100141d108810540c101428445c2020f01e08002d014180c043e10815038403800c109140404903107884002451040015450302282079041c04055030580d00c09818401c26102c04411008101845500c96aa0385001510b40c1c4ca0000c0d00700c665245402840c1c60304c18904190119440590081c00c40155180d03200303c0107030340483c400e282c8014070328000603002e007a4646100141000d400080c19041442d501482004210540f07002c2c0394000c9404410b039a07203c00c011601c0000544001c0e03081ea00001010b441c940c440c4014820015016000003407075034680c2c03240314111072017892800d00c5401c0840107009120507000307040d0241c2000c0c00c004031846070488021300c9009008421504116010441508151084024496840000b00300c045200350032000c904111400240c2400403451007a10501c052401207071030700c00c885010b2118503424640d40c0a12845041c0140302c409a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187066609 1250 187065359 187065391
    0x9070f030e1c02010f0b03060c0c07080d03020d0e0708070605160818030f01050f0a02071a0a060801060509010b1602010512040501020a030b090415020a030e0a0f0318140603 76
    0x3800030030100801e603004000c20782c04080d44100c0682101c0602840340f002c03038100168603079035807800210550000c010340419996508000a00c40c1003200b03e400820326805000003c0a00581c10740140c4442d1b00e505004022082c1009881941c9070500d2103060307030035000b035101000f000b400342d0080c0010f03d0f059191049482115690240158400e10058587d07810f0300020040b0381c101080b0700580c030500b500003040242808810389801c036600410f0302e074405030002a5241041003641903401c9000e021405e940e201c5c03c02030324080c007500c43c50188007203540c0303420b100040da0300c4e202030b04034122184040007030f18100760603042141d60019850141c1c10320004102c1e0601641042c08030511807400b44c4001601c480210800030103440e0542115882040301d4000c0c400800c141803001e0400c602e500d40010383e9100c2011080d4003400c0c1d1040b0070324942c0102c122003000d0010340c607088101580b20303075100b121140d4000080100045030340500d044030404540c150a00342086002507402ca0414541e001c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187067859 1250 187066609 187066631
    0x1d0a051315021209030c1f0609091115040f030210090b0d05010302030c1002151005030703030207030b07140a0e010e220c140702010c1a0f1b070209070f03 68
    0x20312001d0076028020700e40d000070251040000e2045944d081400c40b0b02552918000780d60b07040c0c4d13401e0680154a4844464016080d03580040d0744200c0040c80c0c40642845482c070181000c000380f691000e482402000100e40e1750b03a88120042c1110140c60351051200d0170305046400780815034041218100502003002c0002c00d400c20118081c151b50700e40d0300001f055960551051609203a07405039071031300400050001006054011600103421140101942c04030380d940d00a076030001c0c2c0c813940282d800d03003d0820080140740d40030a140082e01e00900c161141c03919210700489001d001c0b0340e40080d00300001d00180580340e210750466800101c1c1450b042c02140c522400007000c603070f082c2c040c404905c0e0302c0c239900518064845c0280c0c255480b00d4240b11480c02c4203011070445074440c8200007070402103480388040400603560002d40c865841d40c0000e1721246070074280e61405031300a4803030b0f580307400b09400802c240350000411903400c280d0281850309240c41c1c0c42070a072001442c158101042c140c4034008a10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187069109 1250 187067859 187067873
    0x304060912050307140619020319021620120601080c01080903041a040302030607031415030a150506011404030804060f030912030204180612030c021305130c1d0a0513 73
    0x3051700313440b4010301502c2c00c22082c2c0a85150301c22400c2d40400c0e00520410105142c9003074a452450020340002d40e44500504040341c00300004000184a004d00c00f081400795600c4e55040149420240d451114481080740042e640d02d40c240703e080c0003a88400c50308001d80d4401d00305181c000301010100c905180c0c861003e000d004080c8002000d0742c03a40458204150b24040111a41100060a00304030b4140078000050200300700500d00c149030303c0140f510034400d4a081041c60340d11604121618010410700b07159801408040d9442400160ba180111031080766090445003105d40c0305c15018a090f18141c010b480300c400b005002c070240f40d664030060000c110001000d0052469641e0b0040c0c1c0c850404192a65100803820040303da5440c10a0911002c294200c1086485405007040c0640c182c503480029802c4002d0040c5142080c140b005000c03008100ca42c01a1b030407131040707505200c015154514100010891804140c03c40800c402145141c040c070f42c090381d00101c108510300803803040c94807440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187070359 1250 187069109 187069133
    0x90b0a090237030609020a0804030e01020712060207020a0b030f04060b01090510030c0917030d0b03070521060106030902010c06090305090303070803090f21090402090a0b0306120304060912050307 86
    0xd841d04900a907515400303a4103220b1803010300045c0608605008040c18001e1069034010070003801c0c04040550781c580350b0300800c0850020701e07441e00c88018105c0c641c40c020010f0341021708100d01070b191124002c54098021020b991040c007000044041c56500c544410000d0040300001e24180081e019001c509900c0d100c0c1c144207001025100407660004d840e6004003160f0050340001c050070040d040101d94400040102e03043d511700c40e8800300741e20f407010000909010072940003d90011003070710301c4608031811a05040c1208803a0064921030780e07807010240c003680c2402070001d000031544074010002a155600c43d80c0c106001e0715100b1309000103100030074a10b5009100550300e40101204100c1c51090030030100d80d113404180080e15003607080c000c0304e09a45d01162050f004580c400311380c14105498a5050307420120740280041812552408601c85a90050301d00c00c0c028070040700901e420034070000440e400c490b0251764000c01d50f4070300120f83d4140031102c0706c2125079000070041d12000c10340628000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187071609 1250 187070359 187070437
    0x150c1b0303050f09220e0705010914060309120408210906040e09010f020a030e0f0c03060f0c0f0708091e0f040c12091202060703092103021201080c0a090b0a0902 71
    0x514108034101b1180ba210096000c2c42c104209a003050050080030700200701e0040069503a81c0d2261140c0101d603041c081e42e1012103000e040d01040000f0060000107040c1c0445404413010f41e60050744881d8440c6a00c5480161900042c2c100010040074015000d40d40e4020380c41c000001c1c14804808a0318141c3e4840703108000004e8031100300e21046542884602031885140c001418038580d0306c000f0940b5808028000d2481d89141400036500c255400c5c11a2044203550086c40d0742e59410345000203154100d812014003030b41080344000202d181103c1e08001d080d4000348040039002440080002038145413500702d0800c0b80110b52510300740f8240c05854500c62060b2005281c003c02d200c002482c1c00e1004015008040c241381d00000420324490400310021007031186440c03a214a19800d90180c480c003004541d142030340b0400051004004160480a03c004465601c80e00ba59802180c080e500c0c040c0e0200c0e403000300c44004004130303c410785c020010358004442500d880f41c00310303041c01440e6203071140c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187072859 1250 187071609 187071611
    0x60c03180b0310050303030114010806031924020a170603011508030301050f0d0f0f110d0c080609010b090c071a0a0609052412010204150c1b0303050f0922 68
    0x5111a0300e401c00b0f10407000d050164021030443d0f142c85201412190711800d128103000300c030008124136031418440300c08003c40b034050229500802d0701c1c00c0d8011400411508400400601030300fa40b2008074001c81e0007001c060f0f5244011604540c0d500e40c0b08040151401da4035650307030080300035844034100041004002d10b0740070b561a51300d070505005210300e00d00b2402d0300c2445007980d900c0000d00e20003103c5040c00d030000c0300c0ca002c4015038175109504000c81096146d00008203a000d108015100504a055942c6031081e074009481c1c41d00301e68240c0e0b140754211139200d44c6800000f020342c1b544501406003207020b541c016490741445000f003003210380142c1e0200074181d00c455040c40b0050060040d10f41081210302d5103200240e1100f0400c0445e4900350071b03e48a84c001c20782c107000c1d00100350140c0f0040c020003085014042c4038241c0250540d8002da90032606965a8440ea0b10402d030100c0d02c400c21241c140e00c600c2d01e89030804040c880c0603806900046d0341310494007001c01c4840651240310701d401ca0301c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187074109 1250 187072859 187072861
    0x9030f06050c0c100f05060f130c0c081603031d07090e1c0909050718060c0f061d07150818030c0709050601030b241606140609010801060f060c03180b03 67
    0x9170380300603520b00070303d0710b0301038000485283d4481d05d864410101c0e100c2100800214440b11070301c11900c040034108046c001c0c2c0e0000c120034180c80701082001072014481c0c1c404100000403000b20951112000c0d20b8551345400c2500c04100d000c01c00c1c0c00612201003000c00f1f465030040340c00040c44641c26103c0b030100008142c1d10040c0704010140c480e19800c580c01e030420b20307a0194100900e12100c03541e4020b01341044290395848080002a00040c00c00640c008010f2141b40c03d4007417051801e6108127001d01007440f441c0f500098100398a0402d0000100740d80d03500d0361554803508a03654540c1d02c240380b6601e40c4010414800c6029003401a200039112807000440c1608020700010b083c0c500c0b0202441c030414007290181c01031403690b18429110340c0c804020700c5c0c0300d0301e014005008a2080c8107016041d21308051400441c5034051465a1040d5011510980240d07200c2031200c1c01ca070500d008100407800303050b20500c04240140c0650f041d06100b40340c60300070034207030b1018694580c00a034066601400c2c040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187075359 1250 187074109 187074131
    0x30906011d0402030705040c120603150c2a020102070e070302030a060617060f010c06090f0b1806060d0c0305010c0903060c020307083108030904060609030f06050c0c10 74
    0x11507100801094040d1081082c14650006512002103215040c4265603503080d080d60f6034003070210301e004c085641204003d202e83d203003011200510030f81c000325026403a105021303050500a0b00034210a41c07a02004020004a24a903000c1d1342d411002c2c2607056209071a40000e8444000b6038681c1b294445580c05601da040010041f4180e56880d006030050100703460000100110038420141e00040c22100000c01c40c90340d41c0140e0314828401c1c0041c0c0107030701700044c0c0814044481f070071040c1a40314110a40345540c0f00bc610100b44050003010003440d402c51400f00c0c855252410044600c28010b44803001516640d980380390840d1070b1140d08070041560410300704140003a500c19500c4120150010314500015503441083d01d104680d4003010f051444074203000341458007030351042c01a009040101d0000c0c0c8900c01240e5a0308a40d1610384107508121000c1441441021840101d0768415840b8031181c20f10b946a41c082c08000303010f86615074051040c1180810200000c00140504140004a6030110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187076609 1250 187075359 187075379
    0x303130303080c04240315030f120c12030e010b0604030b060f04050c0a030908070501020f1803070b090f1f050c060a060605030408160204050a1b0201060b0d0f060b03090601 76
    0x803c02c00c00e0701c01c1813004214030881c4013040440c1080680c0c01414580e40820300781c0050031680d0500c07910420f4404080f04011000c84401035950090107083c0c0206554002154010441030340181611001d4200c0c1d4040344c000d4000c4880b8030110070001c07e0308440800841d00d1900194000d8070b00b00c008506011041c10400450070980d0401c3d20103002501c2c4c02880504036200d07825040303040581d60803405041c440c80030141c03407a0030b80c040002d540c2e44985c0200a1700c540c00461750041c401192a480c10198940082c0b040100d4078030f55203240c140205141003087c85083c403403402d50454a25604500c500c0c0c85107030340b10701100c120f480d1552120091070600b40381000003132121420a103030240501982c0d03045800e030b0b1352040d4130542d05507035844401c01400350010105e1000350070909010901141550980107008008809844071a40d00320002e0101c0c00d0b15003c1c8285103403080c040001c02d0b09283c680d0031411440c2451600818459607400b00106241e000325004d0032581c01c428010301c00b500c95 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187077859 1250 187076609 187076611
    0xf110301050903180a050d0c060906020c011e110706080a0f02031e0c071a071b12030b040209090405030d0605220c0e060c010b030d0c0f020f0f030313030308 69
    0x106500030001031038901001a5244260b10200c242d500c003031400724041d9a180f0242c1805410b01602481c030f2424580f400607102180d502504010901d0b152000c6801840010707540a40c090507500c03205425403016605031034101c6100c40c0e20070030140216441134407030700f00075a0009128a030f49a0250346002018001211460314071100c0040c010414005075822920307902400048041c443e440325169010040c1c42c07842041d0004042c00521240480007818080446210f10801e894504070041803104003042c000c2046d00082501c216a012004682d20a5021046001002d040146800760400015038070300c07002c07102141e8a42c80054034505022090003004001c00d810341c4e21200486444e0040c40085910780300084869580d8020a9a040d12074408031820b1a00074000c16644d500000e130790f5001e00001d10006004c0e101c0d0700745038030801d84203404011505400401580c4441c6035942000580c0c1c900c540605e51100c0c102c14888815078040c001408080c5c8102e1b050b261003031840c036000d0000d40e8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187079109 1250 187077859 187077893
    0x3020a050c15040302100314090a05160e1503010e150426030106030203091606021e0708030906070c08031c15060804120903050303011203020c0411040e10030b040f 72
    0x1110b0b0031001c01e25101102510b0079681d045808251650340450101c1c002c02da48111103000d641030100348030307002c40003161540c07095009000391120040620304212085240380315104802c0e41e101c0005101350002c201d1024804001000031034140040c0000500d031001c4d03024007a255040810a0100300400f03041103c01058000d400d038112800208810381e045d000520811043c0340e000000910641d000f880f01c2c0d000c00d440c089540030700b5500c0d224020741d200ca59003140ca42d101c40080800c07065800c0080e040003111100740c01145004068001e00403284c1001e001102c01c2c821180e00800c40714810320140800d83c06140c59009652001d00f542c90681d200012062648440350342d080c003003690702040f1250b02a800c101c9080700e450300041c08864400c1c0d030b50302c050128000400003080440f49054803840c50390090303080320f941480050402c8200c2e420f00207212400f0b00d00b00400c10900810907000c40d800214112031017030450703407600c4000010300700b250111082c6000e000d5910810240400c80ea260407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187080359 1250 187079109 187079119
    0x70e0108010b0306070c0c05090c07020108070305060a05060a1101050f0403090e040f170918090f060c09011107080307210807120203090f1b0f030f0a08090a03060903020a050c 77
    0x42e440c400803940b15a00604164200500d4035206800c0c07041d611207000c02400302801d000030f146401900440701d600541d00c04c9002400e40000b0401a9102e4041d0a01500008101e100403a00e0041000b2196120034005014460507000d8a00404400c7c46039601c6800303100448429440e00b4600188140e2450b0009120206040244008107080000c07110541c1d50003070002c0d2081000b124420080e0144003141e6911811428440c01008815a04a4021710314181140e002e402a00803042c3c54000448603c00841e01c1400800031962040425209444910007a1442940c540d4042425548844401d40e03a844c0c0c06004540131080c808000c54850005261101c1f45051244005101e81c908005040c1402d0300840400c030081024854a1003000040c01110120075004100721048030342d40848034414404551503016500340030540410201290014098210440e6180039041d00991104c980140c50208007000180c0c26104c0d012a00780680c0080260311041e140c9140780107180702c140c60240b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187081609 1250 187080359 187080371
    0x60129130b130801051306050109020901021b190816090204150c021909050f01060c03050a08040501231009020f0d0b030c040516020601060f0c0f050f0d02070e010801 73
    0x10094500c161041d11005160142e07610803150074004444281d03007008005500e080c041c809031402d0b08001e21852032007031405100c641c0c0c1e201100e104034050391a845000d6088031122204160b4200010019994010038120a035614140c81a1580c005a009280140e100c4410101d03000002c030798500042c18000400d601c0c0c141801d8140302240214400b50051040c0f0078007100071562503030a40d1a1780c01c019805240c02c542d4481c4810082e20050341c048030b000b000751001107801031140502208058264039058501540030f0801c40300501d004005840655a4912052007122440c01c04600c00e942840c3d0003031541000b1100511051240d48061642841000580483c050314019035840280c3c9500009024800f4000311b814400d40051013588079281c0b0080001d000d2810341400c0c180c0040c0d500701e5907640e8a1b00c0e0141d8a448029888c4008a5401d205540000e0b501440802100e4490801d44203042ca00c030b0070103442c1410103c6000056084403000740001d4407035065042c01040490024008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187082859 1250 187081609 187081627
    0xc060b040501050a0303180306150f1202030c0105030901090f031106060d0302060c0d020408010c05040e07030209150a020109020d060606181d060d0c0b0a090b030609060f12060129 79
    0x1a1302e0520005051008540705600c850481144000c0155000035044c07202c480305070300c10b1081c4100d50282d248400704807000490104060480032512a9000d80181300200d61040152100d41000f06541030964944e00001c000030115040c41e9041446038840701d0407c000781c490f042c1002c60040c1824002c942d5100b80d100070070750010700b8641004100c101c07503035179140c150309010191041d03400c050215800c12108005080c0e000d0700601c110780c800700c4900c1c3e054031601c508909a110306100703035500240300b486100842c00650001c14240300f460000141e0005164003140700030254050070b40e46c0ba40c1c2c6150803c00e00381c1210b031030100007000d00c0d9200b43c841e060494181107110300b100350441c0c6250100014581e40ca0b5600316103800364108088030042a554850030b00141e03c15044000010b51004000030083d80e5441039a02905000781255401c2d80c490f0203004c40c02c03c42101880d8001c1c3c1110309024484801d1090340e000e0440d14540141000f0800035208815000d910b403400707071000401080d14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187084109 1250 187082859 187082869
    0x1404020910030c02010212011403061b0a030c0909140603010c09120b060109050901030b01090605010804020d030e0402090d0f1a0609182416051602270103030c060b04050105 76
    0x409901c01c2d05002840c076600c1c0904900a0040e031007901c10319030500e03001240812403400f0300d5124090490466416507107a8044036014280c404003d540c0004c01c0c4095010f4501a42094a2980700d42c986412074603a00d41444007a500c98441032400300c4400028802c60781001e00808880384550306040c001c140c5170408040898101c80c801030224113481003c5042070384960215402844014050301c0341303584a080918540800f07100d81021310349801c40015182d4024034403148615001040702c0000040c0f03031002d4505902c0e440000e42d02c21b030308008000aa40d107085d41d002c0d03018066810400810311625040004011440c1c410507928022010000d85964418a142d8455401110403e8800c040b1201d10724281c2900c451701e11410090030010f5102c1c0c4405030180c4184044040041b001030800015070f9107104408031845051615001c201c0917081158511208a46802c020106446800ea24074024803007a0012000640c07421030407014070050f402091706200086034100010f514041c0052 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187085359 1250 187084109 187084129
    0x60e010906050c03090f04060509090f0d030b0f011805040e0a020f03010513021c08120601080618071b0606091e021c18060903180e0405150405030408030a020714040209 74
    0x941700381100100d1b90324607140c1e608084000c1002030000019420101c40729074a415254002e80702c24032440303410b549490710a005039000b9401c0039001800c60b500010044880380c2e0840c0c08040900c0000c8800203040d01c47e44918081c022145001d0f00300c400d0917104003c204070440000c507100741e042070306000b1710100c83d2000c1a101c950444010340b41d00d124000400708000c2e045805071007904085444e561031504082c00300e20400c400d9071052030f01e54900041107400d403d0b001400c600d00e00b0000000c2e0701716014500a80d2500a041c0e00c1d101c0c04039803a03503008140c0307280c1c0e0400304445440341c0717088110361a843c0c401618820000415414004000c0e01a48071007403003d892001c4c2500e5010002c401c0c03081d00542c25085401070018000c001c0c9504002d0f249603000390906030821101b400000d1544281d080245c0a2548800a86604015007480462000c009041929180002c000000d44031004200070051041503030082c140892500c0001114900303416111400365004004280860303440e40004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187086609 1250 187085359 187085377
    0x801150f0b0a0c050a0309030b130f020f031e030c010c1d01030b01030908030a06030b01090c080109051519050301060b09010503041b090c02011d0309030a030806010c0c060e010906050c03 82
    0x15803a4103090b1012a02d600c040c0d8000b800c2030044c01e083d0001e041d8000060000e80f030154917084801d84503040a4040c00c0d850406c050309000c13003e084940113192100c00303642c0215004084071046141d815500d03056099440e58200c40e03034400a007014407a1802c1c080d41c07080050f20300700f16481200c1005080364581c03d620a144c10103580f034290790940d80c0658010440d084c1c00c21041603c901c6c1003000784000740300d20f000650360040280d00015114950b8040c0380400740050b030308c100880c1d181511400113800b014000c1c206a9062504009140c0c0b10322a08411040001c2d5501728150310782400d1508440a54000444040e0100048181a600041240e07041b640c01100d10702c603213400601d1314141507a40c0c0c200241c02c034104004100d00d0b9505400c40304031140a440c06074041c01007088984c1d80c03441802c013501d4040d00701c200080040780c0149001540f200c410305140821901c0c13a03607105150b403003a0f00068045042d80341d2441a95038446041001341c006424042e02e4920f403070300c01642d640981800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187087859 1250 187086609 187086629
    0x203090d08040816050709020319051f031104111c0e0a081b011518050a050402151e07060c02060f04031e0311030108011e0204060903060b03010b15040801150f 70
    0x10203042100070402d01b401814449421520303814180211062150031030340c40c403da03a081c9404103c002035242c0703203101509812160110345515550b561081140301c0c80702a617003c1c0d510f00094005010b04401490703200c001e18603480781c84611480c544112680c86104100543c041006940000d000101310341c04180c50710360444517081110f1784240940f02c1c207c10240329022a0b0800a405e10f0302552244031002088020b1000342e49803c01082240c20454000e50f2121400070a041e8901040c00105400300140580c6518040e40000d003103000e82c082c00044801c5039542280c0c0d00c80c00c0d41884445d030000a04240e058003030602d0f813001440e0f81c04184103510000525030110041d01c3c0607500c924540c25200105984135030b51800c40c2030081044145440c061174402645070305c038044a10850f0103440140c0c0720b4402250454030b8004c000d250102c00c403a0550f59400c0920403e65070f1100c440f5080801d0003080d5034803418001c18a0a541c10100c000050408034074050010081004400e0f0540d43c0c0060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187089109 1250 187087859 187087897
    0x607020c0f010c1112060a14040c0506090a030605160f030c0801052205010f081908030a050a0221040201031107031e05130b18010509030307030c170d0203090d080408 73
    0x200042001506000542d01c107044c24144645605c000c82e01d544506072006042016441100001c0c030301c403004980051003203d04480521240c540007007d000001c1c00a40801c00b03079500ea0351500120b40c4191585400c00981714042e040d4140d010000d066210306a250522020382045005840c1090600541b48200c40e21021000c1d10b1140300703901003071060000c0c4240b0940d651101095078002803030080140501468000308000f901d41e600c61258640c1c008d5140d8036644d1030844c102c004080c040c1107a0000303502000303000c000000c0840021340e241c030a03003210881400c0034400542120340c04021a512044140034480120b0340151210403160160720340314002e0050240111901d114a101c00d201107410703000d010401e400403001070040c1281d102c00003209480310070f0043d10540035422085a0651040102c800040d20400303100340b0309889880d480e13541c20121000904581c001540d02500e243d4003204105229000300101008100c1b681441119420305403101212885481198182c0d020118 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187090359 1250 187089109 187089113
    0x30406090201140f0408060f190c021911040c0311070b0405030d020a020d0e0a0b03011412030a052805040522060e040b07090e01050118080a11030607020c0f010c 71
    0x4441d06040f40c0b01c40140c1640d503042094140207980043c040c41416100b1180002d1410307120070b010501038a4110800305440700d142013044090104880000c045015400d240038121541449a41400d44202c0340304a42c0f9a943d014803084602e50310b0440209030a2481003100682e4100c22503506940181c401d41d034581d140d08000745544500c5004078000780c400140200803560102d90404a01e00c282c0e01d2415145d19502041081c80e003d024480c4030210800040045602d81201912032210280042c00c0210013540c4c00e50642c0c018080e9a00410400109988043c010500350014203030714141c111201404030300c0040c214010381c010303107005050304501c2c503041100c5403102680c5070107001020b215071901c4000a250001d01505c0c01c54104203c480441c8603203000f0b40000301a01c058801c801c0c100d82c60000110703000400170740ca4011007c101c90000c0351400007480b06903a110700416000801203200001c1c1464070800070807510031500100910085982d42c01d01c0f9102140003480c2c0b2020042181c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187091609 1250 187090359 187090367
    0x4050111070b0d0501050a06020f03042102190501030b01030e03030c1e0a02010f050f0f04020108060103021c2a0e0103050406060803031807050a0501091517010303090806100b030406090201 83
    0xb42c0040300703a144041001d81c00b140154000e18140c82054507801030485e03455106a0b6101810f84201d1265007050009200310f104030011411600e107204c2d03115094980c550082195803072600c1540c416104005410302c00d0356014050710011800a10307081042c40c41d41c0d070900b902da02001d003481140d2080003c0c0344170020b04083c912101b130711440c0f07500c0b90380d9050484007900900402ca216a05e20307080400148a840088020500c1906a2814031302c446d5245e03401145d041400401c040e05041d4240030207104108078440c0141e4084501d14009030040d894601c940c1c8941441480c0e94004a08080d50200640d1000b4400c03101c640071700b000b08442c0c449142442c003414041d04100902d00c001300070000580d0001050b0f107042403801c4181c480b01c540790414014a01500c1c05500d001c1000e590f0200020015142c411030b000001e0311f40b41d031059a250843c40d1403400c00307034010742c00130781d40103400e200a40c02408559004421559184242403070180003a5080c00700801c0900007558031480c103c250f90113 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187092859 1250 187091609 187091623
    0x1501020705060c0607090e0915061504030f0203121314060909040b0601030b0f1c0f0f03111501050d060c030e060c04140306090a080c0a08031008160b04050111 70
    0x5052540720481e50580540d1000d045841e01c0000e6101b2400041000348008124011906000a080d00b07104200b40c618400703a014107042e81200090662110f552000c030b014002031885510482c0002d04c90b03004051529901e40c07040903400004000000d010b03149140300d4006c5801c000640e41c2c5582d11840010460b00a4101990708140800100001c1040410b013540c0b00d40000d0320100015240030081c814aa0099000c1c1034002c50b0829110790001c050381d01543c01e4611810408216003260755031440b0028144c4011004142c840e115011003590078809440b100d1f84441e54010103601d4070002840710310440a019003030315a12002f1092142c0b10b0b801c100c0404015208944242c00c00d0844145540c0c8a8403a02502c0000349910041e14034000ca075041c0030741c1405c8e0083c00c040109403512079555014804040d01403040d00e42501c00160b002000d075100d944880740c0c41e05494905886a0300300300030301102800c9940d01c5042440484008001d031b4064641c01c2c030340204000102c200503854440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187094109 1250 187092859 187092869
    0x4090c030e0c031c0c0f0b060102190309060c020a0906080a0b0a1a01051b01060608091209030a061503060609050402041d060403030519020304060207050708071805070c02120c0405100b0315010207 86
    0x7661b60f98a41408144401d5601804080c0c0c2116104001c20b10b040401d402d40c1c80005002901c40001000485c0c419000560383c54001403500342d010b669003d048040b509a80d02406564008409507028820b10a400507071024200b00180095000f0581c08102c41c0388a1441e203060040210741c0400e08800c102d1000c03551600400204800c070349503000a070400000321180750b40c601c25010034480b0502034100351904240d002e00142071101740c968829018100c103c60600b8081064a0f00102194032405180f00802541d600040e039800d050041c0002d43d844540401030783c0215070010410040006000381c0d116416181c0041c990325060b501c440000c4203012107a402c0d50020bc00d02042c4400740e4000c2007498814800c03580140c1e903d00071a82c0340d44030351040300c60400c409044159045280d40095910004919003001000070540c00110780041034108440c00f640284041e905905191260700e03040082c20000303079250b900d001d08654141c807000b480c42c002c0440918100e0100d9000f08442c1010344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187095359 1250 187094109 187094123
    0x4080f1c02030f0f070c0507091d0610090501051c030809160602070503070e071b03170a050f3607030f0b15040207111e040204090c030e0c031c0c 64
    0x2003080d811900c4202e0301602c500913115444004240c200d40030b411300c03507043e640c0300d13010b000460b00d46007004004040ea490084001020ad40ca0803500c610f05100b181c0c820303040c1c03020380640a814207a283d021282c058100350b024941400c51490fa6912402d1b00a000130b5052407c05155950078100908000e008082074100004904e80400d00e00d4012402c40c00f9901c0660454606039070720341c2010f00a0b042980d030500410248003694140800c0306d101009014024200350f25166150320652452140854030b1641c1699200144149010803e0760144c10040110415208170307125075200c221810b04c841001d509015044010350210014400000210b802a800f89000c0149080c0f440324010101c0705400080d074109603540c41854130740700f551500c40c6c0143c3d039840241180c106000e9503188210300780341c4903500c105000d01c80b641c8900040000d800707101300102d840501400094241c41c3c590071008003a8002d1426001c1c0740d00d00060114081c49940c00103c030b00070001c0402c0e604403c02c141e010707000d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187096609 1250 187095359 187095361
    0x16031e0f0611040302090c04061704080715020910090e07051303141e0106030f06020a0e12100e010908090910030b1501090803070b1b0c010207052404080f1c0203 71
    0x20300b0160107841142d0090780c500f0303110b43e110b00c000784152003030340a00c10100c1d40c100230541000d0600c00c10154028420107029240403410340f5001c42030041d04000c5800c0d241c0000e0780840e1400c106110401d229064140010754508100661141c04001807403101044008541100d075040404040c4005582000b02c01c0c2800390403118250315034803184411a40a8031003807152000c51014031600044907046450045050300654440d0f02952200c0891410002c80c0c1d490204507035260008440c1f500c1e2032200a185802007610014150344020403280c000ea4507105d00385000c0f860f403070f0440340001c0c41111103d60a5132402881c10001550390000340c4100300b05001c000910100b15208058030000f40c881c038100c3d07507440c080540e41784a014001802102c1e040081011210f00b080c0200d01080101442402c14281d69003403401ca80050105550540c01800d203418101c0249122422000307019181c1141d500c0c0c140c0301e119507486050340d8a81111000204041c80100c4490030740c50076000480290341d0703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187097859 1250 187096609 187096631
    0x100521210d0203192313030509030d020a0201030f0b0a050607020418320a020d050c033013060c08040f030602030a0e1b0906190305030c16031e0f06 65
    0x448620b00d9000c00d90146000303440c0d1041280c3c5000c07030501440b8072049451030b51b0792401032514080183c800700c06011060119190703230354080c0302801c200b44c055401000303091060300006041c0e82c000500c2d840450f14040c43e1218503141c50304010191081915003581d01c0c540c91011030010b101000c5501c4d000e011445c4010104030502140700c10500703903844d040b01c80d950035032045503006c3d00001020300103a201c02801d20060034400d94002c0303ca4058410f41d01a0403207100402d081c98402e51312a1400003140820900360316409041d21403055a54030707c00e081111064182180344518010b010501000000f0002001011021940501070b0310f98100e01080c2d80e80342c5103000c0e402c1991013000145c1000c4241800c0f00c0700040c40c010003000002001c01c4050008144000c0c00d00c05082070742c001d0440c0720b144140c442d845003884015885800250380d0350100102c41c03402c0282043e50f480796506120010408070300a60300108401c0c0500b9480d81d5810304900e010f88500044142c01403c0609026241034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187099109 1250 187097859 187097881
    0x30c06041b0608041112060108010903031505030303040201120b10090503060a140105062d04030c0611070315020702100801050f04020c15040302100203100521210d0203 74
    0x8080d910072655142901000c484060800724103014550000d0941030001c3c0114100b01a0209402c601070070b8041180e42c90014141080000d03081040c80c1ea445402d81c004259061050140988040c2143c2810605000000381c0b80e00c0050000f03410010500300552880e100d40d8400700c441c410003410901124a1803102030511a0148117040c03007400f86000243c00c900c440c0c09074509802c074112000c89141c0c24541001603d0300010601030760030280444078095030300d030340300e094885294081c2e049845601e58600302040c1c0d8466000310040040801060100c42c10006285043c0da911031603030600c5945129806000740905100a5407000c2d104614003101c0760450700882c142c4000b030390b0100f01c2c0b02500007440241d00c2200341c1500c0301d43c011802030184144518000703420071720902c10b850190882500c0d60b010307031304262001d1041b80320301c2c01c5c10880b03031a080746000e94854410140040d00e20402e4003094540000c6d001d0f11500301a016060401851400201c7d031042c40c07580e10440d1241883c4018075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187100359 1250 187099109 187099111
    0x1801050f0f07020105060d14150a0b2b060c03111c0501090606020a0b0403020c0d0b091005130f03050c0d0201021305030703022206090c020f010b060c1506060705030c06 74
    0x9103140c4641c1c0c00724142c0707803060060030b111b1000500b2005000302299984261040c13071882480e06400b4220060f07030010b031000d1446006031710290000c99080503a9041040069482407000402c4081e1600e00035104841044c02d002340d45c0180e000200c0102014054025200810744c2e00e40100000a4030084034140c8400d9a801400180c01003200b031780c070350b00c6400440c1c100d4010000540d10180b11100007400c002900d03a0310174800d1040d150411800b03004160140f000c4c0b08200e03445040101000b1000c98108050010814148402d03c41424003011428103500701c0c4d03030042c0c1240d500010b500c0525001d2800c941d0b102c4061011901c1910100500038005c0d046160b8211110581c10400280d5140c0000c917802520303001000c3d000004804c58010904c56411007405821035240e034000104504240f0400c40000401e0300034102c10300300403560700d0031242c1e4103041c00c2c071804040c0690080c00c180015540501c108520441010303031a040c0025a050217507100082003440b00284007181007202203641 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 187101609 1250 187100359 187100371
    0xb030f2e03060c0206010806060a09050c0c0609031b0d0c0f0303110d02070b010b0a2a02030a0b07020c01081005060c150103030f020d020307081804150b180d0503030703051801050f 79
    0x85d80071030b40c071082c0b21a00c858003614140d61140f108207091103041d4099101540061295003411300d002d462500c1d030343c02c102d01180c03000d40e144c001080d91050b80441c8c001880d030500c1d0f0345000c0c200c02d400202e07020f0400d20f100c0e8005003800324049004000c26000341d00c102c5071480d100f485039031a1304003d8039040113503100c1102140e0300b580650001804805400070358034445003980311501e103a001641d0809007594207041100b10281100d20b02400368070240400c001c801c2c061000c400041c03030300030380207031900e681c1201e401e040000386400c1000f981e162101d0340098070750840b6000c2d910150000042e1501a54079810301455070b50304000001c1680004010701d148205400b65844114028000e9031039004140300900f08507010850b1102c4410441d0841c074030018000c3c0000740d0304162801500200c80da940005440c940c0020b020006039106481642c40c80008503500b1f940c1908036941d59459000150000081c103844d180480c000c90100b1003001e000c001010000c0240340b51585051045500940d11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 187102859 1250 187101609 187101613
    0x30a060504020906090405060d0b0c130b09030a02040b04060b0c0601030311190609080d09050105010513020403050a12030204030512070b06040c0206070e010915090504060b030f2e03060c02 83
    0x400540c5042500a84191503002000c59040550134018840074080081510360720a002c98040390005d40143c1209004200080003a41c031104400c1d6000b00d00c0d40c040e040402000b4060100c92025038000904242e02941540c0110300c201060003c20f000c0c1460b9080a1865600841c8c1491002030003d14141224003d5a0302c10b200c031015141d00d03854900d50a4113400c404004040c0e100803031201c1d081040c0c441d03c1540114070b0204130021086c21940803802c00c841e1651250010041460a1003a058038617140d11403c45c0f07410f240d0360320b46940740040030008020000382518896050b009034141c0d0000e58014044d68090702d888400400950301c640d07800c842d40c0b00c500d0081034640c00d040c440d140444482d03400a1406499031101a03c110700d2003240c06041240d402c0010030030401e880c04501c0c2044c0e035074590300022400c20341080700303131100d0707802050006d0030a104120141002070500d5810100040700850442c804e98001460180010540c7c0126588810000308100866110302903413501582 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 187104109 1250 187102859 187102871
    0xa1d060402070b04060e030f160c0e130605090106120302070801060605030f060d05120c070e0901051501051305030109030f030506030a05060a0c0903050f0d231e0706060308030a 78
    0x1040101e029604016110303c001ca0002030000700550f010312911080d80c2c0c2220306042d002202c140d81a8001e2038001403d0048400400c01c00425180400c00f034103003a0109101c034075240480e648400d542c0c91000e40202e48030000706440920039848130019100c00300400d84441c2c034a0401941e25509442048015031030484c0c002402c07842401a28068000780c4000710f00c9494442c02c20418180d0124266454051500102d14405d401c0d0000c0c420182480e005c1c00303105240c918950030b16400103220409a034140780400c07090300d444065107003541c8000d00f4807580b03c0800030150102290380390405a050f45c44c1c603115005040d000071070a500150030307980600295403501d06141c0c41d0107000000504c0c541c001404544000b0054014080c80262031a02c19030141d030f41e07107540b86010301d030040c0030185402ca441044402580854203030300105219004400c449500b007521074040c45541610951000c0c1103910701e07181080c040403901602d801010900100380c0381c1c107000c3c1c1c4540c01520013006007440c180d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 187105359 1250 187104109 187104121
    0xd151205120c0a02010e010203090d232b0210050106030f180c050402090103241a16030818100b01091a040e060d020a12020145050a1d 59
    0x442242c40380c54141d03000e07010b010b585a00541702c00c00d402000c18190300003030140088684500c503280b04294000e1291103000d001c003094485007004410b40c3c03860140c103d48104545030740a0078074004103814605070b50301d001500c01400c2b814000c900740b803912498182400060401da040c0c1014075040a102010000c4100702e001000800049243c01028258168010003c4d4a0294080c00c0e4032481030401003514000e11a10320045080020013000000a00c00c0901802480d42641010010405c95451414501500c2d055008465400040c2000102030001d01119030340a20310000039456022142d08030000c1d443c0c2409040005052400110062000503410702c0e450100368803805903400461070301d0b00300a40c0180200d00144102d40160000c055103005803143e8031401c0013440c03d034084d03c04152032440014000d00240c207014110300558500c1c002c06035840d10501101541285880c4088901c0141e16008011316030b210f0f82d84a00480c1e80040e88101e020030320701411500403903002c21039580b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 187106609 1250 187105359 187105393
    0x7080705070b091003240b03040c0b16060504030201020d0e011d1c0302092403010303180605031f05030f070503120c1e0c0a170f0619020d151205 64
    0x84007442c1d0321504d503000d141c40590003031b440321108004101d1040c241c65908044010030011a51140404600000c00c2100707012503092401c02409a9401c003514104980710144020140150064407240e83d850125003014000d60460f480b881c15444103200403004c03280964001c10f82c0ea01c08201000d8494120340c170400300400d0000c20400d40c0281b002e054000f00070228029000396540c2d54000d6001032440640e0306042c5108400e00c801006039554941c1075280c000c10786441d600c000419034074010001d000c1d081d00501a02e42c0040d04000c400132003410400b03c050100840d03800641c15002e601c00001040c0f101144041c29160107504403000c1b80c610700d00380e005a100d0075228582c1754102014029840b039201880100e0300d088501214800d004480c001404102968072012550311031102c00c02200c00180031951241d07503490081c0001c1d1502041e003c5100510301440c00b030a0390300103101c01c03108031564031100d46100a15084c82820303455200f51072920803140c1081d200c500c90800041e10f50030349 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 187107859 1250 187106609 187106617
    0x101802090f0301142a0708030105010906020307050c06030a090c030606080c090405120a0903080d06031218030b0a020c15220305040b07060e010c0f0908160506030a090807080705070b 80
    0x100803041c3d40d910001c0c0c03110240002c040d003202d5501c00b85e881514402084c0003030b051543c0920038099907545007000240c444903603988034405542040c8400e101040f404501860130b61810382d860399036540d40c409001c0c024044883d000f85840b500e00b501005000d003590000054940d000203c0302c002a164080298044007224020155805001d82e4080700d01d5180181c0300d4003c50741070004d0202c0e2aa56925807a03000345002d44001aa0382c4420001d20805039602100d1065074180106840018821350960f40301c9070101400f0741040902150169406604503649105034101743c0300d5917420700b1030300201c0700426106100e82401800ca00c80410751030700c00394209603a050300c0f01072404ac40c003103500d90f00e6008513005940300c6903912801d120102c028040c4030075044103569178540c002d00f01000a401140030360040d82c03155001c000090514000d151a110540d48102c3c0d105032a50b65190458003d030520071401411800080780c100c1c1004508400303003a03018407c0080d0743c07045032a070300c8a48041c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 187109109 1250 187107859 187107881
    0x5010b010224010b0a0512010603050f06010c03050a080603030d140117010b03150604060f08030910050a021b030a240b090705090405090f0715030506120a030503101802090f0301 78
    0x642c0d040100300e4803182c00020140c2c000340f130500c2400c05004401480c07910800b6800030000c280c84400b00b040a60a04030950b81c8000d007400d005da1451407545004090b4000c0c055107505000b0140041403a13940c08009035202c841000c14140070b0318040c0160f04036501c000384100d840c2411003c074010240d44040c01494213158000e001081d95501000780b00c2001100030300f006420907580e00380820b031110219100c00140c100d410065954852540502255030707400002103007081005d1102d21021507000c104125110040248643d0702620b640c0041e041c04e00d2014020076044c0207202e8584208401c5410202c2d03040480402c04c9804072403018406c0b00c032400c071800b1000030010440c0354018a4141d0145802c800e87e0790445100301555800f03546041f442c0c1d0440301001409071040d8072107036403500607154030a030b0580e101d810380d003c00c0400c15600c0c410343e10300030140f01d80440003c03c455501c4941c0f400408110312880716102110301c07407a009622004c101030041e07041c504100b4441c241405640300002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 187110359 1250 187109109 187109173
    0xa090503030f070e0a06030204080c0409110628081605070209040b0c0c07030b06040f06081930110109020a03060f090501050906010f0e010812090a0305010905010b0102 74
    0x16880c0c030b0340e42c4a02ca4000b4214400d001116242c1c1009894020170350000d82800e071001607440e81004111890100340c500d0203441036081111140c0000d21144d070f00204428180c90b040d4603a58440c1581002180d411190021508800b817200012544600341c00d02074080c9006900554600c480304442d1803080c144c02a420034901404500010100b10320b0540c0462101c0c241e40c24542700b000c4aa080081c00d500176100e0303500210610130381b8a414803a143c402d00100300200266407809010a07280e40403001d250300040d00c038441600c18000c0c8904511412004160f1403081003407099410581c0d04e41400784140040d003501c3c2c2944821105120701544190014000c2c120795117195217481c00341140b08555103081f40c8a01d40c10000403401d0050b14091140600900125070409650401d04c00203035000301022910b040040002000204a000c24003000849d01552598400d01040c4d185a0541c00104198a03144c40d81050100652011070043c009900341c0f19000f8805600c4400155101c405002c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 187111609 1250 187110359 187110361
    0x90c030b0c03090c2106070c1103070311060f0712020a060c050f07060e2401030b0702120a0c050109081b10050105060412050106120b0907091404030f2003120a09050303 74
    0x14174006000c0d0501c029180507003c0080c1d00e40f802d11b400c01030b041d81c603040890341880d68041007141201c3c250302c40400950041200d24615101c0320000726110100354028a00019010084104d08085502c0c0c90b800410400a08480b040300039684c02c0c011000740c9a0742d203006141442684640110340006111000b0182005d01a8540340014030342032a83c0c0c41d00d4400e00418947c82128020042c117014600700760a031456245041c465a1444010070344000c540000b02080b8900c0c00130700076580c601016103409071103109903250007801081030020150900f0070225020305031a5119203052950120302040d1007803440700307140d00c5040d92070038055541d20138410b103c00e1240c1d5110040ca900002d0003a400858031a6075288810038111006e541680c0d102800801c005100300100710150051a100208000345031a090152680f4080038000a0801c251005104005441385480d1009803005440c0f00f84000c4004000d50750360303408107240c00440e03542480050503401082c0300b90309000c4d4022000d5461 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 187112859 1250 187111609 187111633
    0x3030503130c0f050307082107050304031e0201030e06160f02030906031501090b04030201050d0e0c120c030106080c0d03050309100c050706050a051504020904020d090c030b0c0309 79
    0x4a504001c0c030104490762203101c0c0740041141d512000300104040d0303400c2c01400e4240070500d41031410036080a6440d91204000e4080f98006c0780515900c240707012a02c60316000c13649415429440740e0b83c40500a448078414880c440c0c000100c80c483c403e8400d0701c00f040072070040071416481c1c1800700c176207070312400c04142c2c40c690f00c900500ca212010710103441503074540841c09002801642041e500d890b0405500b000a40c00e0396042098400503203400310202d420149550f000070428412040508009603c13203c000541800030450086918001010603130807070030300310f1182d076a0748a000034984a907080480018606e000403030248130250b00944803c1040300f940e1010b6485a10151484110348a05e080c900380d003c0c864440d02208401a07078a2176038401c10303400c010302651005000003035400c0c80c1034240f0a480e020240d2907060316030240c40243c3c070788040c900000c009015052105440909000b1a9800c1042c0e8904a6041d40c1c0700c1d490004181d101c13070b41803849500048820740e070903610084ca0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 187114109 1250 187112859 187112867
    0xc0302060c01090f1203050106050f340303050910060b0d020a090e01060503070801050105031501030b0a0f0b03010f060203030609070309080702210c0619080a0b100c030e09100303 79
    0x840d03249076400810558915030310950302940c003d20983c0d03900d0300c1040300b008041d4907000d2140100402e00e4103038106414805c800b1a144503c0301a2024404010302d143ca00fa06c1480e0a1000440000e1481c042d104407810041e0140a0458011000d8018048401d0b1549418031400d02500c0a405003030f41030502031080c40b0020b40c000c100c2c0b881840b00c40b040000d1140f0341c416299001e44483c0c1e440a40300e00f00174002401c0c0501c1038109034140308060080040b00000a0b17480064000c1c2482e002c90754071140700c0400d164910f140c0085011211594010a00d483d400d00118100c171110302201a02550f1688126264001a00c4040d8019141808240d0003440394100c0d5a015000f041c83c10b24000096000034141420300010800c1c0c0c2585035400480407409010402c042e40c0b0541c1c8051600f0301d000000d00310401c2c0c0c40001014050084045241400e4903480b080b11420080c5c103050208624003809440c0d03407420700c41180010030034818101c0908011081c1c0d80110100c00c2030400090542ea400c0d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 187115359 1250 187114109 187114117
    0x60e0d0903080f04030c2612070602030421021e0a030e191d1501020706141c020c060f400b010e1506071a0402031009080d180c030206 59
    0x510021400c0c40040040340c0c2d81e0444400520400c4414042841441860354201c66001c80c491112341009000381e10011400e800c850b03c0960104c4016540d550310300c1d004034007d107615002c441d00744405200ea1141d07038001a400c1e40100204509584542c3c1e05113201c1c1e514a00060010001040e0040300c180030300b400342c0400080f500c0002c442e4480c6841c1c9603100c01d071004456180c0404103c0006104040510a408820344003081c03024111007030030f0003809482180344880e07948400000103002c548940340d1421800360401070341c90640d51030840702d035041c0c0c1d00c2030284c6500804c62240004143c400c028940222061403c0900400281c0000c1a0094890001d4694446418411100703540041e401a4107a4040c00340c1e01c1c4a22110f0921040d401092104115518004c400c04c204801c0414152001051660b07010b1b220842950307900d02c00710b42070a80c80000941350078101410b00041184070005410b0b9403d1152082003250360920a9001d103030030392100a011840e4014040c409420010014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 187116609 1250 187115359 187115377
    0xf01030b120307110a050306040b04120c05030c070f0806070f030f060308030906090c030a050c040e0c0a06110105070f0f0e060f0c03031f0e0f040312020c0a060e0d090308 75
    0x88a0025001e0000c81c0c00d55008070012180e103021494500c0071403601d408054090701c0c095008044501c0d096940c81d58480300504080e04c0014403280c00e50809101d208000005a40001540e84030341c424110701d80d4031035841c09231220840e00400301041101d8001703500e40c814501560b41020440218405074001c001b20180c1049541d101e81e8080041000200110301034002030004114078580580800e0402c2480321400d4402d8011f420030001046000070301c0840b03411304450000c0c003040070742240d03441d0803035540240350405a00c60b000901c29404c00070f40c00c00700140400034000e59480c1c0408440011452400307138017003043d4040d00c0c2300d000d100741e1661101242c0500b2107803030300f18183c1c1c07040c800340c210442c447c040b98000020081c5028134501d189000710003461010a40d1810041d025218440c0104038402142d00980050207052045400c01e0a00e0700c01801103507036030488101c090b2110684c8109489980c1000201440b03008000b440c2c865403801a80c95480f00c9056607102401a40b151042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 187117859 1250 187116609 187116619
    0x60903050405060703020d080c090d081c1b03180c14040b0307080109020301060b1213030201090204051501080601140a0c05030903120a0809061909031e0503010f0f050f01030b 77
    0xc00300c0d8030f8980300003c115460094000f4032440ea1003060007000d42d0301c0149210030002c41800548003507100d40b01840900c0b5400320302c1c582c4417520034103030f8035941d51003050002240b41070006013083d580f02c0e40e490701181d41c015a8180203c10390303031828100c02c0d80b004500400c4811200740800441005200003034140384010001b003031110500340040d1506c01030380c00c04031a6943d10349240d0f045107001d20580000b0100f526202e07051802c000c1030201154030007400d01c1c002d004020292800c0510030351080c0034070340c0d00500400c224105140c020040b618405c4686001c1940c0f180810183c1d07001e41044030b1203412800c80c1c0c51410014050448441455902c1180c040c84140a01c02e140d42d41800600c1650019800c5607465128144004018410160182c4020b80048062055003442e050148a0b00c4000b014082809203041c50101d40700c0390088685281c001d4000c0304036001c5d0341c1c024001d604807158003512a44113500e80e141009819498811698844503e0500c910554002c0e0400003a001303004103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 187119109 1250 187117859 187117867
    0x9060402070f0b160e0306040c0905100b0f04050111010e0a02040b0109030f060e0610080604021c08070b04110402041d131703160801050108040f02030c0a030602090a17060406090305 80
    0x390b4111030303540989810041019616401d131507164806090204124103d009040f941003030b44400c1c05004050040d00c00350f5480c2c40004000b8005d03502e51000070042000c05a0391185d5100801c6040e410034000d4600007181d220700661500340501600707418000e52405000180d503580c0c03c2000822122007014117020603c4400801b28141410008110703000d600081542440c0828003814200010300944071880d8042041c4103101000414944c07042d416210110b42d1144006404011081080c0c02084d00c20300113405410808400701c00c9000c1e52250b108142c04d00502c00400090b4020340c0214910404040c000ca07080c50140a5001d400c4a285102c0d1452001c040c1c90f01c11261450b032925584070300001060210340311000010300000010b501d03105046504000c0000d1440001903c050880001595508155a4140f2142d000290002d100c140440e0b0b9074a40000030307411000104d44100360100c0b0000e2140d00302105c4c280c8240c02d04000d4686991143d8504004040300e030000d40c01c01c0302c148 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 187120359 1250 187119109 187119113
    0x100c02130b1f020601030b060102120418020915070611210c091c140d0f0507170d0b040506090c0702100c1e0b160f0f030e010c0e030d08010509060402070f 68
    0x81400d058050b681d01030140d40d03040d420700700100040506102d0444d44004603a8408a001d1010b03541070f150391034400041040440b2502c0c019000742c200a0340e2050302c01e00405030206d1072100404026205010030302c0303648036500d1018460301402e000e0500246c3c403080c0d8440c03110700d210310180d80489001245420b0410710004100d1120f200303c41d000c2811038406500c2c0a1008250f80050700040f450f000300404060824010000721701101c01c9811701c00046000000c100d45503070101c5051070304901443e1582441c00c00316020300003d00c0518000d034a0040460028140502440c0c403c800314030384e280c503100a80d401d00c280f450b9459000c03003c001541c0011000500d10b14090607062601040c0052882e00c14107040d0011400a00f1640c840c081800300c1030000f640080702c2c25000040d605000400c000c61160031b4001c0c0c08081c0c00b00049506c0c002c1d64039407080c0c110b260204c9041d0103904454400001080a6491010070300a05070b000721800000303401d5180507002003101c40e202d181c002360006030715 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 187121609 1250 187120359 187120399
    0x5091c020304121a0a09050a02010807170a02030a060f0302060a0f14031509090d080c090d150903020c1905040207080412050609100c08040f05010e0a060b100c02130b 73
    0x701c0400c503a40780350701829100461602e0441500800928170800110f031b03080d40c80315640c0300c8401d0028180840a00003420032400f403040e94440301c04c90341580b07180e441c00040703120095004840342e942c1d1038074081002c103820007016109000d981d40500030901e0a6440c000c280c82300c42d10300c3c0d100420003242c405403410072190000514005c80311543c010302080c100ea02004488030000301303802040e910000c000c59019620440c56904801c220342210f60b92400100894112560941c011b041c00440d6011000ca40c84a58002c05034540240e081d2110790000c84100942007110100805207955050014003040c5000c0d030091601c00d1142230040d180c5941c1e1503644000c7c0f0314802081d5030343d411510400024040c14041d0b0a01c0614000c020040110100340c040c00070305000c0c001608028401c0b040d6001c01030254060041042c026088800c01d400c0c5180000c054000c64003054000c40070003503402c00c13942c06007012003015a402464200300317110741130300b80c4020041c82d41442c0d0320501c001c8900c5000108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 187122859 1250 187121609 187121639
    0x20d0e0a050a03020114130303051902160213021c0506010516030513050a0602030d05060f041e0c051606150306020301060e090c120403050a2a050c0405091c020304 72
    0x209402030441c0320b4090074003900f1a0041c10aa50030820410704102d4a4500c1c00c0110200781c1d807600300000c07241c450445150080c04c200ca401582c080c80000c83e6140328100540d005d043e04d20840d00d5440207644425032100380d02480d040400e8020181200c41300080b0700b0b4000a0340004185010b50900c842e410f2080c0c003403034403400d064011620002d4001581130913461450068203054443d19070151825038025901c2c4650b01c03041011503581c901003101941e500b5400c10040700300a0081c4180c0b0394105001e080c103091b0f0311200007001c0c40d01110300703402409107090315100c08620900100342d204d40d80f00c0102404030f40c49003c441e00164100840040e04910145010b410156900e280f104a42d0040c0010044007401d002ea102c0030a1048000301c0c0d00450f555507001d941890b10075103c0c0084a4140c42003042c01c40403044072103003c41c144d01000c48034000c07031203207070b00500c204c40403214068140b004483d001d8a135003440b5000700458248000c9042811041c591036441101d14150780c4084c80019218 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 187124109 1250 187122859 187122863
    0x1602030f040905071211030105010311040b040608011809050a1101020a060e031305010503010b04061107030803091501091806020f0f13050f03030a09051507050a0311010c0507020303040306020d0e0a 87
    0x80d0f40c00910103030950010040070080c0e6001403c11407410500241c190a000512401d410151111800189a400c0c40c05075001070685800c0c040c0c0720b5440e004040d01d4424240190300400c1d034102804c81c82c00b500c034042d0000e11078015000e05a8007480e51142d00f0703603121541803581075226003a141d00002d240307882050444811180070f1622035803525220001f07080b150f1700544c104101400140201d003e40d001f100d003140d02d00d04060003a400f0210003941049000d07800506003410110411001030800305000c030060f00c03140d5106030780d81e0300e42001004131031480718206805c12a00300e0741000199658000c003191040c90702c5580c10600003811180d0709a06c5038062103043c00d12510304010318100480d000301d880c1d0b0300b2800b8500b0710b204024024091001c0d0303c600307489200c2401e9000d8050900408444400b40c0110541d1640b20090402a02135200307209419065880c010186810320310400c240d41100758024099850140b8585400c0041e4001941e03d02549a650820b0a5240d0b010410180018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 187125359 1250 187124109 187124111
    0xa0908070b01081006061b03090503060a02031005062106010201020c070611010e0c10051c050703051009050603032a030412030e040b1f021011130b0f031602030f0409 73
    0xd810281c00b18240444000091350722410702000b440101d41150070f010800d4801480b1004003220350400b29500c4600c0d81c0469014050720060003803429494000314442c02240302a160510344d1001488000e102c1c0258820035089400c52085c0304107044885640c02220510003d8181b401c00b900070350038081300d9031100d03001c20102c0e19014000c4500303004070301c01c800b010b9010b03104d036081d0100412200401d0282e404100100021007030420000704030824000090000b0410240c41c1c030990140007003400350b4002020880b07154001950b61214090f030f511a0300080d0240d0b040c03a2601c0d40983d02611030440701c3c009182c0585080a0f60081003000c0c3c4003c007103424100c8d20b4040c072801d0160100c910039032014011410320300c26252a840b0940d02c02410300da130424860301c1650080d4101c1c2002c210442004000d4203240429880801500c0030300540c602044508000617550780e02d1074010311030307121141074031803080c80001d1118183c204074520300b00103401680c0c580b5102c0320501d00030394400d4100308011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 187126609 1250 187125359 187125361
    0x703031407050a0201050f04020a0b0f0408011503021801142e03150e01140105030a0f0609020408070806010f0b0729011d061518060d02030114010c0c0306050a0908070b 74
    0x455424006e00360020500404c440b040d04103070b008100050140d0040d0740d001c04000540000400c0c4c0401210000c1c62010001c21140c402103a41091304641d6200980c860039203145156404032000c10440e049410f140d41d0b8070002502c0074240821001101040c1c2d14284012902e04a46024544005040c4455540c001b9107020800100c42c201c890580000750015030480050008000038081004817400c2400c1c095140d035102e50910b00908400501540f41e1410060001960010b580242c01524507080540c1c295548544000e681d50300240b00d003204008a030f00d020045445203c00801440340030303641200807070803080383d050808004c40ba04480382036903070001009034504041c0300c412045503600401e09281040000121001e082400302000c0000c0002e5000104030041070300c108054000d01903d403500c0c0300b0300440c0004d4000348100c0b450b11921101c40760081d803154080194a642c886010402c0b02d00b10b8a0700401800c004110f40402a5118207400209003080701500d80e8511441d030072025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 187127859 1250 187126609 187126627
    0x80301140415080303040b041104091a09010e1e0703080a1710080c0f01020705030d12180c060804050c2101060501080601050d05060604030f0b0a23010902070303140705 74
    0x40718603902d03a10000d20019081401070110110460350402d4100d84070104584603418072400140d00c0c24042c1d5405407030030070318900308100801c08400040b038200c141140da50310f20103414240c2e181e000b890042500a0313030040e80c48440d0442840500341c2207504680c942503d81d0788010b90b41d44200c4100012544d03020b482c164039180175400c20f80c02040251003140c080d2a2008030b81c0c1d0b40020404403031140300c0086484440741d200700966001000014103d8090451408018101c1030071803200002090501c440b030520b14040c1a0714020059100e603202100d10720b414001c8560301c2d40500110342c1d501514034604038a50f510b40c401ea64800242c005a03d440342d81d810b1050858449500490500c000642000207a80e0030200355110440128004541a83d401740014224130540e04018840908024503c05100d681d12134103106005d42c910400810300d54030319600b0380c00109032001584410000040c0103400300c4d500504041c9101e404d002c640319088261090f001d04085901c40c000400224032912 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 187129109 1250 187127859 187127861
    0x9051914070c0f0f230c0316060e040e100b0102060108060408070201050f040b030a06050324010b07111522080604030f031b02280c090207240603030f031b080a02070803011404 77
    0x180310702c12001814180740043e41ea401d201d20609c2204d05100380072444090507140e90700120342009014096814044001035080010041007100318018810032001040c45200021380d24003941c1c0010106003082c049600440381c40d84aa94400401c00d0203008c0022844844070245000344a4a1313404503920341800e09142c0b520180280c039102400382c44481041c61141510203c0c15140144000b03551070f540c078103011502e801580c6800b60082e400b0301190540074001030250400c81480f03542114488008008003a07070400e103000310b10b2a80c100030f01050000703001d489210110301040c00d000ca1011002c3c2e1545040c43d407280707500005030b0460740750750410340200b8600e420100030910744500c889074245c9440c1c2d0140c0190043c190150f9000071f0719018000340340d81103403c1c000940c00c40c550802d030840946001d000c051004070003050300040018003041c0203000c1e0442000d03d081040d504a0364401003100d5918010701480c045550030408440400c0c048001507010b4502040e41900700070103c0f003848 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 187130359 1250 187129109 187129123
    0x30708060112152d020903120c060c18010c020a051f08060d052a15090306010b0304081e0c010204060503060a1703030c0f0409051914070c0f0f23 64
    0x303103c186010505504190104140210748182d0030f0032a40d01102c0070540c50007403081e80c0003d945489640751102102d80850020b20340001c004060b40d90503103c01d0803100f4980210000c00c41411040d00701410705520440040e1002d42c00100107448407540e0b0400b080d44c0356443c0c6030780d0100e500c98130a0041c516030402ca0301a0084810354002080f50f07919160540c40c1c081110343c480301d0076000001403070350508020201c020b182004110300b1103861400c1c1242c22507484401c4040c000d01505000003801038003031082d24032450f00a881a850b1101403605072031042c00130f10403981c40c0502800903840502092000d04080c24032074842a50301d00f4030700c0070402c80c01142e070f2000541a0a942c40c014407480040180d035004159035404d81c1e1a0145000e000c000c6004a4100e0000c041c0780000300a09511011a04a17007000c1351030b0300300a41d01d0170b400d00c0c0c41c118004075442800304002d00e40344000168142d65686065002c0d100036032568101380c3d1044104001e00e10800d80d004410118402d009d08213120380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 187131609 1250 187130359 187130393
    0x13060b0307060905060f04080601060203070c09020403020607060507120f0920010c031223010e070804051c12020c0607020708070f0e04021f02030a0905090f0406050402030708060112 80
    0x7421801c1ca030a50051808a881c05040c2c01260040b44000380d016820058070701410021095032030302d42e118030b8002d590781c002c0401941c2000407020005200c032520320880d02641d4001c0c203841c1c036100310b49d1034031005418050309400070040c0103140303140c0749441c0d4462000c8040400c07602103012102c03400d1014170740c070641c251303802c90208044629443d40c1c1c00500d05a0110b5050030b0005654400011220062540741c09000b81d60420a44010450903082d12072416200005c0c1d62602c1e0b44c4412004560050301150020f12550001c240001c1c48500044244104040d92412160450280d21110142c6e02721084a000d03030360004090000c019014020034002d01580e0005000f210301d04900340504128500c00e5443c40500040441c0a40d00c582c8081c810500d003020307039003001c0000340314000d68036880300c24010001031071b01c14080755618051490600030420626050002e44558031940005d110180040741d140c4501c100006003400c00b03111150084c000da17400c0c10045106403c1118070100c0c52042c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 187132859 1250 187131609 187131613
    0x60d060e1902181c0803010905040308091b0603060409080d090209011e060c0f1209051e0f09130b0412030f0501031e06060b0414130506060715020f0313060b03 70
    0x5114030660f9050394110a0600b04d0b000900081c405150f804070805a800c060807405000002280d11010b41d003085014a20a68880d6001e07541c04121984a050001109102070003441c1c188015180900c0034580000d030003800050407890f9a40c510546620401a4482480d140c40c402d200307503d01400f6860051601c000c40d01201c2541c03181c80400f904250044400b4070002d03500d51400e00245600e5030040c0ca52104d4400343e0385585801c098141d40c0d1038402c244c0319041c400382c0400b101ca03120000c0280b074000540006000b4002c0400c2202000c4028002407150194541c15404100c0b0411014059400740850700c0544e8000000102600d00709c40f41005e180b42054010400210407100c03100d5103442000c41b041803529a0b103071007005000300758800d01840c0004940481e610609440180340400f0845804455448070356610050703031000c582080d03111500703014020110790520426005070681300001894007189281f210829002a240200d03902540445241081910300c1200900101180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 187134109 1250 187132859 187132867
    0x20405120f1510031b0b0711030606190303031a060f13090b0a0603090201030b040c020c09010519050621040c0303030e070b0d020a02030c1c180605030105040209060d060e1902 77
    0x1030010f5040f601e407200620f403007002000c0b0140d5804105d61403001d820410401c2d95651081c0c240f00c0c0e5a02100c610b01c1e07109014000200709a8940f500d243e00d00104c0c00e5461062982c070710346064000b800b595840681d0040001ca400d05e29644280060020243d19144552101d010911816510b203203a00601d503120700c0c0002080550b07441035916022116145804144500544012405132040c0e0103195086403c00c01d04004180d004190341d1400e4005450f540c5150381d851003080000880c01b500742c1071481c0380f03500c14000d500301070740100034200f40032500412440c5103502b9942c01440498003a00c29036603481061042580c140209542c5041540060890340c0c10528036150310b1082e0202800a5030780064020611030090007907030b0040b55108252480a81c00d803251480600f0307807041c0035001801501d0000603200d2440007480540e00341c3c0d6a8079003140c0c02d103014007000750b001c82400c561100061041d4409100a8000e8201601c188081c002c1c45003091030381401c02e120302850b510500c50042c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 187135359 1250 187134109 187134121
    0x7110d020708070315021201030c06030c08040c17190503030a0506060c0c01081005040905010501050f09010e04030f110d110c010c030206270a0506060f0109050f0d06020405120f15 79
    0x140c0d40c0f042e650064442e248003a49002d00100038070801201e0a00e00c4050000042031004084040040f14002d4505020032260303103d085071071080454008000c041c0b0700c00240241d0705084040300c049444071044030152600300068000510114000b200d440d41700008000d240c480600a4079007050b019254141400c0707230360881d01e803221246580706041200a20000d01540340360203101c070080c000078008001e007841d142450b6010705001d00695024021a8010b8115410010b440314100c6141e01121041c1c0e03112a6002c03501d0006c5424130808000b04140000a400f40c14081d40701c50b01026143d51100303003114071400781840c02c1e200003036042c050190041804280c000c1511a44458803007141412030440c0040024802c074203d0403141640300d80140101008800540c80b4000c4100301c071405800d1200c20300456051000d80243c58001c00c1581080c8610b0400c00b81610032140f0483d009402e081e29003010a6002c020301c480c1d42c00ba5400404034184180003070002042c6e1401c0072a00003400c1c9010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 187136609 1250 187135359 187135363
    0x2d0304030f0305060604050a0803040302090708090a0f050309090a09030f02160504020f0705071e0504060f050d1104240f05090613090b04030801050405070801150e01020a080307110d020708 83
    0x586030000d0580fa01c0015000d59101c000b00c8010b0003008100c0141140c0b01d00805aa07900240005ca0040700c40d6004a016035000d03c01d034034419001c003802004910b10565031004586034143d0200c4040c44148175000c419558404a14400d0100702000110060541401003010111a441400b590030040300801001100c070b81c030340291441a0fa02603601e1a001c03a41000c00d00c50000d000d4a070340640d05000c200302025140189190b80f03100c4a84005c1074070f0700c082008940080c0319001c036461030842c0401460030306480c0b008031103001c0d40c000f41745040c104010400755440c54000300c0744d883c0c100b2207104005462901240280c00003800703440f4402e0070720010510600001d042d051091245041c407181100c102d801101c1f04e103500c01c2800003d81414500500321789002c0c0075a5200d2800c200004002e07034442c60350780317041360041260944a02017030780c416141020802a480e04500508141c4008503080c40025130081e100c680d619100c242290b0500c600f0204542285002c54201e004104a11400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 187137859 1250 187136609 187136627
    0x20405130b1513020414011202040806131416150503130305130801020d05041202010504030c080c030c070e0702010612030e090a0e0f0c010e0d0b01030f030201020c032d030403 77
    0x821404007081d0002d000941103502c203103620b8001d01d0001401040d608000040015400d4082e21a03488603c9040d90714016406580104001944400c000403a0140601c07100c0804078080c10802408181044000741826004140c00441c40d41202d420070101e0740300c02c000720720340d441860400c1c19404c24000680401c0c0c04810080d0412401041c041048090315802d0401012840000c6658580d8244140c000e018200c03010390300d0491144544881e5401802880e101d1a45550f4814118810742c0c2c80d040c0c241c01a40107d401480148038071600700008002440141440304908000c40c42c140c0e2000342501c2c03650708160741000c826030010001a801200103103441001b00c8803020107a4408803902e00404106984200501c10380c0000d40e0013001c003042c90350040c1c4007030b0789002155440c001404104003080308000c03da0b418450041010810041041d0111403192001519010502d550245103401050810405015004c61200e04c6403281c000100000e014550305030a40c54140c60182100f11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 187139109 1250 187137859 187137871
    0x507080a11090f2e1e1707050d020d0618061a0c1c0e10090602280804030b01140a03230a02032a04020903190501061a07020405130b 58
    0x440c40280a40594401c2241a4010907440d2000c90700007441041d0310f0722100c282c2c0100702142c550866950b0b19202d50b140d150169245072660b01c40391b41c3ca2803a41110400003000d00f000c00005000099030f1688900050016000700340300816007a05110101801c41c10000c802508203141c604100114051103540140c4035072500c2096442d2200888a0741c1005030740c2d206007070504c41c2005c210b04001c3e0032000754115524192440707010802d000c1c0303040e91000840e005a901680c85101c001140b01802c800040c0c840b140000c04058262003a40c07001c3c025049500129480144600144120043e4505008024408580540c100740c655100c0e410740980390410030703401d815800042030350b4001c104038446205c1e50140c111040300c0c10a40803d45400c2800e11524011220030038084a2890903000351513500c0c0c0020050f1110301c158a0031a010080703c2e41013120036540f5200700007840100380441c045003400d00400680d0358880d80c0304100403650010030110116030071018080100f00d1800351160b2000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 187140359 1250 187139109 187139119
    0x636010e0108220c03060c110c120304150203030601110102090f011d150a02011811060a021f020a08070c0c03080f0408060a0902040b0907051909050d060507080a1109 73
    0x3d1110320320191034106140b10043c16a140c409400100880c011007002102c0c0284800c108108802800b2100742c00e01079034503052640140ba1100302840c116004034442200715086a00d400e681d02e0040c8a0150740502400250700003108000d125600045550850800100210700c3d0819000007c0d80c105048800c443c100003184940c006075036800e9051141c1d0030070080c1601000b86010383d600e10940c0c860908500194200800d13840c042024040140c94035030703c54104059601a10244074aa1704a16490011403150002da42c4018404031002481c2c000e0f0008003507642c0700d0844000d803185801400400801520b0030211011680c10307245042601d81c0102c04c6139651818400307000c200c0c01a07410402e554001c007000d2003a80b0205a0180000a02c252800d0207040301c441d081113080c042c01c440010115404000c151a0300d003181c0c10200701071030301782411a48070362120003050454014000072034180359910b0520200e10b4000c04101d60010300080c05014801130780b018034145001d1038401a0080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 187141609 1250 187140359 187140361
    0x81903030b030f0610090e190f1e020108070f02030a030b062203050105070f050d02030a06030c091524030509010605151b0a031d030a020636010e0108 66
    0x144241c129600942008044440074545240b850392210016201e605031007800040c0080c03059910700510b004080c4680c00741c401000800b030242c4034000c047ca03049a903c1c0070b080070a00081d0580520100a0700245a4410000e0703044c800034100c400003070f0482d4240010500106240ac4d400400ca0703820521502c0d020a284160801246513402102201059070048061074100a0200d0700b0083c1101d0088000b1300154a4107038040d20510141501800003076810000180c0240c05034005640181c03544100040040d545d0702d41504184a40e000b2054803901c90100c0340b4540e6110151038040c00c0340100c00030103040c8800311090040039484c4407200303040d280d400141d0510000e6200100501c40036000c528615525101240c040d406100790041140755114007004201c0005400260164191118040d80030311214900d20042d0026445078984690b11003140140c84407009070000f1030001160b0800000150707440304600d095558080c0c0101d080003540d440c680c0c1d2040300115244401c0c2442116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 187142859 1250 187141609 187141613
    0x140d170f131118070f090e010501090509040507080a140607080118090305040e0903090102070f051c210f090501020606130209010216030c05040605010e090106030c05070b18060108070819 82
    0x340382200381d040076140d40c3c14800c1207406074112811020401e22507a400451035210b0103c1c02081c00b013801800c0c001030050b0018441401d20299403908240031b40201e42d002d40d83c80075054a0528003c4c1d00b103c40f083c80c00e2015500440401016400040e1410411510340c1001d442aa44412035000074900d617444403d85003d143c001c1c81250098918030492030040e01e0300304011641c0741e002148490040c441c00702c000402006544405059540080840e04c10f212250490401202e050800f41c40d49640c01828511462001c43d411021105079141c2091510300b400000e880344500e584007a0554001d0030400c00c441c0e0b9101800c05c098010310900507213031801000100d14001e0130803000010868049404818004040064001c4036800c66003440b0340c5458000440c0c03080054040075801c114104010700c0f607e070090b04810280401171605904020082d04c8103031500e0019200380d5012541e60b00100002682413001501604000b40200102d83c1782c0268159594600c150042000c4140c0d200041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 187144109 1250 187142859 187142869
    0x50a0b0702131d120307110610090c11030a09090e0d0e0d050c0a0602070e06061911030d0609020c01110901020703110102030d06060e01020f0f0c0d140d170f1311 71
    0x80c2c0200203c0441e055902e124a5180940d8016a0408081211918041c00f0540009249032017424403001d0a81142d1800c040c2c04054100f5a130b10302c00344100b1303014010048000f04050134000c5459503078a0026490400d0a10071180d4890403071109401c001c1e00340c00e8117501b01c80e400355615029a03900c40d20342d0250802a051554486149038072100c183d0b00000d05075400500d000580b080104909142c2c1c0b5500100302c0075100703408100050740c28440c1c0d00e00c2e8480c0910010244c1260500980b854500c0c01c0e8640707030840b4400e4011800c1551301044095001344244a4a07100004020030076292104402c0042d41d0b0b140706100090402c42416600c0f8082d0b4803c0c42569400c00c809041842282e48420000c0c00b42285c428101c0e0062042c80841700c0051000651459403103a02d03c0905456041d680071f10110018000042e90f0340c40580140010744042000001c04003206903865500c0c0ca14401141141da86010b4507840030360100e0390500c040704802c0d4000c9200c0940c0302e25400c82100d48540460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 187145359 1250 187144109 187144151
    0x7020a0302180405060907120605181015050a1d090304030203011a040b0a0620070810091a0c0306010e12060a0617060405070504050c0f030c04050a0b070213 69
    0x80d00251900060319a0b00100302046000d188180b09480ca50380e544ca001c03070b5540b400c03403145880100c2c0780c60024001c10030b83d60000d5080b84464241540009407002503d01d052100c0503502d61032551143d800c0c400e0080045004c01410040f2869200c00c0d18046000b002014000500c0310b50b8003500f030100b00301000401c103c03001164081c00034041c41c44001d5001182d0800c0c5402d030b0b40540c0c10442c085840385845d088210640d050f64581c1031541c41900c030000d500951480015480744601c100c0419200010000d803504103401c41c00103c0c0510540c80e1500744288014040c02001c410720050002640c600e60036203030b11071003e07e03041504880d440001031110307864204101c002c5c001c0c04144141c00c011900600d0559501900310040000c2d400b10b95503541000302c0d006001608111b0080c0007614103a000350f07070001a80f501c99410841a00c1d1080220381c419507012000b540001000c0080f41083c201c202c004004080e07003942040c0706d0b0f801046264540e00300d1011440e56030801c0e000b0300c0101450791 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 187146609 1250 187145359 187145363
    0x415110607031a0603090d03050a150e01061403100e070e0d1209060c0c0515040806070e030d140d09170f07051b0d0809040f11090109060201020906070807020a03 71
    0x449860074810300150080450075812640101c950b107420050b4200002242d028040480c000c00001d0510305040b002484d0181140400c1512403c607030028099105480001d031a003240000303a15490840060500444040c003460008401e10400a144010507141c00841300d01001c011107a0303441903012145030544120036940110004660710921071030344020114000651a15000e568035003400f6500320342c440500030082c1d46c11450910036800e140782007041c0580b01174900d0381402e8030b910205003000b00403070391130000428403246911180740c10400440c41514134100440e0900c81706a01c0100340c40347c043d2401c00e5640b81c0d0351003801c20100c001c9841d041035611301801d4840d40c0d42d20300c00146600901c0c003906c851142c01c20303045a6100900b060001c401c40200002c250284a03907800754583c003c5d9500715486a81c40450301012150340c052100d0052102c2c04043d43c50381204005805288160003030307002c5a1050002621640701c9004440d00560000340c1152140c1c030360f02c00103044080a400c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 187147859 1250 187146609 187146613
    0x304090504080d0c17010501021b1e10320414030c030f2d0d08150a0905090d09030b011a07020a0620030a080106031e05041b1a041511 59
    0x514600303036521200e030009601e02c085c9a501d03103980e1070004998900705004100e0500e1000c550003c02ca142003580f0f1a42a400b86161401c1e01044400040e88009091541e5020800e1061600c2a020010040b0341c150452840c5002d806840d8040c0c0381c06500590241e03081c9840c80c100141d2840d0380820141c0c604540c01030454210300420480d86443e10380c82c5140301065042c0114000c45146461032007500340c02140010800d071003946500712034413038001c0d00c00d40041c00e01d18112056074540380070203800b4004405000c501c50400182e06464210f20000c0d2004110031407000f84001500058070b18110380c2d00e104000b400c0005131814081d20b00c13408800950048000c4030006a8940060034480d04201c1d1010585800100701c0c2e20315180e102d1203200d0707000074441342c0040c00703028000c0d80420301d080792082001d4020070003501c02d0380883d4401d641c12782d80790078207000102c441c801c0b0b0386211001e040340c48000070140040ca840200329025034003400382c06d8080e1000d10320381c2a21805214010300c2c1c01e001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 187149109 1250 187147859 187147871
    0x30b0f07080705030712090c0816060327230615030109020f100e0607050106050a0807080a08180303030a0e01051e0103141c0801060f0302120415060f1d0f0402030304090504080d 78
    0x1030a0703075480b4000100c0b0720b8849411800024601d0007445101101d0006002841c26041d945c0f00124020001c41c7e4123b800080366885110b01200d80016284840301d4a002071010381003e2003d815a0303400c08a50a22a80c1040700c3d140068489940ca621450300039a07100427032035128801510030943c0440480d40060b0041405070601a0540140713084501c292100e0601070b450303185072501d5400c0c40c01034086c41e60050610304c00080000000f40800c1707500d161808901c201100009003150b02c182c0300d4418282e141e0080c440704176002c1c850310b900091440b40500e80b0745401d803001074003030074144805010524550540c5018060901100807450440b1241c0e110310104800c018002d50000c0c000c5000142a071401071103032034068404c0702c0c00c9d40b07014281414203a42c2c0e6034841c00741000c2c0e400300d800721517126100080c18002a8400001802006c0d0078030380200304c041c070f031902c00040007840344010b00d242d041400056200030048034140c8902c2c0f030020a4556650410341018480c1c0242041d00500d009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 187150359 1250 187149109 187149119
    0x60b03030c0a11280e06010311070302060f0c0c0a060b0609040213080613200307030602180f0a05060f0a0302120c0c011a0108010612090c030b0f07080705030712090c 73
    0x4160f2142c4901c0c211040121120400403008005004100d154480c80200031306002c0c941d02c0b180f000750b02030014940030842a030140885140703a0490003040300035074481030502088850720200103234080e000c010f501d410101c0f03d0035065903c40d64a4406082c060340c80d20020084d4592008840d0a034074042c10640d41ca540003030502e440304086129010f0030b03015030400302c3c41c0c4850702140a9543ca41002c04590001420714248101c503040c1081c87d649889640d200100150490000d031441c0c0d038070015000e400e1142c06091207084400410141c2c410600098140b14542d41d00c0c0039a805224003100340383d290440c2510a4009204030b20f02012100d101c00e041298199a82c0c000702800340c2240700a201c202960510b660120000c100c4680c04158403000612005104010b8502082140c42003c0f80da50b0007038031030302000040c9800c1500d408481c1030410414144c640410354001d4803030724040ca824540301400800780e0101600c00c0e001c03c141c9401ca4204ea6030140c00c005492174200b162115040c1e510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 187151609 1250 187150359 187150373
    0x5070b04091e090206090f062116020115060e03030d0903090906080c031b190305100b040b0109060503060102030d020c010e0f160e040206070221160b03010308071e080703030f0204050d060b03030c0a 87
    0xb11030300700085a051058040ac1340c4180a140803003544240d00d142c400341032040664060310340102d5140c0510091000c0410201a8011025441c0c040e03111260307014100380b010002e03140036070810152a400300c0c4141c8580d450008600000d004d103800b0700740e5010b0b1030724001101031100c40c441540c1616088400303c140140401d00200820040c0400c01072410b00d94188429183c2400300c07640400e8002c0c5007009043c4c080c2c3e00079a44070750144180c3c0d14100040003030408a8005001181090f951105209500e0504120a26000b091398009254208143d1811510b0154078060242c500149402007011501d5440555024070f500501005008401851071800303502c0304c41000c0c0040c8500c40300020b0511451007450f043d82c0c0340c5808a8656821512010766941c8444005c0301c0354044100c845008003010031751440c56a1040c45000d54600e44d904004098849194001080a104001c10481d95650b20461000950710050111344411604000390860240164004043c00350410f102c04120307103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 187152859 1250 187151609 187151611
    0x7030f050d08010504060b0307031a042f040812092b03080619050f030c150a1202030c03060d0302010902060a18080102121305070b04091e090206090f0621 68
    0x1650381e04611aa44c40c010481a140c00e442880b950311020004940d4080c0310360010450620380c0c56541695841550219003180c41c50441080b1348031418800c190700c0c141d0000e490740b406000380e01d581e04281c142402c1944501d100100201c0760030000038202c0003601c9413156094080c80d51031198000400844226444811000301140010300b03481c0014100d240505640390b44410b02c40e00710070700c90305000600c0381040c0e10103003581c5e0500c24040543c055a4a4001c0745540c14280c1280940301d8841310000b500e08102c883c03005c48118014010001418061801c2c0c0b50700c00303800c650b205c50009240c101070b8010015190042e41103000040d00b1092039400880f1000304c2d50508115000d0b032503807a070300310f801c0340945900c0d461048002000b00c2c503088507a83c020180705000e10161640715568401c08030705940705500514442d070b1a003c1c1180644681c0003100c03022442610180f241281d0343d0b00184280c403c000080f032080d0070602c140c1030a40c4512040c1c0d005034080e00320521046918144540b45208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 187154109 1250 187152859 187152883
    0x2a0a030c050306060a03031d01030905060711150412080711060a050105130e0303010b0c030f04080c090112030e100e090109090b01060c0305090f060d0f0501030c050f0102070902030907030f05 84
    0x72030f0b00040344c003a05264450400320f98140d07440c0c105a09084500f0441d201c00101c03441d0405807103040d6a004514148040c601440098a40321030742c80d41e601da040d052900710300302d80e03610300040e40030003003c00d40c640c070750811411681c6001c030740550301c00805a959052080503140a40b003458100194083c190303000c00c0c16a40300702c52034443c1944810180040e0f9160601c1c000841d001840104000040000509141c2d0004c0058038240810040c130000f0b546c220358007500c0b47c0e500c1072444421030700b0440e02040c09003641281c001074401c82c0361006000308050807400c034040c03032001c0d20009601d4491886015190300007011300c00996513546c501e602800c03003003100343c908204080000604500071200c01803600e0341510b88608041c656420080e0740c508001d0205e030070000800c148030b40d406261081080011644c04c00103055415410080d001240e2a0491070158160780c12000d41030303030001821002c0310ba02d20310150392641d60096070f070300b0540d003030f4801007201c0b070844070700002c03c1801f00c3c81a4021b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 187155359 1250 187154109 187154113
    0xc031b0a08090f030c1e0102040b0307030603020103050a090201020c10020c04061d010f06080a020a03090f08031b18090405190803071704171621031a01022a0a030c0503 74
    0x10042030714084d203a00c0340c0c284401c1d490b0b0106038885d000550040200d00f544e041783c03000504003565454244420b82c000c950650000782d40382c0d418811580c1501c651500b03c00d84070300401135080c0c01d80c0003030b5036181585d1500d4400c074500521500c0803442044122400000503100303002017036445030032158410403075600000c602801000441c0c4111040c2c550030485545a0b9292271a8450052000007503210140690030591543c0c444004a040d0690b621106480344043c0e17562403520004107617010646c0084a481203030700700414000101c001c042921004802c4400d0102500c4d03500d8024a07000d10380c56400c003110401082c0341d050100300c60245200755181c0e251070035245043c0403240c45220045400800c4550501022408034403920060007501a01c00c0200448084c503440e8620103030311865803032104c400516020103516500d405201c001c0a07207070300c0000340c0e80d004d400080e45a0740468511003c1d18001e404c20007540d010300c05c00104c452006400b03510b400307841c2d0410740082c0c0040d0140780e000b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 187156609 1250 187155359 187155373
    0x6170d11060403090506071b06091d0402091504090605090307020a0603050f0106030c021509010c0905061810020a060c0e04050f1905060301060b0c15060105120c031b0a0809 76
    0x20310360200740d0720300c80da605030707600074106040400304081e9801006040ea403c0d1001065441000c14104010700a444141c95004d0120310b0041410240d9207011010a0300c51040070034840142c4a4680880e00402c0ca0a01280c2580c0d601011074020601040054400360520381880060000440141002802540c1c1d8240094854206030281d070400da50306001c00c45410010480c180c03180c2c2c0080a000700741d00c141d0703140c1a5031601c119041003060b00c200903940d549205960303015400003581802804241c40d2141000f018a000c941645001c80040b0b028521285801d002c0520a1052040c801e510020400004414442c0106400520342c038090217070b481c10b004070740b10501d00501148501005862410003009180d03803c0080e00d0702030310072a09592524070100705241803c000d030a21554050043c142e860704001d04d0386030840302401c1141405820401d02114051031003205520a24103202c155581d103800ea0350404214582c50381c1c984100000c150011019400000e1a028106c0c2e14211082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 187157859 1250 187156609 187156637
    0x9060b030a080708030408040e0f0609160903060e16030615051c021003150303020a0c0609080706050703090f03060c020f1b191715070c08030f0a06170d 67
    0x5a80611040030300015818003d00c80020000001540e01030320501c00e0500302947e0340312807842c541059488846010b03110b02000614201000b10940c030101d205000600a58003c00282c00d07032401d400040c1c803081d12041d035094a40381c100541d59030f5000b942000100c09507a410400018007842d0020b10075203000c2c6030700042c0f40c0f0389a0540080a65222500b2002d40303000c0e420000464400801142450b49600340c699100554007400c40085009401805000c1c0346840c15501205890708600103200705c2c1c00080c010200000f8071007054881e0f5040036070f0743e40303154101a07031140c01681c02001e500007002400301c100300f0940c104201c100040d40884410008854060751500750740030709109904000d440781071141c60118195107074038824100941086031100c040ca580c21180c40184443e0750f0142024110010810204950107a607919240b81e0007a0341d980c4204d02484050302481241c400f080200f45040c803540c1c4140014154054941c2e0840d0a4000c8103881d04007080507000441c04d802e00c0707210 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 187159109 1250 187157859 187157863
    0x230603010605030c070615060f1b05030304030f0516030309020f01020d05090f0a0905070305040b130302070e071814042306060c1e0c0916021e0f06040609060b03 71
    0x8140c801c940c80305411a40c0f407152144a035008900d0985410f0307114160806581c9841e0140000350545a4491b00c03680c442003005010b0003541c03015040d501d00756140041c0402c5002c01980d400580c140703040006a50000012104c50080003616070b07414114900180070560541d00c5102c00d103100340c4031107e1a01a8000590301c41d01c80e814100302140e000c1104003040d01c0c003006a103040e401f005003103012481d240e500c1c01c000c540c1c046813003e0100740d42d1020701003404152404254404c01003815036980b640d10350741c0203480700241d124000740c0011036408100d81c24021010005084440103500da5543c1d60b801f00f0701060b0382c0c48000c8034041d620b04510084a00e800c00e1159003004440c50b001101030326900e00388001a4041c2e02c000440780214011058600d44407046d00c10458008030091a10806000c01c10044180103060b01c142d0300f880403841080070b9000b1a548070084503a942d900c0841c8103040303c460030328610213100d4580d1300454041000f045150b920603e0300600a5104119401e407030300600d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 187160359 1250 187159109 187159111
    0x21c080f010302040c03091b0914160f030e06040f0b0919020607050a0c091b030902130b21010e19051b0f0904030201050a0e01061a030c1201230603 65
    0x112860a4000050002d030a10350000f07500c030001480c0004091901d611003101109071013280140348c4014030030400c450341460280c005002c850240300642414001402c042400200130440180140180708950003030081d80900070303030317242c08050301c0462606190210140744403150455100d9202004520382c00c000266008540c503440000c0b82840005408002e100d800c6040708070742c41e01c21100341800050448694078020042d8400100e00d04a5503004072004c268095401c40c1058a84038803080980ea9600070541039402d42c55001403c00460300100d101c5d00d4188800c01100b15100c420600c2840055001108640c3ca20040d6a49904400005c1d8100d4214200c0501140d00c807003508a25902940040c01180c44018079a2040092140c041560b000044a0560242c2d54036020004004041e008000c440e80d0341074001c000490070a940319044403480000040300150100020f112111800c08903081c44024015206c040d6039907c180001025100c0f00550b655504c004c140103007070400360180c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 187161609 1250 187160359 187160371
    0x50414010e070303140903010e07080606240319020a05090a080a0f1502040f090207020f010306050a0b0a020307140c031221060303130801020306120f06070507021f021c08 75
    0x20b8281149192400c50344664034580c1d04481c8a02004483c01580e02442030a00705800c0c04098046985040b420a04001c00180014090030305044e11010b020f080101e1010b445490042e51510f94442030f140130918a00c007880040454400100b00310300c80d4100f0086e01c151101128540205a200c1741440c0e00d600b060361004001c0000314200c0e20000d1005241c2110000000348011300b01399503070030300c0d028a82c17950b400040a0351b4000380741810f504007600000c50300502828203109081c507100101c2d2440c082d5128840c1203508c089000c41d4031a20074007c80e59400d070003184214440014404142c0c40d90710228419100c0d206500c0c10380d4180200700285c50718242c03010b40314420451071060110410304000e1003254035010400036007240c54282c000801c0502052000140c0f640751490900003612000520703003c0c140d101c1940708820200001e1215480106445e1098880340d192010a180207009a103e0841149140c1400c880d81d500040524a8a1158900085101026200b03a0b0740900a90760 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 187162859 1250 187161609 187161613
    0xc090803030601050c120f0703030605030606010c031817010c020c010c0503030105041d01051503010b010315030609210201020306150c0c091b0a0504050a0509070c0b1f09050414010e 80
    0x200c0b00d6016101402d110540c62060b1040640c07110203a0340103602c03910b0361010120012408406040e41441644003400061b801099142040000a806145074400041c1084481701d04060301c2c1c03210401d028000d040e00c000262080401c0300c8814080e04001d44028010300c96080178a01561054824007803064014010f07501d164207000900003e031011074110211084c4080e62802800b00920a01e817040152118540c590401801018250356201c000a8105420800e42812091012030300d18101c0c0c0d07204000003408007103460300c880f8000c1c42c00000b001c3e00c55034114104d1407075010f40003580310741c008030b41842d5102d00f080c001500d140240700da0400254010500c0b1030a85c1001103841e6003020b080c0c0c0114040c1c40c600756088150381e00c0320001a000500220301001036080c12444407002c0c0000315809080d82c9880070005040900e818406800f040c6004007081c104110034071a1240740d4071a40c0000c500744d4913940c0c0e00010b4a001d6030100c48018800107040303000312040c80360110601d940c1e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 187164109 1250 187162859 187162861
    0xc1608040e0a02030705070f0f12080f1f090209040b040e07080c04140a090f0605100e09010203070203030606070c0b070807140706050d0b1f0903031103040f030f081911010c09080303 80
    0x40780000c2c171001c8e0004851800313016680b4804240007040c000c010480c01c0da60361105140c158074800002c40050001e03c1e1003100c841e01d81400c0c102100000065406d4580c0040c0c48820349400580503103027401d0000d420a1400c0003c8101e8103001c01e0340030995030018203c0d0300c3c1c811980244002c8903885610082c2144003200410605002c8d0703007010344a5800b6594600010140340c40303074412900e042e1130f500c0541038800410441a020600380c43c0e4030905c028004c60551600348000380d00d900c401482c5612800d0000381501c10030860307807a00300c090641255859140d0800d4070341030f92039600c14402030341c0b070107201081e90154a030000391500c02d40340c0c0c0f55500c0d400d00c50211580e00240000c0c1d1405035104000380003411043d02644403a920440f4249e582d00c526500d035040240c040e401040c25850550410841400682d0740c0e02e044004883e40001e290020202c2403e01c1c14072030255000c40758661243d0100c103031002e48e004c20f1a4811404101c020800200c003c601a1048a01072003084481d8000f48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 187165359 1250 187164109 187164113
    0xe0c0403030c02041d030a020118050d03110c0105090304061101020a120203130f08031602030412030f0908010509010e0c03010902010c080304080405060a030e010c080415050c1608040e0a0203070507 87
    0x10b903010305034030f2016202142d407011540d008010048508405000340c0e0020400f29421503090058240026161800410b109002c0d00c0c0d05407114400040f0f001850340300d802c0c03240312110740005c460140c6403240081200d4104022403a03241d602a01c0340c500080c40b01403082d101260180f085945040e5180c07520700305003074400c266402a4000a040d080013101e4681041c01080c081000c502c040d80c882d1030082e6882c601451003406a00143e000a0210b50003408180000009001008400e03900760601c5401014030807000c03030701c644241d04214125400c0500f840304c03614054024200101c0340c0400e82e841c080d142c130245822941f0400c0c000c0d0014a02070300aa01103484480110b401070301825025103003503200d2002c00c08540c4240345000000c1d548500d0075481810a20036600052213a1401e100b860030580c0714031119203000e401d9900801ea480020681c40800c0e001107c003440148000c403101b200460030000b890382c01c42e02c9407125540080000403240b811520840340f1400f400c0c1c80d024103180320f43e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 187166609 1250 187165359 187165367
    0x5120a060509120a0302030108010f090209010311031606020a050c10050f221d090a0c050906040b030610031a0105150a11060a0204080f0a03080a0207050c09040501050108070e0c040303 81
    0x605101814003d0f08001c01c01ea41e0040b000b0190450075840160766075244c610f11508541405108040980c40c1c54901001030307454080031170440350042a01040d110840000905165032410802c5c0c8c00340040c2800110960041503442585000304c0035505d40c0e100b8042400a038407101544800050020032900064142c2e000c05802e4445c00340400010040c040c45612000c42e074540c10400c1741c140038006100c400030a07014900d50042c1d82d100070342002e200079540c0344a007500c54081c2c0d03440380091000007103042d00e40f584174404005d4024102c901c6401d22000c51a000d0050b070005076441c02c405508190081e007441a400d049610180c18810345000382100b1600b030b604815060010400100c0c642600f64108118460081c00c03407040042e691841d00d14201c0c41c065400b070411a040d00a031324040042900b1080450303100000b01c10140e03075a1864030300503007408a442099070340000306070b00344802d101d015448541030780c032404102c1f84c5450321003800c10885501100d01240c4504200010f0000030302c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 187167859 1250 187166609 187166611
    0x302010b062115061b0a120305090706030902061c140115030c0207120209180303090105010f0501021b011404090204151b11130609020d0f0c050703050f07030e03060a0501080705120a0605 82
    0x348000381c1c1c03040051b035030390b10030b852542200302400640c8403c18800c8044090140c14010201c500b82003000b5141035002c00d42a0261060200614064003e46160021381e50802c010108501c2c1c8d2240039581c5400c0a0b07500381041030f9480c80040d103403d0032802c480340002145410340d003505101585041c2207a00300045140014012086044c0b0b02c81d281d00c1c954020005540100502c60010a1075070422076280c0800c400c991103141154860b43d8003200000e403840380c6142c103800a29240c00010820f9501c68400c0c0300700d51140280c0f51001900103161b90009400d0400c15800d5070314698070618402c404440c8913141e6402401a0304103040f01f032501e1420584400001070011000b0698a51f105044001ca8100e580761158103031f09c3d2454498103c0e050b00c11110491703558100036081269030b49006006000f02050442a1000000d41c00f0a04d4000c0c80001c00c800001021100140b03011441007010b44803c0c80380c03050b1486800e0b400306161030035407070304105140e01c1d600400c901c0794035441380b001400c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 187169109 1250 187167859 187167907
    0x807090f05062110030b060d080306010c0201090f06030203180102040e0c160b090f100c020c040209040609020406110f0307082a071508010f050307030b040302010b06211506 76
    0xe207048101030007600c3d030300c0007840b4910454807114440d18604110101e1840280301c03a21401c0c0000c41c0c1c000060700c041c1520380041c800c3c0380040410b0032510058511540d250003844903051118000102994140c0046108514964281c41103811008415090f4020340c02060136240020b000120b0184055018004000040284903054050b0361140c20b00032201761020000d0350403007144454002010003622070020b503560002c004400c218071000391a01c24810703486200700e400080c0e075800c65644d40c1022000d409010340840d51650f039280050700030725012281d4003440c0620142041c61400100a44103c1d503040440d062410070f403080c51501c4000401d810500c09400c03c502a06c1c02031342084002d000e00001c05802d060080180405064501c1c164068880100c441344180899107001c40d00720b00b1070794884071060300b54841d0302d0185e002d0040c09a045401802c04501072494150881e000740d100c400c464003407842501c90448010041480b00c0c03080b80c1054040111002c1445c140c520001c2c1a2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 187170359 1250 187169109 187169137
    0xb03060106050a12020f030108150906010510140a020c0a09270203210903010f060f0b07140303040614060301090309031704091103041a090a110a0819030807090f0506 73
    0x44e40031181101280c00101b048417801102200521150300c081140307611a0080380c0034064146040c403d055924003050081c10701952400300303c4066513001e60080306e05401c0c058482522410010002036840c0c44401d94184592500d44002a11440034400c42000300b0680307441043c11441061501803c002200b002c03600b520940e4500e58130074078609550050564054596540d03152190300301800d640100944d03c0c540351a160302003103011116610b510490f15a10003080d1540c15504102d61841d641081626850100004000030004e89a00c101c0008041100c074081c29150700040c1406c80daa084401400b04a812405201254000b010059503040c800c10340c52500d500c0c5c500078001d039802c50003140c58940020080c4020440d80501c4002214400301011f1110701d0b04600309940c6280f0780c1000b45c003420528030f1444558490039038120240a21070304490701415180058450304607208c5090f00007070202c101094615124285c1d4030110303685440d032640803030308203000c10200b0352020031500141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 187171609 1250 187170359 187170377
    0x2004150915020d0302030c07021221040b1207050403020904080306030105010f12030e0a180b0906040e030706090c0e040503070309050102060601021e0c09010e070906081312020703060509100f0b03060106050a 91
    0x10383d610f90311030180c22641750240c00c02f20244c00e440101440628204103c0520a01c420300007080020b050b20702810740c91845501c5502e9403c41505c4030f1041d90406034000141008010902c9003c1c00118050340003034008108688c4c0c1c980082d50700c44a1405a001c03510503038540000800e00c43c91501c021402c0041240c80314030740d115541d200907070319107040340700c0607884c0d1031010054601402c60582c0160142c40502c0001c0720304080e280c492150090080c6851383d00c40042040c04800720000000d0610b060700141d2a06050600384d9a07504110000c40c00204840c1d0041019407012561600a4506800401d80c90010001e00b6545550007a45102240702e1208044807503911044032034000c00c4048401e04d050b003041d1200a0241d0015081001844030140901c000009a0880306026a803c0070141420a80c4208228204021544042c1045050409118224201181c41180b0561002c000c003e400d010a01e0f000c1610340104455601d90030590040142078001c000401010505203815064 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 187172859 1250 187171609 187171613
    0x115021c0507140d1805060415051605010207080919060e061c090f0b070203030c091c020d03050306040e070b03011e0f1503050105040e060a2004150915020d0302030c07 74
    0x6080d0004c0c440e0382c002506050200c5807a0400c01d9507001802c0160761082c0740604210100d070ba1001c54100c0d42e81000000120900d0018142c003135498682c0d4084000d65440115060464464100508003032050040741541c0f913401504071601021580303182c40b00e4641900b0f0f101006030980003404960544440100b0a6a542003148140007002d4131500000aa03081103040580c900c2000078401c2055500070000c1c4000f01910000307490f0f0380380382120340340581210f80328005a03681c0e001c04000e4003c0b004003074003010940c0210184d4800c600650b01000202c5003090844c0e60380045205070340d04c10200300010f00035508900280e01343d1445850900c002241c1c0c8203111100310340180e100140c10300207240c240d05902c1d41406840c0c0100011981400703119440c442ca180c03250b1014090034405966420902481503201c26001003150240c0c5416840ea82e03284201001043c16580d0000050304c0340701b01180c03d088480840402544680c010048481e450005a000354030107444610b1040c424002d03400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 187174109 1250 187172859 187172863
    0x10608010e15181f0204050415090b010504050d0b0612101e0902030319090f0b12070302030712050c0702130c0801060f120207060b15030115021c050714 67
    0xc00c4800d4002040600785490a100348520060f1a15440007166904041403560000744407804120841429007160b003a40d01c2d2000034450359000e1a001800c000c24000d9100312140440c0446214190502c6415100c0c0700440303440c1302d607009247d8000d6003201c00102040001000991000024194025808110010702d20346171641144440d81c2e80c9403148001101c4103070b4020ba2802c461500103200d0310415a0010762a80680c40354048004400c4103180c40b001c0c0704045800041075010352101081b5103a076040100760380030960320203103d100c000202ea18284603200700c034401c800540da41011300c85102900d1001d0800a0100d0194a000744000750240c2e54840c1c0310341c01d14211a03c0001c0480104001420441050707110070706002d80503081d0144035404c805d9000d040110b4040c0141c0d10801440e1400042c00a02d00035608860b51240c3c0742241c0031240d00460585580b4041c1d0703d0401020b40c012039564451820303806060814540100300309008202038100c151180c25034103202c00316808828 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 187175359 1250 187174109 187174121
    0x60706020c1b09010506090103020d060b130311090105010c0209040606030b0c1210050907110a1e020a09050c040b0702010e03010c0801050f010302030f07140c0601120201080903070b0606090301060801 88
    0xd619030001807614500e1151849aa0341542c0c1c03e84084449601d001c00249603801900206414141c00003210041c404581d0f0004002d021032165542e1a8880040320f507110704c006005c05c039003074003100303032110360500d00390f15a1412600c05030f69a2400350a1039090181e401c8010300202c0d6581e442d000080000345185044911a0301d502c84a6a01c5441a0040b40e5850340094261245946104401d0169464500029034040210b091600000701c180030728a05c1d002c07180c00042c210504a0351113620012140081e0304495000f1150004c1080d203629610044540a4420348003501c0700700000c0045815800103001000d0050421520410409001c6800e41d900b9240400c0050500d0006004034605180544400c50b403c0c42c003181113141110f1250000000645424140400c042003103030714103143d00482e00e00c0c4418205940003560b50707000e110180a8181d030100d0107c2d08031800a00a10000025158007607080300000c031081d194030092010941c4000d01e41c0d40c065480d20804225420240212 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 187176609 1250 187175359 187175377
    0x305090a090227011b290405150702190303050712051302092809140a05010b0a0504110313030504080d05070210090303020a08030603070e0106030e0d11071406070602 73
    0x1c02520740720700a40321440040f1262040c14081950054420b41c402d00d1000c0f100b131540040a000ca6006201c2c681d0244000060400c240765000f4080008000f004144807003012248401800c8a4070b030002c0c01e80c0c03180c4104c1030400500f035044801e08042486a00090782010240c181480c0851a2400103416548201c07440003180009100e408210b0400952090303201d49003680c0895144009104485c80d41d82d02081b98034159294407400041c032019403c1c2d104201d11240c21144025581c0c94198003920b8401040e5201d4900d205000810b804c280c01541021075881100518507a0344407138409403002030741402d404000b42408045041e400400801c107080d034544c0c4400e40c455409204000c012040003c0340002c000c0c01c1001000000c0d00000c40c40c070300030b500620303140d229514000424900041644410b0300b5002d400d000240682c1c1561103050b0414000040d00c090f45400780040e200d00b0751110707407a0740c5640029070420011039401022510100002c1c00540b81c071100e900c0f010b059800c03111074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 187177859 1250 187176609 187176637
    0x10902030616120515180105010c0f02060d0e060406150302060d020d06050418060b0d0206030f0414030a0305070f03060b03060d0203010f1a210d08091501080606011106060d0305090a0902 82
    0x11745001c514100c0282d91608011014140340c030340c10a80002e11017460200300400c102d54012444086503142c40a0701c8013440305080800c0010660504190b40310b60a580c250b845502c1c000624040300d44c030032400001d40b50050007080c6029284005440254070844000c01002c0da1003e01141994550103200703c0b441d100c0102e580b5140c1d003810540129501901c0183c031820740980581c3c0141c403501d0680340c0c000d0034030130b83e40e1131642ca03414003140b0100701d503400d0102c500000503290440d0350035500903409074070740e941c400000c0c4250a4064085950b80d010384c900c0714000b880003904620b401d024600c0d10b00d1002d000810000881000702040e104980b11403004041d40415800f0b0300e04160784404030010303aa0000840f00e2189042c1310340c0340c600201859040080f01c0c00080e00c040d01c1040300c0f0168018100c0158bc0f6907a4a0001a448942c151882400901001c484401d81d44000500d54001d440050840c21030042c01c2c2d800365402d41c81407070801e8001e03044e6100010b5003841403015110110b10504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 187179109 1250 187177859 187177891
    0x112712010e10090c06050306060d021215011b110604030203010f0f0c05041802071a1503010510030b06060a020a050d020a05070906032609030f031801020109020306161205 75
    0x1c190790424020924100c50b45242849140c00b144290030742c43d0840e110384c10421741d01d49035000859414441c40880d049202d00000b2903922041c080b2038010f208011815541d0020781c10341c801100c800c90140408149402d0f012410700104981c4501030103040c00090160f031500c0c0e83e80e0301007400e441104150380052aa1151601c801180a00030820b10f00c0003460083e00d0a402c003940607029030740d480c80501c011903010442c03000700320280f0310700d083c207241020f1f410074545010345089016503103141905000b542000086207a094242050340207499120415245642c1c0e4001840080d81100e0510380443c41a0313407407400440e006100010210f620b55000d800c410029080ca01d16202061b44007040007481c244d41080030407800c009e80c40381070f100150b040182103000c510b410820300070100c00d19130600407800000c001d440c000005000d0511407403105504814084e0040e404c9070541e4401079019000f8030f000610303a0100000c0180820054245801d51480c010301c5001140c030b0894540c000981269 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187180359 1250 187179109 187179131
    0x3020c150307021e0102090d0809010f09050a03080705011d06010e0702070e010e09010b0316050910050d021c1a0103050f0724020c100e120111271201 66
    0xc1204041020300410145903081c0001c0095461079091612000c0221340c03154200821004c0d01118040840285072222003504e03030503d001194000000c050120f10070700003400996004d609a1030848030010000340303e00d441c54450059a80c0040300032101d6560301e803501e0710845a048452400d0441010041440c0d41c10f2101500c81042c018150b4010b56000d1a01006400c03006440c203070540f0660401c1611507100e0607a01405003072080c0100350306008103200006010796182004084a030304842e180c20329140e0b660170624000d458000d868001c0149807400c1d0150170f2111040c2d03524034400d11820345d0314820b602c51a03410f1103945d40800d40d00ea5001c0040003440310402c81150700c0c602c0d46001d402d1061806450111038210119031100c0016107102e070317280c03c500030700645041d000050701286804094200040121414004031480390007a0140c400f0106814450400120311907888245006102410750308008010301c80c44075601c14008910351940c82d058000002c07103400c1400865200c8080b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187181609 1250 187180359 187180369
    0x30406050103200a12080c0607020309041d0a030f05070b0c0d1406010f0f021203090a170f04090f06171608010902090f04060b0d0c050f0612150f0d03020c 68
    0x40c07209840310200e00c0120034200d40d1100413020803100004030f5004c440300705281507507490160120058550181104225120760044000d00701c0d09011101001b0b540300c00e5010200e4040340003040c2c24142d00245610000074003c000d805414155801c000741803190555441c2c0303003103408a540d01d2030000003241b058681c1d80e0b140586030710000010400c240342e20b4a040001c0510801821542c01c009054840d200124000d00a405040060641c1a035030f924140602a5860a200b101120001c0400105e169001c041100750b507200305058580602e85841c150307990300603060a03080400c0c00c40d034a403800680b1940c05603450910114a20250000140640c042000d4070b620707500101c01c60b4105002c1200507554a90102d9012030710000521042d240c40c14940020310491a0742600f1282d900006414400248120f80c12514211603032600d02003000244540c500400090b800c5211880000c01c0c01074a100c004182100c0c00a070550f20951400300c0090807400d03a000055016800c005003400090802c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187182859 1250 187181609 187181633
    0xa0c020c21010c08090c0906040b060409051008070807090509011e0c0909050702150c0403050d0203030a0c0f050913201209010902030c010503090703020604090e0c030718110f030406050103 83
    0x10fa41081241c0c0c0c6000d1580503141d85100d09480d10644802c0700040b000d40d106ea0111111580140c52280c8a079212005000200419a0b07424201d40102c1d00014012070001203400982e441d0f030b4046c0401d10b00d0aa69680a05009414100c007552106840700c0b02e0b40360138001c050040c0f075903138001c41d41c00d160940280040c00301d900401c0e100340c104001c03c410650005100024003c4041201c40e503030760b407000000082d0185420050660068810308420705500001a5000c0c444142041043c1649200143c1d0660400300c8244042001400481400c3c503000f0454640003c52500105043c0041c3c103041c4d03c1455030f400c5805043c0d1000c10f1074415080e111301c12941c000081c00080016092580010340d1300c09034200818100180003000494824091040000a5902402c1c5944076500c81d601680a0300e072120a50800388180380c503a480b54580010200111064100c0000b1900c44480140c805016000090b002c80c7d40c0802860004450282c0114030aa004100c0003031030754190728040b041d91003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187184109 1250 187182859 187182881
    0x6050f040c08070f030219230c0a1e06060f06020c0102011a0904080d020a02010203041109071e0203121503060108030310050906130912030b0109030b0a0c020c2101 72
    0x21811641c001201c0e00007258030381064071030910042005822108401030300c43c0c82ea04900901050921128568101048841c0241d405051040915220760020080d000700c1d0a5a0b0290380f140200300c001c14565040340c0c000c03507590b40421301e4420172a200d41080d0b41e625440311807441c0500d841003108a505021419803000240b0081c450001c00d03501c40d000c59005650070b2881039280314041401c114460b800c6030714070f40c3c01040a5444541042c0d01078000d4004540590760744284104000c81032808200700c41c131414054071903004180d034101c1100c0c0b480200010300415444200050f03c0c1c00c4800e0390a10b40700d500710105c00c0344c411080301d0a040c140881a030110383c140c3c4c42441030200f02c0301104226001c0d2003080e0f600d110696180000501d602c81c080720030110180c503001c1c00d807040c000008048880001c9680f010b21100b0744a000450300ba003040d100c0a0701134540d0001040f035640e0f0b150081a405182481250302e4070385503400140400510905005808540403400b0ba0b4518080c003803140140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187185359 1250 187184109 187184111
    0xf0a0c0915050402030604061206050601032019110a0c0f0803040501051603050d060b03060901050102030313110411030c03010303090605040302011d04091e0501180c03030c03020a1506050f04 84
    0x1915001c5420074440745010340762056801200207901d580f02c030380c001c4005010119400013044958100032001744025180203000074109003090001340c0c2008850105182002c42c02d030718240c4842c15503141180310303000e444100608031210a03081002040602d0b025402100040d59082c07610b20f000058401940c0100c2580d0400e00041216a0b000380989800121140c070b00844c0d00141e18088580784280500102d14a25201000c9000f40700000598800c010a5800c2c8000f40d8036a001a656400120f41000081e22411108000035000542d0507a42f0800540082080001c00f000c0400136003048034018510040400104241075126072404000c0102c0d080c001e01d0281144c00007060001500000e115100080d0210040e0761a2648065003058001c8070924407641511a0200343e81c0310f101d000e981960810b070039042c59031510304007028116071089400f00384500d0759138142c0e01c1d41840c032015001d5003c0c58542501044c60002d544201144450001404504040400841c0642c00114900803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187186609 1250 187185359 187185371
    0x17130b040b0a0e0418030507150c030e010c0c171e180907030603080301090222060203040f09060e04020405100305060403121815020306060702040f06050a0b18010e010e030f0a0c09 79
    0xc4070105e0440224240c2521b4140d9880c14135043c559031032100410111680742ca06010351042c1c40c0e056221120b20300c29400244104242030204035682e010f1440045c0070034183c0c000c6019801d075510700500b170380340c071a030381003050101c411020550ba90071401038030050001c8107050030502d140c2204100c3c0c0c0400103080c20480703070f815a1280b1070240014020154481ea00188604203002c02c2c4101c9140e20a03508008882c007a1200c500a4403504039110700510306103191804207985406026450942e0f100100304842a961a003c00014150241c08d86845280340c3c5c0300400440c106000081c4558020b40b00e40504e50f5901410004541d903007545416041101403018002411240030801060780401c1c0140e1031f51250b0000405900c20844029402854601c06040b1a161600040103d942c11501034080c05d9480d2807100c440d11070000001c43c10100140e0100480d80078159640300d850040c503010b2400e00001c0e011918103180883c014003607a22a501401c10015103900c0c0720058841000140a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187187859 1250 187186609 187186631
    0x40b0f040b06090a021b0a020909011107080a0e0d0308040b160203070b1f0306090521041802040b0301080c1203090307030b0c0906030103030801060e03030717130b040b0a0e04 77
    0x7018102070001c901c911101804141e100350b603501074960100101c5101c07a1000d0710303500c003190b883d080400d00301d02808250000403003102c0d040c4100c04490720071b00300c0e042c913120140e0395150465000c200010140100c0c00f0f00c1e25410b0f01c0385515104110310031b40f07807a000c038145400c00900d20350300200440140101c031205820340a5004c030998a005034851260525502c3d80a40500c0341c10610003c2d40c4401840030f00001031003855001410024080c50a4a030581c0310511202c0d104244514081e0039171404120400c003103c10252004c0c1c1510303044100504254035000711500355170080e4440c0c007651b0301141d03000c0c079140b03410726602074181c500c071009524014421011a450b51284c1c840074180c001c0b200d0000d0b000080000c04c585091030000d00c1280d603507849240103440d080089c004d02c00001d98140040300903040c0041190001b50304000c8200101d01300244040c620341c05461313005101c400385600010350000340c4003d0009041e410840507251a50307000700510010780607101c684540c0c100078011407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187189109 1250 187187859 187187873
    0x2070e0112080903070302130b09060a0501080c0d06051302070302150f0610030605030102031e22060e1009060c030c0306031e0f080d14010e1519030b040b040b0f04 72
    0x301c034a600502440c2c03201e02281c00607007806016030010350419031225014490380700300d41c449850100300300e4240d95503072600c9040c40145882400760b240450031140c0800c46031002074000d0a150b06e0468804505691180003040c006285180e8101e6041d8021640e2802c15405229400020106070302d40e003d5498910241c110349900603114900490211015070b68040c40303034120001414001d40250340e24240030501060140790000d009124201c034502140b05001303d00c8128514110500c0c2407160750080d43c456500905010454083d107105408024400b0301850058031241070007000f00140082c1400d1024098a844012400801d46043c00c10300000d401c0d40300340e415082d03456883d040b040308240b501410807031507004058003460010a00c00c02c685981d4016491603005441c07820030340c1e640c5003d1182d40d0b6000385c845200c06d0200c031406030442c0c2007001c08440d41c10a00701c2512291681d03515a8486403605a070181c0c0c4502088041200b44aa64403503075400c440c4d4036413144401e2401c3d403035003d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187190359 1250 187189109 187189139
    0x203190903211428060b0301080c01050c03070b060f030a050f012711030102040f0306200a050d240b04080601081203011401090510081504052802210702070e01 70
    0x700400402d02e5111000c4010070310700c1081c11101c10400c1000c503450703080c2c24030241c00912070749d0080e200383c60495a19510600907030f01c00c120400001e40c01c000c03850740c1c6d80c2003400d801071416411152641c200122a0b908100c0100c0c610300a80203000110b103c0004142511880c13001400038500d6403008020a0309111040304090760803602906da2400b4890019019110b19400a64039111284c0007006010456102000340d1100305072841f000c02036158003d031140a0180c8203070216200b030201c0d140442c4c4a8000a004001400c07076502203040201d298003a031502038102110f00600410280900c4200700042c0740503000840003090307610b0110210400c0c0b0b11050207282200340920302c40180c07590080c0340c00c00181000030900c290806111390001d0a41704211070411241c19403615005203803c09201d698000c8044050a1650041c101d0b14101d00e2925011034442c6a035080100c0140342087d504161014181301c8600714040c24021002071402003650005070f81040c80ca4010402a00282104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187191609 1250 187190359 187190371
    0x20d05010e0a0c020712061a04111c14010e040c05091302190503030f0c0c030d080906070e0a0605090f03010c0c0506010b04182403060f150e0a02031909032114 70
    0x441c500b1a5581d11503907608103004503030b400c503040030b5040001c9400310024044bc0b00107100a143e098452000e0b10068400101342d5240d00d19102d030040c040245d00c0c00c10213034494003400a038110070b41e40b040450920312040b150200c130401d040340c2c0c00007140740001e1600c201912480312641e9079424140065101d1186c40302c012034840e030000e40071a903070000f48440980b00000405545201c80d85c1000138100b00e0080310340040c03e000c2e020000c2c1d50240590201c80c3c4c07052000c4e126075143c1d07042c420300350b400d644500d240700e82c00515141c1d0501c5554007402518518009030344c85950001991500d28a84001a04803550702101804148426030910400d002c203c641c081e404a102e1072029000c180351640c7c8000114601c1c1801c03030110a000c121340026141e516842c40403c20075803152035415030509a40508241100c7c00800f050702e44171642c01031340d0004046491000c11061440ca00402c56107842e004801203007038250b55100501c07a8142609512910610074400121000e6076901025001030078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187192859 1250 187191609 187191611
    0x51003050711060c030f0106080403091e050a140a0501050a020a170d1a130908030a05071808100506090601020c2107090504060e030705030a050d020d05010e0a0c02071206 75
    0x5241a1049810507507441010040e00c0c90f5003400812100300750710882c0c8116100182c1d0000040c0e50744124051485203415541e0800142e00704040445040c0d800020b07943c21908622010896a5035610400020801c1c007562a80f003e00c03201c2844180f0005030300c007505002041c003001c5030554010076040c11650703000c6680562400721740c605000324012008481440b900d480206684642400a0043c00100881e002c1c1d00e903e4503401d000050740c040040040c040107062020a003003074090f80200d42c000b0114200300c900717a09003441c506001091a03001da60f8a91040000c0c0d4070050301403082d80d070050703403c2e5542c41e400d2030817a0011b595240d00c020040c1c01203445400d41c16424050b4083c11520444c01001e4410300c07951050000050a0144c0341030740c4007841c003400f00400e040c00004481403d58044013850414104850913601074005034850305150342c0820550401c4501445031a000e00060000d18100c0e003040403c11040725a80e080d11002d5610800003400f241e09009900d000f1150300003c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187194109 1250 187192859 187192861
    0x2010c0f0203031c05060117060a0e0603030c0312041208011a0a021c0905010e0d0c12110405100303030b10090b09011e052205010905010e24031f05100305 68
    0x2002c07a10703600c01c2c0602c00032490b4503140c900740012015003020b801001c0c26a2108418640b4a002076885a001da0385158440d400140c20407481c0b80d2868425401a0000c0c25a030038001440341c003e00355804041400200e80035502044100000d800440c844001c00703180c964225818480214918403038003075034034044074000c201e03100c10790700c20000c9048107211000c1003d2400100c01010f000c00b082400b45074089402c1e000c50881d1824205101a103564100b03282414052600d540600c01c045d0500050700c03402c100005903521601d441c001d00d40100445644003131864618100102180c41d04446c50340700c2c01c0c043c0c4840d50b509074080610f10a440000f42c44035604d5010354010380320b00103e14581a80010f208015860a9400001600d011402c01035660707035100a040002145c403041c0c0c0140da010a600e00380503c01c0d548111005000c048c405804043d40d0315261000c8120245400003154402a0002c00c0089105a082803a512001d4580c05d03081e00030f09020000d2000c0c0c45941c0c3c0c8004242e582d40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187195359 1250 187194109 187194113
    0x203070c1104022b0f021305040513120210050717010303050d060905040f050c0916050304031709010603020f060a0c0b040c0b030c0711010906120e030c010c0e040b060702010c0f 78
    0x1074100c5201a02122500d59005949413040220202d00741c0d060301aa072800b8a50301c244001030086a00c0c195030420620541b608010800004101c09400c0d46550718034481000700195000030038a1452109030001c00010140004200a41d10020800010840d52001081486401c0c5c0749190540798941000381d2903040a08a110060030381740d210f9a00c4074140350900c01402403040d03c024481e8002e50642c0d013100210030501800031001d596040a140c0c400080d005002c4c8600c01a40c0c0040c403038501544c050042e900d01c0c3c80080010f540d940240e0b551000104110318003164820400c3d1001d0300c0075030901c070080740003a10344205200301a00e550382820014080080c0c00c4044400f07071480407001c580301e081902c2c2c02c081e0364000c0d4800301c41440051290400d150b010741c4001d8100c90407580e4803a80048080c0044018042c0400c0c4102d031031005204c8284074190030f000b400d41c0e0b1705d01c039a2144100d400100803c010b44003090207580c0240e00030021440540da100d90300017640d81d00701d01e00c4d840d0300e8114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187196609 1250 187195359 187195361
    0x5040209010609150305150d0c030203070b0f071401020d020d0c08180d08040f0609050313050301020708030a0c0306080d0f02120c0c011d27060306070210090606180606120203070c1104 81
    0x86108c0c0d00c001400754120400451101c0d02c01582e00a03811500d29a44440a840f428072517081d011200c0c20081c00084001510444508074841180002509050310b04030101c0691300440715600d030044c1c0f0b481041d40a035510072480c40d032004c00a0b95035000c0319014440244c4460004608508002d000000070302402001010003020a50184007082101460b080143e04c03504007a81909503405044000203003032505000340c501c80c6400400c0355180d41c0700c0f43c040074020034501e070410040c03544500d800200e00606028602025400f600d460081c000034401c001e04280e4118800034480340103201c10107c03000d00040501e9250801e00307048190710300c08901d40d4004040b20401b10ba000d01449042003100d158079840c041c09141c08800074500d41c440e01d0405442c1d510407121240164070046030501c11207050f8002011040c060040020740d030351038440c9030760703200c000303a2880c144036844d8401003164541c4074010207034490b0300820071411418120700051072003d60160207040400c0c80403d903802540d031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187197859 1250 187196609 187196641
    0xc020f01200d050c06180706030b0f0405090f10180314040b04080d03060801020a0e040522060b01020609070608060103050c0d0f0903020c03011a09090f0d0305040209010609150305 79
    0x1074074044807100c2034000700003003440c0d0044100010034011107002c80c010307543c10b19900201c01d080307401405196082000440c01044802c035496406a22100003c081c1e444a2050034007400c85030b4042c054000040304010316000c080d25804044600d040e8910b0600041c2e0110180000c0d0f0501c1d10020805000c1c84400312800750b5001012100000600041c81d00070000c2c203408031880c6a00d06221190b900c00c0641d00b02d018030380b00030000c220b446145181c145010341c0181c1d4004004a00c2c4900000354101178030144458400c202d84056030707072100700110744e0104842c0e80c0c00305401001b06821420b1200040990700c0140c0700e14185600ea00100c1c0c10101400181c4403035494501c1c04110404a0b40b0b035600140c941e090041d400750080c069040181d08045c025005071196107400d455065104d5070900c51401801045080c150050910703804601b00e05200c080c0910015a40c040307580c0c00c3c54010041c0103801a40614107220507648100814400d8075526803652605050010f501c0e914881c2c00405260307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187199109 1250 187197859 187197917
    0x1a0f01060e0612060402300606030103030e010c0501020f0a08040b010b0a02071403010204170a061401080c131103040f06050703180f020a080303070906020c0906010e1002071a0c010c0c020f01 84
    0x100c90a2019141c1d0496840c03002c4103100b5000c4651f05844100600c00300380b0082c08082d0001e04010a159075550003502501f040e184504001403a088002d5092800c0360072038100c000c001904c0310240300034001411401400b40c094403400602d440021000a95139014521401e1040c424401d00f140c1c0b9540c00b035040c1c0313000340650040302e5180d86070b14450b1a00c40a02580842d804d80c6852054940880c40c68070640c1030b0343c8804010900044041c0412200303030110442041c04076110201d5010500382e0b540590f0042d481035500c2d80c03100e910352414a0540d50000c011108261402031065240d501c1a10040c02da103400c07880303100c1d2010460000c101205880d0f0450125440300005201c000c40e8400e180030300b10341d025401d5920140080b42005044403090f2201340c0020341076101c030f0480d0315004030101485c2e076042c0110352044c1e95408020b01007160100740088031180101d03103115122000c0c0140a010061442d25000c201c850340d0004e00c0c54034100705911f040081c15502807100c05924400300907490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187200359 1250 187199109 187199137
    0x15030224030a06080f06010303020601170f2e0908070f140f0c10171810111809040201120506010504170303010609080706020d14071a0f01060e0612060402 68
    0x850b10701c040c00c002e030000784103485480c410030004001e80300c4007250180c1a00d5040e4040d003c40c1e464151800d8a5500038620a080c6005244203800903100c02c10039000340c4a4800104039a2000c001803024800800d13441004525040050800011f00c0720400c60351a19031181c4510040ca501d410544e8107421100ca5a2902c1d1148245525a039400080d8003c80f01400b20780900048079150411129500364a07283c0c0491648140810740c848001d01c2101e500c0200c0343e00b200d0000d0b040c40c28020542d5580d141013003501c4000a1080c6000c100301081d03454525040d01c0410803800c00d640007c01460306690b03c140d0007503032000400c0c0700d43e00c60000c42d001000c10040c44000644910b488a84940c800c1c41908081403000100140c4804041038a104860301e40c1c000d002c0240003500180d0718148035081350080c441081010300300280b0074003a1486000e42c3c0101c0700c0060303d800c4d2107200788030f2410f0300101c0500102021031103480d610b46040740d01200c0d5001a011154541e0f00c0490b000e40075189e000700e814 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187201609 1250 187200359 187200361
    0x406030203070507050d0e040e0a0206040b0a17191b23130608180a0f0f0f0c29040b160f02040509060708060d020d03030513060c110f011503022403 65
    0x147c1c1c8500e0184444070126010030010741411701180c1d58452040000390003401c180400c21410318204c014203603100740c50a1516201004c0101a04090300840d848904102c2d040e035000c1090700180710f003049000c90350310204562030b81c00c00060b16900031005640212003103004900500400b030700584100403007840c0b01841d059250000a000140200c9111103581c10030359884250746030020b0300041031500026500d0014000d6181e00303400c0c2801c403200b901c10740600c680d03941c0000c001d003901c00000c0000c4815220003014140d00312074000c610340c07508101c0042c00d0106102800c5103400305c1c1d81d4140401401c0003555100d2800c0680c0b2044440d0280d170140c68070007000498100418072500c1181d1643c0d031f0715981d0781d5100401000c03408400c40a90001c1d011080c103000280290310650704100d100c0080c074406601c9075141803c3c1c590242e121000141e0b03a0074014109402041802c503e014600300a201d1041c2c01409000725804510020f4899001c15000b0b00011202411005204811680e000d40d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187202859 1250 187201609 187201633
    0x405070b0f04170a0f0f050114010e04060e06090c0d030201270c06030614040504030302120411010905090c22030c06030209100824040b030601120308130305040603020307050705 78
    0x740d002881459800022a6100c4520f84001305003109103503842110024603512039150080c0780080c400080703031550b69586000b60410111070666000744901c4122070414a4545030200a640607481813414552001007801420000882e1b9102480320985119824112030304080b805044801c070322003414402c204401043d10b821005a1301c2060003082010203032540e45400f101210400d00ca401450a469800e10f052840e007508020b0700305020386005030405001010041e005001510708844400e82c00e11080040e50308200741c040144401c030b403048114600001600c905210b00840381c102d128280700220820900550090040c5400011040c3c00c40e40301c01029000390700c003940c1d682c0300701d5450a80c00030403881800090312510f050b54030060300900d0407401c150740d00007011000e5401a02c5203003410b00c0b502c003001554000e10354103900c05030f16192410b000d0010100036220342c42d003110000720840460340010440b000c441191800682e29034035184100c4490180c2003005016019045003546 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187204109 1250 187202859 187202887
    0xe0312010b070204050c0f0304030f03060305060709150c2001020a0506100e01050a03020d02010c020f04020f091305071d0f040501091a06090a0b09040608012c06010501090506030405070b 82
    0x91050320a4130b007080107840d4010b07400003901030f0740c0340003507405c85c10000600004d1082111054055490801081032602c0e541c8150921706e04880c0e4000242000c50b04008189100c02c1c200b42408940c240340178040c5190f182c2c4040700c02c0b000050800d80d010956940100d03442081600d801d281c0010541d5031605104421060b141c2d0a44038022110920300c00200d03d5140079540101101d9000b00b1612141c1b009900655104840005c180d0340251014409d080c03a80750341c00206091800045c070b0315590003511042107008841302e213a907150b0a2404080252050308807088180c0248511011039001030000009540c02c1203026403280c1150501c000006e190304150012072011120340303d00880740d900403003881140d005582d40c20364010310702c0008024042d08900100000c40c0c0c0a4000706545881d00442400e598985010710305c0c84140b090741d5104107102c0c0f0780742182d08104801801e925407501d0b0000300054040d00a0300d2141c0c000201160070083c0c100b010f040106800426952a4a00c40d01450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187205359 1250 187204109 187204117
    0x90b030f0f1c020c1003090c0902031003020103060801020f090603040c050d0605040302010c2102220b030924010b0a020a0507030507060e040e060a0203060307030f0f031209150e0312010b 82
    0x80114852070041c08a264004a407840b04d10f00094400603010905000031409085862419580c856191201040c090b60500085104d1145d0800305500d1624600c0018200c0c1e045130b0008585074414454000c1d40311040045a0345040200d13480741d1030f034072281091030a85205501580d440314803880c145081110a03001144600d010380c0080020700e5150341c0c02c1e0764042003100c030082d40b20142800c0f4154020650f02070014a10070501c5c0007102c0300381502c0e420601c04550408108000084104002403c0030000088402140650340e03288040c010020b01d058103041c011060b5840c0046040c1802500c00c000c4d0f0061a03800508440749a0342d281801a101c20703590007800009880045007218500702402550501c00b6540000c020307594551014a0081d040607180c1d0341c0c14001c407580000820745000031044080e008810603041446246405031400d4003881c0314001003802d14040c0b10201d02e540e0030a15081030280408107007080143d4096083d03214000031880800c0602001240d000d803c0c0c4050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187206609 1250 187205359 187205383
    0x7020a0b0301270b1305070c080705070816030f020f060708120a050c0f040302040c0207031b0806010f06021005041e08030402030f0303010515094510090b030f0f 71
    0x100c40d00040403d501003610b885080341600004082d0200784001030b142d01c01c2e54008807d00c0c3c40103406d101c3c0c6e03403580340660008500381d840364011001170106003014840a1a9610507244a00e034151950341c40c00b04442c07544402038402c404d4142c8440d27150302c1d014100d03010711b940401c81550381d8140218140d07a5042c11b450a401040c58000091422817984045030083c1f200510018201881d5900300000f03003008051480840c0a1407000000141e540b1100c01000040c2c25800c07a245412300344041d150a81c140c0c000c42d81d0f40c1030b003001082000d4010600306008543c64401007495170300c80c1001c43c4d0491015541e00c09104210008500344541b44002c0c50081d031003201580c8041080c0408940d80e40800c0c06807a6222010030a80310a80500c2c000800241c000500b243c94556004d10350105024420000365441d0b8100c0280d0b5810421a40080390490940008107285414102c41c91149007046008090260b6918426411580d4080154603600b6450100b00c0d01000e140e060b800c1d441c0c41c00c800c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187207859 1250 187206609 187206659
    0x718031a1b0409050c040b0c0f010c02190303150b0a02030c1005010f060804060e0d0806030d03050114130929090a2d020901031209060e0906040207020a0b0301 70
    0x20850702425003030403003201d1040062a500b814100002903004090141c03801e924400c2c10400040ca84c1e0180e03028010200800c8017401421034507c1c80f1500307450818101008541003192240280d0b07000d00f240c0108943c040c98002401c044a00a440b05940d5941000c079000501140d00e403001b503800401004c0240309281558070340781c145003000e03042d60700a00410a861060340c1e0b0030f000e0b041c49044015442130099a0101e0400721500c0c026060400c280780145c0040e010408110f0541400c0080c014020444c0ca0108601c2d80f40501182c44000c2515901d40714442d0101d1418984040c0d81141c50300f99007100b11642d410308060b00d00c4a000b00030381d4580060a80c2280010041c800100b010207c080c2c214002c544005249003004060300114840038110035108400301025132915000140690b10a26200b001c003090460080c0c09207020381e10003800c01403210f42040d0540c96000303003690040d6080c1c0c0c01685403803081c400141941c509802840082e0004800040d00041280c025070100b208661 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187209109 1250 187207859 187207861
    0x7030e0a140d0912032319090602030a120506060d140f0601050a050409020717030901050708060d0302070308030402041103090a03031b08060d1103010e030d0501060807080705030718031a 82
    0x5026104040c0a1207800004180c01c14a000400c0c0212504046903204801c284100f221b0240c03208110b030803a9010003500d0384051112242160070400301000791170300d8002982441d107107100081241c2144a00614060346a001240e05e540742c0c00180c4050107001142403000b011015001458100c0480d17901890010a070080f0b1455400360040b20924080c0d56078462401c0d0400106502a40c404001155000040b0032408100c030b1800700614000d002880021850b81444100140802c0c0041d001c0b03032190b40c2100c181d40020380c0014444085a40c401105a1241d42d40c0c00010010900c1c5e10009110780f800204021000c41c01041e55003000e8071a8030b003004039270000c18200300b41c0780314001d800e0082107584010030160314117042803c40142c801d2a050210841d10004642903860011000c2c1c9250700c0412103420001490103894090156840d00c1d20a515003240300820303943c80a0005030601000001080f00b03144542c0c45040c00260591900084a43c5c0b8940b1148039035034020400a2500500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187210359 1250 187209109 187209133
    0xf0501060503060d06021c06060203030603070f0503030904050903070206131502012c0c0303130501091e030f030203130b0408011406030601060f02011b0801080706020c061207030e0a14 81
    0x1002d8a005a402070320507445001d1039a5120020341c040021606011a008003002c1d205495000303840290409501460f2241407410506286c401c180c1c000e00641c4901e118180100d0303d0000c140d8100c05802c0390702140d15111065107078110310803c000030b13403c41000101b55101d480d800101e40c041b544918000103500e440000101d00300c4580342540c0c0f0401200a4081c1020240908124039806c0c41005545d035000b504000245154002841c0c0786504503283c01c1045590780181d4502d0041c800f6110040f004080c0351022601901c0901005140110080900382414420410f0300c100c10040d1003250303001600ea4170032552a4200b4425510ba56003400032402c194800348403110300800010b0300400060342046001e5490203000e91840d4115907854000041c44808009103410000302c9407600c40103941011061400e040752600108295846441c5e07442481e120b0408555a4a41c24003080340e4984641c0c204502038030003014224110b00c40c20440c0014441c1300001400c0000414040720707a040c4c154 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187211609 1250 187210359 187210367
    0xc010210050403120c1701180c1805240732120a020a150b030d02060c0304080708041203080a0b12100908090603010f0906091103041103100c02010f050106 68
    0x1201c2c003e00290210039102c02c482a103400c9030510007442c1c02d0502a86134440b40440d00c4003000d901486124200400d05118028140300d9030603881501d1400e0517150700740d4030501070320440320301c10345004441ca03a402c8070201d45c0d2803d204140c0580c4004072035580040b400c14440070500b994506e1841c10101100483c1800c5090081c4e40c01c02ca850003034aa0300d401d0400c40000c6030084103840f402d500070560300c074000404100030030480e070004590020701d0380800020315141142154011041d503200750107108070784560034182c961103a030000c01c01c2e03a64982c1e458404034034042c81d4080c1c0c1142c00454010820503800283c5141300d50388071181046840a840c0c200440c20401d4807000b40700340c2103440310b44505450790704080303141030003541202d260210600100d81640d00c00da00c1f0205114440c0c0c424880a5918054000207280c40e1505010a00a844034200c880c40701800007002002104506041c545050104010170007440404000308103410101a01800c0c810b44480c0005107841d0000c1112401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187212859 1250 187211609 187211611
    0xa0b060c0d030506030102090a091a0105120a09061107052103060604030201031805060408040f0618050d021513140a080a0f030e0306040602180a0b0d2c0c01021005 72
    0x5000014010540a074009500500c0050034031901950200001d030801e80724104804018200d111001402007120040003070101d207681e40e034504110042214192900e806612140c00000b207803030000d26030101d80ba04500910f1510140031103803d0104481040c00004261401c400580201c2d07801c00d03002d0101d15075600c0c8000c0b0354203544290107002c14005548680d0041030000901501c401508419840e4645801d07421142290301d03620020b000c1c01000101d6440100804250070315524464045c0e64007002113602c0e02070503000e50b514110351815540c440c2c03081602641271280e459034441c00010301c2c400750481401103411008510151004030304080a44201312003008001e4800e0f5000380ea11040880c04080c0107a08000740c1c1003480e103103a903081c08080d000e180b02e10401a580d094007078408104c003001201c41403244031802c0080000c202034004881200c4c07684000000c010f0151802c0c0604403070040e891a040107102582028001800a0300501041c0300340c0884504100d403240d07240940e60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187214109 1250 187212859 187212877
    0x111070305012c0c060414010c0203030f1e0405010804110d060f0204060e0a0302132c0303041a0f07050c070803130f0e1014040906020a03090308070e0306010e0c09180a0b06 76
    0x1410801002440700510340c41003607c0051402500030407c507000a07142d2f0700040900b00c10640d0000d521440b007441030040d10480640c86001e942000e151000107004814018009050f00c074a1940c002c2d1103a490b09041780c02c03154007030020458002901c4861000390401e028080c0450120340c54a656450074218a1045030740c001d2045290781c0d40350f440700d800b03440c044084420003541c1520850442141076170301410843c54100560302c030728003820484842d5030048803070743c003d07683e07801484070a00207001010307448859424030039540e6042290b5545403000b142e00c1400e51b0301001c43c1003001c054146801c4000c8440c0700388441c1e4025168442c002c05800f099600ca070900c95100e030100000c4160011080c10310740001d0002600300303000d4a903c0300313981c0110301040c00660707220441d030301300360300175459a4000400d45010018204a000801e07664903040c041c5103582c10215001070fa88202c040112511464040d040c03082400da81c0b002c1c0c0120500a6412040c01b50074840c04e181d19003084810303a02c84207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187215359 1250 187214109 187214119
    0x2070b1305011805030904060504050115030b03070906080c15040f030314040302040903231608030604090c0605190e0a06030b0f0405190b040207020901050111070305012c0c 76
    0x5214048140002004900101c485540301e4000704122a04031070311001043c082c10281d83e44071058410042100c4023078002074811440c1c040140102c0d1030b103191011308143c06041c0000d50200110002e40f0309081540050b00e1039042040c08280d462010494916404040c6c4602e40200c0e0341c00340e060714078092405103074001d00b41c1c40300800101e8414005031a0b098a440912450213440c0e40100c1d050b500400300c15408510007000d0040d6419410000c44c100c0000702000d242018444070b14154209081e02d409400c18402201081860f941c071381c0694202c6610920340e0b5166692100d0180180c4c0000401400b030508450011001c94001ea43c02140707010001c018901c51401c042c0150000c0c0341c402c030203c2e0082c1e10458807202c030342c23128418140524540303140100c00c6100c64000900740c61900f00b02d9802140107000100040e01d07881d03203040c1582e0090905500f07081d0309841562030301c4030766032000d0450341c00d00007640c8480088008000c1102c03881100d20803181702090441c0c1d91183c1a078822034000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187216609 1250 187215359 187215361
    0xd021512250f0c17030415060b090112060504050109140a0b0315040501020922060801090c05090403021507080f060108040c030809040b153028050403031e02070b 71
    0x3041c401c0403002004400c1e070400903043c210b40d03110048925400100d00341c0c141800828441408030b101d401017401c900c031010134400c8034100100c02c0750a00854404506105203241e4410031804242c0113071002d800060400c11256030b544803031001801946034814405018000418580d003401d02039203000b018054010140c10707104446080d00c1e107000030420340f280c0d50b00f4041403165503100309030415010b5280600c880e415619842d0380084030765035403008400341e260500c1100003540321440301c1c0880350200c0d20101c0d650307101d0805905081c24607544001c19201c010800040e01c0d004510940a0103203035510400e2079540500664201c442900c0103080810390b07580420000d1039150040c01000e0024102080d072441080102d0304208000c44a0241040e0220b514003880040c08070342e080d020086049119044128a410401c45030080e240302d250603254548014482c40310001c040c80200c8900081040c1d1500d81001401460004a1704452402d6001c0f1503000501c40c0c02034500c11504401243c2d1a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187217859 1250 187216609 187216681
    0x9390501080601051207090509090c010206180c03060f1e07020a02040f0b130e010c0e010f03051005060c03090108010806190b030a0503040e01060e0301060e0a0b0d021512 75
    0x85041c0080100341007100401c1341c07211100d2248141c0e401401d00761101740e511703810007040000b003440040c030f20704c510307481010030f012160380c000703013454006440d03a10945400b00402d40702030800907038031807043c0c043c4100002d0145d4103082c140e015200c0c030711700a000c6e0702012024040e2611514140c480c000140e20410b050320142c5800c0c1c0c00900310911115000419040d40710100b000c03d10070111007130b400d590340d0044828403002805002c0300c1700864030700703c00c2588442002038180a04183c210040694850001c0c4a0020200c4075002902c00200715503115801c1e5600305549601c111a1640001c40c42000044d00380000110385004101003030a1a40c10207029481400902c2c10a1a00b985846421404800325000b4030090010302440c2e60050344640c101b0002410415903c0841802685007010400c8007000c0b4100c00b42c0c010701013400c00325000c003000340012411115002d019601c001541d40741044a1400c40c0240107000403c40044011380d51303030b00200318110708100100c455040c0303403c003055 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187219109 1250 187217859 187217867
    0x112030503090c130b01020f070f0e0405070b16030e010c21090315061a030f07050306240408010b0604050f060313050d0825020c10020c0409390501 65
    0x20b84070000700102c5001d018040c0000711414544003550080320758a900454207960f042c800310b04003820f50310040501c42c1c42d11100c58a5450140f20701c0040903100390214080000604c0200001c1456090b940d8403901500c0e00d10301c0d5036065400440110b10301c401204840d50203400059401c40d080391842940200380500c08103001807946071a0300f040300c10309020000a04010f90215120401301001440c0c0c0d003444001305612858500c5112500c4003072003040f4441c60698510f5521051a281a50703e035210440862a0901d600d80700451204101d110414001c54042c06082110002c00090104400c24001d1040a01c02d038003c4d030360030502c14541684070382442002180c00048414031401014861b4a0b107034100200080d00c1c0001516000c00d001c400d8540c84081c01e01035500d01c42200742e0600c2c4080c042c0d074031243c1051140c007940400740d402d100b8600134008071030b84400140c0107101140d0b1900d0310192060000ca2000134440194405841d4207800107800c85000c0901030000304141e0600c40155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187220359 1250 187219109 187219111
    0x60702060615250b06030a0503070609020409021807120b0303070b1b0f09130b0306040f03020c1306050a090905061915090504020306090115030803091006180e060112030503 76
    0x245080400418600c42d16816a801c44140380c803c0f00742d0030604901d82940f43c443c000d00310900c01d0b88800b05c0032003c00ca01200721580a94010000103031913280d84041005071440c000080e50021050114108400ba0300030310a03c6135501ea51034a500180030300c42c41040310001c0f80001d401d507005210b00130024000c140204d030041403008881d2012042012030309041d5000b03868020300843d01095040150070990b641d030f44020380d0700c4010f001c107517045800f00c0d6032050020030180c0302c0b24240043d0001c0c14028030070a0700e04140900041d081003600c144900141040b84161405003120748400030b00010144110008240d0260141c001d50b01c0b04c0400a040744111910b019a20b69503951802c84445000c031104010204808045014a0a80100b500f4400010300b03d54032641800081005046813a021400f580c0d0700042d0703103449072140000e843c549140e81400d010324038580b410110740140c1d010a00071038446510418070030f189400606a0f00e4440030b200b11504c0d0745004400c0c1e40003a0240c0091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187221609 1250 187220359 187220389
    0x509211201301403030103150b040504110d0201120c090501110610030318090c0c1a0411061c020408060105120a0b060108180706181208030703020a050705121b0607020606 75
    0x51103030030b5407101030f40381980c0c02a03004a801188420724500f1800c0c0c64087c000030103104480c100201e2801d42c030b07000c0c0450130f00b1107058803d6023441c14a9003113a00851140e6409488400700300080040c0c4d50300900501240d02580d400328515984c5004044400110f06201e0100d141000c0682465641c041c0d50285d075103000d600c001140900c01082ca4000c5216030344c1003c0d0790341c3c1c5401081d4003905021848111001082d11000100410840811809504030b0400c031340c00e0700d5003941c8282c0308490820b0402c0008400e1001030000030001085200011510305942d42110b80303456402a802c446950b0301c00c5001e00505c90b141110000d401741d0302070720f0000c0e403000c5400700344502002e00381c210505116480c0c01010100c0c46505000504444222920010b419540b0030018160143c2c0c5070502c89010060100d000c041e000982e8040c0c082c410800d8880c5540c3c00700890b41c09010701c2c01c007040b86400061200c0804110b042c0044484440001c44e9030003103565802800e4a80c8800e001e00010045036045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187222859 1250 187221609 187221623
    0x31b03060102070e040507030b06010503060f01080a091502030703270b061c030305070206010b07030210020304020a0305060408042c060f0619020f070f031203050921120130 76
    0x20004e0703407260303251100c0d1140e4442d0300a40308050841c90140300e80000549410304210741403082100ea07441e00300a0040c958424202030100b65240031000014001740840100030842c0303507000e00103941e02900a1030081d81191000c0c01a02003540b02e050128840c1280e52000c405100095000f2a001e24901074104501904c810840744440380b034084a03408420046000a40c0c0700c04010340c982c0d05203d850b001d4895603d03030a117050706a8030000d55032407109024009095000001c0b50031555072039029402160b10005681103450103051540c02c0303422504c5000107100c17407201840b140e02c1c0b502890303424485080c4022751250321181c00340030400410410705900100100903110001c8045500c030440340903c0c0e0700400010024510050402010303a200640020030b140c402e20005120300c0c000348070440c0500c0c00095941e11030b00d4507440c04018440b18440ea02102d00b0301075020200c0401480b4202c00c0f10200b4003180d03038034000340c00414844540b028400701c401841d254010030120f440307030802e030041c14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187224109 1250 187222859 187222873
    0x10201020d050405060406050708060604030303150512100b010c120c2d1e05030a230708040311090f070e06090306090616030b0d061e050a05011703031b03060102 71
    0x2110402c60340c0690302542c035544035800304410002d5501030075600055900d0240010f04085000c28680c3c051400010140b627198181c000101c402d40c8112402000000c00c9025004125144561920101641507440d141455280c240c65406020781d04200e9500201540240d0301c103610840e040c0c031141c08102d800031041350340c4080c1d000700068001c81210303811030484102c00e15841d154042c044540b00e09012036403202e203004045403001c07081c2e03000d080f003078141107c130340d808080c12030381d1500c4400f4007994211002c0f40590074005044090010307240326900d0183d44020080800c44d0b0b182085450f00d1900ca03582000895403032092007900050b48000e00341d2030528070544c0000c1c1c2405411547c9903481d6001c441000182005551513078011542400c04000f031100b1800401d600502903070b030240191f03442c2d94070b0003031880108444000703280d101e001c100042c0c101401d0410283c8030a10031284010559418000a04000b0044a00030503071901c038024040703003d1304030310303219080100800c2c15405910 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187225359 1250 187224109 187224127
    0xc0702221409070f06020c0f040504030c0b090c0a090b031b011106090f0d090602070b09010c0b0a05060a0506040b03130c0f0e09150c16052107050c030c06120601020102 74
    0x1081d81c020250075000e0410542800c100100c8514554440380c219400018090344a8a070392034004117004095502148651304c0f803e0607200b1494502c0300801100d048810040340b000e002c24803a03000507044601c00300080d60f4001810584844901150341a000040340308842c2c101c1c0780801b03c4041701810500c06013009400c106040080440d079590300c43d000310100743e21400b0107008075044650f442c141074052505048000795121094000d01110101c006443d245d145c0c01843d108416940c0800381e40c03601c2c600240e5400190109488082c0a01c00c00d10004c40c0300e02d048402c2c2d80507565200340e11350440e55824005440b10b02c8000c0141d5004d0b22008001c650b15481c003810300060300611048000600300410402d00d04080390000c4150400c0303420601c580d84940000300c81100c10f0119072048400810704042d41891860b404880f40c0741e06008800000000100180c54800d0050f010b8072010765000c01031544690003a013400364811003c1124660034401000b0b550b800c0310040c0300050614080d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187226609 1250 187225359 187225391
    0x4031706280312090f06030506011e020c15031909080c0d050304110303031003080d0f150602150106020601030206130503010c0306080f0706050a110c060307170c070222 74
    0x2800c010403002844a020b106024040c0504a0028418070308004480d107400e8540304291614005c034801c043d07ca00c04107845030710480c40c0000f030f4000546c001d0045540c5000107035441e5803246542d8050804c200306081e0951180007901d1041ea03612803504005240e01e021240100400101181c2054040c49100700500003002804405034154481c1d642d0fa04013400e10248411038950a680300340c1c4104100281d083d04502c2d20346c11240e01c0180152a080750790100405401001f40342402540380443d12200f00c184860348804507101602514150070b00f003492075003581d00900074070015074821001000181425802030004030082c110340d80c5042c0d00c0d00002425a01050320200010781c41e03003400e0100300e90a101d10f040158881004222103481c00c40041e04600800f030080092240c0100070a503000c80601c104499a0402842c1071b640e8a4210f80c0584505003500310480c4156612001507071141c889401c94154903002000300240c401c801050280401002c558440c8541e1a82c141500c18098 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187227859 1250 187226609 187226659
    0x70803010314060a0911040504080c010e0d030c020616050f040b041e170c130f09060e0114040503070209100801020a090504050705040609090f06050303030a060303090b0304031706 79
    0x31604090544200d0741d2442c40c90420041c040710101c2d442c100c0f40c8000036040f208000c0000c5030503500841d45555608098406020b4018040265424803844040c2484041594514542d4a0302e0421501c400c204003260368040c2141d003018003402c1d401d203078041240520042c0c248000d0200d03841b407815031a035000c0340058000b5400130845400030f82201024010303180300704d0302030040c0d03280003d072040040001c60703510340003041258041c1015000f1125480000d400c4618001e010078010300070307042d031882c0c44030080114040807400342d440c283c5207110f40c0c0244139646006580007c021404c01c040d0b41c00700030f07051074042c19007000c6021521001600100038005040c045007292075880358245000144000d54600802840c20450100018007009802841d080700384e400260700014408000103c08000700826001a40d1601c03010040010b2a031507074002d641903903c01d5540800160f42d59400e030900380425a4000d000c00c290328184240300051504a551000b8003d10102c03a850700720490b1400104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187229109 1250 187227859 187227863
    0x4051311040602210a020616020106090e03030402130902011e0c0c06020f060a021606020d0b0402030f09070f0b03130611030108030c011401060e22050c0315010c0b18030708030103 79
    0xc034614046404803200900c42c404d01804141d1505412441c000c1d100d00c80240700100b03090030910140311852007544544c01a00c84200c082002d1006625165901c0d00202d07400c03442501031294008500310580550550107506031180102103014040701070304c1c64000700342d00042014681c0c0550218a002d000d00c0b00508090f0043c00c0320000102a240c1007090003002a22920b0040125600380707010800c203240c1c0c540d001200140c03a440c40694a00c041d00f043c2d08031a502a00200a2080045410004030302441407241107518160b84c502d109680c078285440781c03980c0940c041c00051100b181403c505507a003407258100040d168103072041401182c00030f03000441254004180790780400e01c24803c1c42c180341c0e00740003030710807943c580040142103102c0c41c0c603582c0c00f521160241d0181000d14425401030000c15050600152606c04e514180b99001220f80d100d5140c88005070907403a50042140701c12054001214541c25030754115502e100c1c0e06141c141c003003284410007030391000c1020000514081c40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187230215 1106 187229109 187229113
    0x3010f05090c0f0409170325021f0e01060b310306110c0703060207060f05040b010b13090e0102070c0f0e160e0d06060e0c0c0304051311040602 63
    0x200d500c07100106005403060551007581e616901440c80348100c100250758230003500c06540d030001e18a02e09800560400c84405407040c2d031a02181d072003150240380110790504400111400c5954030350000e000301c48003060010702008038640700c040304609142c241c02c01c040a0000141040c00505c0010003041e41c4402200401c0034a109446120050381c0c02d40343e9040d500e0504102946c454102190300e2450202405030b1550184030380c0d80101c4d0071403980442a0b003401120039030759221006200b0b070074605040c0010307400e101d4000e5500d0300d00c50300000340c2ca8102c00c0c5440c21010015400c0015201122041403080c407600c4001c16038800e4441403480a100b038021025205250340000f51a000f03011305540005004164110800b114103c0c8000c000c030703a652070211261030160010441440d001040f0802072407404040e100d40030409141c001030595203080d1a1482548071ba840b92000d030f = true := by decide +kernel

theorem cover : BRFrame.Cov 187050359 187230215 := by
  have h0 := BRFrame.cov_init 187050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187050359 ≤ n) (h2 : n < 187230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
