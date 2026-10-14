-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1898
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:04:50.412194+00:00
-- url     : https://prove2.me/submissions/353159d0-66bf-478d-b4bf-6675a1919bbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341187050 ≤ n < 341366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341188300 1250 341187050 341187071
    0xf02070c030503120a05070507150b0406080c0f090402011713080706020703090e1009180f080307090b0423040e071203090510140a050408030a050406110c0604091509 73
    0x50f40e522254500b402e00c2000e801140300500540603190242c025642c916040c202141c13030b4074040d20505040d6060f02c2e643c5420441c119100d41c01b0f402c1c0103045050180c101001c00c0402d03c441065240c1e04103100350103d07410880140c0c0c014960001102e00f84001c071402c3e80c2c40c40500084902043d801420741c03800841c0c0c11080107055001130407814403a90303036074410b50341c1c03541c0e0925084801e076084d00040741008020b20442c1055400f4103048002480429000e00107522408003030002000c05a03030388180001001005a0400a0b00d801026903030320485ca000c1c50184070400da003140d0b440400d204116414010074540c0c8541119120300b954400795009282d42e03011080041c1d001d40811408248000300019031440c0c0b0603e02400401d19480d19078200c00e00014506550344261020000d11009020100c1d991100300050310182e600e94450b04ea0350b0341000c101414030070400521110700d030720000c640c0007517844200940781100ca00000c04120844041c00034031940004d07401040c050380c60680081c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341189550 1250 341188300 341188303
    0xc05150a050118050c18150d06030b1006120b01050d15051002030c0a020906190303050a0813050a0201030f090503120610180618080d080402031e07090f02070c0305 72
    0x6048405581243d001641142c80032400c0e0788085485602100d0244101c48445940c14020084c040b0010007003404000c42561001641c1c000c1a981c0c8001c076520642030041003100c0014903001449920304098092130018002c0c0100409079401180301e80700ca0004800b0790052007a82c45030181808248040340003d00111406540340c0b003114880c400440703546144900200494003013800308c0003d84880c001c15020b00c00c14000262060790011030031810b14102c001404100c030003561281d560700e540c801e180200105440006841c07810510a03540e04840081c10004800b8100b50342030802180306c500482c02e500c0281200c8802802a000004400c4a0101a950817520404044070040c0d02200300c100b040320345a60381668000c815500100c24003486e4000c00c482d00c80b0b044516080715109440d5541a0309040c00c1d4100140400c24800074001181b9081c000c488a8400d40c258080300500ca50b51340c0c9a903180c0c50f21605000c00d0365100300784048046901242c448036049210b00e0256507680c50b016 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341190800 1250 341189550 341189561
    0xa14040f02252f100e06031311060c030d0e030912010b100e030a140c06120402010e0402130902130b0f04030303060b0316050d0e06090706110f06070c05150a 69
    0x80301ca55100803c00040c400401c0b24400e200c011548002160421a07400c1c0512042800030507828003460100340d0b0302642c1c0b100c005502c1415070107407410f41034503a8545101c0d402d040220b1203200b89018003060180b80000420390310851044e040103c1c1e101100f034003607070542c4590300205811000918050304060030542150b22801c505441007000255118400c90f00082492211941078000000d04000710741c00345c40350a0340355180002e942a604001001560760781c03041100396009004c0380100000c0d50380000c40a00b4420003a9000c1d4a40200c4981d10520a8904c0c002d0010007a07012440214507000181104041c0c02585c0e070056507501181900d0221340c01610048002a00701900880c0b0b855200f01071341d018203c1c1c11424001c42200c8401a03507a6000252141c01d020f41d28540f00001180400c40d460242c80450060100e41d401d200c801881d941056080c860b803940201c0c043c240c4030342c000034480d601000c81d1034522001c895524015003002c12a020f400c0311090300d0380a2007a1003d156111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341192050 1250 341190800 341190803
    0x1030e2a0a030302070509071701090f0507080906340206060901080d0207030f02061e1905071e0c0b0406020705040f1406040b030a080408030304110a14040f0225 71
    0x850010484141000041e080078080100160002d41c010402800d0001c0003d03000702c0241401e4142c003402c1c2d1000700c1046400d07401039460949507000022301c0d002074032465070010124170700900c8901c1c001580c82d40d00d60300030345541c8451803040400842da60403102c48a80c082d03281e0b20108400e0420030b00080d981e21081e030b040c0348992034010001075062400100e911240d00d10313030003404805d8038644580044444888050340c002104000351280c0b29031141c2654050622000d80075258000495038840014140c0c9089041c00010031400e0b010981400208a031071046081ea00c0c6d0600391071030100d00440041d44240c08a44000c100071500680126020080e204142c40401501d0b020210007001c2d03e8803510350a082c1c00700c40d00820401e080c940c0045880c030001400300c0313080c0c954640d0b807040603601681c44040c3c01c0d0070100c20301080000e0031740f817018103040440c6d00303000c464104001c0c020940d001d00c6040384036690f2750070346201c00c1c1c082d038050303550342242301e090904011f46001c11000141c0d407140e0b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341193300 1250 341192050 341192113
    0x140a050f0c060f0708040f060b061b0109060b0406030c050f030a050f0604030f1403070809031603050405040e03040503100213091409061b070311010f050403110c01020703020d06050601030e 83
    0x10102d40c072030309500317106c0ea400c01040e4140b05041e48502008101c20300f065500520100040011b11001d144403001d000c203c5400000d003104641425400c031394040c1d070f00c0c5104504029042003c5980e0030800820f40b181152a1030101e410040040d1809000d0741008201f405440c204000c44280819034501c0b40b406511003100e410480b00d41181c2da02c4054801c0c103c0c1180610100704168824502207a02c004004101e13031501c420b6860a494900c1c258100300e0001c3c10002d42400306081c40d014080c2030840c44401075040605040c000303034561945990f13040d0030b40d5011400c642e00c510200101c030002c006645080160000e113400303100ca6032404544030b610358818000811407048150791501001d408084000b42044110f075011200700c0d07002800f04446d50740714a840540c4020b07907c2801d00451181c6c564510000395620b41c0c0f0b05103105041002d041d9004441d0400160300c0726a0242c800e036611100028440d60b42e030005800400903060340750f29500c25040046c43e106201025010340465015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341194550 1250 341193300 341193331
    0x6090b0306060417070f0b0d0609090503190c0b0a0507030509060f0105150f0c0d02070b03010b16020d05071401021e030a030903090e0a0c030e060403140a050f0c06 72
    0x100802090320007568465000542000100700c0c00320021401c4c16028440c105949a903550fa41000030305808541025000d83c04c001486a00c3c0559031003600010001c80e0350910818900c1e0700d405440b80255142d114402d40d1104820341000c0c41040c4501a031351b07014030046500e0130840c03403c0c1c00070300017215120080791405e004035114020008540384a00f031404000321a80e8207000c2400381f2510440041080d2100a22045403010021000b42c02c102d58940e00030007a150200d44000e103040c2c00c90780041c01d0b0100401c010f1140e4500d49007200c5034900c1c45030180340910294408600c010205600107000c50050000100c1c9401071102e0300c903041d510907803c880c201781d070750b00228480d58107552604400c2d500c2045403503903490081c0c1040350038034020b041c10745000790b0b1201c2100fa410b90845511020664509800003140d0b014424801240500c500505c001d04c0c1960300500020b000407a04903000102140714001503101c0c4040764607441c00559081c0d1260540b014403a0b598000340c0c5c03518115516003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341195800 1250 341194550 341194559
    0x405100309120509010210021611060a080a0c090e090d120b090f062b02030105010e01050f0f04020f070803011410020613030e1c0302010c05090d0b06130e070609 71
    0xd0180c21030707894000324031044410080314156041d901000085056000703000c0d810048403954030250811003100380341c0c2c0c00140010301e1b20041e00b26070034031004d10500702030254542c0203a00c00c41595111800f9070001414030340101d003e481c900702c02e0b802441c2c09000c080400c07aa440000ca004c8080d40d800b034075000295a561340b84e840c00e03280c0c40c3c800700e90070100000003d48007280706816070341c0102c0d01815004050003501d01c80564520035180100d012480d01544000b1400c00340f140e40d0040c148a0b115002c40d5042400003218800c06000b11131048600c00700d040210b5480e0b50446034402951000300d03588410502d040340c5141c109100c0c0541d080c4081d4400c209900b00484000e205c0503242c0d010b0622039440750041d807404e21522806404010307508110b84a142c80320781d8a03013089910306800c140744119510b4000d0954405021000c1082001d010b070030702c141c4800020600d0303298840342e40380c41c135600c0801040c296581c1c02080c0043d40e080c0002e00c070140c0300101c1e4102c242ca00a5440000441c0c54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341197050 1250 341195800 341195807
    0x8060301060b0901050304110a0b0403050d090e0609040204111803070803031302060d09051e0607030c120903021006060e03101109060c190605010807050a0e010b0f04080a0602040510 80
    0x1c41c810824002420407044110750721600c011544944941c42e00c4507e100d0000100340c1101c200c0e045807826820025045c010700c0070800801d807065003a0b1510640c1f072403c0940d4410303540d030301501160098401d40d000c50119911900145030880b03a0748842034642102e50000740444d4440040c3e140079006080340400d100b00044220381c802c03a41440c580095540590074018aa400f80340c1e019044c0b690b40902c0c400080060151900d10183c00c1c400011500100c04040d08000000e40322205051405a00c130b140103400407141d840344a00902c000451203210f00b400e9040040b8040d528461501e00140844c03807a80040d501044c030b80e0306408481708400b021100c01c04440701951b400414420900c0000010302d018001030a0805540040e105159440502c1b48518000510211002901c030320041c04a0481004590028813044541d0340c615454040d0505e16103a06008106d8003600001c0d8202e101c040c05021907005205540844001d11207034200480290400e01405c2e120b2501e00e011201c03140d20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341198300 1250 341197050 341197061
    0xb0315030d0e0f121e030c03030901020406030e3c15070f08010e04020d030c060f060806150607200d050a0510020406051914040f0906050306190c181508060301 70
    0x72104000d04000b85101c881441c12000700c4604005d43c4010030050300e000070b0901c0a1750003281041c00240e140c9042c04c02c003805441911405000903403062800201d8000e1180c04441d034050f44040c8411941552882d10603002c0d440c92410300390340300c1c41e500616004070b00503409200f2b43c001e0390340d18204190b000e030481d5000001c0c400c105982da0240045800340c42c1001000100320301c02d00300071808a031599904e20686103400403001c48195600c9041110f4402440b1459100c41241c1a07503020440700d1000514a00030f5401c05851800690610b17020303801e8a1183c0822104000c042da52900d81074036103503544200b6003030308807828024891074240200c03541c029502560540d403181814080032002c0c90344c41182442450f020040f07041d024590350352341d00c002800508913407404a803601d800c102c00e04094552640c0094082d0303000c0f0f001c20010074101c0b01440f240010b02c940200780345449044c200c540100444092415100303071800010f111540700d185105402181d180c10150359958000c2600b00c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341199550 1250 341198300 341198329
    0xc0b090d020619060e0702010b010f030b010903030516020402030c0d0f0c120207060605090907080106080c150705070e161b0b01150309050a080c070f050a0b0315030d0e0f 75
    0x380402d0201d205002d4002111003840c4850b080054072994030038400b10303885030580c1c000780940d541e561454100e5a000580c400880304908040c085440000002400c111041c44041d0030010089045186815411241303203204e40c0040042d901e900b0064101c1c0d54a40c09020641c03078a52411010050400343da014107403020005464843d1050105141d0502951041c80d040311220b5617024046815130710100c8981c001e0103082c00030312039182858410707800c403103860b000700c0b400340d000202401c3c0075610042060801c2002c0802640c48a20b10b113486071600d0459000074000e4183c1c0400c0000c01002c04e051a2101200f07544c0b0a140b4160251880c2e02e0551410006484407490038014001c400103081c07003039030100d0f003880c002a40c01d495403100350078001200c1003145c081c0d0001481d500071003004c20501d00500100150100305a00d00800120710180a110741a00b9400200004000e500d0030f00860320060b40c0541511107040110000410800440000c5441410940c04056160400c110002e40e0b2a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341200800 1250 341199550 341199553
    0x1b0e1501170702010905070308041d160f020f24010b0703020d360801051605090d1119061101090b0109151e0801050c2d090d030c0b090d02 61
    0x804001c000180041c001091001559210303c83c1d18001030080085c000154012104c2a49030b5050001c0350030804411551600303009510414499102c1d03d0448100460031241040100c41850007400d81c18800201346040d401d000300c10000c1500000d0040b000c03001d003a81c4054004c03680e04c40305100f400e4000c501c4040e0060f0700c80c004584038180202d007218070201c0214200d540c42c00d060010b00e55546450070031012600300000041242da4003d00541c0d410289518071030f112424184400ac4c05030294000c598070500e04408104140002c01714456a0340401400c20360700c0c40382d40102040c415085101c0d04000441d0b03064401d1a90f1818462011404e50080da14580c036403825148030003030f0000c600303042c0c1c940454840000d640000d114195030b01c1030003144c0a10b41e462401c010b0301c1c21214010481c10985034200111032070500816848000a070395011820740180300e080a00c00e890142480d002e8203c128500803c00741508401d08108a92050040c0405030780c480c81d02a0319401e07101d1594016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341202050 1250 341200800 341200817
    0x415030507051e0c0f0c030601080106031208040303020f03090124270b19030506100b07030815040f0b04150807030b0a0b0301090606031406010e01060f020106031b0e1501 75
    0x10140c1c0c1900c0b50461084200c0c43c10b0420507000d0000f4104003180070030b0055988204030a0707030070741020300c80140100300e040c00800420b0f1650b01e6111403240350140311710811424030002010107001ba4180d5000c0b0805680842d00d070715240c068603008001c01040f52013090804040407161041e164020b00c10340700101010051261004900b02d00507074450350003039160751900b10012640e110000d07104680e41102c0c0140350001d180d41000b0341001c80c06481621001c0035154140403401e01e8500315651241c1c18a005444d650310030885c45542001c2c4a042e0340d100d42081981140703496240c20810040c0d030115030401011120856800c06c03142d17603101c1c5800a4102c09410008102d400020303a80c80b0004071000700d074884200f8000b03821240a0201140c042d59960811301c00d012150301d00040050b04000240358a5040c500301850074001441118200700382441d0041c40342d4801c0d00410000c6500516101c500070800144c0410581c0e240144d1481c081076600240714603112002110000d0810b03140d0590 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341203300 1250 341202050 341202067
    0x4020102100e070506070218070c2009061c150c120614040506180f0a180b0411030c040204080715050a080c180d0f0b06042318070b041503050705 64
    0x70b03039411017001a64010f000c2c02300700d0b5040407038041c414824980c0d9503a58544104610304000d610321421042050100c0121013661140c6030900d000d500302d0700c11200c00c1c50542c243d8290390090b86025200610404900d240f03010414007642285049408035181c6140381c24902c0d58000c2103c009105107454642241e507000c049040c51b0b400140c00480c051700c074140c0c0c54000d419040091900b52106419151340b10304004800450744034500c0d0003c900b000140c000b05143d160701c0c0d010320024001900c00b40c100744080c0801d550801600c0c1031180044c00564841343e036604501d0301c4507018464071000040001d50ba44516200300203c5030001220340f03441c511926407902559194000b1070019020005006009445555a806249005115501007026206986801072404001800c141d0056041c403c4291020803c0500798182ca030a41403859a155030b2035048035496000124800c030030380140313000815601454001402900c5000030940d50f00c0304919421021580d0480c0d0308000200140721004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341204550 1250 341203300 341203309
    0xc090b07050c03030c1f0b060706050c042706050f0d08030c040f090c1403090a02040b0607060204030f050c031507030b010c0503042304110f0f04090504030804020102100e0705 77
    0x401603020300c040b5400318080da004645580c0c4298912503e550011801c9035104103012000000d4214001c0148101d2000c0c0300031034000e01810000a140940301c40002d45a0726680e13096800a2440a2025400409131040180020000f0b1800344055007000400325141c20480303100c440440c40a0704d05078034484030382c4820005070070291118000785010400052000d030300c4040c0502811003074800058130341c00c14101038120401d903410360701e4a0105000308a45000003040c01181c440d0140c0300414850f08400000d2401c1c13007046401000c6600c04074010003480410656500c40e41e200e101110861703243e141c100b5580725a0000000c1c000d1504000080380e00b4440e40040800b40010704240d41072440c9642d645007940c0040e04400305004c110700b07802c20054604000d4040d81c04080d0b034104200001503120a6580c071403940c400c0d005010006000442110420403a0024020071b1000c1210742020b2a0082043c5019030f82030b8010b100e00c1c60f511002b001b2a00c60003284518a000034071840d80382c0024003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341205800 1250 341204550 341204557
    0x40902060334050406022b12060b1207020f0328020f0604060218011805100c0b01081b0603090d110325030f0c080301050105030a0b060a0f030c02010c090b 68
    0xd4031003900c0e0755040d50b240e14101220b00e00d081082c3d01d030b95445605000c0002e203000308080c1e45881055503040105410440c0031198109481c40d07103410398520744a000c180010f008182c0c01058121400111164159441d4041602650351642620615040840340640da40120b08200059031801203110840414070008140d808000d40103564000f0703141c407041c40c10b02c8003c9500b500c2039500010783d422840c0150058003003110090074499422300c62208000382903145401440c0c00b8024515036a030009010344004041c441c0d214800502c03541e1119003042e01c0d010b0b203242c1c1d10804403984081c14100d103485002da80c031807104140107000181042e28102c652072490104004980005c00020319115151807411020401020b160030050b01c05240052010719030304e02e4030302080a240c9034240003038008021a411101d003441c0a50b10798545810000043c81080342542d44071400054240c80a904543c46038401d8a50740c404001060305882d0031707400d981c3c014460070000388095606012000805029 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341207050 1250 341205800 341205841
    0xc0403031b020a0302130911060403030203040b0d06051003142203120e010617060601020604170310170114010e09070e1806010324020a0c030c03020c0306011706060409020603 77
    0x2102d80460b50703500451081d1041ca22481c1ca06c1c0d4507a20500c0074010072007000c4d0ba001c401a50070ba03191901c2c2d524025241d003e00d0140c3c1022840000d68071844040782e40040d0043c00c2c00030081e0b0040c50b2505c1010b0001d001c1851944010840384c03000607000e00c07409484503280900345403075007060192542c1c204c58071031105030f020b050386a40f122100d8000000b4071030007014024054291102d00e00e4500c03000d1074020b00415a504650042c4108000101c1d10792601ea1084001b00c8160303125100c61015070040040d540200440d2540d654218580ba20705402107100040d000010304180d0362202c40101003182c1c22540300085901c10b150820038900c1c0d60001541c4043c03142d0203076405041c1e00703080d1410400c0030ba1058400400d00030303401e01000b1541e16100d41585600384118a070150504c0b001d0940401140c0182c2800740042c501014140280054400030000900303032071705985c40303000d0224400314848460180d44104000604141461703c5070000154000b0310003402c0d591003a2550f100d00020481 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341208300 1250 341207050 341207059
    0xf010801182d0602220b0a0207032019060806030c0108060f040f090c05010215010f0e0711011b0e0306040f081c02160213090c1503110f0a080c0403031b02 68
    0x681c00204402d803002d402178544043c0e40d0200f10012504c2d203034568610780c10400f00142c1c10086050400c0d000510001102d03803080c2c0d584840203984240d0724600c1ea11020140d0801e005c00d0884607030034a50b0419030250303442c5c0e031200d4145446d80024143c1d6025490307101408280c25a0114a10346070140d410846001c1c0204003207801101c0011400a4a003980c1044503820509141408950303014004030202410b9512440203c0d8540351580700107521510400c130040c1c9280c03011642042c8140109202c0c00b0000380248140d00c86411780105500c407400700c0b840098070040418200349804601d03035001d00d400072030030301e0103218980310300c0c01c02d034024074003148901a4004103170440c0b0a2400542690b044441d02d81d22610081c1c0144810503560180b10612a0728000e00d21001401c4510342100380e41c0704500c1c0b900c1380b140e048800d500521032954411200b410214a00d060031070480e006004102c5039a64009550b1607116501d0854080c5020050108481005a4040080112543c2c100500041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341209550 1250 341208300 341208383
    0x1501021f0f0f0203090c190b0306040e160f150e13020c0703030e0f0d0203150402010509040e0601240801090b0a03080d020d0c02030c0c0d02040905060f01080118 71
    0x361050202c0e01903514842c811a0040b04000e031540c01444110f0901c1c0084e1103804090400e0200c05520032000d015445070b03024048041035403600d0350303486540203031041000c03179a055009a85441b4030f11424801e088402110642c00b2400003640c1c0300045000074140c0700e100d4035008000820040c200300503607030703d1480c2e401d216450401d0020050240114000d4880c100d00311200000e0103243c500d5900b61a01035036210aa0f00c2c0140c07000a506c45080c807003402c480c61561070700d02c0102c030240f291820140e806400e092000c03e290401140c610304803a4441024910301490301d0b07018407030205034407001c804901d004004128400b0746401c080b000c480002d102c8100360f80c599550081c250828488106510b501103100820b80e029445459060301d9140029418800c0042c0d003aa036400325242c00030301606070460010110344503600300c01080d950040640d28140351a00314007890590920a038426903003031014400c9508024003101c070308190003641e01c2c205803400e030b0b050400c041000315607001421100c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341210800 1250 341209550 341209571
    0x40603110705010903080906220209100509070f180302012025140f0f0f130507051201090b06071419050c030d1b1112030a0206010504051501021f 64
    0x4c1c8644441a803003a00e03a0348840c1081c1c10101d24001c03004200611440d40c45540040c2039409940f60400c0e0780c0d04450404069480780b0318101d43d0342c203d0384910f4021101c47c2c14040116040420b54410786980d40d501c184d0380445040d00c40c0380742410301c80680484e10b0701c0c9a05003a1600541c50140c0c40039000704941a2003044159489940c0b04000d15054200700d902c820f0140071510044031202010031a480d404110035800054006c0c81c040540310711510b43c0101c001900d44500c001c802c0180744080040040d4580500040c046138042200401030100081c00401c3c3d42d10301784618040041f000c0c000d00e08015580e81d0f0308850809000712444c1c24400c01d80701d40301034007804090001007031058020b491134000c0c0308107040c81c00b44410300080900140e5014420104c0c5410500384405401c0300400348159000004100603c80405240303c003400300041c6008000c1d00069124100d80f4255020040c0f40c1d01c07400c0c403040b1080540203150040c2c00269100f1400301558024aa60401442001441c0c0911 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341212050 1250 341210800 341210803
    0x90f040e1f050f0a1505060a0c020a030f030305090f07060f0507120908062a09010e090f040c060806010f0e0406260f031e0d020d02121008010b06040603110705 70
    0x40030103107544984400030042010b80000441d0b0b04074021300c0c0c040c007840503081d0001144683c0750144900468005ca560780c900c0e0300c04c500c4800341e56000b0b00300d198803035106d0406412b500e01c010360a8002c281880041240f20000050f0341c00d200c801c0320040c02c00319041000803580d6440000c190403c210040c4040800705600c0590300511400903143c0b45902c03460030b407406040140c020f002d00e94080390640c0b261703030b4002e504185400c101484480c441c0d8400081d40181c8001318180c459580007880a010030404081214050b8040d5003c4c525051905540f1102101e091038100d0300f9600043d0141030048540303002e40c90203150031800500100780551965820195410704000c1c9a0300030302d0043e40a0305914042c410381c0b0380700d030019010b10700d0541e0707000907031007030f40b010341c150300b80590002429000c0c00714150306032070a0681000c8203540c0d441d2a081034000c00d00d0240c9000c81e8101c140700340040d540505200d2080b04007400707071255007840e00e4260294018090060035141c194070400c02e21000410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341213300 1250 341212050 341212093
    0x50702150c1509060601020a080c42010b07080d0b042405091b030a0b0901060504050f03011a040f0f0e2d12091917010b06090f040e 58
    0x4050001c00c0041c402c4000318801d9070015024012640200c0300f404540d907404134110815940107054070b6900c0c10325500d01494101038106031123034015a0100613503a01d07074003d01c11001c58080b0b030000045290070302c00400901000c1c810482c850500700690700020303104402805001c000003000040300141c80000c1007e60700d00003003d82001c0012642007144100d4880c000c00a0401680c3d1000f05141c100b84010642c000f241d4481034007500840040e98444243d04007590325400600409400d507500c1c9805400d58000780240c5100c0d00344210520000d0a051250104800c5440f070300d080d00740c664200b800001c00600c400740584da52501c4601094403054001c0c0740c600110b060013840301695036000c14890340b404000c800385064484000288100300080c1c4603112103035102c1d2242e520039406001401c100d070f006281d101d512202100c0000c050007614000560182c2803402440320120401c1040442d00c40c42c56400d40c01003440000700001d05050348491400088003042711b2041c07850444c514030188 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341214550 1250 341213300 341213317
    0x216050d12090c05040902030316030c0606171c05070b0f06040c08090c0613170105040606060e0612070215090105060f01080403080a09050709020d15170303010605070215 75
    0x2441031460142859224140316403040c0c1d01001084032100e555104600c249441c41003034442c58840e5100006e56400340103c4007902e402c0005007901e212a45405010318480b00801d664152a100c0f0000d03800c0401d40c0301100786030f4540d0180198000710b080b100601c03007062540b03608202e824411500002c9804035000e01424018140b112917203824410001950301c01e20112082007c0d4500380482c690002502030000842203440d00d4a80c107410039000c1110302540d12440c3d00c050f031000031104900c4190700c4280514002c2d48140319003900c80038140c0b01e4001405010741c0007007080210320384500500f007610b900000c01e4819149145541040701048020540349001540d5680d0148a00740c0b41c90003030913446120a003401c00540c0b805480c09841414000d002c0040a521408100e08210052101c2c0d0701800c8001c1045498035081d2000034010b025444041005080c02030002c0340784080f282104030031102c00c000030340c6503030f0a00b00100e42e00d401c83e00d0201d070040f88501041c0780d0071020102030030091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341215800 1250 341214550 341214553
    0x40221030f0c010f0c0f0e03120703030c2a03120b030d05041503050609010e061f02010606110a0206250203120c0c040921050c07080f060f10050d0303021605 69
    0x352040ba90050031108400d80c0d82d50300c030740f4100d0400c0c80c3c0b94018034180040e40d418105603565042443c08603007008202c1c0030f085003000000035030310f0415070036500ca0148001180d03540d04001d008055001080700c072403810921841d51404c01d680000b441030202c80c1c122800b0081c04170390040c1840200340380ca000c0742c52030320100d600400d0900c44840c880c01400300c41441c1d890103202605000020507800c01d0180141003190800e04e001803030340d48030301c90000060800e814640c054440c00030002402451280030301e071b0011b4410203d04030044800900c0c9440785800a050398078010010b8a40c40b030b0440000c6071a04894421007075100580e5040c0030301c0800104190340d0341e54031a0b20800c0b9604103525a00014462854414507101091703c40d003203100640700e54418040c0ea42da17600c4c4180d400e4003035103403503068520851101285441c00424444c0400700007400b1a2201d44a14040180e115021034414140a40d9a4020401c5150007014448504d00908006141819002c240096074846200a4815 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341217050 1250 341215800 341215807
    0x6031716020a06021c0912150207021003020d1409030909090a080301090f0b041e05060406030f060c020705010c0317041406100f0902040302030a02131107050c010e010512040221030f 80
    0x2007822101c80c441c1c045c245860400c21450030806121107494992801070004120000e2900040031158110f401c4250020903242910420b020b000f00a98442e20107605841d09002405000c10000001c103801803203204007440c1028941c00a00c620442c00811500700c80c481e1030205404240030100444c040d18200501103901902c004000007690a243c1340e01d030040d0f240081491040300307409407528010042c100089120748565000401410098001a0101081036080c9081149076400401c84040c0fa03026200019541c0005441d01d24001070b020300807800e100c07017020b502c0078408080350340203228102d403203590003c02e1800c80c0303407131030843e204800341c00340c440f0501440740c0300d01c890341c000c000b203080a41c07400d07096a01094407440c801800030300500300317403000d5511b0000940145124945400905441e03070080e0818a50301e01c049002280403c0c0b0040b07040140d944500c3c01c0ba6403d0400d20449161610303a075080c000840c040c500380a0b8500c0030071200d9a02c11005100402020030084076a070f4a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341218300 1250 341217050 341217073
    0x901081005010e0409050c030d0306031505040b132d061104120b060a03020315010e1005060f03060f1908070801060608060909120d050f0a06031716020a0602 69
    0x900002a04400300680a26000c220a81c1d10001003108100300b620081001c00d6641781543c035209103c404690301d03008010340140f80d5503151b070080045902032074034040e803560042702c1c010491700c3c2a1005400306d070b55503000501c200c4203c82e4131004580704150015100d400000d40c148039000804104a0203880e204941c010701600b8050008682488210285010f190908503038200740e400c5402460064007100003400b680c0d482034010b00554015003503d0345161f2950004405490900440d8030403c504404218580c1d202c3c07100409540300600401c3c07078000c0b40c2c8003c04d8140c000501865110000c002505055241d04880c0d00c807240100c0c0141d0b150a04219003542420141c0c1c03c400d4150b0b00d01281000410340c0203183d01d81040041d00c20342003039241c0b181d0030b40c1810101c05000d24001c000144642922000e0741c030552045d07000302c440041a4442d0840d15050b9641d0344006003a01c0c07007440e11807111080706401461070f550719011300d488c50400d550100c1d0380c2e50b8150b8404801344c0c118851052 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341219550 1250 341218300 341218307
    0x403080304060519110a030f0b0909060106080108030a09050906041d0303060a090513030c050f0307080415210209061b1e0607170601050403151b090b09150f0403080901 74
    0x716180b409080170710605200400e001d140340212040c0d0300c01c042d03d99002c04201a80d961100310b4055019069940da89007202106545140070301c200c00c0000c000c6070000420007404800d036040f0802ea5603441105920700000c0103500c071009170071641d205940b003101100300359400d5540c001100b8084080c0d030b00d0b403915008200c05400203a02010616040400300850810744181c8460a594142080d07034043c440c81c2401d51501100b0780041d640da00c8009201002d10a000d00a80220ba62444400c01d0340521100200c44881c511802884204030304284500910010b801602210502401c46400c0599903540f901001b580e45841030441d800c0170310780f51120a40380156944907605003009040c1d50400740c000404901c8044d030400460400c030340c040b0310349a00c070b001102c0085421001d0070500c01030b00300400c802412882c150000390340581040300b141e0350141d00d001c0110b46031080e80c142003d800c441401003420680507880400750041004500451403000500042d500940615844216003000503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341220800 1250 341219550 341219581
    0x60e070c050d09060e090406140f01050a0b04150f0212070602040f0906031a061504080615040606020c0607060603020406060206100e01180905010609061215050105100f0504030803040605 82
    0x5404000040b80c040c820507400105c00c1410000c19594800c1c00d50f968148000100f000e040301c410000c0b008814032250002000398035061302e00455a195003642d86803080b556a100f248104d503002d0f0f40014400d02002e00035084940e0b40003060051381e0f4140f801500c0a8000d611003042121080c2e8045400d10052100306101f0700a80b80c0e86e60100090b03419512800140d103000350080c5400302190000900e15140c0d00201140c0d200d03a0f05030749071596150b0407d141c40700e4040f9480c03038600a840031005183d16103402502c0858440360040c0045615580900065900a41058070307040d48424000006840d00d1064500a00503980a081107003490b0158680040c030941c04000004c032070900500101c0800e0207503500c1082c01c00c200250350106481c1103405089580e000d004030900e04100042c801c2c20b0360003082ca01500c100507406055481500303c0d01119801e00603250000b0000480c981030b0350007410a0002540541051414180d03217a407003890546c0107c0f000c03106652106c1c24811242c6090921 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341222050 1250 341220800 341220823
    0x9050d2d050909090c090a050402040b09191a060a0f020601091b270801020d0e0109111504030605092109030d140405060403050a030206090d02060712060e070c05 71
    0x300035140c485004285005600c112845200032101041040340e040000d50840fa20250911486180c61013154004080485052340601d00b0051003801600d06420128401c2c402c0c140085202549001d50000070070490b40400390040700c2503207005190759000f024141c41c2500e80d952a8194128036002424100c0603800b01820b01c1c01c0100080380308051582201e40d010710751070300401400e9144084000741202c0702d0f80300300d0211001c9021030765000640040c0f00400404006001f40f903240c0c2c44041c01c0341c0c03031041c000e41500003c42c417200091500071001401e40d284841c416060039141c0d01ca40080b183c050322091040e601c44c51002070110402d401500b150b200b4000c05500302201e040c0849e86805100e4a800200803c0c0d501c1c402100740c07a0f800340d801800024014a4230380d07480385009a5030341540300d07059002d44500f000050411301d0002c2c8c0540400b480f40c2c09805c5949582009660740549842400300c40c6880300c001050301103900c0c403000d05c21200796a6910031200107003400c90801146000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341223300 1250 341222050 341222117
    0x15160201270314160b0420030303180c0a0e04030207090614090601030618090212031e0d0605040504032c1c0507080303101503022104020409050d 64
    0x8418451100100055150941400c50325a50603c5002c882c5214110f881c0c4454001281c15009202211070310a204d588110b19108000380c500d07921004015100030600c1c2c0c16481000010481c15a20101309a55011102155600840000020500700d6940c01c81a040e030089003c200034558108080c2c030040807417600400406042070680075044820964843c0540d01580c003103811759100e903200100502d44000d40c0000c2d042641826006009644006d030710441c04590311920044000c4102c0d617034402c00352444450046c44070070f403800c030303420600d2081c1120381d0729000098591214080d252081e84656240002040c0b0904188030b182d40c0c201c408100c2c0b0f00b52040f4251141c540c144991070381590040200318400c85864001e103000b49a03005490940000f00900c11030500207041d100543d01d10303045194a400e40200101d04034024112440c04041d0004100818a1074612100381c0190000d031011031500060703190107103800c46070070303004000411101d02c0504a80c41c0340c1184640c1c0076000d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341224550 1250 341223300 341223341
    0x60b0a09090b0904021210020d02090901140a121401050726060108010b090d05010606031d030a09120f050601031101031a0d0b070504080111180402090108160215160201 74
    0xc022410f0b0600042c0001e0007010f590a1044014a04100c80448042005015036070340c01800c15100294001c1d00354140560304420000c213506100c2490181c00c114080c2015001c60b04d0900310b40403048001c0000d03200c448040b4600030440ca030a0060521440c52910b80c0512129083c04c0742c645011000640b0043c9032241082c001c00f45e03800300c1581e0442c0c0200c92415142c204200006104d01c1c50014004c1844d03103444030008015405402480d18645210402c00000305050398550301c038441c003610340340003496190b4180190000303502070051980c00340c54a4040c922031569185e103481000c1c0c1055034170b042d030704100900c50740e07250007000140804041e035121481e2440010422004608070004c0100c42c2240005110912441c161402404450005c0c806180c1804a10046c1c0d0b2000409070440307962030030704039010300b000e0085522410043c6c0d52541d1a50f9088240c070003038003640000900310300420070704a460040c010422405511486072250b40d449512501900b10340038645101070300750740302 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341225800 1250 341224550 341224571
    0x3150207020a0603020a170f01030b0708160c03030b090403170105060a022a03070303050705120910110c130e1e030d240608090d050309100b0a0504060b0a0909 70
    0x310000c100c908070308000d0f8540703000030000c1d19424811f1384600040c400c0e5800700003040c1c4003808914100c0f8040d0217140941c0c0c0703a040d4115010501124401c0c15101d140c80e401892030f118521507203d40303000e440c000a00754041800074030325980c20755058000484002001300340803a2000300381d00525003100e100d4905440528040c0d19111100884c0d4078102d6201c0c0440d01280402c0c50100d22114010203440344240c03a440c01900c01d0f000f41c03c0c107840b9881a4614010308200c0720017101d40e503003002060612840981c1200f00c811281c50025102e01e030150034a020041e4590b801c911807c43c802c0e100c0841c80c950500078841c80d0078400714440c400c0300744021000f003d040001c01110244121030002054104031948001c3c0410300420310b02c0080c44910a000940c1944100914000c200302c04c00d0307881d0001d0142044440d404181e801c60381c5074000403280045100a5072001040001c06041c100b200c90340c1da000a4110b9546920041c1e484900103041c2c400036500c0303002540a0060300d0020042010700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341227050 1250 341225800 341225809
    0x70219030e130507140a0f2a05030406030e010c0e0d0201021005010b0a41040b030711101406011110021303030206130b04060b010c0203060c091e06030f0c0418060315020702 76
    0x70704805042c08412030018239048e010b200e820703132001782c0780d1a61414111a0b00d09070b03540382d2052040c000001d10b00103a4030000b1506008940300e03d2078a40d203200c06e00f81d40320100b0940249900d0100d065218582c40c042d9401a2401200e00804c003a191964503820304036000b400242402500b140350f42d070826401d18902d0690100031804505062940c0c0e5001c080399031100c03681c801d80c0c1000c881600f0100c20001c600f58814180085942c941050340d0342a003080d608203050740e410180303d80200c100b480024480d07510402071501030012280031655041d0781041e00c0400c990200504c40c40715008100140103050301000441c0d00044003807840d1701c00a195403038031000b220010308010100740e00c829110320141c2c0308004207008a90010140d5036281403004921046600c0034107890700945a4088e19200c0150750038802c0303040b42000e840f182c595980c04110802c034040040a85071031690500000c82e6420401c030070400001c00d00d1600141d240d045080000000e00d511440c0c2481d6401040404010307202c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341228300 1250 341227050 341227067
    0xc0303010b070219030f022106220f0803160f1407060603060c080f0a0903020a0b130c06080a060e01030f110f04091b0509070219030e130507140a 64
    0x7038255001e403a0021840003802c014107a940d0700355a00901000402408801c0c98921200c0307200300c4082d03600c2003012100d880614014080c043c815000500081c00200c101e502400e081090450a105d1417015503642c40e84d41868880b084c3ca030b40c800031040100f480000000c8002c40c01050900d2803010403084c000600e121007400c0200381582c4081202801c01c8907a4110f4806190320007818030651112640041c501501100c043c83c56000c0300d004101804090b10500b4810342c2c055001c1e00f658101078403101582e00d0040c004120884650144e00c02054407134007210050066562011814284824884107441c1d05411603081540140700410015180c003c5015000e580403c0003a80c0a00f0784000a03481d011480320160002d0504003041c04001003a00c1907c804100f4922003000152070f9420300800e214100c4105000d644050364141c4504c3c100021140d2951080c0740c100240c0051001082078690390703000c8071000079296010710500d56085414440395030b4420080c181031620705040144001c0303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341229550 1250 341228300 341228309
    0x1020d09060b09060319170c0a230304121b0e092b0f0e031009031d010c080d0e010908071e032309030703050303040215130b09010c0b07030516050c030301 68
    0x61b0162220100580c090120070006a107241c015210b6596188060b00c940540c0ca044403034080f1020300111440b00303204402c005507152030055080608108920300d46418540041d20404002d08096030114440c0d10580050100c91807026228108182ca41e483e05280b00c56220000d407883d9000b42050700e21040040402c0200e2038910b5180905001c151071403d908103100d900f5015854203c146c20140390008c003005071081e0388541030314181006038615000101d00d90f60004214251550100d50924041c100b00c4825500c0060b4000401d4841401c4803104841102e5a00c00414003c0901c222542c8403585c2c52101b00a001c004041560020202c0e14809158007030300794140101480c0c02808400d890807680050b00302c828464403800c01540c0c903041110b00702d10414100d40f036035840035024026101901074000031219140d062010018058000c0c81825041201d0013211b000030480b404041401050151000500b505104604028400003880b5100900c030301040450f80070702e00003080382c0c1140d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341230800 1250 341229550 341229583
    0xa05030610030e010606020c010210060510030e030d2405010507020127030506010305010204030b13080a0c0213051003140d23090607050f1e1005100801020d09060b090603 75
    0x1030301c5201907000300314102491007a03610b06140811601e400048520031130b2400d80032901e183c200340d03104d801a55124002c2d95042031003541c1103520136020f5003022004040035402e880c102010f00c242c203412030308400c2070941c012a071103045848448403030040b01c01501080c64818a050032680010b030400c4102c4c40c02040b21b003001c07501c00b840d1042807003541c4051507001007035070210350790307410014080e4019000a403845000a00400c4284818188481002e644080300c00d040404d03918050b42c14240f00c40c402d17a0081130044003003003107140c14850a44190150b116001c1000c2c01c42c1420340c2d400c9694241c001043e4030074914160703459000849004001e4411030032458044500058201d18007034074622079004940032901c0c00402c20003103000d080980c90281110b400c0d101c0c2664513400e048030709510444640141c904070780220103d400c43c541c06000b60900102240e980c4480a0883c7c0c00144074600c05507403500304408015072406000f003590400c8a80303007828100940040e4480414004d584e4a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341232050 1250 341230800 341230819
    0xc0906020a1103071205010e060601030b011b08090d0602070311030405180612030a260412030c02070f06090509010b21180109030906020d021204050607020d080f0715020a050306 78
    0x83c0d81c2000090060804080c183c000c10303e1500e8500e0103804040b42100c0d55000380c0c000074050303503c60702c40c44020703400580d00c81082c001241400c400845e1060420354010101700248000ad80310219524201c40c072601d00182e0300e501c1810000c00f200c05401c4811581d8004200410855844505051401410a08414150711100c001a1096000c926003c003680004241035550780d8014046c1e0036011000c0540c05418801c401c148103440c0c0701124001c0c40e04981034068651103100c0d500c01c4030305500a0044800151715a803a444210440b54042c5000400341001440706041c5440724900402d010038400f420030034000c01c8e081001740306442e0700d481c2c503858600048081c041c03485940f47c0106000002c000e44181810000c00b07486103400341d003016111f0100401d100c03600c001940c1c01400b611500c10707803e01d030901d81080802c0c1c2c42281c090381d01136090441c0a000c6404100200407070899003410039910350803498103da030300440b64110684148140141e80314580c00c0000c480d8804011200d00d0007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341233300 1250 341232050 341232083
    0x71404140109051302040314030a050a0f020a020d120e090610030b03030d020f21060d0311070b120901060501021603060518060405010e010b100e06070203010920040c0906020a 77
    0x20b90070300551100c1d034030160048084820b461154002c1090324080c035101c000140f0000c0301190780384240410311002580811040300b5280c03040c80035504024551050b01c80d40482038002640000b6140342c1903482800509003135004982007003400585400595072070035180b801d1000201241a0700071020305254642c2c44011007503905000b15018100c040d0801c540390945e1440100ca03680003c42031103d40c02d4070303503032002481c554908503510440c0000c0000f040350320386035404c40f0155407000040d0f005101d080004038429048102801c0c12607503052202031140360004801d801e582c0a54003041c159004071a013070700c403070f040840188141c0b50000c03004210307034440540844100e041d09010202c0c0303018582c10701c0304104040d00884440c0d54004004d0010b16200810004000f031014084000b196059090703503080e00b061405421002d000a0001a0a514a4813001c0c000d240120740c007060814600520700e8107213440c1c4108040c1c80b56520305414018142000650b550f4000c0c42d010b4124402a6250764 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341234550 1250 341233300 341233307
    0xe09040b0403021606030b1003020f1804180501200301080d08150d0503030601080601080112030305090a050a1a09060415090219090903080901050f0415091b0501080714041401 77
    0x80380c4c1060341c64440e03160b5443c002801800c107850601e102e50340440c4003445c0300c5c0c1f107802542c0d0251040b0208601d00812140c006000100c4003500540050300c8044454201c10900d282e040010301900010880040c214100140001040102c1e082c41c0380138030041c030901c0d10004400820024a04002ca0f85445002c04420604400d910716640303c003002d0070711400c025002c0095030203200d0a80f00c080d04c50b2950001942e6048090051001162000d820080400c0c440c0c0c1100340c02c00020b80c2a1481d011040d12800d080c120f1200041c2d500845044031100410210f100e40f40e4008903641c0908140e08066030b45070035082c0040c040e4654141c5541000e000d40d0383e501e08a201881c2040b80c01000350b0381d90001c03e8003401100b00e064011561800c005003060354180a014032444080ea03680801e40d449581d03500c034600d0410f1000703030a903942d51814000650100340780c1c2110340b807106074103641d04e1030b005c0010030759000100210304000008104d240034401c61001e0b9410b5918a030201c651100790000100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341235800 1250 341234550 341234563
    0x402090403020a12030c1704082b0e010b1c0b071d1801060306060c0803010e0c0c06010807031203150506160606090e0c010906050a0e06121609060e09040b040302 71
    0xa40b83e158441204210140c05500c1017031000706c0f586448900b00d100c5103011980c004202c03130103001841c080095030b54010600d403030790007089066480c0c0215150300d0384486040780c0c000d201c8407410740e544d00b000000614103040010f1504000f1a144011550740d5581c001100c4000703001942482081c0030089001d501549001106400c041d0002c15071150403094544030b14428820700380400e10b07200c00400ca880c4243c11800c903443d080752490b8556468504900d81c604001484c06080c00d5090040e852482003d00090b4020701e4041c3c01000c442c3d0650a04007a10091001d4aa080c03502c2c0004414002c4014103480c030403148125049901c03a18810385491006004040c000c007014605803010441c0c90807503115408125000d4119803804810000540c2e02c01801c7c058070012074424046203030b2040c0310721030594145901503e03850902c00345258503080c19000340d17a041080721500000076651b5510060b003c00501e4546804030f4290400c101280318405c1c0508040c01b4044184d000405060082206 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341237050 1250 341235800 341235803
    0x512042403090206070f170f03160903150e0105150916020309060403050f0c010201021e0711040516080604020a120902180108030d0e0d0801330315090c080402090403020a 75
    0x5941d1760030070b40350200d40b0b000548030071284541210403401703200030076a06984802080b030009a2071925000400103d800c03000403c0803c001c00020b011002545201503080c03c0e41080c640400c0314a60380d15802c1c00d640d00201903507030720340321220b078090207542d0b140c1e48640242c1400c01e072a4260910510032400c5100d00b06035a508000c00050010401100040048000071000b00b503500359201040128203034881c2c40080003503030b46180500044100010001c081d02c502c03550900700a1002d02c0c001c1001d4403811603220303d5043c00c1a80c608515508840641d5000c0c40c00c840861410f01c041c1c1000e015028254002413110380e480d80c1d4502103407150382d6800d4603d4001411a0440c0d80d50780006984c941c0301c0803411400d01e080038800418100c000400404c528200e03200d0311166800c01850349807620b91204851702c405a110315100301d540d00c035203006102c50099034000c10032890130858698003a985078401c04069103080301482015600084d0142c00c03035412540c10300305031143e0400b240307030404c201c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341238300 1250 341237050 341237059
    0x90204020f040812030601090e090a0f0b070806010c0b011a040519081605150c030d060e0106020114090a0201050f0f0d090303050105010c030c03231605120424030902 73
    0x12401d03030220881000c0e10442e0059030480d00068400f007100609400155192030100f00c441c1014060950b000307800da03a000300311408452080c1501e45650703500300107404040e241600d07603070309000d8200c2e13001c6642036001400703080200307103100c42e5a60741e03001d0380c0c0520900398030740c40744050380e505074120744c040710010400104101da020240f0b030084c0099132654401d4011610500b103038804c01c01352000700d06003203480c010660503d214a071362883d90715511461003401030f4081005440039503a0341e449408090080003100301d03079542c10f1400103801c480f00c030109507000c0100b000c20401042c9001800803641903080ca0403688624058030308035014050f0384414139000201050764288a60a6406046240d0003668188501d9a0342c00040d1024502c611014000540e5807003550082400303261694414084181040000d40e06040300c4441500149580c5801c2e00c0b0f44602103041c40010403c4203d0391202840c01c42c07505290842201c285928524508942500c494000e085a03019038031903400c2c69001740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341239550 1250 341238300 341238307
    0x1905090d060e0f01150e07050a030e010c0201270503030109020f07020306040b0714030402010806010305041e08040305210a0e030703510209030c03030408030c190206090f0409020402 80
    0x70b07100d900c5a5841444000c1c03503181941c540c010b10050740d01c240c201c0d000e020042c80715444503182111568880c1e4000342c203154542200c8401d80209209201102a03035600004d0703980e91219041c1c0229201c01c00411700c2c410f8903031082010442c0442180d0441d520142c2c0144e03195144005002580281c1034040e5041c0100c0d800c002c24040c20080180c0306503080d580390300302d0701da11074586001e9010564000c0d002034116400070700b0b594083d80c0b0541e00f003800340b0044440d012170752541609c40d40a541080b2040b041c08101002080000c11803441c4aa0110342c03c0c80d90200084c40304440c130f000e462543d07020004101c034001000d0f1802c0c0845000340d504100c442a181650000045c0180760003004035000c0b0000c00044040048030030030000303400b4030f01880c00d41515140744a04019400c4910401e42c940164040025982c0d000c000034801483d025010b1522855604101810107000c4100c20030111144070a10005035074010403600d10140c03c440c1c8801103d55000030a0040c004034200940061000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341240800 1250 341239550 341239571
    0x31e0c0203041509060906030507230702031033090c0905031006060207060309140601060c1a130206030a0f0606121a0a09111c060f05061905090d06 65
    0xc00100b09865811000080100010008031a082d0840c490980000e102200034400a40300c1d0300302c1500b00c2c0113881d04c1c0c1c103400a81c405a00c0c60304041036100c1074030400003a20b0402c40c01d060095070342006207004100700c0e1540c039411200c5c500054000180e0306410500da0661050380c01080040504000310003000310003200d0501138011411400b500348244038444130310034501c0c00b901a01080c0c84803503010b03221070307840c2249c15006005040405c5a03000081c50103901402d404101c40760080065a1302c0c8001e030485e1341007200d5002c903030150100700180b8007010001c10803241200040030310340c1664055a680c0d9a065804000d11081c1c0711000800d00b011000245144e01044044110502c500100814941712582d4200d1411000310a5040382800d1010000c401c1140e000f80345140c11103d00c0e900c0d282400300154246d02255240c0030030b60340d580c0c03001d01807a0901803003000505426a2101e01e406207920815001e1901004c3c580100200082d8403500c90300d81c1d0008003105648444140a03540c242c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341242050 1250 341240800 341240803
    0xa0602070308060a1203020d0f02030c030c030d06080f06040803060a17060a06151e1403010603090c0e01031e050115230405061305060a0f03060507140a050a031e0c02 73
    0x350b580c2c0344204004d44000c1843c003000703400d50401a50540081600a0f000c0e20151a598a400050030a5010501080b000e55200b0320040484445ca50701555440074035007210300450740141c000c0c1965a00c40919a64000c8001403801c1e00560803c40f0320f51a55074007030008010340441e070004c003144400b07098284040b410000d102405041c20740018402c0782e41300d8007410f400d504000d035400700007400b004005100c0054000e07071224410080c54514421141803800780741c160710aa118400203a075071080f0310113000b800d04000c806040b001100740c00315491034660190034858156054034113940e100c4181c08008003580035421844107980c4010b64143d8803001911030510810b903071207982a47c5100c1500c02e20f414407071140f040070300428080c2200c50b260f50181c001c1a00404058004081d004042241a204110a0000c611459020031940f40c41c5800030210104020303402012070007409100c901d1a040015600b090409107800a4800715442072050200545803065110a180460303050000d80e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341243300 1250 341242050 341242067
    0xc040510051c06061d0306130308041a07120608031e1b0106090e06060a1508070216090b030c15041211040c03060302090108030a02060f0a0f0e011e050c031501020a06020703 76
    0x8070081040d00c5e00b03000e6018551680d5045030128a044140c856130700000b8019003c5a0b00603010305200070f0180703541e240303001a00d44144d031242d0118064074030401420102e8042e44000d003850001440c1000e0034590190303040441c88000354084000840c3c4511401d04140d40c1c0d0540c401008002d004203a6200300040c010301d076144010b0a140075000c00503045041c0b50b041c440c03c8400d103480c00924200d10002c100e441c8207000c0c090100f140261102c42d281c91001e420110042c0011810010382d14081c5030401d8a0101c50f80c0c021230081d0360008061400310342c1103040d901103507035540d21082d0301201890003494215a0302c00382c07540320f450100d041c0b403581d80c035a1003001541d209840400d15079888015240d1b880c054400f4140042c0d03c079600080440d64990155a00810b0724400800d000401c42032440a6401d4585000610384d943c5c6500c2c4a00c20f60f000c3d0344659005c514104101d2401c0800000100744401000b0303410f4241c07211b007030f070190780d2080000340300044d0410011500c2e00d5540c680200202c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341244550 1250 341243300 341243327
    0xb06010e040b22060e0603060424150f150f030e0106031e1703040b0606090d05100f0f0209030709090512030f04030e010503090312060a090f0605090c040510051c0606 73
    0x1484c1c400c0100b441e81103c079115006100c0140100646d0f99a035070791032822800241107030200b8a44044107020388019000390342460301c106802150f4141006160103400c13000e42c2c002000d032503001c203954800360f821181d00c05000da050300d400319008540c404818058034481d8801451019125441d4070010742c40000c8a9155100745038400c10b0310f45100f1104a203000555028214a0901c4c0204090340307050340041a0131400601960000c001e962140e030309011004040c1c0808544444000c003aa600f180b144484861a03402c0c01c5040c0801040400e548441d58080d04641c29980d00e13828051150400c140410309520034000340c3c0d2032502a050500194096500700c001c00c8400d842c02513198054001e807445000c99400031400c150200494010600c2c2c0a0b0449801100a2001007042c25040c011440890659000130031980c3c5003000780402e80c6401000085c60300401d1100f4030003030f926180d08008031109454500e031201065400a06110352004180c411340346442030000301a50481e00851081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341245800 1250 341244550 341244619
    0x4080109020f0414010e0405070b0c030306030105010f1404020c0c041b08010e0417090a170102180306040f12050405040603030905030c041a04020c0f2407020a0b06010e040b 76
    0x180c010b04144400d0b038242d650a22030042c1d1040041c071080f10b414068540c410700890484481642d02c41001d8410742c000271094019400000820190b400d0900440c0d0050901c80705808042e450440c444820456410b0524402d43d0002031300c17910018108821169500c0042041100400340804582a007401004541c04a107900300002404a00313001400d100365001400401580b845403540d01c91940304001c80c40d8031120b00d84021820509245420042d00c01d0b1034001030366010060001c0c18155030f4602082d119030320007420040019000a62890010790080707411948140c02d003426101409560040c9801c1450100004245640181071354200c0302d0940507901007240304410701041c0c2c3c0e40154107000d1048081c5d4181518101a0300911091700e140d420744074802c3c403075179100d07080521808520301c0c050141c441300e441c20011f01200c3c42d0800d00e01d000500b0204090355030b03041140b000a20140c11b022000c0e0300c401494030344c2d4000d4490140002c181c40300f01060050740f96030943c540c6c0c2013105c44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341247050 1250 341245800 341245819
    0x515010f050406050405040903030e06011e080c182a0a080a02160803062202040602070602060f01030b06060403020909100510030302150a14010909030815010c020907090b0408010902 80
    0x312030240c8211410b40b2926034440c1d161a04100c1444054803604030100c0c2019543c0820240e400010701680703001c0d200a9490202d22980f50000c0300b4100b05640100398180c00c4160184a41d43e9043d8120481d15419000301c4116070341e1000181d107801a605100020700550f00c6103681d41c02c1840700600704050503440e690030640342c2d85881d40403400b44001d102007c06e00001982d0100c0d200e24051544440020320500580580e104080850704034400c020801b0b40d00802c040c41800c0e0148969001350189200034105494884540d00c0440018400605500315620104115031107100407240603603005414482541443c002081d07896001080400c4640c5c6000c0208400c0783c16113803201c0032240c00d94010158140c2c40c1e02c2500362204060040d04401d9612548200c01e02e0708450300301d0003045144000903500117907040140040301d00409400503040444403035007050380c010240545154040e01c0030b46855490754429110b86200d6081162040404580081d10440540124040910031350b00142c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341248300 1250 341247050 341247077
    0x30309190503030a1e020f190c02150702130c11010605030c030a0b090715120f05041208040314030108011e05090706050a051204030c140607050d0f0f051501 69
    0x311006540d10040c0a50800c0010404114241e04422098541064200c0080b8140d01d4944201da1041e444548251004035004d04034201020411500020300d0800810548841c0c0c001000005c2059002c1c4800c1c81c00704d00341003552a128000161505140ea04200030a0900e0b0054110080c1d4482c1e02c1c21503003482c0c000708150402040d0f052000302d002d801860442c6103951008414200180003100c2486441030001c1c800031034611102c850390942d103030311250b05403401c503040680300101400052103050038148800201c410380d5900d810481841c112915480d10310b811a45240f800e05004031404012002103422030044d401018203108030780e1561000f8484200a2042c1c172003c552140f01500140010005507000300003c248411003490000d1074000c0e0602e501d1090304095500b503001640b4084880100642c1a024040000c403620042401745017048006100d8490301011098454403140002d20701280da400042c84400111010701941c680303c0d845c80802450341c00c21f00d0000e1614200b009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341249550 1250 341248300 341248333
    0x90506130c05030c0a020a0b070801030b0f250e09180c1e0108190204080d080a0902100f0e121c0c03020703172104050c030c060301120c0512030309 65
    0x24801449030300c8103800c5036504e140107070303c94122030540d0302940074120200000403003888029115501d25140c0c000c01c1e505604006a00c2c0c10000d141d94440d4654805224600b541c1e14503025641b10101c00c0241e141010356012603000c825208001d41050141c014810002c0740000104118441c2000b10703465445688104092528050444078100500c0807800c3e91a52150f03130721742d600012808840c41030b220007080210481e0300a5104105641000721403545807540b00d06900d0304400c07040001d001e50221600040c0c5441c00c0c03c00c030365051011011380800f1030340c06200710311018000200000580680c040e03080303032144907200303180310a92524190320810a0007000e081c000b00350540d000b0701240b13066030344499642031940c000c1148c03110700f0702109c903240d1109000044605005015003c0504182c94440c0c0b03002083c6540a100f0f411094401506445003420750b8112000014082030304000c90807c1c0318490b50070b82003540c0002c0e24205c0612820000001580103111032002c8481c1d510200c003140d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341250800 1250 341249550 341249561
    0x3041202011b050d020a022406150306061207030e0a060b0a120c1a0706050109090c090203070f08040f05031201061806050714070510020c011205010b0306060d110409050613 76
    0x12010030303c04e016114065140754041c10a0803040c3c01110540c14200b1030342d12200101100f02030741c2181e0401000700fa410408900d2030801c04000d0680d045090540005502d4003980e145035101c2014480000c0c0f03002c1c813075000f0201c6101c03c0b90603114100440d007860005091403241840c09212907207000a880ca4a0f904940400303500451601222803d040a6001d0450b1221580c100d51509001100c045400341c0308243c003d0905000026580196140855131070301d0b2a8802c002d40b070300c10300401c0020f54000341c01441061080ca0034820a5550f071030000055920068090103d200116804484040002405041e503400d078aa06d4800303d010309011405824034011040020f0041c4044800101c204001c4072035245110140c501480d101c0e00402c180c1101d0742000d0005074001d0652880341d5030080642882c000090809000035810324010350b20b50321018003158011000080c0c0b21500e0312155124070100c4c0030705a03040d0755460b900e00c0c1c0500600380a554880c440c00a844010052054030b1058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341252050 1250 341250800 341250851
    0xc1e0b010b1b1605060304050a020a0f050f010c2d1703010501080a02191b060e061519030f0312020c1b060304020a0905130501112a1908040b0304120201 67
    0x2c40d9600ca04000a11405d42c1000e80200c40502c908000400107a69451002c405400c0c034202c4500c0182c5448100043c4220460714117041c40000e00c41301d00031030594440b1510a003142401c0c940459410003804035aa040320741c0240c1a1000340041d49000e01c41f240041d4100e400c242e954907c1c0780c507000e031090304a108000e02c40c81600b80400010b0703681c5000ea07007100c20308110b42d8030510410760b007a01d4400130f0707518102e5400e103a0b8000f4010019103180703034420940c0c005c4082d50300009030070320444210020840c60101130081402c040c0020201403082d80341800030580f1070310554072034220008150303039a1039601d4020b0342c410701101c410390f040c105201a44d12541d002801c02ea40c9919206003c0c00500002c1d081140b071000c4541c410010500901503511150386009150340d40d107070082c0380742610643c0c103c0a0500402400081a042c490008050b40d148495a818220340240b9103440c060b103201d02c0c0d00c40d41c120680032007000240301c80c0860035209540300c0d400a01c18401185044881d08644100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341253300 1250 341252050 341252083
    0x1d0304060806040f1a040c090803180d08070309080d030e0c12030408030a0c20090a24030b07120203060a060e0d081b1501060c1e0b010b1b 61
    0x2040104a01c12803400ea0840702c00f03400050341d0344114003800305a400c2e440300c0d500540480360000762513040512980c40c8410741898204211410811416181c1c1714046500e85210a50074004402d642c820070103440803640000c045a07208964640541004007a1040210600808101e80019806070190680201c10040035242c0520b5442c20820040c07081718091010b80300600010900110400007001a103030592500b00c00b10220385030441094a070b80001100310707400c0c5096600c0a407201c0031560f130498000f09000c61222822143e0300710044072071021100e2054000000014040448800c500448030303982d40302d50b8030795200b0a1500360f1109035005c50704036049a4041008910500000481d1540103014010029040c3c440352841c1e08501d41109100c80a00340b1270381c84420811044481100c1169100d605600d0044050500340d480b94003e0408006d00007000a8010000715543d10035a02c801c09041c2ca50b11881403554a41208181004003454041080e5204c4000101c0b20226400a00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341254550 1250 341253300 341253307
    0x90b0a0801060815121e03070c061407020306100e06041a0f010210020d060609080c030d030203090a050a11040e07030b1303050409060b07021305131b030212101d03 72
    0x421601041e0052280880c024070078030f110304ca940c407580c0001440c1102801840d060030141c90383c80a0754480c807282d100d071368130410031000059403410188045074523604017009101d0104c4c4a03007240d8070036420000d500d80103c40030412450303d500c80359400d4800740d243c081e925a0701c800c1840103d5107000e540a1070303001d01c0c0c0c40c505018640701e151800d00145c1131050301d00156414044105a03000040b2001c0c1c4191912018400d0380c1d484044400142100d400811000c6c0d403d0012031b454848120b0440200754000000405603202000389444a07540203045542004890070300c06180202541c078a44154105004044034031400218031099a404c40380d04d2115407120300f04c0c0c051071240245e0490a10100b80000100e8001e00e1003403400500408440741d41d03a0b42a44100031629402607680b90f81d9074904000d2007820606070340f10030000c0c1d6001403203405a010031882c00e0409407460f80002c1d0300c00191441212081000715a0b00c541000c0058180316220340072217a503000052a480f40107180d482170 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341255800 1250 341254550 341254559
    0x6081302091306021614060103030f0315120308040215040e060f21070510080c07021e15040905130816031b05031815040e0903041212090b0a0801 64
    0x544000703800090144001001a20683e2104240c3c0c0080a100304a40710540104041c8104c01e00c1001d105404403000d03144940c1981d6001d4484803c4d1009502015505ca900c014032040c1e142d0404003a00c1c4102014840c0c152900e8000c0510400b05c0b001c0380262200c6048000d800c1c0b42000f91004d40e40310600b8102c1c19a5414103111070110700b101d880b030b0f101c0e03880314120100c1d10084164240d540e01e0b0b00007400c4c0a5051600348180e8001e01c00d41c0c0b0007004000410071107030303028401c180c03141c090f8100d41c0381c0045880c03441d190700c00c0c41c03102000a6100340d85010b856520901c0c14014000c940360712030300344055034a50183c440404d4807000040c00b503090800c25801c6130003860781c0400c1c1c0e982c824100700302e100a01e003c03a0004003404000460342540009010030009020f54103500342290211002941c48040305000311107401988a000f1040071004003081c02c0010038000e0b100500310003107062045d0021030070b1560107055070414510100380c41200214030000740e10201d9408407182d880311540350740b80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341257050 1250 341255800 341255809
    0xe01051b16051009060503060a030b090f06130b2e08030c01061205031c020705030d091109060a090e0f010207060605090a090807110402210109060e0f1501090909030f080106081302 79
    0x9000d589e026250482c040001402422618044c1d03403403000030030710129076034034044c036014028040052000211125100040340d0044542d404400c400c000890120a11783d052034500f80c3c004c0040d00d48035400c501048101e00000a48104140040280441d03662480038440307e82d80058003030081d401c2045600a550b64101e0315280103003003800014600040c0c2e445a9040d50415000d6004c1d40d500c410810040c42001c210f40b0515a03c122075203500c50400c2e40028001d10b1040c81004551074955000400090041c49022890040a0025503a9a659180a20040210340101482001000e01007801d10040d4840c1c10b00c0c2c1944807141d45d10300400c0b41c0f035400d032600c180d00006078001d0b02040070710381043c1d0038000d070700322004104e010101d40d504081015059500300e801008401000c201042444002288141c0d0841c22107542042070040c0b070f10040315540c042d6001041c6e06401c1101e810201640140e0040d8044c4055440d5034087c1d880701c83c211120402035a440c082c0d010301e0f610300405071030f1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341258300 1250 341257050 341257057
    0xe06090c0105030c09010e060415050406030605030d0206150301020702030601030c030201141c150b0d06030c17030d090201020f06090a05073305090a0f0509130f030e01051b160510090605 82
    0x4000c00381ea09090751548100c1c512b05865800c4000600041010071000d905401020060001140984220707074401400035911300009003420081c48648461a8054800f0350455554a4000c0c0c1501d42c82d40c0c480c10004400c5040c0d200490004a903400300729262910302c0b00f80da100c03c1c41c103410348050a070114107603409000340c83c0a500403481840343c00901c5c07483d55401081041420840400c00510f941058200301102c1d50000c03c49514110381d401250f6400b1044440e02c1c5100080080d801c000da00040703142200b05504040303a4490b11702800450140000c681c40418804c904a804540e201c0268a81107000080710700441c4c00c0c400100d1158122002c04a058030b4020325100e0300307004030000001e03904020340e40300301d91601c42801e00340502d003041e240c0e095100c041000103c0c840180303580c41444c003040c0408003404000005080300c41e560b1240341160082d0040500341c0c0c110010f000381040d00d4411220700810b2a1022090009041c100445840b4015032a0303155003c080b0f19251050b02d1550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341259550 1250 341258300 341258327
    0x201020702090c2a010c0201060902130504110d09051c030908040501030911040606110114010b090907020708031207300e011d0d0206072d020c040e06090c0105030c0901 74
    0x40880d1011303072210b424a007074051030b2030f000b0780081041401d220000c1d08540c4181c002c0c26080c0d00401c1300d02c8058000c404080111a420741c1c2c0021601c0d0510f204501c64000c03052424070a905003503022060040c0001c00380d04640c054101c0c0c501000c007040c010343c201c44580e00c008080d4a002d03c000c0000e5030081d0310500082d4010365003a03d4003c10300d070008007203c2440c0c0004001c05d01101121051079024414909000c03070300441c1007065410245c01c010340e07000b4140402e2082007035a00060019200384000c800802280044907100c5990040c81c01b0300d03400445000b80000c21403010f07207080f00c0d8250400d4051500501c082e49010510184000140c13240c4801103403d9034030b502c441c0030903031116000b01d40c00030300c00d4019020f00e40d401c030740090502c5d5018148070104620441100540d00482000585800035200c0b40b011211042c2c409a0512905007501540f180c40d101034500030402c0407998a20038003e2400f614030b80c0645000540300c60005482030030b805002031084a031254001c80c1c0996400c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341260800 1250 341259550 341259577
    0x30402030a02030106060519051216050c01090804140f090415060b030a2c0705091b030906090c03120301090903050408030403050f0c0a080d08040602130e06030d0201020702090c 78
    0x41c1c00c0c50700801d080d907216901c08400500e001402c144d0400c01341f40c0e8400d90204918025262012010b40d0039101c503400b41200303485040346021514003a0003503080714060700600e0000c1c01441d2650409410f240c00c00d224a00703016a100c076205c0303241e140c59030750007148201c014000f0056844070b84404451440000500c1441d41d52040c003c613522240001461040005203804150854003a02d004802c45a1038640090b424040340a40c46001021a0030400c0c0c0c0c4040e0b80e48000c542d54681e071501c00028224003503a0010000040c484030050200c3c1443c410f140400813a40c28118120905a60b060208010b003100303901480103100340c0010760071448800380640b4016040948801a80e41141c0c007961003143d41e5401054001910310050008a0100108980070403100349040030b0302c1d44078020443c10a0400820800050070020300d9416076003501086c500c2c40e01d003030382c4071001c07035030400c1d0141c5030240702e8440c842c08c0c11a09032050086070318565003c5d00280454070341c04242030b41d50b0845000d41194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341262050 1250 341260800 341260813
    0x2100203042310020c031b060606030703050405011b0e010306050102061b0c1510140102120a05090102011b170c0301030f02060f0f030a2703140d0f0603052803090b03040203 76
    0x280f40b150b00203080110818805142d403503d10b411441001c880070b03020101c00b60004c1d800c000042d66011700f540da014689050105481d41d4030f14086005100a01d481c030341900348210341c83c0c0e12a038002c4041403207000a80b0108440743d10f44c80103a0707440d07801b04c50480003000b0102c00c013903101c0d003018003074886000000204c80b64442c0320032100e1a800301c1120000b64600744200200104031406042030507400d0b080c006040d10903003492082c5550f01c00d03c004001030200008800000c0d074405d5003e0303505070f08500c49101c183d00c5151001891013204500d800718480300040031660001a031006c50f8103d07a40a000005544850307828084030781c002c0b11850244880510420361010a0700c4011407044892040000c4c50300c010002d81e21001508440c46a105200d0028000000790002500c1600003852400079841703038401c0703294101900e00303000a080c0c050708082c0008100040054030325803201c400d400354800d5a1041a0301c0d00c850b0110f80340500040c58000e400c0002004160080d5007042c0090284c40c45e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341263300 1250 341262050 341262073
    0x41a0d050a06290408150906011401020a111c060246120f05040210030903020d11070503010608031b190201030b010e03010510051e3601090c021002030423 68
    0x1000b0000700080d28028266081188071f40013441124054017a02400c0d880010060300003e42e54400c0c414010414030401243c0c01044d40c410030700c00070b000c0b02c0001e000b00725041407500701d0280d00700d10011222480740c000c0c6104a0300325140c40d40b00c401318000c10041d645203418443c0c082075103e1448902403000b00001202001c0d198021100c50030b0341c805004c80c0d5030800b4070502800d80700c0c40c00c1c0e4a0030146045410f1000960109030404c0b940002d2a181a801c6a12303014030342008101e911143d49586400c400282020022000d000c181a0b50300c24407001d5404031613200e03151002094880791840c06080040010343c0030307602c448a030180c1071412010600380e40010900312071041c0c035400110001e6200070001c42c84c1014031900d1a107030082c19004866a845d002c1001c11001d074034841c00c0301d20949000450003c0762034903070603640b071042e071000d0380c0b56540c6003804000d240b02c0798188014041c0305407009000a0b54000c881c01607030b0000605400308034440e88141c401e0075896040750140108040b018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341264550 1250 341263300 341263303
    0x6061d06030a02090a09200a0e09040303110a0c1a04030915020727050703020f0d09020f0a0f06080c0a17060a2301090e070804080f041a0d050a06290408 67
    0x5888404000541441f0350301940460550b000b02514480c4000c200b003500559101c080d0744888542911111400d48503032400380e000d072070744940c3c5510324103010440340d050552207000007801c2030284100c00d6100340312109454940f01e0403240a07010442848003000f004008201c14041c81c1c40030305c1a41e034a5a11400e072401c03800c000309400d08004101031071b07071b0000403464840c05420001508003140b07001c08011000c94507005a40b1480c080c255503280500564603154400c050310107000340b41526280d01d5095003085064503000d03c0c000030b08100000b6080e101400100e860482c0340ea21342d0003800810701c800304000c0500900316a04034a00c494002103c10b07003064107d90f00f0501c6009013804c117a040d800100000038681c00590801c0e041d4090001d000e03042003040340c00c5900520303520b5641d1110400070a50307108a0744140003448102c500394418501081c00b514071080304103410b00442e00c03200402000e0303030040e024000a501d0103800d4410040f901d1200b840c003c001e07a03442541004d07520000203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341265800 1250 341264550 341264569
    0x2060a030204090506030c0f0d0501060b0d091202060408070f0f06060605190216060804140304030c150e1005031e0f06041506020a110a0e180106061d06030a0209 71
    0x4a41c0208040c0801c90341c2c3d01560fa4000c07400d400a006800301c0c0d030001103039650a200c4640c05401d6040740070082c82020341000e00501150f4024556803102140d01200504000400390303a40900086013940c550b03c0418904d0007240c110b03010600f020344e50303102e200d10311111120031507078034501d09940d20002e02c40e801200010142c4d61950380d103c5020f240c1112469803000c1d030b0072046412076007100000022403210741060fa059481c18a86598581c6800f50100300001d0a024040c48040380000400a1703504586003554110b003450115806c0c521800d4420081040d82d13191321007802d101b40d00440e817181c4003840d070214810752900c903010640e070192040c5680640325840d210843c44100049800c01e401010550141a4004400e8601e804c0b070081d11682880002850420b003002d0b080c2c1145d40c1c41c14140082c1000c000305c01071509100f40021032584407041e24841c503508209000071164010a1141080f404001000058110070401c0102c550300c0141804955982030045044503150340818 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341267050 1250 341265800 341265817
    0x23090301050a0e070605070c03060b0d1b05040c110606010e01030b18040203060c0403080d0c030f06080120130603090f14100e010b010518030c06160c0b0403051213030206 75
    0x3c0c1d010307602d41d4610f0502e9296042641400410400000050804844201181d0300f0410009024080c0800a84601e102907805480100d1500e295151210b000e1060ba0445104603403c01036071740c07800c0b0190b40081810041c8849508a01c1c00a03066502409940901d075205245c001403545c1d0810004100e0340c00440350b9a009c56a580405c021403c041000301e4110255001c6281002d03d03503075031883c4c240f00354030341220082e44070044440641c2c000d81104104400c90314042c170049407180032050080c01d039202d406d0003184003a20507003100500720702250090350703142d1150b918542c04d1040a5024100b42001102c0c138170009503c03070000c143e18602d000e000500c0b6074007030300402a0400f0002d0640d8403011440159902d030900701d40c1141e81240c11181c3d299000349084c001a491080001c0c01d150034680300c950403c45c005408d440e15581c0441d030725601441111405490307621148003d4690096010040c40750740060007500c01c501e8000301034201c160041c400c403200b00b0780b658003051036504140803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341268300 1250 341267050 341267071
    0x91005060c0a020301050f150d051203070815041401090c090504140105130c020c211b0316050d080f0706020d051005031b21070b1305102309030105 65
    0x5402c11843c0a004258015103980140c803090305005404001c824003000d40e041c40ba11180d0104e02c10800140300c19000100743c01c505a0716131401c0c00014100b000d08a50500c904c03110f10b54190040d1906220b04c14050710200340745c404a030f08040051002b000440561024480303140c2c000a400d50743c0d8043e6500340740c0440c1c00750240d0f524000600105a12218032000b10a09200ca10307020036500080440500000700c400c2080e6445508500c400a105901c403a15a405600900280160030242800710740c0340c00d80131500030b02c9050404600013200c5004541c0c1c00403418032a03c01241c02c0c10042c00007001f000483d01d10340781e501d42d102e130100c1c0d0020100048c03150b11101000521004070300104000c020640203400000c04c0b00103158491201c080040348146e092607007200c40e4840c03403140884040300c2c2c0c0041ba440f454440c540314409400001d84c0243e00d0810320380c0480d440c1005c02051031980d00584074103506030007481c03192002001e0500c1d26501c0007001c1c00030584560b0700340141c9008050303104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341269550 1250 341268300 341268313
    0x17070308060a240c02100f0206160203030105090411130504060b0d020d14030904061403120a05030a0e01020f0d09110303030c0d09020d020a0f0617070c02091005060c 73
    0x240141a0000080c9241c2c451201d52900b044807151041c00c10603040015101c82014540d071600607591080400b10280d001801800c007018411303041000c0410075050703902207a50541d11035110224044514841000503042400104510304000024680042c40b03205090714034000c0c88082842505110900c01002c0e840d102440b051160710701c1800b038010001c1e1128902c012254000c2a00301c13810b20350081c00040c0d84540f00c02603000c240300355440b030000100140318042d51005149041a00e1110707441c03180c000c180100e660700d9000011100707044101d445041c2159100758030f000c0184144503000881d07540800102c90314031451402032080505114001801902e40d0900302070760405242100d00a44c030400c00e014500b6034203000d4510300c1003d10800b0405041a2000c15081d901c00c00f0001d402103104100400e480000d0200f6030141e450319038844550030b801d01480d0b40e142e007065aa0101080c842440c0030054101071882c0c660103c01c3c400b40700445070b80c80d400303e500d9902107444a440380d04002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341270800 1250 341269550 341269553
    0xd02070b0f010603110f0a0309060e1506040912080403050403210f08040b0105060903010b090a0b010f080606040909140f01020913050103150e1e06041a090d1404031707 74
    0x5001c0680540401d250410100040d02a005940d204402c1010072018001c10500c202600c29000000c038030364032150502030040c9204c6403540d50b0000b640021a034000120028040e410603104d0861134503001b040c12004804003560503254030070301a0095040040802000c408500d04a070303489039401c280340036001d031440380d6000104202006040002081f2612007440003040c02c03030359003506680085440c0f55480c4011b5002a005000c1c2d40300c1584c00182603c1000000f008903401441841c201b82c031207035002003615100725a40c01c0102d0b030855004106000038849252240d1000120724401c03c0f10340503041e4000d1405180892413008980030317a400180300030389401c0c034101220102c08000030901c955415666910046c0c045411800c2071b00d5034418070740c0d40d101002c0100303642056a40744920404215611b4143e183c0408403020380d52084610084000340900303a108a104000000c040d000103c0500d00071501e10342c2640c01807040350028080400403d20001c101503541e00e850000c1c175a07600e841d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341272050 1250 341270800 341270821
    0x71202040e0f0105240901031808040911030108060f0406020903011a040615120917070f060501120503070609020a17100f0504021503060d08030408030604110c03070b09030d02070b 79
    0x58204e680a041d003400b00311401a0700e00c0b04d100086075983c3c2c14540711000710b03004a0040c000e680c10402005e005035400300074000040c0060082d50480c1200b0300c119403c500c13880c4842e100a10464400380e01100c0060303581030110388030a07009441402c026141400540009007518200d05074640038552141c1103012502d010701c505402003010341040500d0346280000a09101210f07209144075540390b0288004110201408040b40e042080f00309842d4502410440e24113034280000b182c15519000010a030100380f0024009080d9014004600c0e2a104c0d94031030025040c0068201c0c1c00155000004c40c403803264803c110782c030342c44c054010800b21115920603416941c0380d40b0300f100400c3c5404107000141c0c07111607000c0405910007904503a6030f01c442001c02c00c900f001245c041c2c0011804014841007003480c600135030285008590501c05c1001c1c0300ca49518601ca400e0764000300b80d03c1040400b002400c1014000d900103540000c3d43c1c244150f5030001d0b002e0364808581210525000820000007450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341273300 1250 341272050 341272081
    0xc0b030c09031c0e0607080d020310030c0614042105061303120902060a1d04020d0218031501090c020c150c07060207060804060f0e150105010905060c0c0603071202040e 74
    0x10f0343c882c5480c2c041c3d9000e4003070030b01e98809a965028010014403581448025000c40b801c81e03e440200f15504c0c5040022900c500442e8042121494100c00000a50340d01c10720b00e200551240802c81c0740341c01c0c81c0c245406001c0b014900325004c1b19018200c6503022600612120b44100840c031a0181c8010301303403a00030404110000269820f6280490620150b11500c1c2500e0b41c25050782050141802075071580031080c2c00d4132084940c010b0001907401101d2046401a0603c514074159109149035850308040e20b61084a541142c400e454200404c48002950013072509441d041c010b58201c88100004614030280b00d252400c032407100002c448071804000c0000388000c010500c05004920b0501d070005103801030140001e03001580750f14204900718415801280b2401c1c0403411039001141100c911401c9003424490580441d000d880f00141d2400c00c8401c44000c000004c0c0a880b218840800b0480d4682010309140c00b00000c8041c400504c1006200900140102c040014694a4000c13070104c0f4100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341274550 1250 341273300 341273323
    0xf14060112090c050105090307090908040e0a05130201031104120f05120a0c020d03030e1c1e051c06050a1707050609061608090406090204090f0c02190c0b030c0903 72
    0x5141280c400b01003204402000107441003481c24595481000d400a032402c1c85c2a00601c098a1802c1c11800400c2480802030080f50281425200d441d0341340c0801808842c41180c81d258050307078001c07400700158400d90080c1031580b840e681070340c00c2907141c81d40160540c61100d03007100d070000d1840c00d00d410700404000100203c50244405880d10b1a01080100801d0041400a00420108600d46c04141c00703038000081d4a4135502c2241c010400d02090b19520a2124201d000441c0b000d5444016540503803d45007103131021511200d00c0c00c5a06011080749071242018240380c0d6035265004600d50380c40541340b100801c0d512031003420301c1c85201c0c4a03d0804205074802c1d0711464040181200701e480c1e690a560b90700c074a401107201000160b0403c036030188a43c0e4481c0b41d02501d040004581411075601a00548204110800100102045160450740c2243c0c00c0310169100c07a007076031504502e14030500c260700c0c410340e02c070f0295690300c21a50500d6001902d90122007040401e0440640c00c080000f0008030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341275800 1250 341274550 341274587
    0x51909050f090709060c0602070819090e0105010f0c1115041d0105150703020f0d0302070501060b09090f0a150b09102d110601080606010f02010903080a0f0f140601 72
    0x1818034850143c01c0d132009104402c00d0100d4405424240205070741a103242c2ca030800d100d542d9809102502c50049040c0c0380242010038001c81c03003c19520b13038941c00355050b1001a1142c1c1d100300030008080d41c1c80641d810b0202e0791700361030400e5624030341c0320000003250b00e00c500c3c3c0300c060f1180d0401a500021030f40000c600c42c3c01c2800300c001080250b5a014280c0d40e030440541c0c0656450140d400c049081c07030120090604548a8880401366051f8154000e08001c1d004d50002c1000c0d58131100c003a4520b00c100c2401580c4030015502080051400320070703603078000d5901840042e0f89800c3c1d01a076580811654030600e04518042450403481c00c108884002898540ca04450207401040e40005074418401202c03e6211002c000c942015005007903003034420b00008201c03401c1c4d603503030f6003c0d82c1e03a2081141d800b40000d01c008444100580140101880c003a419110746101340d6804002400400780600000401500d409070380031100520300c10041c404003a400e8030350803440c0007400035101d2840d001e081c0f00d44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341277050 1250 341275800 341275819
    0x4090c080f121905070f2f030c0603060102070314061803091509040609050108100b1537020106050103060f08060a11120c0903060705030105090f07051909050f 70
    0x82400b940899008100c01c0002110203a5810b82c2140c041c01400c100602c60707039003950f41703105104036004100040d0313290142c1d002c6007550007074100541042002e030b800d806510450416000c0d19150340950740c04030040c8111901e0a580e078a4074140c11a84400e01d01003a0440e005002c44d0000c282c0131240440c194070001c614000c05500450750803075000710310f500c0d070368004a0715000b6a07513183c009100038801440d05000b2075031201030113915100b500011000351032810780050342508128803001881700a402c00d56042c440c3d400400b039150301c550786c214550b0504140c41784130381c1c049403041c501c2103a490303500008080342880005011504150010200d503c4161001c100c1c00c0f8001880a034440d24818010811581c8107213601c00d2801400204c803e101000010000810750f0640941080241103007201c100341c032509070561300342c0b101307009a5801c000b00b1400110014405003205030003501ca4035200340303400942d80030f125030180001c0d480b40008600703180400c03a03072410f2041680104c40440b085400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341278300 1250 341277050 341277073
    0x70e0f030303040b040611041805100509040b09010f02030f0402013f02070503040303110d05070b06091504053c130c0320180106080c0f04030204090c080f 68
    0x1a02d000081004000d01c0c1841d00040030445103410220b8086040100d983c1c50380d44810b5000806416100d0042050346440300041040000070a03140c02c45a0181003d2846e0b201c0c0d8640030400e17280107102c40e040d90340b00c640c10a1000304a10046101d00d003000b5510b03030300d07040600c0011300c1e6550f40301080104083d0344000000c5000300011241e443c0400d4185c1115000003909480b01034096840040c0081c01f01041c004107150708004480d683d985001c00350303821011540f009803840e0240c2c3d0805009005100300081650401c1200b080d0080c0300185c80340300e141c0115000074141c49080b948501c105580b43c0c40d00700d0810000141d104100c0d200ca46010010948051240544100801c002c5001440d09061010300030b03005861400740d60000380c20000420740d0494120031122592070103004030403601c413a01069031000d24507416901d007561006015260f810500304d154200750007110204400304000001a9520b2241074052442070b802d003425140b412000c41c7c100444c244d015211342d0000800002c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341279550 1250 341278300 341278303
    0x3080310170624031e0d122f0909010b040f0b0702030a02041d010504050102090109060f021c050c0a0501061e030c21050f010f060504020403030c060b0f030d0503070e0f03 75
    0x70942003000360700480f200030000901c0c0c84914803d840030200002c000005401010032403841c01d40090300c404000c44200c0c00750404990600301d641c0e1a209503541c00c0c00b01c2a002c900c20915a804100d101c0d4140001d500001c1d070b883e0401e0f44402c02002e0b0006c0c0c200000e840c1005100000e02c035480070300e418001e10f9000f081d1101e84495000380700d907503185140036201802682403c0040100c50080000345054a01207000b50300003400140854821000010f010b441808003078903203070240e40039044207030107017942c04045068050080144502485a58201c000800007010554000c3e0b00206a86281140281c210f0020310602210a5802c0d11306102040e041301001e0308941c14044c005200450070f08585400b0012030318028564000d155884000c0e03c0150095901070303d040e542040301680d6881040100d120314400140894141300844000c600990b200501c5201e026208040411400000a060205068010003c12000700c1401011035000e0b0b0141d40c1a038090b180300044481d0a000203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 341280800 1250 341279550 341279581
    0x50a02180f1f0302070c050f01050a210207150606050c030a0e22090213021c020702031006060503010315020a0905122d1203250306030803101706 64
    0x900800071002416a6522440320032a42c21a04040c8007010700400314005020754444a0309881c1603443c2900803415280030003004646a205031915890032002030001d8580952100080c10b0f40294401400f0003501c1900080424a00c19241510001a544440c40450300a90040c0c002c1140a003e001c82c9140000212004103025041c1540f05184442c0003c0c02d140710044468148040c0c801c03076120780c50700c42c0c0050180c903108540000d558081d00c0d040400302c2c043c213071400307101d444488260414458a50300800f0010300150680b000c4c1d140c27400520050351980c2e0b018000041000004100340100482024038036440d08000358940802b0f408014103005060107800d11510a54481d04101c5400700620300f540381d000d440c202c41d5035103080059600c00e618060121024014443d41c004040305010071640301d1000b04200d9071081d0b5090900200926200c40034200b032640d01e20001c800326070868080c5d03120f4075104801c84059800d01a01c0c0380903000d0034003020300a80c0220240108240c006000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 341282050 1250 341280800 341280847
    0x70611010f02030903160f240c020f031b07170c0a0f0e070509012303090c010804050a030c05070306060b04031203020307020607121d0c18040f02061c1806050a02 71
    0x11030450850031f060030039000c050203a00500d850030710420703c51290b40da1601c46400c1025054100000408094142e0311038210003003001e966007080041a030462950b8650000034030001080319240344d22040c01c060108203080410f8442da02c4840d0f807146a1400d011100e004d0301d08128841411480c04825940c504070207044001404000300b4101c407117902c503140c0301030010300c04d0282c80020040441400c00540c030550f031b50212800745041c165225401a201c031405286e00000030301e440c581c03030b8800715922152501e0441da0b40c09034003400000301c0c0880c01a0f2000d48107810307103d0368071071442ca0a4002c194100000360241070042c807c02c60104c1d00811041e0303100d0320a0500d40703081030380940814020130020b04000074008140100c011150000582400d01c0d02e000c0d50104c1503d00d11320b9206850902c115402045012a107400600504008028280e00c114181400c01c1c0384401308000d41c1a540d440f1500c000e051098141342e4103100d160b0041d00e8016800c48021450110518082c03490034801c801c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 341283300 1250 341282050 341282077
    0x304030c0308091219060605042703031b0f1205070806040b030f010614040b030c130b0a1d1e060a120809060f030f060a0b03071808070611010f02030903 67
    0x10f60b04001d45400c0b0600c580e2495440568052410001d4225510001c40506644c80341c9402c0002c2481c0c01e01d4495001d085c5010110780d000405040041c103500141c081080b010540c841e6140701c1c440100b00400c4d00403400b6911410b03c20f015102e4028445040d00c01c182401d07a0514003071001290300440035a400040954011442c07880c050082840d101c3c5c0414050101d6291200000b401d03501c10b000b14030380450440c1c043c0008680c000c10541e451051081e0f680c3d102000004244032080e0030760008100707440141a09180b280d581c5460b1b03d4000382107e0100d1204400b800b0006020b50000042480e2180ba03105400780d4103200700485c19030311140c01010601d01007044828140320319042a40c4010304010003155484000c202c80b20010781080c1d032007210303d81a4001247d1701e442e11845000a540e58110f0960650781c401c0c8086944202c4100d10b0b480c003030125030020414a60601c40003000e40490f0300d4541c4084011500b0600315625049441800d510600500814001c00310441c0c41541e02104e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 341284550 1250 341283300 341283307
    0x6010c0320100c0207150203220519031104050f0105010f0c080c0304030302070801060305100207060b041407091e050114120112120c021813050a0b0103060e0304030c0308 75
    0x10800300c051150070344461200d01c1201102d500900c650b8001c600712030020390035a640c80d9650210f41e4400c14040e104500503030801c0c403103050b0640e00f16400b8005251070001d0000c2090707a0b800840d803c04280c98206004403c0a041401400034910042c90203a00c01d4600304110f00c2c220b115081c030741c0418003c00781080001030714103c4040c429110b00c20b8039900006015038a0342052000741d070701c3d44a031200b1070160050001c00074402d80b040c0711700800c50350400051b05000580d00717a401c0080d40a680c08684240d075901c1d1051003510365100d400c1480d424581c10343c08604222501615681d0960300110a2415400321195928001512541280c00c00e0130603c5150070440280182070066008100403281c0c03100000594211b450080603501e4014420116803900c0741000b12540708907540c01a41160b0004003c00035a459102116807003484000900030315800d5607a440e04155200c1d03026944e500083c4018028842c40d0710030064403060100c02107203010b185990304250791905e0f1001404046011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 341285800 1250 341284550 341284577
    0x200d12020a020307120506010e1603021b10090201110f03090603150d03050d06061d100210060905090606040b330d051905071d1825050306010c03 64
    0x3004600c0120b42e00809481003903880741e0700c1c250700c0701c00ca1900303992620540d000000c112006810990040742a540300100a0030000b01c241e0180d0301c40e501e107003000603244200b1200000240883c0c042c03200c0011000c96251098000180a1048030141001941043c1c490002d84c02000048900a0380c06440c415202d6a48545809548a08401d916044040e0b41c0c1d4a0f0109035202005080b683c5200740200000b98550a0450b00d403000041d1960f000e51102c0f0031491203140206440c0301c6c400c218412035085001605100e13050b02c074640e0006041c592120140412010103000043d4061010780d820031500700c00710000f40d9041030740344015104000c8405107a0a5003400361006400c040f411b5031080d510464013542500803d0b04072041031303d69254007281c1d88203e1250003214003e4000755905204e602071803841036052103440b80e540781e0007480c41502c88210b00007406001d00c110720245142d209a611405104140c201101d40201007140c1002017048680c0c211600442071509868070021040d100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 341287050 1250 341285800 341285803
    0xa020d080f0c030d0e0a0b04020d060e012d0b0105030c16050604150c0e010e270103060603020315040f061a03120d1a031b0102101503200d1202 63
    0x1400441000048000b52100800c04000018101d4000f030704030420031480e80c2071125481d102600402803070640007078003141c058074090040e015214010b110016910360040c1c8010300310303081004481c40b4032010060301000c09088681c1800815070351101403007404855800245030344002803000c4240741c0c002c5440041d80f040e01c800d030307204194071004441c507030f050605084c00740b001894400c2e5115400c0588001c0904e1003400751000000301038607007180e0391440c18200b0840010301d071503030821401c1c0001661014504e80005034002c60186600151090640c0181400c088821007074182c0e1082c003c091100040c1031440100754150091400140c040022401880c090000c1c4c200b00d07894800c000c40108000d201da80241001c14506404009080201030394140c240545000c055042d0001501701c120b13100d03042d80d06483c0c0031b41407040c2d0342c1c0c41410b607000008888030b030800003584001080c0305004000c21b00d40d07418010801c1c030655501c900704540000c0e40d02d1182d2000140402c05248100060900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 341288300 1250 341287050 341287057
    0xf0e1003080d0501091802010206160c2108090d050702040f0b10270302030c04090302010605180a0c090302030a0f02010516060515040e0307061a090c0c0c040209030a020d08 76
    0x1032020001d55198641124078010303003403e0041d01d0a1514100d64542d0116114180320001c59040e0050180b81d03480310b400f02d62142491100d502480322003e01200001d04d04488201c076120012114405c0240808004028200080902e00300f94001800300105d150002b080d00c1c03404da0304480220321018000440c40c05000e581030340e00e40040d41c844010580e50341181c0c001c20318034408518042c6c801990000781801750796911000e501a04028581421810580c0140418234000d000203c1d0181c1d4500c01309022200030040515106030318021f100b0f204811307015100c0e480b0020b103040704409085030002a2112000701d0024800d210000742d031011640200165561005001e42c102c3d0031394001c0c201800609000c49910030190140340851010b0b10b0144035442540183d01c0c019410980e681d925000144404c4428904482e9100c41003400c81d500e807170703425101d000e0318003140d80c41d2041d25101501d048280844540300300c2c0180905051601d0020f11030301c03000d804a404010042060425000611 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 341289550 1250 341288300 341288303
    0x10c0c1203120f05071d0d03050309120406050703020114100b070c08010e0c0414010b1e07061a0103150302130c03060306020c06011e030206030a0c050c0d090f0603060f0e1003 77
    0x78103003002c403d6003030305035800148100c004c0e89481c400e41c11005152207030341032181b041952003640108200b020902c10405550711210f158102d540c4031107020a000c0441d0015409200002c40c00201c203000c040d421f0107280d002200703820f101501c030308124014000c1089603000707900301c802c00400c418060140f202200b200518a5800820042080b40e045688445403000c000380150b0801e1500181c4041c180c01070b40c12900c69900041c05d02c00912041000c3e809405007a0049000078401a000b0640781c2c4036010b0f808a540018140c0c5011050000d030540c0c11000603502052034503170040025855490410342c0c013a0f8040e00001c0c0c06440058180d008104582001d403a9510100b141d0311210000500c684c140c90a00c0039244100181e041d26480d170720b846004c000d4014106002050441d02c090b084282d07110a9402d28a05010802d81100e140c403100b4080840002d60600040154082550a000c0a00400d103070501006040c406541907810b030610594202489140000301c0c20038a0366101c20145 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 341290800 1250 341289550 341289587
    0xe24090c0a11071809020a1503021b0a02210708100e060606031e060607020d150e011a1002030906040303090e010b0406020a03080c090307090207050606010c0c1203 72
    0x9052000355150107410000180001c15061122605162000a1000219000c03403004202103820342c4040d2010b040c10003422a04005c09170320105590307241104451114540d5640180c8446540c0000307401ba0210400040c6e080e0846039104003d03071240c5444000040d250403103c2e40300070400400903c0c140c419807000a050084900700c003260b00c010b80000208a25420480d801e40c1ca0752410854103110640d841ca04d580400214444508010705010703500c140002c2880742400415008a1a816484141100c00c5400002142d60940c85c2e44914480f4886c0c1d44020445840c0c0d140200c0c0030054a404c9082c4690034050004034200e200f042291701051000d40ba6a0300e0380d6407894054250744c1e540c040c03041c058070b100e030002c245480c4080c15502112401d600401c0c0a980075141510052009060358071980d004001c42c3d1280d44003001a80e005002043c0c00680d00e2010b414031a080c08400742c2014100b002051b410b0740441c04800725135040d82c00e504141300f410361b201c0c98151424401d55102000c00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 341292050 1250 341290800 341290819
    0xd0e0a0506070212070b1204020a17060a0e0304171615090302091504021c0b03030717090d0804060908122a0c041401080c010327080421031202040e24 66
    0x484a82032032807070259100752b5000c28404d072580c00042030702c07a4140c0c07030380590351102000507407031095600310a1040903441c06580c64692202e8800d10742602c80e0341041ca80e43d100c0882074503e00c2c0c000c803540c401400100e21048209110740c00040c0600c840c3d02c0085d124100e00b101080414141c208036000001d801041159240c80f6140b10f484165452503525896a2900d0205551418003000311a081e5030700038801000c14140c17440c1d040d03568100c15203d030742000c155074107940010410030040016100035103070b12990f41c2c0740204039407500d110400201418070080c0002c0fa0803d02c609541400107600f0b41c510000d500048807501c0c80c090308000400e9000781000350072400f1048401e01d2a050359550b10544110ba06540d00642c01c4d5400300348803a442b807a03800700c62148282600c2d0003040030b9100c0e1b01c0c6c0c0ba1a05a032160000c035080d903140c00c11b21091103c4c2c0003031000c0541000010501c6444807800b035040c03c0c0303801089002500014001c540f0000e142102c481c0401d020f5202c8603004100a02c035010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 341293300 1250 341292050 341292067
    0x10605040510330c03030e0a0302010608070b04180c0513092a091a07050703080a0f020d02030915041805190e070302060c0a050f0d0e0a0506070212070b 67
    0x2454280c070303c80c203004425200d2240e555003000c01a001c00ca081100e1801800c02d403240000c84461840302400d50815942d00e00d88695418180311385000303a8000c0d40080754017030521900c5418041c040d40514102842008100078000d04500b8450014152050004042c54442c2054a2030700c10351004404400200001160002c41c85d441001d541d40500b00702803c2041c40d801024410291207840c0011070b0803000100407a540400346c2d81882c8a40301c9807141025802e581d80c0d46082402d40040302d10102c08101c1a404c0344c4d0007236a240702c21407144014014171555580c060b44a00c0764041c8a03000b0384402100010309010308003100c0052020b42466034202410705490401000117503010a0381c02c0c00b22041c58003803911402403139000c0c001c6c0d20190803500d18650811101b9030000caa802c5450240c50881008141c00b8040d104569084101804c103c10034203100520401d03e0754100c0d031040c0210781c418081915000d042c0c0b80625815540480011408142d4510b400e08941c848022080e00044441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 341294550 1250 341293300 341293321
    0x10140613020405090a14011520010b040c0507050d0503070906320d050703052202030c0405040c0e06060310090207050a050601080a0c12050a03080a0204050306010e01081e030a110106050405 83
    0x500c10070b01b840103a000741e600d410212242800c102c028000240e10480400d070000d40944500c00500d05450000403d008080c0204042d9200b4010f560081040802c550342803080038800130340421b02c0da18105145240ca24005003100680d400760008000b50104c0c003103074020f506030001d841400c0040d103c1c03040485410451045512022003030000d1424080400c0805001e402004c0c040d04000c00c0d06170151007102c030403c02003d83c000d01130380d0612500c8105210343c1c0f200e20030035001d2405040c80c80310413401c00c80b040440701c60192015000311010000c102200c481c009604080c1c40c1c0000c00584e927090795042071480c1010004016115014800000520762030026024816920460052000e1039640408109020710320790090999004245a000083d03ca4108290300c0603080c08010b0405031550003013468204240c00551882480d08014818200d00304a9000000d047c9200009125103140546440b8007808040d80c041c01a10004203410310f40a4004030042d04000d0810842454003078440c1c2d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 341295800 1250 341294550 341294561
    0x10b1e3c041518061b110a0b07050d0c03051206011106070503061903050307230703060f0b040b031b0103110c01090614151e031e10140613020405090a 66
    0x803004550030520b44a00303042c0c0707603808074200c030043e17100d840d0700b8424900188020050034104071081e800c0840d20016581d07034914124040c1034113505064448020b850521b1410080b0180f64044c0404040d00c880001c3e40102242c0442600445139042c2e502c0d81e0300180d401e407400390754046e014094002080341d040c1c0e020340a544604011941030b980060410342c00c140400081c00080d109401c200440d00c00308a44d01c07a07200307030441e580400e55200700c04214414100510394200300e60498a0701031700541603116014101c548081240c003000608204000a680d8804201ca0842d0304216801f2010050780240d1100c02107544044485030303a44500901d5900920380d01400301c5410303142421030701e49419040c1501e4440d81c5401111a400302461003080610090307404103103150300d40500304d030101e03032024090300f07041142a49085065580c4039118a08181e5050100d80d045881c1c40c03441500303c1e0740340d481070b604500280e07482c0307048941c0601040c02a1003a50001a042000201800340c0d0284641c4007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 341297050 1250 341295800 341295839
    0x20f0711031e07090218060409060504050c04290d0c03090c080a08030114061603080402011e020c01081e0c03040302160e04030315030b010b1e3c04 65
    0x142d48408100d1101da032581c03025940340d240300307500c0900300707100300c6100c1d50061489224010000b01d0720041040024825842030f0403004069807540c1c030400490070b0600599800805907a2035a08080c00c02a807141400751102410318840243c0140d000389519003021a4104103190600703000c001000030026018007482c107801c45031020840000109943c0200d031000700311340d200410510f56480e102e02100100c0c03000b1046a4450700420921080b48400d903e01c0702d50b43d00c43c5e05e4030a054549400050856030740e100e6041d21111002c0c2e14403011aa003c55021094082424000d040d40c03127090600604040b503800c2818030707030840c0d03061000610011001d076104901c20740c219031103404104802000e4071054800d52240c11002d4010400180c06a0450496030504145c0e4088031070b40d07511142c903c0c841c203901120514100061402c02610700c220800030200d0340c80101484c180707000c0064521803c11000282e28101e907044c151b0a14090320b0003411500100d011b1307060701e503612038800e03002d40303180c5484 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 341298300 1250 341297050 341297053
    0x50108010902030402010512090c030a11010e180a11071a040b180c01080408072f0402160f051204140f010201050613022109010b0108060102031204080706020f071103 73
    0x35481440d0b00880b03110b6941a9142810300242402d4120705e50300280401070180180c24541d141d540782007101d12800d074001c50600180815110016002c080c1040403a4000e40758005c15102a500b01c1c80069040251004009902203680401c0401c5000303071700d001800c05a00d4440b005001c05059010360190740501c4540c842500c56100075410a85601d0350b031881034001891815503503001755140e07540302e030007090850f2414805130b4548001e900f00c0705a031001e180181e0311360041d10380307140302100b58000c09681c110300d00000360008041d04482e62000900740c4100c003e05200300031041c404e82000b95080d810b0103443e16107447d0144140707502c16800c0d501400305401c01c000c181d8814040d240c000e94005d40b031902540d184a403048042d500110038030b00e48440802e070040c0404181e07001288242e440600000750940701e41c000414a02c8050611811540180f24192000191015050b04543d000c003503542c3d0740800e031502c1000707070050750130140321403401141c50018080305024013282c40c6411030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 341299550 1250 341298300 341298317
    0x1503070801060c122010060305060603070324060b040f0518070c0b070302041203180b0406050a050d0902090f04050d02010e2a0d080c01060e011a161b0501 68
    0xc00c101c90b9203050766030162a403100000c0c40c0071494050a2a0f800c1041d90614049100b45c00d0004240781c80e011200d54004e1a50345c010800034803206003c3e950b00000c044000e46a4186581c94001c0e02002d0100b412500030941014011300240c10303807000000f001010003030b680300d0750f0340e00c0d80c130803450303207070700c10240a40d5a400340d11410401d0704080c04d204040645802c080400300d9115100f040f00001c0c148024164200b0010800044624907014114840c1c0d980003014140200f00301003060b000d900020002c0000d200500800e500300040e00d181452600c1d110b604d0b10381101c000c1e0060640d8040181d042001642800200c0d1f0b000950700d442140110220f961081c0485800c0f03080f520755000c588078542114040703c18828a079002440c244004030a14114103003050000360840300c0071402142c50070800903158030841001e019042c010140750108421540c03501a280860340010800b4064561001a605a1105511092850180d0452505502e030702c41c2e030030801c02c00461402264082984007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 341300800 1250 341299550 341299559
    0x5190b1c050d02060601140f0a2706200c190906060c05010c0f0207050f0d0b0c07020102150402100c05100903020c040605031b09040c0801090302070510081b13051503070801 76
    0x80e4994030395450710514591800c2148c81c20100d003a000000032000b001940c60400b10b0102da07454044c418440c0c0ba95001c00140c2c50240041c00300703180085840042403014807082c400100102d2840c3d6048005d0300c0042050f230070503001c41c85441498026100c050f140207004201c05030b010740001c00d00c80c401d1008221441012400b0f54903202a140324400680c000c034414401810480c03c0b405d1081c001624040300b14540d031362402d141318000c48102030000310101e042c1c0f0030b541c0c1c1080441c0c09507250701554841418560089180c801c0307001188000e103c0c0f14038050003002070411100c3c0201c0100c2d8000c010360041450000e440d04488030096216505080c0003045500e400301d981600c1c16040030f8420854441c00051000b40d03c8010b00c140c8984408602c0000e10b00f1081c0204070440b41f0039070107400c9041c02c010802c0b00d1482c0f02c0001004100340f110822524106c6803064080c61250005503d803540d01c0ca6150625250755908640e4008440c15001d0311286d41d014042c5014908030303110007045a0703c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 341302050 1250 341300800 341300807
    0xd0504031e02011a040e030c011a0109120f03181706070f0207080a12051306050301090c08091b0a0b0a031401091107030c020112061202090a05190b1c050d02060601 72
    0x8900c1c3c2444d140c1c40c49070220216140c9584410411842e440a0342e003410307100303115142120f50100d0a4140000c0460040200f50780c486c1400024210440d441000a00d540c3c9813003d62604818009043c01090148c03140410100741d07032100104200d0a0407002c0001004000d5150780c1c0030f40f80d010110700304c82c1c0c021803280d001145540071344015400030504502c1c95162a0007551072a0160303130900104104010290426005a00c0544040d890f0290740e540f40c41540d01c201d80d20480d502081004460a2280011011641c49604078458040a00e6114a00001043d4030000d41c0200886600024030400c0310b9016085008540d240020550140c0c2c0d031045031b001a51000342c04d1700b000280c20426100004d00550070807561314018908100782025072000d080c00c846007a004820718102071000c0408615148081c40e9210303003541400d00150805070009024103224202d8181007a446414040e10f9858000d02c501440002c070348a102805050b0a1251725900c8802d90720006010300c01c00034019501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 341303300 1250 341302050 341302061
    0x9020f04020910050f040e010e1005041401030809040e1e0601080a020303040302010c0c05032e060b0301210b160906050909072f061005120316080d0504031e0201 71
    0xb000342c043c0010344058881120b9540c0004031210b406072007070001049603590341131254040e004140024009084c1004400315a0324154030440c030417424212a12090191940d5440c116944901d4254440385a600082c0c050b09001c81000d04074461720106041840c00c018000144200c900300340c070481c1e40c072204695103a407424070300690150300c100020001541314100d0244107034000d450703805e0b9281e241c1c1c000038107080502d28044000c0201034120310b124401343c201045101c1e184181002aa4546020000b850005100b005240a402184912420081c890540d0320079844041c80c0e0382480d00c450041d0b2001030031155400081c5030f091002c103007a40640d04840c40d94800500e80b540310f5a4180e8126a405900c1c0c200e00d11801d8030b281d10611085020004088400342200948102d25148071115224101980001d2041b140c41d0102800d0350404003c50314030518200d8146490106e03400c09100c51b104d01d45541c0040c0e850302c400c01c41496800300101c10803140414030f050003444070250032804e0701c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 341304550 1250 341303300 341303317
    0x5101706130803071806021f020901020703020609031002130819030e040c0908030309060f160c0605070c0c0e0702100c080f04050c0a06110607140301090b0f090a09020f0402 76
    0x1582141d454000c900c0c00400707158007850ba45441c00c1240b100703c10181c00c0049a034840c0b00980d010b01942650102c440000102e070000c0e001045080c5803c150000b075451503603110103030040d40f0007d10301c10647c80620502c2441c14035402d080d983c41c225800c2e10200055903105401460107205103000d91200c02c0058010750340d0b01503a40d8041d42b4802d004100003018540103120900a5803007002880d030701d040c000b031407103482214090907561524100c40c1a00d4880103002020701c040408094404641003c281c24002e90021400100ca80d40c000b001e07102a03406420190030f01902104c0043c60500090180784105000d0342600c3d8100700108000d01510000700d0303854003003076803100010a00c5031401d4801b9803081c016001c44100d00f800d000880d141d806903800c01c00000f860b80302c1461080c50104400c0e6009007441c42c100240030300c00407280101b400103005943c0c0f107607100c031549070440d07561910300159408001c0000c0c00c503080146001300200401e42049014175042484c070720781407070b080c401d032192074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 341305800 1250 341304550 341304571
    0x9020903120f041a0703030e010b03070e0a0f0e0f07090501030305120402041e0f05130f14070f0f1e050a090c050c0a050606011709071202030c030105101706 69
    0x240c5860507810501e401004604100140500c0700140c040040c07a4040c01011540b000359a0324461400e00038180d61a002c2c103244181c0c180640d0003402e4030006481001c441070009409807584801c40c0c060054a42c03581d101540604140500d403144001040e18000c80640a0440d0085552800c4840c1561001d20014001c1607040c408214003c2404c4400e40d803251000384009800051041040d1450f2147c054904941e0f5540c0d082084010f1701d4416160006070042810011405680e47c4821500d0005801403440440d00f1020300e5402081240c6000382101a4401c00002e403190340b000b601e800c25100e40c2d07482c1c1c5214200340407a045008021400e039600a402c0e14004c030309141c100c40c05091441c01080c1004402c1222410410050001900640c8500003800c50341c10004001440202c0181000f0340d005580d4051200c9034800182c03040440c1c085891640310016a40002410100c0302e08665406500380005c000305010240c1046055940103c400d0390a01c0700c00c0d02c0c0907601e040460700310041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 341307050 1250 341305800 341305813
    0x301170d0c08070219090e0d0206090a020415170319050c0d0e1306030506090705010206100e1e0907180e030f1b0304090f050a0207030f08061201020c031309020903 72
    0xc5100100105100d40c0050710170040700e00020801d4401460700c0e030040100c2a540d802c1c07080020001d202ca00e00c901e4080c8000d00850a0801c4600e445061407840244250350351510700a100364120030b81802007141282c248202d10495038155104d502c5a401c2e0340711980081c41c085c0800d406403080c0c500d20314242009000e032000010069403484400504550b0104000c2d45688107814640910005544110003510311410a03e94031890448148c2210741990000b804114000c0e508980942c1198888000401c40c0d85580200023848200c1c0000848143d8000c0c003008413007900094401c04550700800c900d00300c884207080d8a41203c9034096618407039081081092074210380c15001c4d14005400601c0ca44014100c50314040c03840d8050b0380242c001c02e888074038150340282284205a4040c0d0030324810b6140112aa500400064000050905101d580c0d0041020380c1c40740c18403442d4400641e40215603941460260395a02d802044840c0c60031800d28074085140c4103507009956650202034010400d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 341308300 1250 341307050 341307053
    0x8060a050a0b1b01061208040305100501380c0607080105010e01200705030703030906080a0b0d020108040516140a29031e1905060405220501020d0905030301170d0c 72
    0x2039410f01d61003914540d00c1e070402080c150109104036910b42d101e410748603521803952414505004d048103603403074440d281000402a260301d51038a662040399449a1164001a621581c41c100101100404400401003904202d0800009255000c0c1d042c0791070f803c1150b82d0355001102c90148210249002032445480c001000ca0050310a881040d110404c0c2e86515480b1400f103450203a41d6031040e0009540c250041261030b421034a030b04d810001401d4240110401d000102d124036011483c005e0404c440680041d05116092040100812903110322040242d96080c404400c0e05040d102d0703e204010030000007425080e500c0061280358202e00d030b000c00114454072039481c940c1005141042003000b512000003000060b0603000c0c8200c04180d40e1482c1c8000e141100402c440c4014080c5018500d0007040c040c8060342c1d10080d44170b101248081e00404046850601d0281c0210390510030403034100002d00c07040080201c0918140d41010840e0061000c0c2105144d640710454641b26000c2803031302070001c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 341309550 1250 341308300 341308327
    0x1401050f0f010e090a1401062d0c0204050c040503010e0604051c1e12110703020a020618040e0a020f0a0e011e17070f060509061b0a0b0708060a050a0b 66
    0x41c0c00c4014145002208005004074007001070884800c0d4070705590b020103580d94188070310110302401741480c2001042c0400c3c0080341e0040c3d041c3d051501200003152800c21050322860030015800d502034414800d03400d002c0b500f04602e8005000d0304c0d11a5003000c02c0d01c1c2000000190300c40c03007280c014008191402d0020020750042d4080c00c000341c1081207111100c00042c4203400165992003a81c0e5034a400c003d0203044031012209141405503040c18100300c8400401c1d030003c3c1c4441800c0e0102c1e1784039078410004216280760710880700c1c0c140d000f81c20048002c10a1001080b80d44945009a640980136101c032020405d07490014010520744400c07290042c8040c9000700200d038501280c0e105100c00741600c6020700c01c28410140304219482d4015001413011a01407411040244101d0500d14105440d45000840a00440e24143c2a02c0348456000391b900c40e0070006107070803030340041ea1820b141c00c000b030b030007401c110084030098003400070380303d000500c4e080c040f03500c0701120a02905141450440315841 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 341310800 1250 341309550 341309569
    0x3010e161211030a080919180507020c1201090204050f06090c071106030108160b0c21040e01121b150806010e0a06050403150b0102190303020c0a14011401050f 70
    0xa56070301c101e00d4203600040d14104907480504c1d0261000d55162444641000380c40001072044605940301e451040007000e05d0020b20400241152001080d90340d22458200d2030091154800c50303004c0341030340010084c10019804501040d0082d141808165100c82c00246085404d80791680c01044040004484490035005010003902c900003a043c1140310070300007803940d0070a81100103075030010740c46044401d0300100c0c8070000b4240d00c1011130070020300700c8002d030b22654514601800c41c4582070f410b2580c6551802160058682000068010350311a801c44180c10762061040741c406000f00c1080e403504a060444c513045074440c0307000050035554514111801e030030151043e4103104507151001d5140e81c0b1081400081d0415568094903036140d4100754005504042d80c00d030f0180c0c50410700b081281d03408240c0d50b84040040000c00c0c0c00703d41e03600d0114020301c00c61b082c4d40410700900b00e07200100300e06400545c151003a0341c0000c0c0040d14402e80b41caa0890f00a104e85503200c514003071404810304181000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 341312050 1250 341310800 341310803
    0x90102040306020f09030d032a0e10031415030a0312021306030506010212030405060414030c03030115030605060327010213090510060f0f0503151201090203010e1612 73
    0x140c141541d980d10081660000302699040f200c01064021041c182081801c28928042c6024400c41c210002c000700180003051031200f41a000c0900300c410035001d40c0f03c10b42c680e003020b044a0900052240300030018056002c0010711040031b000400c01072290055540a02207004000e00504a03c540d0181d880d01e00ca940840000c68080c0003e40190f02c4826049000306196200440d051510500081c2010495038408c5402c2ca0103105000100b0350020b5502da002d070303220103c4080c2103d01c3c0300c000c5c40d5001e042c03407030030303107884000008038078100c5606000e20410342c1030300e0078411162280300300900d030f0104954034007903505101c07519210881f820b4154807800d4400c1000514040641e40c0341300800c0c8242e006464402c0c0c4840903c010b6840d0b58080c0c20080005203449080031804102c001c03ca864825000800c114000c8040b4003c0034004000540d003080c010500104c511990a02c60b01900c4610070580c230951070701000c27103000b00d40403510f0f064500c1450860100f8506043c10100303103401a400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 341313300 1250 341312050 341312053
    0x4022724120a091401050708130c0e061206090a1b060509040f0b06070323030601021002031009140907060f02100e010204030501090b0114010f0e01030207020f090705071b140909 78
    0x1c040031550340080d2000784c00b075500002c581c9203011007001e80345840c09400031884c4010a0703203102c08641c030308190b0790a85141000300200b5855090000d1024175520700942c010b4040c1505102e032040700050800c8055224115070b80c45114031003c80d440301c0946210f00303408140100300c00a060f1405900c90b041c4000c1c2c41300005501400300002c00c29903002040100c0100e03000300ea00054150642e018003d00d00b60840050380703103160030f000007516688446054044540c0120214007810310114001001e00460300e03041012790700c01900c25180381c001381c80c1d0409030b0241e4100400d506102d185110940e90b4960024944002c0480300100280a00210070305039540c02d00010000a42c21300800c5a814012038122185505001003603030600c044010b52414040c03a40d00403440980c00c000c010311550301c00d080040e15816180085082e0381e40401650307600400a00411420a03040005045006d002d144070180d915070704503a40740d00204901a45504c0c042e140c0301030042d841c023104140c2c0e00c151042c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 341314550 1250 341313300 341313311
    0xe0907020a200103050c0f040501050a1b06090b100819051c0c02031b010c140115060f090503011103010506130816030308060306060d06020904022724120a 68
    0x8503015a0b66941d440d1400b12020085000c00a543c1c2c14040e064120019448562401e100c4080e101180e00c00d510405040c0030000c03944100d518000c608011400c0315016900d680e56801d480e000d4010010f802c0c0480b14242440041801ca00c9003048040c20748035044002d11012400a0100942d800a0740c4201d0702446a840b05500b000084803400d0a0402c0c1034640340507481d8284100750820350aa50340c0d204551b00240940c1c450380e4000040c40c20b064014840c01031340141904210301421440c40c82031802849400c001030510b5200d0303400008428182d40780004652200700301400e071818008110302c5948103000621240c54007000520714983d02000100d00c0c1680c403d41d0780e04085c00400b0807029808014410000d050b0000901681301d002100036000794509000010046101640041d00059001c40d405002e0b4555074111030b800340e00120445e202e5183c041d400310301c8030010700c0158003581d068507a41c0300c8c1c8400036480910844540980c1d6080c034200c252660b440c3c20b0b0042c011021151240c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 341315800 1250 341314550 341314553
    0x1a060d020f060912070e070807020d0f050705061608010807120602031e070e010305010902120414031309051815041b0b0a05032406040b030405011424010f0e0907020a 73
    0x85001c131040c4425000608046440c0c8003d01039001c2c0024411028440b5602c00c0141060740464900c416150301d0404c441d44c0110b84904848600503603400800900c140303014480d16045000e400c00408010b6542d4103503030ba0725a17440701c0e1900c805201e1442c4010989441074002251a0055540000300f60160b840241c00611000800c501c05e0b80d1020208000707095044040d6814025a0301501c41c1d08030641c07825851001c4079441d084c001b44054403100310201d4003d0502d6042c0700721403180d035490394182c2800e52111000401003405a030941d09c548009000c0006a08000c58061081015040381170041d6545488110500119942015a502d0001404181c024140b40901141121a82c46640320729200d101e612200081c215104204901501d409440759100c0040b2000d90340300d20302d41d41d104d40b564503109000d072001d030202e805e8800100d410054004504842d08818040301010324403803030766050041d51041c922103c20b10001d2454800b6074602c0c00c0105203c1d41040e8a07104440780102103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 341317050 1250 341315800 341315809
    0x10516020607140d05180f031218040e010b09270307080d0507090803041203031407031b0503010609090504030c0b040506010f1a030a0e030c0102040b071a060d020f0609 74
    0x9900701c41001d10204086010030701001130070701010b183e080c410310f0220704a91840f104030140400c940b2079002e288080c011602c05002d070060004200032042d84840c4428240c8800c00c0c0746000c018002ca00d804103120720490140210400c021000c1c20481050311520003219101e043d81042ca5401285141b420351364103002c0004000e1180154a45520380540d0702d104003c0d518040c02c42010819601414081c031140070044904407148500180800754152030103a018001c0f4030448401c0700b0313040c020461501d8041e0401c89952450b0340310071841e240c7e907180640d1503000a016802c0001c14600c424400304481c1ea010b142c00030b00a0800e020a45010782c1c0e19840c48100720340c2181c041d0007130001081111401900072020380654141d1002e42103ca03041504036000042441065907100c000100f4214028005c54100140030002556500d1310782d804841142c1c080c903c100d885007600ba103e400306000c0c0c540c0150046000400203240380d1000d40811042544901c100c2d42e100c00c1c10071100415640703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 341318300 1250 341317050 341317057
    0x103230109051012020306190e01060b0a022811041806090b0a06030b0408031005030607080405060c030408090409050102041809060507030b0603041e060f052a04050105160206 77
    0x1d1240800d5520306100d22420740d86460744030400c0c1000e1040c1000041e039010404680c001d070b01d0081d61402e4a4422914000b0b0207803240301034211351800304086240780c0403a0041102503060380031101245484803007060025480b1901921905c0306c07290000006840e40c41895619000510100348103252048224220b104a81c0403104a513461844800b0410540c2c025a40806541003c2180701e10b140c55810391880001c00040c4030183c000002424070040088103005420b014007218858a880d03803002c0c002003000e607010b41e041d01c54900042c45040c03140049070f10466209000394102950801400301a1404100840f010754081c4404181042140300e40d0b0360300c030000036010131414600d0402000f2200f02074020001c16040107003030300168070782c41c0417203410540c000d1440d00380030102c4084000341e1207200c40060070b90303041080e02d010074680768100d0f90203901c000038503550341407581c00ca240300c0c0c02d15481d80104545040c0410440c43d07028038090003400da422144005c44a2540d8001101c035070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 341319550 1250 341318300 341318309
    0x20d110310020414040f050105100e031204060f110105070f3207031106040f120c0b0a141005030d030f0e03130f1403060a0908070b01091a1e01032301 66
    0x11303420020710252a26001c3c1001818804104001550401011035102407891022000740b0008015000032a10100308008408035401c090980f526240c5000500a03c0b81c2120f400015180e41884c541c2c100061150900402e01512407050b05e85441500750781a42000401c5031000c51140702e40702c0401d00c4441c0446010b20001111a1361300c1151502821110101d102660b040d0321003170030040014040c0c000c0c5030b140340d004098151040300d216006c440994144c080104189251014864000885d03040810070048a18000c1182d90340c10703542498000c40b51041560681c010003084481c14040c1e80105144140103001003050160b418803d4a507900808900704080c442c1c6100b00104221250100702400302c422911a200c151000000d6032031601030f00d60b040040c0da61101c0010854020700b190181030b40072900d030005695079a8145c1c0240806400c241c1c818004d0860528586400c3c0300482c9082803a5251140204810b401100186a010080c0c02403204002c5402d01000c01c540c0024001c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 341320800 1250 341319550 341319569
    0x9031204050c12011503030c0c0f0f1412100507020a050303043e1e09090615010c03051207050f0403082206020c04091707082203020d1103100204 64
    0x4003804010f020074104000324046140e45011110843c4803a00f40d04001142d4151074090507550007800c107414890000e0740504c6103048445000610084800903241c1280c01c1000340440780c0c1707180824400d80c45540404518035030000b04002094001640c040d94100945104a4100c04100d5441341e140d5401500d040d280da41c040700300c522220390f40c140110959194500c0d5900844110a803080c070201d018110345214070740c0200104800310308082c000701e140700f000780003207034505100311400d460f5201660542030041c20041d0046d07803540641c80042240342d156403401d00e89450012030031f00610001c0c0101c402c02c6810080f025002c09440050406140076801460f41ca00961160342900c164000c8010582c81d8210420401d450700490302c00384240c02503030f0220300414503103840c91401944a0001d181c0c0034020850320284031011024295040e00c0d240700547c540840d08005001c030b41184402903201c4d40b503003a07010000c0c0c00030340800412240501141c1e0000c002c3c80c01034059801582040c00136 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 341322050 1250 341320800 341320813
    0x301020d0b0301060f060903240203010902090909030a0c060e0a0209090601080c0a0e280f540f0b07020d08220203100c030227180903120405 62
    0x242c0c40d0a04c40c983c010314010b0011302015245c4840644a800b003840042c16441c40641c0d03c09442e14100c0180c408021051070842d81da686070f0b000c110003034000d4180c01e4050071080001804d1035070000f044801340c803200d03143c0060024090703503201d01130411600c0e800200e01411362484010307292064600c0c01819000060001036040039285032a084c02403210600c40c84c0080400c00140c054000c50680117861203642c074010748854020354490042d00303ea004c3c0941d05d030040c070f40c41c81442d60744910a5a01c40810600702000c0151904c900101401007007081c031140200a000e6502d40e030441c01e14011300202d0f581d003040301180c03a406400b12100b401900d48002c19020003444503814003d0310703e0000c2d5420481c45600b0900d01e0b04142c091314900b401c0500080d45c0e078800555408100300d00b014480510107101d41104560000c02079007068491007401e0405602c0b5010785d02d44600d101c0c0303d05c6006042031011800d544a5861f2400014001411901082240c101803a00104440f4416401200102007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 341323300 1250 341322050 341322071
    0x17010303050714010209010c03110c03160f090908040b210f01090501080604050c010806130908040e010b040b0a0507030e0d111516080d020c060702010501051003020c06060409050c0301020d 83
    0x141800f001250300f403240d10402103240c00e60f801500c0303000000d8044c0780070b070b00c969250b00c04585800f030b10781c805c260316105241e00c3c000944400d4220200b964010000c034424070340c0c1c40b174401040d031b482100c0041a050003800140110b06803403000e0541510404e00340381c0081030700980a1881c01c404da0300b2546088090005108601c454024140184103060041c00a490941c42c0c607a10741c46407403511810000000e003c1007299488407400e204654903d10100085541d42c85c0c40c10081e400381c4607165101510b8000041c0b5114030750165800c132201e10b05454600b4a0000088869501c80807049017402000301a84000f5210410035403512845003e000f00c1c005100e40409c8204540d12340107010301c00b41040000459030154070028195075019840c25154000e86000074064062041812158403440c0c041204440d8150032540c1283c0b400e9030ba0905980d00b20a007201644079541c46104194400d902042080c242036003c450440c0c0901c00381c4200416200001e401ea0703202144160605880340c40010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 341324550 1250 341323300 341323313
    0x22e1a1009240e040c030e030f07020a06170414101d060a050603030405090406110a0f11030403030504231003151502120a0903051203041b06020601090903170103030507 74
    0x1050944500d40c90b0020740c400301801861506485001402591140b07030200301c0c58081d0b0800d0400035001400d480c0c0341c88445d40d0289139500000400e900c030700882903001945500401d0400920426084203ea0b10754594076020040310040c050840e65202d82000020784010500c5008003401551004100e880700c040809441c045001c1c1142402034544024042a9500042200c041782e400752400412603550782421002000d90a00469858000052241140b907011800310a0110262104101c0061042c030107962402135000c0140480e908210501c8400c241c1421040c900c0320582940c030246003c0b002092545c0081030741000480d881e110404210601c4848000261412510540140c9841d9074025617441402c83c009840d8a00003a040490a11a800c0074020f180c11200710b501e04070340f1840101e2980c4c01160155001f03040c00d0404c1c0803401c10300e01c0c0c0b0b0080f1072080c0c0c001c5c2a50390901d00e08000405040780d08800744400380042481d604051102d50780214041d40b540b0746c03a04410709144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 341325800 1250 341324550 341324579
    0x40612050610050d150b04090c080c090303040e04051c0201060510020c031002070206130609090b100c0b0a020705070909060608030309030f090f0d050d022e1a1009 72
    0x292046a03800849500b081c1d0000698900800f19080410110060031800380d244c91946c01111900b44005408209040250000007801c400c0744e84080045d5120790404c10306000d1f40700c074290f0540040004201400700e50041b540c01c00c2c0103005440462031045018561881d640c1301100c00360b51500020406490a1012100e1010300360002e0310000c014840029151107003011014202540842c00b5015501c41006076805074400444014940740c803804040c20171010f501c9280c5030f0609000651b07030701d81051a0f0420f064280c1e51651500701c0e100307a03035000003004001d06140c2e0281e400d20840003c50020001d19005007024080080c1caaa2142419015182d240c0c02010055004100b4000c0e0610000100c6880c0d0041074451078503141080300080500145100d0503a12070228a01141445808190308407590071603004c45101c48061820004250840c000f200706100d80c00200154810031034004900140340c5591050388000400002a8a02d440c00b0070600060352001c0d0900050b031000079070303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 341327050 1250 341325800 341325811
    0xd0203070c02031b030319110a03090e1003120e1513030210030608070b0a090905010b120105030610060e060702090702061024120f020a03090b010509090312070c020604061205 77
    0x19132602c618900483d54a1042184002c02c0401d24401001080d110304078505d41400d11405451004030281401483c11500d8080d8221a80d141400300c4c0400e80000b035000100c0c1e600907000b414000e04110151005402c4460103a00442d5040a240f0118020b0b030003407181460710b8609505a074198010300c4000b042e00c0420101f414600007003801000c00005000d0300302c542d901d080e1340e600d0f0f04402c0c2c100c800300300660215601c2030500b00081003065420003c0c04034501220844001c0d61b81e66010540d60380419074404078081e1301560103100c00380c81000305040309000a4142c0d07140c400365034041b5810900844842006070030500c18001c047c0a410349840007400c01d074907000c8207594010740c0300440704440354201c820b00002c9000141700901c250090790800004c88011902e40702c3c01400500580540c0808640412002c40041103a1402c241c0c0c160240e15000010742c1844000c0c200c0d0700a0203400350485060161000e107000050b651a4000c0016003404d035242e040b16041d504031041034600140c80c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 341328300 1250 341327050 341327083
    0x200f010b03190f051f050702011a0603060f01051204081b0604050c06030403030e07090501091805190f050a030509091e0c130801020c0f190b0105060f0d0203070c0203 73
    0x40414910480e0a00c82c0720007a00051010307807007222450b2161070082da83d04410810944203070751100c00700302a0320039440f42200d50001e01040121850500c9121104541c1613448601800414554100a500b02e01d1030503040c103015207840e90647c04012040e10445084460481c00a428442c000c101c00b400c02151520000401041c101556030381c0e243c1c4011680b0902a540200000d4140b51081c0c02c4134001c8080300c019101466125182c0401810342405400090750a00f000c40c01d02e00b04030b500d81e00000d03800101820903400805400041020444030603140d00340580341d0540414800d10121440a200b901c3d50742da42c03101c01d011300c52099001084c601807403084034003003101c8a99018403281d000308542452a40c070040b040f90507444000c203070002c00b001d61021803007940260b00081c4034800e2114140c1200c4c0542030005120311072140d0800d0040248680100410440c14400007900d044109650603504002e01c440148003203800854102000034000c0c0e00710015820280186a5030098551 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 341329550 1250 341328300 341328313
    0x80a020d090f121110080106020f12030a02030a02041a0301210f0308040305162603070c06020a020c2d0906010e060705120703020f0c01050a0e010c03200f010b03 71
    0x1a00880b10241902c2100d88216040208608000300081d40c0c007558040108901000c1d510840b008182c0d403024007650f0050312446001c00082c1c0000500010741c081c41d51612032450f600c2d00d1804000c1e42001e000c0414941c2c088c400401e200038101000304080b440441c3d11901ca6240008510b0924100c40401c0460068100d020001c290010040d07c8120342504103207003541c40b0b0345001c64003840740504c04061011820200000c000003808001c1660300740c26901d070326810542004154910096451402260381c284180000444940152090340f030b050064402103218000841c10a180181009220383c103104a000750842c198091400040416160b011251a0100c0040c040b0740b03041a03000d100307010200e184001c00c80100200301441c440804800e481d14114a8065501c40d5141e8011806010f551180e4a5552090042c1d880c0100c4039a500010008034a00543d0401038204c000c0c2c0400040009440c00000302c0c501e5080c08004200c01005403016803807081c3d08442541f20603a00c2504400e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 341330800 1250 341329550 341329559
    0xd0605280212010905130204021c0f0b0108180304080d0f020d02011a0103020f07080c030901082401120e011d0c0301140a0c0512040809010306050303070b04080a0203090d080a020d09 80
    0x451000e81502c9040302e000445e0f07142c242d0040001d04003036400943c4a0300004006400c07a070301c00310000d5200d06d41c00082c045884a003010505031010a040d9600140d0088002181c0300118a01c840f4040d001d541502d103001d40341c0e1007803810568030b078802c4c1c0082992400c102450503070402039040c003621103100030051030b00008a030590780a00320035003d04041d00403441d034032005001c100311031150b83d022113041e5882d006080f1180d10394200d1700101d4085000c0700d001075080c110900c200300c070410100010209a038100070054a00010300c014a511003540c2d0b42c02e1201000023403094142410310308940b16924000c00d641546014407001c03006000b81d050010b400c904520500c0740d19003003c0c20000200f1184010041201d0382e008888100003e80f074030700140018419194010405d041003a80d0a011842e12a4141079903840b604800074802040f210024011405000103444500014810740b8a021803900000b10754400d901e00036179031b035a0005050707062542c040100c0000c680c4030b42004522140790 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 341332050 1250 341330800 341330827
    0x20a050d0515100e04150509060f01030b10091a0901080c0a05041808030a05010503060f01230f0a0602030d0b0a1212030605120c0a081204140d06052802 67
    0xc440542030b48042d60004544485040308200e00a072040106601e114036040c02c02a1000b44c1084449044c40d00d82030116200300350124020b88a010b0009484078071307034030315520351202c0440104030581407100000085000107013401032614249400d41b162204118034010800d070341d0f006a00c9842990300240c3d556505485c1c0c48200401c99008440020340c901c0600110f01c46912001001010300800004000d16180c080d481103041e184142c1c01c0750010354038000840407824007030040003160030760124141200050300c20b00031208a000350a881d01c40c140f50300402c4081040381c0050380542c0011a241c10851558852240300c800304407a0031482c41d20f844140000825001c6001e03160404002c81569000d000b500140020b0801900402d0b0031840b00e440f094803000c100c002d1500c140c072100000240d82000041d40d0100c0740c60340c5021483d1601c1e00a030a8041c8a00c130050942080c0407040c94000b0414910843d880f6242010b00c107501980c00c040c1d110880d4940314131200c9040e00c148010f84001c881c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 341333300 1250 341332050 341332063
    0x5090601050f0607051203241c0b06300c04200d15090c0e01030908090d0c1703040e0106020a030f080903090d120201060518040b13060c0c020a050d05 66
    0xc00c0d03505540e6503284e0305000b414980c803490525003e50001041c080c04000401c08801125030003841002e02d034143e04104907100c000c140e80408031141c0840c1403004034200c400c031a43c00c0300004040c20f1202d5507e6000b9000e145800c95407100703920a110608111203400c0c041001e089000300c800b08007050700e4450b0600c20744010610310022503008141030404e29420380c011588440143d01c0c0c41d011a0744c070a9410044d00340c0e0005c3d14006034000d200c0d202d065000b0301031501e05981c080708003400d2440c40818802003101f00c0c4010307104a11042400103505207014801070728400010701a50b560f0b420b00c0b505e051400c02c1a801041150312488030000801c0c1e00410075110214180b410302501d4403a524464514081c51072016800026241d600d010000c2c89050b003800b802c4141c00074484940e0342d008101c004008409042440740c0a0400980010340030008030b9070212034030000307840e0134105440360021a59041c42032000325a2a100003419881d2040e1b4001c0249801c503400b00b03403461a0740e10340c2d0311400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 341334550 1250 341333300 341333329
    0x1b0708030106050705160b090a1e0902090a0f0906030c0503070612020315030d0903050f010e0307021528140703050a140912061b13060e0109030215030a0509060105 72
    0x2401044080801c001844200302c100440c6c0c0b007092400e40c80f40e1a541113984082d403910b100d040f88407000109480040300c00d000c40e1507000840d0310224500039010010b5441805959030040320020007140d801c07a1121440060581501c0000d6120b0640c9410a03a400e500e4018910942c0140d00801845034003001901c06014611009a1280c540c0d4009072108544000120780c14041c13881114502a8060217030130840c1d021b44101d950301c0c2c42802590303003211071103100380c40f06401c100491009410f01400341c2d135014200804c210714050f00d203c4040d0200c00700400fa4a40985605141002c0380da100c200c0002c1d40481c6c000707441c60f0400b955000f0b401c40c8602c1031080301340700c10710b001c8030402e9100c20103440d81b0150140c941d00e8100707880e4800c19294041107845511440302003c3e03801d2007007250002d94a41101565403481e210b07091000642d0400c140c0901d10303040200300e000100040e29180fa11410f0006c4a44080f07440b414150547c80c1586c100502d2114250b004600401160340d03104020f02c0c109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 341335800 1250 341334550 341334557
    0x2030f0a020f0405040e060703050105120a020409080904090c03200a03060b220906150b07080f0c0106060302180103050c030703020d02070c121a0403020d08070216030503031b0708030106 82
    0x100016481c0c031009010300c4e848250312030301e04490602200c10104842d4440d0ba02650700300066a250420081c41a43c14003000700194403100c100e01c0182069804007801d2402012090f00b04400100024191100ca5004503000e0007220810010005507840c0c01c1030003035401444620b00f4000b0004580074003194803001e012a520f8001010080e141da0351001c0040c41c0d4188405070003040007220381d01515001000b200c0c201d241a5010040070b8a5007e40c0003940c400710403842c07402c1d516032207140080e0844020024894820051098083ca003441003400402d025107004da01d4000602c4903a21804410500390b061600305410007a40c904210101c0e680640c007400c00503101d80b025a03d2800900603a107004011001402c1d01044a81503003142e003800500c2000100d503000100030205a08030030907500103015900c26980408041e01904202e644034440b48100d90454048411101440d8010745c410780b00e58000000380302d40c144404071304000d2010000c1c201490283d41d2303510521070b44014071411081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 341337050 1250 341335800 341335807
    0x51501290c06061e0d060518010501030203030a27030302070e0702030a0909020f040f030501060828030305180a0b01050411091e0103060803032e290c1f060902030f0a02 74
    0x130954101c1ca0310301d0b80040501102200403951906c00010542582c0d41800201d0404081d142c0780382c14020241600d9000d0055820151003540640d201440f890007510b180c80400010310b40010a40980030040d402030f802011854900300a41083d41c1000d4040021900100004210913412080f204102c480010740141e42c0e1943d04081e0409016036002003a10b00da410748000244101500101d0594166500b078030649082e800344517804140342c5182c07101e60300c200950b40011900039400103a21242c199182c3e202c2c40380888140d030910b1b150f254122046045900148551f003040d203e14000345000b0190345286c008080005865010039030880d4034450101e1005001591003504080c00800c1c22001b220340320304002c0d1b42c40d41c4600003d480610110307002450b00030301c204d40602000c100c0c1c4076013111000b200c0c968090402d880c00000662188020100304c65003014008109031110102d400203401120294050b0f47c0040d06c0c80c0c2d50050300814014001c0c080441c40e00903695800c008094801683c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 341338300 1250 341337050 341337079
    0x717060d080d110903070803090915150a0c140c03030d050604020706021303121403010504020c0a0c0f1806140d03180906052713051501290c0606 64
    0x45911400d5500d8500d00d0030540d2002007001042e001d0000c40c4c03001c40c19900200d4903615000c0e40c03402034450307141c0c0c8099254040307000b80c0e0b60b6203280941c10788090640d040300040c460f900f050983c40001e200000502d40c0091805004401d1000b4035040e040c40041d02200700d40d000000c2d901c1c010303501c898000c035940c0c501181103950340380d04980405a01c01015903d8821036081c5200c048075511040c1c62890000c03008114942c0b084071150705010b110021141141d00b0007050000a400c4102c0e8104c0324420444600041410304010a0042c15070405001300c803410700c00b205604040098010b180705003060000c4c407880c1100090101a0749003554541048091400d040380c06000c10750503c028501c0c880408114945590841025903000b07507070300101d860b0803281d280304020b16030414100350001240410742c161030008110300c0c0980104104c403d144542100054420800ea200e417901c40c1080d4036481021031010346045488510000c0c5a04105114184d0340d02d44100505051080e01c1c500040071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 341339550 1250 341338300 341338313
    0x522150e0102160e071103071709031e01020a121109010c03020304090603030f0e0f010e010806041401120506180c01050f070506100303020c10020c0d0204020408190b0717060d 77
    0xd00c00d001000a0310007169243c3c44c51525003810394508002615a4800140d101d000208680d403103540100100c004e81c51100c0310304402c4d0401e1700d14680c14040e0480e040745030790340388080711940d0030f81c4000141d840004550140c01030084111594130142010140a0034540c24015100e01c0747c803c4c28405094412440c040f406d51213140c03c01007100b0b1800a01009241c5d002d501e2044000440d2501811278040c00d0411000000d0030300600d0025203040101282944240492a080103001d04003145005016540581c802e02c241c00166040e52290308240034084d041041d5a0000f9400300311138846282c3c1090036440e081d114040038107011000800910312100c1c2e000b2075940a400c9000c1e1089410098105038403010548025070052003001080242444c3c108000540e240f1076800610319254000e081c40460400100182d0f40300c0e6080c400003075841c0080c042d0a030118040f50031f41c0c5c803800080c40c000d210349401070280300400c40c1e0f0710b02d59012940c0804140360800011200003074a06000c1c40c101c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 341340800 1250 341339550 341339563
    0x30206130b0d2304150e0309030f01091719080402030a0b0a0b010e030607051804090231020f0301030303020c0708070f0806090105100b0d0e0d0522150e0102 69
    0x25200044002210001201030358040094103400fa440301e00c10744000f50b03c80c00c507040182c0d03020b0000103603150520401030580d80050203905050003603038240030344840064141a800c407000110340c0d44858a003402c1090540340c03000c4610603400a141413031a84043c42c500c9081700440d540a1240080200301035590400c90740c0d614076840f002c1625540703452107400d4060f04640c030085002c29001c02c1142c689140c00b099252040c078440d6145800e02c034410240d03c3c089200344070700907003190759485500c0150300c4944e91034100e0900c180c440b44100c103c0c90000c0000b5140c42420048081c414080c5016004d150802c60341143e13098a0b0141c2c807070f15030715601030030041701c5d500024444c802c41f0b070001080d60700c5450344805c40d20640c0582d00d25a449416a900745c0c1c2c0c0890b5541d5041100d02c40c140040c1c070a040140c5068a1305131400240030550025203458268418100000302d0400b1402582c480c800c02682c040e404400303030540c224940790034003081c102507003020380400748503001d200081164401c1206 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 341342050 1250 341340800 341340809
    0x60f0706060f0504050618070e0f0301050702011b260717090d0f08100b071a010b0d0c0c0b0a321501080103170a050d090510060909080403020613 64
    0x42000d10303034032506450250302c2449254003076810000040c406140070b00030b0f2103aa0170160203041a03640c0350a000c951007644018440d9000c00c0703208081c45030351001d1183ca849000340350000102e0250500c1c1608000c2c4100d0005802c11010000782e000398111a03190a03039219514060300c40d903071526007041e9904002031600144018130794081000e00e05000400d15103410054036050f5401d54074000032225a0340c100c0c1d030200a07400074141080100d584000401d40e0318000e8900b0071801018288580d088007080e84420142640455085501369035407064044403034450030610f03501c01c519624514a001c00900e86c0300010350b81d500c0300b41d0001c4403056030000000381c5035865101410854480054130f4040d6040103004646c080c1d185440d5003c0d000b0103050301e410010200c000704400403d412241c0c0180300007030801c507040c480075400100710f024000300a40308030042c0402015600700f000450702c590740031013482c0d070034580c414001c1003da5080703a0960760103803134007a0364038560742031089805680e030321 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 341343300 1250 341342050 341342063
    0x160b060d050a11010e180601090f030c1824030302072c180304060201060906080105071215030c12020103050c04060905010e030c0a0314060106030b061c0e03040f0f090608030405060f07 81
    0x150500501b0801c1041c1d40302d100240c0303981c07580a8541d8404122141d071030200400d000c00e0350000b1700c00c4006c0111312840380a8003050218100501860710f40d0100034580d550f00310030890318804c2c01055014040300c0007400042911402250003030081800d0b003c0c40d000900d087c07044880102d01c403210444140060b00302408200d1340e8540c0c0c1d070003009008120900c02c2d001039514000001c0341c11038060140700d0207039003d55200c4103440b180326190710007840480c048140d821b1040b480000041c854410001c018030324070107860f520440b1400050b064400003401c044200004020911809400000c0300003a81c50a20f041c6004846a001181c0f825458003082680510980000810440b0303440d41c400000348641c080c1c50b02c0e40da8544040e03003917a01c004002580304d542070002411480040c0006c0707a9014124a0220f0781c0e1403155440380c2154800e0300403042c4001000c4007441040d0748480d1102c010100c0040070400185040d081c40d45a00550082030300c216000542007160820b00c1007601c81c9a40c0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 341344550 1250 341343300 341343319
    0x309091807091b110a050c0616061401080c041b211401180902060f0c0109060606020c041d10020c120a020d03052a0307110102160b060d050a11010e 65
    0x20103a051460460400013450000e040c54140f2804118880410340c80030042c0038064858081012a8010286240c9180d19115003a400304105c0d02440d0030148200421603510350400c0007460516480c00c2c001409241400300540804404100b03407002100580741507158650840d080d00c0807414a9113a14544030704140300210803d601b000750034103c50b54400440b07161001c050b440c2041d034040309806503001e1800c2c0100c01c44050654000c052001d62400000303441c007400d0380c0d8441101c0d0540c1164005030b100d50100881802c0510550b03045204c2e01035070107440300c00c90fa4960b42d152000701c2c80d403100a03004100701c001c6200c10059030030b1100010b44403a8586052100095503045500c00d02070003c0c3c2002d003c1403000e404181d1700311080b0903442c1040c820005040302541c10307038000f606000030064940c20000030708800384064002c552504010074000c0703010b424a0385c1002c0c1d000d803070300b48555a100c210f000002d0001503252840ca6206400170706019140e0700607200b10061000040e000080038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 341345800 1250 341344550 341344571
    0x7240e06090610120506070c030c021801090b0406050d020607020604081b030d0311070f150207031d011115040204140a0509010e0102032806050a030f14030909180709 73
    0x1094180c410010910900e524660740c201d6980300d8189804041c1c406d412000220740c400d40710f0408820a00e01a0078000794180103a404540441010f412031520711140304010312400c04c1e1400358840d080ca088034140101ca080c0000601003040e004002407203003034006140d004540320007042d10020200e401c2a2004541207420003400841d01141d101d203e40220a000d0208034028819403c0c0c084000301501d0a1034125590f1804441c0c3e03c40003a2035844203d401404004542d00003049054843d40e14840019101c1007034104c01841501154140461110384851801b03000410305100002c03503d10001513121030001c50010301d184a02101d07404031030702c104044a5202e401031801440c03004000c02801c1c0c420103017203080780000c0d00d8030341002d5000d5000c8004a04a082071503080307040d00e00001205070780d6000081d6071200c182d00450b500706044141d0750603c400307091020000803150000d1868224140001950010010203903000522002074441500700e0400c0210003600710030070700f0007101c4082d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 341347050 1250 341345800 341345803
    0x103020d0f0920010503130f150f090303110c0d080a1811090901090b0105061b011b09080a030e0d0503090405040c05030d09030203121c1a010e0607240e0609 69
    0x4030a50807284410a9007200c1c26500c05c804880c461401100036660038050f0380d03600d030084612200141c4882c8003007a400c911103400e510070000c0700010400c0008100310700740b8024054507809a9152602c0e0014005d84c880400003280548514a1a14290f02182c0d180e83c4800c006202103141751400c207404000000c2040600c2c8120503983d80100c4400306e00e0344e02ca10342c0600362500248000c0495881c0c1004100a0500001801c490360030b00000080e0000e0086095003103e06c424009141c1d011010b0800d003115070000c801030041e0101e00c1c058100ca110300c0e10081d080050384030a4900444011008900b03000050080d03a1003d0401001807081782040d00f031600c0366419070301800b0301ca8020500b403a20064001e480300001c036507010b40030b891100340494110206800900c1417620f560440441070821640b1841f403110840018251008621080c40c001404401c20a120601405d420821000459010b40380000d0200b4006812840d20800d16800c4018000d400c0600700f041c0300303c205018003c0ba0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341348300 1250 341347050 341347073
    0xc07031b090f0507120b0a05120a1209080a110402070b180705030f19020f030d1701052d06090d140f010c0f0305100506030103060c140a020c0103020d0f09 68
    0x100c032030034400540c2c111001e1007268015108880400d10031070f801041001c803501300c0701c050000180200b4071642d81d0790106003da00c016115981d15003140420204000d101707420a204000c80d0b01d021041c00307040c40c148982d10301d82e40002510000440d1030407046580e950f012660055801901d11290341400304000404860140e0345110328080d02c4004103890400042120340c4ca500180205001e0481d120301d8038410700c06540590700b1900c0501d1198080d20100000d4402da450303551030008052a02d498031000400681005104428181c07070481c1e5846c007080c0000200c440001c0c2c0c00c50b4603543c0c8000540a10404030f0484d0001c8031816000184800454110308410903103040d50384084a07000c60360700f291641c900c5c0e00c021561030091202820710a0b4421944030208420200046449000050090300244e000b00c50b06a110101c41050a5000c60103105584178040102e003020200c440c040e446002c1c004c0c80c5410981d010421071100e040e540c11808101030042c0e010000d840b1103083c40c92040c0c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 341349550 1250 341348300 341348309
    0x3080f070501061a1c0e0f0607090504060501080a021c0515040609090308010e04060b0402030406020309150c044406070801080a02040b01050705060f0106020d090f06050c07031b 78
    0x1442e0407000036004000c00342a4071030840c00300295181c80300446108900a0172928182c900941d00e2250141d8400101708140e402d081c1c003401801c81c1d00c1c010800414040e4140c110a000e5410b105007000a41d8000e542c158112194490158844401e808403020800d8100ea20001c241e09140521504023040303450a40d402d41c0548051000c2c0d51104454025038240704001000244c0403030040000b4a030001403190068810752000c241e0805044c005001d907081900d041c0d61240c0d00000b841140d90302003108002c0340500304100041484d14150300c400324016031243c00704101880c00010154004c240305001c22241048486800316443c00094550445072075005004d4810040400c0c0d03810302401400e4125000840240a9114290700b80009001d02804031814848180301405c0001d009110310381c071400c000c150641066144c1040240f90030300c50031401c004d00401c580140a0f100458510328107851003030516551340c0c1c03013007000c0b0741c5490f4141d44040c0070080034604103906100030380c44840890703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 341350800 1250 341349550 341349553
    0x3020909011e170a060213090204031a132117010b031608100306110d140601120b010801051203190e10050a02030d0902010e03010c0504051009060c03140403080f0705 73
    0x120307142c54a90610450040e00f5581651103152054002070840d0000c02a2608080d06445000c1c0e9a031040300a80c3c000760801c03130b107040000d1505801e081040303101c582e100f8484c030380303555000c0380035203c40d800c000f1180e0700c1e00c0b481e0044490341280b1030700654280c08884120700c0c2d14503c660351042c02da0030039042134500c1764040c015464440399480c0702c0c401d040c0c041c5005c180c2d44940c8500d16901c8400900074900d43d031b103000740c00b4003200e00c03080c003a441240340303068060001c200c0c10b19100e2300042031083d400b1600040e552400314010500d036804803849054800607180c80d48800c1003180c086280d8045c0581c00d010300ca00741c488030007607264400d080780200c440540b00342071003203036021040d2070600484881c4001a84103103d6044c1407102c80e080795840138010f040501500204001003400c1d5a40040c503003000c90340c001002c105504001d01c20f101c089143d454540c403c141049402003416400c0030b005020081444c42200b0302d078646c4000c680095510500c0566105071400d80384d050350f00044e00c1920b0a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 341352050 1250 341350800 341350859
    0x120304050c0a08060703020703092408060301110706020f0903030c1b0108070f0302090a0b0f07050c0612070c030e0612070806030a0b0601111002041e0b090a0b07030302090901 77
    0xc40c200340b000c1400740ca40220140c01213640d0444220020340040300181d04004101d50f002031030884140c2e80c00c400030010010f5001041050348043c08000c0050900340c0268540301d040b603003840082042d40d0b10301d81d02c4440035a4400e50a00000d29900400e000c3c6645404001203c041d2034400123001c241d1210040860112210303248010740e146001210b410700442c440100c1d07200368030311a60041585141c0141b4243c0c1003611030386600d400340c1095018101c2040000380d600d040c00020403280034041e074100d03019450305034010201d0b042a6805481c000c1488070041c840c400b0140603c0c14107024440190519031140300545a1280c505420b464500c0450010320105003e030801042c01410319411800384541c0d0b4488600440d0400700303506002e00280142807900705811000d00080000b01807544142410f117441c00d246d07181d0111298401925440100204102030303d0307562a040c12605802145030700c03200c01c0d04056001e8481d20000c1a40101ca1000200301100401019010131101c3d2005901 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 341353300 1250 341352050 341352073
    0x5040b0a0902150c01090c030507180207050c1c0807050105010509070206040f11120609071e080607120608010516140408060c03130c0602010c0314010b161412030405 73
    0x8461050102a4010307192000c904400c1c240c2400409100360410000203500811f40c68000c0c100301241c01c110f90340e400c50042085007202401d5140320b444900001140b800d0b00541d1030369a180c0301c1043c80c6010f900c0e040090341510204401e040398064114011940d140302d0303450b0140c02803c09000c2e80c3e00c034030000c01c0445d10040c03001812078403481c9c0c0504800c10381695501e4444840c1401298258401d04510048003180c0c4248902c0e4014241c07103008290031410030303240c00c00d16240700e00c2d020b00c02d111800003040034140015945030000c2103810405800040361040d00060003031074010001c6582040280107280340c06900c440101d81aa540e05084440030481004a51103144640401c3da0b00c0000440c065034201c000460308a0b503c10740d80d0a04900b2a035551400e00300e503034003a41c00b50755105a042e0443c4d0b098040e4800d10704007080a083c0c7c560400341500d41c3c50065281c810282d0039036000d4802000003c42c105140403942d0310413104580e007500240d0b9495882100c089609001d01400e551 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 341354550 1250 341353300 341353321
    0xe030601171204051305100510020609071401141617030910112b24050102060124020f060907061d060307050a020304240305070206090d0e011e0305040b 67
    0x5050311360040c0b59030f01041e000380120002e00005081042a8003034520001010368454405000c103034140d402400c814500002868100001c580c4840c24110309503546010582c1e0211f84202e00807143d182c5d4a0721007002454040d07030140d0b140400bc001da5140081400a00d030000c3c05540320302d04040031241000050300d00002607030900c00c40040d003454103001030002d100200c5a16070000003400a005240600081c24609441000b05010340c2c80e9a0950188892070803501000043c200c280001d00095140c0b4014442005165820380201069421386d44815442800ba079014070007c8401c0384d0342c606158150545401d080c0c4500408507418900d08582c0410b030a220300241135000706494110740c2d410205807000c0e80004610380071804108800314651902051100140c0c0c0481c0400b80c01074243c50000d006c540024102d48290f50042080200c4240d0020300b1503c017154034030b01186114120380068841ca02c1c0440101d6040002ca622144c515626501030b41c4103c1c01050301440701e45070411900d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 341355800 1250 341354550 341354557
    0x120f12020a031407030c080d0209030d0201090b0105010305071803030e040e0106030b0f04080705060108070905090c10051b120d0605011404050f0a08010e011d01060e160e0306011712 80
    0xc010416521503e014209114090400e40f4060300b4070b00d440c0d44540e03440b00d007161f211403541c41460b80d0128000e42c90f401d0402021900002c0c60000300000c21003030f100c00c200603d0521030941010340b41c0c00051480da03c40c11500102c511100e070390b441d545841f0700c0e01038a4501081e00041c0601d16240311103000c24814020a811241c00450904144e250700485070f0200b00010000d80d070489040100740c0c0010420441741d8028039000003e841b405081079030240580d5005070112541c9d5002d10070002140d91422600455021a81011551035052950301c952124031002102010301030048807a1100010100501ea20312100d03c00304001c90303e03240195034090b000c0a034400300120502c018402400e00785030307103852000001c2903070444543e900712550940708021035841c07031a5108c0b07808545900e080390070351540c40b4455000780841b504281401c1c6c07400c2c00003808540050740e401000e441d003501071a07000c94564000380a8550030368481c2c10001410001000084061144080140410a080056 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 341357050 1250 341355800 341355803
    0x60c0703050d02210c0c1005030a15081005220f020907090e0114010201061701241503050414250b04141012240f08120304030207120f12020a 62
    0x5243c11303507442c1800058550000303207511550388074005031240595212803004051050582c1ca40d552803920451070000e9503444a40d0f8403414480203070600000502084542c402c41d0007440001e565524000414018912241c0c4400d1302c01401d1104424800b03159809443c060090314240100c0d194600c00321540c40c1140b080180c0085000010b100a81ca8500d204896520520001c503099171138148100310003248102000e21a9941c590780032950340da00c00b51503400480944c4007941c140c41c0c200540c00c003410009000080580d0b400000701000500710175848800c480ca411205030004402401008009151060040007442d81000070350700182170441d41030b2148040700d046400020028011607075562701c1507405010b02d454900e601c1052034410200d55071107004804440c4425035004d0040382c00d071508202200710550b1428030044000080c0300d003400c03503a5089079540c1d58403810100e0030f040311a04502c4000924807686d00500943e0741d00f00d190315018240d18542d007800b10000366507490b0049070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 341358300 1250 341357050 341357083
    0x7060513081b07080105240a0f141c060e100203060d1e050105282309070b0a0f0f0c12030e010b03100e07050d0f110609060c0703050d02 60
    0x1404540c0c00b060307000b98410300744008403a041c503181da03902030a6079800c0384e034151709001c1701d940d801c060080004512400b00c01916101152810494015038841c100d0040607030100d04142c5c2c0400d20741f0354446140f9001d0f505541c9443c0c0c0e018500d003010113008050409803952048280c021903c610900c00c8038050300c0300070b2059445506544e00e0b031303000c014502c0803902e45501003070320321011a800f0b000302071140da000502c6541401010040300d1000f801b13038141844a84c503111906c5040d901c20040d250b02003002191501c560780d0f4a00b680c519240c942c2e005554078240100700c0c1c1000b250095a0105481803540721304554904030b01003100d01c12610b10b0054030099543d440001c0890081e0b0080614800d108000320f0542000808245002d4544004080342c50781c8d40c45001803c581030001d40d029107002c40d07030700398401d20945442404403030303a2038058509200d50701340d0340003a40d8800845041103000352180741c03600b1340e108869460320000d03c402d481c0c1d40680154504900c2c408103903d01080c08104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 341359550 1250 341358300 341358307
    0x141212060f011b03031e14130807020d0f170a050a0c14070803071403030f240a0b130611190c0e09070614070201050d05040f1401020706051308 63
    0x10000d0010766040d2080c18407803181d41200c2440911440c05508038002e031004103960750308130b1816085032400c2c00700c03101e82c510f000001e04042d070f0107a121542241c0070804442e06e10701c1d6030034443c0d820300c50a0030003036108016013101010420304080000c182409408610010448009068200d218400003400054010400100701e64042e101030790038580030f942d201c54900d44a640240c50000240c001d1081c590003c0b610345c01708408034100e01d9a60740180051829414483d4038000100e20282455060442e0340d0843c805c81d038100d4401e00d0303245000502041646695860071390240d8014245908000c0c03110101003802402040300c0340c0c0c0c5910420081903140204a14a0548803454404681252150000240f040780c07407a803d41c0980035500141c46d00398685000070b01800d29200c9800c124460902510000d03070380040c282c13001c0150610740891103075540d00c2c225a42050003100100301d00400c29420200c0001503025044040c850380042183e600c0c1d8030f00c0070b68004009007000300000d1040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341360800 1250 341359550 341359561
    0xc1606020307090807080c0411180108071106010b0a031401050604091a09010b09010f0f02100c030f09050304180501051e030a050f060f0c0a08040b060a090207141212 73
    0x29402180e2041440c43c11602c541c1d19101c4640c20000c0c9603014000da6030100099241a14003403243c5030340d450000d01170502d8103410011194800c000c960169050092140c0007805260041343c4c40300b540ea01030805e0790321940c0c5512810001d60060300030440024a0580405030050100741c205040c1d0704001c03c2c00c5d052602e080d01c208041d00703100444001100d1011510f140c0398071201103040c0600502c401903603c4802490005000343c3c0f10600f0324082002000e8102c901c141c01282c01200d18000940100316080c0b501415409040382e001d2103c42c540c5010a130100b840030104c007800548600c0113070311036203800d4109100c1c01d03035400307000c2d20343e100702801566580825040c00c14105124007400395400109180c4600c0e0038096510000034807500a2001c000c0c1d600c1441e0b42060b80314510f13841c01424141c02001c02054060010b00041960b00100b0119140741d440b40a00d8004082c5103106550701c0d1031a2a10020501000d80c0f40d10b510310a8400000d221044501511100d000410b0007603800daa03039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341362050 1250 341360800 341360813
    0x1b01051006030c020c040e1504080406080f1e0628030311341d22080304020915150c060105090613050618041208090613030c05030904021b060c16 64
    0x1d0005220901c0740b5400e0550030700401440c944922b016103405030725507161900150509a00401d84004085403108000d0840032980b5802c0d030002c196900f43e01250350700404a141c04030240880707c5d05040d02044101110004004082a40c0c4a80d0341c00e404da40102c00d41d15918080a12a440c0c0d50851070000740e180994042203482102c09030040380881552070070080d1035104403699050a0340d80120800c130580c0b110a40c225043c1c1c021001030106110030303840b914658000948020711641c0c5080104104164030303a401c10b0710700d00042500c0c0040842d000142040e521882d41c00f5542c0c010341000241c14034000030568401c0c1e4001d0030444011000b000240c00402006120316407104108550700e00b00704003101d50030700c124803030800c00c5110302d800c2e00c000d800c0c400010f0000603940e00600c20000794003888101e00700d800c0d50604101211406030700e407060075030189080140d000382c4042802901100d03100106100000f401c01998401c0e01c9841c40400741b40315110f104800c2100c28150900002c0c070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341363300 1250 341362050 341362061
    0x60c0e0109031106120106180b130302061b030f0703170714030c040906172a061c05100302120d05030f0c16150b0a05130c051b01051006030c020c04 65
    0x100514503056008031524040242038102d1000241c18050241c010901c0c143e850009e0285003001c2410822042c0112034030405d9400028026480424031010903d07002e1071005180c0005000c0e2a01d07030380740e400c1c0d05026403c500c03000d4000400c81003100c5d8407c150345c10130340d010b4035256035a00030000078040c03904441e85c0068251131550200308000900c00c4030610130040507002001400c14880b03802d40d4103615020702c075920681c0603810489100d980c10082032040280c1c41d0141c0d43c841d281c40035080b05400705090902d0065846040604010031040d500c0440c1090780e00c203e6464020718014044540d03a20b03034600b04400443c50403c0421119a0100601944403040e1050385203040f15400c0f11110248070320108440961a0343d0604e080f111240c02840e0301c420043c0d0344441940d1902c00040d0a10072020b0300240e4135691100c401d07040da84103030111502c0001c944d4040c204216411211070080400b2191040c000610600102c1c03414824050741503e02c01c41c2e4007d1500c0d00202080000030321 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341364550 1250 341363300 341363333
    0x1080d03110711061b0601030516080303060a060e2d03010e0d0503040308180d0f0305060402090310020702030109171c02070f0b0c190201050105030d0905090f07030204120609060c0e010903 83
    0x5e0301c5000c0340c14000010081180694402c40c05090107045030101c060684030550001e82a0f41c0080c0100141d80e2074285484044411503e045101200d42c41b02242036540d02000c6525002e0707140080307030f07010030318402d0041e20201c003038000b00b01d5541202c600c5500d56001c0c0b007a41000480070404240843e208184c07050704891040c0d1003201210981c151a40f0702544040102d012850004401c14159054411640c0c00786081e2010f40c6480181ea0019894006502650349034a41c040754450654409521080c02c0c15441443c064110841c8800f51100d900300324900c0d5640c81800100c0180181940280c0d0451a884052400720410680d03407490600002020032940c1d08081c4442038204610451000b41800181c000140e1740d418a8141810400040214410b008014404003c00d8403660712169001c036601c41040c0740e50b280d0b0001100648a030b64021412000009194802e101040d07120396025442100c0801038200d0049081e900410f99215250215041c080100301080e6a03a00104502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341365800 1250 341364550 341364577
    0xa1205031b1005090c01090302090c0f0c030403380405010b03030a090f051507080d06031a060f15031909150e100509071802090901080d0311071106 65
    0x30419114600901048200c641076a030b20000c19031400c003080703120b6241c21024400c0504400181100041c10120041c0300080c010b00c41800001c641c013092401765a4584440f60391180c2d9074256409969407a0020301007a264500d46da000c40d02c1c590529154008840c41f1416042d0000b5000101304042e900020003e50301d035500c41214404940d010b10042c0340e41400390320792820950500d01d14480a120301d0300414054621251040240d07441d10b4295540568804003c50743c03002e0781c1d2007076805800c070303544001d1030f6243e0a031505501e04850030a5a109103800c2d9580b4080340012420400503900e404e025000300c000c204041049141c14020218100044070b80c007182e82c82e03560352007207503d8403080d04160969903101d0031800710080600603044010f020040c01d1006080401103552545a1072041d13103100300b1076280708807000f5056019039022100080c0554010741c0e46810150716405c0c60f402c5100006c0c40c1203242070b188004202035507a482d13000700d040c020780c10444090001710742c003001c6c200741c88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341366906 1106 341365800 341365807
    0x415080402090a0c0c050703050616030209010e060a090e01030f0507170601050915030f0105060112020703080a0c0509150414010c0f2a1e0801020304020a120503 71
    0xa40c0040f00240356020440140c40c4a20034000c000c00d903004440c000418890f000c44c005106d450100340d080b00048038024102d08038407900e12160b0124140090200180c28076102800710307106c540c14085a5207460300c00c0003940c08002d0b801200c1a1407015140800c0080501000c00241903040c1102110744a803010380b034840b00140150b44c000c907200000501e04258080014055810160507101503c59605040e8043d1500302c03615800b060b00d401c0d8461a0350442d01c01c4521150b01a51441c1c8680c81e03100100d4050b0414000d41010031905105d25022960b40d07000d000c02007404290519629860000c4c07541e0b5101c0c5407284c10b07050041031304512022840004203050032682c40503c0c000011052090001d81d084040780d00c103c00541b44c1000310355030026031581d04a0008400280b08003a0f0382d091000d0a0b4801282c2c02074100c400d01c002041003010040222442c01d200d401a81e04 = true := by decide +kernel

theorem cover : BRFrame.Cov 341187050 341366906 := by
  have h0 := BRFrame.cov_init 341187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341187050 ≤ n) (h2 : n < 341366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
