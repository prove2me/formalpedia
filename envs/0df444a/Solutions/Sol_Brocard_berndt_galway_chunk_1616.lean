-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1616
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:56.287382+00:00
-- url     : https://prove2.me/submissions/8b1d7612-e9c2-4fd5-9fdc-1f96c9483444

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 290467625 ≤ n < 290647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 290468875 1250 290467625 290467631
    0x2060a03060510030902010212071704060807090b0403051f0f15150c0f11010c0501060603050f06040b130f020f070b0f0601050c120a11030c0109050c03010c051206030f060901 77
    0x50204110040d14940c81d80b0f400c05281000c1140141d0b00000d40c14050742c0c45030030032600c0d40c84600e090700c14202800701301c2119038004180042c5844d04108820300490003511290b8007182c840c080c00400c2d0065203c094065442000c41c2c07608102040e810114805134524045041a514000d400c117458224420100d184d03040c0701c0230426034959100c420b02c0754010745000390b2991a5a1100306820b0488a4007400c4c00e4400003011800740e0156688070b00ca140d010000780002a540c1c0f0001c3c0081208071000100c541511b400a00e003454140b06920302010700078540c002c141c803030860000052040e8612418417a90810502000041704400b1307001e0544201c00704141c0d4034015110b80d500740710180c5180e05003d02404034000f0260b01080311031000d0082c0c42c0040e04c2d1111b4810440c2d040e00d800b480107210380000141d02045030419000b00e078407280510122091140d8000506080b1003c2400c040000788061010752000a0101d0581d500404014100c4040d42c000d50030050404030151402c6042d41c0d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 290470125 1250 290468875 290468879
    0x40f03030507090515030c040e0f0603060105180406050903040801021305100305090a081e07051605222a1205090303060a050d06090b090d1d030a020d060902060a0306 73
    0x10381070180030340c4007a0360310380190341e145031101184821304019060041000702200040c64031500c4000c0d100100a4942c04004905107140315891060060740da0314002c0c0108000070440f41030045496040316030741702c6802807a0b9600d8503880010a0094064441404200000115464240060b0400c101c41400c403021007480d02c42048142202e000003041410709100c2000940c40b00410069171107138000703405640d83c0552241c0c000c00d1341d400305040030701d215000c9062000e00600051a4010207042e6100740901030716203040101c4c4603856070740000c40d00e58164505605d540381c3d0700490b4095a81d00070111141540da200d0385034012022090000081080c040a104006240101500032280801441c9036007007100100f603447c8001d004160044214088030010011154400388409400c600030b200381d03060007040c10740c03a06000c64000001034420621064502c0e8003040c00c0311080760040040011030704c10750a001480380c4840051700d0040da501e02004c0582c071000d0042412001c25500010424 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 290471375 1250 290470125 290470127
    0x1060e1008061f030803090304050d14010e0109020f10090b040308032a0403030305041b0b030603010b1207031211150a0e1f0f0f06120201080106080903030705030c090306040f03 78
    0x154009000d0354266180c3e0303604004888003075a4080940b600314001559039520b20419038554400c55010a401c072005001490030b2006104038000807130349140092004a8842c003020f4240d074a601c001a6101c80a10b8486e2054035140034101060103450402c012000c0d9203107031054440e005684180d40c1c0e110004100300c0001d0904103607840320440c403a40c000041a041542461030301440c0002000d155079040031a0500400d09003008030092801801c050440c0c039500c200f1400c1c0c00a5402902a43c01d1640102282c941000f03001d401c501d00c480140ba941c1d00d5510303115840038003400e15109000280d0707420200311070709001c1ea10070004002030001c0c550400d40f0184c021500307180103a00650300b10040111a2007803a00d075824002c0c0c00c0f01e2020810b00c003002c5000004100c240c45098516203801e00c00a0005954061110390768001d8a80034041da036601380580d00d800302240c400f00190001c000182c8050b004102444e000152022442e0a0101501c0424508042038405544588107032580314101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 290472625 1250 290471375 290471383
    0x80f270a020a060f0206012709030309050c0105040506090411070b090a12140d050402012a060b030307230a1a1008070510030b0418151103040b0406050901060e1008 72
    0x500080c41d10885441381510002e48600042c000e8005c41e0842000401054088044001b03206184071402c10004440303140c00341c018045003600f118180160700c07103c2d245601503810b1340c0c121a070250942d490700740440d04000c010484d418482d951409c06001010101c3c24122070a442241514002c1501010b030f41044910b1008000b0108200b149002145c45102c43d02c0080e60343d00100c015001c40c03507440c0d6100584001c503480c1200c4603492a4240c010001d411005081e107000e83c01442d00f000040c0301c3c4014107440f40301d940000f60002541b401c00a92407005400404201c100c050300b950811200c95481d00d0b841c03404101e5900754894103c09203c444a0072040e40300091a20100410380c40b450f00c0c002c509890010030200c0181540c4420b40e001a854540100164908028070309030882d95618152440240c440401c11840d4a045040d900c07800300343d01103c0c055508801030f0329182d41e80d070351100080c210003803131201555210700c8005030449031100000d00405c42501c02c1068281000412454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 290473875 1250 290472625 290472629
    0x1107030210110904180209092a030d12140115030b01020a0203071710020a05040f0f05180408070c0602030c0c041812090b040b0d0c0c0201080f270a020a 67
    0x681480c091a85031400c500c0070483c2c80c030302020341c1c001c0b85415000040d01c07417501030450080d420801d150104009540d000c00c01480841010f11042540b110aa08013803040a446182503015484900b01750211b0307004440c190401c20607000c0c007081c890125240c0c4281281c0a80c440c00c001c40c1c070403081c201c81c1a0580100f52003450207200074074060b415900040d540710018415601c000301110203101911a05000013000701001ea4019950750422902c01491a03201c0d100300168115001008141c0a50602006040307440c028124551259943c034074200d40c850190080350220303000c0160308001015078601600810700e90f005503484078882d11400c0d08040048260a1003a480d040c41e030000003001c0b580030030b9000c0d0401201c1c03810021002c0c090b21404100d802044019501003030014003404480d00400d102c0c4100c40e006d06c85a0164901135a503501428802400b003100b41c00002d003003102c100c50181d84400c150078203008640710103182107441c5420f0441200740e50445007001045d411301c03510303400c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 290475125 1250 290473875 290473903
    0x30a0f110103051f0510020a050102030114120304060503150109030510140c090a0b3103051005130611040b0d061d0906040f060929010503070f060c0c0911070302 71
    0x10182d6803032113002c8120215401540e10a90000c590100c8032442003003070082c4a98810f000710340e25612180d9020198415141140c405c108090444c44001c0d004401c1d5022145992a0b150039511000142001b1005010807581042030010000002c0355041000810900000c1d42c0001c506c0568400c2e8200726000800004241501300702c5510141c40704402c0108641c0c011100c99120150000d9041a0441d41d034400401180051500c000d014171601040084031b210340125031030740c9580d440c980183c800807140086000000700066000c220316400081c200000c00e8145032400ea1520080001d6070030044009020950ba8402800140140100005682518150f80d41f0918008085980c1e50700014001407120b850892464100480f40d0004984280d000c01000810811b404c1a503800904894041440b100514000100b81c10046046025610080c0d40000110b040801c11f07255031161140481c5c1081c00d00b42c0019040415110b252420802c4512440d507544843c10001e00e07290060380707460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 290476375 1250 290475125 290475151
    0x16031b170d062408130c0303120c030c080f06010903120906110319050c0304090c0509130b0306060d0311060408040618060c02040b040e1e011404021e030a0f11010305 73
    0x4060612030307254072500030b50704d00c0e040072a0b81c0c0e400124130107000000802070600305043c001000301500118480e204022010040081e140382c00da040741555500c10346080441c040202007040710140500171a40084103040c1200071075aa41d580a4420114981d01c900003803c050741032089a910151001c100803110000f5410300500910158140107050642820301c080000d0400c4001c1c03042c0142c40052400040802c1400d03610f030400743c565440140102d00c105030241201a00b10642c0c840c500d04010007600405040da14031f42440031640180780140c003807150420501141c00020489244114030901219450ba40b6104002c0c061400005510681c002452014880c3c80d9011103441c40c1c0036012640800d503004103c002c00d0003442050b410718114041c140100781555041c0f207600c100300003045c0080015850884006444030b0098070002e510190307071240f80302c00758900c3c1c03007081c00c50340300800f41c4e00d070423107503540d00400d0f260705007030444103407092400d840c40641e00b6104440d07101148420003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 290477625 1250 290476375 290476409
    0xd06050613090c0b22081b0306041208151c1b08331008190b0f06040e030406031a010f0c0308090102090a090203040b01050616031b170d06 61
    0x40f070f00480d540201c0c40c800c60301240b256140581402d401c06000c0d25080c40008031904c03070070101d490f5580040300c41000d804c44540d408550030005242c40c841c030f8010f00001c1d601e908200080b03611203005003503200034509030f880c81c2c2900d541d00344030035546001c5c28080c40481c41007850045100550021040354041c04940f00f0081174401107548a214410342c005590700f581c1c40000c0c0d410141c0c6081410308081410020411301d44d0343d075003401c810b40e51040c1c01c80704642d03a00302e003241d5510442c02001700039030503413004202c05d07020028039180c00900050001c64070441440300c0c1e41c9103810507070020380042d858405500c02041701c00f02c0180394240c02c1c600401c04030000800600721603075041c001004c100448000400446082d03066a06070440240705c0c010055035182000d01941003510305580c2040000000911841d14508030313408074000881c5039282640f1a20b055803294176140c00d12040820000d42400061003504036190089400001d258540d0709000c0d90000b1146607400140e0060408c0641c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 290478875 1250 290477625 290477633
    0x140604050703030c03170c0306031203160c05120f0d0b030c06030c130b030702010e10050402210102040810020403060e0705060d0f0e12030906071706040207050c0d0605061309 77
    0x8140e042e02d4040c00c10402c01004e91404881c000b10032280c290f007400c10b5005100c107041d0900c004502030b8400b141102d40703403e100c101448861005a560030020b08a4405c8461007501030141c0f451000d00a40540c0d541019810b010880b40d0701203a0341007508000040d4401d08103031b41d8458919103c405034001c000724040000494010702c0040c00c018103841c8080303500302c0c80440c905002c202501858062507213034101060040d002c0c1800d00003204090082150b004400d60640c46094803490b001801c3d400701074241041442144070700100b152003175408220200d04c4050170807028400c3d1101c40001a52103186007040012101400041d5404c0c0d080150304104907900e41c001c2e50000c000300c00c00000d510b10000e80c610010703c0019401300840c0110300c01020a0400840275602c2a0f2411046d20120396a903101201d03402040c101003040106d140c0c3c041180d50410341d015052091003135017142d6040076410006251040d00340e42c11200a5101c00411405040403141c9186c400b003040320900c1040d503941d807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 290480125 1250 290478875 290478883
    0x51f35070e13020901080403030209030a05010903113c0a05070308030a062c060103090f0f260d020f04030602071101021c0203032e090204060305011d0601120605100c14060405 77
    0x400078040540200c0e810220354cc01303204000020398420000c2002d4030b030034940640f8040c2c3d0840200e10601841c811400312510041c0e0f0003280c50f0031403503542071180f40c505088551400c40e0004a1240c460a41554005001088800302a40c020f080740c1c2d880f03142c03265032503040d6541038101007203140041c41c05400307403819050814556960860340d03424542d10400120f004015401010303180080110481050050049443d03c0703880c002c0d42180042c00503025807040b22a000f10000496000410480d0591001036002d46a20f416071002d040c03421f070750313901d03800242d0300256019201d9041e40341c0d80001c1e139031f010051402040e0488206803111803194a0103510303808010040e25640d01c00f140c03140458003038020762000b64107400d03619031a41c41e00c41440000a400c80d0280c1e001003883c0c8400403c0e00340c030b0440c48140301c9d07980310113180d15913840900442d0700360002e0700450400c0340c03200800314103651400105a0741601c01d503507803000000c4c54181041d04d00282c480da900c054028000781300110700045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 290481375 1250 290480125 290480131
    0x17010c0504051e060906040b121003121409120c0103060614250519060c0e06030c130f0b0d051305030a1b0b040606051f35070e1302090108 61
    0x1d1944102d900c5050b000c113400348034072044142d10075400a00450308400110207004104c3d4003452404090744e6501820070701300c115000180100c4500b1100409039032003220b55603211252203249030b04201c9a5000700b0300e00c0c034481c005820389400080c1482c0842d40c0c548030300710040042c2d10348811440c3c8100700c1111130b4451108488601c0c010140703540c080c0c69280e529107003070300e034000d0460303020f0016020011504040401c5c215051820417024418141c400c1d0303500104d88400030440d03480d60315404030140b42d581c4210881d01d0a204158400511190400b0043d002014560b2850ba907407501c281d510000c85400918080c0d0100340e01d03890401003200041a1041a403407030602040034079500f04d1508171103004040061040803504204402c01c0540d40014044580585441d07084d461040f9000c103407400303441140000500021b0750402c03459142456019419080010340c02c0b1040142400401050101d0321080400e00146101015041800c002c0f01c1201d1003e10450400e4403090000700311000103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 290482625 1250 290481375 290481409
    0x1050601080c0c010b03031318020901170a1808360906010c0b040c03020906030c011706010c0c0801050702071e0605090112090f210e060309011517010c050405 70
    0x102c3c8016680409521a200114004003240e40350340c10300e00c0e08101100c841c050408000400700680c440c0c0c410b10700a40380c045505071559440b800c10103280c0b90540c40002d141d1075010381c90792212060b00d2054614408024000c00c0865610b00e070080900449102c0d4442040c001c00405c04501e8914a829030003800100045443c40d031aa02c0740b500481c0c10440401010f45104517200a10041001c45200072084034400d0342c01b000150345590403d901c1e4800700c0d440c0c1e4007159510b00103007088000f003040356521900c1410842c80d18080d5882d84c0c020302e0a03e8124a815a66031030620101c0d41c1c040104000a250f085c1403040c080403440d4407100c000440748245002d008012450220503070107100707a00b145003154a010800303298141801e915089001d882a6000755220543c810340c2d0024a5200d141180c0d00c0e164215040300502c180585948014607111340d55503214410345190030b15034056401000840c18201011003440011307821550800051000e00c001008104031035101c04160030b84010304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 290483875 1250 290482625 290482627
    0x90b0f03040303060f120213020328060902070308010e010e090d0e0319050604030806010306080316020f0d0b09070506030f0601110f061f0b03040812040c091802011101050601080c 79
    0x7039260980203000a0b4000700441c14084d0741c0844c0170b905a01d00c018919008580300306950310030110400492009499214103c5404080d034500724044181901015051300700005000f580e40d161401242c000340000c41c006104503004010307880c00310403128050800c8040303440107405d04d5000342d136840300285030369418131200d07506070102994213100e80301c44002080c03007099201a50b403802540b01c80e8121000c0300800c03101004500194440e1040c00107858040004602d01024074030240101c0100c00022640181d0102d00c107030b15a02c520803220921071050600c07110604007055500e00386010b5801140c0200014000c11100102800da01d58018800782000c00c6444600280142046c980d0b542110b0716104400c18014099018030240001e50344812030518445d44440700c00e4454442520064800802405140201942e10300540d030024400c95503028030079a038500c8c44040c0c0e07041202101034000c210f1492000d40d40c11043c083d80c0500040000c1296143ca030001034056080909015011030b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 290485125 1250 290483875 290483881
    0x110d120b06090d150e070f0608070e2d040e030901091d0f070c1211010606090e0402090613060603050f071b1403130f090b060705060406050c04180c08010501090b0f03 73
    0x160b5a400103030b1805e201c1083e20312171a229504091303000310a20a0900148000c40000c1e1043d12662003c00058030003014007200b408010074001e602240d01c02007914141d04000c1e81b80069950f4413516000d40c040e140610b4440205600140451019034840010961030304142100c00300c001d481c41c1d44c0b0001010001a40307482d8504201c0ba10780c00464000c000001d2440d2000e215500020800d0890086000a001d41034a4510454902410703100b001092000304020400529102d013400d40c1c4910043c203424a1034045444041c207441c4a42d1014012036034480520012720340d41c074045c80d40048241010242c403130400320300c01100000c0b5800a000f16035000740f4620050014422900d02c0310800181e0440e0a13103449002984010501c034000c400c03031601c0407108160611303205890b551358100c00508059501c5454420280c100200000403c0c42c040002080008442c000b0b400e00d000d00380c00010340f5520741c51000d40502c8041c1c2105050000200c01004450034180880b5541c0700407030450394a80d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 290486375 1250 290485125 290485163
    0x60a080a0213090906060e0c0a02060117030c030d0504150e033a05060a0519060f0201021b211309020705010905060106230f0a0c03110d120b06090d 65
    0x84416000f40301110b0600003802c0901c41142c0140342540c0516448010b251140e03400082140f040060321005078000c900100300380d100941440d1001070903403081d00c0c42c010b851900182154031840c0703211041603032003052209001002c8026032100103400810841d541c0080d00e16950f9014192140c1c801400908106402c01c104003075400d00719001c0c410802c60290102882405410304a41081c06000c1407031000034540f03000802804141c4041c2100e14844e4100101118030109000c040025136400b04070100403007200d0360910744920700b25806411a204000049428041c4600100804440030320402d002001c03946084021500d00b00700059884542e4901076003d0881c0060140641c0140d500002c0c886400c2108040708105480d016400c441d001c0c060600715009144450000350000e200f02200c55020704140c5400d28000d043c0214802c256440c0245804000c1c42d200c4006201c403511600e81031040e002e1080040000c50f81e4608000c81c2801181035030780420000f504065026007180094 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 290487625 1250 290486375 290486407
    0x20102040f210b16020c10050912120423040603052e0e1509010c0e100c0b190605010c020303031317030f1e07080109020a1101021603020c060a080a02 66
    0x2090340960080310354504039511010243c4040c6138070300980121546551b0724541160503401f8081d2945410381070501120034000c41a5456895000910031528405581094034020344000c3c0680c0246000c2c5644042990080080d0200c9650245080100c00e000280c00460101c09070310507031040048038100310340290009448a0b03404a405850403581c0041480003180c20072443e00c0c50320941d50191542e0020600f210a015403031b00c0040d525800c0340c1c9031840c1032100f00000400c1c03480c100f10007a0442d2101c00315041d054038a2061100c03800303042506140c03a070080c5402400c1c24209007882460301e0700465240e1000a0810021004119480c020080f040d00314000d40380844813815120f1410b4900301000120580c3c08401581c41c00d90040e400c2078040300e281d4420b40d4555980c103074030791810494002a4100d4102d440c14015002c40c40e400d954024409040d4000e001d0589821620440c10041c4c2880806100c2500490b020031000c1500c44d005141c507504800183c500681d241908104d0002c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 290488875 1250 290487625 290487689
    0x301171f1b021c3005040210090b0d050402040f2406111504021804030503010504050f041a0c09100905090f01060914010504030b040602031e0126071e090c020102040f 73
    0x8a0900b69184401884d6030751000707200d01d02c2510705070302c088607501098800c0700481c0301c0c2c46003c22003004140d94540c900d410082d00a40702070700c08100208443c5a400684102001c1200f6407a4248a0148607144c000080002032665041407241206005005da80b518180f480d0b0075004400c0201040454071100700f0a4043c18101060614500305031170000c00c1031348207201d400d21490400c00411900b8010b020443d000b260f11000007010100c50034a03440e010200240740048118050201ca44242c903810042001440d642c3e642c411402c2c185010800c4019000e840520b1405030300006224550b00100d0f0041075804540404061888071001220303144520303000104844105400d1004108481d0080d40c0940b082041c44880704002e40400359808601344207010042c0c103240701e042400000c105000040514140599181c1c60320b402c074010b0f0340340c482040b900d24040e80030300400c40041c683c85140200c0b81d0b41d20081d443c2a2500d00c07620903015080c09607851404440c01000c82072410303070440f181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 290490125 1250 290488875 290488937
    0xd080903010e03040609061403060d230d08131211123702190512070f0308010e0c0712030f0e0106290301171f1b021c 52
    0x110b0441c03844510358403504075224450100700e05200110702c060090204000484a08074081d0442e034400003000360034105003c0c10364520081101500440e4001c5640c580d0703000e410b4004054071300c03041400901903040284041c00d19182c140380f00c00061b10b8207044141c0c1112a14140041000300122641080b842d45d4030141c0091000482e04420000c6840041107094060419041c40546203094001d40c00324822103c01a0000e5150816041c49055034038021801002207915038a100c00d0315038029070121380195582c040103c0326808142d40042c03894050004842982d19600300150048a10300640d01c0c01024400540c4068201c28802e52204100c00010300c000c1c40302c0044d84200c68000c08441c0120b04c03c54446284c4046005042114000c01d1070140481d41e2a43c0e10304001c1b0100e95820482e41521030140440605403000d1302007001d02c55006e480070004e200f4802e101303c0d9205c4454002030108ad03401c00c440d150f0240460080031010fa10386401d1a10300e00da03010051046511200003400303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 290491375 1250 290490125 290490131
    0x5030f07030206040c29220b2224050d1d06010609050108040f020a0338060303030412031d0102030f070e060f0702010c080c0610060509010e0d08090301 67
    0xc0e06056000441500a0b805409041e02d5280c5843c000c0c199090920501b18045015100202c0c66100d4000203209203035820665001d00f540b54003541e918640c03694440501114049a021201449005041d000303440000652034541d01d400881e485d084a9103a003040400748035841080400e01401c11114080d5031507008101c7d46a18a245110542803048a10903034890907002203500d0340036102000075602e050719080c84a035510b43e20501c185001d0041240c00c250720010010000d10785a01824004480007c0c000740f020101e220350211001302036003c040c0c00c61071418416252000310403260425003085c020311080a14800580103044c0009000b260b19410000e0000c4040042d4003860260b843d4200a14254448200441c1e03031005902d06a40c0c0280704005031043d0b600990000c0c80c4a51060500b03100e5086c0c0e50b19003150a070001444074000e500103108120001080701e1207400608040d003001c45c107000140340000e1a2240790503400740514154103d013414010300405840400000030b00074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 290492625 1250 290491375 290491387
    0x60109030807061b18290423010e150903070e0a0f05101a0315040204030f050606030d0503060d02030703080f0702011e02101d12030603150103020907050705030f 71
    0x3160062030082c03081801e290f10511030402181c8a16100030717806031a90070800c102818032182040c40d8107808608462a0801825a503041d0010b601920042050700941c10708500008541d800c2c03d10b0b411402e604105881c8100c4035a80d440a00d655481d4012031002074807103a6040c00b1a1030282150050904911903104109107880640c020030085440701b00c00784501e0329403041400c0c24045502580409074030b4003c9030301140c086000910350054807002c01025054800c800b00d42203a109803c00d50340b58a41c40c0681041c048104992078204400b90014941121040c0c401015408080e084901c103038203d81a03241556070410000010b16003040e1000d50380c07007040340059035070b5002c200103e0224145002c002c2c160580e80507964003961140e0054000b501e40054284c0040c602c40310b60308034500100e041d20041c81c100300300c80408003034800100f82c2d583c2020070416260a403400c0d609901c0745030792001400180c03601c402d4541c0000c81d40c02c1c480e442d48520b01e080d03070541c0600d40000100c03450128171 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 290493875 1250 290492625 290492633
    0x109050d030f02040b03060405040804030b041208010e0720030d050c1806030103053a09030c050618090901060b0c1501140306061005090a0f080105161205060109030807 74
    0xc40098103001d440c00c00c81d050309684088241e0040d4419031440c40780610001c0c0803070401c2e4000b164814030030380c84549016141d0fa1026803403801900c05580f840442c00800b1001608040c03100c0c05850703900e191601c01d2400000052414080c01c0c91203159840000400c2c03203e450030015120003009580045c03102c0c0c036005171040180d03049081031b60a11a44c810321501542040c40460741620740000203003180701d090005071041c8907607403446407807020008201c84260440025688230000c8541e03840a15040c91420171000c890856080244241020030020340341030002601c517448603a00f07a4001c81c4d47c0da2090241401000ea0307a0202c1d900d04800201c00e17902220110b402c4080c68094182c08001e66290603044001d04100c906194043d4001000b0075582e2034030a8011405554518100d440e2100e0302021481c000d140758402841e0306a0b07035805101040c401e00a007070303118030000e400c0c01d100a181c64005001040102361502d07807680e15404114142d1148114101442d0811700441e0b8502407890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 290495125 1250 290493875 290493883
    0x313020d0804091e0f0603050703030e0a05090a0b01030b03070f0603050c0d1815060f090e07051009030611130b0a0903050106270509030307050903010902040603060e070609030503030f06010c05010905 88
    0x14103d402030303c0d11039174468610440c4100c000f540c0d004002444007505654040c0d80302103031504880d5004080c0e1078000303030598410f0b40f540c1c81842140400300d0035200c03290014080d100080400c42c070a8200e2141403102844401204040740c006280c082001c2d00c0d1000020070038030400196a06243c02d00203600350079000c003030440580c1841380f120355190604095942003283d140e401020400d40c940007041010f640a0303000a2202d8007404107941803581d03600c00044c90900b100c919540441e059150803c103000e200c1c49106110320030092030780c2c0f80c04441404031181c0d0017180600c0d9a0072001250392200203102d84440000f0b175034020020070015031503100c8410b02d0160501644d074100e088586550126480b401428004c41c4660002c0d03040d034a07450380a0b21150400b500b00b5800d0340d07907403008101681e11401440b000314090b1600052188128086608080441d0820814007a101e5400c2001034400400c03680d00100d4920050042d44400d001220300031140c1c080501a50700b0b0060341d5050250100e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 290496375 1250 290495125 290495171
    0xf0601050a0915020f100606021f02160303050105100c08120403020a1713060c02180613020d0b030f1614010e060a0207092702040207020103090512040306110313020d080409 76
    0x4000c46400c51b4044803058141c0c0c035030b4000c01c00141c0084646070409000038804180740e11070100090304000400064883d038800d21241600020344850041201c0c0c2821501d00c1d03240c0d4001d14043c1009003150f1207075801c0c0d01c40c018080405100c403000244c1414402e100c0000801d034489240b1541e4014150132030015048040404003031801d01c0c200040c040c0c046c407030408106a01400054124103107841d0b01c0e418980c001d00440d0414483c0700551880302c0244000c04840c0d25010002031403d2043e401d2500c1c00f054540010102c0e40000c2c609114446629140d2040b6803802c07a1100f4492508070040b038001c0502c0c00b10079000303400883d4004001d90049451026180052002c010031190081722100700801071960311300c000b002c89806009420319400800c426070040c1008030742c0840c15035a251030106111030012581c100031500784100710360b501a244109028038400c030700314240301071502160500c5220081c465800003000358204080c40040d60020011036104110662200036041d0301c2c02403c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 290497625 1250 290496375 290496403
    0x5030408180901080c130903020c0405040602040906031506080105071209031407031205100515031f0312080c1801031a0307121a0403020303180705040f0911090f0601050a091502 78
    0x941006e2001d100303116403800b0682503401089a580408140001090068410b5600903000c01002c03c4082c114040d40009520451003c2e903442c41c803003060f104480c2c2e25040940c0d5a41001c0138019140d070b0040c5800c0702da00da8404001495103080c0742c01d0b20700420742030410450030310200d1804240354000524240c1c00c1e4484105002c6942d41c40e07842c0000d00c1d0f4a0041681c407889409403240038a41c1303200607503405814004101100c071110600012118455401241c40001c20155074900e140c1c0311500c1a0042d0710070300c4a9040c4803002c3c07940c481c0c2c0d005400a190402d42c0d128100007c035810000803120403a00601525251038030b070380507290180c2000000743c60520303241746191ba08400c4140c80e1031107150185e02950441e2103582d0174118100e5030741860b1a0600c210300c0d01155690703440c402c102c0101000000081e01140301e2070902d0400034518010361042406004016103401c0b442c8d10300d03034008001d1034129900c6400c0c6600383c8140ca0184c2040e0544d80421101c7e0520a07000282c10b07200040c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 290498875 1250 290497625 290497639
    0xc030408070b19090e0c090d0b0406020403170406020a02131523011b03080c070b090105011701181b0b040b09030105100f050607020a0e091e01090305030408180901080c 74
    0x10f441c41660544e0304d134440d00c1003101103032000801c6048854084c2c03140420007010b400d50005261241051050305a6048c0c0d40103600107010130804c0458182480206100340106e41003510f0100302a450341d00030300c4003074018054449400b028102541c081c50461110100200045441d440c0d8003807044040b0b4848941d80bd590b412030b800a40c000d80b8145d58641c1500344030707104190950340071508001b015141c0c0702d41c540c09120010028040500707444c45414013030000140d640c540039a07450f68105201c1d025903580d02d03001503050078042c10601d66024941151004840080c4055054203107140c540c00048244c90104000c1007541e0100010446088110001e001c1d6885521411002d004144100c041d8902c40203800c20040c100300c0042c2c104a40020b0004103281d960300c0c458070340040304441034a05a0840001c03080a00c0486800c20703d00b01508008000c1520590b074054054480680050400000442c05e07004612a22080d26540400a1f140640d5540c8d5800d410b5585c807a801007092183c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 290500125 1250 290498875 290498917
    0x904080a120b090403091509030c03080a020304031e1704050603040611090d051b0f0d0f0515040605102304020d020c030406020d03050105030c0108010905061f0f030e010605150c030408070b 83
    0x111400e0440c003a6a0005030041c43cae02e00d5030365198035592020b0900300039408107105c004040703035400325854181c450340315441000e03902074906031203110203404d140404030b0414401441540c580070141c9502560150300020202e00c0c08907483d21500a81a200e94000c0c10381c0310000811401145407600d64100390304071a10701c00c2e01410091516044c0ba1210b4104640d14640342c045944000c00402d66030090090702c00070155000c0703444d11140c04036420343c1d049840f007050000c617000700d05170000103042ca0384000c942e201d400440210b4008040c2c280d588603d40100340311520911641c101c90651000e201180c1e6100d0f91164040c0d21081c2134540f00c0042494403000240c18140800d08255410b0305a44000440e800e20b003c04008040141245401004102d0032401241c88680c810300e0880c540d494542803403c0c102801020740e40c280203d00d0b6980d042400030441500c40b503a019262a02c4e810700562181c2c2624010303403031809550b0002806204200000401455000041c5280c05500c100421004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 290501375 1250 290500125 290500127
    0x80d02151003050c100c02181503060705030621030a110f010b0a050d06090c0602031801030b031902030322061403040b0402060d0902031005150904080a120b0904030915 74
    0xd04510018200d83c100c0c421131151840c2010241501c15024145150640c107590049010900007003c10440d010050041c890240c091441c843c03844101100106164500000000c0031030201400c2240110241180d0b034541400c0c411035a5800c142d18400c0b071740c8480c5084002402510305210300207590040c4040901e0700007040c041c660800d44050f01c01c080380b500d00414041302e5041d1600580d1510350340c155260000d0100c40a0400401e6254011070b00d80001c507a5540c1151080e401c1f45040c14506113407c1c078907407030201d6081c0d0958000341c401040140d00c0d0000c242503108100c640008507016040000755210031210207000d4800703580e540c640f5041400c00c0b5034101d100607540070f0074840113400001d00602c0c1003401011401d08070341020039002d00030ba0200c1d19100541c011480d040751108200000b24182c40501d011244040355032115508103611110790030f126142260041165400e0310201c4001d0b1a08600c078243e4001e85000e41742d28007030034010103052850003080100041c00010034126 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 290502625 1250 290501375 290501401
    0xa0c030b0c070b28020c0a06050106050c060402280f1503090b0a0b220b12030a0909050c13060e031501150302090d0606120b0601050703050703030e07080d0215 70
    0xb644219205859200e0384038024920881307800314585400780c08104200034201d40081c20200c402540200248a203916080041d500c05810034810071505200419040780700041080d0041d805a42000c03080c4d08080707000907109182003114400962200303000031449920b050f80c404403104000100c00d1312000281c1107042c3c54400c0000317042c1021581c04113010742c840d82d228045940005100c554250281c000054441e500e0011158055544100c500d107242010010b84400041c14405513181080103134020703101c43c02e24024151f40981e0366000605880000341280c103489145406600c019a0341c2c1030080c0707c0228000828040d0040100402c00305900ca40040e040c0d82d8905940140488c10f0030048000b03411040e81c0c2a40641d80e1455080443e009200748405494024031090510f503660401d440304010185c001030400204212440220364041d0580b02c0050385440c010070307a19101d4102510b03101440d00f0424042c0900d81c10344410351b0300010040a5400f03222861489561781103481004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 290503875 1250 290502625 290502637
    0x10f0e0c03010303081009150512070f0b0a030612061b0315330801150203030402090a110c0d120f060503070605071406010b0d1815050c07050a0c030b0c 67
    0x503050280014400207014030b9160703a108490403041e0052642e9000c001003a2440c018030300b032040082d09401e00c400d0828107a415850083d48000381142864111245c1240c2410b09c240002c1c80c0c0049010030540e442078105000030000c0e102d1b01c10300e0307104a00b030820042100c0240521400036071004c4041d214028029a1642000c18144040d0317140b4004007805000b486840621100b09240b02880038034010340c4417611403980507074031240c0b1581031a1840840302000c05168003507510510030000160b9405015aa22180b401c4011500c00030b00d15220419000e0001080d040780940140813980d59400f44a9030705002c0ca202c01400030006010703842d400c4400c0c500840c5d0305034100000070f00610340100004d1161500c16034510900d100c4950b08a0304111003078200800c51000000e0705c3d68038505600070074020395156080700c1240035203a5035880d40e09580e2489242d000da2904001406001031130f003a9424035070428180c8015503c145030454000c100c4c1d000459403181c455012469105480d800c0d604 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 290505125 1250 290503875 290503891
    0x81305010c02013602060a050c0a051501080708030414010c1e0b161409190602030712030c0503070c050c030312010509100b0a1209021c120206090a170403020612010f0e 74
    0x802d803011390302030050030380c4040c4d045418000200411602e05004201144001e4044c48c050644030313110301e0045000c03503010307485000d01781e00c0382c041488040d030702200319411a80045003407083e0b442c00d4001651803038082c60002d41101f81c0c4503000c4042040454140c0c000c10301c10110031001da95071030700310100a1600d211010006400f40980d65060b850f10000b4003680e40700030204541003003007000c1c00c6003c4286da0040320040c1c2022942c0c03420885400c0040002460604050010010805004189020041100f010030030700e1266003060190034014007900c24005002d496a070744e041c16440307861403028030030180a100c05070009859020311039200400c0d22a02c10126181038121201250750030080c20890040030395981500d80180c0e9404044215400ca1515003580918107040501d03100b040c0303806503015900500304100c0c090201155600c0484ea01420b45a180010070342d80400340d001e180c00080d08200300088021301c002c4900010b504950911302c40c038140b15160310030b10340c080d0000c0d039110b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 290506375 1250 290505125 290505221
    0x1d0703050c1303080f120405070905090c010f0f030e030c0109140d0503010e09100504112427091807090605060403060e010207150605030c0a1203081305010c0201 71
    0x1000055400c0014176007078650310401410040058000060030078281c80c1101c01380e02107002009808140c0c01025480b0110300040c081c40d040c000c00103410131100c0d607038100c20013071201c01c4030b0b03000c070701a920411382000c2800c1140e44070003a65010a00800703940b0030640b03102007107100d00c0108003800140c2a0800f8003546c0ca66080d40d2810000800115001d000078550b03005003058030580d00e680c1d1003508d10841c081c0540e034006120307060920400e500649242d440400c0b020941002407403915045070b07401a0b411682540052668034480140303811800daa5a020103540107110307070a0b0703001e005c10f070f1406260b10aa5000c29514910f00040328031034403410303800081c10702040003c2901584400382001050001515050450b1703900302c20a0210b0020f82c50807556a40c00f4405810208114441800305030b03400c0355118240714480c0b0507120361540080801c07250200107006100c0e04014800c1c3d0550040081c0030403401540064064000108142411006200c07541410000d01032601809485c0440c14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 290507625 1250 290506375 290506379
    0x402030c09041401142e0603020901020a080c100615080f0604140c032e0b09010507080d1a011b2604090f0506090412030908130e06030f030f0d151d0703050c13 70
    0x90700650094001d8904cd0f0069407090400314611100030060407005074040d050485450007000211101500400e400842e5001c1034900503030000d4506030040c074a840081c0ca5540e07148005070150010111860181c0c0c118010702a0722407000c03000d103000d04a42c601c00b69514074003814195150300441001003c50a00390010022004a0740c02003c110b60f040c034141c1e260846513220903030954848500c11000d5544d5005e4144207039108961454400d00900e080030074800727071001383c001004003c00d000c0c1441d100c3d1010100e451719040b2982040949540d005502d8940e20800540201264000b901a80b400c120004800e0b1520b2100c20b44150351100300c0c5141c10410110840062070440c200b140c3c9602d0800c01041c400c0c42d10f980b020010042100103d41e00c1c50600141400d1440340348080c02d440e4000c2c0041c0200b0f0822400341d60013a04c6940300000d03409141c0c50111a00c840a07448254070000b1007400004c80e0040f11020743c41031120384c400b0f0011341c0380c4600a588501c5040203500c074134501483c0c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 290508875 1250 290507625 290507627
    0x6040f11011e05071a0603030904020310050904080a020706080c04061808030c0a150b01051c0b0d0b0402010f0e060d0e10020f030f0f0402030c09041401142e06 70
    0x846041141071604500e080c0310070882d00480d000301010744021482c003150520400040d41d80b4008401c8503401e510341c40781445000310790390f400b845a8462090b50044002602184002d005078010f000082c0540c449040500f03140c003055010a803480018003035071601150043c021940c030ba00402044540c20701d003a1800700c0403590120840c07600484840100fa000038a01e204101811910001c040a04110800e51900c0c5410a502030426806182003004201c4141c1c0c100341580d0010340ca100150f00e610380304044034801414a2455a41d2001c0c14290540038440d050031064400d1b8400c1e01c80303059280401c44142c9800c44550f1400794001c10030000420f0303041040d0400410200c1c3d441c1102c20221140c440001030741c00c2500d082114806c08800c00c50721100c90304203641c201e0344a15800c1c502d410300b074020a80b5200300e4160f40e40141c0c8a0404682000141100b100c50b104d1081c00800011803541044c4c1d60f103030015646e030404814003505190100c04c0c0404070b01110b13902c2000c0c0b1a403241ca0414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 290510125 1250 290508875 290508893
    0x3030c060207050c09011e0f0f060c0213090b040212150601051e070807052803050921011406010302180d020319030f030f0b01020a02090a0204080d0201020705060906040f 75
    0x1004880c1030080380d071580641c5e1600180f80e4003070500924410714005400b52486042211944441004024814100055003038090b450041d40c80b60324104c52101803a0022960001c07005170308500c00b501d0070b0b07040f009000a800d80e0714080e5108840341d0005244041c0c24a0f9103074051310024250706181008102d145d8051b800406091200e000849010201c00c0d110071190b030001001078461171800210041046014449885804a4855115403040314030300b044204002c0c1c2c020007001c0c008006401069940d40e0304d021204100e170520003041e00002005001e010b0056400e130558140489400708100b5030181c000d0312500d2030311400030b000d10750904040151100c28604140e030540981c407684400084103100300d0720400e01075150f04910200740d0200500301d45003040320003c454503241c03565229030f07404520340440300d17011212469075407546080383c4024802d0784d012031700a10800d540e401c00c094041d00604401402041600c00560714440101d4940008890080440b20001c15a5001404100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 290511375 1250 290510125 290510137
    0xa11030f0406200307030b0a081212060109060912030909061d010b0313060b0607020402070c0e071b08031f0f08071410050d0b030a060b030c120712060e0d03050f01090603030c0602 79
    0x1008c1049856803103a4017400e11320740d281c000315803010000314640910020a20503070045030a18005080921b0044010440c8007240920f000bc0300c4241c407030307000349071003103140e00040c1c03a501c0c904201c4c01e96034800c14118040c09030095612307480040000141d1b0070a07201070303d215007514502401020300d0780c0c4d104001004c3c0e41100d203500503400c3c4040b102680715840070704403440c861210341080b13504100d900081900c004040004004003100c04004040e452000501a990702488054403074a0307010441034118580512401d40540320480000c4010008060000b21031840046c1e4580030740380c2101521680020b040c564010000780e07900c60505100b8030007042c0007416101d002900c01e042c01c000030304103045240d042e1a1180c48010703044561405101396216034004a401d1102c101004c00074076250441c40c450440000180002002400029001000c44c2e105c0d990a407030b130b0012068405001440700759400c0c90011401400071503403001c02d02c10203007a00d8240d1106600c0040729a00c40010394414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 290512625 1250 290511375 290511379
    0x1e0524150406030f0c050a170a0305030424020301090f021e030903161212052401020f0102030124020307030903080d0609050405010501031b1d0a11030f0406200307030b 74
    0xd8100202140e4200e130300c00c42c8648503181800f612407030282008420300c026000340c00c5050704030100c0c0c44400c80000307090a50a40c1400c04903100d40c0d03541440c0030084247d50f0312034440344040350700ea0740484091340194143c40303219404211051508103140100c0c0515401c0c1c4c1d80c400b900300c03029884c2e44061300155902020110071245403141c0c8400072019a0340c3e0140440708080340030b540014140d00300e0404a0940c0201c44104980c0c601444104500c15013162104034000003a04203881c164800e0004c2d20120317402d40700030356403943d40b44034000d15600b98a611000d210030700b400c2103501e10310101c1100d24180d01580d554100d41d095440c1c0410b80da0044260703040d0309030384502c0010300b0f01013401241c3c030680c051000003ea5601d10f041441d0080141000b220300017401303210501082001d00801c5d4000c4141c08200807581d50b824900c0d00003403130030220140b00200d004c004c01c8030b609200f00403c1d20661007041c5c00c0c024007144c01e1701115103400d240d0844008540510000310340520136400403500503c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 290513875 1250 290512625 290512631
    0x5090c06030c0c0f070603020a0806010f0516030210150f060504120b1f0303030e0c1507030305090a1b1401020303011404020c1e030703030b030a0503040605070606031e05241504 78
    0x1c1e0145c80c100c0ca9511100210b500811a00405500001c5a9a00000a003014030740303e0480000100703d4440c16802c0e01e051110b0380b40c05c40c10f05108220a034250340411008008050031101c4102600206104518001c11402c0e0301003010352040050720221640c500c1c40010100440c9e031549140b0800425200c6203540e0340c141100080d2702c4103103110046000e034800151a20401841a08211200c04010f021301007107a201800e0741a1501214041600751a000803942c48064005080174050203020302205d00720714200d21210b0409440500f290f0b00d080c000300b8134a01c02401a40c03240000d00c103800e1803070b070003081901c02414590018003005808105440c2c00c0303256008021a0501c00321141c1c1002d0307001003280f20415401d807040c0c408500c0100c0052807070590540e140c565074842d03402007804010010a80ba020400b0a40007000555030084c03c600140e200341070b4900d0001002041510640308100c1864106d540000104500d0890341e0040c2036180c0d5002070091500d40f0680d000b43e003240d030f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 290515125 1250 290513875 290513893
    0x17030a150f140d031d13090c05120a050604030c02132d02090f041119050a0e1c03050a11030d0606030c080702030a030b0a0e090a02010305090c06030c0c 67
    0x10000d4010140c4160020103401c1d508100180e92000c08180001d400340d10440112804250480f41c003280e0100060320b41240c140407900415407000d1040e800c16005400d20080c6401c100c1524800801c1d01c400f40d071f0144000301080f0030300d03a0301c5550380c801500940081010402091051250306609070001d4103007841e0444080c09401120f07108039002007020202c400540010030848402d80c40144400c00a5040c07043c68000944c507100d03040354907807095988144203a0002680804e80d903c0714944103418082000441e00030b4202c0d40807130440800900007030a00c0c0c20a103443c12440b0b50092541c04c00300c0c50308003243d900755000c1d072205448509000a5058043e2084000c00040ca001c2c00300d001c0104400380b501c03001906449040800009000c0c054041103116580041a00c10761101480c010a0005940b80031440301629900050304500c269010400007103000200a031140e0310070b03642085295076000c0d025448071003802c4055803140741000401ca441c0ca019018204091100080d0b840c080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 290516375 1250 290515125 290515151
    0xf1412040f0b040309051e060f09120d020d120603050a0b090c0301020a09080607051c05040804030c0605031b090312090a05030609060901050a1e0216050607050d060b0717030a 77
    0xb03001102c084000030b84502041c04242031004410600700c031100400b1009580710400a03602c0d0149031000a608400401d140206569810001410b43d184105075003509200351301c02502c079840da0500501241a1240401d4555690302c1910122a0400098145405540e840b80715000f0054000c1c2100d10600c440303c007071660207200130a107607805503c620551506d00070416040130b00085c00304041c0507041c040000032502010080c94030400240e0000b85595403490a18443d00a0f604050042c00d0007400100e241d903003100040d4016010040701c4071444440212150803481100c4a841e09a04400509001500d03003d002d0001043c2c010b0592600e5512140441e00d044011030f0001210f500c100e0601c000804203105854100c501100d06001c6500105600052a5940145140c4003a400504403180c04d02c0b04018080d03469115043d1060780c00c0820300144107405c1901004036040c1f60041c00103118443d00e084a1744107900c441c400a1030b40410b14001310f142c000501c1c030145c41e0b4496820312444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 290517625 1250 290516375 290516393
    0x40b0d02130b04081e0d0516081306031e0c02030904200c03190207030f02060304050f10020301090b0f0a030b2d0a141b03150904120f1412040f 63
    0x281c494071000309102211148205c1e00080340e105103406542010705512075465010089403050407a01440e95040c013214074000c81248034001452413900001d01d00481c2d0284d041c2c20095100090341360703d00d502c155015050f011200e00c1b05150006d41d20821040b03081c0c2c1000e8203e0046241860b200d141003130510080040150f00502a807081e07078000041c41e8400902c10b005094040126100400425040da51215034098514002a108400110014040040403c140d0784140b100c80f007525503400003041c0407001b9420a00908121500303144160400b801c003501ea4041c0d03444018110b402180c070f0750700c4007200c1d030102410f4125601121944049107110043c3c6003100f1b0b1240c121010386524007215010202c40c0840e025031480340104d024440d0031010702c208051400c1e08001800d0340c98540074a24120142c8901c101c9800c0701041c400c1100b03011f000c040048500c1c115803150103002c1401c0c01c08560b039061000c0c0d1011300107003d208210170000d0200940d0750041c41602080703035040ca030707498a03001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 290518875 1250 290517625 290517629
    0x1501080a05101a0309070b030118110903010903020a03090b0c1009050c150306010e0d0b071d1009090c030506030a030c170d05090c040608030a0c02030703021c03020105010605040b0d02130b04 84
    0x10f48000002400307084002040008001c02444600760300b1941014828544a91905144140181c07075002050382600032070f088501c5420014020051603e161401035281d040c15031090340818480390340050742d102c0c00c0c000c43d030080c14002c0c0a1303c2c260112000c20300041c042d003c0162064890351031404031a44514400d02901c0ba0103030342c201c1d1a8035102000509000c014140c60303008082148041002617420003456411203041d0510741d201c2041805404011703c03041081030341c050b00c01202d00d003e00390005840c4050b104100d00612081303546080540544a0580e005601540000f20240120707208801c090317002c0c1e12a07564075001c03800366902c0c2c0095410003400084140e941c0c60501100781410062882003000c251001d115503072420074090303240d018030106841448060110103085503400d2000300040e613801440c42036820903200003000c164919240840244d03103031400125007203001d8019502210b0402210030715100c2c01d06958400b9402c440504646912098004250041081c0140c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 290520125 1250 290518875 290518919
    0x9030d05010815060303130b160204060b04031704080d0807210209030d08010e010b07060908071103062503020a03021b0f1506180702100c02030901081501080a0510 72
    0x40002c0308560843c80080c06004c240c4658000c100450451008074400000c0f00d01c0e12030044d03150380740402401001c0c0c0b840e050080d4064680a008111a81000302400540e4010702c00c081f0420b5a00c80341e1980740c4660700600c4103030351208009414942c03055007440e0b802030580c90174003100e2846210121580b2280b0a501403003c0c7c01255944007410304124220410394546001000c652400c4101d082d00703070060080020082001401d038044c0600b80d000a04825440307949503030b44880e9400c06442034026000120700c240103500100e00394420a0382c844100703648444110340c50407a0b41c0e03400d4000394401540c0070141502801880c019942081d80c0e00240e01a5002920a5500d07214001b820074004c4c55581e0f00c5c22000c6400c1c8003454490207140601c4010704442c00305980c650b91407d0f0303c0d114440292020050500f01c1c500a0664007102034410008281c030b0342009501d4000502e40c184a0520840d40000e103847d002446240c11504501e8201c80030740d11100d142c9440300f00c8080380200220300c0c45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 290521375 1250 290520125 290520133
    0xf091a1b0607020714061908180304030c0f1d0601080a0615230c0307080a031e0b04050609060f040b041b0306030512030103030912020f18040204141006030509030d050108 75
    0xc40c44003488298800f407217044541d0341c6030026035080c0b001110135041e10007041100c203900041c55049848007840d04600c014045035103c550364581b080c07030101140101d062052001700700040c2c041c0114454000040d05048440066440e84011503050300010075a9194688031800020345642d040131000158a940e66038040041e0102281c403514004190140000d0f601002a41c00745c44011050350a1254001e0390355603181c1803410114041d1403081400440c811702111500c00e6a08154403481e0180300c26501480f4030342c2c038081004820700c411160309070448a86900303601030b4a060b40c801440740714001c0c00003451054491111816000745a159000304c0d99500c02442444000c00c018002140e0b000c04031031440d81140da00800c014000e11940c00c480c20020f64041c1156111000c1120004001d001c082d03620003025a03034440c1c14000c5c0c400b68041c500d050480301c00072064060f001d10800c240d00c00c40c82107525001d0110020301005085410500040c0002201406a4040c641c02404180c00030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 290522625 1250 290521375 290521379
    0x180f0f08031305010b091b09060c03030106090807080109110603042d03030f06142106040606060810030201080c09011709030a090b09130c030209031005070f091a1b06070207 76
    0x1060858030303080e0283c0c6c0b081168500f0802c0314104010400490140280c4240d00c40b000c01010a03e01d0003484500c400c90700001c400402c2c8540e02101c26411074035034008481c4040e0742c2d10402404c8802c001d102403c0100b54000c0e010a17410600025a005482450540c83c045510004c01050700c02c1ca14141d4800b07000da004007018035038580510350f0740e942001c0c3c040010600d0f240300c0f41c40d0b503d40030740038500464640c15406089000050395144451140d0306071002454a4070b41040213210324015540814072030404140340e0016103140fa41580e0307040c6c44516868a615144001603006401e03c18100030102d4015036041d0702251000f40a601d8440040d5210b118070171019210184981001404207030a2102c40301d2503944440381c50140d03200600028030b0380014001240a0700c11501250341610450708100c212080b1640002d01c103145035a18082c0c925580402140c0a5805101c0c9240d6044404124840500c03490001c0400341e2800449a0207020a0ac007414207008040f40c46c4070158000c2803003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 290523875 1250 290522625 290522633
    0x715091209080601080606100207120b04060c05030603062413020d050c0a05030610030e03071b050409030e040e0c150306030705040903080414101d010e01180f0f080313 74
    0x8140c02600301070000d8030656040c03105c0c03c0e5440703900038426885260350f440310a8441d0f00a01ca01800741c080340c001061442e410303042a4034298000c0da4111140c61400c044000d401d4404c806490041304000d015003900c0d15012002c2d61a0745e490f11038001d00c4500144000456550103050316450082280c0258071030f480c40c5601412610001e00242284030200400381b1103c1d0721902b12548207504035000304151040480440040845140c1c4855030b20000910300140209003050211030880140f161400540302d00a0005a071502d180050101d1180e04c1da4042d18682178003d051008240000c6481030010800046c0c0900c00e9507401c2c0301007810010030f211241c01c0902400300075040a6070248a2a24180da00a00d001c4000700060400300d103030031780804144824000d012040780d07801e400380404041030000031030b8021a9290290b440d841c000d01c1542411040c0142100c0080711000c0810017100d136100c044640c261100e08842100e40c14418000292045000e9405003030361a014989022030740c60 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 290525125 1250 290523875 290523887
    0x7050f0c16210602030a0212010306020c071a04060302180a1206050f0c0d02130302040f0b0f0d0804030308091f0b030118200103090807120215010311010507150912 72
    0x114120b86160410395000c40019019405590f801500103940c5c2d80d846030250024001c5560354103200514000000900540d80c000d0680c1c80500bc040c0d40d1402e5131001e0003038856031144207504400c1d00a0004001c664020b40c0602031450300107401c4100481000001103542c109074100d81c2028a8164a0f8000d0014038440c1e10b52001d0710014101c06400c166145a620707000701c200030f400c92600061082c2c42c0d07040050842c402954050002d114458400165078080c2840403101400b43c962400040b031107182100d041400d0941007044945841d082d504c0840764102d000344128050b1203514070389081d0040b840b10340c4101c030144010014008a943c0c08050a40d071920740441e500b1203010300e0f0013000c180310044d1281000ca11600641c455040400113902a040040d0050400c4501040c03071f02c00c1c459a829869000c140c0d40d03007940d40d03443c07039400320001d0b56500f800042c01004400c0c0507c0403950080c0000c02410780648581f10744031118030b5010040d194010700440710401364120071200c05422070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 290526375 1250 290525125 290525129
    0x1e030e01151502031602061b01050f09010f050105180403140c0304060912020a0e09071a070308162705040e070e0c0403030804020f0f0603070c05161d07050f0c16 71
    0xf1020b07500d481484401c1e03d000c54186200070340b040e82d001a00245102040c0d400780c0f034505d0014001d0003907290141c1c002440c014103c0340e40105500b000302c5000f201071640b04050507104014214010b0313090481c7c0e04112068010000c40c10f11242508009030a01642c0252a02004400c015039485050400081015255500101141c1038510f4448010307502d00c10035074141d6104080d0544260380d101c0442e494014168040d11400810003e540844540440108040f500a40303c2207140c0d03d90b4072223201d048082206000000e030b0038142043c1c0343d281070b250301169070725524843d10324283c440e80040e00310b035081e0341c81d4001903201300d0081102c20107a1204030761080e60164070904243c510385018148007402440244150401a058449991054401500d03000b01503c0503460385080307403000c0c080030758265041e1110708c10980d03051883c0c0901955002a2445081c200821003a220240c03d40480c0140c402420b10500780600d0310f40c120410040c051000c091001040c81c40101030940814003599 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 290527625 1250 290526375 290526377
    0xc030706060905130f03030f020a020c03071215020a0c1a0403030507090b040b0c011805030a08010f1a160b1003031e020303161206060903150603031e030e011515 71
    0x12208000300350b0514465131401a40008079210504218502203008000c40ca01c80880c8901c003040c0301c502164005541c2c01410400da0480e40d117151212103403e4800c054100040c105000d44900c25a50040d540103030507103d000703040041100b0103c0d075075002c9460081d0500b120f4000762004000a155040c00303090b40105043c200700407540d0170014002203d1013180586030f400c1c034002902d545007880c00d601c00e0703101c4440303d041081d40810710702e04aa141c5c2c0c00300c2c00103800a42980c001264090000319901f080320780d4460b2080120481240114241e08201c8a814050020101000114000c0084184121192401411102c0c150b181c05001c80e109141c480108401b0351080420054001003101e07044007403040345901c080d07138428040742c91380c5042c0104140726091103000038110340c200c0d6040060b2031240034898603013038039112800101c4441d4800500010300c3c46080c0c022490760184041d440000500c0c01180c22203440c01c1d41402d48500c0d00601442c440386800411410300803121501c04101c007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 290528875 1250 290527625 290527631
    0xa030807480b09010c0c0302060c030403051516120b19060207090e0318060705030a02011e02092808061311060406020d080c19020708011a131107080c0307060609 71
    0x100800003526000f0016600d06000b00c003010441404248082440150f82c024001b40e82da00c07045654a46940241c482182c0d5803080c2c100343c500100301104500e02c901c980c00d0156400ca41072044c2250828401c0d4030311440c041c0e45a50314440d5407101003031060078480150f05c0700c0d4420300c0c001000b0b140c03d485074400064039160851459080b20b0102c120ba96134000300d81d5981070440c13201c000417603520030640000c01a1000049142c2c00913019008100408645038207a4006900e8034110000d074400d015007140c1c030501c0c00305020300c2d8080c03005901030b484008100e454100f944600321149444416100300100e844c9801020080000741490b4001880055450909007864440c001c1c0d501c10100c00e0703c8041c4032820000407074003d40c0310203492844101c003035003c42480d0070000207515101c150207000001e500b000345c2e0428413081c0700515100b025002d408a031146840c078403400001c0c80402c0c0228400c00301000700c240492406006041c488002e040035564501e1585000012200c156104400300c9007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 290530125 1250 290528875 290528879
    0x1c061e030f110402040509090106090606142205030a060b0a0f0e0a0908090913020109090c09060809010f090c09060e040b131505100509150a03080748 66
    0x10403010450840c1d50204811540d502100000b0f8080d002e00e070400f03608420f0032020880e03144415004001250092a010483d040d280e0b00d0844001c8614203646c1040070003000f5458113034072251100d0f14106d42d5020040881ca84030f50000303051600030901034034041c8d2140002d8086207046040c081c0142413a8514100385403030b01040440e20f0800503c0e03c042e45d075481003d0ba040c000c02c07504035820701d100104600d449240045440f10f84001d03121007640000d421141c0030490304818843c5802c0c030340039a15002c0e0000d00c0c10f0300c04ca50300080101050343c00c1d502c03000c42c03c40c00c82060155824503880f4034442c101d0344e4144840c0c241207039680d90186481240031004d000100301c8124810fa00030441c0d1511105071481810040c181014000040c4640f41c40d00d0704001c03c0f540d0f04111541a603c0c111210410f40e00da84101d085c42c484a9480180e001450b03d0081000800c00802441d090f40b062038524901a0b040e94001030141684407065128968000455035007060b2070031042c5d8011260700a12440c43c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 290531375 1250 290530125 290530133
    0x80f06010905060d15170606030115150207120308070f0c0b040303050601110d210207120c0c0b0d0b04060506120103021203120c090a0e090c04020a03021c061e03 71
    0x74015210b038901460303000482040010341500070100e0b2141001c150003145a036a80d803030b000d0081036000304129014650201e03810f45410700030881011660814404c06c81e04003940b80c008141003c403a0303802d502c81c41c4400182c0414a4140c1c5038020f0090b11030381084e10781107802070001076020008004110010b0354101c009031035242080c1e00700e40c051800145982d907450050351a40070111665a480c8901500b2a2505a00c0302c4084c60070360105030f071217540c41c186201c003405a0191002c0100103603d100700403201c00d4071401c00d03c80c21901030340305140358617505c000d000c0745070f0b01200745500415241c1d2a42c070801c0c00c090186000510b0140d0300d1615151091462020701038040c040244507039404962a23660040810540d8400d5413000d594000e2410901d14019855128005142c00ba140c0c4980004030180c007405098440c0ca20300d809401c40e015160300b0070000b540100394800c185982070141c000d800640f45c20704180801c2c0700500150b030500f000d192445a50307000c15041c1c0802151070b03081c0001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 290532625 1250 290531375 290531387
    0x151804031209021206010f0f030507030b040302120703020703020f1e1201060504182310020c0a0b01030f06050c0309120912010212040c060305150603091c0f080f0601 73
    0x40d400d407808503040441c0c100104054050614040e40c81444450481004503011909504035021000f564120719915110014038110a210191440d0010001003002c2406ea0040700e5000b40300f441aa60104500030303000d00700b034101c11420360040e480b00c0f07814000c50811020780102c24508850015000064407040d0360315104d00250140100001c0c28800300352002500010090a00244140a44800d0100710018903041c1c4005980700481e4004d0a05103200d10000341400b41010000b41141c5018a09210081c0d480100c1c1c07601c5074800c041c000c202240c40385e1120750181d4450800d58034500313428180441950400b410a640e042020418007401d2540014030a0404001c480c030385031146601800202501444002c01c05554000106521004000500c151107684600496440191030b5181101100c1c0300b200e40e407410034642d00202200f80351040142d94800007000071a044c540302200c03941c80c040d4103241004046107980a11508403604100c04a5101645c03604004031807400000003890 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 290533875 1250 290532625 290532631
    0x1e060e01210902010c050607050d060b070c031e05060c1207030509062205011b1d09060f120d020d0e040509100e0f030408100506010201021204021201020d0f02031518 73
    0x1c0a80d48415060459004a034150515034009040d155589810300010301258010002d280340700d454442c0116100e01810103542009810000d07120800303055554030720b00d0124056508400c11040c0d045c80c030004404107d6684618851800161101e4120010110b60780c0090f14000515080c00c0410881e80400112036600c40c1c14071030103580c50018407100003062541c401c0d020301305500b040d500580091401880c00345501d215903a601071064450081d05104043e080825403241c9200c002c10040d15007010310400c9207100424452014a100117040d141c91540380b101c5000d81c1010b0b034070400b43c81e0455007072005032600340c905004601d8249106e0b43c0714403030303403450b210202d030f40d403a031082005020062040e522000301c0c104d84c0d0340c9865a2a065888010209082455052800103051544107009699000758900304603d80c5880c1c0c0e500b0402ca09801d03442e0100da5660a0090889107416801103440e00b8084000060b903d0030200740d06501c0800541916001e0580b51130b07204450b10600020030745c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 290535125 1250 290533875 290533937
    0x1b160f260c10051b01140106020304080c0103020d1404060b040506040b0105120705161401050a0e0c0d031b060b0411030c0d050a110c060f09120d0509071e060e01 71
    0x400c6000e01c2c1810b079900d002c2c2d10718070840d00b501031420642c8594154405001c007485400b040070340c0d81e40d6074402ca80d071b403146006a0340707143c20224803115154001c1c1c001e06980300b4259030105403140d44400c49031108000710b4095411230344500790004a1b040a01c40e8642204090701c1c103200c40910180040c02500c124181031130764407c4840000c4035540302d0019a100f0012860004412000c0c3d414030321008103540081c509154607050209070900201c0c81101201d9000c40050041c2e08228420401d440e4184e10b416400d101a6119605603404c1c00d100a098030b074414100040c0003141036007807000b00c07604104d0303159182808100340125110014181c58411400c1388009c2810765509071b6100207082c070030b128004a000042040d41c0ca041d0042001880340c250884000ba80d640c031a000c01d2b42c0c0f48a4000100f03080d0b6000c12000070403d01a4102c0343d4400e403810b0031602000e80d07600c0592115071154201800100d5107450078880035601c1011030304a401d0920307000c500001713030301c41c0290701c01d24800c00c1e48 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 290536375 1250 290535125 290535139
    0x6010e0a0605120606040b040f21210315060309030e0a140d050f0624011701060c03050418020c070603140a1d0a05070504060501050c031b160f260c 65
    0x20f4042c3c0d10039080b940546442c031f00090310744d40e442d44490560030f4180100700310b10408101d1500160810794800329482d0304907854134103002c1c0e030f200070603440f80040001b581010346500c5841c58803082026a17200901035076400154021050500610103114000510320071054130004201046559510015103030040701d4480d50141140790040c600203000140000340c1c000d000800c050484a13411f400100d280e005019005102441e004550820300410303d080e900c28044010701c45148642c4024055500c00d080951910b900c42c040a10b4a03118500c00744941c1d0f0b00015401c0012030148102c100810081c01d041c0100d104504410780b500708000c06050000350b0b030700720440350f5040524040202032101801d48850140c0e9003084c9848004601030a40101d04004000400354800d034120b584500d0780202860030104450b8a6400c550700e541240180b9110f032090040c2c0340b51264a8050083c0045100400385602e04198402c00c4804e01400054500c94040c00800f500c401040c1d6450702c2d03c084400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 290537625 1250 290536375 290536381
    0x90e0a0506062104200d081c15080d050c06071d130501050a0605090105190c0507081506040b0d0b062d0a080a080a0c030903120806010e0a060512 64
    0x80707203040c05100070300001c2c4805032440c0f900d441100c00703a144c099400340ca81014012185030349004580042c10b10f083e0000b800c07490b240041155100a890b040d210007004441c41301021f4040c8080d02c40c900c01000030303d503081904000f40c10f410490500b41069074109182058406110700762034031b01c024501000c0c00103024451610310140c00c41d03600383e084c0003000305040c5510140780500034132007405000d00406030030b0004600f0b54014000c5e144074050582d606442c3c144c035161080c50a4000c0c03000741051102d94011003000030b00c107200c110080c11449000707003108181d0310301c07801c8808001351007240030358a032502410640e182d00c809600b84642084000940383c56074400308113201ca10440000f51031840040e400d800c01c101c60001c110240d070494074942c1160b110403105d5100d14550400802e100b1b01000b0000c0c41501590340b45003e103001c0e0400b0a0015a2610b034503000c2080c1202050008038400c04114107981c20400748141100283c036450300090518002511500c14407401d04812a450307000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 290538875 1250 290537625 290537629
    0x7021e010204030b0c0705070501091809020316030b040501061d1311030102130f08030f091009030f060c02060906040b011413060308091512070302070503130321090e0a0506 76
    0x102c034000c55105403000700c0c502c4e14101c07041060304074900c202d03401e006014000030150b02c81c0e640d0400f0764401c000150050300c022140c1000034443c43c0412038050081000b80c151004007502c400c8001c40c0a20400e42a80c5031524100c0e0840d00a500b10103440b00038059039024000b001c404680d441039103d2600c0c41d5000707560030b240740308442d910034143d419070000401b440001d81d10011107040b0303040c0040000003141c4035000281c8901502d08211900c1109104000081c5400f500c0d242401e8024282003030030988035140d01e001d42102c11800c2d1204d42d10307031240480d119410001240e01040030710151825040950302c02182044c107100b240c110801e07124010b1000c1c0e0310390007046030b50031070030302d0400405551385030102841e040210031a104a00d1403a40c2441e42c0341c50011110605d0b00c1c0f1b20760381e06e999141c0506800079040540b06503031500c818028400500311a140c036101850140046003402d0300c051101020b044500c04040c010444030708010850300c08000221500720011540204d030720355031a00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290540125 1250 290538875 290538877
    0x21c0804180b0316091a0607080a09080102070602030f06060702130b031203092d1c09030f050601210b01090e0f1608010b270703020c070806190507021e0102 69
    0x2400d15810300076800344544140e4441c244c4001c0345d010990038003214416644a0010880407082c0d143c010724100482c00000c0c0007d001000003c41c10b0626011403629011031500b260000c1c0012110740d0b900006008800e4804d50115031700c4003048070380d2454042585e000c0f07081c68401c0f0038140040c0b9150102100666030a200301b0400c0302c04408540c7c0c90b8a08000e009560b80c000f40c080d10525101c0071170700701100d060f00c401e10003020388501c0244000c521400007500c4080400f5102010014448c40100016222584800c0c40f1030141c3c00811255042405d08a0058031020114148180e8500100c002403400c0c050141114968000001c91140c0c40844c2402e01d41d10941c214014001c03e0072061000c80e224150f0016035a24034000c109000840c4240092450001e480c0b00c20700f40340080c081544000020b01c281d00a249140c050b08041c0d41d0b120700c500c1c010b82d81d0400c98458010004108080000c0203070105010754100c0c003400070707040000c0c019464a006081006100405030600c00104000f50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290541375 1250 290540125 290540141
    0xc0405090c0411090a090b0607120314090a0b06010e0a030803040807080c1b0114040b0a1806050d0f0504020913050a08030103060c0f080903041202040915020403021c080418 76
    0x80c0c800c2c4588102110810419405013840a20030840100d000c0380074005442481500400608010314280f0030303403500825507203450071000c100740d02c82e880444071000402602d4002d079031080060802e0034261803d002402401449a0704010302900c841c25981e80e085904401c498001300c80c9592a1158100380d0854032801001912240000800140e01c65000924181c00f20350415840d044510b000011100c41034080e1400c01c5201d0140300520104210400404041596040c02d00e140d40a08160b0f0311941c100b82d0055003c20300109a00030b499205000303070391840c205480104142e140c1680020203800c0090511402111200082d00800c04100100d0003c00e0300403d07840d840350703543d140190180ac040703940000000c1032100008510783c025440d40d030294045201850500d030610000d00682c10203880180e034072541321000745001ca0311604c0399500d03a05a504025079030b80e0460060000d4454089000c031105e240040c40e0401069524094800f0785000540481c0250104100c200141c0050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290542625 1250 290541375 290541379
    0x6121104142703090603070c1401050702030d0209010e100807021005040f1122020403030906020610050909100501030503030702070b0712050904020405030d0f03230114011e030506010e040e0c0405090c 88
    0x744003030990000b22342a040c9100d42c044a21980300075244500340c07041558000b001d03910038006820b82010540140c10007210614050600081950014880e50110520702c404241601d041c02a51075050001d920200c0300080140880d00709681d0b406e080300d0911a000d890002e00c21004e40b880c0d502c0d5078020b2100c00c1808000c008410068444030002d41c040d11089001c1440500d0010300c0754000300385244074031000401920303c07910702800d110b01080f008008015a000b01c0d101c044a5554902c1018042d5025000654072460011790107854440240c00c0740d03030541e41c1401040002508500250409002481c1464a90004101240280c051030b0006a414014552000b02d02a1b22012004500c80d459a0a010300115005902d10711031040ea02480000050401840002144040801a0007041c9030003002d0011480b0007580103041d6041e004002511070080c403d403581e00c031255400a20301100c00300560012590015500c0500c444850300507900c0303000040717070160140100c0c9149400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290543875 1250 290542625 290542627
    0x6031207080a11061801140408190e040e06090705010915030e0a060f0f0c030b0a1a070b100317041815080102130519120f06061211041427030906 64
    0x4100c1104a02c441040003000d02076280447c1403e01c020344006040c00f983e0000f0009192201c2d000b11616012003281e200c01c20b11a14000c9400d9603180c030f108142840f90190003030300c081d0400c00140d80c140782082d40940e041010102c014803454000c545015540a01814001410301407409080c2c104800358001811261802c4103100660980c0c4d0003000d04280c0221041042c010500d800b9811a010000400d42114100c0c0050029400b03042c00a1462404800840e092528545d10b41d4010102110740103007007513455000b0030400c48031255403000c0e03400740c8000300d00b2b042c14000050003800c401e10301001441d031100d118176030980300009a4006011284000d40d560031010040d4021003003d8400e0b00d015202118280701c01201120010060711a003407940b01d50182262904400d40e45410403d035003050b81c613040090080304400c1b8444516214140d442c0c00784000c54100000c640c040d1920460440c29501000031a2000c020000714066241d001c07003928000c0c2c0b4840e98a076002e07440c006070300454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290545125 1250 290543875 290543881
    0x13030c02180f1b091302040e04050703050708120a0f120f05010807080c03060601140d060e0f062e0207231504140105092d01030506031207080a1106 65
    0x10041480c81440000803a81c020388401e143d04592182a102030301c1800e4044c401401c040c40c04141c804580201c1d20700250a190700c0c0c02002c001c00030203540c120b8542d84074040402c1001410f00c100001064203001070501501c80741e071000380038414004140304200b21a401030000e1030090180c03d0042c188004104000b420418900000b00002e01034954244034440700000d000900280c050440480503010b40b05d0f5441c2e04005407100a01c105450000844c00d106181658040344901401041a51011182400c0132020054003990280c0f81c64062020b5082074880d0759482d01901e405650b0305514681c100f0103040080381015010b411100412420001c090480c041440d0350244841d0200c812440d035020f424070031100c51040d803044c1116094100b05090582d80603001500c48074001601c405032070300c4100100356803038018541400b407440c8032101d075600a592602ca2991312100540040050740174080c1300841030f0046420042c010000007480e84243e601c100c2110610b0810b0000320741d4642 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290546375 1250 290545125 290545159
    0x3020d1505040c14030c01121a0d060c0f081312020102090d060509060601020706090b07110a0608071d0a090e0309120607020f030415030f2007050c03010c0813030c02 73
    0xc2d04c04c40207050030500714481d042c80d022480070003645050b120141010104210040903044811907820704c80c01101c0919103588032450701c1884a13109040000704501c010801420300074080c2c9a1004000c2a0410000b009200304802096540c2020f11103a1400c00300324100d02920031041456000584040c00204216494010500a8600c4429908190386a50049030740c0e000500c14980050610202001900110360041c140103016000c680c02a088010104041ca4219031043c400102d186040042580d4000f4940c51060000c180c1c03000c4603040c8400048201e900e40c0502c00160381e50300e55800c0302100c20000c491800a02414500d002c45403001000d0300c6120440351800517008080705910300d00000700448058800030990601c05a00801040740180711140c41004c0c1141d031032039050380c400200c0240c90400c980b40d540c09030f0789618603d050b500b0700000f100e0213806070307060191400e03074640c004210941c03020425514006541090804581041c140c0038040d4011255500c054820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290547625 1250 290546375 290546393
    0x1002040b07020307150203030103020904150c050408010b0111100c050c0a0807050d0201020406021c03020c1c11030306130e1513060b1801030b090c090c0409060e01030c03020d150504 80
    0x21900860a80b04540e98400b5020202d1103039045c6500181c00410041c80180303800480550400d0049990000d046a0100b08170200c1d0f4202d03050001051020504208664007402010030065083c84c290703815141884006940c0c050050b00420f5403030321a00c0c4035558500c00d0064508088210044074401e0710a81005015580909003c0c0c4150059465052026005000b1038048071116402440d00100040300f030101142811052020507408100000701010108208500080188044810110000e0010380112a40000e80301c0c690018000c0018954a9640c11098910741c1a000300d0b0080e041025075062131141c4200d041d416452205010b07041080310214100301c4d100c0c1c24100007080544040043c2c03501128500680010300000505c00030b00c007002141e8000381d0034000c13100030f650890005204084d04840c2e8110440d000b107030401030500c4600965000303000c002402100d550554950800c5050a0301001e80521042000e04081000d114480d4401880b4bc5004001a00309441c0031626 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290548875 1250 290547625 290547637
    0xa080306040501061b02010f05091002060601020c03010c021005100b070b1f030807110604090606051201140a0303050a1209060b090f130b1e01060f0201200702060c1002040b 76
    0x210b00d004008260f5078000c40b0460070514204104268031500c580c01180c1441ea124008400c2000c288852122511040c0125020b59405c1c0c018000516009000a2401040c092014820380c10030b48038400c43c40d00802e8880c90080345034004036956882c4604100201c5481e40105042400020388405103c4c420f0482d501444040704542171800c004000c0d8511100c60703000282202804026640009248040616032114050321403424181d80d60650001c541e096840840810340000e01c04076449140d09019014014581c00310b25401103010114600005600005007800400208407880c14003801d1051a030000d100000e00024025185c0b20001d000001251406415000e01240120741d03044801c0b8411114503d10009007000ca4640841424020b02141880f118560b10501d400c0b40e0780c050903001c0c165548440f0b0b411081c4600080c2142d14480c0b1b403691019180704010f40c1d41c094081118146901201d030300c1d480e0110148011b0070700c0045008803403201d01c009070010b032140c201e2001c0e110b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290550125 1250 290548875 290548879
    0x50d030809011a090a051008070801020418060f1205151512010902150711040603060b09090115030b04080d1a01030e03040509060d150c0203090915010807031802030a080306 76
    0x491520300e000c41a1070601140700640c824139510001d44000140d0b400554440d004624140069591307016850429400341c01c4442c00d0703500041e040c840b8019050024881003100c81d000c202a520700141c2d9800045280281c4459217220b80c1040244041044411512603400b2050035240c205101c1150700741050003013560281c6200c0020803401174061140c99141500901040031041004c0b40020310707640008800c4680140e4940401d00980b168800c0d1005036101301c00014148000c0410007040303090081c200d09060b03040c82c41000f011548500d0035011a5400001c0700065140c500e403009207070040c44501c42000380341952500d01d00010031540c5480c4882a20100017913200103502944074461350251030b030091184408140d035800e0054440366510700440400070703085903280c00340c429070300718024910051b0301c00720743d0802c0c3d031401c8988075400116400c03e03690b140c50002e001070a81c9200070440d00c24155101c840e01d8000b940e80c1c401d4507100703500405980c0080b800b860644110b420541c0e80ca8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290551375 1250 290550125 290550131
    0x80307120c022b021b0126040b060a2301110109210f08060d080909010b0705070e06010804060504020109050607060f050a020a02030f0705070512010e0c0f0607060510050d03080901 79
    0x4480d10f1040b1100d518036009913015000c01c0b0a00d01c00780304519040c01c3d500f030400411611050900750303020100c080c902d801c43c4c82d509150426080c90b4010513400390240e071140f01c2c0b064080040d0702c85600340205a82c0318031451518241400d006803a502c044881c1580e065003404c1e006420440f0080303842107510302030155090000981041102c8903003100b003c04001c0b0b104580462011b26042070014074048c4903459051400304d001c03020400b8044c00f80d01a10101c0e401045000400c20b0074000700014088051400f000c0d032a00100080c05402c0182000d08856035400200e42564807515140d409018003410480c0d883c8458507142008000c00102c0c0344c2400d01d4007021881031480342c02154010702c5640e0056040a009440c400110f5002100c100c0f614807030403c000599448a900e04040140d044000140c3d00600580d914100449100031038031540308003814003040e55981007507419079900f1060000e510354030a00c0f1491588003580245a100750301300c0c0c0c640c007019400302509100c0c0c40e101c0c0080c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290552625 1250 290551375 290551423
    0x30809061303050d090606080601081207030e190f140306060d051e03040e01031202100b0a0b090105040b220e130303020c010207020d2f0904080307120c02 68
    0x2a125241070324420460000c90481d40007280c810700181121040c001c80009909403180d544100301c0301154041400b41e00003030010000b10303009024031950004514421031409520350b03801006410010f0003a8400d032860040c8540c44806400c8440180489210b42c284550321000c40c0d2840740005000c05109101e10300018081d1304114034250b84565005000306002c02180100d95400006891aa5054801804001041c132004007007140218010041680900c641d04002410000355401a440703041c00c100c0d242419848140d0200300719240c8401441d01e4442402c012901480b55a000100c05600445c4003030403d034031000320301c1e03503004244040307000350b5a82c4210203602c03181180c040c403040c883c03508414080b90207a001080848120800140f6000d00c0e90300140b6052103000c4196060034842020348038031380c0c21108135412031003144920a401035003400090296903000300018020000131011410003402034820b0134820701c00d40b0342030129140011000303584031226040034000d08020100c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290553875 1250 290552625 290552641
    0xb010e0a0b060408060708042631140a050a0b0c06060a0602190f0b09010c030501170318041112040312050411100207050612060909160603050406090812040308 70
    0x80f1402c40e0001c5001d4002c5a41e100303001d983d001c2000348255004040c880000f5074009400420310f00642450310020f031a90b105d42401c0040420300d1244109120210300104c1e00500883d290340c049501e010750110b0200c40754804168925480d5001c5034225130608408030326600000d000c1e002e804443c1044403810b45d82c2404001120703200380301f60805600078050b030040c0501031840708065207018019615440b0099602d1250006c421a04c003a603903591501e2901c036041d8035024241c018a0b54a503d1030200c4c08101185031a0701c42c03178611402002601102c19255192a0001000380d40c0c800c2c6440d888150311040c05288660454086000030000040c000d03541d01d9901c600b078002c58200305c40c1708040c000d540074851898291386410095205074030f0001407c0c4d4070b00c0c2c0203101c14490318415246908001c002d01110441c0a000195a85c02c03c05800c0d009860318844036044585a19021a00e9180e0b8180f0034010240f81601428003500011441e60712102d5606a1380218420780e01c102a83e070750034034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290555125 1250 290553875 290553877
    0x207140d02090f09071205010c09060810060c1e120f0302071e030c0209090109110901030b0c0f09040204060c120e03100f0209040501090903080903040b0f0d090b010e0a0b06 76
    0x254001503901c003040074015140b040031350040c040c004990307901c0d0712113003100c2c15a403607220b00311010313911480b0f580122a0322a03040c000a10190810244030300306182c0394000d6041c0c5001c0c0e40c0400005a0045050060329030100111600706d1102180c01007140c105810403001000c0c040021580b01014040114800d10841e4900341d040b1061000c0050711604103295215050780036010800f01c0c09030040035940b08007406000d0f4010308000140c612003490103494200c40459954818a8600010008220b480100701c2d4008001803e10b42e0311001380c681c20409001e03140b11550081e01c04030b804108650000d401070303402c1d4000d450780300103c96805000c40f80b01551042c038680541200a480c90701103e181c0103c245100c581c400513041c040c414020070116a001da11120b040c07034031801e002d001d040c0c02907130050f089100000174510307103400c00c1541d010034818151001014a4000f81d4003403400e03266030001405982c40b43c0c140c98556950200a00d48140c1910204c80d00b61030800704d600036140141c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290556375 1250 290555125 290555149
    0x1b0706020d0507140607052d07030503250c0b06040c020a060b0a051302030109050c030403020a030813020909011506020c0934090e070c02010c0f170a020714 69
    0x190003404881a51241100c080d00f051000300c1d449100c0c40d14a111502050007402e110700c086030380385034071031082e41040410050403e5442c155031051000390380a1508600444011a8141c24025500e441c5c00d00d0301c000181400709504030380c40200030041c9100b98084d588041441c042c1d0680707146519081c1c10402120000040a0301580c00b6016640004005820620800c1d000070111440c195840012400d0f000030000002c0640398004018000210035100b155080311068507102d0851400b6030b03000e50780c0c0c1a40b42d409400d0090180000381c01c10200c2d2200f912250340070784000814200084464043c0c40d051009072115580d205000c01e0040c8000f80b01034640c3c000500d64800b903206d50306d051f4a0326543c24000702000090543d014180ca0401c0400a540c50340c0740e0750215480e01d00710403446281c101404800400c80240c605c400035030b900403840d00d00c00750000b1013a8142034403860000b204225600501100e99404a03448600c19000720b40c0004407144c580e0355541040280c010400029440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290557625 1250 290556375 290556377
    0x180103050f04060c050910030e070f031a0405011d0d03110f04030b0a0219020d260414010b03070801200c061602010e03030c03070e04050103120315050a03081b0706 72
    0x50000d004105030303800c0409000130781e0a01510384030b1b015000c900c520b0000c1d004800402e031502084140c1000410500c00107000401111003100c1c00c50352045c02409214034004441c403850000300301802401e60114419000e98458403160520a0103429151404107680034082860041084025003820b800c980d886000d0302c0016141900b56030b03a4540050001e0480b04406600380508184202c605904041210054008000c60100a90010542039006261001d81b01000b281101c991007103c02c0b13190401da10a401030143c030f01e030b11407050050241000c0240d040c807804000103241c900650082c04401e560140030200111042c103c6000c0788140c82e40403400d54400c80001e06111200d0304410000344d203510000c2650144500300b2031543e001501c201d030b03800c44000180410603401000e0380c4013000003600e00b0b01056142d03444400909800281c3d4005050310303a40c100300403c5050740c50700b015090041c402c11965131681040100ca0f004200510000310203141e5a50710785100080d21800c90b002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290558875 1250 290557625 290557651
    0x2e080105030d0f121802131e0903020a2004050c0301090e0102030906130201090803071209090e0c0f010311030a0c030c020a0b071404030b090d0207090207021813020904060218010305 80
    0x80c59500724005c04141801e0032105041411080050f0703900141026a040d04e14404a18400018104909210f150000144851401c1c0321140000e40209049034501d410000d6900c5040c5030702c11449000103c60800795020f85000200420048000b000e0b50513988900310400426155031011400c0703100640380d00b92180d0240000400341641348520b44c2c0c0161041c5003502030b150751014142c1c41c680000c4000c030380340206128030f50345080d888644d5400502c0d10640030b005041c15007407860344404802100d0fa0096400203003420899010340c0055809080300c01d4890760b2841d014000b075009059840e0044002410941d0b01c0110754800030f01008400d070040101da1031515110b0040d034500c01c1154445a00007401e1000001040000b105c8622503010720014000762292008000d0400030503420030030503181b042c8404805078032900c502e040f200381c1141825074a80c5031907075039400c0d04034504c800950007000d0808020030000283c0285c061124014503c0340e060074004019810349004964107400501 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290560125 1250 290558875 290558897
    0x16080106090915050702070510030c1803031d060f040824010e0705030916090b03070b0f04121401110409050a050c030c07020a0923090d020a022e080105030d0f 70
    0x4032581c000382e040801c500442d51381558070004281c56100314095100403c0da0bc22201030b0854014500140d1031206442400e005070071a900a8130071082d20307024180d548000c880070751050321078100b11510b40d0907546009490700d94410000c0d035200100101540400c10754044201082216001213040e1050154105c843d541c0d41d442c111465000246001802d1140400050201c40002e0320304010b4420314101188505c1c1e80000c0c5441c0a0f580d50000070b4584040290010303090ba01c0d001d480650390086050f80c80404030b42030807803402184e0b00c807000d11546001521007071056044c009004403603030740c07070b041c080c940c0d4a90401044400031103d81c0054401080014a4150003000800807148000d08109101c0e44600b0101c0407141c41c48403244803030b1454244d040150001b10141940724641d40010403d10480050081d02d9603d5902c000340a0704482c5603020002130703550452500030b01000381c404080f05041c4001420740c802803044a0080c041c00c4003030b0300710600c41c0c030103942e140580d45c586c000d82c82 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290561375 1250 290560125 290560163
    0x1a300607020a1502040e040f061a030316031403070203190306080c010c03110a0809040f0506030a03111015030212010507080708280b040e06040b040b18160801060909 73
    0x101d0303403c1d200c1082a420080807500f024003129690207503001d00022a001d00ea1468400c1c200c9040c00c0c003660701c0002e108001c000300d981c00411a02d50480c00030703285e24014464501035402220705002100700100c003004200386554004080c2c124500c07da40d140d040c440d12040e041e8200c40701c5010724829500049502201035015062070303403805100f882c0c000804c207040100c3c1d906019000208072089400081d85201e41d02e810b008030f01a0100c80c850412890500030300203940c64070050002411701010903400c10a920703082c8441c1c0c0c5185503401d41480300d600288103080c04000f075030104a1140101d2565644240c0b814802c8501c121311a80310301c095922403078010b40380c45000604001c0c0c238541c038a80e1010400c08a41d401840703200464408600290001c0401059813000025600181c0c001030402010031507200d90240c20a400640b90382c0c0b01c0d1151444040752042d0040c40102c180b0803003103040141281b030710b0740101311010030000302b14107a1595480000c2c0d400040d070190100844501d850a05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290562625 1250 290561375 290561393
    0x3102f0708120709081c02060a060b0d0b1804030206010e16020606010e0a090e0c090a09030903030c03020a170306011101020a1d06070f031d0a03080d1a300607020a 72
    0x10014140a1500d0740e0707602e05c003417400680301c100030700500c20b100c1c600d00750300d8041241c1c94110601f0f42d401e000c400d0501c0b10403040e034020900d0540d00b29444510001098840c03030304030190300030000101440c41c0f038581806541d441c028072400103500f03084c40029034240c410400042d9440c0c00c0307038003514941e200c1400441c0e2011100000c84d07844001000300080900703843c4039060b03203600c41602074101c40c60398604210413040001c0c000e944050a00da1a03100180c5d1000f203180030350307a05040c000b5000030141012440d0400f42c0c2c030020520226410b0000813600160050341c8100300076603d00c0a101c0310031540c2800c0c0e00078040d20f903000c5910044500300c00b458100d0b0b030f01030f01d0700080e00350380c10b0070b072552202d40d06480f40010a034042208a25010b58000c0100f2102c09142c4080d294415190b1031540c8440301c9200b80030004e02d0031a501d901f0055824030001d6101c660b100c1c010040350f0241c00b10305000b40c03000030b006003640034000214003000c2c0305040814a40c1c8510196006885140e80a0700c0c0c40d204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290563875 1250 290562625 290562631
    0x60e0438040b0403120f0e16030305040b1c0501090f0c2c0111031201062304120203010e070b0a090815010306050403021608031908131103102f070812 66
    0xd00c10030007154500600c20307104407401d5016801d00807d4500c020f800c100c0c144540c3e18903024181d00501c02c00d0010942000842d0102c458200c402a5101600184d03559280c4c1561044000242800c0000801c41c10680051981d00200d0fa0100310401a8060540d0404100071020b04100e8441e4070f220722150020020321811079060524207154240e20711601c1c11079005854500902c080b020043c800d4030350121441000080075581c0d00c1c1d4401a0305000c1403503008a200e042c5120503003002000464a082d04402700403050340003210301d826201c5040c030318281c10142465001908804000034101000070308a601d400300859560f0a40e4216125180a4a00100b0036010341c860071840707942d5800200c11060042091201540d21519044030800c0340341c00c030342c003103808014032402404041083c01000721100c1d684400d20340c00d004030b6503000c079007442d6a483c3d441100601e4000882c00b5401c19544101c034044030b000000400510134210b201c0329000c2c48a000d4041e0740c0034000805603c10079541d503a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290565125 1250 290563875 290563877
    0xb01080402131802030102041d060109060219030c0812060103050a06180906020714060103060f0b030606040e0c0612040b09062401090e0702150f060d030302030a060e0438040b0403 79
    0xc0d03c5040d8011a0030b83e80306a1040202106c4032551003a04041c1a100a42056003403820113591407426000941c0e5807640234502c0217030480440160b0405000d100d0346c0706507981c020b00e003e85030f5141a0f46039101001c201d840300d02007828040051031151003445610162070402c948201c0f60001c100d140401040980300031261aa400c201c0786000c01c0c0003441006030441814000c05403507040d0314120044d103010214180e001c0707040c0761044005603000300d4440da101a0a83c9e001410200c03503024145004c58880b107168010341c00141040103d40c2d23980d103041c0300d10700904480707800362102c1021664540003104d20707003d1415000b183c00321541c00c083d80c034501c0b03500516040482642300d442104552009035804009a409101a414200c2d454034650364000c01c803610b502c50750701c5e04102040c50b04d40c0e0300d08028201340c2d0004c00203040c00915489940540285505188945401d103054a8a0414503425034815040314451040d2020180113500c10690b00503005403e540783c5580721220000041e100f10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290566375 1250 290565125 290565161
    0x408030703121d100c030b0d0213060e072d09031511030c18040b0a0504020a051201151e050405090402120a050c1203120f06060c01020d060501030b0108040213 70
    0x1e0a0030074100340d4411966500740540f0b4101c0f8180302c010100c41d4911817000501d82485030042465a621800600c801d4040e0f580030095035000c0300c9170004144035048822000722981c01d018010f07a1003e185543d010410000721201a009100011085100105c41c00000c0e036400c001d00000d08080c0c44a480003403000d0001c1030040c0851005800c540080328480e005420100d13216207101000d40e541c90cc150380c180c0d010030440241d00c011841107201400307858016a000900400200e05c120f046454800c598560400396585510400003140300800d0440001100400e010822400c80c5400003403248242d216140707031518001c103124601a0003082a40e01035410b000040c0e00e81e00c01c0c4820030500388114040e001030700e081c40801000e08009656820390360300031f0107014603094111502c0d0ba00300782c201d0030441203941c80c0c2000621604c1480000c111550011410901c82c0c505500300806607002604d003803001954010044444074404c6501035880880c150390201c104400303500c500741c1491403598007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290567625 1250 290566375 290566391
    0x906060905150412050319080601030b040209031b0d050a0f0501050f16180e07090e07050403030e0d0203011b090f0905130f1131020f2709010e061302040803070312 72
    0x8603580c08040040011404230b00401282d503a044c89220b212103070446046041c03108a101207961030206103105820f501410140030910782c2c800d0701d031041e0503900a040b200e40b14890314120058101c000c0c1e04640540c00d05021070b101040502900c2c0c460800b16010302569504044100c2d403908091101c035030701c041c00d1800400e03000515154076119810903108c10b02e0751880c185003d11001c20060030042086000c0c041840026400b02029280400c00c071405411780206000107030050065480f0b01004007a240742003240c480e0802988001c455903118071134562552107007035500b610700c12074549032040d4015140000058503e807034101294001c0685040190701c0002260111110704e13101c00e201c41c1c1851700d10800c0a40942c03040c10747c060b00301e02507050240d180410000c41c0108000b2620400e4220310b00481d641a00c00c0403000c0340030040c003240095030b581000c6030000700190b5040740540010259a6080032a034002ca0782210085401185051460340b0100c8154074180c6000d20010340b90340d14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290568875 1250 290567625 290567647
    0x2040e04080d1e050601140f12090309100c11090f060d15180204050606040b070807030e060a05030f090f2d030a020f06070c0b010b030903070c09060609051504120503 73
    0x442c8841c190803c0d0006290070b0642c009080101c4041c10030041500800c002550400f00405481d580302140c00d444c4103948403128250b08501032203039201d401c1440040a25069a80200640701540c006c10340c40c0b046032030460501158000440d240111014000081092410082060302096004a0625203480000c071040b40030384040141c984603580d034040181d001e62a091003196040700b0202c2d402c600d000c0c40d104514580d03006907800902554000705841d4141401081116507401008010035505d042448020741207030000d0350528820548000094140e04000507500c41c40780800c1e000388001c2d1881950f042e1941605038120b42020303c4440300c91181a41000a0007010115802030a9192070040c64280b8000009011100308a48441c1802c08280590b4125066859018002d0358079030310311126034070b14403400b840101103075505a80001c85180a920200c203886442da00c60340116541c2040000c220041004000c414104000401c038450b800380c40010740f680310f0303001d0b07a05000600030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290570125 1250 290568875 290568911
    0x15050d05040b1b03061014071a01090605041415010c1e210e04020306063007030908041707030206040f051504030308070e1c05011b0302040e04080d 65
    0x9011075442001c9024490f4150b11100100014141082418203614200d4001084010400740c450144040401001044501d52003168100c035041007000340f05100d6031070031070302d124003d01c00c1e292001e2400c0c0c0007040740e2911380100a40b01c521002c0550040d140c15042031010300c000071187c2d051006010310040000c8041c1f401089913001035003000c0c80c4101c141012070100400500440d9160030350000e80c0380c1103402c688035080111056500680300d035600408245140710b00840102d00108260f01d002501200404800104c80300600e401200c0c2c485007003d50585007021310060410b2018042840410f00d815000b00c850720703003001203904c01c6503a5004515182d0190f0043c10b0303801c0e41d10905124500b030680a49146010883d4942d18180c0f45031401014800b01418510800040c00d00d45051035503102d88107000e100510f9078907505001c103417070f010f03009014502e2503028031600140008100ca001c1d100b41d404886428401c0221035079203581e00c181035800883c2e91401240d441c1450018016040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290571375 1250 290570125 290570131
    0xf06030705030d0302120a0b0a0b0a05131221051b2104090c080613020c07081c02070b130b071b06031d120406050c010b030f0303060112020304030915050d05 69
    0x34030700681e2101401b01000c00e0a00050021501c00d007015110721581d01c420311071504560909000a850300078000d0211581d20850b4032081031800701c1000850000324000c50b00c10502c0c400c1d81d1580501e603002010040c420881124440810303001d011001000e4144c04011040b01011401d84a460701015076841b0740008210485092141c085001d004182d82446000085000c03030400d10428500302000802c44804d0300091204a900400c0402c9140410044030000c4c2c14081d0994190382d8440032452481000607035450f00611503800c0002c0c42c02855811203001b1030540ea121a0114101011030489070301041e4201c80240a086034401000754003411728025003015a00450488a000b4658407040034000d0319070b41513007000c3c18000b0700c0b0301e40f00c0031102260310b141070907a00c0f00c42400c1c04600510b62107000c281c15010f6040704600460001c00110b00c140c2d0242c07250003018981007181d20172070104840c02404280c034240c00f402001806040411140034500c3d1042c03a2848008603042628400d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290572625 1250 290571375 290571377
    0x50d1512020901060228031707020d030b040e120310090207150506030316110613080c01030c051c02130305010f050901050903181c05031207020c0402120f06030705030d 74
    0x8400e500c04600e82160018010305081c401002d02c0411800310348182d0303410200000c04106105c60741010107009240e0801951160120703154107140445005e9100ca4800300140000382ca00941e880c828074041c17142c45050481c0d1002070441e04800c3c11007100a41c40500064070030055200300258841c001e000418a1034440c2e94032400410400e448001954809841103210790003c0c4016035094020b00000021680c020000e50700400b40d00f004250b00344075081509440480100d801b0545000000750050303028005ea030204500c284d40b520466103401880005072075245020400144080c658014012002c0e8103c80945010355030b503101c0303013114804089060350310740b504c080045000c0284100780d03000750a48065440d1505c1d001e0b01098540b141c05c5101d104600300359103102d04016000c2204001c4d03900200b1a42d0700c3d03243c140400c00107142103540400622071600030940d1070804c0d0013520100d0050b00894007007604c1d40f0014500c105001040c40c1d40620134080000781965080003100415045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290573875 1250 290572625 290572649
    0x71110020a0311070b130c090c1e02061b0f16050604050c1f1b0503030106090e09011109040b01140a0930080304060207020d0b0901140c0307050d15 65
    0x81d280068142c40801e41c00d10649030040c042840401c1d10072503500d0b4052071051104c0c91542040c64140c4802c0c4054102d80912807410b2204483c0130342214000141c203440c045c0d09804104040c60403a5940740840f100e50812080d01d0011070b503551428041e0220350000c0c0100b504200d10101c2c141c0c0380591000701543c8551042050206200c000d204101500030240c602ca1655407100140b014101d0a1103588003c00c50540b115500355010100f038045950390110541c0c5d030f40d583d00c507002080c40d03841d402064081ca1030103003c0340c050f110510410440c0d2840010a0b42020620000c01c8010200300e0003850502511001c18601c100c000c1c0c0041090079070540b5400c40184c00d00b81028810369050744142032443c0c03201c20345500518030000309020640e00031501ca650f03903180d140a6001e805200e0000750844030500300b070010013444081c43ca21034503086008000c0e0441c01d10380d082c0554030079a401c0011540810104016600c1040145840d60889402180c5044021114102100c0300e50094074480c030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290575125 1250 290573875 290573887
    0x6120a180f1509020604050d050106090908040e1806150607050a151d0601030f021201020315041b21020f0c010f11120f06040b0301020327010903090e07111002 70
    0xca2050500d000b50041c0108010145165001c501544200c2c06903521030400051101b041003002d400c8000603042d101c000380a0f000e00b92401144a402500642ca0b500640c0d400098440d2242190300341e4080300e00008084d1130b1176062200708410364800407280c005008008820105000704162008103225101c034809500605604e01d003201d81d41000500c071035010503268610160000740541c15a0741083d60f941000e246440020a844c180e442c91000380e50000c003c0140304c504081c44914030b121700f5501442844070001240c03d84054901440d0003041d500c070b21401c8901c004441c0c013028040c40c0d00c0c0c01460704445141c20f1405412140030358107169140c04500c0c03100d10850040c3c45001c514842c07894104182e411426120321001003148480c640214000b56095841d500312450409020b402103550b07040a19030440750001d41c07140380800e40d0004880000c010414840c0c6904160181d0380c102245003445945a00703507401402101c108040c11500f440006814091500d12000c1d0302d8005130741e40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290576375 1250 290575125 290575133
    0xd081602010c06052a070506160c0f1103010b0a1212140c1b010908120310030b2d130807060e1510060e100e2803170906120a180f 57
    0xf614048071965205c42c1803001c2d100084c0d0005e8025000034620311100c481c2e54010340c0c1240c410780402c0010b40980142c1c4140b000388266095070503200031027a4000d20a001407203051207024140c500c119082c01c50082c040318080355803d11501c00b4940307a803030103151103012281200c03040e810854844184e50010301500a80c000c01c2030000b41840c4c02801d1100d4268070301a1155180e40c80800e15030150007000000641d000088501003018540c0920081100d04140b518020404d041714021410003c20003a9120b0145503003c0d4a071003581070b003c2c4514040040c0d51002540e80107258112102515550448011641804078507110300300d2105000451a0583c1c500441400c981d0210060014100503020036880b00c01c0c523000c600c280e41c28110341e03800825010502c02080707000b003150748800c0015040c06503150480a001101d000d4140036a5140c00c0503281c2c4450710500241c203610150400c0120810b51320380132032a50011000100040d20050f140c60041c0c000c00c104400c44803000101e030080200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290577625 1250 290576375 290576431
    0xa120320030c1b0f010f050910030203070e0307030809010302130905090a0b10080601050f0303070b070302040f06110a0b1015030504031b0c0b0c01200702040b0d081602010c0605 78
    0x40183c100d86104003041c25004942d011621500103410411205403d11980b8003600499403161b2024101020340703003100d00010000d4005448001c00101640c400641c1841d00195034002d40e40c12185c818604044540150001e520210a046e50400f80d45ea001840000ca4400c11f845108010081d0a45030151301c1c00c610f015a00602c00005008160b0040c4281e1070f0008100d4155501135030415074200803100000d1950045010013020024040104401310b541a00500111017801484030261078441c0c0c4191008070328042c99030200d50050301510041543c00c10301f50741004840c5501590191926144001e6100b0240d90a02003600c0d0340500081583c4442c04100350506c580b41d50051110954904e07003114458800c0000800010410000011003940f202c6070801070b507030008004620550011142e41c001307940c10f81c4540e18100f500205030400403403501001e94082c0341c0d245030884440405c010306000900c00d90420030300040405c002411032141600032050004080005a410801c1d4690 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290578875 1250 290577625 290577643
    0xc050c120a111f050105123003040f030207080a1703070908030a020a15110315040b030f0f07060201020a080106050a03060b0f090301060b040803090618091e010807050a120320030c 79
    0x7c00080c03100a20200d0045520000002960071000c2440501e0b80c5103004510240c3c00c1d101500340000520041003020070801030b1441c481d03001d41e001103948100c15901d90b40d0305c0c84090103120f01c002083c00c100a03c040119440851428040f00c21f03074450401e1841c5800c042054009a0b00265100302440008410020140c5441d0014483d4500310801807910b804013908a008007000c0d0030b03040002d543c50303421641c41002c02400726802003400340c10099440c00005007502190060010206d100c0d07206000701e85401c1c1c2d06885c0c1d14000d900c0e120040f00c2a82c4002d01c0e5030101503a0341c00120350b8001c144010b010188803588119143c42d0340e0410142124996400300108200401c010040303804044284c5245070000c8031500e8a1704000e41d29096600a400b14640d4080245070410982610100541c19400d0b0568803412007680c0b901040c59a0340807a0050300d9000c02042800c020106134192881e42d154440c1c907141074400600d101c103001c5400451120300450700049a600300404080000c2d841d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290580125 1250 290578875 290578879
    0x3092a0604030b07030905060915090a0b01030b0703090b18010c0c02011b0c0503010905030309070f06051b0139030501051509062205040c050c120a111f050105 70
    0x6040440400180d6039104501c001411030510b640007445550003540014035254004080d6005850f018600b903881d504200c5416a021440c1c3d80407801c0c032400002d2214510764860400c21417642180c640e401407400003017000d010507440740b03004e20006620411550144103c8404042142043c2c4007560945102803025020003e0608070340d805070303034030030120000400e040040307a2016000781400b44103c1483d070015a01903083c001004100a4004011441110f48a040e6001141c44902246440d82c140c8900c000182052100005100418481c0b82c03190031404000030341075590031000b400006100241d0030010121520704c800940f694081141c0c4640986004c200640c180300000d60040065494400c0841d4041a090001d444c0c80045844403078050400c03002da0180d500004003d23428074041e090045040104801d9003c3c080c03000d459900c501040a0414403101480686041d00620110340400148000307088040200380480f43d068078181564004585025000308290341069212034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290581375 1250 290580125 290580193
    0x11010e01081005060c010209030a1209080a1101031a100804020a15050f0c0f0a0f05010b010509030c0d020a0f09050a0c0207080d03050907091a09010e10060e03120309 73
    0xa07010600004041c1561011130303509885000518045009000741c020003034051150321050b0003030100700c1c038411090401d1030b52000d04864072001413645400440400a0a48400784040c6002c0d60084e040a811429825142d1030800280000103000c68003184003070010540703200a02003541400320390f10000d410141221510f50f60b00715030081a5100d04410940180004038078186010410300454007060188021585101114100000c509003141011034480d803900ca00301c000c55001d00c0565038880401000b40c08107900600a11403c800c41c800220b03448501041c0101d01d000403915048080d080c113440c000713810300d01044c1510854104003a228155405100204041500020680b0600080f0720300819151076500e60703103103464415000b0b809540d09040d810103c95204001205092404444072960359988194042004005a030f5012590040d070400b03100103405115507140d00000501140d03403000310890302144130307001900d09040d10b0300b01040040c10804080854007409d4403c43d229 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290582625 1250 290581375 290581381
    0xf0b060405072a0203030d02030f1008070f1202120316110409050a02060f2803150e0a11040b031611030901021b0103150b031605070c090b1c11010e0108 67
    0xc0721000035070404010f07001d4220388520110f4405105460f03e840c0c22403003c5d0348070f0424008070711444804668280388100b25000010799290005540d60444140c1c3c00744d04840c46c184640400c15860041c0d084e40c0222018800000f020301c1007004050b41c25034056150390b580310920701440d805d0480c4d5204d030720442c14000100007003400402e4003010564100c0f081036460300242c1e502c500600900c42e9540c4443c81e4050140c201d18400308001c00c15840c1c9a40411000070002221480e802c024003c0f1000720000400161401c21f080e4040915518078210032401d056407506100300c00d910440ea0481c41c80d414003030f8404116000b9001820403a0161301450030100140c0c0000d40d5a240b1810495440443d100c2c0b486080e40294800200c2d0850344144000c45a240c440d0010a40d1050b41d0310003050102035081500f05100d002a03071501d039803001c66032039090714203660790000e44040e06819901c008140901010381c000c3c5106103980911404107a41c95024100c009840c14034803548041c1071044990030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290583875 1250 290582625 290582657
    0x10513060b032d0907030b010617010302040b04240915081504061404030804030207060c081204230c010e04020711360f060409030f0302030c070f0b06040507 69
    0x10749500141200312094030302000702c0031040d118204203ca1840c0000e40044c440d00c0000801c910b0705a81c011003503000542d030f032680d0031030b24507101c1441c0ca0702408052005200525003a0024074840c94006c00c0400c0b22400c600c842a0521030018008114070309015003041042468003540803036282c1200710b504000d1411080c1a02d800003030340a80d10500d641000a01084025803205041d1119041205034520f000e1401034140b0318240c0302540540700f00c00740003c0c5203201e4a03007010240c0c0d01261710350600e00d40701e0f0760034843e00c0081c000b01c2d0044a00c040d2184441c121100e40c01d4142c61600c001c21800403228009001c4920340005140502c0c0100041c4000ca2180748806444503c00d075030454103843c000004c001781e50a60002c0e60b800944800100120414032a1103d0003108843d080080c16100c490820044038110b240007004074101c84402c0b05518020760142d9402070b05082413a01d0038003980d80c1c0186400c918030303003250301c504148140300803401d2074400c646e40501182090f050614074101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290585125 1250 290583875 290583877
    0x9050a14060706051f03050109060506091b0c1207030512060414010302060a0908010f0b03010e0a050a03050309030702130c02062406070503090405070309141f02250b010513060b 78
    0x10054143c6403600c0c04102500d800e6a451000c0007581a904035003c1d460f450064003910700c6100070f607055403c080201c2c100d80f6100c2101070082100c0054446581341c811803007103040d0030101901c0100d01a0545400030310010400a000303a074425520f45685190b44070100c0700e000c00150407039005d585004d0355070806100d80310003241981e40444455881e130b800400d0860780740c00c554210107895400c008050f10042e4031508100700014084009018181e151a41c0b1691840f402e0b101030b155511003032a02000c01e0149000b1908104640240da1802e0503035000b003a08002d0a0f007203c0c0b8516510380e4100c5a640e4140400e68018101020b05002640409c220710300001c492111188640800241041004820001c42c2c1d010302003d03106000500c1d0071040a0000c1c51150401d4031031404006910440c0c28000c43c4443c4200e41c000b04a0020310300c000021340081d08140c1c1036541c0100441c030224107a030360140c69102c01510948021460303606041c14007801091075038030540340340c2c1010701c1400b051001e04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290586375 1250 290585125 290585137
    0x170a050f06010c06021e09040608010506090a0b0d080a09030618031d030c0405090106030302190510150302031b010908070e011206021306080106080c0702031509031909050a1406 78
    0x4606401c0110b150b0038030f08028868089100c40031b8003801d003502c42e08500100900643c04d03044504001d0580d84140302c0342230b5101150359503801441c45001402c0d50b251070b0b020f5020918040d04c0030603142e03110341e47c030000359000d070710040081121441c0c10000c109480c000e040d1034070010703a40b1544401141d07a000c3c0014808100003410134084104040d583e0300c08001a030740c0a1001402032140e8100304200da03000388214041540140a000507201e0520300a0504030a86940038005284009007a103c88009008003407803400c2c0314500c4880000566400c000c0121007803003088002246112071000540071285a9110811030780003402c04108820b141940541150101c880c110004000d52070200024414003008560502a9420220b046580100700724103865668680401d03d0311b884080b1070721809a144020351581c011080e44045080801d5200e400c1324220080702d04111400507680201c1c0c1c411010702c00002d84c040782c2000740c2e00d81a002907005014955400d82008600804a01c4d03612400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290587625 1250 290586375 290586377
    0x1a0d3005030601121503081b12031909080c0303251409030f0102120901140c041404090203011b120504111009030204090303240b0d0e07030605010303170a050f0601 72
    0x31221250b01d10131500718128a22400d03659940603074603460010300702e8114440c1030108640001c0380c015550f200003469000301c1c038100b5455003981e4402440c0744c1040c110700ca403101c06540359201d50b0f0015680c400502448007034039000e56101d00e00490400d0780703440f00d0b5448616100712100340c40403403504802080c1e0105114480783e542d600750240030034540840310365201581c0d031000a81144074450f00d0201809000032070000d110801074031000c003200003015102c8103000c4000b000100541c0040c2e01034420045e9020304041510382054000a08480481085010740c0d46e031035012866095000c07001240364203090314100801e0800e512000030f0181c800c3d003520702849411044010b42802003040000456004100340681d40d480d240c01400381081d0300100034052410b0a814903051007d8072448280e818252855080c503018000c010040c0252080300c2509005501012000c110a800782038040c60103038880240080904407544130f01c05004204c84038076894003050008001032041420703000502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290588875 1250 290587625 290587637
    0x1080a090f0b0703091401110d1e32130b06130c050d05160f080606091201090b070207080705210f07090c0201060b07061a0d3005030601 60
    0x107441d02028030840e40d04090481807030030307040000c0c50781d140d044131804c03901c00d1312460f40f03181c0542d0405090350f40307581450289060601c4218000000741d40300b4101104007405544c0c8800781d0003a064200c0e41d413412070b0390503056000e40e1030f100c0701d407014003501000e4030400e540c004500c1c211590040300c070b42c000b0f0010101480000810241d9461032506503d05450b240c0810102c104480e0103041c3d03034420074001c1e5030740f4109800079944100c4220349015203035040d141c1e4a24000d880204030f80207000200320303543c090028030088500d52510540201c007420080000112688182050300a111004101d1000c5500810040c80652000f0500c08110f031000e60702c5888058002c14840950880b2072884495031064881940701040e00107110710880d11070310030800040d40d47c0340049091306c4003409502c010b42c80400c40f40c00084c10700d5009505064910260701d2842d81c0c2c8400085965034040f02c152400c480301c00d6000d48007001c144c1401d00c4800710468041006400201c007911a02000300402c1c1805a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290590125 1250 290588875 290588891
    0x30f091504030210080906010e010305100c050d150905060f031b0102011e05041226040804030203030309070f080a170d14010b0a0306080601050607141203010e0f1501080a 75
    0xc0c00c1500c015550050110b080007071000402400c00804a0300203482c0d00c6060000580c6010786401c0c141625000300c00f03400c0900c400741d20702015200740c1b202d21040042c108407a071400105031244c442e8690b1508841d4048a10341000d10040d2640600360b00d11030b401a0410008d2654002801d4581d80c03000c00c050300c52000300d440180c0c01001260000f08048101c440000c01d070080a074811481a13110b8801c00200034075420080300c4241c001104048140c0d1020400400c2c516041c2d20103510611a0048078649a202d9000c40c0c155003082c0d442004a900c0340354180f0000b03c05442c444041d2020f10010181c542c16070b151f01b00c0c00c2d80c85400094075040001504810b649164000c108a6025804504140d596031201c2d8102a4052880a0006481d1a03808103d040022034a58100c0708000c0019007070007600e46030741221a01d070400c00c5001d40f241e00f011140c0d03440c8150255000b018040c0c8100901d2a045000000c3d00c4001403086d17419070f06030b4074222450781c0c00040e8960048055600001c0c901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290591375 1250 290590125 290590159
    0x903021306030213020306100e01050d11040b120709080f0a02090406150b1c050912031312030507091418060a08010e03090324160e100c05070503030f09 67
    0x90240c00182d0032070380e04e0705a040b586110780c004501402c01501e5121600c0c4ca8510100c0e0b1101c0c46050250000d00c081154040c41e44036a00240d8184100305440b91030642c2c0d40144040d10707446006028003211186042008140e00800b2202c005e123080d01c00f4180c1805084a81a140c48111400900c28080c004c00300303060003e02d52000505005915002402503107843d0f4640103500115504445540b034609100c03010415406418007480b1400001c0c51180703d10283c50000e50401007140d402803020b034a840c4041641d40003843c0010105443c001070505140c40020120b40c0e10b500000d15031400001d010100c0c2d2504031080b004074070307880048111902d40c40d0004020860b5544000590340c00c1c2401156212008401007035901c40440c00c9800d8003100e0110a02000012851090319003040740001d070240305008801c00f00d0084620300144113803080c0f400146d081e6111808100028a101c4000c01008020001a0050700b0110015400e00074000240c00c420300c900c9071040e016107240b6580035180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290592625 1250 290591375 290591381
    0xa060c0903020316050301050105041802060304061103070309050606010503010308180301020c070b120906100311031c020d080a060f0b07020a12200603070f0c031e120b040c09030213 80
    0x2642d0b009054450400310300704100b41c86100d50207458070075440c0c8000011149010b100380f501030101c40d811810350011580130081143c1000b40107031240d94491f098160160300718001944070f404281c400141c61012401c0c21032030208020f000c0340c140a82040140040b0300720005840c0e07184100883e442c080c44445003c24003901444842c1105403061083c042907420959015047d40b105811407580503a5418204642c3c480c810b40300400741c0b0b00c0031700003400802e520b44441c541c14440901150401000c64514001001e607420100300180c20402c600e4110710f6101420300c1d04001d00ca00148005405c0081c00d422000b65032107640800c40000482c0e81c1151a410070100045c1881c0031205003582883c1440071140e070f40c4c0381b0303040810200525840b80518000d0107480c02040d007561030f247c01d0020795409550b09014100c0a409101038401c002c681d12400c3c5041040c100c11599610000e610364a0042040d81e42c4a00d034184982e0078190082d00c0d40345e01003440030840e601114100350001024040c4002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290593875 1250 290592625 290592629
    0x5010509010513112107140402040b09091e070f020f07060e060a1101060803070c060507030504030807080c0708010c030c090e0412210b090c1c0f0b0603090a0605180a060c09 76
    0x6030840605e03030028005000b1030300c00222800014401d00c404020f40422049100324000c43d61051010702080d03905040a14005078046000c0541450014100e201d8001d002802c4078a000003805484900003002d034148550141c0148a000a007942800c041002c1d20b4030150b51000c4c1e01801c0c001ca00682c1e00c80c4a4003c00004201c088020030007283c88a101c2900c0e03522009060340d00700c00d000d000088440c400d80440306d001d601582c4040c00c1c98116a20600c1a60180000b0344000e4070a00c80724800180a004000007807501071300009414100e400050251a820f040010038440c0e4118200b25290302410071550183d444501c2c290150501801601c41ca0005c0c000c24405070002802c9107401c0e1915401040b5043d0f0484528030159290700d80e882d12885041e820380c6940700003003071004d04202d094100303c0c0340f40542c903008107881ca20403012078496002101d141c007181d03004150703820038080746100c2e054000308109080490071700074440c801da642e13080810003084141e590134400260792203180c0d1540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290595125 1250 290593875 290593909
    0x201090603090b151c0c03120f17040606170607030e0c010806060a0302071a0601021b1c02030c1804020411030405190606120605070305010603020310140a1208070501050901051311 79
    0x340c180046c03c0c048801981404116040a1a940e4281107240a40d400d450300032640d9444d60300c0f08007003242d0f000c031003400504111020758541001141240310b0300d041d13410034040c1d40c0040c4102c1ca0090001801c0e0307101c1d001420442d401c20342440718180d030300403100380e4041d000351a00ea94650509408900900c58200d010b022032540d0300307040d040e42038100c02c01d600420099080700d0b08405c101e2841180c051840811951140d04c40b42c1c054080d00d01c50505009040c00241600d03c21803c15001c03c0c10014441404c01c2a10034100c00c0004600c0c0078031412410280c441c0d1514154500703a669196240310343c105103030300d03120303071668800800c042130b00311a01070044840c091120300c41515105010704029a0006c0100b41017400221f120f034401d1003924481d5030024050b0090b9441c081210602070301050a05801a06400c0c000c1261901c401c076070f20b012486802c411341d40340d426003020303405c5800282c0f40319101d07410070051201c201c4e56442c84040f181e811110040d002103942000840070801041d85007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290596375 1250 290595125 290595169
    0x301292803080705060a0c1e02120301120c1521020c070909030206060301151205010f020307090e090a02010c12020a0b0c03010f05030c1f090b0d090201090603090b15 73
    0x301c10091001c002d40185480341044401a46440c0030217801c1d1a40700e001840080c40380031030800a031010746c01d0703a0440401801603c00300307480010300c44100c0d070098203c00c45a04500e010700c010000e140890600501d0016400541ca000003440200402058500041071034940c501c012010840340d4112604196804101d0300482d80d2004a600a800c440c0d00640260107690009511410706000b02645105007000d0b070001c140c2030410f803d030410115034017512159030f01d02011000507220700c011030040072551a0b50129070f02e404642201c0341801804402550854a070304401070b60404418000303c0d40c003580689160015500891400071a0407000e803201d44c91030103200c40518690003c5041e640c0309000f44400355200d2040c10341c0c4031a403400c0550442d00000c0d086d80000c4d1008200703545803500d480e08080e169524401c0fa804c680028030000e0010360384800400c00c66070817070f03d064018286c604040c42409055190300e413070711200400050290700c18000740c5246545502807841c07103251082c0c007c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290597625 1250 290596375 290596379
    0x40e0a060c090f3b0a050615090d06021b1608070f0609121104020310030203010e150f070309021305010f05040605031c090f0801060f050114040303030b030307060f020903012928 78
    0x200001e0031b8181c5445001d48925000c12201014010403130350f0403000a087c030703049a4070940e101d40095200006803030000220400c0c0b496520010310881d00914040051621a03d00340303000e079401c00c8000ea200c801e83c0c07440c60300d0400129402c60b4042040b0750b08000010004030070f034200b14603640c82c11a0406d81c094400410000750107641410350781680e000764000c010f40c4401100c1c195641c40087c40c9081c1d84041c01001510080c0a5035801c0d60050080c680801c0e6008190702049800c034400005021454030342006021000c83c1d40d40545c010142102d041c484140303440080f81e1601903d00018100309500c2c2005082c190040760f4100c0184040ba0b42c48a070b140da102c504c54000d04540c00f0f03042c1c524441000004866109051180003061590f0800c0d14091a591b01a0000c0c10015600c5070140010702c45800030400d43d00c00c03404400c0707584e000542e0f01c008110030142181d1a41000000748140d80f035225814120b00c1d84401c03000c0c0000d03640811a031201081001c2c202102c401c080c01d486940c03001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290598875 1250 290597625 290597641
    0x124200a12270602150c041203051b07030312200d0218040908030105061c051003050c0d080a210c020c03060a060803030402040b040e0a060c090f3b 65
    0x70031030010030ba0002e800010329825980d502480c010740304000c0140e2003201c1d400f03894010102c503140c0200000001a28203642c41c5c030f2805042c3c280d1a0141e001c11004a491800d510396080c1a0b001400d030b40700030341146810350350090400d07801e44641c1d681485c0c0d100002c000311a410a400708212240c0103103980c0303902e8000b0584000c1d50010403000c404002007200090a820180210007a403035000c0c1f03506055a090005005258008011b01c8005e10070340020340c0441c0c0100c0c805c20b805140f40120794074009085040080c50141c0c101c1c403407400388420703401e50000b0038040710585080c00c0442c07a2074111000845204910800308101000703003a40342070710880da440e400081c4590181d03810750590f580c503a0b81e62401c0c400c4a01d00e00c00c1c4a6180c10400005005191950200c0442000140b0014010700e0010b51b10740b0300110980d085500f030f030f9248561006e003a00301040350000c120301e60b4a1b6501078204005c0082d80000b0b1080c07a600e00c1c144400c05001c2c0c29020390f803008681761003409070202c0c0c982480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290600125 1250 290598875 290598887
    0xb07122105090303060a14060703030e031204260a02060a0e01141f0b0708040303050a030f020d09020a08120d09110607080a090f030201020604240e03030124200a12 72
    0x19505d8030130500018000350304504030400009004000306050300b801700a40b0f058003e0500d045604c0030b107000400507882100c111840c040d004078019400000d03622032402005040d201c40310080c01104005002d80d81d80c2c19070000e01d0769800400300c2808a20500d440800701d015180c1006800040800d000401151020b90789c5540709580f6218031010038503a581c0039216107031040c00c1014082040421041c030200b4003e80040800720709925000401000f441c44070f00403a0000400240d1458072441a001580352526840c0090301c807144c080c2214035050842e4480d03d108007002011220b8640c1030351000c1c460301d094910401440a0046540e5071000e20b00a52383d5400040b00701c0203e02c200d0004200c0c210116107620560741e06800a00e11526203407113200d0211010755200c8602c1e0140540082c24100c1c2d030007241c03400300100c0d0086403203504006c11010b0303601426038402441c40507541c001203250340c844034001c0c0041d5103483d003469009121801b581012000394018002c014088016a840c0764048 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290601375 1250 290600125 290600131
    0x1b1206081002131a030c0309070e041101080a15050d060e0a0506040314030601051b070b0c071404020702030c060d0b0402182e030b040603060f0c090b07122105090303 73
    0x149482c1050f98480801500700040e00c045240c5031001400081c0d9007140341c10055800c10800400c481d090756a42c15043d5800904480445000c00c1d1090b0703020341542c01c41b014980011b910310040c0480d1185d071008100034081d51180c5449410040c012078140415a40481c81081c04030051351415a828103100340d5400c0281c0d012800514079002a010700040c0c44103603070203228141d6500f0726065102c403a002c12940095600040b501031040c0005171068620010300d06100ea40c000780c000585024148000001012032040c01180100700410060745d01160700c60400904540ea16103910070038080c5001868200c01302a007142c03002502030a0b00c0100520b040d11084101d88448522400702c02c2c0000b5102d41e0001541b40e80c2072251484030281c00380c1c12001c10801d018000003000c0b50789813180020b4a49000818000581e991256134034241d002c1c80f18400780141d01403040c900b08842e80c813000051000d00d181000c00c40044000790340d00320f4101400ca0240d01012080c4014100407441c603449510507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290602625 1250 290601375 290601397
    0x1c030905030a170a060501050d020702030f0f01051b0f070303020a17010b18030c0a090b062a1e060a020a0309050f1b031b1201060e01080307050d031b1206081002 71
    0x201000130030b840c1050003901d080d510107960321800c1030a900c1e4128040d421080003243e16003d800103a07681c0640c03c006140c0d03403045c824000324803400c000f203210120508070640c20464960800c04019030f0428682155200740c0d140c900140e07180c500340300854140010000d42002d664040b00001604400100508000480901c186c0030104026082540d102c000000e00f60300400300f02030402c4240b555a00c071030507158018100e1450004c490fa03000005440c400a5060381c28031b900d80c0c0c5c0101a500300904002881154110a0300c21012207100307964440080c103c2030216000101111f03070b684a034203d110b62079402005c0f03d403010725109000e5120310942045404200403802200710074600000c1910303215015150384070140b4100d0081c003004e507074080c106050f01d648510001030740c83c0d00f103a0194020040d03140078546038400703460708500b0048001c842808041c00c2c100031840c1003004680a5007100043d0425410080803000084090442c1c0c3e8440700182c0540c1c501d810140705140c0040c8a01611 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290603875 1250 290602625 290602667
    0x13030510060608131103010e07080106060216150e101116150507050f060708010e0a021201050d0f120c0308060603150d110d08090907020601081c030905030a 69
    0x1600080c044801d2840348000148007400440d029510140c1d1140c100340c003560010031032159510210f800c2d04c410744241c0c003155011030f20810032002c0030f01c030f18009882c01c1e1003e0980c84604c01c545110348041ca000b480d02c4420700e2810040780500400c52030b1410100a4500c1840d005001400350105480d18510b90040c001c1000780c0c01c400540c40c1740401584c411030603c644040034054116026049049c08170b407244106500c070050342c42c00301f144910030681c56a62103e99810210421011300340a45522081c50050200d004c01c020b00354052410b484040d0748107592140075040580310165445009003648400032456000182d00c00905c2040500035181e007129a101d000a005083c40115031200342040401032a0156180440c08039000324000d1458034540030100000510711541d80d54220740702c00c40090203510b142440e40c90b0301e41c810300c54009407070103600d840c44c0b06e0388070f54191813000c0210301801a50fa6100c0c0c00b035440903020703070780190031240c4840481c1b070060400e03400e000c024000e143e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290605125 1250 290603875 290603893
    0x71b050d0303022101032312030903090114120105010c030e0d051b150906030c0408030f03041109060f091b0c0d030b030d0c0201300504110109050303191103130305 72
    0x280b450b5419040b00ea00200e4800f10411090480c00b041c10205206a914000c075880c50804260230301c0510b004000c2c1101641e92110345030000b41400300c4546042c600c4000600c16000c01060302c0000b24110f40d400e0030440242c04807864216541e2034005440d944c082c02d440248002e01100141d00c440c400003036594959441042010810010f180c0c04a414a5000030410820a820484003941d08040e800180d542440c6d121a599030443c0c2000b1000c4200030000320402042c41140c134090028280252481d0284d802c3c102e0200baa24030520640c06d000b40440004152501d00304450a241a048104000d44600031586501e4942c0305070400c110010b418241c201c040c81c500401d41d058034400c40d880d040e088465a078015500702180c0c1d80380414004031500b0043e180c44d58145c03008804486a4070000f541c0c50207150040c52a000600d1440c10446241c0041c070198800200326030b0707010700d10a0005002d6240500860f003159101c0005456808042a026901080304c19001c056a12038006e407a41e0038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290606375 1250 290605125 290605177
    0x1a060612130512090d11061b0f100207080306090601120204030302010605090a020406021902010c0209090a0312230a02090a18050c0a05090f011e050403020f0d08071b050d030302 78
    0x1001d04842d056115154004642c009800f01301c80d45003101c0c000d019241440030780c0101100303402000c03230444400d0b0407800403440c03040d000744800c0c1040c030b611403421410708023a511884600d010003825640a0717a40c2d0380200c4c0701a0f0080d50002d2401101c00000d56136107441c0e00d0000d010300014819180603103032003030105d8203505082c0203136000c0e0703540d55006020302c0624031200c10305c540e44401c0603411b021080c40c5001c0540c450454032842100344030000e10010350b40e450000d1100003c50050410f81d86025403200c15402034040034a000190b210200170b00e515400e2501e80288510101725600c100071440c0091b05220584000b00240700c0319004000c99522009144458410b0040c08000600100301030b0304c01e80740400b601d00000781b0614081908031050105400e640e06008807450100341c0216003002141341c09125520010415500c09500d40840c5e9070398005401440e000405181c02d00044010b003c149000040003008002c0102240744000e0038094000c0d44522802c1154480c0c03441c03010946 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290607625 1250 290606375 290606377
    0x150c03040e091207020d0c080607080115020c0307060315090e010b01020d0504030506060907030e010510150201020f07111c0b0a061502070e0c040519050a121a060612130512 76
    0x58104150070504e0700307489500708160300300006401c0702d02c0c0c1519a030104400404021f0382c0c0c4110072540740c8445550611280c081c003907035884250380440d880126102101e03100800c0f10021518031707081c0480c640801950840303000d65560050041c0d640f8080004042000540040800c3c400c280c0030f641001d40c0380102100c9500c50ba010240803a03200c5c0c4080791403400d100e58001d40c003031007900e0001040c1c40070000707007403c0d5402950b036421804070352501841170540342450100d203011540000c41c03901102a0040c5094094118040c0c440481260b10307003401c0d211802c02e40c402001d40440310500010307034502070868070010f43d0071700805842e01c0e60120314002c50201a104407030240d00100452441c009442c036640070010405603030302d10240400100b544032a50351007000460381c202c3c0480f2904000912100e203c1d2540000005840e180842002c18080304c0200383c1c00e5510500f40341155984804a05039110703020303801c1410701c00581005442d400340000700242c00d00c10401d072054100d10f02c00b03003d11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290608875 1250 290607625 290607643
    0x8160603180611180a03051203130203060f061306030b0a0c02030424031802061b100c050c1002030c0f09011b03030e010c11151803030103030206040501050903040311040902150c03040e09 82
    0xa10740c050036a400c3c4007012100515030290318050f407a1101c0d0740740e072f01003401c050303003958906082442c41c0c0501030141740c0070200c0311b00080c40c50300c104061403558880d19409000940342ea000180c2e170301001ca00702407090040350302500710391142d212403c40c441e41c0b00744040641c0300110300203841c4c1440701d804502042418500726800820300b5003441103107602e141c40a881035500b50304a1195004a44100289000d0614038200719207409890355605440b003418070300b15851640d40f00d84100100070000e402c410540e4a4622401d09503034640c45600300581d5060f030380b1030030310498024140a0340205903042d0010888034000d500280980c8892110541c0c1d20611185054238513007000c01e00000c01c41041ca42c00d548240961851440c00160b0b210a45c2968002c0c3c0090b00180c00010070801440000d000b82600104007000642c6400e02d5170711502491200720611910071a12440701009540d40c0348220034640e84844852a56010211040c566a601a11400050581c52400a452100041401c541c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290610125 1250 290608875 290608883
    0x207051507020103021803010f09021c1a04050a0507090203190902090106050d0624020d0801030b0a020a020c040e2a09040227091608160603180611180a03 68
    0x41020301c280d00641c040e4000081c25100000c9000c420341c0345036824010312002d4100c81d8000114622580140028138040c0c84c148801444e401843d04006421040025681404c2249a000c40d8550345070590421320160700241061207040c0001c68603d499030b00460142d43c3d4007910007070401c40c400012050380c14251001c1c1d4441000c000410080d40070304001c0081c1800c00b000040d113191142112007480c0341c4040301c00d10801010701551240c58041003a0543c40c8150b04102005624640c1c89011291005000b55010b0350089004c00100e0300070441e1804202d03006009204100004810507500c421400c4143d544000c2d611a456400c050791520411940000c0d02c0080c8030b645070340030301026102d80428001c0c003041c0514800140b000600038240a080003001600c0504106546d50709642103d400000c682d0700004040718111603a69032850440c0c140d4100420380c00c0c1e28017500108220b2000000e020682800c181b540b462103208000e00c4044034465402ca2405090400c2c0700345101c035400028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290611375 1250 290610125 290610127
    0x160305160815060c0606040b06030c0702130923120901020604261c0b0a0e2a04120b011a07060207051603110301050a0507020c280308040602070515 65
    0x2940c1948a4200c070380c1c0c84650688032012031512440442d085502860940c145a0800703818081589064024032104031011a01e960075424150500a03542c0b040c00c200034868003900007101c03d8010190031903440715800c2028a51204c0c030100c4520300840708040d40b41154001c0d0660a10140180000e60b0031030081a402003040f0307a10307030f03480105604d081c1142c0070124105016a82c41212040e0050211030a404d0800601241440220058900c0c00440600c41c10704200700b4008801100c0b48242c0c08099801c00c00407000702001c8072a41e094800c0700402480030005004141c0c10705050303514046520540c800e91781684e0354458260703c030a40040804418208000c403001007100e6801400016000d4020b03244044048104125005035550040320140f0f01050714512925003841940e903c034007058000d00107803501d900001e499a10000c40c0138401e00d5140c1c2005010758228800c080d40c00c1c03945403807610b030a4903410032401c6038100d8401c2d00010321400e9000301c2d01d8103141024800c4a15581411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290612625 1250 290611375 290611411
    0x90108060712021e0f0403050712120207120209060a03021512060d080a080403020f0304030c05030105090606220902060304030c0b0903040303050403061d01141b0f04151404030b160305 81
    0x104c200d0b030011040c0c0e00700c5a0180300210100d81e0920045008015030b01500703080c0f040c0c0d45080f108400300c852005055400c18413081004214030a41601c040f44e040351117110700e43d00d0704c0014004203155000a1740010921780205070f2240b070309000342402c09414040001c0795a8003810452003112008000300400001d2040302090b038010b05200360001c0c400d0041da250360307403078188903480e5030810b500a47d90340b8043c1c47c04000508080c8101c0342c001c2d40c90000b4280070326000c00410001803220000c040e00d1404078540b045e0407031207644010394240e0300402083e6641410b05005044420042098503e00c2d0540081016880000225002c4907895180c0600700f41c40c580b0f400c4000d06240d526184400d40201d00300c0e40c1c604081c494401e07403070081c108000040c100441240c41c116500c408003a076007042081001e41415252042d502200c44014080070740d140c000c0b00031640703945c541030411203100001c10007201f00071203800840d220342400720520754083d1036048100c082da4000d54001418444c85004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290613875 1250 290612625 290612677
    0xb040f151517161d01020705060a0306050901030f17160305071403071a0a150b0f040512030702100503130f082b0e03210a0b09010806071202 62
    0x8000400707211800d100903904032020080501c50001c45442807400301c81400d01c2162500203200000107042d03507076400c0007850b151001030356460050150b00d105040c0890070f112564802d42240b4094a406011034031503594902d80410040c0c2200001c030342c80340b41c000810703000180032001e5540b442040d019078403001d03100d0744090b1090381c0051002e071048112145c200c00b001c42c04100614101d071184007c9522000d40800c040001c0c04c010f00522529414041c3ca4180f450000c01554140c45840b0100780c0d0390820500c080213148682d1b400079030805454844c2480c600c1e4080040c2045a009842140c00f00d001c1800844081c0310488451080741100510346000c110740c034900015aa224030358103441d010200721101384024405100681c00142c915108200a0711030180b0440c00714004001c6040c0f01c0c01070042080b04008400703510100e44810009000f10455400c044003103600901f20a0389945c481c50816101e007001c4031001d000c01c1d200505401000802d01c00c550040e081110180c0001952502c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290615125 1250 290613875 290613899
    0x280f0509100b071a04111008092a030109050319050a0c06020d0b09161d06030412020304030f0605090c0a03170703050f0c0f1516030228030b040f15 65
    0x3c025100354101d14182c400c445090a80140614007441c00e1201e107020503800c00000142c0311003141c08112000d001c0c0b1190042c005203a83d008680c0d182c400c803010701303020b541d000d22441e0b80030707425070540c201a000402d1090100040562800704c0161b1003400111100035030b118420700c038410f40040e84100001c804140594054585c01404501c04207040b8004000126100e4003543e000080c040c40070600180d40b038002c001c40740d92241c0b02040031091551078001400a000090010f01484040807441d58024401d1080b900910752000301e600150116052040003400c04881c984101c5c40364408010361442c0c4404c2a004484d44840ea84041c10091a6181e0792034002d00c03030403000e1020602100e82402d001c1c3d00030700a08840e0300001e054007510000144d190170843e604000b405e001d02024810710b403881c24200450640c1078100584e0f80c40326241544410303003841c2007190303204000b9401400e10340ea164110411400e800c860500414030614440021148000040c001c000100041003000c3c0300814 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290616375 1250 290615125 290615137
    0x15020615030c121f050a06080a050606010e0a0e0705041d041511090d05010506040c0f080708040305040803070308091c020705101716020d0e01021506280f0509100b 72
    0x20b01500c81c2041074072154916071004040140340291900304200550b0b06e0f61050100a00003000200403078041d584809494503c050005810441203142441c03003902c801d0006001002510085109890214030041060704240207241d051a100020a00440310302414207010b550001007400c3c41301105034448004181078404210f071004180b14000250b65a50b8610800b280114008209440c0130070400007241c4a10f0309110a019484491400c4180e1213086a64018141d05241806440340e040c180e070f2601855202011070700c00010a03904156005400b07c0c01244810111080d02d031403140580913002d081154500160b018150400142c541902d015514031950f05003c221040e802e9000d034030b800c2003110200400c1c0c12607580d603011603a0410049814a41a140400200051300d0001f911415880c020b07040c0c0c00301104c0401c015941c0d404d005c11000095458241070071a18405010303030017945128008400711200c0b40000c141c200180b10714480c15a03814000e2480e410204421120780110f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290617625 1250 290616375 290616409
    0x5071716020118031101050702030f070609050316060e1513031d04090507030308061801060e190801150503010c0e10030209060a09090e010908040621050115020615030c 74
    0x2404440f120500d4012103034880f40d009580300c0403842c0c412071001d400d50300c02510050465200b045090031031134040381507680d41940040b000c40c00c21858280a4a98052042da5413144076400e6411010840075070720443d40780c4034407030a580104068001d2401d81420437201010107144028500700068071500180d40c0ba01d41c18401d02c4141004040030404681d0030210480b007541c8948000d100b4160401201035000c1e02c2111410040b004113071602c01e0010042c881c000134001d80140c40d481d103139280f003544150000200b000d02403071503803001614040c00081890410310f0310030050114440c1010701a81440000d19220030389407006030418800b11034451803040c010154203000408031b554800000b412082d03170680e501d1400d41e080071340c1c2c1003c9030001700818103103a1500341c0c1040010240e0050300d040f2a5142002c41c442440e00340065186840c00148414041c9844008200c010b051413000164081302e0382110501d94540304004506070220115950591000501d800b0038a0000b440301900320700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290618875 1250 290617625 290617631
    0x30210020d18081c061521050c0316031b0e1801140a1211010509151207031b1704020103020d0f061811070b0631050717160201 56
    0x2c4030414803074829092801c9070b00c010000b4541c414201e9549002240c807200140410440b0303d042610070400e041d0058880501c60604407040c41411086c2801441c1c42c000e1405000e9880e20b00d440e900d00742c1c0700312081305401c02800c10341b4400c42c1c0b00784114414518000071132440410011425034103441511210b82e0300400001d000c4805108089070b071070081070001804c5680b2403420342080380d0a1816007080001d070343e019541502140c810907288915031401e0030b02e59601c1e41484042803d0310083d5a0002e16114001181001b080d4a00302581c4144041d6501b04211641d0362003c0c10030826407080440040d24051601d05a500440c2c0703429005881414010700d00040122140180d8156440302c80c00c1325501e400130004080030150013441030003207038400c01034502c600101110a000e1240080e0030000c00d20b000a9480c0c5640c00440881c44000018410081d40c01003025030301151010300e00e46113400c03c030102d07040901455001d0042d40301c40c0750b0b10354180c1c5c0380c03019059503080d00300403103046640b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290620125 1250 290618875 290618891
    0x307080a030201090515132414013b0601020a0b01030b0f090601150c050304030501020418060e0f0c0304051c020708012009120a170711090103030210020d 68
    0x26042010300a12842600040755000c180d0030030b01e051001c034110444050b1080001c000000510180303c40a90703500c0400e400d92044a211007800d428083c01c55041918a0107000103011040081c026040319098254501e8503c040b405462134545042e40c003402801c004891595505c22404509600c01410300c11150000c10079282d0700e0307a2020170b0b40151240c600003414811400c0645c12420707440600352005224a500d00700f007489541500407000300802c400340d43c075101009010700841e4000c0d034201009640340c9072a8030703044507403040050900c21007034900b440000382c40c44480541442842c201403070224a40c1e0703002031601107900082003145c00d0b000780c5000341c80810346049441d000d21040e500610205040c1510750382140c04141c03154400400681c100f00456440d501140c121104c141c49044030f0b00380380745040c0d20b0680000030003400890a6100001001c11020140540b0343c01801030021003440c4e2414070806031000e000180040e0800c0c0310f40e08403800b040e0020101248001c1000815a07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290621375 1250 290620125 290620139
    0x403020108072d021b130e07030f0318080c0d030c061404200406050d020607170a0302030615030f0f1801240e07121104120507090e011104140307 64
    0x100312892060f103454840d0002080e026810000c0c14001c2250203032055842c0c141c04000303120381c1101c1c010040c1c2c60b500d074006a65049014050040110b621500b05040009181b801420741c8511480d010008807100c1800202c040c030009020180c0c1030003801030308010705540c07021140d40c100703030001385c1c1d501e80c0710201e440300d0100036041e0034425801009014034a2010001c1c0c1162002c0207031041d8030541c01d0010503c01076450450000c00d050303040b1181669124145002d8070410740d4110060000303080400c8000301207802d6001948103817011100820b13080c0b034501690010740804c0c0e42c0e00d071480c2240400201c42c0c02081c00c07240e40003101c1d00c07611010306503101d44160a489000d4105488611701c401450008044152940050900c07850409058034050320014280c0c403200c4540303203c1c0b40e103034000314111300000d4040b40c000d4080180c00c042d6059241c14240d42d01c04051140302060b0b0316284100100100600c5140c001c0101130403d04e203000d00d440000d6410219480c0c0c10b940c940544040000c0b80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290622625 1250 290621375 290621417
    0x50a0c021e0405010501050705030f031302030f071805010305030a030c050c1b0a050301050c0a05070303020d050c0912010c050a03110405041e060801020f0a0f1707031a0411040302010807 82
    0x9540e01c10300e00000701000c01070209649040c2c1c045410b0120130310074100004c8000c804c1d1145900600c5499449903100080c00e079124240e01d001a40601811000d0000e807440418a5000e6030065011581c11400300703010041140d07030074440585250814440200218400d42041c8040740302441c200e400e20030274500850401654160b0818030301c0c00301d20800c51500b005034504000b80402c1b0000c001c0361400c1113840320b07184200c55032a4200000024010b04041c003a070305403020400283c00070002490a003540400310340c004400280700344101c039205c051030342050041c80269400e5a641908240242009801070000d0000494003108140404200d5484034030451030410031002c2c003e1010014241c00749e040710ba00d9045540c00345d0040005170b088009080480c1e42d4040117150028058030103000c100e8a910040703124140300401c10092150080c1d040e08200340d030000362030f03051380c601000d6001c0100b04d07071030304020541c807460500007007001d98080c145541d8816034506107807800028072450007c038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290623875 1250 290622625 290622649
    0x30e1201020d06050909030f030606071406041218081906200a0906050a0206041103010e370b01030303150801020a020a0b070c03080c0f0d020f030f091c050a0c02 71
    0x40c90f680e01c0100800d1500c012682d81055528010310703d404c030000c5000b0070714400107000e24004c3c0f10006071481001100c43c82c0c500710132103100540f941404c282c58864000340b00c140754000020f01041c09034501ca1048000d190444030118001d24a40c0c91503803006c214100402805c1d40d4013075032132070001d0341142c2110030542c0c00d00070100c440d0369611500d40c01500d6003003d80c2007202000001e01900104540000f000e60300103802600f40c000c80d02d0b40000190240c408001c5c1d0107141d01600c000120f40d07030504011b100c41003020600e46184c2c250580c2d20310040304603480020300b58903410740041010901a60040950036000710803050003e8413441040e09980c4298100b000503848941144248440a465160007008603d81405501c50a4400400031540586400d8446000061102c40c01d02500c0846d140310500c00c10030b5403180c0010521101c150030486a1004035805400058010080480d082034580082e00660000300c2c00f5000031552500078000300c10500941514000c096030301d646091107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290625125 1250 290623875 290623897
    0x201030b0607080c0109050d08010305100f0b1906091e180213030f05010606032d060812090a050307080a080705070f08010f0c0f020703020904060f020408150c0f0403030e120102 78
    0x11b00c45414134001e0f103442041400001008000e03001400051800b1890002c83e480341c80c3c000c0354440312841100c0081c007291282690210000c1c4030204035003c0b211010003201d500b6211101c050360354516910000985c401c00348880a6160010300c848820010843c83c0f1001083c4010b00f0b240c1d02c1c180b00c0050100740d80013030303401a6004900e00204242405078902500e95450144500c851190385004c0101e00d585040b40c446802040e162f0719840d00c0d40c4a04020b00e0141c0869918102e01c2c09882c0c070503440100803a000e440118800b190904000880404a070b01c02c00041c9966222601c5034032a64002040072582400f69080004110035210038031000341c09003000005a46848a0190040f5065080083c0a22142142c1c4a01e056008101c1c02e01316078060311141d6555490745000130007407240c0151035405074400701f404544410300003074046010300c52118a12a0381c1703600000040c03900810000101c2c00000b0841840028030500721001d00c0c04001d415510f1010701145141d00760707040240d10607 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290626375 1250 290625125 290625131
    0x30605070809060a060e01030201300b1503040503070f060204180f0e060405070605130f030c031205040e15180a021818011e08070e041208130201030b0607080c01 71
    0x90a0280800f540120b02c19104000d45442c18000d502021303014440a07050102409030404041aa0038004020054041420f141031a0749820100100544501903004d00d1580300c0040940303a625040f2800707150040021420308005036250300c41100200000c681171a028000040c4009100791a151921990380021030100c120504000490f03404100744512030b4000f1007800046030011410009a42c1c481c07400e40c0e980c4507041480035164075603030705c45800350104505c0001840800b860101c203882c4a0074004e4401703030607008110b4590059015000b0045c0009010489250016080c0503031180c0260815600e10041c2c02e078044080012509003e40c1ca030001100703841f50307554080c4070311f60082c1100c801d40414070003c94101540014010028103009c00a02110100c000c811100010917105c0111603109031101c920b44076000d000c1c0c43c110358461242c05c041c2e5880740074600c42880707130701000103801e00810f00b60011005014542505034000008100f0000440c1c00000108602d0050304004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290627625 1250 290626375 290626381
    0x50a050109062405120c0a0b0406140f0405010c1e26120a2313120912260f0301081b0904060507050405060406120b060a0c060203040c0306050708 64
    0x2815982c0a020030b42c2590810b144003402c501a40a01e0f2081d00c40030b88880c0c2810450100b00351030010905c002a40c007202c0d404002511200d00d034000c0054035100d0b5180074003911b02c01d42c180c89034051142c4070651402c00707000c1803240c0e520612510450500a600d41c0f500a601581c80c0860600d650300d055412070000c006640480c1c4002c0c2d070010b40103102403c4245480c181011800c124800070713100d40c13003035500c0b1400351107482d002a03102c507807041680d250601c0604011800300c841841c0d01204a44041c0c58101c0f142c070381c501650081c81160301450300c1010070740303040e80c892138031080d04000f404250341030f1800da4814200b0340d4041c10a40d030803d4402681c1354142802140b038000b0301e40800d400b24580760895001d84d00c6040407150441d9200c1c40206190300c4500041d02d045c05541c1155070825000b040c001070080d440112190301003044801000014403010034000903115200040340032440c14a054800204030381e000315806805200030119007901c9640b40b01c01d6400a031002c100040d070110038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290628875 1250 290627625 290627633
    0x102030d0609292103070b0c12150d0605040303061502030403020111070b070b0c04030210171b0301060e01020f10050f01060801080a06050c0c010e07210506060405090a050a050109 79
    0x40089107001032440c15101c14450380c001340c0c46845020400103416034032460301100070030400076910305540c445050b4080345840080800030350400c072417900052481c0b00c041030384040400b0400c440054060140100c0d0703141500d405020300b0000d40110b04243d0356860000310002c0d842460703020082c00e640a150f0781c0b86503000060a03524103604406550b00103900801c0100e22500480d000f580e40a014541d5035a5480c20449843c060350b0301c040d4000740302220300aa02e5074032041400b07940034040d1a08030f00d0380320707101c10106201c0c0300703288170509003405c00041c88142d004070901e40c000c600c148103d404000e0039407421410481c00700d503c01019030b1140d05012400000d00d6015005d403141d45450303141c2e5031421404c0b030760b42d0184040141030160b490f800b1034100d003607510071110040050070081c082880282c450a0352401d00703115142d01d070803146440d007c440c49889080c081890f08040100a035480d403d041000a04002e4485002c0344190220500084d6040c0500c000050250000107406401420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290630125 1250 290628875 290628911
    0x30b010510050313020f18012606090c0909070f080607020c011110020906070f0f0201021b130e071d1f05060706110d060f05040b010f0f0e0102030d0609 67
    0xc000082c07040600c1000418036580703004008964045418a0007007003c40089902c48400c12152045000c01c4000405e0301140290207407101c0c40000402c84081d10301c80c0d285a20f6030b405807481c04068010120b1100103140c60046190440710300d0064034640340e41c9540400d10026941d2128801ea0812010001180d405110040d0f4220080c240040000504003000303403201c3c032501c0040e5859034085155a240c0d220007043e01d075855400718003407001c2c090b6400c00b4008034140c1c0c0e404074014410180b68140c6d5041700c1280010901c00604500d100b1080504107c015040000e034024051140d9200000c18001d01515400f00c4141868104a036040c85800150410110000c46110aa400f0000c00098031441c003112441c94000c07a00007940708450140c20715a1045840c1c280c245c504141000c500713000081140400c40d24203d904101c40b18500e40152840074039184410b020400e83d0750f100004a00880940b400f0a40502c1a68500b45506203403208468a9400c410503081c0e0703800c100440700003a49 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290631375 1250 290630125 290630149
    0xf141603020105241f0e0405040f0b010f180f110a0f1704031403070207150906020c0d020a0303050f070615051002010e061b07060c0201050f130c050409110406030b0105 74
    0x200d42201081940000c41d00d01201c4000c60581d085c20124482e65191141a58191000300280240414106030400202c246d1140d08150f500c81080c00001610284111440d4112102111050108200e480320309004046517042031941a8841c85450111681070004003894006a200e900050740050b0740104001200c0e1543d411401118080c0404250003082410841d00d4a01180d580da03660000200d0030400d056008802e10100034a414800e9a0407a4090f000c0d24110b03421500079040c0d05003000a00e00b16040d0294222031038540510100741304200602411010801a81c90700c038441d5280406c84c0c2807400038000c0012031050520040c07410b40300d40b0709421450301c000c1c4240f4040080c03407501d900c2c000d00520021b000358028102401410420f03a1241500904104450000724030042c1c080e0904641600c481100c100000741e0b0303031300b950003a04840360b040070410b5070190800051100811040c042994402a0010a41c01556441c001c46000d5071140011030742552408040c890350242e5030f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290632625 1250 290631375 290631421
    0x30b01170304030807020d0501090c08010608010c03110a0309020315040f02180907060e0102120f0409051006050a0f0306150e0108090a02031b060c15070f0c030f141603020105 77
    0x2c202c01c0002c02c0e0300d00255031031941c040741d081000104900c2d02d140103000c03d41c001440e00c81c40000000d03c021043d4001e0088900400084c04120080c8a04808440802261040030348045c8451100c00344240e200c498140d201500311608a10a4000d036905664103d40440c1d40d641600894011030038115121141d00013002d14016803030070840351140d02c1c0d43c02401540108483c104400c0d2050703100f00700c400008176201c5029982d840c2c0341c41403c011644203019540c4442d04203c04181207100c0c58a2440896080303549807820451040011a090b00d2010b80100405403622030201e244050044007903034840250315202d165103580000074007000002020301d1000e400014000b4003680b1b01040300308000d035040005409040c503080026125000d5040503e10702e11941e00c0c0e11404803817480529026014546038640041210a42183c80a10400300140000c0d080c4481443e401d00030809011001e86417a40e1a05020007218401021114a482900180e440e103052000b0b06000e41004e00001242d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290633875 1250 290632625 290632627
    0x31a06060304020f010201021606051006050a0512131205030a05151005072d2114132111030d0503061203130f0e2401050a020307020a030b011703 64
    0x21010004446010080002e07006440000d48410145c1c030070b5044a0202040c524000d0b03c2c2c01c00c60910400a00c0111040201d0700054400859490302560a8030b81041555803520b190910180c005440124040c05121b0b030318900b120010002020481e03508400b10055641644915180700244199030000e0603050424052103000e49080c1c84550203142515801c3c100030380d403581a8508580c2075299000381c4503040300e841203100500200c008401c01c4403406003210001c11403404644e1001c1e0689000e054002c40e0b00f09000d0000b03c036541010300222140c034048124001e5a50b8111041030344400b107520003400841c03030a50100031400f8001440e01c041500100b4000071a8a406043ca2101500040c400d170052882e008084000300229403022043e0010072080c81e82c0c0b6044c0080d038040302d01550000543d00070000b9480108860b0214100105920700c4206608030001541c03942c0c00105811f045001c204132281c09a21040081ca00a40c4108814069585400300285010000507145009500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290635125 1250 290633875 290633881
    0x412080405030406050702010212191709150705070219050a09060f05190305100b120a0302070621050c0414030609101515080901050702010c1707090803070c031a 71
    0x800070541e801c0d6401c130b0905946e25821400140c4c40c00ca11a100014004000a03240045120750720b810071510303030325445425410483c03040c80d003103008080b280100a540090075000c502070501c00300541140650a0039803400d0301c541c010a000d14a842846030b0804800c000c10030141c200000c415004160700c1e00c0422215086c0540034070240c0345403040d24030850900d0609480030710040c403420000c645c40780485803911007600080015184d1641c8043c81483c03031100006040002140000038940d140d8007500030f140c02c0c00410f4444c03500c4160340720400a0113880003d111805441114010b50200c02103c0d251450300070f5028003081c2c54410903010350444001d11071100f0f0b0015608201070600d0f0004982c2d803801e1000605120441da00c50800717011500c0f140c198a035000390703000d40900c040c240248242c0c5d07210f1405a00ba511080340402c00501001140007192000140c0346400c102c031494011a440e95940d540751a6811029050303d5904020004104008400d034210740c0e0f902088555940d149 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290636375 1250 290635125 290635133
    0xc3014220c0509100e100608040b060102071205060601090b2d0c030408060117030f040603110f07060f0b0f150904060302150a02011b1b02010207050901120507050f0607080c0a02030a030804120804 86
    0x10006070000b0b00d031000440120f031240c1c0c00ed001d4000904020510210b60000341c0c1892070380c6a20544126022413141500450582507000032a0340320780704010782030000c24100d0a20b9038280d0032401c21000100042c420845400410b20003400103101d00d8004000c0c6506040044891060b25480000c5581c0100032145014043d442510115102c0d03007400500755099426481710f61081c0d0740700450800b0005403c00c208561507001085c1203c00c01d0081003903a80d40c2007806641465280b11640c8910715044020f0761109850003031240c404090004618680d481d40401c5010002c000b06400d905c0c808900c02e8180c0303509103e0310456083d120315204918421810203411809130b04c0301404e42805030038103c815a402008038400030840500451581e45e5207110b86080c00e04544800c81d0540501240010b6500d0a61b0301e00f149154000d0425242c50201d60355411340368884030150600f401103045140c00350b0b40c03d003c1c1000003406601e0b41714881c607040c07414010307001c0340c4180c4009101540c0c05200100f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290637625 1250 290636375 290636387
    0x2151c0903080105120a060603032c0604050d0303090503070c05030610050904150e0f210304022b0803011e090e0c040c3014220c0509100e1006 63
    0x1070340281e0740300f0411381703c0032205410400420701c064801401c2c20800070815a0040302d0404030b42c40394610380aa255002c2e103141e000c91581010aa00c603100b80002c0c011890580e5841d020079100b4100000d204005170b59075800c5800010098503441d104910030001c504040c45500d503c00300c4149841c2c02c040c100800240c82ea0f1020300064007072840015103000c400000d0b44015450758140d0100d0340c052848101c1c455403818950032030310140e5040034589a010001d079003a01c2c059a8000e00303d00c108404c100000800c0354003100c031640031809812040020441940046000e04003044042c0307507106803500c08280301e80c40c66202d0040c4034540103050b10b0200002c2910480c0240442d17020821002d0600222544d91000d200706c051660035041d801d040c4040d840707642d5a2011003482c248941800090008107402084480240f591900b49000244500c07a0710304040151146001c05825602c8070042440e9a10443d00c900310740c88408414000c6642c080e00c0342d9848603800c41215070060802c0001800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290638875 1250 290637625 290637629
    0x301060e13120c0203030d0509070501020102133308010e1806070c080d1401050915061c02040f06030e070e070f0305060f030d0818030a1d030a02151c09030801 70
    0x1486000c12030448803280b00390890103c19400808980d100c401240b8803000400382600c50800b14801c08200080d42c3d40107000b55511000f0305401004681d240031442c070000800409030400741100c0c2c5041c00203600c0301081221480c2c80070340d120002ca6041546040542c140500509688520200c09a86e048030004c2e0b030355405a01498180f01c04140c078586411980219200e0801e154241b0b00d11060022007203200074122141141c1108541e16807000c508a282c855581864003c0410040040c0501c402e5080e40540c84c0c041c1c90043c546071395405071004c000a00e40280c0002a2a00c80d8506c1540b0208000c0010382035801d9032481600300350501806440c0c0c089441c034140740e11507000590031380d40c18241024808025060f03401c1c84220740720040441100311800e17400b0000c05810300c0403100001055030020810303515200214400c0c0302c08880d1401031204180d6061084181c140010703114102e0306000c070314943c2045602c4000307612078a05a482c10584001d1a40d10344650240880d50200305181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290640125 1250 290638875 290638883
    0x708090d0228060f020315040b1020070315050105040b01030b0f12070b0f070b071407140c150901020c06120115021516030605060c060c092b020301060e13 68
    0x42e5041502d0448040d00b03200c040500e04030300c04420040340b000c0d207480040440000311400c2001c65158010001903440c1d41c84800002911800c1c4c02134024048046020006000d8040380e5030b4507500d03030341c1d03400c1451031400c070b0f50b10075484000400c2070f030501d4080d4005050007401d060040c03402000105907240d4403001440c1c8140c0006028a62090042c0080c2c3c002d054500d0145650b070351041d11340b28055100b030704100e80b01e41d407070000164203d103d1540e840c1c0e004080d80c80c4601d00145500c81c1111140112592030f45401540c103d030001d59034952090500811005002c4d84130703400d00e0006810092040c40490203208200030b168054155038140714150350518808482d4401e41341402c80c82c0c01c0c440340891515080b44000d110344184c10340040700d0b607010550380c203100e03142e150310600010303005501002c01e044c2d105001080101d45000082c1840000c0605810510b4060081100c480352080c0c10500c0912005000034041d0b00b002e004003005812700340b000d03d00d0f5090803801580e04810065002d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 290641375 1250 290640125 290640193
    0x6020d0e010c0314030a020d090503250803010504110d1805071d01030f0302010209060a030204180c020a02010804050c1909050901060b070807170408011d01050903160c0306050708090d02 82
    0x14206e81103a4180d5256103e0302c1400c00c003131480e514007130703507aa800010701a101040b014440d503406904c010304a00302075400008203003164608018040a001d41c0c1981d08201c5030144204400c0320340030310501e0310615451001e00380c0700c82d650402d00e0074108250000300703582512400464500544c0c2c2104c40c110f07a40304441075007140782c50808a00a001d02100b6507880880098140101645600504262000220648450705014600c002112011580c2c0b80168200102d198003560242c0b4070158081c0c028030541e816183ca9900140607245136030304c2c00c0d0824061030820b02550b14944241c40d48843c0c854001c01c001070034550141b4180c01303500707001804090002800da08220100c0365404c0800554503d841e1503a444070242c9000e80700c020004d64003030001c8004111801c0c014002c45000d07003c035070051841d0544290040c64807005c0000b060756481540100000000c110b03104952040c0e0266441e42c54a0520490302e500f0402c99614030700440d4004c2000c203005080c1d1001c10f480e0052107160701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 290642625 1250 290641375 290641381
    0x50904140708040302011b0f0c140105070f1107051c1515080613030801150e031b09010803030f01060e130f02090a050105040e0105010c0302150106020d0e010c031403 73
    0x180140484000034048400c140c0140440140c01180319030146210760003d02c00110791030380c14405094859074000c00030701c04620b24869940100035010005024030315101036007000038201c07403c0d14000d5801c00006450b4060b080441a0701403401c107a03400c200406818031340c1c135240006d00d44000e101e0610b1103400e903031001c600400011600d208808509144140318500b03943c03460060701940c030b210700e01c3c45006000c00580220b07609034000354035a40c1a161001140d09103003854101d84a07207005642800b00000b802c0c600c0b96010048140c1c204d0340d11180d4179403085240180200c400d0181d00a08a591003070051040e5040300d01c4a0304d05460103441c29041145240300001c0903180078088030314805150014895180c8100d0f0010315441100b5680000c04544e210300446140c856486108074004043c40140140e42c4112064100316000388122144911f4084101038034141c02c0e0302201c0940e2141004000382a00b20f403698102040c2400c000c0d0340c18260b82c0b0040c01c6908904000d0384910400000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 290643875 1250 290642625 290642629
    0x3080a0e0f071e09052a0a0f03020a0309050102070f1e0b041514040b011716050613030206030903040306050a02070206031b0f0703022a0a1e1502030a1e020d0509 71
    0x8000010040314500b4042401c06c1d03101225010103100e04070116803142d0500035140c506460490312080d4640c2d80350015401004800c40c020b403c003200300e400301512a680400415024005070044030b011b81d055501c0c00300075140c071424400300840d80750090101601480701040300003417038962040d0000603100c0d084a6645040c40140b072008004082c80407928148401d0150034952181650701c0550b804040d8545c10310020390390080c8501203d1034190405040c02a400d000d80940844c0c40c80b400980001501d9500045080e04201c44030f0b04250310110f81041841858020150003840110045142100603000b0610510000300030034403002051307481202d9030086078103c0e070041f01c0c4002640c0e21100145002515100c0c0032843c40d91401c030b80341514005034031003081003c0c0071000828078040c85190800402000070402c14519140c104a080080d001310b04100c48050b02e000c81d4040e681e950f04010003e010390a408400650001480749044489500010108591035150916a45403141000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 290645125 1250 290643875 290643929
    0xe0a060905010b041a030d2d18060f0e093d0f050d1e020a0b0306090a0603020f0609190305010605120a0308060915030a03080a0e0f07 59
    0x2008585882140024040103610031000d8910481d414800044042840c1d000901c14056407a4580c01004101e00840c4c0641012414070600f030070b40c24019501140d10b81840903e442090010480c480013401c3e0f400d480301803440150901d070034803004540c0c95000007071070040703100c682c80d010f0441034020802003801140c41001b01159aa000100206404122a18080514140c0d032803904420008146060712030b5036901550405000038884510756241c01000e5907551054903c119522501032016840d1250900050102820b0860b503d050550900c030301c5000050a0000181c50031109200603520b841d03915500c2002101c1d440d4945540c5000aa41c1400d00c14660414401c150400020000190043c0c011990101e8548082000c82c4481a4460101e0030000300002c201400040d507618180c1e43c260341088203000740f40d01ea801c585020034505501c02e1790603000b1030702d0001001001941d50041c001502c182001910b1100c0c2d024166a0b0394030b401d4002c2c03410f43c4480d05845032030668400d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 290646375 1250 290645125 290645143
    0x30f07020f040f020d0f0203010b070602090109180c0e0103182603010f0501020105160203090d170310082e090f05060403030902090a02120412021608011b02010e0604060e 75
    0xb401040451a2600403c000f50b0044e000d4107416410410029162103040c4241c2e0304a8503420801d500c1c24483d981c525000b5840b2420403414440c1c00b02d808602100d504900c3d008800c2c441200080030620100080c00051400002604150a00c168502c100c3c0e65908200c010721f03072000440b00b59110f41e0060000c3c00000c44119101d40d1804800003401854060000d4110303042a00200b04d183c841e104900410b00c2500ea2071000360703004014141d42820b120030030024081c012503036034002ca420300003080340903881640d01505106032840f060180202c00d000c0421003000034041640c1001c0c440d00d05049030100c040464000941e80c1301540144050b11004884499102c0c0680c1d601c0d10b00781c80c018004040e0090241e0080003c5000544408054400c03224000c40c0d01c2c1c62017215589650716144001d0340c01907254114061a1444403000e031360080f0403405007060100204040101041682c44c0900d800e820700c1c11a030601910b0b25000700042607282e001900030754041000740a00040610f010078038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 290647482 1107 290646375 290646379
    0x70605010e2203030906090609020f03030a2a1a01081006140607171615270602130f1d0103020307140109080d05040521030f07020f 58
    0x101180b007803194400d16004c035001c2500e5440700240c650202c0f0464101e91500842d90442c600385a11410405054004504080b480340b0300a000c580510201401c902c124001d50486600001c00c0c0f0088507001001c2000950340e400c04074281071024401d01711140281003100003801e58038020082200c07500e01c04191354607840020030496902c0f5100465414071100602403c058291015000c00900c110031101c8045041c14202154640800790904e003034030345405003280c01c800e041150f4500c000301c00008500d030f8951a040f0000e12641d801c412203031300e03900300001c0c2ca042d811010400303440841800e44a01d02442c20011304000c002e0000a40c5500909828003070301d4042c0a40c602115414504851020f41d01c045a6092610a189520010318005802d100c00e0619600000d42080014070f414180e125112500d0385a005880e6209884c1100290000555035142d8000313201d8440 = true := by decide +kernel

theorem cover : BRFrame.Cov 290467625 290647482 := by
  have h0 := BRFrame.cov_init 290467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 290467625 ≤ n) (h2 : n < 290647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
