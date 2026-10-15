-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:52:25.769785+00:00
-- url     : https://prove2.me/submissions/138e31c6-dc4b-417b-bfef-9ddcc81a5fe6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 811870503 ≤ n < 812050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 811871753 1250 811870503 811870523
    0x1603050601060f050712180902091804031d12070305030d050c0408030f090a050405010915060201020a090e10080a0c081b28090606270806070f02012304 67
    0xc0b40200c9003100c4103103d02c4000755081c801000420103504240004180c1414095801c04003002c100c8004685540101201540481d101075241804e42c4540115203003130096420f01c1c07615582c0642265401c2288040e174030340603121380407141c80f031081200c40c4603185d0089a0075a0780d03d00e0255030742e41c40140c00001031070a040100f80d1015110313064400b5a12290301035401d020111400c504c00da04046e1483d9400000c607540044c041d00c46c3d12034140642404280070840000c194007c0c404002158400011a03104012010307885a2141740d03042903d043e02c80400301c0e0303101c83c034241110703c21030707000701c0c045020f250001c404100144007094221848201943d2444034203107800c210000d01303183c3d0213400100b2464500201c44011a4a0a8441102c00041800d649411704403045990721f0300f0010104101100381c54a80c0300e22070354910211519040c058005040500f03640e1600e02c040c1c0924180102044000701d0355000390048021408000c00c03070604165181c801c070300c0711541500c1c166015200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 811873003 1250 811871753 811871759
    0x110315031b0109051002070e16080f01050f0402070305190c0c080307020109090f091703010503012a050a110d0c0b0c0c2122030b130b06211603050601 66
    0x110050805010710161074000585207054180104a1034805149045010300140881c01c1c1c1c1c185010140103040180c41c0c0b250a9403a044003402c444c1c400f030040c40450715800010460303075071640c40c01c0c40b03418025078000da15803031039240c16515030040440c414500540c0350142132a5950003202941124044d0f2110030101303560b0306459451388503040380680007a2121409008003919a0031400511040c0c2400240040468840d0350100e0001040e100120744d00000400040c5403d024140c10351130301c450120f0f42d1080d00c030301c080491484005c40340c003802008a40010703907500545096030211002d20036201e04000c6035074024001c101644049800c0c40300c0e0743c0450750580c8120156815800c086000303220b9a40ba0b400c1c981a940482030040440a6040000d03001000e41007010b101000b03040031081c01080e0540c9030072200260028802c0a00803226000e1001103100c0f0785003180c11440c103454041c000801c808010305212107403c4400e05034032890740340029040129a01d40c040700d0040003519500d0362 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 811874253 1250 811873003 811873033
    0x40b071b12020906012610050a06021b01030b12060103030206010b0c2505060705031903020702060f090409060207030e12010b210106030c0807170a0201091811031503 73
    0x5000d000e01201408006540001803d020145a40000050500001144824400040c4410b050349203961282c45442401198141e801880020303000440d04140b8490030440d00a541d0640004078004000c0c0d82d000c42c10703003030340a50700c1080300c0c040250211002d60011030b41d860b6628400e00c02240180b041e070000159001216003550f4100c103500c00038201c032070b981d8080140c030401c8101e50755141c409240d8001940c1e69980b00144034491164001d9500d03841d500001c5103003031800009207001d00d40100b081200617a13800048505042c2041046030312810668042001400034200c01400e00788006490028150030035060811a03074200c2e4086402c0c86111030300342c26501d41000080d00108803c0310311760a00d5044a40b03600d500c5d100b000001d946503a81e2105c08020b401644007500c9038200031428000038030f2202009005139450740c002c040442055000a12910b003502c140040008445490206200150401c1420301e906003040e030745030304000d003a030b0350b500d070444c54880d00c648210b4400c050000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 811875503 1250 811874253 811874303
    0x406170c090d0206130902031e100308120a090f0f020f01032007050a0b0f010e0106030501061b0f0b150a140303040e072d0f0e090624040b07 62
    0x202002e001c140d1020010781c01d0100035008403c96600040f283e40e008102c0e9a0b151005c1c6100f00300005203c14140c03084040c4050000c4041e2423990118400102030001c02e0ba07440440f075400c80b940221084556401041c20010114850024001018104c0000510880e00d602c4504c1c03074000c6401e4100792017020010340443d514244800440f0040300b4249000b24444400703414958000d00c103a80d4284240d030b481d1051072001700d9031601b10039a444018820728036884a1180540780701e090800c69541019005080404013000507100780400010b2a400c0155100c414034420b46d00526441140c14070f0220410b03000c40390302d041409086420340004886030755041301f2503507820181c0036614050a000e881c1d082a0001001481800710001e603c95404c8802482045e140007001c5101090314800c0200078016140c07000760004100c1445403500086d60f4034440c040d000101194000000b60035141007950354040e80c00510186140070400050303605c0c5a00084c00c90a1194020030140c6100f1030038041e87d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 811876753 1250 811875503 811875517
    0x120c0f061407082a0d1107172d30070e090f2206050603120712111c030f0b060c03040303030e03090d0f121b06020d060b0406170c 57
    0x94001d0840c004c950b04540b403a40c0803d0190007002510303001242c4400810350300070001c8403c0e00e400c0045c3c5041030040b502083c54050400f075403101d140c0b10850042138210030b00c0b194004403a0241e41440016070079010300701d4620300da9260b20200280e4640c18056103401949103a0340194a202c40000c001500ca001e50311010f5000501440454032510300f0040340907002000c0d0b0140c0d105001d1003440c000b903240c5035803195900c50361010881d0304c2c00409260800b219040c01c1c102101c4c0c1809203030001034588580e03912441642c58000c1169010300f0f0a20301d451b00850804030000f0041c2c1d242800c02e0307031540040009141010701803162898101c2440030302d11981c000d8040a80081c4001d0000034840e070003540788941e0020450741020950340000304481c4800d01d003140c1c4c040c2e405e07411004100d544c50808502041908000703140604c0d440440d5040108040020306059002600400c070321410f0303000741e000d0705484180303075202d0761540405420012400708204ac0810319a0008055a2050080b2448 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 811878003 1250 811876753 811876771
    0x60513061b0f12090c1e051c0f0516120b0c0a090b130312080703050603060103080301060309020303071406010e010e09030d0c020a0b0c0d060e06030a120c0f06140708 73
    0x10000c02c2100490302c03080100007101d400d540360f0307094401050b01030078001c1c05002000101911129403219000c100c03040c9030703c428020744da08006060310b410485280303901340350000d04680e05c03c0307510310b0500e00b001804c0044800c1d00500307071408100904500003003500c00c3d01c01c03131002d602911403210030105805000b80090003d1100036041c010f155581018000361210b080302840101e0b01d80d40d4a1035070021800e68074000400035001c011485503d8028280c21410681c0a05155415a1034032519484140100414076840700070107030864a0400c00c903000a44c020300301180c3e010318050038a484032000c2c030809181b440c01000100d158000032141c1030050006800851800700d44019020240070701010303400640c010011010702103202d01c04102d1180c4a4049859a914642804941260191340107040e0304c002c0c900410046071400207415a58981102c1c501405c004101c0c011140007003031940041c01e103080b4015040400000d504a50006200070240c468184d4a002045600100468482038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 811879253 1250 811878003 811878017
    0xa0c090b032413081b01020a080a14070509061308010608241b040b1c11040302010203090904060908070b0a32102106050c070c14010c060513061b 64
    0x8040e500a41641ca1024883c0703038001d0503c1c0310362800e8042c0380e141c00045ca80e036075000200c0c070761107541c4050080d43c0b00e4890401007180070014100ba0b0120074000380300106100780042ca4154aa650605803525180c1600c079a006058842800b01c0c042e080354444c02290303100b00c2121a94400e806040752500115503040c0302070f507a13600044040c50303400340c1c0e1909486e40001c000106c0d80600b100002c0c60031781c1c035140d0250301e1a00d403034542c0005c890741080b4102001c2c00c18001440141e901004440c8500e404079028aa152610706000340204080b480040c8100c5000400c44d00300540081c1852003825180d20401c0300e4604c42701501c6030005400c9600d8400120040304c0301c800b009850409030003c0f800c3d100c10450719111800c0e14552400488484090401840620100025805000c0d030101d00c8001150400402c0c0c0e80d06050705a00703008040752044458031840003039204591420390b480c0c00000a010b2414818104e0040511458050314482d0900307404074518003149122100c85c4540b03586200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 811880503 1250 811879253 811879261
    0x4021c020a031b022b090e0405281502030c04060c21090306050916060f03020910080604050f0c0a030207020f060d0e250302040e0a0c090b0324 63
    0x1000039449074400c0303400d155541c080714100001800300c0240c1c10f1140d8005000301d54056110749010036242da008180325001c0c655240b400c0d0350043d8040d080f01c1025564a09a413901c0c0b80c0507080c24100b070801441e0341c000800303207072100100d4291465218050710401880c255041c9161050b480304550120001c001040308110343d41c0b043c031040c10341d01e014001c99500303070300c0301c610350a204910145c1000005040e00300031b2040c400b441c031405800900c010300401c0042c410780d111805070030603881000144500ca0000c0c03503040b8020340440d11149001003440400e00c0804402800d50076003510f40340e006070300e02000a4240541d04000d54000c0c003024040038100343c01d0710011400b95000c60412604121850000310958a030b0001500314101c2451b404514294100d074094540715011032240441080d0080c80403644406600440c04d807178050790003140040840030076901e804585040100328020002c0c00089103540f0382d1109428403422800d80b2280860030440703803811641426100019400a030105d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 811881753 1250 811880503 811880557
    0x40608040b06061603030605031515060a050708040806010314300c061e090601060f030f06050603100f0807060933080105030106050901080d080a1503030203040806060402 75
    0xd54400c20040030b8626044a0006109684c030b489802100843c0d00d4204c03c0c041450144075000340e648201c1443c0b0000e14100310f82c52411500461024002e440c00140312080310702c01c000311580640c100711016a5265076244182e5502024482924404407650b80c60080500c0420703c035450800c5620380e007020707402840407000e002c0465a00451010401c101c01c10041009110591140e1000042c0312104401031440c5040c03544001c001e4402c580045c070043c0600c0d5040450b0800400c05480e00180614644c010031006041075004a0340c07080001c010040a1030394500010255042d0012001c0150b0b69000f80c942c4c3c41c80b45024801c086030600380c0a00c012032003009110881c2812686010300c0c520204c440b10400040b02081d0390001e043c405c0103114a0900b40100002064103a42c1c4d58815850025400d0710f948804d080d8804100c10140850f41480c60f5400c42c4203103074800c0f11b01c015400e0b0b03a8507019640ea8030034494524207018800006985250603c01e03204104150180700c0c84c01c03110b060340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 811883003 1250 811881753 811881773
    0x1407080316022802091f0e15152d09120111070b010e0709030b04020420030106030e100204030f020607060908030a02043f0507030609060b0111010204060804 69
    0x229508503c200924202245044024058101035070300040181040d24014402c000d00024540007800201c03204d01801059010119412030768603c0100e05540c80e0304541da9095414003a07502d6000b01e1259a00c50000503e03001041000c2c0043d0314840151020020301c0350b20302c0c92210700c1c00c3d01d00051040c0310050903d0001c0380d101c80311044c0009102c0c1d983c8030f03200c0b4498111190a4a8015603100103201c05d10b840610f45400040b0350070b0a40000d0710315540c0c425510002400240115180c1c9110b0310460180c24290041400340784c2c00c6604c0b503840314002001801c107000c2c020702130300c20400c0045c54148980301712000d494009902e01f10f810459024403c69501c9420101c0e4200d6031141c0c0c51700850386400185000b2040b1400143e80c42c2d1a048444075044400da001c03200c841d0071000b03251a0000c12103503407901c031102d40d560b101c440c0702d407424807038100b48180c1c0c0068451810b0404070002c028180c0c1c020307204804240c03a0181141d0701e19000750b080b4021801100040b60006012902003184158 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 811884253 1250 811883003 811883041
    0xc1106070f090b1812060108030409090503070c06181e06030908040e070f112e06121101030e0d080c09060c030d0b040b19090c260714070803 62
    0x108201403641c0c811008045038440c0d9400c04c41e0300402c01145020b0301c0c01c10843c080c40c0412000030041c81d410034900325220711661180c0001d95a4440790340b4104941481030350444c64100410015040e5610405003902c0a20b81254600706540326020541c580d4000c0c18001d4010180f0050b00c04a0401e4800c2d0000d040200c42964070b580144000a02000340804181c440c0c4800d80c0c07058000406914050301c003200710740616500c0c1c0c109002c84907203824501030199041c40b81d9070440151a0a1004800c000d0840380c001e04c800d4001d06c5030304403d0001c5030040ba06290400c2c0d03004c201c1d0a00b210606912401c0500c02e920004420102042000c08904060302519400502303080c03030710214410280c03565011101e00841c0903150540103956207054450241e40601c1502d5440400f03002541044020006010b01d0100f29a40e0004040b480d220300f0030110444460940d81d9850003e0740c0d40c1d41c0c04204100c41c0400000d00100046029248420540324021342c41800e00d42103850300304a008200462603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 811885503 1250 811884253 811884257
    0x3070f0b090a120c15020f070f0c0803040b071406190f0b1c03090501021207030c330b0f0109091d011b0806030c010503010509070c17030a0c1106070f 66
    0x82c0601003030708018102e909801c070351281d0075441203500c1c3c40000c0842c066041003140c6d1040c4204180d00103180c0440d103171103900c0b240c41010a001850b16949850568206d051070340320109020980d414240d00906440d409040032805040ca0940440d41d05d810444104c1184c540f611003402c04100d050f0041640807030074050126000b00740074041180c6140381301110120100303000025060541104035035014090078400781c01884e07060011011130b8414a8401403c0205261040c818400c5440001c41820800002520221441001011010070310700402e00c03020b1510401000c18135105407101091541030711a008598903065480f001403521111104881400404c0300d030b0f1108080c41035202c5400e000200e40070309210038000800000006184a02952180e4240000f903030b08407041e40d0448000f02c4548400c0d42c0c40c49801c54590040c000020b011145820030007812029280113180303e1a400b40003003207440400f80085800303150b00491402c0f260040c50204820030310861204886010034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 811886753 1250 811885503 811885513
    0x60c0f1205011d1b0f09040b030111190203090d121101060509060603091c0203040816050306010b0c03070c06020304230f0616080301230d0b0f0a1d06100803070f0b09 73
    0xc40b03106283d40000e0320150317036140002c2c020f0114940752040d0541c0c0013096008110403e002c002040c2d880c4900087c2015421860b565460214400c10032902244801303040d481f04030030700d85800c01241850b450904081040701201164006051062500310381e001410013040d0340720401881016840549802428003d0744242d0402820120f030355050a5080e5008540d1107140201d86401d262200d0034109105840080c02c20159500107050b90640310150100c96031013102c1049580b4522507a040100328004012000500030340101c050011102c00301e00c0c081c4560b135101c0700302c0c5034081d0a071092540031100c8181c4411608100c8080c0907940b005c0d04101000e020940c640d4101600261301941440400384400344030003076401c85000949400317803a420014034866543e03006240e002442e0b1048110150300182104002d50003180851000c2c107151204410601c00240d26010200d44c0e083d40c203454004c0000f226540082100c5140350481d60000031442a592000c806400141540c4414070031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 811888003 1250 811886753 811886791
    0x915042c150f04091103120f030a0b0a15050c151303030906022505011121071814010207080715120b0a06050304030f020a030f0e0d060c0f1205011d 65
    0xf148600c0101c01d02880c1103610364042c0f0390825152000b107941a1001e410140408801c641900f004d41e81c001c80030080200717204104801080070031103142e00048581c1c0c0c40c060a6608160040010500900b910341030354003109000c0d058035640281078a1100d00c4003c15028040441d119a00c184403084c480d02c009403802e440010b0b419926015040d00c0780c8002da1110055080107002d1180e02450314514030740c03034203084e281d060381c1d15844850500340d0035101121b800140a40e10a060791f95040c0022400d8040440d202c0c1e400040402c1301000e16405072042200100c0e508000168444c210740c820b0401042c8061248021a90100420340f800703841070b110b03602000e4591f29090008003401d02d0360b030303134680741e20b080c0c2001440081c100c040601550040e04104001c06e034031200303040a0801604022030310301030003404550f486142060240c041860030f8040c1c200741d540302c5441c4c18280066070b29103010389103514803001112402c0c0b0880f0142c0c88410a80384c914540301c00c11980c480082c50b00ca603c11b41c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 811889253 1250 811888003 811888009
    0x402090403170a02041d1003081305031c0e0123090a0b121009020309030f07051c0f090504051e06010c060f200a020a1103030915042c150f 61
    0x3000d403201112190082030030301c01072841c05034180c80740e02c4904006c555401d02c0d078490140030504d03000c05841000000340946035000c0d10004040145400340c11180304d6010745081c80010384000500030f000844035400c00f5400d620890602c80801d13588044e0070461018007003800c1c2d140d8449042c1c2c0d90820b01003070780094154072400c06460030600801050040e86818a000300454201c2e40105070304510520502c00c261900000355a1003000d5a45019502e0ba1142030040c83d003500c0d0300d0302401d10f004413516100e00c2ea41c0416860f040d02940e48580c0b0b2950b858500700400c0e25030494880b03200c031131a01750b2481c0b003083c200c9810782c1200c018100342941640940310781e020b4903604104d0355a00c0d41c848070441070700f420380304036504856410b255540c10007070340f000d0017034442020721009461a088030400d06a2035406104440c0f15103001041c903d810144e06a40d6402074000344110002e0300d00c10194005520399a440c1d40e021200c034002c03e0400e9a8a006080d000e5980301c1500d15080b02100c030301014545c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 811890503 1250 811889253 811889297
    0x6151d19090504140a030c0201141b01090201020106090e0c0f0d020a0b0405030c011b0308060402210105090702010c0f080a020409020307020105091c1205150a171b090402090403 78
    0x844100204442c0303010f00b455503d0311342d0415000059805030b0050000f01303500c1007031401c90a070b0900e0100d028124070b842000c80760152510001da0b020040c0100c50f02d120b41544070082d854401c1e0000d01207a5038a0700080100c2e001c1002940c0e00d5084040070140340d2802c07419001c55001c000301480754010103500070a000c000280c0218460100024051119103020000751166120918241c1a01c1c07140b0b0001079005909800018140301a0b2004510556900c0c0c0544400b400c21602007600030002d50326070a0700100c20b10a090045006201191201e80b040c000d401002c1640e031240d02e845440ea040444107141c00502c2ca039041e80d428000030840f501240025030141c000795001140501b09134000c0360400c00c00c89810008000180142d66140350000307000d007911513580c000040d040e40d0701483c00c03001c41e903620300c070580c49a07803c4404116641c1d6510030303618107032403441155001041d402000300340c101c0b04000c071940004030900140042c80c0c80440b6030750051080ca007076031860900c4566000e846c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 811891753 1250 811890503 811890509
    0x903101401140607030512101503090c14060403140109020405011d0711060a15051201140c03040215030408070515090d090f1205070b030a090606151d19 67
    0x1803400ca001040202050b400055540000f250010715000c003d5801030401e2080c050306900b614914000560844e0594280900918241c21400b010b0144a48002c0043c011240102c403500210400400c2044210f020003000c260f0141c03505290078115280d240d0081e90081411a041d0748403105000141c0300c2d40503031030007820303410f20041c0c0700700d10032112208151000b400c5034100060b2a0026048800c0002c8517174015601e06000244c0d204a1420b00c003a007500303034012a8005407409001c0e05641c1056000034008866005491103503224803540710101d21064501942c8080704644c513a400c02d2807800155003052086000078685540c9a55082c1441c09800123800040391000070400c0fa60014807090b100a09203150610506080c000d851103401c02c90b0140c0d00d0951400001c3c0c4003007100030403034180607060b08010340c3e4030b034030300300c002d8201400019600712070050400b0000542688046003459580c8244c0d00e48e54201c00800098042441d01c1100c91644001c800c031543c0d4480010002c08009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 811893003 1250 811891753 811891781
    0x71704020604030609051f0b130b1e01020f01021305030d1815030608060405061506040e0453091014160f0507060c020d080f04090f09060e030a14090310 67
    0x8c01709085040201950400384c0e01d460035818215845000d546440134008007100c447c0000c80d03400070481c0101e14102180d441e128145d880001c1c0294103040640c0b240003125801c40c111010000200e00490718141c2e894140b41e0300c0c132000201402003060385010b03540428034134500003d0721517958021901d00402aa41510a03810040501154080c06040b261038544140c1d01a03107000c0c5885203640711104002c2001d04400c4001084401d0406c0071101030580074426040c00703000d00101e61a1070400382410341c140a8100140c10641107102c030207406c3d6858228000c000f21200301031000705903a0170300c0d00f03485640124000c000d206203040c0402c800c0035680340586400381c4440120319015180000d50740000d03040c4241d40443c500141c0d190101108826400410f0302d484038401c00760440e50380116001440490b0038486032048901080d8840300003035000340c04c18005040303441030305d0307840344980017a0b40c00094613590010700c1030021a00030f088800000e400c9501609042c940e14045070600644040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 811894253 1250 811893003 811893011
    0x5070501050c04050a060c020609030d0f0207051806040b03010609020f0d050a0204080d050c0a05071701200912030706050703090516180b010201090b01080303071704020604030609051f 81
    0x6202003403182039400034600c11a00d10303050801c0c001a04c810602d2041000b040a807802d00400c5440d0381d0203485100c50302404840c055110090040c003d2200c1a40341c200503c0b80c81000a880d240168003805154100203132000c5944500d0240b0000d00045040c01da050b6488900c0042e4003440c80c07008259528161700c810707844103194080360007074800142c00c5000707150060106204000700132403802c02c1c0f0000c0307042049d0b4070f1315006c3d0054100080140e01604078021050000350b40b01d51a200c010380c0411b5a8020003111807221024500007101340e901100118007440202c0c0b507802d006684900c0d840c4c2e02c0c1d00b282c3c01e20a45944440a4500c11528000000d450300000300805c041000079040c180341c604017944499040c452800b46c0d95110459000e20b145d12405801404d9000398054426a80c2041341c500c0315684441c0c1d0560359501c20b075961030005089095a049044010b1319071406641c0c0204014076140c5035865040140107034480c1510303940650503908006e04034007007140b5900d0300b074488045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 811895503 1250 811894253 811894267
    0xb072f03030714070b16210204063509072706061b0219090207030c020901050a0803041a0c0a0f17030c0720040c05310b0a03180305 58
    0x2c00164034a81041d030310f024103000e5031000460360744400742c0c0035100030010107004e4081a821603094104d440442c0304070309120f41104104103150001c000b601e40c40d46603020703840f00c860055100d906c0710300c4081c0f14510071b06141c507041c482c0317a0451355000780405003100d11301c07915032000ca4020403003660b100c1c080b0300d0350701010076160340d0700e0140b0001041d090410810700301182522080b031100c400c1c2c00a224a82400740c101d00502d20030075800c05071108400864880c601490050311020b0440070517031290304000c0000501c3e1614920301010358000d000518203140c03503d0030744400c804694444082070304080c40f540603c0030041001100003400764024000d104c1142c01c28000c2200c40b00c207003c04410041003045241c018000481e40b2441d8048000346001c07006942c181c00320040c8003600e641c0b05041c1001524115132003005411007009286030f09082c107000034465080009400c014204803040301c14200402254040a440a5000c6003008182e040c5107010b2650318a01501e0210081200450a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 811896753 1250 811895503 811895507
    0x1c021b010c0312090c09050c03040606050405150616020324090312040807170f0d05100e040818090406060611010c1220071a090a0b072f030307 63
    0x202405240a0821140e900681e8500400d0000322101101c811038482c58a07a08009000031020002e1128030380c10011424280026400b0b640251030507644c050130302d20086880d180600c0b41c1030045401510088900c1c2640041c00300d1030304161052444a42c21200700f4000d62021301010804250101c590246d80b00d0702c0102074603030720000d000c4940b40e03401030201604016280a079540c1040c0c04c50304442d02d4803a2031500b011811032076060001c8110000c035108509100990284c60b602202032020710090b510402c0c02004040345104800440c50a40081070200d007440c4d0041000c1c0002c00e003030618100c07a60000c00c4002c1c40503103085856641d01d0108011030340d40040050000d21041009001803a14000018424104460ba0707404180d0345201003121083c0d0200d954411201280105032078042c0c6003024950998440012902002c0400001c2d0051201060800841d0762040d51810319480d4580210341e047c0750411005054072140e2a001d4042244040414800c0d0250008641c2da1078000c80c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 811898003 1250 811896753 811896793
    0x111040e0a051308070204150f0807170604020f06070c060c1e1a07031512020301050f0106080c09060c010509060106021905030708090303040b0403060b040b06041d091c02 75
    0x441a40c80e0302e04018800301d011516803082015800000b07140d100e58240c00002c0c01851803100400459500c0c1c44001009286421088111006541070320310031940d030381c0103900c092080f905031034003a0400b10001d07006140001c50460082c0000e8009801c01a170380d035440c405841c40f50060008645001221000c201003400034140112401030b0140c800d41d41991254050710058409032000c411000006803140c1c03082e4003901044030505500440c607a0786032501005043c40a034281d02035420180010041111109100e040350250340d91103529944c1d28440501c540c11100440740d1140c801c2019600241090091a004101c000e000d0011035242a00292a11000c100201e408411190b00743c0c01191012080c0c60070706801080c00c0390b903100c2006c006811841581c0050142d0710011030302005020003903001d051203040990f002c000d442d02907070400000307001c1c520980d41c40420018181700f4403e60001c0c040e802640c50421600d05104512030410007907585441c10f00183c8c01114800800c01400302 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 811899253 1250 811898003 811898011
    0x6041106040803090d0501180b1602060c03011e05061b0f190609020a1205070303030b060316110a062d0c080f070c081207122a09080111040e 62
    0x14034510705441c01c0e104607120b00584070404e01c5013028104003001e000c029001a050440c010a9240d8241040d203400300a010041e2105809060a0551241c40c603000250040c081d11441910a003140c2c41c00f4119010300b10b04c0c0b900d00e048003403541c40000e410b884110207050171140402240644070b1051040c01e19010500090742c2c0c3c194890f03001c013054902c5040c5202070300c0c0e80006011500d0304a0b800440c4004406502c105031030000b0200d00d41c14042c011880c0004c1da442903506002d1130f008042044200c1c0020349003108411001c290300d0841d0f500440c04405400300440594541514584466044560f204901c0242e0542074521180c00d1400b85400c0d035400981540030003204074801c000411414009010303042c03000548000c15074540c0940145107200d5441421240d480c0403400c0c00001d94501036404102080c0700e50340400b8040014043d041d901b403084d09811004506e902003800100c00400514014040c01ca0b601141c408401c0c01703800c08011110400a580707a2400c130961914800c014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811900503 1250 811899253 811899259
    0x140a140919020a050c10060b030a0b04022701091202010e22060902130906030b0109020a050f1317030937030b040201171b07031209050c100f090b0c01110408060411 72
    0x1f80d01800304640080c140d079040114643c1c001426009080454000c0c8030712101510120b13004000e10001a210480c03030642c2040a0741c801ca8180c0d0785211262065890720f01c020b001c02e54088401046046c00f04000c88149040c1140c450a1681e621101080f5a81034114103105a000103403014260500c15a04004001d020700411a0b13134a90b03110520741c54010b000c0c03003040ca900001c148202074450016903206c00021301032960303206903404414100500300e00ca40002c6520201d080240e9620110a607150300c81c0c09007160212150720f040155240780060441c114007103480c010312241080b510f5196028510846495a05003028000505072040c805540d074002080d10003040150150354003032440d00443c06800c02d4031440700b17140c1031749c00c44c0d4030415038621245001105010b02c80001194100c9000a5520744450b6003650001c485c070070441c0075500081a4580303401c00183c0a403800422100314490000200c115a50f061403219a20560210165902c81030521040c400c400102c0410401c0032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811901753 1250 811900503 811900511
    0x30206010504063809150405040b01080112030807090b1c0e03040f0303050d021612080c13030209040519201804082a07140a140919020a050c10 63
    0x820240c030800c284e95a840280240d00c032003200d0003030f80f03c9800e0325540d8400a104140d50b003405c80c15100182c00c01c0c03191621a0303007080d98108035540513001590503108a06004a00410603840603507030810058500300030042d404000180600149020300004a1144600c8134842d0401401005440d6046c0cce0700d08098204010070810302c4031400e17151084992504000c0c1d2500041092070b0003d000d80b00f186074650455655000c00c00c40c402c151041e0361003182e1200643c0752540cac40e440e80280144902e0000c1e080102ca014005481c1407000c0741d520a20400840704c11520040c900f001c070390201003046411003069400d2a00301c8003507c2842148840955000d851000e040c0307010400c1c0003000d00040d28010700040d03034a52042c5034841d0001c5e140c0c80c03000e540c0308481000c03c0b15075840c400c40c440d035016002c99510780390491030f21001d80001c45052503018014207003020108107079800080e00032071110081d0b4145001d02c0e00c0e24009005c54007015100c00e900c6d035003170501550400500c010003407101450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811903003 1250 811901753 811901789
    0x9030314010b1207031503030e01080f0105150c07080a050705150f030a1814060709050111030729070e0a0803070506180c1302090a1a0315180403020601050406 70
    0xd0081610081103c402c01800c40c1d46074001c081c0c0061902c000350454210366201d0220515802408083c14400c080e40c81441030f0f51965040c05100b4000c2c00b5055000020192000034061040c000e04650309400c4151541665103002142c90203250b04821140703900300040c100319a2400c4212610514064968186441c0b001420444180300007051a03800c50790300d816000140c2c40307850900001581c0010720141c00030070076130650703a604001c0f100c40c0300052a20401150b40d510a01c81c2c6c9000e60345800080d0300b0b1022a41d204100e0040c034045402010341304500c500c280c06000c44819009021585429820740000c03000e0107450000d980000810b5401004002c00042000078601e51090003103e410001c250031902d00340c2400c2100c04419403013210700410a440d650b0b60341c014403a1000444443c48080c0e81c0303074251180700d281000100301e84e000920004042c0d080744a15101003600081c0007100700d00110703105480100c0e05440580050b4041c038014041420a44100d1001d840001042e05103402c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811904253 1250 811903003 811903019
    0x50d0b01080f06130219030b24010309080d2409050f010e15010f140a08090601050d0201230d02210c0313030e13060b030709050d0206030a15030c06030903031401 71
    0x84c2502c0000e01400704a6181e07022801e06540d040007071341e403110110720300341410820740c5944095514048060045000803028940c004d12640b91520b601483c0c00341041c03003100c0c0907001000c61500c0340110119a424203511299505d9180c406840e80c80c10028150030070b800f490100100581204070b41c520b1070070a12407035083d4540980c240b0402441c1042920b49192401c4070750300900c880c030314410100030401b40340403078020344402c1c4100b00c8a801c69149aa03035030704120741d1410300b49029010490301c03034110020b131014500b04580f848110000c6441c00d4440c2c48040102c0e0b200700d8101c1450111640c501c100e4910f900300711500306558410090031401d00a104114011311800c00800340302c01c00030081d2054841c5403c80e00b00368501c1c00f04000003039880c056078800e0b0303008690000000e0351032503021403c1e144c808402246a45c0140c809415951003a544a009007036035480450207603c152800400500c6440c41c60700644800d66020520b00351a24000d01a101c1048074580d02c05815401800055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811905503 1250 811904253 811904281
    0xa0b2e02010b15030a110310050411070f0b10030503070807031706031002070201110a030201051b1317210d0b180703090309030f080a0f2d09050d0b01080f06 69
    0xa01c2803d1601d54a48404075aa0010800c07028a002c0c5101c0200c100f02c0c140108251100c100c031025030b8284404000d06d20021401d11480f0300042c001d440802c0305401080d16a00c0b1305a010000d1a0f40038280381e00c9441700e5245401036441100c0d09540040c07503004241d4000c0d41402885a01d00e04403070217081000000e03880720914011541d442c0d0f408156042960303c50024a0203c4000c642514054146802e00a02030502128905200382200940e200c501c4002c0046030000f104240140b0f41c21030801c0295558109542614140d82c402e006010441032075094680214842c115449666030481800d80400d4030450100796201d80c03040404040c03c0004403990f80e62103025450b0000340c1c4a0149000d40c1c00c4003298001805081d1a0448202045060b8006010070b20541c0c84813030390064443c0c0100d514500a40001c0106c140d0a13000a43c5881100c0c12049168400d0800c2200d9076101c6001c609611035060381079403018482c40c010040b0140902900d211100c00304054050be18010101d44201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811906753 1250 811905503 811905529
    0x1e0702010e13090b1801060b07050c090711060709090f090503030f10030b040822051c0c0801020c0714090105030a0f05030405041b0e040608070303080a0b2e02010b 72
    0x42c0c2d4011a54aa40c0300d159016400450b800f910450003410714a80da0001942c0d000d051920f03030340c03078100003051404020098500955103c0700070b14403007422006101c00d1315405000d0009102c44015a010344030b134107010142c42080d4544da0050b1007840c0138540d90503503540101c0d48000920700308149011440110403641c0c4000241c118201d6600c0f0707034000e24440511a40044c0680e2801d805220030010001c004141c0b12400c2c003a0352460904008484281c1050752042a9101408c840e41c030300c1424a18645118950142400d90101030342e0b40040307400d903801001c1b40c0d080303a0044e05083c0103070b24a00e0414007101ca4150f5040c0390315810800407a42e1140116000390261800c186003004201e0108100d0b805060043c00c14801003c040480844091f204006180490745110302081c039410188140c504032000342e8000c103c000e02c0d41c0c0b0181c1d00301201600301e985258589002207141d484e01ca0010b880500012604880c3c80e48402d4075075a41b00d2104200411a4101996059240c1d14031004040da = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811908003 1250 811906753 811906759
    0x150605071709040c020312060a120f02150a02010e120705120d061802071e02011e030f09050705090c0c030928060e240304030c0c08121e0702010e 64
    0x44004507008605036014210590f075009040044024009901201800c9140b0f003015040d1000e031240010001c2d4492a0b010f1098591250118070b000302d80182c00000c0e00c0d03030000e0000c01a4408200440c0c2c040e900c2070300c1001c0580c3d1a88051a402d5104000c01800030100c0403a040c00d0004550b1025103401e100340740b20b4101000401c0c590138900070f4ad400f80000344003646040c014a00b0714101000a5085540103454000b00c001540c114031541e000d804400c1c65050303565106088007010b4842002c04071500c0201010740c0c0c1c0d544c01c000d0350f01ca80319011561f0b014a00402410740b4000400190410041c900c0100410a0101800003038001094030782040c001c88940560308105604180c500880b41002c6043c520300042c0084d2030b582240b0380485814003a114145095051200c9502c1c030b034102c400c106803091040000401283c4150b0351100898410134260262517950054240f07003005d100b00074465603400040e8070050030708000d403a414114901c40c4d042d08250f90703500041c00070b56087c007107940 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811909253 1250 811908003 811908023
    0x1b06030a0b03070f030c06030b030313151b11030c0319110103091a0a150602030403080904020f0c0c0a0608041113110c030904060533041d090115060507 67
    0x2103641d80503c00e61000c3c0c010303090814240c9642e4104007040a00318454000801d00d8949180132a040c040300300d851a5100c1d10440c45401e00e0440700c00300015401d83c295040010740350401440b441c909401c2c00140d03019050088040e0080710401d400c5c1809009054407030360064000c0f400e81c0300c01c0608a89910f4020410080b8030080400590143c03107150b02c0104400000060703044030a12510415005801c211401c00442c01e014840c280b03010024024040542c0c414881080000d034400014092000d01600250070800320541704e05182d005082852400d0b003045181e8003030b0b402c0200c0302c0d400a200703d281250b12030900c0d0b200c540015141d518a14002c203101c0110703a82504550700100e010012048240381d681031201c44540d00c9401c4034488030320450a108001070b0a141c131054410b81e0a80315184d100402c02004001004400d00d4004051180410300000030044c51309600007910700306816503280c0c10701d41100c1142c00c4032150360b044c0000721030401c024000c007584403064443c11603100c80b800c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811910503 1250 811909253 811909271
    0x5132703020a1e0b0a023c0316180e0c18030d050903070f0b160512030c120a0c08070c06140a06031401110a0e01120e01050601021b06030a 61
    0x7418028848005000f03030b100004001a5248075648105400340101011041034851200c4c2d9030071703032290140b0340314080e100241c01c40e101c0c4101c228a0000500b10440a0004050020030311201c0d00f08030313806031040e180300545e80d40203500202042c81600380d540c0344240c081d040262445440300090844070140e80c0201d043c0f4078410000d01c2c20070411400408a079204004400000d041c0c0d8017005400d402805144030009400041c1e0480c0001e0b98183c08038603081c07003002e10b188240110020002c0d04c4522498102e052440c02000040d802043d0381c0b80200ea6a01c2042c803c2c614500e00681100045403910740707103860050348455143d4014844c0e14003040d45204600748078015000b02107003d040002c0325030521401e031059501080840b88500200c2c0d18950242c00a2401c903528050000c20741c010030080756108900c2100e990340c40c003005042010341015100d020303808680d4280c11150300b07a0740d10400c1c00b6640d82c0400c10040f8034034218081410700c0105501040f030600018020001d150313201c0380c000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811911753 1250 811910503 811910507
    0x1181e0f0b030a08040828080304020d1403030403110a020906010509030c09010806070206090d09260a0609030806041a040b030a0b0c090a050904230102040504060f05132703 76
    0x740420750401400c41c0c0c1280b680303003030a08440d80244118025481001c1140030320415428020042182d03080c0f101ca5032441c284c0b103440c0313168001001280d001c0c4c480e0214a000880c0220540240d0110800031503d84c5482e143c054080702e0b4162a651080d80280442401a66010360070f40d408003013031800b03549850300c0e8000f01e0b29028503d541650f10150b5007001055a00c40024042c0c402c1c2010f070b003264616200d4921454a8a001605500000d2019182070040b039130941420b00482c4641c0c801c08522103240415242081c9030440100d92080e110f9065805060740000c0c01600848201c07030030030001c00d4414145018a5613443c800d40a0343c2c4523840d200c00340d40e0030710050307240326005a15500a45400307501034216510140d081c42c0700d90b51412021440c1c1c184581058440c030360014200c128020b031080505800d544400042801e50b4003000041481e440f640641d50081007107191080340981003004000180700580c45040307503149481c084034030080444080c41200031104d010612080c506042c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811913003 1250 811911753 811911761
    0x70b0a0c030e01140a06290306012d080a02131202030a0506010e0412170609061f050d0e0303040f021003020f18030606030d0816020307061401181e0f 66
    0x120b425500c3c1001a0a1103420000030611844464604003c4140c485100b84c0324900307440c0420360003104412140c14100c20b501c004640040c0141007060313006844030680040e1002688841c031079408428522078540d0f4018181c41d4101032900000c0d828201403250f000e80200861064810070200c00310080c056440510043c1079090300501a10700940c0c43d01c2c10103c40d04070076541100c2d50420900c2f4504040e01c01e0420310380d8400100c0340103a90303803220b2041003101100a407085900502c41c4201c2c0c124441c0c10590f26407a40007648030940c4940e02d60b080c0d8800c603016038200040ca034004108000000e40781c0b11071003160b50f904440ca181c4c2900c074000103c0081c001d0300c16940704410300103420100000c0c29845508005003c03812152207580d100180740e10b0301481a402c2c0082004074003c1800c0c2120030010005001180c41280e081c07000d507480d010250b94a440c45d80c600a41c040c00140480c01e0043c0705140d41010002003030080e242403500c949821020380c1e60030225141c0d02c01129205241c1600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811914253 1250 811913003 811913021
    0xb1812070c030507061107090e03030103020609120f010c02151e07091a0405040c020d0e061b0109080306031203040f0b06270105041a03280b010602010917070b0a0c03 73
    0x13220221a1200005400035006214011061180b0040003d411205008400030701100c5005035007035928507402d0110541000b0102c1e58061041943d411282d5030400c545289841d0020000c00e0100c13000e00007074103140600141041e42c60004003080b80074014014405802c001903002c0c21030a030b444440440d8038020070b0300840900d0300c0e0800c174403a490181c100035006680080790100031030700d24848140e03550410f0124001c0841d14510440180b4a8884007408502e0701c8034241d900da903140880124211440c0c8401112415804800c0c441503090401642c0243c20f901702d00c0502d14142501d45615071100010014802c92503200058210740b10640e4400c040c01c21140031a2a20070044141d81181800f4020385019518100e000c40d220f04204480400540c0068043c0070b00c1c0e00702c6966018400c0105801c803100580031047c0c00006010f0301e61685c02041654000981d00846140840c43c8004616403406c00350010303c400804528681001a00690360300070024400c600d0040c00d03401741010031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811915503 1250 811914253 811914263
    0x1270b010e06010e0d05160906140f040e070b030405060106030e1216020904030c11010516200a0803040e01080a08090108060307080123010510050405010807030216030c0b1812070c03 80
    0x342c83d52040000000354600c031005116501121f19031140f1000007103070b0340b5200b00031010b904481a242c82d418028003415044a01a1011a003500102d210301c1c82c00e0800e5005410000c000000c01060010500c104c1d409000c10b8075003404000040e51016588001d504203842030140002942d038141503050750484440e5038041c00c0850703949800c1c14003501020120505564103041c0248068a561244040302d10101e40c0040905000305180c89952024010750a05400201490305c0c0c030300c0f25542c07150040c0c007c0007840011580c0c1c2e03017444004c803480d0a06a05c40c448941c0900f41440000300850250303243d0650a190058055840380d00207458141660f001962652a003065029070000000d850114901c81349004a2966603444c00e0203500040c0340761800014000f44014011903105a4042d40c011019181c0982440142c0e04489006002d03000105c000c05c1904800100700002808950f62003501e4402c04103591f009100c0191b141e201c41540750540b00760008040d01002080345088000d9a082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811916753 1250 811915503 811915519
    0x82706130b0c0c030d17060108070f030c09090905160b040506040308030702030d0c020d031d10050606040b040f05010e06070b04060b13020301030b01030512030106050901050906040902070501270b010e06010e 91
    0x3080e000352086d01d24102c44a0015006400601194080c88019000d8200c60350f43d014102014030049004001c981125800c004042d4000282130005010f0305822500500140124030121809070410b041c0d80d600603080c040c400e001c104540e42d00ea00985d0304503500002740680e6940e0301e0400724203603c18138444aa4003803800c0350b900d105940c00034222003000207503201004520f1210500560842c480510880d19502c00780641c0a4500d0079005280c00000c064102420141c60f042c40c24041c0c0c0041c2c00407009000089020001580d0100780e040f2a090b040d56107a281244684420702c0441c40200f02030202030b160400040389445800c1000101c00204400315200c1d40c681c54550302d4404203100540d5a03105901c92840c16100d10001c0b01d04884507900c49a10b82042c42c03005440c2d58001864096010400340300015003c1854001481543c0c031400000504901f41038840340c80c0204d07000b401034090115001380d000154600f82c500e040d10240d02d009100c1c0d9482c80c0040320301350f030000c0c0c0d1b054001c614 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811918003 1250 811916753 811916773
    0xf0203070e090601030e03070609030e0d030f023901021e0109060f02090a0324020a0809010e0f07090f24031202030a0804110d082706130b0c0c03 64
    0x1c00018000100c00454803011581c850100440a44150050594441d00200642000070741039138000f42145200b8100000c1f104092000030301e0410840c10140c0204003910340320071580703070306000c85581c0300b9441ca103410744c600e0382134a40d42502d903c03222102140c500b8241e00817003d80c0208481151515010700001c2203082558500b030103045d26000448a0600b4441c0e804081da4071740c020303148190790142c450440c130740c03860b2105e008100000c4841c0003038400c0303401d00b59000d51041c001400c1800e480e48802c0200c1c10802401d42c00c40e80c4d0780702100500d03000041f040407042c10100f0b1100c200d4070f08030008100400016006002003030300000001041c0218a00340101c0382c011801c050450b03018000300008880e00c10350617030710392095246140000d150350700003d002490114003c0c1d8420300250040f150311109503a64849a81b01c0c1d081d540c280d82c10400c0300040b2130408a401c0380101c7e41910b04034103064042e140c09510340040d00541c07040407004508000001b504201c4010b0b0104001e00b12100401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811919253 1250 811918003 811918007
    0x7063002030c091905180406020d0c03140907050604150e100827070e0411040603051e0f0c01031820090114031c09080a050706080f011a0702040f020307 67
    0x1103d461220702841c1c11407404c068080944922800310381010f0441584141c1002c06000038540082085a4440c0e00b03204d00c00540580f4460303c448401541c90000e882c102824120350030707200040403e070842e40b000303c060100d500c90f041640c040707400c03450005403008901ba200b83c581054450b961500301401c1076140f41c03101e40c03046507a80900b80041c01c480d0075840d00c14521307049943c02d440386455540281ca04200b84105030f64a10780c17150049152803401480701c070005003910882d500c2a40c1642c03110681d40009c00c0113810540d04401000010b02c0250030391801942c0350369107205100c0c18590780c0d00e82c04050b14606e8002d00a030a5011414805a000407244603e44d40048104503000c1c05c4900008500c40314402035040010380c00400800d0311403820003020f401c0005c91101d1a082080140e000291018100f03d00b40103280f140024000f0316080130001881c680004114001001a0800401101040d524200c64813800d1001c6150f81d070000340045402b42c20301035080240584000200a00a6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811920503 1250 811919253 811919257
    0xb01021516090b03010308070807020126100501030209130b06040503030a0f08010506090904061a13020c1c140a0212180109050303031005060310030503030f071107063002030c 77
    0x54458584514254458200380f01a0209010042181000f00003807c0420f2194024012180c414034125015445858000400d40c00000001510380d0f074840a04c45004804017010340a000207107402c42c1000710035030005813100318514101c8145661001c49144075206e2004031405002c000c1c0840b50b0350205500000c00c03103125921780700001500c840021034a468504121103001c0e1004040c030307903c3e80703030b0380c0700e400061007200c021051090100100d148542c0328003803802400c0301031500060312018000e40d503500707144405101004503051242032001580d04420003401c0c280c4000001798640444010580c60100a120440a1180d02103481c1784203a0080c4486a02200c1c02e98900c000ba950359030a050b40c1e0b0200380d55544502c6180340f414000c40c1410740186901844591025054645d01d4650700e003581d01c107888075a001c032080340401000c1030700400c07042285482d20004050307052602400805020100314104481e40a03841d00104404100b44400e110b031180c54000c55032420722090700090740d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811921753 1250 811920503 811920541
    0xb040f050706020a120f110d0207030b0c0717030703240612060311010c0203010f05131b0e0606070f05120c070f0803092101020a210218040b010215 65
    0xa0720a07541d01044851012901d0900c040e44a58480d44e4010424803c0c0c90f000d90300c0800e0b0f81000800002d0401588003040008194056500640361082c21403c00c0400c42c02d004004154800041010300001400350380c10b030180303002c1d58900e1038480d215028118007901c2030241031903140c11401c80c1c20190111549003c41119020703110058045103032000e01003503070040d1101406400c40c001d42404d465006240700c00c40c0314801000040c0542d40620080c0407100c003903035001504012052910104001e00b01510721216000c2040010646440001003658000400103805061f021400c4030030403a07071591204003150b000c82515200300036040800001e4004041c021403d01ca0420009032403004024807409503101c4001440c40e01c4926003d01c09000000051054104c46000c540c1440000c20310252240751045d6aa0307010181141c0584040c505941c0030b881d503403a104200c48400c0102404200d0b080392003d40e40400c1040d24640180e0900d00e112025001d80301159041240a441056041d501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811923003 1250 811921753 811921763
    0x71a070e01031a04050702070e09060709050a0e0604110f0319182d0c0b070303060510081b04150309060f05010302090a1a120a12020c06250b040f 64
    0x811505400110150ba100040140c0450070f50740403181d05041603003001d03a0200c4940102c90b0615660b03140490280d1040f100c61620f038112105000c0c103194401102c5004100c215101d078491410010702203104032000d0040c2d44039940d070380e8100c100a510703603041e151f502c09031544050301d07407030050b04041000742c6102501c11401d103402404020925103103044000d0540103865404241c3c0303400403020103040c1d80001003101040d100c00b403400080842206d58050502d14103103036118040d91a0140541e820303a00114460038140c1e01403074095901000c090350210011410b0341028824484c41d07010341c0300f660044c04540c000d0b00318034a0a2078068000300145489504200a0110303006050400c0320800c0c08000e40c4944c0005c0800d0840c0c0c450382040ca4030f0202c01d400b00407420f03050390004080303002d403074001c4102d90000300e2408148034001c1481400c0d0a1540054a502c044000014100d48a8410803244a50541e008981c10710f50b90104290000c0c2c3c802c2103c4130a00b00f9003002c03424464407000c2194 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811924253 1250 811923003 811923017
    0x1508030a020705012a1406011d0702060c0a0c0311011b110c0f1e030d12050702010509061b04080a06090b0705120a02030a090213051005040e030a0c0305071a07 70
    0x3d4294410358182015a4071395820310541c140e002d00340d0015600349002034902048428450307256240c28000c0300d009003c0c3c00780390b100008405090340850f20000b0429415034000f001084601c003040c500b1140003402030f02c0e0008090649103400d451038041c04521400d10340c81c105814003a000d0b910094a03444c11107403550891010f04800700390350341c10130746511604400740307403000140e40c10302c0200d401511400c1d51242e42030712001d502107407070822a0442c1c0c500040111210280c0c161480c49202d8100303183d0b10081c404c1d450840c81140da1110050310060303030f0500344400c0811468444003510040d005c3d08003510304540050608030054640380c0010b0f164020f8140100d00700320b01034801c43e1642112414a0030140d951185035500a40004026035544e903140d00704040141d580c0000c20100c801e001c42e001a00e8280200e0050b40c042103a008503000d03031306c0c00e450241c00c002d00000742e544a0005240019400302545401c841038016510001c1c0440c0d1030b4207900950300304d8840110f1159003c3e07aa440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811925503 1250 811924253 811924259
    0x20319140c0a050a1a0d021204030f030e0606121005010e09070f1203120b03032b0b0f060307170a09031707080406110f070b25050d020a02011508030a0207 68
    0x1420140350b00c50f8641c00303250300300d040010401d40082c04503801340b15000c841c2003010b18007404060340d0004442e00c2c500703500341c030812042503009400325991010525040000708490100f107952070390050800707072051a0344d4000007a9500100000400c580c4444410310165a41d074120b591241e00c140d40007011030181080102d101029942c281c03044070040f42200107850711036101684e11307204800c0d034010f40c99141d00c0800140d840800081190351403400310501d4142001c0780000720b803460200e51015060400c00446403c1c0e40301d10f040300c0c180d407048800303a589407036003101520360002103903d10b1111070812040125001040e40407440c41c500903101c03a07041003c1c090b001e50300600111440c0000c80c4000000c200400d42a030b0006454007001d000141c5409c1c05101008410713040303d0412601c000d0382000300301401c0440e10104a644c40c119034005207100e0000c10241c5140919951100764075401302d2400b50b441e01c01d401590840b4024080c4003011521060703016140e9020349614405889111000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811926753 1250 811925503 811925509
    0x310020304151e0903050a08101d0a0b03070605190e1f140d0e010605180f07030902060f0415021216020a0302041404021302071e020319140c 62
    0x1284100d0307020035240c0410700b0600c09480101058804505410040c5181c100c07501da041c0700302041d10340a9101c160311444504401400301900030802400780c10b03552002c022088100c40304110000601901207443c1d0360740035040b0002c0c41c0380e901e1154107200e1040d00040031394000b8001c0c000115203404038600f03100e03548829030320f80d442c4444d2103030400c4007800840e02010080a900391042807918080c4404070780f051040415401900805008554ac0d07000d208411500b440361100a200c1616030640e503524102894103100070040000c5002024034000494082c801c2e84440521940100b440e500c0c0d00c04040d40803260340090107080074600d041c1c04a214803d00003d040360301d61548021861401032042000501c0f581140000c1381c00403048070021005a4442c00713080102404008915851700c1c190042004064034455411b401c28810000c0b000841c200301c03182141081e181c0d41c0080142c0c00d034400700e807500074040c90b91242d039484050120108407061840c0709030707410070700c0031280600101010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811928003 1250 811926753 811926757
    0x1a21160e09070c03020f1c1709030f09060d09060f051305070303180503100906060e0f0411010909090c0e0c0f04170705030a03020309090c0f0711060f040602010902031002 75
    0x160750141e011400500302c140b01e055010034541c400d00c161050107400360f00d4075140ca091360b500914003245410045103910360040c80c48107a41e8115100d203010b81030074075455489108000500f041c0d00e1002501c522141c8500044890b0718000b0101040380c8012410a0320060030182e16012110342800e0104100310402c4a5081000e50420080c200316031540d0360668442d81214881e40308200071140010301c0b65400e000b4402e80340300b4900003081058080c603041c1d003101c0c44c640000000408040510034414441c40d20144d000c1c3d8005200890b040c12603005841c000c0300780c3c1c0509080b6041040b0704007000798203106c000407510b680b6012240390321000300c3c20b40e80d405a110400140001400300701300c192003408007903407802480d1059a4085444001107030501c82e40000540240e0300c0006c00001d141071210301c007a80501002880741c14000e894100d15201e00c1990406000c03460b6003c1544e60326645c99080b01c41d02c004124500341d9540c0d8490001e07018000c0158241c2c403c1c013402c150f0101162503402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811929253 1250 811928003 811928027
    0xa090b1c02030c120715020f16080a03050c151f090b13050612060f040c0e010f0b030604060e1005010206161e12110306040510050a1a2116 61
    0x503240d05109002400820795182c0300941c1305100f00c5000041000c9076800c0035262a51950203046074500348221940f4082c00303109082c420401c140c0d4204004400032a50801c13469040c5491070303071070031031084052a00d000710402c0e00c0012030745024401c0e14206000000d40d6a02d06215123413031283e95200ca0350480301880106904003000000910392108681d01c20356101c4d400810704289191500400751031300c1012a910701003207103000103100500012204500080840340810300f140c1d0f050141041d00b40849101d0500106c1d404008202a9500e45e0007075809486005000540340c0b402e075003c121900703450b1081034058040c001c00302d9010a080da40f280c1c00203510340c8408156103160300d010701c8030586c440464030400c4031450303500d0303800c0ca01405804820348102d81515181d04262080100b200d0014220b06110304111008102544808400c4000c42d01000380c114040c0318456120031240c410380940c85101122501800d2407203d00070702c1980580c113160084121840e002d54142c61007a9070741 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811930503 1250 811929253 811929259
    0x7050c010b04050c2a03030703050f1605070201080a0b1e010e010302090a030b060a180906050f090a061113092003220609050d031e090c0e090c0a090b1c02 68
    0x17050300c58207240d0b6100c40c07000c0c164000300100317440c1681e20503065070410f58030304c0002611541444096230300c00c01020380240032030100940c0782448881c06001071240d40340c004c0c14410404001940c42c2180d6124a01c102405402d2042c0c002140030301d90045400c0c5414280402c208145200d80740d486482540c1071000c0161031403080794210740300d00366040801001550301141640340440c04100721050400010340410700841e05c1aa945400300644400a1440380003d031030000300001d5400005200761201d0700010009141d00307002c10b0b120080d201c0c00341540d000c1d07000c03c040091400000d03030054141c1080c1d00200640340c240403c241505200c00e85001c40c4074000d54281e500d030b00504d40d0a45850b079128940000c2e030039140b0780c0c0b4642050f0400d40000e010903603034060122004004c51140e0b030082d805d0a0108803a62141c1d9a07400038841c1030103503180c844640b00c001003031140108103000d24044024480e91800384d80d61a000050726001d40d038607005040c2080500c40008a40701592080c0d5801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811931753 1250 811930503 811930507
    0x4030c21021018021504081b04060518130c1214060c091f09120f02011116171014101d06040f091403070219031101140d0507050c010b04050c 62
    0x540811490031030110000800b0142000001f501c10300420010100050b11100e03411072600401c10442105e250b80e11050041e03990a0801c030910603000182644901001c3c942c420b0b0f05c920b414902178602054100c60300c1501c0d0030b0b403d07800744801d000254484010030340c21074285079605000114107000311100981c0000b0b210140311100b00d803a0001507400d05846c41c041c200685d84140902c1d40c01d0205100340c072000d4100b0700340d40a42d644041449210a201320052248070030803a00c680604059201d811188032002c00c8090302c541062003540403e1080600c01d220060742d00c0c542900d0024151040811441e0440d800034440b805040020740d000741100186099a4801c410702001c0d105006822007055078851001000403c9005010701c1c429490000310348851143c81440440700c80e858150615242203801000000c10304206d03921000c0080c41c041007400051b80748080c1c540a41414003030100d0803c000c110032598454090148224400001e00015881e00c0610044440986041c003480c002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811933003 1250 811931753 811931801
    0x8100608070f0e040305090a170d0807201203040809031b03120a050c010c0503010f0e0606190c0507031a060d0c060311070b150118150804030c210210 66
    0x1058120744c00b50003070401e1854035070355900103000c010268000c0c000d1012880c6c080580a07804018071014400e541c10f020215007821a40138203e0761151860000245250020b00d108100a00a01c01500200c1c0c0c0c40b942c0301e082618120303815420880c8413500a00c65440c0c40e08070207035014a9071040d901c0283c06400c10909031034940d44240d009008003020b1241c1001130203c420424440c42c0019800359484a44950500c4004a4022010f40c40106140840c3e0140100799072100201c400c01250030070000c40541c902e507429240031400c003801034440d00540b4000014011503203000300d0020441c0449200e15a1050200507aa2001d1100517142d029811400e200480c0281c1c0190100000161201c2c00c080007556035003201c4e101102c030a40042103410000304d42c1d582026160290001e9101804169810305103140070000c440100c820400440d040407070113060003014400c1c59242c00c8540c4180c2c0f1000d03082c102c2c144440b00d940724001031060030052445580c035449090b002c1402030701d0b425074000c1c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811934253 1250 811933003 811933019
    0x5011d0c0d27030201060602060709050a1205071e030b0f070503040b06010909063503070b04080f0d05041110140903010f060e04060e0d12022208100608070f 69
    0x30580b5003400654031842030300102c001154840401e500c203500114000b405c2c48030007814258090b00c0390050024001c03082c02543d45104c400f4050383c460482d0002040b24506000b440c0c40102c1e400403000305420f90111484105694000c8282d9001c0c003c0183e0b603440e4072100ca0308084c0110380040c0051390510108000804400016420100c1490008104e50702e801c80c403000c69059600090003454090600c80c1041c1280031043c0100580b800030760b06000211040f152a882503043c01003d0a501800050030404140c05030341002e1500c00425844031100002d5030010b1400b902c01b52135003992030300c3d411810f14203004140d1803044240d03030302d00e1000b8520101c070307059821004a0310b5142d502c50101040c2d0700703801e100e0721000300550845c00c0018106810020101c0304c80400601e032907000103903080c03102900a09003030320031051108010b079510002404844102c04c0d00001104448110f02c2c00140c0e0313000041c148020510524042152aa5998296940d00306c0c46c81070a18910310301c041006120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811935503 1250 811934253 811934261
    0xc0a0201180b06190506030a0b01031a060f0d0e0304030605041506141c0b070e10030c0f050306040b0a1509170a110604030605070903030305070e030a021e030102070605011d0c0d 78
    0x20701120030510f0344600c0090002e0301f0071500c6e815183d40d240020b040e01e691500175801264003d4079880c091000d050041101841250900808502c002954107a4a82d2543c03107040004441c6041c0c0b0349413a00c0741303080c10103094140c5091700c0c07800054154004402c00b0b4170490b800c8610b03c48010459240c10400e11a0145490800d49844040103818102089800104a20680e6141d850712680f051400400094030003080c00d034410545411a100c180d070344c002048110f028000d042c880c2e100e13030318480000d02422404401a03003050b00000009203540120347d0380715608041d038403008109920b80f0400c1c07500300a800d80120b45588044a9280800c5411480d100c00318000340c65145400d13204d031104025120144c0d0140c0004074210410014982c5c03500c40c00303030080050721302910b030000c501000035610320321603002922039407051042c034801840290801e405254090001e41d1070b650303030741022001400f0034480e1503050b802c0c1000d04c06805121031803261007800050078540c20000b010301d0b104010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811936753 1250 811935503 811935529
    0xe1f0807091a07031b0b0112020a03061e0b01050a1202220e0a0b0a05010c030f030e0d08061c020d060207050705281e030212010b04050c0a0201180b06 66
    0x11000101c40841c514003070380c1d1400d0b4030603600b0803030303e0765003016140c0100002c0380c3d02441c904011010302001c00089162183c4d90444e1204991880842801d00004034252400e52005200c0c03031030000c0703000080c2c14240700601d10341e004010401146c2c1c1050010346031072041080190018821840f503040c80356850380507090a0180f0318072102c440da4501481e0980340100d421a010344403420080000329034483c02070140310501560155034030340c50a00083c0824584560040901944201c0c0c900700324400d622810a404120003111807241d000f04028201c0203055915030b0080030350240e00c04000c091400041c5007a54050840c048101054940d18001d42006034100d0b4540114000000c050342c45141044200007089842d0f4403405203680d404465000b42da06c10483c0c005203441c0c11443ca6400d0301e9880c1182e4040c0c07038250030b080b0302c209040d00626528100f42d5201d4685818010380849a4020f0400070380309070002c000110700b250345144040c2142100520b00075a0b400010401d0074581a24502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811938003 1250 811936753 811936757
    0x1b0207121e0206120103050106091404031b020a090e0606091b070302030415030f18020310020a030b030106030b041502040f050d020f031203100605090f0105091c030903030e1f0807 79
    0x3004895800a030395940880002041061350034010b1052010071700c130340001084031a60403c4038a40d04010b9081403a002000a41880f00080040341c4c1c2d513250a0075000f0480d0b0040030004182e4070307a01c0d050010b210b08020001144600400035403141031000743d8500601086003142c80d081c81c11007041c0719a91014400301d046000612002a102c01848a80030b11342803240ca0108500c584412800125520708a5190298000c0e09002e000750300c0200e41e022401d10401d001681d41e8140403010750150040082c0341d900340d0302e041c4000040c003110340d107014000c1d4412800d000024003a041031109030b000b0743c043d084401c41e400070204070b9407804100350f0424600c082c0c40c2000300703450310780000e082070b40c040341d210b901e001e0000c2004081540182420b000d8000f0381002d07420070aa010100f6942007807444102c0c18810300045541655840c18840e43c114216281d2203000720300d451800500c0c0240520080300810380169100d420780c42c003060350304100c005092035683d81000c681412140070302c000e440707501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811939253 1250 811938003 811938053
    0x309100b19080c040c0f08060603130b090607080f1e041a0709050a0803120a020c030c0618010f050103020d200a081b0312040b07051e011b020712 64
    0x20381109282100010982d5030007404001e005001800240e80101d13034020704020340024074106160704075541980002e0195521038981d0340d03180c0349425205070380c140a404c00d42c0e45010030000341800101180308035080c3d5038410b6039490b090902c03d06030000340da4070001b1550401e0166004040181c2456104c0e008072183c2804401e0b0300d41c03044140d201590240009031584105000904254404000034850b0310300451420091403619240e441001d042c03105d982c1c1c0c002a07a0080701d01c040003a10138440507101038079180d0400c1c004e941c058540c0d03841d00411035400d214082c1180f00c0c03d445000e04894001d4440b5182000e9955400c2210007400c82e200400a1103c000058607125985484050030f0502c000b0510100600074186038084542400f510030360010120209200d2103c0a41d422200f08001c0641c07100c00c286015410721000d0782071418034900c000d001c500160015001605a040a191555101e05020008070386421007030203144424000b142880d00011401d20b0f50b001d04d0302c144a0500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811940503 1250 811939253 811939279
    0xd0c141f0e1c0f03090b031e090f241f0306051306061710020301080a0311030f070803061c021e01140c060106020f160e042603100b0309100b 62
    0x1a20070340c0c4007003e891800640e80c1035010507800c01c03804000751004251603030039441c080ba10482e10249803690120f203480d1440118080d08400c101566940c04010b0a8480e409510103604012010704002c243d2100381c420046030050f49007200da84a401741d44140041050f04548501c405004007601c1d24000355400204c0d000032401520a6401414024003000441c031420f05072146041d1440303a00c2d03000c462041004202c0d01200241c0032803440d52509015880341031245115040d8003601000c1d01d440303100051001c0801c03820600640c400e001c1200d102001c160340a0300800b840f102208000d42014001403503d12240000105403030940301458590003070100041881920b0300422882041640315400600038150188510800c414241c40102244110248a24030300c132014854500103ca2100c04103043c800011038ad4103140d8800d800c207001c500080040310101e41c1c02207940c40c9402d4124500802c4140e41c200032640a4844140107014203078100c50b85100500d005030b9a20381c000d002030070f44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811941753 1250 811940503 811940539
    0xc1d0d021e09160e0909070608060d0803071806081303030f0e100f0c0206390a021006121502031005030a03050310350c0d0c141f0e 58
    0x510407003200a90300d1030b0f2004880d0282490840c9502e80307200708041402c03c0b04400b00092030200721042442c0c011010744030fa60128403041e940f002d0191807a480042045a8070f600000c04010008045003040c030b19580e60b203070403a01d2020580d40301c641440c0300404180441d100382c00c0445030b0040200c000900111840c4603e181480300801c0c42005929844c07690380901640c0301e4480e86000760300241040b8034003007610340107071088031070781038000782c201c4410f44941c007a2014843d5900e1103088405940c0d400c010000b941d100c3c542d085010440742440d03408103c048201901d000d4103a070040315450400f09002c0c0d401301942000708661101440c2c60b20018150346d04112100c201400782e221031380c2c2c80c10300f42c881c940032103020303000b1810403800646820740d810034020a1300c2d92148441000149500e150b054241444813600780d50764000c13820444201800000541c103001c8907840100c0701c4008004e00103000c00160b2201900050b090003540000620f4000c040110400c13200030320710103480c07004502c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811943003 1250 811941753 811941769
    0x1e0709060305010b13090803040b13120e09010f0506040314011103010303110705090114090417040b18100512041b15120e0318030f0609010c1d0d021e 66
    0x20a036010382d102c080040450030040c17030f1103080c0d0041d400140300c15045d80c1c03680050ba10024000400f9103085c08002449404a02d1a130400c0355402a80754400c07500d0301c50010458521080c1c25072169410900011389040148145411a28054415400d0501c2d44d250308201c11010302110300c465486248100e045081840210f001c1c510944403954420100f0080d02d242c40500d03001640500070b02070050049100302600c2c00b41d0304404a0700042550750301d207172408809014069440c0e1810010034041154400720028040c600d011801000c0c02c0320080c1c0800034140301c04240c00000c9001042240005482c00581660150098402c2080c02c0b07900c200c2040308003004d5100c91080401c80c06a00c0c0480c0e40b004200a0491202c40c0c148458810320f42401e440b0320504040901c6401c152a20800d1600c0600c01c20844401c104141c1d00f462802c62210b034043d110764030340d81000904046c4191040302c016050360392400e501404030740304103800e5404d100e140c0040c81120306101c901060060000da41c0c4000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811944253 1250 811943003 811943009
    0x1a0f2d060f0d1508060403020c060304240509160f030b040c08100b010806031537020403060506010206040804032d0f0201020106060504030803060609060c25171e070906 74
    0x42c002a1a00f510181001c40005079007000400b0b40203007043c4000700794001425101264201c880300e40d80d03103c40c6841c80d1040c14640c080350a20710f0700f080441d48040b0944c0510b108880000686030411181038801c03030211401c0c00303401e0b452681d4100910100b94400c01842c1d205101d00b15100791191244581c5241003824181403003103640361840200c055a0001c140c0382c100c007054008100d5044c07044a07480803198000c10071104044120b40d01800b1001c00c0c3c1d02d00320000c03003011f4090a082e0800030080080c1d0303c680004e90700ea90410b4042415548000f614920690700180098245402c40d6182014042c41d81140701c803040660b0035a0345494500741d409400c0710311a840b0955071890380d10000e42500d103203501180038007100788420004107244004580d802001221402e81d1418140000f500d24060b442c40c20b1960303c208200d801d620740e0800e5403c010800d240e08840c8445a4514500010350401c1d0b58485d403d40100740c00d0710544c480c061400312122001d6060b141406e0711b0b0400300049034070381e41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811945503 1250 811944253 811944277
    0xc0c030c090c0e030c041104051801030b070c0819030603081204030807180501030f020d0e0703060f02091806010207080607030b011b050a030f0302040305011a0f2d060f 74
    0x94010811182203102d0854400d4803030501043c481c05140000741c0f6841c0303d04055000d41c7c0c4424800c401d2005840440300506402002e500006494010010556800740011100003610001050350140505a01040151321032011844c00e029644900c42174040c5141c000f05060712a480400000e050720040d201180307014900c1d40c85031810b400c00400044001e004035043c4030f40c12104040000e1031500e8030f0b003541c0c001c1c2000304030301340f001031000d009204500207040c500d880c01004466000c000300d070103c1100d028240a21070180352030f440400b00d2007011711440e071111281d006480440c4182d10b103d0fa228905005540710305a41d85102401c20030f08031042c5002a54801070304d601c075a04034890440d044224001041e0750a010358540340d48204c803580203020f1060642039100411311903012a4040d40c1c0c000005c1c004045160380f21080310020800c07051050140c3c1c2d1000089080848402c00022a4100e212440d0200910084412002c810103960000b0040104a00b04001c0b00010040c01c81c0348 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811946753 1250 811945503 811945523
    0x110f0405060d0f022b0b150f09100915030203012102030a050a0837081012080a0f110601150513080d090509012709021801030c0801110304120c0c03 65
    0xd445240c0217412904c17050032040d89880c1000e90ba60f162220604102030300ca4202c1c0d0303a2150800344450300c1f0300641d1021540030340340d1007800c0c0c441c0d94012042030454445001916900c0381044080e020383c0000d000d00151002c041d0044018403a4803407450b42c00340e0010b03095502c5080181c5178035003002032080d41966105da0020b00120612071040b19175803014000006c2c4040c0c0740c1c00503100b25980b6019050a02089042c030080344044044014480081680e00741c501000301282ca408141034000a09450214440082d56074200e03000395420304c03145030400b02502c0c2c260300740b00d00c12021445400d00081000720a014001641d051403c031440076120400040039009000c480c000e20411060f040640109504d20040087e10171103440e0074a04480807040c6403071540007446501c01400d070054060351180a1800307100c10702c5e0301c0f902a24141c03406000346c4001d0940711a0700030309a44903484005072414007000064003240400c810644445a00d20300b6440b0f4954a03140c411845110360010344020900c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811948003 1250 811946753 811946797
    0x70606030b1003030c081b150109051501020c1201270606150c060b150f09011103040f051509040e0d03150e0609042105070303110f0405060d0f02 64
    0x1003140d10302d81c07100b0000590200c850440e50000c040345d84401004107070340000f150201c5650700e00c0c245204501d0414048542d441a84800d01200303070b00c20700c980e804003031401d00070401308940c4005058404074181c000b400e6240091051142c03070700c4a00ca185d0754a540c0c44605038481c64001104682e02c603020103906011007813a042c08422035180b603010401c030380503400e00360030070313503080b60358115400d4200c0380000e0b0b8000000045003410707042c50400340011000150380c1030300084010140c070344d0820a03070b107a1140c0b100e0070701300540c4e9100303a0140c1e002c5c5240502080046e49404200007001c0c800f03c2d0806e40c1081d82c0c2c500800d0690354441340e61103071138000c2110b024003141c1c14400d801341040c0d5000c160b40e44030b103441619601c0300c0d409801d180c0906071000004007845024000042010501e446d4001e000c070710080e0041894212040440009082c5a000e590072140d90050f0f0314000282c040c1140340528203070400a05500400500440c191101c112201c00041c2c0c0c030152680c41450010381d40380000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811949253 1250 811948003 811948013
    0x18030a021509240a022206111203160c0203150103051522021c030206070f030212130f050105040c03030e041806020a03060305071409090f06150f0607060603 69
    0x1c001007501c00240e1000c3d007811941015290390704102e80c141440382c649900c0340d141d910082c0c0305840800300c41004025817550448082030301e22040324025030b20b40c00c142d100b200601e5180c0401c09100d041005e01400494480c90744481c940c9101709460030312901602d0580e001c2401c100c121203e1100000a04004209001d42844a070701c00c0b8070f101ea4460b0881c60804105000c0c0307500c0038407030030000c044030240504540340d40072000000440c0c1e00e10428440824030f802552000e0440d070500006520401620101e0300a0090303034190a8900d03a280c030a6a90003481084d1000c4240c0203549807444201c00c04040baa00384101801103020b07001c501ca0701411420081c2044024148842c05585400c0c1000e4448801900c0c95050550002015a07520201801100079080e2a0806401406aa18002546540e16010100c3c50f04140c0e82c0b4144d581c2d4100c038050300da00400300724004a40114001039405154081038420590f40100346529901080307001c80c0c520341180703000310b40c51940ca03241802030103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811950503 1250 811949253 811949293
    0x130f180602131212140706020d06060e040b0105031b1606061406120a0f0b031b0315070c0b040f0b011401020f06090a0f081b10150b0405010818030a02 66
    0x3c4901403090442240e41c0c8500411080d0303a19001001160f2030041e100061040485000725008101951102c0114540a0081101b48039130030114094281034820380c1400e01884020b600b0586641d410359640010b07121601507006401c4103942030400c504015402d0302c010350f40250340112400074002c1c1c01c0201054004a07000707030f000c0c40394070103005094105a0020780d41d035005001da400400c01d0003404010034047c064070002142e0501604c0412480308900c0d8001201340d1000720100e803492410600007400c88a016a07030b100014400c0c010030004917203141d03041d58126200c0c11080c0018221500c8030411003d00780c01807042d104291042c21090340e030401003640081d070900007429031401c00214450f5100d504900003042c0b1084806242d040c031a402041d201810103100091100b001c0900d441502e03000100c821000c0300d4071f040f003111500501003d110b4107494030441d000e45020305017030042d951440e00820301d5589907101940c034840340e0340c14000f40240051710b07002840c4030748820400f54850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811951753 1250 811950503 811950509
    0x142e03141e192a120c0b091005220603060312090e130f060f0b01091a1c1d030a090b0f0403020126010311091302130f18060213 56
    0xd601c0500c803101190315407407082c1c51040c0c0c040f40c0c00d04a40303007400820b6051101c42c0e010310314100b0000c000040080c0e203044d450400390301c00d1031100c21460b25413412900502403c1c0010341c00a00008104805038041c0d40140300140c0003201004a40081c01c01c4080743d40179540101c030000307842d07200030030401143d21141c41613181d071070801100090130241015062a0300130700081081003020070000c1407201d4400703e00e013003070303002403040c458541810502c40181491232050740c00541444c200007100ba450340100c090840703105541a10706098005041e669203011110401c003960b8981c40f04040c9540320041a5034210044051500c8443d400c1000c1c0c21a452640031100c2100200b10320403010500c00c0481d800d4a50900b480141018140310b1403200c1e402100b5480241410000082305010f99041e414031485403c480c0759807a42e0342c103156000046000c9000a411032801440c074028154242c003d00c05224000c02d000801606221090320203680d05102690405e41c0042d111705c040342c0c455805405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811953003 1250 811951753 811951813
    0x1091a13081b100903050708030301331d040e0d1805010804021903140a1e151d011d06150a090e01111b01142e0314 51
    0x42000041c0310310b1000c4480540705100d40c489603150020780e801044500c01442c0c114044800d0a40c40e81c1324150f07658428060075603501203205400200904400c05542c8840d1041141e00c4600006201a07400383c00c50080000b0340d6004503501076158440303114820103501c1e0300004001d003545141007e0443e144085222121142d40c4506000d1a40c00444060b0850760591381c45070041a54440451103003003603040103240c81e541c05525581c40750002040042c0a018000d641d880d1182240e80d46040c0f41141c5004100361004103a0800034009607200f072040e6032407444180c2030029420080d070300312002e580b0926031400c109103923088600410000d0304c0d070205541d441d80864030310349800504441c1503803007078481031600d07100e8104d007000382908034942d001d43d01299207072141c1d48a071001d201c204521100380c08940c42c0102c918480000e0f0080a4001d00200d0301800c0c50031019454a01c800c01caa50b1403503490190380d000003000034200800c0da500c14001c107015001c030000e10400454511440481c03081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811954253 1250 811953003 811953013
    0x9060405010b250803090d08091f05060a21032316060609060303050304060507180b0d060b0d14010806070228120f170c070f0201091a1308 61
    0x4140c580e03900700c1e01c140100c10750790440030010301c5807003003d241c030b4503030040c2140c0001c41404030080e00000c0860549910f501c13419090342d0b5103c60b0a99440824025051845c0c402140004500300c9a201e560804030180c548155103442e0348011198030003080030011001e54040c060002d042e4000c05804600840200100310004c0d9190202200c1c0240070200c00c4184007004c095003000682e600c540000c00307041d00203100c8c096607424060700710741084030180c07010f03400d000c00039420034030070743c080da0020701c030207101054642c1000906503172a08880088101c1230390314100401d60b01040000b0744150300381c00c44041684c00481300c004d8003a02d01a4010b41465200100344141260007181c0c041110742045501c0402e00740c4880c02442550102c540505240310b00d4000755400c83d80f1003840c100103151601d41114403804200e40d036082d0f0340c5c00c9a4020801c81c0034441100060707440001a00c0c5103005140001702c80380c84420503a03030107900902d00c080c3c1c1c95001075050380317242c164a0306200030080a0007070700e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811955503 1250 811954253 811954259
    0x304050307080327061902010c032f0d0905060109020408010c0507050d08062205150a060e090403020f03041202010243211a0403120c020c0d050604020906040501 71
    0x4001d881c4c503000300520252441c0034280c1142c03502c90985422441c1910124500c010000d8080c2c003d0600504650001e42019461038180349503110040b0849072492a8600a85500750424050703000b81e4440010591180304180c0450b03420881e95000c0c0103203800040c1d40718584107905085500d40c3d43c0031001d000c02841280040740b408180b0020009050405220710703920100000e03981501c070156a00780811203065803042610340c5e0700c00c6118072580200c00f0b44044001c5c0802c48101c025200e480d00080f9224a0701029041c89880250040c0c0300340102c0712040c0005101e40e04540060b0049803421700340d00801801d542e0304004440d00f4a602d160801d60180c0481c4401c040c407030300040180c005001c01d41d96441d03003403800c040d40c10003030084401c0c0100c04411410104802c9041e400d06465912085802052016440d141706d809243e040c1c42da24540c0c00f1200d031000280803005083e50940c081c91041d0241502c4640d40c08803000d114034041d1000d13240a204000100703401510160060f071601c0014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811956753 1250 811955503 811955527
    0x18050111030d0519091515050a12060608010c05220b0904150302130f062310140301090c020d0206012102060702060f040302032803030c0e1203040503070803 69
    0xc2c2c80d450b01050b40890749a82c1e00c034241c0d00d1100f10710038a10134245007140900078400b1043c00416401c042d4202070006c41e80010420f1348101050088580c410110710080150040300b0f407803200f4640c80b5071b4001c02d013141c3d40c0310b405086031003e03840e14000c10030002e0941201d24030030102042d8018100351000f0300703d00300300c04184a4001c541c01280525a6442d00d81103050380320800600a542c02400d6006080140e005400a003a040060587d06d500b0b10b074000c80d1a003e203203050f0702c1c0040c844c50380341203400c0c141c8200212040c0402000c400c0c041d164000c1d40400c0310300802103010304026240400e5000350140c0c000c2c070b0510380007484c2c4215080000103020121004070b60113401c08140d80f00124070945800091071070705c5a500025070040001803081c1d140e01c4410f001d0f208490017102500d00f0035080607203007142101400084000c4000d04541c0000180c0070750302200d840700081c03800c0d05040d070302403002c0b41c3d10080c5801021448e0340045401c10082c41e04216040180510002541c1854450074903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811958003 1250 811956753 811956757
    0x50405060c21070c1203020a020c0a0e04031803080f0909060d0f080307050426060714040306020a050c0d030e0c19090b010203070f14210a1d0a061805011103 69
    0x2000b181d24480001080d1068800c0002c2801190440d0011983c0401d0701c002078001c4d8800d040c20005801100755030482e034580b007a150801c07150507008030084c4d17544c0c80d0f600320b800065095000040361030300d480100c08a480704000c2c00c0c441548030300082d603850350304040010407040100454498a201700d80d1000044007030740b056290b43d074000000794a0352521442a01d0324042d40d000100340705040d091030f41c0041d20038010880c1302e048080980b0a030740c07180b2200700d03504180c003404002d10b03c004020800000f01c10b0390040100107421702e07100342008207503200c035801c140d49400d8a0300000c2e100d04010912501c1446068941d40c0304403030035005511000341800390030a16114144c142c960301c02c907a07040c0c0d034000c2c41141c50043c1c0c09501c1c02c181d07a40c1482c0c421000091005003c041d44682d0a030486004d2114030356074440d66805c40010b0034411050b004485504400c1c02c0e4504505d0b0380b0640e845184c4880680602400c40c2d5158244c0d5800c18018543c030000403030344180d04000d81304044000444010003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811959253 1250 811958003 811958047
    0x2041203090e010b0c0d0c0c1208040314010213060e0406051e03010f0c120e01090f12020d030203010609172d060c0a09050d0f020a030809010810030308060d06060513050405060c 78
    0x5150b07071f100c900d80c148400208001d40c44100ba000f003290903801008050002041607e2080d2400c840500400e100d050803806511009182d011840000b4400d040c0038200000004200500100d1002e444030701003141c48045001913051420701a025000b14a000c1c0942902c0c50541041002501c111400c001c040800001890003400d50f1600d080c0711111080d081032083c2d0f5000041c085468440e850001010300c55104002c0040c055200b0b61134841d4400d000b100d04880d4035546282e40c81e42000d1081b080e40070f084801c200148200c209021000a80d1600c0304d8015051031484000e41040650b030904040c801400343c0814039040109038401a044410441506e2003541c40795116112880c00100c1019005000f9510000c0c07020000b04000e041c80040001c01d03c20790720b800d03540c0c980e604122004000d901008022807015000544103050101840c082c1c907000c0c04011454643c1c402c041441440020748900c0a161114204014081308010958104002042035031800c0540c0003821104d41100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811960503 1250 811959253 811959257
    0x10215061005091f0503090601090e030306210a06020d0c05030417162f030c01081803040f030809090f040803040609112805061206040f02041203090e010b0c0d 70
    0x100383c1d50502e031600900200301d8150803024400c4801ca0b07450107061a0821280300d04640301d8000041000320f118011248038080c082c0045055407200400c1006050001d00c0c4400c4c444400c960110b0b000c1001c2202104480c0224801a55141400328804c251040010140c05210303003042403000245000d41031710b841c00b9082c0c08080d194030140004081c114520700010300070002c1e40b5025900c14550103190220080d0400400455034040401d05840d603200c4452140840e80c12000a00090303051500744c041e000e040016280342645a200f03500d040d1807150010703039400700086014600f03400c0c06c01c8496001031650224100915241e614454544002000104450f80b50041c2904104296121601540009140405414000300742021403901d5100c0320000c41510f150008007410040111184102c1d81840e021056441d5400c1c031014202420301d1000380d40e0308000c0040d00001403500003881500c651341f240d0805141c9001c9100004060300480b079150010000400d00000c0010081c42d800303518 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811961753 1250 811960503 811960507
    0x51e04060c021c08060f01030c051b242a040603021c021b0c04020a022e021b0607091d06130f06090f060e040f21030b010215061005 58
    0x70300100c2c02c04414841c00651000b0140f0703045010360b0424040b40c4252416900b8500300080c020044040e2754114450b48046030040040c1d4800100c01c404d400c08010b020400c407040b042442d442c1001d04a0000400c50721420b03590280207243d100d202c2c940002040c035030b043c1c800300d11080b0100006072140b0f108000616900080181d0262400a000300d08018048000c5494000129803650b05050444a012540c05080418035032854544286c843e28100ca03070040008140d01003061040e941d07407108403406503500c460074505001c01400249400c641e0b22110711340001e0601807040c6403210141480050242c42c0105001b03c01e43e0600400284e828940c0120312504c804001c15071050b54150803601c0581000618024080c0301d4001c10115114060204060311052614800302c6900c0d0241c482180c10b19404600421200c040d03e40f1903600030b580311030b07000040c4070500c03402c0c40d0448010404070b034907840c480400390380610a01070600c0303600351030901d01c0c40c0c030000103924100a103980009000d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811963003 1250 811961753 811961771
    0xe060115030b09041109131121010e010603140312041502132c09030901080402060c19020a0504020705120a0905030609010510051903080703270504051e0406 69
    0x1c2074000701400c8101500100150800303003000e0740e8040c00d810540d800f1341e0035000481c1c01d0400200500c10660b070001c4056282814502c01c03c0101004c8540071540c1507075400d5600307031065007032140100c00314401d00005030301c03032071854101440c401d00c404007a02c0e46c109110104201002c4805164001e40c042d0380b8404024031600c22400a0084203440340742910044008030708809800aa03103406d134943d11800d2525007074411502c106c0f2800701c4074a1203d800c14040310500d540659101e46c0c00910041c00e160a000d040034800346071869265460540c110120440e00c190b00380624114003400d002c0d103056241c030070241c44542d600c181c01444201d41c1f402c000764000072144610580c0025140080694050f4113050a0550103442e0039616144140180000021589440d4100624108000c5d400e07007030302451611588119000701d01c0590600015040000b1000e15840d90004103000182650a40343d091200780001c80b580140000760702c0c4010b4150100000c2024a801c0d400b6a105d0000f0a00c040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811964253 1250 811963003 811963007
    0x9191e020a150306080105010b04210c120b0406051b190e150c0115050a1a0909010605030a054b010e01090c08060a060e030a081c0b040e060115 63
    0x40d060340085102d5040070401041c0590581100c1c00f102c500000a114690700d0380100f040c140718070312800204200da02d40c1e088110520385408200d250090701d07209540c5542d001003d41c0d040100707508031540b601d114200400c020032486006d07082400c4c03880e842c800100301021402d00707200e01e562a0036a8941c9180c09003089104180003d08040080e02e292880d2400711182c91a0f40c000b42180c0d48154201411003078956010341e040c0045580040c4041c512525002600c04122940181c29010400402c00c41105882d09400240241015912135940b0300c0c014168808840001c0c0c0806400c290b088056201c24140b000c0b80e604000102c10038410400c2c8000b18442e04800a01c222401c0109490000035042c84000d01103040790342d111001c0c0515050750380b00b200c001800702c88171940049420400c0c8556403054040c101c0048000c1d00f100d4010307680d91074000454010020080c5131900c6801c058100c4440f40c007403d01c100a059406100b0140720148032902c604050082c1c44c80c140c1103003041c1ca801c41c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811965503 1250 811964253 811964269
    0xd0216050d11040e0f19080415020111120411011106010b1b06010306091202070812210103060203071211030414330115120209010c051509191e02 64
    0x304020300030403c00382400c03001d43e22040d10b1a000c16880c007546248960340c900741ca5506c0052584920058a07250030b2551a00078640101013610440d907840940040d10802440209010040501c1d845220724082c603003001045e48844000f41003180c520318000302c0c02400a559819100c02c149015210a419042015151002d100580c842d00c0784100010600c01207901c03210819001d0000d41c011020504d40c03c1e03a0f2203a07584149010b5910042000d40c0096008018003055454004e009582003076401d0700260003602a0010360742e0780e40c0001406400350b00020100b100801607042449090883e0000340300501009001038008400b20010004c044010310501c071591f40260041c0d07415201c41241118081400c03500d0213040000140042010a04410031440c1c2d001555589c000c0e803a244450381019401010b40a4103000341c20113010005001030020560407420018400d01c589400c00d01c003460482d0a426155010300e40c0192070000c03480c8403040401610003000359041c0c078415440820484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811966753 1250 811965503 811965533
    0xe1323100e1c1b0b0f07140310051516050c04060f0807050904060207051b010305061225080318030d1e03180c061e030e0d032712020d0216050d 63
    0x44d541c0200f0013a440c550404418050b0106a640981018280082085030710096a0364140002d594000304410300d01806400c04900305a15050b007828a510455503c41c40304140c101c8450704995a110203c0c00c10b4482d400c0241a05002a114503280c468030584804840c0034250040e00008006018080d0540480d8081c03036110702281c44501c100b100c0e11940d031015030030281c002402c0002282e468600b1641030800f0403100d4018042085412402f40f58542514081c0d411005003e400080d007840305001910203203840c01c0600410003102c0080504000201c4500740c00c0c020001d8101914040b0484c2d00d911444039800d002805040c01c20407250642c0c20b96a00030052070b40703000c1c0403e500b0381c031203031001080c95107441c0780b0140d90002105500351900900c012203554042100f9082952080d08582c2c000c9440e48030f40b4104a03884110005001c080001c142c55910100162116080c0c0c10020001c5503002d52001e000440c1036813035503203001c000e18801c1c17078455510022107009210310b1400c03024003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811968003 1250 811966753 811966763
    0x60f05180d0c1401090e070c030e0a060306060207120302034303081e19060806040c0302100314161b0b01051003060e1323100e1c1b 58
    0x40c03298a41103020020a005510f484040c602c82d210581d4003c0e010034090781c0350340e454011140c6d2040d00032505003451130400c0d003c00142c1141d19031030342c6440d03020f0320103402544d50124403a8142103020f498110030751302c6002c01040700c03031102c00400d0380401641c812a0001402081c8178400012120699004990841c1c07401140c0040c50410840d10b102c04841c90312030b40f10308160340d4880d02d0b8550411038902c3c100075920304480004d45911a102401c5405a2505400140b51515065128a0104100e07400c441c00040200c052080d40b80180da0750090002e5480e061202c0d0b610511003294018025005103606a0315006900906014824122500f542403d0354100050b250409200da501d083c801c2901070135a044d03840038a144240200412b0320b212421110349078441003030003002e0341010901920750b070030480401926140c454a114644641100007841d10108c800358410171103e2803291711405604c840401c0c0d42407584c469480881e903409003014031140451a02540d1040c1c1030100040ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811969253 1250 811968003 811968019
    0x614060a20100c0305090c0112020a1205010b0a0206130c1203051c1d0f0601030b100e04060e010b0a120b191107060b03010605010504150309151a0a060f0518 69
    0x1c4040d00303034800c3c16040081da40900a54854040c071a89030a4500210340c0010a0520840529017980d0002c00d0503400d540340920b1442401c80c50002210803c0c1c1001400103400154a4940c90341001059049840b143e030ba2240006941e440c2d48901c0840e05c60300e17640e102c1601501041c14051410384000410400c0304a0000200482560003004101c01181e0007400701880b5001100c4000350401026101d000180740590071038642c1106500002d00d041aa0080d515000c200882143d08141c00740380700f0000414035030141e119560950301c0b8040500d010710400c40003004909404580c4030f24130354003c4c507540100c0d1074007000301054a0031a19018403041c1009541c508500010004080701030280c1c0c4104441c1e21200d08143c01d96100d1311590380050410f103c00d03c41304064440380060000705090005071508d081d5641195207450480c1088102e03642e150040100c1341c549182c25240800b1184034011508100e40070700141c201d0840442041404942c1c0c1d00000505407030f484591400801e405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811970503 1250 811969253 811969273
    0x9230a020d0f0b010f081005120f1c0e03030315010c2f0306012411070306050c1b0706270f171005150f030c04050f06040614060a20 58
    0xb00183c22070064407400101448450580c0501c00d096050240d10369001e801780c454a00020046046404c4903600c1d294020a60201001c207802c101400e1001480c070000d00700c414203014003400765031031400c1141c080d410405c200039100b9a40c010300d0300c0444c003d090080c030f1400d850404540300900800407145c20407110410100e2243c1c09200484135540817804c5030030301ea0b01d62018402690390602055684211343c10080040b0340540100584100020b08035144c1903503c0c2c5920043d1b51081c2c442c003500c400c000501c0700085498903116540403007806e0050103400d00d0b0000050001443e84414203006c01c24691450360f019419090100804480000c40c2100e0f4840099180601100300c1480507440394110a4142d6030f0b80d030190368030171548480c403c3ca50b4214681401032a450303202b05543e050142c80c00340c0240b40d0303c03889010301903540b01d5480351312440c004003804121041c070303009401c0308203071076075005030555030801110f003000c10514003d0346000b42c18103000051001401c11340302034000c2034200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811971753 1250 811970503 811970531
    0x312110d06260106030b06010e0102210405130902010903020f060d0203010305030a0941130905010605030304032a050d080702030c0607030503070807020f0111031009230a020d 77
    0xc0c000b14441c040042034030103108070624202c40d543d110003000d04000c00001403035503000e10600744001c0010300680d898940000c0c0030b04910151806a103038440c001040c01e000e641451281200002c01c10070003040f00204030340020f4980175803444003d02c50440320085c0003503900c4807019602e1003200f041d015922561a85007403078484e001003000e0400909640c0d00040c8107607006006940c203039a100041480038410401b04440d05003030018600c0b6804140141508a0302e480d005141d40c0b44100000094400051514900b5900980d100c0d07031082d4010b0000f800800c2c9106055002900340b01d180360506400088081070718121940041d41c0843c0581444c400e20901c80000c2468901c0cc4003903600e4029640704000040c01500b1003d030015a041c00003507041c90140c2d04076078020b00703540120b4209122001905080d101c0301c008408400b600441441014140408000c01518040105200e00461a884400090418080042c051202d80701044c00004180c2c104c0d4001a03800c01c0c20700030407040e0200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811973003 1250 811971753 811971779
    0x4020a08030d061d010f060311040e01140301111812011b0503151c08071b0b04030605090601031106250819020609060a230109060e070302070312110d06 67
    0x10301390450009545601c8800d294190b40d81610765000c4080b03025420b0200403402004501c01c44403103000100f001180f80142001d080b13000f0b100700c0d0f00940c030803010034080c1400e403550606441c10302d400034400c070100d800c4d51001c030109698065500290740515949410b025001c88070255100c9d28100480d420210f03031010045202e850004051a4848801410b02074560031900100c200a441d6030103090002c1e050310002c084290091074900c0d41680d40c040c614511002a0303204140b40c0c08001070030010001da50040682c0001100043c1400b589162241c10040c80070143d6944201d400048124200c42007400d4658005a880d0344054000c826141ca6001a070000f846848008000804400402d10019010303204586100c0a0440f0b5240c40f02e4460203003610030b0340c0d4044540703030390103e4441075881110310f402800030010126480d031400c6226910408064090b200b05401044003201086c0c01500c100382410148100044584080044143c0c81c01884904174110f0308081d80082d2400780f03909 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811974253 1250 811973003 811973009
    0x1a01140d02181503070c1401090c092705060105040905100e070603060e1911090607050318030316081e0703020a0b0705040f030602030c0705070e010311060f03060904020a08030d06 79
    0x38103007a00d0401d541183e4420f010844a200c005070312401a04002240d56500c200c00c80390b140004110003c0e40e40d54201d5544541d00442000c1c0d0703072104070440d1490700b460702070300f100d04149083c8040da003207880b080c0e2505014001c0c1805680c840812504200c02000040d5501d0307220070b400c000c0c1400340040503488007524450712000900b40340000c240114054070013802410316140c0982c008409140c1c0a01800d0b80090641e0b895a09011548507078913070310b0081503940c1c0700b0800703103a40709000394110b51010313207160825000754000d105013400b00030124002d60f40720390803001513602c03200c0c8054483c02103012501c5600c240307100854040b0400d5000100e920302a80b107410029000d5481d480115024001e500c01e5001410054008002081c00d503401550004070382113000e4903040c042e49502d8508401d0760710004e0001c0d0311303030010028001c6c2c2003c00c004844044607624505a28108200c20500010385540d218000060100307046658030715400009101d490250380d01c840010000c60001c00041c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811975503 1250 811974253 811974259
    0x40b090609180f16030219143a091a090c21010c0f0909020304020a090504080a1205060d030f110d0f090503030f07080d0e0105040c060f031a01140d0218 67
    0x124100801802802510710314100d440e801d100e0b4003410a0b041b00c4801d0b4403800c0030110001048110a801c2c04420304042c8a41c0320001340e4420096024000b11400c040000c011252b403419592200203421041c9031100d0703030a1000c1c040101c0c4c03a43d02e400760030614008aa954401c6020010b84181c0c2c44811403601440c060100030050310b0010710080c2c0300070104ea80c801c00018105035091000b90604e50103560000d00207041411417a40b00c01162086544c26501a140700d06c0104e8860f0310143d010032480881c00c03c140040c0080e080c010041035140303010410040612802c03820f540f100d1441040c83d582492005800c0b1a0700000c1502c0213440c04607011070b44000518010004140c0e414000200c59090f010081001e04d0031485855040c52504040340700c01240362500912107401400340030302e50140b405968004089454010f003d40035617030691448080c141040341070701842d0741621903118000380a00303043c40c07003600001d50008c151040c9196a40035a201003003042c00d84603412022070103a2819 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811976753 1250 811975503 811975531
    0x1206010e0316060c110319020307060e06040e0405011404030909060807180b0d050102040b030106080105040516030f0902030106030c05030606372102040b0402040b090609180f 77
    0x1400a140d02c0e144480101c0c000c0307203069001008500d01ca4000c1400c120300038a105e10380030f00d514000a0500e244c080c14548865014043c1d041945403d000700002000c11303040121030024250003040050050744204c800d02954080000c050110a402003d910204040300407080d03e4103190142054105004088020345841c1000c030b18200c0001f440703030a071440d500141c03c085500c1000100541903c90000e600071220404180000300240003420240180706440c0c0c2d181d60410000900514059010a00c1030341001c0903c171000c5185184545d41c00018500820b5400800c03010102424603200020741540c030f481e40000620a81c050381000303480f000c90580f142c5840301c40c2040405444100d28131191503c05c220102e8010328007a503004401c0203884564281e55540784e510001c002c4484d901046420204000811481d0510600f0083c003c2141d04508150400c0015581c0f409064031070b600404000960550f1666481200122040a24020305081c5050029401c203054143c684141180359 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811978003 1250 811976753 811976777
    0x11090325080f100c0e06030705070b060f0d060c0302090621010603021317120f1206010f020a031404080a0c0603111219090b0c0408070b030603060f040512120601 71
    0xc95440b8411090100070840024041da04000400202d00043c040c0480911410f50a03110200514855151034440d581ca50340d140c00c1011003080000c1009103da08252014030780d0b0780e10148008052a0015000503805002070310031b50080c031810b23044552010010bd00698600d022024402c40303a080d8446d085200c1e41e0b50601a0140e0191402200c10340b0254501402106205a2405002c5030306100721200014524016a543c0c2d10030b00340803c10010005400944421000c442900a4030031310745299031041c107010003034a414091000404100f14003003809004c03180705080c0d07006005501d0039580010b004c3d1600e038158502c503104d0788000c641416031400f1211802d20644808280511a850080d1b403040f41c0d003441ca001c00000805281e90703c810250102c0e07010308045202d00303035541c039a6030b545040c04003061920f0303455440290075101c00c20804c0640d0314081580d82c1c0000341c920100e040d44c0c480c0e01e0450b041842610040c0030448011500c08400e02c907480745280101c03420313240c080c03079160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811979253 1250 811978003 811978019
    0x17010f03030314151909110304030206070207050907050901030f060b030910050c12060103090b040b1905040816050f2e05071d031e06040b100e0a11090325 68
    0x100c116901c001c038940007400100c503400c0000000c00d181104034804540361b41c85035100811124030a090121404010003000708154041011580083c9a4002080c11358034103130000310032000041c050340c20050003103074200721a4025002401030b80c1850100b80655034661212000341d820495980c20140701d400303001200320a03948a40d600071041c04039401d24100c0d400c070405100343c2001d0200c604142ea200e100901051224040703c1c01107101c1c0340040b81c01c0c03c2455201860440f241d600040726441c000c1800005860002140c40c0b0741000c5518220781800f5007802c80c1802450110208580240b0280311148920400032620154030301590390100d000d01c12203c4210740c0c1c11a03015003c41d0b803501d40d44200040034280344c185d901e001022580c00f148242d80c0f9004503600c1e461203119652103041400700f000b8502d0991640841601c0d010581146803843c5036400301d00107010342c0c100c950f03240c0c40c1d602c000701c40300c00300d0756026005807c5840680b4504117080d12012072070404000c003250002e01168500f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811980503 1250 811979253 811979291
    0x6020a031e091b06020a03030b0a121a01090b01020a200d0602040e0a0b0d0201030f150306020301080d02030304200d0b07050a03200a0e060405030a0b0702060a11120717010f030303 79
    0x244c51540140710340d8000ea40c081d00117041c0282c103150b011264600000b5124440d202c0502e4240c41091003240c282c41c140141c2ca032040341a0060800b29060086142c400e1340d00048000d07903203800114500d400805001c001c20841001c884594100200d100c07c03200b03001031038004000325007520400c0c010907611114540e088030620340c801036000000d0801d0501540c481d80103031292980c41a800900c500100b000c103240b01a0581c011a00c882e0080b0042041c2c400600c0b140b04e1448003400607610b07514080da604510311030050342101c000c1c01d00700c03202d80c00758a4240c8005415503020305400c01e54100b10030b0250081d0403007056200028203002408001300391180e040052240e0b1955014240041240180c4049000085041e0020000e20001a07107030750410525142c2805204503148504100c1030007401c1c40301c018030640700d042c2028113100013210740781c044506407110145c0d4003140351101c20301168814020740d44c1c00c54400c254800824114440103ca50440b442610100b156413180c4810349005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811981753 1250 811980503 811980509
    0xc190c030c0b0601030605040606111203220f050105041a090d020d0e0303090d0c05130b010804060c182d0806041214070303050a11031306020a031e091b 67
    0xda40079894000003212401d00907001541410080340c00c03601d400200302203070b4aa600180026005d4186e80808071014088840c1d030b03601e0964614031310326008403101d080d1481d48604041070300c50149a40280101640d03241c0034540d001c002407150782482e09003914402c107203250700c0c0040c00e40c03180401e84032800081e103400b079940c1d42d401400506c02548030660f00640c4205469416020030401210300b5aa0410040310192003101350310609810700c1c05025100140610010901e860320ba0f2040c01c0d684c0140640f40d0096002c0c00103c0d2480c250382044490307001c0520007045a02d8013250110b101c4000c0041001c1c241c0094182c1090544007038500f4403a0080340c81102c4d040d4104401107030210300720031714800281042d8102450319140b0756050400f0340c1d100000540000e90766100b0302c01d407903010b80520a1900e200c00812030650918a603100c400c0380400c5401040d0740d80c0012200500740c0240c22031f41d1084030500710a04031400c08034012014005014044458800fa04c90704041441c3c45501c40c425 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811983003 1250 811981753 811981757
    0x18040212011a0903061e070507030e0405061804051507020102090f0909120a0507022707030e1c180509040503040306020c0705060409020a02150105061611090c190c03 73
    0xa41c0c2d10300540410407a03003074154803902040c20015a0403a4078200308440c0a0b101041c43c10070350402c0705035400d0310010301406102c1041000c10000010035440030f5115143d2b00200c90004154640200040998884100f180101564202040240400416024520525400c42040d0703540c510004908030301c60b0802180e400b807045443d01c220ba0802d444605e520084540445480180440c0240c1c1070303030840d015040004200103039120443c00c0c2490310320300b5010b00682600b59541592201010b4201c014202801c06542e200b0b40044604100031001d1290a0a41ca40e4091014007030024500c1071100e0071503419440340000001c290401035942031056030030402460800c1d0450f42c91401941c00443c8208051154540104459580c1ca0081c0000d040894005994844100300641411410a50b0788078400300c040040010751140021509030107142580c1030304d402c1b081e140c5210302e0321030254150340040c1e250f01040324800440009000e4070f41c1e0381c03141c80040070700004112820401d01e003000300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811984253 1250 811983003 811983037
    0x3061802040b06130909170408070614250609020a0909061107030206010e10050907050913060609180e0114041a04121d180709081b01050f041802180402 67
    0x172030709540380c1c0401e800034810806145500380704111300314039412580110080307801c40340b420040d241d0017401503805c01119240140c20995000403403400c5104d00407294802480341305890041000c00d13071043c0403d03607000740f0b0b0308080380e12003502400402008204540851a0241000075080d07540d05441c140ea0b4158018070b0141e0906075186520300b00a4002144d0b40700e0458040303040ea03100c3d0a40c038421a60307540c9164070b0300320030403c1003c0c02c03a028800d00003c81c600035007404210b60280d4070074195a4401c141d82129440c9440f00001041c6401c084141381d481c2c08103543c00c40020481c00c41c000c07802880107160f05414500000342d48901910000d002c40f54500405c5c8000780104021042403406442c80d0720700c00341c04c1d4080748100c0405080e0441c0e82c2c24010400c40b03030b00d0304140000040e0181c0344c01050b0701d07441524285000551510401e0520a001c1100b4110400102c102d501a01c2129131101350719501d82000c2020303400c043d034241c0c0209450280246142494820f542074403201003c1d0034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811985503 1250 811984253 811984259
    0x180c1403150d0606061e0e0a03020f0d060e0c0102010e031207080414010c0c060c090501020c24040b2701051801090b0a090f06080402010c170403061802040b0613 71
    0x80001401c0c444058100c40325440c201d0106045204080082c0101d4986808809002c280011840011407040e0309200341001c001000f031b110b4141c045d0039644e05498505a50b0140030000301c081d0303400b64000308118144403200d101c040300401c107001500e10a8009002c450b68442545807a07024010312034043e11803040c00195500c0c481d98806030851300800308640c4181c1f07811070090a452800d002d00c40032440400fa11400c01080e0300c01c089500009161601900c0c0c20500001e48410b070002e802c41c4903444c4e20242c0c0307464110801c01c1a5455920004c040d0740c1341c2c1d48079000e00c202c1d04594001003100c41140c640c0c007035041d00142c403a5604141656598645080000c1d000b036a000c90611940c100448443d0110300f00c401400184841d10098540748905403500404a15520441d040441000540400d010060341c02c462480c0b132050384082500e14031100b51041c2601c80c0110351000e44402d04120f40c80052030200080100c01d18000d0340c040c04400f80c40400c3c01101d01c5078000c08549144a0382c0e0030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811986753 1250 811985503 811985521
    0x603080a0e0114070807030909020f0a050f39013806030106030f0513050d0818070608090c01020a0c120807140309100f02030304020d1b180c1403 64
    0xc029400790504000742a120032945515a0341c1003034604880c600c0002544800381134010803d480204200c510951801c410507104240c05d0040103500c5042c0400840d102c1c41c5160030905651102d201d0201888182d0150700703841244800315400d102801c044a1141b088106040c040c19100d2020005403442c4441000349100e200c1810000c0309007082006400450b91fa629080207600034810703950040380005507070b09a40103c0e200034000c0c000040c184070402e00021000b154609800400d410a0b001540da4170020541d10038000030141114003580c1d00c080f070f4181e040707182c2e40e000f141e070302c0d00300c1e19401d0622005903078580d0b0104024104a0703183c1020496010300f175403803041c40c0d44243d0b4641e082005541d40d603444065000f40001e41a080460b40c09440c1c1428a07843c20640700ea0700d44590103940540002c0d4491001a1010b40104101c603207413024440145800c6203002000c00300c9003030040e5201100250801128a80040e050030700c011040440d02c00c05031b065050304000c102038078517200c04401d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811988003 1250 811986753 811986767
    0x40201091a07061104050a0905090d031d01020307050703030e0f060a0c0e0607060605100f0c0b040f021003090b09070f140f06130618180914010905010e060108010603080a 75
    0x24840703a81c00c08004020004509009800f05580081d000c10b480b28140700070024402c001d9003215508500d00010412411400181c0c12510441400e000420110315003032040150754080c6049425800041801003059018000305040b078000d603401c00007213401c800516142c04002d9401000740d441980172880c1104550303c40301c40d44603a810480342c1c4550f100042607440d08070740303015107006564650800c42c40c1045001141c1007842450450107159200c0c4002e0001ea0b030016000d09500340340700c0003504004c20000340c4100d40d0303001060440007122905008001d051019001c6440d00c0f24400402c0051038009044c400341d1300344404140c1030070f08100c10b4040c0707048400c801e40d520100440b030700f10142d200c031070081c03c40400100f071101455013032000103000c00302d00440d20822084540e0080041000e04154070340e400102c0040468004000c0c00c000d00b090008000501c020751925480b041000015440340e03070100088410303104107aa031054414220340c0d49101c0900006030401a4025a40c42092 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811989253 1250 811988003 811988039
    0xf020c03120a0b0a080f0d0504080715030b061204210e0f041d210306010f1d1c0303050a090f0f080d060e01090b0a270902060f0a08090604020109 64
    0x2600401500001c0d071601348542c00041c058108603100814060284000041070700107003011481c0034a00003410350b032540d0f01d125400d40400c11050fa50340452103904003c0088070010034240c1ca898041c0d248001c4480c05a0703040b180a001016501070b403001030490034102d80d25503110005112404c1c02408500384c003490b1450b83c419520394820a10880e0401d801280760440801450a8803008a05c0802c94800800e0f0b0b180e1007506204009a41c0c0e40000c100145410500c0e000307640b08146850b00b0910b00d070072000564407080c28102d0100008148100150b12806560700b03006a485000e032440c00c0316071030100602a00c2902e0f9507400805c1030704002c12507882c402e90400780b074030300500c0030038045400359000152a0810400108035442c028012480340000488410603090724001c0d1401a110f0b41d020001c120208040142500f1909170f4400150a6005413805586802c4c201042080b51302610810001c24540030104081003000100d072441641c0c180c4170360340c4845c1082c000c41c2c1054180e117 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811990503 1250 811989253 811989271
    0x1106040c0b07060209131d120301121e060c140708030637030b070e090403030b0a1d06010323062209030914010c05120309070308040e0a0f020c0312 65
    0x400748001e130301c0d081d00040d000c28059800045987d100003034501440700d44148050035902810308003011400c0b01d01182d0448500140c030301155082072415208142010980c4c011041c196405002440341c3ea80141002c2c1181d17a42e00c4140c41d1503000003038411f028080c400b90620340309000103151420615486d0501c1020b000341450607008070706a0001d202120520080031320b42a00080080004404055170060719138244184810b840d90085081d00600901c090101601c5040807400c6894501b0400301400b4500d00b004c4101d4000d1119150240003902c545002074501007030105a103440041b00f80310352201072451202c4d0f40b5040c0c10031801d21007049c00380c1d05558a550702c1a10594440c4030304150203100e51543e8200ca840c000c8003240e01a008a03a05040c0f01080038140c0028801090b02042400341c520065140d40b1440f94061400c9200d0700010300240d400180840c03a0308294640380d00c9290680014042058000105001d17402801c416030003550050007a104d01c0440070b6202984040c5003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811991753 1250 811990503 811990507
    0x60902040f2603040b0c01060902040b030a0c090b0a05030906010506031015030f0513021f09170a08070510050a02090a0b070f06050a0906050604060f26070905071106040c0b070602 79
    0x2c0441e45045503c15848900701404c0060a41d0304c0040a0142c1801003280647c210706083c5844440c0c1c8031848000c20300e0304890b503501c0c18141110300440444001d8495400269218865039101520707a81c002e540d00c120301d00c07860000107054600402203a01c5884440b480e0b004035071030070300200348500c0002c003210103044d1500c0980590b485148500c40c0b203841202c0140d00b03040402d006025602181d1401c04200034031f1401a00f00345504030402c00100c40ca003c882c1211441103018040c10004425001441d45400081e2001400743c0000c48503c3c200e0508410005921885080c004901c10258015044614110204414910b0f0710140c203020b07005105c00c2c03c8000c06980c0740e40440300104c03000020b095486500b001441024820180c3c451300a4500700001810540091103100d41c1e441018140c50740c25060a824139100c170004940c00000c5002c80d4041921a05508044d20084031503400041c80e4803448802d0110000b000f0b8003850704079003e50815800c0c00f44640309070b407040c1810b42e040750702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811993003 1250 811991753 811991819
    0xc0f220e01290d0308060f0d050109050c031506010c140109050a050d021905030301030b3133020f071b09140412030504020a0324060902040f 62
    0x2e00501c100310410100381c0100b03003811107080901e5541c4241d00c0e07015042404441000030303008185660468800c648540403440302c20000380118411180041141d401c3c88840c8003005000100510011021005e891204100b5842c02e05000801c0b1015400100110240c03004035080f030104001c0000254004200002e02d91145403800343c9441d0102c5581c0e20100e822510036905014100341c00c0c1d031100ca07481400c84503480d500d64074001800054071801c403c9000c100500500d901c152001d8682d86000c1d00d50921120518107107520550050310724403814480d03204034103080d1039600d202d48107041c1d201c2c44407070300c072801040250072403d60045940f204020a401295219a220b06d02e18981c0c481d41044a05001c651300541e20899421801d460401003840f00144440038082c0560302d01c0d144c0099aa500d0b800042c0001c002544060b169100d08041d981582424950002040c02101d005000d035641d2100c100049118600c140d00740c015003900300b8003480010805900203c05803a0001c808421 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811994253 1250 811993003 811993031
    0x61401142a0a0b07030606020c0312030c0909090f01050105180a050402010207091e06120302060708061c0828020c0d0f1e0c080a03050d0f06170109050c0f22 69
    0x5038a94043d120140341004000c81c5075450b00403103001d413000744050991381c4041130200f55500404152090340103004000141155101020380d111083c2c0201400c44a0805070201501d81c115074528100b994280320000c00c640c144600301500d40d4810341c08800c2c0030742e0ba440c200c800400c4040c20807811806102400640700c04240110520480500b0040718010410700250702110b4240d40090017041503002c060011903004904c242e481455414408282e590b000005108405086d80449918803c06c40010a011158014000c40c11401c08a024422225840403003645c0b0358ac1402d01c0144e01130041e01c8541c0c01d001d42c2c44401c242c8900a640300c1e050140d900c40c8003e024403401d1480444201900000780007660044130300402962003d0441c0d00079988000780580b19202e10b40d43e599407540d1074030038011155401100100058481c08004858001c441e50103046410802e407524481d04501b02d5079890605101e5001e240003c146203d21900d180321900200c001c42118008690b80341341c12341f1040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811995503 1250 811994253 811994263
    0xc030604020c070806161e210204030512120f010806010603090303020c1014011a1b1e0c040e0111030106080603030408072702090108070516080409061401142a 70
    0x10041c02a000700e45000300300042c85031841040d00c9100c01c642d4006051003681198204000c2318030345044000b000c0209414601030310581d44010a5807103100200c06801c560003015044000940c04c0074003207a182c0103114040008280520b9195070005001081814000c0d40f040913940e00c01c0c03d01504180104007030a00340000310300c04000c40358075011000f01d0b0f200e500009030301500901d0610711500982100158041c0280e515400c0f62804440700c0e2101c4181c20412003031821511039581703a4280340030100c0d64987c0000103160740200c5c20001d90241ca40010302500c5a0000400c0e401400c2d83e280440440e40700030040c1c03080c1c3e01400300704000b01e10110140139820180401c40154440070000841a150b2806141c080030641c62040c4801304035aa0700190703a94010002d0f00e080c64865658800712810f00c4040c2500034038901c400140000c0021300d079000041100e03180111294201c0c0d5950040d00c113040d000c112200030300c0b810400000d210743c1003020054480420294001080c0c07003180303124984 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811996753 1250 811995503 811995511
    0x60f03090803270d020309011b02120c0405011211210a05240f04110109091a0a050103020a090b07060204031a271921051803060c030604020c070806 65
    0x60f10002e04404808030b250307003061980e41801c800030031402440c110000e4583c0680c05059041001243c2d6a61415429070003203061150000c0440c83c51030107644105aa03a0b440b1500c2d14091401c143c00000e00d4000842000700c015005030b140004c80041800b0403000150b5250201c00c0300030b440d5281030795403c0800075000c045200301c005000e041d4050000303500ca8114139034480341c0540c6403070070001414030280d9860340244c0d0140c082a00301c1000d40044c0d0703110000340c00030040d0a01d401c0426141c0c26030740e40d203903004010a60700071101e0750300e542c0110141d1180c1040c0350f01003175541a0403c0070b0381010f00142001d50041c1700040c20f09440f6598505242c9c15944404413103181c100c10311481c0a48110325268040b11046001c8808543c0d003015a1a040c894184d408181c80062006040c840527405242c220901084004860388078100c0c041c007182c00c00305070740c0c00ba504215850000e606001940602508680c002d55040d6910a000c0002070b6000783c4050042d070041c08000a8190710401c106805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811998003 1250 811996753 811996771
    0x30709091d190302060c090d080c0c0319110a06021e150f0601030e01060f121b121205040b0904020a1b061d01330b070c0303110c0109060f03090803 65
    0xc60b42c0c040c14000e140c807101130202d001901c801c00481c000c5e82e41c1d203400c00c014650b021400c980c41d4810ba44039a81050004040300e50103000b5030881462100202c44a03c61081c4034100195411001d0024003403441071a019613000359002e04000000e445420540d00060380415040300d2049801ca42d0801d0301c54400c1d55003003040381c2d0400c06d0094540c0c05000301e0141c4e480030030080040a00c0c1c0030403488000c1c114400c60392129000d5134030f1000d02000d20851b40382d075030700d0001d440c0c14541d840c04000c101d01803424080d41c80070702c60720b400d06150b84241c0c03c44c1d0443d40f00c0700800e07046c207145c401004000e40c82031103003100380420483c0529144640c41070b0a010a402507100041944000e04080e008051107500388005900d421a0f4440000c9604000b604122000415030300803443d1030011101e107581c85d08030900f0020081584020015000f2000090303c0c440d44d180c0300208680e00c6420b030b0307569281600c940454981c1005101c1284074441503490307005140307800700e440c4107180c50300780241e48151000f00b5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811999253 1250 811998003 811998043
    0xc0705120306090a0209010c17040503010510050108132103020d05070309060c0201020703120509010605031e10050108031b1612021008130f230a0b0606030709091d 72
    0x102c0c3e28140c202a58800d54801c002e518005083c00002c12002d41d9010041c0641544800d004a4a0082c400d45026041c060f008010a0918110300b0b00c6108481c4101070007c3c031a100090107440d450340100342d0300d03540000d90600c5450291404002d50b203044000604065003030004000d200114010036004110725200021045a44e040c540c00781c400c00007010b400e584c0101b0024000079809010351080701508400080c0a8450f00030300c40c09000310b41d02540d030500c920107a10140408403a50312003242518400c0301d0091201c2074001003960000d00c00c040c03103500241321880304044840103610804008005031b07444500b00502c6a081b40d250783d04071811444460620408600705030603c1c801c49512414146601d00d42070b07000b0459800780f604001c0045072210740f00d904000b404003c801070188038643c410007250700e412900e592100d00180542c0d10f03450600200b00241040002c880c040c3c00c036a03803020591428500c83c0406807410010b80040c420b0f1031100166000c86c240944104a807511050031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812000503 1250 811999253 811999261
    0xa23040510020a02070501031503050d0203042c040f020406150908060a0203090d050715020307053015010e030316050601080304061209290105010f050f0904050c07051203 75
    0x1494032094034a40c03000c441c81004030449454000403411700b00c030024030300130445440d84414100d1b031090990004002c1e02c62035000003a01c03a000301c00740003035031041c00042c0c62000d000c0400440d00009880141c003440940c0380868080350310165224211030010304042685680ea1034050780c4035a25014400c00142c00c0340c410700580405202c030382c0d04040c03c04030650a504046440e00d0300e40750a201503105102d800120b84041110f104a24200117115010840d22031911410140aa9114142003818a2185c0081800304e01c1507403403808805915845161740ca9942c001d00b00000c03201c001025040c09540920f9070400d9404100419000078154603103080c10350f00745056442c0020607002094282c0040c0424070005074040d00c8002d820300c00c210040740101d0390b400c01801c0741a0920303811803180b1081040f20110f445d03080b200d6040f11000eaa811021820140701198035009000340403a104c80b041111104602c0c1a0300216000986a0b00c13aa00d0440c4565a2070701d85480e04040c1011410007000304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812001753 1250 812000503 812000513
    0x50106020f0114072102040905060a091b0513051c050c030f0d200a06090212030a050d050c09060c100c0801030305070b07050c01060306050412091203080a2304 70
    0x3940c0c0d2420300000910100c3d22840700703003840b07550052618040110ba21492402181040202219008980c0003190340700d807a03c50241c06008110303605806183c9203240061422081c2c0710b446250700d0700d1525000078084010702112254042c400f102c0002400040c04a015620200089607100034824a02c80d040c0091503c0d6040101110305988203400c0200c1010b00c01d040402c5002064280b881c024a12603503146030360b02e041c80d08045014082c1300300e920001c10481c155102000d110b00807150101c5498100d00b4141c1d0342d10459402c6c100189080c0100000440e85422007504180c0e021312403030500032201d0210f503142d006003007440000c0d8800ea4000319104a40d218414051540d80b0b0f20714010760650b103011b4824420b50b9002807205030725000054045104405a60b84541244009d204050741c0c0d08005016110030b5505485051400c011203445500a0080c8004c89090110650b003002160302c080d01c51401c010013420074103480b6445800007500f03241040c00e40c48100c3c00c4030140d9003403074101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812003003 1250 812001753 812001763
    0xe0303040c14010503071404150507030801210611041e030b1302100e19090e070b03062214040f061802030721020603040809030d1806030b01030902031005010602 71
    0x14900038a060040358050740d1000817680d1041042c140301c2c0e80085541035080340d900c81d5600020550302c030000011401a80040200300c01402951404413a90700c4807172080540e08400c190008050f0f400e04c024000502940042068820030b06103e41410354079408100500030f2403070b11100801a4000500c204450784d010300c1d03045459000200d008e482035a0220720350910800e200c4041c0032208226031541c1e50391101c540c80c0006081600310010781c0d5076a484015210115040350341d8042c015020030407002c09000e41c1e1041d44018921138131404080400f201020145010450395610380003404482c2e100001c2841c0114410f40c91400407a605050407001c42e900c0c005000350444081100c2030141c2c0d000600350080e25020013400701c003404d0f848000c54003c0f480210080d00440d000c41080709211912001d03180e00d0100703405032840140c07455012520381d401016000510351100383c0a1241d148690b0024100e0041810700181c084a940c0000c0e00e05810300081080c4592640014041194107000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812004253 1250 812003003 812003009
    0x270a12020a0302240c0c1e030a02011a030703021005040801020315010815150f0702031905070509010612110d0f0507030c230304061b1119052e0e0303040c 68
    0x241d04840185080d50700c4401304016110780003a11010420b414101001c3c890176603c02c41d00104103494250300c10f026600e1350000034120740554038001403204031306000c041c40800880000c000e460300600315030810445001002040381004001c1c4404a4100c0c800d00c003c501031504032030b40fa40310f030032444001482028010540081d4814104240101c0e4403240b95681010b440314100c1c58803204e40c03c0b1507010750301903928060f505221300b50099440f044040101110140544103a90005440b42e080c48088002840340c0d00001e03145503040c5200300711640c410b8403601140d5540c6450003811862000c203840700350320120300243d6544d00780420150944900340068142d400c01c1801c0c411840244580b0501080802c01051740002c0000d081190380c0c0d010307481078941090540c5030706005400050003011591000461441060164600d503030024418162442d4000700500d000d1403414030080500707040741c0c034488049683c210003644942c075a000f040782406110008503168903003070034600007920450b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812005503 1250 812004253 812004283
    0x7060212041505341125170a08160b0721050603070e0603010f020f030a060501080402100c17180118050f190302180717270a12020a0302 60
    0x1210791344460848142140003004014080c005503000000d007640e00c030034500d82e00360315802100e501c45030407403a010840c40000c0d84146810082030300c0b00d400f030411180580480d0007a52250030410b00103000e1100520846072a004025140112956401000c0710281c41542c041034404503503c1804201c21a2141d40d0040a242407200b401d0030004251501c0035406565842032200c000130b40345840940040d0081022018112f50b130f8840310010294035001501e140741054201100007070290711402d01c01e401103400400309101d03089880c10a6a09201c2d000c400c40342c42d210412565801c900396806415610500d0348010940088440010503092991031403100115030000103201540383c5002c00c0301e514000791500c422008500c03103031500c41882503100951002191381261070700e48044020754083c4001d80c07038080030000c0c9140c29101129048600708522030080c0c00304050981d10074600844a0901c00c16500d10042c2c0f51548900f4120408080d005a0301681070a010583d0411803d1400c40980b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812006753 1250 812005503 812005531
    0x60e0919170f09060703090305070911041211030604030207050406120b161407210302120402060d0b090108070f0503070807180209030303070e0405130506060607060212041505 77
    0x2a655991501c1a060040309101c0c00410089440b00440d01100e0b01c142005100039216101458014556042030108803414020040001081c03151401040341200c800391741c0c141041d040880d11105005008000d45400c1e540c50382001c03280d101400018022402a0f01401540c0d00381011300c0f05031905a0720039249100c91840030b4001c610140000c1b0781080318503000303408100b0703040c00032101010294814032824000055440c200f04951901050951b0605100030800c14005400c1d012406941c4001004110b04400240149050001410b0604010000040c06010700c0e002c102c030b9030401d03000311b49694441c2e617041c0000301a201d1024005c200c00c4009000030740c02e01080e1600e8000324482c480c881c0c0c040307104000d1034a40301d405443c3c8828014040340d40741c1c03408000c02801000c10550180c003035450000801e0318400541c4000c41c105401c0001000d0035150030082c000d040d0320400301580c0360382d1f090040307009000d89818618001d0f8021184001c0203000000104110f0f81c01401000e001d10310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812008003 1250 812006753 812006803
    0x207030809061311060703091503020c0d030903120506060418091e0210030b0120010203070f020f0304050904060207020a06050403210f050a030e0303090f071a2704060e09 75
    0x5113101d00d000110781a00e0311030701c0700d51a14064070000c50782d030008080d90142c0560481d01c00c0e8142d010b800c4103401071040b030303051100800341541210402c0c503029001800c410107080703013100c070b51b0401500b140003d00014a0503035100d40c0d01c0c104007041c402c400041920303014041d0910900381480350000d4450b100b501d1003080d1903800920780c0a411a4030005150721991512040c0e801842c030f40c0d5100b1740e00840c000d041614040154000d602c11a5020041503104040603815803000683e11030a6500b0320056140c1401d0904001c0764403401082100c07456000c00c41c08006840c0c0f141c010000380b80c2d5884560300c3e01c3c00e40c648103030704040290021411400001c52580c0065200d8544100c1c9901414566a40c411046044001d407100510710340700f0380b00c0041808020100001e900281140d810140c81103140c80381c00b80c0284500d0a2400c5416510038483e58490140301004d80390440e5000244800a10b08900441e040d18203a5102410854241e400c02c030075210107120342c24400a40b0701482c41c241003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812009253 1250 812008003 812008013
    0x3021905180a090506250f02060a0209040b030f06240a0b0903010207061d070501050c0d0e031011030601030b0904120e01020f070305030306011e0801052202070308090613 75
    0x2004104220181e160301180c8080e5050340729058864110058070107070720b440300e040c52490140240860421910007661400345115a69040792041d050b4041c02d0a900c0368201d0304080d42040310959846030750340d5224a400d950401c5040381c8194060050001c5140564103408251045403540314030b40c6030009000b182d660f90803081e109645a00a0007074581d50000082802030080080c001e020516042001101a0201140350502500c0f01c045925a503100c600444080c00750000c03202d035592105800310b14180c0180c0ca03030740307480501404a45040321000441810b444206031500c140000c00414002c15503814011100200c9007039484160606066849496038500103410700c0810442d4251540103030701c24003440c1a6217264404132084c0d00d880c0d0070481e07185da105590355030101d100c1100d040003403900461240c404c04007540707482c07410741c0c079000070300c820300782c0d440808038150341c0c80110321034000b200c0d202030a0024040d656000b807928002d0015071405401078143c00702001c2100c11180060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812010503 1250 812009253 812009269
    0x1e01030b3601081f0605040513110103022508190f030605010f210b0612010e5a1006020601180e03041703120105100f110f1603021905 59
    0x950b460140303200040841003c4c40100b1503904101da02c10305080070700c10300300c1c040031800d181e29001d0300250004038a200c005500320300c980d1184101c2094030740d20000c07116414408520500d40211420f518019510390741901c0d00c01c80c3c0000e2401b140880e981c0802d001d60521818020388030a0030b00702e812110211014010b2001102c3e40c0b08886020382d4200c0300b9010f140c000106100001d8442910744a020460400c800c6090007125002c0c1c042000041500301804090326a910380b1840018035003560049819441854989401e426910f040d00705130080e03422250081b848a8811a41d102c80c01e2190b114640d0341203683c0413204541c00714006000741400d00f0348100b848070880c200051010002d1264508500a944c0302e00800520a440107821801c003000a06040c8414940010180c0c0c030382040006150810480c8000948250003002015018a02d01c40400301c0c220200d43d40705001081ca1442c000821201020780084d05800b0411030500380d50020741c06041140c04e4130360078103280116442c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812011753 1250 812010503 812010523
    0x10306020c070f1202011701120821100521071206090605010303050306150f03060f040930022802131a0a090b1e01030b360108 56
    0x1990006406a03540c00401030701000f0642c06203030419035551100c1074400d8003400a01640460100380503207622401d03da01c1c01d8180c1c1c8005180f03044141c401c1e1a4107200760040b607004240e403c0d130b029003404a1084c0f00c011621480307601074100c11003400e19007844407011141c001e45103100242c0c1450300c1100302c0030810b982522510340802742c05402c242042806040344101c00b600302490709002006240c0c0c09001107100320412f0307411242c1224690510350039413040c0c1707803041e80841c42480821020314002c210b1900f5010300030000f1800d1003064803001d6843e54808903240000c11000f010040a20b408003a075244441240007a110002e040000b20b00502c080045012045148010319001c5503101c1111742d42c9412540d10030480280c4c003402400c20a503850841c5c4d48140d41c00f0200252114640c000c00002240141580c0d011008010310310505102d61956141419111507402286484d40c480340d01d11658501c0181d04000a071041081c012903003003100c007000c4500500144418100001c0388240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812013003 1250 812011753 812011763
    0x10515010305100e18010e070b07110a08010c030c0e040e070e0414060a050411060304150f0225150c02030f0a0210020a020d0305060604050d060504020d0209130c0503150103 76
    0x3941d07266040301d011001e45403c94114800341c0000d02c451810f401245e181e4040c6000c00800248400440e2199546814400c5400c0c54400304050300010f8940800094250300103040b030260103494161160030740e055501f460000a955203000403000741e0054148250702803e450410140f190f09103c035440b0074035401080307910300402c0007007400c02207002c141d00003800111041e0381c8203003061000200640010780d0182d40c0030360745901211291520604990040760f000081c50310503056514074401510001483e255096401c0c411660804603c58a082d40f0b03102e40c1902081241c038615240088440c0b44095482061805c803c0602103900003040310210017134a00003548404444000300e14102248020356502400421a841c0b42c80d000141e0420049a40d00c05004668580003071158600a43c4560f55000c62800c1043e00440c1d01c07a80443c0d0000e002a2892800482e00d401203050802d094808001e03441741d0001d03540c00d02c0880020580508000c030081c05100d15080b0000e11038803818003010704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812014253 1250 812013003 812013011
    0x307030311030c0609060106080c12072d02100501090b09041b09060b0306010f030b06090d030201060e0f01030b010603060b0304230f0304181b050f070c090c110105150103 75
    0x1286003001600c640c80701c0142104c81c0751410410381602e61400f8031481e0003013a051008248404829810b031340c1082c030004204605640c0ea0034040703c0243c40306201d050391500180b1088401c823040310903a5003120079a00185011012804c10804a480590201d01c90301d00c1c0c81e420074403595490038516080303508191030b11425100e40c445425032400b0b80d44140104c501e84580080c020420101030f511641c4240c03120150122501c90030b030252018480e086501000405c04480e0070b02d03014010b4090349009100016010b078940d01418121303101031780d0301060205c40400400030080710545c102c1c00340c8030030b103018001d280c40c1c59030200d01408060002402c1801341d10300d40081182c0450311440c856103440440c4c4210030356500c05600d0707900c54040c11202d05000c07824010440c0040c00380136054010016802600d1541050446054001400080d2200e9080109401044840202030003a08030f01900007075404003074030007034254003424100c03001d964180410000070040c040140e0114503401e09006c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812015503 1250 812014253 812014277
    0x204020901110f211305220e060921030604020906091c03031805060a23010902090415030b160201020f070503090a1205060c09031204060203120a060503070303 70
    0x10b6190b01c0a400112038500c00d030010143d0b4240300003002c4d180d07082c1304482c21100c0340e0100c112a43c68424041420182e00949404101a04003489100444902650128040e4890170031001c1034480c0c085030344000340e02510912032664410301114203c40c00541ca42c032001c69085030388440c180401401244555070200c1d000a46840d141c085a0000800800022400f065034500060305241c084003580000d28200300700105000000c10f12103800d0704100206600c0c1d5503d02090003030b004103500400818800e086086650a426104030302034002e10202603260b0304504103000455a00443c41d5a00106401e0100080b50001200e01e411406108110000c10140101a40680314940d49a40100c00000e0303800b040c40404009050b002e00c040792103128090392102c0381182c0300c403201805045504110003085c81d502d03e903c010601407101800303985410640c10300c200d149401640c000c1000d40c100040302c543d000e00196101d40d120380701000c00c000079418140440d5030b44400c1e010040910098039626 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812016753 1250 812015503 812015507
    0x3005090a0f09050712020405032505030a0c090c090b0901030c0306080d11010b030c0603190603021801060806032a01021203100602070806090a0b040305120a1a031501030204020901 79
    0x5040500003510807403150075035a045000090030704540d60400100130b400d4060b0042d80d940211170444000500801c40d1880b001d403103124461408000c04101064401c0000c0c040e1028010540500e018404900100b881c00005900350ba0074580300c1c00401511100c20701494080300c050707455045003881d0000760510001d0f070030b5005104581010384030b4402d6210800405500080020690b0306130002880b10254880600d84d43d0021035036075642c0315205000081c45100301406140009170b441c0340114030145e40c1d8001c0b640170041c0c0b542149103002030000500c1169044900580c01c180c054006040d070000107640c50407160800700440940c4200d400703855045a10800c80c0541c1c820240342d4055603400c0c00c181c103091441c0c032407190308094000d00b240000c4140000c0707406031290580e03034050001403440c0d03a81c0852a03000180110240141400f030000e0348031000e43d01522503c4580f800040103890414044500302c100e0310b40c248207a002c40d8134000c00c5290340c200d090442e03074142c60240e2104056001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812018003 1250 812016753 812016769
    0x8070c02010f0c2a09110f040b0319050c0a031404110907032702040501050d1e03140a0e1e010203040e0901060510080103031202040b030615160f300509 67
    0x8404410078440c5156911082d000b00060304542e11480100140c0d11881d64500580c011280707010041c800030b1202700714800c40e40000b55440300e1403420442c0356050b40c00082085071402c5d5000c851111010030a003c0d801c0e09403044650380d4001c1181028140f60568072580d001041c03084040c002e542d51000b0613420343c0640c00030203d08013520b0545c0c9001803c81407801c601c0600c0c01d01079105038100b20002840781091034261502c0307a08500341d103941c40140041b155040b00e031450103d0401401c0000d1001e2071180c10f0151041fa402ca965800d08911070380304102225903c2141044910640c060300d06a581e000021902200c6562800c000c0540d141424035005007665400640c00c4685541d421050f17690141045058910076150345400818000c01c0904038000c0d8001d0454001080000c02c3c0546000d25000b004d200904502a2404215008084905071002c50448034200049001000c2000180d081118000c4d281c4441c51249400810600030b40c401c2560305045c09000120300c6041c2d00c43c400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812019253 1250 812018003 812018033
    0x1507020d080903191a07080a02180607061e230a0902030d020a05010f060f5603070509010c0c15090e1612180b01080d08070c02010f0c 59
    0x641c4c505015411007902d01c01d003000d804580300700c60001c4c180d03a810407080e8041d020321513560f9065004e46d507030107120000f94415541091080038002c0035502c559503140051042922400000c01d040c0c10040749018441e64000f001545103040ca280601c0044005d2009210301401c5235403c0f4054030f815a007000100b00007940a074140c09003911540805070002402d8400a220390002c202c0030090004840072034031140510024081e500c68100b00f25020664030381511281c0c0940d902c980100a045203050281d07132042190500031a0140d0030300c400c214096450154041d1240030320b54900340d4070082c85882000e0718141170000c0500c1403001c3c8011038421201402c0701401070b4280032442180500a61403c0c40f9031000700047c180064280394a0f080c6607a280500d43d2221400b86203000c4083e001360188158821110710030b20125000b003101824818001c00801001e80300c880c1c0709000081810600804031002d04c9030701c0c0701190040c1d91004500381c0c02d1843c4c0c94080040b10b25454a01485240b0308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812020503 1250 812019253 812019259
    0x5030a02070c08010509031908091e01020c0708070f0608010308090d1509083a0b0319080c160e0c0306011b03030624020304050d06060803030708060f1507020d0809 72
    0x50402618220010040c0034443c1c007030f58050620000c01323804542544085072162501d03041502c0c5400c81072401105e54070f000c0582000582001c0008102502e8078403954000a50b660000ea002c10110681540800c00740c0000d02e0a240780d5030454a0740c80162284a03a240d008450304a0300c035080c089100403040d4909100351080c0080046410a04850f402401c2500118100b81c46264005400132807210003007140d0160502d1541e041b50b0080d401407000000e40d81d01401090701c03e01c2e40305840544101220311440c03402d52201050b03203c0b41d1410441d60714610354803191000c24050303510341040d07841e48101c50000065a83d9122001252080701401c28a030350322a034005a10308164041c1c00c40e9081d00c940c8070342c0c4c10240b101c8150050a81e4220900600940c00400c02440f060420140d0030020900031030700441c01d1640c0e141c070145142d0040740d081000030b00c0042885018030742075614500030030080321f02280c404840e00f0400911b1083c0d1500034440c040801740b440c01c00c200a81a200c0c80b134001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812021753 1250 812020503 812020511
    0x27010504031208040506010f0e04030c03090f06080417030c04120206040f26010c0504030308130506040b0711120d1806060f03051c0f05070602070b0c09030c040c05030a02070c0801 79
    0x20000580302400540d0226444d002c3c0700e00100c8c1409013a8a04401c80d1078100f1030010980f11500c080e41c500d40312010983c10000c41c2d007404039000001d0b650308001002c96582d61031440c507203030400284851942d800007181d03600070014031407020480c0d000d807001e4860619168106400610002d9514461540302d4006e40c00340000003d00f0042d011044c421744040c0076020500030b40c1e0802c030a0701722404901140041b4005001c21301c042031040e4241540002c010030400300014580e1035903490722004031012581d058000c2c003009a090740c04400500800c10140003040302d011100c4030410b19000700c400500c00d0036074449035041c0e48c0301c209400005040c4c010004204044e100d10191400c03901030300090f01c07140b04500108591170301201e2400180c02150341c5003418144406002ca5403584400004d44016409201940c04181c1c0c0700340045c01354002c1d00e24940e139040c0031400e0500b0002c4080d14684164600307074200200f690000100d941c0034141140040e6205020705d48201680340c0d13038000f800c040d072030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812023003 1250 812021753 812021783
    0x1e0118080d18140f0703020a0b0a02030405040f0209030d08010509010608092a03070b1801111e0a02090a14010501082205100e070803040302041a0d0c06142701050403 73
    0x300303c0d440140c0420300c905032800c9003031450a1603038402091100235000000454100825a944400362001d2015032065a1a041d0740c0c1c0001400c0ea4420110b00079101e5001894400d00c0c41c041050a05c0018a414905031546c580800514819814800c0384240310758600011000c034400d22405507403000d20421000306580102d21025402c0c6100f2001c4d00030310442030f003c504e02c14688192451f08003040c954824a084030001100c1c910f01045c0030051520802008c241d480c0c2c0c5054a01c007103420a1002000c15a5180c0100000e140010b0b1004040c0c80c038040a03481c1d14180c01820f181507840c00e09140859803281e441901c0b12004410842d00624510702c800c4041110110352580856038024041c4030300038100c080c0c55150041c3d0b2142c103c0c03950003080108018102500300c01c1803202e041000150314030604001c01d10783d030442030044540380718001d0144002c40e080680c3c0458070144822160911205044481354242800c2494046442540c52083c103070b8030a0044402469028070542010342e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812024253 1250 812023003 812023013
    0x60e0708040b06030106050f040b0103021605030a08060906100c02010509040606050301090b04140403080705070204020a0807081f0b0c030f0415030b011806030f060312021e0118080d18 81
    0x40240c07401c442d0b0b00c58000c045420351905001d82c00a07150010080081c2c942c0017810800203003c201c03141030515030240541156406607140d200c60090241000e540d0307621400500031b02d182c8000f881244225008002d1007501d0b259441c907512464064140b1000c2044075000582c0c00740585170003568081d00f005000300d206075000c0051412191001d40c1800b28014000400c419a1340c42c0003901d8981000364005804248901c0c3da45402000350308015161204135004602030b0780c00300940b03074040f55000d800e101c1a69400340c0d05560200c0044004400710880c08904844200303030b88949040355002244810410b00140102c0d0b02c18001705410a6895950b00320404800c91800342d20f00210385001d1400c0c0c51540501c01002129614a848403105400d100095000f05000b0840c0711100f952500e0210000c0e8610b4100e080045458005100518516440c244078200660800b091039040c40700d850307501d0341c4804059001a900c00400f985403100c94103400010328400b001500329a01c078204d85000d05ca = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812025503 1250 812024253 812024267
    0x509100e01090c0f1518030602130503150c18030c030a0b06100311030f0702030d0c03021e090f010f021005010311120313090c030e060f090c01080106051903060e07 72
    0x500c10094000169501c1d00d000b02c1c4d1252602c19211a640414003c6034a60700c540d034031082d00482002000107154407070703e444017260030040c484800398100710720070300a515003001512040d0840c034240f240d09140c0300048400030b02843e101041600780390029241265018817215252540c050200d80c02c83c155402c2071840700c3e000b56002801200a5102e240c43c442c46402100101d000b0b20720103514507241e103090317820340036801050501140002d00c11b4440034201070003503298084047c0d0b40580c841460402c00200c42407c02c140c2c004410f030030040e140890312065200c9042200c2401d1038000a02d90940990400014240b03062070f49140200202c1002180303140c0d010102c00944e0041524400f40039455944c1c070131500c0501040058000411a0101d541c00a00c0f44c40c444d031801041848100c00c0c103c0c40d003d000e60300e4216458002e810403420103070400003800d43d02400d2910040079490b02101604074890580c0b40c010030041d50030a42c41c554041c1e0044c034010544554410942d1501d080700400705 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812026753 1250 812025503 812025521
    0x90f021c0f0b0d1e1403030411010908030a0e06030a020f0703020307031701030f1515060c111525020604030803060a060201050c0906131e060f0903150509100e01 71
    0xc146000c812004904008a9182c61250702c5480c8108070756130205282603241c0110422100400e0200e207241c4010000c3c406907008a1184200340481c200c9400050401010794000301d0140e031080c48001c20050303002ca03140e101080f0503984207560b61a82110180a40b0a0000c1014020350014042082603070000060103020f002c0d503901c0182004580c045541c036013081c44054100c01080c2e803038501182c03400d603021400d0075200f00e001410110703d02180381d41f107003554040800b040050a042003031200c61b403040d55021404842a1000c0d074070585184400c0d0196100e2042920b410362003a01480100ba0500c20f40c0c280c008003c10b85499036441c120440340d000311101070045901d9440002c4681c014002c150144001c802c46a0510075071205006050f0440c03081c461102d0070071140010411140814240420389070951400c0060404101505d451050500070042110180040011075080140b02610300b490010100740303504e64200843c500440300702003808092600701c181000d11015402981c075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812028003 1250 812026753 812026781
    0x1107031b12030519081506030712180213020c1504030c0501140403180305210d111207020f03041202010c0203060a0f06060203120c13080703050d110d09090f021c 71
    0x180100403130044030050001d84004d0301400030300d205803c0c213142840107964014807a10341407041c100d1003070b8444262550700901038102c005d00b640017429810005481714044402100951402080c240002d94810302c400340364201c92100030126003058801c05421222941100007804500101400c2e50520f2400f910218041440c82c0c0070039641c1419100248110b80e044030140222195140c03800c4000000c8484800480380c1c2005001c45100c0740f441244001c05404e11119141c002c4403c3e40c111201e0301500403010355000d0b41400000f040000b081740d040c1c40c4036400c03480703000c59544016100c60305c05200003035160098104110801190740e10920918001c1c103000e0200c11342c1c80e2000e0340c032403107080c0c0c020310594082000a0350000d82d801c01096040481d80700c4064155444200f2400d288007500122116003048900d02c954942c810104d08254030520302034101c00e00943e0340508609000c0c840d80d002d298513941000c00e440c202d42d06951561141e0303d118111021003036007080c0101300c4030014100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812029253 1250 812028003 812028037
    0x2060c060f1603091718062d18060d060e0a090c1202030606041a030601030b09070609080a021e10020f010c09051503090a0f211107031b120305 63
    0x2e09544240210302551340c001c44c400181d000540003045296001c10301c80c00458141051021203501c4400c002c100c41ea240c503407850307a8060032641c94440800c4050122001c080c0500403041d16000701c0120450403002192045d940c1e0b5251460800902a40d070700042c14035145400b04021904140c0003400302d5841030482c1e858030782e1191890810b680003e10041d415070300207400240c1e00d0406a11911440141d10200c160b0381d4006c4001a1a180007604100d0b0445a101c00307001c401803040021001420171410042d89941c10042d009641e4400800060f2042ca51a90349203010804400401c143d00800303409908802000035010796034403026003a245180d0f1034500d8815441d8842c203201c0003505d4009000b4060540999200001900007600300e204900442010800145901246150b142e120316945500004e044100e0400b004003403101c1d07003d000b00100103c980320700201e204010f5035805528074207030043c0d040402443c500b46421809200040e409094141b5800c040505441da4461903100c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812030503 1250 812029253 812029291
    0x8042102091e090607050409090501380603060f010f030b04050c0403210e1318110f010e030c06220603060f080d0c060c1b060b1003020c071202060c060f 67
    0x50355130202140c05000140050105210340c0c03620b500020302150107070001251581d02e81518040134984c4c4805031039014004a0003401140d401c505400d1009030460700b0034107619107680030031804054144454100f014a440000c802d9000354058007400314090b10400c190315004c2000c03c515032040c001030b5400361b070748000032001c040204401205000c1595a209403002c07960240903902035490011071030251600005103062059010b840f1000c0d008240350700701e004d4150203000d01030300e1080701d031810060711558008403a00e0000e40c8446043d400d885072642e03540d183c0f1540300b5a91040d14070400c040d000c00d40005525070705400c10001d0b20100c43d03801d03600a41d80c0041c9507888606440b2a004103c0e000c000304081107031913101e4034030a00607040214411226201c60320046c400941c0c2251841d0b5035600c00e0046052030070308102e85682e04c0c04e0440c44c0920440e02c259407406d8508c50707a0300ca121000143c5c0c0c215203840e000d4031481c00c0e9030000c4a070380f801c200e000c091540004686044c03000f1407004900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812031753 1250 812030503 812030521
    0x4060807082521060f14210109020a050d0c051504080105130606061704080a03140a14010602010b0d08070c0810060911090907080a0e0a0503070605010e010308042102091e 75
    0x13a4085494800100000c2841c003429694444118804141c1c410700c41c40d0b903680080e08500c000051104440c00006d2104964410088400419000180115101c2d010030300050142e20f41759064501c2144c0e008508803015102d036030603119036007280d5459400c000034003940259400020740114800d072001e100785512618101c50060a6081c06c100c020944408500442e07040c0b402045542d1483c038001c03c034060022600c480030782d810f03211800c046075141410119019800e8203140034010310b03c028401000c800001445c3d001542e40d020303141010008940040250082c840801404800150307201e108000400780007c1c40517106800a01c1d0400303d450000c42c0400b4111003028400400c044404d40702c0388011140d41900401c001c0c1620340c1c500d10030304a01400c00c0f104416910507801035548602d285010425600306900080940000c0001800010030034000d5805542c01240c7c1c010040703007000b0f0114070300c04800740c010b9000f18400052102244440d00080009448161b0700c1c400c5c3c2c0c5895120f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812033003 1250 812031753 812031761
    0x10e0903030910090201020304030b0103122003090f0f09010f03050f240603120c0322050a03120c06110d050708060105030115020f0714120304060807082521 69
    0xc02c400d80262105000c0d403a40d07503210002da40c0c010710450341003d4982d078401c0b806100a030000d6862089010052035a03540c00560040c1c0043c0366a4400c160303100c07102015a41b4000c2a1260f88150190b202c0d110715520303207100500c00d040c40207042107500d595585d411403090b000303070106a170540224038129100b81d01c0016901e00002c1240746080101d00c64015200320318501a01d050340c1401050b50480e400310710f44000e0480e80a00f17801455840c11001d11305160055080289444403070021410020ba9a40c94103590441360444c2c545038146c008120112007807102a200101094580411156400ca00f880600144d02021a04210640781c0600035500d8400449200c4d000650420040c000030714202d618995501c0180104da051140705051941844620f0700511000d4000202800b003130324284a09461840000002e945041d0405400424444c0d00806000c14000d20034007103242100045414150010b00100c02226005008401007005c405100418004941c401a00d070131001c203440303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812034253 1250 812033003 812033011
    0xc052203150b06160312140603060f09150a0c09060314041106070b1302041817030c04150807260103200603101e06051e0918010e090303 60
    0x8202201c25204100140103044820302980c1c11490901c02604916600ca00c2420380b5032280e15100805c5050040380403c4035903582841c940000c2e4a024000161404111580c0080c000fa002400070781d58021041e190050000340c03010a0000e88041058814440d8070900020905640e825071071030303446904509030b4042003144000b4000c1c45003c180050107000c09001c0c1040040d0080e801d0170850f480340c4d8001c0c4412954100441c12064800085203400d10030040c0c1403004040310b00c1c00c905592920f99181e581030030640da10541c00400301c0c40f4140c1c603200b554000c100c4400c05112507078484200414120042d102c040201d400c607003100e01503034000f00c805050705200b86880d40490b03103036496074501605a40015040703186229081e4030b203910380b82d000b503100c1c0a030315034880c03100d506d8004222054034200001e0f840c82240b840091003600e0b0300104603003100070074020720f030300c0d000300c94a554030303680700340f505a036888940700280156200e030b5404124100c4a5240e603d03e33070365841c8080251a403000711 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812035503 1250 812034253 812034263
    0x9041a100605190908120702030c0402120a0c090e07020d020708030c190c030f05211801030c120609140105040209240903030d091e020907210c052203 66
    0x801a4501c0d50074443c86aa6049120703d0140041684c0ba10340c1400c0c505002e8400600c01d100143c804150f040c00c0082c103022000644017140f4140030040c0e100d80c032030800ba081c0410303151550321114115100d000c42001618900c0347e100c0650030700580280d501c1d42e20070102e8002d070042100003e071021011068603440380e032440140c6000c01c082001203002204a000407203080008134030200200340740c9140640f401340316030024140c00044400e219a0b103400c21682c0b8088142c01c002c11040e01d04a0510590700e82402c1c03d010900d0203110b041562143d2440c0c41450441c0e2030b02c0340c0069a8002500911000c1c24240020750540c1d0302c03101030000381c1c4291481c540d0400079030100d40d2a4000310011610721105805906814460744500082c1158070480004d00055292031070b000506c400e5046500380d0081102103403c2210980d0f005c80e001000060840c000c0c0101d50705100b005c060580041650041480d40803c013a03050400c0250590b045051781c0c14042e51404c01d44801c0c03100c85100c240c1566082 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812036753 1250 812035503 812035507
    0x80f04080a050d021606091502030c0412030c210e0105040503030a0516140d1d0a090e010f06091406030a0302060604020717030406050105190b0313030e09041a100605 73
    0x441c0d003911558080510320985039400c0105500c0b070209007402c40c075101d10031034001c24103240c14240000c5402251f031f0528851403041040c0031885c02d6607000c90b002c45080d802004030010441c00c0541d43c040c810100545607a212034869070901c1020350150b080b0b4840b54641c60a494005001102c06008a00400350594806c00103160014002d40c040d108024008820b010310543c9035440d80c010307250403284000581e03c402d01d40b140d259001902d000c5800c0c0c002c1c542e000c070041241c0c0000c2d0b410039240710700c1031100d65802c06071010a000707400005041c1c0098900384455a900c0707007014002c00d544e000b00d0f5401d65031f1801203446403902040b40380c0700a030140d0041a881d02c514013040003c6d0310101044aa0803807290403020422002000703184110300408000841d98505028403110f40f1100f9405910340000c43c4003070080c2002d00055a412040f1006900500c1c0d14030f14080d50070098810007542d001c24041c0030003042100741034055600b040780301100e0b00a6100d4000c000c1568281d0700803940401c0e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812038003 1250 812036753 812036767
    0xf0203070212120c030408190809010809160803180423130b0f060306010b0c0316060209030105040f110105090a03020f1315030201030e2811030319080f0408 69
    0x10089030000b109440100796198422030700d08000441e0300843e450009900049000c000c151010b00c0000c5c4000724058000e05556996690102140710b4505880d0510480c50003040c44010304001c080300f800c007030701444072103191968105960b90f002a400e411003604441d0040403c0c2c2068000c00c90003014140418410340165403181c071100000500c01020300140c14034210100e00c0d01c0000301d028076858544d1209a0400e0018181040c80c140c0000c54070f1041000303440c04011b0000304a0340c2c2078a2075002c0b495485914074141010344104980150300d50300702014002840007081341c10604610503045410140d565100554550152001d05607004032030200801c003605010900c0780d6802d000400d400780300c0344052070410440b0280030b01c0d14503a503079144042c421540c140c401e1403000c07124140185481042540400380402e40e6400300d02030083c24180b007008001006140c605500310041c1501c4e2907005200f0001a41340044080400142c0c80c2000314509000580c01d0600545d00005903600d4419 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812039253 1250 812038003 812038009
    0x3020a1406041802070b0a0b10111b121506130b0a05041119020f0c090f07140d020403030c03090e0f04030318050a1214040e071407020301050a090606060f02030702 72
    0x80010300c401401c2d408229017000145c5c0301c800a0302c42c0880038000078901c480032040c80901c4d41c240b0115000c1c001d18592200c1881000102c00105400703102c2098040900c03e008107024442042d0400c2c03942c0b160ba6032005205900c101c3d02c510640050303d55410300c55106021101f9103c40b000c0e0a500002c074014280901d05094200d00554050381c00d10b289041034231600c1d0506001c00201520043c0c00c001c1c50b070007503c1400e0010101040040390180a90b0070b2281c81e0b06800c0c080030f0b1a104c00d02032004001a400b400351002d50b4100c940d4603104646855490801a0503030840d01000c42c0082c607031010209203003d410703d80c1030050405509540f082d60380e655040d8018840c075000740b241840c0804d514000501c08101400d1072610442030068100080b40740030308180722407440c081105000380000e001800e1079a0025074000a2880c10f03074ac042d82a0011051103106030780001e50503508003401c00c004600245c2021500600c40c031010005503560b04001c981251002d4075180c01601304000200243c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812040503 1250 812039253 812039279
    0x503030417190f140d0e0c060909011e0f03080d0b0a0b03272a010906020a0305030a02043206040b0f0c030d0207050a0c0e0705160507050907020703020a140604 70
    0x14203418440e0a035031402e00c80f0030b0381303410694054217401d85405000354106400d000c0800205401e0392801d04001c2e03180d0000c1c5030300c00140180180c1d0340c00e4603031255401e082149690b0082495800110f4815180d0030140e02561124552041090511031030442d2030801302c1c03070b1008690500340180d0850300e070346042c0f076000f078070054181405861340706001418107001e1003030740c06103000d480405200c103154200c855103004000044c0341c144020900100602a004030304400303000e90610b005641c0f50b40d000f41801c000d020b6600142c84024031101c40c1c54480d24000d61068145007070300d00383d404082d055001c0014034421030003040d40201060004000e90b04814000c0e111604050f0240c80c10040c03503150007402c03a0005c810136110380d8011030380d001c01c1c40fa1424031b0f84003070150444940c0841c81c100034050100e02c901c299036615100c6009100e01440703000e1002c00060003000f045140203003040c041c000d543d40741501003a4810000c0d541e00003000108000d00701090180a07001c11708281ca4100510245 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812041753 1250 812040503 812040527
    0x30c030726070f0c051e0105060a0e0414031204060902030f06010320010908010c0917060c044412190f0203040801090f0b0106210f0b0904050303041719 67
    0x20000d01d116120006030180800030306d40e0444200030100b000817902d51030a5444c050540f034000d58103004144604001340401c50b9226801c42c4000569460401d003861840c414200c0181044000000f03100c1040013542044400038021001c803a000703094040b0403501e9150030701c4028034480741002115001d00025103440380d9081e050400f240d04541d181c80d51402e448648005100003800c0600c24401e841d900c1600d0202c4040c00700c01030880f40b902b64000c0c4228426405402402c0c0c50112416580615050f40700740020b41c21a08800e401d69562106404072144075150182805010362030a41d4056490613180d800b00009259200c0b80820700c41500c00c0117902401200b140010413012401c03800074003855034103038425081725000380c003d4240000c6075101a00b1400c02c000c050074440c0c0000155211000b68092600000a001c050071f030b442000808100e88202e030420b03085002c0000348a404405544580c0c040d110f6010f02420069404190b40305d817a01d403425061000e1100f01840c0c0c440c250f61512 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812043003 1250 812041753 812041757
    0xc08181201052e05030a0b1f0807060c020406080a14010c020d09120c17030901020d08060f042d022107020d1103091e0103140c2d030c030726070f 64
    0x2d032a296000310381096010b1001b50744850805040c4600584548c00da401c2e401c0d02d04a13010840340c1070a04040d2510700c1e1b1303c24042001151000302007950740701e90000300100220011121085603a1400d41032084841010140e03951a00c140018460700214038444a10324656402d105142020700010460440b42c20030f0701d9040000c0c401007000005030000365004010b40c0c008540b6040707070500080c034010031049080208400030003406000c1d1100310302980045000c44000c20001008014080f0420b04c0a01d46d10090440038130120b20a5030a9004095104080e076100c1043c0545c0003540782c80301d00a4400200503807140b00c080740540d119058280c8500500d5013920f00e0154184000b461040c1171404c18035130503040c02c0b92142d132584c06100d1003c0407004a50078a0075442d029966443ea40104100d501d00e50905d040080c3d111040480c05000307a60036620115141d0408009074241c0d50811155800410b00080080c000e44580c2e118102c0d9450860784250510f640c1c80108946200c107a0801b83d007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812044253 1250 812043003 812043091
    0x40e010e061f0503030a120c1211040e10053001090c1e060917070306050c07050f030711010c020f13050a0b010e1f0c0818120105 57
    0x1000401485068041c1d609100c2c288400855061007912560155004500c25802042540a01d54008007224100140000c0025440344090003c0e5000010400001c0c020361074291141c20851001d00900181c80c810310020005a031801c4143c5480d81881c00b803d9448008888c540c0228800781243c40441f240000ba05801cbc80041c0d000d0320f0940701801411104040f90040070b10500302e18040f5100d692400f08980c2c0c80711403a1560107484070f201c602800007000141600500ba400e8204102001181e010904002c54a00103103641591341100740e08417901e02420100d000381810010a07607040b00d40051068441c00c0404006444840250000b20380107110300000321903d0340c8503000b0210034040124042298946441c01608660100c0092414001801ca0401c056150840c19808007001c1005103011801d9055054900a01144c00244a640c001420f203d070280c070500e82c01c100c500309864000d03114a44071001800c2e0b07401100d210304250207201048240054064550340204c040b04042c038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812045503 1250 812044253 812044271
    0xa02070906080a080a09420815030321010911040312081b0c0a11011704020607060b0603130308010e1e0703290f09060901030303051009090f05010b061602040e01 71
    0x89660705001b100c40010000400301244461f400d04441c04002c050b8001d000c6603016400c13028014000280517806003901d80c0e81c00b245651000c104659283c074405081101d2400b016030960030258007401440880b90800c0031f2400c0c018280c505442c01e40e5407003101c025284030405c00c2111500e0008080f4000c54407051500d5204002d01c000400800307201ca070183c00150480e0810380c80e0440340c510b40b14100b150310b076051340c42c070b090040002c2e0b0032541c1118010394410749030400102500003000d00a0b841a000414000a00078070b09458244920075200c01c0c07116a61031745855503804c000c586591014004c640804e0200210076000c95111050341030004030002034080c08400c142e00c408880c04080c1c1b170030810442c0c80c90315540741c01210508413401c101500d07003200418101070040c072004040c5500d40700071480114242c944400540000d000030802039031170b03003041450f0711010740040e02d0300d52070541c0e109101c0c104241110303032000503203c40c003212074410760900c0024060240305e032180303550b940c02071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812046753 1250 812045503 812045519
    0x20d030b01032012060f0f0607080d0c050705060709050f120708011d0127020904031103190305091b150403080c060403020f031908040f0204110a02070906080a080a09 73
    0x1503c5801d26103100d5521941840e0700444520800b4050314403031a010f144500301b941e613a413000c4030081003c2d582c40c1d8a030240b5241080d51030140200e154481030404800c084207982c40800b419003d80243c0441d00b85403125030040e2544016801280e41251248003081c40342d0819202600c00300e41902d00f01c50a869541400a007100c2d805040200e01c42d01c2a031100d85c3c3c02030240651280906244100560919107960541210281e420001e010781c11a000240900d805a00c01820f13404070074054960703c0141c1c08041002c844a0041980840e1410020402c0120009040004d103c0c10407001d22960300072a080095561030003845c40c180c0d00c5d08010200001c2c4a9201a02c0841d04a4000301150b061134030f000303410404181d80d0036200b68070920004054241110200310480c065042c010065112800d05181c2d015030b03448007a40260405565030a80703a4800002d200389001c0d9401e9441c081e403031702180000d0321a11f01c101229940121049008138580c0001018140807500741039070b0040c0e0722600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812048003 1250 812046753 812046791
    0x2d0609251206170d033c05090a0c030332070501200301031203020d0e0a020a051023250201030507080405060739020a0503030a020d030b0103 62
    0x10440c0000c0e50694802240805409a0b00160003011485003034945410074041c2c0c0e9844da1001c1c07804154840406110790360080161002003070b940141171961030324040b00c00080f00c218441404d909858800011400040030032040310040d030160080440c5451502c0c122001c90000c950090300d11042e40c18848080f0f1100c24400c00406c40c1100c2d00c1d141c0610741003503400c480340d140240d008008400b0507072042c41102c3e8100c0b0f0541c1c0c1d002d22102000310090070f01310000d00800c112001e1980c0340070000e0741c407942c0020702c07600c400d0b2080300c0641003a5221014820003240d8250504d0205905160f000080c0782416a041e43c0c204400c0e00142c10080b141c080b154000c1c1004d0480c0d9180c0b154882e40809550303150040d07030340c4585181001480390400707582d00342d541c050050440081042e00e0a020f00340e001c0e00241d60001101c502c803c03801c0c00035114503140130340c0c0005d98101d01c82d03d02000001080e04011055400000d51500680001c407104001500070740008108079040640c3d42401003215038043c0c034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812049253 1250 812048003 812048071
    0xa0b0a060c0c08031c0c09090231051509030a12050414060f0403020405191a1e0913030c02060d0b2701090c050714062d0609 55
    0x2a03403555401e01d038104008011029003214806410411003040d0f1540c0300d80d50700c22100015400012103041d8220300f180d001004d038001d0b10440f800040c400081054503c0040191162204100a10940e0010340c4000c500709100f80c5030011741101001c40283c4508000c0c2c03215900240c01e40313003101469658640928003125210011601c041170500c4280300c24002036541c014146c40701e52070191a1001d40132640501e00c0f000344600c1d120800680203000d0b4219101c0d0501d171660781440018031003a04075a4444a02c1d0003107008402103065000340d5040c010303552001d500c0140502440d51203108800440185414043c0c052154410413240140c403403000030001004000400200c0e1040001001150034003080c040141a039415120421506901c003240c0c1140e51882c000591400320380700564041c01141001741c0b20400d00174806076000380c003140d130390b1041d0715013241980300d08034181419019022406a0032215503500700000d00508001d4150380e0060308074118400c1c60600d000700c071580d400e1150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812050359 1106 812049253 812049257
    0x105030a0525091503050c07060c0c050604060203011a07030210051b120603160b030c16020301020d2f0d0902150a0207180911090a0b0a06 61
    0x100d01d01415064550080c02c91581105000e03020040d5445030060854810b0341030480d1501c240326003485440011f51079418240c5c03030707150807004101e0400b0210034030504400320004110100601c42c401c9105810142c0c1d0f0358103121403100d80c0000d0a46841640000340f10020000c7d13004035544540240844000885a9440809169942504809000c0210006108502e1103800c81b1070034815041a400c8030040c24203a48640c41a061510032459a0b09046c004207642701c00c10001050840740030902e0b18030f100c040d0b07000a42240c2c0882240c041c0f50703642c0d60072018240011001051000c2c60340c001410182d0381c00c090241036104220443c4a02c9603204181800c5656404d0990700803018942c0c4140c403003103c9100a50b54029601401e01814048500100603c071240907456016901160300001c5015a2090012a0101038003501589841c2c1010030384030340b21581c604000300342039 = true := by decide +kernel

theorem cover : BRFrame.Cov 811870503 812050359 := by
  have h0 := BRFrame.cov_init 811870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 811870503 ≤ n) (h2 : n < 812050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
