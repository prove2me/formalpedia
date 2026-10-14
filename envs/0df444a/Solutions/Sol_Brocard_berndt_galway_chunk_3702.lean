-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3702
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:00.611307+00:00
-- url     : https://prove2.me/submissions/dda1bbc2-8885-460e-9fb1-09eed0943f3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 665647482 ≤ n < 665827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 665648732 1250 665647482 665647487
    0x2f0d05040c1d070e030a0f350406021612110402041203090801051821040f091a0103050c09010e060f28080708072102040807090510030503120702070305010501060c0210 74
    0x20240c401000300640c0c1e14541c01040602c02044a48003500e1b400b10741200a03008c0300745002041a2100c429810007007010b1144c0c980500c40d01e030782048100b48d000a02c1e440c0c17203c0307103004c1c10000402070070320301034000c110b0915260781d0115400307020307402d01269418030b0030b107002004110144a11101c079460700c1d0106d030941100035501c12848400100070507035034030b448070080480c1d1803200000d548841c04001c00545031207818202f40007003100c0680011840000d80780c3c40c06040305504018101031505081062040328001940d240031030a103000c0203030300c0719500420407501c50010351910070030380820f200c0c41d03004008840014540c11816650b1000d04440d0081d0380400d4280c4041340407a00d414002600c007441003d0550070811423440d060034010100107680103e0707000b0340255816030031101090000700018050150410801410341c1c0b200c0e4555241c1986a006001c3c840030f00350304000109140c60301c00c00c042d001464212000700315a595a00014001c00450b507003c034010205018038010450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 665649982 1250 665648732 665648743
    0x509040e03090303120a180c2d2102090103061b020a080409111903020c16080a0201051c1109120d020d08130606092f0d05040c1d070e03 60
    0xb5014006500748910704000691800000302405d0065a0f80c010b411041c0c0e9814080784030150280c03074001c44840c107140b550304640da162203030b4510034000f41800e650035480004011044072041503802c90340d04800f01c03074030b1000341c039100001e50301c610010700201c01c0c0b20107588541c80000c9030f911105421140c40d5001d9803140c00c11035020300011360034001002056400d81080803200301e84007484e498039408804840d82100d081d00f05900081d40402c1d5442c04050070019244414030005101e01464540a400d0ba5a10010303c0300a04002c1c000c01c00b1800a0160b00c41c0c48000300d054041400500580111701c0507c0c1c0140c0c8409100ba030540c1e60401c044072000c0340b2144920303003e9002d410940000f04041e1915070001d03020100401a00114601113000ca01c030b078001408001c1d10209400c03115581c011034610104d0740103100310403542d95006800c0c5240044070880307078481401203056030700c03420070b902c0d644a954409182007a081d503420100d804800a03040c41014561115085207070018107055560707 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 665651232 1250 665649982 665649997
    0x709020d020c06071b08210f0f0c07052a06191407050c04110c0d08011401050406050307030b0a0306050a090605010905070207060509030c040e10060e060607030f030e0303070509040e03 81
    0x455110141002048042e80203100501400300c7c400b0201142c410700003242001160b44002c2080140144101c01081c0c00045070881c0010240c1424848241c07500c41e00d03001c84004688564403141a40c50010400842409200c2c000800c81915107441034114600c0700c14501d040c00c0003542080c00d18040026090540b40007540017401044550b00003000d0200508403512400802d082c1489038240304001000b01e1500200165a02846540340c40071901c42403520090081c10b0010920062080c0e65004083c1c0740d000c071940c5004903a09603404041501030409400150200f420041000328044094202048940c4948000c20807680c1e52400b441c1128401d0b1850350040e08400400c01c00980312340090f29007a8002407d0340c009180640c001401c4510740d6402103a80c0d082840078010395500c51041d0401400c2520380784140380b0340303440099824403c0940040600003400020390107a403290740328038280048202103039074900b400e0001904640102c02000d01c21707802c0c551604428080442941c41e032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 665652482 1250 665651232 665651267
    0xc04030c0e13020108060406090e010b1507030c03080403051c0615020c01020c04020f0d02040801061e05030d05030702010221011e21021203040b130608270709020d020c0607 76
    0x20350b820340c011114840040e2020703902c240c0b02d00000c10901520301c01e10b98000d18460000464100000a00580410110000c0b807000300a01519011940049000c00ca280e854070703009185036103516068a5034041c0c0c050340200070013055880054130300f850740041b0507204500c2c0303c0a0918401c110490342e0f08458031955006070000400004a820f154019100c4803862040304c9003040f81c440c0c041c0040386c00540c031202d80d50791500c004120009401c0540c0103020b4689660484070f034100b01c0429070780c40c15952404204600080041e219074800c1d41542c5400b5086c4485400040b2007042c0d038028080d080c0035207843c0d140c5030200441c0f891a02c0805400720740800e00c1152004a40c0144865100c00c43e40059070480e030007018030000350b03000380000d101604c2116891511241ca0488038162113925400030014040040d007401190803240d03003104000c0014035907031014041c52003896400d220095211424090000c070301c11103450701940180c040c0d005031804460036075a40b0301c3c08a170701e4004404110b02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 665653732 1250 665652482 665652511
    0x604142a01020f12130501080f04021003090506070f020709020406170c0903030301080a0c1a0714010e070e01180203060a06111c0503180309150c0a0b0c04030c0e 71
    0x103162508112403000e4200c1401500c0ea102803124400b424034402c903801100310800003c4c01030803445208820300140a0a28061105207081c1c040c41c04960b030040c0000c1e00c120181c0141c05121840b0b508081000d990001c00d442e504c2c00c055001034031000b0803824020150080f02d902155000c81817007510100e402580e1108080030310080c038159401000b1740f69030f1220310104020700d200c2e10108015402004c0a10040030703000300d581054540100281c10028040e41414885c81c9044075031030607652015042440440f04111200c100c07030040400841c03009803401800700009008010300c0c5650f048138101d542010300b16041c044043c040348011900075900814242c2c0030300c50130340300708461024100384200b120a41603510390403020707211401401c0000508000200070301105411308e0000c01d40e60600c001e50508a444000602803031491003c12050790011403c000d08034800c01140c09510740090044001d030034171480350303151548940001d035400201c0b5000018580500c40c8090700c0b42182180641 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 665654982 1250 665653732 665653783
    0x9030d0e130b0a0b070812090a0209060613080715020c0a210c08010f0f15140d06021e0306090f0702030d0f0b0a08030a17060a03082a060414 62
    0x400821440c5621a040303c0c25040110f84805018020070380103001d0804240c640140d0356264000310001400c40a00e5003004502e000181c58064076503030040000c0b501e079500d644031128a07000700700e001d80c080c500740d12501c40c0004448205050840704d000c280c1e42036882c055928424000f00011070701c1428088041c812040301200c010502e500e0500388510542c1d10419034078220303103080d120300085c24070b081680c80005030500c444034450100307540c2d440000c1c07002c1e040c82c110020b005090f00d2140316010700c510b141030b14208840d0f036048031001e080d50402e40380d403a00f0b45003054085800c11605039004000d9040401c1c000b0360a11030407880f0b1407840d80210b2500501c00240e801800012604d132000e10345070302c600c8a040d81d85070038950150141c24025034540060b251300515000c80004041004a075110503c02c0076203849000c0d000b500e03080110b2030750b1142c003100d80d000314400ba80c100b9015203160100349860b00c5130101d04e150066021318184005083c0850800f600c50901c06503080320b1081580414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 665656232 1250 665654982 665655019
    0x30f02071d0c071707030206180d0906030c05040f08060402040e0f0303070c03121b02011d030d0908090a03030507023c030118060203160e0105070602030405120f09030d0e 75
    0x80c8000d502c04d0f200e182041159244441c0c0c1038000520407809030b0072620404c140031490401c0461010541001406a51041880500112940e00901e001c168980b041c1c40c50240c028402c840c003c1c068601c4011a050742c0341581c030f48401d03050394224416030411101e1030b660f200010340d00d1912204900614516101c0d2203098130f40d6035018000301c003403000541080704441e9492044141408448095100311005038100908580381101442c04503030300303031001030103009000041c2d4001e14040d00b0002000c00c51070401804902409608a500039010704012040591010140c180c0510036591401840011101c1d016012504200030080d449000c000040f855003421a1103120a000780c000030b5001c1044004a0009105280c280d800c690008103009004060320141c400500c03192404504104440000811502c510000900110303004404102803020038000c42e2008c1c2107042c000741e40c0e54400329070001581c000610151003030241034520024103000f5000c01d4107116009003034403045446103045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 665657482 1250 665656232 665656237
    0x703050a0c020a0518040b0f1012080408030a05180108010e04030c020d05060a021c15030305030a021303060c170c09040903030902040c0525170c0c0a03030f02071d0c 73
    0x81e039101036078050004d803035264846404801c0c4038407000440c451800e410444500403000c1c1a8a001c0503c0400700800190032415103802d85000303118510406400d8248100075001f0341c0c209a0f4540000200fa1440caa00440100f030000b9013041c0500f026401200152104a024030070400e91390441400200000d01c90000d100b0102c0c40145440140b081c0d5884035490810b0483e5440da40c194001484c114074100795403aa6001c900c00c050501941c2008811120343c550706200080900401101044004440f901074548a00c00d4110f2072800036038a04111000d0045400040d02107240e02c12800d5070b1104107040316104a0503103150515084400301804020941071308141c0405a5038121400180c4c2c07240101c02c44529603646007611030290003000b0082c1c0f142140303002c5492402c00c000c0d80006800a288403806a011040e9035120344100d00140c5c2007606001050340c0c002800400801050341110701006240d801e0f40c21510ba02d80c84040c11000d869503202140031001c19070001a0040098900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 665658732 1250 665657482 665657507
    0xe0619081207080d0906240f2c1501121503080a0e04020409090210020a050a02060a0e1210060b071e06060b04030503040311010c020f01030504021c050c1002030703050a 74
    0xf6034a8480042c000c0320442e02000001c441c6952105041040410700242c5a0940c455204400090340d10308a41c0620303406091045512142903541100c0b0510f5551016105100700000c00c1d00c4c2d03a151459030490801d50002429000c6003081c3c854502411480c81800862114181001c00b5141103445001da260440c0c40b000d000c00107071404103002034503140042c000510607040b0114698140344100f00c0210840e1071418110350141e4051000705800180030501d442e0191203041d070f42c00045900b11042c0c00b0a910b166048010306096800340e14001407101001c0048800820007140c45603400d003550310840e8009400c4880f014618400640c81c41d00741e000c0688184070000300c0681e20038205002e0b411650059590790000700e01041481040c2c1c3e54550402005d10b828400c400706980012241c1c40308004d4035042641e184006070840d2203241c1040180c00003510024442131303946c80c1299071036803280304c2c40f401107030080707113190712107000000b0303104140d50584805080c111165800c9412105448 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 665659982 1250 665658732 665658743
    0x50c0c0112021306080a1a030607080c0702150d0501051507150b041506020c010203030709140109030b10081b060f0f0f0703080f060a030b0118150e0619081207 70
    0x10b000c2c0f0b0200d20140d1000410362a1140c03055881e00f09800000c581402d84c84c1000380854084e00b003d00c2d98003250b070725844501410841840d4840400c0e0030501c2c0510310f0020b41006803500c0c0b00900c581448c01914a0500002090143e1380c1c83c5c90a05c10103c01400b45035161142c1031115034000350901068003d01040c0c1100000c1109030000060305481102d824540c0c0c60403d420b00f403081540c1405a940d034030b50280002c40c43c506001d034004083c00201e21510742c030303c0c01c140481521680b0805100c8015a0481b48801d42810048500d500185443c4a80c0342030f44a00b046541981010450003442018000c00a50511310b800401403441e0f880f030b11040c0307a0711504010a036060184100034041d114002e41d50b00ca8145400b8110401400c0080d2880c1e1040800d400100001580050494151a04110804030301092a0501d070003078095251180b0303020107e481d011580c0340c44040e1452140c90121404d401d0700b54201222095100c844c0031b0001c0070f800c1360005d0161951040003c0601c00e1140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 665661232 1250 665659982 665659987
    0x120f0c0d02040e0105010f0f0e07080106031a13020324030309240c030d2717070602040914061c06090201170405010506010e040c0806090705070c030b0402040c050c0c011202 76
    0x7450f800d0842d9801d0b040b44a013202039420a00c50841100540f0000e040d000650744a6400c2500f0041e0000c2030500c0703000105034947d02d0004400081464030f5090f80c4007c1d198103c0c42a0500741c89000e50411540145000d0744070702182400c420700030780706219000c060042c6181920100074040c0c084190b5803400781110418900300070030095040104044d400c100042c42c0c0ba0b46020301928281c0f21034080f074100e02882041405500d4003100c5005481d40e61040508528841c1c11800d44070138000e2001c0508250720101d00007130800c0c40c5400c8070301076030911003d1b58699500c1000308800c070418140d0740d14005a00508000004484c0c1c0e10482405005040248241e00300e030f09900c7c24808201c030100c560343d441d901444540d517003000c015a80e0742003ca030280400241154001d007004c900500b9507214000c0000410400c0740128101c40420360010401002c41381c503414008030309241503904a000d41e02e0300c58039101c4984604243c1c5c403528407043c00b8100e080e02d800011650128141d00d9042030640c00c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 665662482 1250 665661232 665661251
    0x70602030618010306020322020609040e0c041d070605270414191b2a02060c0a03020601050609061c0f1802010e0307150c0f081206120f0c0d0204 64
    0x202482c00c1c001c511417840541d5038644038400c42e41e0503c0c9000c80258400c190560140180d03183d006841c55050300f0340e0f00040b101d00308621140381030090741c055504145004440006a4070602d4441481c80c6054110741d01d099a40e40d04490604c1851504400750a411031081c2a880c11460144c0e0440001840807440007076200e0821036035042a85c1452401034180c800400400143c0100c0c1100300741181d400266420003007019140c00441d2003031030010b0003c600021062880c0b00100888030750007414071921000c407446030507902c0b55041e00c04e13005445058000102c2d403906804a034094180a0002d508180c09030b642016007030360b040d0010f04850348070f84014211034200e10415901c2c003c81507900411034503500000d0400f03004030405901a07044000140101d2034008032801d00740708549045800803459041204a65180d00c4001700340320000213071401d0803403029008034001c0b03800300c0e1202080a029503801d9501c0440340414400d9401c29030180e12503180007031555003580d00280001ca0404c1d074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 665663732 1250 665662482 665662519
    0x60305060a0501092009010513120305042d050409030c0204140714071a090f0f07061e020703120c05011509050708070804170403081306031803050706020306 69
    0x34100d81410066568400401c0a01010300450b8003150380a000f410200154814003a00c5118012801d0305010700003d09a6220710340c13419034002046104030b1120f540f406843c1c0104154864400d8010712189807080c140300454000101403407000c0c1c003010305d480c14034002c01e001c09002e007800140c0611084200c49000f50300c0d03034000e03180010701100f41018580381410001d800480c0b603040c0118040c2085c00404005079a80341c59504803a04040c40255070741e1054822031078400002c0c2c3d8038406000e05c51a074900b00600065071001d5800644803a0040c9010f81c46a0750300201c400b0700640107a101980410100c0c02100c04292102520b00d011480040c0c0e03911064291805105004240c451b01e00e402c00c001c0c441c61142c16080760071454004040d060034071009040b4007010f040508050804130000306082d60341000c803001150b201990079104c040a0642c800d58402ca031141c000800c2c2003200090190b4400c8407207241c019496280d05090421725200c0c44002e420040000c7d4005946003000340c807811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 665664982 1250 665663732 665663743
    0x6020706030c030b03030a0f08010b0a0509040f0605060c07060f0806030618011506110615091501021515030f01150e090f01020c100e0601051005030603160602101d1c03060305 77
    0x8984840b60341108d000310080c0480d4051740074400f008030600803600310690082c11036812030700c11100850402280780309034000341855401380360310080005101c14580c201240381d00450382540c550340c80d002c81541c0c0c140c070356401c01c851881e89600441c0001d42d442c2103420100c401080d01c9800010780e9010450031411250341600b00c540403d142c0900107020002c1040741c1a070184c0144031401c2a540f038030000c110500c0004e003011440a1444070340090a034070801040050720b8245110f0701c0b0f40d00344020101080003101c02c0d400d01130300900c0304121814105020340c1c440c02c011008441c0365140341101c00c007210000504010f40f64014162068189030090018080c41e01425002d40b00010f00440550201d07901200d0340c00c40c40e0461030042100d55202400c10380c407494a4102136a40359901000a070900031109640e4040354031104020601e00e0740003a1002c0c10018080d002c00032801c640d4550000b4618544014803240e22650b00680900314004091298484074240841d130162295684c50409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 665666232 1250 665664982 665664997
    0xe120705060d14010801151a120412080a140105040c17010306020c3904020712051e04030f030f090b160c090507080402060906070f080a02010b01080106020706030c030b0303 76
    0x340ca031030080c0d0f00090700d40100360041090f030380200b101403101c1e404044151054407031034501c0f210760079024140f1b0107618100c42d01e404000030406024a06843c21034004402c419046002030039050000303c071003a180c491005500d07140c1c420700302240c1c07800b0700300320180140000300e608022000f880c0c002c00c02c5a0030201801385201b81000b5888081d021042ca203407440f00e0101a8040001d408d1055508000f05080340c0f400d009550380d8034103080901c0210b030207840740010003001101c00396060a0b6865000b8060551000888011858038510302c2040505000e1400050729200181282c1000a4001c0303020444050560500390201551050801601e4008421030107100149003200002c000044080e40e01914800d04100150304200700f00a00e1440010f200174007038032000441061907503c81055030b0303205922540307150542035a0301d0481401d410003003140d00550b007864110510707580503240c1981640d0b542c4c0d00900010f0300e0020120044c3c11300341c4501003419518055912580c40900090004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 665667482 1250 665666232 665666257
    0x712020d06080a06201306180810090b010f03083001031a06060a0e0405040318030c0e0c031312050d09080c2503030c0c08160e09010603030e12070506 66
    0x2817200c4000c0440c40c810403125580303030300f00c801c014070482c6440399a912002d0745c0d4070b0310700450f40d204104101d1052214030341001d82544182d00d03c60a440f03000d50007100c1340038495070001086903a561071401f00450300d40801040c2c0c900a105400d01c1c0e6040740e44002c0d807034003801781c280c10b009901d0000b00f1080c502030300140c88029800c1c00b0003d072103030340c1505a43c01850540d071b9145842c0484c81300a100d458242c00307582c416901c4a02040030f0610422064941c6102a480402403030f60343d1601c5180c4000328445c80380242191000907081200320700c11b8030700c01c22010040c3c51507500c5c0c40d034a0402000c8200660004c0c8030060215800c0c1071041e10412444038410f0440542d141c81002000e440d02002d900012081840c05401d110aa00507032902c40032a0340c035044c040b2500c4514070b41043d0550040e0094003a904c140085001d040310441c40c42001c80c2c0c42c2640b488031030f40300c512609090750007a01018000c00c1d0b08841803000d600744400440340104c03805003a13805140c0c441000580680c45030000148 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 665668732 1250 665667482 665667491
    0x50303041106091c03110d020709050603010e0c010c030c06050c070317010f05120a05100518010e030405121005070809010b010207080705040c020f030d060f060203030712020d06080a06 81
    0x1005440c00c05150700c16000c966050070b00f090b80c000184161a2003c92891074445030045000305030180210b00c07480300e00c00003a54103600b00d00300c00a50b12001c07440f0f4404110304290103e480c070704040c4111140d000740c41000c0d00c14940400015030f41c1000c0c080c7c08404000c803071f04010000c9026440780502030503030288103650b02c842d1401d008110b04640c025040c500f400d464010009001201500d0b0115501035a51a80490840b070200d4142042c41c0030140007401600c04034481e80c035031940654440c860f071208001601c104130901508a076074202120302703658000c020500c22840c0816030000d840c0443d20845a41e803211102d0041a1442030380c211002c03e00c090b0902074020b5080c001c50318031450070710003043c0c080e1921000e6070356194288210790055580e0038407140601d01c02e0004811148030303401100e0303448805103840001840c0c14400c2c801c01c00620000030039414030200c100c0f4000c060659492415501c00400c810080d4041d00114482e142c1e03070400001c2c10700e414040910414010f140005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 665669982 1250 665668732 665668741
    0x9060905010510030b0904030e040906021b0f03040b0f0313060c3203010b0d0902120313150804030e0f03010f0f0e0d0f26010b03150301020a021213050d050303 70
    0x5001c00103c0700320b00501d82020940c032040d84581c42015070043d054944511007010301c1b804a802030041043c0906442c1c000590009100041600040b44252240888a0140c1c02d42803e40e00e90045004d8414020003c0140c1d103105c0d51110080c54000c94160307002c180007501c41e078840086400400c000303c04038620800ea0030a010701030341c1c10385181c0003500000d100818203031a030700400d100c140202600e0400104c5c0302502072850354461100d00764003411140320301000d000702aa6a412428044071002020705001ca1040c841030b000d13641001058440100c15201c1d550159030341e044440069810030b00c01c00c844842ca07542401091141c002210000404201c0d8600031015107580ea00780440303035442408000105a400088400b041d0020301d0202d220780003410030203221812228100b4254030752100003280546046004601441c2600800d0b00b6005080041c5800e03030045c0481d000150304070400c3c0034444900a0000c02000800c00b500040154481c0d0004003040000303181903403680c0c004010031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 665671232 1250 665669982 665669989
    0xe04030e0d060e0c04020c030703080c040b0a0909050c0a0c020d0501110414040f0603031b06020409020d020a0807181205100504060608150f06060a03290301061703030a020306010504090609050105 86
    0x2084c0f0007000e4a09515040381c1c0402580e8031300c14508010308200201001841c020007010a54016101d81c0284e10765407010004010301c26003260051000382131600300410702940d59041150b6240da060f4580e400450302a400f080001c00130184180c50554035041480341001e0b150005002401400d003104400d0500d0300702b4001154001c502d00081c0f903141c00c40500100740c2005014000181c3d03044902d140e103c0d03625221011340580c1e80a40840b42c00828601540c00c01900601038024090383e0340d46466844400440b0700302e02d000884006410510710a1140c50580c0d42d03600000e46c019002c58684801456031801111022602640c025135510414041400d040c0040c0a4121801c0c604140900f420302940d00041c1c000b0707058030302c601000104401310034001d402c0356110489401001124041d04e10480240400c5050703036a10035440c02c4404203407600007103030716490030004a00850540e6142e82d030280080d03001610482c180001403000240303c484070b025440143c006040c0200d0b01c0d5141c5402e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 665672482 1250 665671232 665671243
    0x909012a0210091505060105040b040305060415020726070c0308030402040509060c09060a2c040b03032809080d02030d05070801080a020108060a2d06030b09010e04030e0d060e 77
    0x1402d0890501e150f0380c0101d40303041c140d4019140303960000a1700c1e481e401d00503a030a203d564046040a840032400200348400800c4036441a4000e0550b811080d030b080507000700300c0c450580300904c101b44003080641c08032202d00d105011202d400407041c0c0307441540d455401607802c0a40c0121001e4200004200c114200b501642d6041500307007008004504010001c26214043c401440e40681c01c04600391800a10910294141354408260b03070660700d0a10304d64061003015846130030f002d58141402e02c801c4e4200001141d1403103111601900500014002c440d02d0307805c00c07007020010070030803000c0440c0d0000d052003e02100030300c0382c004654580e96000c14005986004046400703002114004200001e000b0401814241c1e09207020040d0360380b014000707281100260005111038080000c2c211010444408030000a862114000704840d40d4450480075a220800030580080b000c00042001c42841c9112540080c401e0a00000101c10b21010481d191880740c0c05136001c40d25500660080c403028400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 665673732 1250 665672482 665672503
    0x80a20030102070b070509010504091b02011113031e12020307140706080601200118140a0c120f0803131112031b010612080408100204140909012a02 65
    0x940c10040f054940c441c04070b0b0f000f80a002032101c0000e031001960320441c100d4018100f1058100880b1111100000040010340407040140d07203040840d04940c18140103440c803104801c24202a602c1c256694448003841d60500c1000406118100c54005070b40075220b0050074041d0f0b80256116030f2a81041192900d00c07212101d801d800160090052582c090740c0960302400a00300021400c042015030304040b800d492400c4859403030030080c0d520600c00702080000721402010307a1011102040034094803a4103404000700440603951041100c0802801c01c060980d00030900c0c801200680d0b215288030740d004480841803218516418401c00a01e0103140c40720050945c1c0301180d07488803844041d564442c0381d844201070300d001e1510880d00803007508000003506c514903a00c88055418503000c18150018041c1c1d04090042140c43d4180c254075209035812510010702509004100a0911940d2074000d00050450754940f40c043c80e081c51410060081420348080c04282d083d03440314000e0600742e4001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 665674982 1250 665673732 665673739
    0x16081c0504050606040506010e041b093c0e01060305060a09090b1f050303070b07170c07020607080405120709050702030c06041121010209010801240c0606080a20 71
    0x41c0030220348000307a0640d0025041e140055503441742401a50f288401e044007075480790410362076000c1202300e2401c11501003e00e480e07540580703480e10620f0b4800060307200c0c109900054041d03c507800d054210b81e00796904085a0518149a403a8800c210110009810140120703803a042405003d0402c807950740300912100c80b0420610109507a040a4903a01402150b80c40a8451a0070a808034407010a0004c0500030f08032981e915091030080c4030f010003110f18501241500340c0b0700008880108502e449850604010f5103481d01541c2040305d2038000d410309880700300c824040414035440340440c1c04030390752004000b8041289403490310410b0314802004001103400034094869003100001c1c426401c680c0c02014008480300040c04204101307801241e1701e81c1c501d540c1100c48184607040d4000c102222080e600c0302c00c00e07030301c81030903401021100301c00600c40c1c2c20b52006100e00340c0c414241d9090f554800c0c0b00c081400c9039240c0c6254034104e502182500e0348070401c0d0707015290036410b0b81d40b800200ca054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 665676232 1250 665674982 665674991
    0xa020102190504060c1127060301061505190e0d030c020f030c011218170d0c0801030f0b090a02031006141c020d050c060307030c2003090d020616081c 66
    0x4e84000c00c010315140c001042c2480c140220403166440101c602d0a00e5003806800c0404d10350501c4040e105201030322440d0107546403490100e0a0850380c14640d5100149444092900542c40312400018030080c201e4400c001c400d010071011981c4140c80408080d00079698142e0b040c41500420400722101003503580319a015810400659030080c1d88100707251030a00000079402c204100444891140340c86c01019009400c80b00c0540001c01e402400c90703c022824200328200c4042000d8490300ca0a02014100f40d41d079444040004503031054843d03000d010501920000c98103540441e00d0589050a20840b070344d2a00c90500c10340c0e04050351451031883c1218034128081ca01002c41407114000070000c0d002c0c1c105c0c0c400d04000d114040040300000403001e014a9034a01e0003207002002041000b118000107030b02c103da4410b4000d442c00318900c1c6281140041c0d40b511100e1010050303400a4000300f01d8000d003052100103803401c0d2071070482000c1d1b40102000d90b90380300403503900d1040360800607581002605e070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 665677482 1250 665676232 665676239
    0x1110050105100e1516050f01060303120b0316080d0f03050c120606210a06050121051308040b0415090f03020f01030e24070309020d081e0a020102190504 67
    0x889405003442022814142c07103541c4100042140200c00503219801100002a03203100d2005c00c1c1d5008415902640c10b81d01c209802c10495402c0e503810f8840540040c035140c02d0914044502d03030102c0d2104100804980d60054400e600e00398441203644040602d0b0000c200c1c04100300d800c80d054105800280c9000c0000b813402d000465480d010307544200c090744050400081240d01e4010854403207401361040c803070312445007400e0010005400c4502c1000305082000c0000c0b030b03502031104c210191a030946c002000120090440340145002056140c00351a03005051002c590980000c10103040600219550b40b405c0c040c40501c040d414150342800c210384400100322141006400d001501da04445203400d42c80c2c5d0b900100c014212546e400c012074061000c4021031265034140e000c03c0640003040e03c1503039655484081d0100e640c2c900019400c00f840b04030100000e00e0344d000600303220250814000444444d613440c141560082200c54016039800265604c501007030f034020026441091514a01d803604 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 665678732 1250 665677482 665677489
    0xf010f050702011e0c051c0204050a0905010e04140319020c040509030301050303040306020904022115010e060f0d02070f03080f1f05100207170c01030e0a031b06020c0d1110050105 79
    0x10f00c844e0118115698031004503066105104507080c0756010329070002c14941040c2100b00940c031031b104541c4541ca00c3c03580002c4481160203a030341220360503409440207554507192481c1125080d42c480d0417600041204000307130341e601360300e031070344030100da8001c0c036160400000348407c80e200504507480c542d005000400060703070000215015280e2201015840f182ca04000c0b601030300440070944250140d00f412180c441c009a034416201d08800300c000414200500010f640085602c0c120741d03040341c01048426041c01c0381900400110500c42c000502d40f106d107865032441c2c0130f54024101c1c0003400300340c240400c4044e8812a06e811990001901c0c0b502419026018440e080d03d101d65030140d09002003084c00305000344a000020981051520b8019403016042c3d03445e20703803020704903000c41d20380341140700303405000220780704055450380f03c00c521f20a07500e81c4400700f0304506004507a142d400700310704a544201840f4150242019880e845407000040d03805078142000d00d40700744003261801004001503603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 665679982 1250 665678732 665678771
    0x10905130212070e04140d030b010516022b05061e010909030e03010e1614060306010813120e090a020901020c150708031015050c03030114120f010f05070201 69
    0x794102c800781d02d20500c003030b10241004042d511070801208100c0410050050303c1c0d032125644110700c42500c084598045065040b1403084100900060080c442404003040300103062031f40c0ba000810a01b645880d141e0240c28040e081008080c1c0c0c40605940682042400c02070360ba0401480c104622044265422181031001c0501c030b1044c006860f12109401d050107a4000102003402900a0150210000f06245d40340316003000f110f103a83c6182c4001500c28080f1165206041d0010700481c40c5403901001106c00e248064405c2d21228500450b00000516041e07000309401c0c0a5140c1410b110140d0f810001e00c01d0f0001d200c24038035801046284a00e030780c04a091360310054201d441140300b6000310b10080f914001c00704010503006c400418005540c0ca5549010202c603820651045507400f4030800310381d24040c00707500c1c0c1d200d0b510500044c41a0040700540c10210200681141110800301c810186407010700c165510031a5500d4105604040060103115403080c03c50000f032102c00301c1c24a40c00d8605 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 665681232 1250 665679982 665680021
    0x70f0b090a1e020d0f0f110d080d0c05091003050601080c0c031b0c0d1109060d0b0109180b0705090f0f1e370806010b0306010507060f060603060e010905 67
    0x205011060700045503210201c580200f500481c07400200300d81e40c5046840701b010804141d4581002c200303801800e181000400c1c09080d030101a50341040312910f1038030050001801c030401072040c240420051500c03400500c00c004c12284e68080b47c44c0c201103001404040780030f40048580001000002c5030481e0000880c5c003001803c1001000081400c294642088d5181406c036a00192a10f204002d00c44685000300d83c105040340c4886030b64a8100c200121500d03414002860144180010030059600c0d1384101040e2039803004079102c003529030351110100d0300103d0b4001d0120f070010580392020701380710152107403124041d1440c0c505070703028070006070624141d00c51140402d460b1b44c208001c1da888501c074080b0030306082410032200e880b4000c1025031030159405413960009148100061103003000850b641210748102009146441d11001114581e00184081c0c0da216210501060040310900c00d1351300400c13460750001000d600300b98004030340d8041070b4440180681400203018190020b8000c62810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 665682482 1250 665681232 665681273
    0x52b02010917071a010807060e060703090618080312010e06040911040c0e0604032a0510080406140108010e0111130b0c0a120c0c081b04020a0e06070f0b090a 69
    0x2503d40310710b0800c0284c103500d1403007000c410b03d01000040480b40054000b09850a54884041001724001805070f180100d92020b0001800c3d0102080024080c2c149000751811514044d025943c4801c0c50518640c0700d602500b0404400034010003001080d01626034002c03a01301d03400d000e1500152100c440511a40100710310503695400040d503500c0c003400c482903c0d50782c09001103449950701d09141075440403042507042419000110040081d4900803003c068500007005481c1c40700710844100d0300d645004200b242e42a41e5640001d60b00043c10310000e00034600000003154803542c0498550075925070b141228607020040c4010740790520420318400039103000d01e8655071210109131149141c803580c038030081c0c12400d282078a807080c2e0b13510410300d2107600d0082d0760501103240e64241d0701e9500c1d5039260510010404550b070210441c03520790000c003141e84103460110f503c2004640010450b43c041d500403107206040485080c100402d11b10b4450742b1403007940160100c0103050f200d1800f04c41034841401d54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 665683732 1250 665682482 665682487
    0x111f09090c030906061805010b040305030a0c020d0602030405010c09330c1712060f06031306020c010608070302030d020f030313050319180509160516052b02010917 72
    0x780c1500c0303a4452001c1d250042d01c20701c0442e40d01c0c89014503140700310042c100c000b170500001180c10750700b02d41101c0480c1c1e884070056191040c1010210351071701f440c8100301e90060409895030007107011030000e10b000e28051000000c884a030020060600c581c80e6204980c942d89036210400500f4150f81d210702ca00007002100720700160045400c84030665044402031504a002290303608000c2c4e000003a00805004920b0070009441d0b5408101c445030b9100000d9034044420030010f0781e00c5500701101d074901442380e00c0141c10000840d91941c00d549007034011100e940d1207200100150700e42007180780e40710b20b00c90024107248424010f41a44074030006001c2540c0b035460009a03401c00204000320b034405501d009410038030040ca900700804510b202400480d8442a0b8480403c0324949040c0740744c0142c00f02809202440000c441c107484581180c0030b000d81c2d180101c112030020580501076568400000300d1022800c550302078003400c0c607004210740e6004582c0b40c481e250000a60fa00030b00c81644030510909038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 665684982 1250 665683732 665683751
    0x10020123060f030102030708180a0c0501031a0a0b0a03152402120f0a030b0103060b09042d020c060f07080105060d02220f09150b130b0304111f0909 65
    0xc1c400d1402c05807440c0c1540c400020000e001d94003002d03160288607410b04507111940c1c40100036030381e200c1082c80034003044081c000801143d07000364000c00740304009113040075540903a000043c400742440d6000301e014a82c002400c240301a070500c2025428030341d1510f0f070015a420042000f01d840e00255407507071076070b20304409582545d00030050b81e80c0c01600841d403e0307034174407030a1645265500421141c00100341400c403007140070345c0070303000e00d0060b2150103460508084080741000302403c0c82c110752640c1402d21422446401140d05418000002002c4025030355461030105a454008010f2445c181d00010a05004220703034441c81d0141142c86c00c8a00380e440c2d108084503007000b8800d440d2032790b40707a03884400c0070307880364082e070850b4801c48050100100240ea50b0704180e105030b0f241c901060b0031449061805100d5018844003a2141990392000c4590054688010000981c0700b0345082d61210f40c545051841c83c03420104e245c10942070181c403044407903003400f030141201200340151071800741c0f9025180c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 665686232 1250 665684982 665684989
    0x7110f010513030507030b0c0c0c040f27030915081603020d0e060906010b0c030409021623070504060b0a0f2105040510050712050406090b151002012306 67
    0x895016000c11030320031560f40e49150255480809100460385490500c0005400300c2c0d85c0416240501c2c01c08010300305104c1808100401400c1c810f41b180c00180c0e490142c01c980c4c0d0703018450b054080300708404c8000030603203904018180c4a0780da840381951140314410080b19030f0380561034681041219007038460b001d1801005801a0150b0401101d609103000050f00c2190305c000f910a00400c1d030032003034444990321034001e007241d032240240b40c00a65004200403c000030702a4020008142d002c0071103c920700e540d076150400701405a0600b02011982e031241d1030b000200380a000028041203400f00102841c02c085001140280600038003800010251251014015010568008040d451807411481d42103117040c0100b50994040e10a42302c0c00c1d1003540250b849104150141100d0f4583c001d2200420825401411004204584481d1a4291000014001031840d40985c90400e820f10480700c6200904c1220502c81809601310780c14a549c910025001005c60000d5800139032140c0d12981d59039021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 665687482 1250 665686232 665686237
    0x509060d020a020a020f090105030c06090a15020f01060605030f011806090e0f070f060206011511070603140709030b1303030612060603020109080604030f0f0c0f050d0201060b07110f0105 82
    0x40219807400000e9500180f94003040c220180d601c01c030f401c1e10300600c2c0c0318144074001409014a0b038040d800000d070405940f1300385014203442c4100619000d8040e4540458103000d82611130004090703801028440c440507800c1c0501e9025259078540710f42546016144180030710010700ca000400c80310401203d022a0303850300208081d19074502c0900112280c0c1044564a101003180800a40184200481c0c601c990174000340c101c1d5142e6000b01040c0e400c0100301c401d51003501c03911000740141d40c0012240b42900340242e000800494030300140c113001ca40c80520600301d00038415400c101858000b440000c101c3d003072032070300182030400d810312540b1503190541c020540307508000c041c28403400108081110355040b04064a200780e0b1807042c0c0580d03882060b5502e072000d0b41c2c002d001c105100c0705801044d10034000405070010520380310080c0800d80e01c9502552512540990b40c1e90084070300300044540901811004011051045d803901615444641026039088641446015141120702079a03109006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 665688732 1250 665687482 665687497
    0xc120c07052508070f1401091706100815071d0d080711060307051804180b0919030905040506180906041104090b06040b13020d02030a1d0d050906 64
    0x11915007403008140700040300310001450300b41d0b10020b04040b443c00c2021803000111503501c403841000900340034070103030700e980401381d203a040000c05800001e1087e040c01c48541e4400300e0340007800880c1407412002480c1401c5070044031150b4003041e0030b0700f20501c041c803086501100904e0861404200300301850b80c59000c0c0c110702a4026851145130b403d10040700300900c00144540d41d034032040607090040c014103010840da072402056007406215290303180202c00e01c0400c030f0f0060000074522004811000708128030030040c4c40b1460410f042145800781042040588244020110014545590001c180f4062801414040c584803000700741070303489150300112a4141700700f00b4166464207080499032200c0840b001c0d01c14484d0800481c0250810b071048070701d0359401c9441c1080e541d03103010502014061060040e43c02c403030b03084601c0031506c04500c00b40c01076010304000943e603800c099464500303440540100c00702c51040da81c0900349040f0b00040403a5440440d042980c0c45000400024500e80540070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 665689982 1250 665688732 665688743
    0x5010302131a010c151d1b030a1b050604030b0609010f05030c01200d050c0723120a050607030c0206010f1512020904020a030e010c0e090a0e0a0507090b0a0605030c120c07 75
    0xd0001800f0207846200b100c042a00c44103d1380486031340483d1f150001c0107c2e680c250950005110940030130660740c1c0110304d0003910340881203160307a2100400e455a0003a0b10036070750011003800b404210305c0c01c030048070300400303020200c003962a00f0840042e8580034003800c014148141c0605854140107044030086a02c3c9030002171310340900c0c1200c4054010341c8080c4025455010300580820590f508564910319035001c121103414005186041c400d540e80c810404043c41e1003008002000503508001141c401c074025500401c103042e41d5027000c3e240c48010303085120280ca204000788491071600140540d02e00d198078020601d1a110040013000f03108102000750450b0002a2402c4c0c2150181c001801c6e041d2a00c1c020024002c0c10001200c0141c07c0f20f6100d40d0042014003c1103c210702500000600441c05060700c55000b0700755140780c9010701d19446000700b16120078040c179440c40c003501400014501420f240346549003d00f030488051144200c1308110b00c0e18000030494400500041d01e08255001c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 665691232 1250 665689982 665689991
    0x405041512050a0302060c040806040305090301090512091206040206191b21032013050d0c0603140906130f05030703121a011b0303110301030605010302131a010c15 72
    0x600b02251a9402c140b020360151041102051008101104940450b5100c42c0903011544550b0350882c0d131035021110841c0e143d07480c1c82008011800c05c0c00244948a642d00701140c0e90185141840803148400c3d0074806150006000c00026807620000c4131400045808010001d0008440554450460540c09110207403d00010010460324030041c00c9103524494142920b07092003070046003560811000a2400f80015100301030120103140a07000e0032298500800e50582c0310360208501030b40d111000c0d2141000c0c0841084002e8140c400c03048480f20700d40c00c0800390302c2c01d400c0099540344082c0207a54004d04c5a41508d00b400b0784c00030010b03140d0354880c00b031720343c4d48038a805c00900000350898020309851a00081c3c0980009072091460303000d106071500d88030300022400c01c004103000c200e4141e041c5600c0301d0307600360040100c0780118007a51069000241650550040c0066103005141d4803080d02e02d05440300130840a50020041180c01c2481c02c07500c490060310300704841c0b9141d100100b5025051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 665692482 1250 665691232 665691269
    0xb121302041415130c020307030f050904091a060411040b03041118090601050105030601120f0f0606020f011808030a05180115060e0303040e0c0a020c090420090c04050415 75
    0x240341c500c00100031a12143c2c413400103010380040310351201d50740c0c01690040000320000b81c0610b200d09074a08140c1001c5007040c2811010609071141c504d001c80b900c10303406008941988641809035080b050503241002001602100350416103da0700070300754801390103c0020200701204d0b200880c000c10140c40d1100d800305200c1c140c8083c600c15200c801c25805820004185940300c1c900f6a4441d240503905d0410132200b46220000a00703400c40f10200341b0381c44014007040410140101030085c07501d5801401c940501031900d80c01c489003c10b0642c040307082c405d80c080100324540244c0c0d4100700c03042c2d000212903c50386103800c0c1d510b035036a507050364a50820303c0240082a0741d280d10001c4882c2ca8445c01810201c480030541c99110781e0003003840162030340001c107002401340006094140034a0044130050000b00e000190300d045e04642c12074148000040f9001504c42200304600c0d00700c8181c441a0207410000ca004a1a010300d000300c5003e540c1d00c400c995480300501048200030502803a05410107080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 665693732 1250 665692482 665692501
    0x301050607060b031e010b011403071d0d0503070510050124051c02030601090b030c03010620060108030a0306090b1003050604140c0d0b0303043510090204060b1213020414 75
    0x42c00d44107017519510741050311419500a00b400000e1002a000c00c2d46150740381d00058a030804002c02c2c0d0070304401418030b520b0b5513071102c5a0002c6640d0250b8000c0d0389030031180c0f9105103441c44c2c4ce403c210303115040c640100300b200310205590603220300e031191150840e080410101c07814011203c410910300700da125854002030095004602884003a40c0303001446443c0c4107207000710b01c403d40f40c01580510800042001074440c64110640040e00c0b8805190058030601003031500900703800864460708005401c0c07080c40c2d011720072403000740703001b5500780f000d80700500008040d08801d60603a01072688400000d105a070307669001c0941044c117421003007071074246512102d80507040f03201c136040c00502d01803100499240000c192000c07510321810815000ea140d410f803110454154185c00094842c0301114400e28078203001010307560710071080c0000c2090a50041005984543d440000803a1081045803800311080c54001d510451140c0f01e186940810f2002c00d004103200542a9041d00f060014002c00c1d62 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 665694982 1250 665693732 665693773
    0x90403050d0c2109081b01090f061401170a1104060f0b0309060a0e03040311011404030f0b060603010b0904090c08010903050423060910030b0928050c0301050607060b03 74
    0x190401004900d220383c1c0744110115010380e0b102504a080901004802250b4200210741382da07003400012071100c1040e564688c1e50203d0200441d2001d8440310b4440036400003030f4610b4010000407a8040013a441c50142d01d4444c0c0c80c0c9c000240c450448ea50702c82900c0d03103951300810000c00341c00010009095032151443c120350000c2e103124080e40918030201d0221030303407130007a49903121000c8061840d06103140d03640048030890359009418058200000716540c1400b402802c011801382c030280144860514201014401c01807007681b0a0100348010f0003015110400c3e03980703484080d103000030685003074208a903c18406a11164543d03003415620820035612202401c00c54080f0420040c1c846020942a074443d006150b407181c01050512001b070a614103071760700c411004035900780051082000c5010808078002124240070282c2c01c0c2d1028417400390300480e414982c05403280108100e0a080062500741e02c0103204440c4185004160705e001c0c004030b030303215a98505000b03044030710122200300030b040e42c1d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 665696232 1250 665694982 665695007
    0x50702040917040f050603091207031b140f0105160f0c05061501120902030c01050a030b03060705041403060402100f02031c060302040b09070f030e0703241d0309090403050d0c 77
    0x50804c4000221400c100c3c068a000c1c0d280321014004243d00c42414001a400a850903010025440b080b031b1021030080b2036502045000c0c10340c070050410000180c0d8030342081450102016854502013014411440041d1203071742c07140c1d143c4401c0b034104c101400c4400140300d10014085001d21000d104025804d03c0c00d914102c54280c803004001c0300002c00c00005c0b11000341000e500350300682540030702580300b680142550b40250400240444400c00030071b180c10750031980303000030500015043c010b100e041d40c0c0d1a4002c2c03808500034880340c641940403840f030880c104141c030103000c100d4046402c1d90f0b0082c000d135513441184440c1150441c1c07454074020301a00103484140e02640c43c0019401c4903003091181c89206407060385a0503401d924480d0124010029080079100a000d030f0300020001800701003892000e10700e1605600d000164000c46201103a00c4614206420401c00c80400441d03800801a206881012142c6003110b07501c5007019900351061038451118140303042c00c80b00156400140c04181d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 665697482 1250 665696232 665696249
    0x3071805060109050a0f1a07060f0b010923040203090c0907020c13020301031e0302030f0c01090c05030a0f0f050703020a0806041506260f120c0105060307031205070204091704 77
    0x100350744c3c60070302021000c1405103181510b141c030010300480f110224101e81e1285421f0341d00346403040c0c580701d4004660305c588560310485d450344100c2c07866603801203540001d8160090103051840aa0060f1803030111a075007900c1c003454001c0b0004039404000d00000494100180c07011026113030a0400075166541201c0c854400c0540b59000d1818219038401d50b03050300c1c1e0100540c0002c0c0c90628103442d90b502c510000b14210701c010401303049071001c418094020300a03010008140e61800c0d2138411460101a040180617500034007040c00441c108a02d20034150341c128102000b40302060500e6800c140013074002070341009a03903200154241000520b907100b58040d400303101c030407000007045400390344592040c2407282c055203060301e5200c90516041140d0490301d400311908002403c20680c200801d15858028801002c124071100d900c003800f506c0d40c4000c08030040c0c40072508581e00c000400801300f6030032082200c0822048115113440c0d2010080f580c128410b00c030070161401407001d0541c46401071a29 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 665698732 1250 665697482 665697497
    0xd05241006021b09130c090605040f0b03060403140708030115030f0b0906122803120b06040b1c0e0c032107020603100915091b09050f030718050601 65
    0xe41c03a00c0031074081d410120600300201800c1e07070101040310300700c40a4010050a0340000060000a50104030500142420311006c641c0354030300000c000459100320104840b4505010420286907400b0403020350003075150408989100140c0c120b001c003400380b64001844100e001002040348014030030450100001542e00344001c2829641400035200c4c1d080220790004030100100b0b9180ca0803404034003100720b0540c01c03035540c41640c4070095101c08c0c10180b45130505034680c40500c24560701c401003e00c4400030140c2800018808400318440c0d10562081045c002c6000c80c01d018503204650159050308105a000c0c000000b4940009440e90340f044c540728441c0c41103032090b0344c0324040c910001c441440d00c00385607810030106400303103c4140e00003491010700300000310000c103581c2d03043d100e180d0f0a08400010703041810300f004001c0048400102130b40400c2d402c00c01300250382c1039000b09000d00b500e00c10394000c091364030400f0200b071030318000e9040107000c802145911035000c03803540d200901c150401d80e2002c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 665699982 1250 665698732 665698739
    0xc150105150c0a08030c0c0304090c0807050f030106030207380919060e160608041a0c09040b040e1b040b06040509070507020d0803090d0327020d052410 67
    0xc01c41c82008842c1c2c1641d04590342400104902c60003135a80180d1070003d40b885c010207011100e0960703100360040d0015994a0002d810000ea001c0310301075100c0e102d800c195251120360b0f4900c1c00302e404140300ea003080580008080041020055880100f91541075a103031501c8410402e40030001480310909800c4404d030300001c0e42d125000180003400381c40c44007684911010310b4540d41c01405201c6030303401c3e203449043c1203d080b01c0968458080102015038600faa2414603241c2410806030034000d80300400a10b5042c8052480c40004499800034110740001d03400d0426000716001e8001a4083d0308070380a20700844640000c014503801000ea0111000c11408003001c04010540c0201d01546400007141c100103a08103000f0700091080c02c0c0010006825500c01d07035981c3d1050740c4201c2d0b018400f90000441e090569405000da1802c8404008900c440c00210401303130303412200312060191080303d27152101400d008082c0503014071f642001201d02c440c0c85070161441301003030065500c1d000c405040403000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 665701232 1250 665699982 665700019
    0xd0e06090c01090e0615030c0a020c0301060303090509130b1f0b07050c010804140a08070201110a121d030111040501090602010c080402130f05070323091509030c150105 74
    0x28905074105031074108825013480c3c07402d200140000e0140d9080745442c410f40c0c008840390030145200f185295101036881c5801d8000034209201c0d000c0980c0641e0400d5010b0002940002901d002c1e00d0701950259010794881c160154803450481d4040c050840b05820b01444152001103050845c040e18420030b2000d03901c50380309110b48600701c00540507402001d0700e00140c6d031040d0751054115000302e12075804421318900087c200700c0c840301c1c1210b941340009030b0b01d4110750704001050442e0054601400c40700c1b545480f0701255001414200040065641314000100090b0442c0320303070400094020800901011a01405a03005008450202d90500400a140391050156092031683c81d0b450407500e444540c01c0c007c403036681c1d1020b071410588500c8980c1c0780009034421544501301d142c0d03002c6000c507000c150040300300c0040546030307203031070082c00070401c47c010300007070348c1100744001d042620403036a85200190450144000410107805003501c00c2003c20303070599819060b10000c4980c800c58007a0301042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 665702482 1250 665701232 665701243
    0x110a081609020a09090e06060103050105030a150b18010807170303070f0309060207061401091109090f130b040614152d0d0501020316030c120e0709020d0e0609 70
    0x14aa00c0c0300e0050090080340d41d41e4000d407042210794180b001c002501c3d4504202035400404221880364880e8003041030755a07050080303d004003016009040d43c190141c44044048030540b402c4541262202e942da10203840e008040c0f0030381005603101d01c801d9611604103a49804c194070500708901601a125180d016004c012a4000d11041d1a06141d41c40340c418258080c00b5180400e50700c02d50f00f400200081030140c025a11640307610703032081c0034540c14481250219080c004540c0300b82d00702480003105545881c00c1807604003007040300c8410b544d41c52040700314540500c004002c0c0071364414003d000400110b5003055070341d241b50301c21202442e6501c603054141c40e12000c201c03540c012840d43c08032040d04509a015444490729600c00c0420144e2040480c208040440040340e05030360000801c03803c0c1d8494291100c000d541c9140920900107421170081120303404513005d96005651b40703403075400e201d000c01150005001400d810364580c0c00d4601004000d14011441f81200d00402c030000c0d0080102046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 665703732 1250 665702482 665702503
    0x60306050703050f160903080d020a030c05040f1202030a05030c0d090503120a12060e131509080f0a03020c0a0f060b0f0310021e13050a061706010c020402090d110a08 73
    0x2040322160742d9241080780c40e0305c40320914010b00c0b020359008004500c80701c00a028012254030090307a10740e00d460300242190036030144401001002e020a20140c600094680100e80c004d44125854070340710300000c3d0403c2d81da05d100600f1071000250f10782203000d0104200001d216030707440e041c4002c2c1c0c0d140f09268884031100254aa803000420098820602032400d01c079003055203140015980b9213410b0005090306055840004541184103210200882004044428291502d09004d1888a0303a40c038001400b6170001c0001c0b048003c10902c4800b4442c1d0305881101c11017108407849160a41480d610300712240740c1c00d48145040c04c4e0f1440766401c0c1034003405106100070380100041c0310060060b9000390494072030310084541d004c03030f0354000d842c2c00005490800110207004803180c2c03405e01042507144081d40300f182400078070b40f0098170741081c203080e09500c16030a0901100f50b185c20b100060080c45514015a4006064034880d020f018500e141d400da040d0080d41c1c200440da450b0409660f66102020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 665704982 1250 665703732 665703751
    0x4020a0323040c05090702010b1203040510170103121107091b030e0606240c100b400e0d02060604021612090e25030207032309060d06030605070305 65
    0x44003005130342030074136001340e000100d403000095103460107001550140b10800d1443c141d0740003040c14003071464030040c01c1900d500c0500303003810314041e444450640206d051002400b840b05a641a0102c80d00405400c003400c0d82601c02e9a52441e2100c1c4003000070080d2035441c80f000041e2240c402c0c0568040c3c4121030342200781200030141d980d2800300f0001c1d000103442c09040828611a0043c1c45281c1000150400001000190095480144100045034800c0359494801d1005000005580b007510300c00021502c9010480c1201007100c1201082219a051400e0340080c540450300b640c4000220b00c0c3b40b98004030b6820354681342c07140c0081000360300507081035514109294031400e0000340503001490940c0c0d402d00b80804207035600e10540c030302d054089550340c02a10200c000c0078242c03c860b200301e000d212034500f8114181641c5840080c00f202100c2045a030b443c4404e2602c05110031148160b075030400c00109003a0743e0384500100c4902520b001c3c40308644450514000c50100c42c064022a0311911400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 665706232 1250 665704982 665705003
    0xa050115080a20060c0307060b100906080a060b0c210f0d020c151003060e1c18090e030a020601050d0f0b1e01090605030613080f0c0c04020a032304 65
    0x25181c0900b45402001c840c1900106442d0030800e03038485070b0243c00205d00303040203545c440c0c0f47d07414038005440e08158803070700c9042e0704001c15552a4201c40b100c41518031501d021000741d40c40803407500c01401e2036081050000b03001300e404110454000f17014000e000750342c41c03000e0002051445101484c003c07101000c0d03d42505006191444180f540600940c247c0d01c41100c030711000303241e00d22170341c00b0080c0c0300c2d0300f0b40003541c40e4144180100d6002e0b0f050300e00f101600804440040300b400d0340800003264100002c00c8444040051504419034852000d01048941040311001e40c88207143e0300c1c2e011000341d10150140000000d0b00d880d0045d02c0c00307a1950024003801c00da2485030380703d141601009001449291201410b1840303450000c2547c2c1c00380c40600340008420b8200010145008030051124560500c610250400520b100041e505182c4c0e03000030150310b420032007c001c0d041660016200350400c1c80032130501d00443c0e1540240c1d0140f054002c542009255a42e81160480d80c200c80242041514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 665707482 1250 665706232 665706253
    0x6070f05030c1213060e0d08180703023007050102030d09210201020301060207122003070e090307150c021e0c03030c0601061407050c0d02040e01020d0e06131a090f030c0a05011508 79
    0x4950507030412702d8007082520010703520303640040c08540b01014103071840e6000d00300103440003001c2e5000d0040b864400d0300402c00b46290900003581d1744150340d840103545403240188400c000418107012004188801d49414014030714500038001e4100348a0f0350300511600c3e00010302c1c0a1a400d40321441da4010030f410706050b00681641d6000d4803507102c0c00350988150440010b0300200040c890f805480084007a580e55241c500b4a260040c03041a08040c04900c0e044488210b82e40000310a005440d080013510244d80101115070300345140c2180c955014040010541200c8801181b000d060720203a8498680c4006205216125402031100040c020b9014480e5144a031a16803c545007151009002143d020901000942642c000e414512540e80c0c0307504014101600c244840e940c8401441505409010140c840b10704c08080140203102e03008031600030540000003485a41c03c94005070040b240e0700c500382e5403916960300c094070068801e03510b090060789840d0307010a600c0301111300f03040c02070851910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 665708732 1250 665707482 665707501
    0xc0f0103110702060c0f0d0504030c0603050622020d0c05040f080604032007170a02030607030510030f0204090615140d030e01030c020f010c02100e06070f05030c1213060e0d08 77
    0x1d072407005c03d4415124a03a121040c00c120103c0d640d1601e55815071035528502c1d0203407001149400800901d4248002c0050300d85440c1d41c800300641c612040c0d2500e03600c030a1524400bc4c410945c0c207081c0241002d2a24000d642c228000303008440a441c42c01d041250350354612601c03002c003070b2401400208102070b86040018802d1811100301240c1040e00d051681d5070059008205a18030b050a007504490340e510150700d070502035954409140d04090119103411848580c0300040c2c0d000091080c0d07030303000085055403141c0d840003034201c0e803119040080640c0c0c600400e5004145116030324007414000e4080c2842d060030001440746070b9054850040801600c40198081d043c03042081046102c0c0c80e40102421009000c0c169141c034868000e042070303040ba0003443c425526055529469907200c8010b00c219541d108045000140340c628080703490b6114242403041034403a4039400007440c484941480000790400c0300c1c052106200b01410800e42d0354840005132110704203000c60b00440e40a1001489824 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 665709982 1250 665708732 665708737
    0x40903020c0d03030b09071205070e10030207080d0204090504170f03010504050603030c10050703110f0a080c12041a060306100e0c070b0c04170f0705011b0b07020c0f010311070206 79
    0xc0c401d0402280c1081700e40089090044102c07030071030005480d4580d44028140360301c90290402d000e072038014060b1801c8804100244140301d1010100f5a0000781c540910030110240d8140d44d40c0c0020a550725a03440c1c6024015000c241d400740c0e1019a1006c40140c0d16000c40202d400450010350b241781107078070300b00401004080c0100344030740501041000c4000d840c3c090040c0749120f0f652043c00100c905102e00c00a0884a00e0b0481140d40c40040020b404885000425507014003c6858140500e44e54034072502618060307641ea421507a446d40d0240001c01000403d06032040c8051040d042c1c80795920010103070b03600000d969040c4a80d55803101400b1000c00c4660f00f0303601c1046500b04500c1c02050765642c4600003400c4401050081001c2810300280140308203040c401d814002c0240800f80d807844e0901c0d00c07240c02c1d1094a05020b041031218501d00c028440c0110500e400c03824145681c5041c000180d1260701c0292070174414031040014402940c0288640030714505905522801c00c03c0c550b09104c09903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 665711232 1250 665709982 665710009
    0x602070e070c152a080c0c1c0306031209061209110d050309030a050609060f091203040302010908040320090903040603180506090d09080303130602070201181e05040903020c 76
    0x1a8948134041c081d04110248292407161040c1094841c40750358800400403240601813904100080108070010900002d200740d0400c03084419201003d5000c100303400400c099071004210790130214100c50b145800108034401c0300c2c03160716450903034901c0380011300841e88030b100002c0507108480616006420700148441030340c2e00c608201c9152080c0c080009282c0028008200c2d0b0325480b82041020025003400407a4100100d898920300500b0803c5010340c803040c0320305403554448800f1001401340b40c804d4101c411015000710a05036260b841c0d0405013001540400d0280d092036000e102d100c014101249868841c21540c009113080034208031044002d003100c0110003003c45a11200c4001080b41484800c1c00307901844020b214000f40000301814668031a44292000d41040c0704201005101d601d0f00404103034000801642c9010070700c010303a461203d0b000c0b9845011626240407522205a011070000c5092040201001c96950301c100700903140f84500c000d005800110248405080040c0e590001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 665712482 1250 665711232 665711273
    0xd0b0303070f031809020c0a02031902030c0108071403040303020306040b0d0302070b0a030608030a0203041a0c0c0f01020a0c1710050c040b07080c010504201801180e01150602070e070c 81
    0x5a513607401c280582c0c1040343e13254188c0d04101c000c0c404500c0c0c02c0294401185980c110841c9800e00e50300080d8039036045c944124103024581000491080c072507403010b850b891038103074059101d00305414005c00a400440b507246c042c41c0307441142425858107501108809906078018083d942c2440c4886501341c02244c940c00038581c858101051241003840900300c00b19140d4019601c9920745803c13501c0c449506041402061000c00082c102d608010803846448401540c00d00a0b8198490040b460f00444030b501402154100030301003100c2d09021402c804000c0c01c02e00f1940d580a40500d144101c8205440301404008108020000203c000c40a040c990780070340e400d00d041c075001441280c2521000c4074101d0301e6444a02c403074420240251032842030002c09441006081100c02c407410b4084006002d41703015181e00343c050608596030380e00b00a5880c0107400090101d2221a83c1c0e9482c403540340d001e2503002d4007500c14041406001001c03000e00c91000b942c0d40e10181c0b6100d40382c5a00800d03901004400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 665713732 1250 665712482 665712527
    0x30809010908031b3a1115090706051201140402120f19090809040504020a0807080f0d030e0703200409030e09071b0b150a0b0d0b0303070f03 62
    0x8624800b40060140400c90f420b01361080d0034082003d40c103081d100c401440722650154003001d001170078000c0d1181d004482540744030845003a02400d5440c14440510030070248501c038400d541400e100a41d09000d503208008403103010b503c601c1e060300c0c1402a20901010001c11100400c415003001601c4461003902030001460040102c0c03c0444000046070841d0400c01800180a074035201d042520f50200002e050400c014103c41d96038114500c070358022180708a86940200b0150f5840401c004002c001240454844030340d10501e5517151500704032980051b005640c100340c03943e4024090101012388550140c80700d24116514001d5556143c0b40400242c070300112043c0c1e0b01d40f164499020003074003d0711000a14114402000701da050300414450820074903410366681541c2d0403000b10701702030780200101940d0f61240002c800700740c10646071a9200c40b43c460001440a40306006100029010f2402d01900440344149556442a120010b102c0b24560144101017882a0000e5490420110200c403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 665714982 1250 665713732 665713739
    0xc12010308120a0903080411120f010605130b0a05060a0504030c12140a0503032206050408030601021e0705060a020f0d0203212a040e0403092d0308090109 68
    0x4101540903082200d014900140c00b0032040402c1c0b000b107502824007142408030882d80c2e6030041c5450005400144044850600d003105c5aa84140300d08103800c0e008126008034115030a694060012407050b43d0186801c2c0c80741890f411918003440300050300203094881d03004d14001c00e0050ba64419048a010000d00b8000807000440d6415040001c001e425400401c17030b006428018030500080181700d04c030360301c07009518001901c08030a6990014150407801c584020310081c1164400010031700801c29441c00d000c2004103c0c446020318000c41e82a421600c2040c004510231351181c000303100d40341c0c035030b030040404003c0c038582440204405420303441654183c01794142801c3c50503030244241e90140e040401d125002e4074620903000314000ca024010501c504045260004800c0800f403a051070280d00000040360a40b0b0808a400030005a407100d941072400b8200185040c00d0381c02821004995803540d05000c06c000400c0c1540d00c410000e400076980c2c039650f114100ca03401801d8090600c80c0040d00003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 665716232 1250 665714982 665715007
    0x702010509180406050f010506070b15030106080102040801060f050a0b1e07050d080103051605010503060f030a0b0408040815070203190908100e0d02060c04140103060302060f1c1b03050c 82
    0x243e020798070429022070642000702c0c01402d4088160030031400b610003448414042003c0c1960070741c000d0082c440c0d14202400e0040400c0c00b50003550408034041d8000200002d030032905610420841e80c4071100031030200c0e107170020400062000c2c4900000910140209540c900c02c054482d00745a0b180307141a40f0708210340d5942410000072501d600003050140b0f004005000c402d010031201ca11034140289405410200082d203103001c0170f0682c0c2e00070000795403a00c0042d2070412901d040d241c1c00401c03c0300245024070f0701300226840390003081d0003401070800e5451718654a20080d030103000160091070520b0081030305010742014010341c03c0304100c99281c00142c224014002658111840784001c14000080b006403031503c1041e840340c0003107500500c1042110704403101030700c0580303069926500d00041a103004a000d4451500043c0d801040046c1d41a507a107034100052551408030304000015140c0401c6842c11922510000043c0e4440d030741884005c0741c4681c0c020396004030a018403604044400006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 665717482 1250 665716232 665716279
    0x6030e1b18010620061e0603030403061103180a02011202031b0a0e0f09070f0f021203011203110c0a120816050f06010f2402030d0e010c03150305030702010509 70
    0xc1c00c0131403c108841c8152030020b60440580310a041e00511644c203001c1d000d0440c0b00d1020170b280550054100c0403400654052013200c0040d5041103080c00340c80180c0200390382c1c56100780d5290303981d1808036071203000458010817401002e64050315100403414010508001030740c001021880611000300d43e4103076101c0000c000c1c050071012640d43d8540441c0c05000c0c4002951014009403041481c00d0803c4070265008101c41000c0e1902d107032000404800030270136403501640341034042500401000118080d101104100c0540f0b0007591303448100d520011400f03403500414045950001b25102c01404030154050345e45103200d100794a6140b500c5404c4ac0c0f11524040390352001c95550b00301d500c001c42d40243c100038040c058860042507020161401103290160620101d4054400411016003403015000b4400c0e60082c0304028420701042c00041d10807402010b15441810200346411800003400046070084026a0740c050025860984240c00550309600246440c60b4001c19600354001101811080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 665718732 1250 665717482 665717489
    0x105280609050f03010203010e0105010318050a030c03031406090403030e150103062004150309060b120d0801140a030b1302120c0112091505060f04061404050106030e1b1801 76
    0x125800c1c80c03410401000070b01c554000c58544242e00510040c072100c11414202411945c0901300041d4801007100b25840c44031901c10040d00340c0c010400c000c010f0603001160780e00359601c01e660070400c441640f1820002208140d03625070b0000e030300030001000203000390300404030706c040f01e401c4404c03c2200c0d848542031034a09070401c8407002c2c1c031004420840304101c0700030220248000e039018145400c04200d02c6100b124264081c1c20140c8400b549024807441794441c16030000068542c001003a002082c0690781c010702c0c074402002528580c0001031250310101116041e060041c102d0041920359150008a02e0010b00882c5540b40c3c00d0000d080141d80f100418145420b515014095840f0000000b6100b2100411a112a1030030804503900042900030162103481101d05d0014241d220f25000c00c00e4a00e000c0c0c00c49030001c0c03510030301180115911140403501d450849051160b03070780380e0808078203503020b80c9840c22a0b035006070134000c5160507140d9022982c001c041c105c0311740341c04541035807803041000303a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665719982 1250 665718732 665718737
    0x90d0e01052208010b0a0b0703031112090d0806011b1b08011d06011401050306090403020703021005042c0403050c010f021801031404020a05060c10050f1e0f01052806 73
    0x7003040001c0c0c6000e018110300c0710390858030094080c0c9411000c11007441503d4008040503a0b4002f168030901411046d140c040c0d62001c46e0ba001440d100401e5030780c880c0c90750300380030102d00701c940040c160750710550482070110044042e4041100d6195546500503000003443e00794440811400300c0c030400240718441d0401c49869460304180803540341e04e07041080c10381010444802d488282420350340c1080803290429015501080c4941c1c3d41c1c00c0880c100741d02608003d41c0040e000d4409285240d0000c0607205a40c0184203685400440c010f803201d480030051454145e0020000010300401d00820142070700c00008000450600c0d02401e401d4102c0c2c0c012149503080750542038110115503071510410b0004400d00d201d400580c20700c0c0d000200925080e100342071143d6000902800c0401082c40300690015404a0034401803c24038000d2114110880e107000c0204062140070103c403052a180700c1c011031024100d04070507401c21082c400d0081000d40b0350844d4188000c08400710303040d032950b004014034095 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665721232 1250 665719982 665720047
    0x504051606030b01020a031101090b190f0b0319050a0c0e240f12071e1406121302010e120d09051e13060f03051506010305090d0e0105 59
    0x100c80c0e140200315070030201c201481c29000c1201030740c0000c0d0780e6210342d0305401e14443d401d1203861a580034102844004102c40c4106003806a4415010203000300a041c840091000610001120302111141014540e1580c490005183c042c03a0161034040818061804e80d036029049403100c8111100c00e40c07040341c4880034541004038110143d18941217046d0311b00aa0401108100000340052980115080c4681260150003c00360010450000207044104c00000720401d441402281c0c0b11f0107110f000343c0506103c04561552805004507520b4500600e03c800d041d86401c1d0b044d003688044500220706100144034001c40d01d5a507003da48000c0140400103141d0801c00260081c41d160543e80510300070030b062560028800c0c0c0e442c40c000d466481c140d91410041d501d14107020b005d089103501201404032a8040442400004030740748900c0180203030910010b88801004408840046030380312805d82116291240b2280728510042803160145403042c14114a090b441d010303000301d80c070380c1e010b603400302c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665722482 1250 665721232 665721253
    0x5190f0227010905042f0d0f0203011503150e190b0709080319030b060d061d130209060f01021f060f080319080a021c0903030b0910121401050405 64
    0x12406980905420881070000741040d81c3c61000706c175095031481e520909054006013505141205140514100905103410200c180c203108200b214201c8090f800ba5090158203c1a0103a010000e41120b50007181550444030349515140107204c40d418043c081e0180144084840c2000300e50402040c0c0950008006405d05060242c10600d40380d01c00302064009105001f0340082c002c48020700d050b924100429010b00c00c0d07000940e940714458040e030b141d610f030400108420300929101d0311012101d41000c030b0b40351100c01d40584401344034a8001e600000c3c010014110341009504080002410b00450385100d403103c03041d501c041c2c803102b80081d81d44d0f600d01c000c2020301a140c1704a002420b03140b001c0c40c60b00710340705100c2c1c014840a03071404091001200214045428030750481c0c1a903400d00e820064154881c10f07800025203100b00083e400281003a0910040c0c1c41d001070054000c0d100340d410b01d15501c4c41c240a14941048044d0103841402c1c84480d1040a02403c1c000c05205510900192151091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665723732 1250 665722482 665722549
    0x504061b0c090e06070c0803060d0f05070e0708090a05030a111915061706070f0c081912140604050606040305070f030b220f0c09020c0f0d030905190f02 67
    0x2030041c00101041005804c6c0703400704007504101c0e5003007101a140100310721150701b481e50007041d1f0210014160322130588000b0b6503800f18188070f40100916507aa01d96510360401641d5202c4c28583c020341140c20400c8030b4200c2da4002c01141204020202c00d80e03800e0f200020003496070690003107003a28581d101e0304038012000e84500c10b4201070704101c0d070301c501c04407148039210340d81e000b0040003882400740e17a9480e4080700303000748604441c142d4494900d0707a371b6141040e65641c00350008421071001c14031003600c01e544400c244c0103100c2651b864080034550350356010700300320240401428164001100b0480400440c40501c010300140c14160100c0c002c071451807030300100542c1c00030203490704600503d04041c48000840c04008280e60802c81528186105013844446101580e000c0824540300044000c0314290209400ca14500340d9010b507140315050110590a0f54110040107000d604900d40001503401d004030710340c01e00350043c03070303440712210055002c1100e086512070b807210180b0300d07480c5803401080d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665724982 1250 665723732 665723743
    0x3031c050702160504090203030c030f0d0b0f0102031215060409050402030c090405070b031506041e0602120f030a14090703060e0a0f0b070c0b010609090509010b010504061b0c090e 79
    0x1c0ea200900c43c940d100f6400b400354010b14003610380305940b80d204250079950200240c5003e849403100740c941d60b00300c40450364859400f4404000700c1509050310b607911840e042038500401c10040c1c02035031419558800090b4291802001c00d203030781c82508201099600d5480150000d03000b956000211401c090042610b031402085801d031043c0da000c01004000b590100f1108110b07003070071601c41e489458030368440e140004408002a00124042400182082c04c05c148200e010604810b5100030b6071a603800300e80b243c540b01c45c012880402040041841d0040c480116402103040200207014504080c0d840e803038400c242c070000120792090f4400d20038442c45105610b032361640c1038000c0c2028550f07640e4840504441d41d502408000d454000216001d008034194104030f54003100c1c1444943c0c480c00050405c0d60f55000b2004c0d40b0349001c00144881c40b0510894914040c140c60b43c1d8100351514108441d0264180640c110701c3c0480200c490004c0d400010100140001c02e8001c949144031000742c92429 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665726232 1250 665724982 665724991
    0xf1c052b02060a0903050f071115030a050a0c05341119141302070c030507140609031c05040801060b0a110d08060f06040b0c0604120906080f100503031c05 68
    0x150315020340c03e00003d420204030340c07440511f402c000d82c90b0913039802e1a1071034081004040303030400740b6a64a1003600141800841c0300c0e11030500e04200b151213200d4044d00703d41503c242540411400c0240d8a0b01d20203000340701c022171803484944440f0821400502c3c11603443c0791411245424850903045581c030302041c401d100004c60300c2806014900d0002108912416121054000c41c52080307640c800005940440c1e10701504058a0081d075079070b0746001c580c1c9000ca03118403240e08080c01851245442e00d00120340f10340e42c00600a114150048e403454070b01034502c80f03280043c010b082000160540c02802114001c000c1c000409440701c91001d00036154007640319150b0f8064102004002c1d100e600301400b207801000c152003842820040380045807040c8210340250b00b50b8940410611a041800164144038900c00e15682000303e6a540b015a854070f000d0080e40c2c04100b90000081450704411a141e07800105020b01001b801c1d91040444d013598014680500d0890282d40c040501181e180900780c0c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665727482 1250 665726232 665726251
    0xa030e0319050f04120f02131401051c150504030e0607081204152c01020f03010e06010323060102061f03020f0d08270f1c052b0206 58
    0x28081e01881c03007a10940829941002e1100118100c900c1400403000c0e58068810200c004140e03a020741400408800d9444d01244100c290000c03a91404526000c0d00f10140c003940568101c0da420310041200c1030110340a108078029808071000c000c10040300007048075011b208000500ca080078280100f040e82d40c050198082d600411050002400003011586c915000e091100002c2d25246801c000803401407585e404102e0600032000a0041180d80044003980c2150288803401e5003a001d1901743e00442090b049002c0c1c061004001000107440030f1640510140f4001500300081c80c00c0800e08144500100c80c6c00464508000095804001c055008010301e40000b034141c08a81242521a005002c002c0c0100e01d4010031202c5a1508441072031907990102082e86c81d0110382c03541400251200302504e1960f40660031b86100c40c00c0c04003982440303200140640460900c50b241001081002000840e054865100301c7d541c0d0351344213103400030010305100c00b0140c1e04040a200924100016150103a13 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665728732 1250 665727482 665727487
    0x203100e061c02010305090a02101808070e0105061803060106120f270305070b070806010207120308151909150905010506040e0705040807030633030215090409080a030e03 75
    0x202556460514103510340c3c2440c01060a580742c9070303450304000c400400290800c00d043c040202031508249860321400f03001000400c020f99500b04540d841710580301319042a13641500503c03007818200c0c020903d440d101561609a8000368000ca071400900340e0140d80064107042403240164454002c01c1d040d0180c03c2c03010f1280f40f42d800d0700940c25581845c072f2406403490703410b03861040600403402c1d5403503160009001102823400d41e10180070110100d40b01e9005000c0c100c40460b050824881180c81240c06540b5415107a450207011481286070741000c59001e501e02c00f5440e160236a95041c01e002e400681c4000c80c02404040904c0d508403031a03000901c040d0b04003801880540c9600d0140c404496160310f50300f040f501d032800192480d02c503a411046403400f0395107000c000e0240b5900083e8100720340c6150b044885c0005004803070015031100d10440420b100b688200094501994180301c454460b0403803034601b40e030001c0010101ea0002d001200e1125000c02c60100042e010b200350310035400e05001861 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665729982 1250 665728732 665728759
    0x4141609140f040b07030f1e231006081302061614070e0a0f0e3a1209030e040212040c0504050103020102030a050304050a02122d0a021507060203100e06 67
    0x41c00c2e13002000501095598503000099a040390414414400504000141080310040030805015914210300c5680c424584881e80c0100350384081e442941d10791540c00d152414207104035082080a0051407018500302c100e1000350361a4002842190041440ad589500c607a140040241010404041c2c40e41c03c20700c410094000c02840c60395000b61180000250a0341c04000480140030312130588183e4030490450412581882c001303441d20403010301700b00201e000c00042e16030728030406001200010f88110494a2190700399041184110f110f420890040302c2550041401c90300600b0403a00c0800d401001c0c8028040c0e00e00004c0b002e800e0a507810b0049604640001c0e54900c25410752100f00540000001c040c000b0500c800030006500801740b001140d081107040303031b668800d000012011038013080510304d624481d000d0010315150110282103080c82c10f03000c04c400520350161100a0310010802400054a540f000398820314100250310566418184180381d401d0004014034081c0540c0c0c0c4503072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665731232 1250 665729982 665729993
    0x9020a14160209040213090507030b0a05011409101520060108060103081b0a030e09070c0201090512030d051003050609031314060c0111042c04141609140f04 69
    0x7640301601074401e400c06843d40c0c4007103002e800c1c021540081962a000820040080c007040300c10807240584c40800703450321455010340440e0030078481e405241140e81c00c01069401d046803035590202400c500c0729181a50780f1140c008035901d00c40c1e04000248140001d20007141071801c1c0c0c91841c801800200032660401601a5440a040c007000d404860045107500b0710503246107110401e400d07900241c82a070407844c54060083c582050440748501c155400207013540d0710410070400c500c2d4059684001491810b401d10004801802a00c0000e0108000c2c0c2c1001c900c8a010f000e002d910700030036600d0290305d90b040981c14048081d100040d590420032510b80c0400e14228003a06440c0d4465001c00307044101d03800110540300e40c052541c0994204541c0e506c51040c80fa02034400c03500b071b80e01c8009020b5054081518035402c1400401e102c20154404100450300040d03500c80403194207011100c55102d00c035031185000402e58400401c0c191100c514141d42c200e407001c0241c228026100307080280c1006d03a42c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665732482 1250 665731232 665731267
    0x50a0c080d0f17150a0807060504090b100e1e090907030629011d04051305160b1902010608150103050c060307020a1203021e03042a03032709020a14 65
    0x1001c0754140c03140400b07290360707894004800900821007250138065a904001c9c0058029101c0d0841c4685001c0184241d81418109100e80022a642c0c039840d0b0142e8502704981c410188010401190030004890407540310704c1c1405000b000204000c08409103940f0788041910501e40c0f000d908009100e85000305241250724000d034010342420071035901c640600001c294032031002e9140340d109040c001400140304401d002d40c91154091410b8682c100c0c281151245a440c16204034401680700304507040d9002d00310718003a1032010a601c00420301c07603562142e251910b65921841c9a002c07050400401c04c01c0001c019107c5c1143d01034507080d09501d812900a5140c41c0c0d091000340c55004410400302a4512941c100c40d20a11078401011049681c401441010380003210211845658540400c0043c92900d00ca007500d819420758220140d03007950780c01c881c08a60700c1c0000f01048640c2426606c40090150b1404c0074100e0030400603220101441c000709042d180e4010140c2005e0200000c0828613422443c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665733732 1250 665732482 665732491
    0x20303041506080601030b091005010e090c10050a050f040302360c0f070302070503030a0302071403030f0c0f192a0201082e0b0702010f03140a09050a0c080d0f17 71
    0x281010f9580c1811281c102700e060181c2d00e0b100c919180011801c94110b24900e4001c2c2010310448540c03040d02d000380518125102c1c81500803d006211070440644a24001e00c03461441e4455503040035a40d501040600c1000000320702d80c14804190901620007203a09010440304803e2603010714100742104990310f105109030209000310000e4010140741c001c011040c0281005001c60750b9400f0401c000400a40110f00100c4a11a040c9194510300f20000240ea019440c2c0140c101da0540740c65020b142194031800d061000c0c03400910103611082640e44140070464015180c0701320b90071007603000101300065402c85c0d0310708020b03807800c0e100941d9200c1c402c40e500850340416101d1042480c0c041c03500c1042c8030185150543c004000105100d1085c40c06000c5452003a2070b18000c0c412103981c01d03800e440580106891554200d000a50740d243c103604005007440c0244103940c2c41e41c000c2d4135402c440311540e4100490035800b80c43c00d99030150340b100400b800041c1a151600700103032220940000041c0140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665734982 1250 665733732 665733743
    0x30305070f050312090c010201152114010609050109050a020a08150a050a090e061003031e050d090c210308040f0516060306060201060b12061003180302030304150608060103 76
    0x70301c080d0402600300b044851004501c0340340036042c90000b080c030b50f07070380e4442c4800c500550804600d060108503a8000c1c001f0340c1c19040c040b00f131083d81c000442c1036181c03200d6401d07203030b415036144400c1c201c46c008c0c0f00f4032002c0c00d00500702190a6050190600030f541001d0b0501c4080e5104000300440c0580c000d06480d08404540c1c0c00d0420b040c03007030340007030304034480c0d034102582c0001c80356030002c0d0348586640034811400559043c0c4030a55074862a503021212148000f50105040c84120110340b6202e0f80600003c7c12282007560501c0c07401020f90045407500c0c48200ca22040f5454288a00c59424030700f403801d200d0344400d641d0034a002d91f500506810000d04001c1180308040e1180e810040c4c140801410103000b43d55580701942d42d0070008000e4456481aa0095413030200003003504101034049a071005640d094043c0340c0e4484909009264502e42d681d00b08240d541d03001000c0341c3c50382e04c0611078280d010340e0046440c3d0400d41800c1440f800d440b0001d104080c0307002000c01030b650010411a0440ea0040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665736232 1250 665734982 665735003
    0x42402070f0e0a2c0a0c09050103030206071412010602011508010c09180e150703140f0f1510020106060e0603130f080c100501031109070503060d030e090f0f0a0603030507 75
    0x1c02010748100014004040d210704040384c150070f1400005007450100d0150210040303840e41e4800e52012288213000140041e0000c00c0041c0e8014002d50b03070039000c424090341d6140f803c101103480c0c9800c940282c1010005035151a84c40042002030f08100303010b40350b600001c0061046654001d04a40132030310400c1d072a0080d44611083c04e601c964030020a02c122401926030141406030450700c0305504541141c0420725003403850149610301340d034551281d82e1809060025480308134000d500740d0001414410786009014081130b0303d80702c280c000700c203c103000c1e00041101030505801034204500d8001250041d90140100803010038826603440380650089440c403084246030070600300a200c0c030b541c3e034190f520880c484142141446e034843e034122402340807020103614003801046000841501c1e4500011421700c003095061038256400e42400d407003401c01c4100e000304080460059441286c40c551486003101c10403a00d0750743c200c041580041002c0c800c0210740e0542d40c0c0a0920702a50038080c050f076401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665737482 1250 665736232 665736251
    0x180c010509040b0d05010f020714010506061225031a060322020316030c06080106050304022d130b0f032404061e061505130b030c042402070f0e0a 64
    0x12850041070b085e8000c0000c3c0801210810164060751001104071441c002e50004403076605c106110302030190000402103403910325400001c5114040c058400c641e02d86641103116007690120f4442c494660303982e01c002c1030035003800c0345c0242c20645050307078580034000070010011041004024640707a40e041c40340340050b00b40359002003850b000900030200440e44a000b008420310070802d21000c1118036a035507001140ea00d4510848a500060f02c00a4209800c12029041082e0103506c507040d00055001c1108106c060100044500c0d04005620382640d6880c0e00102d0b145c00c2c50700844d40048402c1e0010202e445c20f500500006050002aa0340f0300c108c5180032504121060700210749442c6a40250248403058050030b400425661096245a02208403040300003030094040d22246200b1020304201903251160001d242e9000905440b00d0f81c80802c40480c44203a0402071300460011001041e8940700070303100c060b1800c031454006942c4103192070b50802c2072900240b40300754890f004040109800c0d20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665738732 1250 665737482 665737489
    0x150a05070e010203490c03020724020d020f030604060608011a0a0507080c1b0a12020f0f1809070506031909150f0c081503190503160803180c010509040b 67
    0x202c948030101c0f1305000440c002204a0f046810f080d54000b80c01040102e100c940b5400d40892252742c000602500b60076290040d4000c800b02d4105402c8600360015251044107407207042282d20402040140201c04400d208407800d107442194050251402c0000c200e504100c0c41180890b07085519222000000600700c0c201c0c1d00c1042690b540380d40c01141140c8440c201c9056a440b58000300742100c1c00d46c2040c4e51041a40b410840640449440c4158140f440000d6024089005541c40b56a40c22840c9007040501548a0401600e82c144042a10b52640d041070700c00b9a040c07001340c4d44450300c104d1050040c4402c0c164200329032200280d000500081d4405541b5050800c0c020001300481d0045c50098001c4c41c40700c0c00d0304007240002550307032052101e90300c000284904070200c4001540650140c48070500e00c84600703081c0c1126a024500b2070b8281070300da400c1c03a0241c100c24002260542030210511824464045202c17411260a0014200503004900000c0c00c80c0200c101c090700c11a01c540f4080c5486d01d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665739982 1250 665738732 665738797
    0x80601060e0d1a0103030c14010507120f110304050a020907080405100b030a0b180705011e08040c0b03151002010218010e0a090510050102121e0702040608150a05070e010203 76
    0x1005481040c41036a40c0d01b03014050b031400260554600c10710700031050081a045c4030f428400c03d00c80d02c507121989050300da0440103102d094800c004540c0d0b1001406151220303807002d1403245105400401d9102460f1050000c1c40781302525082c280500d9030248000500c0c0400d0509041003816000603891069030002480e0142202000d08070780319540512841d501000c0382d8a007078154040448141729590401182c4c0480c0c1c025001402c940c810107409003143c410f204054010340070713110798481c2d15202c100360810b65000b40e440325005411540c0309451130a107144031010310501800218203044010301e002c603002d1060010030b4100281d4441c4e545596403401200005410000420803131441c2c40000b01c161841940501400f40c45003801e0003592003a5042103d480300c1c41447d0300c6080801654541182e41c2014504a921586078503000c240e07840100400c290484543c0300107a030354180340001408554024107000100082c0c0d41c4441c4e003690300042114411882e80ca120343d80c144c0ca820200e00e044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665741232 1250 665739982 665740013
    0x6050d0f06150201060f1a0f090d08041e05010306031a07140d051f080304120302070317090109080c0f010503181e010c0e010e1903080301090603050106080601060e0d 73
    0xb04042e119100360780f5815405401600da181201851031501c0ea50440903915590b00e02510281007001500c4414401a010b0501c0c20383c058024003000555984e081103d0704103801800d014440c140c880c994030a14034103420000d0000703003410003c040c1141c50b8041c0b2994a01c0407550641c01e020b000c110450310800d803103003480340c0d00307820192660036900d822809080306452212001640b0250300442c0a801d542113000c07038058078011480c041c90008445400003040c04103405500030400000302213108108038522118121660341e0341c0740c018000151204400f90401c003030942c850307840622540c0300c1500d2115008004d0804076103903944c01103404090720340c140052095000d8402003c41d205035410101651002010080c09030b0215650100d401000c0c03888107900180302c21941a145007802d0f04594400191440802406078403a01c83c07035000e074820790102c54200c1e943c0b0340800901000380308070805000351801800c034a52420070020400c1074160a1940b182242c545000204041582403000c203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665742482 1250 665741232 665741249
    0x3030f02160f0501031116120e060a0522030512130f0e090d081b0a031b0503100b030103120e210c010306050102010912051b010f0911010906050d0f06 66
    0x290740c990101000b5441e203440b0307040c003203810b00340e50780080d070150701c25030384403880f04008401c64500c543c407540c0b0003600a00403c8248080d2681c605803907100d40b001000d41e07000303030344035660780d07aa02c0400034801c040210f40d480b00f818901403040c0005000403402c0f41d08200850b9040d48c445d6a441d4036442c401c0c0c0300fa0b1003e42c0c40071185a000a8698182c142d243c401c003110026100342d96070008054600c104102d17824502540c1c4444a07200321421b00c800381c0a0548a843c000030741c00d0768642241c551855020000c8081040401000522104820710702c02410484003010b0440d49559252500100c40710208001d11000c00882101074441c0d9883e010ba103000c16050300b0200401151482c2c07119074040c64103000134105000443c4a500501446a009911544030030b07000c940480212030b03642021444018110b40000c4800c4440000d00440748003006a40f0001800402c078640303c045003507401400c138144050841c0810059400130700381d40c0c030303003801c000301203000d03107004000b0401000f0a400c4001e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665743732 1250 665742482 665742523
    0x6020f100b060d141e01031a0a0b0607050a050d020706080c03040201030b0604290306030c01032a110d0e060d0c0c290c03090a0602070f05030408160f0f03030f02 71
    0x107400d013080402034040c0030340d407504a05e001480f4058009550b002d000140626041d4074030b0f003004220084200b5801991890b00003071194452000400660129005460340c8d40101d09501c1440424012020048150300041c500103103007003000340034880c0040c0114070800000c000201564082c3d000405003940c010b05083d07450f505c0d028810101b0380e0b8140400c03100400209200c101c146c2190880c0d00840005006008000d032480046000d020300c0b845190789603040f0400b8022090b480d400f2880c0000c40c1e0345070300d230150000250700c603d8084440040d0742003040382995072516480e510100d8400d01c90348007010078851204002602e84112204008006074031103421815559100007110520001c104131103100c90b1604081c00c11180000d40e4400c6058000440080006859500800010b07100b0070242400c400d0544610382160015071200d46181c0050018480c80c4005450725800341c400b00001c2d8010504000301d40c102c0c8425800028140401c264203611030364000c0185000c246c015000f082e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665744982 1250 665743732 665743751
    0x34120302030d050702030708071e080f041404090210050a0302130605090f010c0203031803070305060f1e01030807141504030909061a03150d0b0906060a06020f100b060d 74
    0x35900c2c0d0000c0d40309040c1e18030b06004144d641c0c4c40030046504064204600c3c0d4140300d002e03111402011035035414a407000c08842002000900300c6005032003914000f003945074580d850002c20a0400b80520b04540c891443d0030300f48801a86d5071550408488440d20b440c40e03c5162001c41030700284038104580c405080340440c005000c50b4064002c000c56401603c0395000c9410140040d0b80f1844440c0009606400074131524004001c032602c4011040c0703004044a01c09980c0b82c880f40c3c1001801d503105d14104001004000c2c000c00e40d10040902864080070f04041985142c0ba560064015103000a0200d25034115078070003914200409540c404a00c180035141c0e007424507001d09500c00318420b41c03030340c9400c19800240301d04140c112107071071201e83c0300042c1c40d40d6280d160202c0c03074040200b8155880894014446c0203d80002600c40c03050b0110360040190b802c00c4001c01103504410f138020f404640c000c010300f0b00e400c440806d9480d004155a10040b5900d40c10600007001801442904d1607064a00203440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665746232 1250 665744982 665744987
    0xc050102161713090b0a170114010b03130209191503060e0316020d050111030a0204030c0f0501021c03200714030a2307020604080a02030609341203 65
    0x501c0390600c28614100100b04000859090f4012020b040d01d5100300083c08001c00c011a42000312100c02c000c2c40a044aa00c56140d248036001a6015a1079695179000d401600c205045d02d4a0240c20100e2440b42946028151780c072445000780d034001e01070034616012410340c08403034461900b04050301300c06011305402c0c0002e01403402c9061009840c003034113208404040c4400401242c001001e050325038140e0b500e10b0307000d01406a440c408112019943e0b0348100340c00d128284007444c05107004003005a80d8600d141400c1d03107503002541018100445410081103203a07000a1030301c00610305401c220382c60624068041d00100042c0340d80c1c0729152a54202002807942d000010205d052080c2d07007032036041c5114443c403030f0340b4081c2ca40c0c004081403d545075183e00c003070b1340700165841035242c0c422180f030075140d41e01151081c1c00c40c0e80802000c4d44020286421407506002c035980c40354044008061415040e24018040c0c14040c120801d0303e800c81070781c140b041150101004c0075180007981c0c01000200361800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665747482 1250 665746232 665746267
    0x2004050705070303151406092803052b08040f060e100f0e0c0d0c0812090f0114090d020301090204020f0c28060b061c020c1203011211010c050102 64
    0x4400180ca00300c400c01c01c032810400307000c007510424928800e4601b9000141300042d400120865440680140c03c814551020a01c0900b8480011030581e10b00e0b24500d00503103041e1810355401485007440d800b00c9210b000482c05000252140d00d00001c3c65100d1f402d100401104040d0040e01c1c0904109408030900c9000490020780001403008101c003a0b0510100800c40f20140c90000c42500854003040d054500080d551000b41d000d080c0d000c90159841100900d04030314240c15480a08021480446c240303042511901c103441d013800c0c8039204d04850030b9094803d100c1e20340901c2c0b00c1c2d51358941071030554509601c515a032990190045503140400d81508003075401840702e00c80c95106210050b070b1000c41103802416101d02145201d2420700d0703103586400141060200b5135800c620140040404030f80f000013101ea44000f8a100140d5403800c1015a0741418908502120000010801042103002c08031034201c44070380104d8150001c488002c0100c2d0000003820000d003441d0b0004c1042020800c4d20747e10f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665748732 1250 665747482 665747497
    0x408151b03150f0d0605060a05090415050c0c1504060e030309060613020d05011202030d09061202091f030c110d0c1b0b0315040615050a140d0e1e010212042004050705 73
    0x90b238400c007039912807c100782c140c0c1c1140e0007044c4882520310041000c800da00800d805c0908104c4060800c4920300c0c656181901046502c071704410a01c3c24042805002e10807c03000002550240d4518070300031508aa4404019100c05c0c019800c010081c0325042107a415103243d2030118009201c0340d6905e0160104103c00f8200a0b84680a10b4407100e0750107005000c900c084460640b1075050400b10010184002d41120486c140c208a14901e01c0542c9030415801740c441031202c3e01d00003062038034400020030052a240043c10198842c031055201150071240c94a2410361060101d4845e0000740441c0450580a50010359440700100030322102d105c044503613403550b5005450412045aa0344081c070f06103c10a1075000202d80d0420094910f144214551007211080100d0716141801e8039200c4800c460700e00720a5070454011030a00300f41400700c020080b404080d21002036050483d0700e0060b04000c44090300040c07280030034040c40b001070f00a10b060281c01d007000030000c00c014a401c5a001c7c2c126800081d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665749982 1250 665748732 665748739
    0x10e01051005030c03062a04030305071203111606110c0f010e01020a0e06030709051507021f0504150315030f02011701080c06070212030408151b03150f0d060506 71
    0x4402103040d043c009034100009500030020b10540d240c0010903410034a4080500d40c461611110940704200607900400045100e5990b143c0d40f0135250610200182d90405c10074100b50510030400d40c0781c501181900d07041581c0a1721880c041c00c4c140b5040c03000300701d0415450814100030440803c15400481c82050009954009021000050000c18200d00c40c0d11032190101c0c5442144903181d041000c00340d580600d080c201804042d4a480c0003440554080310031042c80b141c00203201d401c60502d030b103484c0d511030041c1881f81003040d10402c010f49240604c0c040c84180032461074103002d6036882031300841c0356120070610040358180c0b04e08208141c040e0302003069000c1202d0180610850194100700740c100e0329924050042015601c0422130654000301d8140d038001070500c51001014410f00c010001061078200410303403003e140c8100400030600074007507043c1e80d4003084a41c00400c2610b04403640500307642a4032644c0b2104100180c0301004010040340c00201c20398950f000c01501d80d200328000c007000c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665751232 1250 665749982 665750011
    0x1509042003061f050f07032309030111030f060f0a0b030c03010f080a020307150c020a0806070807080f0a0c11011b031107020a0b09010c021201230402010f0c0204020c010e0105 77
    0x512a4100061407143c1000002e40c0401603101c0e202003500107410300341d210303203007040b641c840140c4c0700320781420015003840c10390000082945844c5400d21918050041c041071007415440c2602d040d9040010040007075000e04081d004056460b80c4640f00c07007000c3d01d000381c4801e80745c1c207110501459039003007400707000e0b0780040603c0e0104501c0400500a0720f00c0798014000d105880c10840002540c202d10340440040c014240511001a9907c46000c001740207080010055850301501c014040600a40031106100120040c00f90013662107180980c4082c1c0076402092400d240401141c1240909141802ca0351034003a00d04060703107040d1005203000c0f046aa06000444000410042070310558000a51100c0500420170001c1c0010010381041e820504003440e8442454000c6940403c80da10b0000c082d944d110030000b448004078040141e0701c0300900c030b900f04038640b907400a4841a540141c0c4020311050450160440da116011502d000300450024070041d04e0942042e4060101a030b025051111032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665752482 1250 665751232 665751259
    0x10f05010e010b0a0f02030f0a170106080103031b080415030506010e011e120603020402120103050613170306040e0706020703230d050f07020a0b0403061505150904200306 75
    0x148941581038075034030f044440c0344c40724038501910100307810f90946066000c14040e00b12400c00c2079000c0c012211007512140304800c0000e00341010600d050300107105120032000140302180e07120005441050090002000415140c1859505800b643d444001004039a02c2c40c80f620790b034175402035805210280c03201100390310300000660750022504c0250952074800c0c81101000340c4511200c900031582c030040020300d01d0f141c1e0089403ea0348032118040302d690442c401001084000c0040c0c130382c845102c442a100e81e260075075030b900d030b0600d0000d83c92010340c01c007101040d8940c4c3c480d8461054160000c08680e0826614480030b902d8071010320096803070003075a10340c145100131854200c404240d4800040d08400348184025a002d82002d04059440c0300240076070030050300c4020400703018155460642e500d59283d4508601134400b41d848900b503240d0007803001c2146071030b91403000d401e1018060794107450710089000310b0001d003464a640219021010f410b05400d070380d1200150300415081da14100074180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665753732 1250 665752482 665752499
    0xa1101021b061602190c05030a1b081b04020d0216050c10021617191a240108130f0f1101081003020f01030e03030a05070e0a0609030213090f05010f0501 67
    0x41d43c0b40f0502507008280b01c0c28800121861210002e0311072100468810744500200745060b4594800310780c00360100d221152500c0d88c020400008082c03c50050034200c181c0c0902c10031154001c420030340a143c000ca40111051100d40649034051154003440888800a081c004d03542c00e003030220a4040c0c60130904101e901403000c2401d8410034112641001e040b451b01a0f0408203640307402d5184c40e04e0044451803103000501001d44004e4a000c7c44040c402c0070480c00341074191810240c0321080442d83c5040c15000720181c2078456060a10900b05a100c80d03648032040b806542054a0080504280e400b10710100042400410700603801a1151400c01082030015605624241d4011144854070a400c000510f042d5411a041d018103160201d01b12114441041c43c6400c01c1c0c40e4500c800713448004108070365a00800a03001074104448280d005403500c0805059281c0502020340174150050081d03460f880300790041400694000d40c10203d030216070a00034020320b0300800b000481c4e4140b000010714141c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665754982 1250 665753732 665753761
    0xa0605060a050604151403040c0911272205090706030b090c0304030302090406060c210f0c0f0b011211040b090a09060b0306152e050a1101021b06 64
    0x107a010748498646420010266203c00c0900c416004104544946c02c84400011000d14002c510412901c4140340c10501d100d0f080c0c3d095404614841c0c14103100d4080d0003e079510408160b82d807207020004110841c54042681d450500314000b0b0070b4800b54215160008056114a11918141041ea03000c180c840a00b10181c0d521281459400381c20f03d4041081004184000c5400502c0390400500d880c507188045019a00703d80d0141021900c0100c000062280c410540f44104140304081150344040c0d100141458201a483c80100403c68041500300700500c0310701100d5a8000540b000c8642c2d5682d15980b0280d1070303c5040f10025041d0025074098107190007818a8500b00410320306182d61a6180b120003009a84000d440c601d855203111103540c0c8041c054140207805220b000d100c1500c10300244444c4401140e510b0319012614500030b03000c6610000c0320303225099645803482d40d0b4042c203a41214401170480d017110392548005413010604000700b034442c5184c08040706442081e96607031001c000c080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665756232 1250 665754982 665754989
    0x30c11070b0a021e1e01020904060e091014131b0308280e04020a180e010510080603061803210a061e180f0204080303091c020d0c060b03010e0a0605060a 67
    0x190f02c0101c002171005101c100795000040203100040c06d2401c03060000d4244c2d00ea07175126860088800e018402001c4050000070782d0018203000174864005210010b40012200030040320880300c44000d01020040100c265142180c00460700841e9151241040d250981c0201101e00d08000d05948070700e22040000482d00c400d03100c9840700030340d520b10b200c1400007951103040701c50100503100580c28500c0104644c4680944000408030210f581404c050054020648001d00300344880c2801b04100c0e6540020010b902c00034540000d51044d9580000c1c0d46107005003840300c8044403c1c0b1485814044052500900ca80071b100380a000881d95a1002000c2c0d6001e2000d41121602600c1c05102d4103200700f0185803d07040110001a20a0855091908176049600940515080042071246602040000e03440e08000000081125035881d40b02a6a607a62500041d0500108003680070600072540c1c032030752048a0240c0207114441c0514040703501c400c40d9860495010340f415011803564142107810a00b034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665757482 1250 665756232 665756293
    0xc060f07171b04030218190207152c010e0d03020c1b130f0605040f020918040614071809020a020706050c120703170108010912030c11070b0a02 63
    0x15155800c1c00351031030303000c48004940100100f100200603154501d410040321880f0356020000d0a01c01140511076080101140d0ba40380140030100204450030034060050504080018140e69182d81305104104840605041184241411041c108040d007290314000070340016180b48501101c415001ca02035080304041a501126200301254021081e40103188001802c020740b41d802800051b007a180503020900350540c4604042109040c0741c040c000c0c100405800550070401d6a00c0480c2400010000500b0070484032000b145c00d10966510500d0b10b060781808480c03d80c030744000c02030300540a000000107400d0a1400c00215031080e071090704c0c050b107160303405400d210345008411a4641c00001140c41140244a000c001c4a0380e40c00081502a11a854074004103014030302c1c42a58880c140e1100b5002e1341016411800101308141030181368105084c00118216524001c8401c0c000b040c09050071489172407400f16080741d107c0090314169103590f084400302044081d0344c0c3c0480c0b809035102c0c0c40b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665758732 1250 665757482 665757527
    0xf0b0315010c0f0f0f02031b0f040b030a0224040b03060310270512030a150b0306010503040f1104060303050d1805151b0310051e1e0f060c060f07 64
    0x2d0804c80e207000041c1d0103541a41c48119030780e00000d0a00e2050044c01c220b030200113030448440e040010b011100c55901b110100407010510000c80d0b00c644403984001e1107a40141f804241c05035500550050030724801031943e4a0340e0701c61341000001d41c0141c805900c03920800c1c0b40c0490344016406024440d902c43d9030b1040b4299059802c90512a1070564122414042e04541850030440140518411281c030100840c418071001a1782550b407000c0d800a803001401002045400d9800004a85c1c000d90700000e02e030075151540c20f00c5180000c2e2001d01070380c05410903d00109251344080900f0840508203002c00400a0406a001c10741c3c074107401c0180290400300d01d2240c003070520761031030354090001f48008607501c0f1506200b1900341e0080300d07002d03401c40c44070405000c02c5c1001200b803c0700d801040703c44000c03400010b0000c2c001200e0b150340c3d20580521050215410b0b21541d000c2d244403400a00207070340300d885001000340c64102c112030034000d080080780081d052034842c0d502c04d03403040014800da00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665759982 1250 665758732 665758763
    0x80a03150509040f12110a1a071107050112020f0720060403150b0a171c09081c0e0411211611011d1005060109081203060a0f0b0315010c 60
    0x44000302d03100010740a1211075032180307003001c6c0d0074491800c05a22511800711050310080d07000c1a007a8000c5c00550400c8070001144410500011360802610300900706801d031100703003900b048068820185080d80950000c00c546007080105075140c020300120003a00c900c1030380d40c0f400b808024091444090001910481c60f1614085158042c401d5104080c1c01401d04544512000c00781e15100404e5001d241d1100c5c1c021916402c0081811000021514200300010310b01041c00342c1d00c06071085604d00000e480c0780d9010f141030180700305010240000d03206014540b00700442c03048239000f10f40448000040c1446100704640150001882004012086140105066811a0703020a280a003144640d03039500c0b068140180b002d04103552400450040c5022106903041c83d00390307000506494180720500e0400c1c000c1380e01c0401c5298880c0704040f10240c89944500014000100e01d501c0480d0030180303440d02042e0140390380019481100307413011403407403c5900c100441d1304038800540500031000d180d4165 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665761232 1250 665759982 665759993
    0x6150507030503040c030b040803150603040f1401060305010c031a03010203040507360c12060312032705010207030807020606090f0411031507110f060c16080a03150509040f 76
    0x3c5800074010303400c860000b5200d507521030040009440c02d40300d0040100030050b00901038210080800c0d4240e0b54542181402d68540c0d5030580b19040c014603a907048928582100c0c000d52042001f543c000c0000e002c1440000405801401070358000000c0e5040d060060320707142014000c0364010340d4041c0081111f1032a09070038020038403907403002820001c800c4405036040e4015030404070180c40e032460300194080d80264044d00480e005489594040c0c2004810001b19880644200411400d0300f4085000c001c0b50f4441c80590240040301c9407038240840042c000c0c054154003404035288642c071005c1ea81c0c0c07910103003680e40c1c000c101ca9542d8081e0030100041ca40c12044002c0301d41040c03099000403640c14039000020b04261403010300d080d090031031008000009522003049281c0d0740d03084019040810f001c5c2c010680340c003001000300030840000150104e80c1c02e03880b00d04200180d006000e6a840768082d810040281c110320240b01118002214046030300d180c0285110300603a4801c1072280c0c4d141e099030744e0b07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665762482 1250 665761232 665761237
    0x18010905151008030d050f060409030f080c1215090f10030f06022106090a0903080606030726100e15040c1803050109060c140301090908090d08030a061505070305 71
    0x202e0802200080001d05000c08001a00c9000383d21400440c5504d40186413103000303800200b00300d1140781428408404660000e40c010140c0e03540c0d01d040c2c8042d03500c0c41d140883d10f104da04090031160f44d0110030811a24150798000b1551041250380c00c0c044e88a002c2c11080c5610251210700080070014401c0000030440110001024460072015040045051440c01529004840e00e812141e4000400c181c0b494220b20707166200e05d500100b0843c0711010346004200724001400c03a40202c10001c0413441d01401403e48110110100043d852904d101c00b0700102202c0c41515000000e90040501103100e440648060740714014001c03030038400c00100700030407025290080d83c00082c8190364a883c50030324007100904000c0c500520000c540c0800514004c002c88643c0c030303e07041c204500314003100380e200c0c2410100d030b0440e00d0304040414564510300300480244248050346070f015180c2005102000b092001a62113200d040008004040e65504101242640f1142080000b54200401000a80510b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665763732 1250 665762482 665762491
    0xa0e061e091501060e120706020a060b060409020304030215070206070e091f0f0f05060325031112010603052a0a020307050111030f07030204030803010909060906060e1801090515 78
    0x1c8034080444102c00e029680820380002d8000340a10f10384e600c00307040c4a00040100d8400c0801410841e00d440402900c1c1d02e41e1300f00013070040752180c100c45031550301d00b026103000e0480408219a24209490060b40d10882c0080784a0f9011450f40064070850001c52074511605103500c60310380840c0c0a800300070211800805d81e0b9942d00d101112418251103c0c490303400a8a039201d01d110003a1308089031010800c804e980300171f100701e20410811034000340b1070300711a200360a0304100031848280b00005a02600c00591414902040422103450500110701c02c20b040300c0c2203071002c21290310b5a480c942e82103480d81005240c00d00b0416040c60007803040800511148081e441600c0c100145603580300e080d2000542c0420740d850001c0148000c051400c40f4603070b00420642000c40c40d2500c0d550b10900640014420000761a542d0400d034018840b40390401c3c0c000c1d650218041080381e8650001c1090868203035034038a44200302e400031b1359034003505108940d1525001001000c00c1180c030940d00745c00d040c0062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665764982 1250 665763732 665763751
    0xc1b060905010e030d0f0204080c10020a0605040609061a010804081806030109020a03061e0306051e0a09140f0309090402014b1704080415080a0e061e 66
    0x55090041002841110103c0d24a44061503503034890816035816142d0404c4480c810601c10001004049000101c000c1105001d880c1c0d418120b40700d00d400c0c2d040014100300503200a084c40200010480542d111080d080e119040802c000340c19880003580c54110300c112036010915141c0842c01150042005d0b0003180070002c10a114503e10030080358181d0003c0e4415903c4c2a00802c2c0803c06942500130900500070010725440d500046241803800c548003480041c02c3d496660002c02c1d0b00c122214009103030303c100c024080c4107600b09400000010301a07000c0a94140450003c00d0440c404003107520309411001c00009c40c1030a150504000742402c0283c0201e041c4011442032001c644803500d80f03034a9002100c3c0c021251144c840740350090b05148a40600d03068400486061403c0d9004180380c0c1c442c4071000c500204c80d5499281441d00e52085800039401c5a000c0599400b140341d001c0e0003180700d81d48420041c01051468044c29507030311402d481d4590001d50703c1101c4210a100000050381c080101d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665766232 1250 665764982 665764991
    0x1080a1704050a0b09030105012106150b0703021b010f0507021c0b04031815052218060501090909050304180b0d0308041109011404110f04080313090c1b06 68
    0x4000144903156a54800c4101641c0170400010300d180c01c0c41010f00420301e60750340300740b042d4401150b48014020710314014500c0356200d40040c0444030b941c40303003400f80c00ca030566103a5682150602a603585000740c0c29030700c42e41d03400f092200301d035105420030002d20301300d500e4180c100711503075003000411246516182011414170100700042914030f0711480c007450103a10b80740030045441020300488096030f08010750310995030b01b0461203964850f044400c56002100b0b004410040008917045134000c0f903002130310420000c00301791010145644000c040750030036254420a10360725030410007690000792000d409904144020071001e000183e0455003141c0100b0b0020b00d092400002070302c00313031401605800003480e034000c010030010042440070742c20074121a5040319614105400e00c10b03006011078940a162504101c000210300c0ba0180c0f26004942d12032103803035a407501d00c059580c7d04184401c454030052128001440c080742d1103690b4038403019580e00c005001280e02800c05501f440c9508960f0556134 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665767482 1250 665766232 665766239
    0xa020309030a061d0d0804020405181515010216060e0321040306050c071203230f0f010510050f03070c210f0323040206190806040c030501080a1704 65
    0x3808080c545510600c000102010450480d229184140b10160000e900c440e02c00e6060940001b681a80682d04950104041d23070b4025044d0780c10302c3d01041404040c4600c441d00f045200e036490000e84900030410945030240800e000490740c0341006450420038006804050011a208281d1a80c103034002600302c42c07c6800300c85003866488008000b6403006600800d0920411065003d401c1c0c11117407649445c0d061030040e85a110b4505c02c900752480501d9a94041c2030400c0017041c610b4207181107044031020301c519000303251110342c1400b182d0040f40e00400400200c0c0078503105141c4102c801d001e540380e9050031780c00c500450351075102070184400d21016888241c0013170180c054031901d02c3c003c0034040c402c040740c480002c2c02040b0441c4090083c0b6040043c0ca41c501800f04039400d800346202ca40c42406501d0314000f0561701d1013101e06900040c0c13030502c8041c0503e6044003c0600840c0181c07000c00501103414822011508203019101040d000b88800300041000c2450b0700e0004640c07036003180c0c5440d68 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665768732 1250 665767482 665767489
    0x13050c10171f12211215170f16030b07050901090302040e0307030e0901150309061112070807020a21020f0102180406080c06090111070906030c090f0b010203040b0a020309 75
    0xb1954400c00c604180300a18104011001c0c9a0a0b294130303000301c034050707031401e40a800b400c2c03078074800e0000c0780c0c1c95075420300780f0110b81c40320341d0310401030000e00f00304401d1228418a1075220404152aa0b08a202d400d89001c440d504440e1100708880e0002030411b07a0fa101c1c0c110403240303580071a2360641008030303500002c0302581c0c075881a100c410480704021992a492898040d03d01c59032102e010740b2a010f40c1c0d004000b0030440c410442107109051800182000b1280741440051141c2107d107906a540170891465000c0d800f200355001c0c01082c0c030f410300180d0b2a07803807c03aa1802c460100812241c88010819461000182c1345a00503001c1c0c0107076a003000780175883c81d0880e0041500e840302e22190104110181c02c0c244503482c06400c0600140100700c21305070124030103100c1c0d0700500e4100002d140c900300390460180b0207500036100b000014080b00d0380da400c0c82c0401008502070318444a2404d00d403040c9964180c0f06010700560f040c1c020303504080c6044604002070b000300009005500040203001010358 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665769982 1250 665768732 665768791
    0x131a043b0721120f090506071b08030702130e0307110d06050f01050f011106070c0201090305100504120c02010c030f030f0f02130e1e190513050c1017 66
    0x40c0425100d0307500d000c1410704070510003d40411000b800b84500b14840302c5640b002e054010350f5400d441c2076599a00f50310305410300309100c52800c1e400102e00c0002081c940d902200800081c1c1c006c8440b80150f2504030040021a008100c42c458207038410400000094a10400c1c00d00c500e200400142c0c2c2c5466a0721041c0075603808030341d060a09410800148154070b010710310212202800e1800d00b03034800e2501c0a4a548040117805141440030346c1ca2418116841001000003541c0e1180c15900c2c000c040e010002f0190006131070440e036011640e40f044403170611402030804490340503074884995913090b031816540ea80144130710030101515080b0a5400d1030040c0981c05c0c142c41c41220059480c0945080c4056000441d0010002c1c9180082882010001107e0295040320400c200c0102500da94922462141184030707003c40080c1040300f00070042d0b51944c24015494010402e450f8900c190800b0001c0c0c01c20b4030650744001c1800d880c01c0348048142d030301e074055000140c0d03541004861080040283c094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665771232 1250 665769982 665770019
    0x90c0d020c0c10050901120b0a0503190b01050f0906010c1704032102060403090b0307091a180a05010210112a011104120f02131a043b07 60
    0x80d030140300c02c0031560620316100e43c0c1c1e07a540c51405074280f030b000c08002806000200c20301028a92540c030115102e5450408100c02003a000f41201c0c0005406514913010021180c0c042c1c80d00f04000f000060142848440c02d468003000401902d0f56540e041c0056606501004040da00010301c0c0c8030847c80000300c10005e0001d14028411050491101140000110050700e103a40854010005201c006608081180152400101503035225030316540222110300444d802803060706071000014640c0b10804004003102000400407a6000c441641401442070300c0f80b1455005030b0000003a80c41001c0d0719445040744d405040e2000786410382c03215040040c5240248001c40f1085141d00300e842c040800d200304c481380c0044022003810705160403801c000c0804421030142c01b502d000d5402a0442d41ca54110007510440c14000304400e1341e40e20000701910858480e118004c034641140c0c60b21001b040e1009440141c0401e1801554070034005814003003110462513405640b18044020613400faa01000d003404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665772482 1250 665771232 665771257
    0x112062606010b0c072102090c0301080f070305060a110714030405010f030c020a14011d010516110c1c0501020301090504120f0801030b270f060601021605090c0d02 72
    0x811541620034105507041e4003007154a0030070000f01401c4107002c1410002c9070306c881d2500382036414008540314030880c1d82c60001d510aa0800400c44c150b480e60b00918141ea405000b1940c43e00d5926504c0340d82d98005020241150303000f100000d8840080d50840b6541c0c019410002d03040c1405030b40c0d100342440c0a06440c0704a5000414180a0303940c0c849048600600c1900e420300030008000c0019444410b040700c0940302003001c2e030321105180800d41001c4002c1c25a000c149200a1485403c14024003082d10204480d02018041285d4030344a14211455081b030b8001403c050b1641c101000b1400050440d42c00c00750290910240c0840e000b0f1024500800c8441c9000c036052030035203420700541205d10b07071040601480c1007105006a50000c001410740f41d0007140b5401c943c660503003030b81c11014000c440902202054144803242000898445603221589040b900e181d103c138001a45c50342c1d000c18034042c03a001440c4042000c2c0ca001651380b90404211084a0701e44004440d001050b42e1103110981076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665773732 1250 665772482 665772539
    0x204091b0f080c04030f02010c021305061302040b1602180c03040b130b0601270609030221121602040204270203090c040504060e0a0c1809030e011206 66
    0x440c2500300080a00410191401520918000141c400640500c0c04013800c80b04003c004142164011080c038012150010f00940e40d2341c8420f120f480243c90206c4455004001d04021500490760b0740c001c2c2d0707060ba510514410309068034030296000e210081d240690340080c0054249403032000f0720300141d029400c400b10240da2883c184c2401a00d801021346100d1490f02000c4d00540030840a44102d0f810038024682500c8207991141e000d050342c0000c036104410481050740028401e0342000224084a100303961030309034070260390321190640c02108003414040d0071010551544048110040010055000184640002e15001304040340c0090300310020707200b4000b80c42407004200001c1c1e003800d052414800c2d851440e02d40c440c4c1d5100d4480701c0038540590740f21340c00f140800449803c00d00c4c894a561003290903420749820607110540311845010181388a1100c950348000c454080d402c66913405031140c483d1400080300440318a9950120a918565200c1d0040313003116098078010340004aa98600300c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665774982 1250 665773732 665773781
    0xf080309030409110f0301060f1e02030703020c062805210106020c030f0c010309020d08031312020604020a03320c0f06070f0204090311010203040b071b170d020409 72
    0x182201e1310350441000151013481000003100200040f641501c50b68a000502d6900c80c80051b50002c80604640310580314400700740000d59070001c09001f9450207135080b242e1410401040c80180d10682d00d0304d040c110400e014001071080014402c00300e4120a1030810315100c01968081940416245038a20304003200c0e00401c44240e040102c02d00001c01140035141c0d07546400c0000b030362628080e6446040c15260101c042c15542c0c0c1c61903c881c0d0315003107500c82d0364074504045000d41c0b038201d4010840700c0a11625095000c24800519640305640c085e2240d402c090464071082502e805a6038400d420801c86203203c3e59401480e120080c6021a03c1c0041003803090f540104045150041314640c05210180031b104007065060340b221132a0394058400040000c071600303088480034001c0c0b500414540c000018070007000f2140c2d0001d031007000a80d079840c8085443c141e904c00320a41d032250181c24107003c40794080c1f6608105005100058070360000514041e500d944002c140ca20107334820004548005201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665776232 1250 665774982 665774999
    0x61906020705010f110d11010f06030f061b0503010b03220c0312050f25020a0e010911030115081005030f060109050f040f14120c030d0b19120f0803090304 68
    0x5221260351741002202ca0290640356603803a0701c019280401c1004600084034440001c0d032081030700444001c8240b0000f0344a0805051101281600b203524524000e5100541014014501c00b501010380d5061b2859180081c0c071091038002401d40c581c803201c9454158012850148140241803050011405031031650034140c6901d01911076032014010104124005000c0c00c5c0c0407180c0f481a9810004103102074204030002a4280e65002900000c400030089045d00f03054501904a40728000240403a6010302c03100c035101d010a21850101a2504000035600e500920740e080d4808441d5807403d06455960f00003a02d00700100c500042e50340c200d00014040d40800d40240c0d54400f80ea0844107205040650340e00351100d01c12600038050f07603080e0200c81001030051000a141c490500703000360f1110002c0150b00e44a500510305140316034500180f000f02030030003038500602451003440f1303120b14a1500701c00322198030841c001243d850000e41c0800e000640700301e01031030042e140200151389a070b003000303a43e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665777482 1250 665776232 665776247
    0x601020609160b030907090c1e050a0e2e050702091003050c151306090611010920011101050f040c060c051f150b27030a02060306190602070501 63
    0x8041c0d0a40051a0780842c4030410200942181d014051080d074070307510f014009081901d80e0b0852a51366040c2460751080951014800002410445000f8600b0742c42c000c0c151154441e003c1000f01282041c00414010302e4407000c5d02c60312000741e8404140d040b0000c00c2e404004401192081c002c100040307054030070f40c1011a00b043c1d11150310401011014116102d10f65910300285045110309540c001c0b52004415190a0fa0103d0702c6000700d0880407030f200c0741c0146c41d0894a000c4c070000501012100d80e040b160500030b115131540c002c510104d00c4004030240082e0b8403d5400c60034140019440e020300214024417450f8411900941c001920707080a00d05003515442561051082052114852001c140d011900031800e4204440c0a00d510103010040009090300158003580b0300310710380c40061500354240080074005c102e1110540c000c01300010b00d02e1080000f0146d1034060744a0811080141005030003180c000c1401400308520304440a0800c403456015001540140c0144408005550304a4603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665778732 1250 665777482 665777491
    0x6060216090209060702221523150f04050a03060e120c030a03090f05150702280f111e030d050f070615080a210e0d150b1806010206 58
    0x34254034128003500000c2040c0110800a1f11136516403800e4078180180303ca400c250404422814443d1014480c501c000303198035842650154200c58090340840d440d08444824840001003040750020394201c4103010a0300320740f43ca40c018040411001c58281d0340c015800004500c1440007040300c2d050a109103040078001c0f000000e41d21020300c02200072140100035901a405240740018442109041c54031039031103020409801805840d1422442c0c0c4030240c82d40d440f0340310503002c82d07a0003140281c81c040c030b081d041407503084e404400b81480000202252040709041d40511440650521080d001800300100171286c06c4d011a0040d01d803000c1d60405006804203100785080150405c44510010486480b070fa00700100034550740c40641c404a000c4038183c03c054002c450444454000e6407400b00c4000e00581010540c9420502c1c510462074843c044655015034040c0641f110038a0760b541d503100d135200144e000d003400c3e80c8030355a140c0c607521a0032101c2200005000741d45e840e07062060019050100180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665779982 1250 665778732 665778749
    0x141b0601030516030f111503090c042007020118050307270b0114160501020d0c03150803041e030203030f0d2f0c0a02090a060e010609060f03020702031006060216 71
    0x20007013021a0b10811000013041c1c11540f50008190300c1400501101200450b8210010020080c880501c400040d0700e00104d0701540c00300400305010360070403a07244503a070741c040b0100c504011880c01544600d00e40340c0d5001a4100906001e0703110000a4201803031504140801004015640c0d48030080600450f4110081b0b038041000c01c801d400000d2000d05807444600e000c20000034462182c80c000ca0701c03490141d4104008645175810704c50204080d14004c1c4400d030000342000b880d803820001c410350b050110340c0d5460007180707040d282040c810f2680581a84028400507281c80010160f24107000406030110200c504554602441400c00e0442d820a0203082c1292207214404075140381025841d00c441c030340204040d0302c0e0241320448a1906940c0310009400c403001405100e104a100c1d080300054880700e80840d40791740c0c4c8544044450f286144500800103842400c0a4400390081e0f0081c241c60380054243c2c0d41d1040b50b1120307902521581d0340b1001c0180d11030444d24121004408003040580000c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665781232 1250 665779982 665780023
    0xa080d08060130090302030c060708190501050607060b0d0c120308090a12030515220e151321020d0f0306050603040b0c1213030e010905010c03141b06010305 69
    0x1600c0399084240100c3c100d82540d5a5001e00d1005d25000308142d070700b024800003c8819603d4010070040c00c01209580798456800700d61001211884240178407410703203401910050615100c1d0301d901c1c0140c6071800700e8a030010084403400d03012480282c400b101410311b001c403043c1d40c03956901d0700820483c00100900d0b01c2d504400c1c0e00308000f41800d0b6045680c41002c2c035002c00c0c00d4a03a051120400d03582e000102d40e00c00030020014001c040e03e003008104501880b4000c02001e64010b9901e0784a10101c002000291910300010316241109664107a000d0b0069014120a2045417900180180e421000340c004d80e1040d10560328242d480614890f050780d4600e0207002c0c103850600483c1c000c0c0030281000345803014010000e1210320b080d200391a415003021115245038201a41401c410058010058000610070340402c81b955004d000c2220444006070b60f9450850b10315142101c04000c0c030040034015610400404c194a03e84400c844181500c18024114070b5140d4508a03244c51080e0507080b044000340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665782482 1250 665781232 665781287
    0x80a1a0106080f070c0302070503070612050603010b01120911060c0114011703040603021e070f03091a03220c0807081e06011a0702030105040606091a0a05040b0a080d080601 76
    0x20307a190381041032428400b940fa1000d00d1b042c2e040c0000380c1c000c80c0d01445003c03000600c141e0b12061030390703e82503d401c040103646c80b901c0606003a1100001042d003c00e014017468000307807007550b2120104038010381582000155070030010300554000c011121079691165042102c2610308070700d2900512075001c50340d0090066800d211344074015032082c1001e0550100c1c00101e50700c007481491042c0461100c038903940b60300f035180c00d414090200c00c00707400045401704042260400070300007502401d142501c50f4207503940c40d5505d00c420508900001300d1225075901003c0003421485c1000d0141410a018000450900101600d0107684d16403c81420b0f59030040c650400c0300100d955415207000303034644440c80d800e9583e01c0915210302c01c0025010362070b2100300014804540d010700c051358002c1c5018005001c404118201d280340902c039030303984040c101c0c0b020081c900c0c1c50362003a4030540020b0002c84250b5030780c402c42070406d0080301071000401d4010003041400e41e404201c03000b121814100e41d4140102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665783732 1250 665782482 665782501
    0x9060a0504030606030b2521060506070b011a0301180e01090605041202010c020a020a14011e030c0954020a0f050717030c040306021305040f0e0604110a080a1a010608 73
    0x8e0990100c4007407107800d80b14901003d1150000c0000c1d0074085c04651755590f040c50003884d40d907424800d0000802d100c5601804511104c800c41e4100e42044d0810306850320301e101c5150003003001c52041c0fa0700d5982ca50001c0d0000e004c174041c0b87d00c02da010b140d04a41103140d105029082d988061050070441d04060700050050f900c4070022003c2c1c5a0f64a001c0c0b8040013040010fa0711310f020b008004000c400c00d000d040301d9450741500030640404041c1d072440b0340255a45031144100d60410600c802da1680a0b00e1000c6101c81c0820729019075009a0111415145441c02e0640345020080b01190017038002a07841040c64010030010490807031072428614204050700d80f2148024030b02801c1d8000701c1d0000204100700e1600301a42c01a41d000030b400c5641e42e03500106110408074900c40d03240102c0c01e2001c042d01c82c5500d48590000d8651220161107542c0d5290f450b040444485000700c0d41c030042009021890a0041041d100014807500c48190f56580880b0511301000050340a50100415401041003002d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665784982 1250 665783732 665783747
    0xe060705070c0308030618090703050706210f020d060b03010e0c090631060309050c06031014361311010305060a051009031401020f09060a0504030606030b25 69
    0x83e000100710b905c81c0c0b04d020024400e120605000040b90900e80144074600394041414030840e072254044920550740c07080d0681e18050407a0740b09019200c903031441041603c01e500f00640b0f82403003210051504200914410031584150030440651801100600007031501d4040c0c91340151140808a0514648500042c1c0ca8425124040000e001d04804801005030300f61000d04401c02030a40303240c0300e9440d0000100100716001c416112441616003461403400c00000301e03401114559031068805003840c1c030045565091030042c54105c000f140500c0e4407003580940d40071100144240055040701c044042c110040400f400d40c1c2640310818501e000003901020b9451811442800c0100c0c0f250b50300030000d103a610b1258401a0052031000c105100c1d25440910345040c1ca10804111400718583d0ba0402e00301d0141001101c80d02d00304120700000d518010700074140014191602c10f140c280c480da60324040e0345983d0300c1102c201103004180616001e090541c0030710040104920541c0b50a4244010183d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665786232 1250 665784982 665784989
    0x170105040816050a1707061a01050a031e0f140a1404030309140114071103040e0106270b07020f01020d081f0f030b0402040b0d03080106050f0d050a0e060705070c 71
    0x450b1076038500401c0040a221103106650041c9003640d40c0182d545e20031519510010013195131900c0c0903c44400183c400c00a2085a441a92a14203017040500c054000f054000052003043c04c0c41c1240c01c12500b45401007a1007214914404900507a1030314011031070500c0030b440790300080d0808040c0902c00080c507031507640c4140c140c580032503061041e0602024403020380880103447e50030100d1240d40100c250030003c0c01550b855407800032060381c00c140720751240694040c00c083d210b055401085014400c0781d4040c01c210503010b40e17421aa00549920f0f0050107180c0c00a4280d0300080391b10802e5240c460b042032000e00342800a00105248603000400d22500201220340c0410042d039190b0301a12140751100107818800011756400e9100e052146031020201c0e0101e04c41c0c0e0420010020f41e040c500380c40c0b8a411350546400007aa42068401c1d126600300c0d02c3d007212005420b0100d000c2d102c08902031140035403103c400000d000c855200c0c0140c10010001d03e40c0c000e0001c10400300340002e51046109046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665787482 1250 665786232 665786257
    0x1214031f03051005012606040b040204020c0703030804050d03061503050411310b010503040b070216120b0106030203191e090b1e060906040507271701050408 69
    0x228800101400e50355403a00050704512a94892001011080e808103050318450150550b80c1c124045541d51003c400c8010160a40c00c08000300d800034082c810980c2d001031009102500b80410320000500d44800340d4001d0300064003070000e02060081c2805410100c0ba50340c541400307040c2c1040d01e8401c041c14902940810503541b84001403d0100354444030a2015000f00341c52802d80c41e000c0032210380c40b0381c0742070120002d00300702041c0100000b622440342078001c1a12218119a02c580700c81b50340020040c1110254094041e42c1ca1079807654807000009000c6082c2850340188440c10241c0e0303a030005030012030616104000780310700d000c241c0100350184920b02101040c80b03024034620a600c5038a10344904042803c10520380200101c600741c0e50f106d265145642d0154003060942900721550a84135103410121560100e184c0d0300b00707500300d9031b0300c40d04030704203045101c92f901c40301c0000d101d650b0520b00002d50914014011070715800d0a00c00d1902d42c610082c06a030800b070b22050050300c24000b01c2d600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665788732 1250 665787482 665787511
    0x102071e241218110117010b0d0e0c030712080f0415020615030705060c0a0b010b03041a06090a0e0a0f05010f0b030f06010611100c031b0203071a06210703121403 71
    0x540e20480d02000d840346c05038400c40c495690f49008034602d4100440a038803031400d21a5024801c07100007800b80450000400420072071707180580039412141544000d4509550410200c2090300541d8001d0004005800003003004124961000342896405080260500f850840004180d07500041c06416194211903039a6280084071540e4504003c1400c0180710b00e0030600005000000c54014520460003000c0041024030011104070070312408444042d40642034070042000000e40f030340f0094415000d00216a1140c0781a00d640032031000e2050304513210ba454480400901140340514070b4800c00a400400150f28403416154072001c0501501c401c21400c0d0100ba200c950042240850081d502d110802c40c00e0803004006000e003005110b038081d0714a004610885042c0300100302d9a042d5003111408000811202c02400111000f400d02ba034041c2c054808507054a41c666102c5440400800c01007000601c0c514140204100030403a40050000d20750310392607021129030840e40e22a0302e002d103142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665789982 1250 665788732 665788763
    0x7091a0a030b0609090610200a03080f1b0702010e040e1011090307180914060f1b0d09050309041a0411090d140a2109140102071e241218 60
    0xc0b00c0c88030b0244044882d48400c3c203620b00001009c20319084d203d01980e00d0442680d95810703030300c0d41400300760703250040364015904451240c800c40b0003400c072182c8145015540e5008400000d03003a1030302506280c60580049240203c0309443d031040e4404001c030b42d9107150416010b10006900c800044c0314600c0005803595100a90700e441c1ea0150361500e40c4501120801c450010816030b840360110785d6906000308444c0410300c030407005100b0191200c0c0e1a00403528000b180c80c1004c002e00700b101c10807195031205000c3c40b100780d80d03540503c2580b00c00300050182c1d80e04141d0104016a4989150f0400912082007503800300d45401c1d450350442504039010035001c103a108551442c1051451f40680240350610700d01d2069411072066120115807030351500e080300c0d11202410301e80000e0440c0280564060801001015294803c0d0050b0042c4d4919089a060350707960301d403035141402031440c0f0511f001c25110303241c440c1d009403525041c0070384280108088184141d0203200c100344848c0c0a0300c0c058030110100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665791232 1250 665789982 665789987
    0xb010f02031c1b020d030f14011701090602030a09020f0a03260409061d1b0d09140f01020a0216260f12030907170a0b07091a0a030b0609090610 63
    0x103141c07103180e0580c0d600c81c518500c03000a490b1405145017000203070800c55801c8188030f250042c07610003500d18484584507403910b820501400c08100e4205195500e0720031900201d00b02e03101840c410042c3c0360001c01e0301010340c4100403141c0d2507400d00e6482918848000d1010030952503204031001c815410b108003207096007604200034002e55004500322400e001010034044003864807182c0702c1004803002c00035504c0301840c02101d80c1e05100340700c10070103090240c43d2003080a50400d001c1c89005540499800f0f1016448908140003034400202030b03900000d200301c03400d0741007002029542444a030002c145080212102e005500204103a00448811b54080382080d000e00030320900c0e100c00003c0380c00204050114100316002150380031864010100001419182081c0c481764203105880a0160080e040e9100c0f0703464880a020b1000304040d4160202d41e00491050032045210942c01c41c42d2941040c070760080079039a40e000d206016a0b0300b4003d20720580c80d6610410703042401111011444400000304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665792482 1250 665791232 665791241
    0x10b0d0e0a0b0403030b010e040209100f05070204051302090f070c02010e0f0d0b0105030d0c23010902190315060b0720180901050603030a050a0305090715120b010f02031c 75
    0x303402000700c0000c0c8020184c144c0e006c554442c0080e250810415050300401c422400342948068118040740c100c008068840e111001e9442c0311401c2850910265402040850748205e541d901550104003401301075103810720b0310b15404000c1c034a511500380781502c1c004005041004000b17040c00ac901c00c40c41c015030b84220120050726005001d101c130240f071301d0034610749003102840f031180203008222041b18400e1241031048041c40e00b00d812020f4011102120440c21200c060510180b9542c40c1182c00050341d81d41d003070012491001800282003421810b180c0895145284c0000307403949001c00800c00307030088200381e9410580140c0441c0c450000601c10107d02103c511000303502503081d0301c0e018070b102c8070f2102c41c50250880200801450b075035481415924400d5216a40110304c00740003407440b0500c079400441e80301c1c81000c29507a10350f503100f5002e0b0010140051a5010420b010300b1b8040b540b04030b10030310002000920f4001030b601c0701c1980180d200e100e400f255031480c0ca50544030708154080c3d07410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665793732 1250 665792482 665792503
    0x1212090906060901021906063302030a051c0e1203150414060415090e0a0b221502070b0c030f070207050901261b03060f04080a260403031a0108010b0d0e 67
    0xc10a800075080c544090864009c412294004000008501c0700a4070020607929950b0050712041e00e4280480d054400c003401d88614003003801d8845000103e0681e0622402ea020020b02c02080d03183d045c019603041319500800402e0b40900d10704040c3d020401c500004064104800781c078001080d02081c0d07205020622203401c082d0030f41c1d04009140710343d1400003408500307060003078443c101143c4880c0d414580c50000c01e25002440042c0c8040d90700031a030030014809480c9256140103150415603590300c207054000311030b024007040001c0100300d031841010340150b600c02c0c13079880501006e504010002e0003580040c0111142c1010710324804094003c5a0042071a180a1104413510007491714510851051207040c510300074051000441c5400e1000301203d406a980003441904140eaa01021078003004c280400c1600005802c404ca2010100e40c03c1c1d4034045c81c001d07a0301140020a0380a000c041803071a030f1820b410001d10070010458500d140d015a00c21540007034011031614410408985080c20490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665794982 1250 665793732 665793749
    0x3010f0911030112320d11060a0e032514010b0904060c020a17220609050402070309030602031003050733050f03090619060320121209090606090102190606 68
    0x401d0321040414101c00465000307131742044842c000c0c90154100c42c6258405440c100e645d2041010a0b00000c954206556401480702281c0c1045248640d19510203440c8604001e4806521900010700807000035900d40c1c40f524a0081c814814800042002400010009816650b88040d4107040d64401d00000c000703a40c100c04103032246042598240c000e984113842140b0242405500c205000048031680d10488410b07131255102c0c42d15110600001c0d501c080421400c028901401000088407840650b004580450b03900e8030b8181545441c07442c008079900f09a0030700080440d01c2c840c0304118103d81c284004012105000c3c01c034101170541d0180280c6d40800303c000c20100c2000310f031a07400100c0d40d10400c0b0408151513946078507007000c4100c5e80d0a001c040c142c0010f85c04030503008094813203244070302c0320042c0c00000f002020607105c030705020003441a44100c0b400018088138500c1c0640110350042003c0f20704500c0e000d15000007070364405503040300b00700186070400d00314140311880c2c0c0b0100048c0b1640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665796232 1250 665794982 665795033
    0x3302090f0103090203120a0509040e0705010f0f0525030305071b02130b0d031e36090f0903021e0a02090405030c01020a0f1803170f040906030803010f0911030112 71
    0x15031002c8c2c2681c0298140b240140d29104902a00240000d42180ac40b00180c40d23800d200654408100c030b03610450110841480340400075105104e242125024005001c2d40081800440070301c2c0007070a40e0400b0b4540307401c120311450103146c0e005556410303141690f4100c5100e5000b0000b000008040c15442d040a680038000c0e0721060f0506030002004415980b6002c1c1c5600040c003103910603548151542c1181d1400221400250810000301c0c41654501d489840165030310750341e8214040c1a03481d1905480046521745c076114040580405c551030a0540020000c5000c00017907519555824507044083e12a08086010905004051040f5854000103030001c1d9501c42e46034a000c1e0035411014900800074039640c01880710400c40da003203141903a5008056101002c00c1e100180f10380d4201d03500206248100300000100c21030305200d4000110302c604802910396141c40004540481a43d0004c0d400b1420018400c201030b50103030032a4103640c0900038090304010a414140100e50b15604130909070082d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665797482 1250 665796232 665796247
    0x105150a050d1518290a090f151b0e060f0319050c040e060301020702010215060a0e040501060e06150306040c050705030a17060604051f0c3302090f010309020312 71
    0x40c41541464068002101790081a800000d0f1481080e400590342d1044030340405ea5114003a0082c1044a00461710420b0102494403402d51400c0a8651809901d9a81c01a40c070b11400107a00c0004040ba18146040921a2000800d03128480c20407070b41d05039000000000c00502d070000342d089102010039010491803814401d510816401801001c01070b03840c01001603690314050080700c41455041e4054000014500319002c1480c030b0151025521812868000c50780507090036015100d01e008600120780149451003070392001d8000340c0010700440c0c4024850400d11450022240c100c9419a0000785011080c00d00b00c40a00502c03100504a0100046000c10182d11903018001c40342107580384c940f55154101013000303502c00c86c840e90703400c01e808041c2c8030603041d000e0b0102e84000380c0c1414401c00d200705590f50a10700d0b506c4001443c042a40800d03520407100420741086d0205a44100214030340a00240041c0c0c03098040c0c1d61700ca04041c1c541910070219101403000704844d0741d5910566464038603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665798732 1250 665797482 665797511
    0x61506090905010b03011202090907120b0105101b080315150a03060603060f0303031d010c0c03080105180c1b0106090218062b06260105150a050d15 65
    0x1514840c00a81c241044004500c01c1400000c4904072200110a80b08400301603080c4101600001d100c0501c5004215001950034003044080e03182c14800c02e810b000c6e40d0706010802c00300050360044a020081c00055150194005051000040f60003c20554580d9a208101d4201500c160060361700400d04000c015800d42c108009001c14a000d034409015058681508034110b07170541c0f0611007100d130030300f1080010034000e901001c1c650504002440205405012242c01c4da0100c81c80040024050940c04041c1940881001d000d05400c8602032162408120841d0a087c4041c040c001c8006002403c00c07140d220649071400681c45030402400b06076901d6003800000d400401c10008502c1011002a0040c90640200c450fa0807a448800c02480050382e5001c0c01c140100e009120007503900c00300800d9112078468598040310750007109880c04000701800e0707425281c000d0405602821091500001d603960041d4100648009a540d010b420906040c20340ba4089031050450245103800390b039070b40002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665799982 1250 665798732 665798747
    0x501020a030815150c0d1404050112020d11070203060708060d030f02030c0714010f0e090a0908070b01030f062703261f05030d020c1e1c0201031b05090607061506 71
    0x4000c0401d03501b1540180809a83c06d0000c28200c41c4948820401030040758055a10055840011000103003008200203041040f00c00101c0f882d40b20380000f1506a04501d020010035270f2002413841d003040d15080120202d0308480340300703000074148100900180c1c0e405100b00b094402414042048a44a6139103047c02995503140c0c1c0040c50000d420ba140d01501c0500034a442c3c1003121000d03004001c90355030448082c000341400700003110050b03010001c0070046455007092030302842c0907a8a032a0900250700d040b008490003560f40050081d0400454004031402c0700707080228540608001c0d00c03148603081c6103000000386c0150131011140001c144038103050a600e004a000c240075211f003200649400405994400317501222006a0203c80d081c40c460500001c0f016444440032a0360031048010000500f00580e62032110700c0000310340880350251b40c0d140c010542400c0000b8091718143c007684000030010700c2804240c6004000008203002002480da0100101514a280188010761070300c1005002c00b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665801232 1250 665799982 665799997
    0x80702060c040e010b03070e030d0f022404020d210c050c091006110a0206030408070b060a18090f0c0e04030914090103060903020a02031204030c0f0501020a03081515 73
    0x62280c44009100200460111400d840c002400143c0d2686408100a500da00003842c0008005044604102c9500d00300004d03076505200e6112260249284000240b804c1885200500f511450800581c0071b800070003459900030b0b8064032000b42050b2141461884009040342c0114805201400c10000c40d500a114104540c81034040e5182c2d5010002005081c01c016200c00c210445202810401240540a0044a058030318241c8085014039000151130b900212000d03144014000361000c100700240038483e03400802110f20031a9941404610800d52040c101002c45050380c4030521410310002c2c880145100f64081001500c098603940d507804c2c0b08201b6501180440e24850b40800e100181030520b14005001400011107030b861600c60034003900707c0c0b82007a0700b5401841c6100300562018400c2c40c3c1c0240d081c02805964520310701e080c45851425600540c0f154900200074859a0f0707010500b0400b8035058940382d05242c40790380b1180090007038201000c1e0711031102e080e40700c084100d00d40500f400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665802482 1250 665801232 665801237
    0x3414040f05090114300a0b06042409020a0903050706020f1002121302061c06051003021c05100b0a0f12050402090403030e01021c0b0307150905040902011e0807 70
    0x2144d0b69484400703c074541308220154480c41a440351071400d61114840032040d80d1243e980e024460310100801d0601c00008000e44409030a40101b03e090b0810740502d09107120b0358280155070091851842c5039103103040c040c0b07000761a00010002c05080c4200c4824020350307040015101820390300c90019584080070700a404c1c0d18080d0001c84a0034009520980b031031100d007031036008525505c45003244611440c82208a03400399060001494848600c0301c0301c0b01e0502d211000194050a00b020003034005022800501003500406c0302d8548501c800d20b440010640e0300c24042495228802014070100c2035800170080c1d14808510008910703030007041d86038000003d803600a4408008100c0300c0039100210380280d082144140490000f070300c40d80c00003420030105030006040400c019042814880440c2a1424494840b1b541c80601c0c80e0600c6100c0c000c000004050400c3e600117070014010444600c00d191040d0780c0d4416030740542e4054100103181115100d498100940041005018014203032000c200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665803732 1250 665802482 665802499
    0x409020706110f120c0c03070b06120f0c040b0103060e0a090c0b030603030712111906060b09220b041d0d080118230c0309063414040f05 60
    0x924003960203c40c880765200146514090000c215042680000360442c0c040c5001040b12240d00d14051002d0002e0038882e0607040c505003888810024a00c0140d981444982c00440903a20031100004900c4618038040d02c01061030004800142e00074056984140c012000020800400140d190300c081440c82c4141c1c00c07171140c44d450720b40d11241c0d404110344058040c3c0c820041480070840c441c24561621002e41f60003204107071110501c0d42403110903204050003034442042d00301007103d40c2c001c0c0000b030301c000c444260030866261700241d500501c8132115140c4000313034503590006603c182c01c000307000709014200340418809010042c2c60304030b090081c40d26902500e03d04501007481346c0c0b5828100ea040000d080e43c610902d2000300020502c158010280540c0c01d000d0070209001600380500c554008a0125120f161040b21203091010003050a41e1404d2074865082035080041e8054244c0e2500c81d600c0500e4000007881691101d80b49903503107070401004200010544455440b44050756030a07182110b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665804982 1250 665803732 665803751
    0x6081c0302120408070615062d1b0609061a010f0903320601170f011104090905010b0a17160308070f030516050304030b010806090a080c0c0301020409020706 69
    0x20100c0c02044000340e0344101440c08030f000700302c8000150801c5d5000e1034001900d1601e015005c100b0b02507542c0310344042405c520101e0f11081c1410111054485481c01401118400800c024400c0d508443c001040c1d2048240b5070081c081213600074030f030782640003500700007031104004603120034081c080125000807640c504000c07080d40724000a03022254000c0d407040179004400c183c104420010705044412480000d403003114420104400c81c000c0c0000701140a00f1003048521a09103a02c150700c0c0c0040f0b03030512140c2c4144c03a08480458013243c0c40503000084040c0c0610f8280e01508074000350035888040620040b0f10f031b00b00007251074042802c034411103244d000828642c0320031040921000e040c1d01c4047c00000d002c07d10001200301000e20030300c0d2241c0b078503124403980308001b02c05241c11f8540b940003180070310030401500c0d080c83c050041031000b0005450a40c02203075172454000402060030f40b000c901c5050310b400070481100c43c40c03c010029522141c840c00800000e4200305c00c140c1d01c1c2407d2a8512 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665806232 1250 665804982 665804987
    0x150b0304081c200c060a0e0a0222060f0303080c1803160807080f0604060b0a0503101b0512060d1e1b0504060b041707030b0a05092a01030e0a0606081c 66
    0x100e0200c804c40d0702901007550b0f9907003480020a8803441d981700c6d5000e003030b80080042c1e0760070440c1c09003400103015601180c510018918100c403416001100b160569020074000719400510280c0c0c4040310041c00d56403241c070048114182d89003640216010312401c0c0f0481d0552550100c0f00040c0c032282d00c100c3e02d01d581da88850740c1c0d0300c607140c3c0042d002c3c81d00248007140200c1c07580d400c041c15004004d800284115903440c0400d28040140c0c010100ba40e40e1104080b9000c00d0300c081d09141807500380740043c1410f00c0300800081d1000003501662181009c1c3c02000200401e0b5000d601e000031001e81c00d8034600909052000da07a41b00c0305401202d42e0352509000c199441c3c244142c0059490710384003a802c01e410b00c1498030403800c0e8844461018850b1410000000da0300b103420030720400422030041349500304030740c0b1903140059401c1c4040d40e848281030140d01c0718103a03040d14a916002440e0114803092107041300c82c20074404d4034020340054140b51002c1054a8001003113142c2150000d842e10900e42d886804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665807482 1250 665806232 665806237
    0xf0605060405160f05071406070c110105090a05011b050619060e100b13080303040809010206060109053006040f030215060109140102010f1a010210150b0304081c20 72
    0xf100c0200380c0700011943c05a10500150524034440d00c1f000c1e0380c2102c0e143c1d6551a00354102d0340c110000b00c803c48901c08005020b02000c3e882d02007070910f1030410103803000007807407040c560003400e04000d000d0304180446190131042203d83d0390130900b5a0718a04028404001a000810601d12941d04010700081c1086c181042d4a11031802d003000b4004c85400c4c5030b00300c3e00d15401030014001d44840f8007004103580c101807008600417846002042e030b44502500000e42001c1c001003005040c403445000c10446512188101e8081c003c200008452030b03010415880d100161508490764144a06010402045980c06400784440d010fa001c44d41d40328600f054254590104440041c000b4104110400c1820400059550310030014000424010540309207401100c41da010f41400041200d0480034040d41c06110300c017184a059002480305081075030407540940807a01c9541d4400000000003010b0241a4043c1d912941c031802c01d415640c4030508106000d41040105404910114a05003103100d55a508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665808732 1250 665807482 665807521
    0x90255110c0a0303140d0c02100515010206040201031107080d0b12060112020603070908060703140a0905190f0c030503070204060501051216090f06080f01080a2004090f0605060405 79
    0x542c1c100c040c11030f130b0100c0301142c1200407103040000c180417040108100307020f000041c2d401d56005150203c1102001e1094842c041c003441c0e240e031902401c00e081a40c5c003003130007580f0680a0130042440d0b0002d91242500c1e00c6041c02c043d1145030042180d03640841150425100c2440890780098544000e000e1980c4400c03082c8640344028021040600043c01c00300059903015076203080085d140d507510866a400e00204685130f000181e55540e81024210002040c02c1d000313401003034100702546880d900c5c240d46821161120076603112406000e800c00104900c2c031609a68481600c8030300035520300e091681c85c0c1018004070320941c2042004a110f51048094410a40c0100014002911120340c11a204c5000000d90801c1003440c0344003107446948158568003d00345540c0388120b62030b00580746d414000c0c0680043d844d075000714001d140800e07044c4203581d00e04219001c10f00c0440303141c040000d000708a401001000d04642421010502843c0d502962042c0c0382540e043c4060f03602c0040307034004001e50a2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665809982 1250 665808732 665808739
    0x40507080d0c14070b071a010618050409110a06111507120b01030b120c03071502150c0c0703030c020f0411031b0d060e060a090255110c 60
    0x1c800c40b020414041c44003010b0100e1a050358006500d4080d50401e0b64400601541e04004007031140c140d480040d202d9500401891600110b854001d02c04040c00000620a5900c0765880344002c00900142141500512000400c104505580c41d0405004840104505c61060146002c5004c210031030a104034480d81c1190b41d04000444d4452181e40106842c3d03450504040d620210010540c41e01e005201d6901c1012000300f03a9216903500301840e01c002a003040071a9080206130340086500010801c100201c0034001c8100b9640c0d1841c451841e001d6048010841d00c1550000004d154101c7c14010583d40281c5008100c0c0b0181d605220a88100e4a0003e15100e01003002540307840000d40444c9204140003035191801d02110500d80036503003280c0040b141600c5143c01e000301d0340f4150060340014150500150709000303140001c1b8000744034000240c42da032601d00c400c0105940c80341550204030002c1d900c4a841c1d02075412a00f40012004c0425076001c504100c0c5640510000020190142040103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665811232 1250 665809982 665809997
    0x8010806070503250e150306040e03190c050f0d0306060306090515040f060b0705030a0e090c030112030c0501020c07090c090f030f0206120a0c031d0607081f06030203040507080d 78
    0x5610400c1204035160414200311a451205c160741d41c40a1981c162603c1e01c44030a130300c0e410200100000c07240d020300305075510382c0304000f40744046903442c0b091851000e0700e0070030381c012090b242415400c00c11008090782c03080c02083c2e0a04003c03a050f40c4481c06995140d6010000e480e1a0071100f07080781e00c00d0f584034280140c8000403651618040e0007020090b03500c00408103095030f0300c2c1545075154016400484d62034102050021629600c130303803108141c0c8011101e4102c182420750072800644010301980c1c00030040e400b02d1006041c007a18002d8070311a0310000031035407089030b250055260916401415540390401c4407d84411348255401c2040d10351f02d0502140c864510b80d9502c0c5414014502240c021030144004099400c400d003000f0b00c9030700000004100c24854040c0101103030203000d10703600c0c043c180c00307907003100c00d200000c503564000c4c00c42c00e01940030b40761015008015280040c010086c000444000308010342d064001d140110b01c580c0880d9815a21b030f200c0c0c56210382882036101d0000d5040b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665812482 1250 665811232 665811271
    0x12020102030708150d30091701090206070f020d0210020307051c020d0e03071a0307032f0a0c05010f0e07090c0e09070516240e100213050301060608010806070503 71
    0x1304083c10f200a00740c581200501c443e455019501c0f4403806c44501003840c46200f0800e0405a145a04050f1052002040340d076400d6070011b5402c5c05241d0000c3c002c518040500790440d295060300b083c042e03400420961041c0b024000003580e036840000b04844c0780c081c5014060811103000701c4401c800b44540c014007129144140107c84401c0701210841c2d0610440c0000588684251102d141e94040d0901c40c660300e10f0001800380580d071704036201ca10b403107a0030a58580414407408040786404084460700745d071101e000c542102c0e00d1000f44801390180d4a004c0c080c1024060503409840444d0f501c0013640e0b4a10765402c09501201e1201c410710f00071800060b102c0d50186050384000741e000b40d03642042402e01c0e41518980d204900c030103204450300d040308012010100302020307202e2030003079819005120302c10444c0703d900c1d1123100b00c115581d5041c0d00800e4038040f445200c113608014210160081041e107a480750018042d0070203108140c0315000c0c403408a15414454002c8900c1220100d00e401941c601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665813732 1250 665812482 665812493
    0x918120304150b09044205090f030705102d020d0e0313051018181803090302091033020712110d0605090109030f0c0c0e1312020102030708150d 63
    0xb42d06e810a04280319007410142c0781550b5071542d4541c43c941001c0050310345000b401c140d00d840039242a1030311950061000c031000650024400c0e44c000d507015000f0074814000c40200c912410420048603090400c2801d4004c0410b03640e010300b0706044041800e102c03521001242c00c0e202c1c4550b00e00c18034007000c1550305228608044e00c4526107060f461600e1402006084004100c0c0c2445422501042d10305550a14007203121380502c03112068a4400c035440140c044e030f409807002c802444002d0142c180e01000824038210001440c0041c40b4008800c0c00c081c0b40c00300312944143c0d038804140e04490703903e4001c203656440010042e0645420303ca070f94a074902c15031500700032440c1d1804107541c00f8071a240044000762050180034001d041c84400801c5a4190f49800342c092040e1a89510130010030200e14008104c0109514040382d2003c9003244050701c40b06e800c2900d0806440000d40300c2c1e100c4d869001e8100d507055000b10f104d5080d6a075500615160303140d4400800303480341059a4400410040400401c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665814982 1250 665813732 665813783
    0x90f05071406090607030908030a020318060a120b0103020408030f03011505030f01180b04020d0518010219110307020306070c1104021e031e0c04050a140918120304150b0904 76
    0x46c0281000c0600682d1200781900e1a480303202030b00d0041e0000700d07000c03104182080400780c80d00c00c22245241000b07400040108101d035240389010445890b031590b0841c0c3d034001d604031009820044e040d6962009041e00140081d0f00a20400e079064222100014410340318506581c004c4001003c4008103034603051141d0520142e00344503548c226507400000105d541d552006004801c40b960001c6030030301d0001e01c8640d0310340106502c540141d00410825152f40304a242c8800012003908103070501000507044503266000d2010029018810903007481020b07a084490781111760320510505501d00c0c0458140400e0340a0084490f0703211200410395007000c01c0303a5004d1544807104036404144942c2e0040c28081e00201512a40d02ca003100003020301650822890310300141080340d030010f41482044001c0f0780d110b83d0040642088580664000b080c042c824041c180070b1701c106800054403418036061803540d0000702d00b00c9004091801c00e80d00800d08004030340318410358110045100c0f006000654a0444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665816232 1250 665814982 665814997
    0x4020a05090a06091a031903020606012304060801051c0804060804110d0303020c150112030806030f0d091508070c02090910020403121b0b1315090f050714060906 71
    0x540350b242c0841c0608052142c0d070400130716441810705c8400c0201c203060030301e200d0312442a16400c4480c40301d404650001100b94001074286401c41d1400864803041003150702b202c0c24074140080009001403480d910414203070603039408560383d1240b001504a4904088400440104444000d0004000c854050102d0a0740540074081c003a00c09440a40001c001c08000d60044000c2030b40403138a03001640c400c0116101e200c07454cc1c441c000c20b50511014280805004100408200000300024102d460a00210300003032890310480703c13092801000980f400b002d030f0107070485a540d040e0312203400600c00c5410500030021900c2d0210300504540034482401001000e1010320712442703c1c0913171203c0c0036100410055000700301c030f13009501c116035004007000724003c6040240155403056002103030700c840343e66802c140d00c0c02607070407945101d1500495201d0017004c1880b40ca0301c4c003c1c8503003c1c4201070390080602c5101e1425294620b03154503204d05000d050180c0540c10060600801c0f58500300030005088a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665817482 1250 665816232 665816251
    0x10031106090d12120e03091201090b07030509150705120c041d1e0103020907080603010f0507020d091512091b030c09051308030f0717091b0904020a0509 67
    0xc0140e56000b01c2c800000b109001c43d8411814100c15045a40c01007900300700310101d5006010070a460b011090b5240031307240942d0310508088070041d903288400d500c210031052b80100c041d03945181654001d001080c04444201c218000c3c10340340c0e0303488107950308003900c03480007138035054200071380340c0c001144182c801044091800c00422011400d10740441048080d80e001c0c0c030040a061404800b03803560442000d000075141f40f5043c00600060741d6080305242d01a070b691518061642e41c040019014100071048940c07040d10b414240100c055000c034026003e80c045440b480d900307a541d0909052940d4000c140d000c001100d01990400600c081e801c103c010300e0103100400d211807450411030390b400219038400c0b107400f10710042c03c0095050a00030030798480b0f0303a017031f601001c441c40751101150341c40018240c610400e85400018402c5000300700000804085012124007440c2c60f8510035038038014182081004908403100d01c165141c0400018071941d4040c010151003898101804507902010700000360 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665818732 1250 665817482 665817487
    0x140d17041e0f0b0c091228080906190e030601060e130e0102040b040501110102040302030318030a06050106050307020709110712090b0304030509040b040510140d0f110a0b0310031106 80
    0x490748841c0e50704e01411291810381e640d0410081001103000700b10403650002e17009040100308403200140c20121089049144c1d1880040e1032802c40c0440c428821440d501c2403022643c03c0400c24240034a0900a04a89490b41024264010503a81d0b010900c10203001803d04110b1041d0760500b003070100084c030666480410130f10019401075080e41c1040c4c200a100903808602003003950380c8000e00b07011080b59240214641421500402d88902c292040a12140c00384441d002d0251010010000b4003078024130304002e1942c40d140000c0407030f03105441c14001445603103030100e040d0009110f0041301d0052480c040345488400d0b0345500341d5084902ca49000c0c8031148100240a019000045204610964620796561202020001228210300001c1d00403850401041280c0c00c00d014041d0030f03102c0c1040350104000f1070900080844c00c03a0800103044c8484014010100b05c0c9c42401074042500842e40c4842180d103560111040f804101c0d9814041001071030f04001051440942d0303100010050030261 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665819982 1250 665818732 665818763
    0x50702040912180308040b09130f050406050a2a020f1507021b090414240108060c03071b0f08040305100e0c060a05090d140d17041e 58
    0x1401c403480303210300b9220480c603454185929076000100f9403001202109401c01a0b0039500c40118501460041e00c520000001c2c4134074155441e4022084208105001440391401c4a044080a4001074a045030050304040100f1003100c058000c107000040f0a10740310b00740c400d110441440741024061180b040d402085141d907280075050080380002e014481e2022690700300103200134a40000c1840c402800c550402d0441601e0703803012031064100b81c00904086400345070703110803410210384000c603d10700d2010000510030320003a25100c41c129546081600c40a503030f0024440132078442180c1c0000001d02e011150401170101c000e94496140c081c002c90050307010b81c3d039074061584d1320a40050302c0a900c0950609000c000a0045449481000380a44030190850b8049103e0f4098120908248400492001d100e2384400c07607c82480c60f00140b09a90142100c20b006840d030028001060015004465090004083c0c0080d28040d81c1c3c0302e409030610803242d608050f1042600d120494400e2840a00c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 665821232 1250 665819982 665819989
    0xd08070302091003240605190f142101140f0f0315041a0a0f0b0a051c060b0d1b08070501170a09020d0c0609080c090117120c03030a0b120a030f050702 66
    0x201030501c1f501c0e100e95030f805210b80241010040102c082c10003040d101600380c03075903004104007030000b844103007107480e042c06c0341e040a421040305a449030301c6080301b00001082070340780e00006070011083c1c5e2105e05000c010001c0c00b010100f1518415055400170b04402c0e02800070001040d071190248001c0c282c201e2036400c01040f0700b0816182040803a0300da420610111600341304000502d4012076000102e2480c01d002308618103403138514004080e1104200d803003404520f401031207100c5002001c0c10b9240c20a8940b070303402240308080c200f00c060000c080118041e1000103900342540c805845066a81d0390503911a184102c004000c140303a6a00c6105400051f01da400304143c20030311401a01c81c401d420b0ac000104182841e602948480d40b00d0706088a903610b441a946040d10b40390004000c603d25024500d515003864604000140e11000a41400c9100003101450181d0480c140600c03c80490008100b00132240540340300c29500600350f810002800f40a4400ca10382c07003410309908044954001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 665822482 1250 665821232 665821301
    0x162c040318090507110a0302070e1503011409010606020706022a0d0c05270402040b0a051c0c050d150b132c03070b010306050402010c06020c0d08070302091003 70
    0xa103072030b5915481480482900711000700c00c0c0f01e565500410310304100f52402542c0f0101d500c1120004440c0d4004079181d20b0901009003100394001c0d000340440d03894541511001242225a40b09651a00e00d012501900c04a590070450303510354014040481ca00e60b07030700c6100e0f14282012200c400340204036078194548201d0040c00600420440000500c0d207014003400d046000b0410802c500c2a00300d0a100041100140b03403c5034040d100025040034000228400c1c29142e0442d40c1d1000e100e04450030114203103a0420142c40c03140b001d070b00c0007556030018002842001600242214059040c45446144541c0440c0700203000410400080f4000c031100400c40d020640c0700e481d40c1c410040361060950741750750301380c4140c4a04070041d480e0800c01d40b60700020751410300000b000540c03210041000e682c0704034034800721207800850440d42e4601c04841d081c0d4031241035106c0305c0401c4520700003a1805010344203840c0c00030310140c4540a500c8520300c00f1002040700c3c0030307110642c6c111045d000a84032402010f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 665823732 1250 665822482 665822489
    0x10c091a071208041b0812090a03061b0e0102070f090510180e06011a0714030f0a080601020c032b0908011122030c030204110d0905162c040318 63
    0x81d009a1414681018114a104203040060145c43c2c0c050800880800044084031070b10124801a140d40300800012644491544094115420401501c130012080d01b03400100b44459118005000750344001640c8800c0903100340c0c0b581180060b003c206500e0385401541d404100449d180071050340ba6030a119a4006224203212800c2d0740c1c81c401100c2c41402c000007400740106282d00031004413803070440e000520030078038000d0104145a42c004010381003041920f60514911140c80e8a5800800d4010688038080715140e005201d0b00d41c0220190601155030b0140d40070b00030880d16541d100b2031107030764541180c0d481203042140711480091229003c3c805c0a0822415a101540d20340d545900307802001105242c444d20190b001c0c104000150702500c03041c080b80c1e030564011a20280b085444444c0c1d0064001d94000c0c07030b061007042001c002c000f140300000ca0b928040d11481841d290207035044034008900c01c0c156268590a608500c055110f0b0714903910078030030310300030041c10403086100d902d6420315071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 665824982 1250 665823732 665823737
    0x90b04030807020d020c0321040e01030f020f040c0807110a0b3603070308100b2a010b030c0d1113020c060105010c151a040908030402030f010c091a0712 67
    0x805100d40c20f581409a00c2d44d41c0c400303100030001d03061a80e0000b070b218081d580d107039040e9681d01d0210031102c015000c2a80c0041c00303c00748020503580d41c0d0518400202d00d4045c22071003244115849031f42413500e841020603100103561605007aa4480c842030709c000100c0c01c00e407d903510a0240c00f40000364000c05c0c03144a80c0341c408207146440c2c910701e60400c203032090040433034502d0302c043e4440d1220000002600c0c003880e011314280341151074004049444644030f0f003008003181000607202d154044521700e442c203800c4840d008e450380c400e02c000d1024202d40e0740a41031a4150094203440c3c0440c0340401101074410302a1710403050039407509000551460307219010010480c1c01140c1400b0800040c010680144000e080485541016699404c0104c80e007501d002003455545130144c84140c0c540b003d07982d0500000d00308108040d03150a01191941048508078407900c1050411409807006000340e011104050311003c4150741009075807001d42c1c03905001e40c20340040a00088000c1604031109082041494 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 665826232 1250 665824982 665824997
    0x150c030b030106060e1c030e04020403050a05100c1215080d0c061a0117071206080a020a240f0203091f11070e1b0c010e0322050d0b0a090b0403 63
    0x9100741420364002e0b901c414103000c0c1c07404100009484441c56040300d83d407180f000d1222034201d46403d481c00001d030205203402610108002c42088000104100c2190050044801c2d02102980000584424403c5900014402c8000e884141c20302d80010601c90b0a20091021164481d09440d00e820b1005002d0310010b0341c0c090b003203c10301280307204450072000c80b05040c1c80060608400a0301c101741c400d22042c4000f0b2604005146a4410142189981506402405519034800565a4441d40c1101c1a0f12505412400080200d0040c207840c00a10b550721048050701510803080d628440200341030341c00d50104000f444401e070745070825102103072003107641094550100328000b041844801d04290f40c0358802c1e1001c0c00341d04071f1243e007240c2c8814031640c0c0300c8403940d41548410990180604010f83c03503091010180c101e0a010024190110813a1199021841d03d201400c0c601d40c10340c4207030b90708840c524403100c0110305241a11644100000c00100c1c903075000303a03112581c80e942281e0a80006888 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 665827338 1106 665826232 665826251
    0xb0c0c06031302190510050706090f0b010609120c050108060d061815140f100e040b0109051f09200a02060114030c0f06131824080a0f150c03 62
    0x2d8900c50318260320b00c0d103344034610a0081202084c00480c0c081013000c07034207402b0104107401c0095046002d18001c01560750200150849411900500041001c21224011002c01d0b484100e07040c100d0b1507150038208920f0b458403440340d45c03480c100203000242120070360300a034103c00145c0c400c10440d11100c4510760a1030140d8050f0100ca081e410802c028404101e41c504d0403a40700403428000303595040000040a442c40c4980c08285802001c240b14901140e888003982d5401000c0385103030117001005c441d684c1d8220030744060041e0f00c0807005118400c540c40e21026444410381c0240310715030a0300009000c611400c214035000d0b41c3c000c66182c5c82904070343c0c1c2d810300400d182144040445840642d5601070040f07448004d03440da40100340c0e201100340106114084585980107003003400010342d900d031480100c801d02070312000070248038070030010704078030886641d2007041c2c50024a2448 = true := by decide +kernel

theorem cover : BRFrame.Cov 665647482 665827338 := by
  have h0 := BRFrame.cov_init 665647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 665647482 ≤ n) (h2 : n < 665827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
