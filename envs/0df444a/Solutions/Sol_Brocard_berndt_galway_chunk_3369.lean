-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:01.413642+00:00
-- url     : https://prove2.me/submissions/b9c7782e-34e4-4cb6-93fd-c09b2f13dc95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605755395 ≤ n < 605935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605756645 1250 605755395 605755399
    0x105030a031d06071a0906040f060b0f06030c04230102191502030a090605240103090f020303190906030606081603092001020c01170106210c03090201091410030209 72
    0x3a8501542c0c02241d040e0f00192822030722032045082e50040e0b03180501840303600030300c41d000078100c07890161120007604c8034010000d000140d6a0121000588600b102a007030703084094801f036520305103030802d2030440c0d0007031042c1e084039a0094100c40905038900c0b10350b200e00d0310507130090103403c02d1a9451031a07620101d404581185814501101c4281240051486022041d20010314041c141c1018025154014a00207210402048200907100a07007611450302a0a02c1d000514038401c1c540100710501c01d41019515100105140718225040c520056040c0702940d50030b40d02594a40d401d4007941c166000e03410202e403510001410003005900301d408048018903020440403266120300300b54811401d101c010235201c0a94941203541c04001001080d2428a0a2850441d0342000710f000d00d40c040c000c1c0340401440041c0c55a2010742c4122140c2000008a001c100035542050042c0003050140c2c0200e000c10039400c0700003031025120394440544180a00043e40712128210114000e40c0506d004e80c1e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605757895 1250 605756645 605756687
    0x10c1106070f0210090c170a020108040b1504110403020414010e0403030f0f02070b1f05091303170123010906080f0601090b0427020c07060503151c12080105030a03 72
    0x1a98201c0b00d030003481c034554069804d402c00c0c1c0707041078200d6009480c150400047e0340e005010320b00051740d002d58100e170b120b03802c051004229109d05101413105501c555075694801e040c030745820101c500740001001200d1003150200030b01c0c8520300c01c0440e0b41000340300300948021550b0008000c0b074042c3d0441800c20441c10b00000d042140d407080c080490f000448180d440c101800c0420070340d080e070a11401062051144000b41c0107142400003070b02d070800180001b450940c0070101904040c00b90240c1c0c82020030b004801403403980c641070f0440e151050360710800900d07040c82d0100c15565000721001d000361a00c543c0d83e429580d488030507103895221b01410701410007460a02c00070b011402440500060b03d10107201c800c40e2911141c254135001104072001020620410201d00c01100c002103001c1155014100302d600c031b03503580d000ca01031a102500002e80217601d000a1074108007426890320301c90b43c480c0081c18089408000c040360810003d0003199095401a11403030007082c0543c0741d02004144c3e40c90b000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605759145 1250 605757895 605757913
    0x230414031b03151b0a0c110f1c05030405060c031e1201030b04050c04020d0b01180b0a18050a030c03021309030813210201020319020a122309060702010c1106070f02 72
    0xd030982c0d41725100751030025001c0c0d00d03a4810003804503002a241101212060401258140003421190036007092160440c142019082001428400e5400402300100090349403140e41d801561254000f840341000c100f001ca451048114548050325070042e41d5039554034440c0e00315a6013100025000e48141ca95100d2841021681d5031180010070f02848014400304009880718009810b521607000c4461114101e0041400104140e8090320810320035481d002421607246a544894059607422080d00504061008014050441c04040441e03100303071100000031820305d4505048815101c40200040c0440021400c5080c02c0d0358003111036800f82031610507201c55251600c610015100c3c035440540d4000c0b0030483c00c810740da0428200076000490941c038245140303500820803d0f0800da04d14040303035200000800c040d0f800c0181e01a50354010035040c00340c28400481e56454104951002c010340c00c100740d040d6124451400c000e0010351080082510751980300d415554200ea038840c0400710b1090b1105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605760395 1250 605759145 605759191
    0xc0b221211101e0905041d1c050708070533071d041521050c0120010f0b12071208090612130201020601061e230414031b0315 55
    0x9080c004603c5034896401c9585050180425140401e80c1120749010b0b034000e030303030b1680c0703003c1512039200b03a800301142080d13410300005440c0d600403600040d25802c1c002c11864100705e000601c4d031542018004485204502100b4891592007182d00c0b02c06a40b00c242e00400c1143d4066a4004035030a0940182406507244501240c00c076112540c0d03c00518480c42001c1000040ca5202d1030000d8140901600c0000010380300c06540e003034041c0007107040040408038112010004010780c07142c401ca4400034818084078080b440064801042114030840f5042e115406540b00082c41e5400c6902c452200380c0c00740c8440e00d580105401c8000c586030407040c1001031490180140d828244241c80b01c0d5424180c0400c030b400024a0700340b0580014084c03254040d400c400816002003000d1804c0d03602e242c040010380c041c9500503000d0307082c840440820035000c200402c42d01002c4501400b80b1a082c2c0840e80c0051200d806955003440c3c141c1d0b22034143c2c00030302080050300800d403581c581c0030382d03810491740325440c4220b8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605761645 1250 605760395 605760437
    0x28080a0c0822090c050a020a030e0a03170901080a180b0c13030c090b0f010c020d03020a0512090117040b07050313081b160302060f070c0b22121110 65
    0x42024112091514244110f9200c0e1241c006450f5051030100d080c0505200040c1d17503104d002002909010200b081c01c42c0c2a5290300600c0007540c0c4c0408017100304001491821840d030448802640803ca20300002a030091951055100140681181442c41d65458960055050014181007107444003008180b62840d29035241d0270045101c1e9401c1c007010751400d051a01110028100e45200b543c2c0c1c40108000b0343c0c1d01c00105108144c048502444103001d41c0340991400c1c08088008001e070182c5999200c19001010150081007003c0c0c0303412554040c490054400c00e54211001841410702e5004994003070f10480c061680311611007041807403907c40d5124014640c0040c6400c210200c002901011040824008201c900040d00c0b074000e03400e42158000f500700d00071382481008813200400e1140602016031102001410350340c603c20794030354034090302c022103034007116008480c58102140010028407500c44038010907004003c9a242909c02d90410410180040301c2c01b00b002201242d41d0703c6851650 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605762895 1250 605761645 605761687
    0x90f06050315091002030c0301090515040f1b090803120613060f03020a0506070515090c0414060a150c060c09030210030e0c010c17071b030528080a0c08 67
    0x2601c2602a20385100420300e004a01815609690300506c14440301e40e40321002e50b41984c079100d0300403545d5070b02d1592a4600d444403070a015801801e00c01d0303802800c0041c1d0b111082c01715000200d800c420544c29003e803003120080c4104107056000b04002c0400065070000240c0058008080e01410040b40380b1200a480c80382d0441240070f00501d10400c21890044201001090143c0300d0904000341030701d46e16200e03a40c0039848070319400780d00c0004000c0740007809001e0345144020300800c18084140400510f20800b210194062031580001013100d41907001c212100c0781940c0c0c2c600d02e0428241c1c0c0c400300502020103066003440703040c2c4400310050340c0310341201c124031100d9600040c1383c88000c0002444d16080394042414007003000c1c3d1000100d482c0794641040d20b1020005150342d4606440d100d44041d030076220500c2e18031124280401000008924981b5100320030382d5240d40c41e0200c0c0c40c001c2050007410030052030168204581c01c0d16034001c909407150680104a014145a144504090020b180d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605764145 1250 605762895 605762923
    0x224040f0e01080d090501020303131415011502011b180315020a0f030c270f0b03090c03070506070b1b03090109020109080303010b03061201110d09060e16090f060503 73
    0x1400f04420401034100181e400b880c0000c1174910300400030b9120301c0b0142241d903003d49251101402d0119a195014000f110343c0e007220440c00b1040b8440724624828010754038114103000707007414428414003c09000e84c0004150544c40704000e041900e020f400d4203001000382c0380c0c0b00000030200300c204591502e80c1400c0b0b000503a44244000b00103050f54800d9807004145803900c412100000d030b0100d03250411707089840c40490300c03845007200104800c2841e444030340d041000420200e00e40d0003240c003030341c01140302da421121007002c8441050385034082402079030740194051041102140741050300c1a041a612170008403691480580200e4a9104980014050f07444000f05800c6580c03290b207000003003124002440c2154145050300c1c40b40e2202404861080280410404141c00d0030341c00922841d00669940759201c05001e5a030018100079502604e5903440c1c081080b040d0040801d00020341c000442501c1401e9040c05c0d140e40060004203500c1820a681711030104950310200302c002501c402c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605765395 1250 605764145 605764169
    0x11b0b0406140601110c0f04020706180c0f06140d090f030f0f020606091305030c0601060e0f04050f0c03091e012c0706120b0d061506020102070224040f 67
    0x40c030461007407500005003e090420002c1381c241c5002940220304401d4a69088410a03040c50034400010064000d4070000f0306460714094450103203d42c4402525211841a410511050340d41d0707100019080c0c8900c2190301066146c400d0341030100000e4000e200300c229500c00019000b40e142c0318054820040c140440214540c00b900010f815042042400302d8010b500c01045680303001d001098400304041e140032061959907040b9401c010007402611001803030175003123840b950fa40e0304004154000845926010b242401480c0d0100c0c2440d001d03080c410448603652036680c0e02c884184041c66170005200390f1090045240204004014038081020140c0110001c20070302e040104000c642a00b0f110f0408940700e900c01c114400f103070003190340da0072504203041801e00d0041091104000e402410707200c1c1d0b800360720081001c041044c42d504c00002500300c18140d100741d50703c40740183e08034400c0e003401a5110900e41c20603201e40d984041380c2c0e82e0740c0c5920882036052695030310780c1c50440d0980b80c010107001c40d030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605766645 1250 605765395 605765411
    0x20402042411010e0a14070b03070e10050703020303040f050f03072001020c010f180e0403030c02010b1017180a032d120b010908100902030c04060b0306011b0b0406 72
    0xd40082d0000445040000070802241803500503560303400034400060030030002404100c400a001d00201d4002c0031086503003940c074600004024882101c4071640d034424a0071504120585115070266051640c0c140c0007140385440710b88a4101d901c4445104950b544210702500c40088801d01c00340070442d2141800c004516074241515090b250071a411078110f50056841c000540c1e440680d1140c021003500300f41100c42d000c602c4440c0c810303040e60045d0401c03100880030301c800c150741540070007004502c42d402040440d03195010401d8100a20a4100008600d032040480b5122820000e0303810150120700405558441481e0900f813298004066010035480c89100c03c02000c0d0f00150300c030318502c038030010884c5418410b015115040364034518810a54a500e03600d104d90041d41440040c2c00c0010488800980d903150460240541c18801c034064060b103007855003e4103107402070005a5500581007401c1d6560300d4011940346409010b04268003510040d0480496680b509950186010f0320010a00c03007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605767895 1250 605766645 605766647
    0xf0a0815010909260705011b021b1003020d0f0908040e010b090303121f03050706090915030f020d141605181605090306090d0f09031208040204020424 66
    0x80016480b4156080c1008400c20014003903030541090550711004070f030b03104030b183c080381480b50040420003080346d840c100d10200007120740020400c0040055007203404035540740003808107450380da101e6550031041080f0031000503400bd4000d000ca41304121800200c002002400e0016140c00c0001a50415400141800400c0c600f2080a0160100000f40d601d41300b04000401d0341d0b88900d80d032090034548080041100c000b9440780c0d0306042002c02490404107034407401d00b00c0d211321a910507040403404980000484000b0307030080c1c0030521004035010b076040d072554076500702544440704102d0b4021400d180380c100244820842c650300302d000c6030040c078101e070f4002484921a00c09400980c03041113400048a04084010034840e8010b02e0605840200c1020f00e80564050003105000c3e64180948010400701c0c01001460f903096800c646d456201c202c01014041d18040300c0c50202500359039400c0e03000500c0345e00810300607030400e10180c001845c01d0355801803050001c80808444c10070405111040d0391403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605769145 1250 605767895 605767933
    0xc0e0f27010501140403080d0207081b0105150d020a03020d051f0212060402072111010c0c0c050d0f14120a02032d12061201060e1801061a090f0a08 65
    0x2413804064818502401c0d529145a5402110b48103580c60303070000741c140d0030010644250740130811036030400002c41030300c0781d0300c0d0f4060300e0304417103a02c0120b40c04c2940b09814900704039040c0e4101d4010f400a40d0060030b5800340040101384150650b11442801300320400105c0a80c20b925080201c004016260843c0700c0c1d25545054001e841c0f644203030300511100d000300d205000340f5084108401600011103c02407015210341c0640030070491554070f0b10a4a4084580000c403401031a441041a4001d06840b07204100c000c0c1d00500028047c0100e50500c4800109050702171a0440f583c4022280104050780a200403a4446601503005810201d07499100d40100039084168011101000c40090000c180c69060780c050904d100c0c101400480c0424a1074980e0460b10f142c0c40c41da240203022464a80001400c2c4000680740051709582030028607400e024180b00d14002e803110941545031384880e0142010360398000305162039010a00b000110310f40d40d0381c040044001c01441012b0400949010f41000714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605770395 1250 605769145 605769167
    0x3060c05040e060d03180f181b0f020a050703030c050105060f0609010e0a03020a1214030306010516140a0302060a0c09080a02012102070303021c0c0e0f27010501 71
    0x5100d0107100500c04460848102035100342d013507862859007140e50401311002080400054240090050040ba030f078040101c0310f905580c4055004860003005e421184122101c43c1c032138a030f044189100d502003d501c101740c01e00b1008034610449801c00c030300da00c4441c00c00500341c2c412408500b0310041842001800c1c01810b52280d01104c50400b48a018008601d2070b20507003000e80c0c10031070f01c0240110242e941c0d00c1403101464001c0c0c40088115100c1c01441c0805161010030b50710680e82403000d002102c130002c1143e20500c0e069490784d0a00102d4000d44800119010003101c60302d8188c0c0242c03a06103010040300070800e001f40c0c010843c40c00c00c0c15445046424454803141040705441e414001c02c1c000041040300c140e82032a01081e11203015003644200c1d600030a0140805000081000030b01d41d00d50041d21100c64680b141c094003d011001e0142200c250890040115080380d820650518040710840e0321441c0152100b1110010500d5018104285014440041c2e0150f40107008959114188a00f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605771645 1250 605770395 605770397
    0x506030f120306010305091504290c0705060906040c0b031302120a060c020a21050f120103020906010c1211030c0708011e33050907021b09071d0d02090403050403060c 73
    0x18010740c2c14423500c09052401000078141c15840821a00141c800090300081500380340704c5080d5600703194070f01d104680c0c044541500c0c0c0c0d10890011640204020600d1070040f980894414075241c545480102540c000070021901c0a5000383d040c0e001d81c0394406ca0540d450007400c080d040030900d2b803800808940110042c40c1c219806007510400064042d079242412a02000d5400381c4440000300c00c031107901c581082051400700109106d0324209280d5030141c10707a842200c030900c07550b480741700460301d415004101600c1c01c0c00c4007e034600e12901415a035500d000c00c400c207032840c04400e12107091500c41c041c0c1c4040d00d242c1d9a10040030071141002100425000d0441091000754020004082c00480541d0130355811b501d41519a40c0c0e044001c050907000300b001400c0070300e5030714240354060b4480d05050585500c0c1940c00310b10034400d00c0c0c05441d01e8428010743d222959038003c1e00c0c0780c41e10402540c80581d908862208050302c050303a184d80301a442544a036031071590f600d081d4607001d41520704441400c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605772895 1250 605771645 605771653
    0x1216090f0b060723071412070b0f0408010501050402130902160b0118050a020310170c091602010b030d050f09010909020c06040201110a11010f0c061508070f0b0405040506030f12030601030509 84
    0x8098845080007400951b003048034500c1c480a0302c2c515480c00c0c5591503101403120f180000b40350035451400c6015208a400b004002c120603a030724400d000a902c10100403804003003e46006016140ca02e501901c0006030840b11140d40c800030350781e00035406400780c00181480740c80d008012050000ca0042980c011020b4000b5802c508003803541d00c03030303103203241c010542c440d60035140040c00b00004004004034079034001c103071144500388502c0d2003800b00d520342800300055007400005d504030304001811b204e244000e90b4480c0c0c9412461540801e0b143c00c20070090341000341d00b1500160710105400501620801000504080d051038400548035020004902c010f40e003080540c00d001c84c0344400300d01da004000382041c1c000844c90117005c580b1207800d8040107102516002005800400c0e44450900b640d0f0288102c80c5030f0b68640d48043c01000c803c0c82440c0100500b040306102c1e0341455088290051703c01340460f002c02c01e944102e1410001701084101c1021004407c200040d03901d80034054111020002034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605774145 1250 605772895 605772899
    0x1b01060f05042c030c06250806030d2001060f06081b0708070609021002010b0a08012c0c0d03030c0816020307021002100c0206061216090f0b06072307 66
    0x110b01484040c40001c0100224a10f0036800c402050040700c81c200303a038900b030b01c5d40e0b0725101001804100c0350114150700e11580c1442618210f000710344a40c011ba40042c014101414508022103c90030720714103540d4882401d0f5800810a5002d0050402030901c02d1400c0380c01c00d08117400202004001041e40c0700c1d40302d402c030205086400f408201c0e010a03030041501551440203090200c05400c8070344c0029000915506603603626903040d480311030f420307604481078602c01c0c0c2e03212a81c5007030700e40055040740803107a55807248201e04618420300c540c040e050b0041d140e034803140708000f50000700e0a80d402e8002c0b03620b440c42030100540c48071069602c0101020301a070600141c00d0020744e203014043c4001d0140c0e61030000b0a0034507000700036082443c00d076a00248240c03003e03200029210003069545900840c107045071000c49a0000c14072020214250b0040c1c010b075480c201c5060050907212850042c0660303151100026034480c40010b29580d8041ca40c8086244415221520450f54401c1d080010360840e140c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605775395 1250 605774145 605774171
    0x180105030103031b051504080c1b0303090d02030c0901062d090b030a06050316092a05030406061508060f030706050f090406051822050d11031b01060f0504 68
    0x18007250340d0710159480c0c80c02281440d02501d440c0c503061194006d12904d0341004100700469000f0000c5c56040f200765036100301854a102c0c94220800316196041c6c00030700101030b15040c185003100e0b4843c00242100d6503518804c0100321590020703086a030004604d0026404d141102c032500c0b404450720304c808060449131908004018180c58010003600100001c045000c5044d190040c4028000c000d0a4441050000b102400826000e11802011030b003005100c20030f00410b1400740810450035440340e09003117010724088070300d0b070300062003251155660800820b203203284020341014041c480c0c84840c0d1506000081240f82c0ca01030801c0b5100b54030004003449400d034020281c8000301003d4484c25154003070613001038060f0643c0c0d04015040901d0221a42851240c52009400b56811243c9940003508141e008120500580d5029000c1e030320000b80064001c1c4991500301c0106c0686041d2030601140248080c80890344a5280000380c0d1601030501201c840d80200800030402103a042001400c1066 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605776645 1250 605775395 605775407
    0x5120316030e030307050115140603040b06060a050d1a0a0e0405071e050405040501021e070c061d09040b100b090f0f1801060804150501030305032a0d0218010503010303 74
    0x2030000c0800024100d2540035880c20002d4904455219000340002132000078802801d403070510600381d0880480faa54000c509288080700e0059070000314403102c0e40d85a0040c002680d03c041c54903401c01000f0080841c03411100d12918602825282e0410754260000e000c000e02d411503500041245824030090000050b0000b4a176401c039583c405840c40002d90344409004801c883c0c1d130040c0e0708542010108400c00c8019130003014141c0180215882048070840b000c100b03400b4103580205022140b40051100074020700007101517174010b0954042240b400e5001c100394803400d9800b240c40446101c02d0040070524620004041c1500300241800d11090200284a66400900050040043c1c0344150800d49803001d401c00008610000310880d541d46800c002d0250b07800b11420784d0900622821600213100d0b9015250423240c2540d84d00d07085456104a0f04006040c03140c91034801c50000c1c056040180786031014096501e5504070051700d42600c808018040c0100003003180c100001000140300280d0072031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605777895 1250 605776645 605776687
    0xf06040b041a100504090e06090105250c080409020d0203090c03010e0a0308060d171306080f010e0915330109030f1407090209120109021c050c04050f01051203 70
    0x54108422445941c8284c440b48100e0b003000c0c22045c103107024518064030004506007d0001d00d8000c201c299142000c0c01d104035911100c00d882c1d64610100918036030301c20811030942030301482c40070f4039041d5190705690032a0721032040d6024094020041010960b414400b604c01803d00307500034007528510f018000d0b03d4804001e002003e20841e000840c125849003540d01006550080940060b0034407415148a50b4000c036002e00c284482d0a2004503400344121700e0140034040c0319281080507402c01c06c51244a10000700213003031920034546000c0064250409845c0a20314510700c8001103280c0c14140184580b444504080050a034040040540d91119030002207036081904200481c1d10392400400340f9134809080e042034420118080f50740c1d01c40d40d00030b00030504212814400110031402850903100c4c4102d0207540400d54840320060500b01000e07558800d841202981d41c0c07602140002402c5400c2500d488089000c045c0040c8094140f1031003040c00d0b0f02000008508100340b01544e41c002c50318407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605779145 1250 605777895 605777899
    0x30901030f02070b0109091203020414100e130b0103060b070b011203110f030d06090b031c0c0206030c03100f03051207210810060c020303070611070b0f06040b041a 72
    0x103a007207001c200302079070503a8003ca5005000c1101941d480c003201000e0203650f102a1000c003051145081300c03e00a208441c111528039407100c1da0501524100610f002c10510070800340800540520681c1e07484542500362880004000200c2c00c0400000404441d0300350005040841c003000140007043e8054500c6044919600007190710604e94502100c1031000c0c3d0340c180001c0d2145800050b55083e000c0058030741481803080800900741e46607002c10903200050001c80d0140c114403250208070070046464800c00041b0300344104442a03030350118880343c0c402c8800030341c0a00c000c01803240062a078004000100383d858002e04450741140c403400c1d21a540040d40b1009070303000150103401c01c50b402d44240004060200c00c0c40020302c4201014140043c1154081c02c10050200c000c1034240c042c4000c0002240c021f00114102240d6603140001010a0b030064a4003450503c02030002454154200d4441c120f0b0080c0c1c80c035141013100c140015102982e40341840340c0d041c043c2954201c00c100349546452082 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605780395 1250 605779145 605779151
    0x15080309040c1e0804030305070e011e2001090c080a03080a09020d020a081518030f0f1608071104050106270b0a0216080a03020d08180318010e1203090103 68
    0x10700101034500c1c40382c0045803d543d480c1c4040b0754110703039000084a4030640c01b03604e040c4060f9460310002c40390049520109404201200089030300b580e9016205003009040781460201422403e8a4500d29414030000d1540d036910781c0b07030003010840380103150707402801028024520341031180d4001d0074a100042000103480c1d070b40d034801c4003595a01c5100d000c455801030002500720352101082600c0302101501080400d40300f00100c1c01107000c1240180c030b4080210701071414100140441b402030307880541c030100c48460601103107034503c010500c4004028880e0b10501e995501a03e4455150142c04440c00c1c840c0c1c0c034207001001100d030040450b810941c80103070300c1131481c1e4003d60030610040c3c080d00000f620303143c086400d9000a17000030329400469501d2448010300c3d41d55100340c0399180041d200050041e001808840342d0540107070b101a4006603e41c0c074190203100c945010a2840e0003100100c9c0440c0400002c1828a5801c1000741d003002c0c1d0191944604080c0b041d034006c0c1c1e80d1089407451410156 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605781645 1250 605780395 605780411
    0x30506160201060302060d0614180a020d0917120714030a0e030c0a2f0f0603060d120210050601020102030709142e2709110f120a1508030904 62
    0x1c03003907000c0c0014542c01040103486030700702044503000742064003c02108010700c04040c1c2d0580750880760342044040c4000380c205160345100311b50011f900b065903044507842e141c88200000a07000c140d10105001101c01d001e4036000f06464060400c0d2018128109002600c843c0c114217828000440368400800751000c01c0014010003180d01e1849860780c84116802072810b02d0042005000402000030b102003d62017500c7d08a0304024000c0c400e07240d440da8400040640500503040c90b102465120030f0040c0000403054081d150b40d4204040417a800c1c0060308910300501e81003105224840e00600300707100031819440d10a1000d04540c40f02e0017003000390b0391903241c514242e80e02e00746441120b4180b010404446400030728451042d10002c000e10001c00d0007806685034511100d082103081700b45030920032200615011040009001106030b001400c0c0701000b500d90509408002080e00c0c00c0d5885609505240c0084c000080320595400102c1d060202c544c100700b5505e000003a10052502100c00090080c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605782895 1250 605781645 605781647
    0x51507080d0614041a0f0a05100c050601121104200a020f060115200705090c070501050c040803120a1b0807020d0503041e03020a0605181603050616 65
    0x40264000200320032400200302030406410340001e81120088602c6010008000042105a4912a0900200c402120001a41460f00010f50a0044405480000010f4844c00441d100c042c6602021011a003410790180030840708002203401410341d0b1103035078002e0140e55510403011038244062842a5120141c0d841240c01030961120a19004030410340d96001044001e03449413800c003407a60441c000c000000640e050380c3c8240403014052aa20f25481240b4905011a240300503003000d45070f845040c00c0454a5100e050340170380500b0f840301605840d140d0511785a402d460008121418200c0240802c125881d4004196000343c02c00c400b180100c4c3d942d910381080102402c3c0350b1401500140d1b40c0f0075244681181140340101407980c2074940003682d494081d900782c807090b03074018160301e0781c86000e440301e0b0015074030410510b20a1040d520810b1942c1c85e0202521016a000301c0c489a007509040f4102104000d11244524040c1072096840e180d521101d13110180100340c03c0b80440019030312229a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605784145 1250 605782895 605782897
    0x2010509131506140906072406030c030b0603210711091e28090201020c12030408070914040314070506150f01050903061b070f060506150a090515 64
    0x10421031501000140141c0d00100b07800c001c0c510840000c5841c0b2400c3c04240c0a4540403125110000362101c0d140111617611809580c0c680c01c5152094407014036402e10400b00ca0085e40c0003540140f81000300d250035400c00c0c0402201c0545218400c2e4441c0784611341141e181d9080c4480e00d0503540d81c0c01e40318115818220504500c50000e1644070b00706c0d1042000f103008100c09071100601d128040344007a42c6e10040d141c4010380c00989070180c5408110a039140301c80507040f0008181c41841500c003400c3c00762000c074024582c1807031180015080440e09011181c4104000801070407540c0040c01645910411307883c3c414409403000d000c00c060761003480c8207480d5140c212090366070300804a0301c1c145000032900446510b00f8204500c0f500e440b500603902c42d8410015507002d241c008000d07081d036841d00d0303800860101c2c0a410083c0020010300a10001c10103003080d144400e401101d003c41c0c07900d010400c2004001451511013031141050010001d4a07501c60218826100140c40c0d184481d05051010001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605785395 1250 605784145 605784169
    0x41506180302090c0a030b18160504090905100507050a0503060607060912030c02011d06070305180109140d05040b0f0c1e0c030616021f0b0904230105070c02010509 72
    0x50594041c0030560070344c2c0004155200780ba075020400da44038042006681c1042110600c5c030f028503040410070f640582603448032824a80c0c1401c924080e80c9444420985000c15015141c580004141645140341e034010168042c01034680203141810014026216020152403940100030100b034800400920f0341c08070074503036000a00f82c1340314541000c005000e001400da1440041d420704503034540c40132064070151800305401c400f4048540c2ca000c403c500130a130040000d4100c1604239112110103200b84204507000d4003900260343ca107404d6402461510300401c07600020070900300020809000b40c882542c8059482d050001d42e80d1501441252510b42e4410451203840c1140090680103440051000d4441d03000b5403c0d200070750f54150100311540800c6180034056080000e0341c881d8128042d0b85100a0490710000184510703042d40810a140c07401c0340d00f1159210840024482405094040a4250a40c1c0c1c003d00284c50440b900512101200e0070080c1481000b02d44c0c500d05640340310446d08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605786645 1250 605785395 605785399
    0x15190207080904060f090f0612030503092803020f0d020706050a030b0a09270203100c0903050a0606230f1012052424090d1704060e041506180302 64
    0x4c0f494480000c03514202041c0300700c51100345060554403200c0c50f46d00604c0101c1e00380f200030401c29001920140c640d80d00c000d003905028042c2c1c2c5807031460240030024a0740d41100354000481032510364540030b440c110800743e407007031654009841c12060540c0080c64000340d401034a01591a4070005000390701610b980903180780e20192032407000c20740040d03a0f40040c110440103401d403031201142c05800c2c0c000401b9000065010303084003030621402040c60304402c19501c0145440c100507681c03a1a918285201c10f00204c80e46501c680c02044510907501c082c100e035288003c040003038102c070340300002c0a850201045074000c0b9500c061241e0f03510300801003040700c140c0d100070034001481d00040c150300d07041c5000211058071142007100d03145401c0160124503500605942485801d0400f544624580c019032040c582c00388640d881d00000440402d030842100d00104041510303541007a60180c4880380161129004520340380c1411015070b1a4104082200c2450074408001d40080180d1182e244141c3c20180d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605787895 1250 605786645 605786651
    0xd0303020c12030114010e061206040e0703050a060b0a08120d0b060d09110316051e030c031c02070e04150e030d02040e1807080a080307021e0303060315190207080904 73
    0x82c820803510541c10117100c0036030343c062a03a8100400c0001c1c50186a00841c8504c14200000c1c00d10308255104542d013004088c122000713181c2d29912245800c290070011200140c550450001500702644924040d2440310003400780c03c0c440480f048418041c1e09210389000b40c56903c0c46442c0d488400858218010701e4100340001440c2d414103000400720040c98a000e80b0401000580d4403c90095260984100420000310721517000929451b044108507500d6150080040201480d941000b18005900081481c40311050301090301030305002d05640448082c4290104000010314641ca20500441400e0f42c0040c050080310b9426155006001031024814800100400c2d050105212941706403042d4904028103180310000c0c030740391052031044015540c032405e20702e00010b20311800382d54000c645104840012009001060040340d09414848098000100340310041c03e00344034035032104803030350020030803414050b500e4504401290005a4610f42c0854046d040140c1038040761300380c00e0018014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605789145 1250 605787895 605787899
    0x306030f15060f06051908060112021c02120106020c0301020901120c090b1317030406091a1e030a050f040b180f030a030203070f030506030a02061c09110a140d0303020c120301 77
    0x900a0350002c0c2008540310f15070084041b00c0d52040d42454450801039484000c90b00120020b8400780d001404c400303c1048000c901c12100c0c1c152403000c0c0003503800c44034699109500d8003401038180300003000d60a000c0c0c0d0042003d85020707600007240c1c40e00c1c050b440c0f0001038a0340003030404940c1d01c034641c0c02114000c5400180104c4134085114040143c5803021007948442c50071101040e80c9104512030700000c079076040410448182c880904881c40400c12600300e1500c0080a1070616403110a0850007a0b40c10110038818614020b121707865001c600d058058410781465101d0222250000b07041460812681c0020107012000b03000d844003900e4040c003103941722060103c029019420132a20030001920741985640d21a06c82d014090140801130007410100c003040c1c0a1203500d0f4030204054002850180c1c080c1e07243e500510580d40d03414007a5004070340703a070118410020f1500d00356200790500510304500780c1103980c4d103243ca00768656040c100140e854004040c0355084c4000d0007003580d04c209000c400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605790395 1250 605789145 605789147
    0x1d030a020411032d1503070f03080304111e06030903130806070f0f0e01030506011b0606030b0c0c030f13080a08040504060e012105070510030b100306030f15060f06 72
    0x1c1d501520714040031280351000c007483e5a0400134010228940114500c0100b00f07104016851a60000300107070540d80180d84841e840c06400919600c00c130741c60500041080140b01c0181b120114a0a0071540b109005049201c4e0b0460070705c11b0080c0e1841500000085020310030304004444200c0308003002a0b80a580c0c46100c0c41e150b51048801c180440c030a05c821251140c49050200902803964407411307482c0c1039260045005020040c0020f06108181024949114070703a078040070403510884003c601c460951400d1412a9000b500000c0f4495088c000d9490b181c1d4044140c4180342940c86030b03141c4810541e211082c0c4080701354403a100034001c2c1c108800074000761100503c10b951050b2000c1c031245581c0d91180c40b8204003407060000030b091188070300002001c0e03e6034940b001c0c3d005108480e002601c031000580c85807103124100e00442e5584049546a04120001f00100416410304008141c40e680f140d460043c2082d034000d0810503006c1205c03070312030a960b201380b010b00300c1544000c020940b034800c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605791645 1250 605790395 605790397
    0xd15180f06090905011a1f0f0903082704020906040b0904151d0c0301030c0302090723131e0b070516030b0402010318080a0c08041802071509031d030a020411 69
    0x2644106c1004010319000741c0b0f08021001016910f00301d003044090300d40045084030782c800951010010000901c2c1d00002051a0700003910b02410301641c249080403144c00c9107001031500d00300981c0614018001030302d0135620308050310100d42499000da65210884c40010f0000d210205c440407030a90500300104941c1280720790b030582c5903607120704503200f030301c1e48801c90b003c90200340300080142ca80c1000a0006060075400c10340c1181d49420311078100034070264240c00f6840c080030410010880071418024980c9154610002441c40005c0541c250800d2030020f1840c0d060f80c0200450b4440c0094208100300c42048068001a0105080780b25942c0f689001030742d0f140255000e900107030420600c01c01200e238060303010030030315440341205180241e8a60300740c855200604040d107000c00c051100188000c2480d102e000714003489100142c0d10380c1246030040c0c5048070030b08040d240720702d000c2652000981241340030605540d0048180403141d5584002841c08840d840001e401c00d04103c4034461400b2a80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605792895 1250 605791645 605791661
    0x603110a12050703110418060b0f0d0b010e0709091109151c0c0e030106080309010809030307021b0a051003060807080a0b040210030902150d15180f0609090501 70
    0x12960a401581c5020410218020440240c290f811080c0d0420002d0341280b80505100d102420105007000c0340205545c04150f80c10b01901c040d40ca40340c007456a4509800f410003402d4045450130010800ca456958103046c0500906501003c4107010401d0b580c0510408401000c203042c0612865214402c15859904449280c5000e01000d64150110404150681d0101030a0402e000c80700c591a01a01018151012405003444240000b43d6441c0c2c070700380681801340012500450b902c0d074a62000401030a40144007105e1608240144034203103030b01180f094181e40444000d0714040c092100080c001c04002e61240b90301100c4140440341c1c15403d42c00902c100c400c41419035006958840ca8a80c031200300c1180104807504405c00240186400300c040007030001145030005d0809003c3c0c1c0800c132156600d183c2c05003140e00100b180c410801850141317105240e00d091500007036514001c501c0c40c02c1d140e424031000c90b103502e0329a60801c88115a01c84c00c01070460140c188094140d5080c0540202010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605794145 1250 605792895 605792899
    0xc010b030606100507030e210703140a1a0603011b080412020304050d03080949050306010f0320120c12010e040609200108070c03050315030a06060311 66
    0x40400200980340401006001c0a804d45500780750020a650807502020041c5c03206520a00c0c084124210010015103084110074090040c8000740c00e60601ca00c0c4004010b0554040c1da02c00e08502e40002d42c441203030f14000c1c180241c06015900d0385d0380040c0c09050103281d041c0e4104520081446060361040304507003d24043c8513a068000040c007003ca80381e12a6000302c03500b00001d40760b140002481011103c0c0e000c000ca100340c13421184d04c10550740b422541c40840c80982181e021040e03503058160034001c4100d0b190001040e90041408402230060b0000411050510818031003104080c0d01980010340b2a428403c0b51401c1c4c03180044200751b583d08000390862894401c8130000342d403084010202c98040d0120000307011160310b402240c80c1204001081240c0713954944144600150819030b00b200d01c1c504e0410240320440403480010844203000b01282d0820600c0318004000c42c0d0003600320313034001d50640000910b4007052004249494004000207201078a400400020700c1484041000c3d04502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605795395 1250 605794145 605794153
    0x1127030d08070f020106030803060613121b3501090506040510061e150c081c1404170318030f070c0e041a060d081909090c0c0b0601140c010b03 63
    0x100004a00b06c50190100414481040000c070714035142c05005440e0010380c40300d0400246031100b558a1132a414207804482c005e81030206826005808100c000c041c1221900120040304c1e13030502800e4280380f49400803148900c0001002150b407084d005901041c2d046800c51b4810308003482c000750342d01a18503075443ca5501d041c1c4042040d04250b11582036100902042c0422541007040d0b500408450882c82c2c800e001e5008003075000605c803040900080558144070a03035140710340c4080001d8031031140020a4681d02182000000b03090081170028280c5030000300358581c0d0317550b560104c4009000441d9909031002003002e101e40f201c65002029941e00c2010b550302c0c4959141c1c008404248191401410036000d1400c4800302980b41c00c24a0f40500e0041403010380d18074039207941d112640680c4200e05031208141c0c00040f42c540202d405070040c45800b40800001c95062070080010556000c001c1203203c070301c40400e1780d40e88540c40042107011110000c40da02e440c0d803007400e402032420b100514040d002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605796645 1250 605795395 605795417
    0xb07110d24060303021c020a0b09010b010314060904170d06030b04151103010e0a020d02030106020309030f19080c0102040306050f01060e03030415030b010201090624091127030d0807 80
    0x2516000d01c1040f00d50540061100f0140d02e20881030010b850349001c421841482070790070102e0307400340b102030045013100d000199042c43d410004040e50340302c0382c0d02f4401862443c14044035450311891654015009401c03003610005070010044144682080c503518141420802700c02d0111a4451301e00651041d100c207110074400c80c1164013512a02101c02100500900c0104007240c0c0010701994400b004440040c0390642e00b10000703040340c000b038100000681c40410380c0c41c0070382000c0002c444003141000c000c00020f03024541c088230441c0383d107200400c51540420307030405018094050700c0c00755034800350903c1240307800d00a41507004400d100c0d0000182c0f1441000d8250f04001c8129003d03030711510304d901d08528020b03200781d014110700010581103660700c0c6001c401290390b5105c1c65024a405404a0f0411111072019000e1491180c101040603450f00399442078a98501e0201d40c0038480c42481c403030f07903042902409071041ca4144820b5416009028100c910303260b0002e0414418441030f111258140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605797895 1250 605796645 605796713
    0x909010c030b04110307080a0b0d03080a14010b03070e060403151e0608120705150901051906050f15040e09070608180604140c130e010b0d0b010b07110d 67
    0x16108002c0f404c1c07004000c10100342180c2c0300d000d03920307445a0748103404a455010f82c0045603006c0301d048020f40015075458280700b0b140740369019034a640729920007110065410800085e0040c8405841003007070203c05030b030417101600c482c019030b00216008001100855596a4803202034101c44040c0702c0040030044212043c00c00c94420313401601c0d15031000f8491024044400d070995404050262400e20540380c00c141082c454003200c03840350092000119a03400c100c02c01114a8032100007920540d42040c9043c0483e44865807a1200341100b120305401070ba5000024548501c641d400c0300c1001d40b60142003001ca480c001582c0c0e400c41d20b0380d54a03505c3c0340d541d030b4002101403d000c401c6040c02d904040041000715850f800711900220100041ea6107080310000002e0304005c8280c45100010b071210307404502c0c40c6007845000312644083e66007602c59100e5607221400e40c2414014060701b800086003010501140c1d10420b00c040c00c1c007401100446281d82800c0d02c1c210714540c4190181a81c08920031214 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605799145 1250 605797895 605797901
    0x406031509140f0d0c06090803041a01050312030c0703030e030403050106052718120c06060937020702061c06060518010509060d05070c050c010903170901030b0909010c030b04 77
    0x300840c000e058804d44560085030304200080e020f58040b512a04e031a404074500c1c0c0d00841c010340c45091040c2608031048c1d0101d0b01014141d2041c0d01c039403c51100c00c0c1c00d422950701120b600150f5070702450345d20501460140c0c014100c0c42100d0b141880042800f00420005600040c04d40701c00712142c0c01e15030781e034090031000079a4aa548200540511010070300100000e81e03400c04030b18542c416510a243e10318052041d5803c0848104500e51014082c8401400c110b042282c2010341c0910300c0030b2040080b180941c0034410500314441c05860350100d87d00705d40b40c03030703058425043c4d000f0300f901e583e02e040d10380c0c034201c0d0300c040c08000d20154900b100000d002030003501152603980e080d291005031405414015282c40d00302000103034100e113080105003a0030380385220700e81c815422a200d6045142d5541016071a140c039804009040c03000b803101c2480413400b61840900050b030448a2a642d404d04240101d02074030340c403400715801c40b0061040c441d06481c1074001100400301c03950b0802076040058204026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605800395 1250 605799145 605799163
    0xb070501110406050a1206350c0f0622060f030c080405210f030a1b1d040c0203070b01151b0b040201030203040215030a1d0c0307050f040603150914 65
    0x842e00c1002a85417481c0141441c1c43c407420410b500169480d40c0d4960880740303d005000ca00c000800324504560581b04907a20b28081c000390b10010b01201d40309002040c450381200c0300a07885650046401c1c08884020389041d4160104c040d0045445542d81101400c10307903045000d4400700342807108507200b680c0704508151049803c84001c004d03d43c84400706480321690511140010032040103100c1c040350a0303000031406450302d42c0c800a012038501000c005900d4251544400300310a000c4100c13407140e003001d00126800000c60300021140380c105000e901e584600d44000b407103144010b00004000d910072100010301c0c1c4441d1242d0101c0c0104500c0d1004400b4031520051044114074046005544603070701441c0d0042c8098840088802a0012014190402c032054500c890719550b4003516921494420b00d03002e0841c02c010f060f881048400039845040a0044038012409800c0e40d588030b980c0c64024100854209661000340c030b03404481100600204802a954003803c540340d10300b80340000502c500c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605801645 1250 605800395 605800397
    0xb010804030804060518071e0e070c02131b120b01050a090e060604031407090c080f0a0b060f0705061f060f050307020106030618020f0f010207030807020a030c0b070501110406 77
    0x80c0b603455a0300c03240105406000742180e00300070102e0244c0d000080280201801c504190030000d4000300d6148c84540400d904039100405d8a0014003400c0c81e0012480751495504450303603000f9600c400b14100040120018107d44210044003803085541c002c1d07410340c5000075980041c081d100342200150303120b2041d20141d000141c514802003024040700c1d0704841c0c02c02c070000e04561801c3d0b0ba90703e6040b0221104d03207104500780c000c0f040410058410344643c0086090701d0910840c04e1600da030307100ca19050021300401f03c868440e64034011719070b28002110902080c0c07075a00c035110056410004d6596404070b80031180d05601d45055200d4121100003d0216001d903514544072080894003140c0741e030005071940d01550348440001c4001884ca02480700f54001c54103d20301c00031807500410280c6000394544070f0140f1300700024910b50b6640424000300f45e07500300c6000766982c000707407010403088807459001412401c01c880001c24034480c050024001c1500a200038800c0688000b448182d600c07e5102d050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605802895 1250 605801645 605801657
    0xc0d060b130c051c090503122406040302040c020a080c0f011802031e0a0821100602070b090a080a060e1b2b0501050a0b030111030603070501030b0a15020604060b01080403 75
    0xd00008410300d00c14280007442200814201460346e140344c999000309a140c0559200d460400612210807482840c048881c0c84903866041801d030003142c56480b660001a01450329004000a190b000704101d0500304e40c042c1d8900d540e0050031602944401200d94142050f500700190000065000400386c8a520380080c007821655a001c0303418620318030102500d10042c065940e405011a02041c00342c158649541d10000207002c2c000c0b103c0003296401044d080501c48034040520020b54001044e0307050703490000881d40c1d80c60074940043e804c46141d41c06051035124042c2a507003048420342100328400c185004640c031711594044850440001c1d9442150040c4890501000c41511650450306408035651440502c80d00d50712114207503070045407030641061711207038462020300b001d1150051104080c0e02c220b045061039400213490761a507118103810507403100e81c45029a5a03c1103658003c003c454440010101c032090081d480d41022141554040e15020182d003c41d4010001e161040d84c1c103903102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605804145 1250 605802895 605802907
    0x7030b120604110d140a0c051c0c06050a021911100903082505100914011104091104050618011829190c062007030c03020c0d060b130c05 60
    0x102c04d16030101501030310b9448290b17812a203c41418880d040446000c1c1c2c0d200a0712500344020301004800c1d1003017481c0d250003d0348120010036046d022400c181c0d00c42e80b074100d668640f02070b4101e240192000751240140e1101c0e0801c0104401c4500c06100d020042d41c0c40781c40c100031b442080e14802214880606081010041c459203071000d50724014841860304100c039080f61581c0c50700e41c80d003079007402c5120005950301e42e20b1040c402810b08409416514000a102d0030350381c8840105240100d21807800c215854204580190240105641c05840007070a59500d03051059241100f20440c1d008582c08204174480d503211400d4018403000a840300000c5e1151000201d440544205500303818003202d440080c0100e41502040b000025200d0002e661850407c5d20603050480454580303869030103402e8103500700261080c0e095400c3d140383c00e4041c1012490681c10381400c2c4c2c10209a0340203582d0028521001804000c01940551088881a1010203c070088103da4030300315004440a000070231414009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605805395 1250 605804145 605804149
    0x15050a0305190e060a1116140f250f030b061011010204090605090a0204080c1903051c0e03120324040903020a26030117031207030b12060411 62
    0x4041c0c0c012001c82c81007840792014902200488220001181e1560400024090b00ba0120b00911410584140e43c3c240351044040c14807036007a403001c01c0207005081c1030b240140607100603c58500c0c6030700c954055482c00e0210b152600003091800b560000101c14000c0d001c29400380c5c0d032440300c0c01d695015500075a65200c0c4020441d20302e240110040030001400744000c0052000e00180c401080c01320000301c0c4550034181003062a000045c00c0391809072046c4020404400300040c443c42d1060300341e0703c3d404003252034130702c12800003016000545148520190b08a180140d00210007003000c15945074030300406002e0406440340b5800703012501030324082c0081404164400c48194080c80d04420f130011818045022406483d945075040e8096003010000d5800e20130030b00c00d000303406403a5400a260002034980000f90070701040c010b08090300e52500844070444003c004a84030b01304480c0c8211081d1420100043c00380c80610701041c01401c0c0ea0f0a4054000c034001002401203900442c040315003214502 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605806645 1250 605805395 605805401
    0x30105100806060a1d030f0756040618060512060f0301090f0b0a0b090c0712052a120406080406020f0421120c030e0f1f051315050a03 59
    0x17000681d0070b001c8404103246a904109180301d078500f05028080051030946052140e609a035110242e441c0300c42c04400c000600c000e10581e10b66510b0080032014002444100d8900360b400c2d000341d605a10000b0301290035600080303940c40f141089408000081c1c2c450400b2a041d0052051950030101060085840c601d880e5082d04148940900009520015500c43c541039001e8404103582c2d05070040700344503c24400f03010f07003030110728213940000c002e04100c00e040348180b044203030103402002c46141d403142c1e1622440c1200c3e60381c0100a000300c9201010300300c24000410315002c0360128400c09074004149051503040d541103031b4260319201c586650f95100c0c42c02a502071070400076000b00030000480c4001070440301c810340310381881e51030328103001901c1c140003001609280b1000b409010320200c00040d5002940b040e64050607178a0005800d102000308000d1101c40c00c44001030301d081f00c890940030b54448007510641c015919050f4841d03a4441c2c0010200c00351404560000e41c0811185e000140a50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605807895 1250 605806645 605806667
    0xc12040510180f170f04030c0509150105040b03070309021509040c0f090e04020a09110a02070812040621020c0307060605090f06210712201f021908030105100806060a 73
    0x20130150304d001601d6140a6455000d03800494103070240c1c030002d012a080420302d0360f42c8076611134180a14114040c0010b000c0e809144580c01a0500020010390781502c0f0742c01141e1b030107501400211242d15403407100c83c40e40d00403102c4a80154500b903c4520803070b10598540c544034150f0380b41c03501c0c5a41840010960418014010f0307811200745080010042c1d6940300703109282c007028581d55150704072810300074100101540038503000c3e4042d0b00382500d1003600d40e0884044510f40d0408600c1e080301c1030400603c840340b07480e074180154404501030158803000b0000b485c1440c0f24900c100061a1158100035240d60151111060a07000200046007030600a00742c0071400700445039000e03d01004000c00b4540705990b0407200082840300c0240f4100a4a904482c0c51000700c480c440c1d12002245000c600c071892880e00c40c5007504a04250f0b500c800e4001d2013a2486030845180c4075180d15140d007002680d42c0d10a1141500420000070382646091059150f81d0240e04001d050710b142c00c249c1ca4044802003101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605809145 1250 605807895 605807933
    0x2100f0329010309030512070f09090501030519030e040c08071808060403051b0111090114090d0305090f060f070506060618040c090e09060403120e10050c12040510180f 74
    0x10000049801507c0c680107108100c250344013a01480c002c500280758240c0c1d94131400c00d4504000c010701c0020300119100048803018000003041001c20300f8211007041d40303442c2da01d0300039140400150780c250707102d64040c2c8503001a45501c0c0e03210806030a8540c0000480c403071100c854012001240c0000d104000801180e1000b5000ca032100030400c0c15142111b2207035209804030080052071a0195070803201c08a0326032103103c0614146007a0790003103120070085d511300504005000841807c0c82d9104810598802009410152100c0740c500242e06a980012025075092199030001801880c200f403c462211071424090270782860000c6c2070001820410f1040010310030038810102e208010b80c45840d1040102200524103070170300307007005460424840781ea900305508201c41400a1030300090641c500b030101030000039980c4d896412403981c0f4090030b8901103480c0c1c2c13084207000c188203000906c0c0410301d420a03010000c1107900c00d040c40c0c1c00c0c0350500008006031102c03004000810070b49d8040003113080c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605810395 1250 605809145 605809147
    0x2070303080a05150919050f01060e1005220f08060112140c040507021b010315050d150905070311010e0f04020703030e010c020a1a0105010c140a02100f03290103090305 74
    0x200400104103100407100c2c0d2104066070110106d0600040c082c46030090b42d6070522500c1d03035050040003400d180c45410058020040e00c86441d201c2842401218081c29010402144400f40150160802c28591046400322820210302080040e40442c102d412241d16640000c03041c0c0301a40c1e9101c0790f5801d40c86070072290048000c503500030f44542c01500e2142100b83d0103031400c1081101424480b50040ca003581c1010300e8000c803c0355031a8820980801d83c0c8086441c42c401c0c207401d00c2c002d00c190586a800042e02d505045105040000020b114416644982006d0031240e4004c0300440740c5404400d80316510259160391318605040642c000d00700c4902928000c984208120141404d40d840c1401450059000e15860424020000c100d608498000d8000c085654545070008101c8402000d010713000300d51078080b1a281040c10040c4010850b4080e10a221070000d40c03c001d803d810b58800d007600400e0400c0d60184c80c24591880c0d4400340c00c400d40b9040103182c05d02004400070401c2260880501c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605811645 1250 605810395 605810431
    0xd0c05160e0415090308010501050d02071e02010206150a0303051b010c120b0d080306010305061906020304260a150603080f09030f0307080405040c270501020d02070303080a05 77
    0x4921003890024002004a0460600709490404024405050303000b101070301d049a21400290b0125010341150000d103010f07610358580b04a40d400a1080300340003440c2da800402c50368010075448101800282c000d8007035602550301e10b0002403100d19403c0403103074021b2046030140b0009000d8030290141280900c054081c5041e480c100034210394036500c08801084444000ca01415198060389603140015119129100c2240d5510901800081d0107903052540fa03800003449031b1511070143c0c80c0220795030803000d03001d80c2e128000b17900d0ba4850702945e4000904a401210000e450b803580068802c049401000d4140c0b031500c444601c80e086101113030038140c8070700d40000400d16001c0500204940030740d2403565868003004041c6070002c0081403400c1a0014840030001ca02c40200b03940032180181c0f030105490340108000c0b40c42e455440b030f010042c60088054030311605000c85905096400a07021180060842d800c140c1c1c1e1082c1c1440000d0000702071100003004100c10f50410340d0040142100860004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605812895 1250 605811645 605811673
    0x3070608011e0b1c0f0b0102060c030a09080a03091a07270506180414190e100e0f06060f0d031b0204060602061605040e2716081006080d0c05 62
    0x68800a030142113021800c84e2031501010034861108801c0c21514108966060440040e44400004080349045040400002c06444a9400c2051031079401a03035141e030b036000340401030010f0031040001d0364003407005501e20742c0340056421407500070032842c1c443c404201d258110366000e54102d04000540c003885864006401d48a00003c0c040020490414004c0f540c4500e00307000480d14a107143c407880300200c805000a008941244140c85400ca0101055456140b008030345001d500e0302c00c44840c5840c1c6149814900070105680b000315071303200d081e510726448140401c19800d000d0b0003c554042c8038a01c0350300c0001d01513019410704406e008817401081009030001030440315141d102c8009a084141003082070680c941d10b011a501c22170902c6400c250500c41c0003035903180c0c020000819441d45403400e001e0b04846207102c01500030040701b204d0404106c5810740d03041c1d04072449426414490300001c070031941c0a5020704411750742c2c02001800310750381d0014100c810311a0454240c806004101c8100600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605814145 1250 605812895 605812897
    0x9040b030601270b060a050d0b0a060815010903030f0c1b0e040b01080f0a0204091a010f081023041416052e0f0311072003070608011e0b 60
    0x1d101443c00c0102041d940c0c00d48800c14081544098001c40ca0078404044503500e507001e4411001b0940341094440c030748100030800030450401650782c002440040040ca07681c4c0555002d101d103a40d250407031404030460b0015280481d0a00009021032003160511012500c0354174900d40550085000c804105006100029140c10380c2e042203840c8048801000b0030302513444402401802200000c1c8000c500104a2644400000d00020300c501d03210501c400074842181280d51400020010401d9a541d59040c9080e109025100301c04060050700517040400e515807256140a002c69501c8813269001400708102c500380052085402590f10030700c2c001c502408012038440007981d54444a9076a04260810015a03403030f800311654181da44d41c03014045030707404880c5d8003038840d035051020b1010708003001074001d014281e1032690100f0012626405110080c40540c850070651f100490141c0b81600502d603d8a0aa004074000700e08582d004001405001096500d90180e0481c1c2945154840320b466280d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605815395 1250 605814145 605814149
    0xe0603150a090317160507170a02010903030b0301060506181c08070b060a06020319050c0d021005010603060e0c0702030c060a11100c1d0d0b0c031506040b0f09040b030601 75
    0x150580c0d40d80244109a0010202e00302201007640711484d070310b001c9a640d03540c581911031040400001090400412141622200c0d102c1346003901141c41c0c1c401e120000303008008030703807041d00000e007400f5000c1c00b24201881080f003500c0000d8612450040001d0791110f00d4200313008540c2d080000204c4914000401c1030070194490b00c1881c2840e6605d10034104140b400c41c018103040d109250001e130810156800004032585d101d26115000584000c1000c1603030b49014011741090207019081035020825400f00300c400311501110020070450742c07103001c114215841d500401c101c1c50311150210704106036101c090680184014221240c0b0340780c03440890b8180d041144d2000c082109950500c008060500c5000c100e8100c44804200b0000340000007441541c08202810800c400c10b48042101d8036080004601c80d0780001c503aa8140c00c2c00390300e44080380e004840201c2c1030301014002c2c540500d060303011a070888560074419401c00c103075000c001040707510081d078080c0d001c0e64800880c825518240f1113580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605816645 1250 605815395 605815411
    0xf0f0521060c0d06050f060a03051008060118061202010906051c02040b0d0f0b13090213091209060f0e010e06160c1a190807020f0708010b0117100e060315 68
    0x626188003101c540f043c0d51032508138500c6080340c0d004560782d50b160707c0c040d9200200175144c0403030f00391601030110b113180700d0070f0b04042d059008140020914504c11440280d450702a10000c010385655844150700d070a807207040080c0000c600c12820000c152254000c0c04405a0302940521004181e152100c00c85e40180c0c09120120780c080382a80700542c50f4814a0201001a10280610300c84100020211609812003695a07551056240155180da42d14440401d00c030f104100102040b90400d18100602201180009064203102080c40340c4100c050b101d41203220f4a5582d5440541d40055400068480307015070000418442c1c028089108034010fa036180c0680081d101850030900c1603456254003180490450360104106000783e1252109901c2c081c2d40d92901003d140c8070a602241401c4200c202c00640c0d100b15040861509410740c402d83d10342d40262985030341401c51900f0a045080119144100c000c400b42041008450003480320381e0001d001401c0e02c640326016810301078200802d4500701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605817895 1250 605816645 605816647
    0x30721090308070309020a0504020a20030301080c030a03080c0a2f1e0c060306010c0b0412081303021906020d0e06010e01120f140a121101060f0f0521060c 68
    0x2001d268001c0d0003150480724038503041c45900d8041e0049140c0c03452900c00c4034000d6a0001c0c03203080d00c5114041560310390124071034802e800f0700740c0c520155030f0b90001c1c050610103000342d07244c580003490300040240c1072a5054550142554480f0a0034000c1e4002041010600c18810a001640150440411520708425800201d00d0034058180d41c070704061210074a94030346407400d00c14151107001a10544003001140c250396240d44442c01224681c06901000f00000c0c4500d0600c01008014904003031140e40c80c0d61002e03240e950701c40301020312001c481009070150b0040400900015400042c0c1c5035a680505d40152400e250728203254219000110600401c3d0400300051100005480580740100000c0c0b100841d14803080d03c420000000741c0c8001080d02e00102d501c208a02000d00c0389001c00c5400002c01091800314a501400c440c5142c01010065440c140001c00c03207050281c150740a580000d500f00366120300340024001d400c00d254130906044568510041c1320174504101c1c4500c9204080c00742 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605819145 1250 605817895 605817911
    0xa0e0106051c060e06011805041e24180f0c0b0c0709050a020408030a12060f27140612030417030c1e03070213020c0706030e0f07030215030721 63
    0x71000329142030b00d0403d41c50b00100c004000e564410300000c3c1d04e0040707e490000c0c580c0c40390700d000510001140400700e84d044560241b03009129244450111100c8194000d80801c070041705094100c90b081070b801030310740318200c1d0b10202241c0304e040d0801e141c600c03a665802209440c0d055607421034002d40c010180a41c8004414040c0000c980140c0b0380010b0903000030760606007001c16030b507160300640c0840c0042001c01180300008000603009078004281078544011110389508850456400c000d20f0a000003201c107045a0005400b40300c2e0110703c88051090118076200c1e002005164006c1d001c0c9090b81d07100c01e00c0003103600000000e84040010301c00c401182e8075402c1000c6103082020303011501083c0114550713607490400000c0101d07580581e0444400c0c07460781d90280c240c1300900555840e901c1e00d105180010801c5501544094140c0055038200d445490301c0e10b10150b036400b01800002e410100f540d1403161145106030180d908400241000c0b031b42d2161030140e00c0907440e0000302d41c80210f80c0f16000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 605820395 1250 605819145 605819153
    0x705120405100b0906060d0e10020a120506011e030b120601120309060f08010501080705070b150405060409030207050409141b090c09091501022821080a0e0106051c 72
    0x2542418880070388040801c5d2030031701c00150311409030340281d181d080e440e4034101d0f010031802c3c08a41d01000c44124119212000d4403401031120b060b110b0498051858900461059801180c00c15042071080a450441c6124520228094504680e40e650050400e0b60f550100940c2030001e00e01800046a20b2080c200c5241801840080c1d264010780a20400c54a0044100d60010076a41510801c0c28080840c0d25410400c8821303125090000d0002c088a109000040c010701d0190414020300b00d4003030115845d04003c01c0112100c882d03000b0b016900501003081079080903000050428015085a0240178061252074140385401c0f00d0001c807014540e0444170b10746020b500381c54000c0280b08019040810400c003150002071302508215521100020102ca9a8400c00900c1c111303d40e02d004044100d00000c010345101000d8900480e4464030754102e0708080310b1070a1600340641c06683c1d4865072a141c95100b038006000811360800603540703030b03100410b0f943c0b212004c0d85d00020740c0010710070044071a428 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605821645 1250 605820395 605820401
    0x30e0f040e0f07060c080304120905121e0304080a0b040c120302070602011506081816080f100b030309090903070206071217010e010b0f0d060b07030f0c030503040605070512040510 79
    0x24000388005d203042c0e003000c10050425650302913401001221582d04008003581c00142c50f900040c4d000211413091030b081c4030041114441410116007100003603421400080e01d078003a60240c2c51056100030402d1021039079211709650814020700084c52110307220340c1008c0b80002c414100303401682c040c007000c104250707091049510364480c2c0c0c028002000e00300b081c000e00d5444081d09100d1072048010f9480c0d030940e07051100d921202e29000d100007100e55a150501d44070501d20040101900030310a821500003000d00980b80ba40400601552a01400c00104008440003500702085444284070450058540c20001c00c81036025844000300d804d000c18000b0450b204140560809504100040103806000f10407503040d61103100d40306e0b8440500309039a80030343c0507240304032031740c2c82c20500c0c00510200070034018900c0c0b50003541d80c00d8407686041402c5d00d507003149100c01000101c04000190100303046910068200805240113894064038203020b01d40d0b80343c00c2c0c3c1c0c05da400d500b1032100030000901c144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 605822895 1250 605821645 605821649
    0x8010903120b090406330609060801030809060f04030c08010f0e010b0907030b13090b01060311040608041101090810150f030807021003060e0703061503020f07030e0f040e0f07 77
    0x51418000703100d0390340100302c180c0d0000d440141846c4d00d6101842c1d01c505106420044201d441d2070800c10030a4195004512540030f10802c0041480d845010480b98801c40d4841e058903040030b80e0a290040b08002e008243c1e105041040710810300388000f200080074040410024031007a8004200501c010998001700c80c210707112150203070f14206404c01d19480300d0a10a03403103c8207060004c0c0c0701400201003015072441c01990007000c0c0c42e00140504106088840034180c44050360100841d442d20807a8141b0751241e0302420b408100c20b000020001407843d894076001620600d0400c101650b00c0e040780b4907100b1b03140d00f2035131306907101c1034164000c04801c0d92880c01462810b001c29131180c81c40d10f444102e48103c500103800707900c1c1c91803018006802074001000070000c183c140d500901d042c000042c01004d45000b004078501e082401d0b00d0310144203000b5a202440403152103403800c601560107503503030001071620503089a0000e0f91f445107a52244140c0c9810300b01d160150003003201800940d41003240079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 605824145 1250 605822895 605822927
    0x406031401090b10030c140c031c2a050d06121101020c10030e01150e0406060504050601140307020705030d05070203060c07030c0f0501200702030d0c030f030c050c030408010903 78
    0x1282c503042083e81d1345140c01d81c0301c01ca142400100440400c604481c04540f0340340d140401d220004e00c440340b178940000107008551780d041c00760711461000d0000c241680c00a800c0341c0700c800c19241c810784c4480500c41031035000913940e01f0035628000741d03070008005481c3c00390300216403000e00038410410700507070311078040c41c1074000d10203800300c8107032180040e1104502c08140010150b0f5064081c0d1303280c4d000d5000700300040001200b22142d5540c0e489480d1403d4048070110b03051410064001480c0c01e05001d0a409184141c40e0550800e403002c80c6100940c02c010102002c61040c0100012036403428044080e40c90294ae4402e66141c00a0052500c2c005015200c2c0500070750070403014000c01d03404590105810740c070082541e03140d41d080c28114090a80d07070161008a020b4945400050008503006000790b520035015038245c81000c80b0300340c404404201000d000f0880303400c440d0301402e01c0796101805001030b5052160900d40f6a11001e8556001604010b04581d5074444001c14143c0001040400b0024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 605825395 1250 605824145 605824151
    0x2030d0513050c040c1e0e1e1c03020c010c031209120212090616171219050601080f1b0f0406020f07060c030c15090c03020901050f0a15090b040603140109 68
    0x652001000c410f40b1400d5440081b2210715a5404240b02c3c10b018202500002c6c1001d41c02120214214440544403101900c0380e42c444202032901c2e00c3d248010300c030264040e00a001d107084000019540d03000d505d101182001503800c10701030304003202c0c070504a0160240c0800214901c0384130000c0d1406071200d80c8800307000802e200580700c070f680b1441100c0010b55121042e510007402850483c0c5500f9100c0350650000e06d000c5002e03032103030320890b503d02d01c00e1140700c540c1001142200000422100c080d500d00c0d0006590b0300018844450182c5c010b5003041c445008420408243e01a41d151900505a0520604c000181c2000040c6e0304103c0080d148006c08050022585050000381c00140480801030034059031150040034090000003c0040710200f40042c0a4504140740c941a8409140401c80c0b0400020707002081c11300f4007880100002c80c01a0115800300d051910719841d00781418101001c11044540201c0c140b20000c1c05400180210789022540105403d05808040c030160445101070345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 605826645 1250 605825395 605825411
    0x4110111070b0a03290109090b0105090d0c09090311010c09080312070e040603141b010e04050a061203092301050409020c0f012417150702030d0513050c04 68
    0x19020400324219224401c0e05a42c0d0b01160000f80d020700b01141c9414006841d01100028030840145c200000600981c0c0d02603010b500d80c01404100c80c00c00ca010381c000340c0148000d49081c18192410810a800b0300d40d001c0e600e0b983c0701c06003026280c0c5d004c0224001640c00c200c07030031211024002e82c2c80c000902e04000f0451030401202c1956801100001511144c0c401d01050b2528040c01a0019000700600140504c036140e05008504a54809141c00c0612030b91100f402144007010400d00082016590710440904500c1000003800d00500030401f1580d5403074001074100382e25900e030111170344662503035003007076280010300328210204410480c000a511a1404c401d81e030310004940644244000050304e803140400881e09d05001200c040318151310300301c1031545c1c541c0d020588004149810b412101002d807034074003542d003400954103044015070105900e080c0c03050030041e001c1da0001a92040b20300340481c501509040c3d41003030701c046002d006802c0b40075050080c1400b6821000e101503c0600020b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 605827895 1250 605826645 605826677
    0x110403020f06130e01120b090f07050f03071d06150301150f02011803090f0b19030e032b06050102031306030507120218010305010f120219080a030305041101 69
    0x401ca007100d0a1254034005119030a07440c1e00707400310015207054221301582d50386502d603080441325100c07000da40c485070900014820480024194481c0c50800024044651030302c001d0008034144122915490300500c2c0d004a101086401040c1d03020109107400e581c80d013002c2050040901141480b0003943c50200014091501c1c0c00391100c80303041032450270048000c402d10049004100104105800c450341800101c14141c4c4410300109460481740c214610541da0361700840980f06082c1640038188502441c1034900703000c0c1d4000c6c8812079028082e0382ca0004014080c600c1007441d07000c2070074400300700744280541814a2040700040d240a0001f5442c0030340141c001e21550f0840c0c0300d01010035845000080450740f081c0b170b92104904021005545030031040401d00d52221011003107d00180c644000000c0703551042420108031584001158042c030030a800784404140380000c108407041902c0000641c2001c100040b0710300038000d60303001a041c20540381101c6207079802c504040c10030803055188020a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 605829145 1250 605827895 605827909
    0x8030c011b0c05070e041524060f0212070501020f07060212010605251e03081815010b09061c0b210304060507050c040e0f07151d010e0301020f0d11040302 68
    0x5603c070800d81003140d907101e1800d080002807404e4120070081c1003400d0540f607030101891041d802c03440c488a104230035440c3d50307003120785001d00b03a0040d0060f80b084074030852882805000b050003902840001d49841100500c0c000036910070b900460308280e000a900803214045035806000d03002c1303490000d28102c404a030b40072070001041e00c0b091076503010522803420088601e07003400355503040740030020426105041c06081558120340c0c1a5403a0703110b15046400b0320001c12030440ca5980043c1c1e0318026401d16409070380b55000807107000e802510400900341d074030811a072107051201d0f0040d804545584484144500e03030326240006420141c00614605421801101380d50944000c0d180c11500d880746420814505a206840541c00030b1504903400365444011502120f801c00716005c880c01142e03034201c00c09514001d20514400188070402d100502201d4050718034150340b0500d484000d0030144d81c0002d003280d1020740a0005aa0000303038a50700c010321402104110b184440010b03040620316000b284807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 605830395 1250 605829145 605829149
    0x207020d050610031a37050c04030506090706080f070c020306040b01172a03034602030403021005070c060206070e0a0302130b150403050d11030a090312020708030c011b0c0507 77
    0x401d520092420040065540450b40960071b8030400707100c141021084028180e01c41d0000342c41038043c90303000a11b1950005080c01c100c0385e160f030300c0c240543e480d20f01c00f0805800140142e000c20610f41d034900003591382082014056401003203454007652510382d01c0046411201c040402da500040c002000306c48c440010743c40c0700310f00140f4041d6044d040340001b0b400e501c5600056484440700d0314410300b880300054640400182c0c84034040d01e610400f14100700d030300b0038909400710050388100000c0c001420071a0100004002d82e00f4203a00700285959140c001c440b20b43c1081c00141d0002c02080410b9600203154050300f82e05640090406003550080354881c05000032030907141d40c491100c04c0c02d03a120901042241a074118000d030b2a66140d19200740c9031000f040609000032609800c61101001c044215401300c007454450907041c618654941d03078140e802700c02042c03d40c00780030000103081e8420300040411402000c000034511480c801ca1942030640701001c6802c11603540450000509e001a880301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 605831645 1250 605830395 605830441
    0x30a0210110f0a1211210a0e04050f0f060a060c060e0a2f090609060907030e0a031707020d051c09021020120901030207020d050610031a 60
    0xc0d2822903101d065141100c5006052194810246440180600b42c02d03d400400c9090b5501030718034071200b1a89030780b0406d1a60500c2102140c030308100742155140300904014100341071095200100a0004045400480e10124803921000170043c214220798621940072408490920515040000c01040101c000000929103503542ca0304980c036100400868869039802180946001041034101c01c500104c003004640081c12139003900118a04642454403a41002c4e0010303a40d036507103804202d2007200145c240800d141e6a5140750003088410711101b040136010741c60315164400e1015844007202d00040c0f94800315002a03030203140301c03907100c0225100e0101030b006001141542ca003c40c0001c1c071807150004d50040c00324500100240d0001c1e421a80c4e1100e000ca080000d2240b00300c8e507500c070303560140c0485918008000052640d03020b50301524081e130000d0720710406900295262032415405452408101241050820401291102001ca108411140c40c0003504144a460801400880801c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 605832895 1250 605831645 605831657
    0x50a020a17102c010909031403041a010b09090a0c0903030f020304080115081009020319061b020307021e03120901180e2202030c04091b140906030a0210 67
    0xd003440209208080c043c00c10103019501485000003404051103881054031800c00000c1c000142e03d038818401d0010168042d1180d010148205161198652000300b04442c291040c1640d03008400d6034000580c00f820042c4545595621200100200000300400e010101401d01507004000e59004485000700ca0389418121225103031200c00f41c0c1540260b801886c4258078004801003070368030442d4544210307a890026034008119406c070520660700300d90700194242c0c0c000b50703151504d900320240412075180110000a420001d810550100740300d804e402100503031001c070b02d9200390710b09000300c804101e480f4047c46441c0380302c000100703840d0505c810a502000f131000c240381003a40d0227a5030140c0178400040c8103800c0c264075494800b000c0e00f0140d4120030390341c2210680c41c200c020400030016025800a008190340c91040d402c100c05006050390403140d0402c121600074400201c0e15500d030217410b80000004e02c0d94040010300c9142d0400400c0140f087c1e01001c5220007688a020307003a43c44a015107044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 605834145 1250 605832895 605832901
    0x14190b0d23031603050306040617070e09071707150801080a03050304020103091203060e2d1005030f030a030b2b0203190f120504050a1215060b0d050a020a17 69
    0x15500318090341031a07600f0030102800040405030711000442c4030b00300c03c9408100d01c0380c07140c1c000700502001c0141e603040b42d405000c00f8485604404403507a0b2140480702161207061301d440c41c0491009140c500d00450f03034400720702400504a1081108034088040c034040b091580b511045a43d10b00e0362036070250900c0300000110341076902ca50860713082c80350810070200708482000e500600521451040e07041d00300810002c1590300d2404150300c040c100c4103004000440c050799508800601000d410b4281111000c000010300c0d031020301c0403192200b41c2c640555240e4105803030184c00e0b00e0000c0400e034880c2000060048216440182c056a42a104201680d610b4890b2001c2445c140c03101200080003031890ba4403008108021401d04009442414400c802801050056030355006601899500c100c8156007400680b45400c040c1c03007080e0180a43c1c6034081c900e8840381003203c20a411a0a030b40800181000301c2e41b61034040c042c1c104024403011881c1403074002c40202911090000004188400004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 605835395 1250 605834145 605834213
    0x82a0405061206030c0312071e141e0109020d0f020f0a270203150910180506030114090309040f0b030f03070302070905010e0a020d14190b0d 62
    0x1620060400505a10b54680c2c4141501a02980c2156501c0c800d105d003240088142c18042422910701d82d0078115181019503d235180440d5108007040c0707410854800c003007040801c0c03c040205000f08100005090004a40c0908100c00d55003a00d20300f1090b03040c68650b5005844020f0750300c0c0c66582107400c09400784818400101d5140c00302d14829800300c40c4450200f8003d04040d480d04442444050791455076110005240580c08212a03910780003544403019851402c040006562201307450b01c0150400d900c8805040ba103205080c40c1481d00c59940b000c018081c00e00348501510489580309040b035901c0d115500c10703500d02c9840c0c9080d00454503094200c105030710760b0304146840300c03000b403d882e031034112903500d03a0b41e94010f81800d07070061040342c000046480080c481c032410b840714040c1c008016503e48030301001952020211440c0c05580340e440040c003c40b0ba2010318003411b01c1400700038407448551360341803daa80020007503104083d0350207403c0004603010710083c00030f40711100c241a8542e41d105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 605836645 1250 605835395 605835397
    0x306090a0f03050f1c020309010c0c050303070809030c06040f020a08060f01180204050a2c04030f0810080109030206010801050912070231050916030b0f060a33082a 72
    0x5c968001124280180c00d40415801443c800c1b40b8910080040e01b250010031540600c5003c0c010781160010008907160340d10440d01d00b03900288034400c9a00d405404882d0038030b02842110141c4844012026483c218035048054a00401141c0014600350602420101c022001845070612030008080002070000243c0c054034000c20300100b190754090356940740151001d1200410141440e0081d05941c5481c00741c0142c1c0c0c0c002c6801d81d40707210a035007040106031344030500a0003442401c0521800011600c1003405560080c0e446540540965490301b000a800c0d5140174003103642e142c00501c240d0220074888020341b122a501107800e0901c5400c0150001e00c540d160b1140194018030748245201c002007a078115601500c400000c4540300980850038221500b03a40c00000e2001010401041101c51441c10040d0800d1005190a43d10b5984294821551a07101800c02000f480c089551a00c584c0d0044034010f010720341c1c142851149020581600e4024000c01881021103081c5460211070703000d48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 605837895 1250 605836645 605836657
    0x90e0d11120711040b04020a020615041104240806030c0105130902030f1605090108070309060b040c1d150912030c0115090b032d03091503060306090a0f03050f 70
    0x7040c55a03507070003420b20031081c4003820030441c06241042240c41041c1400d200f100d00c45401035000d0021034a40505e482d440c2d19144080b10b6200740c564181c01410341a141c018030051a01403104074210712064540900518900b105109003c1003404002c501d450105952007800424a03040c0d9840600c800454000307101a04032402cac0c01d1010007008840b8280c01c100e54000d41c44d0201c9461161306030001260548039019445000078028000f140c10203001c0e812040c4454404d0030302198412904001c1421242c40c00d8200001400304415500c61704e00141241d080c841d400d6a074501400840d0074088050710481c0066030083d441004111036400c0d060040c0c1d8010101c0710700a024005508880700c80301d00090061040b02440c0401d4040240360014048041010705480d103043c4c14441201440420403140e00025180010481c50943e680d9086030b0051a00080c04200c1d26414400141481c1010080003441c003a80041040c00115481c00d0203541400d9162800c00c1d40c50720310041d1800240561 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 605839145 1250 605837895 605837923
    0x906020c0604030315080303090c121009121407050c15040f0b070b0c130902090105071b080d02240403260108010b24070206070c030516090e0d11 64
    0x7241400200341d410f030404401d1012140714101c806403290b11840d224402a5150340302503100d030311100703454100781c01e14003811450340b0191845e0464401c080c4064580522044890300c207100051240b040e081401030204015040c5030758241009580d48564904001c11400e10488002580d141807140d082c00f11005032000ba0140f0300c0e0b03540c0d541440d181581280300112010030800c400500c1c005110010348130203070016082c1c020903c0c94a04980009d40c0010705c060b040010800076003011a60052180d04803005092003403400da0302e0420454140f02e8004081c01c2190011506a0340c0e00300800c1e20360b2205003403500c00307004649480c602910301c0c444160184041c81042d000b01c10302000002c141078100d62035100248850161402004000003c094400e130340203220a000d01305400c82c1c44041c2c001725101804442c82c10b0980d481e14000e00000e584211616806243d4060031102d5415500c0000d01c4500ca041c003440000c03440d1035032100041c0e1354100400541c44070407001104200200415140030b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 605840395 1250 605839145 605839153
    0x130f05070306020309060f1618170a060b030102070503030a02030a09142505010f0810090207050a12180504050a0f0e0c090f040c03122607020615130906020c 69
    0x1e01d14100000e0b40088a50980760b00072030b000610103102d07036640d030b500c1405d21600d00c41e400d18502c401038400c1d42100c51144001c14500341c0110781350102c1180b6074185a615802401540034a1501d082503584c031072411402070b401804040700060700041941d402003021807025860703644040c0781000a2003080780c060010307541400310404903507010541142e21682000d1048071082100b0310601c038891035100341030008804500d40102d0034400d4810541000204002068003a920302c00c2e00260f802074401510103402c0380346040d082000c0c0b07810101c83c0c80705500780340d22580c608000b40400080b0503c91540601d0b00e40f80040e03450100ea600c2070b007124170b204c03000b000240d4402c039010741e455005050860160741a40045108110312a69052049034013020494829080d0703610f20301c580f1000c00d0b1000a011600d4070812000380d03590002a81c41c9103044c00002986000c0750f00070f18041d0080c3c03106454081d41d003400d0545072100040c0f85100c410f101030104a01c03115183c224000e218000c070003403050003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 605841645 1250 605840395 605840399
    0xf2f120609150d060606032301091104050a03051c0f0206070509040b030d030509010f05160e011421071b060b190f09060803130302010309080c010906060501030f090506130f0507 78
    0x3030958445d43c113941641e9810030000100b0780b01c21800c0301743c4c1d10f0031441026440c17004110324101500b1500011040c507900c5418980d0342c42c08580030062940044074960000484c0881d681c404010f41c5c4a000118900000c400e68031902c069102d00c2d010700780c1c208001d40055641d005403100e4110112109001c0e003150014191140c0050042c4025600c03942d240d400e151a1070040b00490203205e0244105480150034162482010b80e202100d074141c490521103060344058808038003034060300c4e0b00c40004a0111074088140c03074882c90244001d0080003484262100d40c584696600c55002d4082d1340003000149240502000071500c1400548030800c0343c3c1e4520000c182e0b005100260421a900514140200380d00c2d41890fa03140d010701c5c0555211550003c3c401c0000d9032003500700e200180c0c002d041072880c020b0030541c0d1901352290710405541c41c0d0f44a44041209503854426514442c0b01401d04104e001029580e86844031400b80c239980d001c589070104041849941c5d00d061600c2c3d075000d4120340010f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 605842895 1250 605841645 605841653
    0xc050a0c3201200406140d09020315040510060305060711030903030c07050a090629160501150602060702070618090c0c17030c09130f2f120609150d 65
    0x150200602e55440c40f000b000e105159100069405440180d29000311001c9010700000e010780224001400072a16010355a01584041c08a01c0c024942422140000e2520742080c1e442d060444002c0344865182000c10008a200071032042c3e00400d00d4035184002d1140d41d240b451071030040103441c5a041c040021110410f0303000051050444409840121141c1d40d601a404203c031100e1080c07200c19403c80c500b18140e201c5c86000c00c5090140740c282d080c00c01c049800391403110802da10b01119969503d000c10751401e410040030304010501880200168a41282e009464100d2031140d541440b0000326000f0702c4580d2031015002519815004018100e07101c0001882c02264000680e83c144000c00d64900c2e00500e141120f01c0741004441c441c2c03804900e401444020004004403603550307030b512103a001c4040400d00481c0c44982d2080160b25070400759060a44421503a6107520b855401c040004550040000444560050007111010150742d40d06600c003100303c08102c0441d50010311780408070200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 605844145 1250 605842895 605842901
    0xf1808190201080a140105011b1a1801060b0d020c150a0524060901050904090c09020a02100b0906010e06040e07172404180c0b04090c050a0c3201 64
    0xd4001d80e940003260f11103002c860308a992944202030b80310600f2006020a5000340801e00c4011202c800a5603150141e07151080090044200b05c4a1038054405024084803031101e03100c0942910390080000c00d251400c0c854513840745403c000703100c80e004103801907407210501a0401c0702c2052050303e000351034080740c4e5000405040703650508680d070f40e1070031807950044402071444818000d880c80307190440c24001580e0942140790030680c40b0703445d510315000041e00c6603a0b540052401a40140c2c480b000d80c40c000c0d0804104107070005ca55403a20101c0551030740c81e0b124407a0040d200f07081c00c002c15200540802d20ba42300d02e80010444610441c00e1105070340d40043e0215018101114130301c820384500a000380c0040d40700300c0029203108408084202c5141c554826801401801405a150780007a41c0d454800d138044d6001042c20440414204a05021800b4203440507115151051400302440b81c081d000c6400b81001070524918061040c10481c5445600d031034814a001400c1c0301e039186062401e0207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 605845395 1250 605844145 605844193
    0xc07230d080c070f080a020d11060c01320a050c16030e1005070503030f0603010f060306020409050a0501050a03082b0506010e060c072904080318030705010f1808 71
    0x7482004000513980c861125130300e0988000304060701000d0790603020031010040301c9000f690f4624890010520075a6018000d243c40100c100021441004070620812000d101a515a20092041f0602035403420341d0301c010359100300e000d1000117054442403038611241c0180b03010b011888802c0c01e6480306058000008000ba550101c0721188005243d507000c030f45030b019500d13004281354402d0020614148480103d1580050060000903503c15021012000c0d24660b0784151142540087c00740a424113a0007055070018002d4014081c80d498040843e08800c41c030f100280010300c002c54241100e4804041000b65000030303105040140410300e921100400060b24014041841003400c0290340c103103c0d05807140d020b001c074060b10905152140010b440c0700380745841c00d110030103002c03080e550b0841c5c032000d0000348c540d2000070f64070f0380d01155251610003283c4840c1c5210750711084041101c1d0b81d20600c45010170000c0e15100c02168034060500c5c200e200359401440e014000d146c103d820305d004202414138 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 605846645 1250 605845395 605845417
    0x90c040e0c0702100c050a050706051206040b0d02150708070804090c0206041e0c0b070c180908181c05010b0418020f150f0c0a06060501050c07230d08 66
    0x40355126192404000d11808400a400480302c180748401d5074090b02d140c0000702c2c02842030301d12000980d41c680c0d090408030307005600070880c04102c022408400e01d09641e4402c42c240c074100714180e03508001440202e40046c00034400e000c0b1803449140d200c41041503a07811a84101003940303070310720303840c00032047d070064066482c150380f8250400d10700c0e0340b000030300038052074001d07040030b8201c1d40c40403400d00e1707040890ba02945c0056605100041c011206030041500501440306d41041c1820700f100308240541c000c0003c5d01e602c0c10400d441c004106083d048401070004101411060099000801c4146407003004d0002c081803040100001e119041d0007140c4034001c201d4081241800204042e083c0f031840d084080d40110b00804099481c0c100304224a4051070b034103114608050340c0405030320840d40b103c0e49201d440e801181108041003903034014580a0502404d0541c100120345d00303100e03036404040c80303142c130f52a0480703555007184420501c000009041c00f42660346080c1e85400d0030703202070340710500b80c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 605847895 1250 605846645 605846669
    0x2119020a03120b09060603060a12050d02070501020d09150c06090f0501050714040302120c1002010b09060103020703050901031e0c020a110a080715031d1f062111090c04 74
    0x7031040c0c1c003912440c2948035004000c04019205c0e03a05222058100a00f09604142619000320340d001c0c0e58030b0480030750362040d401405502e01100000f820005594011419507001c0c0d560f9405554004101d00700340c0303401c00d600910700c08090400300c40c1c07a020303008040c01c10380c46c0c0304100c0144900340940321401c1d4003400c000d0000751141d010884811226003403540070754400784414401071400b03510113181c0301c00f100700b1940b032040004001420380840759217410161b99074001c02011424031010055110109090840c100841034401130080e1080c0d09080d41015034031840464181000085002d940c21404800c200d10b00021402070b50344c01c03442200355001040f101c2104840d24264804100750f030940c0000d4419945010040e24000c005000d40c50280764442c090717102d070101c04144402030305101500600d201c0c14007c0390b14234001056540200c086007082c034140100080e0b0f000320b1280010003020740749141e0781170034011017501401d0f80044d80810000c05100085d019140500700756800040c41d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 605849145 1250 605847895 605847917
    0x1020a0f0c0308120a060510050715020403060219020c01080c0904051314070e01051903030804030302071a01050f09041e0201091a09030f030406020a11041e022502032119020a03 78
    0xc0007141159238401d0002d041040500e000a041c09000307564444124405070500340c813583d8080c1aa08441822903e0042c2c81c42580318081d4104212150310b5820f08111010741440c000180749071050301c14040c0981d4445000c039041c609501c000301429a003010310741303070076010109819403143c08901c640e04100c441000046402d2400990760070450106030444018039185039401e0303030b450400900903818103900340007510204c1c1c0406a600001800500022050360404d000c00c500c40001100807030144030020100000503940302094540121070708800c505020943c0b004035080741d2503801c41000c820b280302c8a50308010481000e051103000c21020f5560b0129004c0b984d0f50350340164442c1d800140d115500603c0031079070300800720f1211354001d08003040ca140c0b00c0e24105400d03455013115000719580010021485012901e0740c1c481e0140c001c0003002091080c0d00000c1d610300309c0d040d104078146105c0000030060201d25044030168020310114041081da1520007944a00c1000e00650110b0440200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 605850395 1250 605849145 605849149
    0x1104050423011b0e2b0804080c01030c081e0901110705011d0604080904020d0b0303030f0601030e0307020f060a020708070605040801150602061801150b0d060603060501020a0f0c0308120a0605 84
    0x14084c24000301424002d41090300c14000b007100e1841e102d200c0c003030241800980001c240040000c002038804076008000741441c45000400f2105000751180403c000c61041c02842d00c007051000e030050303031207030300020a5845969603140100f01404400000450010b802410000190000d036803110218240c4005115003034038076a06c0c0e00c0100d6004000000802c08000f0b2841c0c50f0740036000e03850451800181c818080c001092540d0300a80e00441c00d003040c0700c1040031942e818000c0806183e01d08000c0c60404119a02240202000300c42e803502c120030110b19003500318400c104450050002c10100c40c281076841c04050415071050044000d5035003040001c198401414211408807030740c0d41e004045036541e81403903500488074140711100554a429035103451207542d000007005042031a0308165162000c51151044610581c084402d150a100080000d40c0e008140106425003107066892038500625140f9145c54881e00010000e035004141d000b001d41d031100300c41b40f0030b20540404118490326042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 605851645 1250 605850395 605850407
    0xa080a06060b0a23091e03070f120201050706090512180406060e01050c1005150111070609050904080f0f07061d0d03020a0201110403050d020610031104050423011b 72
    0x6400301180c50b134128690303034089107520034001401582c0c002d4104a5801c0000711148850b0385924004030307007100b91a0031860140100130007420704d0000107420901d03180d105404010443c40280c1808404200c40080c0030b41a08040110b6910005031101140650159402c0303802c0103035000c0c0c5a4200064518450519200f03030410b83d0f078186c035044412400c50004580949c48000302107024015031100361b07000415405a00c0c051a803101800c1d43d116801000104100d9a40199080944c00640100551608800d41300c043e1079003900c0103807180d0340b42d0800c2c40c1184110480e10480f40d100051102480e80c000c805420700c141f080509005142000741040d034401e540c99403480440d0411444509181e001760b00401a28030300d8000411420750f400750a44040d0420350040c0c0c0d05400409051200980c10310400f40d110403008507212001e41103803a004014590007200d50301803a0385201140034400c90f005008210b400300510103184d00b200c030522901078030f0310504004d4000d0780d01c10fa048840e0702643d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 605852895 1250 605851645 605851657
    0x1707020306010315020c1501140301092607080a050909060906030d0f0908060405031e04080a08070218071205070e0d110a030209100f0b0c0307140106050a080a06060b 73
    0x100241100d03425500c85914000e00d00a41c1000d40c5e0b800c01159006c81414020f84030041e10181000303461358500602c403025030301d03010540f0744240d142c400301c00000f07482c440382030b000442c2489000056410010300e10300e640c4100c0c00060710140d004180d0b1407483c1e074040010144054156180c00d4191944001e006030b441c4241ca1303a42c3e03d90000000080c0c83c6125100c0046258128038004581c10b036500882d41c01c102f01980c003500d1907000000c0c00461001c00c400f44541e1488440d029510b01450202640e40b118502e5200501007000000c03141c0a40d070307400f004e48502419039600d1852505003410042c0600c001001c450b04800e00b010006400e46005900c4180e4603500a04a9500f0305141d554040f180040001c40c10f0b03000c0d0f802280800276880d00c80038244590302264035410540d040c001c2c1d050500e00168400580004100600c81c4410f00200940b4001940405005040003158203401d0141106400c0141c01003000c0c40d00058031080001c0200c06030b4041c0c9002c003c05505e503002d02030391744544 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 605854145 1250 605852895 605852899
    0x6060a1d2d0f10410d060e0606011814130501090c1808120d06080304031a0f011a030a1b050403021311040b070303111c3801020f12030103170702 64
    0x130060349080b0007540c0608841d8015540c6a4451200f460000410b801044c14040e2091651440d002d4100340040000507000b040909105100d218552850320f407485550141c0200f051404154880903121800181c4141c0b451701c40a01440d82c40d141554020640c0d11010303400600000901d89815000000070300660391188054126403040c1f0010051030303072004034804452507a0301c10010b2041c0d0280080d1028500c511071380d1038505181b2207245681d00014001054407002c15004022408500403d020000240c40c050b40d16599204840c00091141181700034031641d54003401609140d00c40c000f0001d8a200b2203401040056540c0e541c003c56600a4000c80d488400704814821501c5c46400341039100d10920700411411104107a886980c0c00420315952525441c03c1c1e00e6038605c80a005141c08950701d10441004510050031200102c09080c0c0510440442041c000f8403991003402414102e44001f802c8412030f0704402000348096100b4031042c4c0e40f10030046246d0f40c00042c45070440d0300766500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 605855395 1250 605854145 605854199
    0xf07080709060c03050f0304030315170a060506030a020907020304080708030f07110303160b04020a21030305070c0f1202060c040b0d0b0d02090906060a1d2d0f10 71
    0x103102c8240e40c1c0e102c60090a409100c001e01c0444111003a080c000d5104a1083ea00400c0c8502c04150040100d146600440c01c05000d844010400800004001e00c0e0950407810200d0b0545410020a08ac803007610300c06900650060100800c80d40c0001c010402c42d4640404c454049070b036600e6850b01c90082c01c1010b02d207050108085000b02e110084c07540f5000f4001026039241c4180340d041c820030401529011214082d07503008100075450048105801003d0354030b00b0784444500b1482d05071204141007402014150740f140425021803140610750b002c55070000740400d0b4040c917810618802e0340c2e9254031000512620001a505000381d0003504c045600d24900a800e2103a01d1801001404c5070304000703900541074038a281c0240e0b5a012000340181e00300c0000e4142401c060091000300d500c95000740c0351481c2078405501200c504c40800552008010307022010f102c0505580a8440400170b22007051108800103201d200c1da40d4000c118050740f8001c20aa034002d503615031051810422031410010050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 605856645 1250 605855395 605855399
    0x30c06070807034101090c1209080d1d10020d060510020307030c150507030c0905010311040b130503030c100c020c1e010c02120a051e0717030d140f07080709 69
    0x3820880e5807801d030110070000350f007601c84e0401c400700040d803d0b03225811080d114541e01c4419900041120800d200c007081c20b0049580c9030b260380a06206116800f5446a919615522b48a03400041d0003464a001070648910841001440002e9002010480b0700107241c00b200048510b02090302c91030381d01682d00918281280c070381f41a9500e414070b05d801d50f0803144449244c03525964910139288208000d132400210714a00f4840107140f8207054000302e06044c40e024940380300c5600030059400303c0e0319101c181e0380d9455000461744607030030706584810f4041c4402b0410b190a0b2001050704207080400c00c0c410448003407444012a5190302903030f28941c00241940c074440b070484815810490500c0181030203151300310940d0200e007490441e02c12602054200c614a002080410b000e000140740380000c000404403900301205803030340c80a110396020240c2d94941086110340500c1500c80094484100300b041e280c0300261140c01f010101d4428004008420001e540b441c0030b01400b074000ca0859607a43e50440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 605857895 1250 605856645 605856701
    0xa1506090b12120f041d041a01050604140303040801060306140705040501050d021b0a060219030b0312210406090c09020a021005060105070609050c0f010f12110c030c0607080703 78
    0x1500c04c140020244204000c04102d4100e0300311002e2502c5c42d009215800c034030342400c0c43c0c1c2c0351044120312560041c23410303030040006541da0001d81d01514101014440103000301c00c0000e02d984140d51246e0441d5003800000424400154030046003495034103500b400995901404441900c1980102c6012810500012a82001950180032034240702d5010314442441620428609038149408039405600011201440d5002611030030068000741030038054000302000103030700d80360440d165124580020901c2045441c2c2d071618203207100070b413500310142070415050240c050074040d4802c1d9000c1c0d0310ba04001800002d244225044080c0e1640640f01c1c80d80354541103005424007611680c100107042c410000851070340d00c0b80360503180c07164005289031001201840740c11214060202d044c0016814101442e40c1c000b810b502803821058000a2501c00307001ea00313403440c040e42d5402031180c03101142900243e840003c805004419544a4289075520380390120162182030003240b05c0c0d011105600071104d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 605859145 1250 605857895 605857897
    0x9010e060916120c0b030a1811120c01020304032904060603031704021c2a090e0303011d060112020c01050603070905150906030c1c03080603070609170a1506090b1212 73
    0x400c81460001c00c107618640c644a05080921206880714140103030394603270398a003034407000c42c4681020002d8001029a40c1c0042e40382c4c0114440503210200500000c9e019140c10584c2003481ca240c420307000d02a00307050508400805243c001100840c4030517030b4990303241507200c102a100b07581c02489000410110442d1090b1007010b0b04044611f260103081041c544c0e20f82091085850040c9147c082c2a1440d0040e8202540c100840c4803260390000c100500c40e07202200da00e142000741c40c1f00d460007541ca56400480302c3d8007420100d601494030100302c103c40204103412030b6002e03507c02c4003201c00c0d40d92600d81d400200c07001a01d9501141820b1714598000e0306100080c01c0c3e000d1001425a42c0d0740d03003a0300c0412031515078100c250f00701c030041482c82e0b0b04160b00040980d40201080e8000c080080c2481030282401540e40205100c1d00d0b41c40c0518840d541e0100b00d5601844e522100450a07900784490000161906000f416115402c1ca0300244481c01c00b10a9801c104101500a000324040600240342d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 605860395 1250 605859145 605859151
    0x114010810140a0c0e03071202030c04200711060f210709211e0302060903030f040609053d1b031e05130605090c010c080309010e060916120c0b03 64
    0x60240120303030f20300191b50500060000786804400c000c0340c0c000c50320405007003140840c6054402c624222008802c41e41d906811240c840d215000c240d2744e190340b130500c010024007003c8019401600051450035801c000005410190400551010301120308840c503a0f02d1081100c0600014030601410480b45100c0341040300ac10440204014002c09c1985900032541a04603c4203002c40402d0044010168100121b50b80660040055403c0d801d000d1105084000058005000720740c40d0401d5005006003030101c002442102e80c094070006c00c54800c080744440510168210001d800045004e900c4006e00404034a00c0e500c1e0b040700f80200281d032043d40140803104514044040f80790340c0450a4200c2e1180601490861414140a0000b03151507016108018404800da800061040c0038607600600841012136200b64016240d07540c2c82c03c0c0700d0041411001da0700480c800c01003442502007000c00c0403841c040304100c0b01c1302c041782c4a611b00c0c018040d40450081c480f100030003003002000c1d803041c05550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 605861645 1250 605860395 605860397
    0xf060f02090a0807081917090126090705180a020310080d03060503100e032d180901090501031a0403031508010c09150e040902120114010810140a0c 65
    0x8100709080020070200d06164100c204641c1c446981030214074020089008008042010001030500703e40d80c607808403503102e030300440020010520391000e84c0a0420740d00e500540c0001a051424000c0b030042203010140d40305000c5e40122480441e142c1400f41c0700c100e0080050200d50010b4079194200c03402948002e00108580d40382e8600800e001034282b04124004004e5640414414203180401d800d001484607042405890030544a08201c00401550040d4005000601c0c4803072498904442c072a0405600d04044680001c8103c0c3c600b04411040b44200d405840014941e0303250020031040310b4080c00040d024a203c0400942d6040304002c180340d0061280c5004920384100c40d0050303e40d0f5490740c00c01c41c03160751203141d0b10000d20b82c080d840310028041c8642030710140800322006400e00030102400c0e03020310b496404807402d548544841111012541c3c00811640c8031014000440f240c0078002c80d44103005030610181800854000c100e609081141000701c10340351508034400030328804e0140c40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 605862895 1250 605861645 605861647
    0x31504050a0219030605090d0f050a0215010b04090b0f180903090a0617060a050934020d080c0304031b02010c06060603050612010219050f0c010c0c0308070c0f060f02 73
    0x20010f072a0900b1407070040c3c9500ea0300c90241da041d803030f0075000d4480083c041c1c1d5507584031040c2c401c640ca920407400c2c0320760081c40c10110707564000030a0403400c04a1916011902e42101400010403402d040d004004580303003048100425204481001940803640f000d49910a100103a0381d400c01501d1080380c1d80042c10203040303074944500031010400050256020b403000c03600d042a40540001d44051495225204440c1c8000950400300001c0110001030070050400312506010507405211603600b501d182800c5021800001134030300002c0d07945029800110020302a1f40100b13188045c0d880507680900da040d202c05480e0009207442c150142d040132403c2c1d0411900c01c41c80700100f8954414040581403aaa0100f003a281906c1072000c90a46104024110783c030400c40c0b40f5a5504003000d2101c0c0180300e01d4910381e1a03103040c40d0800a406aa54900059464500d0b040c030381503085400c817900c40d031180c0c0350040565900c00d01510107013421000609401d039a003c5400001d1640d600107030310524030315401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 605864145 1250 605862895 605862913
    0x1704020916120c020102030a0608161503020c0a1b17060c0702010c080c0c011128051e16050a0b0304030309140d050408210409020d02070f080706050108010b03150405 73
    0x928161881500f005001d0707580041071003030109850255001400c002001818158041741c021090321400303104101e2441d03c1606043c42031132007a0111115030045104840d0140d28034105030f43d0701003c0039000888004403200000301f003200c0590903a456001c6201801641e81c4002c41d145032680310280403410860b0f0040d000740028001d034098900c40400768020900c0c542180300141206035006006142c0341c1c0701d100011901001d4140f03018140f0680c9a06025000882c034003c2d03d4188244850700b208940b031186245000d000185411a05800010316400d03076a68500b1b101c0e20396602d01840211000800009010a0190b08580c1916120310940642c440300d100d5650b0411601159100c001680042c041101e10b00c10407603000d040308220510601c1c003003101120f6821b841b983c41a03601254000c64040c0c03051900c1c0e8151400a500a0340d902003100141c41d2a02041c1c0c0158405c8500030703e8207002151007401407040242103031001d4010810134079517203400e0816081c000c000303c42d17501c956248 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 605865395 1250 605864145 605864177
    0x80702040e0a030e0105090d02010e13050405030309070f0b090621070f080906060306190608010606080118050403021b0307030609030f170f04081b0d020c011704020916 74
    0x701c205010704030000e840c461903640b8000f00301070884c4440504000302480302d1030301070703481c1583c00280e00d40c2420300c8982220400c001c10508800f05007591400351818040009204002c00210b20407100309003503441c455119214400040300c2401000d08440060110203002e05014000f00142c001082d50100592a103401184807030100301d40c4030780010300e5070300600529504290700742d03008140e4030064400c5103414000f003641c2d07406c000d0448034403180f03584100f2000c0195078040d0010b02007101c002e002d029120390025003070101c01c0c40307034000d104a0030721901400318a0384581c60040754560301034210004542c0074094140f108036403440e45070054200000c0099568805d04e20242e11984801c2c0100c0c9107440c2c05003003007201c540410041011f800030801c10316a210700103170344158001080d0742c495181d401220a00c102241030004248100d03103080e0740c0385800180800e0981400d0780e40510390070b10142c00411605060b1002908807591002191103001813100f0302404110700e00d4508094011000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 605866645 1250 605865395 605865401
    0x120303040c0e151906120e030304171b0601060e220f0b190914090705010837060f050a0311012606040b060f03040f060615170106092108070204 63
    0x10102c1d0b4650103414200305c2a0f13000b846c088120380003044108000f14840c01e000b5228400140000c0c10100f04d1400c41111b085000141c1e0104a800c03102034603a40c00d02050315642d5002801030304049101000054201c0c64040708c50584450001301928800e050000070f040a440d03010500c5940c0b03034170381c08940403a442d2140d642d00518041400140b1080c6080203440890b988940920741d9400c814013003203292400080e01100302c2d03100f8601420700b03659141060044000d565031240789032544c40075080c10304603100000d0102c90500351042141c43d40d00d0040d105030740e4591082c543c1104140c003040000c1910403020210405040c1003442603480311000344840075105000441d2095518001c1c0402c42c1000c0c8906da003052400e440351454100402404451404000c2c402841e043e402281c0074100714958010300018041410f241d02c190101100c050102c0c8104070345140c80e58020400010b030f40e0312544200048500d4010b941d6042c0c3c0c559030011407141d510310410b5500180c20000301c0c005880d144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 605867895 1250 605866645 605866669
    0x8090406230f011e030b040f150e0606040b1914040518040f140f0f0309090c0c070b340f170435010501050109050d03110a080306120303040c0e15 64
    0x2540004906801d0b0003044101d48e400254510003500d0a440102c808804c2c0000100342c85010107900781ca03035101c40000c3e604ac07150b41c204422450300407404845111240303401c060460b21a445413080806001082c400ca030140c0c1c818607602c99441040300036410f0b0110b003031230b810902610076034401c020180c8505c401440d040c04100026802103100ca1443c85043c014010040301440c040c42c40c128403400010304980003e05070b01c02403400015102070075070741041904010b2501c210016152800e01101c00714074150440100060194038510003641d03c581181042e41d00c0e4040cc0c0100b8211031510303054908400804c40c504044402c020205040c00000c429002e2115005203010003140c022080c0800c0320b80203c080e120b00e07030425005005c41e1381c02951407000e80300c054070025024901c80c00c0488590f0180c1c00a00141d014852075001801139440045214400940701106102840341e600360340c910040701c000c0c04240343c010702403202000c1244800c0e00510039110042e0366425060018241844803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 605869145 1250 605867895 605867897
    0x6130b011215030b010b0a0807031d060702100e0f190525150f021b06070b010b250807030c110306090a0506060d050c06090102011808090406230f011e 66
    0x4004104204045250282d01410328168991f00f0030340562009404ca8a000e03101a042c540c99010b052056161880283d082044001c1201c0d07083c01c0c4230b000603448100881d86403400c1400c01c12182d44200f0001a0300d0704003825140208001041e0080210b66503101100490707640c02280b41140326110801400e401440340d407452400154644140d0342c0710720000c0580d0409002d5040c140003000390700401c140d07459420b101042c440c0c070201e1000103560303032045980c0106040f40c108008542c00c00110007601c25210a245810f406854250313808100e0ba2400030005d0072103200b00040f03c0004d110340c41d4414024416081001b03540e07103070800282400e5080b110185258004c070301907424440f0400100b83c0048040d507510701030b003070203440b031503201c0b030071580d00b00d0180e2030000300c3c1043c40e4801d501944111005205040b14a1524982424142e00031a008c5124905084c0701298804680c902034424040e04a510447c0f69030b10310a120054407141310107030500030300898211085804410300d114044c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 605870395 1250 605869145 605869181
    0x19060e092401080604030f02280606050103050f01061d0603010801090209010510050a08090309030601232e1101020307031508070509071d130207060b0906130b0112 72
    0x16201c003806000002000d07001091a600004020b06800801c20b00d4200750107280140207011840020703440c042c200c0700d041c00b0003410031400203400529030083c20300d0684140f000340040c1d80e40d18011004e403101079030007804c205081d0f00100401402881c10203028170440c002d400c110410700c00001d0007508242e0201850f07035107809108007140343c820051409020100d41a00281d821584020b105000d00310000301440740b644041514000d0030002d542840e24001c044071095a1203180005000c541e8240094202c140c840403a4803619143c40d07002001e070400401c400c01a01a610610383e060b21090300c50091060301c0090fa460340d2030070300045100b94401d45021824402d0941c902c09600c41c07580c060300840e082b4040030b0001da9182801c0c290010396600c3c01440b0000d074507000740308280200d05881d40c0040c80712440b030152070b4243c014140f001d0042004100740d40c1c00c5000c2c031030800e40850344194003c0d28801019a1000154401e40c81d428040c54a2400701810350103020469141c1491810342040e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 605871645 1250 605870395 605870413
    0x308121306051e1b03010b0a030b030613020310060e0a110d060e0117060103020f010302070c080604031206080307050a03030c03020d0e1507050a050406030c0c02090708010906050a05030619060e09 86
    0x101d5454403580162240c94112100704d04802e50010901060081aa0502000070001d514501c2500a000ba0200c010141c8600d810b01600e40c1f035402802d802c00300d01034010780c0d01c0322100c00910f10884044410441c0c4450a5660b400610002001c1200d400215200180601c20010100b441005e000d4286202d80310f03810b504000c082c1d6079040c81071180010782d9010000502c010f031292452078020380028200035803509a01d00d44607601140300e800080c00c03440364000700b20500d6440b0b0749100e055000e0400c00c00c20a501e521301c0a8076071181200142c00c55104111550020303101741d00a01150030249001800e0600240004054600388881c003180341e030044c0100f44001450b8100c1942000d03043c1400382c507001d058a80949035000301d00c2818241555000d1041c81d460041e8485484a07030b0040c98038415141840000e1f011910a02419010340e2804030003040301d0a00070020801d664004004110a5888190300c051480b030200c217001019490301800038004242030100c0380103041c41e4000d000b01031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 605872895 1250 605871645 605871691
    0x3030f0117010c0c080d06081002120f130f15060b0c010b0f0108040b13060e0a062f1e0f03071b020d200a1d010f030812130605 56
    0x50254500c54400741d1402d66801e000503001a03143c50415403040017651281b074580891070051038294080b03085c0740500d807281c0d100b034011617000300a0030011405031002034480c0c41015030560800c4a6100d1400c00000c1e1000c080380d4401081c008840c0f040310344401032040254024240d9815510608000c5004178240450740d0f42802027408159060791905010340300e0100003014968040c101800c603550040c0851110500110300ca00c245821400034032490705080002da903501007101080d24142d240420245590500b404003980715001c20042c6c1c0110758468410400641c410140300070b400344800002114521424090240203008003c4140c4034540310a0282040481c81c590b145040c94500c2c541005a4030714482040142c0c12a407442d50444004098580c0050100122680001c0308200024110440c0035405441c2e010904a20340700d0740e8480320003d041205000041142405100d003001c18400e044016522613101c580c04051140703a91aa8002c490080e82c414000c4140344040324070003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 605874145 1250 605872895 605872919
    0x7091e0f0c0207051005040302041104260d0e010c021c03390302241803030903031b1c05251202181201020d15140f1203030f01 56
    0x4204250148200411a40003d45030403d6001e11880b40c1d600c25002c0200c1803003501514040c545c0a8001c210b5145100401c6a007900710740b00341a942030902c010300655080c0380d1107a0000e583c00400410790319640790f80940700c0025581c1528100070441c010100035980b0344110b900c0d040081401021200580d0034010701202003000101681422480c07811030604040d2801c031031780505030304d00880c0c001c1e46140490034480e2822841c0c15440b40380c2544060310303003200345050140341603003405145104030004136916404121403400711500203100003040d01005603a5500d030045010201864a80201c1e110001c003084402100e0a80b5076407000c0100010051544142800c14980e403140c16280440d401031a880071400c00c101d0302900420019004021500c19a1509030014050f401608968285500035003003004210690343c18001000d1960210005a009580090344003090504c0c4ca4410b208035a81c200400c160485455401d692142800303001550003140b45040261055141000721000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 605875395 1250 605874145 605874161
    0x2030c27180c0904110d0c111006061d041404050312480705011e0905070918020604060216050108010b0d150306050c03010315050708060d0507091e 65
    0x220700300005000c90b0940c1c030000d960311074808840c0030616116031064910349000740700240f4030003400d046103616000d40003c81a04104a02c031300300d8824500201c60103059031490311074240460080907105507003c81a07160b0195010015002252901e80184d40b01d91000e0b0480b4203850f0b40e00042a0340340d8482d02407604c20740288000b49403558488070300102d4441c1280c0000103611842d070f111030051041c10798482c681c881c40080b9840c5031b00c0ea460390038070740d0290000b020706948000f400d01c2c980b0120b00c89480741c0d80c1003a8010000f00712042c24a0045001404511004200300841c00d2101d00160346503c0107101a021582c0030740b21568500d80c1c580b036100070745d030001030506c01010014000380c0203420540d10301d81c1d40fa07040841e40401203200400c54010b03d400140c03603141000204441d08050788011b40c102d9110380040769010b8010307580101150360036a0200002490b0f880851954903098000298480c020f00540d00ea4680d00c95458040354100382c2c14039100a00000300603004201c81c07140703400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 605876645 1250 605875395 605875429
    0x80907081506060c010b0325051906080c0708040308040302010e1f031e09030807110a08030601080a02090a03031e0c0b040201050327060103150b0a0902030c27 70
    0x4044207810000c40c020002440940180804030b80982507600075009000c89000150a41e020149a88000c1901e140120780c241035420f0700490006141c100f070340d80001821200100340d412203050100403901581c010b046043c000a05010150110341200000c100541c031038a90740703685920f148005004c651050a901d4401e00444040115020b81a001079008064620b000103004c6a0702c01c0d17110401c0405086000241c0c41d00c400c00081540000300d550107284162a00860302c0d4455119913a11070300f00c000240041000e002280403540110342441c2c00440412015080031001c00108034080015407054000480300950403005280c13840c2c08402451231450a11500d03007041c0c0301c43c040c901d4041e000904100c0000f0001d031046080c000e1408e40788616501d0f80430400c1c141070016603220700a0000f039a07400c00075a280c54120714a4480c0c0100301c4001f1700f052624034a40500007000b900014529a140f4a0810020384011148583c0d800b0600001500c3c5a03500007107401c0c4410100c403154400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 605877895 1250 605876645 605876653
    0x40315020307140c030d0f142203080606070f0c03030e0f090f07200a0213060e0f10080a1a13080409090602042303010e01021c0e03040503030a08090708 67
    0x24090358010703e990082140118207543e03401110402c2459032081b07103e4070b00b00c0f902c0d180240c4200c803031540000080741c8114003030740741c0781e00e401710050314005801c41c0c50000e000f0300e01400300009014140403580407000a10a174202600354846145400d00c00e04100c43d0300c142000b0038020580c12141d01c2d80454015075075040c510f0401c2c004202680e002500d508050301d199030026655074403d900d082d00c3c2c1310b030800909407a6980300358041e542d440507440491080b10842c0c5400340b84c1705548900170895244000780d442984031240392090f400c002504102c140055040d000c00c003040c0810886140c28498850030019280014280c044003401905030100305035941046400714141c081904d00f940e0103020005090003240c5800d100034841d0342d001c00c000c09000d40b040325000c6002d804009811006070000d000444114142500300c0c421042d402d00c440055501110b00b91025a22000d00c0c01544001c07a45050784900009246400c6414954006200c1104101c900c1c00c06118201c003c0603020300030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 605879145 1250 605877895 605877901
    0x10306022d040311060405040630020a06080601020f071e080109080708130819051905061504090503040905060a080105040302030a050c10050408090102010b1c03080712050108030403150203 83
    0x3050301d44100d11019151a1410b0240c40c05650b030f140403640144002002000303407680c1c80540265401d6100c03500649545200100102194100000002c603640103145111407801c1142c00e864400300940b031141140b061038840c141401c0100240c6024002e0010041a50507031a225803000442d02d800124103a41440c501600040000c0181e540e40381d40b0402e0152144910901c0c02d0f2906100c0d400000c03644907138208603400c100182d42e40c6030b080380124161039400800c001040e6040e100f4138801001d661081c00083d4488001150392a00401c0c020004a081c903041c1c2c6689245400a42040e0800c940d5a018010070b46000b507185402044620000c0c001071500703803006901c90051422841c01d200d000100c928640c0c5040c0080d20a500d1422010480703420942000e4901c0c2d00030b40c074482e0140d840c144c050040c0c4d00e050704403c0151500c0201d801c4203045a581c04441e4004007505260034042da0020300d608040071400b5643c040d0900c1c4004544a52035410b00c290740004081c103400302c13a032041040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 605880395 1250 605879145 605879227
    0x30d020a12050307110307030f0801050d0203060105010f270e0127020a052502090109020f0d09140a051507050a02251805060306010602010605100f021501030602 71
    0x8031084201d051160f1659a80f81c42650807180d00c500059003400000743e69010035401a10340700080c6a10303075588803c2e80e280c20507c0810360f07500c40003039403607441800100b09540c45018070800c2a0720382e1510311000c80054805910070494000102c4034000f01d80c00c1031240451000c8030718010004126041308d421120110601f8481a010b03000c80b0b41900081c1001c0c0c03050080e811180440c40c280c1d03481c01880707041c10a0843c2c825030b2080880c031a03031143c0000610a105402a900c1d00c4000240042c0b07428800554100100f1221104440010040c1640355501c4410702c00d1105460144000d001080c00391055000e466034003c0290042c00303c1403114417445640012204080604102022501003c0f044400c02c000c2540e4083e81e402c0c105c03040c0b210b11655490700800d009503001d80c22078001c2d0b40c903510182d0a991813401102e4001154008020045100f14062441044c4c140141c2d11110301c885184521480d0076001503403801d40003e1102a07100300080354642803c0b101100b2451880d00c150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 605881645 1250 605880395 605880413
    0x2306030325020d170a0f020c060906160803010e07030b03010606092106020313060f0e1504080403080304081206152a0f070f09051003290411030d020a 66
    0xc003074011160940e4400007107460705648030407069003040100c1810018010300c0022070b44202880380010700743c0c4000000d10742c00050650b40310100248014181080e00040c849260003040c0c1e80402150050001000324442100460103812452083e002914010344081c007a10000b8021034000c5c2e14028080101d5940940380360181e1f903070b00b480c0c50030b0030740454195020010034220241685100000b80903296a14000401c8131a100341800d018040401060704221400080b2000446e080b03600b107018600200c8000c103a00c030380b0070701c010307400d007900e83d1248003160300103c604440740710000910b00c2103d1140d0600c40e60241d0100d403d05103e48a110000e00e0302e014010044c000101664100e03170001031100c1101052901000454100ca001c080c030307007940c6140314480c80f11000d0b0040800300b85100e060141e14030400e001c811000d40c1a2440c2d881807040b0500010414284004100c5d4421240322400c0690007640a200b91000070100c1c4800c15042c0100c00b2181c009641c401622500003907402d10f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 605882895 1250 605881645 605881687
    0x10204030807080c1b0d1203090b0a1b02060f0c070309031b0f05190302221b0306170d1206030209040b060906060403030c1b0e091b0607051c02030d23060303 69
    0x20010380c500c020207d00a502411444400410b038601d0001000765008155211559040500201241d035044002c03041e6150801a00d11804801603031000800e040c001d440140703092031092900156240d40d82e101c25005841d100300e00d181c891030340f00c000c200301c0e0210380800c1e01a100445180e011445688030130120072180c1e1000a000782c0c0f5044e000390540c550901d11440821140d82e091059140c1d0703d4000c0803c008580340c0401180c6010b40c081155205c484854000d8032400c2c004000304c21180c88251010f6884020411905860b00342c00300050721260201c60103035100d0700107490b440c1403a0080041e0900c00411403030007034100740000c00c01301f0743c4503402d0b00401e40c0101c1e10303040039010b0300a03141100c051030300300610005054060180314a00000c00100b0000c4111280b0030040000d81005818420389101421541c407125109410303d0300c0260852109030940110391408a070741200750195181d09030100c0003007041e24025200500f030b000d8001c0d8000c004402861070001c0302c0c1d80e40d07036040405d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 605884145 1250 605882895 605882903
    0xa0510081603020c07030309090f09050a0b060402130603020702031e0d0c02030f0105041a090d0e040c11011109040b0405010f0e10050904060204060e191403010204030807080c1b0d 79
    0x10241000128041d43c1165480c1c2e83c0c500c141c5225984a04014005108901c91030710307001c6c0350550000004c400c0c2e11421280503030103c050580394805490f080c84030b44029209a03845a03080140350542e00d0114100d00042681d80c90158503803041c0e00415040c45040ca40788017540980c10308403044d5200c00700f60031100e003c00e420400e5941101d400481c0c545208040b4003034040d0710b424103200c188590b03170103088044103407881c0f543c0080da1090300b429104d043d0101d500001c2031860507008078038501600b03c103018108a1511030300c0104140c40450940320143c0b400300d5680000142c466503401d207401003903183d21054805200c0355241c00e0300c11104204e0381c8070b11016880c844000c00c4044901b0b0400c40001c020040011a083c20a8204000250310a00c100008a0490100c5010302c2c108000324500b0381c44c508240f81c58503450301c4d6164500c41114a0142c4e4155802c100c040002a0000040c0c50b0160082030700c0e80d240c60205007903070f10b030600700314140ca20a003070345505000996070711010310000c0d980 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 605885395 1250 605884145 605884171
    0x5042312070609051504020a08010c020a060513061a10031a010c05030d060b1201060201180b181002120705040f152f101112090c0604060305060a051008 67
    0xc2d080a03001410403000090aa00600481003244010303c0704076030040d80220f640d2010503640e061501c1c220707640a9014405a0403004c03520010494a5000700e600005411110702705402c00d90300c2d80c003282c1070400201c030340101e200704100041c08d0000916100d09a0b07810100a00c111600141c0c44410500d103e090402151b0344132001004014410740c0d11400402c0c1060044035124440c01c00960800340600302d0300e900840000030110310501400b01034032206086044030180a4444204002000308440885030b02041e201c0e0860100f00130749803180f28042c40060f151224141c0000d6500030142c6040104a418070081c80a8010369071200b0072115039013090302c1c990028010644000d0240c0400c0f890090090b06c807614102294007500c61003001c881c040c0d0780c103526205209001c60700030154440d00d084040c441081c0500301250001d4121816404031220300d094400002c0c0c00c1e500075049080040e48400074030405040081007840070744005c8980028038444d510000301400da00a00c4481e80985c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 605886645 1250 605885395 605885407
    0x7030b010530070501020c010903150f0e0708061015020d050c1606030e07060f09050f04020724110306060708030a1d1b06130510120f05042312 63
    0x501019403141065012202c024100074061507a91034038401d1003900d0242c0a0700d0b242d01100e61154440c0019242d21030340011400b0b08001e9048020301b8040d60030580503954104841411004000607001040c0c12001401640b9007400030700c00c40c14859120701d00740d0940c2800c10b44003a4000c2940c42c0c070b111291818075200c0e48180c0c0100c1c82c050510011190350f0110080105600707078582c000907000241c00044030040380d0b48807001c507801c03c103000e00310b4000390500c401400f4510340b01c87d10500305000103101500740611510341c00390b403484000340111501c0c41081048e61030f0301240109181e0b0070f0b0404102e4154034000e8042041403043c0ea10007441d00000000250004c0030360340c06004508548003008805030120464181c0d52548808545c100c0c1c105103503500400e02e018070031240410640328215a00301c2c0391000b4031118140c002115410320101c0301020100c0485881141702c0d5526200c000304060500d030410900310006801d11415855a12800c44403040300000d0038003d210760020041e640315 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 605887895 1250 605886645 605886679
    0xd050f0f040302090f01030302010c0206070203030105040b060d0212060312070201141b070306050703060b18010f0c06020d020a080606130e0603030d0204080309010207080a051902010c14100e07030b0105 89
    0x8441e941000791301002460078031044440d501c5405058910980081141c10074480003a82e98907400c0f0b800ca001640b08100500250500340c010103d4400082c0905003801d501708203410a0742c0007034803041c21040e042c2003004004e01d010020303040c1d010600c0c144c15142041d55000280400b102c2c11020041c654005482d9810a262444001c40003510394150340074aa16441c2c490040e105c240c070344d44006400c0c03401c0841c502c030040048813842901c1c5070070410621004801900c000c80031010f20024400740d102c130600410090700042146040c4040e00603622640c0020107000250060b0002e405502c09100301c641c1c800d640181402550852840c0f0103441e521400003921b148115070490909900203c1e001400a40002c064904088243c099a440a4441c211141d4a00e4100d001a207582c1c85201003000d090031403040b030f080b02c034010b2511281d6917140b03407038000400c408181401015400548401c1d4030348068440c88002a15410240c413400e40f0316200c00e211080103010300351103800003103901a0340c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 605889145 1250 605887895 605887897
    0x50d0506180a0f060f0503030909071e0c0c06050a1d061c150602151906031703040510050903070b18010e0a0b2a0c0c030f100e0d050f0f 60
    0x3902255200d00341450418600800361010f00c104807a11801d1a0f00884c110195610382029218040d009504103a4000104482150050090401d1010000004030300218001c0c050708030146a407590b60705541c562810070400d0724254032003003c20405018030055154000d00800490710389521a0540301c44079000550a4820300081201c20030420b614a074084c1200d42054901482c42940c2c05400d5a03115001c0c1d886545c820000d80303c606080c0b0009244103101c52900d00301a04039080041ca40f5165520620140204c81750443d59a10100400c0300308001002201c00c00040340d07400384410304112090b81d65901448c50018900921840050403644400065084810541000707004046d28660603a13142c4080e9a4142d58020043d8001105451050034042080b01d0000c640b800126041190910701d0700001447c4042d40603040c2c9004860f50b0402ca0258054804009480c032994210801d00445c1e83d000180390032500056051051305030028180d4014441003c02240c0d99a5103400301611 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 605890395 1250 605889145 605889169
    0x1012110a09060e090d0e090a090f0b0a2405010f03020f130e090604020d02090903120103060b0f0f0a050904020d060f0c0329010509040603050102030901050a1b050d0506 74
    0x844019100000c1140d682c0d04940c0440b1038820128010b030f01e0b20350000e42c550340d80e0079400020500da2800c06500d81442001a0703805250038500060740c40a990b221088100314032400e5840020350b4050140b480c20600c90320580390206d11000a40d60000034800d0140f1140c0e00c170781814040c04079807a44280b4082d40498080c005c95000075980c800568a48000304041c0e4001c2c040019248400660385d072200203810790095070010200f01000250340e007004110100108811481c1c0070500075080350f03d0110300314030b020303611481001c138803500a0000e0054110441c071045202e080c3c8089401500e8441544000039218113503034905403030303072a8008a461141c4035400186000e15000d04c4025010a5902c0a001d040055805100f11021140c00e0b544082110070240c0c4040e2121001229641c0220300805000f0405007010036540d135642c903203d017260002c0b134802c00965104d804200214403030f032080b0103040c02c54400b20384090b40c14030402800c50044011410165560390080b587d969102540c09407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 605891645 1250 605890395 605890399
    0x703260301030507060807170f04020d02031903030b060702130f0b030a060608061b0d200c1509070315110d0f090303060f050f010c082203030f0206101211 68
    0x9581e5949180c0580c2d41d0b0b0341846170f140001c40f0b034001309540e00d125182100421141d89590390300394854200301210910044c100b2a03000b01c41d10051001038400b40310b41c000c07251402d44001e21559103402d000c0c065989510f5024420442040001c0042c1d4811401150781e850b50000003030390030f80c1709612400600c01c550b000ca50604ca00701c0c8610810203550400380603155088243c3e03c0603107850b0b500100440200041d20300c01c0106120808054100b40d1098296440020000010090003c0740801341d44c44017082c00e038140c110900c00403201d2070f60203007143c100300500000c00c8000c1c0f5680341c3c184080c01e6155844101e61301d440d0010340d82c03000700b815542d940c00e8070303201008000303a00c0c0c5001004116001d022804241040000201c040d110303840101214400b130300b15000720440c1310044500e4072081c40700b250320b00c038207200301d2024100d80c00880d0b025000c90b040a041041c15828007a002c3c80d500c0907c401150310907000c010b13034003d000c881041161203140c2c1c460307194401490200900001920003035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 605892895 1250 605891645 605891647
    0x1305160c0c0b0708071103030f091905040204090e12030601090e1302030706110615030d0302090d0b0411090c070f020f01110d050d0605010e0604030f1403210a0905070326 75
    0x1488030404c0203101c2da5102d4201142008070740c1050607240c0c0290f03540b210b0911820b01210711203003001c02900b2100308415803800e10960b00d0350006001ca03000794029490703650381d9512640c41003404010710403c0c10f80c10308006007145420b200007031020985000381d0050510703440c085110380c2c03842844185155030003029240040e40700c3e135000b42400300d04030703500700030780709071030100d5008080e860582003c0f1101501410060f000304c0400d4000e5030001e800203130001d02c44580314001c5401005035502070b84c4a03002c04200207050100300201e00030043d08440c5c0400d01007001c1000600101000070b446030303041e01c00c0b840a8200780d006840f5180d40b0700c0700c3c071468001c80818910040c0e0180c0104078016903ca000c02050f5290401100c0301d400d0444036a400160401040c4045080114610881c41c41081160919806440003078110f41007400201200c1c040780d00c40c01c001c59071400409601c80a001410403e902980d00d03100c0c2d8444491002034516004a028005d8884944080080384800481c4071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 605894145 1250 605892895 605892907
    0x4603030209010e12061506040522200a03051306020a09030b1605180319050102040303090515120402032401030611090102030a030b0109050d111305160c0c0b 69
    0x19020794001201c06000841d600c0c4696401d1801030120781c16240b024004100039545c0c00503a807044503410001d51303803041c0c0a10000405542c1c41000b402400910741070b514101c3c040960f940180c0f181c4400c01002c600380111425032042c4102c060750a9080340740b5001c1159210003080408000c200382000d4041800010346180c4d46030440d00b0101224451081440c01d5503500815403542804080d150001420403c45402508803000d40a8100d45005050320030100329500560001076440310100c4899402160400500da081030350240241426a160b000703540d00503d840d200742c070403813030071005290310180420b0940d281000070201b80c030142d81058810070030221030600d802c40c00f40f00c02c403411800e0814582288044074140c0f00c43e00e4060b0011810b1100c9404180d0280140048450420041c008009041c0d986c2540c868101ca0040c0c200056841d45101803041e0200341041c2451041e0608090201c80105001424004006441c1084c0700a840e03142907000310f9200d6201c01d00914002c100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 605895395 1250 605894145 605894147
    0xc060a140d110304022b111206010303020d020721080706450b07080c0d0204120303140108031605070509070305181501030201030c0e0a0b0408010b034603 68
    0x56004900880c0c18500300600c4000b81b40144801242001c0500da0030201d84000039528061082100300c0145440e0003860b092400514080c0243d005500680c0100d5106402c1d80c2c0601c40c000c05801548950060442650002c0396150000e000081500c1c3d00010310400340900d07680802821100c0300c100e20703940c007401e4144082c216522520b102c42c00541010000c503450340405402501a440f0510480c5555036520540303101400500b04003604408020380000d043d0a440240003411085101802c000d6050070024203c0d19402c6283c00200d00724001403000345000415100f40000c4114501406221454030358100ba2459101740e40042c40b000c18004060f400d900b088d841068010110301e4040d1800c1c049a503100460010f6100d42041c800040c0f015503c207130403000218000d030900801c400d0041001c5841e40351660301c030f01d50040010030309100501c028040e80710600344c00c4004001003082840442c103001007085891182c08042c0d000e0022866002c641c8000030f143da00740b880c14003c02818 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 605896645 1250 605895395 605895397
    0x3090a080304050102010606090f151205131101020a15020a0c0c03050c040b030625051209060105040627090303090f060b0a1205030901030b2803140c060a140d11 71
    0x1483c2c2c055420154080380c4248210400e008407485200d82040c0140780c4100e000c03d030300000b0300c01c80c1000982a1903034448621400307001d01400c2039103007c02500381c07075081802c00c002100c641fa50454010050000c08034100941e810811361180400590740c0320061025a00105000002825402466400801d01c035000c1154002c034a01a502842031404d40c1040644502e41140c484c5c54a19403c4002540c410010010786000c61050400c986086c0c40da10700e54031092000c50310a21158401c43c010f115500341405039030004d01809610b00c0c0c3c040c8041c004541220700c12100d21004607030303d220031014541310f600310300c01617504459030601d03e1055092210141c0050b0300b0140c050840b81750006103420020b000c040c1c01a401c040518201a00c650044014041c0000c40e2030384244501541f521542e8405802e2035810208091045414039514041c00500c020f0784c0705014a03000100f6000303ca40ba41400c0b601002c0c4030703182044509280595401d0cc60240880c1d182000d85803800140350f04003684 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 605897895 1250 605896645 605896649
    0xf030809161706060303160602030622091101051e031e270c0109030f0c05040e0c0a0503011b050d06120f0b0f070504140103060833012603090a080304 66
    0x2d0560700a039850009040d80c074859549000c110300814000c6501081a40d4040d50b00b014004095206188035140c4807a22003003200c0d211103140f507880592204114689000801070202820304a041000c512019008000c0c00c400083d41050f000000500060035030103c60b17240c801000c07507080c081c10311142c01c4001001da1020205c581c1001c03108a490914006050f5003a400141d64031280d050856030355800c1d00c41030a00c1240c08500f80c41c000306d5541c1c1d603401110304000a1200601c0c44698030010032202c3c1074254030440c0264900328200320044035003007131186181541e081460350381c8a034500400041c0010350181400c4440c0e004240e04002d180c0c184004120300800a044458441003145582400152501008500c0402c0108817650301c62541c40c120210505000402c2c1c3e6440d1017003070424460410403010300c0005080c2c800300410000c0746407405080340340f1840b03456040c004101300403015114002c13624481d25201c036240741410012100c68001c06041c24000ca076891500c20b42d02d030028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 605899145 1250 605897895 605897939
    0x7020105100906230315040303020d181a041412040f090c020607031112040b0f090f0d120608160305010b0d02030a29010806060109120f03080916 64
    0x940780091034455501661065400200148503504020840c10b000015008206a00340c001c07403444208a008800109104600a441c096036a040d50750741c901c1107801a0800c4400d400000c0b07000c03400314509000c200c05043c042c1c6007202054499051100c003202c9068080101c0b4031603550800c1808180002400072950b0210300203050039211031050742503822005649005a00446c0024050b9100b904007424050f0b407a06807031b2900104080c124a005400c8406843d42c8464034144062040c6e0300341c02c10790042d00d04000e030001c071003041d23203958507040e2624902080041a009078051041540c0c4542c00030074480d41101c0702840740d03541d8101170481c10300c800e035169480e11303500440d2420040da060810030381c004c010300188045660f5404c0034011000c210252003268540c6100540b0804105074080e150324001055580b80c120001013400d23440f40c1001440b40004510040014800524256034a505042650b1160347e003811161404030200e401d614088a103900004100d80c81909500c5400c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605900395 1250 605899145 605899171
    0x3030f04090b0103020406020a0b060a09020f031b040e0c070c0b041203020d02060717181e070b04060e06070f0501110703030525050f0c07030803070f0c08040512030d0507020105 78
    0xb51801507040f4002c500c504000341c0c02405102c000a5221101d69900c54801040500f035682c0340d50524040b60803e10401302c605800000780a032f2440c81048903800c00410b003014070b01d85400d000202c0366900001d42404042c050128601c0c0c1003048001024000d040c035070380115292951000311311b03500000004190094061720001d00c4626101042c1d0380d12502e60354490f1f07501c9001c440a2058004130003002030400c0710700030020b022691028880000b840d040740d03005099500801442c0e505210407640040302140c1c00308001c009d1250020002400c0c032400300c1d909521141d0606100fa950080c000c0d0050403546020401d0382244001000341869500a80e000c000f241d40d0088443c0b11400b41035040031049040f40c409100e42c2d0310440003080d0b450601c08100e0304020241c3c10391440e10003160001c96019001104001202d0740c4040c40f100300c0303065450304010b0800907860b4450103201e1401002d0146600310f041042503507081007150205d981800c003c12803442e210310004d0007014140c82d88002201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605901645 1250 605900395 605900411
    0xc0604230a0302061b0c0601080f1606090603110903100f0b03010e100e0703050a03020303071d0a030204051e01030b09060115090e06130905010605010210140402040504030e03030f0409 81
    0xc4005448240c640c0e01d6002440b05803182900c50310003100e0b90000d091061020010500040024021a8001e00a1400a060590804010b40c0c2401d510b20680400e080d5050030400c40c1d0740e071211401c0300321400c0b4140044d8281e0040c6c038a01c03ca00c01e54001c65054400d84444003450019944200c480d408451000c00c08850500100b40c00c0e98010a082e0b88a507102d18101032a894135a8030261000c034400c41190445540c0e655058184400f034641600941c201104103c40c10380c0042d03101000103030210107070f030200065500041c4003050500010380101c2d900c600142d450041030003042c0020b819074412072915a17491a010900300d0f0f040711046254024800000390140e0400001024a005da440f00c5000500341710039407295400040041d6803083c07600381c0c00c01d14481103215051401cac1c021800421034508060000e440d12504141ca0049a80b4140700704500100c82c07020307030303820943c11540881c0c20b0311a4201201c0b848404480365905010010f0b80b01c144601c204014030032901e01001c1400a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605902895 1250 605901645 605901713
    0x2060708400b1c09050d0c030e0d02011205101802180102150406050402010e09070302090f03120a0e040207120206070906140708091305070e0a0f030309051201020c0604 74
    0xc9038911036200040400c3c005198a00d482c055181a1040b40040015400c4440e4940300e02d03140030030b01d2840110711520307403100500d544484035101d41034040c3c0c2c20b80ca412640d85d00091035422140785056a180d80c1d6801308409590300460311000700015039050515011014a6078004c0d8015002100462454200c2d10300c20750011070410792440071124810780555964903a00e0140800030070484c10040d0306032180641c0d0b95002c03035040c000d01c403030303070340141c131082103030288119404403201491095108108800624000034200d4801402607d420384481d2112404107010b805400030082c20360000f8001c6000a40d400500345100d21083e50b110242c10ba608d0350281d84844d4000d1000ea285c3c0020410400451803036001001280d40c00741c03110fa400741c26035642404458040c0c500b0b800080e180e41940300c603031030000424400b80003002c04900c0369615690703020b0190405441543e0040b449600d01003441102035040d190010380c1d074001e490943c505482c00040c101c0d588902c0000c800402203c00d0510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605904145 1250 605902895 605903017
    0xe1201051e16020a080c070f030303091a15040f0902090a02370e031e060709050102013b070311120a030f05030c07050109050309100503040f02060708 66
    0x1000c9a801130080700d40103032034080c034982c054126804030744a100c8001848800c106d03c5803001318040e940008030001186885030369500b00b40101800307130680030300340b10601c041d403561288103140880e400102510302c00c0d9481c2c0034101c0310340041d6012004034204000300b0802e0300242072002c081105c80142032555422024411901400340d403040e21031848058046002b014050301b40c9030700500702c80014000a8042e43d08504014030750000703411010a202c01c0d40c2e000380200c00a01024002804411a00580c28940d204c14422480380b0700c070542400003548c110045110307004d41411341628040342d10383c00d14100c0c40c0f143c003055501030108440401c0c46400b022441d010701541c9036541c04600c0142010454980d00302a0000302861030800c28440092402d20840303a009104001864440080780c007042103d03044942c0039810701000b001013000140e80c03c48031401c0c2560448400e601d84440341041040c034014216500c1c10101c06040410300240d2032152101a00c0c0000b07000c14160f111790841c1421 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605905395 1250 605904145 605904181
    0x70b090c0108130803040804150914031506132915030c121009060f050406120b010e070527150c07210209131704050d030e1201051e 58
    0xc9110154031000003135420b10095401ca0301404502d803d05d6150503540003050403040c2904081811a1410008103514005504802d03504030042e00e814503a19030482260b010040c2070a200d040d040810300c08060740c075440078146903044042c104410041822401c0c003821f9038064584200003050110140321500720881c3c0c8110fa522000034203007000800d5034420458050128203c6103d150008100380085209040040005040d02111513113410244022260a43c200f004c0c0311405440c800c1c086609080c8a904650551160655030780e103e41d001ca40030b0043c00140c03005083c00b103c4280348a101c451400001e50001c451a14108102c00c0c0c40301054416082000c0c459000044200001c5841111101e0b0302d654445881c1c61503005580042e440314002c590000c450b203114000d90080c410f00c00d081009a403140f2801c00d240c40c0c00c185c00103a400c0c068050081c01c00c2000984e03403050b40c030340140b071100c0c1c0d046203c000e01182c184084001e40d00c280c0406000d0894840b2400900405680c3c502201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605906645 1250 605905395 605905411
    0x3020607030302070c0e0907030b06040b030c0112091e11010c030f0c0201050706050a05010806070c0c2303060106050c0c0402040f03080903070e010906180b010f051c02070b090c0108 80
    0x4a0903015540940c082e401c419416580e401c2d00c00000550f50400800d20780c0324480314400381841c10700310701d00500ca400000d030016015515106a008041c2c80c0014494000070090070004582d102d4001c1c5039005c0e00c02070724001d00d502c141c0c640000c841c043e5400719850562042c1c0d40c0002810b205001140c408080e440060009100c000d0100707010740c005c0342e03107030501030040c5400340c5028403036140e45050720403e8a40c4494075941d00300400c094a400c0c01480d0b000350b02031402c06a014000d4540498900050044082c82c80806225905400b00c400c00040d0040300074041e50640c0d81d440c400a4016000500843c0150040c0740d0885031510b040d1080750280c13030118401c0c038120360850326010700301d800100c0c50a4044c446c1242c04101d40f450400410700030540800040703240703810440c0404d244480c800c28125aa82445a94209030b0b030000f01d54005400140390942e154011111103c14a4221903483c8400c5407000030400c041c8000ca0032001e1040100d82c0031240080150801100c0011007240c3c016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605907895 1250 605906645 605906647
    0xf07050c040e1506060306040207061a0108070f0c030e010302040801093512073c030903170423010b0a080f0a080906070c12050f0105011512020f0310180501030206 72
    0x500746185c048081c0d43c000b0005800141020420798443d02164081c1051404060f00c03046641c0c650b41e400b084050f0f1140003490006943c40e038690b40a0181c0003041030090602010b40c00c649030b11391081d0705171130050124a00921210017181042c103c445a4603004803003088844448101075600121014203100142001c00d01c1d09556606140d485800030b4060070800c002144003d10265410050480480074041801000c00c80d95070510803040c0c000c0c1006052504080a5a01090300003901a04801d2203040c0c1200711b60f50b03450082c000140d1801400010404440f14114210f41580003203894201502c8104d00a616048181d03511100c00c60b4101c5a81e00508220000070148800f500d0300341030142050b070800341550f07500801c507500b640021500e901506032000c10f009003003000c1c1001c400400000c010344d50401c8900840d040e003411004090216042c15501c010060351b0407101c0081c107022001e41c40c0e0910541c9040031000c0c81c802c10700a21381c0706459041500c024803405040ba603000f0005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605909145 1250 605907895 605907901
    0x140a030201050903240910090305041413060605300c0a030e010c08071b0b06010c030203040b040b130803121503100e01021b0a120c080f07050c040e15 66
    0x11280740d4030003504260136000e03007801c04c2a60440c2140c13101940840c0c4009904528111041a00d020b0440043c41c1c030041c10581d044003c40d8000c81190151601c4008100180c544030010400c1410502d04081502e0726050002500c140e00102500907003c04603840004000c007403412080b440c0c0381c004c11024895024004c19031070340310200108030a802c82e082c0172a0840b00760700400c0c00c464042e4035070404110040304000059910044690341d0942948078110041d45640b201c0c4547e0388000d01445c14001c54180000c1814000c0056034000c04035104d070940d544d82c40fa00c41c42d08039000f601c3ea1060891029202141c03000b00441910000c0c1000c1c001210309586100c0031040c080e001458440d05800b4200c02c803014810310307000f1308103540c0a513400907035188026487d48000e1380503078802a19940198204e41c000403480300210113500000d01e0405221401801c000b1b11612808410318105d4400140c01010094040303115400900304480800014071003500381921200f00323049805a0768015000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605910395 1250 605909145 605909147
    0x5030108060c0c070b0a050a20100e031b01090b01060c032a02123d0b0103140f0a050f060904060c030f090606170705090406020a140d050709140a030201 67
    0x2601400d642c03001180c4136241e5400b0080c506611580d0360740e0000b58001303107681c0a6900002c104000d110f5a0f40c00c2c03800c2c40107901e4501c0e140c00d21000e0500c031039a100c4c4d4603682004c50400568021034801c4817244603121140841c10b0003007800c01e40c2255204d05003400007503d20f0040c200410015010307242c01d110120b080c00b11500742800314200241c4880e084c13031054096199203605c03e00d420b0002009015800540004d86800c40c0710390224000041e0341000a240d00c20312007010006081c4c03401d004294182d0030401038018010302200c014070400c0c15820041400c100044081c041c1d068090104010b8581001d070071840a42107604030f4001400c1004900020b0321580040c009603094030740040e203d804001c0b82411780360640d01c01d940395620b0344424081c00b41c038942c81b503940051314030042c440d0916040102d810b202c00108080c00309a070109994400d140901c0d03081d05c28404400ca0107071742e0740d4071099110041c00251210030000b401113402081d40800c01018911201c401842036094500d03541c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605911645 1250 605910395 605910397
    0x3040306090f0605090607080c040b1e07060c020a0b0601020106120320030a020714060304020a120507080a06020c0124051e30010510090216051606020d05030108060c 73
    0x4110b900c0c82c032000003032021504500c2028002d0181502900f41420716900003810340d0405446054240001c010030420202e1280449003420300d00d2a841a210300700300031a8404d070142c4440548650f0400004030051a03020407411080d40c071a042496072074403458012400c854050259090b168003146180380443d020b8001781c04034100118420f81c3d1031400c1c407845c50454100407464030160b03006030300070300c26031403042c815542d20790058a11504501d42134002452000e150310448000449600d075184c14007106010f10000b0704010412240081c50b05d00e0300b60000c4d8042c092410301940790070070340700c540e1a910381c020b1483c2090380324050b18542058104a0290605040d040701d6400c03011080e222515800100f0490a8410350188a566510340d43c0d403688030000c9400300d240b80d141070108050004d0703564000e000c6c3c5001100040e00c41844caa0700d005400795031800900035204034000303450654640d420b076005a85855007510006c41c0005025140380c0020f018411140e0418070000b6101c0360f680c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605912895 1250 605911645 605911661
    0x150e1803030705310807050301091502070302030403080a0503010e060910031502131d070512130812040c091b0503181c090609060f0507020d24020912010203070203040306 75
    0x26800c914250a50403045407200d4444c003800308035136640604000710745050002c07000805c01603000b030141c00c42d242e8503030040003511040079400300c2e404602002498420020f89006e1544041c0466a600090801403c1500700f441140042500d81d0005461402d2a60449028001d0383d840358055508594581200c85a00d4404246141d42841341a924a00f0b24544100811a000218803584400300d403000703500e80c000f40514144041000303c6c0c920307807a003c0e580e40d1340480035105090b002645468074812a100c2c0510040e494019613040c0070502103103210b54821515000c50030890388c40da00340c454082c0800c0100c480c02040e820300002e07080882d4480200310300d98110080d600c0c0241142c0c8003210104100714428002903000100340000c07034014803490b010f0b2010b0309041c080c45000c40c030000c0c0325100f44140280a0b00c1c0d456100000c1250f0b03042001d100c00041070024503c0408900b00030001e4008440c1c0d280310700d02c0139a04100500042c402c4038040c08140d800b0b0351529055807503c070094400a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605914145 1250 605912895 605912917
    0x50d0504061806020c0c0306160f0c0b01080610080613031b020d150f0506060706020d0b06040602010e01060e220816060b0f0a0e07030b03070504150e1803030705 71
    0x1405005190301000e4a0340c03000b4900c90b150040c0c40f6800c94005601e4002684010b50213030b403000c41403220380344c8116280707030051003a890201c20440c208582110341a8400200600d6490a0000881d1035840481c00c14812241d901da01030034203a0781c024060707540a0588103140c1011400c54560007003486001c4103403000803507000c40104200c4603070105d00c0c1101900400d658420803200004c130b60018038082c10848921008041c401818004c000920f80e10070030328010f2895500158120350400c2036001070b203eaa40c018071058840c1c4d41c0710000307406020a2604000c0359403030808049603108440401500a929014203059000080803001007403d08202c01074400080c14040f0710395011190f04084c5c521880ac09001c218052000140800d10004c4d0700358130b205d40c0702c019040c06200c01030348010f640300c0f20901c6c02107094040000803070b0821aa0382c000c0790700f060500261413250000300100f40e08982c2424200d41b515070700e5014002640d428400f9440031500100045295144268050000c040d24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605915395 1250 605914145 605914151
    0xa0b04051c02030703060506011b02010801090b031606090f0801020f030c0f040803072126220602031006050307020a0f1a090c0a091103130512030a0203090601090903050d050406 78
    0xc90b40020385400003981c000c840b1340b901c17a01000403a5134424140c0000007414040d200c0b0200780c40d030018003200014050f416089544400701d00c4c140c1c0d400c01c8180c048331864290141e440c0c0d19510000d040381c40a01803601103410192001540250503c00c07211841400d8035034600315103400718a42e205501400c098480c0751020b00c00801c441c3d0062009101541c4104841038403104421035500b840d81054080d82d05225011910440d80e040d031100d15210388040030340e4140140d84030030054503010120442444040e025200c900c0401405500542c040d8a00034144000342c1e1362920304031070f14030007250b0660041c1c00603d6600000b03000070142a15041c403d0000d0040120342240c0b44444501c100c038814200e40c0304c082000468100710756008050310982c035060088045813485002c10744000307000700301503c11410030032003440300c14840785022004090400382c0e241000704500c0c01a420640b0a0516402440000500d011143c42000b140035850346070141000c80280c070b0311004000c0100150380f8035071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605916645 1250 605915395 605915449
    0x311010302040f1401020c09060315060a0b04030b0603151603020a12051906090b06071410020705030a090501020a1a070e03070f0810064a060f0a0b0405 67
    0x150001c0301001d0120600303103460321364004000901c1c00180e941214021003c20060010549004c030b1750f6000c2490202c1c10401644800e000310740b80361007691100895070001b1501000700102e0f000c000b400340385d08500320350504000c0c9440180803142500c018103000c9a4170449125180250046e150304501c500f094034014121f804003c09550b030403111802c034116154030b60b000961840c40351902820010400700000c243c8034010984d20300c582c04004c2c0c01d182c440740c0030b80e0ba0f8540820046010140c0c100f010354860a6038a03080da42c9400c13000c0641c01084002001040b15403001403622200c40d00882040450781103040f00f14041c0c1005032614081000c4c190900700707a52000c0221780001c161500c4e03000d0005241c4181e542c24003403550001440c3c9410100d0400c00385c6000351506110064840ea2050010300300d00c04a00c2400762500302100c1c2008100e83d280740c07076182a0b0740e217105040903108a20f0341800c9604101d500e401c28015005420410b11041c0818142020b00c05086034038242c0c030b80b032808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605917895 1250 605916645 605916659
    0xb0a0f05071709070f05060906070203010c2c03150406090c031506140f0f22051b091e150c030d06120803060d020a0e0f07030c020c0a031101030204 65
    0x604100c07064004210201c81c032100b842800c803600d0340e1000381c10700a4818517042503045802c0661070f1285c681700d1580420002613513501c0741d00710303454954010020001200c81d40400b9151090030303403c10300a41408030900c0300b06002c0030110340722510020042c20701840b5003040054580f002400541d103840c0d5074a0039400040443d003c040240d402001c41d18002100c024050090300c210f82c0040038010003203d2004480c1c2c4940d0134054070344408a643c41d01e001e1700c41c80451602d405042c0c1c40c640ca2030300c0840492210380381d94000b03070042907140050300400303005915007002d07072040d80102070308680d110030b10207104000190905207040e0010580c4807484d844040041d0b8503003000c039401a00780c0000034808001c01c01c030300c294001440700b9200340c9560710503601c40c030f0b40b02d0100502850003a0282c0c2046400c641d41e0741c445d82c3c05000c00c1580000d80381007581400d084070104031422000b03e80740903520701c0514000540d24500d6000244009110b90031a80d81715000c01600103000d05250f001d010200741c1d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605919145 1250 605917895 605917901
    0x210301061409030d0c0203070602010c0c3306030b0714091e0d0c0905220b0702031b0615040e07051302090406121104050c0d0209010e130606080a02040807030b0a0f 72
    0x3c1c1c20582d02c01700140701c140101810b0102d5035010f03100707580c5080807a40466821821304030342c05800031200000328484d003061555691083d01c1628800d600301c259010000407036801801030b240110b040444640d5444020384d40030010061200103e00140449203031480e044403102e1b450f000f107080c2061013030b46090208011a0781a4000c40d07502d000404148103001040c49032a5200c100c41c0e03041003610f121200c48601e41a03d0400280031a01c09400103801d41b8020400c44a45401c2d5400c40804107800721902615050b042d0f07030b18807108040c90110503052415000e00805050307818040c14200745020200940300c00c001c1c441100082d003d010360740e041c5e9254460783c001801400b041d40c500d40458079140d404440c44102682c89507281c070052000283d81c61081e202d1000c10b4a0f40141c1c0c40403400c006aa4400c06c10b250140c0c0304030110050715038148143c1084c0200c1c0d0843d2504551a110b4000410a034000c500030111250b00050741040071661000c91140c10402080001414081074403c600903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605920395 1250 605919145 605919163
    0x30f030d090203011802090f04170316021011191803060504030206090d02070302010f0c0209100f080c130c090b03090102042303120c100e01050402010221030106140903 74
    0x18565268030704420750500f030141c00307050140c2200e0200030307407010383c00506140c7c0081e100302402001980020f08010b5086000742400c004041055100d00d0a0541c024441221111180c014080c40711368842a02c04c60058292105030036000c5810310180c000318050404d0f180000004100801c1d250f041b16041d03441c9080b0185010f0034020075546800d04000c0e01c0d100e80540304004551050100344441a4042001d000ba21b0b42480d01400c00d1100c1841101c07840d0702001c0c042d52140030b5030144144c3c01d059009032412206005040d030b00c1d0315914046507071580b0654001d46c4d0808281c010044401c0c0b081e41c440c140a03182e07400d0010101d0344400c4401e44640003110600740a030340c002010310028180400c40512000c002200700c0110561402090301c0b807818142c5050b0512010a030020711007010711182c02044510781c4100000c00604d03c40a01814081e2000e0303000d400f843c101c101d9001d034a840c20f0850b154021075002d1450340b13400b1007110080a40512008410428407030342c0240e650a00400324 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605921645 1250 605920395 605920417
    0x10f0212030a1d1605060a030905030d09051e15070315060f020106050916031a06070302061006091a03040c09050c03060f0a050109090b040f0c20030a0c060b030f03 72
    0x198550f0010710a20704001c91001200b0359500c84213041d80056a24520002940d80648403d9224400d0f101e041d405081c801000400c0d501011607144108007040d40701a00040c01031003212190901c404010344006030280c180911034001814030307400c99114400d015084441854002480b100726460000c080381d00d900448006140c29040d102020303030901a0b44046c05045402000506100705c2d400c07041c0b11a140c50206141e00c0e960794031040040c0008070310031644054030702941e40f2000d240003529051304807001c012400c0b0742000840c2e814070458460301954260707624041114a00c0e819000140c100600840300d4150145c07021030a10002c1c045e40b0700440d00107030015100c0c00c0010402101d0001115a203000e481a4403040007581e0388040e400c1d080302c20600c000103038041c085007ca4081c01904d05032054803401c0107103054807150b2207441e0b070048a07041c800c142c00301e1200300007003904c1c0c0c81101e0303038400060a800302004c0401c45550256003540c000400300c1e0132900f410400d0078110f410a400181d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605922895 1250 605921645 605921651
    0x120703050127020d111f1709061f1a0307020606010e030c011805090c0714010c02060610030207120e1003060305031b1002070f02040c030902030c010f0212030a 70
    0x41010034011120b01520b040c000410111061280003804042e01034040c1c4102d424848602c18040e1041c5092103c100180403850005515a1688618030080c50400001010030f0783d000700f44c944d1a03035814014003400000d0700d01502d4042c98050891842d41d0000d200800c1d102c4009810324204034880141242d188a0540b6807804082c06420300c8001010541449002000f010283c0c2d00032840440891003400c1826524810301e82060784440c16030041500902c8203000d2096160044014000540c071641102e0201e443c80301c1d01ca4203951128000d11b000d80e002c080442c1143c40d01072801d880100852074018104005030b00c501c00d0b066090480180441c8400070a485c181c141706c5040701052049040030f200d040d00d10741c0c803a9502e1241140b4007040c21514003001941403410320001004100700c7c8400d64640300c03213080940d81d20801c04c804030301c540e16200c18030000d64043d004042c01241c00074050700c3d4040b8024010341e030252a03111b601d01107000b24440c8000702c1d620391010318060301500d1000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605924145 1250 605922895 605922899
    0x7031103030f1510270911040311060c190303020c03070c03150c02100c020a05150106030501301b0303080f090304151101022709010609050319111207 66
    0x600300764200c003521a80a0911301c007103402000d400c801e00c2409280408040c89210a0600d011004840550818159036041c80710b58481c0c00310b00b40146c0260380c06008040780c51261031081144501c07a446080f4425048400c0e802c0b404a03005400701e00c1d060190901500e0030f01d07221140360465101c0002203680381c00958040c028041c19140d042c82e045d80502042000c6c85806c00c02a50b0380b00c001070551820b40d211480c50741918400d100303440b00306500200b03e804444e885032042d44010024011140040d2034440000b03013030b80081714107140e8984807600780014800c4100b0101c503d6806e40b217003600c00320b48511541d02c0c4181c4000c6448000c43c0a55035020301420304511001d882c1030041e01c0c0803081e60040c402400b1a070040c4441c1c0b4412800e6090080258140f0b19101d40680942c14511014445040c2c01809a5101041c104528101140c14070540d03a2200000d451440d01401071980503400303001c41582404024030b0042010b4040da0203101d82c03415000009809400701030361111150491542 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605925395 1250 605924145 605924161
    0x6010602070b0c0c120f07051e0d080903010207030f030f111c09080c0a1704080c06030a060b031303110604030e06070c080a05031207020706020d050703110106090b0a060206040f0807031103030f 85
    0x204c0e40203404100d540f02600411019126109ca09610704d00340300d4651075900381d042207003000c100c80340210090000d54072a0990300700940209500303400900484d0602800e0070710300740288244840040358a48440c00e140400b500c0401c2070074514041c0c0c0c1c54655400c01480800d4008014094400c80c4800900c001000c074a01000c0c040300c1c072501c045c42108140014042610b01040c40901e039034080ea8400d889559266001e4080c1106510090f100c0d6000014080c6032440c81d5002031505000791550205114000942640d40c20110b402900107180c03148a4070070361401070000e00b100e038011001841d42c98bc807500440d043c02e4402408035001c0c0d20016035000303244001501c17580d014a06001030220320b03242180103510350111350030b100c080003000213458003014011840824641204402000059110850340c0c0c02042440105172180401c8400020710ba84000b419500c15580155000114040d43c0d0361301c00d142d00501803c07014007514581001c44a80200007940c4038004c10f5489410301d0800c282 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605926645 1250 605925395 605925403
    0xc010e010f180b0a2310030b0c12070806060d0e0d030608072d030b070207030530181305060a0906060c030e0121050f0906010602070b0c0c120f 63
    0x5041000619811482d00200703480049882c0e0005004501188008007a810008101d103161030300142c04c0f22500900c19000030110180040e40e01c10700c41e40d032094403031007a408924060191034036881103103070000540d800c0c4146003a035008500549010b080c50318041800b4240c2c0c00501e0000035542c404218081c0080c0d01d40240310081410101a140c490308100900001c105001140c4070800440040f4064454030b9414001c001c2d600500c59103042d041800000392940176510040c1c0705807203000c42602503101340e540050390328403180380810700c1c6550a20030007809800111460001402c000301000d11a11400714203210004100c900080900e003980400c90000315a8202c0c018203031030000c051089903040300d400c0100d07030307010f062440c1600f500c840100c07070442d400c2083c401803490210081c2d8045803940c026a00810902030158060342d01d031056255114000d00c02c280040e8046001005030f80c085000401190740d400d020740d040c1602410104019a190310f025881036401040c0d01c9401d088280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605927895 1250 605926645 605926661
    0x7031e0204030605060f01181e03060612030f03180311030c0319090f031a060a15030e011b17040303060f030c0e1f051905030607180806010602070e0702030c010e010f 73
    0x420315224004c0c400310440b0041d02305001b500260102e056080102c00405189000250341c010818022551035070303001206116558002c0f0040342140c2080d0106600078000c1c1d074614001010307080c084086607141280e111402e00d130150241d000c00c1048000e840401e100401400c900d0200045090740400e8000340440300d1a8031110382c059840c90103100282c2940d191441c983e040002c1b041d20364684034002036005640d607100c2c0f000d030044031508400a5805410010908249000802144400d480c44c03049200302c3c00210000a0340391861000c12284c10382500781c0140c000c0c580050090745480740c03400c85e0056500b040e1401d1201440800101e0b128104903513220105606020607a00c00b0241109003214038021b8038403071039401865000240d140d0741d010f4001c0c040181202e0003820580006000001d8030f04020201e60403191011601c40800500503040361016070040041c0c0b4602004464014005840303a41180002c00050608001c03d010784401120b84000000305141e901c1003400881d2222 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605929145 1250 605927895 605927897
    0x7031202161410030f05040506101a0304080f16030e090106050c0604020f0d1a090c060a120902042c0c0d05120a170c0706110c0607031e0204030605060f01 68
    0xc0c4006000c003940035204000c0e076042c250b50f203640c100403035103058014240485003880c03c14544000c0006001c00010040c2c040c0c1c04d41c132510943c0b01d45078001c0d041c4c3d081000c00c684034001010008980080d4401005014240707441c00b125050012248801e0760000000b00147d0000f911042c41038418a40f81e00018010541428018548807107030003210341b03039035000384068403a003850a00c9007004e4036540115110f040c0d04c4074100c2d02a0320910b9100c0c0d01140d084e14006800c0c030a07208082224100b610450301d0118140e25500054655010050b02600482034100c0e00309454802e80c01a0800c00c104c40664a281088011002ca0300004060702d0005584580380c4100000c28203c00814008221203e1040070790856682d00e0704040d205903042400c82c1c80307540b55025400100980144901e02a20056100d42010300c44029130003103040203406000b600390b2464200304003003a401406540004d045402d1fa00d8072090f40e60900c07550600300e80040d030056441c0c548034010000c00b1716028030511800002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605930395 1250 605929145 605929183
    0x7050403032a0f0302030c030f0d0c0e0315091c020c03060901050c0403081803120415080c0f1812100516020a080d1806140709031113020c07031202 65
    0x100000000080c5011000c0c040000f080d000c801414401c2c403c4800c1000000101e07590f461185400310003e51005e00e544a40b5403074101c0e8003004911645c90a528440018000c00c284001c00c0d54413049044094900407881c07141c0707070500041c580c6e980c0d2071125084198001c1d24280b01c6a40506081100007880c901c51070745010700b00712000003040265010341390004149902e646a1000c040e10344142c819005a00d44075070a000e44000d424070b401041941c1c070421021134060008201911145030a641e44c0d184c1440511000140c007540c0b0000c3c2c002d6843c0a40103800c880d03004004110403c408009280d419044100d0782a01a410f80c0585900424000f500c0b007001c241c92100292144408900141620300026503030004060941010400011001c410807500210346030020041c01c0041c49419400b05410018403c540601540c0d0100d0b504a407101400d41c2042040200108410903003c8146a0a0000107402c2c00700f00619005148181c40c4c401120072821006031070b0000345190b6140000e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605931645 1250 605930395 605930447
    0x40516261b0405030f03030103120905060412050307150e0d05070803070c0309031e0b010803090f060309071a13170703030815060a0f0318050606190e0705040303 71
    0x40e03000c40c9154071003004040116400014003294495201e030750f001d00d9052140e8969141071384404070055040302c1c4980400314580c180b43c0426120000180306155100b07905110400240c1040101c55100030300c074a095901c0d0841c6c0f0340c6d48800c455048401806001e07a034260b001600e600800c00c07030307042c440141441d5050250507620741e041444000c207910b007004105040c0d0010540100c81c00006554402146041c0500241c40620401c030809420340710903117520000205020040215021018088c18924022000c2c000348444c80d440a0500d0950f0b00c204840000d984c4000310300b1442586004054599604042102c2c1d00d90b039100d508400d0001c141c02d03810701454080052403a045981c0f50500c028070703507200380c150051707013440a00c40b40e0440c40c0028481e15150344a0042d414065003510308200320909104180e0400d4001c5000611079440b02d00450f001d07240500b05080516000e24880c0e03240e031b071943d4805080d800103a61000c0443c40c00705081c4200b41d000744081800e0503035141443c0d0345803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605932895 1250 605931645 605931707
    0x20609071a09060d1d0c0a1a0d09081e0c070e0f15040f09150e0304061d031009030513050f060702100311040f0501110a0b0106140702040516 62
    0x1110b4000c4043c41908006644004906107810141c04126191410343e84040f40401003a1561b034031610041c0714400b480f1004c1201d8865044522122082400807402c0288109240005080041d8261000d10040c04207091044a098428443d0280c21200585175880019a079140c03c2e45a045510210301c903604001b00b81c0145403580d5441044884c200551181c140081001041044242d035485030030803c84c0800c3c020502d11584140110350750810600f4203824140307440380124082e40f800280180d60307001e07903403600560000ea4220000c007903400e800f01861041040314880399084001c510007040c104d0704032040f04407030300080030255a4149d0346c42608000405500c940707480244210f012041c020b69192095000c2440c60442c0800b01e5520340d2103554145da00c610520409001400a00b51540a000701084c2d0b40c0e0a150b00200340c2c14140d0038040309880111082c020075203008410720441c0c016079121301030b25006000a030780c0b551440144900080c0403a88000b81c0d01c440c010580e074500101c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605934145 1250 605932895 605932897
    0x609010b0607021507021507050c01030501150c03021e15070c2609090103061e090b040b0601230301090b010c05060a02130909080a0e1f1815020609071a 67
    0xd00d03411100340304903ca02201604d0f45000d01c50001c0e401c20103010b0801000b404a8008203c0b55000b2801c541e0005406401141507902c240229100c0300300001211032414010b8a104004a219006544031600340600000180790070b0500c50149500c00c0802c0701203144481e49242c0c2003109440c0107000b80c8460f4072028101801100c40301080f01e07000310078040c01301d551801e075244d00000400d61503595940c1c0c1010009422480e410341c0448944c030041007800c2801c0d1140140d00e03903004044003140c0e91740d43c441d56440003004203580e05000741c0b0107100c2c00b08001510040030800507004c01c50388a505010440d000c40303072000c110342c0c10301c9104440c0001066000603900d40c041e450503070160303030781950018001074508150301407124241054000c00030008031101030000c00940e035481b04803a15058040100c4040c040c5100c0300c000142c11000102e0900c0360760107a411003c400c1000448950710b4104c82e5080c0d41c548541c3e00140c1010040c45110380042c4001d100901c1c20aa01e0303000790011165481e91 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605935251 1106 605934145 605934157
    0x50a0201080603030913020a020f030d05010f171b210f0d0504180b0d021f0e19050402031f060c0605100e04080c16060207080609010b06 60
    0x505001003600c0301750764000c180d5501c0400b2840d286000754010b00a22045008465001101240410003064500c078100000a000c2d0716200403508480d0590b0130100c440d800700741c1d40e000d0440c8001442e15440c0341d2406e004840c1c60107640002c000620b258180e440c030792001c403401d5203200000300780e4025268040041c0e60100907020701c00c903200d01c120302501206442c7d04105800c082919801401524005402ca00d80c2c400144c00007190200c0f00f8084c88030041c2003401d20f1000642c41507000300940820340741c0c0d003000004025206000a554040c0500469010001074089000341c04501c04640c00c0c48882050a03445010040c0901080c02c0241c4216043c038004c00c0012012a4541c000c1b0364440756041c01548403540d40c40709a610404c2c08804c1c91242c5c1038a54580b0006824a900030407081d00284041d5280c1040a802c128000380201d5940c1d01d400c191104070340f034080c05c03982 = true := by decide +kernel

theorem cover : BRFrame.Cov 605755395 605935251 := by
  have h0 := BRFrame.cov_init 605755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605755395 ≤ n) (h2 : n < 605935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
