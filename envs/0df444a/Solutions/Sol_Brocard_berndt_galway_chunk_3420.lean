-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:51.925874+00:00
-- url     : https://prove2.me/submissions/8349eac4-37ee-42ff-8daf-45a5985766da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614928057 ≤ n < 615107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614929307 1250 614928057 614928071
    0x1804020c0c0a0b04170114220c060906080a09021e0103020d020313170a02071203050d0908031b12010519030501052a090109050f0a0b0408010f180804050427030f080901 74
    0x1d4000761400206a044a81048e500009a188003000c1c41d204040d00013071042c41041c0c840000401c4c03c2624480d000004002001040451015106944403940c0c001c0502d8882c10010051301c65045402c5945411315600340400000381c84e003030004500c00ca01c005a403560103059032a051582c0c0807441060f20800c03905100c40c202e00b580009810b01525404803800342c18080510301141c051080a6050b88183e0a01130068100805807000d1070054640400b0510481c900d000402d0240c0900900034140301c201e8070042015081451000d40150b200003410383c1915240c0c0c441509696050320a48413072134000d040c407005000c102c034443c101407282a5100e441c00071050700080c0000070754081c15100e846240c02c1c00356660340c1d1840c182c0c002c1a210030210303211962060b04600170003c1203503030808203080000b080349005d4400000c04009034489140c0d170410741008137001c0201102c41c4041010759804070160700203500701c080448140c0c0f295507407540d071440b43c05005142e1003014091200f00d0f814610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614930557 1250 614929307 614929331
    0x3060503030c0a062d09060b0627010c020105040905100803070305070b0f0f06040506030c130e0705060a140d021615140106090303110703061805060c1804020c0c0a0b041701 76
    0x102175204564456000b06a2459074142840102818030b94a6800340c000180380704000c0c0c0da004088000c04644405122500c08036005603094122044000c0c00940c00300030070f00c00042e050b400260403100e4007902ca1a425218480e007860350b880404c0903004258040350090410100c02c0ea072aa20045005e01800da0382444c0f0150804410050880b80c17081e07803640002504d0761000c00c519074010f03200510142d100c0d60000e000717500410940b201101d0278020080042014145802120200803480c0d0b42c0d44581400d098041025070410450081420707000c02c0100d1480105484010409010b0061110000ca401341c11108031012044408981e032403103c010040d0540185c402411280c05042510780b04004158640c05c11240d600b004101c3c5107013000101c4079076600c004c4290700d244104202d0301c81d502c8107507503020680203808042580d06149000a411420550042c240c040d40107000c40741c450400700d00003182040550001d44802c8004075040155040440c10101c0c5079410200801c90301c500c00e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614931807 1250 614930557 614930621
    0x1060f05010c0f06050c0d0f0c020319050702040203011d060a0b2d040605030103050f0604050c0f01120e06150103051501050318060103030c11091e0703060503030c0a06 74
    0x2120300da050000340761070041032015590000c0c4610340d11910400c11440e20002260f115042841c554012920b054050501c0e0b9805114504070f41100b9001103040540031081c10000030506420101002810311107000140c455001850180c00c1e1880050718030f00354440041c0740444021b01251144004260802c1032660400032515600d0b40380c400c012250301e0b81510000e005178001c00c0070a81c4080010300040041e030110245050341c0c803031b9003912000144840c2003503580303034142d401401a401c40000c80c0154602910a0802c01c44103040c424003540f04144020300b101c100094142c21a0030860030050b040e115004102d60020003403c0800c040d0a2204088600311500309039181400000000b0070f0401003008850396041035035200b1142d4540c0c4900c0d00802100303406904803419400702c03564000314500a2402d80c820200320345e402d0700c0d80225654011503e20044e00d02c005240e5149008551074506200801407054150000c0428014a15090044410b0800c0303030781c13540500080045540200d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614933057 1250 614931807 614931809
    0x30a0e030a0c03080604090c080a030806060f030f07030f141501020a030e09040204020c0610180605090609042a080709060b1b0c060301060e09010e0615070f0b01081c0201060f 77
    0x103150004c81c940d9843e012a0007800301540240a01e0362081000500d004002200040203100790380e8000f00d43c4030407041c0b01c4940a54101e00c6035030b49091000400c0c2c8001700250551061980c41e01280c14078074040071034120f410050200403e1581d002c1009408404050201d050342003e100500d08513419440061480501d0201c04c0c1c85000380c5404030302556110703010341c0c0c03150103090251840c6040888068040004034030805403401c2001c2031107004104984508400c947c409400010b6550303078a01040000c01c0d00500c211078141c4102850801c03011301c0400075a5018005c103007942a0350404002c986400d00a500903c101d0f410032405201c2c441c8050140d8100c030300c8510450300e240c580c080e04103040c0550507080907084000400000340c81c581c0315020403500c036020703a880003403a45c9800f596501100d0444500780c00c2801c13800811041e40440c001880320300c0c0140a000660b000c2952403981101c8213a21050442e440070281c40c425039020501d01908072800d0008018240c5024010241c02150f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614934307 1250 614933057 614933063
    0x10b1210060b190c14151005030d1209031e050a080f041212020409021204060e0d0917030f03010602010504030912020a0302060a0201150f09060603110403020409030c17030a0e030a0c 80
    0x41130816400300080f00058401064042094603105480706000c0d1070f110b401290200040c030120200055a0706010030703071580d01826039403552074000c80e01d040746000d4074003c20110100314540c00d22041c40e28291101c45440c10540da5120343c1c498404400a000380350140c060f07000312402030240000103643c2c088017030100301c55081c03c040000301251110000d003e1640030740c80c007500004040200a00003643c2d18030503480340f4020840f005a030f01c0c1456442c03081c0b81c02600070401038a0140030701400048091400d00300041268901445e83e00601d641d0781080e800341016070346030ba0904c010140c1240d4010301030070404a13030704a584000e0f00001c0b0419528440603014040004500154078803e41090240742c8201d883c2010f01503482ca0851a00702092043d0f85990f8549600441c1562103805900c00032101c400e1554106400c40e020032004003d0301e80c00701c0034000c440c440ea8000641000d030351182c4800344003100e0b403280340104081050741c2003140920010780003084192051600301142070381082d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614935557 1250 614934307 614934317
    0x30f062301051606050709080a050717071e031103030304030203090405060a03052e0c0c120c0c0e041a0f0f04030e060f0d060b13030f05010b1210060b19 67
    0x204000103070b44030320420440c0f00c8111008600d010503c0700c20340105016800584e900c031050345e50b44004541314580020000e0950b00180f00400c08a03941d4103000761071540600549200d650f0b5010134030081d4080b1000d103000c0384089a41001070058040d41455450400c5c0c028600c1d518250340c000b501e0f4411891070070720032960742012401c00c3d00c84900039800340d2b42c003500712441c1d8000484242d807801b060444901c80c10452070781403c0b40d14498003410303c5824541e140c0c524407078100c0d912410152444c0c50854100b0901111185c040b034084405c0500030101c0700c0c0c1d00070050a160612000620440341c21590000c0d01070140030052098100c02130303100314000d0080b50203842d140750480d402038566003a00d0b071100d00400d0801c00b4007208002010b60300403401040152a6a0726811419030003a0801484140c0400804101280e0381c0003008405601c40c00001078024010030004e0402030680354140f12a9020780c040040204240c07003000d01810010320b105080c080800c00d0003090203800d08000c2c0800c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614936807 1250 614935557 614935619
    0x140a0207151104090906050f0a23040204110a0c110312250501061d01141012020d0203010308092403130c0b07050105100626181b01030f06 61
    0x1156035083c2c0303026200402c4240070300d1a10741001c9002e010142d4140c007602e24106c000c030302034415500c80c48a104d201030700f00b200c81d40065500b44405000040c0141d81083d15100a040300320345076030007403001f200291111001e084c25810070041e00d9103282c05d294020f0340b081108072140c0c554401510850b80b4080e0b04951040c004025206508242040c0208a5800d20034080350a10b402d1040c2c0e80892110410300c2620384ea00c0320003a10f0401000c080c03d0304144c40d00e0071910058481c151152107a4500074000d860074042010800803640300364015078903d000810b48041c2d6140c9083d803800c18045028046080b808903030f160040c07520000c0d107680c41c0140c0008000c0104031426840c2c01c004c102c5c1d507402c1d40d15944103042540c064502107902170a01e038081040802d8050240d50b12441164074080000c0405104c801a103049038405090a40359035070000c0115809102000503030884e41c0c01c5280d000c42083c00b14005000da4090900c4020b64a003000e0080c06072200c041804912101c12605901031070b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614938057 1250 614936807 614936831
    0x3090f09020414060a110a0302010f0b04050609010b0f070b010e04060c0e03060718030c0b0408160b270907030c03060b0711060a20070503061b030a0e0c040906140a020715 75
    0x16209006c0785101038041d44044806060b010361040c24800c500c020280809130b050410070085801c02c65000354007011460041c0305010507034014001d240c22403140703640b5241c0c0913191901c440009030b00c0648c81018942c2000300300441c5008510f108501400c00000244441c0300003030b02c4000061040b400c11070f1288208200c040340b8000103004507040400d0600e101d894010003046540203018003209071061030602250b005445005e10212501e0302d06240c1400840f6420100d200042480d0034031810110740101c042d42d8440d681c082c02406c41b17860010b028074400d0303005403d80701107170300810207a903084c403610002c01c480311030501e07140d802141d00507070359042550240c030520744144510907031001280c1b20701072500000400360181c0354120212030b115996101d400b0000004581e0147d00e0742400c1c00070030320700c545503000440c0119840d4151034406c9070135004541140d101d19800c0e125241c48602042e10403c110708020307041480d503c03040d4903200e1152a14421b01040d13054050000da0b480586a80c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614939307 1250 614938057 614938067
    0x615050307021506041d0618070308070803060a03020901091a090108031b01060801051602060c03150d030e150403170301060f0f0c12030c021b0a060c0203100903090f09020414060a 79
    0x4440c03406c1d10303001080f6075050700c1c0e80f0345084030304000c60a03168000303e10f04d01000510b182240d5000c0b03481c0d407501c41580e40c0c521050300060071054000c20f10580102c0181c3e03603080040c0c00f0300040080010200986401000e290358820307200e90090300f141d0014071840c032003c000c45042621015654010102c665074041c0148400d902800c865480e1074103104030702890100461300b0740076550841c1d1907a140c02c61038464610054450b22503040340a0340100040c10001008642c4600034242800d84c0d50045002c2289000c4258402d101000300107014020469800c044800404911014500b9581090006000322003804018024442c0b0740c60f000d4804c904c02c0304107140407984150303950f41030064010040e000c0d003151101c800141c09200b41051b103402c0111a541d1380b28500601c00c90485140103c00d84018401c0360007030340c060040f0180d09040d00c02c07902441c80c00d43e200c0e0b900c00209900d090304401409000345c014180c00703030042104005441c806840c2d6004524119491540c8507005041554 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614940557 1250 614939307 614939321
    0x1905010e0f0609030a080319021c09020303090310020903010e0703020f01030902150a0c0309060c0203070b0c0109080301120b18061605040e070207050a06030b09041509020d06061505030702150604 86
    0x54136100c2d00e0482d004200081001c0c6000f84075600a0313425500d10525000c00364082c151030a01d4202541001554001894000600640c0094156850300341c1c43d13070110742001000c0030400070868000400d0151800c0922400f111550600302510041c3c1c11640000c0480c0d40c52031425040507103503a07452040d50f40c2c00300ba420781c1030060410315548821802c000780050900320803d5000c5610f0100c0010246d008403880e03100607034018081d0030120b0030031000e80040d03005960083c0056583d0002c2c80e0009001900660181c00603a4515a080e06c0c1d602d09040c0341c03c0020404411030b50090311096040342d00140084e041500412201207d0321180000c41d082d014503030155102c1c04484041c002d15540106641041d2041900d00d0584191076610580640e911400c0d03660700715403828005000305941070920301071000700c520003040da6107854002450122600c00c0646080c1e640e00c1c0d0811102595088072180c91285040c920309501e004107000c0e46171741c1d00c0d0040803218081c24002605a9485d0b500c921 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614941807 1250 614940557 614940559
    0x405090a050604270201030c08010803120c040b0403030201020403062403081e18010f020607120b0a03020a150305010e0c0703031d160807050315011a0705010501141905010e0f0609 79
    0x101c4e480314410070a104486120042c0d0100c1e1030600d00c207014510030304401d410f1740c0825004510b4403120680203800c500b0010038003120300d5010b0002080400b420001000250b01907070001d0703180c1d800c1d070034070800b103c0383c03400800051040e00d12529032142800301181c040760f800030206a01c6d088070050808019803c1c4070900000640041c48403540c414141403044c030410280d8a00d900f050824a013a070341e40307105881d02c0b00455900c000000210310603402c41005488040c0018010b41d54035030200706aa0120740000304d94450806070361840300e40c1407064600600c90101254024201204203130b40b20310914401800300b42e2508030481c5018545e540d0341d00301c42c5150044894206400141c04114541400307950300038090050001140c0c40d0024940c418080028107810150740b80c41103034190764002c0a09134040f2202402210701103007007032081c9402070101c1e01c58600100f1070041000440074010b00d9003048141c050300c09000e166130045481c1107100f81a90340360301340b1701c150b000a112401904061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614943057 1250 614941807 614941841
    0x21002010902060426010e1207140d05070b07080105060f0d02220f050f09130519050c011e0e0112090f05070501031404170702150a020d140405090a050604 68
    0x8610340d090032012005401980c01030b03960203078404006d00741d40400303014401c0c45c1e02c030b140c807072900c032090740000c1525031b1003800e15443c00c4c02460308040c00c0158015104010a00201f00c901c00e101d061410181d224095140680741507042c03500180160080e0210b00e10b8000010801c40204100303941164946110034a400701200c4080d01a510480c101d80241c59030b40708400c0000407070703040120501001190050030020165030340c1092401d03890072010143c581d44500c40d00c81c6180e6904004c100c1840d80220081d01c00c00108900142900003c00b040350b49040c40742d400c03169a40d600c058414000e48007441d041d0310f1a60440007540c081c00201c003003d0105500c41950204118000038040b086031400c1e00d0a1044403d202c849610301501200c0c003911103000b08188600903441080103110203880244690305032140039000302d00603040a45040c016900c48001240c10030340004030034000c005036062092605081c0004698a0040504030202403501c1d040800c40c0fa503551342052182050246907 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614944307 1250 614943057 614943059
    0x71109040f02030c0604031a150d0b04030e090106050a0f020c0a0902070b060d0206030703020c030714010506030f2a03070e0708070809060103030e0d0309091e06090b030a0210020109020604 83
    0x402004040403508038402d102c2c4c070161854504001050700d08072038206c420481511040c0001c841c2c5030000070421121440d842c0784144031a030b50a0101481c1d03078001d44049031035161919001d00005501a60944500b54120042140c203074084e040355103240f520b26242402000200303059141c10301020502354072142c8408003061040703050f80034088550081081c0001a00d840c81400b40d902001c000107508103e0400c001203283d4040d030002e258001000301104d00e8003081c0d8540a900040c4030740b120340c00b85d448000b448420f28040003a0310742400c0d1007002d0240e0744050741003c0e1000320000d110001e6220602e001108a070307001d0001100500d038110352141c813407615a60040441004842010118442d0008640c0711240090ba00e4141d980c181c48000e4901c8116042080c034040c170760380c11010000003101c0460a04d4040c02142d0040081e680d01e46000c038000e49150043d94250b410014449161801c903541d16a400201d6400ca25010380d40b00002d024004000c030302400540d04040d40102c80024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614945557 1250 614944307 614944313
    0x303071e1b17010f05010501020c150d0f14071d0d0311061807080c10080a2a0e030a0c060c1505072303040c0b0c010e190308100f060507110904 63
    0x218106620b10648020400205041c8568040310028025907006034032805040515080c80e9009203045403c5c1c0d5641d50505800d80d0140003903038040300d138501c040b58541c49070104002da14080d098228500341001803402400e01d40d60030070041c42c0070b10140720700c482c0741c40300081c14041d0f042c403002d500221055030305070b282c40f00c0c0848407107021180388034481c40b070f00c000001c05803004181d03540c10090042042101d8010344a080740c0041c80a400316004035507845180707050301c07088620442003086990f80d50341280c1d101180940030302d0b410f03403429010340c100302d030414005001480000f007903400906241890b640c1c642001400d1600c56012030380d1880c904014801e41c90380125094a0b84d0410500701c21805007000305c40e080502080d18002c2c2103081c02034051020b0750061001e02903a01950000107513030008000d44a140403007001f04684240c5001d1001da082c540e10500c0c031548a04180744251310ba5140c035101c42d89000191081c0c100300031022420768100142d1b040e00d1010460000e04181a50070242 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614946807 1250 614945557 614945579
    0x11101050a060e0709030c03240c0905032404080d0e191b140d0311030a0c20030304170102040306090506060a080d1b0602070c0e04110303071e1b 64
    0x102a85402c01c00d035100151050b03105c1d00e0b100c13050301d0740156040715040c030f541c2d038040320007015070380343d4a002d02140800c07001002c451240c18800c0086030341e40742d005071400c420706080c54030b03190740c0e0590078442c0e86440d070b11085010690743d0010341c40031080780e581010a580c203008143c4030401c07900b1402841001f01c01c215100d500c0a1010340139902c042c81e501c4413000e1103400d5045030304c40e8a410030100c040b4840d1500c4c000119081460190914101d242240a00355045d41e200c0300c2d4500205240c400888103220810082d8100105100c0030030902d4030440000a0340c0f40110322a02c61403505280641082e40000e40581d00150340c81082841403540a1406607298003084907064080c0740014000100c40400046502c1240842d4271040d501d0540c0850312044101d0000f0140e40243e002c10254001950102c03200c0010004103c1a52544c2882d240c182c141665221280f4401e9009010307800101d403580c0c030703d8442520202210501902e840c500007160559001c10240142415040001c00c0c010324 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614948057 1250 614946807 614946809
    0x51216080312010b0304031b03140c030a08060a05060702100315090e01050906042324010303120212070e03010f0c05031005010c0f0201080c0c07032904031d011101050a06 75
    0x106082c50016a22860300c041e40340001c44001d400558110240b0340c0104801c0803000b4128040d280c40c0b00c00078909410a41e946e485038000b020b042d17100003800080c9a42c00700c041ea8100300221059060700c1d00d0700c3e0000c0c0081c0034220010f172045040100002070341c0d000b07a002543e84c565200c041400c484d52240c00c0e2000b070080c00d840d403a4139402c0500040c0745035408282c56100e240d0100003030100d81c0c0501015000d03a40c011041010b40d01c0b484200780d9001c601c0b5281c9038098070070072400ca02658110315008018203503604140034094014450610003140400c6800c0d4003410918101f0040c0c0c8414001a0140071036445004200d0b00c0c080115440300d038820025032059400c245a1100307242e0329001141d000562400140c0210701d0245c1140c0190b00c100d010039004906000201c0c281090680c01070305103a02c9520440c0c845d01e41c10541107454140c40d07603001c030140e1411111559071810381c030003031b10f05002d0b05412104036881c5e048122071a030103441919641c11040008001916007400d61900502ca5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614949307 1250 614948057 614948077
    0x403031a1302090111030c010c11030a09050906150309060609010f08030904180b0c120705030105102307030c0c05030607020d0507021c08071203020a090512160803 72
    0x14151041444003019031004080040a002610107070101c100420080d000b000e95a41000081c082d03e58003143c082016260181500000190221501c0005804c00c01c6003061303601d850b00180f00d074002c246d0b0080203001c01c032003003643c2ea050340f0340d06e180000e8a4410705c80411186404040284144590001a814170885081c0ca4540a80c2d8a50380400c1401086102d44030745079204114440c100d0905412600c02c0c0f000d61001e40c07103010300320b5940191181046400c40d0741d2100100310500c01610085045070880e41c2801c00ea0b28550401010860001c10340c5100740c14060340807807903003018114240045180615289580d01e440f010b03c3c0003402c3c01203914040d0381c0600c01d6000850645000314101e401410700390014a81d80c11114000d46041c2c12402040e03034800c004105203000d55907983d203044202c0d44120300e6503075601740700c1c0b401130640c00f11316044504251040c0000e420b5036400104c5103041d19000c56107401000001c041d00c524001c1e006820b404807805120002540040c008094a03200380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614950557 1250 614949307 614949311
    0x10150206061003061208090d06140f1302091303090305030c0c0307090203010e04140109060606080601020610060905060f0405030a1b080105060a0b07051c080106020c09060d1713030b040303 83
    0x20b4810400c4080e00c000c1c0c0128030041c61526410f0000030060030080841d000050310346001082591181c108a4140008000c024a888010000401c03030b01d05400d61720105440b00703844100c105401060040400600c400410001c1a29290034140504098001164004102c90307454500c03041443d115404111091f0080c13181400c04100c04100340260b90503140c1c1c060031800e2503a07031034a0701c811403134522030300000302d550b11514600410502d00501c400742c1202c3c1c4030f2910a080007400203152900c01006240070241c500000c1c80080d40c0554a4404c54408a40041d11b5003041d030312880184c4034a5100a603d0711031505074000f000f440e042e1140303411700100c42400c41c05a40c0c1d51040d007070f14000c80c0d005602c0792100d80284482c41c049005040d00300d0246003181c100561113410740150380904a407240c0806d20103001004402d904000c4400241001e0368050618200312000c0344800c18801c40c01050032600081c3c0e44080d8441c031050340d03954108601c010704c070150b40782070182c1c411409480c1500028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614951807 1250 614950557 614950579
    0x90a0206030c0702090a0c022e090201181401090503150a0e010b0d050a03080912041a040801020a09170f1515030a03090806060a080c010c0623010920030406051015020606 75
    0x100c88010701c04401c40802420f11b20310100d22080401044a1101203050010701d951800f01c412370200703460702401440201d54418500039001611641032584802c3c0f2a82c055020b81900d10021114070b508901800000710700c1c3c0d140c0c03440c03c1e40035001d82c48210750041e000320281d90a001d8000b5500c1d0707502e4040e48030f02c0d8446d15a550707a2501d80018480329203c3c00f204000c2044203522400d11180e070184500701d018149901d0f0714000b401d80e884410200c0010b8402402400324400384140c141c610503840e001400c00d010100d00c169100c2040c500305074000c0000c8000240c022204101d212515640181650908006868050070075420381c00f480c02188079103000240c040c00c14a241d0030035559044014007141081c1001140ca01c990740074102d962a490350102c49100c101041680241100901c10381c1c0d00d036040c45299801c0350200e0201c007480050030750f42d240031003c0c03620407242c02c150006008940b0f59117900c44c00c1e220801561190b581210030705040d0f910303c0d0307004c01c00303a00400c4102ca500c0110303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614953057 1250 614951807 614951833
    0xa0c1202071d06041e050a0f0e1221010803070309080604150e010e010e0d1206030803010b030a06030f030f030509120414010c02190e070305090a0206030c0702090a0c02 74
    0x9032454020005107010092041038900c11242c0b045500040040c004120800313030842608162900c4400705517140d44600c00e000c0300022602a48008034400e000c05c010481000c03400ca507035200000b1401c3c6040724001011442c0019023070f20030340c8003601c2c074914807040d5960785a8a0b03940d600008003500000d03d00f280200340701c5004200107010326000151040c4080b09001041c0c000c10081c80c0c0055a5960344502c410801020b000360303840c10180b10040e00c0000e0416030040c101507a800c4900748168603220701440080c8405050f01e065400c0241c4c5142c9a90703410b19402d000305040d800c00342201018000030410558040b0b010442c804281c0d40030700c15130710b82260741940c0d642c98810100290308140804d000c00700d12250506283c2c2814900141d00070055004501f14048000e554401c104040b0301c02d2184503d80009150000c40718602042580303869085181c40e001c7c00c0b0f000038480c18000011a51a40480090382e4019800818014460401c3c0f103440d0010240e050404000d4003d0070240016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614954307 1250 614953057 614953063
    0x5130c0b091e0409060e1e010b031c05070f2004050f04060509240a06150c1b030b0f1506070f1118040c05010210020f12070e03030a0c1202 61
    0x30840050445200c1d00d0200341e81d1804040c080c0708058029136116036100100e07a8a0055400441c40c410140c640c49492040484c241c20307140410f000c990b03040c002040c415840010340465030500d101100802c14080c484110340c58826039002405052603041d0110601c10300365004190a0b0b0500121501445080240010303603208030f072100c610800130800500802ca040d08a90307404105002a40c007106031803c0c4100005004228520801c00100308000d4440090b200d110043c00720088103100000c00400000c2950007680801000b15080e0040101000380079120340b80510b070701003034030049460520081c4000303100c00c1b220b41d4034185000101448034204034040b1001c003500321203407244000181d121031100c109008000342e007105e00600780c1c0c5e110441283e04940190301c00c14501854501e1300c1d000920784040034a07403c0505104002500c00d171020b0b40f045540310036400c040c082140c0d80718102918090a0500360305d400d0b00000594081d000e40c4000410484c52148000c4080c80a032520200d80e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614955557 1250 614954307 614954317
    0xb06060c07140102011a3a0b060306070201050c0a0f0e0607030201090209100f0314100e070e0603071203030e0718020d15120807240605032116051005130c0b 69
    0xa0031580c3c81f0084c0080703005a0140581051211804402242058021001078017038203400391400b4401806105a03482c0c00d101c0c0d0354000e4803a10080c4454140200709030100c2c41101031040510001e442c10416a5000d07003001d4142c0c00c1e0040000b80c4400741424042c1c064104010b041b40711b60710101c0000c1a01c2059422503054071110184161300394150303594409008680c00d00c3c002c59205021000303c0800b00d0380520342c40c1001e500c0c05002214075003404000706985c0a4283c602c6600941800c2c40710201a6110a0600d5014a00400d05501d880081400c0c405250030030791801600880510401c1020f8005206074450000c04201d500041c00816410803004e000d45e4107002003891303090b40402c1c00a8081c00c0c440c0d0142c200c40781280c01301c2c0c0000704020040d5050079103e54407280100030f02e180510507884001c00a1b425030320110010110401e6601c903d11603051450140019401400b104200c202e2900040840400143c100a0409448a15030b55811100c6281d1610080703141d42142069903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614956807 1250 614955557 614955559
    0x905041e0e28060204050a060e090f0609040f02011b05011b0806131e060906140409120f050906030a0b1c08030a02160f06060e07020312040b06060c07140102011a 71
    0x100030000d40c2c1019802000305600c040da180c0c1d40a00c07000ca03956641c881900000d0400f9114003e0020000052180a560092110b11421100707400c018240d116013154952080c1d010211050030800da00c01a2005180c1c65103528003d451040c045080090550050107108103240b400b0a0041d220141101e85a50448200743c0012403000342400c3e1607a550040c07080343e4060000e0400103140b0444080c1242e246074400c092080e1198010001b01c2c0003911066000d05040d5414403042c00780c0d8817018884a882e00d8000304014103260756060080c4201c0680744614030003000e0380c0d6a800c0404014020309101801e140c400d880103074003400710030134034540800f121b680420054203581d03403022100700030740003810340c000d110480d8000301d4001040c130620703801540c0c40f03100c1c0081e4050901007940140308000308102c06560082100700190100e0100865020350702401092050f80d907580841c0b118012401e11413110702c200000482c2804d00d9150a142d105001c1e0b000300301e440300c08000f9010442244c8896 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614958057 1250 614956807 614956843
    0x50f011b0212031b0f04050f0a060804020f040f0c030e0d0206011d070903170c0c0a0b0409020702040f0204060f140f04060825050a030f0504020a05100905041e0e 71
    0x20b8901e00c2460010f5a0700c15113000004100601d65540c2c80103d0f4428003040343c1e800e40000781403016140c4008840480c00080d24032a8245041c040003825400c0c014102074030500d1070184250495071643c10000350112200420301030011000030150181140e07050f0b41b400342c05240840703c1010b200181c9941211500b0b490000843c12101c034242240c0e2010305400204410014044041440c50560001031010340c8500c613550030303881d0034450402c804060500d02c2440b581c1010040450800e0584007590442100180c0c1c1d4005480018004c1a990030b00000300d500100d03000074030790341110b941d0384803210584807900149040c06490006110320002d0901c3c0da00c05110071f21500d40304080380d5600c041d0550741810507540441001ea80c24840340c199900084001420425143c2d060061500b0742d16604800d02c2136042030360018802c40202d00070540100d0342d2811595031140b00e44844c1e0b0042001900800c6080c1101c4c451200000202c00c00b030a983d030508012420340726001540c070f80380741480705031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614959307 1250 614958057 614958073
    0xb04200c06012c13050601030c030b0a0504120e0301061211031002160f02120a050d0f0e090403050f0f0a03020301140f220f0e0703050120040902090616050f011b02 72
    0x10141c0d2400c06041500154584c12199002a2042054502035270040c161000d003107255282280000d04d0042c0750040d190f06190901000071011807101000f400f2604041c161001c4210201e40140350980c0b01c800d0410203e40c03070388240b00686488040d0340c80154150350420003080754400c141d219020100d84403c2c0e054540102040344600035200051009080c0200400c0d20503071036250000440c81a901074002400841145030451000258040c8030309084500b005504000713550403500820280c00d01c14000344940071821000100c1c1e884c905c0d80780982d502e8461540c03004000750400d000c1c85a0310000d65a0080311032800c4491b0080c0031340c000702244140000342c2c540b080c000e280c00d21020017403600e03000549c100c039031180a02e100442d805802011700358a18100b503400d46d4070b0081b0101080240c8080481901d8008088806840c841c55001d41d0b1040c035400442c6651180754034042c110b51001e503e10041060200d40400c0004071840240f1018159112000303c5a01045403040941d0100e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614960557 1250 614959307 614959379
    0x607051c050c07020d030f091403031c2d14040f060902010e030f0615010306060816090321080f060f1203091009060215060d03030b04200c0601 63
    0x711641c410400d00e07545007402c2280e03020601ca0101e15034110041851181d03400a030781e03400072001d40240700c13000c14000901054804252248070300c502003500072032a0b204260050540e9000068208101031000c0399000c10000a504050510350101146908260001a180c0130040910380107540111701300d4603c0b480e40e541d02d0024100300c00d049062088035000349103956400d011107468207010602414081c03034903803140203144404034080381c1418500070003444420344c000c940c954480461105000c00d102e60000544854a41d6880102042029640800425120040c03451180f80c6912013940c1c2d078445c0903415090001c00c65581e508a06203072501c2000380b0b009908034040c0c54441c401d5910b045c103040c0c042444900c01010741004201640010800a5810000c1559400c41e0801d078400c10f04140340002c4804405070000707030415484501d842903907540c07940107598540b0002c2d50200090f0000e400e151440c0c0024209200502400000040380ca00182d40842108001d145180030380444103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614961807 1250 614960557 614960561
    0x130603091a040f15091514041b090c030e1006051f050d0f06050102100c020a02060d020c060117150f06240304110a140109060809011404140607051c 65
    0x800a95a40310303600310f0301010071141c03409944080d4089501003102d0805040007090449840740307008000d45044012140885030150580d080343d4050724441291084a0550300d182d095504218101441d085041032216007550002181c00e0035401601d03480103400003000d080340c929218190f000240001401d240c0d2200032035a50303074180c0380d00303003d810020007140b003c00301c41c4019190302015030360f038405111030760301044440300910750300d0800d02c0f42d0080f664000b5110300407071078000d009540104075600141650340580303581d41e8030a42111519a540c40300381142c0e0081801c41003c0e801642c0d0081400400c000c0014402e05044400d030400e030700c4403001c0c4240c102210030020007403e4259414481035112a0085000318054010107015628600c10070500301150303071001d038400d080c980203040240d0f0803001c92011141e1a0614190740e03940d000b440c6014210700481404601c4c2100108070412403c41503100c080b10013170080301c41941c1c030080f0582d1244541d010b00114140c488810746201d48481d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614963057 1250 614961807 614961811
    0x10503130b0c0f13030302250b0a140703080f0601113004090f0f0e0a03030515040c02030d063002062106040b040204051c021507030203130603091a 65
    0x42c1c41d038903140001c1500b00c0c0f034194010900749a03040300310342c0e001c0003815410041c1059a21440340d0b2208602d1500c40c2c03c13142001c03a4441c0009502e07021400048450084800c203606e5088000d035180e49600515008082c00d82c1100c1e401074a160403004100c441d44107041282840d00300170010139004044c0e045d03640038441f400c0070300003c05080785031020141d5009005800249841d01010800710782d5500c881c010381e0b560010318000c03149081072815041000007104540c003605401c0c0051181c480051480c10255500040380e0020f08001c0f14646a5034004014a000f0420000c10413100b42c03204503408001103803d100016032030004004404c01c8030b4419400030401d01c000c1240349012104040c03181e11400a03000428008585010448181018040d0144824045508502c1d15040c0380015010034154220b05544c80b64440303a4204645818080d4074007107030305e1501d07282c9038202494005d50300c1d8010061380c2c003a0b541d61900026614003900074010310a5129107110005419401503d59810b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614964307 1250 614963057 614963071
    0x50c0901092c15040f050f16061701090b0f03011b110f2d0d050c0f060c0f070c080f0109020a080d020303070c08090406090f0e060c12060102030403060c03020405040605010503130b 79
    0x3541741d4080c006141005202c01484010019011107107482444000440d084c0e8410700c180b04021503080d0b8404a20243c00d0f0640e0000000000d072009402c02041012284844564140d0320703048081d0345001c02d10140700481d014994400e02c01a291500701511026003203072000b655401411000c0380040b60b2180f45100d150b0001164108441c01c003101850409500340100105500064030007030301030148422034800708044000d0426060140003045c0300c0c0b151a00001c44040003040d003000700521903124400a01d403210441d0303108440b00085038000d204141d0200c0c0300c0d80c5606400104400c010403606107400d016005181195a29902030380c982144c80002c0310039031410030081e05581c2d074520500014081d0150001005100f422440c3c00700c42c6221486585503006d80104070031110b042c5c049600c140001c1c85900f82c140c44030030040c0d1560080d83c2004059030300300903211995541c07550141c03049480843e41440300b2542c48005646906c01900c64035078200385a0820404240700003915600020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614965557 1250 614964307 614964323
    0x1091a0918100207060614040504030806040c020f010e0105061c0f0303090c0306050f0115020111071203061802090901050d0201050901080403021905031809071704050c0901092c1504 80
    0x4500440c2d401c91344515004c482440d5550302c10312080341c070701c02880011031095a040103103040c55140a4485140100010300c5180c440c1c1d48100354510a01800046140505c02030142616840407240a0403088592601546595003191000e81912a2100d004d0741c1002e0008004100f071b0700c0c01c8020341055401940d400307a500c1400000610349114451283c0c001c1d041d1030a0b95410406c0780713401807244c0204c80086a041c25014005103d0000445000950241c400040c1130104101079010782003035841600b400340805200c1581040580041ca0681421503441d0000d80e00d640800007441b0700e9240103400504140541c2b091035001d0000c241d0454080d0045a10020b1450f903140c1340000f0140c0211141d400100e04001074000b515041707240404c040f00c2440940c60208401014168480c50a20b40850703004041420f1010500000c01c00d0140680038400643e1a00d03815400b604d00d6615120419544c48843c0c0040341d000c88080e00c1d2440e010000d000f4484c2d0b11803204660020140040d0b607048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614966807 1250 614965557 614965573
    0x20a0f11061e030a1409120d060905130c0501050f0414041b0309030306050913150212070507150908091e03010f290a0b031f06050301091a0918 63
    0x5100e1a00c0c94680c80d2400071075070f560715141065200740d811a5581800208102c8184084200041264100c4e00c030b22050305910340380390f80103102c013074041c81e0b001c4070391540f0b03110a021744030140c452568840d03405407440c0b80c032076943e803001110103100f903000c003c0008006100078010b203498110004030480e40104041180d00c842c2c1c1d08124200714455146e00070079510700020040503014040c1c0f0005007002c880700011880c2c60a80405a0240c032100101084050040455942d156a0540b10307218082d2244014510744968041c04503444600c0a40d510b841d036813264003000d015806008103030780e07000800c94200f03000201440900356605021400f40482d80701041101d443c02d104440c180030000d0700201d0b01d44d004014200c141c5030400304030a9012200030100c186034a500c404c0c00110380d0480d003919641d03500d003040c901300e1014580d002085100c48034400282c144c0d0003030156058030401c10082040c0c21548800b0611107400a5a6540095000000400c141c1c05030182042c10043c42c001e9503c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614968057 1250 614966807 614966827
    0x1d0601030c03140c030a0e030c030702060a09081b090901021e0d0e0105131112030901080a14070801030b060105041a070602070b09031201061103181504061d01020a0f1106 75
    0x1040403a085440c007040441000046ca045001e80203071079402c038024518205004100c2c6489100e02e0402900415000443d40401881008a40e0003040303080f056a8504400c150030814178440c1e0000e60344035601020226401c14018800c8444403d4801d416514400800c1c04204d003e400026844900d26a10806005101070078000c00e4440c4003107030406c0407481628a09040141020140709000c0c1d240e000466405040c00011035403006801d00700b4141c80c2d981c0c00030007809442d000340c0403030400001805100c440c64210881506881c0704400e02c1c00035a07190001106d40780110700c202d240c680c2c10301c0c51101c0f00700c002d0341c003d1802d1401080c01501d007230515212401c6100040e1101d20481d44001340a005000100b1103207409440c0d58030700b03000817010f902401a03907400307440b010100414455500702015500e80743c400303a441d030f40780022a45503551260040c2c21610001d107a026076074040c90a4212661020400e1100150304c4269100c41d031442d034070f8000c1c1e0600905501e58202c0003c2000b0707068 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614969307 1250 614968057 614968091
    0x190c05030c0d020304240f0e060d0c05030601030e010e0a0605150306160e060a080c0c07030b070c020a08030f0307050f1c050403121b0e0415030311071d0601030c03 72
    0x394500b590002c2d685e031440d00040086203050320404010086000c0c1c03040c0d0140780d000e145d035030028210385402c0e02c00040d0100060030f03902c510014400014940604418500d40060185104d0107091b02c00b0401d00b0310410505090303411954291080380c000d5030f0b0101c001840d0340e01013504915000b00c40709480d032584022a01d403100c1542e590015000c00f0004c104411b900218060400740203803010340c2000810500038105102c003415041000da00819506452481001600029030f0001c00454050900000203840500b00710b0381030340116100ca40100b000340e00001240c40a074050f00e402c920319a01d000080310140c10802e21040a60402c228030207124401c910800030566042000003044c0c109481c0103040d007021980ca11072914200f4001c190707901d98028040d000b006442c1082682e6411a8000030014070312485050303012404003d011003030682c00880000510600022111250f44800d202c1c0d00114003001d05404400c0342c4000214654420303008400314405a080c045001030401c042050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614970557 1250 614969307 614969323
    0x200c03060f161e1b060c0504080114010810020318060c04060305010e130b420102150601030b0d021e040501060509012f070e09060c190c05030c 63
    0x1c0c5942000e42408000ca0020300360190b0b8802508241070480c0f4054224159080003840d400280038020441507100701c1c11003008040d20790700ca8000c020032007507010042d10303640013402146901e620341301070252508101c0507041d0503658408010a20304401d070030b080c4080e5100a11001c2c11106035440381c40c60020030031030700d4001c4800d80402c1e505c0d1403c04100a0403a80305130711108400398100c1c2885100e5801e1100791a40c1c94000304680046d55075403602d16200c81d00000d07a2100800401c0107a000010003801c8100500842201001603091000049070740e9010542c80d081b0303100005010909560003688003901a01014003071404030002d5070001038403000c0c191208041c1e455580d424040f02d2038a841168050500c5003802c03820940e85400007003641001c1440800c00f00300c0c51500c40f0590616145960000010600b06c0c0e004035110030a0202650382500c4002451090b20041500705560100760361070b80b01c1940340c00841035410036080ba40e00c005400d0660300b500003000821440354090280803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614971807 1250 614970557 614970571
    0x20610290309010632090c1b0102040810020d18020616060b04090803061f0504031106070f2405040210030c1206061d0d03020c01050a0e182401200c0306 67
    0x942505000512505d01050211442000c03280c0411100c4006c60707040d00d40d00102c81c04100311a00054111900911464001600c0d80c0305518041d200e0061540003000004224401407101a0420b80151790b809000700009521450601541c0c9548200d501c071100b2550240d000418882d1440000c10211180420143d50500d00001000001d08040f603604442c4658101c40c82e44188801100070310394021800028820031904501924998500007a41c50a6412402400b208501403030082c0f50b0810580f00041e601d07086c0c9209803503819891052500c5550045c00d054400c9a0300f0000320000d04d1015940030921424001d142e034034040394400d13040600000c1e00c8035204c410904d120040c10500f4080910311401c80380c171103000042ea012841034820a402c0c20250749911a1040c1503a600c004521104e802c40aa040c1d03070352400d110240028040c205102c0070040454884254030310451200c0840b0f800304109103800d0403400c3c0900c018910220f85d08041d20816100000020f0030200c082da615 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614973057 1250 614971807 614971859
    0x5090c03010e240f041119080a110d050c070c0905060a0819020f0102031207020319030903140d1d0a02040c17040201080a0207080a0206102903090106 66
    0x51220110903241981c0107045a40014803010481460950f90300140380b405000703810300f01071441552901e40189820300ca0718624180c89189641c004a883c10041d199480014804400300e20400c100d442202d8807007900101d40ca14000a050642000d0074015081901129040010070003040c0f8210201e8040e01c50440e0200f420306007881002480b01e4550400c01d203540014104c03c450780c042c0017411900c00d0b815600b403110540440010b2f401c6000b602100b03151070749060101304410354040000e003e100d058189101040240e058218101d49610000401150b4404d01811000360074101030007401d41c00603804181c0c1104566034034402c0c0d00303001003041c1d0741d8006d00f541c3c0c04500e458020b10072101c03180d250224420703440010800908001070006414880454041804005c1c0d68048600c03454100195581e0344040480c02544c6400c00c80380c004003184d8001012460f51021400843c48412890040f4815000c240074201c650f40040c0404000350341c6d5243c0020241070104807000c20103500c41d24 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614974307 1250 614973057 614973059
    0x270c013009060b041107110303071e0c0b0a08150a091103010f0611060a0f111b210d2415120908160c0e18100c020c061305090c0301 58
    0x102d42c00391500d4820807441035061003003908207014101c0503614281d4100c0e0350140301801c0000441d0039441001405418200a071a51164008102c0d547c0100f55100d02581110903030b441c403c5800c03074001c0d0646403001036000008170358030b01c0c0b8111810756008030061807000c0907aa10444e040440701401c2076440e8803000400100503240c01d65401100624003414840b500107420903544e600d8400041810780165501c200f280e070828840e0780040b00384c086001140782c2d01d8006c89110800c4500d10b8071500c000d40f0452102e481075060800d903a0030002410030440b4100051381c0c004002800100d142150070074007a0840c0f034a0002e44045080090a8014500d6014480a00d0080060b1a4440100c1d040c0d8207003204900011114412540ca0a2600842680c100356a26210008400c298461006101d255051140960b80150b00742803000301d4201b1500b00c00c200d02d21540940c1c1071300403000701580140740c181286040942c0102001ea0b4012860050700e0344410018110702c80580300c0220302040840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614975557 1250 614974307 614974313
    0xf1d0a05070509010501020d0c0c03020402040f08061e01050f010509030303040c0f0b090312090d020406030308090d110604110a030b0702010204150804170d02120c03270c013009 78
    0x901e00c003030101603503a030340301d036050100123940c0303450224292040000c040542c00c10f0100a21080010b154010000c0d50b440b036a034207070183c9034401400b8400c02030013200c02107030720460400d400008090082c45161116864981041802c4101c03200b600c0c1031202c10400001c841c1e405000440c1b049115a00c4515040e05044604142041981107055604402c100440041d079001940d0007010701e4034110907aa441d0980c0c0450540030308040c0007034210341082004010950001c0b40d07a4800c0e840351085400c040503000c0200e80340040300713480d4440b540001011038085686101d45850a00c00640f49100c401e40ea070707880082d5160101c2d54040107135400f05040c0048c1900400b14600c940052410880e5418107172210846c0000f2990f00025140c400220000d00302c0c881d0b015200c02120000c0c9000c5149481e403c41101c55204a80b00100c0313040301d1804614240f0402c5160400c00d00920050900403022001501c83d01c450740700a15001c2c2d0443c0c0080c150460800048a401110180103d0011410710b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614976807 1250 614975557 614975563
    0xb03011e0617030708183001150f030f02030c06070501091a0403051c060503011505041404080304030f02160b09101e050f091008011403011a040f1d0a05 67
    0x3100a8005410800081005c61404010307589403040000c1e03c1001840050f0010765480b03440e003100c406910b40d0341c111900f0320030303580d16082022030308600a010440c504101e00740380c41000d0050b00341c0f1001241040c000b05441413603201e240c910240450f529500c4000c002a1036400c40b140848a6a440d52958400c104030b81c43c4030301400321080403400d1030341030507a00a41140036050a200710395120301c46480103220a134101800800c0041d000300140703d024940100e2405042c010140128201250050104031b2550032621494010100e10704540319954100c0f005228452031030110700c200070111040e8a000c80034440100070800344656960001c100340040220000c16a1041c480243c40c100b901940c80c8480c041186402e28000755182c1c5050001d0a01d80140c0c0e02158020390925003a00140d034220141606071244d0303011020920401000701802d032401c00e4119501031021078070321111805c2c01d0300028807448140b9000b140081100c0c1c40c22041d0392644861900c540d10540300001444024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614978057 1250 614976807 614976839
    0x40503040b121b16120c0804080c040e0304061b030908060a05010806060901050109060c0311030a0c1e080a031d060c0d06080c060406080408041e09050c120402040b03011e06 76
    0x28900d814040940c03001c4e00c40712214800600811107804640d9201071003032203039084280e07000310055125a29581880d0f9074070743d403260503030081c3d2030111a950041c00c000151011500656118682103100d00e0713441e05029091141142405203d460100d6607103010f220a034440c0000720000142903251a855500d00070002d0f110798055800c210042c003050760f00c00305040130f440030760034055072199241c6400c540c0f04202004440840c0030110310040e00c258455400d02001d40995002d210f124002125801c07a005560001461031008204035400035010340c2201403129841404c80c041d51150024950070184100c07020786001341d0014285112400070700c03400001e014048010b049000c034030030104400744618080c41062141100c001010401000e049a004d0011501a03850605200c07503660080d82140c05a0850ce0b4140800182c070100c410040c0e80103001012015034071a01d4940a0100400011a0700c81e0103540b40d200100c2c007100c00d0000540354000c41000000c00c0d900d0013034206202c40513 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614979307 1250 614978057 614978101
    0x51609090c030209091510050a0e0915060d0b040b06040515090c03060f030f21180d021f080610050a1202032212020d080903040905040503040b12 64
    0x380c880d006010070600318051054a50550b22480705464500100d40361503d82004032081c00b25000800c6161900445540c00312001034654045080c0c4400c1e000c12144421190011b05030311072140c02007051040390f905504500c02510741903000c0d4042d1075841700c0050844003079031000c2c82c00e014028241010b209065000c0082c0e10040c0da030800580008012a0010340090341505c0c010010807a10b40c2c5102c803c08605d80000c003100d55401c8140e1007540c40f800081c43e81250f403030322010b200070b0020b890000c40f00c0901c0c02c01601807541a82c042048042c034200c480598006010300f40c8a2441040c004185a0b4180700d602c030104075142c11001c004100300030608580800401b40409a80580c01c02c62803107813601054800358581d034500000307603002d60b2542024640e402c81e6540141c2070040204011040c1d40c0c25a09645a014510000350360702001501e42c81c00c554002c0200300080150b40e4030007508988a80c0503285896500c0210412070380001c00c15644081c110b60610407160a0b0304018505425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614980557 1250 614979307 614979311
    0x1050f0705090d0b0406060b0a1d031902060d0e0102030705070c140306040f080706060e070806100e06070c08100e0d080c0414271f12030e0307090603051609 69
    0x31060002c185203e202c240020400135089004c2070403c40ca41c1c0002010700150080d00d5168403001c5001016150a000c40468010a044030f0190a0502151002c1c4000520750800c5214205500b8417805903c4011b051034102d40d5040001c28010017030008600608441da2419104c0710207042100c030341c0300140e1002c3c081007908004c40109890100d4403540c800e80120349038036403030810b0520b02194072440fa0020140742c908207000c100c2207050400140655099507e1a205580c0d10b0300703100304104290038041c04a403901159501c50724010300142211481503480c906142e5a410f106813412002c009994030103912105501c0344c604007000750350400c04440c40c000c00340f401c25000d040d01911490244070318030f003a07480c200680c0307440320f01c1e4083c181402007032000034880b00b4200041420009840134a09094102c0c2e0342400b81e208cc882c01000c5c3c982084110f0400e8076180e50549091452a00150f0180118040000e007414a0712500c0d0046000c1c0c00548408409040f14580400164001010b524 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614981807 1250 614980557 614980567
    0x1308010c0225050402030403110a0b010905010b09092e030812160e040c090509190f0b1c06090510060602070b0705031b010b06040902070b06120d1d09010801050f0705 73
    0x6114009403070102c60050b0b13001a580d4075039090850f40000c21000404840c0f098801c40000c2140c0822028106c0e21400c0c4100450b036241e40740300140b40320351009031303078050000d40c0480d0079036510303601320b050058296010001944020041201c100d846030b005540d07548010034101d400380500c1c45603d0f84403600b00c0c082201d50b054600d0103885803520720801e6018030f695440f8144654000e072000c0d00901401800c1d42d10030314000501c0d400d6500781c075143c48401030911502080b0722410b40201881040010f1079040308100408c0d50680040711100140ca4441e214007814000c10010302150440380151031011400a042c04806031505000da0322403460304c0001c2000602140c40401920030444101100d00d010707811480c1040c1c050204a4500c5a118400180004051609500800f000c84c8100441c0c540784d5224020401d04143c5081040c2440d0001c0040e051402c2c401c050350140d002007000d65903402d400c03070f0000c100070200903009011169501c0d0140149803e000308401e920180501e00035180c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614983057 1250 614981807 614981863
    0x90914061003020403051e0a06020c0a02010e01090620070e0708180a0f150605030d020a06110f07080a140307090518060102070b0a120c02161712030c1308010c02 71
    0x60200c43d511f01d42c2c044003000a110b2499402c0c480380f0300b43c0e070300080259250100ca03034441c2d40303840050b50109e021480140000c3c601d54054005078040700c09588039581c8982d29410300c2c102c8004130b518286514040d004011620003800c0c2c01d52402891569985441442e0480d510f40c03a03004601c680c8601d66010010400006d0a00051145c5003607002030300da1080800311400390054142a004540d0600403000e240303404903400541600880e0003030600340b248880c0c181000078035200303848644403000c004000c94070221300240300038540c401ca9460440b0742710440c140c8201b82c6d0b801c152015800565076820070007041c80c003c58144a501c1e242800a40076040400000c0c1d03a881480c4209282c1c00c0c0d010901d01c20705801002280469032800d04140000c00c44014003d40301d4039030b0100b0001000da5880e000c0364100001104110807005140240310407101a6481215504010009001d1403000c0103500e018156a840c41c030010000d00c070021038a031a9811340641403c50100048005d0840d400c440110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614984307 1250 614983057 614983063
    0x506090a091b15020d0e0a032a06180b0901020d2601031208010b041404050a020714010e100911090603210406030c0c0b150109091406100302040305 65
    0x4854084400103080000b03107050150303040404000c1070407405010001a0102d2000240c144494865003910315184c02d201c000d4039a103000b80b2025402140c40c61003400080c1500306180b131090703030026421280005130001800030034240d4026000041682c10b05480c80c00c4580c0800003e4042811800d00b00580c1000003523a46007032280be0780c100600009091035089050001c20484040c101045d0b07040d41c1c49041c10480110381680440008200710000202d4100c0042903c05594590400c280f0300300d03507402000003a090181140b0f13010740c0d080080034002025900150803203c0000300200c0c00d03010b0082c043c1c0c103004080161110a60404c51400c00007942460707540c21400c0101c1d225680ea0300d8010209150241c2590504a50310500040c0485115003c0140c001c0340c070241d40510a88611640c1101c07100d840318002840c218201d00420110741c0d455030321540510042c94003191003651410408183d90a03001c030b10082c05610303024050300381445140c0341803011141c101903145c507185544040d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614985557 1250 614984307 614984311
    0x120304020102030d050c041716080f030f0c010605060a0c031d011202070c121b06020703030914040f230a1a1002030c010f051503150604020a05040302040e030913050609 74
    0xe02e90340e440000803c0c1c1d0700e041091f60080c1c5240c1055a02181d4441051940c0d040d0240300d1150005090f5400100c110300094a100d03008041c501842c1040050400320200343c01003d210800c55403900f0000ca038a444603800307401070103003036a00c0911082ea142000780c40f000d1414112452410840d003210482d90700b0605d44035042e5008040107035681034a0409007150355075508005c085461401070001480b10340c1548c48809040d445072010559590081aa610f520030710004011521450b02004044c0722140e820450510107080030581041d9500ea24045502000d14124041c00112409500d4401428280d5002100440c00c100211490721408490b016026020740710b5040c0c081c001a1035403091082d00c016890000090000c5405034030220041c0100b02d500c1451a46000841c1d003007840c00041182c20354004003441602c9880391001d00000e035015501c04800d00608100000050712580f1030080d040c00c1c624040d5484005486c00c00c0414100791000c0103000b800c00003480341945e100000c4603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614986807 1250 614985557 614985577
    0x12010614100c0c090204150c0302060705090f0907020d020f0f030403241401030209060405060a060807260f061e04050a0e0319080901060f0b281112030402010203 71
    0x18010038940c1001c664114011500419010010f00001464407140e005481581d0a480c42c803400803c054004940c0fa50b006400070340180e0000001c580c42c140110002c201048020f41760340380050032000410010b107030139102400140d006820070b28255a0504c24030310704006603400b80000b40900f190166a901a50001070141d0380c0c2e0381c41c08290b44c3c061341114900b5030800c0f101480f200c0c04164030705010390310905c0240c0c05000314800045152070f00d84280c2d48252070080050003100c0c2081c07000c40740890024010710a120f24422201c27108144807004000c5007800c103124902c1b510342408541a40c003409001c01b8000d4080b062807810300892414206002d01e4155000030b050303540c9111440c0030700800f42044085000000c0d90964040c10b0140088844075551a40d5840e9224209000c4c00c03650188101044808901020300540d0030076401868581c19001c2e404046040d40c803298a002210850710380003060205000710110310042c003515249a071404901d60551a0540000c0e441c0d100e911032807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614988057 1250 614986807 614986819
    0x102010e16090e03090a030c0e010506030c071506080a050705330901020a151401050a05030a0605150603250203070b0609090f07120204141302190909030e12010614 72
    0x1840340420a0b00c0c0170345070050040605503920300786070b40d410740c807805203411402040001141508102c41241d01035034406441c0b44c0b8091403a160300c1b14110070340324401c000301e841d648000b03003e81d0104034002c0c4841c0500050301c04580390804002d55900007660100c411030a961844040780440d01c100b144080c10190029510101d140c0102e0524500c914028090150340600144080380f550101c1000109000c2c0200240d032142d0400c07800130300c180300d1640d00d070f0f00c81071400b00021036507000541c0003140d081c8019040828940001c007190002c940406a11900e406038130f0340369984140002d00000c107400990b2401c0f01304d4540c045075640c014205030241f0f0010011a14900c010002894000c1c00442651003080d150448100160b16500b003d074415802d000030b120041c015511042c0c00380541c0e815031580c40800f9401c2c010001c40c0030407107208600e0350100006d00701c0e101e400380c08a114400e03a58901d00300c2e0800c08110380c2c1d8461010140035603151001c18400a011504c1940820703034103d0300307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614989307 1250 614988057 614988071
    0x13050a020d1b020d232a060c0d020a03020403020406240807080a090f0203060903030105010e0f09070806010c0b090a12020a0f030e03010204031a250504050f12010c0e0102010e1609 79
    0x1800718060070303c503005d5402e10400652004107040c0319070811600c4003640c5070110410151806d00703540b40c80996400e21440810800c1207030703000c110703401440c000c00c060901500f040d54036000101145d0440c1d0202000e0402c250340b40e500000b01d2000040c15611f2410030510f05d04041030b0050440c02c0080c000d01c29640d54001840601c205900c80600f0241d0080445440c0e29140314110741701c1d08284101d0380403e810700000c408900c2d16400740844804090b0140d00c01e680c81c808200d600c484058841c07410300c00709568210204034010040b9100b416914000e00c500350407407519628004a112000c3d0854001030342403000500e00940c084005500f5161144c0326208403400680244115440204400c15207022150200c8280d84014480c0500c40c0c0216a42490314040d1420042d0344044c210004504002c180050b10308020300c41c0c0d41940c0603107141c0e01002c0c460b03e42c0b809c4030050948100810300300d41d803503030056038240100100c890180300a040d04504181c9407011080d05801040071a548601c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614990557 1250 614989307 614989337
    0x602030a06030203010905071a0a0507200d0501060e1806070e04110703020f07050102031c050916091a030c0a06030e2103010e0a02120106030b13050a020d1b020d 71
    0x8401c0181d50010020402e6240d04e107000e55685000c0c2c07142054051444ca800904802c4a00942e50002c50a8035610b2802c2c60954419942035801070007036602c0c01c0030044c020781c103441c1c2d804925005845100002000e6040001c0e0b40f55403803008001250304200d0810302d08400c0c1e404580140c002c0d0312802d10f006403100020005000d0300c3c0654107500700a83c003040031024154002000101c1d01d5000050b651195290001282c03244500f400343c103c0c2c0040c000e010704041c019584031550201001081d21034010010003507400700c1e502c50303025002280c1c80b070589035880120f03448070880394042140248940b0194a01081c05070009126410070316036a002c8400c40d00e441403045450a034104064518419900b103003801b03032a00f00f070194110344480000000c11003041d902c212191106011607040c560380c43e00301c04038094a45804243e8004981d2110344102d00070300c0c0506030103104071000c00361711082410107640c202c4104125144100360f4001c00d101c6001c6d004605807822441500e00015107106183c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614991807 1250 614990557 614990561
    0x3130603110a2a0b10090b030313030b09030d1a010201150812070204110705060106080a09050a0206032a0405040b010302041401030203091f0f0c0e0901051e03062e030f0602030a 78
    0xc03c003510b00c100100802826a03942010030341a222041d0003003082d4881c000070b0641c1c81c001e10141c0340c19040307907000c02d0000c15092000c0c1d40d070103415070702142d1070100012035201c140c80c500780b4100e030460f260701c9000b215076070203005141038185a084680c03a014070b008806650707500c13101c8055100c41c0300065540155100c0f41c002c206116055419690303111150310702607645440910440d0005000e07000856a81c172a01d0003031107921134000d002030103000070036003c1002607407000d4002010122088406041880e5901091b20810803440e9080c1d21549424144415682010407850400d80704100911003002580c41074651000e0a103401612035540e000e0302403810306060260517900010bc1d10302d960104054001c841c20400d400c0c070901c02c6040089058a10140410b40705501c0000c0f00c0040c0024141509480384206400341d141c80d95400c1000402e04100c0160355a0782e2001c40e04615821049440f01c0300d2454004408021054915580f220042e0700c642c108010621034000000c11b03074100240d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614993057 1250 614991807 614991887
    0xf0c0307140418180804050603071718070602030406081308120103080d180308130302071a03102120040f09020405010801020a021e01090503130603110a 67
    0x1031140c03a40e44603283d0083d00c076200d07845210400f010741461615040c55915406000c41c16034099403441c1043e04210420075503030001092402008001c00c171003051038245160f218081c4604600c058204001c3e81103c90500070310f508100c040d0340c8104420011258030200243c2e010001d1810040000c85510740107a44d032080a20391040801d03410004024050b001e4000c10420000c00030401c200040e2200c031a40c5d90304100c5015010448110000b1000000c0c82034402082d482031058415240d12010700310500c800000280b04c0b110310100401c44080603c0c1c1c40b003405803600310948004080001c010345540d00301e0050040c40101c459100413207904103148a074040302c00040c0b00b0312501010302d803504c004103000001684a1800d103000000d9101c0c0600c201c44048509502074401400f10351240040d207402403422105640d42d484001c00480d1090000c1c6c0032210110035140046881d101b001015544080c800c98560390042241d070b601a138101040804841c0051407000340c62120a5050b0f1440000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614994307 1250 614993057 614993087
    0x10e01083105010903090609090c080106390b06061201121b0e060414092a0a0b03091b011e051909060215060a0302040b060c0f07050a0e0f0c0307 64
    0x80c52080130401d500072800101b520303441e5645201183c1c0d10018081a68100360315a40491000350050240300d204400c0b02c034052450380001540d41100c6105140820108108031b17210341085440705040141da594000c3d0002800c4808a0409100c1c51151404500600c600b90314408840d085004100525140040481c2c8203a440711034240c0c1c413042c0c941400c0049851910441c0742c410b20207840c0809240060207201c1070401825105a4074070b500b02c0d08080e40c01d4034440340c1c2b02c2c0c03c5072040c141d0f41d842c800d401410046607540d03268145650514500581145981c901c0b15070200e410700241d170710110460b42000110501000101422030075038080c4034024884040000040700c1c5075403260880050011504141c1c21a40b05181e005444008a0b90030b80e4119807045110304104050b2902d40c0000740a41b000418141c03500c81d541716070906d0710484006a00c10341c0c120501c200302524182c410704000f01741d05441c021031441c02c60003000302110000c3c08002ea11201102050015200c2c114009150b44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614995557 1250 614994307 614994311
    0x80427020c16080105070818070b070c05010e09040503030c09011116053d0e130b1512060d0c0f030f05120c15091002030c09010e0108310501 62
    0x84001c641a203884940318400401261960005100d0005105041c415401c50b510501070b0b44400e0514410800c44035100e250724410500d010541c40c0e03518000f0591140305400399101d01c3c3c6003030b001401404034020107074899202d02c801c01c00452400300c100c81d44010040d114560b168005030040c0c52103541c00d903042449214400c0d2444070312040f105103c003a1036085071f9941c0c00316541c0c240c07401c0c0720034404903000c104d001c220038124200344482c11003200c000075410808544021480411780c4034038030440001c0415120200001d01d82010000c0403c7d0304401d01d201c03407500081451007a52080040e00807400744c502c80304004c003030108284160003d4078002900e000402d40c1c0b402c3c0325a0b00d400041003a28503005200380da401600d03041040300d90a1403c1c0d4050081d40b0b0b0720880510329001e008056060b1802049040d07002e1341e0b003502c000c5200303095081390b054403002448001000c0c260b0140103a810322075800309000740b20901c019900380822204001307d80540d0340012310b54441c580241c009200d0341c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614996807 1250 614995557 614995567
    0x40f0611030f0603010f0605031902270a06060504030b0606070501060306022109070501090b180409030f120c081306020c0a1208101206050c07050f01051005010c08042702 75
    0x803003007440040c00785604600038011b02600580c1d11040b41c0080c410f40c1d40c554000601c0071507843c0c6012140d014140001c003280c1244084015070b00e03151011402d544290030490b010800811103a1103500c0c041c0c40c042c607020303091030f0441e6605c1861650213001548142800700308482000400d400040c040c0d98000015503ca0200308104400d140b5184c40700101c10201c500012905000094a48201e8505a449080c003c0c0b8084031001d46a000480c0c110914140300c000481584032030103513500140c0700e555011040c0748840c2c4000c1c0804903100352854640e0400c3d15010b6000c0d4484003494000c4000c01380802e985d5200e103032010081c49041c42c84003490003000d0280702070000d020003c500c400050388513581c0c070740d4584149981c01d104a0080101034882e91841902140c155804681d02c04018802645046080d40b103140c40c010a1081e413a2803a07441e5002c211280300d242005500814003030038041c8000c501c0755280d5601c0e0245011b41d100742049800c8110701c1524140c4121202e0758102c2c0c0c01c42d07441d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614998057 1250 614996807 614996821
    0x120209041506080a0b12070b07140a050601172e020408011a0301060509012103110f0109030e04020c0304090209031911100518210f070503061509040f061103 69
    0x1c01e0013250b55418051402803643c1e01420b040a01c040442d104801401e409420800000003903084048156014a1079883c2449401c0c2c08202e4409100d0089004001c50b600d4800042c00288042c910080c554110000c0c6040088080d0a9540c4d54804520106407550b40070044400a000c0e5a115042c151300301000752141800c00c504180d1105010340090100c551940140035104a0a200e469007c00401045c9501080e410710511120b03071080c6041e903200c0c881104010314010320b070700d92074a069540b01640010560005424543d0f4001500c09508103000c2040c013a4481c0547d1040c00001500000c0c00a0f003a6020311090800d030b40700e0314204100823424206600c01c21000216680242004409464a240a80709031000c00c1c100703990065281100d0024003000308a00440000450410310b540c51006800b03005911114a0940080034114a45810503190101c09081217900c0100500650940d4580005103a40107401c007826107045002841d06e0001800c00541c51358403c08084140018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614999307 1250 614998057 614998067
    0xc0201140d0614010201060f03080d1d0f010e12040e0a0e010203041202060601020a23150916050609030703120e0d030306030204381201090b0402010f05040303120209041506 76
    0x5880601106400f8160b482005908a402d1030007007611010124100b000000d1900b0001c0140004546001c1032613408040c000c5039803c040d50f1010074541140d03001c0481e4448c00d11500400112010041c00584d00d9880000c1961085000340400300c401030001038044040f580015000d560482c008545d41c1c90542480044040c030030304d000005002c0e410114451f503200103140074030769800c20301000e02864481100146800c2c2c41c4406000e030701560b000f03644000580c400c035038880c0c0c1118018040501c0609241c40900e0016003085200d224140100401d9460016041c4250307a8055407400c60942070030390075110801e041c50301c25072206050b10510708041d41030300041c048078401c0c2c0c0c0901410942040c90a11341c1068140d120040b04803900e0781503032030010035010b030101c0c4000d4428181c1c8048500301c41c2c00d4815904c802e644072000081404110f59016140e0b8001030540d141c8581050700316034000300300503000d07101c51603c1600440c1003100395441341d000074403001c40020b5066595907940c5020f05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615000557 1250 614999307 614999309
    0x120092d09090607080105040b030c040501171203010e060118080a0503040e0a0524010c150c23040e042f0f0102031305060a03020415050301050f120c010c0201140d06 73
    0x201401c4000c0210701002000207400c1d000d5015511041744580c01c01c0c0c10b00c0024950700e403425070715102c0c03846403d00a1b115880741038003034160524090405443d2140003858404021078100c00503c0420040201d10703140c0c2d030419006a005d107010304c0d1041c00001d48401c01849a0004030307a6000e03410145c400c1110020041080700d0b03609140700341c0c594602f0a00411180100c0300c040e205204016002e880513a00c021000b50303440141003000112606441e0018241840d801102030356581c4c003404411180c00c914041c00040030512002c203140084120406140142e00c6459810200c05000c80c0820100c4c0383c0c0c2c00400700d00700724001d24107400380c00c030070400c800101005806507000201a0a0952000c0200c8100c0c581c04c2e030041803c54500320910401d9030002c0a070000305a400c0c0700c04940b014035141d06041103802603603904d80303a50602d0108015442e1400c0c050348240034800c005801c40f0008100d43c07403c11402d08201c001008039000580e0808204a07000d000e289001640c241c003012241e1040d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615001807 1250 615000557 615000559
    0x50307120e0f0f010f08092805011406011e050922060f0f0b090316080604060b06130608130b0a061d070504120609061e0e0120092d 58
    0x15240c040490140900e40d90f00180d0640010790103584641c000d8021800715801940c14003c881100c42c2c010008142070020b03000141c8004000031402e414800309003d08561900c0b8218050f140b8101080013903d1605040c1ca0351218028a044a11101d80200c00341e41a24101910035a00340c14100d8040a1102020102179901460500081496100c070000d1505482e00d01e5450b0707079000d0500b4618030789500901001a814030079031000006115052240e280108841c40040041d81003d150200c01e5410000c027003802140c05100b500c6c0450341d29446541180c0860034032074090b80390030b0703030303a02203d8a090310240081440000b4010f40c81d110f60300c03210440d0900040004140780d00080300d111400241c07004800220188420320880a00c404107800e1107114040014039507802d95100c900303952040d500040304c0a6800691603501c84203008500d68078550320000c0007040c20307001844d600c40b40443e02521140d10045901c0d8180e8440b00500020085c50000801d90891030000902c104012a1201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615003057 1250 615001807 615001819
    0x1506080906070c080a1107050d12110303070e0618040e0d1403040804030605100e0403030519150b03060a0902130302032b0f26041110080f04050307120e 67
    0x100c49510400c030f0100708907400144d4501d895400d91040742e4a50380d104540e141d0307003d01c0d400040c03c1d075200d0500c1d000c4244511010311a07a00b0080e000381c110840341c80a520560420010000389a51011050b40c106004480080d120218800c40301e071b0030080014040c0d00185007107401180c02e00000307804060a031113560350f1402ea24002a40d0116800b09840c0200b17444401e100070b000190700350700066030020700b0309a0314440680d10b100038141c0580543d0154042980d803014440c015480c50400030350000010310a000060000908400f040307014461240e251201101045180e0340d101518001001104019034647c0c07000c1140702008205d91100300c2c840d11481d070400c400c030101d040d450342e0781f0409000440300040c011407003540ca5a440720f50100800501d590501a40c0407004100f124044c21a80750840f549028078141030401003400174644070780aa90740d50b07400301e40e00941050344510712001d1010143c460b85405072450040700401401e80e841303c0e00b55219298010703501c1e00700c0c4400b242d00f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615004307 1250 615003057 615003061
    0x241009080f030703080a020f070506040309050307050a06050a1d060d02090414040c090203070c0c060e090f012d03020a060c0308010923060a03060c0c0201020708120417011506080906 80
    0x5001c2d5284104080180810014030008007818020390103089080e074101a81885e141c1c4e155038560074414112400c42c041000c021040c4100d05003080102e020b0a01510480c42003402c2c0800548580140313022401040042e8080200300303100c8078541c0a5683c00070307091b1a210401d0304c1d009406504201e402a024031700d0b1200c40042d445d100f45009009a4000044900450520541c500698002840d0358280450700c1d55403400101c194035420002c05040d650b41c0003840d000c00810942d282c016041100c01c5500f000103100038862300070390310400f408650186480355681d0040e64000c5c40300b584003942c0321910740303400280d00d81c1040b0b81c07400181c0710365074030011a07803902860000c41b0641525043d005800c40b5192021100510794940c000c00003d042008030b550340c0e03881a040d01e400c101c4044c002100c2421500442d6010882c04001c0e03d030b06d85c027900020481030340c01b220a000383d1040c0c4115601d50b18610344c81030000c0d8480102c592001806451300380e1990030203002c01200341e03200452031182d200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615005557 1250 615004307 615004333
    0x180313090e011506080411060301090509011a100c2a0602061e0601030f0207020d08041703072105041d040201140703020c011d03010f05040506100e24100908 69
    0x440d00030500e05910901c10b41501300f11044450000c0103108441100d9051400400b03a80c500000e0350007401e652101103024074055031000e0a41d03600283e00010007070700340941c0c1c1c00e580d110002031140324402c3c5030100030000e86007882080c4032000100b2102c40b400410404880c5a400c7c02c100095410a400f1511396848030691945042d0381c3d0f00d500404003800002003040c66109410607061900314560140c1828a244c000501038400000308656800c4000f50801484944501c521580d0007840e018500b007007103e484004011144540d6103200c0d1b106000c40041890203038003940d01a101220710000c0c070f000d0980125081c00c2e0103a800307034040b6514800940c4100b9103003041f80c00f125490760203800061a002300559450359005c4140302c21601031032181c0e2540c0c07800d100d071a401c2c203883d41001c1101c0c141810704e01d080513406443ca0100440800c424030000000340c0d102c1e80c0080c0c800d42c1140080428103086030828070000f09055104403880c1002c04880d038005c8000c42600e100005941e0480d510344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615006807 1250 615005557 615005561
    0xa051b03040507091505040e15010f080c0d03110304120c0504111911100f1a03030301031203090605150108090106051c06150b1c020a120203180313090e01 68
    0x40c1c1c014115482400140006040b54200203020749509503030100031900c840c00201610300c0d24410300425400044d0640c1d008400f141214010106544000016070a110030140c9490031030000600400c1c0d00e00f404420548140c186803040c0981d10152510b65440b155a5001219154410b481d2035541ca0008192894544100a0036094040303003546440c0c00903d075282c00140812a00c0240440502e941404040c14007031900501076a26001415045002041d001c030b41d8510310071b07806211503420003100768030004100c07810f40750045050240940c14000c210094030203980004c04640c100010300c6100d4160152030341140c04262140340d0b0507a500940705080311520b10a10b540a85081a090040364030118481a842c1c00b8440206100e01001405021b81d41554040c01c2d501200140303c084134105500c09002d4001c189000b985480784518000f04182c03c260303040c4c2031090703000010410401a603405141e5042808054940b1400c14040880010f14944980344026080c901d802c90810018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615008057 1250 615006807 615006811
    0x1b02151b07180507051602130507032a05041a0403170705101401060c0516060206061c03050904020c0a06110307020d020f030a0c050f01021611011b0605060f090a051b03 74
    0x45c0c1c0e1003904241c040d402440c10003003904030a0360443ca40141c0384800c005240500f134440c0c040c0761400b0910460042403031a01001c3d078140c1c111107d850300c40743c2c200e070365101c2d003143c0c11211000d0001100711072101d0100c103a4440c0e41d2004020401d000380343c0b66041c041d9009230441e0b40c0140d007640d04c8200107140c04416a00ca000c40c44c00e080f0001c00043c4200d50040b2694405680070b20100e6000c420a034010358001d032941e402607005a0700010400215142c10341e00d250480720601c0300342e41c2c49015903038050040d0198050302480381b0340104140a82c10010004221101c0d04450203100184240c842e513034299005176018401405a134044140880c00011840780200c45a0004d52504c0c01c00a0102c0703980219040454842c02820442a8580001d0010b00046644400200382590f960f19045140248405d140c905000d02c0081a0521440c2e80d030b900750341d0a070001c1012919655a0000030020801c0104184d4041108000d2120100c21580010701c100c841220052152580303102005081c081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615009307 1250 615008057 615008071
    0x180312070f1719050d0b03060405060103050606060a09090b06070204020a0c0615140d02061201141009051c0311120c06060906060a030c180b0a0905011b02151b071805 73
    0x20f0980c04072403e00c14002840b50662452000400d00380c400d00081c18100c00f903c0a44039980294014828004284103040d0804001c0f9420781ca0800340c070b500540b04480903c64040103507a6011246c241d0344400e411030b00e40c1e641c0280308651310b166502000d000c060300d030325050750f19a241550000704500300400301c000355040e44141c24003803130240c01004048040c074402240c01070380074401d0050001400c0c10007406001241c02c1e10707040c2256602400f03910b405a43ca240208900240100b00540743c80003000049080ca1040d000300102500b0300350b814030300076504444907102d0003002030b98040119003e0040101c4500907102d10382c030b442c0300300218590180c2e03017030b50302203001c00a038600180a54000b840349001d90811517003c1080290000c00232580f50f0068000d850300094070194541d00501c07410144c482401d040303040200c0c1c4902140041c400e82030090164944800b591005583c500076507100300380300340030100044040e0300d4058a440c020f02c18207010300b50410350044244610f02496110b209 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615010557 1250 615009307 615009337
    0x105040b0d110f032701022a01060305060c040f0b0309060609040c09050114040f06082a120d110d0e0405070e0d2001080606180312070f17 61
    0x4440200c80000c04019541040480c0704111414a0800035005140705003005040c5e002110304c40d130351030f0140c2c4060610300307500c0740d02c100481002009158892038074100b0311107060703038040000f4842034010aa10b81002c1c06500c20f4008010380d0512201c01881a54910020050b585607a90031286d0719000a590402031a00078400140003410221080da510034010844034032038a55070203410044900a81024042039020a4007007074508042c002c201c4d401d401460100002490485503940740d400803640080303c02801c0020300d60f80b0065140004241c100180003091003150301c02c5090391184510601400703c2e5202034402e40c0040301084400c0c401c3c0781c41e00c40e1036140840340f04200007000024400c0c400d01c00350021091154840f4410690b80d02d118982210078511400c41040401d100e50032a2810420040304101040e1107050aa81d110818040b24450715a051304c006401e2a00c984c41031006c4960200d20101400341000c140003100340103400500c04011800e00f8000325105000b180c400c005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615011807 1250 615010557 615010567
    0xe07270501050a021507051e0c0606060310030204150801051b091311120103020906040908121e070201090b01150c020f062109010507050a0c110112020408030a0e0105040b 75
    0xd400b40780102441595441900c4640707000400801a002007595004009000421088409281740c507041e40791a00d44040c080c00d2204240c851503462000822031401b07a00040003007080141c08040c50005142d00900502000407141070360f0780c5007c19841001c00a41c00c00001c02d245918003a0705040900c0b030740e00381030710384641717a8180074141620b0780495550983e26402503130030750b02150191440c0007032030785201c10070351442c01001074101001d400e40b403043c4d141c0508400000c5460040314040440401100d2855440c800054403107600c5039040b6003100750200c00c01a800358107500424000340b00f02c0f803541c2180d80f00c08649058114280d00c800200304114029009481c00c24405d004004006004500d010344107402070f9460a8100001c402c1d600790a07050011562007801010341c01481c42c50940e003481094a030080480601c5200030303080c6a072112544c02540d200c0c5d5010a10001245419981c80740d41c1c0e00155078a40c420504880010a40482020658881d070304175011105965812400c1c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615013057 1250 615011807 615011809
    0x803160809060c07020604031202010902042004060e0f21010f0c05040501320d050a090305070803040804080d09140a06020619090f240b060301030f0f06060e072705 72
    0x10b94488041a6441b50303083c0800400130300e59407001240c1c0c44140e800072a80500310320602c000c4d56030034002070a814140702c11000da0407020000b0350782258060301d002c1c0b0307041c00b2240120794442480803103141c0081034000070840200d005085004aa4041c0008024402c0b4080b5503c0444070f41071a40307000290b040004002c0f640c030980303480d10352058110b00f80981d0101484200e100c103038103e07842a141000401c1c406c05600d200e104403a881500900103120f4136480e0b41c1c00410714030480100410020000c4003140074080c08106481c041c0c0546401c4034442c212100c400b8051909a11030440c540240c4510340b601400e00075500c0d011074000b6001014281c4401034000c0142e05200c070640c6040303590310700002c0413800b2074140441ca103008922a4008401340d514030301100340d41c40702c1d454681c0c0c180007035803900340c582400722411a908051400154030301403401c882140346c0d5640103840c060903c4004604c290822094034004d58054460303003a60b030391508420901000144807503404881844040240f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615014307 1250 615013057 615013081
    0x601080601080919050d0201060e0937030903120c0308190e0a080c0105010b0c1f0b04020d0501060801060c050604060c02160e0109050a0207051902040f09080316080906 74
    0x364048040ea00303640e02e01d01305424401c400c624280c0341544141e290201c0550284540005840625948055440c2100e1010703a180c0c032340b05440c2d10306240301442c502045c40034002c0074000c01034006451000c5102c0d00340245a041103010648400d421012520380c0305024289900101340e00d40c46640995640e002903010710f01b040004a81031589400b840030b0009030a016034420346106809a82d00d800071604040d0844005801000f0100800c10040301c503080d0000b406048040c1d207602c2102c012080d5007441028102240c1450340042c00400c401c2c11070700c0e0326005141a1103a55480c50700903070303031400308641d000b041c450b015006402040104000c03035203d8200150b002c0007801142c1c0c9801c210601866411004e6228410308441540140103683c102d024560b04003061103019402e00701c260b1212a290482d881c000c507420480200e01c9030841d02da80d0801c0d03400f02d2150200700072f40704003030410b5882c42d0310803aa81d2083d41c0101c40300400c010700941c0d009005030039000040010341d54004260b08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615015557 1250 615014307 615014311
    0xe04020f0411131206050604050c030c0c0312070320131403010902060703080124140307021c11060f090a0803090c0303040303111915150306020403060204050a090203060108060108 79
    0xd0220001c11043d02d0404581140b607000300800c2121001060050130704404994020700b5191190b810102030044900d00305090341d42102211080c25920954945404e245200d5a8407184d2400c00c1a81003000c030326056030001c800a0145000c0c00550615104c00207911310403205140343da1802c01d2010301040c84110046001c1101c040c000055002c1e4580015070540c015a0301100018004030050100c03109102c807500690f0340d1403800c8040340d4560800075107061030003400000a141d002c00020f01240c802c101200200c0024100848100d80c5940d000b421002c1c030360b00520b094070507440441c0105001c5e540c0c040c81010210003400c1d0121081d5100d0007a98005071035081c0e40e2180414045035664284000c00c0214800d40301d4517045d5072102c040a0030114410b10307410104813000010b001140c04003100d0340c031000951074002540314407103009040e40302c071641004c1e055510119003c41000b01640c01002500d4046035003400d02666450200d0030b901c400c03101d041c001800840451419401800300f0b913 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615016807 1250 615015557 615015581
    0xf090501120b030a05030310030516080c0405070215010603020c0106050a0f15021e07061e0206151305180c1f030902012a0b070e09040f0602130f0603060e04020f04 72
    0x4c21240c0c46031600343c6580c01c02d440c0c51190140441080081000c10064a90a894000c4401030b60f14030345030344039403030340c0340a0b141e030380101d80780c0002030341451081c0f090f0308201e00b00059080d06940c45600082c001d4104940c3c204581d03103040c1c4080f0f1035103001c0e8419070860342403081c070803c02801d103010348861902c0e8070031001c154854402d4a1000c4881c3e40c000c5002c40a184004201c0b031460039100a212442e00390520b201c001d400441460550390101d4010b0b0300200d591900104621004049118848101d0301a140319240c207003482000900119580c1006016408840076541044100300c2c000c100c40e8014446101d074070300d94802081c0250020340045005040801000780b42d0120748030a520060350b140c250342085006503040000d07401c0e00320b404c0046e61a040450280f500041400c0100c042d1001d0196849201104100f1030a030701211954102610425012aa25100d2040540c880e000300740200341410f9000c02c10400d4203420328441c6400516041c14003440d18103100080440841d20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615018057 1250 615016807 615016813
    0x1e05180c042c1908120703060509040b06012606040605090105011e051303060e010c030516080c1303033507050705120f04060e091003030534030f090501120b03 70
    0x403e506101c1d008040c0e4114003640c0d9881d41d8050340202d80358a400002c1c4003d05145c5000d0051205441d815503107a803095000300740d85216110100140d501691140140d104403190f09083d81618482e2090381e4000c542c10394060100c6c5480d1810031001040900070140000c0c06401201841c0e10495907030310142d0500e0030154505045000bc0ba140c41c04035410a840d0b1a486991032241b10400748a022840750192030100028184640d0b0404e1195042072141c007080060400700f9518950710341251802e006004000c962140e40340360140c446001d00c41d01c0c0548020078115290006070301010b94901200c211a066825990200283c40e5900310b460255602e2003100134041054811030300410714075481c40b544a4840e89000d000400d07544007807442d103000da06c109040c0444480c25919803c2030301d505d410700315225803290102020b901001c070710a140615080c0d01c034854000da1440340e459201e00075038806402d072444a000780c1c0c48410781e102d424005807500c0c001c050b1081c0140c0c40f55070740a20040030303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615019307 1250 615018057 615018073
    0x315040f11060a05181e0f0a051806030d0f020703030f11010f0f0e030c030304240c0c060509030703080103020f010933021c031e05180c042c 62
    0x4558940c10040c01280400d038002003c004125068611014170403003210001010084103e1040c1c3c45103d2514a40c061140800544419620340c21082c001c1c00740601030036103501d0700f0301c0c2c2003001c440c051700d00c00d0080c05204000c844482c81144c0d000c0c1748450340e030018a280d500c1c40e9011586080d084d4644400c0106034204d50302102000c3c01103c0042010103401708608030509840d40840391a800441a00d0740204491000c1c0341011040c1c2c3c0e801a000185089403958500c907845074000405d200f80005460038100c1d081d007070b8100410140d02c6010f42070801442d03417030822103135a91140134009804602c2e5003004200604e4151402040040c0614142e14500d0703888140740143e4110000030800611890550348043d884441c07440c15000300b5200a0400980d1030449414501d4034180c0030782055100e101071b0200c1c0d0407003403400603c0f294400c02001a0300d0302c403018807100030140740707060082c3c05038850418241c03a250041c000400403942d10150100030310b41ca10100994081c040417154058121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615020557 1250 615019307 615019309
    0x30b061009051c12020a03081801060b0c06040c061718030c101a0a0e0a0506040b0a03050606010314090304090504050f0a080a0215100b070203390315040f11 69
    0x450561660b10365458101806441d0012410000d041101c00315030001506c1d001180d48540c2d050b80101300407400448940c00e00d00c006002d403000750001b10460340e000034038440c0000c1c0010614400c03402016020102030720303102e08079800384180700814450000d070030106901841490f029425180340b80e080703d00d050601b40e81c1c2410510b00410300850701d0764a400b0303a000442030142000155604488000c900790070320f4941c156000d8041c5c00b4160407513841001540c1c40d15542d0111189000003052078080d036607281341c00c40d5a00340440d03205001a09081e01c114001e102c07480441e02810700103014505182c1440b03030000040074000c000f0794007031242c0040303420a90004e1100700495405440c206540e0b00540c103002e031a00001c2582c0b6081032181004026241109020840030f660f44071059030713901c6219000103880c0c0761200c622064034216054040444a119040b20031010641c00c250000d845101002c2545408410300c0d40070b410014500024002904484c80050709031082104807550710201c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615021807 1250 615020557 615020569
    0xa0216051f09031b0e3105101109030f0c0a060e0d080307020a031707020601050d02122e020913090c0906120312051b2a030a030e07030b06100905 64
    0x4c8026468600c0308407052190030400d0b00d0b8140c1c807550412400117031040b034030703514441144039103200000340c0c021801907820400284960304240c25088010b0000d400c0d900e0501d451940842401e41c40b9108004c05400340c5200468103400b071f8103004000c180c01501c0e1407420b807010014180c2c1c0341d40c0003850200364030000344c00c580554012081640109481c3c06980b40203040b24004018034020b50034200f08000300b19500140f1281514025115682c50030743d14804201d0070700034001c18071481d02030407d0642076421481104481c4280c0091003c01d4210061032a00032841080007460300806011052000c6441c140c00c1440441e02c682c043c140c40030b13901c0d00c0410850784d441d040448080d111085500c00d240d070204d00420301d810004402c0045051403820400c9110418101d071604003008136520683e0402c102803048201d131050321190f50b40d04c1504601d511381e40860301110202e440c04d40498102040000c50500303499001d1070034165a220707141040901d004a0040c0c0b4108644801c02242c580c84d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615023057 1250 615021807 615021833
    0x61015050904090f0c060507050a08090103020f0711030c150301090203090309060409061d01121101121107050d0801050319050715110c060a050d0e0a050703080a0216051f0903 77
    0x40e02d03024440d00340c517241940806070160300000030400144481808a80081000f8009507401501940d0314001680113034041c3c0140e803160040d4a802207405403c0c070000359081c4110a5040341900c03089030b01003040020140c3c1ca0038040107015402c0c00140f041a1155004503002100f0074226410640c0040004d092030784240c01000345140c80e46002c110401e05000102d08041d4114080c55840d03040010700361200c1c660f18030240c0040a0312508486503400341007000007003400f1032008d1192003040c186012580d40f01050482e0756108401e0540e510600c02c2c0e0026042c1c40005014025441620306c04401d070960b1800c06079024066601c2c0012102c143c0666480341034000d840d60b0b100c103a840c8500d0780c1048020507416020f03290802c01e00d030f00d00ea072100480300c0741c40d0407000020b07403101541c540c43c1c0761455140c001081445589001700c140b00c50080505409007890742241d9406403002000b0148203414401d84d6000240c242e04812100c4200000c400c0e1140103240051200d03649484559a007000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615024307 1250 615023057 615023063
    0x60d06051f0902040302061611060c0d1407020108131401020d050601030e010902090612011508011b030b03060403050a030212010906152a08041805010f060206101505090409 76
    0x50420302095840751101458010080c1a00071401c2a15540100d503840c42010401800c1c00c80e4030044104100251500c0180e40501400058a64820301d2180365284004c030031f48000300b200c00303442405030340c910740c2110780300341c0d041e0b48040198a8641111408004103d81100c0101c0070f00c412243c40c0509101030803a6400840c0e0115031800c00d0300014044035100340100213180d0400110002503210042c0c1ca030f4215800345c903044498118181214010b01d400050600c1c2c9400e000c80c0042c1c00401508030391400c500c1d01d070f00f400300c18507208010341c03c4409024007603070903400c10000100400c1c020360107404444078030705003d858880440d0b5800d0009078240c1000c000180d50b4030081c007030103400801007912030120307041c02c41d811020080c40b008a17040245c00303500d03001001c0e14002c040240d000709850003442c3c2620507281c19240f060719a4040e0401340140c03401e40c0074400340001e00901c00100503000d43c2040781c40010003030410304450016400c081c032800030b0110030401040c094036544a20b07060140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615025557 1250 615024307 615024331
    0x11011b0b010e0612060c0307020a05030708070209060a030f1b0801090c080601062a02180f0613090f0f030e0a090207060605011107060324030f0c06030221060d0605 72
    0x810404001840c0300c2c003406850298040c1030311903100c1d100000315590000091520f003900e030343d56240103d15041a5407002007060002286100030400843c1c003410700684211069591980c0d014103100740902c1910000c0d1840a5030064100030a800c4013400e24003103003600c4a2019207441e204100d0035640f4a03941252445203190080012a500744030107405071441d0324164640307400c484a02c80047c0c0c0a540c602106c1c00c070400b00d00b0b0441d600c4014a1006d10001542c4c0351161a290302d454003070550031103ea9000c0d098116110741c95442600c11000302503030008641060054036140c1ca208092240c2c2c0482c1840001088625940d64820541e40107100020300541d654483d481d019061780c903250300003410b122903643c00c1d241c3d0740070104040050300e43c149400074041346130501a181240e181200354500108001000c0203002c82c0f1510124103901450001e40341c40d545034411000c0388a004085040b03035a801200e403c01720480c503840703608a0002415650803441341e81345c010440b4001c0c1c0e14400c80309 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615026807 1250 615025557 615025559
    0x7121211040314010c0806010e0105091f0c050f0c130207020f060c030c010b09280609090609020f0d1e0201050c010e0d0f090f1719030201020901021002070203070311011b0b01 77
    0xf40003406125407108046c600040141000800030b49146009031115050020116801034507440e8110b107a48490705100d1140030528502c00080d0800c0002d11043d1400d0091402c41000000e001550517612000607180820340b05104134900b0081d0030000040381d0001000401e15010740c0d504001e8001484035802941d40ca12024042c9401c548810200e140030f03d50740c604010840c0d418801102d0000800c50340108008420402d41c1c00030503141d04a60280c0b40b81c910f4120a010107a44203038641c510075100064100002001c100d040b0400d5640200241c400754060740d111580c500b25604480d206041c0300d0305140b40c1c1020705003034a40a8041c60310b04d50000082c0c4442507400701140c0c00031150303820700e41d4105041c50b4511000403207a00920003c2e49000c070401c11103900030402214004030712605101042182e203030081c003075401400e5442c010b10a20103511107100c4140700310f440c9242c3c02001000d0b00ca1a607034682c00b000c01001000e6060001407030004032400d06801300010305520074170000b8465 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615028057 1250 615026807 615026843
    0xc0703050706091208030a2301080601030b07020c0922081b010b01051918083c1b06040e0a0c0201110a0c030e0f100206010e0c071212110403 62
    0x35450b07a032002c0e0700c605044540c580417034800c9040742d42042e0610b60200d441881c8a01440740040481d005c1c10101e4075102c000196000c02042c01c0703040e43e101d01d001e25a141c82e504412130740c1c2c0098000c03140d40141c04501103884000400703d043c01820304c036200e0440410594981c1000ca4000c4c0406681d0700806200800e40100203100e82001c0314801d00300181440c107102d82c185042c1092030001024420a051222071001c8442c00c400000c10b9170400310781c60710100c4c41e032011035402005607001d44c3c400b201d00c0351100960341180d01032021802d0001010788207040031094441f554040709864101404010204486041188d994882d403220344c2e002c1584158018001e0071504110808080301d00c091002c0d81d03070340760300800c1c0307095207900340c900340b071003108841d0014010100c102083c5510158483e06002000d03008507140303040341c4011000c009a50b40700070326940d152180c03110081200c0c9001c0308a210084c000c0164a001d240700190001c1d091400b04c03403400f00d42c0d009401c1070f02c1040d0710541010749 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615029307 1250 615028057 615028067
    0x3070501060f0320031903050a08090f120318060103030507120c02010e060a121506031a0105220f0b09040c0e0f060702220b030d0c03051b030c0703050706 68
    0x300b500c071000c0c804451440d00d03440e6103400300c11000b0400c1050507949540c940e40401940226800c0450300f03141090f9149009000756102a40c18001300707070140e0018400800119074134030341c108010042c100721246020381843d2075000410f14001c280d000c500221010b0f00401045001e1882500c90130750b00e00007401c1440400b1a800c40c800d082003c00da8520300140d900c5001c084181405a41b4292550410103081c2e44080f2202d20380302d801850054441e001c0507841c5805411180e2070b4404004c01200200b81d210b04450200c90580801d204000032061364480700341d00c06030118250003525415444070070126a140441e031010000b4840801c01c034445261521038981c400c400c1e414500c43c1a12014081040301920a00040c41024042140e6082d5180c03c0c640f5000c2d2150040784414110b4040c000300b0060000741101c9000c4d100d108004094680180b882c454030755015200d0500b03040104255908440b42005400054002403000b403120680c1006807201852041c0d010704903003400c20000500c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615030557 1250 615029307 615029309
    0x70c0c0803090102030405040c050c011505040b0420090a081c0f1d01050a0c06051003030207080607050301051c08280302070b061009120b0601030b0a1d040c0f080307050106 76
    0x4150801c00c045400b980c3c00100300c400704c85003511701003044141e6070f1080d500350082c440501225401d003038182c020440030210580949008a80802c8903c18040602c4119040e90390345002c2c50219031840100740d110007020b172a2a8800030040700800d5202d40e204ca051401c5d81c1a10b1265040001e00d04850350303086400d01407a0030307062401524802c0c011821000d06005002e074607061060000d003800ca0386100c2c8901411181d0007420a102c00e007031948007203140f5840e6110540041c060b101c0c01241459010610b05c3c010803103642e606040d07900700010401000302c4940e950031104011400c5000240410380640b22100380c0c1440700000d60440c52098151100d0800c0031703000c15104111079000581e500f041c4c1900030a0a070307030800d0310702c08218096440c001c4030782144003a028a00d04000070070107651f5040d8030441c002c1e1b0b801e0050280003030522150110305c0c00b42100ca00d0003000d04070718549170b403000c40c0d6100d4040c201481400759030300d964200000f80d03604400265000020744000380301d02401071034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615031807 1250 615030557 615030569
    0x30815040e030d0f02090a030311010605040b09180705040509100e070506072a0f0f0608010b030105010e0315090138060f19030c1701050a14040e06070c0c 68
    0x100c400c8408004594881c843d02040642d8640e0b0744260200c02402c075810b880e1114400b500b9941015200e003130240050542c3c01031061250700303102c800f003104e042c41d0080303125a24000d0300e6072003d45c850b8103924101040036400383d03460348213a0100244594035401400e00805d0726001502e0712030142c120340740541d00c4030b00310703403805070b2014004000c55200d00341200c010315003100e4244a2204810801303031021140742c90076100049a40300110714801500c1d82031044880701c8814040c030541d120300a580c880000d124000f0340601c01e00040101e54000d4040a41101c401415144ca00c0c03150341041e4041c40c429a4641e50340d030354400350070781a40300324001007164101c0e4041d00386124400d0040818010120509140503100100d0348058001c0084c007a245400e5044c1000303110ad011001c4000d0003810301c0701140c00020b242d01c5048100c0c1c80301100507811b8a03806060007818605081e1841001b003551041542c0080e0b45e02c4c800d17151480c00344030035400351040f940c80c40c41303500e5142001940f0341d001e5080070b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615033057 1250 615031807 615031811
    0x6050a021515180712020915031008060a0c0f0813150218040902030c120307050f030d0c0e1f05070606031a09060f0112060603051b040e0304060c0609060e0a03081504 73
    0x11102481e0445805d00d0110361000025a40707032444404980070441842ca81c03560080d001c014050703412107081104042c5c0e030485040702d0156942007084402d6a8100f5a143c0101d0700700c1c0b001c0e2906510400c8002e0b401004000301c50440c0019555807032003659551070003540d480d400300e40e1006010741302402d0307060380c101102c05215440d810380010b9100c08801001d40c0c490149040b40307201d03114003402600d00d442e8109054400c0183c05403013141d2179a100350000d480c92481c244132000c4050140c04500c024040260502880d041c4031924031484e110200040c1c01442000c0c012080011140d00078080a507110700c40340758044201800000b078030800a082c82100b9080002000005a1042d68045c111140b070800548840c3c09070604030014003160704042d01c14014406401d02e03501d1015a480da0f01d1406690400c20b9182d0340f55000d4480c0510301450300000c20150b030010115409800c150706443c00750700c000030000520020903142403d074200c101d0101c7e1441c020003480312500d04c42c2040f07540040c1c1d81 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615034307 1250 615033057 615033061
    0x40e01060b1207020f0f1605100203030f0702071e03060627020f0f0a08090c1212030603010209042d0903090618050301110c07081606050a02151518 65
    0x40d0305150080c141034407070602d141c03800240c0c49842000091004460b2005460a15100c450110745500c03c0d19110098102c05003400507203070502901c0118200714540c00b96040d600c5240e001c643d160009040f160840c0718014010500700c001c1c4080700340d1041400d410715452072440c6000402c1d600583d11150b801287e0901035041d0300039241c0143d0300c1d5440c090f40180e0302d03549003000020070b008010201c0407264012662039405908980e03164014081441144c40c007407440c00070444005052541261150055054010040d44143c05950040030003000581498420f50201c2c0c00c4410380c6508082c0303151442e40ca0f030000188101c00c0501c0d00b6551038144529001c03a240546200081e01c40c034000c010903000c40010400042400001505008001b4041d00c90f500740d840049030081c4601071042e014a0740c001401c840e000428054402a2000300d07802149480001d68068012124850641c081c2400e00d9507140714030b546083c45540f4a9444800048400d024000d0116140071610701c80ca2412003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615035557 1250 615034307 615034319
    0xe060d2c0703020607030c0c0e010623091c021509010908031801080403120603230f07150c120c11300109140a030215010b07030503040c12030c02040e0106 68
    0xe00381d402e880d01038482603900c5c0a036140858240c01300c0ca0020740000040da4020441400a48850b0b0499040e6a60703100c00802002c9804040d5521a070f80c061000390812100041c0d040203000c6007003111609240c0f40041d030031500450380b2407110b600c0740410020001900410703036810407541d034054441c03000118202001c8440c1010510320894201e4140104c510000301010b1080500b0505400f018000b170023400c0e5645440e41c80301c46d10700c3c21241420b01d0500c2a00503140d0018aa01d0030a04010051100303500c1c0800c4031a6681807403090348200034920550001040c0c4000b0710030602070340380c0d890041c114804c5c00c001043d041400304882c800c80c50018000d0050800351709104803d01d8019001c4400c202e90307000030b801002c16440c028140b44410b28104010500850000446402902a00d03586100c82e0b01e0185210024091080070410070f0141e18003007481071015681c0203205030a040e07401512050070401c0969084012000038944601030b00c11820300d03000e9010b13004c5410009004407800c003c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615036807 1250 615035557 615035563
    0x8030703050306060d090b0610170109091a0103110310022107091d0f010509070903060b04020706181209080c1e180f0106140f07030e060d2c 62
    0x140140401c8800710100c1c94075030325070003101c03815600d00004121070411850070b8a480c90013129090720640148060400c0d9a0103100302083e240f91720b840d01503180e801c0c000414010a40158251400c130440c0f80021151620007078005d000c1c40c01040b061b201100f1003c2051310b0501c002141030320385401403000c07000c8481859480c1c007048004e503038403802c1c1d5070341d00101f202d029100d40e022603050080c50040c1c0481f00d0b07488418a000c2d47d0b989401030066a2a90280006503000b51454070004200f900304201094082c0d104140754400244098075068203521842c0c16030f0a101a0364a582c404e540325075080090682c21000400a2420030b0a1001d180c52403090325032114400d07090241c0700c4c54544031003c035042c61128040001c01030902c22001401c41c00b50306c00340e46c100c800c52030407940c400010030b200e03025410210f41e07a052070b6492840c00c2c48034040000c09400840084081c00384c40d20141050780c4c0c4060260a002621007800210842408099070301041914504c180c11511450340d00103101000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615038057 1250 615036807 615036817
    0x70b0a11040e191d0f030a0c0846020105151c080d02030103030207060513121103010905060a06051207060302071b080106091a010c1709030a0807031403010803 70
    0x20540c48103440d6240b5070070034a204001401d1440151501501019801c081e04900c59007031140000c0b20180100482255968071034010014041241c4c14081e00001d001d100083c07a086c0c00e25400181501c400d101e20b4108154007200c000742203140c3c003200307400c4000c1c0340d00700031070448ac1407000340054180800341c01c10403a00e41540f00c0c02203207084040300401c1c211600f500e042c264040303d1130303565a1815841400030742080c002207006018071240014060b114600b5504a088040c17584410149040c16600503086265805c80e0845102807a048032030364207100d46041d09008001920322450180095411240ca03904480d1150190080c42480803130002021015503540303003030040c0c2c1ea09890802c8a81080c1003c00031b032080ca06820041690901034005908aa610120901049403030032107540d0028041c036401400a03103040901c1d00481c8074400d01141c0c440c500c0c50725034505402d10000c039051050b0200107682120000500c20f00300369010000101490210491a0555040c5000070f5101d2040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615039307 1250 615038057 615038069
    0x150a051308090409020a030b040b160503010b0307120c020109060605060a020c1e0d050d030c050a0c02040c0e03030f04031b05060706091703010e1803090a030204150e0c070b0a1104 79
    0xb194030035098859a00ca035070419001401103000344d603240b03002d802c01e601c1100c0c00c0b00e41030f09000100320b806010784050701e04e00401d03855107425170303003080b07404a01c54000403c10810014504101008000c0c01e1080c0c548460382d0781e0000c51426804d081c207200342c40303c513441503020701d204016011805a01064510042e403048074080d600b1106142c03000a103000801d00349600c0001c10000d00100070001807402e101c2c4503113860911803201e4600e419191405601d4403080807800b0035031008018078040d400350981600c10300304281d240503090b0204c2c1c6160800143c0005410f0700040900a1000544403076868002d0102d41e10002410203010aa060040707113001009542c54900c042c2c1081382c1d001040704031213080c1d50003688941c0e40d5400e0034400507003582e188070180c403465014400703c0d0010003241d4160102030032101da00c034915070034040200641a0030f0100a8100a008202d010200305000c3c018040503030031603200d0200382000c94001d031000e045140c40e14070345242e6050a4034a1401e44040b00c1d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615040557 1250 615039307 615039323
    0x9010b03121e0d0608060a0506040c0c0b04020102100c02010204170a030f050c1f0b130c023301090204051807092c0405060a0b06030c04090b0a1502150a0513 69
    0x903040c1e503044040d004140f88105600e0401c40007145204000880310302c00d1103404c03014821a10703514103020494040650726070000e0000012100800c0801102c02d40040c03061044030300c80c850401030302c42101c010828800040c1d4000504101d00c4071000050420552140041e1910310842c1c1d401509041c0300d80c80c410309020010950424401e400c5c407018105415100b00141501480c980c450000c007114640d4034400c0308408400420303c642c0d80700d0005144110b0b0020004043c091600c0080748480c5510708103000d40d03200b20f540f001e051400c03109000b00b0b600b40b00035072214104402c10104e00010651100b1092100d001c0000b060741c44110f842c1154a20711002080c03884100c100e50000c01c121300c0303150f1303d089600240320403c030000491a1041c01448800c014062000042140910041d20300300c41210041c00300340500c40303181d072216040c0d05000301445407c540d6242040041c08d031400c005030150300981c90010010314959030341c070f500090044c0100443d03e4076001000e940c042c00c1d5805405a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615041807 1250 615040557 615040597
    0x20d02150112022d151e030c0c01060b1b0d021c0c080a0c15020c03030c090103060e010f03060606260709270c08040b012c09030309010b0312 62
    0x526220b0340c82071301682c1c6150540d21548641811095110182c1c02280101240c85640807510202800c6d6084110900e0440c040007204134111041c0341c00240c41108546020000c44040c04805d128a900500c0d282080e143c8852130415000c0d506001081c0844c0240c0092841036100e0768007086d00004081c60651024040700303104011103582180201c014003501c0001070b047c060507001040e0f020a144a00b101e844150790814000d41a40110030150341a58018008211014101009030000180624000130b00c0c0f5610307032214840310800e900c18400341d00810300a0061000034010b8a001e400141002044000505044085495601400c1035007035a1403021966661003500c1e508003c24029007100c01402c0b55400202d05201407181052805203007003c100c01346c078051000188515001a010324481e86098680c0e55801d22080c078401000c00c0710641011f0311140720048502660b81d80000f5a01c034500143d0580c00c4404501c69a0710a40c004505000c240800c03c007150701140ea03040c1040016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615043057 1250 615041807 615041809
    0xf0a0c0c080c0a0b0109021309022b0b091914010303080c28020304090b0312030f070201020d020304140d09081e0a0501091b0905100504230115020d0215011202 70
    0x10601d1450000d04c11881c90f40000340140d5130760040c0400c1c1041e02100e5114654510100341244511040c014600340402c0180d6405130700c601441540741c0f00c1c90000700f00f0540000014500e800201c84003454203208000c100480303000382c420b1000001c000503241183d9419600d02424501c40200348012201001500a40c0f041754100b10b0002d00400c424107000e0300004440280d12034000b4007820000ea0300d0000080094034001442e90b00d5003007280c1e417103865078894161000c0a0781c0005c020384155034003003200b050b40d032401d4401184201c2c0254240d1a1010060300414205070742003041400b0001841001e104c0c1050100c0d24580100c0d0322801200840042490710741000c0010b14054040e501c2c1071000710901070740e54000c4060b1058903101c0c204aa460380f6181040303d0040d101c918520040910a002a0070070b039001448100002e0f4283c5c100f55040702d00c05403a1542600014500d0070002c145000c0d981e0100030b000354030070042c00640340402d101d0074810088141403007400c1d503401c90580c2038025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615044307 1250 615043057 615043063
    0x50d020a05030a06050f130c0b0714070f0815010e01090b0312040303030603151406040b0d021816050304032106030b04050c120f1c230405090709080a0210031e050f0a0c0c080c 77
    0x840108bc5007a00c0380250380b1000724149122038450303e1804d0140e4140c2010340352030b448009058410f007000711030280e42800d060500a09100b40007580500c146200501900705880240c0f004500ca135030042200b50a41c07419640b0042a2070404046a050000c0000c100104c80c50440c0e0282e4281c0740020318040c00d40c001aaa07281c0c40702d000c0c4d080030141071804181c0e030011403103602c034001078040d0b500b0340942108111540d200469002d80001c00540c41d1009401d481880c00d010029a4140861010f44075202c4014036881941d0484441c1d0244034024001d043c407c21100741c15447d82e000e400500036000c1c1d001c0c0c845032000c0007103120f44002d240b8905500d00619030b0801c043d4418010512141c10410005000d80c06401303640e10030b0b510400000c1c0824422280c030710070b440e0440c4c05031461120360f80c03d2100700308600d00750360185511500c4e911a1449441d9a5196041c40c410300858a403c0c00060b61a10001c054130417000346041c01c4910b0b40e0290400100038045922809a0f03988104820b90581 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615045557 1250 615044307 615044333
    0xf0e060f040b030f01080606030723090c070203060a02160f02060c0a0f052107030305060103060b0a090f23010c11030a200316050d020a05030a06050f130c0b07 70
    0x260000c000326021500c4286280a0b40c403842d4649104105a42c030b50392420795a0204a41c17203039140d80038900c18049903001d400c407a0300d03d05502e101020a15107000000d88644400c680c880f0a240380491010190300c1c04002d82900080a2041149001008120700c040030340481d038040c009140c145440000c5444110032102400040c000ba10f00e0038a141c6051b03684901e50060a80c1c1500c101000c080e10f503040011045498901e8014461030004d85036403c1d0060507000f005181071640d181d4000070090001c5009156103061070780c45240311410402d90219001c4140c20455030001c401e034180c41c50300780b40e50f40c840b1a2507090821042d42030551900200e00700318036000542500400007148100302d05464000e0f1442c03d07c120a02c444030b0042d00340742d5241d003000c1c030190315295594010030443c18030518000d80d541c00a040c0141e140c2d220804030b0310f00710500700120b885943d2001009003414407a0364003604194002d40c0d0b40d600e400f60b62100070f20002d250007001032485001030318004100806030522 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615046807 1250 615045557 615045577
    0x1014060a0c0501090c0e0a06060e04050703090c090c020f070305032209110d0c0e0a051009050603190b1e132702040e071d0a02360d030f0e06 62
    0x84465201d500c2e001c00b0317000d420301c10708140304006408684142c0355030040340150340c815994202180342c5041000042d100103054802491b030b40307400b0b0401254103008000c1c080c080205010030700d0660301c00b0013440c00e0303604500200d05401403081840000c03000b100303c401586e505c00e50315440c121070340800342c901061644500c021500d0149000010008880500381c4503e00000400415000c0001600e0302c02001c0e0480b90301510504c0c2c01c2c402441c281c9603c0c9100d030b840707140001c4810b0725000803c155500c2582c01000d064254070000c8182407042c01201340f41142591947c00d243d603002210341d2a00200c2c850070748a9400c80450562099241c1e010540348804151441410140c0183d040400d2190381c0007640201d040c90f102d034407040e000040b11720880b8a20070300469a103440800221080c10060301060481c1d80820080e2010300d0b8002800d59030b01500b009042100740d0705d050700f82101d50074505c02401400e05400b810042034200c1ca10004415580c01c1601c0036030482d50004040c0d108451810f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615048057 1250 615046807 615046811
    0x80c070f06030b0901050f1c0302120d150803090904330c03050a050c0f160b070f0206060d03051c0b0a0b09240f13081e061014060a0c0501 61
    0x61080d40b580103002c1c0700b1010b445100d80380c0d8031001482070700804241c06540090700c20300281040c681140c80d1a001c18002d1041e5030100700705614070003050384036140101e217135070301d851040003004011020321006080c03400c011444c0a0051300461851100108040c0c03d10a03918070000340810101440b102d00d100070710b070b210b160620944018000301000102031000901c2d000c0020140d9030244500c5000d10551041d0b1418000c000b40c1c40e240390307404240d40361401040c64074100c00044600088500a44c42034031154510048510001d140c82030040002d4400c0080c420b001d0086070300201168820190800d400034400400c4070f005000e881c10086803500a000140c0000ea903818040c003800d0207200c100d800c1c440c2d14070006041c0800f110508041882f2041c100800a0034103070fa00b0042c1000002c080c0c5074061107688074007035810a604010510f4040d0000b20310004c0c050020304c900c1d51320004600c0c03100b4525050807010710700704000170b09070750080c1d000040e03003c5010b0240300503046050b803060007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615049307 1250 615048057 615048059
    0x40f050601090603060e060105130f0b04020408010234060b2d0102010c0c050c010302031009060305010f0b1906050306012d030608030703050904020702040f1404020109080c01020a080c070f 83
    0x2d22004041d24401030301c456140c00a00c84207440d0100b100b50407110000e00102c2d101e400f110f040c20080005114400344941e480a00d840c0e01e03215030000c0d10080181c04001600c86c0030f084886600e15140280510465907040c100007141201d039900c011600e904000c00140c0c0714103100202c0c0f200910040410030b294440c1640502100401c0c0c03480c0e8188400703900900004e0004282514800303c004401045900640c0b95100554829400b450b40400810f160340003003990780d40c1c07100880d0b038a6002900d003a511100c9150341d095147c026070108100c1661000a0051100c1a2880c106d495000da18100701e000004282a81e200340d807500c1110040b400c2c12141d03031890944040c96141001e0245021070304210300004c50341004011390345242d4060321842d02e40044d40041000031340c40032104030b074002d95401810080b45802d1052203028501700c40701210f1803c0500014002c50a80d6010605c5a032100c0444d003280d90340407a4810000c4c0d440700b07040da103404491501500f0542d080e0400c0402d8011a20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615050557 1250 615049307 615049319
    0x50c1504240314090f2416030207080f030105150315090a0b0301020a03150f0803120901090606081e1b0904060b15030a0c050405010905010c0c030503040b090f180f040f050601 77
    0x85c40e04d681c1d62810115144c456864403241054000c84a10b28a541074010020702c140d644050385003003890561400500d017416607a54004682c01618050100c2c400110051116091440c0f240c00b420361083c0c0035a0840c509104101010340400300d03c58042c150480100301250401d8000c5121218020025501e509c075802d0010010919507200c03004010400ca0002200c0052034802d130140c4500402661908000c40303414500310b20060424481c41d945c40d0168400f0070034070b200c5c24015080f070304040d000802400701c40c115a407040d0002401c80b030f00f00c0c2d03500ca6554030001d8a00700032000107540d00107050b540d40c1440401004151440b035004003c00c400f8500d07100100b4001c612581b00c010040203044840101111240141e0141030b001c202d03410b000380950360089174010700b16442034038429145612130340c4007829600554230501102c4008500301b42545099000340ca04050199004880c90074000034280300780c1d40103003a50100c501e4100114083c004d510300503210443c1c203c0101c88842d41d48007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615051807 1250 615050557 615050563
    0xc06040b09010e09040c03230313050906010e03190201050f0f033405030a02190203040801182a1d06090f0603120d02090904050c150424031409 63
    0x140300c40d800500c1c51030300f0034140d1400c0340e2001e00454000c50004a07003803c0d03039070f003601c018894241e9001800b14103132000301500c2c00300000c11001c0450030030078a9443c5028148014a0030140400341804101c0040420301d840004403044500110000605035005600040c2c40074402d0544c040000d8200027404124100c0c1c8500850241e001c900106054a81c1c0b505400b003000301c0900741680025590058600f00391090380a1500440003440c0140781c50064000d541024481c0f0030920003580010604006001d401e205d581d0304a00c1100c900150406140d50341d00c4004404004100c0030303058000c1803481a000c40038031001514a2010390040214002c0760314070100c00031035190b0b100b0f1420b14009142081340b1588680110b07805002419441c0410800080c29044100b04a5255909200c05107860390f8058103540214040c401170300c2c00010000c140704c1000b4101c40c1701c41c821141004100040810540341206800c000710501c003d451103000d089021f0910800d40280c100a90018450404008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615053057 1250 615051807 615051817
    0x22a06070b0603070b0f03151201020c01060f1e0504110405061303061802010e09090c1c0606080105010e0703090507030c0303030b0f0406050d0305090f0d0c06030605010201020310090b030c06040b 86
    0x21811114015555001006140b04d175445600c0401e40500201c8c0045c144103020402901d402415440340c02200d04c1803908a801c0f0640c1c01000703a442d0442080915a480d0a04010b0110f040003242c2c42440303542e503800c03004518494280140d5598640300085241c4005690103410010131441c0d848080d8802d13583d2800c1c0c81d0005503038440c0f07000441070005000800d040c0d05554107855a080303208001c0c0c100658482c5c01008000c0900410604a03429621614480d8044405256596000b400341c1040000c0b103400c0c7e00040f0b1960701d000300500018070540f26103580040700b8500031801c5c036030382d00d0894141180c1d40c0c002451410f03129404820160075801a6024034016100c01c00034410031410041580c0300c5201d042c2e08040d0908990000c24411801041d16502c00b03405881c4401d0303810046110324078a040150f40300c0c000101d040c0500d41c1d040c0100002004244020742c05e41c03c041907502c0181100b80704070f0860613610440300e5a10b48041c090321011070302c0202f00c3e80e00c07296038040800040d446 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615054307 1250 615053057 615053059
    0x405120304080d031b03151701090b150108040206030c07061a180402061c020903070621090209060d05010e0109081308120f13090504030e041b022a06070b06 69
    0x900300034520501e1185c441c1c0038000c01c0c0d00034007850800b010ba4064000b000d5600c601c40c03104031a0040030503003800015424052806d88030001070078500d5420079500301c000c0601300d4000807080c1d05051007c1d030392050031940c0154040303400b15900c0d21014107103886d1317104503400280001c0c00c10988804840b1403905100111f070003500d00c1000e222060101340e20620080300c00a5201500b40162000c03d00701d621140c9800003900c81c014600400da0001038500002607000d6400034a0900402042850880c40c5070601121004240108442a4001000110000c021134000d031090a40c1e041070045c250000b01e1140c1ea03080c02001070050031304020519070303c0003441241c0068007207000107156000007858800ca24122400c41d00b031110000300c50006a04c092000d0b1450640038034089080c0c5030a1003568007407032081d214446c4200180081c00306542c1030190702d2610b145c0c018090700b840c0340c004c20011500c0c0f0b1441c0d00304844005003824a00340f11071314104c598203e08007140c95010008261945401040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615055557 1250 615054307 615054313
    0x6090105060f0402070b160302040306060f090b0d03020c131d0d2604020607020612180114040f02040b0a080a0c1a03010617040221030316020607020a1403040512030408 74
    0x350b150203002c180c0c0f04500c0018900c680003400140d40b0300c400000c001e10850b00346030252078140d03030b5207440058902542016400e01002030302001101418483d5003180f8005031101c01c0b000ca40740d180030703407111001390a49005015005005622840d85d03401441c4441d03006100d6051901e001804956410700e04081c00c0100d00c4108800701c43c00d2103241041000c000e41d81c2e0400aa80c0d40c0d502307210303d6401248041340c000c0f209000c41d100720f0207a20901440f408208521050400a0003001801e545510000d00c11040b501010310010803802e00b40680c03a0340e01583c010a80e19a84000b0a043c84000e0b0300076180d81c040c2080080801c0300030482001102e00d560780c1c000042a40a00300b144505c402e1056030b01066000240301602c4041207110782c2e025000074079580d0405442424140c500d1740021202241d604000b08003d09003260b60310710007804416200408003494503520196a681a21001601502d950704212400310403c0041b2000b811014013040040b042e402c40b0b160340c1381c0090041401e140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615056807 1250 615055557 615055579
    0xf0c04030c03060c110c0a0501110f06281b0806130f0b120705010c2009010603020c060714030a0905100905010b010f0e100f03090210090603061d0a18050609010506 72
    0x342000a1b82001e061004122185c0c003440c01c1d0040d94950710710341205050740900b680001d50b2040901806114445044070080c00301d240b1201e40c500d00f40b004650002030b0746408101484100415414150261142003030b034450b407147c1c00007170700b08103141d03080c6c24005041003c072204102d545e0700a6900c113002940e8400c0750040c0d56155030b031919803034080c00c5e0000701c101c116030020a43c0c0441c0d20041556616074108200f900a01003001c0d01c4090700080701280e0001504030110904008059000c019032a040042d041c40400001113440007520f150301310b580b50201d65061050038090079011003080d48040060118a180ca907000c0e007011803503035010680c40c01200200c03d000f00303441c60150000421000c50500365003c00c1d1040c81603211140105641c0743d0a010050310b448550756030318005a100c09040510309400102a14026000045880da8001500d8603c0d021007107000e40004190501050303282095000920404603080050f11620443c41440941d14065002900402d4280d078582819 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615058057 1250 615056807 615056837
    0x301090302250e0a1509050f01030b150306010302130e1e06073b31090503070f0203150109062102010c141204180608010b0303030f0c04030c03060c 65
    0x1d20341c1032003060f901045082c005000903400340d10400030500c0e0034084c003e0320380d283c0c003100d421103400700c4162030036660b5900144240000200700f01e074401d0b022050030280d01c83e000c0120703441d580c0620000340595100700d244010945150003008401c5010380498828007940d41c80041c81e41010711202c1410b0094801080d176552040100e08108200004003035030407528040950300080d2446075580c1c244220301c592048070b645286648801d8402130740d40550070240e2181e81180d04040b0450b94001500d0304841c0400108003005403034219400400d1001464218000f090410702c007200f111401179000800410021100e5001c0400e460b0354442c90800100842001c1d1800740c640d140290206400011100020300b0800c1e286030540d4100064941c51312800c600d502894210340c0000081c80900d03000d49821140314400c140003030401c10000d100c50b50729038021903220320000d0b09040b803103a01c0e0b80c001002502250111401154460014051503959007040f200404000c014040041c0403002d942c03041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615059307 1250 615058057 615058123
    0x5040e01050c0307050f070818090a0c020c1210090c031202060106050f0309010b030102210f01030c0e070c020a030803040b0f040c05010e01020a120915031116020f0301090302 77
    0xc21841c1076002031554954013001e07a0349402074007000030080303003c204641c0000c15242c00b601600d0700b140744192040c00340c00308000f00d1860041c2030303950080c40c1044100c0e600f0ba0000312440200c00698410a00c0c0c6900d544190400b865003a050b102641050005010082d6148400b422030b801150b4a19680000003c1261198001e01c030b81c80000e03006000020507400044000e5411070014000052403496840c080782c2642c000343e100c120b081d428005064240b003028504c041c0c2c00001c1d10103041094ac110b03a1421040012030050b040d04c07407501c0001a00890088405d01c0e04a0340080c4258901d55032486d241e039055200325070482d580101c14010402008003110701a01595022041e920103a09180c011035060418908c03290441c03244110340d50100d40102172010309410b184c3c1c0c3d040282420806890071190500382450201450a44010040c409010a480e0307500b609416652440d4068000140840c113031140c00395142d40b074800e0f0b540401d6000111540b00d00784484010b0705001c4a20740c02c1117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615060557 1250 615059307 615059311
    0x3210309101509020a0507120305061e151b03070b01030c050102031905160609050d080711061314032703070605030a0504061d01021e0427060b1305040e0105 69
    0x11101071405014041c00d43d4940142c6000510b91909a083c0811070719244070242d043c2c40c030070b00400e40e60707414400c0d107040074204502018800c0c1c54204c450564900880c114044c042c00c030405546010030050f400701d4800c02c41c914802d81c808101c90300c1c0da0060800201c0c010081c4000c0380e000b420030b4400111540084265464200d000e42c540c98989401c000540c2c00da0b001501c1c452816443c1d400d0327440082c5061060f010320900400c0100180c92200802906050020f0921814022280102010604006905540400034003000c004140440c542000724480c004043c00c40c0d400086075260140f03405184008500c400c0340e51980442805500303160b25014039000e5040014000c10026012045c1a002a50010300c100d10000b0031f01c450041d42000d51501100c0c21207aa500060015544030100c1c0410f4039030410682d41c07920b42890b1110018000260150703040007a101410284200171142d03002d05c00905a4100c05a61a400c01810382d16001803405a24810352802651401c04101485000c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615061807 1250 615060557 615060581
    0xa0512100c0203041806080c0303070b1321050c01150518060d06091202070e160c11030105010602010b150a0f051803031c23010b07020321030910 64
    0xc8030511040c10300c050509441080d05500c402c0000013100c1c05020711440c60460f804000090417414200c10a040068542c0050310941c0140a040c003c1848040e50700e42241081c005440254818a84000d1151041e403036956018a411041da002e41d801800406600101000800035840401d51041a14007503016030b40c4c000d00c011550201c2001c00800080d04401e0062800d4140100795469000341c0703c03042021603040c4241d050700b41c0002c1d010098800036007640c16a00c032607850700303000c02c801c2202e80b003e55004200180c007906c01071140b04082500342d9030010b80240400d6841c0c3c80064080e200c054101c0340035861000080001d550040d003a40c840d5541aa1001c81114000ba400c0f00c0c560042200c4101700320300c2d1140920140d0303041000306200300c803000f0f0440790fa0720a6403004c4100c0c3c402c0a404420303001148079000181d10309400003419030751103400243c0c0302d081324004249414140d200400500091030200807286030071202545c072902c1c404d000c82d90b6144c036101d0305c3d500752039410102c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615063057 1250 615061807 615061813
    0x30f140402090f0925081e0f0705030a120e0a03120f020102032505040b1201090608030a0e10090b030405100e0708071203120f060812090f06070c08030a0206060a0512 73
    0x1410000007011070b285c000c071614a401145152581070309800e0a840c640c11101100e044880140782020620030302a8086890001e4100d1924140200340c5a83c1048401895006e42d0252144400e01456208000380c0e405001000c1d000e03160700e4200401e070845000721001c5020b03652a2a045481402140d1052402c4140103001e11803603c80b44100c6241d0a940a05011003400003090201c1003901900704948400141c8026516105200080f035103d500440f075207400c20003032070f1201074028082e0404a18166000c0c449078100744400c4a8030030094210f01c4000f03100000340010300c00006004016106010000c1180300008144190f1300c4a01d48100007040d08414020048100d903c400340c0c40a0380a401c10760b0030042c0c0300c5040801c42e00d045d0714040c138403603482d64240101c2408128004903842e008090b103141130420b000080e04a11007904940c0301d0900094104100604154018020202c501c11207440c0c1d91000406034580302c0403103e00740a00e821400000b030b00e151109190b000c0f8640c1c0000307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615064307 1250 615063057 615063073
    0x4050115090908120a0605031207030801060504030201052b09051f0510120609060603030c120503070e0909010204030b04050a0b2206020904060503060915090106061e030f140402090f09 81
    0x500b13031010704014140c81e1450b03070725040086d403501d062004044150545040c1941c03060985006081910103030401030070080d0070b00c408d00060341c100c001c813081c04d841c0c41041c0d404070466006030348800e194030290b003001c641080181c40c1002800900030b0310110300c842420150303076042c0100904482c01103034440c0315448000d1040003a00807003440d80b1031050003001c010401544c140c40d09015104598011000100100c5a0307105000c040341c9440382c581d02a00e421840e50800d004010076410513022190b1042020304003241e190007003581114000e581c0100c040e40d5516290910580710400c24605440b0500990b00181c0d2a00207980b42c410664018081c80203003201c1511414000d411254425420580d2100045041e680420000c0d202e400c804000303080004606000134051030001d071039424541c0c1800428014590420b004000c407450001d400d080d0401148021000782050b14484003003c0e00d0b082080100d861946d5103240f01d64000da4016242d030319000703640c1d00e01d041d088440f40c2d1107410103a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615065557 1250 615064307 615064327
    0x90d02060706180b01060f020624060d05010e07120605061e0d090803151206060906150406050720181302120105060901060f0f031104080604050115090908 68
    0x140c4192406010001541c1e0f1007051a501868500361040d1034141d03800004026a039405156490820500e1025105604016154218900032854000b19040e50354540f121039459030001e851441494007418080c0356074460803800c3e5842c080e00d409001074a180981031003060a4010036040764005045a0300d000034016801c51610f010b01c142e500589801c010280c2c0c0074005014061a040c00341e0307801c0d80c0d00c1c10010f21041c00d01c548a03420902425010305170540c0d00501282c00790381b19005643d02c00003981d480d00061016003030f030100c5288c00707280441c0100c0ca203a4090701500c40148034481c0003c91074905181030303440f81c40011441d83c1c8048401580150766000025071604401c810365480c0806803607034009480307004440d1030398000307a55800c00c01049150981082d40100402e09102c0004004610001d08580900303202800741916140203020407417904084400800444090300c086007000e00d80349000e0702c00003050f0014080a524003159100c114441c1d0074115910098062500340c01d66 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615066807 1250 615065557 615065569
    0x10b10020a0303110f0a09140409080f03250207082e0903021f0504020f060306010507030c020d02330c0706210606090305071202090c071103031b0c0402090d02 70
    0x70704d5980d0704410038000c25801c0458540038002c1611a40c81d5070620a0420340400c0e5900c640080c0b6a01c59410306070301c40081a140f0044815003003c0740a5641e913956484040c130583c070340ca0350900d42640c19000d4030030545980454084181d851501c1034404044000800c581c03206245024050341144030300e5003121242103a03100120561083c015915850501d040c26854000ca80c1000e80e4000d444030104030862420b00211409540111081401d500303009000030014000c9403070003801c0c414608100c1d0255501d0024000c5410b900400340c00c030302264000340791a49000300740995400c468084078020800c5110f800d031100b0143c0440100303042890040d04032004c84100c00041e019032910609440140f4090068402030409506e4180d0154558a4000e240c00426440208491460400d110069541f000e0140d0014601107107a41c039038203941071010020100350030321941440001480703625900440150070886100d0300c2559122002e020030b000503072084c907614547c8a01004580d00052410b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615068057 1250 615066807 615066821
    0x180509060f0303030c0901020f0d0206070c0f05060403050d0507020105220606150203031006031a01050d020c1c0f0309050a14150a14070219080f0903120c010b10020a0303 75
    0x1445001c0c801c0900002c01d095500513110344003160070000d2501802e50b01000703020310002d0807000901804060a0000b5154a0060000400c12a6200303200303040c40500b00600e03018540100594210b81041e2030007a10551040510301262428080020f080381c1c0103100c0c0c0c511584d8804204900c072101020032006209203100700326440c0f0b84d81d0320041040100c03e103005110914a4004540d6030811080c214200180d60740144101801e20401071900178544030704414181c030a00b40b907602c81c8124070860000c0e00641c021144984100407480c2a230134809103811450307030950b0f00c80301c0d003083c1d240038210f00b660100c92001d002c5030310035030200002800c000000040e018005096540c640390048280c03240e401c042c1c8003805c1840d100c080104410364900400f03030304800140000c1404132040e041c06079410108003000342c8007202c007140d184030107403c10b011282c0e01c68008044e1111210380d9610088250400350340074810358600b00220130b450070302e01040003a51250340c0084c200300400307075800c5003e4104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615069307 1250 615068057 615068059
    0x6150429070f111815031504080a0309030509060c161d042d0b0103170414120111070b16050405180703180305030403080609060a050103020904150803031618050906 72
    0x810444c2e00b0b00c2d400a0900c075008100501010075904481010145800401f00717100250340004024800041c81583c01c0b9504107a55040200315440c150500307071220300030f40c02030795000000040d00700e00480c00810910141c01241c1d0080e4002906c2d02d20a081c2e00081c00c020b600040181004034021030070b41c0101d101c029202110a10780d000505040408031540c800c411940c6d005502c00520030001040200140450f0111043d401c3c64a0042245240072404043c1030040040a40e05010000c003074000742c144000c1c0403e41a07403041c452400750560082101d0b032948120307440554030b4607244198102c4007101d80c01004681c2d46013039072800c072500c0c500c058048400e050b500c1c0e03101203003940c20741c07000c4550310f020b900c030b5940368502410050060080102014071400e030755010081c1550b900403480040e101d00b0710780107884502040105001300303c50f80c0396030b400a660003400038882d000080218414a090742442c42c1d0300c00416400d440c80c0d403824140d20170650070960144164104903c0007540540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615070557 1250 615069307 615069319
    0x602030703140403021f0305090a0f11030a170c0c0315011e08010c032a05030a0905161217030f0105040905010b10080a14130b06150429070f11 63
    0x50b90768006030244643e140b039120245034200d06d440c251505032080561140080b0040c001c4482e9642e50f002021042800040c14140b20140d101e846840802c0000b40c020360018a5541d030100e00e22a680c070540003c560042c092250815604013818003003203c2c2c138480e0080c00c112403103908285e520254441c0400b000b00c091811b001c00001c1400c024000c45455003520340b4001451004180c01d140500348003a10300c02d110705003481c4695080d50120403240d002e003106a00042d0b69600e454400c0c108411084403903641507812101040c0300703101420700c1c00b003c1d105040035100d0694004a501039400201e401140c9250a0001044542440c0d0091a000d9200364000581c4820600c00200013000440402c00054410020401500010700c82c84d008ac1029140700100b51500c0740c040b80d441502804024403072200365020500e66140c81035103003607240302406503540b141d4454400702d0b17030318a2400341d00c40340901c6c9018100400c0e8402c2c04451505030004020748400c8025200c3c41d600040681312a90091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615071807 1250 615070557 615070559
    0x216050f03030f070602130909020a05090a0212010b0306030f07080307030c020a0305031615182d0302030307090e16111612050607020606030a030e0a030b010323010606020307031404 80
    0x155a540044c48054816000180c480994000c54050000c540d0050031000b03103411010400743c1c1d6180c6040080b5401183c410066640710360500021b170007855140650844603200203d508841480594401c101c240c044810f006103180e800e541e00c12030f0303118800c2550410000407010a11071105c0b04a420b002030300c0120703c07030b0f030780d5031080d255038807044c8150074050081540b0420441008401800013449290912904072040006803c1869000c00100b04100141d1042ca070024400002e8001e544508004010f07014a401e01944a5200710b03003501c00581e03000c00c01704000f40001010341c0102c6818107555010303400944259a100304880d411107561280244185c0c017080d542d02c5a80c094461818405030391003252070103d144c144003038030b40ca081d900290700300240ca440000301510115050f01d85090700c0010440801c0c0d50b01120f42001c2d00031032000e00040140500038202c0742201c0d03201c009002000c403007009002e08940844c01010010b8104012503404207104201d0021400d020068042c80c01e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615073057 1250 615071807 615071827
    0x11b0e0a0b0c010902010e100f081b0304030215130807080a0905120d090b070b160c1505091501060906050904111204030f0c0b0a051801050702010e0d0216050f0303 72
    0x10b9045044094a141c3d1140402411540e02040c07038190000c0036070b510344880b03289000245c580c41e80c044583c8104030051001807803a04060b04007aa4110b4010081c642d60b05003800d00940780c04401a052602008031004244410300700d12103110542e8000300320508040c055030361007400e0341c4400c002c582044008a004200f40d40d0b02c8410000f01d85084004003103800d0307482405003c80d01c40da8000c0303605040600442011848040c5003c0d4041c11194104507c811001020303180d0400400015001000e40d042411a14043e548424094807040342250001e60040c844020220300074015034002500b1508104030450054001c0d1015640c014000706d0702c00d07200c10210101b46c0010f0046451000041c043c80181500800d02c0314002c07403203103400700d1481401d450b080d81c0d010700a0b00c0c851106550390002005600c12070790162145030380300d00901007070409010080c040e0070000940b0400d80035402c9a40c0303e03079000051102c40d040304072002c0025945014108155040382d1640160180810450480c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615074307 1250 615073057 615073079
    0xb07110f0303100603051308070311011433040b2b0b090f19060204030206272205061c0309090f0c02100c0e0a0e060f03011b0e0a 57
    0x400400c4000658880c0741800303400e40d890065502c1202894508001e00000c980c2d610480e0501720741100c4035a503180c1d03891078222144000c015065010b94a0b10103070b001d80c0c1c40c0500015004241e805c04540184122070310340081f000080844c10580f201100c01403c060801d078216900d0200028490b4039a0045c28508010203501e41d04803554180446220208001c4044800f070340102a0400510030214811655556100c1d0070582052038407187d01050708001058049078042d40e8040c107040e03190040d054032044c0c80ea4100420400303162a81c450000d9509001542240c1445c00c04561002d44607440c81500042401910301a08207400d0007003080c6100d449880c40c5a4680b080d5500a5002d140c2580c1c08211542700d09910308449c286a0b00340601c5da4006404e607180c04c200100084d85c40d070141c0301a940141d0034440c054002c800c000c1e001854403014a8120320a040996002140d4400c2000b003508a65000340d20403100c03028000c000040a00c5032241c401e801c1000350400c143c06441d40c03c1a10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615075557 1250 615074307 615074323
    0x305090f1510090b131505101806030b130905030910050d06060f0504030b07093206030c1e1309051e0c0306040e03040906060c1406040b040b0711 64
    0x6000c050006102403003103182e080a00503c1549000c102244000c8005007480300c103542d8a00c00340d500e8081101d080d2403580c809400422005203640c20049250b00058a41c5030029200411074100c204000f038414000c0c090b52140440c0181043e440175a0318407030030014544002d081d90035103c01c7c41200c60503160b10b0300e002003a004d991242074440c0030100c5a8170a0b51059005802001191600e60306a9904041918103595101261910660301d011040b41c413000c20380d0200c22400d00507030904185441ca41d50030080004a0b03045440182ca0020603c0340a01c01505c054a400c401080340c09401c80410707043c441c0000540010510740810f0341c52801c0c83e5550b5411099030542d50300140034406121b05402c0c19802c1d6810f4078122140b40c09286d00646000040845010310340301c52055006100034401c503005088800d004114541d00ca25004007241c082420442d00c821814980c10807032840010840e100d10703844111002555180e50b100b1000c800007910820910402038044021100b081c4a101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615076807 1250 615075557 615075583
    0xa0b0d180b01082b030e010e1606110c0a0b07051501030501050a180b070807020703050109140c06120112020a0510120b06090a0e090a0c231503070305090f 68
    0xa07065414803819605204140d44030f03008154040d04007085441c8180c12080208180e41030009020501c5840d10340508050184000716000300304203000c0c5400349a520304240e4100d980c9407000001c140007220340e0341d014007130300c19030001c2085000c02041d401c05008251052190003a03401454441c2490640c280007a002100c01da5115400c00a1000c910300c00e10100c0180039030740700e144401030b88512200d010080e0080c0c003040f80b038a0000d15558000c000703040003035601000030800e480003804c015803803520305000500d1070300928120003003174644803003600d606180309855600184d103010070b02d0560015505007260406415000000c10b035403010742c1d00009060700c5e154200b014114580d03c804031480128070030702c42d900c10301c51845c003a143c440c10f0703d0941f8001184041caca511804000361910440c103400a01040d403561002c118000208810751000340da80c0122454410480304010b144006181003545a0301d0901c005000c0610a41182c3d4010040005450704070044a0b4410700b86038060a204c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615078057 1250 615076807 615076823
    0x10e071b140d03020405010e040c0201020c030f090913240b040e010c0e060c0a110d0615030b06010801180938060405061f0e0306100501021b0a0b0d18 66
    0x800700c00c12003800700e4502401c0b10300d01185001c1c14400064407980802280c01d00540d625041418014000d6044502c00c0300e0400403a82c40340e510070f9107107405511450f005806606403c0103c1c603100e035030403441401c80e82c0c404014492440c0c1010350702c10b04039140802150311a15040004900d480710b01c2840c158004000003c1210340f010900501110110b401d0135010300303000c0104000409010607a030080d55400360244043e40c0c10070001441580b44040c020b401c1ca413800203046d0780030038241c1142080300d115140f58025a900c40b0010f5820b02e40034850b5a00002d1160004404042c441d4000e0342c11034461840d000b01e0110540745101c034076503c058503020003424030350300d2990210481041a070101007120184810301d810750100300741603110030f10390b82a40166012800941d00a07414103800d048050100e9101e803415400004044c07100707104460140c0501134151f04885078400400c80f0030103024200d841c402c8d20384104140280d00c201016200d040d42c510020060484240d451001c0d20702640c51 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615079307 1250 615078057 615078083
    0x10902091806090705100f17090601030b0f0c070f03120c02060901110412060c091d0a27080307090801021c1d0c0603040206040e0702010507020c0a0806010e071b 71
    0x200e01d0100060825205130b8030080007004140e43d40d0020069a801625120a03039141b00801038840411005e0304030071400d494820400200000541c942c101c81c011103040030240c40d2a540035000c0e01068030702a5455004100500c0801e20001c1c284400c90701c03034901b10141000c0407a030f07030046840c00c1a1020041e0407103400d000d02d61200340100160051a100504d14051510702d60b01005001c1280092050707031140c0503c030390103001d415044000c1013929080507442c2e190a1480710201c0c41201d642d1219441d102d1070210207900c1e80303503c941c034980c40d0200e2403a581c0b1503201c215141e003009100f0350801c5658280810140c9003130010f009110f11182d4a10341c07810200f900082502c0030451049041d500c01d0641030000c0200140d10103407940151605503894550b4000300d02188619041b00352209681e0b400c2c002d4142e0f055100c2c510401444d4265646d02d0721440c100300001009129004051b070002e4014484c00580c1d0403070581010709070400d1010900a0640e0142c4203241e10f04c19600d1220800c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615080557 1250 615079307 615079351
    0x821040501051006050f1206032109030d03060b1605010b0604141203120109021e0c0a1a070c0b06060706060f030c08030a05190e09150f18040b0901090209 68
    0x143c00018000b103051144c24072160020724025402081c0c07000301802d1000002c100305880900c00c0410041400f400211030101c100d9190005500800c2982d009220303541e426000b2074442d108001c1620f00d0060510710f01f540c40c0b1204400d400c0210302c240c0c0c040d581c4000300c0d0210765840c001170005140500c03100191f0282034007001800740d0050300d001c840d50002c010f0b5424412a46400c0c0303040d070315203200040e2156600c5882c00f00d0400381c0e400320200300a00103449440c0b620001040002a442a040700c520f40743c049408503400321040c0d17004004600324401880000f04004541c030b86c00140505550306101c00c070340707901045d100e80303034446406000000424403d04c030754007056401501081005602e0200285001810b030703c41c44444003007007003506c0c1e00030709800d10848c0d5510f00d0b014020018030741d0b41071400d04858071010251105102e0070705801408550f040841d0641c5020b600b610710408613503295120401c490400038419896035584103100b0300183c0c3c405c0d101d9801180c9003108814031050240f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615081807 1250 615080557 615080581
    0x12705030c040203040c150e15040801051311060d09170a080c0421080c0d051305030106080a020114191e170604020a09050901090b0907050313082104050105 69
    0x1441c040d0103980100308200106100d0702c82c15046501101d80780840c104003500480b4103850f801241507024004124031110041848040c00a941a9000810540d00c0707074400c401100703c8079080100390400c2003031005030702d25101000d09a955040e5201203514481c80e52808402e195005000f103400c0c0c1e01040810769140c1c07003617015074000745070b4200c1407030030f0700700009510000300d0305168070700313010100400004011402e0705489447c9081421241c4007698510081d241d0b801900100716108140b003c00240f07450140180b004840d21840901000151500115100804800c0537030203503004100c8420010440208048490360f41c0d03440701c01c160440c40d851500c055130300e00100c0401c02c0b040001a001d500b01ca00440d04580212001640c840c00c1c11400c3d04c0c2c2002a5000700d5100002034000614190710750400096004100c4840d000750b42c5256064401d804243c0da4101181b52000e8244000381d10131009008140301000c11008440d00e41000b84400070045a0895a2380d45980071700400782001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615083057 1250 615081807 615081823
    0xd0c091107201503090109110d0305041802040e0f0103020f040b1c02040b0a0803120c03010602120c210c0f0f0a0312060302150a020d030b010e09040201270503 70
    0x1114a5900d801c125031220591441501c2807840c1d00e442225904209664500c0c164480010301000e184c1c807481c051640d41d0080032107110580d2490361113240c03c003c0d8500603980b1a04168103856244c14a401c040c11040c961482a165000d0680c1c20000458442021168144195000000d1522031340c118418080c290b00e0151542c2d000b070b41001d50b40c1341d0b9a915109000d0450900d0000700c0041d400358000540901061941140c122083d568081041c0f58080001e00305140b402c518281d807522040384901051000744155070050300202320030b180c0104404001c0c140c1404103c1102c408035120703114901a205244036407080d00d00000388440d0a03203024859282030103864400380446500d410300342501c03580108001010070981300c000c2c85128009038044406940c001e400360f000b0315102c60043c685035006564540140c810443e40c82c4800b807281c010300012030390680d50701484070a92806e10181d403201030f10490510030400c8159681e0301890318407105110b10201464800c070700d0b210a041c2800c40c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615084307 1250 615083057 615083081
    0x6050106031104060c1b170705041103010b0a2001140606120606031807060c1101031b14130b07020a0f060e120c030a030f12020301120f0f150507111917090d0c09 71
    0x411540001c0440d502f03065034110703004450503e0780c139241e007401103810310030700b181c620b6003103018680843c0c45860541c8001c0b600200810464095143c0604004050040c140314440c2d2506042c00039440741481406560091030740c0ca42100034159810b005400d0040c1d6410441c006400001c0200a100c407803011942c07680000e0070100401401c49020748050380c003400180b014840f9950202d1400e520724800c0f240c010058039600121540c544144041581c80300905a00c00d4522080200782c0340b0b040042101150b8154442c050003032101014015010519600324085014010300c12006032000d00c140c00003d8803031f640e2600b10704030f0b2240152442228105900c8418814001030141480b800c8900010640009400d0343c2901c042c0b50100341d42ca02c0401c014a0300c02510810032441d94150030050160b5250384940d42c1e004000f51031956511104414168000d40345060071000c1485e104200c01e159460351996440c029001000c20300c15002084203c811400c0780004004a512503c0740d1610311b11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615085557 1250 615084307 615084311
    0xc0f1b061d0f010903050109110a0b0316031109030f10150503030d0e030c07090605130504030509010e0a150c05190c030b0c09090406050406050106031104060c1b17070504 75
    0x4000a034410704100c0d1141c03003070094040d442141d050742c0c05211948025580034000340804001840c2c42d845d40c090040e442030044a0507180423622142d00810740340b10b0100d543c0b860008400140c802c0300640304008056011100410808001c2d440c144a8150542c00020003002c0c0d41d850002c03214201c54401884031802e0284200a014556008c4212680304100310404249042c3d22200e081c114460581a00c02030303c40d032800000d2030281d942080341114011509500b00008403041c0ea825a60210780c01400114200442c000540c01030341100349605000e048101119268030b41c80c00010b115a107034001203007210210004003c0304012580c1041c024110900380c44146a581d441d000d05940070045c406418a000641d04801c1d8505981002c50000e00d41f05041c10070b070030001c008140a480070750710b0504180c004a030f030074020700034800e450941c44141440c207807801e1803c0302c0e814179000040380c00080303d107812800c00400f2a0160b01902c26000030055555107207180524020890340010302480c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615086807 1250 615085557 615085577
    0x1b0606050a260616080c0c01050106090911040b04030318090204061206080c0306010e091c0903140d1407030e0301020307020102092e03020307030e011125020f0f010c0f1b06 76
    0x11040401102e1440c1c513604240401d504e88a40702180c43c0610442d608403580f0302000000d0241e8031009120450710315080800480107864121a00e0340300c1d0740a41e06142c0401c21040000a110300c04131400401c003c4180c12182d5240c120040507603110307600103800901c510100c12601c004034419007004140b039034010301c602104540842d45030720b414419580700d281240d0000c0c00005042c0b240140c83e5500d642d00140300e041c8000c020741409054003007582c0700c0c0d030020f54514405c5000a04d0790000700103902e030710005130010500f90300a0fa01155046003008084641c1c5001c50300e09001070760186c0070360340003d40c58035450000d008040c8080010f950151403548105030302c0c1300440384144c0e0084c80c540ba001d60391350744000c019000b03041518035903484d0358a000c00040c4143c0060000e00050115599440003411020542d04004007201c44060341c001d541441c1d0311007030716080780091001c07103041c100744040c0d141d580c8458100c00c03050744054400301500240f424640100d180400d02400300350800076049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615088057 1250 615086807 615086821
    0x27010e07090518010c05070b0f0f0a0e0102070c120b0609040f1b050d0303050405011d122b060602010c0c030c030c0203030d09030522061b0606050a2606 67
    0x303480e4a206a00ca07072540e800224203c9000012558051078491000f401031010038400102103511804040e21110b400e0710209403208411403816004060650316001c9a031201009600284032048003529135650070880280018480c04240c1c0c01083c1c244000f425001160500a290080c000c0000d44118200c508010004c0d10548034404610742109903050083e043e2401d4400d425129080a0340c0003401c0b00c400820140e254104902c82c5101c0c0d030003440707142210b15120600c0f486140b0500400d40060303000d0700ca2801c008010b808000b00309401e848140c0e4012003202c040280e05007810074040d85420f8184002c0c1d8090190103808200c1b440c081c1902c1c07400da1002401078008031402810003114103402d2080d55010000e0ba00e01c0c030340700c0c101042203640c986000340541c0d201241c2d18801140c0c52485030070041100c128201155040d480ea0303203400e104262150721500341000201c4100380c1d030b4070001c07403240c890752038050103801c0103082a00130030141070030f109140c0c000c0c4100c110340780d1050003040b40b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615089307 1250 615088057 615088063
    0x1509020405040e01021908040c05120d020c03060603030412062a0e180c0d06050909070e01080303011226040b070b24060703260412020d08070e011727010e 68
    0x4607580c40d07d0302a0307254489103400d101c2040143d12490b488044182a07142246000c40d140082904176000c071880070040206041d01c0ea142160340c0ca03815042404208504000c84800b440168418200040c180503288002c014a0707944a010381c8610104044a01c17100350000720402d9020004c4682c0e00100040e900c0d81446104020003a20440d4400b03e071084c2008200e0300400083d0000402101c120f107080b02919946034151311501d00e1000800f000040c4071400401220305a8903091a0008004215181ea0840380d011160301e011084003041c40215405a0b04003400140915580d2595645039504210f02e80c000f0113805010300000582c400010760043d01c0200441c900141c0b002c94076002d49041c01c0c0d884041d2000320302004401c5807158038402c940121901e102e180f003070450010500b04200202d94440d003048003400465505004a005c0d1130040c048000d8560341450b2412a4096185600a440400340c8840c41480551500d0f2030650714214928844001a18002c000101003000c0e02c0d55 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615090557 1250 615089307 615089347
    0x1120311011b05091c14120304050319110a0c03060b03030307090e1506030c090405180c041d0d020f0f0a03050909060a03020607030908100501080c0f03011509020405040e0102 77
    0x103000f4000344102c050f444141d10521041d522042d910038800c4103051800c0601105003610181e030150402584c040b100803c1500d0103260404000c43c100843c4448180c0a448141001c1040c40000d48040d07800d540100311034140903100f2240c0803540c2e8030394a08402925102d510151203030304240200700a84c0c5e0b005c2c1041080750301301092030b54540c40c1e010032900e03c008100c80c038907000440042005000f044403001480d040500317403010046903075509040e5986003c00e008070070064202c01d080341c1a62030a0341010104010320245400700c154041059440c101c9101864000340e00041c01d51954004240100e9a10054060240010301690359004005104007107605200d0401100850215150a1664005140d0160145588030818200542806030300d200c1c005080c81800c4070310107400030b640a00b074100d45800c80103000010200082001a51480503603580543d42c416a50b0442c00818220070010300101c0d2005981d242400b00303002c151411840e43c0101da038010000440f1080542607100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615091807 1250 615090557 615090611
    0x17070e010816030e0a050a0213110d090c180e0c0a0b0f0d0b210c0d1e0303151403100204080d050318010510050f0d0302330112031101 59
    0xa071440120b9074180c00809800b000041148100f0251404000000a102d0002402261807101103054500020700f6a4135040650042103818065401c1e40346454020700100c62103031420703074030140c0c072800c074104480d03210b5a0150a290b201d0401354240070041c0500d0041000903141c1c0000b1904000107808640b04012000c50306d000300240224031484154130642000c44020660700d80c03003070010819100701400001e401d00500030400c00341c52a28221003541081580714003103204c3e14941e40c4040d40405103001083d424540c0300c0010758508078411000d50094105e404100715192150028145440c0740384100102d6184100014001140e0006806c1a280c42a01e810740e0741c1c0c0d5848078604000600c410031b1096540c00c2105110a031020110581c003545c0060b14040c42c5207240d0008c01030f080b03405c40c1014002da009002628070700038042c60308a402d800c40c03540c0000d6104050381061052102603024040d50f880c20321102d0109940845012000c03081c0d4002070144054800002c40c40c07030580d1740c9035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615093057 1250 615091807 615091831
    0x150f07020f060409020c070e100506090112060b0307030612110d1b0f090f0b0a05060a03090b04050d03050618060d2301050114061e07050a021017070e0108 68
    0x105046503200c0c55800d607098805400507448541e00c0c59620065000084012003d0060120206226180d601701c1882401c0d2042250750740d0b80743c0414813255500a00100d81000f1001c802c0781c11110390b500035403005051801c1025035030f250036400202203605907040341c040010441e95200100301d0903d090003d620007110f0310580d00c00035181c01c0042d211950380030314000c80d4000000481403400a1004211a0a610144141da41503440c810443d140c2c040440c0d84804000410301040c100b81001c1c110703403c0c00e802c0000c2e00c000c0d03544030040340c3c1c0000c1703400302c0f195032144141d010400d62600a5076085182a545540041d106054451400304010300d0f0038026117a04040a0510910000e0494080b801c01140c20b5480f00c0c041490740a482e09004003d400600200a843c590510204503141100d88003800541d000c4092112400c583c420401500c0f28030944903c040540e030780c8016100840041d8071001d00d80e258588038411a000002c00e002c0c140702800c62000c1050342c100b410300c1c0c1d00070094895 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615094307 1250 615093057 615093067
    0xb01090c05070209071107240e030f1605040605010503091b13090b07020c09010f050f060d020c10050a09030804030e1906050403050601080606210f0109030914150f 72
    0xc00c6505010300c200103503124181c02c0502c2090394002c09440c90706080300054845154071030040380402810105048103418003c0c10b80c004180c49140114400d45008040d181582c00844e649454108039004003450700501c1401041b20745400c3c42044011b00003828403d0952030102e22003a114990b6001201594101c0d4045007144d5540b0740b400384040c41d42e94810030981c003881c01c08491046003102c150016100f429500180c1c1d00c0c0c5984110f04841d103241400c11801d007001c080c0200104c000d4030031904440107010b0b8081d45502ca0025200502c14400204900450f5030340c002c0c19030360301a00c0140c1040c90070b10f0002c0841d074888181540540c00d82041c0c940703220380c1c00c08604140c11180101e00741c03107590fa001207841e903881001082201d005500300c40c081d90321003541e01c0d1205801d903500c5074041940300300c01046548108010055003208425110304030341340040b45080d503100c4001100041c3c48104103002007403145c200b501502200381d44121580300610b035511003074407640c21303c0420030002041d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615095557 1250 615094307 615094331
    0x5071203020106030c0e0f07030e0c01030b21061f0305030702060f16050d0e03061006080c120112060606020102030907030b0a06080a1202010b0d0c0909080c030307020709180b0109 79
    0x5000131644075800500c096074030b07002001d000109132080c800000e900c40100b00024440d014860001800c00c0142191008030300040d0300402d44001700d0750b000008105406240b01c07006481c810912600c04c0a002c4520303120304414034005c00042c040070b40d031f02c0310241132010610010941e02d40550540342d00da83c1c0c9d08111040744260151032035079590415170b0b80e0518104480820400c10104003a00e0f0360f011408001c080644a5104858803601c5440e07107041040220710400459402129912900e442c04695100c091100e1001740c03c440702d407203400a0f18030200b0195200354001000f031031000b1402e6081c4030301510384134a03441c8006020008054041505003455a01040003095402c007203c00c00c100504c1d1000101407102c1d0071101552a1010425607810b11003240404a40e11500f2a04018105203100300144621070007034541c440b017800b050507010700410081d4000c2032560000d055980ca0440303400b00f82c500c1c0000c20000715000108400000d002086004d0640d10780c00c41c00300e02100c0780380c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615096807 1250 615095557 615095561
    0x5030714071407031707051504020d020a0306050106080a06150f1209050105060f040504023703081b03091302070503120106050d0b01020102030105131a360103050712030201 76
    0x10314050001080036007036008000000a58000302c91044e8051841211034024949013406050310240082c8c10010042212601e112200340c0d0262008202c1d0080c0300070380d000b06600b00c030250411196140e03500c0051110710303000401e455200b50309800a20101f801c3c1030300442c050a200c090314085c0000151300c1400540500d03016140c0403812082006180900c2c10458040c21090b40c140d4020361641003014041d0809004161280d034016010440880505a288007801030f0310013800a940150025040b880c40024180001035004103501c03034441c20750726200400360038860b5450803198420860007100e03440e49140b00b020018110001030701c2c1c00d03a900f0000d007907109035449020101114400450013a4018001d04951015402d041011608150059080b0f11007805031540c00801d200503400c141d00150411100c0500803842c80c1e184040747e5011821200110391803040d40c20040d240b00850800c0000305081002690000340c105d03500d1511441d48406150040c051080d154464400c1411300075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615098057 1250 615096807 615096817
    0x903020f010e01020904051303020727020403290403080c070201020f071e060207030302060c09180a0c020c03060606030c07170309030901110307150b0307081504020a0e0705030714 79
    0x4000344040381104042d0b5000354440f14880c0c0c4a249040c010030300e581254954001203a525800a207180c034201215500450105803420400d2880d000b419402d07580c242c00981300451050451b030181082200c100c55416a4a20455030700385045000c00000c41d9005c0c8072180c0012007807035950395400003800100d0070852007e01c00b1040b44126080000c40d40511002c0080040251002c41c5100307840341c10890b1218102d20000d00180e00540c04960740d80d00c0140104500c001c010131200f800c046042c50032548203012907100c9010740d0748040c1ca20009805002500c2440340480203480c451404000007140c40c04007824030b02030080c0c0407540b130003002803030040c141d1003640d0360220a4880c5481078001c1d40e6580084078885c00211065035502d44014000103403020036a1012404160020011010004189401e801c1d41e0600c034409000596400c18030442d44107404018051481c1d150170300600840012651141189044404c2045a01070b4490b0582e5001000d900e80180d1b09072028440340528011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615099307 1250 615098057 615098083
    0xc0c03030f070e10080601140405040e01090605160c0b0a0b0d0804092a0f0201020906130806070806010507110d020603010e090606061602010c06061d0a0e0d050d090302 74
    0x180400c20412100151154403140e948410907442c0308144113101d00d010703d6110100e0344620124403550700403e05511001040340b0494140341d07903040081e048d101e4815203003034681d540720005414003130980603d03070b40110005008034108200410003003100706480c1014108500040100700c01003d243c028520040740106010341604a600300062107034454822002c04500d007485d0712801140c1d0290140c024004251034201840840c0c000303462240f181050340d021950700f0802100c640c0c1e141c0010308107104107070300c40c2c08071a030030403005070314011015001006101100c402c0096513a0301200702c0c4d048940c40240503540c1103100e40480c991400070f4600a600150100002c50711416880c8d80b82c2c4603082c6032048402c80d4550806210703280c429205502c0070041810781480240d40030701407504c4001c0c481c1d580003032041e81c3c4080039074406086002c552401c041200901c00d5110448c0204000041202c0180440c41a080005491403081440c8000016250500b000a0500074400f9181502d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615100557 1250 615099307 615099313
    0xc0c030409051b0f03010806060118180608010e0c0315011406370f0914011d061b1510210f05010203070908060126032203020f0f0d0204050c0c 63
    0x4d40301d03400380703980e0000d01a486045c072801c00007075610361040e000c0103400c041d908080485182040554221714804401182e81240ca40b200040c41c02c00922400300b03082e961034050071800e0804000c06050040d098442c60340601e00c800180300700200c41d03e2074000000110340560303a818040c8080d151001d0001b000c808102c402d00d40880c2001105c0c00c0700054203509907100d08030411910b40942e0803045500800e001c500c610088186154060b5080c1002940b03110110303215900d443c000078450b6807280c0302413060f0b103240b1004500010000c201c801811809400b140d684c501d89421084030703075031080c4150410030080d103800603402d1480d80400f010084d00038020006211003410b005001c0e41c400e4a00000051104500040d2643d01044070381c1030b58501c0384045d0b0000400c6071461314260520103001001d000c01c20040080c002012100000300c42260034403131520389140100718803a048001c11030b01501c0c0e0307900300606031340d14142114505581101e00141c2d50301e924603415443d000c4c5079030740035080c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 615101807 1250 615100557 615100567
    0xc0603070c17030a060503060709030210122307081b090f060d0504020909010605130207050f0a140717030a030924200901080f15040603080d050c0c030409051b 70
    0x40e07505005610403001c008085c0203042e0784100703140e0348003001c0311070390001096100103000601c0d00940c13210304007416260041660070700308651411140c1c40d1001c40444038455100480820040d10a540c0c00700035401e04012924004400224230442406074088140c030014020216036140ca90304c05440402401041c0c071400b000d4200401020250b405074410310020f800110030788014080c010035204064600b003560200070805030041d41041d10304039242d000d03082c001038070704108100100c08107000b42c00c00c504a540a020740ca0424440d0341200c0f8000324009096803440c040001143c0350300700c0600d0700251440389410694054030b03100d200c803034400b0f401c0002440301c003d040d0032060600c00e504c1900103850b1072400c920035051107100205400302e00110006210347c4010b5202c1d581c4010a044086148110900014111001d541080382c0b84135003c80d013185542154440c050380200389a1902e458990a41482075072806203205548403e5103500014406507015428044503002a280146e121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 615103057 1250 615101807 615101843
    0x204030816060b150f070f05011e060608011202060a0311130e102103020106050d06060e0f10090f060906120302240f0601020f0f0706020c01030e0c0603070c 69
    0x10a01210041d03544500f0f002c030348000c40c07502003021801100c44180c51031a150001c8000300160300701160940d0680301c8020b00d400455000e0080c40541d100d150000031041400c08034800484000d9000f9008004048005120400320351082040054049030400e4642c0490030f0101d0107045818180d0000c1c030804a000c1002503901442c14040c0c44501c80301401d42d40e203654815034403c489100d071400241d0303560003000c1c4040341040750400d070b0b60191001046950315080813422010668038201d445c036580d4042084000c0c50042d07003d4001039042031300c035228203192500b140303c2c203040d000b003e907140c2c0d40d14400d0304600e000d80d01030002011001d20034001d01d5a5009090394650b4401000d401502982240f290000703184812002103812040e0052900c1e201c04142d49405400140b103103055100c0c189881001b00010001e010750451074030001c03d051400c200740203040001c10084a810305061404100588102080502c5802c509940c0e15481e507030741003012682d0110590380500a400c24880c10401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 615104307 1250 615103057 615103087
    0x4050319120c14030103021210050f04021806090406021813091e031d060d1517010b0306040b1e07110111090303031b091005041809022202040308 64
    0x950085081c2044220296007040c1d901c40d2080122402c10041000144014544480b150444200c00340c1111089a4000d04050071036400b9110301010307149440c06c2004500d000700d1000600200b1040a005a090280c00f15003040c20252005004503004551091420f400c22188100302200504101d10548058612802807030494400d40384c41143c07010403605405030410100380181d1581d144140c3d94181c06840d040c000c101480c180e1302001c101710700d486204880c014003420024005040c3c5c912032030403a000103181d8048a003503223740d040c03c4030b1031625540483c2242c1d00036049a0380c1100e5640e805044510308400c03002004d200a4402c06002c0e130710754051003203400003a80c8030080040780301080300e0003594045c40e480d40764941c2c0104001503050445020f03050400d034100360800d08000fa4000028a0207922007000c8002403404102045800d801070341050312000f1404080201c50f807a60081010203140580b142c003200c041c04040103180700d041e41250001c58004601c0307910f903101da0f142c21305 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 615105557 1250 615104307 615104327
    0x121b0a030f0501061b03030f06090609020c06061009031b0b070807140309090406020a0311040801020a021002030c070f0312090c0501110d020304050409020109170105250503070804050319 82
    0x3040303031410001080b010300641e04034441d85200a01715007071085030b5a04034043d10511448144451301d4041c0015400c40038003401003d041280300168590f00d50400c1180b500c200100058401c400041846038515006240c03e000da0b500550a010801c0341c461300a02036a00e294040c420704400010208140200e103405410b001d4441e500300d141540c1c110031019500d000e81c2c20499482518440450700251141e8009d00b6401428200071a014660394506d20840d0450343c050801d40c0d4002071301e41d0600d03905010308a0310203032002e401c5085040a0f003540740680908100284095281800003084c50700a50150041d160714442c01d10200d01645000341e00c1c5000d92003010702041c00c202050714250001310b180c3c0c50301e4078581d0003541824a81001c0201501808806a040c808001d002280c0000207644a40317a115120b40003044a084c401a1009000e9040e00f0030b11402c00402001298154030408603a0040e2080c981098241c40d541416811441000b0750303144400301c11000203504c182c01c8900c600d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 615106807 1250 615105557 615105581
    0x40515090904060b13020f19030b030a0b070e01030e0c0609131506080105030f1b060c070f0602071a12041401020a030608010506010e030c1309140f07060e0303121b0a03 74
    0x1601402960441106a0047c441f02d52008401444094a02240f031584c0b0003404e80c2c0ca1801281d6840c101001c64142203d0704000e4418080100c03c0040054000ca11068030550a2a08000001110590740e85a4404079540e51080d0f0700010942025500c904401c030310307491454808c01c900010030166112202c02031043d000403a8415000041c940b40104031164a4949a009440c103040309004d8041e81c00d40340f40003e80d01c4403003802120b00543c0100b24141c00b070040491550021402c2040181c50302c0b40b1903001803009005500b01c910741072821410380d080c0043c03074140142180c0304c6207008a03070300f241c0800300d0070250300c04141c081440f64150859021240b41d600204103607105d480045130901040c2c0748283e01a03112801c038040900f001003655221040260b40040d01900a543c0c000080400c0404510940d100301031500740d1800038081d8000401c110f08043c60781c00c68a4011980342c1c0070f031501c140c420356400400141f618004108000e0030000c6d4142c0307140d0300c0030168000380040c01c051202d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 615107913 1106 615106807 615106819
    0xc06060915240f070b0c0918130f0803040b0a150b0309030f04170c0904110904020f04050c0a0314040506040212011407120c14040515090904060b 64
    0x142024555443d100396454a6a0501000142c00680844850743e01080540b10f641e030381c1020b95076140c240d1185022207035190300d0b00c040c25500000300504000920a451000c02002c2802584221b204901d1007540380c0f2900070400c1241c0c040880c0400e400352807113003400b07500020009140d000040c07204a80c0b0b40b202e100300e0030320b0a030080d9204c0160703c40c90803055248180140803070502c00701e0035074500301e091034503441c0e00d04042c041c00d9003e4000e000500108042d515040508150740307102030400d000b1801e01c42c0e00d8040b00e40c044021400000c0c03601e044007442c80102e4203500d010b1600b1000070700841e15a40c00300813005e1000c2d8038150907903688ac10758a211000415005200d03804588450f6007101c0501a00d40039940d584e81400c00308890750b8062042d1081600684094076800c0e5005804040d8090751a02d0520071039100c1540074903030b042000200491a00802e403514801c1e108 = true := by decide +kernel

theorem cover : BRFrame.Cov 614928057 615107913 := by
  have h0 := BRFrame.cov_init 614928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614928057 ≤ n) (h2 : n < 615107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
