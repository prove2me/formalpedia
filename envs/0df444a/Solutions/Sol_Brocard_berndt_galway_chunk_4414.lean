-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:32:30.973328+00:00
-- url     : https://prove2.me/submissions/3198d0dd-972c-419e-bd88-e3ab84d3f302

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 793705035 ≤ n < 793884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 793706285 1250 793705035 793705037
    0x4050a021503191e1508010b0901031a18030c011d0a11040c090509040818102705120106050306090d0503070e06120c0d050604020a0f05030606120106020304031209030201 75
    0x1c001c500d49030400040c210540c0c11540c14400c4c01030000c03901018012110042c0102d04401a164030303101490f401c441440300344503c201e0446004001040c04402000d0031200c885907100c49544030740007a018840d0312003540740c21030300000c160b44003c80d2040d40140203040441580400301c0c060200696121500c03c40700030940f00000d04250813500b0b05500041442e0040d08219550548070800150002e604680468011b03c00140100c0c0b5118a1070040d021000242d654500c411407081d03000e0601042241d6040541c1034042c401c1101c18504da1907500205030150440c944040150310321400b07409039000700d50091155101090382d0240c005800c2c004102d0b940c0d562811515061b000b00c074298102055207034040e009001e501c55601d08100038a001c0c0d601484015600c01d00c800c109026554010061485588144000068540c11080098800f14607160269417036642030005506405100304600c10610540004156550000010004c0d0f0380160050444482207210455a641c03003170000038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 793707535 1250 793706285 793706311
    0x70e010602031b0c06030108030414090708010b0d060b0c0705120c010519030902041a090a06030c050418051020031909061d0705041508060408091804050a021503 71
    0x500510301000707403890b079040c1c000c151404c1d5a403000004040760002e800c116941e0300006410054480a1802c66240f0601034501c94130074500660003400700c400520507140e1034000042e0084072014607a102c80c02a2862034a240d4889001c400300315501d24650003024040e09117041c1122008400142c20001c80d0170503542c0b24a8071850141200001240d50007100030f142d02d80460340300694a034003a040c05004906540703007101c4200c4082011481020b070000c8046440c0c10000e00c00b04414102031000d6410544002c11003000156182d190300c0c0180001600c9802415000d00f11490b6a401049114900b0311075801c0417100c12a05104505c020341c0c1c258912107032404200150b020b10f800882442d4042c6100240b81a250703002100c25034580e81c03817582d15401051084c4250310f464424020b40c800d0590095840f1418544910340d14200030f000075104000213309900250755461191540714000a50340559007403e1078031603039032458850224444c5003100c2040800c18130720b03800e41b8820705500d0b4040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 793708785 1250 793707535 793707547
    0x6090f0d0302190303020304031704020d080309030f030405031305270c0d0e0706030f021309180c0b0306041404030f14040f0806040606060e03120f0409110c070e01060203 75
    0x402505101582201540201d010742045070700d00e60f08041d07850b8013030344002d41c1c3c1c0c0c60185001800f018203001007107410900c1000b4000981c5540320380700e0300141d02c0340c0c0e0580e4039150124420b1450180b0a06032201110010801c410804040042c0542d8a5001246c0104607111000c00c00c0100502c3c00050f004148510181c1641c98100030058101e135801700840e24250343c822a03402522a400070816443d404044100b01e126414498164104951402182411160a043c04410303580e441082149070304c2e00d41c0240d045450280000803160302400400301e040c0d44005d0748046030000c40d6018032961810f07808002b1103500e0b1899920443d85503503035460b03a01d5005400d950181540440354015070044c000490419a0004560040e1401c1d00c000c0c01d461400d40740c06002d9a2880d0022800c01c40a074402420b552400243d40700352061250080c1e441ea005070440c03458a00982e0300010246083c40c81501307881000b0401412a00c074a14180c81d4a80d454881400801400f0301c21040141c3c010009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 793710035 1250 793708785 793708789
    0x1401030f12030609092109150e03070506120403080106051c0c020a06181106070b1305030f0a050405010815150f0712020d11060f0a0b030a06060e06040b06090f 70
    0x31118400e106400c2c005010f58483c1da03403400701c40c417144c03049030100740b020311b8010100e550b6140c12840b41820301c2c00200e03190030518407024101c140d503009420302c110140c1c0c103000c036a0705001c010042c08010f060f15455000410203032542040560b400c0c0d000c0746143c800400c03214071807402c64010501c00d01a01340400c1741e00150400a1035410740c0942140901d0002c180050701d94040c200001c44c1520003130130842103030f09103c1040d1030006042c62294008125070000203034810bc500354040c0c812102c0c03c64550f06810901d096206109100700b800c040040c1683c02990081c0c058000d441d004e07661407040f50343c2d0452403100008540a125481841c000031a401407904000800084030244103250402b8400d58a0101c42c842031100c070809a00f006c0c10aa1440d82e11801408170a0441b600a003d030341403410340c68440c518083e0948422a40318051504142c0381085152561580b040d0304021080e642c02c8086144a404e9481610603804c02c2c0d9140b4443c50705806540445900422040c101501101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 793711285 1250 793710035 793710053
    0x130b030720011a0306090d080c0409020c061b120f07050d020c0d08070c0b160908031801181d18031b0d110c1311040f08011401030f 58
    0x210004201d11400c45501440031000a903001c0036004001040c0300b0071610b5a02110001a000b0740c0c0240e00c4202000382003080014001c681e25800e0400c446142c4030928008428801d40d0051407240d0300008050282550002d606842504080b107040d018500e4985184030307501c281890402c000a400020031041400c0c20513098002215080c017070314002c030015a203c1607800c0400e1901098004400541442d038200050036070100c96850034000004041e030342e4429001b000703001a46030002204001c049035000f044540003600701041100d407616000ca00c041c02201d035041440f40046e03007080340301940740c000d00c0000003600c01030ba05140928000f0191014113031802030200b10746045030009005091400e0006010f084203040307010740700c83e101c00101d900d803100e924201c03004c0056028640740c400300003054070601d000c0129058140c2501d002c0080010b0500205600d642c4000018005002e050000340d060845090b10024009002d03842c1082c43d04210901c00900a078088600b90400501301c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 793712535 1250 793711285 793711291
    0x30c120a0608010624051314040b040204030f020a05100e0112091a01140319080c0f0d2001020f04060f180611100608191a04051e0102130b03 62
    0x80c100080c56503690070040e00b520100d51041a110115141603190f18143d5019000c5501c0c0e03600b8414500000000200780b141c426110b480e9922094015014055035550440c180c00100104150344031512800e01404040f09817500300e1140303a90410000b50f40c20300f83c28514511203a51150004200c181006450360309500c15405e000396a904119000240381141e0000031b80008420a04950304140c0543c000b4041c598059129921054450810324030721b000e044181070740320fa1800d40360001460294a42004036152803114000d03215070942d41a4003516545889802c00c040321043c075403107202c1d9402c0784501304801c002920f04101c1403000710f000e840c14104d031016915000c818080340b4454104c3c2510b95401880000d0319a005440e08400100406500020303481d00c100007451620303030078607942e001c12280008001003041c45503050210700381c555001d065282d850800180b0b45842e101e0303104c00c03080e451003141c900803540445c0f060f0780c144240c0c2c0c0582070b1600607080c418200048039050750001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 793713785 1250 793712535 793712551
    0x15030b0f01320307021014040609030c0c030506270c0111070b16060b090708150418050a06050f100e0a112209020f0d0b03070e18070b030c12 62
    0x10003041440c02e00e44502c1549002500355080d240c0c14242c0c0c000303040c000c0d03000c1544c0e910750800030388400b03852185003100e4101e64042c034005411129442d0030398402100610243c6501c18600700041803000100344184107401000d801c080c80050f0794110501445001c101c06070561203803801100340e500400c085c600c1502510216001c45079150010b580036406030740b10764005a008000c03401006040e00a030341410004407101119850a600010305070b41005100034900d12402a118085071642e0b80700703400c4030000b8135401d88800350170705142e5503034035804404031009443c090024103144c46c0b007a9454080d405070000007904926200c030440300d11342c001d0440e0080c1d5a5884066404c02088401014407654041c00c0f00c0d5241401840d03003030301040540c482c0c041a401004903e4100e4031550072038082118102e8009101e00440300440c0c45c0c00380e241c01c0340000907a16824001020b44180e80e4100c4545044c4c00c6442d070325104c90644c08203020a80d01d20b51a03210a00c00c1c1e6000c0d02d89203041c59440000d0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 793715035 1250 793713785 793713827
    0xe03070b04050f1c0e040f0618050f0f040b040b04061803080a0c0f09030303180206030c041806030201080f0403021c0c0c05040903021f021e030115030b0f01 69
    0x419112004900c20a8030120340039400000c0704003410310207104202c1341c1040ea0b44035054103001603102030009140c0303202d09445190343d06252550b10302e5552001004d0040d02d000019401c03643c95201000302001d031101c1c00d898456600007060441c941da003a5201e2039000030705000b035441d0bd43d205c00781c0315405032007210440e40f1a0441001c4d86d40c0a800030719034900940d11414030f402c0619086041f0703a10001c2c020200040d81035035404080c4c210136500200ca5040c030303002901038110302c0111860100010000d500c80c07000002c0c08051180300c4003030003d952a0109606078001e400c1c091000325a8540f0000380401c0784580025249008003054950007070003401662000f100341e910a00c417840c45c090040c004078002e02885401c1c002230360413030340290006841c10031440341e250310301a64480000035920058041c4c1125804c4c55056070701035606c0c03600000d041d89025201e1440020840d002409450792000c425040249050720901030144040e0020309218200c1c803002c030044401c02d0748180000d155560f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 793716285 1250 793715035 793715047
    0xe01060806011703040b0d0b1f1b21030e030a031e0207150f1e0203150a031110050c070f0e1e04020f030316060606020c0102060c04260a0606030501110f04090e03 71
    0x1540c00f807034090b103c4c02412104c9c03030300200480902605a1007a2000030810340b2110380c400684010f0700062046c070b0f008956030744008405011000740880f62074502c800d002c00b045283c030b4a5055085801c03002c0a020744821070182c0c42142404078018210081c100c141162007002d1030b9010b0394808a02e5030381420001c616686e413550600c01c40000541214620ba0f4000100f2580c100c0c11000c0740c0503118100c60345100e5a186448071444421103103401d03445940c03e910602c0700c0f01d0181e0110f8820300e01030300946290545c3c880d461100e007850741c8601c00c02c01001c00000b480c4500d04089070010152130004d50707490303921690280b0020304401c0c000c154142c8000c01010341d8130b0980d03d40c1710b0060391050401083da541080d000900f4000792031500c90655010009000c0080c1440c415102910300207105450000042409071100c0040085003441034010790780c068080c490a90003402c01d481c0504001d1080c0c0d4540500802c0c140308403406510948000d02c004c0c06040d50641107000191507140440b41454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 793717535 1250 793716285 793716289
    0x9070c03050d110706090510060b04050102060109020a02240403090e09060411040e0109150e03040503030d0f151523120a0605041b03060503011a12100e01060806011703040b0d0b 78
    0x1d00c1d9001b050347c2641c409030081d1200b1402c0d005000181c44004a040e082c1460140042d58598041c00b444c000d4a0b004140c003140a482040017400c03507031030f00314486e00b5104000104111038a084d201580017404120740818002e8944031518001c1e0381c4200248040e135110307100c44083e8a2006015680591070300ba40041d40203090081070780f618050f91440c646032110095103421200140312000ca0f5402c24001001180c0d804020f0342c8100020040100340d401c0a07005031402440b80d20060b2606400104010440d141404d00300d8090042980360300c3c0f442074280c03c021304401c035070383e14540700b24104100701d188100c608081f50790010f610480c0840d000e40c581e0002820343d01d1906000c031203807440d8003c6446081e454022240200401d4000300040490001000c0041c00c1c580640ca00821411044011000f402c02c26141c01c1c00b084801000030000c4200340c2400b8006900c602d458522078600082610701480b04981002c8507128021480c092429210340d109070080e818140003180d40d440085016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 793718785 1250 793717535 793717541
    0x9070f060e010c05011d190503030112051002040e060102012f0d0e120919030803041e0605090309100801180c2003040e01240806220b09070c03050d110706 68
    0x4e02607406503140104080b50f14203140c1020604d0041c0240301d1f424640300480c00210880c0d05513011410301c00c1d0f0b4028076080c4140380600414140928030720000d0000303114480c04c040c0c03034007801090340207100440818401920800c9144203d41584101c1e16100c00342c040210000c01180032145404100750418000c0d06003407124402d03000c1c50741000062100da040c03424403000c1c1314503007000d8505041e160864451101d40d0000800c001c0c03281c5895800b40341d0103807031162004071080d48010184440d2a101d810f09842e50401420b080c00b90a401c400c2c400c3d160301803400107050b00c0380108207a540b0b40f40201c504006c0d0902c25103004c140000d42195900341c020400c2c0040140c111000195541d619000e054400360760143d00c64070046114243c80010300d0320340001c0c0028002ca40c50500c4e0b1580791180044c50764071111000300f40900f45c1040514100d0025008414440001c40d0310032550b03519a442581c0091070004004c0003d0010480c085e0152010303400100f8840a000d001414005265500012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793720035 1250 793718785 793718801
    0x109020d050703030816080703020a0908061003050c040e030d09030c0503030a051024080a0209120a02040b030a03020a1709090702030904050a0b060a080606161a09070f060e010c0501 80
    0x309811070b0a0510500d9008100150843c0c1c80000007503a2407a040e0006010010180610041540001e80c20010502c1985a032005c3c20300301c003e90740d00d03007401c98884001c00110311003169107010301044107070300380313001d2141800501044002e540341903000702c800d100805d002d140417030500c1145a6050042030f0708201541c07091075803900c0025281001c2c01200101c400c43d6101407a04005c504035030790700d03144040e00303554003100ca801c14200f5500c82c0c2c3c0812011b4060355909a4004034401c408140c1d01100080e0106628025241003102c04466018075071555507914000e40540d220551080c0098440f82980581d10060130140e814040309000150302d003142911181c0060b48013080b130390498601072154a4126686440400001d91000b002c10307514014400c0480512400c000050301944401e4129003242d940610403c000b2650b5141c43c5003d081482c43c2c1c81d03040350440c00040c031018000604e00d410340351800c0000707800910744041225200c04000e000e40c1084111040d40d00024000d01400d0b02d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793721285 1250 793720035 793720043
    0x1309020c030706060504180b191e0e1b120f0a0b010503010507022a0f0a0e041a01032607020406150f02060f060405090a080c01020901121b0e030109020d 67
    0x155403001030920f041540d0464005501c91840d105201004402001603984034603803010140e0110380e10707280406a20002c040e4008055030038000d070881100c03002e4100e0100c10340203039010408071040200e403030354400f49d00b641d84050a420361a030140318030782100c0c281c8500800108445a102e1340440f02c1d0308000b80e0707031004c0f00c021503242e0045c0201d140a00605078030240d90310050980c1d83d500320141c480c240a00b1071009010f04000b2940c0119102d402c6844400a00500078800e0903a0301c200403003000404031001da400c1c007403030560854001c0000700c10270304032074000740d0708210780c44d954041c04017840701600c0d03504802c0c1c000c029820060b1101d0013400000c04110034440c1c4403011040e0041c02c0b00c01e0410142c1c046400c60000c0080541500131000e030001002d45d070000355980e601880300e14144501001424204010a4800410700f0540040c400803900380c2c1d5905900c3c83e40e1aa40b008d81c0e0b0480c02c0844810101d407031040e0030341e114480c990f103800002000441c1c04440c94003c900900704d00c110070307a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793722535 1250 793721285 793721287
    0x6070f11040b0303120601050307090302090414011503050d051c050f010905180303040b090a0510020919030201021921030204080607081324020f1e0a0c02061309020c03 74
    0xc9081c545442150b07145802580918a0f02c0411002e031819144018000c905018020000c01c50030361142031844043c40e405860761400c4c1c00c09082c410050207510207030103559070800742c0c00c107005490340a6500880754004c001303081c11003000000341c840313404c400c9103c1c07513075055220a004141c400340105806078102013200826541400d4602c1c0131b603040108040101c0b06464540042d10200004896006402401d520b00725101d0b401ca0034141a58502c000d0058865000803200342e101c0395004001c407040c101c81006500703250761050601a01c0500c006400358203d0007110825030010301d00180180d00c6070304d480d001d801c824140c80002004c1100c0403c00280d01290502400750300300060340c0c010141d0305042840c1e1804624003403507203600c070400811240c4856a00c9165007807500c0c0080e08a4206501135444868480b0741280359007084c5280050200d0001800c0c0c07039003440c10101c4040801c03e64544048201c0c513002d009141d0b00840c4408002d100f0304000040e10000d40c8094681104e81700059 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793723785 1250 793722535 793722563
    0xf0b0712230a0e0105040b0d090218090d0314130311160810050c03042609030105010311031606091a0c0703050d1d0901033801230a0902070206070f 65
    0x6100340000f0080c40d0600008120038003000b064207044d40c0504825207004503c0400c9840452402903007030301030180241c403041c244404400085547c40001c1d0260781c0400010080044040c0c1844d0141c03100c02058000118800100e4030512180a80b200f0704001c40c0c0c03440e070401d0704d40d42c40300603640d000b442c207a045070200f4085202180900358200105c0c032501411810903840e9581d03c0340d042440b00c1008040d4807644d40c401c507403030025103094402c014000c100641e500c0c20300130300d500f0030030442034441e0280301c035030255186c0c0808101055513560355443d100d490600c40c82c260307a015403800d500f032107100038010a00f01c50300411640c00594440c001a06e55180c0d134080c040c18501c8444d000c2d843e9407140ca0310343c1800d511068019070440e43c000c0640c01c04030307044804c50382241c43e1075024429a00e03100505902c181131215001d42c121012110800204410a020441c280c4106c174255170307022000310410400c1c014103802410040d40000d214501d0050250780300c140443d8101700454126a115403e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793725035 1250 793723785 793723787
    0x1110050711010b0a0510020709020f120702030c0c22050103050d0e150901030513060212060102100e1905011401120204060b0901051b0115060c0c0f0b0712230a 70
    0x8a08070000c21400900004610600054501c075043c0074040c021000321050101e11442000701000411030742a04641c0c031520702c1ca011009070b0107148807600380c1050303101091145100004855200140038060a000703507818041080c0c810802d0000d852207103020a641d060030700d540c41041d00a510030b20003030044100c0342601400c4c140707a0810345031040c00c0c298070508940f035101007125415071092030005404d960301c0400c000909000c07100034144902c00306125000d84e1100400c18042c5400342c08890040005036040c03070543e0b0201c0080300154000c0820b583d00081802c540340f0301d05d0b02c240d001080c0b050700c0200c0020404000d80c042030b0100c00340081d6009509040c410701c40a8140000c0f003d00e00341a2100103440d070701c107500b61030415108100445102440a50040c20442042c9182450b00350f510180103065041106c010790312058143c0300040c0301035100e20b4050484418103107050400740d4070344a5552517490307034007a01c1c2806202044034115814202c50b0703240340394014100e60385580c030500c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793726285 1250 793725035 793725047
    0x3030e011508060c0a05030a0b01030f0e0c040501050402180d021c1a0604050411060306131e0f0b0a0b0309073b0105210106050613030512070f0204050711100507 71
    0x80300c9841c4d07032420001202d4a82d840021207074003c58052010a8030390b01180101e0080850249550700c8030b28002c8541420f130b20119040c106010f040364148026601c0e00308001c2280b00d225084446101c0304218945070741400380c94840d1483c00200001250540780d61401c8110844540c101c3c0c0c0e420840c1c0e5090a84855814442e8101c2d030207441c100141c0c6010380d100c80203079a526540b503100d6500480050301541e1650001030101e592114140102040c0040180707011148450310420b0904200d00391104208600c200760b00c01c88020a5501040d1410012006c694805007900d040380c00307250f07004210314100d190301c0c540040612884000c0942442030380b81840c5402c103841807134451840010005030392002041034078241302c8898403094503400300c0c80710b0052a65074400f5402c030201088202d00364076900c0d8803400b100e010390242c80604001c030403201400c2c481c07127000a01042607601d641d000750400d43d21240e800303007850800b00114250002840c0c9014980054600315071b40b00c4003000383d0703d64459 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793727535 1250 793726285 793726291
    0xf040b01080c0d020f27070207051c021005070b151e030a1203090c0e090c01021603060216050322140303120a0212100305120a080f0403030e01150806 66
    0x4405803000c1c0d002d9400141c0c00b03491014010b0303ca180c440c10460780d25900c0018007490213265103002e140410f0034034449081800300302c801c10054021246c00184504248854001031707452800410304414084d400c0121001d8004c2248003045002d0004400042040380060b0059500101144506400300c04010103440201c044104046007140d0303160b46514002115a6050750005060300203017002e4000f1001003080304409040f01c01d525000064002c000001903006a00344026551201e04030030041e0780c0d441c051010440c9000c0540c2e0100b01080d03207940602440300c0d1420144803c100c454540c9891508120304e9200038074150f2071964048000d140070800107010885258001c01c0c03008002a89170f000d841902078084620500281092206074100c40103014191110310711404c0501c0103449030b403a940411102841240a5410700141800644d4400403190781e501219680d001e003140c03e802070150085040c1521401d800e10312240070700500b1116000c3c201148132143c6440c0410386030540203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793728785 1250 793727535 793727549
    0x2100f110c0106230f01110309210d2d0306030b0f060f031b0d0f0f03050408012009130b0303030c0d051005090c0a0918060617091c0212030f040b01 65
    0x602100180c0d51250a4450b6000e002420407400640240300303858118402d64241c140e1020700c968150a604ad04000c0d0b0442460711a022650790110400d02515482494074840152100b1881c00d001100d42416000078108903a10b40402d4051b900d07074a203114004203859568007200a030040000d2820001c05081c04500d0450007009031a19958402001a11264855001e450703000350400512000074800c0f011241e0202a01e900c030302c12401c00a0664001d409460059400c10b8100e03c0e01652421016090044140c003052900f140e00c010000d0700301003d070180340c138144c44410b0f8862030f540c24800303188034001002c4030302c1d940d00c00e032801041102d10007040d02001001c509014081601c8045000f580180c0381c504040e03503824000400d5540391015801036240c081c8002030007246044a401203000c648030b989034854501c444503080c40165004560b030036169401070700f038040114000c4542801282031401a0b0b10705c0f07203100a801243e5441160581c982e011a001880700b00060130300140d00500c56 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793730035 1250 793728785 793728839
    0x10e0a0308150d0507080102120a0203010f060c0203010f0f020c0709020c060a020c0a0f0501020904050a0c21060b070602040303020609030a0c06050c0f0a0801230102100f110c0106 79
    0xa036000303044480060042c200c12040d400c0c040c01c1c42d440b9003039200c5581c0d800c14101c076402955040740724040d600c4000007030700310104480860721820031802564140c0f44e216a00c280e403582032000803a2205c042c1f0f0020b0780d2540d01c800005e500080140308000c00100011009a951000070070214070b0010243c0c4080903640c070420080304102008a80d96401060182026a0781ca40101c100c03445c041c0c1150001e041c0e91031001681c410800c05500038490180280d4003800180e445180e6a8125941c0c03401c8074000c54150120040851656a6202c0740703c803041c0030018880e5115202c840c00c070740001000b29083d0785e002406106140c0c0405c00c450f40104404019441c180c91518000c10720059000020b103040d03124404100d0301641001907a4605140300c09607919542d13040d03401400e01c00d081c810440380e504003e203a910300140140707095604110607001007103440c0400350407400406002c0c0451699556880004074904445002020702410210020404e2030400300c882001c24501c230400010408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793731285 1250 793730035 793730053
    0x14070308041406040302060301080307150612110103020409141e090d03020d141312020c030d080a0e25080316110a0506030a02040e06100e0d080f04030308010503010e 73
    0x2045811907041d0b404a0290108030000034000c81d4050003035410080d800003000c03001103410f0b03400001415036503004440141030710103440020801c4031014021013840d801c0078043d000100740040d89640c1044410300d401803800d5034500b04075080300c10194000e554101d040c1d00340400e038800800d01b0704110b0501c545a14181c105805441c0c0e6942e000d0348d000d01859000324103400928070a5205100000f41c44143d00381f145407020503610110070b040c03411640d104c00b0407498030b04030740b000441200c0400060002e01d41500c00602c180d60002d8020024210f03e51505913032051144e00b400f00503e82500e420710341c0c00d0b480307029075a141d607a40039400040c81640140542043c0002d0414840d0031030b074001d00421a410304c00303004074082800a400180d0081800410300201452660041080b9214101d483c503aa0700c85400300852121240000d0000900b50407211400d881c1c4540303440c03006807080c15420719200d5014070705200c5400c580d10a4000c903589500410850900707004490344104820302a0048074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793732535 1250 793731285 793731293
    0x81813290916180b040e0115080403090501030207050703140c0a061119051005070e01030b01080609040b370c05030402030d110a0203011107050c150a39140703 70
    0x4468a00101d0030410f0411440070b00d00045060400600b40549041c3c1d0b44a440381050402e080081c4100c02ca88010020031624051240380c05e03900695042d030310500700d14907001c011070180d005660213484a025280c0c0000004180440c038136003c00040010301001081036041021a00d1641d129a040c0103c0b034840004402000c100d01e010701c210244040b10544050400a103010b465141c0e021881e0302d0602400b410a800c0304001e0500c0000340c1c4c06018200070200110742c414000c1d60807a41200015020074000b51250646c00d901c003440725a2102c960885002102a03900a0455080040b03440b02125032100c00d40e010301c6e0100041400c10626504240d03010030f540d0703981c1000e041c0810180c0750050311a40428004420b455800a009000d0644d40b0201e00780282d000302801c49840c852864a6605820301d40c0d0138000c40e007120a981c60604031084015640701d1040e00041c20b000c0d01c1c550718102122038883d0321058002104269403035104251420b00110641c03518050501c1e40101c03c100002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793733785 1250 793732535 793732561
    0x4050a0605100801051305010e0f0a14030c061f0504020a050306040b12070305011409120a0c020109030213020901080711030403060b0a0506120f060103090818132909 73
    0x1650340014001059907454080000142d07198119591070b50030711041c0315840050003c4009841c2c0030720005c00031000c04030141e43c0d460001c8203420205400810001c000319078401040c00c8034800c036500340c900c2c0111031183c4509189007101c01500d210501414004c20a100c000030030041c0800340d80840c07600c600030034060420b00006050501c21a110412940c007030300c8580b40900c600e0100c104480007903459207081800781c034800558000801121001502103940064008600c4040e000c01c0d924040c6107101c2200e03107960a220a0f8140018003a0000c0182c0310842c0d070488101e00d0800050715041000d0005119007400340100c010080c52039808543c0040201c215000c0f00e41c407000c0062510f0700303000442c03640c0482c0d070311040d4800000300d0707840d5405400b510b4040c461200255046616500d8000643c12030762040c801601c145020701500145071952074000c4511b41000301241c0d0070511400f0a901a50303020411401030a00c580e500d1940303001170031131100d1000802c9402c90b24910b8011408841 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793735035 1250 793733785 793733803
    0xc0c0d03090f0212010908030a09030e0a050d02100201020c16150c0201091206060b030405161a030135070503150c07031b0b040f0b06030d080a02030601091d0612060405 74
    0x1280e0180c0c6103910610b10709500a06c48154844541c03612860444400c0000b40515401607011600c0820b020280b03103000c65480054a5004080b441c03415000e40900c40c020040c0704044082d59800c00c00c04490701c408104100010862124148d1001d0034095a0101c28150741c002c0000d01245105a80040c0e0b00020004140d842642c50343c1d803684518200701b07003d40465400000d0600c8004144800e210340440ca203c1c094040d01a800c0505a442441000300b880640d000380491005000500000d4a120800e001c2d414886006082c00f0314851503850306e02e03070115070304081a40401e1040159007000d02940c0003014048030148042d2511500003805886a00401410003408030740c80c4032150440201d285070f894004001c0301140c0b0f05440c0c1201ca441c079a0500741d070f1000408002540034130700013511903083c0e001d550340c510b01600d515401c00c0103504050001780c1070203840c60010a04111501861003190b260750052002400e0010901c0001c107019101504160865030070400403d20018500e80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793736285 1250 793735035 793735039
    0x803032d07031122210807020d030c02060c0604113a0c031104050114031506030c030f01020d0b2e1403090c01021023040f08030c0c0d03090f02 63
    0x30440342c2420f52030381c00d01c149075520b0083c0d6070030026614035010f0210b41d4015502c602c00740007901d40e60000e04811400f044d410081181008012520043c06c03c4075041030100d00c01d04100010011990002d003283d000580551640d500180c10441403040e21a800c602c828025104000c40307400c144c00308181403c0400366500d08a5581d40c88861942100c40c070b40c40b001d504841034684903502c901d80304082c640c1d40c4440c10300c076504120002c103a4408100c0c1004007420024001c10807843c0c0c0703040301126000c000301704030383c1400741102c200110f8505200c6032000c14500400140c0d11600b40503401c04403405401040d018912007580610394941b190114486012280c00d40c0001681c0d4850403140400b405460901306180482031000e0b00e03030300088100d00080242c00b0b581403102d0300c2d10b5080c100c54070743c1071010704401c5017030000c841c58800d01207131a00640561100c40ca0303d005500e608995500136980000b41e1900043e41e16954003040c05001c0e0207044030b180034004000152101003200504a001078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793737535 1250 793736285 793736291
    0x50c0703180e18100b0a050f030c061801020f061006201006230f040b0f03011a090a020f0316020a0203010e1b0603010513020c160803032d0703 63
    0x81c08610200c0e50741c004151140074807400f450900c1c0322000c10210300c02080300c0d0740b04460000b03a40000034060060070b40d40c054105600c551410382040240d03000b05803c42e0701805000d00d2a0100e0311240700410412000d80540000089441d0009292127130216058545130448000d105800c2c5030501d40d032044a80c580341c080607100f020807561440141031541c10701188103d40203d41b50310500e402c1501111f5654540080202c2006041c0c4002c001e8401019030000d00b03021400d00705c0c43c250b030207150f20038005080303981750296020209003142c0e41c08401503240908071a40c1403103498080007040e80401d00140640c240140c0c0380481c4402c0c0400781c40c142421166030381c100c0c80c00b4800c010840c02180c00034020b0000c7c400303c0c9841915240d410518910030050b226000034541000e604980c1201e4002c0c02c4c80c0c004140d50303c00100250081c038030303154180c010035840160b0240d4040399040600501409541c8e02d0170a0700203001d480440090170100ca0388540c5040c80301c0341030070503419807000031400c002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793738785 1250 793737535 793737557
    0x14120c0904140304180c0507111203070206070503030412020d0210090f0b160206061009031226060301050711061305030f04060908010c1701061b081206030c04050c0703 74
    0xb09580c42c09401c42048644804500054110702540c070744800342004020030443c40c2c0215104440b07500c2a000b000e849184203060045d0141014042140c0014016090303a08002081d400201540c0c454407040c2c0d400e0340003000707020900220241880e100401f5000420b540351707134010040d4840a5000c0800390090341c0340a140140102036208910040d4403080c040843d19021910045580616900780014840e481c001001400c1500d8401c0e8502141c0d105e0b141c02070b19542d1800c4c082617034041d00c6010488107101c24502240d4007030113492100032680c3c0040192402505060031580000d01e28410007903040b00301c40c12000041001c5400903099090005011241d01b0031510b9803181ca64a00d500200014000036030560290190b401d4588080080c410300d40520f4081b80c81e1010402000c007140d05850040024038010545540c0c441c4c02e104800e680c10744503864000ea280c10404224510b11401410080b0500e010b002905042c14119010016810302203466200c1c4c1c0104d420090500c500708400e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793740035 1250 793738785 793738793
    0x160801020c12122415030f0601090b0d05130804030803041505040f020d02010c080c0115050a1a07050106120606240509120c03191a0903092e080114120c0904 69
    0xa000d013600c401030301c00c00f0608108880002c0d82d03401200ca08103030b500d205000c80d0166100c0c0708854125a1034001d0f035420000d600c136204008140240400311003c00c605019000180c440c0d020f40300440c05501900e44924003420144841618009071840452a003010440003d02c4030300c4d02c801954040c3d9688006a40610040c0c2d000266a0000f4002400c0480d6911141c5415000343c41c1e0001c00318401151169a042400071140e203034000c015082c3e25414004844520003805896124000c80000c103003244d80e44039880085007000c8041d81e040c0e8480c070080c05944443d007100000c55401c19a022a00c003010440100f85001e0070300c8043c070407089031a50380948881006048c2203060300806071084203014801483c03c1540c2d000d400c4800801351502e8405504951065900c940c04460245161141d840308001c881d45000038402d00f403c0034282403852401c108071210b0541000b039103c621180d4185581c2075081b05000ca80c03c1c0c894985070003480160800401c0f002c0b00800240c0c0c0081a540f55403070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793741285 1250 793740035 793740091
    0x5120f0d0b06120a051005011d0427150606020d0c0308060609060408060732030402131b14090f06070c0512011e062105160801020c1212 60
    0x5040d4804030120f0b05010240c61264400c5020341e01c0080c84143d015660801954030780304000d8106040100c008070040036051907004411080040c0c110002c0070045003600003a03018030030200350354a0401c1440e688207240b0921a90000e0100e900040c811760810180080041c544490010100001c55001c224607840d0842611004035004048640703840c4c4030741440c0d0b175841c012102070300024046175810070714951340c1c039038440080d061886c0c02c0c5501c0e95021800080c1d0344058402c81c0c1000c59184224030304445441480302c496807903c043c600a8203610401002c00c0c611484880d01200b0400640140d50784000c40c074200b545007a54820b840e00b031241440030119841d54012a000040602c0141c034024041d440300380684e40208500520040b4242c0744006c0b1401c501075226451385003507044010400e8a1007444601e80305108440505d91901a481d0042005a0261030365030340101d403100d02c0b81c50030f100800d038030540c5400d00e070300f0682652100c22000b1305c054600e0003003885444652200e241054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793742535 1250 793741285 793741297
    0x12061a04020f03060406060905030d032307020f07050109150809010e030f03070306080712081b01060b1c0b010813080c0d11010c0c3801060c05120f0d0b06 68
    0x42045465000c5101500b54590049580901c51407a0510206456014000f203405a80c0040d0007085c02518100f03099009010400c1e0318003103401c02035071085049074010b01c80c5201f403d0035400b520a01d203c1208641c64001d10307400c01414084403075018000d01181191103509400c1c186800c01607901e034410440d0040c07101c603541a0840c000011060b00ca210800c00542c001c000d95a400c1080310360ba80c00494650086020308000814949844070100d0315070700140c62244032920f600f1024564070b08500b03007155801d80c0700000301840440c0c44069400e0107100790101040144007400f020140000003080148000c0a04000805000d070324001e01160000380d0b02044080012a042207081c0000902a114028194581c540c241132040c0714491040704001d400a9000100e14802c00d50400a5403c0f000d10313040805200354808503195401c9410310140e4006c0c029625920f042c04aa41012420141401c48000040c0340070030642102c0f581a02c11108034032040040001c0303e074100b100248041c0310328 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793743785 1250 793742535 793742539
    0x15101701060201021c0b06070b1905190c03230903040b0a080402121603260d0b100804030e1009120302011d0a020607021014070515060a12061a 63
    0x42800480c1c01c640560040201001d000d048540d08204002d002085c2d0700c10f01c4c8055007022050140300002084000650f42120442a0740c16110300802001000c07120115241018010000b1745164503d81d1441540400581880d0038005a0089490305d04903001583d4480f120003151000144126001e009580140105410140c0e60345850f0100400a4200380ca06a120711841401a9040d000c0010016050124012840700841ca59107410140c0c50240c54106a4100c82407035082d008280a4005e0518803800381e000517a10307542c40148140c19031010241e4050003a00424400440d403c9a82c03528034081c100c070391410318030f0713442e0049801c4080c2d54003140501d580c0e9104030040503010740080408520680086640801500131950340703007188000039410103420400c010140c01c081103000c4804c551410721684426100d148062141d205050545040e00002c030b4444440120b00ca034070360001c1c01200e500e892981045031822030001e5160008007400d0342c43d044410601d0990107800041000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793745035 1250 793743785 793743827
    0xb1801061211161e030e0907050a120e0f0a060f0e030c060a0506190e0f0a020901090306020904020f03011d0601080609131109010803070b0a020f040302010c08070c03120809061510 79
    0x1349203400380080031040041c622070070706000040c0c0080e1080041e03400c000c41d01d075200d0380e00e26400440b40c2d00400c5004803080c030700e002e82620494105001c00200da0014402d090005800c2d1480c0f101030212010030340f103000e06030010007002220000c00100c0300d800c0202c034600050641c42c2d50300054250304492a0765103d49136030100014821215041e510700c11110203900c1c030034642d00d0098910480c450300b08048d0110300c09141c01c0c000710381c80d0341c081c04035100098801458400c10aa2541d0250170903803103c0c050700c2081c040906404a0590015040202030078580110306050002071705901008190400d9080300c0810707101071100c85c0b01c0a035004040035000014035611455020340b20391011500b075900d44202008601d100c0341c54800c441001547e0b10b034581c1028111350045031412a241d10907100c80405100480100c0c81c0715180000840c862013071080104511940030344000383c014107000443d0449030800c0ba17034802c01f9000d1001c2183c2120300e82d00c4002010f506660740350318503c0c2280c4840c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793746285 1250 793745035 793745093
    0xc020630070e040c1d2d0109141302070f2003070f0302090a3606050a140115110f0708010b030d0903060f0b180106121116 54
    0x10000c240d60250380c0641d1000000110740d010310003074039568060362001035818549a40c0192181040c2da00d000001031070410381c86c03c448009400910940030b4100c1035481c1c00042c15075580c05c40140e030001d08854803604240c1740440c0002e21310020606844100715000035103c8100b00180340f18412803603001c40c0010170380c260b1001e0800f0000d495050300b802441014008a4001000024170044941c01040000203507030711020701024004584030411510310240302c604480b090095009018503411048034145240c80c00e101007902e42c064809030100385440e5030001c2519010301c4842c15107100140c00c3c062100110341c00c03181c1a003c684c2d0b20704140110f520800c180d1001198100440720410000e10000100004042c0c40d0380070018400c000c1003005d0700800009829030000b10201e015a82d0000b8410016000b1070300706070050204000101a41005102d10390304880c03604500094040108101d0250210026681c8121003180c02c05e01002c1e45c40d14100141e402c00e424409243d10782c1682d90314 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793747535 1250 793746285 793746367
    0x19030b010b0d110d1505040e031602030304030b1518130f151a030f19030e0d0b01090914160e04150204030503040f0e190e0f030c0c01030f06060c0206 66
    0x1c0c5e007220030780d0100d0884800061034a494042d030030141074258003a40c601110070366255030310807150a04030f070540810b00c000030102d402c03000c2a034070542400740520113022a0701d0802422020580b220800c1e01c02407000c1c80b4881041c4014001e0603070f440f020120b0601d5039404c15400d02558131518912850400b21540700040203e0f2242c01e03100d50a40031503074031000f5006036540f142d5901212460b1200d100e00e11901185c80361200e50340b0203001500c07000741a00d160307c6810740d02c60b09800074550300d504c5503001820005408280d681c02c02400c2d0207084000d8403072081007541100303445604103d000e09004030f003d001d420040c0e0070302d03d000c110301150740d107a41c3e24115882e60490700c50000b12a0302c0450004c3d80c4980c0039204e80c4a800c6104080ca0b0f09618801c8800c014440681184024421742641c46c3d042c3d007007080280500324545d00248503001c01c03040010261240f00c0c0c41525010700f4007004000b42604003ca15050550403118151926140230010040500c080d8094113589001101140e1035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793748785 1250 793747535 793747541
    0x301140907111b030708070510120603062901020c01050a0507050708030301170607260a020c100608010b01140a0809031e0d24030b07031805010b19030b010b0d110d 72
    0x2040050303050390b2003a5919146c2130740b600d07101d10a41c0c0d040b48503000034880903803107010440b00c80000c0311000502d0603242d841d0442254040440015583d644c6050107050031013461240e00082c809100074607610350200c000a02d940980c02181c403d002c00402c0010400c070040c4903403809000450308403a181d41e5503020f9131400301c0d400c070746e4204c40d406410003142c40c15200380c0d1b0700b4580340503490604d505850000c1c0304040141c0d0090080c01d0f50790f802d010f43d80c00350006210780d922801b84031a011600904242032103085521000d0304034140700740c400f80c03c0c013145000416140061a2030810000303540d1944401802d52080328032106201c468038441310b4001c000040940003031584180c0800c4040500da10500804460024078554020a9401003000642c0c8010059101e6100d240102d40a0701d0204919034100036801b003220b103a5140e400751807030390600d07160741e064115070074881200c40d900d5911071401d044018011001124000100e41141000c03c0d04801c0395400c030324101a079200d0400c0100360003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793750035 1250 793748785 793748833
    0xf091b0e01060512060f040627050c04030f08030403030b030a0f050c0a030203100504080d1a090a0b0108040f02010203040e0f0a0f150501030f060f0f03050d05030114090711 76
    0x8400322002060880c03248080d200902c94004040d00540c8a201c01c0001901840300419809500c6060202c6d454412100c410100c041007070285c03a02d40107100b00e41c400c1e244014110b0120100902c420000310740c5030362588c482c903a0090052944c03916030307060032030242941c003039100c4d003521070307142d0007810001c582c80c1240c1254042c601307840c510203030178041014109051002a506a0000c43e02407036100d02d0f41d100c00d4101e0710500025141c181000a600196101030b040583c05030001d921901c458142000056440b00783e0000422603682c40c240060145580500701801d6444070607060011a40204201d4014201d124580300803460880e070b10318000c22049034801461424010f480c0840103241c001c01950040d0134480601281c00c0100440041461b202c0015081d6140c030000138100e0a41c0a840c00a44000c43d00b6211080c11820140c0c9070940303541e010340c1004402c0004012540b40103c00c0d02d00040210b81407111503d40c1601141c100710300c0e00803050103008102500ca031f0040b80082c0520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793751285 1250 793750035 793750049
    0x30109060501151205040807021018080106050f040513080309030c0a0b09010c11060a1a04152d15050c010c0305390901110d1701090e0a03030f091b 65
    0x42a5442c189121042c3c941c15200201000d40900c50580145410030001c1e8100e540c0303180c4000c5c1811901c040b98100c917072f04c1d40b00c540b05940d980418806800c1102c0d0980551509460602450a00702d111050303c44841c100603066400200104681100520844101c2600d04003220340c40480d0341000c18980b40140c540c40c43da9803808501c88585800b4262080103078840101402c1c1e00d0369541c0002000d00b0b40b80500030311036801004880300d2a07a4911a4101f501c81d031741b00441d115401e01e8503511003900303039040700f5900407036403224210ba4070b080720819810740e08030010890a0110642068034a4082c012041015509145040c610941d0590141d84034101c2e1000b124031448400307022010f00104001c03a011000c00c011131480314100310310002c140805041c0740c0120f100060710b28a6007490742d5010104000783c015601101440b107102d01c1e031400351030104001c12940d0203800b00c1a544007080c4000405168841c11074420480160b44820f03c619000038a5032118004002c05c9400c070361250241403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793752535 1250 793751285 793751297
    0x616180603290915041805030307080105061305010e0a17101b0926060109050f0105100819110d02040e102d090c0503061008090a020d0203010906050115 67
    0x10681c901e610201800700030b0242200c100c94a40c00b10100c1103040c0441250340203926424078101c94038041c2c0300c1000190040c0091522420680001801020f041e44001d11801040c025000404000c50041c801c803034090a00c3c2c030f4501411008a5030a04044d4001c4c02d0086140801c10a1401c012910042240030304504000181d00240c0e410f9400d00c13000701d41d1001411010040c4002d445600c824800002c050440001442941003623524110007608603c105a44803800d002007111988400c0740900801c0b41c40e05202c1c008083c008041402c028040c541c4203103c0040c040c2403011035030242103251012446540d89603003200034680694064450308100036010347c00544408030000c507010546221202c00c400940c21180c0040780e8485038441e82861036040e400000b1500c043d845054020300c00382d1107040d1249442002c01031401c0c5822030200c1070001b2401008030030704010600b1450705a04070303001c170710340328040c00840e0052040250081580303241c80000f0503000590b03202d29003903a000c1d9a0315 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793753785 1250 793752535 793752581
    0x151018061803170c010219020609060601050f0a1101020a030213090b0616031e08062403071b0609050a0b0114030c0609030c0a03150e030405030616180603 68
    0x12214044030107a080c0c0e5520407000140005046200344400c1c10400d00d0340c040c201084030700e1882c22603100c0c04102da02c001c1d8803804811480e8050007c240c0c8858a00060145440c011001a04c140300c1d04c3c14000300e5550025a450001c2d0045214100440140300210345628030410701600952210a0019548141c0c0c0800541007560340200d19200c00c0c06031482d81040d485030146502c508100390220188480c4886948a06241480303409001c0903503500c10385242800800d0040c1c852a070329084c41d58416a00d8074504914507202100d41207400c5141094403a60b20a07002070b2240c80c5140010680c50808415005012000410010150080ca1500030b545d07600d14190800c55100e006054064004c100754014a11308100034000030a0041c0030b072940f0441b40d60006580852680048441c941221740c14245400e0500ca4520034071000c00c001c0d880d00781480c0009a44200040000c24120300d80303900c0c0301020344602212105050030001e200c0c8030948070302000d0003411421b611840a083e8860308 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793755035 1250 793753785 793753787
    0x1f050a06170a020f0d080712083d0302030a060f0c090e13020105070b040f2d082b0605030c01050702010815150406020a0209090601050105030a0515101806 68
    0x2000107150a000080490b98882d07400d02040743d0f10340d82116409005a6a0800803901c8040240401485401441001076495002909807070019090345200313001e03095622a0b41c076002003098083c54040c3c1a261124605103030b81c00400d071040c0c00080d01070055601040802006400821070707008000310a200414bc640001c807500e0a480c030031717520b1040b280e00100c1c0907410b442c00008284c50040c9001e5140008548407400132105c09d440440b01e100611444c94184034140046111076200c8050340403180c110340741c40280103031841601611481d80000c1074103d1b0031402d01100c00c5a1100c945000b1844040703900980202081e20455000e8000c0314482805036202e081100c5a09605856940481c0c5950f003509402100b290f125542149020100c01c0300b01911001410040005034010301d0388804510502038602c00140840044e5407000006101c02ea130440203503a40100d00403800a203d079950462880084c06010190b90000040210080d10a5000d018210380d41c1c001c22100c4610743e030b5220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793756285 1250 793755035 793755059
    0xf0f04020c160e040b010308090406090c0f0806040e0309041a0d120e030a1205071106030c0d0605040506182d040b1608070f02070b0412050601080a030f050c1f050a06 73
    0xc2c00605d4412990014000500810302610300c20502810000314540c46a0780801122441c44c400d50200b81d15103085003295510120803a4010790980e0140b14100d859041283d40c5d0040b0150288901e13116821a500c0000441034a002c04000801c500401002070074500d0441c4100e443da0700008541d00b00c40030103803d002948151040d4001800d0000b0074035000c0855442e00203007000c4400101041100f41555558000743d409000400c2c11145da440300c0a03481c3c1c0c00c48109501c00e9010364205410403240f5035601c80d24007a0080b5910b07030704400d0745d034152548a0382040315103800d03140b9070702414459626016041d020301c100e01c83ca800b01c0322510303140540c20342207680c05000000101d030040000e104500c20344d404040280b09004880c60991100c81081039604943c11542d07194a000d1134a00c20f001040100c0c50040c81e41601804034100c02da20018140c400070300b07449090140004041003401d00400c90918031043c210305004034180c48203007020107014150350811000381400000f00c0c40414180c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793757535 1250 793756285 793756291
    0x50f010c02030a0809030c01050f091905060720060f1801050402030639091008010b040909020612040b15040e0c040c0e1c02011b020f0f0f04020c160e 66
    0x1e001103081507103e07041120884070040041406000600070f04007210024040c1768000d14820b040c10b102440c00d18481403030009901103440620f00c000e420440410700c0411a150000740301d150050041403091880011502100ca07601d02900c22138041004102c034141200740140741200d1a4040110004c5c406426035a042d50040d41c540c009001145a20f50621107001e0070b11032034000941c0255001c500c1081340400700703042d4000c151001130402d41c43d250160043c0040d10142c20500300c254104003d501841c01540543c81d041950780500074103640c1c5800c00e403280101000c2c0368030349500e40b41c40c113030149030000d5940b0750000040c0701140c3c41501d000e000718141000c00c0f00c014214099858200400303400004106401d005400309001c0345622000c100c1c419003205a0300d484070013070180c800100742910a40394420344142e94042c1c032005940300301011b2031810040b548240d9070780c040c2c400030b004010407001c050b5005100041c2d8424449000c1018080c038040030103940041e0b545c50000e0154040300b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793758785 1250 793757535 793757537
    0xf0506010309230c030f010501080d0207030308070819050412031b0c0204050a1b092409051225091107021c0c0f060917010b031020040e04050f010c 65
    0x38110501041000c0c102140c000c000e0780d04484c807140011003c01c3c203000c4044104009079446800500401d2020400160b04e80da0a10082a4070303465501c1c014a1010090441d01c10848028007041c44d0040c4207218000a10307119404100c10b04162400c040c42ea00300c24101c601080c1002e9452002d00300a1642e00c3e07000b80580c58401e0a07580e00d40c2044001c110080c81c0a001542c0e4440414002140000180c800c4440381c4071002c40904100700b5110400198410f01c01042508101007620380e40507880d0812500169003041c0450129a46035041c02c514001400c1ca059540d40394800c00702046441e0002c680382c50200304050b240c0b000280d2800e12907400040d400104518800f038008a41c205401502030040d0059480c00c0c1d1103018010381030030554441c0d80000c1c0a500288401c103008980d94507403046a100800650354034501180e1176100f1040722464803540c40901030482250f00300c5141320a0f01030a05165282d032240094111a0720980f804d45244c40317107035941100c0582c1403080229481103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793760035 1250 793758785 793758803
    0x30d0309031e050c01050109090b1510050d02071202160f1203080c0f0c03120a200a090b03130c0b040f03120323010302120c010512060a180f0506010309 67
    0x4080b620001e020120919102044010000c1c603042120a2103068068468600003080b80d403001d04150580d03c4000d0250000d280c03c1e01d03c0c1060030b540b80015001c4982c003604125846404540120009014802016007075070000c00505091650114424115200540a081d5000d4072644045c6411455000e006400a01b850b07074000400c1c007441c142503000441c00300c01490f008002c2040415a00012100302c1c0e160300104002004041040d81158010507009041001005841000f107211800c051001e00010001805201c041e10409248002c1d0408078280c655905000c60a0020441004000d8800040790400814000280300460303080b03c41d002510f003c03107070440d01d48200070031106510405042c1d6408440d00102183e450042c08122220000c05c000d42c594018466101468240782c5a5030300800c0030344096a0b046402e46450300001c1010110035036908010580c00c6589400c2607040d80d04085500842a406410149400c489a02c0c18005c580b04c031401581910380e813081c01456669 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793761285 1250 793760035 793760057
    0x2a03030206280e010e19030e040b030a0b251e05090904080a030612080912030a1d040b2e0503040c18110c0106051c0206120912030c09030d030903 64
    0x55650000a2036001200000460704a003070b00a51400404006c0d800709030141440354414960051030b079000602040d80c052241396400000a40c807030214200003450152010b011070410b5007030007000c0c180c000002d0152001c03403e0503500504603100300490091500f200c07644866865221318151440c80d440548644101e84490755a65610703009000e000081550b43c5000045d5090105902004c00b4001c02e1800d5903414000c041c40411800d088068441d54010811032905a901251201218410121000d00e20352200000390140211000b4540e1080c9070040811903095820220050740d00211044042c0521102051303485000807103004e00b03c44207084080103212450800040b03208011103002924281c050f082c40807980052040100c140c4d901c0c0011701c40d9007403a10740040c414184000280380c641440c1c0c000b032003e10820380743d80c07107000b9001c02192018a0070400c190901015000c9640c41f46002802e038001504886c07211440b034411001d081c000940039110700700c900343e05660f850314032031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793762535 1250 793761285 793761361
    0x313030206030916060e01020114010b180a05040e03030f0f070c03030c11060c0c19080f28030f060b0a0215070203090d0b0912040e04030c2a03030206 66
    0x5040200494494010440c990f280c090744c01c001e03680540b506413140d02940318410002400c4440c20100c4d00c2801d09500010f01480036020306461554a0a001803c44540183c01080d0a01c1c0950300140e041810042849224200400518882d14945a2300e481c2a031754000d00142008041d992071000c60380c00ca16580120b0301c650800f01d8210b03010305009507403800c0c0740a02458248100e440e00d01c241c901080070046481c1c10b00448403240340c00b54580c1720112641d128900c07544120f042d040310090340002d10012a03c139040f58519904030502d00318460340c41100000e000b809049a414143c030385410390202e208500309003910b044601542c0208108051031030020220320015141c00d05611080c003081c0e5290350343c3e01100e11104d210300003242d0350b402e011070701e1450504900800500d041d800e11051150f0208094642c1d8040d4040c50041082841400d204001c1903680b42024030140c4010210010101c0441801d000c0360312035822260540e4496224202c030b501c0b81e50b01c07512500c00c596207050307280c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793763785 1250 793762535 793762537
    0x1503060c160804030f0c050103050a021c09060e070b0301030c0906060e010f0e0a260321220b19022109100504031e0513090903090509090f010e0313030206 68
    0x1040c40b07242020324158076510340d1a110b400c4048222011110301c403003445696810700555400511141041d8100940301c10890003494100c940344071030315507903202c8005000a83d00082d1440012a040d5000192100401c1103240d1003400192800c0004260000301c81c910f920480d802c489c0c103940d441d0744d18450304004441004561407210204840300807503020700d9440b0600c9600030510301c41c0e5804401c1e01401c201c5042180d081c134010712600103114005119510246e65a0b4003d11252109040e0399910200115941d654003080100d9a003900f00b001004141c204860080c85034444078110014102d4490003079106240c442e40710184503200c01c2d40c40307045a11507542c210601d00140d0742c080d04044000000c5401c00c0307038180c0000e00c84841c44c1c0180c440c170846805250149140c213500d031441000c140c0621003414400c4003405552001214103241c4200d03004806880c00816005003070400f000290ba541850101e01403a83d464103200035802c4800004035405002c071a405094030710726513000c101c41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793765035 1250 793763785 793763827
    0x70305030f060f130b1903050a03050f0c030d0605030610051f09330f140306040b03070f06020d1b0816060f150602030c07050405180106030602031503060c 68
    0x1060b03104450b00d0b541d00e644004090721381c0700030006100d416490401c411243c1040130403082c81e003c2d10090000c101c02040400300f150300340c1019566010038100c1c0c0c5c0c2003841480044105030102080f40240d00a232034000400301e0314200c04641654940c074804c114461001e10078681d0041500d0100341042818200c00c003603c1e0b0050418408665480305201c41d2401480144c6401c2c4200c45100c0c05186040303080c10b0340620f4545020307042441c507890060064945103806c2c050904000c8001a403690307c41c1c1103002ca0b40c001038191020300341d80d015102107071103803030090801501400901d141401d10803040341d0038554008500e0300058040307846c3c640003644400c5050806001107500c2c600403451a014644c640c803584040016405000c00300c81c10481c0d507641080c401c5400402c220008100001860010354008803000122030303e808400500303a1801c4459008594205180001400b003158051031141c0e0b0004d0031044150701902c20192142000c0724a074207800001e10500301401010080501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793766285 1250 793765035 793765039
    0xe2b030e030f030315030106060f08043c0b0718050d0201090b1201080c060307020604111c03050301050a080102090d0f02210102030a0b0306011208070c1e031106070305030f06 77
    0x301034002d5400903400c5900132152a800c0a980c4041651541024401c1e40c008010500e012010a5200c0800800a40000e8400352480000803140004a1003259008042204840d001c18604007071a051318001c14110500741c40f0a201d19000500880c000c9034940c03542c0c110000d200344500d041c4010010441d07501c560a80c100100c1d540c01180d1010900c1c01088d860707044111400c03440d0700d840c21440c5009400c162540c0034031021700a00c4a49038000401540080c0e100e408002d20090580102d8003501454034030701080070143c2c15200a158110008606a40c804d407035010401d52030301c21041c240c1c0b00d00252250814001c0382c481e4040b0301129001010b59200400480b803081e12030155000b20b107040014240340e650300009220f0703080b0f901d10808504c660240c0282060790b14110311a040d02c20488009041031074009101800c2020404182c4040d14079040c1d094401030018201104030032440c0800c440200c1001079066035131034400c099178001e0380c0c15950186150b03511141201d070500b010b08103035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793767535 1250 793766285 793766293
    0x1e02030c09040513061b050d050702010f1104051503090312070c020a181a03030f0a02010e0f0105070f090f180b0d3f0e0a0806070e2b030e03 62
    0x101d5550745a000d12030142c460b004480c00074400070f05145040301c074981d07041c85103650564a001c0e011a0450140c0389846a034642c00520340e1f690f20f0044e4050034002560759501d40c0740c088440000c21404014105803841650294502034203030709288120b02c815281c0b100c4607030081c080b0700c00c16459802c002c4d6000712645001400745903942d020800030444c2e80c0040e44904001040c000543d0603a20a181c80c02080040301d440d101d4130b0030040ba8803841a10843e81040780001f0b03003004000e0003500005a2140c00b603048450f00c00100d40d156009001c1503a034800043c1e0748131041d030121841904000191001091009009031620030041046496082c49610668850a0b0b4102d00c1d55019009007885025961032259109404e06c0b01080340708181c00c050718000b908050031000780d17909180304140801802e102c1d24001d042c50000700081d680381c0c440c1d400ea119240c2009455940040b411480e420180d030410b096010440712019003540d6804159025448100c3e500c0200e0300c00c00504850b07060286c160307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793768785 1250 793767535 793767547
    0x30d09020a0f030c062d05030901020702090103050607020705101e0c120801060206061804110415031a06040204050306060904060221100801020702030601062303010303080702060601031e02030c 85
    0xb1510b0403a540d4030540d44d441a00d40c04029081c1c0141703a1001e040d4030800350129540180740094003407104201c0c0d207402c0102c04000100400000d44c100c441032500108066030350741e520f160940da581804c0750600c0060080e038200140c9802c0507a040d500c1b0305c605445140000c08210010000c1c1040341c0d8001c02040f6104a490300443d08190026420395a44e1b41d941042e9814500d02a2405002070402c902603c01195404400111035484603000f590000c1d030f0181400c1658005006400c0215071401403400da20400000c0004040d09001503075241c144005503540c03000c1c204001c0f40103503c00da03505904031800041403480c1c10a4483d40c481c1c1b0410740103040008040d440700705241c40c8034291091845210600ca0158402c4412000404100000b5881c000c070b1580880e45429043c8918400d1003114450102181d160320070f95822445040e056030388940e5a8140200201c0c4159400d0000d4090714000c07031025407090041144052540e483c07480c51020201210000390b200038a2001c0ba031805101c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793770035 1250 793768785 793768799
    0x25150902150a050c0d050a0914060f0c07060f081603021608030109091e050304170c060d020904140f060105090303090d05060106080c030f07051b0a060e0f010509030d09020a 76
    0x16003250b8601e030342c81603120b451a814161034264004100b0040c0002441228241540030040d08142c0348000c075507821901260001c24001e0254000d0b0200c214400b10701d5000030170700090f2000031030b0740c260740709070607020104010b486452007544d0404074072988119500301c0c14000d40040014440c801c1d000141627101d52240030440c0c1007a08a1017a454031800030b40188500e400b0150b56404d0500001c1c40c0d4458103543c0c59549102d07a1082c06680140c64022044140d000d05c14842c612401404440d516001030318088000d5004941c010310403482c20b51100d80020000201c00d100340c5001c1045c0c4081c0c0c4030140156096001100d0459161104009404c4c1c90b0b1150402103c606228800408965044c100060036401004000c0d03510710006004000c2624180c1500c990000d4150614680c1c0741001008082582010140d085461042c80201420003003158401c819004014055480108000c44604c1c280d801c141c451a01e103500030302950000903003aa100100c5544010001200b050742c07294 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793771285 1250 793770035 793770037
    0x40f1103150124110601030b04150c030605040c182706180b030a0f030c02010504080f0a0623040602090a03050d120b040e06040b040c08122515090215 66
    0x4890041d04045229003c1e0651600c141007091504040260000200c84c003580d401e014030000d8014036001011800303000003100120588501108140000b420100c03026010300704074414580100c0c40c01d45c0e507c680c0c42c4a115011304421038011203052581c640145c0301c060400c2841c8d4a070510b0702034821481c40c03081c01c0c86210010209a40581d000c08086c030700e914101d0350b090150501070342100301c42c00001404c0c001d404921a034142016100c880e4140012111800382e50400d102512030b58050351080c0781c0004444800c0752180c60207001c03110010102c030000a8084010007140f107240000310f030001d01d40c1c0c2c015204250b03016041210721075903a100c0c145000c98411409003c241050240700080000340104c5042c080248d4040c411407540c00010790307071142c0041003d402c920304400030900700490003038000020f01e10101200c2014041038503042c260762140e04800d9031003aa000d09501c1150204114100d01500410340c50f0b410120b1500100240020390401c13a4800010311200c40d00c206120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793772535 1250 793771285 793771289
    0xf060305090607080f070302070f0c0303020c120f0304060806030a170a08060a0f0918120504050109080f060103201e0f0103050c0307030c02120d23040f11031501 71
    0x95400305203428082203140c1440400b5000e0000c0001e40c80401c103d16010021a80d004840e5140050b960042410f140f40405585034008145880c9103030b000003850750002e40c40c4907047c0111220340f00700c041c031180c1e05e960324010382c2c613001ca98005100400c02c01c1c3c00780100c00d600c000c02034203030b44098190365503034982200302055510030b4890100721401d2150b44400d003168428002d881e902c0605042c83e0b80c2d4040f244d998841d01c0c90254890442992a08103008180b8099a10240d000805400c5030005011900140a00c0d0300080820341c00140903040010104800311030f0b0009844140d0841d01c0394803844028030245d0744000030103913461103181c8030902c180c4030060381100d116185032810410884940140f900d900d0415080005002246c6000710440f50001d00c00e04000816003510b00307050b0705045503405118040c2c0d002148100202405800c074026080c880c1d290010310f040090880030710860142c401030000c1e40c05408840c00201106454510700b04000c04490b8600b40140580100b03401c26 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793773785 1250 793772535 793772537
    0x60c030501061413030803060402070203100b13140f060619080403030b060309100b040f060b18090c04062109051e07050108160e0603090c03071215050604060f06 71
    0x103440100b2080e81e02c07401c0a84003407031a05100749041c020f5811808800554040a09110b0001010450716556541160f8060b980542501d035140420042c2c0001800d59494150003400044000d41403280103100e0544003036031000088069444851540a00d40d000500603600010b007009880c01e800580c2c001d9014a650560b1010b002d441c040ca402000e070b1700c004807000c0c0101024030610285513000704480074919010340001031002c01400029005e00700e203d03070010110340340c20030101e51104220002e0480d080e41b01c00300c007843c14240e03080c0034150710308481000c8a500144418070403544a03030381d07040a4071200780c48207074121901c124101c00c66111f400d085031a07a00040c20140c400c102010301102e0700402c840a0142145440000303008808001c0c81a10302c0c0c0e8045000300701249c000c0d20004512030f405001c940d164500300240365692402007071101e110b44651346000490322500a891240729500101c0c141150045d81c1044016000141000b544180c0b140783c08241c1c0010310380801c00074445 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793775035 1250 793773785 793773791
    0x71e0b0d091a060a06030207120f090b0d0515030a020a090f0914030307020106060e06041707030609030810080105010b0a0e010309290c071106071a190b030d080a0b030a060c03 77
    0x20700f04010001400b6440903050500500240c0041011000c0a10500c07000d4104005480c04440040715101215006011179980202d204052502c503079201c644030320780c0440100200000e02003050b50321816660025441103c02405000c4010250000741581c0c10402e00455481042d5843c4818060303030b824a4080d40d4400700c00c2040842d424050701f03001340070a040591054406c03501003001c1d480b49000d41400c190005450071649401041a82e001b15040001080701e4190b502d0020081d0740b055910251580c18924046400a0180b07e814120b071505c078240d91600e28840c905580c80e2408a100c2d606041d51a2100c0000c509004202c01000c0811804a260110780700c4500a4110700580b0701c102c600001e000841c0014071400a1559401c000c4451580350001c61074200042032030708000f1003110b0b58103002c0c04900ca030a05410303021602554014000c080002050507a95411043c00c0e400080c1105c006c50802c800070390003041c8202003d0180c40ca401d6540d150070f02660b000012540009513 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793776285 1250 793775035 793775041
    0xf15071505041b0e0606130b0406030605100f05120c0c0f100e06010f090522050c040b03150a0507020a05030c060708071407061503120e03071e0b0d091a 67
    0xa24900a201070f4a40c1c0403803200b21410b100d00c2e140040d1004200c140900c500190060740c2280b030411000081c04c0800003959155103905006014107602d2048a019042000c9070004039401550064804002c550307800b802d1000c0d40e40f1038240114098401c2e030712020208140d8900030008d2040b003219086950041c044000c20f402003804540050a101101b904044010311480c004e511040d400c4074040e0101042c9500d4411502040700180310a001d118031060500c28200403010076800d02a52048130200140d1507014149611000783c10f103c0c800b9110140009401106035500c5075401408070710440349004a66501c2c01e00c0d590158121003400d034000d800304480d4591010b0165400740c44c510b46201038a80c00d8a1115560040709001000c0944420540350340030b01d0035921200035a00a100b007010a140040050a41443c111100d0302034040c001011130405d4110742503005228194003c00c1c00103103404c410032015041040e90315041e507112030950000c10b00b03a018040001c5940303003c2104900b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793777535 1250 793776285 793776293
    0x1b0a0b0a18050a0302012003190f0914100f0207121407052b06090804030b1905060d0204050c0d140f06010c03050a0e1f0f08150f1507150504 62
    0x50420b034070051007009920810700060741d200500d1158050314900039030203802917100450450290183c001c50240462007540340069110402281c04406500c82c0d402c055112a0b121114000381d403c082c0d0002014800b106c880b52090b220800001180d1050340c400716221146070492221040080d0350f0000c0044101885040a000c400000d2600301ea07401882190b90801010010a440c80e00300d90410f00c3c20104103000e450340241d011a9400b40b1069507032522881c00780a5110705a807000d080920907484c14100c0150741c40b40602480004021007007105140d03003000043c120040c15035403032030018010440c0510b90780c05074881d0101803404010341d601c0e024a420f40c00450061940f4108180b0480420100707401030111440c0340c07200d18040000401c008082041c00d00008041e0b14070041c0410a110011b030300042540350b075165980c1d0f220300c0d0345030055907080c1c1017400d1056580c42101011401a58600713140d40000400c1d580b1405403d119290b1503460121900c021803100b115124001c0000700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793778785 1250 793777535 793777577
    0xa05010b040c0801050904050304050a090c021b06040b0a14040314210426100209030d0c0c062007060c02010e04180605131b0e0c0a021b0a0b0a 63
    0x14140c1520204a450310746400240002010f2040c18000d500c0e4802040602c1400d10885010b8038001e448440c0c003c3c1e80f600303840010300007003940e8401070154013001c103641c80d00418214043c1c0700040101341400d08240c41000719600c60741c4008240002d60941c0c141c41c521320b0300508001c50040031f440c1e594000307007a041070500c224410691400b00152956008078443c02090300d090300d0300304c0002c915082180c007170525003000518004449225005904c2e4010303c00e5002003181941c180d041d10103104915000b515540302c2a180140011903e01d0148804d0388150003590700c0305070030f1050881d9948034000321810b02c0140d4000c100040c40e40b624000555811844a44800d502500c0420441441032a8002d1402149100410740d0340c80300c010488a55000c0200c03a2426006078090340e48091540100945005600c0340d03803042c1e80c801300020080c54130303038049e14240c41441e0042d189a001149444100c484130704400d40d845004030740b0200f82800c42c507000d40b0168046032584e09000c42500c00c26020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793780035 1250 793778785 793778801
    0x230604080903010e16030f02010e19030c080d1b051609050f100308070204050c04260c0102010b10080903041a0d06051509010503100806040807120816051b030307020a0501 75
    0xc2d5100342c08440103175401c20350703d104480c0c0040b402c5580d0321003480122414600c1d01c011980c003004201b81e2041c0b180d41c400740e0302e040364802c5206c1e030000755441e944142c0310410a680300d4045110710b82d042044843e4644003207060781c071410590b81c01188483c0c25001100c4180c000d0341c0303a107540d1803c005d074625510304119001034400c5840d01200d461039580c0c00c40b40c4540c1030000d0140d501c88010904401c0182d042c0e6002d80b501000138003401d554510447e00c86070420491400b07911540044400035401846100b2408402500d41c400d4520a814103072103801c1e000d081d0400501c0100800a2514001041c80400800e034041191361403c4e07840401d41510115048070b441400f20040c8084111042800c441e40b020b402c0c20002c0d102e580d441c080340003e001710390090059014400410040141d03d030010701459115810444202d00c0d07114045541880031542540300780304402ca241d60301030080d0003502006618a040300044100302403d00c0c1140c0050351540301690280840008200080c003d00300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793781285 1250 793780035 793780061
    0x203030c0d27090e010e010c02010c02060114010e15091c0311070e0a0e030408031b071d13020f3003070b070f23030f0a0b010c23060408090301 63
    0x140781c1411084a00b908215445560703041c6680d03c1c01d60110004c01e41080c081c50401c100208840c0841d0417000e4040d01c403c00200005001301000445c1814541100141c2d411041e52082500042d141c00e003d2413200181d9096200003083c0310100091741c800008003080b074842070030400c4203041840d014010040301c100c0b01e8001d07042001e091203100c0c00036420640c05180c0580200c0c881c2442d0310418210311590308010740c540400a0142d42c000b008000c042c03900360495040301e91480e550186001c501a104001d8000340c281e440100f60412410300b4030700120740c0000e280f030a60b4144000014005000002240f04c1c81e041e440030200c64200e8010319a2500444c2c901542c500040303540c1d55000f00781c00034601420301645c8080526514425a1260780c0003c410b20f804614200d8141c407101c261300121040044a0318440010b2081403031805208106041030312801c0c840c1000399070302d0016080c1a0040c102040d9002581d08002e1410081c10380550b005900c01c0d40e44544440070705003074404038803100e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793782535 1250 793781285 793781327
    0x5070309140f1b180c070c0b16060209041e060608011a04030b092d010f0b03030904050612030a0801090b0103050717070338010905130213030203030c0d 67
    0x1404100302240c03d0401804650540b00c0d600ca182d0002440c21944807007980030f00c00e08074100210690a44d00a00815000d01e000e40c1000e66590b01e07107449032040700380070085d030750b04410300000003192600500803020004101044a4422001502180c0c01080a80b0291a15450100166500700748440e000d4050a072480c0c2070003096614070f02c26840b8074400185800440300000c1c40421060091058000028251908900c01d0b00e1355a0030481002c110480e01f07500e4411540c4c1c1c1c2c40c030075110b240200100038025509252b850000c2000800c1c000349100e4010001800500030101c0c00d000804c1071381402c1d210301c480c5504041242c0110384035030803040c0c14580b07028240300485030003981c40c0c00060410318000c541c664032144210058a40c06410032065040d0901480d140d56241102c280c1d901d08402c0310b0303500d801c1400011100c0d100a032040711f801c807103200a450384280030b035001400380c2c00700184500326107552035010a29540c0f0800c2010003030b402414104081c6a0f11015048000c1802c010070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793783785 1250 793782535 793782553
    0x11030a0509060706062402070e0103150e100609150e0105181b04030c06020c09011401140c0a030c021306150e0d141c020f061b07060507030914 63
    0x3030401c0c410307550306a101d42e0000c1402001c00131160030a00241030203014000c8080c2901c4108407400342d40300c01406c09402070700004a00c66140c0c040050480390001a01000140f40d041141c0c000e0032a150110001e0080c0d03c00380e21858400d00a00340203201400e0002800703d59070508903a040c4103030300002084540d04004000b1962000c0c81607001d01500602c030b109940714583e8403c00c110485039016030f2003501003400414006009085000c541458081d80c62140e00c51003000000b0b0000d0040132120f008410040e022544181c01064540051f81e0307030b0603d000c40008801e8540303d900c0c84101c000400f00e040c0441103080540f0500041800800d06006043c104803200c10b5a1684400c4101082001c0100c200c0c5541c0d4030580e5030300c03a6081000c0d00141c030003450106032100d1300814054209500d1080c0e10f50340328400145641421180c0b005425161940c50103188803041d1085126040403040c0f141e40d020400c030b03104a1713004401e103031400280d160700c82c030300541007140350711030140e40303810807035807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793785035 1250 793783785 793783787
    0x7060e030a0201081306090602030a0c02060f0403140706240b0406090e0c16031205240f032d070b0906070b10080d180e1012081c0b0111030a 62
    0x10400740c1507424200000d05550781c0c511014a0358884401410141c00c10a00d441400016801140103040140c02801103903858201a41d840c00165615012680d030440000d010170300c10811a180e00784000d15182c6081c9150311450295a01e1004c80c9103440704074401980c0000304c0e05000001080745030015810145841c9004d00488214858694524000c000241010140e034007200e4480d6100007540fa07a03c0da003030400070640748003503200c202500e02e060301084401d6074601c400104d4415140c40d80c24a020340b1001c1c07054841521340c480350180300f881e2030341e003801100000b1602120a00d0245100708a62500454585816580215403503481000b12945603290803007101c1529401c4500c0100c56143e11800c00784030000341c1d0044495026588002c21070707503030000f80c002000301c203642c2c0c00710000d844204072180c6182c2540c01070070000383e80e10100480c0034108981d480940c004c403501400e01003400b0480c411200d40c0c0c40c101d03280303690b240025241580c000c2012148083c4c450020740c14231f03c2c00d0710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793786285 1250 793785035 793785043
    0x10090e0c0f121b0d08070605070207060810060c1509140c0a14060711030708030901170f040f1103011406010314091207020a08010204120215191d09040c060207060e03 73
    0x714040e0f68002031840f0342d1980b134040d0a4881e81368000c404503604d12075030624400418003901c21500500841a001840710300c0b030701200340101032506c81d0240c128900941507818045465086501703045244050420100910411507214010107a410318074a00d50703e03417824aa2082900d6120b0001c000c428802d41d002109044040d0310240c40d03c070399460480c204003507503500250380d003581446505808108400b0101c080d24041d5001e03220800c540208100041007884210303551204585604002008640c0e2405000c2c02c0a0040f012440301e00c141002103820740d20000e00002411084400340180355078503110f046c000a50a150030750050030000981d0303807030b66401c000c00285032001145080566a80780c110350018546c1000856950b942c40d203222284010383c81007039102da445950b2401002040d20200c0c0d084020015607100304000491058441001c1e1240f0982450315580c400816510307540d850038003a5010b13039900b1510900c2c0200003482c100b09500b2800810030303d04212840c80c0c40000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793787535 1250 793786285 793786303
    0x3150e060a09050c04050109020d06060207051507080d050703020703200607051b030301090f06050a03240605040e1c09061403040515040f0b07090e0f10090e0c0f12 72
    0xc0710105549074981003840c501009000303010751180c0b81078000541d80700c040e0300030807040781c06940c180300705581d50304180d0b110a1244280c2d44c110894001d01184154400020f0010511880b1400d04041516512008488086a41c0d5010a5000942034141508000100540c000814031512a0b074920b0144980310700000d0702607000e00030042403048200c0151600a01d030743c84100c1c200c2e83c0b20b6a43d08000300c05890480c818290891810b600450642008010982074a40013900031034002418204c0b441c8043c40e404410740500c1c0c0d54840802d140d40d680c0500448120713400000c01440070301f0100359102c43c02104540c07003440303074042080001c02e030001c4003800300e81410003400b9120358890a010342011140980900107001e1607041108020301d075102ca10915029660401c0180d0300c2420542d8044000c0c014840c503010070303000248a043c09404215400054151180c0daa2a40c590801068070510404c100d6203070030124640100381004542040d0411003201d03650507411042000c5900c4110301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793788785 1250 793787535 793787551
    0x30a0c0204060909210527090c07121b0609080d1415040906200a0914062b1107050c0d112103040308040312080601090b070507180603150e06 62
    0x101e03c0d200000c3c1c000d8050b0341b01f0f00802c0c1d03000035100d1400d1016880c0080004c14080c480c013982c80c08190b8a4800b031040d640c54941c030102e002030f46807006605a6104208400d005080c50821441030001036890140002c42d504c501c0d07031191101e12490303400342910000e81c6501005102d020400040c10582d20f6006800d00080c1ca00060040e641e0401a01911101e404100682c0c8803141d8080b0004403900100704150342c41c1e9940f08819110805d218a07001100515984407c0c140000d5851004990840403201070104241c065055100da0010580301040850304201c040030900c5c005001043c00040b0850908482c0c40301c04403095600d203e411805c150002d13000303101e18640e141d2000800003075038080d20306c0c58007102e848542e00e2504d2002ca92180c001103800b01d220041820344240240e4189014580507124004c5050034100083c0c401c0d003165400391075501c29510300040c0020480c41280c40b0820002c00400c2c2141142801c08903018211011580c1c1890644141c2a41c41c0110b14176802c5612 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793790035 1250 793788785 793788833
    0x61a1f05040603022104050705120d08040b06040905010c02031b01140106080402120703060b0a050904030c0b190203040804061b2a080316061109010206040605060a08030a0c0204060909 81
    0x50325110f000e0322a205582a05c40c240038040c402405400644c41d412a042103403002d68031200c04074030545960901d0301403004280c0103c080340000381400c48281d80300c90040d0000640d441c070764507420b00303603081d00b400d03400540c00c0010030381c190307540d6400203000d5103141000034041016158403a480f40d4005205a80030400080082000c41d03813a00c50780c500d1070808130b0031107103920784905004008080000c1c041e0f10540200700005813031f0030312456807441180c26071100142c4080c0e644800210210051042600c400c41c0080110f680300e4600c091405140980451a200e40c10038001400b901c40c048101c0c4134072502d45007400001108011a034401c070b1030450b240001c1003548120b11000c26210b81003107485000109200c18641074550348074920320b0044105000040400c40844000c3c4503003981c144c010380000340000d0100e91144c200540088001c4c06602c4030316039070101d460030340e080241250009074441d46000158135141c01000c0142c00581c5081001c02c6a03035866001c1440e900c810f0202c0c0c3c0301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793791285 1250 793790035 793790047
    0x9061508160b0d0c0e100e0a05090f0f150406120512030c0f0f0f0a030f0b0f010c0209090a12120e07120f050109020a080f0f010203090c1c061a1f0504060302 69
    0x7109440c4c0340d511240280105441c0030384000054406200d2002d044d000b0003508c41c0000b014a48070b000c0e05c0c0100030980c007003021038490340c5824414542c001d00c0c1c0d1140381e614010b644c1c4103446502c1400c00800e1418144040d28075140b07000340c00c20f00700410142e0720703140902c00c0c880c2240110b021510700c141e0001115640d40e0140c421440b4078060405184040b20000c5444d040b010b8268000c0d80031440d04607020001a64035a04002000c00130706500d9002801200d413101c018241164410b4109100c42c08440c00d8680d55510107180101403100e0b00002541c0404002807042c19020380c90000d44400c001c0d000550034030985c0c40b02030713010050150407e0350341a141800e00c8420b6100ca540960084c00c0d20a040b41c41e021003a641e0300344181d05d00f401e4440c08804a20420303040c829a0300440b161409840d19280803410040e6206004907600c003440d0500c10341c000050b020784980220b0542021040c041d500c03410b002c11649185241c40540005030b121042d501f52381d4080102c030245c0301c89041c0162104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793792535 1250 793791285 793791287
    0xf1b0402040f05220f09020f03010908270301020a0f0f0206010501050d0f0e2a03011a040e100203130b01080604020d14120d0b030d0519050a0309061508160b0d0c 71
    0x4d05a024150b0a02c0d144c400e400404402680264035400c2c000e0b5000782e807841481e414142211500b03400507001d54000e00213009054110b44c00340803401808115020501d81030000039089a00c1416031a01150b4a07002c11070a03d0380000090004601d40d0000c0e203800d41c581400609030b4882c4800c65014165119564401d040b16940040b503045200000c9414064031040c14000e0044850419401c0c2182560200054035050140c2d100c3c0041901c41100120b003030a042c00081c040e903200c0c1c20441c0c09000d280b61100002031014621400401e00700d0001100e950820300ca6603603061f00003da50303070801020000582c4501d0780c5007149a0b070003240039070004039003030342e840c2401d000310705810301d00f5400100590010310540022444090440030f8503001c0c4c0b40c00b1416501c91180c441c1c01428078520b20140b6500c107000ea00078282d06029800e010030b040d084c035a01c0c28101c0e410402014064043e0070410b00850504001104195084400c11804c00b401c24182c001d0341e002d000080d6404c2916194002c01c60303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793793785 1250 793792535 793792579
    0x908040e041a040c450e0f0a06020c0c09040818060708030f100f06021615020703080a020c0901080604060501090509190c0e0c04060f050412030f110f1b0402040f05 72
    0x1d020202c661941e40d4089090621414003101c25940c42a04051044000b821b000c42c1c0500202c403071100420101140303644880203500011404140c03805842c2c101c8100392100102244210720a244541c1c0d181d1a0900c580b00e5264401ea410380603213400e10400c0e0018450000f220b40017803581d0104c4240d076036006002ca912052641002000a5404500084054000a6402e02155441207246003030f5168081810040e44464500005034081383c0104041400f6000500100000d4816612840c0000d0081221800281c1c0b0054030741c0c3c040c0c0c0402092000c00e10645001d005503500034042801d001031195941c2e0b200d0b02408019580031155041003003541035a01c00140b0051525000b89d00d805404012079801030f1040e10085162109030034102031244003120143c8070a44036409500680382c0b022a445074040c46ca040902c04000c41c0ca44000300b0822501c84c509455800401d690103601210b9207406c4810b08806004d14014481841030244410fa214259142174030659119011070b0818080d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793795035 1250 793793785 793793849
    0x606070c0801420b1b06160e0409020901091104030213060e010608010501120b03031e090307141302091f020d08060613050907030908040e041a040c 65
    0x15610b4104088040d0350381101c0d800d848060b9044001d052104040e8031440256800502c100e24140c0c03102c1444107000c120f010f0490210b401d00d13002170301c8251030307a4a485c20100b03851074509050790044a81002d60f010105010a8205450902038a0796683c080303083e9036418002c4032206511a403450704003a5407081500e00850f001420220510718a0040c0c400030130090060603540c040500022403164029201c882c100c41c0c060f91141c0c5a800000c143c5001400310803102c59050204214181d00b030814084148000031062100507662990700c0209032802415901c10609201c600d07000300b007a0f40d10061f03000b0149510420140c0c1d102140b46c00120641f03860356100006104482034003460550004203948068480c0e1109049603c40b00f007000a2070040c01640c48170710501e80428010340c140500f9080e0007000a0401017030400a035610308095402a030080343c032040c2181c3c00c200c01c1c42140c06203d81c2d450740d0f4104000c41030500303485601484905001b101e92085c03c2d0000c0d64151480400380c004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793796285 1250 793795035 793795049
    0x305090409050a2d050303150d0b0405010c030e0703150903030914031e07110411210a1808030115051209061609081504290103060c0206040b0606070c 66
    0x1803000589402c0c4503a45029036510a80e205095040c0c00c1d14204003204031601d500171005505540d07442d10015440d240b0ba01445411540072820340c000a1038a08846024902c540004501d44d40551801001c031621800b4010240e800140308001003a8444074401c0c100180b440c0105080140781010313005800041c00c010a00709a54a4010403d6004000b511013070b04003c0e6070245840b80e00c0890703580c0e40104000a801c666140c0d0081e11709241a9002800d40420201c800d03003807046922441e800b44150360110007150b5060710802c5501030700c3d8814003245000d24840582d0b981260b88032198180014040c40703080c000025103d203007031400341041e00d0350400d00000030041440d003510b2964a600d011f5841b40f8403c000441c6400210780585081800d40310350400500703800f0a0741241d0500c080c006802030302d481e180d000304010307800150030350801ca201440303210180c030b540b66207000360880b40341d00142000c41d0411400e10001852018003030b50806d0b41102c1d065110101070400b0780b446452540680 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793797535 1250 793796285 793796293
    0x6090911090a120c09021e0306030f01151e03082b2a1e120e0102041e060f08010b03040809031b0f04091101081009051e090c0d030509040905 62
    0xa1125203009600f01030340c0c4903015410b04150350741e0040060f805142c0d0070f0000b0040506054650003040b1002c0c5602820060445200e9486d0301d02980c00c41d12a00f410301b402807403d80f010b010743d40856451100b4100b05110302c8503442c0c9035884155550042c010b0b1064022400c0c4503658020031121801c1c0203108050104000b080d18400014101c2c4c0896a01d515241e004503c1c5410303800c0c0620446540721240010800003d020000300711541401c0038022102e46a4411652940500900c098000b9100350001840c83c01c100f03402e005400541c2c2c0e40003c00308070b080359461100b16840151541100c0000710b01035120703110341c5841e81751401590b18668042c0b08030341c1c0c208580ca1800303541ca1403014003660390150050030101400f0542e00310010103010302c119a501039021b54841c41c032541d0300c201401d142c0300c0700ea501e441c80c8106442040e510361581c05e010441c00c0d112056000031903a0448610002082c0030303003004012600100003070b040a000c0c000041880704071503c543d00b00b00d101075800b5060f6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793798785 1250 793797535 793797539
    0x1203090703110306160e03120706090c0b340b04030906090b0c03090d1707030305150a060e090613060f0312022107020609120d02061006090911090a 65
    0x966446005100c02c0e14020300c800c9506405040100e0113034015508503a4412003480e03418000c0c2d8140110f0a1401d130180314100d40785884104290160804511604022400d0007070b506001810561b2504034035a1204100205100003101c031401c20401c001103181d07076a007500301070303002c104c0b844041201418241d6440e00300410150320039104001d54a0702c3d12420000350b00c0b0840e12925004594201056610811000c4040e1030840e98088a075440380200342160b680904a801c181d41002c035044001c02c0d110030a00514040e0021181c40081040d22104036140c58801d00805090603800c406010705900d001180b56604c5241c030041c0c00ba002c140c000e00400f1783d00c0060b8140e082081c40242c611203622200b0481d52440411128060007064140c88030b55140d800d443e440c258800b60302242c0c4030004200d00551031b11060a0a0340c0b01c4402c60203000d1240c000200a070418000804000701645452814807205070016a900217603030311010005146500d81e208410940f08600005500a4540e600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793800035 1250 793798785 793798801
    0x42106020a05130e06010207060e120708030a1b1502030a0b0a06021b1801060f121104050906040506130209060d14100801050f070e0105090a2d14040e1203 68
    0x7014401e160110f03ca22082c4e44e0407080c034502c24151461401038000c01c4082003400d104c0c100c282c41a00340240400c0517096080302040c50201d490344604983d0308007107106402d240c0c200c181e02b80707400102107240548000325601c6000c458440e240d00100700b1703804000309508524541c80b807401201c02801820030745844000c043d60301d2205420044d0003505070307401050345042c50756690100a10b00709038264581d003449020794000610882c200204510404410401e10050107840a4089400c22440d07407035040405000810100030507160080381000280f240540b5400c0130b80503a000c000900503295038103100003404074410040c01550060520001c80c104140d0791000f0740c012140a07000085280e600c02940742a100304640c0e42070f01c280c0120000d1a451f00548541c4000e40052429610b4070880c00c0000d0650100354120801c0800010760900704899031011000d5002154191100c00d10b2401030201030143e0204402d5004907242c100148032000100302c2c811700c10340c4150120792a07250000b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793801285 1250 793800035 793800037
    0x901050a06090207080a4a0102160317040810050708070206070804080304081c0c020c060705060a0f02120420010e06030703110c030706021e0f042106020a05 69
    0x4800800d98582140041c41c00654403c441c00303503900c03000040c14600b11510580392030202000340d0030024810020052014108071a100da071403030410100403150540d80f041410024555140b506640c0000e880c900c2c00c0d04101ca4510487e85e0240c01203509a0750640f15841c94000c580c00305407184642c080e4011454080c2d0407141c4580c5041c1e13120881d40e40c910b07004981da82026541080030540d20300c0818040780b0f42c1c0d00116070040c0103480d00c43c0b41c216031540386130b1003000307591175100c51550b288126000d4170b6041c0400300003280c0460b43d40742003207255110f480c0c98481c00741080c6003c7d0303610912150445000d80568400d0703502d81c0d1000615140c2410001d44202568030f03840100c0290000d88041580120312019000c030003d00414156550284194020a03440303140144008052040d0780654904000621065209007130240c1c40d8480e001e5a41d40700344600c407820082c0103007401260b28100140e000d41d0f00301c0c1c0c0c40c4c0150040c1500204c00c12545013400c05405040d240c00000c202e291103801c58 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793802535 1250 793801285 793801291
    0x100b06042c060d020a030303051b030a0c0e030f030a0e0d021512100b040905041406070c03140c1903050d02130806070309051b190e0103031803050d05031e090105 71
    0x1041078541d69a02002c100d080805004000d5208900000920102c1d10982c04680d000c20144006030300740c2c240c49002100c2e50030450366008242d455442211170039510607640c4003030050035002460340c401c005960325280e00480c0e004c07a08200054030b40c030189587da050900341c8590050202510000710f01c80c030140b59802190364486568481022030940716810200030300b20384950040c9414a07007002e442030040d00c8054401e0310601203451020449007000e004550252005440d500a189014900500040d0140c1202c0c000418103100c101c0002402142980140c02d58008002d040c1e20540350640d510701646900c1101e02c1d02c0070807000c0b80060076902c00c00c25255014100e0703909585164044007030f6002c014004080e40c00115a2005031031040120380f501020050280b044500004085024404181c0c0303c81115102c843c01002072640125840d201e00e42c2c07440d2100110307411600d52039610009001e01c0300401100100140b104240100c4000805424407070301320030b90a000c01082e010302829 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793803785 1250 793802535 793802609
    0x21390305061b13050904030e13061802091008040203120313140a020d060b040b0405190e0a03050a12021207020a06050105060403020112021822050c0a02100b0604 71
    0x40d10b04039009000d4001d84107041026040140c11500309020301843d0200940201c0c18031030280703403013042e643d11540a101240d40b10174000502c0e40c40c2200380744134845003c04990b0301c0d600c1080075090036201d81c841103805207401d00f0000426101d03440480d180101c040c030075240d04c90022090052001c003418511118501840d03c0f2202c090061700016182c1c007420348003c2d881200600c0307900001e00d0b45e801c00241030100500004001003000081004e80d081150300f0810100000c002030702c051800d102d50a8010b042900034200203d403658050300600c0354002c4041403188030610080280e4880d01100c4d02c00c045850b0300031981c100444081c1d030720b010100e81290510308120001c209810303d01c09a60440f038059480c24101e44800e200d420013548a0414150070b00e98003004914a91601d42020031404c039002d80e81d0b450a4111a100f804440014024800a0341d003088040201303640085ca40c40300b807000000000714006800005080d520a591150304a82822403c100d06440d01b983d01c02c00f08002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793805035 1250 793803785 793803811
    0x61505061c020a110a1a160f03050406020d06030b0417070c090b0301150b1c1e09020d02040504140c030309090403030b0307031203091106090a030311010609050408042139030506 78
    0x11f2038a841342c002509081103400600c0001907495050710a0b000a07030000d0141c04c1c010b150040d10040c68054034100c0e0002d071030001d590410f01040080d0340f6130002d0352410841500f07081514640c0d800b1015400c0740320b11040151590381850385503070294000460306403001d03843c17034510307941e1421410550403403000785904c4c010700e49041c51003008a020303481d080c00030003151030503c070310a6040c1c000500103d50140e030409500f0110307a00503195882018044d60140042c8040e2400c50b600d103900e4420490940c83c0a40c1060000741c01e141c441d034000c40d40060740742c00c010420303100c400301007460080c8a510143c8050303412240e0b100b207650964800210b807805500441c5500380840b0510840d0300c80d0281464025806040400100c2d10684d0510010041c2000104a03985d9541e4803405540045c0c80a80e460040014200a01144040b000d000c000b0711040e04071240e821a2207100d02c400c2c03141030b00010303800c00c0c040009415103014140f20b01d000d0300f0404003d50903100c0c1851a0358180440f010102062 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793806285 1250 793805035 793805041
    0x6040b040303150501020705060a030608030d05041e080d0f0219050306040f0e03070f080c07090c0f031e110708120906060d0b01151407061505061c020a110a1a 70
    0x354402143c09451060b0010312403507261400303100659104604070407c26517503080100b0500d0040c00200303001002d00318041420f052504004104c150b00c0403c028580301c1042240c00007a81881c182c41c42d00c21310810020b003000136401c1a0010f44180b56040007810038601c094458075802c44d01560040405890800000c81d081240800316403401044603c541d006201c2000000e1000b808500050310400a035410f0800030251680781071155042035541c280c440d0710700c1400d45c0e44140c000c8032410345c0385400c0c4561403c0102c145c54945c011244074107038588841c521064502154100c81150380d20011072a40d407040500182e0003000144c9680e1070f42c0c041d1202045041c501140080c4099800640c0c56049910f030001e11101c0e48101c100078001d22100b50b00d20045004298050300c0820702030038001c201d10329148014540190507401c503a110300014001181000807405100c0d0000310442401651101c00101c1528950701c8685035458500c903042c014420004880c41100c00703030403249000b08860f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793807535 1250 793806285 793806311
    0xd050a140c06011e030b011e0f060c02090708130609050313140306070f0503150a1203020109060605030105090c15040b160302011a1813051c08010b04050d080d060806040b040303 78
    0x64417072001030500460b4600521080080e2554110015200382c1c1741004959102240120880aa80400c1c0810003c01c0359900b50701740394024075402501d43c5007410032440c100c048412400014a005440076685a810700c003000f00400c00c480d400c91751050441c000d9681e0300f8a80d5071964500c040d5038004d005040100d04014040e480004405680e40c4801c1c1c02c43c0d032401d491540c0408940381e030580c0a03011500c0040c032212030004400c2ca0314000c2d2b0010914403800c0c105034055511540c4841c0c02a07240c1010045840403701e01100362160484d6000c2e038083c415080403c041c09550010220158001a0700f0540c0d400c05003090b148a100b50024460500780013010f111101d11950f01c0c5802264070210070004020080c1e2007680424101c900c00d04020032615940e18108240410001010390480c03034401207900a072266006143e0300802a203414108408258090040b0000504503000411100c03044200c50f0400005406ca035001c0712a00e01d400e01b0510b5842805a4007580482c0c60641007070005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793808785 1250 793807535 793807589
    0xa06050a120f030809030909040807020108280f140702031c0504150c03020c0d020106170304030c03030509060c16090c03050f061507080c010617030406020d050a140c0601 75
    0x101c2d040800b00002c2c1c21161070503600c1c50001403120344c0901040101c0340e6540c2d94420100c0c0528020f4040f9502c5003207520003d00703844c0c00a001c0c0f80001c0441615400c503080d11400c3c4c00c00e2050300340740102c0c480064502a1024040325110b000304680907408000000354000040d040150100c083c60000c0e00f4030b81c00510071035005450191215104c0d100d504e58200d07140c1c22440c651103052034010325180c1c1c8113403c00c0c00d0013815207401c40183d4507010100040c14019540e001c01c801c16101a40c58240fa507515a50743e0300d850701c00101400700100b2400e28660b40c900c00d4449202c00c8500340d4903078070035090409601582c03038060140e01c41d01d40074000301681e11a01c5000c2c4100c420043c20269a12810108422400c50146844000b0b40c00c02014000600e118040d03c0095801800400d840e030410040d890b00304100c400744a5142e005100070008145d0002e5071240103559420103594900c07555404035120f524481c0d80c0040410002002c1200e00c0b00050124101d640d9450842080ca241030890000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793810035 1250 793808785 793808819
    0x5092502210c210f0703050d0213090c02010e100c0216060302120c090f1207120c030506010501110601030318090614040f0216060f0b0a0e010e07030c3002030a06050a 73
    0x10000007403260b90000c903104401814172500900b0300301d0620841480801c140e90116803001c0400407051000c1003051418003d06d86054600c4c0024055a0400c140d426584c1c00321624210a10780c81d00117034004a4000c0c0105d50f04071035203200f500f40d5244c030359001501a40c4020040099030401e000092020341008041e41d2501c4401400210610550410840480d01e4200d0100306406412400144061842d0014440c1481141041c0c2c00034038500344207084c604142d12160601440d5070300002080404205070b41540d601d401d0024149040101610194102c1e80200c1200c52034460041100c103c0ca01135901c83c2d0f00200c90501103c1d80c2c5203e01d2040e0702540e00c402c0245101d20039281e0001e0300c01e410448035148460000900703080032100141040360241d00c0804c1c0720083d54014450704103102d0f012940880e150400f88030500e880301004000020102d02c1d21f0361305110b0003040000d90350250420071035009205082d0340301d040c0000c4840c010701551091520824142000040b85060a500f080c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793811285 1250 793810035 793810093
    0x3130c150806370602060604200705240a150302011e11150106080f0c03151f0f111209040b0607050d02070f05092502210c 54
    0x586882c0d00e410b0103503020319004014405410703c50009141c1d42d0700c15046800800c0c00f03404507241440e00f00064280200030380f0f42809141841c40d01480d02c4610703049095401c1211008503641c003143c2c02c205040001040d45a031504c0180d298880c80c0b40c0c110780003503001d04d0110104104040003241d0141c5010181d00c0300901240c0da800015a01548542660350070f8082e40c01c0080c660b4a210091038106030340180d46400329110039005011040d4080042c03903106000050300245c900746a0140320007070000525100004a0094201060f074490001c09180303400d007040d1000760907812072006801c44c1d822050410004010100a400030380000502c070800f1030850710000e03c0c04400c40b0500000d016012036458210700100860700005108000141000c038696014000403820409560100e00b555480140f0503010740c4107100000e20b041c103401c80981098002d092828540b198280d003032440d000c4444c55984800c4c80000c03006004500200202c015600c20f0728041140c10a84109000200113000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793812535 1250 793811285 793811297
    0x161b031a160e060307020708150412050301291605010c0e011d0f030307051218041b030b13020a05030a0b01092405070c080102070201030f020309031c090803130c15 72
    0x4241c3d08259000b15002503491060f01c540300d4407040d00c030b4070300315425619045034142003003004180b0180601d02e004015003480c206186500d03000f000b100116402d45680401c00c082c031100700f000c04400c0c0450780340c1070749220740f601c2405050810500805801e00c3c400c0103d110443c1803070032507120740c3c4c10340711240d8507a102c5440e04240fa0203000700da42003c800c1c0c603003503c420404030010071810880112008110304040f540c507815200300c03801d90980054454020b508100c21b002102c181c1d01d14068218000d4500080c001c212100014140e1241100501c1c10610002d1518021030307112004500c28403c0341c0080c00106060300c011200010079114211900559050720f200b60080082c13420408881c5150840c180070080c0c0b9912213400056200070803580d4001642421035070903004803040303000094011400c0d4507100000c00d0301c0303119074804101e001c1c1c20203d40701020001a0701c50044e8642080c0d21a0322441c044146d8000f45840b50f00545290350700c0c44d0001503a02c1c00c06204403a4202c290383e69 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793813785 1250 793812535 793812557
    0xc0606051c061802030a15140910140106140327060a1802180907030219050103110903070b0a050903010219020606120c0f030102041a030103020909030c0a0206091f0905011d06161b031a16 82
    0x20f210b00380c00151800c010084e013455001e400003007030390d042601d001c20003010b0002401c0c50103074202103603000c15104100300c03c1c002400c4007580e202d1910301a6602905d49c005980d075200e4000b01d00703042d05a00003c0d8802090301800694544142c0b0b1501543c44c281c0b4200200c4500c0e000101c4d10b40150a07000e40c1c503031701120017807040c0892100540b817148014100036080058200c0082c0c01e98102e14001d06070038000f030380c0301c00c0d4a5a04000c003d40045090707a51502d280842ca00c0241c17a24442802c0c00c1c001c5030a00c91000c0503407002d41c121001015050290500c1c4d500c0400f54010540c400c0c40168070600944000c01c0303c4e5800481107580f082e1041006240b010361f603030f09209203034100308030f020307404420300b4440d40450b04078001da03006030001c4d6030f034110180c3d05210000d066140403494541c8080b803158200304040c2c0350701017140c1c240e07201501d10168244140c5800c00200d00d0000d801d0a00d0402c2d00c81c004100303c41c1c040c240145080d240020070860b0b0740e800d80c00c0c00f140c40002090001031203030307da1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793815035 1250 793813785 793813817
    0x1b121c0302212202030a080c010b090a0e0a030f0203040f080625051c02211b070309031502040815060103061401080402010c0606051c061802030a15140910140106 71
    0x1490300943c406406d4130b0054100e0303100c9891a40128002e841d641c2d4442c0c0d166641032521104007544140506410090850065806503581c0c1d040321008081c4190300352070324000c40c003c109590042411110341007550361241d001c03c2c4c444406403480380c14030b03003103c40b200400350714040040e200603225551207080c42d0090000c074107081010300c2090302c0345a0810542ca081c12056000e0341070886440c1c00200c041c10405500702c203a0003101c40030070700a4170a2180030006680140d943c403c4980241c1c2e08000052840c00401c02842290f0050b00c440c8501c400c0056246a002c444c00e1140400343c0b4104256941c0d6044c10070b550001d104034600043e111000200198007481c2a6054180142c40000340030b40c0725008902c2e0260600201800c40490003d0034042040500400e03821101404101d0031403c5258042907850a038084010a00300000c80d80140b40070341544110540b8014020356182d0703007002c3c114280c45c4c004000c4203c502c2d906102c00d10040701e104030049412034200c1d0b5500c4000150b01c1c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793816285 1250 793815035 793815091
    0xe010c030810170a05070605160201030e01110a0c05070e0403050406030c030b03070b0d0501140306042d0f0614100501030b01020c101106091b121c030221 68
    0x340c0840b00058071408900c990341d10400d086070019040081101094a003095840c05c600b9030f108504214080020030919202c12850b900110350a09020811092041c0100e024100b03943c2c0c4680c1000c07003c40d2200f103d0780e00048047c41c641c0280c0503108120307249e07658007120320320031540580422820801001024400d6102451001c01450000b80261038000001d040155940c01108000b6005c655281e0130f003903d100e128010501d0002c0404140e102c00b02091303c5034030043c4060079041c00300d40310340c2903180071102f90305004030f44c403590302c400f10b0701460410b042030070001c0241d800901e04030680e0480c40c4001140d038003d2403082407007081c080c6000011001340039403204a60440c0034207134030100f043e107403400100d0b2940341c951640800c030340c1802d110300c1c23038003400074003044003644a504800300d15408107111607203084080d144544c6c85103603281610300d03103180f00129241c081180448401401c0d27055004d01103801d1503814444138115604400d081400301035411040c603a070351004980046091030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793817535 1250 793816285 793816291
    0x9011b030c020a0303032403051c11030a17060603090a020f06040801050c0304110319020402160b130302061617070311030c071b030b1303020c030109031805010e010c0308 75
    0x1c50401038a18965001c90b2400e40d40780e20407400700c0e880313001d05402050301d1040000d038140441d104008241c07031034079041d0342e5209c5030403070000c07056074000c2461001d8820b4100441d000c0714181100d0361286050001010500800400407403031210b030010035114646241200c0c0100c01050003402d8030810b42d02085030420441045651082d42040b0004880e40c00380500c038807828601501c103490345403c0c02c003150392888a850f0f07140300380c0000c03071074050340e00c0c6054402050540503100103031108862201904131040b9413002800244104040201040d407140c044841c10380300754242c07403580e21a142510800c420503402c0c1b0021582010b40c0201d81081207004950007401460041003030800619191140e61096a041d020340c000040c2040501c8817055040404000355010795514928584507410407036000344c44c1c680d441144404400c2490f01c200519142c1e444010000c0182004524000e03120000c00034102c00f41900c80d110024007503001d440340c001c01080603150b4041c01d07126503800700c031601001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793818785 1250 793817535 793817537
    0x10e1306050c130e09120301060504090203090a0803090102030a0b1906030f14070c05150c160201020a02090a060509060406120803040611040314100e19031b08120c09011b03 76
    0x10711440e074402e400f60401e400101581c0c14001a9814686580d60810070394103151101070310200010032200f03600c042200c0496500020040e140d0f1902600641031070120040a0000c29012091000341a01035008500419007501c4c2000103075005070610804161074601044034401d0b51104102840c0280c010301c40750650040005008051a91040023020041c3d50900016041e6071150742044400c2200c400d10f050318400c014018600020b600700b00d803007489280d50654880001000445e4000c10591040c2d45c0c1c02001c20784189003840111703004041520400e0300c290030580c042005401c151240c001501c0300910603c26000d80d13034541c4241c0358405401107a01c07a41e103800f010a08981740002d80f02452003412188203141060f00e05034602854100c0e000402c516090080d140c0c40800142e203e401101039880d09050f1506090942c2c10a002c0b5039408581c0a281790484104080c030300003809241d40320019050981c441500c1c0704c000b0700481400303e000c607520750443c10605840c03400784080280710b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793820035 1250 793818785 793818787
    0xb010909080909010303020705100302030f1303020a0c06030f0f05220512040e060406080c180a0b090108010921080a110f0a030b03240f2d040506010e1306050c 70
    0x251004146902c03c00d030320550040c0c100401c01c0c0902e18010800f680301e07050510b025411814590641152503002411300d840500384000183e081500a0116214841d0082903d020340c070b1342e80c1400780140496400000006150070042d801c03043c094481c0078040e4a0749241070300401c229011111880030070390310a440a1164412242c8004079400040010704081195440d4900f028000e0000ba0707007850f04030314225004003004452944030395900704141002040d200c1041e44907400034070018450ba404142c0c011001c0720002c036030780e0415008204228440c1d01c0071414403070300e8055038101d84840c2000030002984440462020301064008040035180300c403c051404c041c0c21f10080e415030000002c40003294a941a01d62980740c1440100721950048502401c8100c85250240c0721000080070012984010804524525064503042c0e2203450040c0c403000030300d294035040c1c00841d442160304842d02d202e000008a429084021260300450941324004003440c03940d030f12013002c1c0c4070003040104031801c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 793821285 1250 793820035 793820047
    0x30515060a08030a020a06060b0708090d030e030111041d0601050f0f040905010311040501090c0e0108040c030b0c030f0124050c0a1502120a0c0e1905130605030c0d0b01090908 77
    0x100f400280a04c9000e900101010003aa20740b400035940036034032400c0410024466400491892400c42c0d04800e8111510601d40e411132401740d6580d20400f482507010340c030b4941c84220070304010005005607900000c4012000725090030410f48500c040b540280010301c20f000c80103241c503a02010301300b4403070685605400c0c50b8658040d941155000d074025180d506a1a8038501c3e036080620500e40035111003c030603c83c8014000004d4540b4010415090410a0781800182485604d0602c0f9010b503a0103422009103041c031054544164000fa5281003a00f003688000089036072050403440c030303a00e4075020b4010002000c3c000640c2c0c81d4100f4007041580d405055007410010701c1040580b06015144480180c0f50862995980c1018100402e123140743c40c541070300c03810036542000040c031718008201da0300e814950f9100d00c484010845030784025040203d80b6a161846010741e008081510070507005c82d10b40007d480d081014000505a02402d4206008018007200c50243c111814150044c2e1a492801d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 793822535 1250 793821285 793821299
    0x4080408030d091b060f0e060409060806091c090611100509070614040b040306320f07021504060b030705060403110910030b060d060b0d0606150504030515060a 70
    0x15000c22000d80310039581c0c80d100b60410100e202c0381a01440c040480d01c04c424145070000d88415450002542444128064000d0f2a07841000702d60141c41c040e203040c0000c81e0313501401c96444c641950481c8040c0103405403401c2c0f8010014209e0310301c00060f0350308002c0d00d00d045000d03181641d40c203030b0a80ca03074000c041d107404c2199964082c0740e001d001c034040284945450490010072242c3d81140d00418103604000130002a00020b06440a0304d4203d400043c01d0308022802c0101c01c0711181820b0070600302d49001000601c909241e40303114403408501103010743e84040080761580300e520003001d01c98220b6400f29011503069441244150380150854800300c2d1200c001600c01d80090344100c0351220088580701117030402e05641500100900d024040490440d6155010b59000402c0350703015680d02c26820040c04031541100300e6400c07002e481000585100e0504a0182915001f00d40340a412020b8032070070b041c0300340111821240c00202500e949903944a0441c0808c0015000c0b640c0304000385d8000c1945 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 793823785 1250 793822535 793822537
    0x30a020622020319351819180203010e2a1201090b0907170a1503060507020d02030a020d1d030d0914100c0209061f0f0e030607170408040803 62
    0x1c130402d0815600c00b10307030724903200310003e101e07200080703406840458010854084031581c400240085c0343e171039100d03d985d1b0410006030000108103070780880c0a140310801c10318540a800240c8140c1640d00c4070312200c400c0340d14240d210a1180814a03844c01f0000f03006120040304100c0c0c40c646441c048245000340d0081030b00d01e80c011500d030480b08000301e80100200c00443c49401004401607032181700602d40f10310007808501101c0c0c1004c251400140010303038020b15035402012040340e4240064003031307a2079007000030051408680c9400035104a402090711070b4000801d0b03851000ca00d07030007400c83d40304071201200d80240c41c40a0841ca41800d6500c0c02d41660b0501808643c00800da9884100c0c0345030507001902241080c032468000e104c82119a00c01d154441c20002d50303141c040d10f12010984400c0c001c40c221403894100d46a60342c01c414060100c956016010b00c0d00002d40342d440160b030200c000105503c40d0002c1d44c0c01d1012520440c100c0e188110010b50065115015684503410659101103640c11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 793825035 1250 793823785 793823803
    0x3091e0503071502011a09010e040c0b0a0e04201602040f050a050619080d03020a020c03011a010201060504051e071704061d061b0c07030503040909030809030a0206220203 75
    0x8800034100c0303c00d039496824070500000c1820326041070000c04c8a500419a0300e507040c085c0074120f1781c2443c00581405080d142080c014410080800d0782c900c0100c070000c02d12168148500c0c861401c005400d05d07080c0404010102101006420b945404698441c0d1400c141e4042d01c12600151140049041002e85106d11845680d040394007182ca0710b411003c11030b209840d5000300107000c651080130f008403240082c0c80d00110b015410011381c1c900300c0e800180c0c584141030940a61560900d01c2650019244030410135130501d0a800904c040d5031224200030981d5012030b1150301c9601d814011080a1404103407a030307004017150800380e14003845d5192071004000b00b15802d503100340c1c03112403030140c40401036000e508004080c0c01a01460414405241c020010200d46040f485004500d46c2103118041c0003140085601004990761181c1d5840c0c0500902800b45003a000301c1c1451000610b020000700403034845003170550152801f039550410018840c52b440c07050b010481020b004080060f1010085105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 793826285 1250 793825035 793825049
    0xc10030b040f051005180c03040201030612121b17030c04030c03050a031403040807020915120f0705030316060507050712170709062f03130f0902040303091e050307 72
    0x6102e11301007981d040c81c0020340d409603016440305515280020350418890b600041d403819096525104c0307000403005020207402c1521030015564401c81000303484841d08101c101c45481d00d06140b0010307804290100b0111b40c019013078025080174030403070001c29401954031036500650281010313265201c10700400c1c400d40044940703a00c0204004141908a0000e403004103181d003010740f03035103004d640b1100103006050000f40200d420802140c80d0740d402141030b83c05100c020f4000c00c218280400b540781d41c0d404c0f1000483ea24040e2400c00304184c2000b004917202d00308442c041c906540a01e40c2d80100814005041e20304005050220320001341190390740700c2c0b4026040c1d803086010080c1c5161030a01c54405400d0505104042008105003034005401c080c81c0e010344020390f000709043c008481e41c01140400401002d0100103001ca107078013914083c0c1416114801d55400040e91900c6106080307100d01c3c00701402207a40e03d00104002280c181144540a03018616081429a29400f213440c184017230700042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 793827535 1250 793826285 793826291
    0x906140c03040b0c1204140d030c02040203070f03051b1c020d0f0b030105060406150c020102010b090f0f01150207050609180a29150f19050a0f020309030c10030b040f 73
    0x4a0b0f00020040d100c91120918002880c017498542178100316171610080c10700448d90641001d05040c000c0c10101a0550060720940d0b403480e00600050000380c458030071300c0c00719180c00007203001e17003000c440c040208031203070300c0b13001c1c5003c6603201080e00c40c0b001140c00e02c0c4000d4003001094006942405101c1614886540120344491403808260a43e40c4c000c00f200e00491600008011905840040c0318803c40c1505100920454600040740035101000c0e41030741005413142070000300b070b41d022001842080010010091345e40c80b07034600401000b684840b82d00580c82208103010518258005000e040c4009000007003c01c200140c1c100810070889503940250780e0340402506050744c031511031520080080310036442d0340003100010b43c1e107108041151001d10000c9444241c070b0048000302c810b140151480714a5030221600300600e283d01a80c044030000304240b484810060001003600c01820300103018209080151040c44000351086806808060300c0b038481c52003c1d00c0310710034040d01740f11500000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 793828785 1250 793827535 793827547
    0x503040602060a050f07020c0910030b010806100b0f09300105061003020f1801030212010902040302031537111806040302030d08060301090c0909020a080d0906140c03040b 75
    0x400320740e13000b40b0350101d00c90120200000c10354013143d600b0002c0d4089981e04441d440b14000e542114000e0f42000f880c0c42c24917400441c1c9000e001502030310800841c3c40c0c08401c0e03601ca0441c140d10b4022905215601c480620800550b032a1542c04482500e480c1f044011480d8100d05402402c039942d64444082655600184031044c01c086c2030000d01a41941070130340c900b00c0c244007200801d1085079400d001c08540d025030903809038829011a40c2c41d80c003100d00c030121561920b048000071341c45440700700d06c00d00c51500401c03103a1007460251403064644603011070011004c21140420140300bc0c800c0b40705203050044451240031188101c981c3c04800e5610300d9102e40c650314641d2009008203580d684100b90034001040140c0d40002c00500c1c41c901864285015201c10340464050003406100a281c40729442012850350441d40c02001c3c202e008540c16a1b580b6a074842c001d0321021148031440020310458000d02101c1c1c0242094980400c0141140d0b00e440071410441e811500b0036040488000000944 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 793830035 1250 793828785 793828801
    0x402070807060c0513060302030c070c030309090b15030402130b1906080f2a0405100e04050a05041e0206090405040c06121404020f011806051903050c090105070f050304060206 77
    0x900fa90484641c14010314041c2d0200c850000a0081d10429040680000014090101c82c005903021180d01c00c204030b24080c0c4a00e806017000000d1301506030360a1400c120b01e580c920b0088003581d021569103c01c14a95141c035000c5c846402c00e00345900c1300b80e9072542c52a51968484000b09001103030504511503000341013020003040c140000d0094506c00c4610310910901c8032280c4201d0341c5d400380c520035410300b06080307803800d10303540c09030760300c810390024031007603055503054118094a000704070454003003101b0f03075900800d1812500140d402800e045c0b52480d0385403040e40342c00384044c81ca5000400740c0c0d00b402804400030303040e180111011503042d0b2030490200081038209103840d0243c003800c0410b105007040031525008600006101901c50080001080440c0e409540c1e070407556102c40c80c42c030342025185c80c0040d05a611000038101d038602c0f584000450f8521070f10801303005032a00d050051409940e40011540c0e504021400c1d2801e28201044000086040008100401403a0003070811032801c202e03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 793831285 1250 793830035 793830041
    0x120a270e010603060504050c190210110a120e061f180e0f030c1b04091e110a05010c060b031f0e0105130210030c0311070c050a050307050604090911040207080706 71
    0x100186c090b5007040144030400301c011080d5203030012068030001154040400881c60200c101480c16085850020300c95110a103a100410540c5065118000500039080d0000c080b04ca03609003002c6150018000702e4140b030041c0c1c600171220060701040c0303201d0b00d8071031940180900305600610581c1e80d03035040380c0c100140b0a004180301c011044014601b4074a611220a449001d007144d1158980400900d0442941d0b841c1d00c810000b9030020240f203d0342c4002c10b04640d94214000c02541c130882840c900d4466490300041d91415241c3c180c2d0b500101d1112540c40c1000380405520395a41406000b070200245000000780c4815031400c0707400420314000d040404de0840f4005004e003005c00b8120204600544c40d07d80c0d1000c1040241d140014024803020405c134000d080c00005960900c03000541c050500c0038900921094403000c4851074807150381c0c0d901f01959100c20784100c54010324240010490223503a80e20611106004030100c00c0721070130300000101241d00c1141d080728100004200744003402003503c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 793832535 1250 793831285 793831289
    0x51815150d0206120405030d0c0305101a0406030209030a0b0f0f0901020702010c0f11040e030d3903020702060301060c140c0603181c05030403080702120a270e01060306 74
    0x1d00c2140d558459a0080740d500d00c1142a002560030a500c049010844200b049403861040441c04110740c0c2c0f4400002405028291010000801d100d000400c00e00d061000c004804c070034845240e460640fa105050740039400050509526005480c0b414011489030140b00c3d215401c1c0c0041071b4117070300d052400004000c0001e041c0c6125684184440c10060341c22a1907a000c2d00d07080045014100d032180b41c10700c0c43c4005025080c0e00309051419002071250004081d1110700e07880340c814462800c11a680130200708510030f00d040e204154144000724184000c079908502c00f45481c000d403a2a2560b004120700e540700703a2181d00043c4405980e1001c0c014a09042d20007514454054954154290700040d074500002d010140107584540c80d0601c0030f0010800c02581000c621031884404c3c08051024109400444040d408a0320700b00001fa0034138400710b540354140c4445003119060010492003140c18940a0425841c0400d0b20100d07400000030182d0110000c18043c05600d03890740c1001d6004050300c0542d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 793833785 1250 793832535 793832539
    0x50c1905090303120c0c0a06020d0e0609060c070215030c07110415030809030f010905030a020606100203031f090e0d031b0504050904020406170a170705060a05181515 73
    0x10301070031410356404822502030000360740050b42580c4485071200c00a1095119001c42031113894110000c1284a40280503580124003003000584034801426807660720032078111010742c10071400983d84004082c0641f08550001d03101d420900c03244400c42680d6441a100d0303081c145030100700701041016040e80c22850400c151000e02c28046032071103802c01e8075142e0000034030b000c42c00f1550302d80704c1e11f0411004a80c0306003040240040c5c561742c10001c0e11b0b6408105c9003001802030000042180c1001c201d02c666000180c3d00443c50f5a0f81c150b1665556010b8880305100c5094203040090704110740c0c00358a03801e110400143c8251102d6020207802c03a02c24100d94521036075003d14140d031080e044000c2d103080350000e8600560940c3d4920005009080740d030414520b0200c90f000601c1a02c0d400907181d400744c2d205000d59541c0e08001c46010500303007e80c0307000130039a501010000714200055000240c20809084076550180700750841607080c0902007000080e03546a4004103d4100c2407822402203107101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 793835035 1250 793833785 793833787
    0x5151c0b061815041409041b030b10080a030504090c1e2706120e07033c0f0204020a181701060f051503040309030f06060501080f091c12050c1905 64
    0x24051004e5528201707032079031600c40c0d00b115000406000c0011262042c1c41d01c448a03400486443c6e2505920b044010717155461007020788180401c10340c10018008400030340680b2035508080c40c20b40020042c06000b140081005403452418900e001c03989019480c0c030580d61035910180f152184044401c0040c0d550940d400c40290f03208100d0319400512407209510b5000001c10b9414500308514a040420ba1000700050400260f01030303440750350380c1500180c0d101c0c104c4601421500828064156a5498000d003000b86d24480d54001132078198010030745032b452400c18004c0c0c3d0701807142020042640303610040901031101c0358a103141400f1301c9a0806003400640d0b09140e40d003403001080300b00741e11340d0148010050010204050500482c1d004c0000c640c4101e00403140b0b002440d00c030002e0301c040c0c4036a0340070030b2074040031600444540c0d030410300c50901171000700082240b15248408061403501040d05000340d80a800204001ca0701903a4419510070301c10f079a4402505031022080b4814464107803c00074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 793836285 1250 793835035 793835039
    0x1d04060f06030b01060509031e06090d030b09221424090c010c0305130305161508040b103206040308071101050c01180c05151c0b06181504 61
    0x10390000084c1960b005281854844c0c65140100380360010f55030308019121004000381d2544003001aa051140c0b11100a40d0709071000030809809407440b0200c43e50344200301800140411061115120111202c5203800c1030102141c0c541e5903c2c056441081a0907070420a40c00060306e00907074101c0803403064500c0b0445203282013071015454860300360040d810046081006824940f156041c1c03010000c900800d01030080e640d190241d82c0310940129005071201c2a06e0000da0109000905440180340d40c0761020740355144c0d6200146200020800011850b28030310100d83d0400c400c03004040d101a02203020718143c205040000f004010711039440c403c410400040c000070301420256204e40b03a04c20703214440441e608005803000e02031941c00c0c0c1c58641ca27208680341c45200c4100c5000709140148149a4480d80301d20600c4000d00b5680201861000c00f0040795150301b285030429001c61000010002d209890303000007a950703900c11084501c410f02079010507040e620301040c11515483e40c000c680d0345054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 793837535 1250 793836285 793836293
    0x4061d0d11160905070c020316050102010f060b0714120409020403020f0a0302031c140a031a0301050c0715020915040603050c07120815090c12091b09101d04060f0603 73
    0x790710f0062294454965002c180c2c0b65024080402c4110f60040c1901c0589504040c0d0a080020390300c82c0c0341c019800c1c40c003180308503d468400c842c26030b003a03031112501d0054662a104944141500d41803940d100d0b080110115a10b00000b40018086a11015076250b146004100e007981c5410304061142c9040041000141c0d800541c4001e04003200c044103804040c80c07841908d22100c50000340c1c09046e0000341000305650b044d4458402041d240c01b00c1021600404141800c0311812101c4030003125080102d2004600d80004c4104100c0c2e00e0301e40540703840381c0c179408540030304e01860090909603000314051208a0301801107a91090790041105c3c01d10505484403200b0402000e5424280580c80c00820580e04801d040448101d8015090310154105082c4a44540d0302171541050301078001000b14160800205002e4406003c903c540c08a40c0c900400b00800c0043c05801d9a10804201200103515021442186002803650100d45298501360820006690507541b400001901d0168140005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 793838785 1250 793837535 793837573
    0x150c11060c031b0111030411043b10020c01230f041203091a07021203010f30050102071109060a18020f190f0819020304061d0d11 57
    0x14108504400c502100034a414010020f100c417014840c4800001c10050114200c0c80000c0100c09540c2000500154004404a844160311504911140c500205078681c00c1400d210110721011069815030b40104c940c05003240e2010f103031046603035114210105a0a40d040c0c0f8901032880388110f5043d40d01e403015021084410061000780303003864011050100510076400f0120969020052040c0b00403402c40c003644c0d00300d00b165500014407801c98140f01c00d94011064038101c8880700e8850f503540d410004110240100c08540d40303402105c441c1220800503c003132106980134015000169259900d0600441d801410150640600a4882407040c9030b1500488042104d2443d0b841c400306407101c01800010b441070030801c4586500209141611030f101a8420300d1400c1c00762110500900e481034283d89015045aa0380004a800d0b41040060b0b0700c0d9400030b6a0140c455400001d4020300315421301018400c88000c020580d00000f41c107056660052203414000b46440001c0c601409205560303405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 793840035 1250 793838785 793838797
    0x2060c0412060902100306031707020117060103140406061e0612050405120409050901050708040c140310020d0e0615030c01120f060308030403020d090609050d0309150c11060c03 78
    0x207290503400c0d040c0078400140d1120800e254014420310900510303020040c003425050000f658845122000481101c10b54005c8440a80c0e060711403400305250f4000003507100300000c0c03a0f0381c18152a4205040090380d05554640b1851082000184d03181c01c0000c0500e102440d2207280d0301a0108403010301c0f00c5034205448000180207035001080c0d0390b072a80b03003040c203103508003086a076440d502050124098125030421849494071078020811a50b5411007240d00880603a00a05204031402040c080049503501e250f440040140071901e59680c1070002c002268001d81d0140d545940c0c504050340d0481050003100d0308031191009030b4142e014101d0010352298100d5510f81c0c1440700581c4508800704180d000003509061100c400c000003903487c01c0111b8260b1003150708030010b00030204070b044860f00848440c0140c07200d0703946040c0c8481c14042400981030a5001c25024403100703080010305022110701a050b100c000383c0d91818040342500d00501c802c00c0c80ca140c40c0c880c40041c84200c2d03280780700100b6112 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 793841285 1250 793840035 793840049
    0x60603010b13150c0506090a0b061e0d030c1e0804140f03070806010614190c060f1508192604080106030503180d1109090309041a1002060c04 62
    0x1960354040c0c0541c05030b201072a40282c4102e516000c0d600d540980040e40d90400b580500151703030300e646d64000b02e0390725078104407402480c801c00207000c42d80c1400d100764030001010400c0c00c500496490f032b000003803441001c81800c1b4005544d00c00220200160700d815502d0880c811305648200c58900d9880009074000c5000340c500802c0c0c40c05950f00259240761b0811108036026068035141600d0b0030129486010901520001c81c149002213907207040c02e2805c4a450250040144115452102c001c594003800c0210654503107445440c003081030940c13440b60701042407c1c0b0161030700807854001d2039400c20740c040d803080d0607040c895140240881c030000e07088541e1000d0f1a80d80d00c00f1410021090741640616003007104251328001d0040308000f0700200801c201c000020b0b240c0b0300034102c43c0400031188101c0340b000302140880011201d81d4102030000e680c00200310001d881c280844040070604881089004e8001c4c05402e51168040c1d0804050402d602e01b030714030152480e86480741c42e284d402c1c440c51207a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 793842535 1250 793841285 793841287
    0x100305061e0f1903060c110d03020d0f050f04020f030c06031602070e0c090906102717030d0b090f010e0402010c081803010b1f121803050a0207050108060603010b 71
    0x5510703901c240c100a21071400820000000c504440f148100c82e01a00003207170041e1811000e1228940500400c00c04112060010501e400c808103044020f500084c034007500b030680714645041004554000c040c0320301d4003000103200c14603080c0100310203044a100d400780680c0001920141545071b28003102c5e0b00142c040d600c4010340d00b450344105e28180082e402150003146400900810040307502c01440c940404840820135500c5090400c4950024034103040080f4840d50b2482103580e03400401c44144600c40f0040b0002641d890400171025005c00d4000c0500e134100003a0340205015500ca81e402c03024058542d10002d00c3d000381442c140300c0040c040c2c683e0580744c110006046a200304490300e0340ea903100040c103449800550780161141c00c44403545110f542081c40341d083c01c0c1400c0d01d0321206544c2c02042c0f801481042d0009a5210082400c03607621292107080c103150851070a0782c0041414425654150f90344c40c0030380002d0a05c02e494000904100c090024400b0660300c92059906403003d22040f070b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 793843785 1250 793842535 793842589
    0x2041506120504150903021b0105040f090f090c0b040f090e06012106180201170405060a0b13050903040518070203040e0c0c060103080301080d083106051510030506 72
    0x342c4c03044601412000520390501e4240d0080550215180f65110411102c00350021140f1006590502560158000c0b00303212000800c00c58510360815424034241b0040080c40381403035200c841d4000c8803504080410800080c0c00c00c00000341d00040801003800d15001c101c826107507140140c48100c188280c0790040c2c0c0e175001b512034801420300b010001d103074011820080c4a02c02058407151080c4200241c2c04903440400d071030001d010500420740301f81c0e40100544101d595075149c1c40c3c003c1403240d14542c1c22001007085d0031234012451013214020040540211b40303c61610040011406207900510462440307001030003134044d00001a201540c080d145841410341e10000015030a00034030856034294403505000009000500000314141c0d41d950090341e1481c01c14000503101c41e0070a0f0f40c9042442101929a411005101d6441d09030300300c1244142501c03c81612070005880c0107440a42151020301c081081c24a8005004d42c00403000303050a1180b85030200025511099410781e040b407401e00790f024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 793845035 1250 793843785 793843793
    0xa150c050f0c010605010908010e0604060c0504030b04061b0216050d0f1505090d020c15030718150306050a05101218061a0a0e040f05030d020a0c02041506120504 71
    0x2a190014980070000762034010112415000c4c1c42d5a11a071408186045804107094506000302002c0c850310500411054a4555800c0d0040803070b250310204102c800c3c07001000180100f1a56401107008040100d15442903c0300c0300b413a41505141082550702c40a100808548007180d05011a0821120a45000c285051071140f5508041c001440709400c01581081248a07604c800d0240150741c3c01c41d40070060450301071b40c1d200c441030b075156404400c00300d00480300c1e1800c1005650000e45450140c1e81316000d40c8107020340381d400e034200320b00400c1c0c9500420001541072184030003d010482d5001042d41c50300300030420354a00d100d102000c0240801480d080011660001c41c030200c8042195100340a032810040001e240888000b041d000f55801807129524201641d1401c0d1100000318404603180c5948040f504802c509007120940070912490040b10000d2000c0e104201c61511122041002c0e48104012545241c5100820003090b080c18020103904c1080d0390300e0740702d00040004181d11036040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 793846285 1250 793845035 793845037
    0x15011d07020a0c24030b06090603150402030403081506070b010603021b1906060e0121030207031a2e1203180609080f01110a08070e12011a030a150c05 66
    0x40c020307102251079000040c90741c1c00010760018540d400e0040d00550300d8484412801d40307086c030490342d50100040c00003d20354034102004503080400c0601d100c0a003448000440c0c241d0704100d509a010a004000b00070300e03c94900503c41d2012001c1300d200e0304c1d16500350f0310b03608010010b0103440300301980404c0c03014440c4495003590a06540100c01c5951040312407080d03d20003902550210703455800c10000040c200c070f02d42c0c6441c2c141c1e0014200e6182d41040c0381555428045802d02c15000c511440c6c00020120b0723b000c015460a9032400200d1600740351003210361104c059540203d0100a070b20400354007240c003002c440314042d01c003040240400c3c44883d0900300d03002c0c181140b0003814010100d000244258011146d0303c200c50014050380c00075468140c41c0c908907495181302d030b502100204820b4505074407401c0c0c81d5511120a051118083e0300031400f0881090300c40311070071200d82d500d4407114100d000c2081c940415140843c02480ba45001d17035601404104410f003181241c2c0c1e19848040c1d410b0340194 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 793847535 1250 793846285 793846303
    0x901090515030f01051501090f06180f0608071b05060c09040204090e0106080c01021b15040b12091b0f10050f0c0106090f02160b04030e0d1415011d0702 67
    0x18100c2d88a80001603d40303000380303019103420f801c0343e4600060701400d50042c446030080358a0801e0100c0900d1a001080d514110b154540c41e241c2c6e080c502021518904110200c00a421660b85010702840d0035400a017490b05248020a88003d00503283c00000f0f02c0014143da010304000c01003600c0350001c801041c064003c0c1c1e000314600030b00b466030000788068154044000c0700c48031700071907410115050041e070310f50020500c000a01c02c82e0840385046400d00000e110411304000d40240c3c035142c1d071005001e03403d0700100e41011003490404140800034a0401207844515401d4003c2c00061a100e00000c006c69110b10302c2c18059502c24821801a17402442941c11091981c00c6d071b00e0b42e0783c910b80b00041c02098640517007032005103003400f2811140079a00c25100804981d8100f091001403a84603090304000c002e004908106648009150607141c50301380c0041140310f40c050940301c0c0541900c007410065409150f9000c0031400c1c00410601812402e01816419440603401d0a6254400201d045c42c1c150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 793848785 1250 793847535 793847539
    0xc011a0913030c150c08060a0f0b030a02071704090207060f02041d06040902100206070f0509061b0a1506030b130809210610080c0d11010f0c0c0311090f060901090515 73
    0x4401d05d00d00e00c40d04107014a00c581c8041722814603013074132400000d4000b0090b020b4142c02c42818400a55096142d42c0100a49405800c070801c4980e10241e6000c5541d1180e00541d10b4550041482010040b00d401a0782d00849070a06c19801d06042c03162401e8020071044810f0090202880403600c3c40d200c65122150f03580d00503100c54005e500c00c14000e035a80c81c00f5030701500054846503060541d00e10541c15101d401400601481c50040401c204900c1141404440001070040700d03448800144035418007414010406070110b5080d1135810f007400c10300f10080080410000d9a40d40000240380807003214802c1100326421580885111000000100b0240c83c42d840d611031358090165038400c0e1800002140d03046402c5500c0d600c03c003802e0098505039580024140450b80d00030038455070040164185680b014501450100c8040d164907400316202d51040c0c420515000d1210b0399410407203490345d406100500740000e2420035a001c9503112030140319020306595980040740301000301842d100c081d07101c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 793850035 1250 793848785 793848791
    0x6040f1b03020307080c03060a270c02060a06081209150d020c010b210705060c121303020405010b07081603050c060907050909070b0706020903120c011a0913030c15 72
    0x14500e405002544184c030f1071000f1820074000610074801c0f4100710303481200090300009200b45001402c4070152441e0729003881207890788071758103551103152060941c500d01540c000d140508091150104030750194000603080e4000400b07004400c0300c0501112901c80301030300c1c49260b4081031043c5500501843d915014602d00025061214901c1508400d8400d44211003000003251500c844500501c0c1c06400c82901e50026402085240340c60000b41c5421095241566010204082440c81070f5201c101091401810030f802031055040c98801c0501401165a00600d404510340b6a0340703041c02002500d043c5546440341c0360040500c24800c2c0c5212070503c804580e1103040603080f09445000d0b50080f90b00031064600056061301700080c55004076404446985d00d448555126603029502c100d468907014442c03907144495205440c1d00401e00c1c0c0c0d100301c0001410f40780d94a284042c0b0401609c0c038510511010b420f0005200d10104d00e44085589804d02c0719482c2214030301030950a581c3c1d0071060145103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 793851285 1250 793850035 793850081
    0x1060302040303080a140f06010e190806011d0103240f02030610080114240703020d030e010c050406210501080d110d05090d030203090d24110306040f 66
    0x28040d00a0020b0302e201340c84441081d940e80c9004811260810b150b41c40380d2421401142c00761141c3c9031402e401040c185008500048000007241c0c004402c602c0081003001c0100d001c00200030140042400741c9044008003001d8417507040712400360003040c00003902862294003c220309149042a00705001225003080c4041412002c006000750000c4405038001c0b440e50240c0300c02544a0045c40713050740c2002aa1041200002c4203000340034100b061441130f401c1b100e43c8503403281c4004002801c0c0680c42a4000c2489080060313008081c0c500c2c4011680e1540c0c14a202000c40340e80020589003600e1892426566100d546542281000014003244902c01d142ca80045900d60010644004031032803501c03041c0401101c486280da903010800702560004809104d1a292031406e801c2054200340244103c0b030030031001100044000d85296400c65001d2420306001d6051440c0e540710000c80e06c50020104044803134603c4100907480010641031040340d03181c1c44a408103019610943c0c414030b0b03001e102a0948 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 793852535 1250 793851285 793851287
    0x509030c0a4e0207030503041202030304080f010c0216050a360b010f080c0409051e09010b0a0611060a0b12070b070303060e040819052809171906090b0106 68
    0x220300d040b51101000328482d441110f0000a000341101d030b00c01c1c01075280514089400c260f4011400c0100c0c3e050104000001d0390b401c041103140402c034011000000d01440b000806842c0844500c0f04079080303040050200466951205c10300c0490386d0b141c031190742c0c41d13010901c0c10740d501c16509541c1070b203160a0129401c200c4541d030300540c240e02080c1c9804140401c80b440688410104540403690f00b02c08000511102e82c150f04005d80101032068041d0100c101c02c255440003503c1142c4119640e0f5480d50b10000710b01e091505031000340039504010246481170182c10b501c6180c000e20040c1400e44038500c0203400e0702d410440f146d0342e80b0000c056580c2c940c1c4500b100380040c0c0c48580243c000906003240480c820700d54000c1c05001c1c0d13511140c26440d00c0b4410001c0700c060001080500306000061001a034001c1024002c01000c210309100d1840b9a82c0445000c1c201512503042501d2412400c00760f02c00c9034000191440e420703031031600c03080400d100031b1800c0005031003441001030187c80c003480006174a03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 793853785 1250 793852535 793852643
    0xd17091f020a200609040e030c0d030e1018020111070b041701051513091a130c1e260307030503070f031404020603070c02150d0509030c0a 61
    0x641c4100d504038910071403180c0c98845214010f0340580d101c2d20400600500c0d00c1d00b644100c2e012103111054900b0044d0703600c140350801000d84592000f0a49402a182d0001c1051021100b03201d500d030b00402c074500d00f900500d031309440070b54802414410320074003001d0540e901b004094024589803825070b503101e4695162002070750040f40d041443c2d60821001c22010400c1c4030103c14240005020703a11400701d544000c401411203a0010340d00100c05052030700c4401140990103115440c1c880310241203145515202c0c1204001d58404141242c010300781c11001951341c460380040311105484105010032010b0715080b11601c00203814114400007038840201a00117003d144184400d0322000c0000110a1040d016202c588509042d03403884140000d0040c90080003654014000f4580501da900b501d5000c141001c1d110115402e18030710200301150f0610003070288079403064100e4083d505112410003150760301c0c40080720080102610050206103c4a4465019191241d5000d01001d9014a030110303028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 793855035 1250 793853785 793853803
    0x702030c030706020a08030c0d1118041104140307081009020913080406200106030605011e03050c2b030e0a060201020c0c10020f030f0a0e0d17091f02 66
    0x340116090034180e8900400c20004580c2603402514120ba02c5941d0b0603080d90000300084844882030004d00c6084a40344201e050a840040d24035a44103d601844400c07209001a254400c83c2044002c4403020f056a041c0c1d4101c0e0384114001d00d046480f8000a41482425005002284245c6000f00c9000300c403504002c4049000361040c20741901c0b101c3c0700403041e05440d81c015241b15805c020400229100c3c1c04010382074242e00648004034110020035600b56803455109a070840e44400040c001c0605e802803481c00101d206c1c400c03c0350a0310756994207807200e041e07400262240c40c0b404442926010f6240300c95009208000b00b24240e02d50524014003150100300c07455008519080b0003262640c0144215a00b00e88510001c012490f490300410482c4400700c528502180991211b250792010108007034607410704069541034441e1500803008090900c07600d405845108410410004204030900718441180c52096095480010780c2c04a104003800f500044800e120301c05040c11480c3d400316401030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 793856285 1250 793855035 793855039
    0x1803020d08030f10270e0303090106081612110406030b0405010c0f0507020303091e060a030b040f02040e1f030b0103030f080f061507020a0b1201090b030105010b1b120f0702 76
    0x91961544c0362148198013a500070704c0550241015200225103038855880300001c10740320301040001c6050045801d50308180e5695505a4403007005001400b000d121a211400342000c0d040a054a401c696090258200300081c004480c65010300d0541d498680042c1b0243d60003814000b514249460642c0c020034191050707100180050b890092824806c100700c6540e2078004000f182050814410080b1a0556110340c440c2002c041050301d24a40310240500040400d6450018640040100b0f01064412a40441c03068501c10003003405600d06008002e900840e240c00040442c101040500c0e800d00800d400292103031000d030000104040d031218514201c1e02d000d9445103d039459100070412503490030303100e0f2940460341e01c0c140d01c05980b080b40546542d5000810100c0059603401c20075106621200f00500c0006d8514014040ca42c1103000c2d0102c1941c041c1c0c020052076250801d1140940240c0da40d201c01d284100e00c58592400d0100400e1419075422403407581e88001d503049150695009001c100c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 793857535 1250 793856285 793856311
    0x40e03300907051e0d0b070c210c0308070c0602040e0123061606140414150c04050d0f0b10060909090b01060503041b0e010303120b010f1803020d0803 66
    0x900e48260205400302110805040c10241034a044d0f290686a54640101500280d07181d1504000c24010300100d4001e078401d80300c2180c0c02500d13050a44426411014401c0061101a2100301b0300354402c40d400e51140c1c240c5020813080c2c803903c100b110750f6811940051b0005d8000300380420400e0503d10058122007507100001040110001c02c024840b00c010342d41a8401424092a2100d61111610740040c6208410024a22958034810003000c03400b51000c0d44e295561000002e01c0e000d080184194101c008d01c02d20250385050010180140b2903401b4003030007105502982c1007003204607941c1c242a55800030162109180102401d50403070032a01c1140700042c80b9410002c0c0c510f500c3c1c8190200240c100030400e40607802c1040075100380d88080c00494034800400140040520b049142a001c1e100d101c011019039450b506004141d09088004025040d103040d07100c003032176a005002d0f81c07140300d0303070b41462005070410340d8415894030003d5201a4208107110840000c01c94106d0080d445003603650218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 793858785 1250 793857535 793857541
    0x90f0703081309050402031b13060e06030d05190c020d12021015030c0905060f032a0603070c110307080d020307020312043606080d02010507030b010905040e0330 71
    0x1003069403420340d001ba4058203c0c08020604699510a4100300d040103000f05c5044544c0c4101c02040722100d602641d401c0d0340032000d0008900d4107114101c0d191080d0303e0310b282000e141c118140316840407800e04a06110311340986804640719041d00080c5290045040035007074018050181d15404496900718025180c180c03a280f0099840c0c00c410141ca82181e00c84007001e040c5120000105005000654419202043c2128940d800c1140c040c403c003610344c480e4250319070344481c4000c0c0416402c071b00d40f14110910030401c01c0d99000c0480707001280c03c03009407542001404040303400c01c1e11a41025003203014a0440c4003001d0b030004001c207400b40c402e070100c41b01030b4600d0743c003060240500d006a403011000e0891001c25076200101c2c0042d014100100b4180d25191a502038003211100e501ca51940d4014a41d041080c07902031107003c1c3c0c010190708040c002e020780307440020108411070080905c110350b40c0b608085c070704070700700243c0f660f800241c00c3c56224600c02c04852101341512600d1004103510745400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 793860035 1250 793858785 793858799
    0x112230d0f0801081b0f0a0b040617040b04030f03090510060e090105010e1b090303030f07110105011809051c0c05100e030a0e010e2e0224090f07030813 67
    0x10b0078129050305010b025910481d9040c6080c07038051202656018001c1c540004a0f03958285080d002041040c2c04130307a4132454040f018200345649152070b10000c10b00c80030000450030b8040c00940c4181c1c03601c1c141c6904801e07140207a00403d943c070000f4105200341050782046e04001e038805400d1301c1c03950081c1452940c4103883c29099550900584c00701d900700c20302156801a10b10a03080080b02c141031840d08240117000842c0c80c540044a026044800e1401401700f0b06402202030707551008810b0003400f280d818486082207822100c143c4901c215900c0b500d017403d0000a00550a10190f4020f29010001c03a4040c010040300f10410301f65544d00400d40055a81e041610a510a6a80980145050110003882a1550b2078518a282c3c140640301c0c40803d910350701d49400f2400d0714070040f03692805610b8112aa18001c014090315025580301c088c00d004483d02d85030701d1105055500104100c05d59901c003d4034201b69111070820a14852041c01004014880003c2c2c95010400356020070ba00390340c1d0300c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 793861285 1250 793860035 793860047
    0x60102010b060f071202030d090c21050c010f0509040603060501080c1002060105011404181d030a0203030c0705010b12060f07030c12050403030e07080a020f0405040305030112230d0f 80
    0x2e0000303d1010000b480c001043c482030400783c0c1d1801c1c01941d0802180d40264401d0fa0800002250681480313801448803083d0030124040c032a4621880341000120b40d03035440c2d510000041d10f241800703c5089038060725482001101d0000001802c10700c20940d403840c00402412081c0034480b014080c20182c2d450701e04196400c103a078080170b42c3c020f122a034644001501c02c1207810030500d0322405c041001240710322504a003884041400d00002071801d440d40c000282c294110704540949030400c020307031708802c1e03400400d0303c1d0400c80c249259a651703451444c0c07480c010117100300c0d10f5410420076540c11a81142c0442d841d8441e00e5900401070f019611901d0032012a0016070b1b500d004920210b10400304600a6404a80d129120f800d0008180b210241c00310302e0001244d10500741540b001300410b086080c03050f203c04407a10250780a01450a040d5800307030113400f050040301c00e0004920300032800d001c089444220356143c13010004020b03010700b02000c2c1e101d060340664000410808002280c02c039215031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 793862535 1250 793861285 793861297
    0x405060d0c17121204031715090c0c0d0503010317090a0308030621031e09060405010f03180c0305060609090303060d03091e0e070f120b06160b060102010b06 69
    0x18900030000e0300b031020301030b16211011202c0009110382e103021004602c1e004000d0642410500c1c094002e031030b04d45002459000c451006c40000d010071800d108001f03d102d9071100743e0040c00c60310204981c0ea100001685030003001c034078001a1040310440c0c5d412542002c029816280a8006400200b450b40d460303034a948240c1286a0b001800f22400704081f90000010b9130308098010141c0c1e00000fa0480c0082801c91f0480c1e46811340c0e000011440c0310410f040424180381ca001c0b240e2a400c0c0a0303e42c001030000d000301d2050702d042c4030708400d8548a1510991007a0384e0b955042e200c3d64407628181c10061989895808100c80900c1100c1c0442c00d00d00d401c4100e5403088446038001d500d50340c2d82c0801e2140030190204d00302c0500c01c140713101007003407200741594a040d00214122000440d141c690724460700c21000e8240814084c010400f902c1e0f040d40070000b420407045c0e054002c02c3c0a902c1c800455010b200c0c40d62141d88040d20091010200402c251040e4080c0001b40e009000c130400340d50030042141b0401c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 793863785 1250 793862535 793862543
    0x2805070809090a0f0e1e190201140408060109020a0e03011503060b0f060c0d0e09040f032105040c060e0a2303011b03061a0306030d030e011b08060405060d 68
    0x240005503007807402c2c0d40c0c42503100c140c440001c01c03001801c0c500c08059407250380b06404203401c01038000c90412006550140016100d00041ca40082a01090048003900b40b0029040215010760394407650042022140100000301c04c030780310745d0382d2448120000d41280d011a0b00140720101c20300e8652405000344180030100520b408a01445c40e528440100180c03401c00e9001601401c0b0082903641e2500980480c0322508007030304440c0c86c0c0c4140101900200e005040c4190410f4080c4404140455040c1c0381241c2c2c9810b01f2003040251918610300c1c8bc50380b00c688501e490800041100f005002c40444045a42d130f42c840e2a00b10010100300000220745008080c40700c1c07000003940202d8156840c00c0c0e00c8040000d4000545500d205101d08a070301e010142800c08a915500104000d091102d81e00150b50100c256460441c1440400261106060303180401015290750100480e41c42c00c1d032014001500d945071401c80944c00704005009054201c40c41c61117103140500050580c2401c10b541ca9440f584 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 793865035 1250 793863785 793863787
    0xc0604151d0d0809091e01090b1305011502070905090c0607080408010213080705010c0210050d060e0a0f0501080a020f0607051002040b0316020a030203041a0c0328050708 75
    0x303814030460720005845506030301007202038000c91081c2c4841c1c924901250141140c5981d80d42684140b0134100f030007800041a2902c1c24050000b0315201d900507c0c1036500003031010034002c4250f000110283c8407809030070211481e1100004680b02c00c5200703011001c10350340031b031200d40c1c0d83c559941080340c40407101400d19800903d4902e8943c0741000080a02071b04c2100100c0c08d141d12941e400b8220380105041d400a412421700901840c841000220000c0c00240303088212107815a010480310702c0740e05640340502c0004150f1340910141900301a0262980e06000080c5242508034000032b07042c0b02d00206250b0f07103490000300380008003281c10310760650007070541400c4c080c882d0240076041c1c0c81040240c509004000d007210344864980005c1c0b000342101c4e105551282401022118030b07410a4005800b59130101c101400026004025101111546d00c0e4400303859050b204070200c40e200c1c030742da411440c0c000040d88001c94600108003e80302e03113200d8189001181c002d2020744152144030303000703042c500b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 793866285 1250 793865035 793865069
    0xd0e010b2e030204031407030213020901020a02010309140a03051305010806030703020d03021203010f090506030a0c03021302071a0901050105060403030824030d03060e0606130e04021c030c050c0604 87
    0x2082141100e61400c0314030b00103152945c5c0b519a00f5141420031400c501c2908905c000f042035281c02e20000000d40310b140c0045160440c544000f070343d02c412008000b07041c9603c4000000234400201c251030b100701d400070181e84581c80c0600e0004e1060344001003a88040c070049001060a5200c0c0c5001881180c018000304041c1c2e046800700100d141c030f05202102140310f05e00c00138200810420295000340074004c11418205e080c2b4820b10b040da00014107848c0603611640752480464032400c0004112501599050042d043e241c0c0030b40c000c0c2c0f003841d80c064071491400c128440d003084981c1c0301900c6156803d0080100b42d0302c91040110512903888045c000902410200c0c1c04030307031a43c00d4004039403c0108030807072484081000c00d0a06001d40301c000c01203503492000f00914003407081e0255003d00708640e10381c42c0080d8020031a00c001c507940601c00c11400f040c0300160441d02c075000c008c2c0107804082e4140c4034000301780c0307030080142916290072500703070095401c4000c450501d00d00741c07801d840b81c5034030184d8840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 793867535 1250 793866285 793866349
    0x503030f0f07120504050109061409370504182d020a09050414070f120809190311060a0518031c090806151807090b0d0e010b 55
    0x340208001004074482000b02c200020000002c41072200c61948495072103901c3c00c80090400d03030f0b980d4840001d0000c11305c0d8101301011550202e81d15840c048407044000c44490b04800c240144031400b003a040480d10040d08200c10307815000f80212001120140400d50210452404c841c411001c001c01320498031103428004240b09403c0000d841c1e40050340c4440b0745064000030201e0031150710a80c40d0940d2002480244900c806210072020318050080071524640784007a9003001551007800d08904003103000c0d0301082084801c4880c1800028804201d06220009150340344040384021550800882008609421b2800a44800c1d24440c3c0351a0b08081c440d007403d2203088100e0807a550325020b00c145030701c0c09022541c401e0340d040c00d455039101d64040c208001c0c14035228000d00a01e092854884031042c00c0e07a14107900185400c068220b115660301c5050055800117407940115155440100b4044000743c4c1d154170010340e054a0b20700900880f030300e86050140701032000305215542520282591592 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 793868785 1250 793867535 793867537
    0x7150c09050904080c19030206090105010e0612010b04050c1902010b15030c0c0a030513081903050c07030c0303031a0105070209150612180d080906160c080a0c03180503030f 76
    0xa40139096061510390b5031140107040040102c1c00451042071a000c1506141d0304104c120361050b00000204815410300c414602084070040c102d5105005004940316210020b4103c03891030315014105014501344000200c010360058074540c0190110b00c00816410b5105009030b07422110082c0c4a0301142107030110010080e44000c221a500f80300420003100044020081804907500030350380d940d00c400e565034011001c81322036840b07901650f10482d2290ba8100450084003c05035250030903030ba59149848045060011503400682820390081c00082811f0f0103422210301c0f0280e020041141c50410790054405001e06400a500041c40b50300150014421005281c441d04d80140803504040106591070340400048070101ca1441c1d242e0a18070543c14200102402441c590800c0c528610782140b036980e840000610464103402c051040700003080c0103981c91091b50340c12a105550350110b208001e131040300c3c8140708400003907008000c030364010402600300702510030046c061490030190741f40714511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 793870035 1250 793868785 793868791
    0x10e0316060221071701050a0e15030a0804030302071508041104090302010605040f0204050a060c050a0f151a01020f03090a060c170a080114100f051b01020f07150c090509 75
    0xc031940421000041e95a0f0329030b803610851059450702150110f211486840c010107034001d0b03020305624001844203907860400181c0c000320100d5440307544d407010000280342410455001e40b0006001402005241c0d01103910016507080d40322901026001c44022200d940c81143d01400541c105d91210441d807801c3c0d00100441c87c001d00c0080390036074580e4001070841d10032000110744140d00040402c02800d100040000a050303900704550051880d84519403100b100c04001000406d0416400c010080d0500d001140e40c480841d0030010310000f644884e104034140c0100b5400f5100700100e150340341100004840040b50007a1448a00c245006400e403003400c18020120784a046402c080f003030140840000d0100d4815544c0c2e080225498005032400e200200040d075070203009540d0040005941014000109003070710300d820340c4d65505114100c21043c00750f0b0341445103540000750461200070f208024280380c1d0300400f1117407240203241600303908071a01c05000d0300103e01c81c04820411481e01d030026681c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 793871285 1250 793870035 793870057
    0x18071203120b0402370c02090a020d110703180305210f0c0a1707081b0f0a0507180e07050f01020f010c0f1103030702060a2f040503010e03160602 64
    0xc2c242c1124800641130340c120748440140345c03038840400340c51103a44502101d2200b041c07840090400401040041501d10421000b0340104641d1010030680d100581c103c0300262001002044400000e400048041c0d1002c2d03030035000a10b03040d04400c0c3d000c10a81d1084200c9a2100040600090842e68444000c4801e40c00d40549401407102d00718a5401c030004003111050315018104502c15843c020000e00c805401c010700540301480f80303c001070381401c01c640d900030341c0729100321154410b414000d14100e0b903800912080e00030007500c84108030380000d89806030341b044050808841540c00c1103400b1240d6400d055025607010650030003d07400d00c8568842180818416903d610340400103c81c20f40d0202c04580000901d00c0819940c0726900019540c8250301c20409140b450402140003952004080e12901502d588d80c401882800480700c0403000d80540702c01c07040c40c0c50303600d04001d44098100f44200c50103542048140f000e0028048115020325140c541d2050703900810703403944402500021310f202 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 793872535 1250 793871285 793871291
    0x61828090215040905090a0c05010c020a03060f05220b040204050408070b010303050309060106030b01021b06042c1e07080903070b0c0d0c0503010602030d0e03070c030b1807120312 79
    0x200540c079a005a01030601502c91003e64481c035211aa80446400806040b1980c01445440c0009030381040b2807800c0b02e01c00d21305041c40488a0001400080c200c7e840144140c2c94104100840702c1240c00952243e5030b0000004900c01490039201d0781c0c010342c040001d1600c04104005001441c0543c0141d800c98002c08129082c0540c43d6112580800281c0007900401e034003004100c00e241007040395a02400a618083c0492780c0160001303940c80d290961001520302034074051000c0c585903001901d00400510900b4960a407420402d1480c0030720181307000d82401c10400c0029803e00e08533800c0340f0030b90542d40c0e0010883c1c0c2c980d5012074803c41d000c2c0003020a07000c208090030100c0d1090003000d028182009c2030707660703510308032484404440b01110010203224042c0010800c50b5004011f41e0a05080c0c900045082040300390160f0442c4982500100b214034512004800d200414500c6032186140c80c5201c030b002203070007622035600c141603c03410019910250340ea10000c5d204101b5194000751410b004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 793873785 1250 793872535 793872551
    0x5010e15040b0f0309061b0706050603120a0e18011a0d2901021c0228050709091b0b0703030209010e030609062409040807141005061828 60
    0x3192984080c0d596403141c6400300600c90001700500415801120601d5600c080740e4403039200070058010100e0140c80141e0300d0703000491035201401a40c1d400038240402c2541c40c0480781c4007500501129142070700640e14501d019990074601240b16050314900740850881008100c07070008680d01c0311081e00011030f104d15040341000801c018402c1e050300c002d0f1030106052181d100081c900000210030b0340802c2e090f071035906a06600030641d4600c01e4042d50059101d03120559090300000b501c1c100003070892241c10000298142c3d241c1c401403d0b07a204107142902c081740c03035005000108480c0203048442e8410440d03000064020740c002c0018440604104075170405c84c0d400203080140403210800690041c00070030610700c0900e1625450110340c26240003c01030020003040c0c801500410090600030006204018048419807000c2101e0059007103508002c034110701d0f031002d0103096803014011040c8080f0401691000381880e44942680c905130703000a100d481c0c44000c021041090b4000c06130741e41c0c0c12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 793875035 1250 793873785 793873799
    0x402060909071b060605100503040c0527012612041e030605131533030c0b04030507060c050604020409060e0106080c240f0a0e060c0a061505010e1504 66
    0xf605010502a801c00601729240609200303880c8106021341e410010204100000036039180304010039a401603a07000d440c0d080740b0030a0401286080d59441d000404100006607628922008211144298180030039402c40d441d8026a600000d07404900320303120900090001e184004510a40d404c01890210415030ba40c0c3c403020100e88080e20258410000c0c400303610305012000071062030045c200c181c20010807500038554007049001024602d444001c00c1c44d400410a00307000110061500000d5103070445039a41c1241219901ca2302c1b04440c1400384d1500015114064210802c1980d001005400a9074a0f40c0c00c0100410740b5060403103240b6500c884a041d244005d104440c0079243c00401040a80e0100c0100800850100030700440c6144c10200da00380760f00c00400f500c0076822140c01154951000d43c6d0140c2d40212410b089070f801c00340100c3d005455040000710b51400341d0080a0400240c0130728132120030f00d03031503238056640800d40200440c107660502c4480c0130204021524094109030312108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 793876285 1250 793875035 793875077
    0x1b01031d0109020f0a0b0f070510060e0103030e040207230a050105090a020f040203060120010b04140601033c1e090b0a180b13050d05040801060e040206090907 70
    0x20342080c80360b55601d050000c50400c44d0562601c10012a00c0c0c0013200e181c002c01600510414081203100540444d0a004002007040013a40c641c400240074007040e43c80c0c040104020400340320540004010401c0740d040ca04051003200c540c641c22640c10210b01e101c00c0c00450303680d01d90529642403486100d203008086802842451f014400c0c2c0000303025404854010090100310f90080148180d104100b8001030381e800842804901485480319030320382c0305515645004005543c450383e000782c1030280b28001d141d80b0b05922072141c03c090320304000308802407240462030308400c0381c40c0c4880c801c1140c814805451550007141811904c10012440c001e00c5107a060b903e02e103103040103c00c1c5444140900800060b062810307400300c2c2080040080074012810105c0b20ba180d032002400801c07171200030604800110010300c0550350003104440500d4418540140598402d1081004952078800e0201305ca0866160144c0103d0300189254203200d4401c0400001040180054051000365210034640460b404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 793877535 1250 793876285 793876331
    0x61a120601090b0105090306070e01110a241404030e03030417011d1501090b040b03030a0c210e042a030f050c0a05070f03120213050f0a081b0103 64
    0x44040d000300c1d45064180c60030750f140c0160726814000140520314041e00d0000d40c99034090107526194465940420040c0e40c1c810a042e4035168902680600a05000910300100800e24107403460b4090340b00103c1001c0122281041d41080800300c034000324021a1184544003924400281568a03083e502e0281c20864038181c3d8404405944400302d02190840400180fa90740300d0100c0503040a0000e8588000580014025101d00d165200e03180002ca8a07107a0100c10450005000c4076a24900107002400503204c0c207504071840c0d907070400d490342c0080340c4104680c540002c03500e6420044900e1001c01025155150502100c4680702ea140c0a500030202c1400c2e031504002d4030001103110401d0424403ea0b40000c0c1010410b0200b08031010b0701d540d1142c115040683c1101d0200312050003458112040c801c00038100304614004605d00754044404605c90301200c2d02200d42d003961950b002c041c400200c50303074032643c00c103600100d8507207071042c400300c207110345424052500080c48041d0841c2c2c6120080340c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 793878785 1250 793877535 793877569
    0x1f03030c050d0c03230d0507030b090c090f0d111c0b0903090f04090201360e0114060a030b21010b01030b0f060a0215010803071205030c0304061a 64
    0x110000360502078140894100d0781c09502d455a01d00303501ea103002d4801d50302455500c0d44000c016001000070800003050b40c410005210b010b02c0581001c1c40c0c01809001d074144064401d40104011503501e440d1401203850700c2030090113800c1d4401e510001c00058022002c01510b4400b103401884c5a10781d900e070360b500c18240103147e1000c520001d03400c0c403030038103280180588200d84c07003041300d50342d56550400c114500304002c5074086900034242c030040722070700b507500700c1e907415002e0801c5a0a000b81c251039130300f01900451403811620590701c1400b5600a50b080c0308120740c0c05921500744540c0c0c1003840050460640c10305001c520220800085443c00f00e28011812075034041500e84c2c44c02c00000c0c000e01c1d043d50401d18003400700b8055003001070f0b0180c00c0800c8261242c0d4001807001e007614001e0101102a1886110024056a6944c10603481e50311030941118017401804000510900031400e40380a1540032000e0780c21030b902c50355118002d0940c043d0424106034040c0c6850420b58910b05030401480315 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 793880035 1250 793878785 793878797
    0xc11060a091208010602070311030a06050a0b010e1e040b06070503040620060702070e09070e0c0409200906070f080d0b0909070305150c13060f080f010311091f0303 72
    0x1042c00d0050300602800180000c0102981c01002400d80c00903000050740e4000300405038100003040040c0c68440090701c000c02103400d200402c020284594440c0c0e50502080e02c520015622160811540b000390003000d04281105c1d070301180e0542000e600c44204a040500300620b402015200c103840c60700036a222000251142003180e09008207401c280702402041c80081000342481e403c065180c00040c000c0502401075000011107190701045170800074503008030301690509040031484460790141c061441c0d0341e0700380f045410384140d4030700c000d03c0700b40c1c0001c1600c2d04220668080241544c0034500a88100041c540090080b90034903004003400403c08030006041e020180034450140c00003082c3e24560b401212042012620109194132000081c160328841035440b4290300b0001c1c006c400070b400f10088144004903505400000c001c40942880e21040080da80e03010800300610401d000c01083c1681d100e1340b114103400d01400c6160000741622820800d520006402c6440350490f43c029000a46 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 793881285 1250 793880035 793880051
    0x40b030c031f05010804030c051e101119030f0219170702010b06070b1b0301061101060b21040501092103180203030405100507050a060c080a1e0c11060a 67
    0x1044404541c1e1048241c5190b41801d880c1c900040c0c54824014009010b22021842040c01c100e814480c1060303500014424100c442202612140e8580040610690140c646a1801d0400c100705080d166401200542d45040390301c4128201e0160410304a0301418030380900005111020500c92440d07062603698440030701d01c000300d0b6001420f0501406c00c2c019a450959483e105860b01d204540c41c0135008043c0d80c6180e241d40901140182c0703250610b88102d08048004240c85a10030003104070300e07044800a10219849251501403072044e0b0b4a8507030700e8103030480200b4004400003612a4084d020f8400082c408400340c40c1d05942002d5078141d06a1036580841ca80a495094441d0440700c440c3c82c0206000007403d41c0c0400d039644114003c152080d2900c011240d56a84984201c41c60741d42d01c0f1083d17400341125460001e0140c04c010491300c0110307060340009003c010180c401c40d03508003001c0f0080c0c400c0300e0603003410800900600703400700c04010217020100860b9000304060b45c01212000380c0015480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 793882535 1250 793881285 793881301
    0x90f2403181509030901050c030c01020307050304231e1005091e03121302030f030a020102120609131506031a1e0f01090f090f030e0a05060c060c0c03040b030c03 71
    0x126402c556440040c1d00e03042030144408000058540000080c206695950030540525107140141c20702d940103507000000700021554007801442c00b552203820009200680111980ea51138a44044003c03c0d40c009610a07182e190054000c40c1c2c1d80144006407044204641e1581040d0b43c1c0440e5903090320742c0b16080320880c040410030302000e40550355002e14108450721715940c0400e6805411707800803441c81f079200c50556806200c10428040c136141101d903950700d203e0300130f4080c1d00504101c0920101d42000911a414800c0c0401c3c40b922480100c02141c90696440c00c000d000d000074000c110b07581d12075000c40010008107581807600d0002038103040d145031005a15808801006003c41d80b00c0b1050b0500841050403603029041d11414a008100d40707074110300e40e10003060000c01c080c00c10182401c42406141e0001c804000b119410740346498519203803418002c1621405019200a42c400310000d4044170340040a0300c01c44070b6a100366407030540d40d9520f001075500207a0f614400c42c080042401901 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 793883785 1250 793882535 793882543
    0xf091f061b140c0a0906090c1d0d140703080301030510020f070b0601020309060f0a09090c0203071106040f030506070305060d0803150a1a040e0903090f240318 70
    0x4000c680303089054000000c25400344080d950100515040e45119030440d507030010b000103501190060702c0b2200603590b0704101c5001c2c0c101442181d549501d4104880350792441525041100c1038030126070660fa128080070310088104207901900e404801404034600b0000a1081200541c000c60303410340c4039415410721a06000c8421490400f2038030400c0002c41c0e00c80c1103010f8880d0349400a520000665503980141d085104000c075095003c0000942e60b5002d01c01c01d03026103d0007490342e651600c110f07201d144900850b00505280d1000d81c3c030a002e1310000030314442c0c010850140180c9000d041030340c0c030300c1c0003505103030190021100c0e070700030200b00280241d140c803444c0d034031074070469444004075411740310350f41d643c480a410750410700182001128030b0f45a0118070310040000f5044280440541d03804160310384c01c180244000c0107010350200340510710001c15143c2c8001c0041c1010280400c04041050740e814010a11800813402004071090480e00b4000d10b1185540302c0155201622101503e410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 793884892 1107 793883785 793883789
    0x30e060f0d06121514060d0c03060c0906080f040803070e032b2007140319030c0c0b120a050604060b040f170a03021002090f091f 57
    0x6410103070f06510410240a076aa802101c10504030700340a90342c1e6020000084185000411058a03013010600c0126201d02c00302444c141d40c0307079103100545403001511408210811002c00102d03070400780080d401034241c02204030f5071901c0d50b103182281c00090000802c112030000c525400d0344003044648164103409000800c00c50410f158210140c04c140c46183c001407803075031600725009440e0100310061100401500310700e0f00303142d40041c0d10003113868456490b00c64072265030804900800f00da1551745c083c2e9a100c403880c3c080c4c00d00c1900d50010381d000b164a503004010f46451204052280d5800c200101008143d0352192000034001d000d69402560012a0010b4001140008803020750101c070390781c444107042500c1815146446652445001c1d015800202e00d07800c0c418215401410f41c1c0740005c007818507201e01c003c00305420720012110740f44079484a02000854000440e2840c3c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 793705035 793884892 := by
  have h0 := BRFrame.cov_init 793705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 793705035 ≤ n) (h2 : n < 793884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
