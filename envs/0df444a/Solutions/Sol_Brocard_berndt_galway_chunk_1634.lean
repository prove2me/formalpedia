-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1634
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:58:19.698859+00:00
-- url     : https://prove2.me/submissions/5f74926b-ad91-46dd-94c9-af83a6a8e5fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 293705035 ≤ n < 293884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 293706285 1250 293705035 293705063
    0x2100306031410111204141e0601080d02210a0e0a030503090f1009121a01060c0c0506033304050a0902190305070e0c0f07060204170604110d 62
    0xb180080081040c084000d220341d1203801c4501065072910004ca40303071300100b0b000c51480410303a2090f01e42c0240d4001307003501d00c8241c0c040c40d443c5040c0b00380f01c100a10308100c1013030707213500d060114942e0b0503654a2410b80e048001d0044041c1d0391542c06040030b010348190321090312903245102e0060882d50010346040c1103c1c0f80840009802d0592640050300c031a007000440290710304d8114030f60b52180500703840341000e10b54211005009600c03d40310f10110300d500b203100a42000650761116851514000403401a0350b12100c008098200300402101d417003c41e05004940c0d440d028007503900c16075001100300032a12800ca040703001c0d1841c90702810b1001039800c03c0103015541d24090a48034402c0305000082074074a500402c9134540804040124080841e402400441e50115079002654106200c007040f030703140d640d003084242c031554020010308000800c44074200300c500d800403c1195140550094466412900540c88007070076500105a0110061038800c2c0e814030241020b60240121080e8203a22 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 293707535 1250 293706285 293706293
    0x60a0f0c020402210f06090a09050a08030106090f0906080601180e0d050d11030f0a0203040224090a060203030609070f0216030f0212030a0804030c020a0506070c0e01140d0210030603 80
    0x180240e0840f40c105540d0344440091362444603007081c1d20800c0080005154200ba10101c1d0001d07001418503419652518080703810f00508111414400e6030112005a1f2907a40d850b0061041040d0b0180340180b42280000203514422802807209031003510018180c80c4e4038145419140403211808951003139150300154000d040c05000c068941e040b680c8415981e41300446203c0304450120302344050116091051009441026404030383c4401300247c0169a030311180009000000c0034400020901a0342c5041806184e495020f4150740205803031a0138034503114001a030701c03800120391150700505c121340022241c1744503000d0000180c160f401650b8641c2c43e08903100ba1292400d42042e40d880000e000c80c4d4045083c560720b0304180c12400d401070b50074809200001482c0940c090009400c000c240035280741503559404a990080c2300040a0f5a99013101e4505840202140d1046401a0f001710000103150b00200804082da04002000311135801050790801641482820103413007007541e0717200044005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 293708785 1250 293707535 293707537
    0xa06140a0305042108070206010807031718060304030f08060604140d0305040b0f03060307080316060e03090a17150705121b0a020a0c080c010c0602030601021c03022106060a0f0c020402 81
    0x2600352580d17050a41d01d07040c880a484c020341a44120082d80c0728100030000314100160508014078486202c0c2d03032b1034082e0010803090150806511340d219800000748020107410150030006588651a01940c90342c4220810030030740114400d802c102c800c0401400c44600d0a03050b03404586110f400c100e41040c0d182c00381140150041c62022f01c00c24800000cac08840c0c80c0410201c00100400c000079032a25111000c1317010800f28100b0018a10364450700181c014450034415524a99400f820803c10300d5562009600001c3c611404801180204590100c0511944c01c5d44c5201790610b0325501e107044c02d0003548c2210b00b040140f00800703000442d101100d0000c1020001c0404008507230040840c180b2908010702c000e407a80d404602d02ea44401403103400d41e41c00130110301da40c5800c420016126500c01d80140d04111507401c40c0a40880010900b100198141c2d010b050401c441c08d90001010f16a003030480c2201c070064404c00d078040390520140c041c4500c01c850594485000345040245008203601103016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 293710035 1250 293708785 293708843
    0x180206180d0519030912050d0513090c0c1109061012061502060910140604110c01110c0d080618090a12080a1416050d14040b060a06140a030504 63
    0x2e105510982c03c814980d02c04902030143c8160700c2c0c402410502940c5a036954000706e54800d051040101302c540e006002c02c20540014201660184803985035158020b100d14081d590880b0601001c44000d4114108085024403805c1e01600c0c09508440e9800250b480c80311040d101200107407542ca0100d031301125010000344011b2a90000c000500300400b000c0e003481a0071142840151415200080000c4903110040c0c01590607200010407101c841d51900e96403144e18001e50156092603c000360300c3d81c040004040002c01c0701d0940380500c14103041151402000d5400682c41801a0341d01c6100c4240b00c044240c20494843c1183c4103580256140d031391a001586512020a41749010000c144c0040d00800c0c10004004810703a00e140340004c443c1265003000e05141040110202c1c0a940e4401140d010714100075031007003004114a400d140c144040751003280c1c030700d024800c0900001034050049c814000305141d1001c010b818815214021401050010025200d0040300c114111103040c048441c034107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 293711285 1250 293710035 293710063
    0xe0d1104020c01141503060708011206022704270b090708070b130608040f2a080307020301061d0a0b01050913020703030e060712050a020702060c03070303180206180d05 74
    0x4060310341890702d4103105c0449080640660064020042416170140949040d04c0d05505030820004403410198002e000e181207010410a402d0415002d0703200700700204420600403603090101020f0304495500c143e40d45d1031081403900c1e884200301c00041e01c2d07000701580300042504540e0351640d54000706d8603008441d4403101c081400024500c000c0c003208410300026203a01d04000e50541402ea44100302e45001000c090091440c440d1184030714407880c000d440c3c24003c01003880c0c81d259204d100c0c194881d031104200304e10940c80d041d400900302481615034a910401c101d0310911a41c2c1c0d03091544003400407200000d0402604018148031030b80e0f8203100200720710310840c00588850079444d018003100c5103590001c2040d0302150400864a5100c414034032110001c0c0b03008609070310348441180c064082e40500940c00200070410202590f8008050081c2c0c1c0d009640a010b48000906c241005500f40d000c041d411000400651b0440d12051071914081400601464102c03512510317542d040c5111245142 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 293712535 1250 293711285 293711321
    0xd090807060f0203040804060f1e050c06010e0106210902060406030b030c1516060b0607140d14120618040503040512031204060b0a180203070305070e0d1104020c01 72
    0x102444090b114490400c85010300442c61420241c03030710501400380d8401d02c8108400f04002208c031510030181c0c00e03540c0302d1502c0c44400c3c080d0072600c050320b0384d000907210400e90b01c80c510000402000c50030340c00303040381c0d41c5403910f1446208421100e0b1402092044220000d9142c1c0900c20058440d04010310003040290b0700012a103400508140c100000380c00c0d107522540c07080c1c281b140f410740a48101d5078840a56000380e103550440d0f180c00030107405e8422055511180200e11031003806010400d404070300740d10320141e9400c28030348030003035403201c501c40b50066040106001c50a004c40c001e216968100500821404010074849906102c10310110b504841c035410200307082015090903100b0566031a2010055418141c4d10140b008168500400146c2003548801e1650300c1a1100700075a40542504889515071500d8401c2d014045e504c00e0f034042000915001c00110803d201e00d014240c966001030007a01e40a121b61038016038a008248010390040d030810840b161000309110b00a06d280e5100020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 293713785 1250 293712535 293712547
    0x21060301240b071b080a38180118030e030d020c011d190e15010e0f0409050f0a030e060c1507030b0d05070807091b12151e05030f0d030e030d0908 64
    0x40350b98203120301c0c1c41f10640307005071030040003498040900108000701e1108000040d80d80c1d940110a8440000f00400e81e54030303201d020100091002100c00d0614001c2e21741100d641c19000c10b05075500c0c0321441040040e080b8591002c15584030311440c2c60ba500c24120510003021304100051040b11070341c20741c6071080c03015281c1004000191032406600850080074034507801144d9001801d0803c1c0002c049220b07a914401c054034a940e06c0c0d00640c10a03402400703d90013482582816550b0310740b040000d9012a0802011040c0c9103440e100f10740403026848044c02114031210f80440c0d0300300300908501c2c10b00d511160128a503849411b401c0c0384140c0a0300003054405d10b01826281440d4441d00a0790455052003040e40100007003d2051134000c00e03030300d4221485210500c0160003000410b550300407030248018001140c082417408000021420300317413003507100d40c1c400401d6640d40c9030320310030005030700080b245903e5103001e94800050b00c25114143c2c3e02d0800d143d42550110b94444400311600380010802d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 293715035 1250 293713785 293713793
    0x90a12110d0203160602220314060609071202071406131b0803040512030d051914060a12020a0302060a05030906130c0b0a030221060301240b071b080a 66
    0x41c01e403a0308590024520713040708400100c802c20745084001c0e0421341c00041940c419900303000840c8100c02d180c02076580c1c040d10780c5072480401e00a41e04d2281c140c82420041004c0b403618001160050000351160342c001c2030342c2403903080039402144054482c0300310496030320b2440506000c0e02e4030501c8c10824841c0f09040c1d5107084406c03041c100350b400d915051600350034050700b0400802c450540310100c030030400c0d000c400b4801c1031461080d980702610884c14402400745c0c05100440008200000c0c031b50900406043c02ca0f0320101c01c104950340c07980990700400400c0440d01508148601e0350001e08030110b160b8894020034803030b50007007034071100094000040292003101840f506401c54500504640292159210052111a00e0250a4072000c001070201d40c80e034006d038111640080d00081300215070390003142602e041030044401c1d40c0694204844c1c0d40a4040c06805820f00e909021210812282031603000c045079000440210703001030b0741a10a589640c034580c141001000e059004000c0c03a1000c0c40c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 293716285 1250 293715035 293715043
    0x30f280b130504050304030308190c1214130b0703020d021201030b060d0302070b0d0e0a030201060f0506130306020703111902010e0111060619210615060503010e090a1211 75
    0x80071400038508000e1000203207002c000c5a040765014034004e038070b03922440100e000c0300158001c003a102074a400c04c10050560000810707d0038894042040080c0c003802405c00d000400304aa040e5480c8080400080016451007a690740020a6140040c1040104821003049a1001c0341014900d14068010410031408007007080c1c0c400415100304c480000c16943c0a0341e0b41d5054020100c5914000c158a00d0440c40c603440910700341c0c000c1c4115010b040d010b04000e4020045030062070b0741e046164101203000d061440c03c64404824001080f600c02c1d00d1a1217020080d00040c404a04220020114610b103481c100b081d1501d000a606100300108905d10000d0300070300c41d10340d005040c07040c980e040d00c211290200b542ca900407020b90385d04646d03c01c601540d060140c1207801c10088403000c4402d64038442c0044411a118501c070f10b20802450354641d881c0c0e9084020b5200b41d20015900f00014025100c0041c111500000d98000300e46803180c1c103540340348443e0303410705102c1d0000e1b0905030207180380c14ec100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 293717535 1250 293716285 293716309
    0x10c021302040f1e14091305120313060f050c090906240d0b0306040201050921030a0504080105150604050d0305040305030d02121e060f060f13050112020f030f280b 72
    0x2541005007400b68004940b10030801408461410900c04e951028031a0520201c0c064160455803180eaa150240d00c400306911103c00942e50cc0340f41c514000c081e03103000e1040314016401254180d0500701070b0b40030040c0c0c441005081301d4102e450707a80104103200c85000c140c0340a94020790003130f8542c550600c1c45002c4880e42d28580c1d100364014810b0002503600f0400715150300105481d259506070305003145038004c08207000c99074080d120014000c200c4035031020290003942d41c1c0d074009103d280c4480c4a804d9490f946010020b0b4486010401008545003c5000e0007005110b41452400d0966176122141586c00004114a0f9190000b4021444008013452030b64451641030f02441802d802c001100948000104502d000e441c1f2880394a000342d03240c0013600d8100802030801c80d604c1c0c040d140c01c1f401005041c070442d03000c81c94005442569112a0003a0703511551828022415695021012607a100c006440e221540070a03c84d0035041042c0c3d950031040c850001c0c20042100d0b40110140050b40c00c0725 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 293718785 1250 293717535 293717549
    0xa140a1d06071e170c07020d0b180c06090a140a0f0b1309140103021c1509050706050c0303060405040303090b1609080304030302060f090f15040c060509010c021302040f1e 75
    0x1a00c00260300110514135030003003000710840361580e08600c00b003a081d140324000034000d01d240d80100107581fa03900c4111b51000c0d90010527114035250500501c5510702a9a584541c0120083c20603c03954040041107007166500502e400012555201010201e8280307402004840b00002106038420203040f2504005101d4004c0400042c0b5407024100c0381c600041c00024410303903181c2c4e48603898406c0000d04200d95500141c1d115100d2030540641c01c002d00c0782000c119410300404000049260195040e01d0404d03500034080c600d5a070380c103001c00005000080045052607510316000e400b1600d04181f00388112503030341c03102040c080542c001234031540d507590001c4801c0d8410002440001da0105401d904a0348411003103446403294004281069211640040644181e240c0380c680403140710b00c600d020f20b015076085540641c0312642122284502499640803d9580c030847c0300509089240c40d50001c0113050041c200f0380c56540b0586070500c10f600005120003003526040611002e01080b41c000c0100e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293720035 1250 293718785 293718797
    0x11203030b090c070b0405012301090b0324040503040b0d1a0307060203070308060a0509040503030106080609060d0b1801020307020f010b0a031707080412120201050a140a1d06071e 79
    0xf40c0140c02e028440d540d002008190504081400c1001c00d4022003c605440c030108076a602442102d00740500342440b40b60b0505040c02000091810080360315081000c80c0400b07880030001000c2200c1d044d240203003045480c1d11003003100280043c01031300036003082440304502190301c035030328044001504074050740e1900c66000100304014658000049542c010341c075003040120b96031440005002d00d080d50784160381081a6000f00010064048000e505075a410744865105480c0c0000b403200c42c0804131030b1280c12001036114100440c180d81e102541c4500d5003440c07180303180c088000141c00c1e41c1040e510700025030700400d599090004203006803070a8840548415480d13500d5a1580c0c404a41082e2081c041c00d0300016a4001b4080c0303c17011100a016010411288110f01d4a809001e201c11880d8010040d440e00d404502c8171516400b038440714803607100d15819552142c0c12100c0041104003175480d00404582d90ba890450303004e0040314030403001c41d00c45200e641d408036007900440c05030101e04420001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293721285 1250 293720035 293720041
    0x30d090b0f2505090409081e1908040609020a150e040908090f010c1a1021151508030a030c0207290c030d06030606060e06191403011203030b09 63
    0x40e0402251000d2800c10002c20b948051a0b541501c07103109482c40130b50805d06001016060241200042801c0030070425140d0004070341103c2010303240103114030500148103200300d003103d0300d1107845940d401c031340240300014651400740c5c0000d2803400700d039201c8007804030007842e64003210782c2100c4690803a001c252418490b1302e21960f201080ca100f1a036038184038451300340c1d0701c070910392090400085843d800140d050040041d00c84218440c04110351040c3c442080441c0450401d4008007001135801c90010545103030360340340c2d80d03280b10342100328500406950750b960420300d81042000e1450040031504040c65403499a0b5000034159400c101ca8038043d0740c0701444c200031311042d8040410304030400160780b000300001450554441d106005503500940300105080304c0c40205e5501003c1180e03c50700c0200103980e0f46079420346018000c90909980000240910036070404131403009201046030b46040160313200c10508046c0150000e801c241c00a0114140302001c241e00f41c8911300d00000200c0b00424145 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293722535 1250 293721285 293721301
    0x605040c091203050c0a0501200c0a0b060f0a12140a030c080306130614280e06030a05010603051606030501050a0b0c0c0301020a0f090902040b071b08030d090b0f 71
    0x3140d440740d0307100e07006005084024144210145c0f034101203440d094400c9240d41c0d0800c240608400e080b28a028004e009050080c8500c50b01210207004069010302030003000b90b12040214400100305542100c030301103260646585110b075680c050041081111042c098504160b001301c0d0034080414045d50002c1e80000109030440c01201c2c10030f07404000c1950f42d81e41d40b004105411100e203047d002c0281020004201f490030000550f2420800740c4188500c0c0d42c4e260b036440c00700461080544425100f000050240104100319154001000307000c5070a400c545035641800c445070381d441602d954015030112040e4203a8181020000c2c1241e180c14030155041c580000d04101ca54400d2032046030b80011004003840050110098400e0000c2c003c544030345030340b003003d4a140031105c1c0010002c0c104a43c04a8140784501c20307603050344c40002ca00360a088441da680c000c2c0f194500c00301031410514a0001901d42c4040000f8095807a000741f01256038107840c9010450300718040c20310b1007104200c0c01007086071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293723785 1250 293722535 293722547
    0x60d27020a031203110d1b02060712020d06150206010527010506030405250906060201020c03041e0b130e07110a120c021c110604031e02012c03010605040c 68
    0xb40b034200d4104588060004410341c0140a01400d440000b48007040c4030420111503030000b91101c024003203503d00669076600c1243c46031012941013021800a03032070324140ba00e490340503003a8141080d00002c0ca01d900c4485003e101003c00c0c0280740140c2c03181e40107000608000f801c40f10b080700d2054908903448210019218514414000d45002d0180480000d040c030104000c89900700c1d02d08282030383c8004074042071751a102c2c101d02410103007500708200062280c1c814406c41d0000581034000d182424202070308100700500a030300c04002904401e00100e50114007000509030b8200e0055042d041500d000300220070800010410b00c180b2074580400703d00c880300898a00c0200e580041e50030485030000006603144020b41c080a5080481e030004050403c8107250300520b1280218242000d02e00c13880100720311407140b4080100340281c0d0f505140219080780103510344071072050401c00da9140c004841080b85c80c2280035000390300c40004030b4031400c9040c2071040201400713003a01d05119100c9800780103020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293725035 1250 293723785 293723789
    0x7080901050a1e0e040510080705240408030703090509070203030601080a0f0c080a0b1f05031009090503090a3213180311071203030c020c060d27020a 66
    0x41c4030002820b40701d01032255061100010f000c00361400300c103151a80040003c104c0c40040f5024034982000b061907615150601c000300c0d0b49081c000c2100303074101001d000866003c80030240c9400d49052181d20310503d0040904050042000103503210004c0c3c2c03c3c020590b80d1300e070780118058103410007400601c542c040103c0341d010b04282043e0209486281480e0300400c1280302c40408545400d406580742d0b980104024094010340000f800207600110411104a404012090500410301c01b4800c0c0075008101560f0300940d1044d03d5005540d0781c81c0e03000d01f40e4074100c0c003c81e00c1c0d03000018200e1851901045010143c00240080090319410030040c0d0b8a01600c011800d80640840d00b80005a684947c24040c001c02405020f2000c010380000e581a14401020700b1804115045400141240000b56103c2100d00c460310b210700c00da1694401b034008001340e01505045001e120790084481c0c036845c006107804242c60100040203001242c107001c0440540440c10204611850741d080540d481c1580901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293726285 1250 293725035 293725037
    0xf040c090c0503060d2103090b091504030c0804120c060815010212090d0c061106131205090409120504140f030c01032706020d060e0f01090e0a0501090605011a07080901 74
    0x110317102420703d240080f060922100224400303400302410700d0342c140c2181030454410000c4c29941e458180011f034561062201507607800550000050129100301d996400f41401740300a01d1905031940111000d110080d402034640708030134641040207541c07050300c40d60720007404090f030a000e103c3d24000070f4444106010707400c100000402c080c07200ea5100104e490400341c0c800004bc00d041d9a40300060805504140e401c0420700544002400503500054442c1149500002c2102144030303821041c0e0303564003d82020368205a60f0a03e036400100d288850940070b0250b51182600c1d5868040030368031207000c0307840840c05501c80740c46803000c0e5100015061004a030908003c00c3e40300c10b4940104440000031900c06d02034100071400024840c050307004000840c08203000340302d0180c65401c1a2001e00b81610b00c44000c9510000400040c00e42c0d0340300364108400da1064804100d2240c0300da600b507490b140000c1d82c20301c1c0e82e84010040000d8a420303148a01d400703090300504111203502c0b441028068510304078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293727535 1250 293726285 293726299
    0x207050108070201060905090109020f01110706142a0105010f0e0a050a0e07060e0301060e0f0a0b0a08030708090427032703080a030605121b12060f040c090c050306 72
    0x10001c9000f90170800141c50103103010031580c40d2441100e400b8088407142070707005000b2044aa0390952007003000c800707000440302c01403440b40c0c40e01c5012039011440b20303140040c040041c40b600c0e10300c641c1c8460780c2c540d4030f4448086d0303603a1000c400380290850798107078880b040784005001b00b0085002e8278526260300c2042c030000040c2c907555021410018081908490055014080b404a00c840e0440181c10b912001600200106a220401110350002c00d84410010042c00800203040490070340211011a1000e007011030744982c3c400030075185801c414801c40d01d0000108071a1150b00340380c820280e440d051107513604030480018031900298482088043c1c00c0000303442e49840402c500c24500000700c0020b15030142001d9490910612035000a00000d0003c0c3c14004000313591b10300100500c00a5420501030a000e5903000c404250600c903606801c0d4118013084804109501c041c00030700d02ca4400ca030241c42e0913180c0f500e480f01c04900e00d504504440d529140c00010341c203a224064076807205040c0d0b10b103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293728785 1250 293727535 293727541
    0x90a2c060406030c08061009060e13050a0204020301060e152107030b090f010311030601050a1806120f050f01111e0903070f0906060c0f0609020607120201051608070207050108 77
    0x3081c064016500b000d0f02554040500090074080003030b03132071f00c03030540014040003e03511600c0c44130581d0598414600c440d02072402050040c001d03140e04044507807185040b5002200c8690200d820782e0002d038041000300301b0031240500c150500085c282103d211501c41603281030f108840b843c80d41691031700248441c50300880000d0b000c500a40c03009210340390040283c51103280400c00c2c2c4c2d0800209010484080010740c4034400e4038200007038011f0603500020481d042082c1000ca0204802c40101d041d90340300c94503600c0028615801045464030140162007409030309150f400c109191074540300c0e0405981e894a1503950140c241003065601d08503000c618800c0003107080c0d20008041c013502c0d58540d45805140701c00112600320544017412104540014424180e4504064801110a00010301100071504101d00010b40c036500c2206550300c0203040904002054550811005004030760b00090b0391368000340b210b480c4594880d90385182d010329101c1c21030300d80700c0c0000b52184028401d06051120913408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293730035 1250 293728785 293728789
    0xd02071707030b130803090d1d01210f091b08030a1202090f030d02070302030f030f0f0c01090f030e040b04020405030c220f060f0e0403090e040305070803040503090a2c06 75
    0x1800d13255040941141c403030503ea04d6840e01c400000514101007040501e0080ca0041c0310420795000e100140c44445007180480d401c10207681d81400c09076a4140e540c00b425956014900c501c14907240242c600158140c80c2804410f4618001d400056150b48184240341480d540044034000310100710340050784070440e11010403007221401d004582e044c01038a4030001c2d119800110001164022001c4421460b80d42e21115141d125444070015101d00401009001518400003000ca5131811000043c0da003495880f92000e00d0100081200081c0c0305d443c1304681460f09019255640c0d03401c407004c5180c249030600007a66031008081c1c0a01a03007000321031b85115401c80800c2c2c1c49001829105000000c5407001881c000c040c0d0307010b000303032080a01d10b0200396404840001c078801c50307041e1503c0001d20f00300040b8a2103810024070131000c000e802c00070440001c88120165004034071840085071200620010000c04014903009001c480303141040c0e0102c690b0b10240d0a0040c0001c41030130240350786070440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293731285 1250 293730035 293730061
    0x3150103060e2d0c180d050d020f0f0316110d0c17011b09031e020a1701051302061903150609080f01091113020c010c020d02071707030b 60
    0x4000056101004104283d00d000c0d1480d11541402a030040d10108200c07500b94925048140d0f14102c445605100100c0c0c0220308854400c540c49008200b40c0d1090030941d2201d16101c1c600c903101c00160040524120300e03540420100c0140f41494000d1170030f214000b0b6030203005a2480340d019000d80c2c4840314031403442d220178101c1088075070060b4400f00410780b03454802125405a612080040d07203404116080c0362034482011a03280f001d503498030440380c07860b142d681201760001454a01e001d1440e050000680da1944c0c00001410500380d0403581c10805803000d402c443c3d00400d04020514490b011400594a1004450760400e040a00d8829454402003c40c010544150a102c01022450010401c00d070041c51103002c68105908940501081c45005801c4c1e50043d80e0040940c20074003941c12040ca0201c0d200c2e5030001101c40018204040c60042d542999017854490740960070800d0740001895040c051003000e006104000c480c410082c80302d482d0b40705076500c0050052440300b40480c280c0442e8603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293732535 1250 293731285 293731289
    0x30305030a05071209061a1e22090614071107151101180203010c09080304050d0602090306070c03020d180e0a090c030803010f090c020604110406080109050a02090c0f0315010306 78
    0x200401800c0c00b50f1401900034009500d448940b6910400c203c142454682236141038880650351f001c3d0a1440780060104081001c1501044240da0001c2100740b260a407080f00c01e01e5006010100c0c07805180c00602c08140c5020340000100211000036164170b080c00145042200d40040400050232101041196840b000e011164065400e051240c1e01d15038490500c2d0001c01e000310001c2000e130714036940c01d440e408050311880300b6070380090000308101e00c1c121034403495407405400c000d842d008c900c030000703410080103c070260041142c2d08049018503504100e028038400880c100100290041c0c2e08000380c2c03910900c543c400e5000700c1c000054849803282c022044a079404121203030041c1d241d140c40082d5030000d000340201c401c070201c0005222082801182010300058010307001c180c6458480020318811031b0303011a0465103840000680c01000d1080304501c500500c01341500c0c8104e0700c10002100e0014206086da131809020302c0c1102e0300e5040480341c100800d1240c0f0396603d5002070058001e09038035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293733785 1250 293732535 293732567
    0xa1205070b03040b1f0b1c1e15060504050a060309021504120c0503030a05040e0910060b0c0f011109012d0207090e0a380703020714010e0c01120608010204060e0108010f030305030a0507 81
    0x2894223003030400ba078001c8111580c608000d94911500e9120440c2c00c2e0060b4426941d0001845804102050280c0d0145400c1030000c0c081d1440ca40041e48190040e0303001764441840c2c40300541c090001e00c40c513490001c014001c200d01540c60100c8007a8014540d0145003d84004440064045041c00c0ca08120008840c110040b080c8030343d9580f940d201d2a2a0456520000103008800ea000303a00c10f018481c640e005076007602004d0501c9503c100440348410212103c545898120902d02c1242010b69800c034484150796004020490401c1000c9081c2c0d0b140c02e040307007040c1e8081002c1400040c0040304242c10381900807102d43d00d00d5a0b456003412811010a88094804244010b00c24404e62640080140500500031040f055000b441c0c903900300c414000b242c1070707180c02103030110003550310030a60410703000b614140205145860341d43e454220782c03007a072114010500d00d100d1100c865801c0a102c90040402c543c490910341d02d1601c0c00340451100812450340c0320b0791140000c00041c0941406000c0c2450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293735035 1250 293733785 293733821
    0x10f1103100807060206011703130b0307030f020c070e04051c021b1e0411090301060b120610020d03091a040f061a0a1205070b03040b1f0b1c 62
    0x44414001229882a92401c0040003249004a03240000103100c2c41161055402821240c0c038005541c82034072042c070060661400b080000c02401210440407030054440e88010a6403418004805401c50b0342010380f0602550043c000c0360541103010507441c1c21100e6804000c5201e82d1140340c0a418105203000110101c40411200e16801d6400119080616918405210b0a08168080290301440c6105004e6046070350101494141819001600c560a904450a00704600d6400190a4803825040076010520205550307558034505080c554000314140d88403107021800d400000e4076892240210800e0584800340501008035840c0250b85240403480800050700f440d00d4012441401040b041e078000d420aa04182c2e11401c180110303d000e5001060a55118504608103001d414a4007042e05d050041003030029243e019030004611982c824090304007180b8281110054110345010b06c05400d42c5491020f03c84814400225500e0618060b0740c040110b282d4030300740016200840404107140c0c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293736285 1250 293735035 293735051
    0xe0a08092106041203181704080102040905061905010804240603050f060c090d02010806030f0102030708100605030601090306090f150c0207050d0503090108090f0a0f0201020c010801230102010f 85
    0x1007a141e000310b00c50001302409801074501142520003103001400100d0314201403000040310035524800d604400d10019040c995914001030032a0010390016001540b00c4080082038503001d11300c811850861201c03090355506140000b05030420080004001c1060b2050b811902d8400c0020080a28090702e818005a43c4030f103000c2e5211b400c8001b0001c501c1c441c00c1d020411620b80e4806607060a070025083d020608010b400454028102800140c1c150052407049181d5600c00e000452040c00d06855203062030408801c458901b80040d44984200031052040c85030340d0b83d01408100c204c940151000c9030f290300a0503d40303401104000c0050110304030102c045117604807178202d805041c006400391140541c3d59001d2051100010400810f203800402c00c200c815800385615030340040c1d00d00c08580940c0c14186d4018540102103d082d91240072000d800411136034100001151001c0c20700c2d0694071949000020b880501201c40050b15151203403a81088030b034801d500c401400052440103000751300d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293737535 1250 293736285 293736349
    0x70f030306082b0302071a01090b100206040c06030c05090904050c040e0303060a050904080c2e18060c02161206230a1505060705070f06030e0a0809 65
    0x1960b11070380d0320a000e040071081507051080700e449009210ba40c9560081c0440c000b00701c000f13501c111001c8545003448102840c000789076001c800c1c060458100c000400070941000c0103940021490180300710761141e8200300004030700991100484415043c04240c254200900b0381e400e001740d04040d80c200900170100003d000c00001e580006080503102080385401c034a000940320300c0103d49081d001081080100614105001c43e268010b004110782030a0200c60504039040111072010300350031010000c8020700800c41c411607250120b032107842c1004184443c0d40440ca81d900f1110b00601070f1030fa2052545c1c103850084c40700b48030122410040e45080703a110b940b14040e4401d030030016600f8a140100c0d00c00c1c03003400e8401e0a041d039075080044070030903600c606280028200500c01e4030744000140b003001070785d85c9556002e484510f1007171001e040c0c0305090084140d181c00481e40143e04040c00d0507002d90400c0800b1030510502a0802c14490391600f0070004034254140c592200e00c0044d0444070086c03019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293738785 1250 293737535 293737541
    0x1819120c050907050a050313020f06030c090f0d02010206180102041703030a060506030f04060b040b0904060f0f05060609090903041a0a0e03070614030406060e0a0b1c08070b0c070f0303 81
    0x2640003101e02c816103484400d003c407268015048060003290782040401c01044040740351400b1540300510309a5045110404a5669001550342030403024001c41c580c101450025100c07010004296001c1340403000b6500000d66421016018010f00c1403190304110110071300b034048801034140c45800003012050050f215507a0b50080342c0e0100da180c500240414540744c04003c4a008508100d0405010784454940f8002000d8100c0c409a21542d180c020040c0c584504110600c5079018640000d09400350344102803d4441d498043c048607441c140c2009550b07500d00f01546c030342c40d4003900c1c0c8044a0f516200564034510464100070b00307076000a10042414400030b001050303924101c1d039491081c031402c03005141e91010540154400f1641c82c2295101c107251140c05168003a0044002003440c998503440c0da1402c850950f8440403903030700c4401f0910581041340e002c0020541001824400310340340e0f11100f4941c01240b05c000c1c2101140c4010503404400541560301194001081e00c030a1072040c42c001e401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293740035 1250 293738785 293738789
    0x6040f06020613081b030403050a032c0102190f05010603111009060c110f090a050901060e06032d240901151a0f04081608031819120c 59
    0x5202e0500043d607000301e294803001699a0120150b810058405a001c03c0001484680c102d1440103110010119808000f44002c0c18002d460705c405098005643c030313a81c1c050401c0c1c02c049280d000008180d55990001e8510614031031a5142504075929160002d061a4028005001503003020008010300903211020203d5640031194400710405034a03058940c0e0b9481e11441002c01d9980c1040303000b02d04540781001c802d003002402e01090400420005110400a03a40c03c10003e58a00400100381024802d1401034644400b8583c05850807100081d90b03401084240440e6103a9040000201e0001d2088003800695800680d0340c4401401489a000100b261002c00c2e1202c8840c00300b0455103061191350407000003020202150b90510b1502204068150308880c0c0c00c039000c01c0504601070902019001400800d009011210784c00c030740c0c141d84100160440040c0b504104036000e8544156104000c00b1042070b69048075400c6043c10704400102c603a44054083c13640c54102100f044258a9601e00f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293741285 1250 293740035 293740037
    0x22a06030a1d06071e03020706020d05041104151811040b0c01232e08150901110d0b03100c03021e0a0f0e0a0503011d060a05060a03031d06040f06 64
    0x4042d50300d042030358888040d0398000210790b848201c45141030440c1400c0c0b08003442030034094030300440b60f03480314102c1c1c1c48501c0302d03255951303600244401c100320b80180f41c2c921a000c0328103018071412286030304112800ca102e00041c40301c0140182030500c04540011080024100c040380c0c03141e5580311801c5c032650001002c0740995181c40303465030590507564804048648900080c036a1940d9107a07907620380b800f0918480c600002201150032004003203d40f1170014000c0c0b80003070040d00034681035205080d00042c01040711641404420300c0c102028001340c5c1e1040725400c0020815000000119050012600701d08070740d1401e1642c00b540041d0540c00030403455007078040310b00340b03000c01070321800da2800380b0480c00e000122481305040030148035042c485a0000300074240815642c1d158006400c40b11040c83e8501d02d6003920079800306d813100500c0310540c8420301100a204914100c00003030b00c003921b6800020b05100d1350400081c0803102010305c4c02129180a0040c03690340b602d03459500000400362003494 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293742535 1250 293741285 293741321
    0x1060f030e03041419081204031502092d06030a2405010f030e0c18040c08070303090e0901021b03180d0b06100c0f060204050a05030c01022a06030a 65
    0x940500000b102c3c1110985981510958040c01c2040ba200940141494081a80502c00b0a80301001d001540c05018420740c815521860352a02054041c442c0f01c8019041e032041c40f40c0480c076122012420100300641c3c1c0f013140040d000581c03104600c85d0344d800e107903000781b0040f080000321042a406564010030321074401c0189042c100b03510a00d11030318055280010030301448524802d00941013140c000d01d524040c0c503c0b60028001060f0341d02103081d101189901d00e02c09200c288910307601c84a026206c0c3e100904449411910040d000c3c10340c6200d10700f409820040002c040f01130a40c161361201815040c0303c00004111155541d076600807820403040d64207801e02d2001e041c40c0061980c00ba03958000c0800740150383d564200700710700b0100000d442c00d000c04c001c0d80e5800589038120545101c1e00c14400182c981d0304000c1801060b64980d000a07000f988072869622080c1c0e000941142242c851900c411006854000e0101502e030080c80c44541110b07000c028403020701c100d500400b8400c103440500c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293743785 1250 293742535 293742551
    0x6091d040201020c01080c0403080304080a031514210f0a0209010501030b330a08040b060109120b0a0204051008010503060709030c0e040611030a090b060301112a01020301060f03 78
    0x14026544140d80003800b40c0d002800c0804075500410fa550380c44440740b41c1b468105940ca45914005070f000700c800b1903c030b0b08006001601507405100d100065501c688440c403c15080c079000c8819039a4058010340714085098400c8041c1c0c078031200c05411904080700b0b48461001040d5481d98031410b810080f40b00764614000800c03594403c2c880d280300910001c060b40d075049110007403440721009000552000e9a00d0031781c44080441c90703034014150481d40d540c401c5030350300c0d09041c035111450f00030706400d0400121250400540c00ba0700d0712480325075080201510a0380307900c91032070000d100344d6014a40040101e2a42118550444442d504880d000c1e01565100d1343c81010807194051103001c0140381d1030f21407401f8000c0703485420030a6405031060f94001415030246001c0c407990b40046481944103511402c60204201403400c803150020700980c028030650b6001c6200c41a240240c42049440342c11a030407502c880104140300c40304001194000710b41e29611014000c091510107a16040428203190403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293745035 1250 293743785 293743829
    0x60c0513061806051b1501090605060f0d05060a03051f050a060501142d0a111b0d030509060406051b030a05070611090a17010e06010305060402090405160609 69
    0x186402c0d15054140e000100e0611500b640d00d13800026810820311074102800445034020043c0d80743d84250594003807207546c50044a0401d45143d5000980034150a109251302d44007580183d469080721480c022420380e0703800011522110003548041d004d40b18172a0000061a14041020152145450144015a00d02c242001602d540d885081d00180000c0386016021580748003401e0700c02c8014800c0a1008880d075a804001648565080001800020740034500ca41050980196503c81405003090740c50341c242d02410f0004002e001030084030715001d11010544900103e48120400810030794541e41c079404000d1880c1c20140740c180c0740300061282c1c068601000410358081052a655061030701e611982c80c000038020030b011515800b8010711078407400790765200905000d89007094080b01502c4400000c039080da01a042c5d00c8942d13800c004010300109001150031070340140c0540380341b2400d03100d40c60900c0c45e0404030203140300790a44e1131101040c040c1c0d000c600b000840b80e07d40c2250305c030495800c1d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293746285 1250 293745035 293745047
    0xc010e0a08030c0708130321170c03070201060518010501090815151201090605190204032003030f030f0114061c0f0b03030d0209180907120f060c051306 67
    0x401420708003080c0000740300d80f1141c4004120700d40c40351030303804d0500c8200b00740d805c81c40000c0c0d0011610000d51550740b4204032104155444514014907140e00812101e0000c0004404003400c40300e1062400030029010314004d4200c00001d0001410300320400708041e0032062040800c2c0100c50005420240c0040d17035000010310000121031840c00c1d841503890b000343c0814110030100e00c258008040741d0b14032034240b1081c454080410701408002c0307078a00e400c640c400208010302000900c228410312081c0042600c0200b100740c07413101040e424a90900020010b465400b60558480102e030340001003200c03006030030300c0581c100e80300c1c0400c640c0607180b4402000300a01540c600412114514008034880f031116810681035100b28141c00105901540f0120b819640306607240804541c0024030351006042601443d220707988010300c10059410014945c40e100d050b1441031029070403086c1c0c0604180f00b00c4074080c021156000904201704014144080c02c1604580940b50b85c0100320300c0300285141c0920 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293747535 1250 293746285 293746303
    0x201060806070c1a07050d1104080705010503090a0b01030804030506010504090b151f03020a09090b150307030e0601060c0605060a0e1f03060c0e031207020603010303050913110c010e 80
    0x30080c14041c1d880010448142c4040007050b140c2d600380b101c0b0324a070a60b0b81d2010b42e000307440660f03c80d50b0703036003011001d2015607000358501065654100010891402d0110b0740f0800c1c2c1d8024030b0050b64944840b40e0092800c0d145000103801281c0c550000001c000c41a002482220302c034005558044e03076210300304411202044400743c6400d000300c00258003810180001c50300050018984480d07240c00d4171600380d800600566580c0840c7e80080c051504c0c54100307056200820f42c4075401d0200c0c07002e08020404140030800d2410000c10040085207040380a90000c1c185000444119140d9680d84c10740148a2121241c0c241e07050361400f0702203091402c14462500035a03140712072403801911419003902150014151141e0700a413003410120001d03000c1c0c01400d4001c03402c0d545a03243c0b0003041c4201810309000c2c4050302c0b9401000c0100c840140c0322181502d04590305400d103283c56451140c0829280d42c0c1c210f8024100301d181081040010080e50090302c50360346003d0082107984c0b00300b610556205544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293748785 1250 293747535 293747549
    0xf03130302042c0309010207050a0515030721090b07030504050c010e0f0d0f110306240a090f0507110a020307170c190303140a120c09080d03060f06020106 68
    0x1460050015042c26081800d1440742045000e01802192400b0b03010801d10340c5a1030807640001616445c9503030b040110402809084500c25252884c7c04006000b43c45828030f04400c03036801200280c0c401d0300403428002c03110f04030780241484c40c000b4042840200035000341266200c1c105d80c00300e8001807080c443c0d944202e0384034006003241107941006445204100041541c02001180580d0864030303a0b03032404003c02d1080a1000c0e4a04072807800950800079050f900d80264001801c204a103481d480e0312941580a4021070360323018070128041640c0c40c0c3c6607005004402d09280c010b003280103281d800113204804030340d20b600103458141f14442e100c5440d0140030350726030f02c4035a090028a9550b030401b000324200070121000c403525000814450640c40b54072440b200c104500030801d041d0011600d41d414502c88c4205464408035400182003600c4010120034039036600d5060440c501c0c0105841d81c050062007003210f00308401900d005001c0c1120340144044424000301c00900f09005000d141e00344c07414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293750035 1250 293748785 293748817
    0xa03080f0703180b060411070602030a0608030a0210051f030506090708031305040221010303080708070309240e1009030e040605030703150f050115180e0610022d0f03 73
    0x40741c4c540740c1c5981e1003c0c1c0361590140e92840540c808400075002000482d04c03400340541c9918000c00c00a04643c0c00380e0200315150400c102d0241e41d641d0100e8010001c1080703100019898441c48161440c0b8249800c0e04078604100400200c1408000640702d841107204800700d400740354480c441541c9074021a00d0104108207880020b000c640340c10340292860000d0b04100760340c3c050f02c0c02c1e07200034240c0c000e90003500450700d42d00901c08c00c40e0340034680d640c0c0a4070fa41801e101e51b02c0d9a0780e84040c0d0070580050004003c540b000040f03040441e81c0c120001001c0d031041144c12000340c160740d020090030210390840106a140b008880182172500505007114802000341400d6440c680b10000590030050380f02200c0c582d2000c401401000e148200c502800910403424002c0c0002000a06001801189030414402c03101c8100300104452003010307400202610800c400382040c0d13409a1030a91483c10b20411001e03010b034110304038880d8920341d82c440407c0400f00d84180b50f043c032241d9128410210100c00e03102c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293751285 1250 293750035 293750081
    0xe09010f1a0f151803030705070308030601091d040f02010203070507080d111b01140f030a02120a02070f080c0a050118031806080103020f130c03051911090f010903050a03080f0703 79
    0x101c0024104d01204040c042d03d103048210355074981001c034103400031140148007005001c410b50f841400c18001c3d02581d014440726856011451000fa070000380003c04018080941908592090080e5130b03016611400715120a9214410b0750307101c200c40350075440010314032000c1c244292400180c412031784600300c04001c2d00e40190001103800c582c0d40d40c3d142030b401d14104100080b600f445401507200fa86c030000010f071603103000e60800b01c04900180035030051600500400740420034001911407580c0d400703a946941d80c0c4c07200c0c56240c100100c1100140c400c0d4a031030000700106c00c42c9101e10080d584a6910050b403a07003861400e09a1103110b02840c000204070100620060800c222640300300d104c010055030034801900e514a00340c401c05a12980029100c50511202c0c42002e41c80d203c8071881e4020034400c144d4200b401c9203007401240c4005100c4c01108044501e540d01400400c0042c503044410b4433a0300d1a281001b6103800d6056a540911007001000100500d1203841071074a141d808001d0300095070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293752535 1250 293751285 293751307
    0x1113063210050f070606050f0402040b03070c021203040603021e2a150a0b01170903070b15040c0c03110a08191707020f070e060a0e09010f1a0f15 64
    0x724040c191002403103010800c4100c074169400260648a20459011500c0340c1010306004ea4041d0500c0b009000e43e0040c0814446d0701880411342c3d60000d85440c200c0c05503200383c0001180180921034000003400300060102e013007681600209079407e114419030aa0413054a000c86051060f40310b107401c440b041800d0b41510440401003003034041207031030441e000c4809035149010f81a00a50301c0c90749440c0d07545060145075030440f103204d80b0161040707107c12441c500003000980b240710b003003801001c0d03804400000e842602c0300407805601000123070007002402a00c850141c1035451804041c0d022840c1560211140030000685580699010300d489081541b82080e90248819854a030828803e2507100d413160203a01a5405104014a40c02415011050078800b42055442d8002d103442407a48400c11a0989400c07851004641b09490f4414007907845404543c01807804082d1801402d0038044181008042c00064030320700c150031103540401002c0a001c0001407200b18101e41b021001c01e011804d00c803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293753785 1250 293752535 293752549
    0x50f0901050618180601080f040b01050d0c12120801080c0a0e1302040e101d210c0d05070605090309090402010f020a0b040c060806091b0711130632 65
    0x1031080c030000c07501d43c05840014001240607107612810502000c00c100240da4011a20b5802c50700f9a030798901c1a04250303d508120388414001e17a03000322221580c3c2400c100c4110310b841c00404d0080400d080149461800489081000c3c02580000d03502d0070020550070030210302c0c0d890b03106e0009c04240e00c282c40e00b00903100c07202d002000203502484101c0e0080140c0c441e4018100d05007452400f0701403144804a04608640690986141c0a4040364403001072500c000750102800c1b2490b110003105420207040c4800500c1b948901c0441c030700500da403a10755a0b4106016064147c465103051040742d0b0750030704c5280e47c0e0250030801d80c0e12030028004a005540941100c5402d40380078811346200184946070f080c40300700155022910641002800c10030182e11540054000100b110b04000504018021503072041c00781981a0040300700094140c00c000041002e00401e2802030002a0541039281d4510020072040c4503031a9030001030940138041c2421620780c0d10303000489150a402400c00c1c03405000d26 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293755035 1250 293753785 293753797
    0xc0706020d11060121080d051b090f15040b1306090e160804051908090906190303180e04080705060a0c0504091508010509030a0216180507090504060b07020901050f09010506 76
    0x754002041c01075020071030506c02424500b42080010a040c140081007005186a0400b000f44400090080c1c0b642030b84c2e06a084807007054200d8a580e0f40841e104280f03d51481164801e04070242c2c00501c1044100141a45104480f496103610203182d41d5068071489501d811605529090360003420070754624050524150840d020300c1c120f40341c407105040e09050910404c1810b9844078001f04500c0d81500e00300c86d116070b0000094030410000c6108010002440040d400010f06106450914100c41d04c201142103000b4038002e0202070b5141054100b4070011740c04002c0030b441d0b5004030f1000030206001800303492820350340c9a0301c65107401c0c5807141c100700501c01031007a15080c8062120021f1003040034040e55000d0000007010b507640c0c4100340030181c981815118a0303044000b8a440400c00d0024410510600405681000c14207a03034814084981c04126048a68440c2c03412002046984011000d49200e0380f080d01c030b5403140e0f62030380d040145022000b24810360208c849001400a13040400242c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293756285 1250 293755035 293755079
    0x12040f03140318061c0f092102030a0809011b0c060e011103061201240e0906010b1206031e010e0706080c0706020913110304030f030c12050c0c030c0706020d110601 72
    0x10401c2c0c0c0d0012817050360400340b42c0c40e10003600c1d032514200340110103001c1c91404803410030340414603991903c080d45034015080c3c0c20f01400324207000151a92000c0d0411501040115404806a4100b203405443c00400380d0b0244c4501340790004000540c03105208080304051242072940c110360360a020001144a0201010000e54842e4450401503000900407030050344a010800006410b06400991507003004181c490580d20440c01040880340c01c070b046568a505021400c100d40d07032480c0110b0b01d000080300301c070210848000304210307185078190321500075a01d203602038810740c0742d80b181c0403103a40e84142d17030303000c010b000403c0035100140d0315a0081408040c00340400b4030191030b1070506011a5801c080702c0c0010b0320004200410154030220540c0c01044504082000c8004000c0003040780361500c1060500a54900104034040400c05c165810039140d14204c984c0c0e40c81c1081e0b0300d500d4640522031640540701c1c441484070402c2c001c03420218221204002090b050780b03400c03408203910842412102c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293757535 1250 293756285 293756317
    0x20603070917010203151005070807081204060b0102060a0b01021903030e1f0b01090605090d14030a20120d020a03060f0608160e030d1112040f0314031806 68
    0x741034104241e01a000700b003034100040c1c0302d103010305507080302d03540804c4030b6841010103000140100c0d4100c4152000560481441c984401440c40d010b00c1d81e109a80300320103c4101c080420040002903089913087c0d9800380e09035001605e4080200b07003902c025146035400358112801c0320b40003c140d4111112402e00070b00c0d001c1407400004400c541003101c000c07004000d0802381344031100607032107a01445e001a4020310b030031242c442c54030030010042c1c010b041c3d29510030f4040c4203100301840b00c42190134100c01c0710f003400d0704da41d021405409444040ba50300c3c1001644511001c00c1c5030b03035801155041d410300040c91554030301480b0804081c003d5200014507070030700d41d031100045000785034a105000604801d441e441128200404600180711010480d2001c02c14580500c0b561500e000c180c1d42c0201c14241498640d00410701d4000d801c00905840050302e180d00031400141d01240d60407034008070b9000b205195060100401e4054982c850681c4501030314005408001d072600304030005125811a0220107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293758785 1250 293757535 293757539
    0xc0204050627040611040501090b07170a03021209030405090414010e0304150e040c05090f01171510020105063109110109050105180906180103030206150d020d0206030709 75
    0x10030840c0700b09254000200008070410080016500ca81e0f0851700e00d41420f142414900320009080c1c95040c001c400c0500004900030003000307404040c20000310000c3c2c0c5056181e22029100500940184045800140d011740c08100384210100c1100c0a6503800340640d0701990340c0f0b454aa03140010315012500e19981ca0001545601c028805000a000910071592841e001c8031401804440b651030f8503445113103000b00041010703030883c0840b0a04e80703090742d842c050710b80e000c401a03c511081400c40c44080035142c04100404440d400c01083c039003001c071130314595500700307034412404c0b20300071107c01c3d41103c82100213090704001a84030725103a003940082e1050701c00940005030151040100202c6046d64001030710b0388a9078001c4c8030385000c0c10083c40e10a0034042c0c80ad1848200d44820000c2a00a070701c42c6020510740e850740c512841080f07980450304001941d4074036000390307900001c0b244521051071600104a261400d070500c841456001051a0002203003902000000e500180c001010f200d900500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293760035 1250 293758785 293758819
    0x504020d1b0b04031101080a0c080a0e0705060415020f0a08070b04060603050a0c03050d0512041b1e0e180303161107120c0501020d021e0a0606091505100c02040506 72
    0x400285201c1c1032170031181c55005001420044010306114134460031b241c550b20070300f81d0100d0b000d6440190300c000460000380c0303007401504260711900800c0d00010001400310f07464800e2400d050000e000b40d801c0320740144001200d951a4880708800916000d0304005030b501041303030650000d4105000b91800114650f0f20f942e420700d0030070682c01c1118081d06908040007446004d00c4146c0310f4000c0da0403c0f81c940100c07901d10b001644001803005020340549003800e031130314003103152680280117103805040000480c214405d00c0d9443c188076500d80c039480c24000480c0144601c0c82802c049803c8802107042d921050751140710b152a500d014020003411030071100b8150300400c140ea0040047e1403148022040c2424421500540b5030456030656120800c0c80d6403095000503403440c42c801c104241c4405020b60f07281075040000507607000e441142003140c0410f4801d6940d2080405000c19805207280c0c1e503a803401d0081241c00742d00c500d008200b0303c120010250409802260b40503c0c01443d01c4052840c805c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293761285 1250 293760035 293760037
    0x302091c031d010914090406090f03020601030b13030509060c0a0804090c2c0904030c0503031e06040e100c120212090f1516020102070b010e1006030504020d1b0b 71
    0x1d400041c0e1001041c0682c282e22054000225028640010b10360305008449141c15210400b4600503940b0030009014404c485c0d20a02603a40d010090340c03100402420001e580700c0f02800181d60030200130300070480111418031038403556035041c0c403071070b040071403010800059411001100034540100d4203071740002124000140701401d1702200018204100700c070014480d81000d0301030a00c240c04c00c100203440001080100303a400d001150315500e60b0341c452404651794110309a00401510010050101500440140c50302c40f9120024450060340e81030200001c0d9201f031400600700341c104a805200c1520680c0103412a480300342050306a0f00c0116020004990101440f203003011340c4a0300380318950b0710a009455009105000404941240c2107a00c81c4140d4043c4c241c0d40402c558446c03114155000790152131155400c420700e50420f44c0d41b101c2e4082a800c040380d00031428180007202040ca20300034442d20380641d8000e4100d40501d401d0b613075401e0031440c141100c0c80c8600130902c0700180d0020448 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293762535 1250 293761285 293761339
    0x181401030303150806130828030c0210090f021215040305091804260c0a0c0608010b03010b0a03270f02030c06040305030306040c05090306190b09070c06090c0911030108160f0303030209 81
    0x56400901cac4807449030000d003402038a400b42031003e0b050024150126074038603401d140c196011924140724440f2000f43c5c41c41c21698820851541280c10200400c0c950010043d019149040d6002020020402042e00705424110750090100c2005141c1440e02d100362010103080c4015000f0f01481c0941007143c09203041c40c0c3d00400c03074422914040074400e00b40c3c0315600c2401010659072480c29541014601000740c01005110300030143c1d9003041490f52a81c0c02482051385000c00003280e8949180c5c100280404400e420a0340203100c0d07200030003020304081c1d040b20212500000610300350b0b11854200b1010300034200030401008024015050aa070382802140c1c02810100c400f003144051003440c45054542040c0d071306100e4040c0408000c200d1380c10850040160394440d1002a4004203854a0032100d986504410482460102039015920146001714141ca0b9148200e401903030a5458803001405a805000b400440600c0c00f040043c0c00307500603252510300203100b455451210180c03030b54207903618 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293763785 1250 293762535 293762537
    0x90306070f1b0c090606020609031e091e0f09074103090105010b0403020604030b07120c0906020f0316140a0501020d0f0b040510181401030303150806130828 69
    0xf030740041004040a10601c4c1c018080f030f0001e0a403d00e42040c0381da80b64040c8050300121790b00c023000381c0844514058110f882d48000100f131031075109110400e80c0454021070710b01c0c80c06610720080d041224507203030801c280b082c0f000c0d0303692110162000519030140e05d83c1000084044181d070741c03201d1070061214401c1c5050901d201c40a500c03880d12001c042d080d110706034032181d6020380420090015850300320480b01a60340013400ba0620740c0b01c0c0442290005010306030300c40703500e10b040c030b0050070749901c075280e1012500c05d5800c1356a200c1100d004039859104405445040206031745075400011820f0004807013050084054800103145c03504c0b40b60130380c0e02646804090a540d01c1003e40d44030101d200c0c0c08500c1e1002e03102040030b4a800010f0605181d454043c08002c21841480b007501c2c6445074100c0d442030301202030842c5042d40d4034a80500540306c907040324003003000c100e480401d0725000024078500c10b020081058400c034a2a44030b4034040e91012050000c1c00340ca0303032003504048850789103500071555031b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293765035 1250 293763785 293763803
    0x121c05090a0609060f050c0a1a01140108090d0f0507050303130b1812030613061814091203040c0509040f060c1d100309020a030c080d0302090306070f1b 67
    0x1a80820074070300207640104051040e103003414041550f00c40c1040d001e01c400c9040c410f540b500180c840c4ca00d000c00e4010020f00811500d01066903040d0040c2c045070403294410948003407000b000006650f0540100c030b106100703a00c2118001e0803507226542c103201c0e601a60034028a03001140e1260b41c10366108449003d101e1617510307000340811215040c026800001d100c2c9014401b001004030350b8440c10002d032403040d008000b1001c5019542c459032161034100703010404000e00c0342c0d10031941308520500391144041c249484605443c1c0d90341c103850300340300380001005810380c2d040000e110b840300d80001d0b1043c1d071700305108400440d040c0c1f107100d071460080d809006032500040061400c241911072070904541040b401d1803c0c0800c1c00c3d6054200c0010841c211004111100e41d4081223005001e81e0a0181d406a85804c000050002c840440b0059a036448141c5e610100100d0007602a0b200d031000d015015132061001601080c412021285241c51920b8106500810305d2042881c0c005515403d641c6000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293766285 1250 293765035 293765047
    0x9050a080a0201090e0402090a05040809041d0d02010c0507170f0f032e06050903010e01180302121c0b040e030d0e0c031207030c05031201170606041505121c05 70
    0x4c2c01803116001404c044220500d9803400c0e501003902c0c040050b0091400c66140c0b80860200507165098801884c00648100700c030000a40d10300300f401e0b800343c5100c0d01c14019000c030000305070302c1802600c0044206807111890003490344d41d014214141c0f529045901c541c184001803010580a0061002840110f00191203041018558100a40c10b044080c0807103d03510701815a40b02d0800660120751803801d005403104a2000032034050076007160344042e10751900c1203901440e07142c0b4401c0e03040180250308650950940b181c0510b250302c2810044007140d80541050752255446400600e05800080c0c00442e08280c1500e02c0c40c59074000510030078403552551054020005d041003540324501003280281804860800480c4030f9124070b00000d001c0040045602c1e0034098208200d80700e812901c07415805569440640f035030114000d2421284034007681c00840c05500d00b0307008141180f171105400d071440724605020801c2041030580107809902a06030440308020355100240c0d640ca216413151079480c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293767535 1250 293766285 293766287
    0x106060903030e01110c060d0f0e07080d051c0207020301090c08030406030e070e0105040c02210a170601020d031a09040f06181e0222090b100b0708090109050a080a0201 74
    0xd42420b003d18104401c4980244031144006543c0c8a040d1042d251355503141d0110031480302510218192000550600401980003240080c00c0d00407a15036400356180d00351492b100320790910561441d03100c401a0382801d2210350351142c0c0100380051000340002000c0c510755940d1004454507600415894002060812181d0740500860030760b0740001c03000d070044e00d04141d00c1c442d1586040c05141d010710b81d01d4440180d0b41c2d0081207020500001e881280c29103100303503041c101e0654011040c10b4002030f05091005007094246c040c1500807107050b00580701d000905031040b001054844a10003542501c9040c0c56415141d962003113007d40c0c0240320905031041c01e81800c0098903929460302c00761481140102c0c0102d4907512031030580441c90003042030ba0320203900004801e80402d0520210b011081c1d82902851950b42c0d1013000518411030804445548043c0c0a0b40300035403a11a070b0103152010442d13000066200300040054030414141a441d140d19075010441c1040e0a4100a1070313a4081003119040d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293768785 1250 293767535 293767547
    0x103050603030c0a0602071b0f06031d0d0806060f0408010e0d020708030f03040f151b0e01020a06050c040e1801050f060604050d02031e010213080a0201080c130305010606090303 78
    0x34069004520b08080040303070b00c0c0d4075200060058006580454090200000c50825002120044540350409070322680e6461006e002e038425500400c1c60140715404d9910700030110810480510003400e20440114410f80c1e82050051205912a100f0402d20003400301c0c0034080e0010740140710001032120078624140d890502252000400d541c0400c504114000b0000212181c2c481c29140b01502c0340c48519001d07411208845004281150740348107841440100e50100c490006c0314101d810380426440003e5802051000d2401d00507000707a00c0c403d0225155801c400e0f0090821000c840ca0b0568a150001c40c0403015552410105207882513031403008400d002c5c50f078200603410380350b03406801d000c0c0008140788228400c00d8050060840041c0030340d41c06210342d2002c40b00c2842c811008059224100f8000d502400320396642c4074003101d0200c0d0312900014014a1180d041e180c1040b40e403203004081000390040d00400b040d11b183e118000c00010428002c2000601c05903d032004005e045250107004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293770035 1250 293768785 293768791
    0xe03190308010e09062a211f05060a0c0f0b040506090d0c0215090907030213080705030c010516120906110d0c02040b1c08030105011e0507120903140c010305 69
    0x41407102d00d007800280500800c0d00b58000500c0003800489403290f48540f038041c00c04244c810719620021903090040098400038081c0c10911090007819035423400b04030180c1c2c03019040c6d148007480c130201c0c090100e0b0505900424064025040c0014956413030b0356500e40e01c0e02e0f81e10048586003100300901003000f034200106038114213810042d01c4011a043d9000f0701d04002160040c3c45268070301450018003040c44102d480110000d0b120500c1803608003000390280d800090250029902c60f03000254442c8003041c2c3c8815140c0060191a100344a00f00444883d000480710701081c90041c4445000281600c0b19a41c2d141029181c60181070319200d03014101c0c240c145800c0740ca03504414490803445038480d61003540350303034100e40009410344018082401d00d404c005c0c1000d0b0f901e014242260a10007500081e504aa40276a5681c0b0341409080c504558003070300854010201d80c051141c50000f070b03040c8c4019201034030305181220003103a494a41c1d0100c0d60b094455038089130030040d41d00a655900d07025440d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293771285 1250 293770035 293770049
    0x10902180708060d0624030210090f0b0310120b060a05040c020a0303090c050301150306050c0403200f040507080703140105030a1403090d050f010c03150501030b010e0319030801 78
    0x580740c280005031401e04000c01c110b20525140c0c4c82c40080092581c4021003c0202000d0000e000c580c0e2560082e981d00c0300c2c0001d900c5542c00080030507400380300b503c0c2002528010884201c0d400d1402c150001190800b0340410342510750a440811100180010340d0f281500400c0c0342c83d25800c0400030300c691803000ea00818082c030308017071140d444c99070001a000c6a05905103400a40d6900300d05100c000303591503420255140d402c092000c14411196100c0300c0989003c1e5808200d55101c0f1002d45015205d00d00c401401000e60b0425803681480c84c6802030561000500207079244104000090201e0310215407482c0800c112030280030425a01d0f1080d214403217002c19900200e5410240020360b20194810300038040c0c11030781c1c2c00d0313510303180244142c41c2583d0000d0070702040000305150440d100c034005035140300c80b580b0f8403140000092090050310706004942e05001d00d45814140114040c00320808070a0501800340014580341c0c500300b007030a6424103800f0324280c1190300b51800400036541071344026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293772535 1250 293771285 293771329
    0x43c14030a03140a09031b05040509070806060d080f07081b0f0c04020d0608100e0f19060203040302011d030d230a0509120406081902280c080c010902 66
    0x240000f6080a002e41405110941854483e02408803c803070040c85070b0001402049100c481501c080c2036140034000b514800c650611455030390503200b542c1c0d1050f0744501d404580c455000700e242c07400c00500090205010394603041c544601800020030560249104031041140000c92811780b241c00d02225002d02d1420001d03101c540500d118159490354102e00c0280704550004050720788400a910100040030244140c5000010a00d6000b004204c043d4001000380550f9007092071118000c030703440d40c1000e4540031182c0d501050781c0702c1d08000d4100610490966680e07158170990701c100c2c4450f0310036800b07502d0011543e550306200d05900b42c40c1031070b008081c1000380e000310701980900b0b80042c5c0e91110b10844006644c0c1d07541c880503031808412116126400000040202c1c845910400365441824040700d08001d0750040c02d1824128420844440b1040c0880448282480804041c881441c0e04074074100e211244c0a80300c1c229a580480702c0313400303180c0d0745204000450418210700d80c5450391450100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293773785 1250 293772535 293772553
    0x6040c0309050607110705040f0c0306050117040f030e030313060906140702130216081306050403080d0506060d02040b03060a140d0303020705011e090c0506030c043c1403 75
    0x402d54800010b01364809200b9507500c0c8214440d000c101c294014500148248012071070a80c011004200300c4e251140040c3c01d002021a07194042c401d203540040829100c4000e03903545495904d861807400000300e080041d00024000d5a942c10400340c042401c6950800b00e07100d2401c480070b4080450340c1d10240038040521000c001c5074820a00ba81c0d981501614901c0c220244d0b4500f002c0280701e5100c00c200c0b080003c1c00780c00d0610402201400d5a000c0e211000d888058548105841d1401a8480144545010060b89000342c040d80c10060700480c02801c01030a00750070080700c0040e6003280d00308802d403180120800c5418600b4040c08001858040b41e0406a90419404a48030041c2c0700806003e0640001701e410403c0002d500048a40070b0b03044901400001c1380310300201030b0400e10030a861000b621880490103280950480e405161800100d41c0361601d00000404240d0f0010113034801d00504984403014441502a90303010103c000715940d5a0900b403101c902441d004e808056406503100c802c1c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293775035 1250 293773785 293773793
    0x1410080601050405130e070b0315011706060901030e061602190507120302070504020301030c1410050313110a0308040509010803070507030807060e16061b020315040510110306040c0309 81
    0x850742661825544401c12445200f40700006c0d042c6c020703043c0071500c222100000c21807408405103001d480304864140051214200444030764400901a45d84003031140302103286854008001c042501c81030401140c0f00c4414100302c1c3c00c0200403202d6403c40200b101720303002c08650501c04c002001050303104800b4011095200c195440e0228001c044015036800d03117450906008010301c40007484020010340d900d60310f80c036140120942510500c01c5084401f02400340501d0090000316a2006503900c0500b075660301c240f000c940440e11541540c106203e0125981c080c2c80301c1d00004085e60251036110b03030707131407811085c4044914140e00c0310145070014800d84000a00124402003201c1e08180d040b0b486440340d04004004241040050a117481802d441c2440806082003140854155031103180024103141c6010601030003810000354035070802207040721141c16010005030054003039412038040741500d036a400200d60802d2408420305601000700031080c90f0038090420303810075a1034144039070511070355 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293776285 1250 293775035 293775037
    0x60f0910030206030403090f141003180b0c27150f070305030a180b070206450307030201090c06110c0904060b040c03050a060509190b030304090501141008060105 71
    0x2440f91030000041400d1511402100000c0c0504d2101c8200c0140c1d140c41740b96481007400c1c00710307006982c00da0b02c05114900030b00c03071445009003c0010144002d0566910038181030010421a400c0e1401c1c0031490102c05140621140c100c843d940055082541900700007141d1889128020707400c10800c00e0101100c8000c1c1540c003195454100203880b500d03016030b0140038240c180416210582c0320340d980d2040c03180007100c40f8005c000c1034080d24020380321810315901c3c0704610424110030100644c02d0307424402c4c034201402c0c0e0301420118aa0402c40a10700d80b40d08551002400707a0060391110551414090003642140050041e41046c0c020104081c07621034880500460140c45444580001400e11040d50080b500d4100000d0041000c801750300c0740070300108000c7e5188d80d140c0345802c0001c81c450910801c01801501d603240b40e4203d00c40401c082c5400f0b04046141e07990140410b2000180e041d45501485019007070301405048880c0e5444203000d2001101c1c0c4c0c05030b04004c20300e0203104007a60040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293777535 1250 293776285 293776289
    0x6030604031e020c1807090e01080d081314030414040b010906080403021507020d03060801090b0f0403090f0906060e2e03140106052109060a09050a120305060f0910 72
    0x85020141030b0802d0005a04040c41811040d401c0003082c81c94103030000c1001980c40c0318400d0f079100d0044903070711344a03001d03000c840034000c4d0401684242c082019050040004507400316000100c42140c00e0b840d81d44045543d400c0d60315800c140d10101c0c0074050507081c41da000c0821042514100109540440000c210164500c43e42c024071030203d003c1410300d842400308140344910700100140300d050940001b9921581003040c2000a0324065003c03c5840040c080e000d906078220f9044c52454840d10302c4c0c1d8420a9001e0411801c1c403d0750304001640d403008440340c5008001243e030001d0081c0c1340c040081e004c0c00403400403d1041d003000403540e01642160030306900d485103415001056040c1188141d009240b03280034001e0001078440000b403102d0340308006000c0240025032800c030111000304103080c0e40c2015160080140c1200000804a10007039000c00c2c0e4690180e0704032400b42401c1e450341c510352180c040403000005e4031141000050300300f1508911020b8070641c2c010040c0e1610701c43d4440000403038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293778785 1250 293777535 293777567
    0x10030b0d0b040201110109030e150906030c22080105060a0b0309060114010e0901030b01080705030a03170703020405060a022b0519030905060114040c1d040c05042c0603060403 77
    0x800d0100b01964403800405440c400c0c01d100030000d01c1131509002d040d8845844030240b00760b440c3e90030240507100d80006d0310800000030306118250b031582c0031580c0a68024004400602103605400c000c405000398030300004104038000015103003009000d0000100b42900144c00c41c503010810311078030100014a0504440440820007181d59400d401228160746a240b8940d01c94581d01c001b0052222440381c0c2070407294080b00311694159580700345500c070386c44044060301013101d42c948000031181c1a2100c540c440483d10300189010f86500001e015904804601d4006901c003214225203114445c41046000080c0138101d440300251420060107403140f506664441460155801e20309406a0031855069a000d0b0a4400c550f0319400c24052040000c0e44ca5031040d801c0400d9101a240201030020b000501140e8036004c1c440706005020103445990106d80800c00c0801c00050007028400c61103a0080c800a540701c280380302d02c40d100349543c0c0301a142d6880b81d0080000d1100190300042c050031501d810b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293780035 1250 293778785 293778803
    0x40801140103150b27090105090c010c0609030504050a060f0921021504080708030d0b041b0c1505090703050709110a120207060935092b0501020910030b0d 68
    0x1a10f40450345c1c0c040c0402160008015800020250070100f800c0305200e071400f031000f00003903590000d1265584041c0e043d1680419681c80c0d650b000300b03001c2d0b003150b0161400390810a1510395598007044100c4080c0c2d001c440080ca00303408490180703a0050b85040100f412031407074180c42c0c2610141a680390340c0c2c070740000d12034030324004a168001103103400d58000301000340c165454640d40f0101e1503241d90103843e040308858580304404046160502c203a003000d00c0030b04a0322001000f11a010786040001d2407003646d00403010f80c84139003013100d9030042911999000c1c001d80b403040d00e5450004e10307081054100100407410401cad0300e214a4183c405407203001a071407502034584074002c0442402482001005000c1d907003081002c100344076443e80011030502c0c3c02c54105285801520721981c8101d80d242c0900c00381c1c10200008120751501c01c24240d0001101031041e2000d0010b0b01c504100711409150480b00381e5004a840c0119240c02c0078454841d07811400c0a001d150411700c0019880c052690004044800f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293781285 1250 293780035 293780051
    0x90903030a0e0c060f190503090606090a0e010f0c140c030306040908040312050702120316110102010608060f0402030616050f0a05160b010906050a0308090f120a030504080114010315 80
    0x2c01042008442e0f00c01400a50b55000030002511540c6d11000c0208440d082074092010181d11542c1224800c0d03e81d02c0203011036403110800c02c495111302801440c0403070380300e2004144181080c4507244141c004002d0016040200341c4024003407444503103540025107014014030500c08408003c583d84900304840005404421b07291501260003203400c050441110b80f1442100981c00c42c00030114140210b80d40300310201e501c1c80e281c1d074911924a10405055003040300720001040034041c4012601d05000200d1010b455900b0b85203013400c04c4035a010282c080c1e0b800d01055003030a1089603008030221a812904d94040c01c40644288644c22074208404000036a4139100da00c5072003a55400086500b41d03400190035410024124030003030040c10301040ca00300c4001b0b000d107000740e84070f401c50307a10689982c10b2444030000c1002c01781c40034800980004540c194504201e00c1809400e0360070340f06c0d03118a03072074a08000000e030842e907055683c00d51130314403080103001040350010010040a400000441c51b04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293782535 1250 293781285 293781311
    0x50318070e070306050a1512111c0b100305040c2115050703060b030112150f02030118180803010e0709210201080606090f100905032a090903030a 64
    0x1458a03881400a00d920100340807a140c3d143c1c0000c001c50300116400700510b61502001950f0a14070349000b004100c0c51440301180c0ea900ba0000e00c900c1064414090400701403151983d010020020082c140c0c2e591455100c900380f8060101b40044200c030301d42001706281503541c2d0914040c40780101000f41100ca2000d042c40c000301e00d0048805580907402040c4030b40c6044c9044007414059600101003424040c0c04900300c0222816241280c7e81c6541200c450845500d864040c0c5c0c04c2d882a0003602500c881c0c514400b146580011402004604549401a400840c10104980c2e000c40a0a4030702031822428004c030306644152419aa00c40e0b0620f40e2584914200383c0c0e00140540c007480354030f00300c100600300d110503d0300d0712031402d4000e03218000507179206010000f0520906007041d034811902c0c0c2444036039040070ba0107800d0003007860514000042e118800645080d00c21400c0c40410410241d401c908061500101200000e0a981040305801d01d00122a141d000c0246613110555540003591540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293783785 1250 293782535 293782543
    0x80c01140c0102070f051c02060c07050c0604060507020a0905010b03040204020a1b1101090e0912070318030b15030102090904110a0b040306020d0509070303140f0d02130501081501050318 82
    0x7481c030078000f1940d80d032041ca800c0c0580750342200242d80d03d0144031802084000505038141c007041582d1301801456540b10140308a07a004102c1c140d8031803240c8104203945480e03484c001c0c0041d116540320681c4449680c810089103001d03980111454030b0078000100490500a416242c01a0381150f001d0780780c442c0003804803003503c0241004a034200301da101020078001c00201a5400c24030a9035a8290f02d900c1d42c21a42180800b40e6903079605034802c04102c81c56031009005071034203510914008508c9603000c0d40414001701680c2094490018032070500c03120450380003e000d6813140540095091448410003d0403040c1c0040c4050164810340008250941d42ea0f403c0c140906a100301054450342c80c0d04118000350080d40740c403000107190401103800040c002030410308030f9034107595043c01c45241c41308520007500a645506006001070104004407001800a00600c00c4007514446100b0704e8540010801840603060038208032a80e485901140d07404800c81c0d611441c00c900c103030520b0700d2802006241c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293785035 1250 293783785 293783797
    0x809010f030e19030e0f01021c03060f0603050118090f020f0a09020c0f0d0305010b07031211040303031a01081012050307021206040b0f07091404060b0417011401080c0114 75
    0x1580241e424500c3c40c0003140895040c024040c2d59500302c960355103003e00c01c0c451210000540580c0c0a040d1710503400c002c01894040350b49507854007049090345ca060149211420f0307000440800c8e11500107100821100280d00c640030031985040c030160781c242e01d5034072000303031900c0d00039004134551000c2611544990715030300d0081549602c119680e071081c000d000d0310f0b2004a41a42503500410061000e41807090007100d059505103c096440c180c143da80603a521351005801d50042a1100c40d00c54030707500010b002c0d10065000f03803404104808a41c0c0d4801411079101e2511b0305110898061014010706c4a41810642e0108500004a0320003424080c1c0b950007030342c000030750001c003401c401e500506020030003070300980c4905089105919984150b11b42a00304948520000d079030319400b0805034000001c2c1c4420b078000540005882d9443e411040c441d5030041e0007201702034016000e491014482440f4111810100c150001c50319410300410a440794103070030b003084c1008448192010154004011204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293786285 1250 293785035 293785061
    0x8190e0d050405130c020316030306081203060306070f020c0d14032109030424030e0604081e0f120408040e3408010911040f0b04080d0c0809010f03 65
    0x90800e96000c00100194064022103001d4107614450380c0c1c081c0f8503802a8441d44000b0740243d4241142034022284420f44003c0690030182c84040000d4000014402d5132014994402000c0c3c0d645410700a16180180180800c01007050b08008050055404540021001d01c2101c44071500c00e06130900800e01082020034080b94003001514400448a0040a41820a0815042446075901c0c4001c68a0703001c0c0b031080700b60079040c00c104882d100070010b040d4401003043d0b0070000313030100c8448182490010215002c0300c01c0100080c412500d285405130400002044100e0640791a4041c01ca61b25180984030a6aa1681d41800402c003017116a00c2a0340191041100344102c9180140103100d031502e80342c03411103a1051040c81210a0104941c036a004080031ba200c503031580c1d10b004620307001040b001803e45200300d8180404640050b10084004c002e000d166061521141003404940c00c0515a068110620580300d088000051900050300d42c640c009003000d81c0c0f2940703880010740142041c410003030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293787535 1250 293786285 293786293
    0x260402131509020a0228020904021f080405070f060e04020703050f0c10150e0f040303020405040207060209040e0706090e0c041a0c01050601080105060d0209060708041518030308190e 80
    0x310702c507242d03075024100ca607460f5800c490880e4220903410607031502280101811040e106640c6c0094200f08040b160031a00c040c001304050400c0240400161402c20f91800005c3d20050a002c180001082980c1c040e1142c0259031092038a00080170f40040409010503004d540c001c5100005c0c5801001034032805002412156510340d18410600d86031001030100c5180b45150038800080d4506500c10710302500c48045034a61107444e00301800300401c400503c100c080540030000460244c549002034000280f107050003684643d580d01c10002960089956445154403400c42000b815601c00300c003208448840e1005c0c2281c0e120302c0c4082d015441140c20140240c0e0924005140541c1403900400d40003007840000c006603100c540045031012800c0c86852b41c054002e2202d060100190341c01000d1008004000a00e00055a6139107000360b0400d90003541e8140084000e002115004840d02440c4000c410607014280e007541d40150821002a0075241c2d40c0d41440720a51542019901c08440126100119 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293788785 1250 293787535 293787539
    0xe011b1b0209010303020f060c0f18040902150409061d0c1e1204060510030c0512030d090605060a060302070c03060c110708010e280605060a12030305072604021315 72
    0xc0c7d50b990a09807154240e00c100c100040a4460140079038401152054409140156051021100011040310f40382d000d541e0f00c6120005984542054202e40700100b070309502c9501c0c0101c00c5045400503440242d810078558940903c0d80d1480c444103510040480341e19440c1c13a41c14032a286104031400c2901c03010078002441e80402b090540c0d00074030482c402c60041c01140c1c0c400810448903200c6100042035194118414030442c5072900760000350008000072242080070404520003078400e0844180c491a51b00d805108490606d0b0458101400440c182549805810b9030360445010040c4009092035944000524095215540c82d6000c07002c1030f022202456100d0001c5402070617012030060603031150504200c959080c62003001c1e0505a0300c3e842588450140d02e410016060080c03040c0c0e48084420400300b08803c580100ca0380d058080c1c1da0001d0f01d49480310001d020441c50014104d0a10b0303031b26010980c4081c00310710513035216605441500d0f102c0c0406ea805000380c240c0880080700b0b4031040c540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293790035 1250 293788785 293788787
    0x90903080f01060c02010e12010e0723031204050405060a0302040c0809060601090609090e190302070509010608061c2f1302040b18061314040e011b1b0209010303 71
    0x4068001d804a00d0361032240d980e100415500401013031002408035104011a8459103800145440d4514070100003058003020b45680c98208071581c0c00c401c2041d920301c14807108040030300135172425146041d00240102c40b07040d000e26485004600c80ca034401c2c0e440c1d80001c0e0494403010012001958090024000c00d141c200d00a0242c241c110340e5070f40ea62013080300007403075036101d690003104541142c3c81d040343c103900f0203c0000c0030b007880c042c1030719083c81a140d940b0003504001c991141114000d80c0a0400c2500740307400c0081c001c0b010380c811010071a00f0002d00c00280d507030140440b0352800104a540c03200c9000c0c60150302503500b1840110b01c0381c00a5000003131050a852055491940445420290024070403010f0228003850144001580c028000c060072003100102c0b084081c1d07002844642080035940000100008036084051180000a00044a404c02d130054958101c5614000d000b074400e44079072031f00d0040d04030100380100200c192130303030205100d01c1800800254002d424071075290f03100c0c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293791285 1250 293790035 293790047
    0x10b0d0902131a100c0807020315010b03100e0402220605040219170f04020d080906070c06030f0b01080c07030e0a1202031516111c02070810090f0b10090903 69
    0x403400100b405401c05242c25103084264813504426944442085001c40c3e140d000d41500820001c0f0381500c5045800000c08030300b025214003c200e09010075540385840c1106c03103045891a40403c9032780600314180001030303446900400a070740041c0c0440c03204110f00a50300300039261039440b898100380f00107202d0407407070280d03045038040344500e440c1e2605003030300503400803200d050461b44a00c845406c100850014038200f5151a0000c0c0101892400d008034240000c0e041e50144000b1a80e600110000b0032040e60140108801810541c01c100071900750000043c00f985001017103100c520b000003600904050080403142e01104016005211468642040d03d00319000000b00b40d100c1e00c2031039002000043e410700854820720402604e1150b18800c9031b000e8580e000c800a07405598080c10000b00c48880c4201c0054078214181d60003000074610340b407500380c10044500c40c40680c0034100b20408020501d81001d4218003580040030b22125507903100c4075804058950098403640d4100840c00b010305a001c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293792535 1250 293791285 293791301
    0xa0e0907031506080105060f0c0304030b13030e0904031706151204060b1c0323131701090b0609060d05030c0601030c050a080a06050a02090a0f090609060509010b0d090213 75
    0x3409640881d01c64a058a0001d006d225156002004004240c2e4040c0108080d0200342c449000301c0e82460780307a80c0c2d55040803904480700f04901c24840c0c1d80f002810741c080d100c11112801070f501c412007818542c40040450a003400140304074541c16001c00e255450304000408601e80c070250031034442c181c811207000c00240540f400d07140d05081a824200c01d1078100c100000c00d00c2c3e820480341c8108883da40a0300c07100010301074615040c01c031034005c62024619100804119002c480c5003201541066800c4a030003060a020788400e038900138030f42c40040ca00001b0181c00502c1242d05e6000c0765103000c006140340700d10040003842400042450f008999000910034103991061154681da20f440b4002e1210180042c412461a40d010400920125a45600458114510b0f1305c0144c40c2503240c00c04600742400580c014103045000f86001c120030300302481900003a003c8610244020f51403c0005281580d043c080c010941900117100d505006050303104180e40c560203000300502040a00c0200c000301154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293793785 1250 293792535 293792561
    0x10918020c010b030c10080c0d0f020c0f0c10030513080406050a020f01090327030605071d04020405030616020f01141f03120c060e120702131103010504020a0e090703 73
    0x410441ca01d403802040382d55144201030081d4045800c6c0240450301c503400a000e01803e00170401924805820f41d000c2c50f0500c000740e400c056900c80003c182e0902c0e00308482c0380461540c000b42085849a03a4010f00904210380614020a543e00c0e0602c0344440c480851074014103403600020300050392600100a0100544982c0950300c012650482c0d55007a10780301200113002039450f0808600703c2b0016014030040710b04c49580c5210041c0c60b5600c038800c0f2041520010007003804e07058081030803000c7c000204036091003918154200b5103040d0100e071b601d500150640d803000280d0760240050360700c01c120f01d5000242840c020302c10190404030f0002c40e804240c50280004641c5150500c42400208020b4200d030740c4444904a1009840002c075040950342c0310807602c0907200c00002c1d07040b0f0020480b070900c40e4480d10280707903520060310402c4410490b108a4a10090500020304c60384000081568112002a14050781e1411400400c4130841c0940d81c0b00c9911680100500000507410350040102040c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293795035 1250 293793785 293793791
    0x90f061b0a290f07270918050601060e0303070501020711011403092a1305070305060d030804032105040507050901090b0a180e07031a0f010b0711010918020c01 70
    0x2600c40101c2c66640c141844003100c9540d010441036003098466551002240c54820303030b541c444175070464403450180312100d100d2908060603c1440064400c1141d2262244030103505c41c034007655031580b251414400c2c401807291104a4040030b4809000f04da10255100c2e000315074981079450601c40188102826600040d13540c0d45650100c440101105c0c020008040107001403981d0070002000b00c2e03006800089450b0750484000e10035125108401c5410210903c04a1a03191520009041380c3c00200198820011213101c0800310350448003280e0042d80500d410300d1030070602c604410040413035400c000d036018988010002403180102d402016140c00310f40904030341e40e803a15940181c0324501407603503100358902000c00103100044505440d1001018020807402c884040c0c05042018a51060b64051010713084201220303600ca000d1540441d0f410421100381d41442002030460145170001403c4004000326020180c5c02a0710f40c100602218035001c1d2822421005540650080300001c1c4203036003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293796285 1250 293795035 293795063
    0xf0c0501030c17061201020403050f0d020a031215030c080604050607020601060e0105071b080607090e01140111010b03030301090c021b010e09220305180a0308090f061b0a 75
    0x200c07a00520610303180036600c004051081002a6250103000f800c01c03940603010f41c0c0010b820303070001c2c00030340029402350019000105c107540080307050102c50a10401150011040c15001927000b001503002c034038101000141d141c10281c0105550b900c1a000609961074018002a00350300002d20b29204503c07600a4a0181d00c0360441a80d50b12428080d88010071112042100d00354030600107005224059500307441d0b6803143d00f080010b15080c1c0e40116805401890811000036045030302c100007007082054000b003540c900009541000a503c280504205802c040242c7d068401d4024442d064001070950740e80b542c0d60940300c40200360f4040b042015000c3c034002d81061620700e150764296034106841d12020307a2180400c009141400a203400c4039100800150b0f8126003800e520428103610a4580c146d441c11401170151000d50a441c5c464840c6500c0c00040c000200214141c402010003554001d608003440c0c0c001441d64040c00318204440c1c5890780c520340d010b170320004a07038401d64001c01a510720300d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293797535 1250 293796285 293796287
    0x110a150e0c0d150e0c181b2a011e020405040e01060b0a080613060602060106110607090314010908030c030610050c061f080f0d020f010c0e090a09020a030f0c0501 71
    0x100404003805442c1802c3c944020100039400c40c00c9030850840a0b02e44180c0301d1000181d4040c0040e01d0000c607144000308104841406815207560108100041410084440003180c080040d2007059140ca2101c91300046059034250409500501d00103075407040a0a10001c03c0001c0d0040d00c94284101d0400c0484035400c901072144900b5526002203403441d042d01d018041c1e131004400f41c080c54000d41c0c080410701c4102181e01c24000502000c0e405009503514220b001498039079036600d4484207802c00c00502200300e40100c502030071244d110b604401c944409000ca1801003410310701c054241000002000010403078040210b02c5107004482c81c105106501c2002c8034917000e14108050342d58000720204051007181c0300a00703034650005002110403034440c05030609140c4040e0b11031a15901444501c9401c1d074041c8000c54401d00071078002c0090717403907100e001840350b0030841c0300b00d01501d5010007041d84032144c1d03084032151036000b805441708a0fa6916280d254480c1c030420581d000850020013040701c1d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293798785 1250 293797535 293797549
    0x3010212071206081507141c0b06162307060201090c090b0108181912020c03460c06080106020303060d0602181507061505060a110a150e0c 61
    0x350360311500400b46205405d490491421020308070b9400d100d4042522404443c6410040c60f003222080c03211a40d140415038001e0540d42c820600702d20414090007101701c040180480e00520300d40000140c11207070134100100240303203081261902c0c540680c5402141c0c0755015000944031901c6815000c011640d034802d69000c842c00c408280c1c1c002603840d00441e2112400341c00b80408400c2c03081c21384e90100481d14013001d9021030018201c1380f6202c0f12103d050300e25014000740303d40c444294007074070041001c40382515001c4e0b25030340300002c0170100c1c42021851003000c0c2603c020007100c45207103400604a03410107000d08881d0340f09280c00103401000101d03a1074400310989001c0c82029141040f000b04a90361300d400784d000039180310f00c14100813400940c07580d00c650201030750000c84280c1c540d40d81307441d0403c8400d507442c0101c0d265842441c6641000380380c98040c00c60708012102e00e4111003400350703203c40c0350404402c1103018042c103164810780400701c011540309844c0074110f641200c030900c6481c1c0500c050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293800035 1250 293798785 293798789
    0x90e0901060f051018030609020f030d0203030c0d060503010e0304080714030705120c0a0b04080c0105040e0408030403090806040b070905010837020c0303040303050903070804032003010212071206 86
    0xd52407001c0003c100e03d0511307101e802c02c1c5074a54101710354805c401e10704a2040001c00c0e4010b48100e074030f400320b04040d4100703598054481031040d13000c5c1c203140c1d001c80c00184d940d1201516410044400051403040c94599a01c03403005030400800074851a0300220f20160703203411034010b400640c0103291000503ca4070010b401da0140b40e000c0c001c0e0095615250030082004500320000381180611030f4032000ca9035425540001420924144613226410035200381d240c07850798407600d418400200310078883d100444040e25441075001c5802941c0c1d58071032808845802d10ba80c4400382c58850303a424442002004a0b02501c952070b01d0341c90310311a542e1000110340c1860240d4590510420705041401c4040c0448800400e400901010000d00965003505204980c0300c465100c1c1e0982010082c8800c06616008040d00302c20091b008504100d440c0e150702030544541c6c40014040d6030540c0c41c107541207000f58100d5594074801002151201c00c680d040b03980424003155a00c0000b4904180d120011106103e1001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293801285 1250 293800035 293800049
    0x50304030b1e0708060a0312022503080d0902030c0d03031a01080c03060d170d06080c01050403020a0e072606010207080d0c0b0a09080408070e0703060e28050106090e090106 76
    0x810341c540c65401c0d00c06000145c03a0a80000620b4008408902c0e890a500b500482d290700800008155000b00900070300fa07400c40c3c40c14042d075240100081901201540c00c0c5510440002456001070b00c0080d2611041b1940d03150000d2000c0001000d05815078428a094110a248114654854001102c0304601107859072001d0000b440410054108100c0d02448a0312450700a902a04909880300041d0004c5240464081e1a84810f010680007408861042002824480d00b071600f03540c000b03881d846280c000d800070000190001204d00303104240940c130340010b1a8900d05151064001e040b114041145c10364003501c20840001018400050b00100c060301694032810080c3d655601d480c940c10000d0b150090651302c44081307001180c2450010030081c0700d00030040c00220314000c1d10081c2e00d24000c03c1c4c1404d26141810801c08007501c000a281d0212580760b80e8078004400e03200c005001e680060011314028608800450030a402161b0081500c022004004043e50380e000f056007a52907078060f6030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293802535 1250 293801285 293801341
    0xa0510030206040e072c03070b090607030507060f0c090302031b011e0311130e070c0807020405090114011403100908042c04060f05070c021503070318050304030b 71
    0x403000709201c16071030704003e170f91800e00100307242d000f0003060400001e2407143c0e0a424000b01814149401c100c0d0700d00502042a4050600c0ca942c00001c90070300880034090184a00000e1841c108080b680c440074003860780c00b104122039413194074010036454450000701d000380320b0300d0420480f07901e002440c00d0800c0070595505925183c8010036503070741108140800c0c24151100780302c0040c000c18034007820503030072520500c0d25258500b00842c0317803440001d00044107204141d02040082007070311080790b0f040c90301030340c000c5416240d14043d240185402141c40d107208041000105420110100d0f285000724114201d4070444400e052079401c0342c20800d001884c03450100b201700210160300115100003040c000346800c1c80e819500001103034190071142101d01c03590300d11709034400d060f80b486095046a981d140842d045041a408100d44c46c00c0d44161350350400c4c0c0800003d00c07982c460340281c0800320b01080014011601407804d40da580e00140021240c072240140060484c1c12450380d5800d900c80c16501c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293803785 1250 293802535 293802539
    0x313051008090a112103030717040c030305030717130201180b0d0b0d2018040201051b010e0106031a011a070f030e0604031a0a0c0207060509060c01050f0a051003020604 74
    0x111135450144022250042490390119280c11a180c0c10f01884400c41d40107940c2e0fa15014000526103c090b0b9185140b5608440c140030100307080c07050207400d40380d05080459998541c0c0f0070666001a4680340100351205a00c10018088141c10741c01450764801e0b01e41c030221000600043c5000700484c003410907003800a010003041c04005820070003a90402400c203504903060381e00c541d111014003c080944442221140c801e103410000920342a00c0c10150030b282e107a0825900081c00d0f40304050800c088080100c6000360040d80070b40c01740c010000410000c00c202e503641d1401c00c200001d1071020107010b00050000045a40760103020000700405203400d18600101a600c2440010605000740c00b0082408500100303078841d00010001307035002e44045d082e840382a405007545807000500302c554850030502c84c026465000111101911414105107843c1e82c0c031000401d00a020311811260650308040907c9400364100c09100c0c00340e034070703a00c1c01d0100d661f0340003403040800da4070300c0000d4001d60100b1003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293805035 1250 293803785 293803793
    0x30c0d020616031a09040b150406050112050702011b0c06060803031614041a0c0d14030a09110a0306020901020f01111c090f030201060816030c0b09120313051008090a 73
    0x3c8640f000450505541d84140c1c0c00c013017800c180d8202c5044540301d6910090200913903250072030443c80c031000c490900102d0b0078000020201c0100042c002c030340d646c80341d02040b0365a0003074020000450100e40341603000301e6000c40040c254600c8e004166041450301e04041520310002c42280e10500c0016a200c0782c0f41d494850445100d0428140745544103024171002c5190703e8220100d075510f001c400400e640b102c0f03000408906041c200c0140d60300b030201281405001131108425203502503c40900011000900d00346072100160340310ba0240d00140d903500110400c806540980740e804420f0342112009010711417510308030350b401c01c491079003000c0900800108550305c0900c802c040415100c00f00d070b68a40f6907501c0380d450724001e00c11002750351503103014042e500c5e0401111aa071003403404106081031854441c3c0c0d41e83c0520b4001c2e04641c640000c4c480c3d2031619101c0641ca01c800c02d50044176511300422000201c2c00d015030040d10700ca41d4070406070310380191144190706d029104030300180940c4441c907a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293806285 1250 293805035 293805041
    0x105060703051b010204030b01060503060904021e0603130b090a200409050f1f06050915010e0d030c03090603050c160201030e1002070b100b30010602030c0d02061603 73
    0x180c2101000030401c40141c00480807598684003112180000d6290340c19841c00b011003c41c16080503080003014020401c065840101154000341c05070f9101441e250110400803450112144068024a00106110401c1d40b4000000180781c0510244101038440021460b202d00304000080c4c80540761401e03500c07c2c1503655221a00f442002400010381e0005540c40c1c508004283d020500d054010000821251508092440d40b000b03e21100300001401c100014801c460050112054104603080f200c0c2c035a4000d20b074403100f8803002891581c2c0c40c5880e2500074520060800c0880000310449000500d640c000d0040c0b500440b40314401a081c20101d0403061400d10104000768100341e110410102d040e0340612080610b020070308170150340d56486003411420103001408030001071a180720b04125040001083c0d4040070011a4510080d17401020f1440380074040c02d2880b400019486d000041c070640000040000080840c10344610320514a000da84504d022105a001c02d04d01c4003a85001138800d0f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293807535 1250 293806285 293806297
    0x1509100e0a020d0f110906030304090f060b1b100c0f0f0207030804080c01030b100915030e0d09080c030c01080c160605010f1e030203030a1416050303060a0806010806010506 76
    0x60485120304482d03000503c3c08100c04030280c40d22810a40304c0b0041c0070845030411100c144c2980e500a80d403d0000200707aa1348100c2c4600c07045642c0c1c44502007100a1070b50011401841101ca00300d0b15680c110001c11000b002c40d90038948a803240c4c1e05c1c1e083e580c03201805061f01e00002a02c0381c01800d81520300c281e52090010504408602581b1741c00710009010901600240060300000d00c60203101d88005000c80e0716030319146201d515141484c01c4902d138014504020b40d20051480d9041410781c0740198050421a4403900b0f550080d0310307120421940c00811030048466440448130090003e00505131648451200d15002541000020b075807213544100410031120100318114000c2d0907529084101c0c0c000f03811901d400300c07141c401000028040c21445c4243c854a00700a8090b0f4a1a40025a0703031103150350580c01d00c48a0301d89985d0001d1494103a94002d80e40708d0480d80c14201503d001f6403a40c0c0100c50f01071183c8001d4002155400000030360380e058680c0e00d80103140a03401c000c10880250440b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293808785 1250 293807535 293807561
    0xb010c1709031204050f010203030103020d1101050c03121e0411010516060912180803030114121b0411040b07080310030c15140a080411040f0914150910 67
    0xc1007075880d65201000003584031a07000101c0c43c1c03078038242420400c260002040c1941154001c0c0018409070b42d40c01000e4070a65441201101c280c0d50100060728a8001c01e05220454040822800031008034034076164495008101040020000b803014216030700019100900001081400e024042d4042c10051a05c2101091400c40d054010340d00c050940704080c00c112048184454035280082c4c100c00c4080c444280080d81000850501008640c0c2e40414031803240e060210000315440b0382c69600400d07005003509001d54030380500b00a08681490a00d10469002d02d1400b01d8803c070f51a005800d0b14281d0f07400d100c00a103021101d40f1440981e410242450000700c01d101000000200d1400503000240004886980e510f58944000350410b000e4800002e846003041008001d01980950030903030082d408200000225002004940100114400802e085240c103515a00b4003000c0042010910904001c407804803060390394040d651501914540c3c12688548051050842640c200010040c85 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293810035 1250 293808785 293808787
    0xb0a0f120609060f030b0a050403020d0311040504110307020606060405010f0e12190b090105040f0b0406110c160504020a020604031202090319020f09040804151b06060512010b010c17 80
    0x403501d140c4110f9900d40d200480448106000308100701813106100c1c0c0c8008904005c1003280307410745004c2d403181151000ba0042581d102c3e010999940300c041994007400d00074000b04881001560405c00a0b07100f50f80000c0540314420014241c2e1030100111415100182d480000400e405030054400030441241310341c0c440c01503603002681e88800c0000051160b850040d0340400109402d003a4140d01c0050301101c2170380d041500308000304030054429004075a000e840081a56100d082550003483c040c5601c50f80020000703a044040040010441841c4214006c0680718070358540801c822442000302140143e0003940c0040c01103402080c0010b140b84402e4005480e0000c101c0020341880810002042c8054000000c0f03003c0d0b0806501c004001841035401d000181002d89904829000e14850f88945e02101142e2110462040080c010708146078480a132084682e07180c80b2002d05400e0203124000e0128140851003618140282c0c81c0e8031030113842e1841ea1800c0c80e240c00114a500440324088403034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293811285 1250 293810035 293810039
    0x105040618031502090118050d020f010302071a01050a06080f0610050c1204060306080a0507031509020a0b0c06100b030c090d0b0a0603140102070b13060b0312030103050105010b0a0f1206 82
    0x103001001c2c00d01d43c0c0410016951004180090011610382c0304c25107161010704800c0c000741c0c540040340590150100c0d400507a0001d42001200a80300720a00207001d00200040e0400a000c0c9043c958141c42d02280c1d074400da6511491b0444109100700c519049422001000c2100b038105490b0152220096213006840c080343d4141130b500c1c02100b140141d4107180700160400c8503c0e41817084501030100c24001d811083c1d0581c8489541d00010701010346002e00e5084010441c007815880039808980c06030500f00601d60f907985c00206c0b50800ae00981c268021540050240c402e4855018140e548005140c0e085440d02d400030901a0405803e03160841500c10b0300b200800c1c0e4000041748285c2c4007040100d1b886d820741c60007207052600542912300981c01801000d0020b0008440340380d04c56000826205401c4050030060050161031440a4040c05503080d01c144145101009606a0b8050702c02800666603c45c1452003512402040c000013402c59084800554445d5000c44050480c1d080d003c20301c0c607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293812535 1250 293811285 293811293
    0x5070203031902152422050a06050406061709030a14090607060e060405010b030c0a03060e010914060a0b10090306090317070c17030628090507050a0e0f010504061803 73
    0x1c03206a881105071780f03014900c00054080d10403480e241100980e1540098201d5007103a030f110303500e0444a2072801d0740780c6000450700600c9501200090000620522040e99030b0640640301410380200ca0107010364140004410950010840e86c04a03aa0b9540e195800008441c51aa076003200c484c19a1103181006180003240b41c0740105000405068050200746c2424540a42182c2298010318080d4005290f43c50060381c80b00c040e10300301c2e030b00814086010703003c481d0ba090046c14001801440c138502180703140703413221000170380310b21803080c43c5010400c21514200f0040c0006410f040e0300000f5000150a00000300755400c160720683c4070b401c1040101900e903219094210301111040e0004440d118500300b0b03c0300c5203a6862141c03158141851035428400c0200c0e1b42500001038032842c0a603c42c40005405003103000d0140204065542001681400c50005140d40d00403440000050b04600d00b00c90149007080d038400450078140c42c1e031490640b030000103541c0c04111161041c55401036107000000310b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293813785 1250 293812535 293812573
    0x13060c0f02030105011d240103020a05070c03050604030909110301140f03070e072604030c020303160c170c030c040b01030b030a1211071802070611070605040506060105070203031902 80
    0xa42010b48200783d0403c2e0000c48124601c0006016041f007882105800381e035480151403a02c19a41c1c01e103000341c0d41c2c0c00216810f940c20321580200500220069400005102010034090300880c0700c2ea6402c40d206503200d10701802d54100c01032422003514200b00402005981811080031100040c1040c02c4091b80d0070002420f042d8940e100e424074222482c1000059984081c4d2a2030081c2c440d03100780300c2cac0c10708004d6580ca200c400410050512003026200e40c01d561302003050754030000910f140c0540e04c1c620380c6000c0d038078566a84503002d1400742c8c040401050201c08284019071100c081c00408509101104100c0a00b1941c010317103050603078544985103651400d00c00034000078041e0100f2000e0a0204500912040d80c800441246822100007480402c080d801842400401c440000d6110280e074100324004065560004004a400141081c00c0040541005214601690582d8115a50000150f80c640315200c5c2c000d600d90010084c0c400780410111044085000510441ba2004485461301c405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293815035 1250 293813785 293813789
    0x602120f040612181208070216030210022d070905130204050612100b0310090305070f1a19051b071401180311120f07060b010c020301020406030b01031113060c0f0203010501 76
    0x64052205081c40469000f011b20b035040b02c00c2d44028990102000b03000c4a640c5488e00009102c4c0322100b02c260319042c0708100300c940f00d00240e8071580031441c4051461000030121102500d46020780e42001030800550f00c0341034401d8a00c951107003045030296003040014000108510303030111091501d14641502040041c0300040c02050000b018400c00d020145040740c1e000c280d00d9540c1c100300304500002d038414213451543d03620100407004541d151402e05410703d9492000f0740e007100000d00300b014844461028041d8000900020000c0351107100c100f0015201c0d41002c0008a0000c00812002811111450441a41c2c00c000020f0340152403030035000d2070311109001c2e800900c600c074540d80c1c104020710180704042200705a040c0741c143c2c41891420b06000311f00002d06129900c0f11901d119034000c54240c07d1b000e80c02030003155180d8460710301a000709884250360f4006132034100e9040c0e00c00c0c8a14115080c104095500c10000740c60008121020501504120750090a0740301110042e00e00f406a180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293816285 1250 293815035 293815043
    0xf07060e012c2d09010905100302010f120c080406051602121305030a0303061a070302120a02010b1201051b0322050a0f0606090c02030310030303051005190602120f04061218 76
    0x5400f00080204900648103070080202d9a01d0320f4140462490510a25030450381d082c20020078074075089405607100e803403088501290a040c8100c83d4199031340319241501c41d51044504000303640712400380001000400000030f01591092808503103400200c00681010150700440c00d200d5900c2d0000700b41440c0c824181140425110074090200001e06800c0c40050038412003c6401d10b034540d180290341c0e01800051908551000905501c4a4070070b41282c19030000290120320681d100a010782d0081c1800c6030100407420300c3c03180b615400b80e03520044130300901c03101782c000201071782050642d4112042c05100b103c0c24441c0044920000780d144400107d00381c0900c1d00000d4440c50540210140c95600d21a542150420410003152900d01c0700d22400783c03078061500007001ea40710110b20703901c0e1109070030660340045c001a907041024030342c203281070980340380b9801d45035140d00880d240c10071400380303105202d4001410300c03041c00803612418130704100c4c21880e040072481d40407900c610b001041c154903046c0e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293817535 1250 293816285 293816359
    0x170307020102120a08010603110408011b110727180614010608070815010e0312030a0b09040803010317041203020102130605090303041a0c0f07060e012c 67
    0x10340d078050040f250810f40c1c10480038540410000300034800302c414054402816545d00035500d40400d43c134241d6010b4480c0074003c100000422420030f07042c44402c90303100d00040c1c101c060710382901004902842200e280d4a0710740c0a120880700c0d00c03c083c186400c404504ac03070340c0d19140c20751012a1040707001d40d1401010005804101007039203401090f41600584240300042c070074440c120341d2120140f035106280c0300c10911580d1170240100c5004000d9040681e15124070105148141001e2008500901024208201181c0480c0c180814044111805002490f003800104003003005072240040040000c26694a0b180d16060385071004006000c0a41c0140c0d0701041c0030200440d0340600c80040e141c6401c1485c01c02c06c01c500003903030382c0c841c5002d4040b156504a1025040c00000d106445922143c40252020343d0400e8031043d45d030300d035944514030004110551072441e65006000460205c05500003401d0b00c510b4848040e180e00e01844082d603000124800e042e01076009800585c0d1450b8440c6880d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293818785 1250 293817535 293817547
    0xb10052506090b010e07020c0904080c150c0904050105030a0f330203091005160c0305090901090b0a0b090a0e040812040302010501080d030608071224291e06041703 72
    0xc415505c200420910955009403034001540c4d0b03134103d83c03d030b0080c0d2150307034590399100b07141c41c850a241141f213842806021010a0043c50105040a0a0580d505580421280e030760b510030541d549a0040c400b8024400d081740e00c001085d03e564903000150381c0c5444036112440084000d504a001d80302031420020303404014001d070100c0521454101c0483d040e414801e0b030411550550b451039404440105101da610350050415000350191014510003c2c04505650380d40c0450b031000d0030091a11603c6080342c0c003000305403403102030260ba600c4071003d0800752005003080741038440100043d0040d101082c040c04106051185040d41a00c507610a0707001080c9540350120041c644071103101d0f01c0050505002041c0301c803041c0012100d0441e14030350719940d021440e904252542c0740040241e08552400300c4860003001000d60010744041e40d030022905600c07100c041601400c003860102c026401071080c2012601704e803442492f40320150005114503e00313a521205030a00c4100341070000c40540012980c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293820035 1250 293818785 293818799
    0x608010b0607081e070c0b1801030c0f120e100902011e2709090c090507020a05030d111308030c0c0f0306071d10090f0f030b07050c01021603120b10052506090b01 71
    0x80041c00708e02801c0c244009064148041e1030000300148075410070003140c800e28110200da8000c085d0744144041500c10182e180b100e280d003d05803200050b40491071a059100381101c000703103038141e0100141d41f0406510300c0288124504070b42c000202c00032605c0c050b4023169411841c4a030b503a42910450034180002c0c60902c20303500351040102081c0641d00002001408a100030007181e1200918000004002a42d000c06044d54000c0454241c0c0000c030a031004079052100200810440c259481211004000d240c10408240c41d0071911907011307000000403e030220702550800704103190260900300002c108a01007400311092410100000d141000700300500700394400208040d2001c200c2e03030141e07242551107000040300c2c003414040030040002040c000301c48080d815506803065402503c8402c0d86542070041140c265088904030309860403c0703a809a00e40200301d00d10303582680c1c540034245640301c1c401140318100120090501d2103c004402c0c0020510301c03480890781c1c468a4003460550400b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 293821285 1250 293820035 293820067
    0x1050627041107150209010e1908060108030a02010f020403021804050c06160b06030d23071524030210050a0306030203010c020106060807080601020c13020d0f0608010b0607081e070c0b 81
    0x1c02d006644100102d0b10380341d07030041884040408c00d0b502c03c0a907810302e03103c02c01150a42d601401040c0618800400ca00314040000d20082c00785074001d00c40c0a01c00b02c6804120312a5210096111900d9050b02c03880000c03a040e01172340a40603c00740c50001c86507101007241a400600160200d0341405a0b40c03040040300910b02d500103400f68001c000301103400c04040d121070031300b503403d44c540841600e124003c040c0c000216808254000e81030000700d001a403a1001402806035003c3c1c0d030300c1c0c0030f0501c0f0010000d6103411800b26034000b4140c5203640c03a04182903640d580324031040800c043e2242d03c08070250301c00740582411240c165000041141c50f051008105180c040c00c44002c104008060008980c1d0015041d04038041c1214600304410010303030b8560003445183c3d603260206041125100c0d100703880303034080400c5901e01c0000307000c2841544204411442242c0c03004042c1c2d2411300c1070700158440c000791008000c07580031040e072a001064650300400ca80951040a02c0d0400003047c0d0400f1030424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 293822535 1250 293821285 293821313
    0x3090a0f091112011a0712020703061b080106050f0d0e0606090714030f0c16060527070e13020312031914060f011b030206100e01050627041107 63
    0x11800c0c100380e0007980043c0d5222040c8135891001d544201e40c400b040541d401200c6d030a9901010030f5201c90070031040a501c40c1c17400d10096610514100c0a0744640c084451003212400c459940c00f900c50f030a10400b13031126005000302074003d01c014480d9010201d0f0303c1c8140200303080428001c04491410804224400740020001c0301000031603400c201c0c41c0710b10b200036603810442c084110022039440000d1044503014810100b980c00e00001c2141051080551115000f54480c0c089003140300c1c07001405403141c02607010aa4155801a0402c1000d104d03003448440c1c0169011480264052450300024a0490f2540e40102c41000010901c03c1c1c88600d980025015180070b030051092400110b06460358403401000540501e00d08000f10701660f11031207200b0a280b01360704102801c0391080c24003c1d5030741000c8800140b4030403040300c0840d2000d00c030011203043340c00040c800f6141074107409001e4204980840fa10401c0c50005150051036130b918080e03480100c01d69020951120032604008990000030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 293823785 1250 293822535 293822561
    0x110c030d0c060e03250303390509030307060513050313062705010c020103110d060305060f04050a02010f05190804020f100e0f03160e0f010f050a150203090a0f09 71
    0x80040901c0621407034026004007141c6a5090f002c954607080030b030003509034a0250b00c07040d181c000e14128012241e00480414980e48e10300d01c01192211002643d070382c441d10b46420751680c800d020038800141e06820607580100000149207141d64250307034943c40d43c0c0010500e0901070802c01c03000e00c902c66010611400380300c40550343c81c0e00c00c2d00c0c80c401c43e0404119030180d141000200b001c000103590094105849030780590be8044e59641c14070700b150b4000c103058002120180100360101d41c800c1c2070365480c1401140c0042c00751250840b940d00560b5800015444d481c28800c0a2108200a00101d50494007150880d1241c2001d46400e10400000b4188404a2031040340190034601010380c1c0119000790701ca201740c4a207515603181d0302c00030b0300d8030701d031070307032000c101700070450011419a11001c001c500400d40310365948d035a0390308e450001004100724000d1b10f03041401d4107020014bd00c200310383c4410350b00c140c4c010f4900c0c1a05201c0458140e035410780100403603003a8880101b02003112481100282158 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 293825035 1250 293823785 293823787
    0x305220b070b070c02030715120905070e1b0a030b0a050d0b0f10030506010b040603050105030f030a030209040f050405061015200c0a09090c050405090c01110c030d0c060e03 76
    0x18451a41039078001d103080030345200300480000f28100c1c01a035800960035001422901c3d100c0c0d5940740c1841c52007103540d6410004d02c61076510a0b1200c1c03c0c0c001c2d14030f81035010029205290400c0304d40e4507403007001480c1111000740e00c0c107103554041000000309280d21282d9400b14801001030280048c100c000d60009000707001c03004190011440c00050f1035000402201c00c0310190311152a40d0603011a03d40000d4074a00990000050001451000b13000321991a10184942e07030b81c0308101510782e500c0007603108890f0020405d0303003407640c0300340e00a00244070001c000140d080d407202c88010850f030048404440b242d001c0002c0c0012000102c41c5540245100c56841d490300340b08150040a02c19445e44c00529500180c2c500c40f02c0200900a040211501400780d9a4079903464a00ca070191880038401d5401481c0c0f02000b26090800d4000c0a1240700284010802c003c0305200440c0d1503503842d41c2210b558018110804100d65050110762070b941c2c141d40c1d03500105501030030080304803181d80d081d0044540c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 293826285 1250 293825035 293825039
    0x20c0105130f0f03050d060603020c0c060c1504020d0c090209180603120702040207061e0606050415120e0d0f0801050901030c060f020309030703032a0308060409060204080109030522 80
    0x3054009a400309540503030226250b483c1031030160f509002d40a214810a410a500854580da05034040c003039030619407040310880c0c0e108209108080c842c408101d42a43c001d461040044414001030a401070f2000d8504c3c003140000d51942c80c0301d0380483d088090000d800143d0a405450320700c0101060b1200c481c8038031030390b09180300043d6603040c0c21540c99100c05804030b803a00071340d604c5a060342c0340160030240a209000b00c0c1103000b00c40d010310307a0110582c1440c010007c52070911a1040d40c1c00d91b504642081011f0070200000c0d80d2129500100c0d54240d0348410031000c40610500c04010200740343e8440245a500c1300b00b01900089050b00064010a825801080821000c0200a007122070504104a0355494040100d0651141c030300c01c42c3e01446103020020130075902c88804400180703041100070141401ca000d00e06003142c4c000c1c020700001c2c0030401081091901e0760045903110b128000041c540740c8d07030b628103900350b41e284201540070610129034005c01c1440301681d81c180810050b494800e041c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 293827535 1250 293826285 293826293
    0x60709080615010c0f060506120312010509191b09090203060904060b032505090906190e01021303060b03150106021f1122060e150c0a080409020c010513 67
    0x641c000303200e840b40c00d440c01c0e0614200e034002e462a4a40c0b6802207031462020282d410040041e0005660304c5000741200c40302c1d03407000280031090b1100000d45030020600d45c1d05c1c101c10440b0401014114060125007000e2100b29580350b80304500031220030181c0c502d001581c1c0302c805001da000c02e50112042d140100100000d60b501c1c92811039200340d004000182c501040300200c1e18011074038200040098070f0744038403103444415003c010111141194a140c0300d5072195a4143c1b6158140c401080c80c0c80342080f0800c60b07401c1d41d0008000980c0803400142041c0b03000d8070342107114180d54000e41d8125565481c03c0d000f81002e0180d13502044510240d0401949419130082d90340204850440d901d0240c02c1050942d802d075070700501200000e10031070f2901c1703d04410741e00105250502c0c055024603101040050003a00070040301c48503900007040002000c211025452680e841003850040340e018807201000010f001130050000b403d10301031300680340c410307407041542143d00160141700403849400311a0001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 293828785 1250 293827535 293827543
    0x9210702011b030509030d082202030c0d0203100609091a0609150a030803070509040b010f021e010f1508070e060607080c0a0816031d01021c050705011103040506070908 74
    0x440c407052000707801d40d500e820104d40600805044036031600450000701c0d200380e40140c40320301a80d140c4564141c20500a0f03209040420481c90003074140e0400c0e000342070745181003103506504900240944107800740100440e0304441c201c1d0000060300365a0501c040503c0f2000c40080106900321041d01c07824100070380050b803c2d140003441c0400201c07031802c141a26031644403451005692000c00c2d540c5a0800b01d102910310707001107070710300c2c0280e01e000d92075001507108030b00308200d86c106074001d01a20052005054034401042850294564a4070103802c8500c89c030384529030a441c1100407540840707041280c07141c1031800b640d2005509007951018030003290340b032004903900c1503400007101d40d5401160101ca401c05141240140c0000c1020038110b207074004041308014a05d100782c1e1000d200390b42140f0303146000a40880110f0050b4420290503540d4942c65454040780c060a0078901d06002c0d2a540e85401d4460814922501760004010f12007005410000d050b000589801e10781c15007401c10b00c1c80d95031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 293830035 1250 293828785 293828807
    0x50f03130b180306130201031401050603060d0201110a050c151c0209030f07030b0a0c0305040f060203130f0c03030e12120f0708180901050d030c0b04080d02030921070201 75
    0x601030000b00d42a4000498250340300d01e03403029059641900d040b581644401c213403200240c1c0802d051251100354041031a110a0507a40010011070850300c0300424440403000f000c1040341031002c0c02502004400040200c0a41144148010a01c01003e003052100c54407442d0300782280f800c8180000c0307000e0360002c40176004030000c2850050700c3e4003801000030704c0c0c80082c08180185009100b0088240032441032a40e216001520090094040d1900101c08a40d0202c40203822454806410800a507147d002140c21058003040c0e803200315201e0702c1e2014081d801c0700041700c500c16503031000c108050704a1f000c0c114045040300d04482d800d00700710345103850350a010601d681442001070005807607044281541c0b403007030300403c565440340200a07100c00081403004041d0700c120008070000440e441c11001001c0f1440d45540c5043c810300e41a41c0300e01b0780703003c05002221001401c0c07021048000c501c5c17015620a8400307000410680c80004801c3c01d156840040301e80c5603110402c500c5025036000740c40544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 293831285 1250 293830035 293830049
    0x140a05011a041a13090509010c0207060f05030f0903281205060609090c0d02040b0913061d040501020906160c05010509210a0507120314090a0303030b010e04021303050f0313 76
    0x10f641c040c1c14204481d40600c83d00040034181ca00300c00d1000307e01c815401000304541a03001c5501e103584039042664120040240b04000030010400242c00c1c90a1001c06030b00414400220b03800c00003040041c0c0d0f603869072418503101e100100c000c0c0f00f80da1a844004102c41b410410f03c100302d03504254020540b2407260f0462640214685000b141020200c04201c80644a503c042151641d07110101c1e407541c4c2e0b0046484610540b0f0007115025004114440e82c02112110b0b80040c007034100c3c05500880c032a5005205071095542070094503620303100c00001303007108030010207100d01d400c030245040000309900703400060401000748100480f0f500e031207510000c5244044181164100c41016103440c0c902c0028004142d400303036410001b01e900240f606038000500c41d440d1020800241c440c00d51071801110107090340003100d40d070f0800100f4065400320a4528040c54846403174030260001c60281da00500101e00401c0c1ca40408006101e402e000c0400003216940141d484c0a06001e0394800f440401e0145d60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 293832535 1250 293831285 293831287
    0x305070c1d06011808240a060e1b0906040b030901050a0905030901050c011e0221100315140414010c050309070e100e0c0d111207030f140a05011a041a 66
    0x1c10000007064110043c5240006c64a107a291941e200b041c036070f13000c0180d481d200c50260108001107030078020f460175200c0e404c0c1c0115290784c4640c00110f1104600071259110711042044109a0312404010300c094504a148982d40381410403c842c21600000e0542c3c003114505514040001d402108a60310310809103443c0340c03616100b0555a00400c1c05648149072440c83d01000b000c41e03e9650041c080c90418100f51410004071000e06415140003241e9100668812103014000203c003600440140700b082c040000c0e119030302c6000010501e1045d50f06a400726034808982c03101c11001d000b8040b245c0454980340341182044010581c0d103910f00e01680039441c44140010b040601200f4201d80186981080100141010085030008d90300c1850540d0000c1d040503220042d01c00560220b03085103020124070800da584410040740100078103140c04010a4445810b5503c80103d001003c1c0184d2104000140952600500790604c14000c0741c07415810f801400300b0880c05014100c4554036007160394202d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 293833785 1250 293832535 293832557
    0xc0d1101021b0604020a150806010309211d030304030f020904080715020406090f03030807031a041a1e100815060a030b010801090218040f0e03070305070c1d0601 71
    0x14034064050602044226420900010482080000e1075401640255054030420740c0301c01981524001d90070b045008600b0380d00214400d54444c3d07104400c1d0f18003c0490741d42d50011b11807084060b11040d02550700041141c0b01c5440340e04102c2d00c4844250604800540c070300782c0f440d07850ba81c8071500720300041c4c45511400700140074080c014080b90b20703596105c810207802c110580d041100a42250080400260703a848010030650b01220405080d02c1d0151100070060352560811000b806140c0a904404500340c54003400035182c0b80281e6802c109805c02d4140011120f9007448440c00071500d0740c480f6590352809001c0c0c01e0b1128a45d00c03010000ca0318221038241e8802807210000a42c0e030340b000f42c00482c0010703880c0d84964198060b041002d0266119051640e03200644810f038012624007040e40001852000000d01d0075600610813140c010340085403004180364501c0c10b503005000150b0124034006900c00030081070a1a60003e010003d0b0b080c0c2c14800c828030301050240000f0a5103040c44161008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 293835035 1250 293833785 293833817
    0x130513060905190b01030b0a0504020906040b01030603050706020d0e03010506011b0f0b0a02030105090601020a121b06050414100c020d03020a05190306060f03090b0408090d050601290c0d 82
    0x54161020b000c4806480140442c90304c056a20b400344030568940900308081645907646003d264055500109841203580382c4c80c08100007030425041150500d992030340300000082c0c0c14030002c00100340d2a0081c20300e03104e5a05001d440e0300804540320b442a403610301003080980c0c0058000381940c40941c5d0103200c1451510b400e9442000110000d001c0640c0c1d0b104002078015550021410780e001500c4002140e01d924006a0b9901c0d2051002010341e180d80152480440c41088059409107402d1f0402d00a456581c903084100c0c0d00a98050342c0d5401445400d40c03203060100a43c4200101052003000140e00c4000025210390480e1030b50010190002040c00095100b482540c501d140c0800340580c100002480140080c0403500c100c40202e607000b014209818020701c0b8602c0d901740c00c1100c4101556444d42e401040303034481d00c1d0941c1c1c8041d4001513030001c2602004030034003030140039125812030b26044262030108003169294421060041041006100300466080300b441c5080c100455002001c1d51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 293836285 1250 293835035 293835043
    0x21f090902070606031109041a06010e0405040812060a3006020a0801060305070905031504061107030c0b1014040c030204080f0c1e01020304060c0c120302030702130513060905 77
    0x4040340c541030000c1500070901580384d100030f04807071154144503107104012051000c2d120003154040c1000481d070b0403c000641018106130760240c1d0500d0141510010b07000003804503281580c0c103a80c0881c001c07aa1480170004410266000441140d103e1a49841c100455480100364bc1005840010301800045c507914086000900a035000700c06648600044c1c03401058000244119030004e8241000703d00c801d030040c01c8038016610003a01402040d0084504021120350280c000c0b5003c990380c0c2546100c03000900054a003c1e403182e40d42c807440843c02d090290111001402405a00c5000300302045141c2540c0b0750300c181d004d030070344000c1002485460180c0003030003554400c0e0340e64041d400703114407559130104860304449001c0319020b20b140c2c01d500b0109404941900e00c00d0150740200010701c01240141204c00a40e0300c182c040c180025243c804007882c1d903001410443c05680042100307021468091603c42c240d82564208100c1440d000750000d030074819160010340141d680760112400d00500780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 293837535 1250 293836285 293836289
    0xa030902010c0c0603050a150b04120c0909050a0c060836011505030f0118031d0406180e01051b070302210a020f06150108060f040c02030307030e0703021f09 69
    0xd1110080c2c0d0340e41c2c13400580030306400c0701d180a000c0d26210054503154198080e20081e85c0a09120600b040d00f0846a00b00000c8030034000d440511013001c00080c044458010300c90b1547c443e80151400000d21310303100003004000d400ca0b0b02805070070803c0181c3d500b8408481580c0c841c502c2d032807640080c1d54005101e003422003454160029400d055445006200c00741c0b88600f11401901100c0c031080c03072202414201d600440d6450080d65114011101003849420000c42c5081401d02c641c80c02908040000c0850b06154800b0641d81c203801000304851405105012191005100a20591610f05a00074510b00c0c3d0111f20090900041491414544200703e040c1e13183e042849614445c3c011820280d9007504450b4024005101f29078020407803000c0800d4060140c1d8407038080c40c4000ca2090300644901c00000c1c1a15003000700001c00810990310f80c0192103003a140341c3c010b1656030034100001030070703140c24150989440d80131000401c016154422814100d0019603440c21000403045000c0b60900c1540d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 293838785 1250 293837535 293837543
    0x307170a0c3008190e030d0614040b090f010b1602090a0501030b090307050613060209090403030f060503011a0d080405150405040501060e100c02060c100f0b150a030902010c 76
    0x35000101c2c40710048110707030201030812442e0900111070b0340342116041012070b403040003911485802004a20755400081d40714031140301b682d04003d030010050b030488030300794445d0f1400498040e0700b0303440d0f003001c3c03084501e0460b06803120300706407600c1c51003c4500107041c868404465000106d00c00c008030701e805005219503000b40a4090341c1421000000904402e000942d60340c400301003ca80c40031400001c07aa03480c1d81c010060420307540c80850180514544203000c0d20015000c006a903031940c2d80c09a414400e91094800007a60980c24640c207084401c1c60304510300a80c501a00448900321241c48108103410855610702c41c40d2603860041d91074020f503404035400010494400d107030400310402070002e403101554200044e0b0b98941c0200c9041c03402650147c0c0202008941ca0203040c481d0554480c200d0000e0a190300d000300044081d444d0001c0080034030742c900d5982c40d07a046825501d009000c2c0140c01201c4146105854100c1100345115040191003132541d50005001164003030380c0c5000b4800c2e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 293840035 1250 293838785 293838803
    0x507020a030e040b0a0306050105030c01020f1507120f05090c0102011e1505061204050613030c021306030503041701140601021e0708100212070c110d03110a0f0201110307170a0c 78
    0x542c0c60318401408d800e0092505c00d000e400c03900b0180d94400611004c1ca205480002c010040001d0b0b862403564801034100340410240700034091031306a032802450f07492501250000740605d01894010708110f0f06d01c2d4000d0469042c02c400c40b10046030305d490088036038000c000000b94540b136101e103040d42115546c8602d030403600125855400804080c6010302c501c0c018015100b86513120041c0002c415282c0701d000b0003042220b1954000341c00e0034102100301c807242c00c20010301591242c030341038a140c11503844095142504508100d5901007030003100c80e0401900015042c80c1440c20020b51580e4440c2107001d4103d98180c0031023424241080014010101401500c1d4442c100c0b50004010f0340c802c0041001201414011805403440b66070b01100c1c1a030010070b08403021644208000c4040b44081090f0b00700081100c2407452004244084101c851013410440008a030610024250f241068000039181c4c00600c0440302050445040c1d6101011604400c2e9503a481a6416074281220782c00103446204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 293841285 1250 293840035 293840039
    0x60f030e0f06062e080402060c06151c080405040903180603060f08030901020a140c0312120108150c070201050706143c06030c090a0501060807030507020a030e040b0a 73
    0x30000ca1100e000302000d03214107a010311050400204549000e10384194002443d204c443d419100707010307070b50708148000e1a813490488074038002c23490708400359000c0441201980a40c04589000d480a41003007000d130500c170300317803240035181c0c200d0b58007540c4030f030f031f8002c64442c1e1241c010103125030000008101e5440001c81070b203488000c000d000300342c2030240d0064980d440e900820503180000070f4440c51541640217051081c00c40e41d40d100030b4a6101c03540c004501c150400406155801d100380001101e807040125119000601d00b20510003040c1e022070000d40000c0113010140328a422019400780d80014010380d81c044610048072640b046090181411b850480d055603034004003407100740034210705183c5014003402c001108850140450001e01a0004507910401094400301c100d0b83c40032000b0141d80344000c0040c042070311201d044900c291890341e146d0060040c40c0d08825001e03040583e9140c00c1099103000403000e591130b502c80c60701405201075441d04000c80e0352103801040715000040c00303030102a9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 293842535 1250 293841285 293841313
    0x31806052802090301060906152d02060f13021e0310050c09101107120c030503040602030a090e0f0f04061d0106031709062203200f0f010504060f030e 66
    0xd08140c2001c4d00c03035400d2032400501952540181c0302a0740d250003d05c540c200009100b80c904a1182240c0c110201040a2522074150f001c41080040340c401d80140c80c0c90710b0813a01c1c41c203405100400c3c914071583ca00251a001da00c1d030001c00e1104d800d103468440c0c91640c00c0d0000074030f0000c88402e01504541003004000301d80344000058070301041d041d0350f0b011150005020607a00d9031829501c40c0341c1076101c1041040b0f982034058440c84c2650003024460078541d1280c96690031580503400c180d0140e400000d204110743d07484112400100280300b0014068104071142c1e03040c0150182c904440740400c1c03c0820148082d691108074034103041081416440814601c0398083d110030301c03040d18440400500007070141122011a030180c1d1000b4030140ca0000f40441140ca000600050071605c42070720400840000c0034031001d8a8801842c1140f5400070f000b132010171004518083c55240550281850400d071071743c0181c1940c050b15400d00300486030f01850141280100440c10600410348a5440c400c1440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 293843785 1250 293842535 293842537
    0xe03010c030605031009030516080d0f0222050310111207020609150f0703091a130c060c02031203070c0b0124020604050309060706090f0b0a0507031806052802 70
    0x464041e01515a03145d0410358110031a24001c401501088041042010600d00b40c405c4064507403107900a035040269070303051b00c01100c08031102c16200941c00110178003001e43d000f4403d500c1081740161203150a0502c4007180c0c46180c1c10186419082d00e030624a2612031581054980c03071151414116050304e4007081c002e507101d4040e2a480c045025880000801c0c03682c44050a03c2002c82e00300c0a5002d44440030100c00030001d100c407d0381c031403041ca68405040d50141d0784550190412106400ca00201c0f0f01380440e0380111a0310400034080350019040050f00d011805149820714100019220340d00c5040684071645440030042084c031916001103483c00b0321203000c4003103104031600046180c1040c10b06070307031b01c400a5401070703d20340c0180105015403a1020043c0b40b230b5440740a010810108940c0c0b80c14000140c594201d5145507000c04005900485100e11680700d020392809000741c0341c01c2c2b500b80d6604101424007402c088c0e11000080c08414545149250002d1502c00c00800d8560003003000b402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 293845035 1250 293843785 293843789
    0x9021c060515030601030f061b030b210c011101020903241b12091608030a080f01120b04020d0f03050403030305010b03100b0a110106120605010e091203070e03010c0306 74
    0x200c0745424045401c640d00070940c0c030703040b01000d00103200c56400c64507600070b52800080f00300c810903264543d029444031000e240321081c11042d00e0100320040b15004004440d01c00d00510742c0c445d402e40c1c1010640070780c00a62000c0c010003e003040080780c0704000080d8068822404131541511a0020720244d9940b05c550707016244010908081403034441d8403084041d0706070301440c1c05420344d040c8050f64102c95038405c40c075042a000c508451038071103410b030100c04e0340d5026849a459500085101c0c2c65481d0084a015845417004140140075810f1030810360154242d10000380562460710001411911000f9054120940042000a5a203404d04e0001c2865201f0301003100001c2c00e0034000640501c914050300e001c0c03c0b00750311a84480382000304140c100e410540c0341d4001c02546030041080c4110a11494014000c10040091101038030b00f4400169001079000c1400342c442070081258403000030910b00308821401d0990f83d5a505c504400311200c4124040c595455441c107170700c4581254050b031003c41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 293846285 1250 293845035 293845043
    0x1710150207050a081005090106061e180b03010305010e06161812210203030105010f080a090c0b04060f050403081e0d14040b07020102121b120c0a140f041809021c 71
    0x41c0703a4408507c1030030384945118400101d0700d5244505020303c0c400840ca0036505e12450002e1401a010351a10800d50040d40007845500d0000010b01c240082805a168440c8200004065900300307016440c0d0a215041308540401c4140b2440f200080b1009901c2d074010020802003a22000301401d10495240060a4000000010118416129002100f6039040b10f00584502618541c03146044e10070501c010719201146544404040c002060701315400050200400e02c1078507a03003820400391906100e20080d00600a007804204001013103403040303c1500000001c88094840e409210205a001d0000781a002234104148980d2201c0368a0b100c6207c2c500a1520005984526a0a9080b0b2040420a441032540000080d60140780c0a400700c0c0b1350141e100800303281c020080ba0b000c00e00300c0150f80d00103004000040c1000a0359100c81c444072401d10500381c05107045120070481e04648214410004084000110032107800000ea0102c0401a0040e001a14501c00048007444c0c01e02d500d40111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 293847535 1250 293846285 293846291
    0x30c030d0e0d0912020d051009020f0307050d1b15030207030311071a06030f010c0203030f01060e090a110d021809180d080603030d02070c061710150207050a0810 71
    0xd800d01d0750000b0480c039110324a4a68124090500480c413400c103042010030303a000b03141307040c0c204000385041111480d0008070840014030a10740784100145407001e000001e110381d100c4e60050103540c0d5680f2020b6080c550010510342c1c1101c80e58800065000306a01150444013100030480c0019015001070101e41e00c00c0e40c0810601d151307400a00014041e1110141c408000741400403040c21494591682200e0018100c0d40c007044119441c40c00c1d81c0d404c95030a0010b800100501203100f12820100d809007040b1f08010413030b04000c50105480000051814512646441c945044a1117020445806040c0100150354030030030b08031028030758030626000f58095860100060168a203040912070021403c8014260030685070b501110000d401901456050000704004d09001403284005c240707031440350203050300062800b2805881ca00d0304082090709d220002c02005000c00608481740140c07000100e00742d5080700070503422032420403541c10894000c1c4009201180119002486080e0702d81c01117418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 293848785 1250 293847535 293847551
    0x307030c08010e06061602062a150c03040f0503041508070305090d1103040504021201060f03020703020a02090702030c010608071e300b011d0a020a0e0120030c030d 72
    0x1101e400200348154140f034006078022a1141c0f802c1001802001c100b15401e44c0c0c81c1e44903800040e0076a000c102980c6081c01c50b4892651101a070705054401a06600c0190445c07070f544183c1005507000c01401d018030038500100240030410300d441c1200d503454004044984032a10b41488050281c0200307020f1001c5090b410008450901c40c0c01442d01c10070013880503240c00321600f001502c1d6003103030400301400c2d0300080c0000700702c544507413015000d50943c000031000c0039494100d000e0000605200c05004240c010807902c40480e80000d010340c4807542c1525822401d546240d42203095004496030b0302d0140d400c0640000c0c90660008049003034a49801120f02400e800c0220140300c40d581c3d00c1412000a400c600c1001d41480108031840030400c1010490b00d0300b100d85c0e41d900c01500c0242c101c480f03002d009210f61030303907190724401341c0b54040e006200440ca40b030722548014041e02030141e895410848001000614508100e60702004000c45004882d1035036500c608294690300100b5004a5281c600081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 293850035 1250 293848785 293848787
    0xc0d140f06061e10051803010f0209091e010b030c04030602031609121505070309120507030906092301050c01140f060406030305030c130b0c030706050a05010b0406080a0e0a080307030c 81
    0x1e00307603124000030b180e0004644d081e501501d0300d410441c9070343c0b803a01c01e0020b0011183c4082c059074680c50803210005a80d001d600e002c20a0140004d4501035280710611101007409074408041030541c2c920741d03c000d07102e60f00ea04810b06e5030b1045410080c800340c00801800a000f807440c500710500351030707915000e00c7d0607110103204803612600c10018007403240a03106058843c184d03910040e000f002d14074006c14819195142da01c5816400e0709580c1c00190700007071450034140d1024000025000c545002002540303804d96804000c05a64079038a8000d01c1000846100d0b8080e50841b07110001100c001d104401009042c0a0368040444840d484514a00c001a8040c034042c843c04069070340c0764482d83d0540d1610b6403002030a408c0409941055181c0d1000420103402a1000d00709000b2490011a61031040b441d200042d60009081d404d1101d0802005008141c0104d041c7c40c190380d41850618a00d54404070301b0305c050700800d20001c0c150b019840d080020301000da801107205880030b45052203c040300c498 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 293851285 1250 293850035 293850079
    0x1b130f020d0b0301020a0507300f02070506070305070230030d050f06032e020403080d0e0d09060e0d060203100830070503071b05030c06030402030c0d140f0606 70
    0x40301b400094410405a00095114500c0da2107a0b0b0a1110713450540d44c05d0820a50b00034840d556040c00f20701c2807803007034070740b9941049100302400051720400c1c1000b07103039600685107020304440240b103030f4003c1300b0400d01e145c10313815400ca145901138010032585090105c0582c59510800ca40050b5505200000c0c00080388090300e14000c4d03001400800c10524400a52000d04c0c0002c122048102c0c5400300044c041b015600203003000d03600071406e0ba540c4480d460096011900b01d642c0c04080790300000b2081d0046600050901c080307076030707504008003003032820f100090860076100d40080c40306101200384071224010420580c00d41d8148000c499201e0030410100c0304c0140f05c804411041300a0780b8480f6103190601010b0840c180c071400c01ca0b400d01c441039560000c100d000200a10707044850942c00c0095180810144854902c01e81d00a461810180c022030b4507010b035030f101c25006aa04405407020040344040c0c0c8107990039a20b05031480c40c0004903045480d15402c0d16042d10651420b8840d80460072205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 293852535 1250 293851285 293851297
    0x20c040501050d060518060c030a0b030604050d031509020705030702040c141804021902010902030606040207030215070203090307030f030e061920011d0d050c1b130f020d0b030102 79
    0x1030280000c40d4499584c00e018103c0140590440700d465642840d220b00c0400000380201d80040ca0a5241d1506401d41d078101d40104c1e4056110b64000c10600000ca034021884440400a600d000b0031940e03906541e000c22610f042c0c0c0184417280c4005040828810088094074445100f00e9040c0300c42200404102c501c000c0003e03440e41220402c000c0e69048000c080b1007650081c001070005800c125248544040d2181403450010160751912048404c600e018001d080c2c0c0b0080c100c404500303101c0d00d0307100256101103a01d58141d4041139500850032143c000c000741c0c0d040c1d04c00281101c0b2216180e01d0724240a126410302140410305106915500d0b260460544420400345030907803000745200c90342290000320000c142207458061a0308602c0c0c1d10401e00480c0100030131480003195510100001618011012094031704021080c402d402d080d00c000f0404140354a00308000b003420340745803000079411b03c000c502c40d44a0289010724401108100f030700a8a05100e0100d4104900210b900c280f40c01c1c1e1040d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 293853785 1250 293852535 293852539
    0x306010212030702010603021806040c110705120f120d050a0603020f040510030606060c02120f190615060e040e0f0303180307060e0309100e01020c04020705011515020c04050105 78
    0x80040111240c1c014080c0d0381c40320444c400415659501e80202e441440c0c03c11011040e01514030411031541480d015030344180c2014640450010a14081c250300c80d0ac0a0052034402ea582c1050305c892444100059402d041c8080d040c0c07038840c00c3c2e248000600f03071f119610000310141040002107a04060303109020489030040c0030315600c400d040d802c1100412005003a4010900000790200100f41c02d4425000907001c079850700e5080c18140d0040100d080c14454240c40254040400705032120ba011030302907000c0e46035000401d0419090f15040c00500035130800c002c00840e2011001840301d44c001140c041130b48040e501001500e003651007680e1190f4087e280d0b010503a0080001c5a0401da00384c0030307180c0310800b039000c0d44d003060580c0e41c0d19000d550403110030f400340303500c080f58004040c90441340511880b40d032814250b141851800020391182403140e1050b208a0307000c0785800503c04290070000207007100061001804e03898294408043c015a0030003c01132040c5102004281424494141039402c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 293855035 1250 293853785 293853793
    0xb071806110f0d05130b1c0b21010b120109030806060a020a0606030606051906092c07080103031d030c040c0926060609160e0f0315091203060102 64
    0x600030107403030411248440007818401c81d0301c5442020800e1081c40c10b4900070380e6a040e0744040e400d448400c820f26540181d2140d103030801208021012003c80300c507c6101da0070000c56244d0102c0c00244200020f18800300e00c2442080d4001c111000652003250842001c84503108265240c1d1503403800c035030458900a01091007000481e2051501001400c06c0c0c6440703104a40e09000d00d43e55541c1a00d42c194002c03100a92a0301003401145428144d00c0d4681c23007281c0d5108042403404400503c20003451203203182404018191075101d440600300e01c00c0a1240310810030490420805c01017002009201c02d40000b20180c1020032111003481001c0c1c3c45140041c01060300d035a081c41000010260000d4613418007560041c0025109904400e0a203021005400181c0c1e212229060342d04016004204501c1550120708000e8214110596403c01a40501d0304041c0d583c50040490400c3d940034100075858403810102d59050fa403115095841030101800781d42d50710008011558413404151280c50242e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 293856285 1250 293855035 293855039
    0x250f020d020303041502011a040c02060103150f05070e040e0c030d050c010e0610080c0105030601050301350d020c10050a050c0118030c020f2407020f060c06040b0718 73
    0x152980d801140940010162842c0035580c00b080c240301c00c2ca03c07a640303016035107500d00006000d102c8003500500010589080c0800b00c1c40181c0251540d0b03050200a0100310145850488000e03141e011494031003201c00c041040d810003442c00340010740d0003980d0503c035600b085036581c1900d00c04148000710300d0002c0d00518004c03010007000d0360307246c21400542c0c4940d9a10b504d4255500343c1001264000d1280948288140d41440c03015414035004580d41e0b0b06111080003485001d9038004200c038111009544203136000c03540400884041c24000c0705102c031076481e859442c1120308000c501d1401404040e02154070078210802031106404182c001e880c0410810b00c00028140c0c0600c00402c000204c200000a18006030081d600d1501c0d0f81380350580c00a85106404021802d2009014481e5a41241d48403510113690044c807144c482c0c03a11b001c1800c035001250310801c41d03c6a0384009400d900c024202529000701544103640ea800c01c5a0948040d5803080120780c41c80c0c0a03c041404841c4040140f1300564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 293857535 1250 293856285 293856289
    0xa0f14101a03061b03070e18150901091104060f0e030d03020310090510140a08060108030a08070e03060610050708070803040c0614090907090302100801060906050c1c03110f250f02 79
    0x30401f2035040d0001c4440b04241541d0b030907101c805104140c034052040040514500380a00c00e80141c0103181090f01e0501d440c3c1154568000fa981110343e180b50600344107502e4a02121415002c0b4141d94052060741040741d203a40e0150061446100050f5203e00c004c2d0f61100020180c4d04103480e02d0503018203400c0280200c81464200340c21a1101410040245642d95446031600704240e102d481c2940022404071a03d036130000d4030b240c0088880c40c0c988042652600081e403181d0303010303141a10540e08001d085420700d02403400d0760a90b1b41c11040c0f46440b2009400c2c01020703076200700d5046590001000d0040344d0356018408044c12101240807941c1032810040c14010258000340584052001d01400000165900d07000c4034000511544e40c03007095450050050071041054001c002880800e002c0707800700e000c00162000502114400c88104100c1102d0300b940200f54040d8104016240000c3c03020b56000c1076001042400e8240c1c0e8902039802130100c1c90500c00c65824402021550b01421400c054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 293858785 1250 293857535 293857547
    0x9010c0204023a0513020907080415141803070305031503030403080a0f030e06090a021e150703140307080a2309010c08090a0f14101a03061b0307 64
    0x808001e4085001c85100c0701e08141e001c054403c14a6000c01200c0a03030380c4541d91801074039003041c0080d4520040c81169400a405040002c22400402c1803041c009002d0201e40c940004a080c451981041030198110510701c1c000021206030505241080c00341441c02c8000040700c010540580c0c03401d0441c0c541c0802000c140032a610350540c180300030f02000c0040780120005101c0500700c0d48543c80c00e0f008a41c4003605032041c909076105550414001c02c80703c1803012a400b403003154104c5542465000b03207002c5040c090608003046800a0000101301e0052203100300420105000b42c45640c800702c0211026801c500c0200c80c804001064540400c002c0c0d0110b0304a2444420100a440c8190071800000c40b82c0c40300403103184101c0d030f440d04003890419401c4130180c0d802488280290a20700e50790748480d501d9005415000b0440c0004200c070744000803090041840902140301d081c005041000c0c0824103030201d10701d101d8428042da40c042a50b290113448994000100703c031881e411503555110507690 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 293860035 1250 293858785 293858797
    0x50715051209070504050a0603060b15090609060c060106020f10050108030703140c0a260f030705210c0409060501050307090e090109021f031808190c0f150c020309010c020402 77
    0xb6114480002c01d40d82d4841c000c1c1c501c00e17241c00c0000a5001d1650800b1810313150205516401010302c0f404c1c00303589089080071103d00c04000d4401c2507441240030f02040b0300b40708514200300d05000d20b000210310254040f8445030807140ba4003c9507200d0810b03007081011030700203201d0f40b0341036401002440300080c004e12011002ca010740c4141820071150100d401d00b06a1124401c552000c0c9200c0c598051450309803400a101d010352240c5070926140301c2c0c12150314400540719000b0f00c400416151100d88141c003101080351040d171450125030420648410142d0807a01410a80c10700b000c5012136294441c1058034403174078040c1d0320840a2890311310820200c0001510042c1c4554031004c5d05005a190607003e010f4040d002c1005100c1c030890840c001301282ca450035040c81c0683e00b0888480031542a00c1541c0c002c100051640c21031941c0500161844025404020081c0c643d041104080c4014a07224402c14186000280312141061008984a104480e1514007255400c080000035007440da0140c26 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 293861285 1250 293860035 293860051
    0x117040b0a02190f0908010e030f0d0e03040305010b0a0e040203030d0504030e061c0c0c080418090f050c010206090c0303040306020f0c030f0a09090501141c0b130507150512 76
    0x850401945810f0350103038159050729010414080d240400c0a5121003420000c2c94220020864101801c0c2d10949034880c3d60300c0c0c0c001c0d1103030100341d00c02070300f265a1240c1c01a15040d0704403543c4643d68030b0841d010301104080303144103554800c0001800a2401c160707030310555009014524013440c0044c044000c01c0048c02c1601082050614035440d80c84180c0100b4407a101c0c5440f80a07040c1000404200355105405105e08106280340d1141c00100e0348400c0d28203880c00c2480680e0410090010070008003409070380035001d4030303094005009028000c541c03641126070a80c251841940c643d43d200d81d540307000c888250740590081004001040c000c2c1d01400d802108181010701d0800a11401403654002c6d0707001c16294800051807541c1c0b2500880c0d0a002401e04400503c080c0d1f15108290a85a60442c0c0b4a0b01031302081c2c1800100b00b8104c81c544404c03952014280724075050030182c41d008102c070035104a0711840380400100b060059425000d642103101c0da42d1519000d0980960401c00c0d4020f05600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 293862535 1250 293861285 293861287
    0x10509040303090506010f0e2a0f1909050f0f1003090317040302070e09120f0d02070f050102030912070507031e050f0c130209030705011809180605060117040b0a02 72
    0x43d00141003805402d000302041100c0312101070409100310743c00880030744421004410300058032070b005000080082d8186001d00c1c5541caa56040307550040303d10501120364540c94055102490013a000303410042903507002d440d01101c1c107106005000a02580c5201194015030300340740315100740d109401c54600d0074823038500020460000c0901506031102524220701680000b20f007404514003c80c03610354011001802001c4850043c982101d080c4140d1101e070030306240c0020091440e01281c4c0464448550000c4841d80d01f44403424003074001c1d04191203040c0e403402072400140032445031000740c0b000d40307800c00c0281021625590344d110900e05e80301074060b8044a1f0780568008514240710700034817035031018042e149440c05082080170181803403642510040c410f224482c0c140d10f00003420026101c2c2802d1405160041c10340740010640b16500c401103075030038a10445400800084030b001e58038070441c03041c031041e02c403407005441c0342000ca9002c1000d5003c0100240200f141c9116a68000c2d001500c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 293863785 1250 293862535 293862551
    0x122402090306090a0210081504110c160e1315090f0515070201060506040e0a0b03010b030a0f0209010506030606030703020703031107050c031c091211060a2001020909010509040303 79
    0x7280c02c1400c1210342040503080408001d00b58180f80c078414030508286d103000b1000f4a03140007403143c0080c054107998040c0350707200b0138041c0a05070f00c012507842c0c5165004403807000e10415402566040140030300502131b4060f0340402da4080300344904400484e030001d05009403002c207403c05001041d00d10030580303403014444508070100e402400b00d060304403910a601802c510b44240040e09450407540b0541c01402c08110030010f48460b40d000e9034114181340c901080403403010340000d014244010b44654076010740c01030901000f1b9a0365403c0c0c01c040c42500c20700050313070340e480030002d981c001110802d80290b810000076541c18032960003066510b1090900003420600307140b0b803c0290300110740071a803603448100d03502c0c0a1324040001c6030a1480d225021802d44103000d2004103450400c0c0b084c421903980b4034080e43c0401003541095188602c02070111502c8080c0054020f0079080c1000c0c1545140d114480300081e4450103000300c500410025118111603481d103c14010701490040003a010035030707140e01d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 293865035 1250 293863785 293863789
    0x72a03020112020d0501170d050702100f14040b070b0f0105060405060a18030821040827091f090e0606091f03030206061207080a020f060c060f1012240209 68
    0x1010f01a085d15821079007c0041c07550329a1074107d48510750790a001c0144130090040e611011540c0152605280410784100c030810141c40035010b41c41c8201e52004040f60120381c0b040400042c04486005040710056500c40b00000b00001100307008850700010104428001424000010600d14a0500d02940d02c201c100202c0603c00c40c45810483d495413000941c0c0c9040408041800d24841051100441300d0401d9034440d001d03032244c4902c03041480e50703a4980360080c4001c00028014000d000e00b0a00d8145404008100c0200300c1ca0940441240d0100002c1110012807040741607038591a80281155102d0204011500d10000c0140d0280d280e4406040f40c00c0310480e02d00340081d44240c00815460414104000d620314003509842400ea000c0c1104102450b070000e0b11203030440d0140d4440d040f510300e03600400c00b80c0c4520415070206200350004c2c0181c040b050301c580e611801c9204030500f102502c1e40300960100350300c0b82d0b01030204d604c2c4010040209204d001d0784c40304000b020074018906441c1c1e0300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 293866285 1250 293865035 293865041
    0x90c05160507170607091404021606020417120d11090310050105031b0901030816020307080607080c070b07080627040c0b190c020604050411072a03020112020d 70
    0x100032107194102502c100200450800d81070540341d4980081c03c034500c0d00e600d0080120a5500c902e080c12910303242c02d44000d071165812202e07813100319100095000d1850034603102940c07013841081eaa0754401da04142038003802290b000d090726007440d0744503d001d080145210241004944031082201c00b040007007503a80c0c00300b081c0030110240b403902103903070761400d030805092018001030340d110781c4d011204542455a0301d22149064940c403041942d160100005150b50204101c940207401d0302c5200c901050b0700c81c00188840c8034400350b80d64560f017035480046842990051aa00824024041011800703d42c0256071650b8005000703800c120300040a00c1122403040f4003091004a41ca11020600091001c1110100c2c0034204510000c0e16109a040160f500d40140d41104810892104260401c56580b2011200203040080c0300340040ea95203d00880ba03903128040c200c603030f890030b1021040583c00c148030781045c0b42074074484860b0715442c41c0c0054400d0940d0000c694a220360810403030854009500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 293867535 1250 293866285 293866327
    0x2703120b220e010c02160e0a09080403050604300309030c0203120405010905100f0c140601180b030c031b0406080f1c020105090a0602071e1b09060f090c05 68
    0x107403020a90180351002c560840d101a908075085411007807400320201d0307640e0610401c80d500e5112244080e610341c031500009000c3e411004104c40340c00a0000140400001d8250049003c2c80b89200f00600c148440410080002018618020350004c0d0441c0c55010b94440480c2d00c0c003034201118908200e500090a040082c42c03201c4a008000c1014055075911610000140000395084040d1065403500501114955040b040420003100714502c00c010f151541e095045e0008000c039200c65031a45843c1c00605104111500ca941c03900002840c45d02c0e0009d0298a0300c0c0024002d010000100c2140c81c2c5500710b660413041d007003a114000050048400c000803101c40400c2d02c01380c14190100b620341c407120009901002c0c21a8100818000d401d40c0c00300e00701b00c61962002005030350b03903528a082207446024500011150b180040d0000500c4602c00c0c510001348003400402c4c140300c0d125420f820850f0740300c2c00b410a4020400c50203004d14a040e40c02018180c042d4106282440000c560108010440c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 293868785 1250 293867535 293867599
    0x1a0405070306170a08340819180e09030715060501020d08150603100e041b050d08070b060409020a0602210a0c110112020703032703120b 60
    0x289000c100c0d20010a11462418500d040504042c544903141c401a60045001016564000c0950380764403440303200a000d51b10741c58201c1c040001c03400741041034281d04040e1035071316580c4d005401030003141d00c01c1910552240302c0988003014903081c0041c1ca908600000c0400280b0b200401c50803000c0748000304a0113106c41a40380202d01c0c20f00302400207081a040b1254801400350f0f071000e00c544130032400d000c40c2845105076000c545950f10a0703210342d0b2010965100e41e0b00c85200c5030a00040c041a80700051030700e0715600001440c00d50b200300303102c804020440c2c06409a00c0500000b0009407c0c20100e80c0c102800030004112020a500000c95004590340100c01581c0f00a0a28420f60045a16031110f2030f200348019062644002000e004600c2c040303001840c6051000203200c46a000b00300070264003401120454544d1a646805801080d6000c60320742030b05403140d0f17a040d08041c82c061282e07011b1b500d5551202408142814407019000c494103990344020002c1d180d8000d4180101210108158 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 293870035 1250 293868785 293868791
    0x3111207050a12020613030e2e020d0e1012060506040b0714031e0a02010f11130f03030f0804060b100305041b0b03011214010207030315060807121a04050703 69
    0xa180303820f60510740614085420754112100300201c4210112011200341c1c0c1604208102a51106c0010304015014485608506904100c0c00d408494113107420103015158086500e40d03148401d083c1d500b10b44c04c007000c60384440452074448419200f007814807400303147d00f00701247e960785900c0056005c1d0042d8020700d645640110b055401e021083d00d50310311020910001c2d500d09070b171415510410781c007178500000040000185000d0514801d40c030440300118504401c000045540c2961405a4400d603402e40000e0307070620010a1015800c640312044070b80c55151041410151101a19040c0c170080c015200c0f5681c4031860161520f642d881c9083c88819941c00040c186420f140100221208001043c07040da10712a06100b88404002103d055507960100325800124501c3c000380859441c0c1140882540042424003c058058100340c8002d039548407a28904c503194032044441c0c400841e42000010040304100349190100d6004105100784624006443c6040c100403500ba20300c2071703076140d000a035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 293871285 1250 293870035 293870053
    0x110309240c0d110403060c140306030c0409020d02030d1d010908190548030c0609041503051c021b01210c0903110609060d1d0f060a050a0203040f0311120705 69
    0x1d4490340601c00c2340c44880b140390441c1000781c0440d942c1d2183c2900c040c026581c0d91508010740d903d1003180d056556004044800a0160702d43c014080c2d000800c0c07285040110814030585c560260345d2200c00d0b40e03035403c000c3c080f28040c00b2685218201e5110b09407440c1c01140705c00d1100000f8100402d60300c42000c015480c6842c564a5001e000f11030000050144910401b0300340c0455401042051312070000301c0d20240c4500072030001030010120081c1030008411500000010088041140c110360741645446c076030020030300e06041e61640080f110070621410322411300c48181d0301400789c2648242d68501d0030041089121039080c200c40b0f180c84184042202c8800800401603418226100000140c4260303081c0301081e40408c040b8000c10040c4d02a00380c580f14a240105245400b941d0703111884802c441c2a0300c03c440066494080039950100f006040c000040d440000c0390003100d026907400600071603802c466840489944c007000041c05031034001d42070320741000b80141018120350350041c40900600c138 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 293872535 1250 293871285 293871287
    0x709050a09030c061104030c0f0e0a02040e060f130c12050f0105031905070306020d05190606020a35120105030714090a110d0609050a090809060304080706110309240c0d110403060c 79
    0x210014415075409004000a0143b81e4110f825031303030003aa06032100380815060700000781071840207a40c20b08107a8a00418040303100c0d40100c11690803926003404200700d481d0500d040040c80824041c0c1605a48090314102c0d07162900d011141030103000310140e408064032a0b5406c000c0e64480c40c1c0c81698140c5032424000803044011001c1f1901d1020360b0304200b4a4500140039440d08000100581060f0701c5540d1021a03201e4a130090340840040c5603c540003a00300354616100d41c000c10100c03003001941d0300020925050000b812421303a03844580c4980481c2e034400400541c1c000090000d0709494440c89101d1100208901a08a00c5c3d50120042a400d083c00e200c8412900300406c00c40c00141800004404100004120307030103100141c0f074035a641c0c1d46509000c0207a12030200300401c0740e4030700103951140342002130107507014142075800c0d01c0000307100d04400f41c1158885d64110340010401c0003c20104941b01000305a81c9012003030109405c070850040603403a410562040d1001600c0c0c02c5e104500c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 293873785 1250 293872535 293872559
    0x102070b091005040b070f0e091e010b1e032205061e0f070315030803070c02130504112103030406090b0105120706080a1d0709050a09030c061104030c0f 67
    0x101840c03c000c50719060f203a09100c01e601602801c2448895009013015030321138040381206100203055401d0505003803a1071200414402c19101202045c00004a2800302d1402103a80c5480c2c517001a440314401d0180c451200e50010300071100e0401a64042c8002c4048440e1560700e00b030140300940014940042c401d035000c2404003036040d0008810040001a05200000e41d8000ccd407140743c0010311225141d071501e41010140c0018007500c0740402001b200340d44c440c0c04230510f60f10950720301159840c0c4101550907580166001800c2c00542c07081c60712281080300500380d10b8001d42d00402c01003803608000c242143e0042e03c09a030300c641c4032003101041c440c400707060b140100010344c4c880c0418603000c040359885140c64042c402c100031241c008a1105110b680200355807504602d0040d1680f41c1c1a603850b555022a44250703640e403402c02d400610660388030b2080510058140d10740304503488036640c65400600f81380ca1401082310060001002261032205000082c042e03000801910601b080801041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 293875035 1250 293873785 293873803
    0x506040c030c080c16080318010c030605092e090b0f0306070906050c07050a120201020d050f07081b0a1b0803030c07260c031201050402070b0402210102070b09 70
    0x107041c1440b486406075648421040c0d440b0300310304102900c034510f0104099428007150310240c9441030100030300414800008111082c2400710000b0070111035000070540699009200c0c0951088074000001c285141080307500c1c6084000c0a0b00c02d602030f03801d000000645205800440001f035130741c22514500e0800c400c4102110104070028001460050001012407030903000300d80c2040004255402040810400c103006071a006000b40103041c0c41d9000d4200340b0003a00c00a0340144910724800441034064401c803801c59072800300451924156898410059011080d418203100b40841000d004038410311941c2509881000204100020901a81307295146900111251f41040061042c400c4c0c48a084038070340c0394860907403040d001b02c2d000f040c811050020000c0125050006410030301210100c0186409204d0f84a004120790b01c60003800203d004250000f01003040f40d101150247c50400c4400540030800104400e51001c0e00110a0a80c1c00c0b09400712410309480b01803000c5a907090004da20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 293876285 1250 293875035 293875037
    0x1505040b04060506031602030403202403160e09040602030108060f3d080105070f0306030203030909060d0606030602040f060206040201090303030c020a0b10091508030a0f1e030506040c 81
    0x102c141040000303441e03448042c0140f00446210401d00700058000d10584e002190032000740b4448110300503240007a50209540240f26912004050082e089100e000f64403d10300400b105d421a5684066000720407007900508050041031840720140fa619200c2c05440f4170b10643c40540c4a503d414140c900d0001d000d03041e440f004c40c0c41c40402111420726074620f030f103203100141e0718028000660703000c103004001540215501e00c2e0804000c41c100a05412450051600e65070302d01208411003c11021200c0b40d020080d0300d90810428200303949840308155801c020700030901442820343e582c40c072080701c1c0b0380c0c2d0040791030a802140c10850a03410600400090000340041c041a260070390000f0065011404010185541c544150082c18420030101420581c8103120700f005007007404250506200a12500000c1780c20803a80100003285580785004440500700114100740c0c02000035140350801c60540010018607030440d002075003200b5032404801001d900c00041038206402400190380d011110301c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 293877535 1250 293876285 293876291
    0xa0b0f0703020d05041508040204020d0e01090203280807050712060e0c0603010e0406050903091002070906051207060f03020702040603030521101a09030304060215010503070e0f040201030b041505040b04 89
    0x3044c00610440c4106d1380c0c44510300450340b6a01c0344002030003401000b070b0700c2c031110785000080c01400c407055104600c41802107085421091803038601110b4100b01044620690300c1102e5200005681350002e030000c40d200b1401c0d81c1e620782d1071340440692481c1c49034059580035116055815036113002d209001c410442903862525560405003040e940c010098070003040c0c0340c1e5980002e00306070814003c0d101120001084004e600c240140c0c003e660304181d00419002601c1c1080024035032605902c0d521010043c0380c0035002043c0307091b00039291014000b08010a042d020802d20700141d8032845648091882500e40710b0711055000d140111180b040c40400c00e28081c400180181e6850421100045656801901c12001094000c18032280504011260140b10108001c2400368000c50900c2b05d0f03400280d100807250fa0b94104043d900d0b00d03103100c1e41d43d800c1084804a07070404902610183c1c000d006050104082c004000030800b101c403a500c1100903000701150900c02490507000780d54225000721014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 293878785 1250 293877535 293877539
    0xb0901050301031e02060d150b070302060c071a1303020105070e150a20010504570b03060301060503010e03090603130b0f04140a0c03110a0b0f0703020d0504 69
    0x80c0540c071040c04007600050150304d803036082c0340c0c44c40306149003140d001e0074240c0c030382044106c0f00000d001081d0a610351000c0d07221b80820600b0b51030f01502d80094040e0f0041c28240c603100c0c20020903a205007001d8440201c0b1400421003603e01e042d82c140140c608240e4005d100f84a810005d00716800505007200300300076105d00519959801c4061202040702d000c136183c0d180503860040e140c00d80d8003890444100ca0840d1601104a81035106920650140035450070304001c01c0c18803e800c040c41c0141c81214507007101c3c00710001700d0720958180700312140b070707107840540728007078820090024241e01145c0c0c45400001080801e0500f03001d280300520b41178000740030184600e940070740c5900403046098041c0e0000f00029030b81e4038060a50850a503080812603a2606200e030381c3c032440722800c81b001e0790b84142d4030928400e0280c5c009100c100460f0003140b1065007a0441d0340380100e9000306400d0301d90040404002060b8140020001c0016891010340182d95440c9441c010741000742c6496a142840018002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 293880035 1250 293878785 293878787
    0x160602060411060c01140c0c120301060504031115120105120d02030301231002070e060a0308030403031e02180a060201021c020a0306150302071b140402131205060a060b0901 76
    0x1005504040445401340c607500c114250307070b0040004c83c1038200905403900510103d6020440203000e01c40301c4106841140085c80c005095520080c460000000c60420013040454500381801580322001801c040b003c4144038100022a044002c17007511760594100100000d00d411720b64a5000202100945190040007002a49078001481010112800c83e04040d041010040300d4a80d8020010440080d04100080080d03403400d050081e10310203482e040200d0a140343c00d01d0004100ca50100115145664a03a0214054070501b107000070b046140454070030360100c0b6400604071098491010341c2c6001c00e0b000402c01c2804032a8408400e591042102d90301544a91440110303800c680c90340942d590904410842c003c004c143d0145200c1111102c0b81d10705143d264000b004c41d603019024a10f9a400d4283c0c0043c0c1100103841420508207101c2c11a114904107070b00a44000e08500313103000c983e076a0740c0c034400104a0026400b22003540010b820002070b0202c5105900143c0500d0260f5030504d0b4a01d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 293881285 1250 293880035 293880053
    0x2030a150b090105071406010f030c05031605040905010f0f0b040f0e0a0b0405030f0a030209040506030106051315080604061e02070b040201051b1b01120e031204080d050106021606020604 82
    0x100c69040000010f17440d418032816103114264038070a43e044a00569440c0f100307010310078583c0021103c00512980000d2940b50004410407500b03003106407030001c42c1c50300b42007000500d152002140c055403115000d0754580041e1082224000e1051804209000402c0401c011101084980c010a03407a20132040f1102c000041e080610a600040703155154480f428118074602421000c42442c020008000180c107500d500a422008401d803418405078941c00200743c240c0d0a64040e454000076040d02031854020346400003c442403006244100042e15401c1ca941402d500300d0f07003a9502074552240e0b040c901242c000703203070282d40d80f1082142008215902c08a0084002c3c1c8040c2c104407011a9100600b9640b003000c80403802c80780c04803108122038a21301035030321805501c024040345003601e000f020100c19018100149104c10041c5117480405c1c0d03407845102e04050019512107009200510103180d030303445514040e00d8150024014108001c1078003545035000c1c2c1282003150440e80c04e110015995603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 293882535 1250 293881285 293881297
    0xf091906230f04060504050307050105071715031506130905030306011b0b0103020607151a12010e06010b0a0306050303030a060306060b0708120c2a0d020106080d0c0501060905040602030a150b 84
    0x25101240e46d4a4904101d859400b03601800380c5594070f803000744070140b0b4000f500c0c0511011281c20100143c6e0350341ca21307400296a448121501742d0000d00108080c60b0300ea80b0304541c4204000d20510201c00ba40d180c00d02100e0410030201c540382c1c4004180411984c021800c249600c2d01c0c05000c1200703100558034491001018071001b402418041194810816048403068117029209800c001d10f00701145402c04d42c0d40001e0565008218440301d401d0100e4040c0910007016821000800243e4030304104d000c115031050022908250b59040c0106040d601070004602030703048074030082042c50560402808440c0070f9440411300c41c03010050140010b000c14107a5522803a1135008045507030301e00c41c0c00e0078103100301200b4081250215444c08900500c01d840c2c8040c1e507018904442c96002094001da0880303a00d4020441964403441e2072500e95071040c1044030409210300c002240f25941d0744040d0058800c151001c440680d00441000301910140c4500d1041080d0314404040c008c0c50082010f00f0f501c103c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 293883785 1250 293882535 293882543
    0x6120f0b0d14100e010f291c0206040e070e100f0e0d050d0507050c0907090b0a11010c05030105040c031a1302070c061e02010603030203030f091906230f04 68
    0x44011402150707028410726803e410b210f90700340400c0b034100d00b0890003440c100030002140b0b0310788002d084624840c0410b10381ca01c034010b030704044140744d124100b002c03188104003140501e5008691120050b106c0401500c002e004410070200141815600a808002000c2c031003401401e2240600706103950124804a0b61040c0b42004043d030b11901002c91100811900050080e2240341034a01415a015000740345640c02035007528030ac1c41c0c500080190100050358401d0014032400011300c1000c2e10400100210840b6040a00d80d21035410501420340f401a403a08001c11000f000400207401d0900030120340c07440525040008400b240009200b0407000304446020705088544442680d116030304071548641c104000c00e001d02c1d9180750090500500d900c8100303045c4956004a020103005000f044296036054004d141540d40314040c01098150040c950700141c401d400a4103166880680c0380d000c0329000341c0b00415910401032218040540e206081d04c088004d201c1042410400075503259009644 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 293884892 1107 293883785 293883803
    0xd05100b0103053c0a05071e1e021e0102040f1e140406170a0605100503030d020702041112090c0108090303040f02041506120f0b0d 58
    0x301034819040c0b11094040304c0e00085180c4110620707050242820122018490f403142180500960310041540d69440c2031028440d4001d01541482c2d00380d803105001501000c030000c080003101e40000c6281d810828900103200c1c421f102c014802042091042c18611004425900030b61080c814100780d804801c1002801d5100890320700403000441000d00b191a1030042c14411311007040d01015030240c3d1f18600881c1020032412060400c180301c10007026000010b18181d005c1f80c0c00680300c4c2500400002c403c206540d40007040310000c0c0c2c6140005601c4d4012880810042c2c1168480e0108048000c41c04072003000c400b90b080ca01c0790420360116224500d0b45801950544810396907107525400c1080000c0200341003083c4158041e10180c4001030581c8403425031004a040394100600003000e10f2001740c03c0340580e01546660b404014010032015405030f001508140b00080c0040600e44 = true := by decide +kernel

theorem cover : BRFrame.Cov 293705035 293884892 := by
  have h0 := BRFrame.cov_init 293705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 293705035 ≤ n) (h2 : n < 293884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
