-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:33:38.398756+00:00
-- url     : https://prove2.me/submissions/53ca8095-e6a1-462f-bce9-190852c3b62b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794604316 ≤ n < 794784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794605566 1250 794604316 794604319
    0xf091f06080105100e16050904050a151d2e06020706020c06191b0624080a20010302040b0d05070806093c0709032d080c0a05030a0c02 59
    0x30150315490740200104c40188038912041010303000041c0b046006040406462a880c01c00300e040032010381c006400d40300d003141c00c07a4000780c0d141500c0f40201200b903404002084a46201c02c1400b04540c21314018200082c00101d00502591072900740003d5030015400c0200260b444039240380d100c2100a4440035284502d90052103540c418051900e0300c6c1007150244020681c0c0c148285041c0320f0305035600f0303172040701416089088004460109001e0f0003500290040c1c0d07603a041c1a0300c001c032005c2d1820440ca8000c0c800b00d0780541142d80000360181c0d004101445c000c1c03140e91104001c980100c0107441a5088000e4009012688403014406504150701a0b80300b07031610156581c1d0003007802a9030b03108442c4601e01150105442c9103000c1c6d20044120500c0c81450400484000f46140d0f508869003611100d002401c3c400e0100700b030060b6070401c2080c82240b480c5010044060540c41584c09031100ca0142c0180c6000810050071007080059220540d40042686e84078414618058001076030303201c00fa03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794606816 1250 794605566 794605571
    0x3030a0c110c0a03201509090a020c1b0f0d061d011b03090c0510020c030f010c021b0301020c0718061409040f11060c0a0309090608060f091f060801 65
    0xc1d2800344000c2094150000041c00c002c031600e1030760300d988590321714010445640d40c0c84900b100240d070304e5112503001444a1804078a0b034075507110090111b91800100340000151050045400001c40841c041240355188940920580000c41c00580107441c05114141d11643d07448850080181e150001c0100c101c51905402c603040c03c0c04102400d03140c00c0300c2c40188140740c2000310781c8601d000794000002907014003030a281d03950315100480e110801103c1d01c5000340c0c1c0030058500c503624040104203440340b4800024442c5034038507540070b50b0302c000300b40c4000800e4920b03841508103918254103440100c003035241107450309583e07268102d2a40c1011031303a1b42d4074075080c2207000c20240c2c10340343c9101c0081c10107443d000550307a0341d4846480740c1698000444035200c1006210095039100c4001d001900f11110142107c0011441c2c05486c01c000755001e0354034182000b800300240c4101055181d880308540c090455541d484040b00c03820041150301d2030141410b00c400010301e0000c10341c0040e0a072803030341e4001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794608066 1250 794606816 794606837
    0xb0319050601140d1412120604050a1e3b06130c0608250f11011404080903190b0618090604080c03040509040b040b0f0c0d020306010c0503030a0c 64
    0x4001212070180f03000c603005044200d4540000311403c081c0c200c2d000589040d00c03041100280040c8007076021348100c043e01e9020400b44181071a09105a54110910000410041d10314901c0307a40d25104002003020820fa84428902e101c0c4243c4c0d002140a03401d0320b003050310700c1079103d80f10b01c24040b401c1c07a156040d120b124002a9241d20303015907500403903004005200005c0c030f0014200c0303000e04024088402d803000c852800303143e05812400983c0100c8983c8500a45411050b002000840f900000d0480c80c0c4c10700d4046928116031019591b0020307000046140d0703a208050201c0d01e081042d541c4402050081c00403102480700c5104050b0003010116200e038407544400101103c01002560410300b10b40000c40810002508080140030000074007003542d040a0303a490024402400445003511aa00c00760304000c10460303aa41419801b9101a50900590800c0e9481c80e00c6800b43c0822848603036400004500180e011b1515101102e03400800c49640b4502603003544090f03c911480702e00030a52000d00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794609316 1250 794608066 794608079
    0x1b060906020607051602130203090d08101a0a050408060103050a12050424140406031e05041703060303040e181b060703050d060509010803070c0e07080f0a0b0319050601 74
    0x1c0143c061111540d849081c40c40d6400e075070000c2c422030802241d003e160408511505411400950321600b0b111020f030070b1129026001421100c801081c00005401880044c407038005150164242c03142007013001078880300004001e40380c604c00e40c0c00200d410320411000000b045000950f181e104e6205008a01e0320304031a11095866004500a182c600d0201e901e001d08a5500c002000da88103240d458500064404802640d030942d0254100000080d122164184c0000c100e40c1052081081d0f00c5d0108120b00c0c00303896402902c1d0001e15000400f0300004042402a40d0410603a40a0520030070103517110305105140940c03510740440303002e002c3e005041a0310058000d62161110000001c4c06c01c07443c0844c04ea44c100c590b40d1010340058002a556440420651070b98011039018204440046503680390506003003180390701c0c5a2012044800030340400c009140d10804203074005819031004c8100340c4484a4403406490100300c255090b00c2011481450100d50100c0124158018000d41f5400e0740c8902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794610566 1250 794609316 794609323
    0x14070f1b06030b06030118090b01090e12040e13060e0106141f120f0e0a0f02010908010b0a05010c06090b2a090f01110a0b010807180b0a0902090406031b06090602 71
    0xc0354154804c0040c80100150700312004032052805180e603000580c2c00d00c980d01c00103034800a80081c0c2801e65280e0b000c21584004200c014071b034000b802d0341d041c1010302c1c0c0841040903440081c02c03821841040400c4d18200111a003100c0b42e034218400c002e00519441d0f5007002d00101340240301500c6181e28103901d600b030920100d540b41c0e0460255541d00c0030802c26100e00006032104440d80000943e0b2011782d8070300c402062160366592072140c15800d5030061103000041c041d55450300b142049924180b0190450358070006201c04582080c00c080d081d0122078180030b030051a250300082d00c03020b250300811141744509020150707101c0b00051034503030a42e102d640d821614000e02001513081a2007002c808080e6002e02295040381070751000300c0340e151003079948009a4810a07442098940c0c4400d10601c05d041612000719001150345c03404021904018000510744603180c45035121007076000903601010345031504154080d42c1c004449501d00000b010b54a04404c400d849040f000602c20000030841a1021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794611816 1250 794610566 794610581
    0x3060109150206040605070c060f1d03040e0103020d17180a060201090b340203030f1e070c1509030c02100e090f0a061d0402100e06070314070f1b0603 66
    0x150b0091400e0360742d43d034890008120203000e0b04140180c48090000284a501075020520281400803510041e0580e5170140203040050080c89500244420b10121418440c503a0440e074045810350030302d910078200350031203505181013a039100300c0c0090114240780502e162079800300c1041d00d082e031585544e00c00880c00c9510070307100201190b903c01c0102e0551300280c00708a10f00000c80b2032001030a200800d400e014401c14110f0070340541c001004004e807141c0700c1004079600800d4145204105080003544000700e80d00209000103100d4111020010700030804902109000001000c0000d0005801d001d004040d20700401c03403041d01006c00780501180301e00050b140b410001b5000500c203845202c498000050020700501c181e41d0740c1e10000800d808481010910050100d400c250b041c10035005211501c5d08a401420a129142c0021203080e1600f608543c036844d0107207002c411502c1c8100440303480d8071171040c025141d002c2c0700444009028220008920310a11000003c0c00786968480039416036516 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794613066 1250 794611816 794611859
    0x50f0c06160827010209030115030b060d0c03140a050f0f10060b0304030c05010f1e0c020607021c0c08030a0525020d0c050c310b0609150d020c0303060109 68
    0x7001c3c0460721000141001a05000d00d000003d03081c40d104001080c00c640300b2007445492a07004103010414171000444968105a044d1400c3c482403e40307444120000c0c0c500d2100034400e200e0700c1000600c00d01d043c0845400b803540310b41a01c140d44003524034250340e540b004040b0a8207000d101a011004e0035503220f640c0868146507005030941d5500c0e182511589144881690749540381c2d072502d00890618850160350b80000c00c1882d940d08a048040401c85901c040d0007000d5601c900140038005400080d254a016013400e808894000c00d600202c6030072031a188000e0061001100b48107462100d6042544501d40140d90b403640c04000030285940041c900840d200542c0111503800555440365044003c2280100c1c01c41c2d0020a03142e000c00d8098130020003a4800e841000d811410001a01030743c0300c94003a03203040601118240c00c1c0011068855211400d20655900b5000c4809154110135a10301c021501821502c0b0440c10101c0780e103d600c1102c43c1400621450808600c10740620b41b079180c1c0040303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794614316 1250 794613066 794613091
    0x6092a010807050d050f1b070201170603070905041218030b190e030a0c0c0609301406060a050a0e07030c0201330e040807030e01050f0c061608 63
    0x1088005541d040406820441000030800800801c0d20303a90041038001c4410fa50030403010300c0d1a40c03c0703041d0308501441c10400c14208114040c0543c1c2d0107103949203440c402000d10445a200c09002a1915203250302040c1114140030400007400340b844c03c8041104040d454941146621907224503104000e408028082ea568001041501d18070030301c01d041c1d180c0c81c0800001d80249403441310380346801000c03500700001c407029805010410f9030080a00102210b0030b1131101c0c223040401101460340c241c04e984c240521000c02c0d0850380040d424280704420740010403004407116000003d074071054100d0714580101c0a60800107a5800d01d101020101c4031000411311064603950b508030090404524039204540d21030038060b8200200f9107041d840d030000002d1016541505044100d040020380d0b10010001d41840d00b004042400e04044030901035051030710103010f01800700165181c2c007800503200a001400f050700c04203008001006070150303a584c1103070b88080300a82012610481c044801e543c080d117 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794615566 1250 794614316 794614393
    0xa06030302070e07090914060a15090b09060906130e1311040b040608070807091d1207030c0b1008061f0923040c150504080c061b0d020609 61
    0x3800c8043e41a0400c2080c50100c60066a5000a5042d502480e00400020910130103003c41d45c03070034401c070200030090000320340c41ca40c1c3c4640000e00035102500c80e8501c2407600207145046990350300111004024010125030f00e44003041e00440c4a80410b0040fa0224600c51000c540684024000341200640c01040d007003003a5081c9041c04080c00b002e945240d04240ca9580c08140940c0c10300c02c020281450000614940e880c00240b8000d480491540c09040d40510040358440c803000700c2c00b020000c90b2030120507580c0301d00d40380c2101d20b000890405440000c00006201d601c02c0081050030444208004650668a400740b1200701c0c440c0341c0140d0305003080f41c400c0801c400c00d0903400c41142031000c2c030102181d11041d40810003250804540c01c64403801c40c500306108030302e0100150b0004155130310344039081509101e0000c0e42e070440184128480c0201081b2501403261248031401021881800d40c1c407400107038030700a561003400b0f0b079114016008407070400c4400c82400c882c88c81054400c4800743c4114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794616816 1250 794615566 794615579
    0x906011719060236040c090b0702240406090608090d0e0909010605030f06011502060115300b0109091503230a0f02010f03090317090705030d03050f0a0603030207 71
    0x3948040c2022085011035224944980380900c1804802c445110450084036a04d07130801040b10200030300c09044c000524414041081040b0075102d03c5541616a4440d80b005840124011100004418200303400040d02044c2c25501c842d11900301c030015181c411603a110003d10030384a075007103c1e0813400920140c503081e200d464000040390b0413040e4003000150782d9440b400400e0404401807007a48080d40100010010440081540c516000082c03018016a50404016440b0a0b040318101c1040110000501c1030070070022507580c5036146004c20503c801c6c680c100c4802d000c0c3c41c80e140e115000c9000d0010001e407501c00c0e030145c3e080c41e4440a40d02c109650642d85d410b407029403540e80c4070701105008420640320715010010018844d02074080e11500d024144001403c8550440b00f8104060400c80a0000283c2010ba40c4103c0600c6030202c801c0d99453b404214a001d4003a401954107105241c2545001901907000c10702503030001c030421450f9a2035a903140141e4a9610000300181d0084000f000f06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794618066 1250 794616816 794616821
    0x9020906030a110c0a080408162111120a0b0714160503040509010308030a0513110108130c0603020c06060f030309090a110d0c030e0a03020c1017090601171906 70
    0x2d050070f8424180345010031001d183c481218001c50b040c00000600f4080d0400c208554006040c4d1207003101c00084c20320740074429a01090601d00020066044071500308280780c0c80c007000c09000580502100c20b2144000c07691040d010f04181c8031041c01802081a0b248101c0714140c850305040201840d20030981e003544a0400f441e0016135044c0010322010600384d0750350310f506008500030009181c4134140320000404607440544403c0306100c0094000c4001559112001d115a400b4201507078141d86d417200d07405041116110041444020070170106005803d80d000e40740d5201c100e1708454290341d9003410300808011080526070b06500c140302e14022842c090090030350042c58000c0109030f10010028412568018544036195151111445c0c050039a05201e01080442c0e480014034207840300740c40294031000154282030140a260040c010f03883d01800032000a2114000e1819003403900c40b0607941c0760003081c05030004040882d070b0f0703100301c0031070000c1d851803000450b003200307985c00d042ca9544000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794619316 1250 794618066 794618081
    0x21e10140c010626061312020c130509010c050304020310022208211801030e010e0a120905030d05032809050c011b0f08160212150109020906030a 64
    0x880c408016012030500c0078051203004004426042c04200311301e418540380b441341414046113540c02801005201e040400d6052400c540090701d000b030311001c400c812400d2100d02c051843d0000c1c10040b2803002c80c403680d40f245200360b441c3d40080040c848130a004886900c01550040c2d85a4803080c0754441105d02c5500401c2500c0b0f00d11828040b80c3d202c0c44844043c0400360341300c0c003d590030070107120075031000c1c800c07400c69912005000c0700e28041d0303058100c0212060818107141010f03650715280b6100c000035032010490480c0582140d040442a207070004c02c00c0d0741d80141000007000920002010309000580e048046290384825040d6030320350300e003213500654000c9800c1c403440581d4200301a29940d4400d05c90300500a0020300b0102410100142a0360300702900300144803440049440420050380010845a501c8080943e542800b0388101c2c2e1419210341000e980001040050b00824000003a040b284200500c0b001c1203680e600c100100480c05001c800d0380c1c00c03407420000140710b078406a0040c1c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794620566 1250 794619316 794619347
    0x1106030a09050a14010506010504030503120903220311010203030c160f06141f060504180e0d05030405010f18020613080706111204060c0b090705060304030c021e10 72
    0x14005002e88500c1e150a4144005445100101d40e2078458540e0a0140c01e600c00c100b800c1841c6000e18695400baa80c0c400d1605070542030300048082090100280700710b820002c1d40201e40f81e03043d0300744c05442d010020b45d032108554242110b4200a030b43e50002c42030b031b0320842ca05034040d81003610300030312610147d220803011204602111031078000200c180c492007445001c035083d405820320300740d54982c010b403030030300788441c142d0342052806c100055110007228142c40c0840b4068003d00d00c1c0d028a507020380030390107408482e80204107415505940c8040510b2049004000a0062400074070a440c01c580911041201d0200c040c0b01c1c00016061000c010540780440040c80d80c807407591031941500b040090f030403440000364600700d80010341d042003006500d50f000701001549042c1ca45840035002c0c0b031800350000c0071031600f10002015140217010410050038003811140c4d40e40f4040ca801030615401440880c030600030105a9511460721102e0390540c8840945908400000c0f07820544004c401c1d0100c82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794621816 1250 794620566 794620571
    0x19232b02150706020a030603021e06030c0c0703150209090708090d050a0c02030f0f0c011d0910030c030b1b070c03082208030318030a0e040f18030c1403071106030a 72
    0x1c00090f40c50310003010328041e1a50300040c118107501c1000924048074840d6044440030820124a81c0d60302402c07a904840c01e0401c050390b40b501c800c1c0c4241010220752026015088443d11400481101c1e0001c04807041e049409010a55030302509817410300f0107891032074044c0d00910440a900d4040c0d0001d1101d080f0904000d131114500d60300092034038418000010f0700c2d13046510a03030725404042040c1d25001c81c1c01d0030480b500f628892003c401c00c13039010710b029106d008200d020070f40305a0b070300e03903600d025503000014004016100e007400c0003003400550b985d1004200000b2050301c403032515802e031080710b40e0000d06d01510034510340310000c068020340b40c522406825022150504081900d91400502801014580720b1500e9459900113046519544c0282e400410502d10b850340d000003200c508407021580089c4858212185000a1038080c04030b0740c0c42407290b6440b10505070040442e51241e441986440d40710038152040c0c91300c038050180000c0240000c108850005c1c44c20801440e031008030240f00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794623066 1250 794621816 794621827
    0x1a04120314070c030302190b04020f06040b0d0e0712030e09041401020d0b0906060c060117010f060602010902040e12040314010e03221208070219232b0215 68
    0x1005500442c0c2c22a0304604404040080540521410700b01a810440680b044007080c0c03039100040e0700041000f48681c0e001d00d001c0d1200c1e500e99040d174014000ca002d000351140c4481c42200c1c000e080d07141c00c00d040c602ca070810004e0449040c407400c0315002d900d40c0d0b400e9852030401c000d01050210180080fa2035091a0501040c0b80c0400d101400020f2404003010030300a803104103100d030f00840546658014103040010813001a00041e25a044403451410b40c80b201000e962041d004110181c48504401d08280000420b594150000580d0314000c8800700040700482070650342c1e035919001640c045030824041000411b000180b80b1042c00203030300001c9080141d660000f411030f400203180ba440b100c1203100040718240d5001404016001e84140c44628400c6515004500e0241e0a00240f048485030825214541c0c5c429030140102440c02c0801c80d04202040180083c181c4030b9101c40c01454030b5018a002400c130080c005084203804486410048547c1e024440c070b0311035904c0c030b00010390010804c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794624316 1250 794623066 794623097
    0x3040609090c0329130e030909181603030e01030c1e0c080301081e0601030b0414010209040c09090f02030f01051908101b080603100b01020712050312011a041203 71
    0x2070f11041084401c91940040482c2c080000b81c0032070520170000c1074545440c2081c40c04000040b101502030807038140c0403a94400d244055038805050300001e032402654042c000b1540440c0c0c06a0071f8038881e440d200b2803150030304011802c0ba030381c200c88440025404461919580d02d400038044000910745090b4a410415480d8824103034000ea015180b554440c0c0300c00e410211401d02c034000101641c502814131549141c50324502018080c0001c0e241a2a005403100c0691095044410340d41d40a80184402542c1d5100a8000603075403041e82c04150501080b060310401030310881e4401c000b04070f8a491076900b00b00070310061007500c000070303003090500401c042103001042141d42103c0d9299a00450b0204e60180e4007a1405846000d080a001c00001400080c0e034010504012185c6030721000603006500c0ba0040b0300e0f006039540101e204105200c889024400d011006151042d0f0656050304e080c0d988604100e10100c1c10782c021400c03841c041c0400e00c6050450150140b000b4040e1501440030129080d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794625566 1250 794624316 794624351
    0x5100c0c0f141207051b04060e070908010506124306022b0e030111041d07210507090f060e100305010f030f020a0b030414010e03040609090c03 63
    0xd0142c0310306015145402058100300f00710070792803603002111402d01189a4540e595606a000514a8900040c1040c0010b4503180e00a000a0004495001550034294006441c1e580c1900600d5010350901c00050700500b44103584040d10386c80340b030040c07058907503035043c0c24800e20000e95003010005a101d080c440440e440313103804000c00c034003100b881c00041c507200c400b91130000e4005182c40d00c2840120700c0c08504424035030101800240b0b00742440c0c0d4040e0000000d005005603106880c0c0c80700c1c00300300442d00c40010054080b2002c130760440d005071a02c1d141c3c0165030340d00040c400c40b40d800c1c0aa860380d036800b81c41c6402040d084041428000308664480c0e0f032210702040f46800c0f490010362110320261107490490300c0000d403805c0c03c0c00c0c1007000d5410321800c04100303480c601000e4804a000c00740c140442d1619540300c4000c158a03905280c59040520300080403030300030325903290158280203940800d002d02008650455400c0c2d10b0340344600349070004500281450078880014591b84141070134a0003443d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794626816 1250 794625566 794625593
    0x2010509060c07150f090b1c09150f050606090603130303020c0601060c0308151c081e070516051003051f0902040603110405060703081f030605011403060405100c0c 72
    0x40d1040000761460000c000e0200070117156400c1009280c000c2001200d5080c01125004c0c02490300d810400c408a00128015000302203004024040640c0340c105401065481a40c02d0100100b05100745c0e00c401040000b940594100b50b035100d401000441d0030640700d1994080001d102c0e060260801c90510185410702a090b07010b040031130b00009010301010350000d50141d00c0381101408040c03190390702c00459009610b0b0024451100700b81c03640c1c842441410f10a17142d1541054002c1c1219031800f0a40d07c0d4980c20030700003203941d441821214509400450020016144050481440840f05450403030150a01030b000099181c2c0010320311064a10701004a80500750380b5002583d02d600e4148010100c1c1c80301c1650201341c4a00344410700c902c3e541c0d202140ea0050b0036181c01640d68585044130b1148004480d209246408120400010041310b5040070341240d000714190028109404141521400101d400401981094698405201c050360041d680e180d17540c9403080d22460503a46280665808 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794628066 1250 794626816 794626829
    0x1306150f0c0f0602031b0c07030209100e0108030a0915020c060f040b0c0f0606040c020616030b09010312140702090a0e0705060a09031e0309090b1c061406061602010509060c07 77
    0x401c0150030103070411007246c405821840e0030302d00400b82c881192200014080248500d41781c4001c144d82c0b007038151032a009400d02d00000036181d41c1d10307159a40c1d641e010300801004100c008400264034040803458aa8020503a005416860054030410030141d0216903900303003802c805c0c400400c0300c000020180c00035400d100014140003c0004207240303008001001c6034842c40c105846605004d40c041801c44e0440002116408003504600003540178014420b01c541e00407603074500000030310106800e01c50750780c5420b84855030105181500410f05100700403000c1d400101c1c401c00724508422640c81000750f0f0720110256030300c1c2504c64000502d83d40c0f006c2119000580e41e0300c400d00511500c5110081200d03030f410541c500440c0c01e5a00504182040c2c410b001c1c0f810385ea9010394400b902c1d012901b0b07407110000d01c52422900050316041000b0700706003601e1400780d8407000c00101c003410304078116010342003000680120200240d00440704d56015120b40b580210742803107901c814081c10041c04019040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794629316 1250 794628066 794628071
    0x20f0712150e030f49050405031b100f1401062303070e1c050c060c0f030d1a040b0f0d030507021207241b020609030f010204051306150f0c0f06 63
    0x10068142200c003403061802c04001914150a0010641c4090302c1200c5d00102143c0850b055407103003862400c6004110011107414881c078501440c106011408010005180508100d8060f60b0494203003210072241a1008070075181d00148980e5020300a000401e80e80721060500400030300da440c032002d80013640c0c140041801d2407092501c525000e80c8080641c02050342c901d8a00c80c95466950ba00c0c250094820700031000020a0b070400c1c0001c0c4036003140c0d0701c8248101e07030b905c40c0a0300e01e1500074a403504104201c0e0302410902d11462502d40100c000b600e500400c068011003026040080d4030750300c0c490450510004015160050325a0030000480503c0d00d00a445400c0c50940a51441c04064401010070584030702c96001240d003200804030b0035201a02a60100310303451021982902c520031600d58503100b030b0f03142040e805805400074025144280c503000b4041401d00d5010003031ba5450700562000340c03e8440b0076140f0710702c214260400b004032032130501e020f000e094072484044107200000f91038468 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794630566 1250 794629316 794629357
    0x130807170405150c15090f24010905060a0614090d050d0915050d0207021c230a022101020f0c0105010e01060503061c03050f0406020f0712150e030f 65
    0x20b030441c0e008030750780303c1142d840380382034605070300541c82c1c1c9020301c446940900c07444007280000a0400248086a0344442100c103001c14505000054148143c0400036040c4c1400020800c0715143c09008e01550000e424000c682c0d04119064800b1400daa00c96241140c0c1402085000e641c3e580305234081f1402500a0801d1322030323006004012211913003001c0c0a15030508140010356a116080300ca40b80c0d4603500060b00c8840910020b07103400c05100f400900103054850b603d003404002e64500345c0204d1080c004441d1070170150041500e4541215019510510400d222000002e100c0410421a49030300b000602c1d145400306a50910b801002422a150b95120018030440a01d0f00b04640948440d0801c141503281000001d82e440240c074003009003030b801d100842e104041c000c5040d15107490724540030302d0300c40751502402580d4017510f400c880e00610603008000782443d1900b940080e43c503040038a00306242c030300412902c05001c50a000580703d1200308038810b101c20b85d0300c0142c020f03075442e40380040400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794631816 1250 794630566 794630569
    0x30f09080331080915040b210702100228080108070504060f060315170f12030919050f100b12010b0a061d19030302060c070b130807170405 61
    0x41c0308007281c802d030b1904041c2e104054120703030b5000c01c00352540a0721503503590144801081c0007401c1c0c41a1004a100042000b00304104d42d41c2c041c01210320401d5070740d0f014540b100034450618800b070741d40030096004104900a010401d03001480310b803007030002c08207010382084d9211000f00000c011070740004000c540144000101803240c0f400502d0111014007080d410445144030f4100184202e1092541c0c507a00491010320b5100150028442164540d81c3c04481805180d1030750039581120b0494024644140031001c40502a40d0060b241e08000b09210301c0065a81c26503c1c0e032039181030307407148140b00201c00003040401182860050807080070440c0041c44040c032494104040246006074108241401f46480b000200e60869420f45004420108a109403004a00303070100c40030307081082256040d40310580c1c03600081c01c5910960840d842c0f0307610780d0382c45c0241e40110000104581d800e600440c410720302c0c09c01c0d00403001e4003500d100c3c1d107040c0d66075481d010b22001c3c200d03038240d0860700441d041100e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794633066 1250 794631816 794631841
    0x70305190504030807080a18140f071415121515070339050303041713050103050c0f160227011e0b03090c0a0b0405010e040903030f090803 61
    0x211540450a00180c205568040c184a0000303040030100002e04001030502205a000711049001c9194808c650504a09207015070310722031042028603215844000071100720010b618422075440c0011109182841c01c20050400012000f2685064003880b0f21421704110300f004134000d8019440c1c44041003862002c0c0248450160400c140080082c8075020110f1740001c0310300310000d9800c01b0321010641e41458581141b425203640c18020303a6503005841041000001180560700409101c480703061090340c0d8411a114000ca100314800d900b2000700903a50007508070b80d8105000b1000942080e09100c04da214581220704c503c0d50a54070324081c001035040a001d824407610700c0d008240c202001320000c04031508018400c3c1d041d0000d004080400d24440715006901174a0745010969032030030015140c1d5690b002c401c0c04180310b000b00b460005102001201190b04030364043e11600b0360f084002c03081200500c800c04042c4c040c5519016001e030107600c01d1007014841c2e8407620401e81c8074200f88129100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794634316 1250 794633066 794633101
    0x30207151a0d0206090d06061e030c08010513140a021c03030b0103111b0c0a031b061d010f030603020604170c0a03021f0201020d02040608160f081503030909070305 72
    0x20300000c09030b010158a5540484d202c0220555641100c81d103a4603080c0d0003400a94005910010861680f0b00c000c40c030000c0c84412a40100c1c5030820294a0702d50843c201e54041d203010300c4111007468540c8c00902080318950103960514143e0310812001c0d00803441e41204500105440302d4030640e17510406426200780328007410203280400052940c1070003491144104a0b004c46440b2500d0303c070000c00b0300104018142d1030b2002c2c0108462642c0c0e807a100581da10300c0e030700c40c0220707001c14480800c1940c03007292030018400c03621420b06a4a02400d00644003580008074840030152141004005611345000034001441511000205018001001402d110240c11204c0c45100801030400150f44d840c102008501c180410007000240046400c1c3c1c0281f03e134100c80003440d0b002040000c0c00a0304200d040b403049001d6100a08003605034003040b00d03544401204a80820700e51804100c05503200100f05091001c0a42120318040c6404e000412583d411142400066110400c00944104c290282036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794635566 1250 794634316 794634319
    0xe1f0507090612150503030a180617150f12033402042403030e0f01050c060a1d0f030d0e07080607050901030204170c04050907080c10030207151a 64
    0x1488500b02000100301402d200c85600c080b42d15072481c00c0100304013013205001080e009044035075540f441c210161240b1b0007401c0f0310152103546e0100051003800740100d11440c00744c20848a0b278503550440101c1029440c824400d030040b4a1004e0f440c51a210b544500c4c1202c01204021520f400ae00548411015210036a5810241c0a4480800e01d001c0350b001500e000c0754100c0380402d9910f0800a4900d00180c0300143c125803010700800082456040b20b86001d00c060140d03548080a142c00005540d41d20401101c2d03003095015a00281007034846a0141c412915080d100642044010071194a000c0074103001032136a41000400700d010f0916403083c020b0300307145a0b02034a103c52510300c0c0e450b00d4070b40042c0200700340140003031600d107103030300c2641101d02400748030600c44ca2004514601c941d0300c1421241041c0514508000300b80d02d07000014294088401660040401191040900c0118580403858006240d000d000b1400001d00105400d204131560a0b000102d44160340070a0816143c0e005085 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794636816 1250 794635566 794635577
    0xd051509070f140f090a09020f0603071209050c04020d0f0605030703080a0806011218120e15130b0a020d02070501030b090711070902030126160e040302010e1f0507 72
    0x1003180c0d4480c0240081103c0d044160001c607950304401040c007050301e8284043e40303d00d8600421007215290380c01100268020784012803e2075014043c00218442540e0007004140c42480d500e45410864103d440c6451045081d102070740c4041001c982070b070300210860685240c48400f10104d050151284000810046004048c120721b5a16039504d40d100f24081c5e03100f008044000140140d01620301050300f072003219800c00100e400d0b01000705400410b41c00480b039076805000012212445010710414031030000b07180c1c60421008a9420321a1b0f445001d603072080402c101c00c001000d155580c003500720043d481e009805410b05800c8000c1c1000d200790012414580b83c03069034001c1c2e450300030700700b6801065810002007402d001d540031450007070258081070865000100100e0100c180700704652120740440c0c1792910400c0000320954a03005055081812108160420071419810218054016002e4000012142180794082d4108040710080b505c6820303d00103601490566841510340c42500c52802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794638066 1250 794636816 794636819
    0x14030406080118110d06061d0609040c0c05010e01060302120a05070510030b1005090f04020c0d080c130f170d0804020609040b130608011b0212070c050d05150907 71
    0xe007000c0e5040c000c101000c140040b04018030b0000d40d00000320381d1141003400c2d86903805204640050481406a07200007024400c20500c4020340c031202074080e001c0240b82d01d04012002d000c5c00004c0820780c11000801048021205c04200e0a00c1013480c000e080300700204d41c15045d4018002c0e00744810f0040401580854060004507001207400e405484040b14a00300c0030154540032409050300380141548140440c07008208aa000001040a2181621100c01c016000c0003044203d016801409460b504407560040d034091107056a254094040c400c0103041c807404400c4a01c003004a03820030380001091031020710000f8800070a00a0240c5480010408100421001001040040c0c0000c0c003552001c241c0b010386503a10781182444900281100d070040c0c00703514845024011034030480009528010107070340403507860320008400f02d0468008005081c1e0841c114401940001c1003540d102000c4040410244d0721610703260001e90160340100008401031440707260f1000f01405c04030855100c00c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794639316 1250 794638066 794638079
    0x12251106010303080705090303030906011404020c060c09120a050105010501080c030402011d01140a02030912011118060d05040807050c0109180f0e010e0f100227040608010e0a140304 80
    0x40c024103407641481d202101e0f45400344191258022020002d80c50300000c07040121007600003902c0c0e412580e605c0c00a11211050f1001c1c003049124030071550140e904004001080444c00c00000c03c40b020002e04180c840004001c182030802800c4072045400f40d448500403c91580e1040710207401121301c60600703145081c1540040d18419920f281c01c0c0000401ca07004200d0340c0e0080030039075900a800c0c0880382da80c4086000c003d4617540403500540c400c0e0350802d02051034030b105200c0c1034030081442445902d004107011144403080449400360364008010841040c5005503405540d0260344100c1d005c0c1e459442d03e0bc1c24a040076014400d140c1044010481001640058400c031080140110300c002800703015070640a018060040c00c03041c007982020807440da42c2800040441403142441c1c00d4600348160090201e05910070301c020215921141d1002c119504640350702e14424003030041c00000c81903a00c01e91282590000043d0103840d030000c0202030280500da030b4000c6003002c90f18003d10701d4942482d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 794640566 1250 794639316 794639323
    0x15180a0f061d090f01020a0315150f0507050a080f0d2f0c0c0301110c0706030618020a1701061d030a1502070f15060f080307030c060c0302122511 64
    0x150b41100710b01030a00801d0151906025043d95804140000e5541c1c80203420301401402400e600600b014001e90000210f64160004c0e04a00046d40d60343c803854070540e0351084806820900080e241401603148400c000b4058200030003a002c0400030240d1035030140c04156045400d540801003103500840304000d2a4034903e00320710820000140100c3e201e64100c00014500a002c0116075010343c64002582d1414602d800034000d00d4030548100d403003403034440c4021401e840c4c0034450340022101c4001402c460210540280c10100c0b0585000d4a504518480c900540700d004c4c7d015001140030f8890110802000281d071b43c242040c280c0061076a50741c03660301d02c1c03643e000c030907110034129501040c50740030081d400c030794008030325080080b000341e0f0a603000c0010002c2442d4460095110708403030000603900c0004c005d5503d0070f13030561200c900950240d07e078000501001d0710850b08160f8200007004503608202c020a00a0400024418480402c110700c00d02c0401c04244110600c804a44110b91145000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 794641816 1250 794640566 794640599
    0xc170a050a150b030601090603060e0f0c21031b0d0c02030606040506060910050306030610050616030504090606030b0301050c03010b031b040e04051506010e060403060515180a0f06 79
    0xb074001641c9201c0211984000e1460b03080c159810f01441000041410b4079410620035280030308010002641c1d01ea00d1142d44605009c2e2007410380d00101e62008041c84d080c0131100c805090100c0d01c090440b8807200d0700b429540404084658481651030000450b682040b0079802d0b0340b80c504104c41b0105041d00080d030b80b8940209503521468450000541c903881c1d0b84240c98003c0e00c042c280003820007100c0c0015199404c1120054041e100e803d0000300400d1140c1c0900048400203402a807509200c440c50b90181c0c0c2c00100d0a50901070200030005102c03c0c02d100708401000b4580e00059035014030000c250942e10064020131941c4000d20060000002100480383c1100b49110f08480c1000000f0b284400340c00340d81d0100076005031181c10002407010105810f8000b200f4550000b03515621075005445114403804000e802000510007400000c58681c0800c0e00315401409487c058448500020040b00f03462503024544000344c0c040c08008000d41c0034081140c0343c00c100078007084d4102080441c404101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 794643066 1250 794641816 794641823
    0x703020a053d0f090803070e091003021c0c080718050106140a09120c080607030c021905010902030a05010c0210090f0204091b080106060e01110618030f070c170a050a 73
    0x2a1003108082541d0f5072004030784141e440000d1090130b0380c40c149200c05410484005000c103a480198541600d081055103120344500340d03c9040741402c540a0040c0074002d00e41054199411800304400300301c0c00f28548004000790707401010540c0c01c0548100f1440c4036082228a8142031000500c0055000070300910284021985203031501d1031480102d0f1100001e03849440003e818500a10030322104801040035180394000319500391b240e50344100c0c1211210b803901c030010303004550303d00e40b5803441c4142110300324042c0c000400d15050580009041140905044070260340d242d0001d0323241901404160780144480c1c0003040016034649500b190655500b00080c403456483e0514010400d4001da9054180c40d41c1c0f000624007130304e60300002e0080c4918083e407004140c6000c004002903220b04000005100c6490240035652103411900d500041e01400b0900c282c0010305c41c1d10210242a406007030600d00a071202552149042d003c202e41c065100041d4205410555244010076000034805079100e91 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 794644316 1250 794643066 794643163
    0x71716060f1812210e010e040b04020d140f010f032619030605151e09060c0606040510060c1b051806090f06030601030321020703020a05 60
    0xc100d0070403120381c264080524001802c4110110307145686940c2c003001a0b00c40c00038a5800d210300701c0c0c007010796095102000001420507100306019489140c21081060f0054408541a03d0400002e000d90b0040d41d000300005035540840003044034800301540d0494040b07207550500354106a0080080384c50350101500c440240100b8400c98808040a000c03a004208480381e01e9100800c1c220100c0d84541c002c400010782425400f10b0303149040ca00c0104a680e104c0c44a6281c140c8145a682d5417009040003008222400e02110386980c54050090400c4603508014102a140a0040104072000505400703405400c1e14024444181c100000d020780f01d8120354030505032810100c04211003510340d0016034018000c4030b030030440401c0842c0d5a60041e40d0882c0c18a00c60383d00e51000298568013100c5017135143d403000c801000440e0050b1080204081015031910040f0419051401680e01031402200164840701541c000d0101c00c0c410750020000b14016a0092121211703107400c018080a440d410202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 794645566 1250 794644316 794644337
    0x2d0a05012a020d111008150d1403120f010e01141309080a0f120207030c0f1a0c0306040507081501030b060c0601151e1205060402130807171606 63
    0xe41c14809003185a0003810614038500e0792400600b50341e038070a4210b00619880b41c03076041c40c0d40100685031064182c01c2c1c4070501d14802070108541a451503000752141c80c03002d1001000c0000a02c000c0c441d88894030024042414400f0300919040e205a201c3d40120603374a0052010303c643d01d0008520300c000302ca55240305002c0a1400d00100106480200b038110009054172105030410390003001c0390510340f94208101034104049080c3d2003030b8440180040c480c02c1002c4005801c240041d06110f0288458101880403580d86910b944070a451068040a0100c10840c031490a8050b0316804843e43c17a00d5a204e05110285000e500c2d01760b5501410300d0780382c1c2c1e0020b91076190740c401da421540c0d008085030029655940030f05141101c040016001a0744070010403040450b0191a000c856880d17910602ca1000354407042c8002d040150155500940801540c1d0980d492903003080d014041c2e4071301400d0780741c0c5440c0054049880b02401d21070241c0241c0200c2e201c00d4600b40620007114a513041401c08034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 794646816 1250 794645566 794645627
    0x1e081c0f0518040501030302011d120409110f03010b190c0c090e0114130b060a1802030a09050a110306011202090c0702040b06030a0b0117040816060b2d0a0501 70
    0x6903540c0d90745a80203131928000005065054200c030030750303c20001c4a1403501d11042150340c0c48984040030080b02042c100410840071455900c0420840c40a548150504034002a955190f60003a400f01040040c0800c0e19034a48040700201110302c01c9504183e005004590350345150810355104404140c2c1da2546021a001c0081d003014040c0751a04d80045501e107040148240000c0c0c400c0c205580c44030541c40040c2e203d082440001080d50504180956040107140c07620b00a580020716200c8500d4507070700f0318000181c040180c8106140b0940401b001d66a82100341031074024141e0120045000e200381440258603005e04031500320360f110300100d58610041c008200900300840703030150030401c00401c00180d000b46a100c2065144240e81c0d28110000c41e049400000400341c6004e001038104010082080d2007187d000d8901c3d80c880c000208400343c3c03410009054040d82c48030452044034204134045156000c50810000310740841d000c1100d40e003824002060303880d1802034038800c0c3c08000c1980000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 794648066 1250 794646816 794646847
    0x3052806180504110123030702160e070e04051b030a0b150c0d1d0d030c0203010510140a060f0c11061c0b180c131e081c0f05 55
    0x9000300c1d00c401c0700a00d41c40300914000300000c0f103040c0c801c140480f0f03c1911642c82030b4030720307007100c540b05e6100c860840d43e111400e8002d61015004000358442c640e584c0c10039800a2003003000900c20742d15250070516008601802d0120b4802082d4030462030032040011300c81e04004000c2c0540c40c0802042e440c2d9a40809040081220044466006403240041185045100001c240314100c40068404026400c0425142c0401e032a40e01540070825a140d944a07040c48546140802c0c06460100504803c5401190844900b91804003100c2d258043c18844014492030710f00d42e01c90241c60101c10646080001081108154200410030159079202c0c024488044000440900001d011035641c00c0200301d01c000718090b580c050b61360b141c1403c0284d401443e114034810503020004a44090996465804110303039070040340b041e00720f031119400200744030707125042249c0544025000000024200b51003249480307220b0001c000b511210703070101044d55a0045014522142c1420919118400300942c00c41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 794649316 1250 794648066 794648069
    0x90207080c060a091e1502071a07050a02240f070c080f04030606090e0729030f0919050c04270f032a02090c0403020316051003052806 59
    0x300b441068248075101201d42d00c00b40d0720794803444840e0681840ca411180b100000034602820b14014010302d4003010f86030f900240222880b518042030f040000203510f085a50341a2078000c0016004165080640e0b0104404410300760071805042c0400e2824014418800004010b403003200e584001188c0c42c0b5020f00000040c503648842c595490b120300c01a1030100d070b04284420360f904c600341070000030071103c0340c4200180f0803041c00143c82d00c80e060440d8080400b0040201e4031b0b0b00210403518107540014200550301030542254848030f40e0400302607040c604803800e0040c502c0144014170280010b1800940ca000603001030704c010031080344e44d0300b840c6141070010002e0048074420708050320401c074900c20061051482512482e000100c01c00fa00e00640010400400c070b0b035518106d40c00007503d409141d10360f02c1468491103500d8161a6404a8242202080039240e060803001c3c081c0a10719020400d500008403500d010004d529200d842c918511804075010320b0809440c081b409860143c84d04510b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 794650566 1250 794649316 794649337
    0x3909010c150f0c0f05090d08130b0304020a0b0f03010e10030c140a060e06120a0603050d020f0606010c0b010611210d0f1401061b050706030b010806010306050a09020708 74
    0xc1010000c4407000080c220b1618902c080e40d2a051403010303218098140032901310659940e0b54100400d400903c0b4110f12521002d455444040c800011092410f1050700094988110290313200d00701031042c0f1001e148240c0125070303030f503509000f182611031800c2c1c20307241100c10340303544c00c911030b1107100b100440c58045800181c01040c10720800f08031421190021401030358261102c811059695404039401c186e03a200e120b601810030050360f102201d070106503580103141440006a155a00c0c2c4d94103180000c80e20615015800c030340c4811030015414070280d40c0c4500d017820b01d80c104003190390f00c464001074140030303050a20604810031002e540342000140021260b0401585210351078a0b0b0040726074000107044402c440c20318014010b80d9080b4007554005500a083d9500d50740d0802c50156203486810480000b0090b40c201502d0119800b0000703000140010323100010320702c005c4800100000001080c40d81451f003090713420801754a0700c0002d9012142c0c4500f0068a60b002440e008034944942503010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 794651816 1250 794650566 794650583
    0xc0f0723120406080609100b0d060503030a0206010f0b0c150c0c0105250201020c03041401050d02040603050105120f062d0f070206012304150504020a083909010c 71
    0x5002050441c4000e106407030040d119503800e580c4880410648010480302142002c00d203401c1000142d140300c0c013034402044400c0c8040703030080e00e44000c2460b54101740c1c50000103130321074001085400345201d8220043e1040520322403518081d5500103607500c60b0900040c23010440c0c04002100418080295040d03103e2040c000d11080c14242a02c12078403000d141e100200d04101541d03030b0b6805005201700c0742002c0e41318003d1030426103009007030042c0041800720503050110800401c2c0541c021413004101174800c80e103000901d541030200b4841c4107080b5400d101007581c00080e8003030381240c00280303195002499990f80c40400000c144440422410b40b0317400916120200c0a0040d84a92004058440c0160b9402c988403684c1c1c1c1e829a00b000c007030151f00182d820002c0350090801d42015002004082d04100c55100200d50f90310108007264025000c140c00112014144201c502c5034400100b8040c80810301d0503468000010b40003070b00038801d0200040718000107801035080e4021403c0040441c2c110404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 794653066 1250 794651816 794651833
    0x142104050a032c150702060f0d0b10050904151203021507090302100f0c0803132001020705040b0406030804081c090e280c05040501080c0f0723 63
    0x16658800794060100c0104141c00030180410340b083d460105580c404000201c4501c90034010300c00444503220035410f0b0341d0400c00810000d40c0703440d1300412502800000d096511b25a01124074100d0310004a5030340300f0000340340350740d11a5502400b40c0307080950403039000030249904108001042002d030301041d9410f6850b400c030401e0503000b240180c611210000741039580e40d41e4400c00c0340c3d410400d01000754001d2921800d141514800c201c5c05160754001e0410685001c819110a00c20741c104503020843d2945e156803090820982c0000380d0003c424140d1018150180100040e44a9200317010b0705004540d501e0f405181ea940c0d5070002c500450304202595900c035103422405481d2100c2240b488a07110150207110302c404d20404c00c4004803108061041d196440d110a68000c54070f40700300180c5c60400007116401c0e882c44510070f00d00c070100987c5960795124a0000054200c51006040e030b02900b80070301003500781100070421119503039809800da400c501d0018040c40c0f0400420340c281c000c1d51060640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 794654316 1250 794653066 794653073
    0x606020c0325170a02040510051002120a210f02070b100602030702011b141c0e090105010f0c08030f0f0a021c0213030206120708090d142104 62
    0x2140d400c1000c058069441101c001c8061000c440305142e50200c0841c50070500b00519010b541c01c03440948020030588022814540024041c4e90080e1400f00d089040244200120f1800842ca8000b4240c00e00240c140e03802e4034005808280210b007011070038002c1c0c50300c065001000898080c1c0308110490010001c2e258000c280c00b0084d0800403044030440d02c5280132a422a589068160444005034021071501c01d00303500444100c1881e484070050708544200e545c0011341c80d9105c04200101c07440050074221003501181c9009010034105009001d80200c1c500354544a41d40d00c6c0d415114282010714482c40405030444d014440c4510141c0351480200a01ca407880401c0c10039409059050081a119160f4124840c201c1c480c1120282c5e04141c2c001010030b42d014150040c007012194851602c0c6a10741e60307004114180e00400c0201900ca00c540c041185540c4c0007181c0c190440130440040c410b456108a0180c100039406d507644c10b0300c040101e10300d0542c81a0487c3d501006840c02001441400d1500c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 794655566 1250 794654316 794654323
    0xe0612010608070507050d0e040209060a0c02130c09030b0612060a09060605060903030304022101020d02092110090c050d060f0c0503060f1c0822080a0803070513050301060602 77
    0x28040c0041c0b102404140064803c10541300700c21741000c00740246004092003980d01c4d0708d4118600e5080758081c030500f42c4980d50100034000201c025125041031340031034810840300c901d0303440202d641285814284003185038056400400c8da940a0600040c03903c41750001074100b002030520312214490041001340914440e0440c03005280300d220240700c4207480f641045924090032040c1601035000740005000352822200354441c8404a4a9400c0104010758075a400da030300c81c61407003001c0383c0c000071340603d5411702d10089066040c1040c0c55080300f0700115071607902d41404910580c2019140c100c8001800782030884040100001030072241041d0581c030301080900621481540c007503140500fa160981e00517000c40b8413480c1d00529030b2a0325182002000000d001c0142100e859001c07508100f000948008000d280034082d07c081d600c07401720780008540000c81d190308100c00c0c0c0d410030544013000071550025650407512900300b1603110800b1400d50705031040c160380002c1c1e26600301540041d0b40303600030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 794656816 1250 794655566 794655569
    0x190303090f063b06030a0b1804020901030f06150f0801140c03130501090203030403082d0702010305091908130f12120203120c190206040c0302100e061201 68
    0x18a80062855070316a420b5a46030b4440d864445104000d14800f900b0f064141454400311814800e8000640c1c0001e001c62802d41040303038000c804039903940400507940341040186450030301128800340c0c64601940420011741c1c043c8030042508000303600c603104005244d0045240c0340341c08104105010303550b03002018005003620600381c040d40791221031030550311b0b000b036007c3c4182c590010301403454403110302c0c940f0700c4104240d0568455503170341c0170b0400607030701440108000c41c060388203551a00711161103840032100c5000d00d00d00c41140e2200d20f104084031041501c070000d40909000403d0b607900c6540e6030900e074070b00041004102100790702804012040015001d60150342088095450f115201c21201500b54041c4402c034415905e654000501420110300d82d850303051050b0703800c03c0c0b11480203032200c91060364520310f19030f00441c020030358038105100381030380322170398402030140d410b1a8035200f214405600020f4050302c0d00120345142e860203020025042c8038098405555900d6141d2070481b010000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 794658066 1250 794656816 794656829
    0x1d010906091403191b0c08030403020f03030a020a110609221a0906040e19081c02090607060c030e2b0e031b0d141014090c0f19030309 59
    0xb01650301406200205441c0340030401d81c428140213001c0750301524002c64114264090b01c040030750800c006036800100400030714141009648640c194410815400e552a6103e40030ba802403046483c625400544001034907003114207441e92070700d01408100148180c41640d034000ea88a14415802540e86a039001852000d1208121514040150105c160005084180d00129141c00726110f440d160b808880382c590817a0445070305650003a052184500c8504007a9403180000c2449811488020083c048568042c0e50861820a250000070100d0154060162906035103030807080c500c900a0f8420201c0c40c14010807125110701090415119088200181c41c8103a44400b5140d40700703002d03030b0310782072804001806440760030280b00f680850913859040c483d520014182101000c80c10000003201c9004039a0054100809407a070894241c6255004149050300351104205a440001c1100046101b00b1900c112402c05408001018940a544440c49131901801e000080541000506046621 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 794659316 1250 794658066 794658083
    0x70804060b10021b0a21050709060b0d0f0e120c011406060708180a060c1e120e060f041d090a0201092606010803032e091d01090609 58
    0x6101c41031105203101d503030200c000740e0720852950703107000c0b0940b0a0b243c0e00c0c0f2010740500c0440d5a581500c29058034440e0805000c40069600c000911074188904805030402080900c0725500d000355040903481640d80ba41880340d40da0300812440c66091300200490454101284c902040b5428a21041e6000c2d240504496181c4840400180e02404200748954801000203080c140d150b22015015030000301c00070800d41401c103021a40741d4822540b580074000356540d204105000c0d1030441d03c820262094000c1c43c80070901d0000014500d1200c0300f414200c3e0341b9242c1000c001d18800300707010b0b000303000100031601d40c00300d80410340300d00e032512280280751140420b8804c0e813110f0140c2d50302d40107881c40c064002030b030089041c09401c100000100403841160b10280200d4290100c8a081c1a400e0b04506d00701d03000001030013031026800d03030092048494200f80401c4e400c082c0c000c455030750481e4410911099228003051444500792003000c1e080b00c43ca90001c0c0443c20040c40e00c24000c0410701e0007100d42e5807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 794660566 1250 794659316 794659331
    0x509011d03071e08190f080f010b210a0b040c170105060a0905101211042603040b040b0c01050c1206130b040f1505010822050c040507080406 62
    0x20a444405068900d030240a1890010740740c0f518100e07503560300306180c1021010f0400c43d0004034414000c1c016905080d101e4400d050418000402d9103100e00300c80001c200d60f402c1404a020268000350381103d038003806d03003651590620000820341c1c0c0045100d000e030602190802480104070340110038000030440c0c0401090b1040c090a68461202100c20102d00700c41d00018000350420900500c4680b080e801c11241c11130380d40c0d00207002c8020f10a44900040d0f80d241c0d071503086076034030b001d51520031101166840c00c041c140302240c00a08003200c0300009403107954494035003440c020f10484010301090102a56559101e420000c1c0c940c0c000c4d15010025032070080042c210305414015960500c50b00c58220001da2615010404000c1900c00d169100b85d83e90035881a03541c0c0c8030f01c103c0700215418100480c00303030300f10080c00b48032030742540c0440e050140c514100000e040c03460b61903035031a88180070b91265111060400600d44102803000607041340c5404140280c50b034121060070f2180b031103808103101c0031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 794661816 1250 794660566 794660591
    0x1030e0c040e25080d030902042007021207120206030a2403030207090510030602091363080406030f0518030406120905030708121302150a05070510050901 68
    0x28440791184d19420717049407512401e8180b1076088948090300040020881c030310318420020b40d0000d400c040d04c01100c0c00284200441c1400f8001c240c0d20506200070b4000c00c0e26080c941c1080d4451014005d110f0140000050408226548142e2008085060000000184000403200b074041404164054440c01d080081d0000560155610840f44450284490b0345150340c5d5130060340201034510340c80981006a8100301e911407140d2280f10080c905404014800d00300803089001305e40e407a0410741203002070005800111750140255180300c4080340c0c440c00380c03040703c3e0b40e20300240154020003486c800580042c00c182c0c1900030b0041d2140794107081016440d91102c08401090750300071040541c0081c4010448540182d0031040020724842010034030f001ca580c5d400341154410b040403031724400b000c0f80c1240e0758031240058942c44514400c1c03808612009800159840384425802c9030140c0000901e0008648600705a0380c4c0341d40c3c03290403240d5010345450301c1009004c003101d4900e0030b0741c81e03c11a280b48 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 794663066 1250 794661816 794661883
    0x80307021801030305091002010b0301050703020a0f02120301140a03050f0106090e0a0c0e10080106030f0308011710090303180302010b030c060f040b03040309030c0609050a05150901030e0c040e 85
    0x1204e038152a0b20b841e140500d03041c00080040820400290b5684807021714460700c0a0107014451001a9030040c0d607a139440001400f0b00c5151100c04045500c000c2d01c1c0722120242000712810740e50704a000280c624103000000700d6000b099080186640100416070032110015000320040d070310710a80600c1283d041c3c1e62525510f641100740a846603450581c10800754402d800b4842d00403421038040b001c810b803140c03052804c0d41d555034411100403000301e1401e01415400030581d4007400b400c21086080c550b5401070260b441e0100030302d046600e40c2e28084c4c401018000e50141806008500c140085080700381030280c0201020302106000e402201a01d640c0c0d4a803180441d41d42c0f8445410b031600309810100c10401542008004800344940c820001c00402c0b0280340420040500e5500c800d400c81c2800c0501c80501c2d501d5104a0280c1654400140000460400e45040503004c0ca00000d5080c031241d042481d10101b150f955402601c0c020310b240d00c00c4408680e08030f0341c210b01e09501d510079079901c000101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 794664316 1250 794663066 794663069
    0x11107030c0c0e0c18010e030f3403030e031e01020c06010b09030a0b06030709050412091e0902090103110d020c76080106140c0313080307021801 64
    0x8000c0800c010561507913440c94620451744c0b90615000c540c00d4a01004240381510601081d06194413051903c00381000c07035101c248111010303c4810001e03000f18055648a0315180c04010b0074002d8a11004000703403820032400b583c01071403c1000d41103000486440d4000c0d07010b000064030781d005c0c0300700128812040d2012a02030541c081c0040c901e40c180354882514800c0b0241801e6858012a00002202c25903230160a01030cd0007001e401110380107030780c809130200d1000c0d070141114040f08080394a03082d003405240b00444814010159590020000480041c4501c800c032602001c008220103d070407207a131b8060546100440210740000c5103040d446855002c0710081d13420f01c0001040c09030361083c5004180034040200c0400c4581c421798610038110850124070b07500018207a0409500340070080d20700c0c0171408885a0916100b1f41d414204014419420301c8102d600c0c0507800600403044a808208a452490b9511600300391039482e00e04407602c03940541000d038402c01c0c00741900a0304a40c0d0303000f03207030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 794665566 1250 794664316 794664331
    0x21060c0a08060406050112090816140706090521030d14060102010f050f1506070602070f151b0f0203070506190b150414040b1009091d030904020c011107030c0c0e 71
    0x220800c20440707207c001c0c01d101309046840c51028440481c482154461030000742d03103e005030b484103902e403c240318a07112040e4170080820003543e204101035107030700b0ac0c5103013000360940c13442048110600001746180b090400b10750103a4504519120030010902038240221400d900900c92401c00084c0e06041d24420b603403d048080900011410788a622700500d03142c810050941d03824102c09807100c2d0100c4c2c002410a451444100f019001049035480702054640300c0c0004c208000784000101e03d507210184080b180501c5051280200301d980200296a212036000381110207a00d020f800d062221801103d40c03090b600d0805919041e01d240000d00300b09484003070044603081a20300031422810f02032000741300382c10982d030b050903410b291254002d010340341c1051703121403000b90b00d0101d01e2003c0301c600c920080c15000d0803969600030510080b045514058040b0b502580f036001d02d020b501c0c010700c002d806c0c2c1411040e000035078204054000c9030100f00c07d400703050356241065650721070b8415603100300c640780d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 794666816 1250 794665566 794665577
    0x2030702060d0911130f06060807080402040902190807080606010201020c1c0e0904080c0d0203040f0509100b04060c120503130807060e060a14150102060621060c0a080604060501 78
    0x10340004000c1d0340203c026070f005002554078058001c01103444a110074445400702910344640000c54016402128000c1c0601e18009044e80b800b0300004101001c084c0000b88030390b881d082c40c1c5080d5641d80007a000071240040c40900f810b6900d4104c19030701c0029124103d040d0041500181c0990b0041c070070780b843e44004034040c0c09441e0b1440d085814580b03105030803000748254103040150f03a0b01c82c070a10500c1070303200d1a034550380ca0106001c02403401c4044030109c1c0841d4001c12003071100c07100100c88801211015602d0788400e455214030080111a25080b00e9404280030030300092980c1d001e0307503060b101030044c0c0c0002091640d0840c1143c1d00d210859060041c0038090241c2c0c9e0000d46110001c0054a0259500140d2080c0c01c00c48503083c03c1e02901c00781000c64440351452034940206035400c0d002140d042021003d0302038000040c0d02c5080084c031541c481c40081c0c8010f00c142100712410080b2003038845c1034400ba80303080c40c02c0d481c5076045494500c0000710b0742400209076041c144120400d6034416103e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 794668066 1250 794666816 794666827
    0x2040f0b01232a100203040203060a09051c0c05030a08190501060203040e04020310061e090605100509120d05030703050c09010207090b06040302130204050f0306010b0d1508060906010e070203070206 87
    0x41c0c0e0381c40f000300241d0782e48407010881000c3c040320a00c52003c060425000150344ca0070b2a00400d450a180607080980c21850903d004000400025040500c0c0c0620b040d08000710942c2ca0b4240c84655a078400680603003c0080e251010360382c060348640c0700b143c444d24444180341d41d03045000c0c22200c0900510000d41e00401c810701c180d0b40c140301441c0d40300c0c1c401002c64003001c0038282c0c00c20a65040381c1c032910035291802c5041b10303c91041c26002000e0309604074100a040e2034280001c42804100300c503c81808800541a0b07259100e5140c14001c00c224141264907007e40b00c2e070004e00d940d0084511100207840c1c8070204180070706103800c80e002c2040503401040e04a05190200c002010400b1100c0c2d4802010040000140c84100000e4200d203e403800c0141c03200e2502003800800d00b01c280d0118480d4000100500c95141c00c0c1068039109925002e00240100090011104800c640e4210141e2403082c20300304543c4890005000341601c0c2e002c110303804140c0350f070311050380e8a00801030000e5120070103014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 794669316 1250 794668066 794668087
    0x5041a04150525110601150e0f1f020708060708070c03080a021308060108070f061202090f06040312030b0a080312091608100e031606020d0902040f0b0123 68
    0x10035908650000803900c2040c3d403204841c59540d00c2c829803d0b0220b82c401d21098050403040c0900390045c105445000303001030707071500018040300c10620103a00c21080c803600c0000989880e420700980014007017402203c5010110083e40da240c0510444c2902d00c500c00c000341c1098420501c1c81e0080304c0a4580600d5078055a405442201b0018043c1c0c00303281e0b080c41000d0400080d415500f00401c02d020180c102941001c0c04a4180101904460060032409000308040340e880a001a811303020b016005844800d10400664003041d1210f215a0207180481c001c420f0015801230000c00c16000d8400f04036030300004091024502441c440c01019400501000f00f8a0001d009216400f40006041c1c641c00e032003500714102200c0c3d072030700b094410340e1101d030141110381c5640c0b00b0305200640d02c10085007880d900c00401401e800070040024400381d00420386080141e090b420000c4840d41c014000e00407004801e01c10b800420702141001d0010b41c0481e0301540114029012040300e01891851628014040a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 794670566 1250 794669316 794669321
    0xf1e02070611031611010905060f190501030b06011209020a0501030e0c03121c0e0c040f0e010c0513050619030b0d122610030314071505041a0415 64
    0x21000d48400e9240d2800c40702c1000d80b0300c0218800c0141c50b0500c0740d1200d4520000703100e000711511007056689807000c01800b00354006031041d4032150350011401a6500c1c030501400d40c4100e090f00c50441c0382170100100c01c000d441c895041c82a06d00fa070303c900303050080540c034000b641c450140103900164044070074400d6501c079411138a4170700d24281c2101c60010b284400310385001c0d514100b800201001103186044103c0309a800350307200c881c0c950103005541c02c00d4601074071201d220158501c100d603148200c3c010b4401c15005030f444124204000c0000d501c800740042c0c80e60340000c104102c01c013150310012900d031070582c0584107000c882000003031041601c000181d005001d0101d48981c01a0460b201c0000034103100e004d40d1913106950360701803410b07043d1051850001e81071071405240c10701280400c0103000c11388a50f101100c2c0c051a10055045405080109920517944090010503da81803105415846d410250050b0720074554025803846850100403101e00c10b4a0081140b10101c18090861407982c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 794671816 1250 794670566 794670577
    0x906010302090d1b050f01050403030215061513080d031a0904080408100b0306060a050d1b0803040602030912030906160c0512010c0905010807090b0f070210050304060f1e02 76
    0x900f200036195099240c844c041000012080c04a0f48003103810300c5141080004c01d194900c007170a000d401c240c19039030080c5d11a000421b41040c2400b900300024407607951181d2410600d81c41c2d41000f9a42c0400240c0a1b0441c0941d020f101d03424417079040314103452840391181103c0d004400d00301d0143e8640003000c100c24008081c0065a020310b0a00c00404c08800510048082701c3c0f05040000e000b40403442070505101d0018101481010720440800454445034084000942e0120325808503120f0b0180c0d41d00120480c2c0c1010b82d05110105021482e01e070000002c1098900803500d08002c10a8001525540e01c035444c0095003100d8107000451020121464070b45406118050f0500280d850340007054400b1100780041205a450312a180751140d0841c055002600c0d080ca80b40f861454045405404018980319506204030009956108070301c0103410380740744039402401001050f0b2036240003061500290390544401e45440c201d0742c5c5a03031076841071044a8000d002240c40c07040044a41d00c3c000e4100c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 794673066 1250 794671816 794671819
    0x209160f11010b090f01061b11011214270102031510090905040b010306140105091603090f0804081516080a0216080c0c03060903070f03021f0218040b090601030209 72
    0xd0f00355084069444800c1107100e52058120500e1350761400070002c00000c0c41d00c04031002816042886000716240844140001c0801c1c01e281d0149e03c01140013000400c204600141c0c07183c030342d01c1802216100c0e1030306400c1504080400010b802c00c0d92100908038070040d503401a040543c5080c994540c1440a00250200c03600d0401d80c20084c1c4c0d680c5401c06541e01110104e841942c060014810810305108000040c00114181040756052001081c040c10028020035403a00b0500301c000011b43c8030360400c40d0300c150301c6821400703081e599285c002244c0d085402404664003603a2540316004140181c201d10403182140486038084110400f03403621388014040c0021590200004084d5460203080458545e01c40c180c82640e50300000344681c100040d0f4008a482078206c0014441c0c0d0035030010a450138160801d40000c52200740f441c1c182d15104120b090018107103100c20ba0800c140800350b0107003d6080c015245a80a4919201044200d5028170300c4598060804408128954400d81c09440c07421f00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 794674316 1250 794673066 794673071
    0x31112061c0605130309080c01092601230708070e0409080408011e050601021621050609100c050712080903090d1110030204080607030b210a0209160f1101 68
    0x30740d0346031401662000c4603042c450303c0e643e01c094010140d01c080042c00030035003c0c000c1c00856003c007000a014503228401c1d510b60b82c900c14500003480c0300222003002c8056110b0001c02000480c0c02d11410700c0c43c440341d4108610941c290000710018011031041d4444d0019650340d8030740620450401c801001c002d00240c80d85403081c007000c12120380c00d109a008078545a40f05103007a222000d04001034641c02002941190080745400130b40080740144002990395241d004070302400610b01e0f4030548012803030050040e10412050002e6800c0110307041c981d07106400d00611262500c000c05442e0f40c86140401015241c000500d502550702c180d042c20f411130210310507286410300c013100044092001079010f440442c500080c4c600c90703240001c3d40c01040c402d6410107504040c5400782442d10350b580144400c09041d1520f00d00441907541400c62100d014010890303a003e08400c0061a954541002007207028180540c0803403202032030701318541d17901038083d80d940140c0702107010304680901084030940015034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 794675566 1250 794674316 794674369
    0x10080a02160c0b0d05091b121014090d0f08162f0c030a0f1403040902030411040c140d230403180b0702060a0f0c0507080d03111206 58
    0xc00c4074103224020f20140743d6003615142c61620400455101500c2505a5409030b110860700800c24070103100703076400490b0b030880c1640300326070803d040c05010078110003000d20b0b00030094407084984148500440d1504100c50300010b034900240d5000442080c0c41012800030400101204450079000030200341624084005104405407400031109103034411300d0780140d080e80d03804085000c1095884e00c6504800a01e4060705544801240c0040d004016000640a48001080790402c008a070300400c5015421507907440c050405113803600d459003020744503034208007284003010702c10104909444000720756545055454064417000740a404039002441a622440c1c103111402c280826115a0180e11074000051500000040c00e402c41e4122403041e075410300c01c190168a1740000d8400764012420089a04800c0c1034003900c0741c554643c0020801c5c0704080c408200315102240c0700c42070b9a80c40d1802e00521844107400006406000c5406044007480e0380007a9032071600441441c540c0c07120403a04207900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 794676816 1250 794675566 794675573
    0x50d050f0601090b130b0a17120307030b040f0902011e03060504020d021902062a0c030703030903030b011112030411030610030b0a05040305030a050a0f02040612060510080a0216 78
    0x41c000d80c000e88040f0303551112001642030403944440303800501401001005045d000113807000f0803901803042451480f41c000982c086e020460224182c46031400f242d04c9280c030440080207002c1d0490a07130301540c1002105400006607020b036034442d541c1611032909255101c4c42040c603165494004030201900c8410018a544452004000720143c0c000f015a80f9595101c0d003140450a5000342800c42d4007080030840c1d2a10142d084510640304407003911180d03015002c11300000c1c0101c00e000480c80c00002a01010550140c0c00421075a10944040c0096920900191091404a4003a40c4643c001051010144803e000203590061146100d214202c1e00c90b4040303882c2c03020855410031540201c0344244180011410401d40c1324000c04018041458603030790041441c040070300900f44030ba403200f01007550f840a54100c62854405050215150795403110002c140200456000e140c441c80c0040c0890513080502011054001d15107030344000c1c0d110181560000d6000306103e4510750010010075000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 794678066 1250 794676816 794676823
    0xe161b0f150606030207050706050f07110a0f091b02070503030904201611060a0e09040c180b21030301150e030d05040303030b09270709050f160306030c050d050f 71
    0x64a41684c0c01030b00c0315114540b081c5400a08d8001400b407200c04d120341011041490102c8040d03940c03113400c3c8000311100d50701192083e64981c10040f994140064049002c0d107452340200c1554541104070360544820740c109903200c4032180207003a09504108450041070607e50090026000540c00d00303c8107160000c81c0001d160000300c84662041d1440582030288041d281c0c2d004000b0500b00c9a080ca04024032102610407581c1c0c5152a0117083c4203030004050062450300b4400501c0c03800c082d007000380c82011540c80180300390b0444c0f521a500b9010080c1c104808910340290800761000158656400c01043e51611030b41650044100483c684401c00191001c4c402d52410960a4440540707480c154a4098166001e58840740d0090086608200c08881030281c0e450071001c5c8010750f4044442c08984550600038290046c17046179007024103000a00c0c00d210051807080110310202c2001030b012200450039180244009825821404400e100a00c1c00384800800d0f82e00c44e41c21076500010f041c07959402c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794679316 1250 794678066 794678069
    0xc09020f2502011206061715100f110303090d050f0d02181005070f060506060c0601030f1b080303060105030a020418090b1f0b0a090e010e161b0f1506 66
    0x303016052030725404658004105241410761403c0c140403042c1064001805481705c0e1100350300c3c050000c0b000c0340c40e52040c0301c60149001006003d400358240c01c460042c000125044940d00000d140000346543c442c4040247d900034001070000d000000d20341d2400303d94541040d00300018a5104001d805801c2d50305100a28000c5200da2110f405c4103000403c024800624042102c1031003002c20081e0001580303142550201540204009517070389400700030030344078010070051040e14071546001005000d41491500b960f90300c03c0103101c8500e81c0d01028080d9941c41c0d44100d550341c1e030062011620a44c0a031000d50781c041c0d000c5400505099032401d04c0710b90150610042174080d07684043c03001c10301a88c402c100c1d5115540c1002e81d00c8500502c0409a16040280b180c1107405001182d40c064076803043c01200020458901d0016255845611070b034903050302510ba403150f048111070341e02201030203012500000c92001180b8001c04110b40c50f00d070101810380d03800b2101903600545001c01c8607201d00c83c080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 794680566 1250 794679316 794679367
    0x120a0c05060604020c0309090a11070501060311030c0604030609030c12120f1104380c010b1905090402011107080705030114010302150c0f01060608070305060406030c09020f 76
    0x960041060a01504049002c0c00c0c25025034010400b0340505d480020441e0a0343d14103482007191136807103d80d1b05004046c3c185041040d0440042d6a00c04d001c0150843c0007642e01522807480955400000c142c1d5500d00c58510503000030b010300c400c02c00b281150b800440c80300d00a007001101c02c0d1a85d0780d07407401e000381c550b400c038041081199842c0d03162080e849441450b1000751000c10902105028204090040d4816a004004100c500040c580c403090105400b05248044800d09090391600441c4c4603080f48926080d19031802e000800f591415000014513600901e000f1503180f82060103010180400820507030500921008001d9404001c009240060040b0300261480f41c0c2030404044c00d644100c00d0000d048040f0360014809030765000005503c02c80281d1185aa0300408420a4205800c800f072200155103030044c000798064004d40800d05c1400996020022a0f0b110b07002c10046400700e0001601031480003c040c454514294000c00b250703031203482120304002d00728880411201c1c800340e450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 794681816 1250 794680566 794680577
    0x4020f060d0906022a0705010504140d0236060d0b04081c0c0210021809043801080607120c0302040e13060501060219081b01050f1605160b0702120a 65
    0xf41091072460705c0340c105100410340079110013403500c1c0000386280540d004488810b54142205074540c0c0d42c41d642440d4095016081500c0031030380101c000c0494454950b8401c0e00f401c1004110215a0110300c004d1282d0030003428010041c40c280c40e641600700700100221000780f401c000214104050307009008500d503002c0400724803c0007480c00281802031031001d000f8072900510480039011400e003191800b4400c00d8680e54903541c0c0c1e600300b07100800c407112a0246031040c071206031801200200d815001c440192115003030f06990b1b800540742d884208a41c0100050b60040f03001d810704900380c0200721b070050185000350400e03840d081040c0c544c0000b903900402ca20204500c503010447c003802420300500c01c0f030015200660340c1104001d904e03500400000c0104100003110181207840802122201c901b1030000c0001e850101c01043c4001025542164202d10004c5018215840f0390200d41104184144078805134040340d0f51500000c0001d0032035000c0d4003464100509480c044005458180011382c3c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 794683066 1250 794681816 794681857
    0xf03051605070627092d0c0e010c050a020925020a05060705030609150402040f0803030907090b03031c06080d0f11011a01050a030b030d05090306010e04020f060d090602 74
    0x20300420048906100120702895041302001035103440c003401c0703c2200303001040d0b1031854544e1050890280d00d022140b03403091041040040d94a502c018070f1b440755500d410740441c0c3c0740001507943d11180b0400038001d03031200400b480107003000d003056034102140706800b00c40c1141100c4002c403100440c01e82c5000590103401e084d410300c80c040020981000d2242412891800c00d10042500e042d00100b88089007001091180040d07100c44d41224001c2a0a100203040c69860768102c2c6d48a50050360362007818807618402140d100c1680c45604424407005004601e4504040d21720710107071031280c0d504184141c2d134503400a004042071050000c60010341d42c5180c0301940c800c002405814919500b03130150b1b071515950401c54440c036032070022402002d0900903280c48035800c04501416180e104203400d4040c0e021420398080d040409452200022416540c2d941c0c3c8413090b50704698421140a58480803022000116080c184010004000e00460104c6c5513149034450f50242c5c0d1003140c0303039450703a0038880030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 794684316 1250 794683066 794683079
    0x2a06020a140f13051509100e1309110a0b160201020a0206030a0618021c11130609050111030306030a110d0f11090f060f01030c0207050d0f030206060a120f0305160507 73
    0x145080a002c04617070030310782004c5007104620b050003000d0300c0d03e0180141c0b08000210354000d0900340c802140040c090300d07070800141d14890103001107450440c0d040c102c0b032111038618500400088240c41c20102040e04188584481c101d400740c90200507810340c06100034103c0503031151030043d8800c030302c41c040210749240340a480e103007130501c00449024404d1041c807c05407901118000303411a07440b10900414040800000510b1602c034000040302d17220888070f40010b00d1340d000f1005200b242c0e004d0703d0b0404196070000d0706075100e00c000c0702c02c40d5064200205100021300d108891061605015080c1d2800641c43c0c3d880b07e41c803c001400696100d05c0354000c085031440c0c6400c41d40e0380400100078050315404e001d80414118210390340943d05140d22030b0000c6c0c81c598400c02051000300002030100400074054180000a00c0d80381405178014065030300020301600740003106504450160304228615407050301e602201c00403020080381000820840a4842160810fa160056002e080a0100c0c9840c010307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 794685566 1250 794684316 794684347
    0x150c120f02120601110a0215090306101715041b0e0c030a0c0905090f0402131805010b04060602030f0d29040b010207290708030907062a06020a140f 65
    0x2c0016042119500c001c14010340c0101b2442d031516410b81d912807001101c00111221400f40b1030109402d44180c50130030065140d0045043c0465030882c6101d0a252002e1222a407220449001c609020410b000800c0c0007803c868212089000072040000c510394030740103801040a01582e00c5100081c000c0140981c0302018405c2072946000c03810100e40c1d41d231604011031420580240541031072808040050259120b0342811151039040844c00c001e508032802c21519081c1003280305940315844c19401d41401e080c5449090140e641c0c940080d0708040040d0092480d0f0b9111884030150384e078403502500d002d01404001e8100311400303041082d0222800006201c12140700607485411584000c4041210b12803100c202e40303a081c641000c010480030b641e20310722918401d0141c014001100007003040720445003c11544140e0309640d64130580480007043d01c4503200a0075480316010308519003031800290095000313045417240c90402d103882502e0000741c0c651070f400030004142b1740711002510481c00c40007038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 794686816 1250 794685566 794685571
    0x15080606010f120209010e030115061101110702120703020d0b01060809071401050a0c021003021b011e0b030c181f030c0302091906031a01060309150c120f0212 70
    0xa1904802100b4000b01c01000c4034008625000782c1540020078400991240700c0c0340c98010310141c000e0020401c20900186501c81500c202c0c40044d403560f0701110a08070600a042c1040100303d001420a281a000c1014041071100100002d00c06c00d1000001a01c80a1902102c076014840e50398281d89080b00c06000000c00920002c0c05811400e014001925282e181601c5100c0070701c0c220761240c0e45024180c808103c50080a9400030382124824600740d41038008058150600c02d8a20304103007101c10070744c2a80c1c1d5044c8100100580c032080249108525441782d80500c0005041724284a081c0004c00d03030b0f1200d000d1160300c460b40c1250403c80190f03054001444080140000328150070300c1c3d030b00c0790704083c441400024412601400494803080104a100c808180a25820840c16581e0710300740441c80525185100c1380711541e000001e04e00e010b07100d081d170a29088400c0c20040c6030000c0c650310042c051600000d0510100070b10140c1041d00c94401c00002d0000c0b0000180e9800a0320b0342c503039902030b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 794688066 1250 794686816 794686819
    0x3010312030b03071707030b0c13050603040503040603052215060501020a170d0e0706030f0c0e0d0609060204081603171908090a0204090b0f010b030903160602090415080606 76
    0x40481c1c410b01c6480025100048901500c220041602e502680504000295101415a603000c0040c070900071801001028a901d000030b11010095032281444020f010841e4090320b26003092001b08102c5c0e0094001e158403032401c140c3c03070549e50300c8258910180c1010000c02c0d62040480208213a00340b4030f500ca1a07019180034002404a031040f40d030b03441c811000f03411500d00001000b041c1c80081c0e41d0103403c1401c1e07050509054031802511210010010001740c02020092401c02d050817610600903920005158800341c030300510840140c07102005007103103000850b0304507402c22000a062a0600c0480032903000e2405c11b05106140d402c041d500700f55910302500c5010801c0100c1600c0c42c4070035507080c40307440d801d091440c05039403140e080c03c2c104106060040c1d040b0b4180028402000b01c06d5020500c01e866013034145446913283c4801ca0040d0100f00d440c942c55a00804c290f240c0d90b210320f180200e0081c400c610241c0351000d0a00410192a80d5250007011240a254103008054081c04000e900820 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 794689316 1250 794688066 794688071
    0x50702150a1d011a0d020604030b0112050d1704020105071b09060509010f080c0d0f0503030c19020a20060d02131502010203040203340305160b070b040209070504080a05030301031203 80
    0x280296001013030002c81046807045113813005020071912180140c500440c2c00c001c15080560759800c040381e80801d16803003210b450182c00c0c0482c00160040f540c0901c7e10780c0540340784441390f031942d00549140d40490030076154469541d42c00450004100a0a00607004016010034594a00030900200400681106240b1000410b0038003950302d00240a0100744000c45254120109a003040080000d1201d4041e02c0c40c0000010810100024002841084070f101c0803030b428000c07940e03402c0f80c840110320340007042000941001203558601da01c60382034cc031400410031894a9025113412040b41d0241c51542038039040f0711420003045008140030003805a681c0000e51071403a1950004e91503800c0c840b103007140148112000c0000e0001103140c40c01d210300f030102055001d40ca0381401c43e0398805030058882d2506855001107140d0340c0079820340790801d60100c40d400c460f0301e035942005601c1200070701c20000c2141c1404005400d4a040103c10841e41c040c0300a144c0d694114241600705012281413007007490b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 794690566 1250 794689316 794689331
    0x1503060e060f060310080105010803090901140a060807200a020103200304061812170709030c031103160b07030e09010311040f1e1e1e050702150a1d01 66
    0x807036429a80d182080102d80e031035a03980e5500300101110f17100d50030002c4250b1811001007500e110000081141076411503128003107a0343c0c2c0c558030b140040c03150101d0740c00c4811200f0030044a40180030294104ca41800c10b0b20504000b512800c4c151032850010308400d0340401845020355805206031070091690221a55900200c444038074550301c0007600041c10250361307065001007a142c0c0110001990317880301d80081070140c41c0c1d40c0109551204014102005101c002007408640507804020450f540540380701c8808d8915201d06402c001c0c5232a5032601402001e20301560340c940380c1100d001400380c040c02d0503220b001e141801042d03d10943d041c613001e02a00700c01400450340700b0090440c1c1e84c20480d804121103d03d41c120ba0081c0c03051207848070803804400c2c010324815001d500052400039420045028608403007204105170784074101048820400300b0741c010355851302504070307aa201c0c070140122100705894000a20742c0b05412100544480d0b5114a440c50412402c8801c03407100360400005d10421 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 794691816 1250 794690566 794690569
    0x50106080c1c06030b0f1e060102100b0a0807261911030709020d02090909061320060d0b0f0f06030a0209121903120510050d0206131503060e06 63
    0x103100d002c4840070ba01d2a02c800031400e1403000e0b0080d030081c583c0100c010015061641d014002c8980990f01c1d00c03c00103d00d000c6403900802c01440d940310300740503401080034001915910b0000c0c00060350041d0420000040821245070411908000f804174110241c069460b1000300c0700540c032110304000d400d810025822007401d1030111403040305900701a103132581c03c01d40c400180c070b402c03070903480026254000b190640d06068a6805841010b4090fa030106541e03031341520298484100b110b1041c00040481c1e100300205030081c0500700f42c5444080c2d91408000d1948c0080d2550b000b24003040b45042e00c1d20001d80c01c0741442c0042c1000240c1c292603078034040c0b4a0030001942408020001591140d011840c24171603a5000301c01d00006640500f600d1300300032041c56641007290f4280003500490410a600050740203d803003068850725020075040d0140d4100000c00c02c0340750880c01d05aa001d2800e010004c1c0243c10380010f5001000f03070a55490100d444e0141c094183c81c440d81c0050f0705000c0c1d060420402c3e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 794693066 1250 794691816 794691841
    0x30607080a02280f0305040b040f030207081005061f02070608060316030c1a04080a120c020907081b040b0306040903050705031207030b1e0405071e090905010608 71
    0x2040150410001554034504500000c0c05070404442d1035070b45940c10003039031a01e07031424801020784541d92001c0c5150b43c224140c0c01e449094800800454220b00010701051009900d000fa542c40791043d80d0055a0316542c407880e294405a4201036142c0d15000d106080c0341c8801211a80b04a0300c10b803801190b0407a070080d440700101d21820081c000081e0008106507028049210781d102124010008107172a130030041d1440840b8000c200c0c031070400a01c1c410340da09814003554102ca1140300100010310856480e0311042140342d2240341400321041100700140e03500e184441c031444003951001d4445c54219804c1540418410824601020030441800391048050031a41d002e0b07801c0d035002c50002c80c00d2404075414460554013400c9030002040f861643d00c1102c484500900d841c1e5000c0c864402c00e5001c02c100d110f60742c0d044211000803003000c00e229041c9070300110b520005a040c14440705a81ca42c601840d006140c5003a80001c03410302d0705109950080c800c180c09012149030810140c80c2c0703180d44201 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 794694316 1250 794693066 794693071
    0x60a0c02150403111203040510020702060703050c0102040b0c15010e0603280204020c030a03050a1a24130501080c0c06010608040c0305070f080d03110a030b0d0c2d050306 75
    0x25918a071500042c02c1c18051600420383c040715104480610310504201829034000f503c2c12910b030300072040c130a03580c03a10078000d550500b45c00504141c5010b40da42c0d400d455984c003064513842c046d5000d0000107080c05151020313010014009002c1e01c140d01c4909030010400e41c050b003144105000d501d0a000180d10002a000c3d20b449a280403190424100c4806600703540382680000d510500005401441074004005031480242940b0148902e45a0110b190301307403a0b819030076550f2440c03200b99840903880d1201c640c6004d8000c1120089246503590241074080e8402c41c15031800a60f000020000e82d40e020349044c0e40840c2c119006410b2910b030349400c4d40c0b07809062141904100780d00010806028401036060002c40d80503040f610429941c00380d2094000d9544100b4a01e400783c41229205a802406001d00e5800240742c40c1740b90035034000301600201a203011842d0092030344682000000d034800d01e140090700307007440c1000c07401c0851090500600303000310101c2c04002ea02d940400142c2ca0000702c1d41e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 794695566 1250 794694316 794694343
    0x12120c050f0a0306050d0305040512030c1507051606021309050402091b1201121401140711100e010b0405010b0f0f030c070209071e03180f031106040b09060a0c02 71
    0x240c2d55218001d0403000380101e6002180c0c02204400c0400426421000034011500e081c0c8107100101c0d0314100345d64603401525080605900b180c0011034404601c07010160744284d9034200103040004a0503104c0c4441c851241c116001d5500081440c00c1c01c1406070184020116017800b4411890940c2c082140004050140c541411011500c14840031001040d5080c2c0343c560818070200d5a540e40b1134400140341420161400c2c071390a40d80703c021046c1802a580e00c42c4a041a4080588402504036010001e031040034145004145074a000d0baa818000c418183d10014000f10303c0c4072150041204490060340b008c08940c0d003c110021148001406907280100700000c2640c882e40c1d0b40c0440c000318890380308000e504c200039008100d01c1c903401c00714800c00f00c0d8184845a059810603c2c068003190444030800c40f80c6014010043c0c0021004031480039401e10a2130119031b03260010340080d140c00d109480840d943c0303000c0020003620401c05c208080c1c0c81070100b001806095840300010b52a48280381045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 794696816 1250 794695566 794695597
    0x42901030b060a0b1e1b03030103020406050f1018090606020f06090f0604062004060309060516270905180d03020f03010308070512030c07061803050913110712120c05 73
    0x50383d0104d900000e81c1c600c00c6030310b000ca1141420307001c00d0302c0d07c0303620900003280704c0c03490114042113a041031015007045510103003038420100c21800302612183e950040504040075074a80209000c42580680f90003000c4540050000e5124520000d0a10100900d62041a4811150581070043c0014070b00d80043d08004002600700311042c1c1c2108040e0f4186060305c40c00b100280026445a1561150140b54041c040030445612a6008000700b80e542c40e003480d001903020140620f030004c1008000144034001c1410303528066450041800350b8404a803141c400840c541c07203d16007030b90144200400c0c04110700c0d04528000d10701c1503850b900c4c00180005003402e50301040c8a0100002007004a49100035601402d880c3e10b840c524a54a0758014001115a00d0411810300301c40600b006425589551544615080c07594a00c140590100381344c403204aa2522400388041c41003400d001004403500940100f0080681c0b241d01070150300010440b900c1144c46c1030081c07444140c1c410f0580d00080b180c203203034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 794698066 1250 794696816 794696857
    0x80d0801170f03041205100510230a060e01080a05071d040e070e1b030613090f3e090114060c0111030a1506050909042901030b060a0b 59
    0x307482c9400115401041c0a210000b4041600089030f810121050311903012504020707210607000c0c0a941c0184c0d40da1400f41e10024084c8140000118003409003146005250403191074035000481086940c1d0280010800000610700c0da0350340f240c0540e5110060400c24805800c00590003852802c0c0640003441e4115440014000c6645c0c3d5000385020703411002c01c50701019101d59049031900782c160351400f004914840c1c101c0c410f000311000e0340e20500e0000d100e503c04154242c103c0015040c2e1400440304a208004008002a00034035070401485900014035003020030461156000341c0d9510b41c20018500c0b611942c103541e903030700c0c03120350544000c05612010048000003091550107141119001542402c0d01114400d0003030014510903401d40c0028400080d10b0b10f85982c1640b207030f0140200141c010851281c0a0500207142d58119105503001005040702500145c0c0404070030885291003611302c0c0042080c0108070568982041e001c6510360b1800785841c001c0c2c0681d11039030700c4815200c07140d100e030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 794699316 1250 794698066 794698109
    0x90824060f030312180a0201020601120809030a030f120e0a023003070c0e04020102190c03381006030518060c04080f07031703060d021216080d0801 65
    0x80708801140c050100e03a103898100d407180e21500c400b142c003d0060042d2a2551313410950000e24102015010b0f009008583d091400c8001d04405c40300040d50b100004200000c196101000b10036071310f902a58401c288074aa801000700440021001c5100076420622000c00c86070011602c2240310342e0465280018003458803208440070b0fa14035203410394941c002000c0c11544004801002441d1040c054060840d441d0409007074211001d03140079005134492420201419546c903e83c461090248a030401c040d5a40e81d101410359490401007207903401040b55186029241800c41030300f0203241e5101c5440e6150040301c0c00494003881c882c1c1010103450f10301181d81d48594122480458006209a0750700c1d12304200115041d40c8544500101c6100c1d01d4030720752030340c0000f01d4007205032036204601080d0090403194445481c0c10190400364014000224400180d03612540074454030045009080d03081000c2e46030226420a07544502065042010320000483d130100140f41982ca11139002c400c001b0301c140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 794700566 1250 794699316 794699329
    0x60d12030e0a05100905060901020a02070b0f040b1903050610080703020d0e0d0c0c1409061e0d0303061401030e060a150e091c020a0f02090a0b0d0602090109082406 72
    0x4005400c501800780a800c1310104c0c1c0d0090f220031800741d004c403200d94079a407140718200c0c49400c05040c01600084010301036448400000c1841078402160a41030948408540082c0d9000046401075404136880040e009505406a2035100b00e04035544940300045481c0940f00240040814042540c002554007102680d0750150000c4100d94081b5030300c6100000c0007505003a5a001c0030303594410303031420004440b41c0c60440111000300c06001110306840386401c2c808504c10f0005150700c0304400d410b00101035123a03078443c42000c500985d0f01280c064035180c5100520300c5100388181c1054245015141e01c0840000c0a54122034400c0c000580c1d0208003400c0c1c040220903400001e40c1d4400795060103021a0b000882c080e8800d056001121b41c515131010a0b40d551583c03d0008004031003248180c805440d015507030952120790392030b0101e0722a194000050381280e961034100c92140e07010401e94025680910f09801410301360380200b02d406240c0c07008030f229000c034070060b0503034851000c0060090f44884 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 794701816 1250 794700566 794700583
    0x30a020c060c0702122e09151d0a0f02120f071404050a0513021009080d090e0f0105180604021b0a021f091a070f0507030b060d12030e 59
    0x384255441414004120041a4852032040e40300382c035078000011070050049109894410381c40940c0c60000b100340402d4030410442c00400c040340d5582c0000c00007017040040d00c460100710919001411046a0070340003c2d000583d0701101856001101d190001151580c18030000d640490b044034002460300b000c2d9140c803610081280c954011128002603082ca00000580143c03011034090000741d494007a40c03030071107608984420050401000b001d01604000b89441c4542200b0700c2c00c5c048041e111210249070a482114400c00501694030420083d4110f1400c90381000c1c1868503c1103652511001440c003010884864442010480105809a071789074100c4820106003010b5480c141c028001003034a4030b628601c246c0c05a01e5240352802c080255481003140c04000c1c0d02d92804050900d4451055078400c50a00c00c4134820400003c00846d022580c54414144144000c1c07030070909500c0e00400b01c010203485180244c1911031104005240b605d480e00c01c040040c070300001c0030302c2c202c804140b500d40c95 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 794703066 1250 794701816 794701837
    0x40b0f0304050a0f0b040c090c08010b0d0b09010b040f0b090907180509100302040c0809031c110301150f020a150f0f1407020c010c0b13080c1213080309030c06030a02 73
    0x20f9502210410007071008180c1b003035014040f6201825034449802d02514003003003100700020b10220040c010000c50b00302414010310044070004010303881e82c02203495020203800c02d82052901142c00c0002c2c958841c0010f010b0400e0040080c10541901d001c180c84800c080e00650a00c0300b10b07050014414840032018004040040840d50705040061016001107480d0009a001d2424903008035a03160013422400d000c0d09105004501e0f00d101c40142c0c4116036041c1e08500b0304c90381c0f925014071411220340003070340c00380040d00980000400c01010251408031404441420364002c9950744010491208002c000d008010801103403421602c2401f0000380081c1f5041180f4074035007200404003130001d442c500e21a142903000c6502c1c202d20701c00150f50508900800806042180b000a244400d50002c48108a442a0880c600708071703102415030704200003001d06603a43c88000c6440c1d07041c22b10440a4a005140f103c000d10b142101240c0400c0d100ca42002c0058010a0004007048152610340c1c11220300703412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 794704316 1250 794703066 794703083
    0x5070c060801170a0b1b07050601170c15030a2705070f050a030807060c031d0321011d1504060902090301060506090306181f0e070902040b0f0304050a 66
    0x1124000980800020b0103050888040303501040541900044e422a0b059004501d49040365244a1281e4414128455420282d1001d200b02e41c00a0410070031580030300000040f40c015880043c1d0264504030311031107040d104000079049010048000f0045a0b00072903c01000300749000c1586828010050507080c003602d034203002c800d070004c1c070502140c084242c0b01c0c8115007131203c3d40d642040000c01c1c030b03003400064a43e000400c18500010000c1d070000d104110907080216403001150070321001000c80680308600c640000075050b0784c00c691030f2451a40b0076014468008154140740009490341024030b001500103e00c0c2021540000c2e152045580c5084001c000b8080b03680c5840c15000a5001000300c540258200718011030b95242c1482035038802c0b43c0140051403540c4e01e842c44002c501c42e90310102030140c01a1141c400840240b0003c845030141e20407000315840d036048409070b1511700164440003546105000600c003c0c50081c0032203001c0903038210501d4581e1218245241030440f8038500400f1542c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 794705566 1250 794704316 794704319
    0x10311030c090c0702010f0216061b021909061a0f0702011e110613050c01120204091409060603061012140105090606151c021602041e0f021201120305070c 68
    0x780003000411300c80e4801e80c1d800c500840460410f0369a080100c0000030440c40400741441000d11400000d00c000d0300d1119908814101500807034103440001711801c9220480d4407080c000d0214502542005000700c103250b4550025801800c0d42c1070040d034502100303e4500107004030540e0700c40c0c0c01030409003c54401041c02c10f6410032000c0c24080f5945400345840c0039090004006264041a51490a8000014020034400742c3c004452052640c2010500e4590030722010500c21214443d000159242003180003081c02c120500380d140800c0100b186109501c041c080100b901005a0000300304da00b003c100c80d90312102171601a80f80343c1d680b21541c85a40c80c181c01c201401e41c0000f907490003441c0c255002c0c000c0300b0312500348800743d02c18540c40c003111848a8422070468100f41d40189104c1d41ca0030001c0f640c50600b41d0000e82a03a204076000c18012346a0640d900c01c00505214480e1010003102085141a2425403103500b10a41440b605500d0141544002d00b4103008504407500181e016500c034101c507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 794706816 1250 794705566 794705581
    0x10302010207090b130c1e3f0c0c020a08010504110f0d020d0c0501030c090605122715070918020d02120115080703110d09021f020307060506030106050108010311030c09 74
    0x70400a030b01242141ca2801d0040c0f8158001c20388d225000100c040400c400c00c000b4020100e0b9210480406501050150542200014284202282403201e5076507080c1544480c01003050f8002c2641060903242d1520052000041802201688401c4162110750121240c1c6002031200300708040c0194218044850220070084191b0760740c02a83c01c2602d0410151b229030344200c8005465000d1800410800c01c82240e40100b003142b41680140d0071308103160200b40b500044c603203503c00c034003030b000741a80902800c0b9a021903154203664003c500f8a840b8005d180780030103016541401e0014070358495400602c011003540c80c1e07011280581014003842280d960744186492500703102d071409100056500d808901d607107220f8000d60080f020520440c5040000d0030080e14020140640102d901c840700d808601e100c1c0741501d000c0c03070a0703443d240c004d0741d158101c0d1700348101a5076004104030b100303901d460030030b00840c0e0304080300b281542c0d0044c0012819201e49030110346400441c8614030b0740800c8000c00c200c0746 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 794708066 1250 794706816 794706827
    0x30e0c031005040203010f05070503040b04210809071703040306022101030b16020102070206090f030c040c050d0b0a0501140a1b08091003060303090b0c0a17031b03010302010207090b130c 82
    0xf452003903000b0041000404811401c480042e1030400002d8000c101040104110092480d00715004551481100402103501d4012401120210021075201700070840702030021300442c00182408002c501c007a04100c1e0202c0c5c0c1742d1045020040400354040345540c038001d1491250f0340d518070040d0b0440c030607585a05054107510011107003a03242c5600a404174607800d10600955a40c154094401030410100108105143c00c0c0c1e426031a815220b6100700e81079a9582c2e004076184212039480e07441d0749408c0140144242c0300c02d10421801256425003c025030390b40050803100c604400b03500d45465a03044103044500f014050306512030b10320f000c0214824010307074000501c480c4c40100c2e001040c0082c05d8009800392081d5101c00b0780800c07031815003003180045a0000700030750501c240668490780d460f655104041981031030b400a6002000c010003c41c003440000314600c03c10b130008568259031441e0700007991801175024194483d502c61070b100b0415203c00412400207080d64405012107800c03440020710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 794709316 1250 794708066 794708071
    0x36280b0d0617030f191101050a060f0608010509070806012c0f040516080a1104081c0507120f03181505060a03030905040b0316121719030e0c031005 65
    0x21501c401480790100b030b10004103c60b8144080c414490410b88615089186010401202c00a1102114805001050030300c50984a040b40c1e13980002d031075003000c5000104008542000c0d0911401c0c0780113224a950b120102a0b000704149446440c9541388001281c8072000c1701d4450302c00c0b91100004550601240126050800043d9240c40c10380700100100300a8030810b9550031186c090a00008040520070000310354009620840480c440c5c03070250060400e540f099104002c5904810045070f4000c0d200c40b07007550305051030701e4000e0900095403107642c240842451b840007408510444c588240e07019400c00791602541360f00003450004c0740d041c5410181211005082403e10348800a01c0f0707480e1243e15541030b40e4041d5501d580581c10300301880002c1001c511025070502c00e042c944292010601d0901c0b01400d10100d03007000a01d1a440c0c0072034964590210106048004c0c41b070055060801c800944031b11403103160102c1c071624010384150820116480e12601802102c00705860030720750f600700350b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 794710566 1250 794709316 794709329
    0x304080327150a1a19170c041d060708091c11010e0d0e040519060b0c0c01020705090601080a2c0c0f030307170f36280b0d06 55
    0x14596034a461042282c41e00c00c00340e900b0413491202e0728160700306017807000c41d1010301603645990540c503503410040d0042c0c440300e640d80710741c01042885998101401860090008030f64015a400349840c4001c1e1140d00040800080043c03520014001d00c1e010001b01500f040014041f03272071020200b00040c19000b9510310b1146940c244400d64018040000b0940b400c109075580300354055541d0400c0202526020304a07004800444140383c8640c102846404000c0c5203101010f0350b24032076145000e080c6000c5400c564191b40280200b001030303403500702505034054801d20380f0802c5ca64030721000d40d000705550540551440000c0342e880c6400b0201c2d685103103a0030342c024101d40000c414a0204028491901040303034154000348442000104031403d60b04418015205440c00c1910403403090800390000d0030980501e8041c44070f582e07070501c0201940d08012103801282c0110302000030104540e500403c001d900000444a00308a040d07030040032000142130034110265582524803140c0c00900350500609 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 794711816 1250 794710566 794710603
    0x2010b1f02010b01110706030e0a080f07050601121e0609050709060807080f19020604120c03020103050906330a0b03060a08030406020c0f040608101407140304080327 73
    0x1401c0c5600172414040d5241205004101160610000707c014002400c41c40c0d1180c400e459070600012801c2c0e001d440007003200354140d43c466403242041450104184d01600c0041340b8511080c0218200c0404c03010540034104d20486402401d00d8428010601d0100c058024001c914000c00d40c035003150065400c6401481c01c5914043c6ca0310181500c8200c9000b1100080c1c7c0140c10340755000030008405032500c1d000a02c3d5600703183e690003011000060b81c7c001154a1501c03070b8003d20840d83c140c40340075001101c0c0c0008284516000d107188103400d0880c50f0102c90100f0794014011440035181521100c1c1c0380180c41d4101c01561180303404420340042c2c80191190351821000b08a4042c008140c80442e03425074000d02d0a0030040e02803000303106081c40103a420035290b540201c4c0303110080048068007000f0b4000010300005c0090094101e400c041d1102c0c0400c1240049032620400031404d0360781098228010942d25156000802e50903c03940d2000804503c102441c6110a00080384000d02211042c006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 794713066 1250 794711816 794711831
    0x20d02120d03060510020c0f0d290a020703050304110402040503010f20031b0a090918060f0203090d120204030f121d090708150307170c06040b0702090702010b1f0201 73
    0x4010000f904c640c05c03000168802d03481d14201d0700d0400c124824024014100720007140d010744440300b9451280809140c0090b280c42d8a0744900010200341d0b5001c045040e00b18200800c03607600800a1101030400740040a542c1c40403a06a40c0e117078116002010000d000700b000d1080030394508050008208601d00701000000041b181751212400c81f84500640045182c0310b10072550381c41c0c81d6070404043d000400c42200c0000c15000e045100307401e01c804400c0c00700e6a07800902d280c50300560b41900070307292907180148184a01c0c40c000045aa0a01138103040c102d414119210b030000082c0541c1d40701a250080d80002c2d2000e0280e50810344484910700d50341c40410180318011074400c081a01480c075008624100010000c51180010070b03008000d0740d48070740a040859000a2415085800007003440e0744800352003001d0203041081181d04201134034003a0a0602d003e5600405006606011b401803082c54000f404440c800c0d0300103040000c00402c404c9440790f640c0b032240c9480717005902d4000958a04000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 794714316 1250 794713066 794713069
    0x1006080705190605160b0103030c0209100b0d0f0216030f1101020301050f0d050109020406060e19050a03060b060d0203130c0e25030605060c0a060b1219020d02120d030605 75
    0x210540302d91807502c0581c0ca4980b0700100c601e5800704480c036000501d500c24507000103003400d00d564000d500907076030070000700c074240108400b2407070141280001c60a0400b04100044442e03050f02d04025900b04009402c0c0f900c6140d09011b4410f083c2c4459080298902c21400c05801c5204c1c120300301e505a0310400003502c0314040070300301c2c8020300405921041004118405140c020700d01880e44d03205800214820010380c3c0418142c458a0700180041a2021141d20340390809200020b520303a00c0b060300c403681078a00800703c2d0503503041d40005018562a40c585000d942c8410044813901064583d046689103080182d0f5010100241002c56100740c6913100014166003420340d41d03002d0064091000781031b030000213080703110130440722500c002c0c161a62400140c0707036500f00140110f010014040d211314042440e0490890b500d641c8461310609840b10200c10088000848a001340e042100d47c96540e9000c2c00050000c61001070000d5004038842560344920f0301c003050100c010302c100d40f0240030550b120300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 794715566 1250 794714316 794714329
    0xc0c08030430090b030601090915150512010506030a090b0106080103110406230a09110702120f10020711090a0b03060c0a050f0d06090c0206070206280c09081006080705 74
    0x2c00320070000b6102241400503030f01c000000c0d600308405040c03c1d50055600c0408905a81c05596000308040204504008034011000042680e102d00c0c500f40d40b07003102c400340131851450180540350081c0d030044001402240e495000c200340681212482482d503a482c44000c0a08a09000c12504042c1000d444c0b00740d801d290184000756441402c050660022100541c40705040918039540d02010440f0f0000342401640300c5d00ea1021031a441ca40d5450b4500e0041c0010480d131841e4010b100c0d480508203a4000e0004240641c40704031a03803001d6961004c604018800013507082045500c03c6031501032001003d0658800900f10100b0317002c2d81c50303641d19255a03450901902c1558400700f40104201c556110b410002004514100280055020780798444d200c00c40d4441a445000b50380000103000f2100d4040100da540001125240c0420080c041e9908103014200d481c0d0070742103901e0745002c01c5400d0050003802c000e00b40341d030100c034140c1d02c04c0801c500203054288504080ca004a13100444d590030500d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 794716816 1250 794715566 794715653
    0x30309050d0b0601080907030204062d1401110a1b180b03061501121122120609030e1906110c10050a17161d01020706030c0c080304 58
    0x721502e8540e4840d030054400440043c000b05441c003900e40003100503503132403007802d010f130070a1489a00c205d044600da10220880305031120190441d40701040007030101702840000298001e01c0c081034038000305804c6a01d48008814001c1000001918800c084c1c550005071004480e0310301a5944189841240142100c00100c0c415806410010020380c1d07081489200341c402d0003062400c0c9d01a181400004022202200e000c0500d0b540d00003408204101000740d002c0b142840c2d010b400314110b190101d044000303100101d00070629511070350172006041c01030340410f42144010309068042c8000c00002d40208001c3d0080501203101000346449956001540800d6401d020b80319050240710010103507082d401c00c5418004201c0180d090201c440e0150400c540038001111010070720740d00092002e00880111034001040d10307260034500055a1380050302804594160400140000400b07a048030201024640600710040c000b0a000030800e18415108242004100d480d0800000711b00030503071100c4d00f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 794718066 1250 794716816 794716823
    0xe0d12090b0c0a050f0d020c251406040e091c0c0b04020d17040305010b0108010e04020904020d0c081b0a05010203030f041205071a0403170105130e0c041401030309050d 74
    0x1e100008807280c40a0000304810071aa060403803e0251010109046038049500511a0394000c10181c940312400c010205040c04640d0b2088100088141c0d081c401c0305180c40b84c0e45001c07500e0f00d04c00c0003d44456085a000d0301c0e0344035070003545103840d02001c1d81d00d070140c01c40d01c0c841c8042c0b0040b40c0b010368402d00b0111034142d8043c00050031038866800b004400d0500070010f98101e01244018000c81c00310000500003036124200108180018400240c041c0d02c05901405a0854000030070006a0710240c00a50207507040300d00b02c0100e42d0508081040c501c4a0b0084a101d1041100303518080e81d810b684003040031000c4912100440d01c80004a07100d01080d20386024203884100494001109110403600030f0003289041810405103460b01d500c040300c400c28001c8049000000c1c042899400010150041c003070f550402c2080d450500031030aa40c00e002107880f041a03a81c1a00c4142e010203000c540100c8400038010700ca40000800700440e6882d080c84100c0210b801944006114240120b11600c003540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 794719316 1250 794718066 794718083
    0x20f0a0f0e06090d0b060402190809060c03011a0c120d06050301110a0219141e0118020109060507080f0403050601210c2105010e030d0f0e06150a090e0d1209 69
    0x113070f56a65404012001d800264410b4080c000501e500175420345200180c200c60b50344503254203041d13140608103000600180c1018408000511801926140b40345601501160090340c52103e00c8030a030078010a8610101e1440002903400d51402c215049041500d00840080105103141c4110308442c1c4640d4140d02c0160308107106019064940c0c40d60b50f44aa070040e002c0342c003c1700c0760205850500c820760544400c1942d450909090400b402d106041c418030920a00c150900141c1c1c0000c5d115070b88900c6030004200d800600d010421940303e00780c8503051400320115884a8503490710316110b05090041d02c0107402030942501c903544140315110030311138103c00000c00403400d215084100071503a2844c01c000700200580c04002607400d10440001203042e030040d58840074101d05400a0707031708220000c4112401d00040c40c0d2100c50109100f600f02d010820707014842031402c00072580740d0701e0320b0f40558181c616009505841c9500460001c00004080d5078401d1070030380f000c51038001c0760000e901c050011070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794720566 1250 794719316 794719339
    0x6080318041d06040b0f0a05040221100204120b060108010605031f1502011508070605041401020a020d080702010f1b03030506190609030507090519050a020f0a0f0e0609 74
    0x900d81c0c0700303219070900c0703032078095050142c11445880c100042d1000c456500009040010000060107015000411000d060005003072503000101c2144101c0942d0401c0014200c0c83c400c020010050607110b4403084009549440d40c5121804004140d030105650300643e030300000d015588591451070580300161280340c1551110500c0036481c201c0f52030b28115140e40070001041114a005100a0310105640041841c0d00c10f00207a1030a02c103203038030030b20341a13102c1c800601099400605030b609486554001208910402c00103d14227200044040e4100401007441824000040c0c01420518001e0700c8034150112525421180590942c00407000c0107140c50200380001d1003500860781264000f4040301c104116100c941101705940e80c80200406d07024030081042110a01281e4028034005078100001d240284e42e010060075083c002d012600da4900004054413035650507101c413030200540441d1203a0826102420240c003541e0014040783ca240005201880c2220440b496000301034440750300346 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794721816 1250 794720566 794720569
    0x1407060906030f0b041e1a01020a0b061804030906090608060a0303050c161e0512030307081905070906110c220617060612071d070c0507060e0406080318 67
    0xa050003c1200030301c0341c0b50f02041a150b62035004045001c880b41104440740b1051341820380441e1a00c01860789807000000c0303440b0b200e80c4c0204850325805c0e000310112100b03658100018807200780d55942405c41031401070501c8181544035410400341c4d403080e00c07004043d58681c1c500742c650002c100c50680d40a540100300b400040d10030400340070503451380740031502e120a407480c4904a0060580113450008050658148202507a80c80e200c003c10040d07a200310f841200014a030303280e00c0014400c6051210110200d801080c03c40c44c507031195a4881f038208041d0800c0c10307000b0810b01280c07207094001134606004602424011403011242c0743c0c0108000000c2401d0140d100001c465541c50b1480c4980e100303000908503403040c40c00c0c28044500310141c0114908071041182d01c0c41084e144842c00d9100304400e02c18003d00c0c1c4641c0302c0e10b141d4072010640c80d685101d03080b9255030102000078205d00a034600020056080452140000000c94060000b191107100d0280d59000e0b21186807078019003c018903250b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794723066 1250 794721816 794721821
    0x50702190e07050a11070602010f230a020f120a0501093e0d110a17040b0f06040902120729190e0d11190b0d0b0a050d0807140706090603 60
    0x2181348600b411701a0300e08101e82203040c0305a960103100940d460f201e0f030141500e0741f882182a400034440d80750943c8090240508420b000c02440611a10760006a02002c0d01500c1c1c103845103000601c4401100340b8200540c1c101905082c42342906040c1000c0c0308500009141d28072022803071206648105803038003807812155443c6002c144903000801005004200301850150352148415020314a503030304c1c81c000c0c000f88003401904101401c00b20344014000014800c1c005e980d00310380501079148142c3c032004000380081c030740040025801200c3c202c5821850300041010021604840c0c1003d01402c07d440060101aa031015000c284010411040031283c40e19000301040e41e100b4501001403e13090004284880120343e002d6842c015070b044822580e103040103d1410421400ea06520703d203140c40318404031406000c030b1402c0d43c0c0781c880450310450340b100c036010340060000500c00c0c0b100c01c0b442e08090895a0141009892401d110026062071440008103142103850640d20340c8441e40c9090b030304800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794724316 1250 794723066 794723077
    0x4030c0b0a0b0319050c030607050a120f051504110a020c09041502120f01050d0c0303051b071203020f0307020d020d03111006050f030f07050d0501090203030406050702190e0705 78
    0x900c1d59442d8000050f10200400c0d80e0700b801d00f030b01200d03128485040c20303464000c03214481032282e4480c3e800c01050a9102080e01e09a0310642070117111300014041a001800c482d08171a40198942404c01680001c04929190080000e8404101c0b404105030b80905a11800a107000540d000c50214052800c02c0d81001c2c1d07215000d10181c0000c082c52000b040c2c1070f6071100101d100490201c0f400e019031540b00301e83d040d0050500b11050301c81501c40e0754800d64942c206200c00360a000003c40c034000c5001000d6080041d19980d6030654140f41c0e1902c0200d0761790302e030048090300107102d000c0400f0640840041210413945c1c000341251410b159590810800401100e0124100081440c2c205a101c600704110350003003550b003801003100c60508050001621064106901c6a40705440e4120341c45000315a01c2c054030b030142c0d0301c10308500082c10554058000160020341620000400090480d4000e000d00101403007200c5500c4078800314035025001401501600c50f80d41c180700c01080c4164000c400909 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794725566 1250 794724316 794724331
    0xc0309031e050913060e0c04080a08161208071805091503120c1b03150a0b06160b060f09010e0c070f0605040302070f090e070b0a020705030304061101110304030c0b 72
    0x2482c040010f4041880c0b00c0d600031600040c507890b03010602c14031042c08503181d4040300c035003861818a4a401070056542600b114054004500000c1100c031000303043d02500a40e03500b20880d040d00400c0020014040401100c03030400141d110383c007901106001c840c14000f1035000611841441d1583d00416000b021003002e660340c136120340c540c0700c01141c1e000c101410080c0d01e203d004d004400c0001c007080d0324076486200340318800e40040089011000b01070480e1600807002c2d0400003841c0400102190140c424040d01d481d2040c05010040200f001030080c2c54071410054902000540b112403e200c81510203002e11000c0b040060009151103c4440291490501500b2603580c11420742d15040112801aa42174006030082c076410b01050f480920108000c11003003100b001054240f404403900d90446000c1c00465000015003598920310030441800685402400c3e40d680e55500c1c1006000b14491950580c2c1550030900c0741c40c000102c507000d40784129015122800d8140c420750f034060800344020b2654 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794726816 1250 794725566 794725577
    0x4050f1801150f05090303030a11210603011b0c08070f06020301032105040503150603150f1605040609030204050a0e1b0f090709170106150504090c0309031e 69
    0x144a4810554190081640314400c40030a05807180080004440b40d2090f400c3c441e0810410032107840000441e9840000e070700340043c041e655141030509521520703441c42c100c021408500760110003402d5150f070244904030020080d00d00c0030315000040700a11542140070502e8409420302150105000307000d40c3c0d2180424040d40081359030f900d0101d80003078005444020456013010b01c41c43c1000825590b6a10700d00706982854038140c0004d40e5900719402400104d04280046145601c00300000302d032445149841011526080e0b08021a07101e048503080703e0003014080400e00a1701550072a41681c0e910f0381d4200b40c4904640900019200103821050610390f00d41600d0403086060041102c0c0c181d40d03680c02203014502404020460071220f43c518420302c4200248050903402c54000c9085800600e05883e441034038403040740c0100103070b030300008025600c41400a0055404401001030301c8d9550340420011000c80d000320704507801c2402c000c02140d10794440c034541425450707004800f1825468013 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794728066 1250 794726816 794726839
    0x120603060603060c02150f0109020d0f0c022d03040b0705031207050a182102060c24070206060904110a03230606090c12041713091a0604050f 62
    0x8003011038030594820b0340c01c03541e00c540c01c1220035414000c58448090300f805403c0c8500b444001c00342411070604c02d40c84460750000b840b0030308c00708540084c4109915080100b01000c041c070750180d10340140035021070307444900003640c140082c6203c090400d00401c2e040210b06090400a6240f0701d680301c00d505440512003030244c122900c0004000c28440d208550740c16440e8002041d01610040c0d850100950180010f00d041c085000645010704050300032020ba481003500c28008038405200e8510400b01b58010040c9044c000112007008502910b1006c044224966490074126120403007980c4440d480500d020124020954403800c40b602214002d00314403a0941c5c955480c1243c018080012443d1506c441e40c6403400103050210340d50094044c0d8001460b450941e03141c60b41480b8614101c20007030210404a810b0001c16621841c800000c114081c0d907800711640b01001d80001c07846280342c01d80c2019045003448480101e003040405020f4001ca007010b00b003800304107004440c198440d4000400408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794729316 1250 794728066 794728073
    0x20418080c070602070b0c0a1b150504050913020d0b0402150c070302120d050301031401020d1112090c03030a1412041401180c090f0e0619060f0f06120603 68
    0x404a007004000100074080c5040b002070f041c00f500e5800082070001c14081c4494030346020480883c225400381102010340f4003407942c14018069604078850070100694103e25060704800140b0503100704440e0500c0c10350f90250100441c1210b90002500007125102d4840000c400401c00c0f13812510081c00400050101429011150068410325101341c0c4640410400e60500c0610b090b0010542d170050300e024911500058503078441031000410307142080e03802940881080d07040e201021078402060003581d103416241c030015007105d01d107502c0d8500b01e0f01c0412035124000885032102c01c030250145007050750182080d2811808101824a003100402500c0d112002d400e404510a034854140d5000003e02070b0401802c50b4500d080890303039115840c1090340480c80328103b110407102c14103004180320710702c20f40d114040c185915981d52503100703007810721086480082c0e2441141184400170410305681307448171174080c4c00d41e01c24125a902a08410b0104900c1401c42d01185105840041400c2d95641d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794730566 1250 794729316 794729333
    0xf0d150b13090311120906030703090b010f0915081902010507020901081606140301090b030c0315090d0c150b0a0b041203111b01030f0f090c14030613020418 69
    0x1500c0060359a0b69a9070080640080301e82c0d07440d019820061194420400064241d8480c0443c028810034020000810880c440d07080841e0099112403c0032407541e645c003040041145a010327140e242c1e8103000d07003030100e000d005003440120f41114008007401400c0685401c03a10301e200c0b50076810028104042005601d4692800e4000d00507000201840781c1001070310301c0e00b440d4980142c81048006104500002e0810003501e0544584801c00143c11005d8130000786002030000d0f00c2901070250080344100d420203a800c07903200b841d821081e1118800b007070004503401d002000004090b0300d4000e2000014400503804442c0042010344554201b0703881e40d203501c0d00c41d0020307801006140c00020884081603403200e007907802c20b09020000c244040d140300d07403510080c0c0703000c640a04050b0b0b03605a0600310403894101888280044a040007802c1703a6007410010300e5140d00034040941c0300c2001c141424100091018401e0341d03050540803040440d6800c001c060114401d421215424046110011030701d0503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794731816 1250 794730566 794730589
    0xc02100306030209090708061014191d060f040b0306040816020a03120f0e100c05070542030c0702060706110702090906090a110a0915030c050f0d150b 66
    0x3c03001440a503140584861500348014002746920340500010031034506610804180c1c0b01d42118240900c90042008800b90026580700803142c41c02102e90f80b418404695001c3c5c0114410b4410000e04c00c803580902080e26603031440150554010740009002c81e8000c0054007a10480404501580b0056000105000d425410a0301d2894000c0019160380380c20036008451400d42e403c0c0855005030643c0011440e080c41e5084005110754840c0303500400c481032281c0d8025010003070104c64105100a02c41440701001500c081400d00a0401c3c0d4090003000d056119030041940c8880c4d18642e0b4820404044e90000c0c002203811403018440c0d0703000100c9078052846400202130740682c640c031660041215040000e071070300e042c43d00090306020343c845010404031215604040710b180d000461502003504045990b101368821441c00c0b14054040d01000c1020782101d015644484800791920204400106c1002c4c0840d4080003e0040360001244158440704513403080c000000c91031100c3c404142030305481d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794733066 1250 794731816 794731831
    0x120e0304082404110f04060302100e1306150c0503040807030b090114040302280807060608120a05070b06031501092c0304062003070c050f0f010c02100306030209 71
    0x3030b460005000181422650301040190160306050540702e40464410340405140541a01e440380310440c0c07180d410400c01158007504c4a80b8484040f01c0080044d01e008200900caa040c100c24580103010a003d0101038655500220400400c481026107103005100821a080e0000340f01c0062080d01c24071a0070700440c000d074814100b900c0c203d040c0608585c03600341c000710040e42c00000c0c0b0002c80e90018201074101000411032084205101005506062540d0001c110b4807000600364200079164000908480c0200c00701d41511002060842140c010b21400300b0008400b401103c1c042500d0f00c1b910303a081803000e0280c0c0c0840c10212840200313440c0980009140b20f03141d003502602c0341903607026402002c3c07030303406d010306007005929195450b4400e130322500080081e12548500ca5155010200301c0c3c010b25070049035591001d600d04612038040c903209180c41144c00101e00b80550034a41440d4158980507907a114000d41954200840c0c944404212030030103507200c0d4003200503140e0705030041c0100c2c01c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794734316 1250 794733066 794733073
    0x141306090614030307030e1509091602010513120c03030608030309010e0f010c2304170706020d0804030507060c03020f0d0b090c04030c17031c0e060603071401120e030408 75
    0x18202c0740580501c54440355806503000700007000110341e0112229060041c00ca41d69100102615841c0c4910b000d010099540000104103200d40300403212810301c810704003600280302e03940d540780c4002e8282c0300605000c0c2031028038040d02c805044c4128102080c0610034280010116141c900b41451a0803c651580044e0340d103c4502c0d044c180c0c00c200b0003034140d820030001d00c00e18007070050040000080e002c020420039284181310710100c0c4030409071006010746204660108078151055070740c80b01a03101c0e0030f0141c00755014240c41c0a01c2035034428802c54164540d00d03e407139055a16200241051002c0a0404d036007032042005103032800e401408040c2d0b28000100e0b80300550420858480c0d80503014a4040300f04000420004d9070710742040d0216030710002c03604009042c400841e4154402c802600d40041c44c01c1d502c07042c40d0078160340500850f0000700c0442d0810781d40c0d001807581c0d8046500a06441141d05d40641c00d01e98820360142c514a2100d02c070100d041e20311804000c4c5103030059080f0005540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794735566 1250 794734316 794734319
    0x50c030405061f14133908060d0609050d03090507080604020a0e0c09040f0f0b18060d11030f0706020d03090b0c0703030902130b0114131413060906 65
    0xa010003110f038000c82604044034500c6034540d050022a4100d200c0d444455070203501c1e12280e640c404034921a40d800300001440144842e481c80c2290b441550701403180c126042c2d420b0052102c400310010074545250311015055141c681c200041e81075810000c40b04180c81d50030007800517409010342d503000f20290300c001c1002c0308249080f03420181260885020b50340000c0030007001d40d030b801e00c000f012500880d00700c00054450b00300001e12441031081050308541400d0510490903000da010700070314031003c14100020130268003080702c21603c040001c1e000c00103a001240300351a01c450810200b62050014000542d60b10000c82c3c100802d9411002a54000d070104000d41ca0701886402c18114071460104a0800503955003074555a0180032640110404030f8400c04040c06503100f800081c0d0014140001c4280040310000500704034605180025100382004240340c07941d8041d20180820300c02130b050410b0819074034902081d6031441183e440308a62080324000c2e41c541c89040f024002c0341034040b030407a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794736816 1250 794735566 794735573
    0xe10020309100c0f3504080c070b0409060902071703090c0301090b0103050f0f030a0e27070f090b1602040b0d0302060405160605090108100b0f03010513060602100b010210050c0304 79
    0x200300b02c0864107072a0108013079030948080d0450f40201d002903205d405500343c1ca403801e2440e410b008444000754a0312540306c3c0401c042c2c0b01c00000c1d20481d0030b5508207002c3c00340c440040c0e00c264040c0f40070042030040c04010020741001c800c800b4582c0200c041d03033107450080810340044d0950781100b00c107685402d403003001401808001e0101c21803031500c020042c1511101c40c10748035528030440c401c0704100001003800100e1aa01c60381e04100704809201e4008240d03603171061100910310705580310b0002c10300e443c101c0302d01e81c4e02a28008084a062803c1075080052050740c0303011341640c0141c2240d0096440d1078210413584c4298007100710314003da00419040c501482c006150100c0203043e080c0d052100e070020040c60394408104c0315009402c1c0b03006206a240c0c641c080d050036495400804c42108045041005011000007450490b60b0888810000c0911310700c21400700c5015014000c01030b0001c103a40c032042c0040741c00c02c2c0f2807003a06204442c0080d030b404041d50200c5106841206030006c0000c284400d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794738066 1250 794736816 794736827
    0x20c121207030903200c101d030d0215091216120503060d020409020f03070b09090c040645031218060c02040204030606091d010e10020309100c0f 64
    0x79909040400164400c0e49000c0d002900301ca2146180301c245081c06400d00c941409140030b8000c000e41100203501ca04e0307901038100082240400f01041d0300c440d1031030342c6250000c0d1406601c0803540141c000c2211046c480c411001c0010901d0102d80304801d50803038104600c0c0c00909495002d400303140c04910682ca00b00c0c22981e9000001340800a0500c2800704990314a228400076560442c1c0c00035420617103201044011540c515529418000c0c614002a4030740d1001c0205441102101d00032425038034050030880c580907030b009000c00540003132605600f611400380d0042c0b607154064900218681c48a0b242c204407030a0130100d145190840300c08008100306d14180c104409000d080841104040032203103018141288904810010071580007819502c41340c0c1142c0c0655005070003801540e1701e81c2c240002401c040c40300c9440d000060050f0014461040c41030500c100c0008003e0030503d14403501040c0650809402098180694640384001294600c01d002c14100c076511018007414441001a10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794739316 1250 794738066 794738071
    0x1090819031b171e0105090901240f0506040305060411060403060218040f020c060c0a180305060601080609190911031506040e030a14030403030216050a0c06030c1d0103020c1212 78
    0x1350b4031078000044041290408100c1c192a07080c3c69015855507407454881c094504ea000c3c05d10f95940f24000d07c01c40705040c560305801e4410540415000c140d0314810b0114922a5110142264001c2804134000644ca03000f010510a40117009030b0403da240e40300c020880e808054000c5486501403801a81800c02c2c1c043d900d043c0714a204114100071185d4801034646500078950407149600085120203035000b4201a060084032407445a1095100d1402c50769600d0207580003030110b240076000850500d080078215110780c14101c0e43c1180483c0c1110258090400c160003140e28030060b070309003120f580342040f80c041c00b45400c00941140341410014001114521010032843e500200140c2408070340000301d4107080749a0034505640c0395504e040c00c40003406050001c982441c0040341100074041c0c00183c489056014035103010700740e5070302d0314164111852805524086618004800d00001101052040200041c1000b510781400c0d0f800090600e01410a407040c14000424180c2c03003103e03a80a01d90307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794740566 1250 794739316 794739331
    0x507050106090e0a1218120b0610020d0f260a0b031c08040f080c07150206130b190c0201270c0b0310030c031103060901090819031b17 59
    0x480ca0502642c3d81c2c40d900c0480018083e4500510703540e141134401c16803601d072250525614003c140c0c88004009030341c0c40d2a5016580340c2c0f9018041030a41c03804911a049074443d5030010300a4915550059454510301d5a2220a00400512010b00c811200c1d0300381c011003004100b07516051804090704001c83e41340000082c0640d104020304071110300080e44903182c61005040050159031a440c000a4901003c04000d0213100040b8804000c4080050400c0a60701e4a2540350b40c0e10401144c2260b884500b02c0d40b00a080084014003004110000103507500140c40c000346652042c000d8903000195220b0f4418200181e54900c11040030240550006803607030308400184a0314191034480303041001d02c0b4020860480000008105542008007142000303503440005070000507560b003800c05282100c111614080d00901002442c1290181710b02400036500401d41d505243e120701c140c201c1c0c88855008401410f9503008035138103031195102d0400070b410b0943d070742c46071001351010302c059212405004107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794741816 1250 794740566 794740571
    0x9040f17040503061e0a021c020f0a09140604030201140c0f0706090b1801181502060411060310060509060c01050903280203030a2d06090612050307020628050705010609 74
    0x1041c0e11120a10381c0c006c95010380160720381d155442041c0c0712003804d940c003003d19031001809005444024003e0500c084040c0c40340180d03640da80510210000d0303016041c661000c2d003000107000540c0140c04458800750001d001600301255a0704a44c0380c1226819480364a52202c5800c000d007070380c400c0c85000a80300d08100d040c10005a05001e10120006510850500c044d03c1e12a200600c00e41910100074440d4803401c030480050560b02944844080e58191581005c0050507049414200e04590041d070f860103041160b03600c2c01d102140c0c5a048960307240e40c0b0100410280846120902a15010304102405156070380610412a800c080c1030a064040403110042503500c82030f0044281c81d4441010003000c41c3c400310340407030b19040e080c103a507900c20200c00b8588290041c94681e4070100541e94040001c00c15252104001707016841d0542d001002a8400c010313081c0141000e00c064601c0709018040f41901b25041b601107010503070b040c03611400254000c6410014000240a080300401e00500c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794743066 1250 794741816 794741851
    0x70c21020f0607200105120c030609060d030c200301020403141005061e04090c150f02010e0d050c010b060708070618021309150609020a11011a09040f1704050306 71
    0x100a03001c85107400c15013207280c8611144103e6401101141c6c2807110010450b0058a41611000c646800c10b941031402240b01400158a508203102c01d0090b841d0142c442c0b0581100d0f61313540c000002c446e6100c0707012541010515900d03549090002d48050351044920005480021048619082901e000d05a25605007801d101e034a44401c01107007400d28031014682d1a10000360007180203440c00307400090488103c0c041c0010314103180d0100c801d509840c0e0740d41110184509404909941c1d5403602c1d07180035088070560350f42103402400100700b907500b04000421078018520002e8910b4004030000c3d00c080303000040300e204005840c40b500e03026007032203a604c1c0c4600302e483d000705010003070140344811240d5581d017131030040c0b00080d0050707801c64004d0001400021340354001403010790040c0d1030b804007140030320b10607141d1041c06008403c0085140f900400d443c17100d10301081482c4101400036141c001d054941c11021890410690803070382c0c0750030452550740f40f9140525103004c000804040d64030900840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794744316 1250 794743066 794743073
    0xe0402090a060c050a020d03171b04060f090801050a05061807020c0915101220220308070b100501020f100b03160801230702070b070c21020f0607 64
    0x110741558600d19012040c00210302e0081c2c9402d01c040341c040d5011810f41080820554803610100e407120040d0540707080c5403240031440ba0010141c1170710101c5904284010f0001034810062120741141900d0042d01e5140c0c0e406074242100c80a64090b03c11070744070300401505060001c0965955206028a0119031a08100003511408a0b90846100744c2141c070129561007400c5c40110915203008242140c0100310036005461905403010b4100c001d8200a81c81d1070b032419059410380800180702c00e0300c0c0b82201e40181e0800f8601041111138000c282940080b020882c0722029010103403040d014181c803030a288201d440d000d05a540454110342c40010040e560010114030340410159500303003c514403185100180c105558019060a81d000c601c1000601c0b01054009544c0201040c502c000c0351581300c8500454840c088a000c00540d101c000d0412a4041d00c00040892501400c2c0411001d521450720441942c3c4c103050340000400041c40c02400e5150608290451207011a07241f880c0c030689a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794745566 1250 794744316 794744329
    0xd0503093715021506060304032d0905040647030a0e0106081c02030418020d060918140a061104090b011b1202070305030c0106060e040209 61
    0x403203a010714401c03100c11558600d0010007561a400030107044032404114512001d5488041c07007890401d606000d65010b20500102d0001c41213000c414400f83c0aa50380302c14031100b40c0c0040d204071f04000306800700c0d00d25280c0f5041180450b04040412030310032071007024014020210741e00000c4c0300e285891410002c2040394044000300b90803061500001d03803250240b81590760608000307032050450340b42c10442c20413002402075125000708102000389880a0204030300701e0b0341c28018080c00342e20080d02408908102030301c0b8004494a031044a140070b0b240c05902c3c3c0002d03442529807003d25008900b190082110340100e50203444040010441c0c81000251130005072804800504482c46001c0c4106402074140414034546802044c2403104010b19050b15980e036006219055030f141c03400608038143e611034a10301000080c1144402241c86c460380301c1c109080c0c001d1031104250b05c904900000080d60a0010b400e2008001d400004c08924288015121060040c4428801e0348104900409560b468 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794746816 1250 794745566 794745577
    0x609010b0d09020f190905180304051c17070b1b0a03020a05250c1202030d030209010309021f11240615030c070c090e0c1507020a0f140d0503 62
    0x14407000c500e00e50180042407060700300000890b0480d00505070030004001044201c01142c8002e0300400c5150b07076100255922030f04c4101d642416400410042055240c0a0f406081d0003407019038401b02d484550340c81210301480303841001c0092001103003203070a01241c01440e03a4010300004407215108400c801903507451054050043c10701d0b5010505480345442602a83c92208051032243d0444e2805210101e075641025011164a0b0034803034040741c6501d00840c5d40d042141e002c2c00904111141d840141e0113034109050840c1010b135a00413040140e03858a01c10030410380868030603151100d025100400c401c90034006036446502c0702051110406c0a81c50301d0415081405d168044c07900d40c0030002c0d1032207088050041c00e041c40801800b03807609050b001400d000380710710300051010b551114010295445c1c040c0c2852035030020b030700c104102d08144040300368444e00e03400c0b841e10b40101076000460590f520340100b038008124100c02d000c0ca5407000340d126000241181e210240740708580d940c070703a240701c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794748066 1250 794746816 794746837
    0x3030601170702070f08010b03010e0f0a0f1406040b0a06060f05040b0c010608030c0c01020601060e0d062d0b09090a0c0605090402090607110f0a0f030605042d0b0609010b 75
    0x640300000c40c1640b003408030030301405c8080c2e9901c00d144c2d624030200d8042c107480703191036109500e0700602070207540303002a805880028550240c40800e2042e2141949007981c04030688a8509035510706090500c2440014400d0344105007001d41c0c0e0600907800c0d000c1307814607040700050103d12220990002d0b004415541169155400c0b51ba803000303511a181e01600c01548810703c10b00c000b0a51540702030b0082803600990701d00382c2c00c68800c0d80c0d88640403103211514007034a541141c04d4040120200304607070850107000b585001020b0740d4003411014255817410410a80d80059940d08442c010707850802d1101f42c00c0080311008000c841c004e5160400c6510a500c1030724280100050003114548580d0161440c40c1002010349490350824240504102e10803504240300e0070860300c080d9120724084d6442000c0e14460440c041c411400c6a56500c010000600b0076115284c80d01600030440c0608101c10003800342020120b40c66901302d203007103000400c002c0c00042c4500d40803401070205e400d0810603100354611 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794749316 1250 794748066 794748107
    0x1a031906020d1506050a0f030519180203250f051c0c0b1c050f010f0b0a05040527090a0201020c210a0309180b030307020f060d02160b0903030601 64
    0x107950414500408101403244240214840d00040c245c2e00040a40181030140d00e07040b6121301c41c2c0c07108400f151011114445464062001c16500d204150f00002018552815115076000180c000a1503c0f408401d00302084184a00340184400201001d100a0a00c5103007049010f0900c40014008030301c1242b002281d0300d56544603028442c03030084060050a0580c042c9550705809841030a40420106503840b0980c184000f050003188042c02d00c034100c51002484501c0c16040041e0309034039a014070b0029041100900001ca01c45c2e43e920215561089260103048502c0e42d65080710869034030042c003960079500420b400340090317600840c14292100701200c2c140100c100c0d0383c2d502c03668007414100c1c1100a00c1740d411380908050b000716415058400c00204003000c00fa036543d51030140d6010700340300c58140d00280080700040c20007503002008000014403aa00301613010490700100d801c2003000174840c400141e00002071000c0c80038500d8000d0b804d580610f203907141010003e00a0704041040c0741c290704 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794750566 1250 794749316 794749327
    0x14041e0306050c0a030c0e030a02060309010b1201020c0f0d1e170405060609011a0d0b010905120a020901050d050a030e0418060b13050f070c051c031a03190602 70
    0x18492415240519884101041182000c40107101d1a402130919000802d18200340303d810b080c0184c04c1c01100c80002002081030800650a200041d0170140007040030750340354a008502c566826180e055112990f4000681f514661800c003454900340841c14400703901304400e04035100d5444246a09298000d110f1500496046502200c526068a00c1110740844100c20f001c1005400701b03040b40912412507420090b642c0b50441001c481903499191135a07a8810403191a2600076074200d2004884141018510303181d551000c10042d11350100d800c0c0c030700c1d0807100c0341c041113292000e203182c0500f0307040e10080044801c6940c1c1d00e070f549601100c081c0038031640e0f4440c40c40310340d41c80c2c20250700280894000100d000c280e00d00600a07103008204140309070241c204540b042c80c801e01c41d141c4102c01340005c802c5240c503183d4042e038440c2030468050f2000d016135400ca000102114a0100142c816541c0001d1101821010389a8880b0501c07015842600039510703400e59010480c541074229500510010f036580c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794751816 1250 794750566 794750609
    0x201f060e0a02180d03030f050604050622090f0b01030c1e031b030c0b0406080903070f030f05040e070e0108060117013005030304050f07030b010b0c1f0204090c1404 72
    0x58a050f0441c5a00130b204042a4040503456003051940c00f40b02e200c00e00180c0c80300c01c200310960790100c40541d0407208540414542d201c03c1e082c0610100003080b00041c5a04454a491842c911580c50035116850524010030411140d100c50400400d283c0c00303600310241c0038040601c0e41c51114800904902c40303480c110050010f504dd0040c0045500048000c0b10a580e02c00c10607030b0390058400d820224034842e000076001c0070080216010340e40d00404002184065590035601c11109661801c200300f4140008910020403840c040e00540b45030300d50040c2d01108000040908600a020b113040102d188161055651a0001241903410070007107448640207a06640310882d114190016404034034000d540244900440110b000314001d40603103100b6841141042d070345c0d0480d480f00804043c0d10100400c054240c80e0041d050a50100e0142c0d220403084602240083c40b2a40c0e8039182d80750f000030704001c40c0c0d1070b0307108110f041207003400c1008005072500303171514560003140710310081245202d4014121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794753066 1250 794751816 794751847
    0x9041406010e013c08010b0f0a18090f1707140f070b0a1b0c08011d0307170c0114071b08031501090e01292701201f060e0a02 55
    0x11913008940740710616944031a840d0181900c3e400c964090b002c2c9503400130381801e10090740703016615900908090410170882e584001c0c044501c0660700d000c0910780305000109004004204888062400c680b594000d041015840c5118508015a40d0244801a18140c4007281c803d0445014400054486955210540300100141c40c42040c2007031900440080181f04031202060f55101c0008000000210070244041c8a40c0107001e181c42d030080c800303e0001511010322200c4c2044400300c5c1403c1c200001c900c030782911101e803440400b4498200030000031642c001e0418100f04801e00700040b81306642d403107410443c0310260105540c820380030441ca2280c4d00501c0040c005002255940c51b6960303554200580381d811901e4030701c00e030000b1001d100e5107034008042a10000c00c800382c0502039407641140840b00c045000000d0038103000b00401444008202a0500498021030a01420700c1c902c229140c40001401e00c80d640c90035515141c0f00340510b0344090b1909034401d0707840c10016a10312000150310701 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794754316 1250 794753066 794753159
    0x1606080a0917210a09031e090f030f06050708070509120309190602240109021605030f040501110a0c050d170d06051008010302100315030209041406010e01 68
    0x4a94100082480701e04100303074401c0120b483c012181008a40341c0645410680791003140260000d240d01440c86e06001c0e050607841282032940c01d001104a64404075220800840e07441640c0041e0980c40001c140310250084035804071081c034190407540340014001c1c0c9207000350715004d4050214403030344522a0740c1c20821030700d48500007082d05105494510040601200070301803c0d00602035013000038041c081039004500002c04001800b641a800d00d15020002e400c0615181c20580da4000f9260100d10284000d0181040010001daa5141044005410041c13000070b10340e41d550158142e8008103114a8031401942c2040314441c0c10070440782064100700d002151416203e060004800100103044c1d44200c044540a172070030369070000d901d14103440d07800c000d110281d04071100b2000d00c0c4145211b0307888905086100d0640102c250b85940210b400702c00c040303c0c04c40c0e614000c0b112000c0d428400f000103600402d04200140c45541c188001c140300074111001995030380382081d50200d0001c50403501035a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794755566 1250 794754316 794754353
    0x1090501080a0b180c030709060813080f07060f063305090303280f050309100507020a0501060312170408070215040504090308010302010f2a14060f091606080a09 71
    0x11301c0c5043c2200f40482c2540144c03a0440440d03c0b1540000d002409124207512406403060b640b8612a21500c612440b0f51140d042c1c0c02110078100440b000140c210321524490800d00d080016889050640703648808665990038003207881e200703110503d60412000041090340352031506980362445140480d180d401802070186289503400b101240f451891000c07144600103a540d45001c89020500c1600c0c1071005689060040c1c200d252440aa0103440d00000e07005006441150b0005000e03468403801c540185d04110b4000c490703a103940c0c04c0198000101d86d03410b28603018888480c2002d5032128141c0c0300e40c180081c002c1c1140920485c1c80b061100955004082c06081481403849038039000f030203000d090201300c3c0400c00c1000a110460310802c2c06c4003181c020310030780c1044424a510300607400c010548013251200005655400745107401c3c0280c80c00b0705d800030300403100b50404a8005003014210f845c41901a61000802c120301c1d948120325a4110802d0b6000085d122100c3c14100c00f400080c000b0103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794756816 1250 794755566 794755609
    0x3031204080a0306230d052406030f031c150b04150f080601090b13030816140d0806060711060c0c120d05030c210a06060e01090501080a0b 61
    0x4010311034403400404280700e540d07800b0841540c94041c0017100f480c5e40000d031152600f40d40f64100c0c050800400c80b805040c043c00c11500c80896000c06c0d40c0c95030081c29100c031600e00e0f0322001e0201d107040070482d110708a40040095420082c0111868404405d141440b800c02902d5000320008501d083c9036150190001c21800c0d69200d4aa03441140e814a00a00c460001098800c040301850f10840d0b605028600503500d06c0442d929061291030303540c003c100c03d100079a80d003607400000101202d0007002034041000804a800050b420480c0b5074280340080b00100ba00030201004a10b0362000c1d0b610390103042200d003513858280a0801030b01000f140c1140a07001200000d140c0107440b00007550808500d011540c0c0d00842455220aa444d240441045c401158043c00803501044115000e40303024000009503924000e5094142204140141d500c01a8940d8034002030200c10390010750b690a040c400e0a140c440349141400007800c0c0340c0f00404890729580e9854840c000e07541e4080005040403c100c004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794758066 1250 794756816 794756821
    0x91c0f11100c0e040902100c030e06040609080d020115050603040503071212111602090408071205030a0f0e0c060d060b07230f151513050f0105120c040b030312 70
    0xa004003145a440b8000c039840098000b210714103030203045026079010345403907455000b00b1030590304440000740c03c0382402402201c0c0d1055407681d402900c0141942c1e0b85a105d0f19161002480c00c00603416106000c59060202c01d920160403000c1060440b0001d81d40c1550700c0d5102d090107802c60180450003496042c109441307001e40759003e44200104207299030204414501d00f8062480340c80b90185804000030000d888201528000d500590b11a004000143c946030459580f50528440c209904002c12404018043c0078990b503c5003012045034080100721064000c0c0380c040e55a5081070056226420005410380320302c0a9030442001060780c10342700b90b20f070310403842c04503000c54a0008860b10290403480d024003411700050700e1305002d507040d409400511201d044c030b00c0c1c02c440010007040c4030224905511a083e250030326448101d520001d4002003270b003002500419410010380c030644c4101c1d0100080b0041c68004140480410130888000450303420b80000709055025451000c1c8d440c44c0d21408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794759316 1250 794758066 794758093
    0x2210c10050a11070510050c0f0d0501030501050f0603062e06030218040b01050a05210f0f06120d081f0b0c0609031c0203060102010e01051806091c0f11 67
    0x46540a02e19001050001c0b120711100802c250080040107443c2e41d0001540000250303041d40880d421030313460034aa902c0d10f032144401000030b0788840c034805d5100b40d540004009100081c882c85410200000c0c198045062100020307541c0d01001d032034594080000e80c0d080d21560900c052940b54100c60001c4007440c40d90341c000240003900102c807444400c24903c1c510f440245024822003200080507140c1c141840805d1200b291182c2002c0132034008404050041e6000300010f2403032904c51b90800e91100c0302c600e05034640c5103619602900103805113044201c2d425200c94081940c0300036462502e41803040b5905c1c0c4c84d12038090030f13a46410505040b5075034808650a08107400070030807009954205d524544403024095500c0c070401030055405140d960800002c202c20360011030700301c0b50510020404560800c5d03002c0c00c40c0c400343c92404680219034085003101e0b00c10b0140c1544005054040c12a514008264603410b860040040c410060042c003040c12035801007601d440300002070030032500c2c213a11451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794760566 1250 794759316 794759321
    0x80612011505150301150809010e060103062901090b0c0106030611030405071706010504110d060906080705091b0a0c050f03030406050a09050d0e0a0b0c1005010602030a02210c10 78
    0x4290090303d0319414881401105000c40341200c2d9050015210403240e5141154011400381101d141552160708040102804002003070181d8090340723000076003804080084c21001560928810811900f40b518242ca030f800040c080202c808003c1003a40e11b6958400303041c010030386a080204518a031040e1840c440300c2d10700c09180700c0d9105500f21000f258503070441214800e0000c1004140e90302040052041c0c0c00d0680141010404130b066840c1410456070f02e0340c0690321150419440d01d6554502044900d030b08202510003800d0556107401d09003882c0034200d503017480704100034648085c00140c4600e810720800c039a80c00c503a085401d4400320001040001e0300d035030043d0382c2510081d0070701c804103040d8031042c4110030b102a030040040160f0420058241d50035040c5060f00d40d030046441300300145142040006000c1c4482020140c4080c098000c0b41c071080b201c042e004141154014001d540a0300c0d00010055170400103900c0c44000c685045408103064411000041418025207581002a0f084d58 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794761816 1250 794760566 794760569
    0x80606160b1b0322060212070f0e1909180210050d06150c0f08041a07060f0513080c030904020f0a030b0111151f0e0916030b070806120115 61
    0x24400d4080034100360b6800c5005000541e00c00848440c8101d000d22920036107035050b0480e80c0315482c00b6003044689104104d031083e0032a112004607904598004041d40d200f0480788a17540704440c40700003911760102c0f1418850003406480d5640d03a445c800318142c1410700f00c08240d45075006119001d0704148a030014150341220040d610001c1c01c1103408030f0500007403240c04c0a03244072075030351030f0540e015501c0b1010f02e58581d00c81030b038880e0010040462050312400f55149404440c4242680da1030781031070080119441c503028030382501d20b0103081c81005207403071b0945070f0402d0700140d807181c40340d061036092821441094542e560051000407400c0d0701490b620007814801d16035440030070850401c107005480e0001ca82c1c0142266400c141200e80508101d50486900488409084200f81d0440f071036403c40800103412481c003507030103401006204130003045880840181c802d04005001e1641e076402110040c083c0c492014050740380005a55525000304101020072007a00902061480445101e10a43c15 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794763066 1250 794761816 794761831
    0x602040506191713030509010c170403170f19022401080f120f071403040902072001140c010b090a0c09140603060d030c150c0f1d01080606160b 63
    0x480203d00709070320341c0c0040f00744500b852258010038240e195408880e20f0b441800003505000c448942c000100b00e403128440d40c420301d00f0a92543d1281141024140100c40700079550720404100442c01c1c402800c502556403014012010701c420300f12001c01030382094248158019200081e01d82545803146885440c2d048921540c00c1d01d59980c05109004c3c0c6607070055a440c1c084000030010610311400280c0282012070290343d505691410281480d802d580c0a0391040640e075401040e40810300c00c0004088403440000e140c603402e41288440081c1111010031152916064041100d000e801020b400280d01900018a0130b4103901c5c045e0b48500c018000b031340fa2070300001c4607950085011108401c8140104e42c0060456041d03075074080c20412600345032007003181041640c203220000500c100039204910100700401007040404040d004000035007000c0c140040080038843c80074580390030340320402c107502d0a29000c01070b03584013030110f200b61050400c1a4070099410000100f0300075007035405800b81c1c41d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794764316 1250 794763066 794763077
    0x14150c07030b1b12250f050f07080c010f06121a04110d0309080115060e060d090f060e010b010503010b07062a0806040b090402060f0a0c020a030b10090e19060204050619 74
    0x540c0d0303c094145c00c004005440807403412403100004a00034800340001740c220381400303480c01441d5035a040d80c981201700030101507911803816051340c601a000b242c01500e01c0c0e01c002c2c02e03940015210341211140940e1044400440c0c5e20205050041f802b151000001c40036100810461591034000c00d00b1415105480d0154600b0058200858510806e10100c410560760341408040440401c103080c1c0c0600e030030103101d541d14441c91740000c400c40e03045c9440074000e5800140800c030401440c1c0c00d6074216940c1c2410010104014000040001e00380c5288580002d40065818010140504d00c41c012200200c080c894808010042903030100006108810644080c4490702c182400d00010b420241e034002c1d40100140b021141c1041d940c005000004124a8000303003003d074035008a1010b401c0364000fa00c40c142d49008002c44801c090356244010100d00300704001c00880c0c10b000035181c00101c00003405554481027084144502070f0142d501611000b80faa82e034640310103a2a160034545030310000701041c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794765566 1250 794764316 794764351
    0x10902040507052701091703090a060903120c0b07081f120615031a07020c040609090201020d020d05030a09020f090a02030f0901060b2b0614150c07030b1b12 69
    0x1110103e600c01c130030106031a2005d5240c108031225074840d40c0f15802d051944414001a41c2035640d280e107045c010440c946840b15000e040d0704000c00301d890384041e54014022002050400100d100c1401a40060075142203280303502c5a02144010001c0c4034007250403166031280100c7e0070506811901070b42c502c9070004001c0c64214401c2110301a0151101520b003140c480c908000c50200400114bd1004543c8151840810385000050884505030440d0408a5844c81507808550f010442c550f406200d0780000d003044040300c0c4004085220052103a2651a2034510315004c44d16a10220a040c440052050750140b8002e039043d0000c2d04200e0b03150103c08621408a05840c9040c85010260307042e110203103207851880600c40407019044c628400307403091010347e40340d5003000905c14a405091222200c000325100f6a0401c944484540d124200485007002031601d41d410010300710b4100c039401001c48206503600702601c444040801c03400300209100240000e20400000041d51140c00302c20724a11426 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794766816 1250 794765566 794765617
    0xb0c1c051c050603030901030e150411120a0b06041806110712080c07030e0d200a1d0f07030b03060406091208011503091e0303050f01150203031801090204050705 71
    0x103507000d88440d60542c05c100301300b5034154402e80002d08400100f100719006502074900c07003404020100d40558016a001c40122a18a030014072040380b030101c00c000340425040d507240e070100c1803005840244140d03915450b00c0c00c44540e0200054149030084000c01050088014954072a84003006c201c07101d000031100000b07046d00031441940559000754845080190350b0780c050700c0400e110011507a00107881c0e00c01031b0001d810081d8040000003c803540028142e454003e108405000c0d070015408655000080c03452030607891480c540c8040310807900e105980380c0c94003c0c0c0040222140c0280c06000340030030001845501c4d0480783c5d81501c240e01d040002500d41c0c1d03040782e0a034805e010b00800413403c5208032000502c66044030701018020305180c1120104c04241085036500c0c0740b01280841e482d00200403107034002d034083c54010440400d040c0c8441840240080d1248401414401e091501d0504110071503c00d60000c5055540900b042041f030401010242c00c0750028a040c0032911040312640341c09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794768066 1250 794766816 794766821
    0xc210314090f0604060e1f1d010b03031c1122050d0309030201200d230c0a020603130609150b120628020d090c0609050105040b0c1c051c 60
    0xe8103080b0040d04680e00c0d03d540d488068030809240a01c6840b440000d22840f5100d10100d403804035242400186c400f9101c00240000c1106860104550b450081c0f10a00c503140401104d40c50146440d64607103030016801e40d80c000b803000742c034103151060010600c0c6000030054120118540066440c50210b19560010031a11592400c0000c0019a00c21740c100015401130342c0c2855845143c00c1070031440b8550845103480e02d8001110580000c0102110415a8140d080048400781092010b5071405000900260303882d5140c03031009009440010004420821250b50704a040d9403002c82802010030604080e41c3c0200702100e840340b00340ca05008840245042c181070310702c5a6028000e88003554035444044014078001c4071565001e0000000c5121011991006000084404000044442d2141480303c448441c94000c4000d00c000c0d14410710035a80c01c041540c044400100340103940c0d0014801d070794201182070080740f2600180381c0604003515048009131140d02e43c036000000c180080e40120f0800e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794769316 1250 794768066 794768083
    0x110f0601064b030902030a120906090b07110621041a090a0204020309030d05040f0c080303240a0b121503070b04140d0b0103030206040302150c0a0c21031409 69
    0x40040c24400b4442420031480490b4094100d810300042100e01c40d008079042104100e801c480c41280124142240c1d5001000480640f0b0f036454103d49003401c003109143c19101e032000243c6210706003c64a1095904c4008840a1110b5050320341088c41d104010005911000d440c100c3d0003500d8805607140341c01c2c0035080c95110309003d80c000c00684516800340070096001401072502c80c0001c01140f10321910724081c0501071403051080203691240350030301001e0107002d50000781d1a13401c1002841540524036080030525501020340c4030550102c100010b1742e020403944820042180072802414007400e110501c2d108a80320040d50020460300700402d61600f40c0390060b00341440b01030000340700e4180e80810070030310480d0140c103100348490070307450300035034010700364812001640704000b04410103a05100d80005580c10b600b900d241d030f0519410940e42402a540d481e002c1002c0340c0c9501702880482c2050008000c840c94040d43e2501903203500034094006030210100c0114100c004c640b11110000b040030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794770566 1250 794769316 794769407
    0x801110910120f06030b0a06080303160e010207050d06050a1d0d0c0c0321030b01020313030b04030c12020a03110601120813051507030f02070510110f060106 69
    0x2910005006060701c440c640ca8008841c00d5543e410141c0c82d075001c501c0f0302d0000c1c6000303030700b00141c501d404146102510307032542003004250000c1c0300740720920080402101840c8068103008014072402d10040f443c1000c6a0700c52688a6031071040c4505101040e4811402107800c03000074807800c40072005000007a0099565903c3c198400d0003002015171050980103070302032003049a000d1142d9a0784030311040545140d0900055070049182410305901480b508100d400c0038006181481c5079650081c0c5640210710014216031660000a0300309407043c640306608550000c400d190601034150020340d200000c00c0214085801004141c0d500040083c21504950340c80800c0000c0001c06c0e070703501c541d50300103c89001c0001d440f2807000c11907030f490071000d510002d60000780d241c40e466039083c000c0c803403d200400c003030a5400c80c190074000c60701d498082c580c50b10742c60304008401c0141401003514141c1504000c00342800751074000b040301e9502c4500900d090401280200441b0001e46205c01d031500c1c201e0151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794771816 1250 794770566 794770579
    0x120309191d1b09030705061b070f0b0301051012060807080c0301150b0a0c060606030f05060d11040203070e150a020601080316110d0f030c0c080c01080a021e040f08011109 75
    0x10800320302080041c00502005410380c0c103c00d1b992000303e0b031107801c81c4c41c0503240c0e2001c01c030085581407000c01c04400103001c0101220406450030805000c03d2006000390350140d0080c070b05100e5580d000380741d030410b1700942d11400c020840e5036074071580c1c40304081d00070150580108a8881d0303ca140500030b1301e2001c3c011641000745030b490b240c814107565001200d400140642c102480b40440c01c41d11a00b4001c01c50b41c5c6000c205024402d0b0218104c500003041d90344610125402c0001003a08c58124843c1d8141c1030700d00594907154040103850300d1012008542d07104125a0b100400c1120f643c0c042c0149901d240c08850040e600c414016461f4020141c440c1b0031410f0100b005c0c008204840c4400001c014080c103030701014803143d02c0c0c81c070000280280c20790100305076040c0c04007007096000180c0000c0c40c0000291030024241000202020009498400c1d69500840d40360b01c0238543e4004070155000c0030120669032503840240d0565040035108050702e0f03510740301d6a0110b0010701401c6494210006192 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794773066 1250 794771816 794771851
    0x1c0c02070803090a1415040603140601030c05030703090206040915051207150c061e020304020f01050a0f3c1e080a020a12110706051b0306120309191d 66
    0x2409a008112409141c0c841e0034004213180fa125480010300c040c1c0780275500801c06030052404501b00d03003805013182c3d04161403d03070300076031007070b408000e0304d8116603903103008202640c05000183ca40d00903900000340c400d240048240c0410b801a890b03004803a401e548400350000550b03012629560300d0300c070340100381e107100e100c2c075a03400c0c4940e403250140380c0305100c000b031b185c84009030107849200104a0181030720790001c144000c0d03141000e03490281e08002d20340b992510101c444024902a4129900030601600741c804484000c45064520b0401d040e10400c1212010070f510381400c0b280202c801e030004651504c0d2a0204000202d002e1800b1100d25185c2c5516034846000c1480203501c0409128200140120860544c813814010508584030208000340c5038001c50800c5e0048510141c66018070402561043c43e011161005403980050100c1d07091601541045200c3e05600c20030340001d5002810340d1891a900252450280607101140101d03090303a801d501c0a51031032041900c100301500041c810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794774316 1250 794773066 794773079
    0x203160b03131e20030d020304050d0510140601080c070b1b0c07030516090539031906060e031b010c0f051b060315060d021c0c02070803090a 62
    0x4507101424407890110100b20030200a0f4241e00140c030030112044003401d014415549610700054246100460181c4008080790401a64a101d18802d03d4018810100f0102c2802070a118090b060fa03100300e030a00c00d484040c0d07503c900188080f10020301055002d404907034401c2421043c1e801c415409142140207860741d03c0c0c0d400d07a4080c00300d00c1101c035880070060b0140340681031162800940c42a8000c111001032103078004400070341a000501c489140000304040c040303080d40740c00000c06441c903108507000880d03288201004040e40d00607042d084000309014464003640c041a0b00c0c0000707a60300b0030205440e544101d0751052400380860780340e0701a25140c130884042d46d8541c07807031030014142400018103d5443c00c2c52004240c20940e41398014a4500c04030800c2c00c0f24518654101316651442c2d46020011361516040880301f0703078002e800c00720b40340c8001a80c42d030450314001c80e41041c11136882e000395041d0000e05540c00404006020f80c510000380d01400000ba11a1041d0040070f03038038468103012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794775566 1250 794774316 794774341
    0x601032a1803051903030c0c0c0b030c04030c0609140d110f06190507050c190306020703140c1b0f0607080705013209060705040e070306030213090203160b03 69
    0xc0c5a5044070111110010000e001080b02002c0c0c20300c11510180700d1603860401400322030002c010700090190700204c003c0018503000240058400d06001180c59403107045501545005a40004190f4a0582e001160703c0384c02c680d03514121381956030701e045e80e4490f0009000c0300caa0f181e140140081e42c403529410891404881e8071040040142080341080840780c6221246101d030208170000c0f40c0001910000e000c82030080c0070703440e00c1c26604211241c1d4400c008510702400707403001130403051b8045010000c041c0316864031002088000035503910784030510401d94440c00c0030030500c210a03560f41101d2103903060080c441211504d0050129040070455110951603900c040c104540d0344d581c0311081040c08111128204d416000c02c0c080e4404400700181c0407280403809891411154840c00c1049120765009088406aa001c128040c819803030fa0401507001c0c2c40c1c5c1d508000d6012140c920030780098021382d401038000c81d0088080312980024265040c05981c0d0034041d0b00241441040001c480c4680034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794776816 1250 794775566 794775587
    0x20a110f1f0309030e030715080a020403240e060601121a10080402120a11060a0e0d031d09011a0a02160902030604060803090a031b08030d050601032a 66
    0x80d005107480c030020074101001c40c1c0c0c103401e4000440d50315840381060560028080b08000b40c260f000303204280c14519040e40d070b803400240310020030040200080003c0b42d00d40544004581c401341c034841401c7c0305210701c0656007440203811640c42c80c080502c50003640014109021303506c10386900e00b0000b040300e119406000f5034021803904460310300103403149072542c92003410703185003594513042c19007410f10411503a030113a9020b11001350b00203007140010901024500700030703250807200169645500c440a507001d501c0d0044e144c0d4012160402c00c028140c0040308000c501000d149162141d50000c001c01440314428024510720101050713042918441d4980100400700d124011508694800d55450541000c581c012411140e00401446004c0c01c00f0b0081501812000e8040c5040c61206004104c5e06809480007425103400c1010494982c01034100000141c102c0c4420349035074061040040300909000d0711140d0001e0b103003501c12111403813610801202c041c04401d513000c007007032828011031304800701 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794778066 1250 794776816 794776819
    0x801060503270307060c0c0b01050603061201020304060c0f0f02060a1a060301030f02030d0503010e0f06060f0d0506090106020303070c030f050f0406030e0d050c0316060209030d0206010e07020a110f 87
    0x20007104800400d00081c0b001c03145204000a40c2d0f02c288038546401510140340c0200c003800001120000014000642c9034117490b0140c494503265901c00b00051220f042c5071602e03032070552001050000340320320b6812503450490161101150650000341c1140e807031040d04000c000581081001c19024001500900071032a104502810080005030000d40d45e58002c1c1e1045a56003010402d000c2141400d01407001640590705029045601d0b1041c0c104003084000c04401c0b0501600001170465502c90046d944030258840d030303144c0c40f030380024000701c001c020958410340710b0307800107000082c1d551000046912400c869540c02c0311081040da030680780781c1914000c5406008080c400c1082d8035180b40c025000400c001d550100720707a0425445142848230b0000c4410400c0740410141c1c11812000041781d440120844140c04910003d04086000340160101154107004014030545282c0d8001581030585152420750b5a40c1c3d200c2c14826070362442c400e41d0040c0890440d4080c1c0705603160416100415000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794779316 1250 794778066 794778091
    0x60405060d0204170d080c12010302040e071a0405090a02210411060324040c0905220906020a3b0112050103150c03090203030f0715060f23010801060503 67
    0xc91303200640710600d5810b101c4009900c01100458915440100d2030380015008500514150400c443ca80183d841400041d0190b610780c084410440420401d490003030005c501d00350035400c0c4010484060358000e01c10184a0302514001c0345020303803580b007180d4030090320760040219840310340b03c90700f104030000f481035680e5080c02d5450812921004010751044546260407050290241c00c80c00c40d00700c0080100340550b1510102e9010207070032078490307401c0c1c0b101110161120b00c00c10785180308200b4001424410720b8145040e102c10082c00760090104e54005480f5403401c4071102c50003501504070f0030101e04400324000080e021020000183d0908a403043c9058500220200a02c41c20350f2020f0b0f100721a813841c3c2003003040c0316140c5403040c6501c0700c240303240500c02c000a54002075900d000c0c40b00d07290000313100042c500d0200500300d605103249a031054000e1044030351b00c500e042d50070250742c4560540d0080c1d40c1c1310584c09103000c003150b0f450206c0503151014941d0a0440840d000c1d040181034401480b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794780566 1250 794779316 794779319
    0x31006210212060406080118030809030906070501090201080c160f1e03080108060c1c0c030b0d03090303030605121905120d090c050d1505061c05031206060306060405060d0204 77
    0x10030324001408000d0225078042d80b00e0628006010480e40320350700004441e45001e104081aa207003107407802c1410f80601c0c0c407a0030750b21104c40300c2d400c520503a0300c92548082c0004005d4100001034000d580e55a0023602c5503001c03a070311285207071464880d560030303902c540b014215000d00040184100c001d03040c4c022040c01107503880010946650150010301a004901c0800c01004107031000c004c0b869100c0f4400c000242400403803440c200c088101d44007032a040c552a0002c034003006102c0e90180c40100c00081c04105c20340303050b040180c021074207400150006810401c001c10103091601184e024081c0c040010300184181c0c1d800c00d0520b41c8148001c036094011003100a2624228001074445c400e601880001c3d0b1402918100342e8481c0a94001e80c010070686940d080441e49480c41d90038000400600405c40c1e03074400c00000c01001d40a03d00c05018100b000c904020b0000000207024001484044d2480688906040108a0008440180d840402080700b800b0500307082c00648408030490b800035081a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794781816 1250 794780566 794780627
    0x70e0913060f092103020f07030503060411030c070b0a02041404050411060d06180c0509090c090a030305030f060f060f1b071512050603120a0c210e0105031006 70
    0x86046141c20b0303c008110313101035041c0303550000c01c4101c00030141c10b046191800910f010300c9140103005000c1e06021010002805e0345e02c46802030714120200c1ca00b11580c80c50028401c900b1900003540503a00618845c001500504181c801c80d0113480040c110000c4070703848030302000040c04000308219018a00c2d5200081c1c1605c07620060f0682c07440b5010003041c1c070390a01203000c0d4000340c040420340d102b5081045c4c0c402e540e60420125011f014040c2d070210a50b680b0110396a80b07030700c50500215000540c69000105155206010f13600078070000c0800c44140d04c4c2c200800c20b050703810058095201004102c05030f10203100c0b80080c0354822600402c2006210702c050880e050600a510820844e10301805900d06183c2c4082ca8000410b5401000c001d1401c00b400403d594545c0d0110009030094005911418680500f00c85400c036580000d2a040040c1300b562030816603140e400c00800030449412090009602480a49102d1050804c0c0001c1091410300c0480318100304881115200d0001520002c81 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794783066 1250 794781816 794781821
    0xf050f0907030b220b03070f090513140a0b364b03030106050702180a06051504030b0a0f0e07140f1e090603070527070e0913060f 57
    0x4003c3c15500744040c2c00000100001e807a0f017050100d1280e08a504180211050003490b0000d07100281000100f83c3d5990310f50038001d140e02040036140140302050b25120000c00508148a00d20aa04400140e2103060580030000c2c10450a911182818086c2d9400e00c4c049843c41c03400340d40c01c01c04440066813541d40d007182000603000d104031803034601001402039413050005409100781c0c2441030301d51141e044100c641c5901040c0510010450700041510035961001c41006104911506820b01c500707200e02508001e00e030600c04c0b640120f07030000310480307051740e0441560100c0c0d070080e10900050b5160070b00200113004600d800c9082d69034862400a0082042040001500328125041d002c42d03414000c0020100450700c1907446401d802d000207000602d088070704811008150f490b0141038036107030002410b01c4442d810441e044200c42c145080038007400b0122503481c41c040c0c81d24540031345071200121403442c2c00700c6540380c118420b400807820200020041c81c2c542e23402160000340910400c1108402d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794784172 1106 794783066 794783089
    0xa0906080705042d062109170a09080c0f0a12560403050c010e01020a050a0f0309110d05030c030f130f050f0907030b 52
    0x3001c600981c260b801928816241000382c0903c40140d04820468200201800e2424000001e1a501403503a01e0302151030b40d00748030614400500100701501c96000d04440801600c0366810030606000083d05002140b95110340c803c070f1400c240039103000c1c95001a14410400000500a00d0341e9000301101101d584204600000c5074608044009401c060a00d100004600b80007a401148411001004c0350002c644c03d04200d002401e00d071501007840c044680b0303843c0420042404039010300050306020217203000100e0700b500c16141ca41d0980c0c03c9800c1c5100031030000700e044075650f0703003020141120000a00d000c10030701c0c00d02e486075100b40112490340b03402802d0b000090360a0090503c21602c6041501c1e00300c0e41e48880d01d21007800258400065141d10300d00c5008003280400c00681e16000300c0b5402420000c05007041c0f02040941035018080b281030599803490f1a0302c6464107010703c00d = true := by decide +kernel

theorem cover : BRFrame.Cov 794604316 794784172 := by
  have h0 := BRFrame.cov_init 794604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794604316 ≤ n) (h2 : n < 794784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
