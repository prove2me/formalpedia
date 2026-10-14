-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:50.099918+00:00
-- url     : https://prove2.me/submissions/1b2ff3aa-3246-4738-9984-62fe3e861dee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 402158273 ≤ n < 402338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 402159523 1250 402158273 402158293
    0x608070b090a06030501030b0a0f020c15070905040e06070806010c1703040303060902130e06030307020405131b06080c0f0c0604140d0e060315010e0a0902120f060105120405 76
    0x24021040945500846940d50380c001c1c038140310348004150301074001c040c940401840042c40004110340c1000c58040302007003042a00301031600910500208100f03074420200414803c8446051031840f0b1200c5072a26207500c1d50328810b2100b80e5103071201100b4180c20200000e0300040c02442d00a0f0041ca040c500310041d88039940d02c5200c00c403003280c4114901000031041000b0141d1601a0b140030b8000e03d4405e6061640700c285562401d90320f0b0044ac1d4810314008001002920208103987c811500203209200b1307801c04514400700201100010364030750513a045070402d4013100085060445400307988046d030b50703540e94500a00e107030843c40e240141d2205c20811144e91074420801240190300800c089070b082d0780300090300d61404035030720f103102c1c2849202070f0040060f40d101e0040ea80c2c0040d000d403400a01c004e0140040300c00c0003501c240c0c2c41d400f420400d80810303e045994050102c40807186000b4249848803d01e19440100c100d408030b0004400700041d0503840e00d002011608a4420411a880040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 402160773 1250 402159523 402159539
    0x305010602010b010c0209131401020909011203021f020c0d030203060915030a1101141206041d07030b0406060302280f0b0403061a040c0e032a09070c0602030412022b1206 75
    0x40c0c40b00c9527110b169000318a10406103030040d0018010142003190407420151942e01a403505031020052143c9407030180681c88120b0550115041d200e17804040c0d411080c00114060f009401c1a02d106000d00500000074400100703001c092480030400400804000e2074907a00d50880c400000d1815041106003180301d0400d00300b1001500d1081ca507000c11603082c3c5455010701040f20008650340b428002c0e402741c10740e009203002c6066026680c10a0410724030b0794403414007001600e200e84c80290054400c10040e400d03481c140c10750f4004003480200381c002060b95040480035049150048000c0c2c030f0005c0000300001641948040f161032a4280c0c8000d40d821141e0004c0c04440711203911802040d55807612110078a8184031100c0c0724038009d80e00000003e07600005ca10601c441d034021500680250020800603806030b800500e0144e882a015982c0b407900345050303002c9807407031016400076124000c003603103800c1c0050701009810f14122411402c400c1030a50704460904000150303d0645645440201d8054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 402162023 1250 402160773 402160793
    0xf07050909040b190c0e06090307050d030302070314030403080a020706090c0326040f051002100908040f0b07050a031b020a0b0c0d14070b0406111303030305010602010b010c020913 79
    0x182c003c00303030800d0b01c0ca0400705446210300390a540e140514681003001d1001500300e08a4000c4520582c0d501e500c80000b5004646016501c0e0021503115010141c00c1c410943c0c107800401d0920301c03994984040c00c9240c1c90b1400c19000c10707280280880c04001c0069030304812075000d05201070250102207003407851500e81c96547c2446400075038420810043c030284010340c12aa50111109421400340380a2400e90922504907981c06002d2099909600340341c00d092080100c0c2006519111301003103494010301e071502041e03210b441900f0408440d0440064032581d02e4055910340740e002005008803aa5076982140d8a0201c0010710740300712041203588026803a919034080c040c1600065542c1d6502400403054074061004290030708104003651042c0b070b002086001e8035100740c1d000e04004560703202e6103403446c007403d00000c0f0880c00e01c03808900243c0c20002e045040040340d00030b40b810083d1b6601d0320422802d0312141c1c210107010640c2c02c440403006041c0321081e50f80c07040b17040601c1c045c4030106540b00114a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 402163273 1250 402162023 402162031
    0xa1802100215180a08090303070b010e070906050301030201050a270e220203030a0f090b030a09060506041505090c090439080a0b0301061e06080c0c060f07050909 71
    0x10791101c03026910038002e40346515044000d5a0b0084000c0034025142640c41300410380040070290081441c80302520100140d42807039030f001418040568662280000342c0d20100c5c0e10000040c40c0c188001046070040c002c880c103a82e01a942e031407030030744400d0341035422052041e41c10005c001030700380b222100c00001d44210043c08524100f80020f00b803100c01e24a232030034a038800b1000c2c0658000c0100050354000110b9030484080d05100c01020140d0800351424021584503410303d03034001007006000152076000d206524851041001583c44010500c000c807507140b1002e4840740104d43c800d228a10b4003280503507002040503101c81c036007010100490300343d03a454100c20f44802610350b4440381c0004d00010500c050050080c5450915144003801842c4010192405101540d640d5404104c0e0b1002e420040240009038075002c5400351416000016550501c10301c00010203180100760701490080868004e410ba10300141030f00e0315030880648075408090034950034071901b0000300b03003aa00c5100c846481 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 402164523 1250 402163273 402163277
    0x1407020a05040c0c060f020a21060e01060903030206090c030d05090d0c290a0c020904230303160801150e03070911091804020904060b1305041401060512060a180210 72
    0x59040da85081411b44134056455141c0c02c0c018010044070b60f85c00407070040c6800a80703402a40c0d00f500d401c8440010241034010302c10180c114800421000d81043d443c01c00c40348a03038201d40a5541d4000c1568a43d034a52007400c2e810340040580a00c11440742d40034003221b2900915107002481e0541e60501440ca0341d501c82070303505c43c5110120340712114900c6a8104003100c0358103645420b01003a001030101201d104000c3c81890120f001c80d0522249402d00340c1a2880380070322100307803d149442d26503a80c100311101c0d00c1d9124202042007803144181d5a0300d0480d01c410b00821495800c0440580d080606010b600f6003600c00c0407030000d03103d411406100c4840e1010020241d50310448418421010400e9111482651941c0280070050311208901c41c0d00035080700780094249400c10009410340e000c0c41d011000c6ca401c100070b020074821500c04401c95040100f00802005603554203104e41a401d025a504880d0045000038900d60359a07007118443c1c0f104151180d00031700090b40043e1110400c10071a01c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 402165773 1250 402164523 402164537
    0x307031103010906051206131506090504030c050d0207120b0408091e010f0c03080f070e120313051507121202160210090810180b1806161407020a05040c 67
    0x442030504240482445611310081c00c11403500c92008e0822605403c0b000f00380300c104c11206011006140d119402904036030038180481d082506008255040c180801c0e6140e000311612384201600016619086641840760010002480c6c0c84404ca44000140169100c070800c2141d601340c1e40e580310100d16101c00c4001c2c0454a031816200041186480c0d00368842030115040201001c6a0407201095205291008410480c0d07541d4004a4801085945407901300410601001c419007000c40608070003440f10182500c2c1643d12020005811103810380d030788540e241045800041030310180707032804005540c28081c015007200080f803400c83e80079031407100c8a0365855441d034045103004c98005901e0000f524000f0301e88c80c00e01d0301ca5038a464441003081c19040e91141200484810710311410895070304840d051206103071076819400b45840021548034103000c1c0f100000c40c048a020a0b40f0013100c034a1b030740c4000700d280070300b9a00072503817040d001a0b078000d143e00e10000c0d40b6540c030b0041d1004100710741d031450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 402167023 1250 402165773 402165779
    0x6150303111f02070c05040606210203070e1014160303050a09050706120b060c06010806090a0b010512031e040503011a030d05160506091b061e0307031103010906 71
    0x410300080c1c600001c000740c01c2680070041d24844a50540140c4182c03040041e035803021840c25030041480c41e4000380d002800c0c8200054625088115245910182c075440008030090320460700c100d110448010300416541107403442070342003000695050326400e04241c4210300032441c040c000f54201202c0380000c0c0640200312001c061b454050542c004c59001014000440c4540e00d0755168101c030b018a40c2005100c11058480080b40d0704500340d580c0c80504015a208d10811900751034480900601182d4400c55000c2083c00400050045c100768004002404503400c20cc00c100c0c00b100c1d111103038500c0307120501060b5101c214244121940c1d20300181555603407841c0600345801e590389402c0000d00d2071a140318420071901c01061840700007500785001035941101c0340354010030368a08040036106100f0300042005a2400180242e81e82a0040c10400900320030010441c0c4c42c07203050710b00094100c00c43d202074140d20302e4401a41d00486242000304010a4040c3c640034a82c10036405402c116803126010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 402168273 1250 402167023 402167027
    0xa050c01171302041533090f0302040203060109082508193026010b070609030201020c03210a0e031204020301091205031e01050f060f0706150303 64
    0x46032144881e404640424584102c0c0901c1107a444040a0302607604e595050810350014560b141c003408005041000f0303554030411910320040d00741c0d102c0c001a15010101010a401402d07082e04a440a42c0380502290840e800d03c00a0740010702298180b1483e10030210305084140100c1070100f030040000d008419540c10101c411032203542c450002c5400140c0c08080c0c000c2003401700c00801e50450744000d150b180300141a014143c075800c00c2c0001c2e09101004c0c4444c294450300c01102129403500741214080c400415921400c400e2040f820310740f400b0044200018184c0c8c0200d00c3c0a8001e00005041601028640381554480442d030390071078204140d02024009410f00c95604405080c0d010880a2a0b405080703540340710302400350044460071000942159000d4012050943d48420302c9401c20400c400040c01c80e400c2966500f4041c1e10a0a002d03180181c000c180c44d048450040001000804001c00e00645920802e800020400c0420040000c1800b901070f4200742203030411500c3c101440d500700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 402169523 1250 402168273 402168287
    0x705070206040f170d0915110c09010e190216331409030906040611030906190305090d0e0d1b060203120c04030309060807030e0d020f1513060203090f0a050c01 70
    0x440c24030a031184180a80c40c221061450f4480c1c1d0b6050035440c08c0e081d801d4007850203503400f401541c411302807070000c100100034000450007650100000c801404003054140c00703900800c1410b070368079812071002c0c001142c0c1c01101d81304210b03206103480d1030305080700858800e80c1260055120000b0f44504201c40100307412070b0349a501a8108001c2c0d41888071400025800b84280c0c0700340c60420040740c0b480910080240116000c1000c0100398507981c410260f001d0308050701d1440c0b50310100381351034005180a070011032040100301c065522400c90207a01c0c0100020b140131490291910a450700c6440300d00700b1004440009441290001c40d2960305000c02c1da642050000d0100113180018402000025040b4140b0000e0f41c3d61810801d02a58500348100c005210050007800f41c1d02c00c0a001c0382c1c009401240362500342c4100020355100030440464564201411340d0005400c500820101000c40c1084e0b02850b040180b6005444626808880a81c80d11805440a890b980c0021092500c02c0d82c0000e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 402170773 1250 402169523 402169543
    0xf0b010e040b061801090e09060a0c0503040201140a0504050d14061008030f09010309020618010f020a110609031f02130f0b0313020307121b14090705070206040f17 72
    0x1e0705110080e00310012840a0003110100c203026a03240c01511102da0085e40d20300042c000501082c55240303840c02c41c3e10b035980070945114038407500d00300e0f4524407140f1410480b44100d806842e91054212070f040c0000d42e1358046c0ca610000c00c40180400b0440c1e555441c0c1c04a180c50042c0e41c81c80e032980703072820f4a50510030064803030402410200b1040140250110175140307000c0001440d6501c4a02c1c01c00160050070345024001d5021000107002d4222403150300360100c941e4401e0742c480c0b55030700c07a242c005d0380d03181041030018084c803030403d01080442c80e06400500c4131540103420349030300d803941d40160028044580c45080c03803242c000c00d10780d8440c007031444003030028200c0703825181031245055000000c511014200100c0940c150000d02c06649040261000400b00e900d00441c204080d400e2400c0d0611003c00346010340402d0b030a00113491b888c0c400d8094008200144a10446e448180307040c0c035690700c940800ca82014040c0000640c840050701c50400800c4415405800c0d4600c5500e00360508000303203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 402172023 1250 402170773 402170779
    0x90311010203160803060303070b040b091002031e2e09050c071106090d080301060c02091e01170708070b0903010f15060c0807060507181a031611010f0b010e 69
    0x4032444240503e08000d55607459040106550707a5269140440d0a52041e01f40182030154502c0a0108004101041c07912803420b14080c0d07910001c020b980c0300241c0c801030340c030100e50786148100b80ba40403130070740b0b00c00b070b0800c810410810001e0300700c4440112542c04c1454140c6148038620040103420224000c1580c07081c60705405514240310340e40d98100103080c8242840c00745002050108032515007030701d00702895401004003034403503940c0c18004025000460040f4000d11000b004510812560a80082c107516a618040050303800c0105c074103181004106801e11601c07840400080c0350b11f003400240d0180100807805036517241d5650906007584e03100711b9540380b810302d0b104d800040c40074070f11041410b0720010301c0e203d81e00d15a94200307040c5500a008004c4c1c003240c070301401d010899411a183e4101090045c83c28400c00d640c444180c404a40014a42c5040d40020400980c01d0202000c81c880088401e05108410380c004c644c54a0845505038010303128280c0c0c0f8590460f0568002100d100c82c52011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 402173273 1250 402172023 402172027
    0x6070f081e040605090c0d0507050102071a030703331d042001030b060415080606030705040e040c271d071a0f0706050103060f02070308040b090715090311010203 71
    0x41010381c0e41c0d128014000b4003015070b1407010800c81e440c240030b044120320008008040005844c181113071121101e10170b55000d8031036041c00180325401e2a59459207450001c40650a556607550150302402c801d89480c141a5400110030314888101e41c40710750b80b800088600340c1d03040d050841509120304146407450b01c00f141d200410000404c2c8040c0c1800200d1b003200c414041c204550016406000c2c41c3e202250b10040c04200840c10b000741c007a6868100079076542d00303450f1703031a0074080c05001d1000b80c03907101c0098000c01c0144554410300000c66086446242c20303d91060b0b641100c40349803c0e100b49000032100116100f000e140d0f003240189500c052040e0014010032684c801c030507503191400d2080101058448203000000c818800c01e95500c582041000380c0c0c0c9500c0e61400d00d000780720900044500d03620f800340300d48155000d44280e13001960b0540303420180d40c603580c0f034000054100030000202c51055402c0812200414000c134000035501d9201c1c5625981149400d0300e108220803841e0b8119842 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 402174523 1250 402173273 402173311
    0x9130504110d15020427020f040b0a12060b07120336060c050a020106150f0e0d05010e01150510210f0501170105070c0309140103090506070f08 63
    0x45101c4900180c011240400950714a143c0a01000038201005105504c0845d0008014a1a00540c5548001c860921900a066070196000ca000309031200e03502d40c4080c0000d019001c12071004044141541c20034a110300c00b540003030400d0320a132b6046403941810104840c02080960b840e01001890300742001d10500300402c20490000c005215414541c8415404038000081c030780c51052103090300002c090111100c8280060304540c800170b840c100541c0b920900207001704504c6541321540d00282d80d40e0028040b049000ca400701c2202c14400c0d0700c81c22607015000014802d00c03400b0300d0710070080000b140101078070080d81e4080455900c40b5009070032901001e8001907029003c0600382c200406001107a03d00b0304104070042c0180d000c503c6141d032401c000400c0c1c00700c0c5510f10306540c4014000a0107603a89081084a00429484000300400c42441050001c5070745103120110002041c50001030500c01a11000d02d442429186c6d0b00c080340c03a009200b80c01d1030703010b0561688403880d11100208205 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 402175773 1250 402174523 402174533
    0x6013309092f0d091a0402090c1207212d14041e060e1606110a081b150f070801080d0e0109080a1b150e0d0203010605090405010209130504 61
    0x18503240d24808440008000c24000ca95910120f03105412403d05c00c00d0401002d2410980c20040d1020303803003507030041c000410101410381181c2564030511382d21052905d07006410303038555240b050701c030240e070150520302c1402c52840c2c030611000c00401c42d2000c11000c4185c400c0c1500c1009480d45904a0341404440000149103001198100b640500300301160100c0c9400ca14414030140303802014a0300f0040c400c41d105c90300040d000d414121884c03842d41c4240c1e03100f800761403c0400c0118050203411044000c008180514080c111040c1c469910040d40e2110903441800d090840008a0702460340c0c506100601c1310f409803d59110340c9906004107254141340285944900140c0315000300308030301c1050060b50344a00301010090200c0c4046138440740701031402044a001c4150141785801e00441c00248c1e40340c4ca00722132011104c00d034a882d4406260a01401200682c41e90f043e60076640300c0b00d00264507245c440340c0a00c124083c81c00183c40f112110104407140320101403d0f0100c5060070203120100e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 402177023 1250 402175773 402175841
    0x1206120b011e080d02030304060507080f15060409060f0311010305011a07051507120506032d0f060103031d0f01090902280c031e020601330909 63
    0x2d8112400c900503030800341c408400300c41507504861110700860410310364483d0004051802140b040e50103015690315071034100d404c1041191911500c01d03407100860502016289400540c80b0080d001904d441d81320310000c0290344090344010300a00041c4000c0043c0400401400c0005409280500440d454984101d44403d0000e0080000c0f40c00000e1401c2080010007107114403182e4030304051124504070801404890b01445c6504074a4100740016603140740104080054000410b452404d4030031071034000b22902d00c0c0080c40d0710b0a2060121814040c00b041011038020b50bc071790b440044603800c0d81840d40260f0446070b5228083c00c4030b01c4243e20349a801c0300c100c40640720740080068492099011034199410780704542001400110b0001ca51550b2054032081080d0003911030030028400144200181b160210050f401a08110010300400c8142109034840e446540c000c2e108031001c0c20309805065103002c00344000b08200135420003442d0300e5405002555020004a0100a0b003c0c100c41300d400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 402178273 1250 402177023 402177029
    0xb0c03120a020702040f050f0a09050304140102010f061415090a0306182a0e090607030e0a080a02030a030c020a02030c0108190608012703230702101206120b01 70
    0x4080d5060015412940390780c1600d0301ea5030014000d11204044401c03110080c00141c4520109002d54000240540c095006868091341d1110040d031400d0302e03151940c1103440148009074115500c4600e205004030560003840c014040d82c1c00c42d5810310180400300001da1b00c100c010040ea070181840704d20010303545d141d00d08040707941141010840b081c512403c3d500704c10152000a1403500341080c0c491500c028580d07000c0000c0700001034000215101c0350104140c0d041100c85045581c40880042e407030510a8000034080d805620440d4144265590b4600d0b06400060720100180c0c804500d24803126418000d68048086a0005d001a01201c8e004261641011003565060214440101d509141242403541003112450010400e032500d50b14240d000c4e000038150054440e180d60a008440300040201c010200d9040c0c4580b8090886140d9054000003044c1c1c030b5004400d001c0c000480540c03111050507100001640d60303035a844103240000d42c00c1740d00c150401e03404040307203010400024000038101819 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 402179523 1250 402178273 402178297
    0x60801050d0807081803120412060911131e0c0807030515041508010b09010b070f0f080a2718020d02040f23010c080306101116030c0b0c03 61
    0x280400608210450740f01d0548014101c02c00021072040000d0844a85082d8200480640c0c1c020080e400401459000f60301640005580c6c0041c280006041540320b01c11072407250a110351010b9000002a80d000b12070301c5144140c5d42c56100015000d02060444406114218000c00000280308402420303088010001800e2642e41c0010402480300858003e01902d4000d1041c0701c103480c80424040c0c8000c041c81881d5240d800d00401d1110780ca40070300b98078140d4480755580b6050003510780751400f10032941032055900242c10340e040c0000c281100010030309014182c40350101d10542e80b45d10000c800e8148c4200c4c03003010600006102d107201c840070015150b4841030015071200d01601c441d0000384034980c048031569004440008005000c440214801b10f40000228003d0030f140006641000c0705040051a1010420004a907890703e003082c2032409455240c101110840100c0103450710002c14009514103500c5442001040410324664010b030812103030086c00c001d007034418903a50b40550402419 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402180773 1250 402179523 402179539
    0x6010b07110a0906080312010801060b07200910030218040809100e060301030f1406070c080f07240e030c060a0b1302070308070e10020d0e0a080f06010503150106080105 74
    0x802a41d4080300d0402428582070200701c0c0c3e9645171840c40e5a40d1004011444420403007000086d40345040c81100201d8200404007490701e421a561002d101200c0001900740048444104400c0c1e211000c007244038080400c1c05a0440d41540100004c0f01400c21a0704c8072440038104101c00280520706640712408203030b82088000001c40b0050f0b90170303d10f6108880c2c10401c040000030a0000701904070f0b0f400760041004444405082e0101c0751185001c175808800300c0c420f40d890710001a00080105842000a58171134105501681c850307100d00c0407c0c03b840c601d81c449020740300040c0041e2080c20401c40c26032005610340a81c1d100000d8403444021f0045880b41d94581c510307080340c0c072035814025641074142c90465441010f0704d800703807101c0400d0741e584001842da00c0701002181085200795921f03481d030b60020511115500d00849041c202d48101c95040480342c1400200601d04220359041e000400300540300960415080c146014144106030384290482401013040c580c0082800303041da038040d16550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402182023 1250 402180773 402180803
    0x303201e0708120d0c0807090501050f0c0102070302071a070f0b09072601052d0a0e121903020702060a03020309010b090106020a0b010503071a0c0109060e100b0306010b07 75
    0x141401c00c25072202c0150702492600240480108000788407540704481c3c1005880910300044600481c00c486803000300d504120140155030007400540088070b1a110380034030348510031814170f09907000150304030003680c41100c0c140503178104d00300001596a00c000c1082d0070000651588180c42c01d5186010301404c000c800850b4007030070284490b02c00391103541e01d243c1031110001100008281c0290b6a08455407034000411000b001241810390a0011103410070080c0c0c0c058040c019502d400517058845660340c0b504094074112041c0202c0d6004e40200b0340b00d94030788100850403541c07112001703800d00815104210400040ea111001d442660700e1034640161a65540260b950050001040a586c0003000301c0000403016030009001c210075100307030760a001d1640c0c0c420605903500e100d40541003400c5642e0354051400e02400003c1e049510f80e1400204a1140c40d803520070858286040c81030781340c1c00040741181241100e0040592301202500100010340c50821041c0c035a019000000380011407800c440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402183273 1250 402182023 402182083
    0x11041b05070212070803120a0e030403020d0204180b011211041b0c030216030609060e06070f0c03050904060f0608070c0519110a090507031a15130b030a06030320 71
    0x20b04c3c09021141e00701daa540e103d00e4840034a03142d0072512211000c0c10710740d19000b03422021041d00c04595015103a0207041c441542000060120035059484501e1321004113800714009000143c02043c06401560480c115070405090a4202040060095080c42c018490005034a402d0600e1141d541c40c100001043d6840c0c00c1b03003482c050099844e17404818142c08002e10030300b9400001a98401c440411400e01020309040d181d2408480302030104500f00720458078580103000100e00304780301c1c0c40d01516041e8036174001812682580c000b50301c4400120824805550014144c80d00070358a4100150241c06555070140d0f034400540029100c1c055011480041028442e14800317010002040c0030342c0240ca0b006400000c0c0b40c122500c00c0002e040140e07a011030084130481c082c440c400a0542000e0114403a05e09106174000450b1748030104083c400028143d030f200000d180965141407010580a1460400901e6410340340255950940161300c641c010311400268908079541000c800200800c0031860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402184523 1250 402183273 402183283
    0x20d24060915140c060c21040c05100504030501140901140c03010618050d0b071b020603010306050c090604080714060a210b060c010b27070804080409060311041b05070212 75
    0x496501384a14428041403e06c0d0102400c3c4101e072100100440d80c0641890080100c402d8401a0660b040d0301c0f014000381c04c002c52120201c603480e003010361070517a6a5a0341802c541030100604410405c000c2442040d58082c0035070306444142a148111a04140100121521040c0310781e00900288104e250016025485014010a4010164100d007403060508030040c1e48119403a000164210303000b075a2410512a0710480f940e006801d2500710784c20351b03072882c0c0103280107003070050584c00510181283e40e0340c4400138405480f40c08090002d440c94000882d1206404050251007071005021500e20a50b00c004c0b500e010018400e03c10281441142e0804020442020420740000001400f006c0514054108440828040d078100c030544520700d03050314219541e80452000b010210010480c203600c1080640d804c94000c041c0c152609650352b884030b04681d115441150070f505601071842c15450103115200c10203078202c0304203803204000c10009203207115400b8000d1207010011030341d2040c03c01c1045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402185773 1250 402184523 402184537
    0x30702070b0a02010519060b04030b0a02130b070506010510050a0305130b010803040f08070608060634030f030b031906020f18120d080c0d020d2406091514 68
    0x1031060b681e641a240001c1c0a0704c4110340c1003c0541340076004401c40c4015104031002c444407120032508003415941d404919100280c00f000c81113401380000600d040c440149040180099103030603903100d8030380c50642e003071000590015125419021700140c03207a400104a03081d400052500190a43c1c60100b00e41c00048000b002919481d40c120003c5407100d00040204241c59055210302c0d00240d0f10070080341d541d1040e000b6100000da0440c045603890511401400c6900421001c101d80294000c241c15046108256504450020240311f0024980c10035038031501490140f03800d12803070070b0000119641c3c5e5078003031454007903007401001c110600840d64162001c04e50b0100c0d1107640d0380800144d0649084080304071900c2900000c185544001c0700080208840d0015180c06142c0e0781c4031806500144c2024580c248240c2d000c00050844011902c03544103d410072542910040d0030402c50b0380341010b5690001020301c43c00704000d0000e0390200440c021941ca09191181c10b400043c0c041145038080e210b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402187023 1250 402185773 402185789
    0x5090c2503020a06050f01050103140402030312180a05010605090c180f010e131d0a1707060b060c101b0504050405060109120b06010f0905100e0a050a06050d1109060f03070207 77
    0xc01401b181792400d01625040341e200340d070284172881c0c04000c041440002524003d40c568801c00c070a1000440801d003059000e034100182d100c18060058680b41030580246080711103954641c0d01b030240c0e1070803500039038100e1350880c1d040d41401400403012002c44000120144940c0c101c110003501e9030302c038802d890750b0098068a0515011030210340d200281c040c40031070075980e48924181c40c4c460b403000111031004507045450402da201000c00d44c1c40003544100415240326031100c03100d0743d40751078132001400c01c0e540b01c20040500610103400760089401da4119580740413a0b40301c010340324550104c1502c1c140c070011a40055551184801078922a03c1c036031081c842441443c1400d0103000d41c071404180720306000c6e26070b10b103180791099085401207000d00466a12611100c40883c5c00c0744501c44111303000101030034206c0c13202e0302d62002a180c040c00760300c406c0c00540c00040401c070764061401461284038105030018144100f060010b045409440c200400c5034502000082c89988200b0418000b08204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402188273 1250 402187023 402187031
    0x5121909050601030215070201021911060c15160c080f12191a090f1905100609120b06090a09060617010c09081015080d0905090c2503020a06 62
    0xd454501d858482c00d01c416441070781c1502000100e002d412007205c1905030b05a010b4104041920b00a0001c100d0018040d940d00541889080181d214000242030040c0480e000b4450309a112903500380c0c052009048814840e4603913142c0d0322180e00101c00c12441540504156200d03100c40351b1600e40f90082d41007866124860405202201142410141204884403030501807500c0c103a805d03007415411001d01d0793b00218410300084030f80401c40a40e64020800c130a81c8440315076001c440c0025030340c1c1031703034041c1084a0051081114503040b00308480206405021001e0200451302e0f080c0244000803e21401110040c000813a0520154400b10005500c00400c00c02c3da5151004455596206404042c1300c1d86000700300c440c298003c050202c12144074100512010114940d104040c150001e01100500b06640011074580f0060102012105c2c0c02e98074000f201d450a400c0004100c4054040740051a0420512011100805000e00c2101e00380b9514201904a440e04a103011050345026210501e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402189523 1250 402188273 402188291
    0x60316051e0303070c0b09150c0a03080c19030b0f150313080708161505090d03020a030b090108030c150c071214070605090606030f0303040b041a010803040f15051219 73
    0x561401703413250301d000343c540c0160748d9074003c11004103100741c0c01640302e09c1c0d03c05041d81d00000e20038400301c0e5200104046003402d100c00c00d940d040c07611031005140400700f41c44000c1c02c0824101070005010201d01201c808207507210b83c407800d411138400606540703e1030708400189000d1182190460780055403003400540d444d03100700c00f5104807041d0141d0031140c80081d405250b113880545d02030729026014500c094143c040004a09800961101090070141600e034051840250340e0304028500a006409c09950744503a850340c00703801c016015241a48912110782400807880b480704c01e640015034483c00311550020101401d54074107601031400078104030002005420044103801550056862408172021512007404040d282c621281a8406a40c01400082c0101300340524454005003d40d60407450040005841d43c6040000d0300b02140d00c0c1d00004041181584449202d4020100da07007030100d0302c001900000300503206e11180c0150150521000c40d0075a00d600300782e83c00c0591001c204101c0b5483c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402190773 1250 402189523 402189539
    0x6320601110a060b01020c0402091c170d0b030c01020a052112160906020d020d050306180103050f0705030115050d0c080714091e040813090504030305060316051e0303070c 75
    0x3c01d0350b401500600502018000b18240f0703000350350850400400301030031440450100421582501400d560cc5251031009050b00c0c02200000c0c6850307050008040f90f503000801c24585401c070401c0495046500c185120f10208401103541c1280c03000404699807002c00070308a0200700d0188034031102034207a1103018080b40711400e494408a909142e00c0e0101016034401c000d030703207595420f64440c0240c0c02000417071401b144100002c65015a0003445044030320301c80c540003550781d0341c260400ca40907803212a403084860700401ca640014401140240421508a840711884d2800c610620f0301415000c0c0f06e0b4005c00040710040005400040b0442e6131081e07a5100c07401c0b018039044002801030008801060300c0c018050740e404042c0030210810420703511a030b6211a100d6004003014541980f60100208140c480350040324042ca00079540031866041440c01c150400c10180c10b002079004035030700c040040340c0302c000c4500d2030f170251300c0000c2c05001c2c001f402090451003202d400070122144800d002c60a10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402192023 1250 402190773 402190781
    0x16030e010f0912020a0b01060f03060816051207120605040f02032b052d0d02040b0d1a1e040603050a050d170103170901030b04051306320601110a06 65
    0x41d00441c0f031a040f02c0400301041c0c0e11035003401e0300a084000b00d00c6c01440305902680c0320101c1060300e0700d400140795540b501d119081100d42d012181e0b0303401100c0002c10176454441c070700704000d501c0303a0003901466107000074a850328a84404024010340d01c40d00000d09203d2004104103581e500601a00d0006c00d0741d00542076680111508d140f4a070214851098080d44190142e80c0701200b850f5081414810012451020002c10146001c83c40410080e9440581550000d0001024801001915841404580015551110420a40f02e5a5103c51075819601e0600109502507042140c01c0000c0e2400007040180034190030103072191140d1502d41d0100180080d018020079059941d95902480d07100008060138030038407000d0320000d8070304000900b030712100004003061103050400203021f10b43c640c042401d8038011500100c00340c803501180000e025003405410807400502c4c0301515104042109030074060b003101d605120700c00340040040c03c1039028600d06041e10b0b40d041d080741c5e0718602e1442c20a0140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402193273 1250 402192023 402192041
    0x19080106110a0302060c0309070308040f03050706031815020c190b01060206010b030705030903130315060b03010f180204051207093c060302060c0c0103050f010e16030e010f 76
    0x207008541c0710750502002164a190040c0d16502902950312501450003c41d080500094840c0c0941d100002c002550040280000c103441c5200070b160710f01d50700f81725040c000b05500601c00c4c9410494a000042e161850308003000364080e19a9864030404012a002401807103500c11661107030000640318200111a060009440f42141580d107030b0302c0d810101e840780c60a103d07403d041070080c40030481d0940182c015552010203203089a0901e41451a0100e035000c00754000d582d4081c080918200040082c09510040d0145140407031442d450301c29440503802d01441381e4000b079140c210040c507602d541d1750122030080200900441108005c100f1842e00d0716041c0c0704161165203444000869030704084c4a0401c4a8050540725070210500004030701e10712034051810324555074900703002c001a42e8003001341404208084c014007501c0502000034040701e030042c2290552407400e600401400102c0180b02d40d216190045810b9051940071054014001111025400d542020010424902954810906 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402194523 1250 402193273 402193277
    0x190b07031e0e040b1c03140c060415050f0c250605100e15010f0302092101020d0605030a020a0b070224090f1e01030b060c070803040e0105030708030406031119080106 73
    0x252211340812003480c0c81e0265000501d03141518035800301c0e01900e0007280720020b40440c246800501d04950381422402c8030704880c4039081c50030b61802940e042c0300700d0394010015071142c130481c2800204082c0c0c9006078104181100d0030b0100d0030755080140c052101c1c40da540a0420b1259007020031714081c005841c0d00800001c2154140052035403960030881c00da00c50f038180c594684081500600f207002c0e611600c03030250000351a01462001428550828688042c68000185c4550808950b001035400c29401503100380e0000502c0c0740580d540d0b54400c82100d114a02c055a183c1540c4003243d40584060340b1801950f0414043d50a4403000c6070081505d0340e0308607418501c407683c080c10855060300032242289801c0c12129200c0d0035500a606c54810342000070001030801501412444c075004290300b0611203a000450b0400c4a5004100060f003d00b1b811405441d0342030074104015902e0240d4407901e802c141e1210f002850300c1c0c80c03510895120541d6103004c1c1003414103218015002480c02c3c0314000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402195773 1250 402194523 402194531
    0xd080c01200418020d1e092003060606070c0b04060e0406060503151302161a0108030c06190f0204060c03081f170f0102070f03020606190b07031e0e04 66
    0x103460089800c5400f50b400c0c199101900c02035503000c00340250085400c4c44451580c0314243d105007103240062440f155103245d40414101e0861030700d445100d07280c0103401c58500c1074014074600c0b03507804140c003075102400f500c8844e151289400d048660450583c043d201e071900014005c20300070744c1302074500384080c8140d0302408965900d440885441c0300c1128050b44c0030460158264003890701d80d6188410091004025003020b0111400c41da02902c0750030211186030034280005844005a48581c0c0141080c402560401100c4100e050b00c424005104070000c0000000500c84a40c142c0e00000101041c00701c115121922620058441c641510003a80420210350000c2c512000044902c5000241c02040c11034062505021344a42c488420540609000714030b41c0c2c0c420b0400034809089070340c2c010000600c030840c190901034101440980014000d001d51340c40100000790300325001d000c80baaa40d0034180d56180c68202110300240c0c0c2d4005c00301c222003d84a0300203090303005d040c01c190b01e6801c0394200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402197023 1250 402195773 402195821
    0x13020a0305330703020c0c0415090b0a05031203090a17040303180605040b0f160b01030b01080c0a050f0105090a0e0105040c0302180402031008030a0210050915010b090d080c01 77
    0x281489507100d80c0e600c840310780c040c00540b100b441303a006040c9002c001c20031a4041e101160008041c0c41940003070b1095541504e0003001120701e81e007c1d040710700d00c0a0f51103803501800c00000caa1502c0e840d000300b500c024400400300d035000f0403c02401d41440d030032aa4410f51000401000c3c60300341c0c010710090f0001900d91800300c00182e0903206a5003100c05070344075103181a02c0c262880502d5000b0b003040030360b4001c0138410913202442c66045000d90328400c040406581d811071801c25000641a044010179a0200d0803500e110b88030b84885405440080710a0743d140c01c02d5000485080c49003101d03a507080400c1150000d04080c40101180c161802200c05100303422845204504074060a403448a0014403502c1c0c0d558030f41004d600a41e0042840c0240030030395504c0d8091580395a20011380c09005038005200c0c1213012280d885001d07000043c0d80b0140070300315106180503c8048c018000c0302404540040d004c1c4d09982c4810800e01110350150b461a29424403c0143c2e0007410341c1540d10303901900440800d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402198273 1250 402197023 402197083
    0x1201030209040f080c0a0204060e060a0501180b0d09060608120d02030a0605120c0406320a0b0f031009060b0a0806040209130605180403170703021308060a0b0a05010c0b13020a0305 79
    0x2310301c6107401030338201c821840d00c0c00454100004406140c03600d4103251002c00c8801241d00140840304400d1408904203001c0c1c900071041f2440c03948007290641041d440306110750b0320102118100d10022001585075181ca0300310740000e01040e8002940000442d100d00c0e003d00d00480c0548400c841100c04104099881041c160380c0b00103040b41d10306020141d03d40301002c101190074402100000f90070b42c0002d6403950f484041c0ca910010038001190004002c02c0780d5600c0d045003010181c0090f5405011380d524149103642240105518202801200400182280c60365415220310070001045501208514200d0000a000a00170540564200c000e20441719020045680c084c990660b210001c0da0080700c400c02100c00080c1c48001016001c000c8546c3c0d211494060601820400c80036201c02d00307081c8104000c8502d860402c0b4007601ca41e400400c03141c1c0e044000c4414a41c0c102203122900c0e50307010708584540c2c8821800a600c24104480401880b0300000e0800d0401c1c41d14101305503000300000c1d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402199523 1250 402198273 402198299
    0xf09011506020a1b0317071403040b12060f06190e09160f0903050102120711010c080a1d010501091d06090d12020c060f16051201030209040f080c0a020406 68
    0x10840981d02680a003c0010a0708038a44c0c0719034004814010401c0d12640c44044c003040060640303502d0400800d0b9601404600c0a4441e40071001d00021485d01c0d10b407000419150141d15000811060600d002440a407200c00070410f0515004107040d55410407055910b8080018040c40b400190140c05240614100340c2100382c021101082542180317203800f030048030044249203004041041c101c0001001800900252801603075102d5500d0301841d014400521400a60301201102d07070412246861443d0010140c0d90404040b880c082078213400c040c0700c0707541026408800101503180400009101c01164403c0012a07840241900ea04210225041e44e03140203603110714051304960020700e0b119001c0d1565003040d4107405005810803c0300c00d10a4242042101d544036a0520030302044107203842d20b0041d5500d1441402e0440c14031000082081811405000c02401284a000820207101b1511401184164055030580c0c0e102c030107007040d544a00e8410000c07401903040800c00300300d07008407000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402200773 1250 402199523 402199529
    0x190224060f040207030212070303050a1b08010e0907080a050105160c0c230d120f030908030a0c0c0804031b0e01050d031202130b1c02030c070602210f090115 69
    0x1c2101a509040c1e01044020742c481e9038202d003544541c2e0300004100310700902a0207003d000751000606031424070141011307240c00008400c1031007100000141c0d5184c00102e8503041d503074040c0c0c052640e0340c0d900440516020098104801d00c1c4203010b200001c001c015001a84601b00c0081c001381188c1c4204000d54030b00204000c010300d4150500ac3c01d00000700d960181d2540b036108141c1440503248800b0104a038083e2400060b02c03040680c00c0c001d45100c0e00182c9c0c4404d104164a402c1050007030944074030b40d035404064504080161075000412080d031088000b120116040480345940d11355030320306444403070704140c44481c030f080c5030f9040010100700d080c10803412501d02401c120303049075580d0350444a451144100042c8540d0034008a00000f581c030780040003914804121990703901101005110b4907a045406019180c01001040644080c4000f07855006512007405a00d540100e486181c01e2041320168080b04644030040105030f940302000540203210110082110700c4510404d103040c1120741c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402202023 1250 402200773 402200779
    0x121e02030103050d02030c07150201060e0901020d0c14090d0f020907051c0c090311220c020111160b09010915020304060c0306060e060d06120515130c0501030c030219022406 76
    0xd8230400a680c200d885c1640c1d41007052000080d000d0700c0f0140005510300c00e0310581420b030340c042103240c001890751040206c95822420005810320300c1841c1a07101c2e1207146440b078000d840c1c4c3c8040ca4100012000a001e2030340d80141020118941000d0003000b0350410a180c0030750030040510749141c04080e109841d1b0b041c07055943c2140441c115102c82405001b900702954000c400d5140604564000d116015180c22410902064041d6014002425202c508035000c60319070040200075000e03d5200e400d030000607070021212003255103004a241c01400c540101400c0c1c01000507030403a108415600171403059104001c100800360031000700300c08880d10382c055a80801c0c800501c001940c509580a8940310050003400b1801ca611034400440b035240307002c400c607119400704c516804410310750700340c40e40d114401814400240d51a5100c0c003400c080b403807051b1703410b159840318004a400d121340c04840ca80c007000085020350304802c0400940d10a0300019411004628003044c10200c1001007842c0d0007a0001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402203273 1250 402202023 402202033
    0x203091c15050606161b0e060a06081305060103120809060702150c070203010906020301030201032904020d02120411100f0806060901030216081e0403080703121e02030103050d02030c 80
    0x904541c000601020300400d40c0000e0911171404180203585240040030710909001210329040200c04000b155250030244810101030208011515641011400c4500c2d51800ea041070700c0b510040380c06004501c20240c050300481001106010300904003d06003803140c0d030f40e0781e0580c0d107041d5800d80b03c0006540c1758005801544000104011154402c0d13000040700303418520740070b0198002404c5500c181021501c0d290048010010b541c7c051241c448100c0c0707a6800e00c16042c3c04940d10603080e03034003086030900ca02e034003145034002020701d507040e1842c5602071603659486040c1814421103c0180320b481620503401000070074200c901c01c285030b404001050f19001c4c05516004104169034024a11f1a810075600b80010020300011101d81d030481406001d440d50f07140e0b080d45880c1d07040328141761402c04200f010081000001d42e06004c44820301d405183c03040c46801c8221054010f40030426003000c841c1c02003100785128000c55070042d4104c0b441207046460040110074187d80780e02600f0040c84883d00300c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402204523 1250 402203273 402203303
    0xa0c051c020907020c04020706061701060302130f0f09061a01110c01110f01050709090b030316080904060504060b0a090f080307080d0e030f190905090a09030504150203091c 76
    0x400ba21254004400780142e610400c45240480c0c100c1e0409102602c5482d1240d82c10448002c0d040c80e0000c860840070000d1040c5400d580201d074160590200c0c205149580f4041070818456950000100400b0384c41c00784000101070402c90040c003c540c424148160341035000c0541580500b4403c03454203019030182400007001d1005584241b010a1240c00c54000c3d1540c9010282d028410300d07200f1172560b200c0e09072442c1050b1084007102e1250107100d000740d1080043c5491040040011420175500c462800c1d65002c0c0c08022602901c5c2d50ba00a9030464107150700070484080180286c8100d2400365210b0300886e640300d40d03004c21150240b1500a03150810400391020034504001070000e0030030060082942a01c0412051650f0f000c80702c07006d085200880d64a40700181c3c2d09000b0001041c82c035090748264241000146042400382416040c0c9940e01c8041040500420569005102c043c161040c02075103000065283c0d804154464417880701d03100094002800e8800003100150444031180321040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402205773 1250 402204523 402204529
    0x303150324090602040e01030317150906040b1002011d030412060905250504050f0f01060f0c0203101d0a0812040c0503061008060a0603030e040207080f03090a0c051c02 74
    0x100140c1d50104035848240c4803002c103805000038030003040c070001501103030f41c03540c20000e1a40801e0038800070203250349024040c1c05180c205081000750350882e241c140540b20940028000c01145130b40d660040b01c55900c1c1c54219406500800380343c480300d441880005585685240c5074803c900910036210203d8400b0404a00f5640c0119a00c500c50b40468a42641d08080a641d400810031a40fa241f40d040b1014030650030f01740905a0052101c1c02e050f06141418010f034140c10005004030b10030072400700d400100709445050709100c0e10303402500350340740b0641d0b2150580141c210002d00d420307840050700b0320154540000400201c440e4100d11228103004000001450500d009070060380e00040350007010800390f07000c4c01202d005a02d045401c03064039141c2042c0710b0070180002c04500006291070010804650858038100b141c4400711801a6030304030914151302c030350003034031070300c8070000b8010082228140700006e01720080e074012101a509556a03104000c040280a00440c0007603201c0b000810040c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402207023 1250 402205773 402205823
    0x70219060c21050a0f09021c022106270a0f0c1d0f0a0c0e040207140d0207090f0b010e060c0a0602130e01080d2007081903031503 57
    0x1c03035149480545840701e04414100d0451140c1c1c1ca80e41d042d42d64051006042851058501d82c81c641c00d0240003491342500001c1c0300611455000041d4543c1007030740e4013156554003101d1490f503900b4441240f608019400d0503542c034411290802c106004000c1003181040405021003104044002009084041e07035804802c0c4410500854034002611030100c2d1280f80d0700349110008034505014201031030b01e4000c3e140d9010b00134110707003521803400506540c019846591070045200655000d0398691552920130f149100c2c1010011150148a112010041d03000c1200021034207940024051154203007101c20440394030304542070103d036001004460701d042450180490314454420394240103100d03103400742a6402044085801c3d500d800040c0940c5049034030507800b410b039007070061a211082d00030182803007044510292040d500200c0c2c021240c0300801480c0003910b5081c00792a00e0314030f2010131402c1c0842190040b000308e4100f00e061380845941641c103e040341e400800b0006040d009a9480742c00c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402208273 1250 402207023 402207041
    0x6010f03080a12061503050406050f190b0303120403020a05061609062a08131d040f1e08040303080c032403070e090706081e01051915030c020607021906 67
    0x6840701e20000f0080c107000d185080e010140c6e00c012500d41f615107000c504070341008050444c0d9031480c1c001e2060003001e43c0e104061000840b4070000794050040300083c50360240c424108000c00c4c4260811042603408900d48428910410455405031610156040310780400950310000540004040026911490040c00d401856131444003403041000c0700d900c42000d07008420b0720703000400621583c000010320105001031003e0f400171481c3d05240b010541800102800142c646c5595003c0c51050010710503980e040b00103025007103440901e03e8503113000c280c1c0091009501141c02c5200245004d880b840899201e074101103500880c16040c40040d0701c08003e00500c0540522401801040d02e240600505003d03221a100411034907190140c0140307040001000c0e100a100340d042040000000c1812540c1035500483d401c080200600c524954050003075070204502c0d410080c0d501e80d55076050f80c00f10010a003141e0a603256960b0382c040681c1d40780c02c0500e01502c04d441004000010810650008030a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402209523 1250 402208273 402208307
    0x60901140d0f1509020a050a03030203090d02040b0303040e0a06090605060d0903020712050705040605031603060203060402121501110609031804090f03020f0c0118030f1110030e06010f03080a 84
    0x42e141e065140e1059440c115949400c0841d5582250310640c903203601c0910080100b00c81c21030380981140e80003503ea004120095008a105442100c1155030302c0e0408420890301604070394440390340d1280b2081000301911690384041c50800301107154026401608103484c0054541d40c5070124203a0750310000d203c0b411081e01140540742c404141b0300000148003000c54000d600400b801070526080108881041c0d00091203644800c080f5024000580004412243c200c2c10058803950380e140032802034440d036000e80103426081000c1212225140460640d40002a1b8502a278210308040d02c5a948006640100a5074400d2081c4084203690b4080f0103040746015001080b00c030281d50f039400d030320041403070120096013013802c44495100082200805051007482c1641c9622911004050074200c1400f0140c41416000c5080c170074491010394065050302c018007201c40190082c2401401800b48040480241c0102d0000058440f04865840300b50390300007802c0b514020703a000c0280c40321480e4100c0342c01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402210773 1250 402209523 402209543
    0x40e010b04060807111005090703030215010f23152d03150109030b01030c1a09010c020d03170103081305060c0c09040f2109052202030a020d0612030206060901140d 72
    0xd20009940600c5000d182310301c0060a0031811880c01900b01400c03164041454148100100301000a0390540300c222201c5101d140e00304404011040c154005003800e00e40c000032085242240c040c205c400600501c44910803801580f1001e284200030790040010b14280d5034000c0c40420722101e4034820303840c020001410124841c96403640c450341d528200741d0045d100d02901c00300400991130f01c1c4154204c04200c0c68071107850302d0358101c0007a14103415200040d01031101c56030801c080500070850503402c5c2d00c0c0f0340100490382d81c0d00d103001d0030282c0c0000c0d401102d0004101000946003040c0d4166402120b03500090b2081e0780046090181041c40100141c40781440b0001080100e00701d100050b201700d00719206880511305d0030340041d041048070f03030010307000b001d03100c0b032411940003520341d82c103031100d00407001503541d480f84446c25001e0b00601c844c41c80824508400040c07640ca01d6406045003d01c26000d0b241142d403a603013003000c42030b0701748600c014400e410460300000e45072420320b4881440c49202000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402212023 1250 402210773 402210793
    0xe0303040510020c0709092a03030c120302120a0c030605010914120111070b0915010302010c0320030c1005060d05060a0507201b270a060911040e010b0406080711 71
    0x780c8024201c10748200b840c801c5e030800002c488d14661200c4d51150054040c8003072441e6001007414400000140450100d03224ce011507620980480b003141c1400d2041140c1401e02d1b100f038100a11072450064042880e0460004055000700501e40440b0140c1d66a2030441e20b0010134044241100340d0408040d568549641020451102c050902607000e02da08464038504204002d14041110000441340442030004100607a800310164030310350383c1460401c0c09204010305414015450548641369400301207010708044000040c015601c50401000384400c0c0c0314a81130014000800001a105400c443c0018140646e5074200707542041d428580001c0d42441943ea400c401d202d418111040e80c0c200b584960740c4d0172582d00b001d20221800b150fa04648042601003036214004400342c0802e584641c1e40000d0382003c09030b00c40030051000c4001808075071103c41100080f50b0003402807410981d0b000c1c002113800000d4005031016500561140d00007501e84400540d0170841c0300c0741034401031042102c07030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402213273 1250 402212023 402212039
    0x90906020f160b070518131103010b0d06050a0f03120e130c080906060627090f090d0216123e040b0d08090a030b09060402040e0303040510020c07 64
    0x10019001e0004107024203100c6803503c0340001c50098000002c00000744491054000f412081c0000c240b81100c15200030360503020f040e0003038400d4a000d5108807002000000711003145900a06201c140c06a0404c0311940f40d40421108180038000c050a01200350401d00002e0350010100d0202500c80c04c12100720700b51540010394460a11b014203450701d072a114886891a00030407020340150300100034040501d07107100031421501507140e280340b948440c05040c83c4844035101074210341c114007070540c9981d441c004000c0040354005072140044e900c6980d0025502c1d504c04180c2070300d4020760400401c202d41c50603204031603105460b00180c0d449451a00070103401e0b15002c20b40b44c8055420b43c1503038010f842d030b10000742d84c074012521203901450406005580e9035032508a4803c1132580b00000b1511803207910085880441c0305e4200500010000061085d0041d0014803180b1940c82260240306039a05088070035128041603078010800d50140d40840c141524a4001e455007184100485040540d56641 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402214523 1250 402213273 402213277
    0x513020123070602040603051e0f1012060c0906110a03081017060907090b09160507140c03071d24060403030302070b150102060a020715060308090a1e090906020f 71
    0x4100c51844d800941008182e8250080c01d074414680001d285041401c4c0d000c0e40b207034030b400411403880c03203000200207080800c174242080302801c1a1800c0d40c9140c4042d00d17051000381581c15054001c540352800000d6128070401903c04411500700c0600502003160b6001da540c2c440c0680001c82030025a280030582b4841d6421002462407071074010f1080c0d00f4100c20752400c0010b02c0d0440703084241816140c90907500c401d201d498202415003107441180c028001e0403265405000c00c010300302ca520080c107941010001501c2a0b0704d07007088082d84d0744d096844c41c6500d51b45170031a040c044c1c0b455000700040c00e4280c840d500101060b031505002407520000300c0c002005540507800c200d000c83d5010400300c0c10300000415140c2e01c00d0506078105005c610960000c1c0d600c49000342034041c4180c0003c1c0e039204101c803200700c0c6800d2641a071005e009040c0c0b2440d2040d01d64001c16403a50003036082400002e0305080c000d0f03000e42c20039910701e1101c420034140a01135010340011030703007a15055020004d030044a210b80e40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402215773 1250 402214523 402214537
    0xc090405011d010b010f120605041104080c040b0a091e150e060f01171b040905090f0109031e02210c190b010b0927190513020123 57
    0x42030354485641c0c0b04032060010300118560f141059120303140c0d0700000c000810724004d00b003020740d545200070440c028202903001140c01c5820400002c0580d05440041c0003910201000e580301d5002c03501c203001c2101e200b0440c842c1e00c03841ca11310410035191107503c44c04140400c0301400184620300400c580c165261440304601180c98031800b081103a00039000070340c012008640c502404804100001c0c41c80d119a00014070008400d00440c048150495000c1d040b85184054546c40d05e941c2c1c105100141011215024103004109101841e040c040c856004650f41c10340f0f50010b40101606e000c0400310a54402c281503210b001d11407184c0c0303100364040062040d441d852007951403401a9485082400d0700c000301c1c0701e03004501c00e1000000c510030b1000381921640c1000645855001c0d00180c80c3c510388031079000c5028079441951100340745051103141325800b4801c400e40341d410b80009090899400325215010307100e601c2c0b01140150700c01d608644540c1d0020030b404000708413801403500290301581d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402217023 1250 402215773 402215783
    0x7110a08211902032a0405090604091a13080c0a110105031501050703090312090e0c070507031403190e04050a0501180b2803050115060f050702030c0904 67
    0x700c0c19804030071030340104031401d00c11030109030094103007440081a140c07801003030000103d0300400054008110011000c03a0f5240b00ca212081140d400c1c81110b03180e40c4035028860041a19500041441c1828054441016481a6003004c03540c6070301d247d101000e2010302510a42d450340038042c0082150384003d007001d1880c1d9005041100d140385048006020825002c2e414003200303000704a080d000c111468035907880d0030300f13050b50760700300a2504880b03601150b000103145000c240c030114085584510b1807800d40b1403070344600115480340e400310502d900030102c0040090303106060604c00598104030300454100c02808607030070310048070142d81800e80c4611020001444881120b0380500e07140c022550002000e0608210355414500350150b0581007941180e25a82c44280e1a111074a8410784401321705184c1e49103888082c00c0e450141401001480183c520b5824044c0700c0c00c490200c01d0280040f00d059445003c40c0401b42e540903111508007410990f418050384111003c1d9803100814944128424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402218273 1250 402217023 402217027
    0x9110f13090804150206072a0f0b0f07030b130b180c0a020c0a140f0102070305071e050a0617041406160f020109050303012306040909030f0201020313020907110a08 72
    0x402000d04c1042226500d4045500c0310091002c1036802c90080303d4103c0c100d40d401101c90006030403002c0e0b034006101c4000c202804090040e41840010010b81d401819015003510080d00c407003c3c1203060f40d0308614102d5000c2e642140004e8401c050742d00c58680250068290500e64408062204071000125451040d000c800120211078035810b00040b101240105e80000d29981400c1d80c05805906045200780106844011508941c2c003c0000309d000b03660000031102e0094480003001e411ba50701c110300c0b021014840802049514202c0200c05c1540d443e59900c4c054a02c0300300c0c0c243e004040290066915018400303090ba14080f05010312841001e0a02441103070008082004142c2c4490342201c178116490290f000000500102c100c0e4110b5150003802540c00003106000c444a01c0406003c5a10040001c1d000881c038060f80c201d1100c0b2070080e2182c4400b445d80d080e05038241c3c4000c4807030701c607902205100f4200500c1d00544054110f046840c14544420a03840c0103468814944026202c01c000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402219523 1250 402218273 402218279
    0x111090306010b16030e03150721020c030910050c0d0806120109150e010b1e091602060106050f0f0a08010311060901121d150103050c0409110f13090804 67
    0x304014950042c145021034078a0051458100001420941801410000d0360302041d8440d81d4100b001d0001d4040604158955040005001c0d141d0f001594545424600803021030280818510036030740380350041d801461601012a08000542201c16102c0041c05818405e40308501c408002d1111031909640380e6400b1401d04000f0800c215407201405c80c0d040e07040600400020785c502440078410446030601152411400103000c0c09030400948641c2c000f040d03017140c802d29500c05145840d004409a40342a0303a61180f035441b07181040105040c4001d89d02030401003241c14410070040c42041c1c95101080e04098400f1004403040d440080680c001070358620061060020711400c0042e10082107a10f60315200360100040c00288170070041c02c840030341d40c044030705070107000c0c003200c0e00000c498030182c80061050714824503002030203000640305441010005001c41c1010320070340c3c0b41180c004443e2207010b40c10b00100101500016a9250007900c60203d6030b01c15101809660089482010026100c1d41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402220773 1250 402219523 402219529
    0x50c06060d0c08071d1303051c1d07090b030105010f060503040c1a130801022118031207110115050d051c0207030b0f1323060f07020c0f0901090c020a05011109 70
    0x1005030220b000049500242c20020380c02408403274003510a070a19500c0049011300e010000c010340001c0c00203400100c8204032080b0030114030740040d20080304041045502402c14103080368000d000300040d0503001c0d0b00600c0750900507005140d0092003809491501500d444e00800d00a24044a01091060200c1c5840a0382243e415640203444a00001c504007005410052042c80421011000c8030780b4070000701b160503d121040d045481d40190450307594015172100f80b005500c0850382200054050bd03070789415440180120401686401401509203042c5000c000c0d0303030403896408072182d04c1140e8039034140d000401041807070a4003640140415a1641c2411886c803103004100d584010700082c100402c0d0f000306d04004078141c1c3c000e0103070030f84600e02c81400101018200035000091240904005664200c054070030b204201c1c0e03a00b0b44002d12851018401010b03141300085a0290300d0200501401d0950392211103107201074030480d40d552140d41c4522f0b08649480c20301400b61480050f15141d942 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402222023 1250 402220773 402220829
    0x519020f150d091401061412030a09030305090f0a0620011104091d1603020f030a020d03030b01030908220e070c020d0c0509160f050c06060d0c0807 65
    0x220181d5080000c0c030150201021144200740303050401d695524407441c107000ca05005619900070b513100810220703450319004580808112801407103480000e40030390344003030040f003030b502480d40c0c40c1c64800c180ea0440c0d8060b10b098011544041c0c0004400350212030913550f0701d8204008098545890462200418621150026481c0b0421080c0c0c1001101c50700915040203c070100c1e003101000090450301810307041c1100f4440002a00c0610aa001540007015400e0340703082200d2084404910702c01c3c20a0a160325462403040182d444043c4402c0200803170302a801c594084c030414980002e5540346076442c50070a40080a090741b170031607076080c02050010f52642c220003510060301d1843c0140307131214006003500d07400d86c002801400703958005420043c0500d16180500b030000c00c082c00c50302d0000e0101c23100c050300c014640001000365006101050184040b03418031066100a0306030b5950720310a00201c4050040101d44012111100050b855030510222002d41286682d0702c45c0a804004405855 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402223273 1250 402222023 402222049
    0x1905060903070f12020703170910080f0f04050c030709050f06010e030601030311120a05090114040f0b250c0e0601020c09010e070c02040e01020c010f0218010507050a051902 76
    0x1c0d8020045103010858224101407040d5101c121184500b80204080b400e000c91944000c2c49552440d00038a01074000c50043c100401d810746d01010307010980d000413035441c07a06641e4030126101c46000300704580241c900f080d500c5800f270001c035030202100307802091422807142c0c890308525540304284041e0301d454000c8250051000d2800c03440003000000000d454500c188802014401c03c0b00103184108014004a920048000300080e22000020005001c0b40d11021a050004694001c280d10b00d0140300d05a4060b140e032800058101420007a0302c541c964490419001540126502c00d001c1084482600f103032a48a84802240c0e540b071b21030300c48040140a4492410b41d080684d0603669925004040e0b411071f0000d0750803241a8585410940b500d0f07000d400060b40050810729001c8582c44150001c02202203400002c1000c181030b034501100303d0058040300360742c5103070140071101603600c07800107070618600901c01d55040da00e00d60365403454118250785100e111610380c000c0e00f082d840d0002c004002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402224523 1250 402223273 402223291
    0xa030501080a05060106121401060c021002010507140912010612051006081005070e0d050303090f03043804080105011703090906010315030510050f070504030c05040903030e190506 79
    0x3003a030140e6a0381307440f210140240c070f040182045030900d8080154014102a02c219502c01166584601000b0008108404280e002d010074040c0d60f51024414840d0502c900b0a66a82415100d2880300c0703028103a0105190030740c003000401844080880070b2060800a10545490141241e160700d026414a82c010003101d558602d0032070308000d20840880d2035410005180720010349a900c03560203460035030316480c0054006011400500c01c0241c00001580240504412105849488a11a540ca120354001c01161110010001c001c2d042d400c29804962250241c90340e282c9008408540003d0300268840c3d03489070344031001009440c8150700c00c000c0d9507401350007552809030071601003a20154050b0506041543c4c8180d200032001d40200800301075580001a92041c842c01c52b81d134030140c0415075184038400745032008694918003030b00480e000c595001701008299441d03d42000010705800c00140c0615489a07104c3c12051000e00940c0b02c5025950802070584546040107481d000c2c0080038108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402225773 1250 402224523 402224533
    0x130e19111b03030c03011802040308070f0b240904241a040605011709011107030e040c09030b01090c030213030b1608060f0607050102070210020f06100b09190f08030a03050108 77
    0x40390110790000c486c10744000103400c462103140d00f0300502c000d1066500140c6140c80c04200074041101001c204d29505004e805050f066894464070001105041520100d860900c081806814181f000d5003907401406401602c103142081000e15050031220700401740c981d580c49914138440386041d0841c1a00d21410746007000600c0c10500064185004e601889404c00858800126401c00c00d4220081c015920f04245407100013518000d4101424ad42c0511b1080742010310b448a854480c00c0350008a0f60030428185003a442d100001c4006c15807501030f03a0400d038080008029801d011640c80001718881d110513521864940c10704156044a400d640081003451001e0000c15901c02800c04410801103e031289c0d01c0f045860214028492078800035044401c915015103041c2d0042030b115a860a0001941d0450ba540c00b080f45002c13a6a018a0008400070f04c20854142006185114a4103a84180c030401c540ca90003050321101c0190312007000c96000284200d1801d40c5030040c00c0c010891080246 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402227023 1250 402225773 402225781
    0x90d05012301150806100c0204060302130902030c0612040f030c12090330050a090e09010501031203050c0403060c0e03150603120702030c0d0314030103060603031103130e19111b0303 80
    0x3501100450500c6c104001195021a0030b664603903018000550f8001c00362000140381c01090fa0107400911020b91180c0191942e140780b50034104100d0741401c840019200e16a43d50303995201b003034803011006170100005000300c5800a03d000201c005544840d40700c40c181507146142004a5903c64401c130b60031491040d14049070384910481134641c490329410069100c0c14041c4084841c0d100b507900c400340c4c0000c08001c2c00280c0c0010341c49a81039a0081c4241121b1501d890400d0301a50f01c152001d40c03d00c0d00030402003001c10360903801800060002c2c071704801c1c1000c1e540006407909141d01d4240801000315820710800740740801019100181c860341a40c24402d16400184d11240414060f50190716070240c6042018424a02d070541d04e40d47e030710b141303440356141c1c02c264004041a0001714013049946000d1886850b0000c1503500381d510030b00703590300150b04202c0c0f01440d06c140605140ca560b80d1000d07040702c140096001c0c09804503070380301001c1e0322030799015650380c9110304401c09100e0981082080c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402228273 1250 402227023 402227029
    0x30201020304060b0d12050c0c09150111070b03010521010e010f0c020c130209040b1002010e0705060f030a0c120903084002060f03090d17070203090d05012301150806 73
    0x51601b5007050400ba80ca41d55507007004e40c2424078817820613a01900c08020448400342d01c0c5000702c0c90764001c3e41c940d40982603a402d101e41d50784281c0144030f0040002d100400c924545607a9442451381100c200d24068404150500c0c00d40350301320501602a516009005daa40007a44070303c40c1324020364401410059042d0000c104406800300d0108045900011010b0540d181c903080801c0040000d49940035506903018028000e1a088803e1411409034280c0010540b4100003560984c010702001c561840d2200c650030380c0100140100c03a800d210703648080b06901d26181c414a075525020780c45180643c0341c016144000742604400f60040c0400341c0c809444508894800c45010120440b8010751804071800010498010380c440003420140000400a02a001180b06000c05009403158200c05c00c0c00a0101e90070b400885101f40140e00c1444410880d251041c0c0013801240100000110480c0d0350302081c0410b10fa0387c02401e02890b07031900402c089056191000c051038800e1400c07441c00c0c01c0078400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402229523 1250 402228273 402228293
    0x304050f0d0f02090709031502031e0411120705011205070c12091208040602100614040207020f1002031c140711011e06050a0608010b030c030c070b0103030201020304060b0d 76
    0x1a8501494809440004004040b1990701c0360360303001012420580782100000f0a95401c40c0000c44003104600319030b28281045000b41c0303014050045000704103106d142c2e150150684001e0058075512080940680c4e251610350800c000e0ba59020041c19119040c10000342c104400310006a804900e4501008000d41d8081c4001500b0f59010060111044207074404842000e0580c00ca1103828440204a404011a40c1c0041c41192465025204001000000c45007160058414030510303d441d050540c0852800758010042c02d44001c1c440c0c501583c07628041081c1c1c25007180e411001d6400020030070480050781720070403211119004244042c0745507001d03240c80040040c00c000140401e0103181c0058a0003900050000702d81c41d58041c85034104180c0e007001804443c07040781d000b0303e002407002c2016803140200714140c0d85031007601451502e4000304081c240c1c0c001410451401170501110000841e0703240018021800703580050307283c0c1400d092100032143c0b5607030024482c82d008140840010b4003128 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402230773 1250 402229523 402229549
    0x130b0a090605091c050a05010519060b0702030d0e01030e1b0901240309150203041208101a0a0207030f0f0c0b070b0604110d0606050c010c091a0d15030f1103030405 72
    0x341e904190101885c000345485001c0000800c19400c00c400c00c481c101000740340f00b4422041040c1408000d5640b17242c200c4038800da00010390503410400b400c1c440705019203103e540c000e1045c9000104003001d41d8072941422031010440c2c8010b0070107060003106180c900701c100e01608000e070719814060300651a0b0843c8000c1c20124405042e00c034002d038820300440855035000013807910350079582d900c0e151412140802030212110080389142010860300008180a1000c1e10840d03400e00c0080481001c403000f240d0044004502148251003000c00010000d8001d4880e4510451058070f42503100c0c50b00f4400d68140d41c06c001c00140307007405010081207400c0c2d1030640016080d2000142e0300e5810011102782d1190380f8100081030f040040c00900d469000700285441d0420500800006500860454822000e0701c11043c9542a034050081c1d44103d8500500c00005103000004034104000d9481c10103c60940c0155050000c04160300c0901200710000e1007511001c802852915040000149071141c1c9a2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402232023 1250 402230773 402230809
    0x30d1e0c090911040506070b0a0621020d140d0801081b010804030807090503030f120a05100b0d0905011505040e070501090909081303050d0f020c090a090503130b0a09060509 76
    0x11140580380f0803030700721409000064001640c504250900340340621043c2c464008562500b5000030b0140e00303d42d414074a42c2400c00724440c00903030980030010700e6041c94038240d4981500d404440b014060802c0100c1303444040d5213801d0007562419404a0800b04500e4a520440a6990b15000c1c0750783d116210940c441d501d41040100c03a111040304440002844c0c0007582c00d4400000d901001e0711094020b81100c01060407900855a0380f000140140c030010384060030182c1c0e01d807105102030800c400160818900c03003107000504030340f50703210b06081d5202c518100d800801e040e1401c0c07156007801c1c00b8908003000e0480042460a2070000002d010704003e102c1c140d031296490907502c081010400860702000440704a21001d96203a00702540c40e910f5401540f0080388500c0c1a1804450020890b9054000000c100440c103030703503851b450405058001000c07506070000701709101180c481031540c0c20141c80c00008283d2121108600a8180201500201709105e03040c042031542c0d030345003803183d02864021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402233273 1250 402232023 402232031
    0x405030a080a180602131211010c24090209010503160b1c1104090605030a0b1609150807020d1103040b09040207080d0209030c010c02100e0a08030d1e0c0909 69
    0x1842c050041180340b503210007442c906a120b1003070001d590007409a0b100004c1c50355826a40c5c5400800341240c0c1c40390010400609407201d034880303600031621107250030f000b600740d41454842e216640800700d803000c1c900020140e03100220b006500344002d5507805460164002e04c0c4007407200d4146250800b40c0e12404283e078400144291496107580b044499018031040103006548124840d0b0020b60000d0007180f07605272511200041903e0001003090f060740e0080560706468076030f11500b050302d216103400039003806099107002419450aa90204207103041da624148a4103180740002d0504030318119a1081010000e00c250f200ac401204440440300302035242644e507036080000c20041d00400402402a0901103103007807001a458000b00502c40c0c0c12003d03103100c403107503800545049100a902039041004802d4401c0400d00901d01a100b4410041c0010340c10342d5503e92480c42c40d8880030b9548070080e11034500030000000c201c05507003100d5107030360b0600c01c81110780b0f07004000100d107103e034100ca1515 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402234523 1250 402233273 402233281
    0x160806100813020307080a0507090c0f050a050703170a0903021c0f0846140c090a0801051e0f060105120a060509130209060405040c090b0604080d0f02060106080405030a08 75
    0x81086405d005000402c1030b01d0320710600303040460712401c1c0c0d4800c1010550405609013001886008000d1a1074415151942003105840f82100d498105050480c00d01c500d070f818142c0806221485a4400d00c00c000020500305035500d002410042d520b80c40b075803100ca0703030300d14501c4068005050841d5000989003408141c0e03100c0c10031406030304403000c1d0300409218492161a4110100380d04d41d9141000548421861400000c26170450365800c0c0c48214202040010071840c00e000d000038202d162005086102c003580394403101c0d0031610b066403049400c50b5000101d41501794000c813213075400362820328681d05034904038001808900c6803072503154041516500003280c0320b2061340a1006020702801c55903491030080c9610b21114000700059110f41e14103000900c040c030b0980605486940d0100c6403024041c6000048006440f0a40c64558082000c0c000030581d020204078440607101070361f41d020001405420080d00300311042c0c1000c02009a081c0810011a400204580d000c05003464082c1a99032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402235773 1250 402234523 402234529
    0x1b120d0623092802030a05070f5418051b0f040801050411180601020a1410020d020d060b0a0804020d0f1a010906090207150203070c0b16080610081302 66
    0x4007003c040f0081030b2010040c008202090740c480c5118416940360300210750781908040e51406011041072072180302c000314403002a044c910f0b00d01c2041c1103000f0554190460440306800010b50f0700101c901c18400010304001240b10741860101440ca40602005242054580e009500940301c48150162100040e6070705250320b40000c60b801042c00c2402009107040c2844e00400e0b541c101085d107440341034a1f076034003d1040c5140c7c1e8403d0085405800400d902541c599030a01290490302e85002c840c007650b40c0300c80c2200428002000c0c0003031100801030b81c500207062804120307041c8e60030012600f80140711440803260080c1c4195001901280e00059a645925200e02180e41440340100004440c00c2c0b68607072020202d10140c180c03401900140951500e510315103049004584001c2c00411091001d004200d0a690046800c14000d2810410840c1c081c1c95100341030f80240d800007200c0c00c0b140c4c0f01400095104840703d0b0000c008881c107404002e43c5050045c00d0940c050413521100760449046c0c02155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402237023 1250 402235773 402235831
    0x1009020903030301050405041a010f061427030106081e07080a051908131203092408040501020c0106120b06040c0914010c0203010e1b0306010602031b120d062309 71
    0xc089140c004104ad2303160081c90944040e14412540494410340101440106a2043e660419220f4040c54042100f0648039103102003c211583d07059542d40e0f90100d41c4540c207101032142a0742c4640307001102e0381d0b40c04d50146005010741c040d44442d005405d803070f000100c000c41c14064200c0d0000d03164210340d102e4149041c0b41c2c4552b808450b41504154000905214100041c21005000f07071642d4602c41c0e503807000f070b05105003540480b50b1040988101c24405030301a00c10260480d003d84001400c10041c02105821102a508203404e0000000e504008008044d11825400305050f24144565003c2400140045001d40100c1c501c00445469000403a441906d0b00d0307900c25002002805600c440f41c540ca5220340114101c03820800c1c2000b5007030700c03e05000442904070742c59580150b144c9403c013000c04e400003100d640001d0703850207490349e008141c0c0703050000b03015028015400016043d03d88842c61031803140c841056003803210103680e4036100703a0358059015446540400f620410703c00003000d4003158 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402238273 1250 402237023 402237053
    0x11101020a141803160e090a02010e01050a020a021801050909120d0e1c050c0c0406140904030903080309031809040c0b0903010207020a090603020108062e0e090f100902090303030105040504 83
    0x44c440d81806210030f8520000c0c000442d1b100140c004110780744d920846854280750b11000e804114544085c1e20780754885d40c000c0c4655101032040d20080007495000600410114500d8106810030b00c0051005142200b0200e800500481c0100220107115040360807a009039075800d06100c3d41d034100b90024820034000c0740207464410141c8401442819000f40068002d805643d0403842908420501420030f8450342d010380e0f14007a0000c1c0382210840401010110003001182000b132001c00002c00201c0000c0514003812403c0043c41e01c540003d207040e070001e510000c0780d5200d88480d000f0700c8045000c1d0f0442500b6900d0000c0055034401c07100001c240079100e405c50081d0441c8c855080010b0000c1c0d90303402403095034403da90b8914940c0f079510411002c410715908414001d101160500e24441c240f007513a01c0042182d040c084001c40180e00056120401183c1001e5002c01c0c4d0700410003d490441d000e42e0141031125803c5042ca048540407961701c4c081409010701442c0d50b00080340038000468000c3c200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402239523 1250 402238273 402238279
    0x1113021b01060504020f0306090a0204030f0803060310060e04120302090607031d01030225150504060c0201060b0415050c07050a0b0a0201061a031501030b0907030b011101020a1418 79
    0x940d1540310150000303055211124480c40d460208049068a030a0003107588103066040c4003820754490104014100b000504585c069a5082100000059401948911840c014039200d0349a01c0c18009040c24414003003003c0118524002041c400000d04020303050304540c0000b401992400c000000b90005e00c00c4100303283c2c0c042d40118514040540c41803800d0210011901648407000e2060015000c0e4050782400750a101c04200000c0031402d003112615401e1800380300091341884140c03400070119901510107484641c1c03903031280c45040c0d40900800b001442c0c51000145030504d041c2d84d010b102d8401c07410110070000009000c090041c0b04002250285ca130040070b0040c44ea9842012829a40c080e40380f80d03015500340400011500c3c03000303200e4480c6900c03801e540c80c5035a03034041192405811103849903062691318182c801c400d44903000101c1c414035060300c00061000c40e040025050288159940302c1c03076030040101e180050361008090202d0114011104c0d00da8a07150810b046a43e1503085050f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402240773 1250 402239523 402239527
    0x10e06090d021b03120c030d02030106030b090f22020301060b040801240609030b070302070c03051e0c060702040e0709090507060905030d0206040b070e0d050105180607020604111302 80
    0x14004010400304070801c210340850f281d003203900da0040302d41980e1801465058000c000400482c40c02c0b10000c011600035101520b203018402c48c44032040740c20030b0b0415000260b440408107040d013460380714203421120300c500c0e0008515018040c4111100b220030340b0202c01608002c14021520250086409005a041350350307201e03526008914001d042d9003040108503922110100c0c4664544203050742034800381d685003100107003147c56500321550301600030410554200440e00101d00342c3c60111014601c200054280a640ca001c5058003400f8904c1644098100c18904e1081d036880b40211501d00742d059601190709240100e4060402035550310000d86142028070700c4003005408030300002a5129074a844507201d880b4404c0c10398401c04202054003583c80080824041103103d01c404c1d41c08541842c0002c26065030380080f4020800d0f424040390302c0d81d140d105000b006c40ca4030b5400c00c01c0d407400c03000070300003031034402e00095480c800940003416000c44c2d4400070b0b540741c90303122013003125070580c00c2c00395 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402242023 1250 402240773 402240781
    0xb0f120c03090705011e0305070905031902010f3006030f060213060f120b12010f0e1009021309031b110a060207080c0108090f070f090b0301020313060b0102010e06 72
    0x414964021a035031001d901440e880416658055082800003403030721b040c0e48a45e800440d44c01d400070f00014100f4824004055000210f0790b90810402c2d80d00901d07808000f0031421180300151941260f508440e05010400081503005032440295100d014414011404141681c088400007000709800240201c00000303074200510103103400405942da2410703590080260717107080440d80400c40348480f400040b81c40766809440492604015180c5400810000c0d00700c446000f0706007110b0848520065441d00d50744c1021043d4810701000069030b01c603600c140b1501d43d0702d6001070541800c0030340e06041c42d55601c91240038103200f140703040f075541c08143d000058000541400d104000da0380c00e030309101d818503074404a80a44045805400c45407070000034150040d9400055038640e00040000c2024410358200b0200907004102c100000c000d5440906a240c0c00c010740c01094502004070076001c0d038010014002c043c030301d086400c00100d41240307001640c92141300040b4090301d0749a111030340500c6014140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402243273 1250 402242023 402242041
    0x605091c0c06080f070201140a020306030c1009090605030c3111090306090d0203181f050c060c090d0201052101060509011b0b0705091201020c060a1a09010b0f12 71
    0x119010f0f85200c8003013a9140d444040890231303100d8180054840e0407411001c2400200190051a0086000bc090302c070b6071007075100406c0a44035403085903400580c01e03800401006030541b1611002d000c09a000d043d05178101d00100d000c03a070052041c1201e44000c6440303400e2142c0c07110401840001070b9001806050300a02109003141c0010007010312034041d850101d5204440000d007000500312940155041c90101c800d401d524000302440300340c00800f03807034035442c003800040403000c98030400e40c541030348407200142014600b80c030090103404080c804003d109242d40e00c4102c01131751198240b800b545d8030118220062441d0b4610085840c40c11280c1001240850704100a850362102c01e9031015480560302404100c1070b600703031001070900d05900c0003048400340314100402c0c50f444003030000e50805498095041c22070307001410020303c54204da410310005070700074000c10120500c01004100090b030a000010402c440c18465882040000520b0700304101c10101500d049042d1110240d00b00d2510a0748 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402244523 1250 402243273 402243287
    0x3090709020c012a080c0307020307350307022503080d0903020d0315030206031b0d050405070f082d0a030504031103010c0f030504060f090f020108100605091c0c06 72
    0x2290400000000c0560001c0c1e10f040c09103111300b502d0759003d45a480e000d0300066280e0000d0032200071400100100800b260010081150038440e181401e60121890102c488002c0c204c4040c070203046004000340101c0c50b50000d03000304524254031040300c00031224200f020000c00e40e83d01c01440f2510100301c800084a6075031000202d14002e07000e46e40c03450340b02d040c102d044405041100446461000c41480541020383c0a164000b5901d03808041401c0388411f142444c0d00300c0b201c01203e554841c020401001014032580c40108601e0701b0f4044614104980c51b602c50b20b054254699401c1840880c0307020941c05001e020804000a0503502c640340c2500380100300360700038003080e184141813440141041c2014850441e49000c2e6a80d9a414030382d1080048000d020041d20a079641c54503060a4846140c80f0303c00c003000b061103a45d071a0702000c4d16200140620710000c0080c498008080c50410003241c1140403a107441c20125070a1761241c0b4507407c80c4c907940c2510700019040c5001c00300c0105246401c042c0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402245773 1250 402244523 402244541
    0xb031618030b0703240e040215040806180309010e010c112101061401020619020705060109060510021605060a0302040b0406020604031101060305030421051b0a050315070503090709020c01 82
    0x244c00c1c0300107288404224130300500c65034074000c20b001c5090108010301d440c11000e038100c2c2c0700810010407000d01501203c5a60040d8000d000d040d0062070611440282d01c407000d10000e40c080303015501f007608410001e01100e01c82ca00e80384c140180510036104101d04076900d80540400108039116045038203d4000c020303280c1202c0a1050340c42d041c07003c144c2ca8119101402c411405074020145a96050018000d00c0d42c01600c41c16441e800f4080340d800034000f4480340b40038000f905000910a840c203010050040c0f28052680c0c103542014101ea048c1454421190043c1c8006950b11a03440c006210b084000340715a500075071901e90301240100e1903950101c0d070a0b0060f4001e5a8080104400700e81207030032a885884018000d0340204400c002c8114044d507102500b84140d408081441e086407101030810180300191036403050118411003051030140d9407c4040c20040e00140405c900507802070203111406400401030000c04000105006006c02030700015251801081d51104543e1840c6030180522517 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402247023 1250 402245773 402245777
    0xe0a0218030f01060501180e01170a060f050402100e09041e0602070b04020a0b121f08030d06050109091401030213090c060e09010e1501030e010213030c05030f03040b031618030b07 79
    0x70080403040d01070100c054054070039404001c051646002c1102c100ac441d001002c6655004091440000c146644581d08948202000209035860944101700d42401c2c15100784050010146240080340c0782d049406900c280d00c071102c410380251130303940b0040c02d01001c05c00405035800010b00314204070070402010700851003624002d04d440d0f2079a8181c22103014010407002e032410f540000403190403200e691201500400008080d605486a46080c2164442034a9210458860304204440c1d40d014000c1b01c000d203a151005c00c0000c010340d0741482c1050040c40040d106014490340c140c1e00c001c00c1e030301c0001141da0003580b1881d61555444050580f01071000894400d0064a000040c42d00d44100404c0c41a141142e900f400d03a0080c40c010340040c01c4902418500f59800e004d13000341c00743e4001e00c00002d1400f0702c0c41615568a407804161400c11800c0e58502c0582091000700300ca080020103481e00861201116510304d00f1220f01102d202281807913041c00014a0540003051040c00c1d64640d008000716 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402248273 1250 402247023 402247037
    0x1c02040f0902032e050409050d080a0219081e04050a11100e0108090a0624050604060c0206210c03040203060f011802250507050109080105010e0a0218030f01060501 72
    0x141207004102e000442d104510480c449612003e03050381c040c0303441c2c4110110514202c465886030040b03001c4621340c0400f19800d41c440c100c17141205400800547e80303d002051700394601130f5002002d40441e601d078180034051180780300100d081031206100c08008191000c15802403840c00b401d0041c0e4910104c0800d50b015040c0411001603810410400720003854180c131030b50401c0c0c2c052801161540e40040c00c142b4180901f500000014583d400790306007044000704000d523001941079440ca030150003540240d21503507080104100440e040050044481c1c0c046450a8032003904041c44d4204d01c07840d0689a9030901d0139010818640d518130007540c0194025401c8980f580d96211000c0202e000a020b040443c80d940300e00b4000e240d40301d4000300546420001c1c0c190400303c900802c01d02c0700304022000c603a01d0700049001e1002d540d20181c014000e14102c8000d004e0355143c648150144031018002d4805140c000a60f04032030030011302100b00e084c02c0074049515146e00101c1641c0240750324002c003030014280d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402249523 1250 402248273 402248279
    0x60e190c17100c0806100801080c0904020409023006101a0f040b0a0e0405040b0c0c070f1203033e1c061401020721020d0804080714040e150702031c02040f 68
    0x2007007c02d94188c9107207030010704010741c8080400c001013900030400c984c882c0d210401680140c840701c40070201407214501c41155040f0302e5404034003144040740340e8030117a03115408200700104001d40d00821980070748a031241048003100603100070312503100031040d0b640c40082d000641c0e01043c00104094881e950b200da00c489540350410098a0301500c0c09041e58950030007050b1000e004030003e00c0503803030907411100000da44a041c0c2d68030311042c1c0e100503151a040c248420a264145c000c0c04a00604001041404141030501c030040900e041c0d5183c540001103031141d6900c403c000103c920120140312050840e01241d205c1d00c0180c801402000c0481c0c0c0340d078549680700c1d400015400140c501060103007101907070040b094169124007030410f0343e0000c0e540e0192004201c4480c02080600003140190403107508001c0c4507804400404011401285007040c2080c141c0c0c0c000c600c1d00030188048075084440d81b9030001c00c80c9180140042140102e410925100690b2419801481211061411203006680d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402250773 1250 402249523 402249527
    0xa0e0105040b10050d050c040f08030c010516020a14071a0a031406030d05090d02040606080405010e12070206131802040e0a200304060216060e190c17100c080610 71
    0xc03e1500080800d0060001c401c4898803600070661150742201071504069441810307210021b102d50100e0b40d150000511500303104000c1c010f10394041e0300030b840c040c07001400040085d030764145240302410100c05840300104402051220400501c004e100440c4000d1085a030104954410000c240101e841d0040145000c3c3c1318501d40d600c1000001c000d003081c0302030f42400341d2703c95110760941503004426601d80c40041c3d58078800c1c4005400359986604c1c0c0381c0703804d1420508464443e05030141c9540309507084c00b410300d1703000102d400301c560580c0d03d0b80e15119944203000340040c103038020ba141480807030940c00e800182c641c054000c9a48240c800040c0d82c9840d002ca50880358262100c1d28846906980000e69240341401150084d00c0b60740018601242d2042e24480b07142c5000003100e0313160321000da450b05110100304c00d03e8244100c128601703d4181d20794448841801c81d10528680500000501005000134401441d407000850002d001803010458014061841191460f101c1c12048050545140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402252023 1250 402250773 402250789
    0x7020f010c020309040c0c080c010204170a020d0314070606060f020111090303221508010317160308180a0c150f0509060f27011409031507020a020a0e0105040b 70
    0x882942c000c2c524050b440b2003444050701d003c45016090100e0904079100240c0c081c001040303d640e0040c0016103850070700009158154005d00215801e0b0b000d01140f102613522038900811040e030608240c1241404600d4035200c9010b20340010f030905280c0200000d055410802d410400704055000b000403009418002d1118003c180d209070701648148200308540207480e40000310b08407060096401c555489078210403248504a0130703400520204010401c000640e0b1441c54036001445d07d81e401c020003d49003121404203107c1c0034040180c44004910f04550036000111a0100b6009581d030800c850304090254000e14810300c0760709100280e510b0213082c0310b492a546040072580e04c031450000c4e82c81c04c1140782d0b000210500045d1608004110451600d2103400000170301d1190301d000d44001800000d400b5845410045818400400c1030035600c0d60003080c2000b00d0340381d8100c0300c6c500f600c400504a2030081e44202c020b4000168030004659900d094407814100c400c200c405110780e080282c140401c1d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402253273 1250 402252023 402252041
    0x1050a1503020907050f1818010e040b1f030318060216090c090b180a08011112040602040b12040b011a0307080a0f290402070f0212032107020f01 64
    0x4984204103000500d040078100d40c22491514000e803c0c0300c6c40c40c034900180d52143c074480002200c1158801d10030304101502040c16500d200042130158901141d00c07a980c1f8000308000c01114141300003272190312410f0000c2da14200c1580b04581d8903a120b00d4064003120001500d1000306200800c0050700b2440022b07003001010320b204000715020b2500ca10b1602030700d8070900365014001c0c156000306103800e454002e004841028504243d0380c0400300284124520540c00030703641a41030800043c44800310384129100c0010702140611381e9a00e50502c00001c1c01240c00120301d140000803c0c055a20f02d03914002d0050307000319520106a40d80304002122400a03c8030000350b86424000507050a006449455000c4083e560108200e007004030301600f21600b58103032600c08800c080342e00a01075181c43d402868880265000c604c0c1c4122600c2da0030101c080114001d202d20a11580d40100c0715041c02544d2140b82d940380d20131185114160f0307003d011081103d00d04010700c00c1e005111859a014010407802c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402254523 1250 402253273 402253301
    0xd020105190c230a0e100e0d0302150c0304060e01110906130911070210020d020a06180b010312020118020a050d02270f0c09010c020f0114030a0b09100305030d1a0301090309030501050a 81
    0x401f43e200b1060181c4400134510a6082d4020b084115000d00042d80300300b8803500c108040b1680d01c3c0f41c10728000c0d003160317140124400d0b160324280101202414460480b40010003c6074402c1e107030928020103001181080d00510b0240f41003c0c000d503a5404104090000c0b1442240c4030024015618800c03a51552168041c500607800011420007048082e404580c000000c0d01a11034024a5074a0b2904100420780c811100a45012200c2c413820b5420b100e07006d01601d4004003940000b40c1a000520140b8131801031070b114041d4403400e1402c541c0c9030200501e800307a0032882000c0c6281c0f40030905082450460b0401d1084d0408800246c044000b00f08541d102c1605850704100c0340d2041d009e120035580e961800e1814440e21040e24038610703a41d0b0f00554810307411110b01107450040c91041c0030070761202501206481c2c500c10700c20f000080001c416a084504000400200da10360a003201c405480c8902c07945800d54a8101d141003070503444905001038034001c000911007600c4400c0d0300c07000c072a00d1b0782034502c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402255773 1250 402254523 402254537
    0x270b010c050a031805090f07030b0102010b09190e060901090303060506071e050f0a1515180b1c0302062403070603020f0702060301170d020105190c230a0e10 69
    0xb00281c081c0880b000403c4820007050303111350301c44000c988200300c207590002000d0615000c1045082d4540110441240c0a200a12071746403540d000c2040c521014022500161181c400c4106000595112a000010302c4007159031508000c0a6640203140d1070806a00203801c0420100750703410f1980480f80c0340e591240c0242c100400726400c03d0003e01103440c08481074010400140c0300000b04000c0c18007200e0013504084481617540c002e05045590b114092850340341e503842d0070070140c80c40c0e040c2189070707030300030400420f11100c5407000604040c40d041c80030218295003642d4506042d800580c01c1c0c8104000442e2800d2100d0300c42860300d1800c40107000a6042d031258005004c440d04c80d8003d445000c08480741355080003255400a4420340013600240e8408480e1a1003207401c041c10409868a1041c9000800140c18490000c3c099486040500790762242c55402c01e10b001407084a4034585040b8074803009800350554000441d01e5030000c3c040f080000c00c031041815441c030b4180e008080b610940d4071402c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402257023 1250 402255773 402255793
    0x906140403151113090501090b030a080c160603020c0609010e1b03010906020d09170304050c0d0213050a020310090b0f091e1005090705090f01110304270b010c05 71
    0x80240561091120075881d01e40050f11003000000002e428401003030b0040140d800d0a00c1000000c0341d00c164400d40d1500d04040c0d804d6850b44000ca09081081d800c020000d40d200f0b5245003ca29007203c3c0e030321509400e40d8004000484551690151540c4c0d000781c800d81d0201d03150f0700c202354280c581e40c2014014a030454448213a10b0030420465108000d0050008290304441780c0701d4600301d811101200c400c240c1c4481c0780e6401c00c40c0003441c85c003940e1483c0b04182d00314209078840316512101400000d01600c1c8166840c8150360b60f100d81c428002d040c2d42c4007400320b840c040b58010041d40060342e15140340211010040350071121400356041504019210203a00c0200380b0810900140241086d0f501204400c00344990460f1189610702c50182d001840742d1081c902410301c1900840141510304004081c0610b5803640d407500110b000b681005d01c1c040a5104000804034214403032540000300d00d0003c486014462507034204811610340c103841007080b1054495005403aa020b5840303000f40707e50407900b1a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402258273 1250 402257023 402257033
    0x80a0c02121b0106030c031a0f0a05130209092a060d0c051b01050f0f010b090f120d08042307090e01020d0507021605040e071716030c060906140403 65
    0x10b445000100c0301c1a40442d0121102d2900315001a001610b4018000c8001e10901a0002d40c0ca592249460985020303883c080003c0b1010003c094040d045172502c3d4030100303401241c2c2c00451100d06400a14001c0700c0d042400510341d03502e030810342400f08002401008220f400008c11800304e000d00c00381c011340c60806604041d80003003c101c4804414400140604041c040601c05a5044940000000151800c01070f030000d107012130013404c0c282200c0706100180b0801c80f58900340c50f15407500ba1801d001003c601070010309005250030003030130b45114122400c2d0b590356110000740e00a40c001d5680e10209100c1d950355000c42c1e20758028900030380c1d000d10010000c549040d4814220070400100040c281140803c100c425103500340d031410010382c000e5075004190554103520900825044904000b04801c2c10040768503903200d4421003d040055441c00c1e0030b06002401103040841c108a108542540c983c81d040300c0e00c0d0311a00540c0c00144400e03e02048490080341298925403c518446051078a5a919 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402259523 1250 402258273 402258277
    0x40f0b030a14150c04030c0504090c0b0a020a17120109050c12091207030806040e07030507150e0901030c15080708132301051506031006030b032a01080a0c0212 70
    0x42e5000380c0c030407200e44000208503200000d000f000c5606509540d0340c5942403645a03404260003452245103003420301d200090000421307008803a41c070304940341c645181c40c1088e810f01040b480d0242030320b50507205d10326103803401d10f0060509259500c2c0380c4019903264100307482100d004886601d44000104818a84000d54448103030b80010307460200c8076050000d203075002c440c0c0c103e50b0301240400e4030035003442554a0036000b10003007406840c0c0180003a500d142c990b82e41d40c4071a03204800d0342d280d4801028011502c0f45802c10360010340501f0918040d40c0d40c0c41c01c4a0711800c1407044191004030a068144030740c0c4246003150040040c0c0d92100006e4807040c61121303c00075041c00c202e81e4440141c02d040c40d0075210b044640c101c2c581900c00000c00b031528050307000f002c002035107180d442014100304000105030301202c0d16041d9080c501d03000940c0701d8408042403601a45444465103103807586411124101c40d404500100d807000c0e40c07104803a031600c84401c1c003943c00f101070302d80142c0c1120044102036411580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402260773 1250 402259523 402259553
    0x3100b09011a040902130e0f070206041104150e090601050616080d0902040c020606100f020319090f0e0402150f0d0b0f15130f150f030603080f09040f0b030a 69
    0x141c0b0341c1c602a901c0394904200c0e07102460b2280110340200c402c02000d0b2840030041c0e07118408202c482d6451034503020082d21040010002004600c440d004101c040d2280c1c1c0c0101000c14425a41240c0c0c60344900c1c04000200085416803501e00c00c0400209890611100b80d030440480300c00c10814a401c04d54412580b0340000d45e050018030b0b503e420345405030b61140504568000d49401601f01802c01200744450040ca400d90306e024000203183d0b03070f000d0f264004100c03042c0c0080c5640c20902846070741c00c1242d07100c2c040d9203d410100c803005c2010401c0c103030030040f80b80143d00c216400b04260f6004080b0311a280602210704d4201030341032040d00468500ba400c4101d1040004200309a02090200080c855070340d02403c80c3c0c00d031b5501003411803541c13640c2298000070f03003440341c0c1c1003681500d00656540b01500d4030b4106000c00a10304950224603010303803c18005968412803250711105207240700d991540040c4a0389110f941400500650030409200b4a0034110b001b601030a03d0840701e40b03991840e812540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402262023 1250 402260773 402260819
    0x1306140904050c0306120c100c0c0504050103080c060618060405042402040302181501050c010207060c03020c10060806070e0f030a03020a14010b0901180b09090c03100b0901 76
    0x44540315590703446410300c103070000c0b0091900c0703003400010b0103014030301b20a0350011903010161354215a5030310044082106002c2c94448480c0c035240c40c080f030074460355501c2180c20034103250011080001c007030054517883c0c080b007003120580d81c0c0c0c400401c800e00043c2c843c41d4400c003602c00003080003030038641c210301d620a0003046940020030009042d0102d068105001002442e40414280110310f042c084c04034280260031204c0320310b0f040803c0503806080c1c808550701e06005000900ea00e441000303405403a40260402001c1103250001603001d0301943c0a0480703a41c1078020004002d0505001788242001e5440a0b00100817541d22403005a600900081e91594040b40601d000c10040d5010003403d040103120340d000d403000308107514005a810880e0503601040340d0500c4110482e640380c4c101142d04403002c0300007151944080031602002800452061901700702c8e02000c10400440010300000c80000c282c003211041401c81d100d0804072902e0681c0320754480c52035401004000f22150301c12104641903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402263273 1250 402262023 402262027
    0xc0105010503161a0d150b0307031104080c061605070f17010212010b0d020f030a0906110c0a0303090218150108100e04020423100905150d15060f17070803130614 71
    0x100e1b08524103400342da48010002c80d000803c200050350705024180010442001e91424942001c0320503882d2042c1904d441e001d071501040d46e520303100c0c41a520060098000d400e41d40301688403900c640101742070317001e5200903804001c0014948031051003121201c031811540c1c030f60300341d003849200411640882d0300707952295000c1c090402e0f9004088000c42c09020703500000075800425141c030005580c544001054000010f01c0000079414020500c0d802c25541031074002030741403440c80061031002c030b681c0c00d0401c030043c05420800180d08010700c1010420003601c8060b00c5c0c0c2c0c1c0d03201405138081c886000d00750356002010007040c01800c19800c05100319201104006102c40d81b4640c02410410444100901032650003040120b07a11900c543d98200c04001c10690a116081020404c80000004010003216468100e504004059403210001e0900034040108690359820b0480705013240e40e246103842d01a0640005940b9030000c01c03201d9000820b600002002c2ca01001550715000c0c8404656000c601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402264523 1250 402263273 402263291
    0x4020f060d0c03061539060e011a0a140f0604080d0c11150a1b0c060201140f040c0e040c0503010207060903020d03110f1305060c0105010503161a0d 65
    0x2982c054585100780b103950014035140303403050441341c400090b251803041c0300705882e05191001b07600600c6145600b1324103550010090100c041c512107403140754050300c04c3d4500241d02c8030f1101c2c190080d0745e5100c0c1401c801c40603e01a601004900c80302481a42d240d1051100812054140064843d6040c031006000302d040594540510341844070400351200003814039428102002a00d41800244150035141c0300e07052a40c4a898401c54424a1601c41c10700c821002e400f0744001d411800040903690001c0c01d801c4542c2c1d070b40c902074040d180201340041020180c0f03001414016043c2c9500d8811900510158511480c0844d0314490180283c01030f11010000440170659480900007040100e204840001d50084a810001d05102d4442d901404150912000f0000d06031104180e07504054410310a5030764001041c1c1c0c0303000d02c11554ac84150030507001300340301c018440d040d4001030494a0a805803100005000001c8801c01a82e000c0c0315001c00882100c5c503130041001000d41841501d04000154400c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402265773 1250 402264523 402264547
    0x204090f0506040b0a14060d1e0605060f030610050d020a0f0305030a1d0a03060c0c0203060a09020f100c0f030c0f0b04120203040305070b0c0c15030703051302060304020f06 76
    0x1041280039a01c1d580700d1800d00080020003a00726600208031074040140500002d40301c11a210003400c440c1c454000800b4503800d1016140b00c101a10403d9500e00102e1101880c2c00780160108441d4640b0682644440311510b08020500d54410703102c00f00340301e4082d0f003800208070780201c1c0324206a07040034a81d0400306204c1000220400514001c00c02180c4400403000d00a260400c050541b1708600c0b54003407800c5c06034607000c10040c1660b9100c0c101045000f400e500803100b1240e400d501a503d40314540500040f1a080e034020000d0a00a0307a50a506101300b40078000b40e855441403000c0051000740c40034002c1000440750404e007900c00d141222003040503480d0343d0f00c10036242c1803e996401d010405d00040080700035800070280300c0d0703001660030240742d504c4283d1109403030310a84c06070900000d1145019881403098458440d4000c1c003650b904401d1851003e01c0341c0040b07e81401291410001c00c4004d800410318940c0c1542c010302c5070b03246680f55030a004a181441c02d220760055028020114815 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402267023 1250 402265773 402265793
    0x90309120311010f020702091810020a050d1409030d0b0a0e1e01150207090f0608010203100609050904021e0a0305030c0109020301150506070b0c04030503040f05013009020409 77
    0xa8002c0d550020541944240c90342100c80c60f114800803644100310410042c1c80c0ea4546c1e40d40003121080c1d111000c40c981d00d10905124400000d0352005200007083e244254011004d441d07048014081000744a0b1040e4105072401d0083d507183c0307126031051091241c10300c000e400c00ca10350440039050358125665003001e100700d80402e031600900c405040100384103100e4000f14aa00418181441424002c0c01c107001948441050044441568031503018200300300954100400602001000f19900e26000c0c000049a2125000e17450000ea40034030000b03650326195042034015500281030045d83c070700504448001350a950002c64100410f1400080400c60900c05849104603840021950007078500c1054210741039080d02e0325150810240610842c0c4070340f8291050541e200760b00c0c110310703260440c0d098028040c0b039000400c00e1000190108445030801044001c03600d080e00d6401d80841210500001d9000920040d002810340c820800d04017202500080d09203030014000240f2880540c03141e0600c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402268273 1250 402267023 402267059
    0x309031e120c04090e0d0906030e0a0b0906191a0f181f06170c07030219030201200306010f30051e09060106180e0403020c010e01030c08010504090309 66
    0x82c140c0810104114400d900034564801620b50241c810310401c40c40c0074141d908240104030030903a58aa9000b1200700c104034107418960002c0e1103d00d10718001ca08665220021521410380c0120303401c1018602845000d008182c404000102c40c11140d0314040c400928806200d80b0350217003180092031251085503010380e02541e0007001c81c40201180706e891070000c651580c0100104959184c072034080d0b40088004c0c0b50400380c0600c105568060508040707161200014500d4803800c105080d1204140c2c055109148401c0490110030603c080700000c01c0c3e90740800c071182c41c0460b121500342c0c01503502c05d800803c04601c0d0325008045402d424031003c40801007000250110356034a109003d400e9600c04603545001c21170004040c8035150a00001d03031a407006219900903c001c1d210304008602e0315120752400b42071028443d18607443c15090003503643d40e814490070b0110311607508005840d4400c0c0119941c5070b07841d803181512070b441c05007071200401e060013065042103a480004990800850744440c88 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402269523 1250 402268273 402268291
    0x5280e03120405030613050a0b090a0309060e09040201080417070305090f09061c030905130203180c0a0b2a1b040504020d062a11070504020309031e12 66
    0x450080402030516040a9040c0c122045400740010440e43c0d40c00a0b4240c0d0103042c0d0481c25444100318508146040048040140920711703110400005003000144030b41c030240203a81d40c40d1743e555159000d0b144494100202c64000908c140003034095405503070a240c00500c80d40c01d4060440e04048c1407901908282d0003100002c038009070044c01c51916010400381400d044440d008241881400210180c2008503845103501c500c3c0c0c5a0070a050081c00c6040c014240900007415410301d040203d8020b6000326941c45110340d0b60680c0b14000540085c000034803190182c130743da8070300e030412900001680080c1c1a81d42400581c1c040d00000d94101e00c140000440d002004249400e914030110041c40e000c1c18000d8003d0f4500020000544c0e5051402c003082c2c0d40159000500e0300c1d2520b851440c0d50540c409030b00210400540c860a515440410300c50168501401e0340c601688882c1000301b61310080d0b07409002a4024007200ca010303482c1082c6000300411043c40d4130300d80811a03104c1c4480e03d4088510003c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402270773 1250 402269523 402269537
    0x60112050601090209010c2004060f0305010e06160507060b15030108120307020c0409080909150a0e0609070e010207030c09050a060602010209010906181d0603120412030528 76
    0x1040000c200103050142c81c10681c190b00780302e1343d440028140030030000c0151070382032824140034040c2c103540780321104180040c0081c0030b10364560309000c3c81c60130303548801c0f182580380145002c01d40c0e40104041d8080d130f2a2001c00310f280040340100301c410b608000025a07029580d2001c0241c1d80d500c4110840b9126200c64071540c603903240c065050300b0035800200d4880001b07010410410701a901040b451545d0408590000c1c40d0400381c1040e09a501542125175006a0a81c003405107110b2000091045e401c01283d40ca20541d4503900110206e6005980e401d030010260300106544501502060302600410700c11200029540e865508007a241d03a4048004956200148070252010780988005003c0c0360000b0340c6003001d61000204030311014402c54040080710600c1460b40c90b500110750b4000d0400c2110000001c1d80f6015a1907041c5050310340510911600d250519985225010b0b2422a80400511001e003032641e2015691903205050500300d0b07045110b007052100c0c2074101200c03a01501517494213 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402272023 1250 402270773 402270809
    0x60801140603060103030905040c0e030613170a0504090f23010609060504051806150703022802030d0e0312031312090f09020904022119180f02010207080601 69
    0xc00e1400640340c0c1c0d019070003501c01400071a80120200b001c4803402c0d64002046402074204591082a080e11150b040c0114410311019001400800103c540101c51001c43c0000d8000300c001c0c00c2c03080f0b220100c00f091040c0400c0055174810f50048001e001448800300d244050441d46000041189007074511201103000103100b46c42c0d10403c0240030b040282811482c083c202400100d50034044805003070303402001030001c1c503e0345424020003c60560402c41c1e0381c540c40c01d8a006905c5e0140e80004a0001b10f0090303081040c9000d03a803025134800d0300500030b0440310b01001e204072019007001d40000d0701481400004414000003400461081c418101c2e0420541c526140414110b01d1a0701c03170004028182c0e40620003180b0a904031070031039443d42c9006aa40c06480041406805075007402010640c0b440800140031001c40005840350429001d44c15510001c424484102e41c484c941c1c200160510b40c0e01440040c82c00c03010420501d00500442d508165200e01c01c0303241c0982608600c040103503140e004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402273273 1250 402272023 402272051
    0x905030f1207050f1602012a03080633091c030e011107061d03070f1e0b09010f05091003020a0f080405150c070503160c140a05011101060801060801 65
    0x180c00c03003080c3c500345241010480d00f0700414040c1a02601e88200e0a2800300300b1a80a99014034452a1801c000c5408003031401c1d0116030640c03003607825008251848002401442c052040031010b1203103c0c10900c00782d90f44042c3e00020224880060f8104004010000d2681e58a004903601302c070740703884d61400d1540d444c5801000f000d01d001600f8141301003500d40b0034400700c1c0800d101d01600c10a01c0c240c0c20364141e0000d5055200070412841d50180240c04010404200420000e41a40c884003c4512501c408070b5072242c9424103846070480500c0180848040d540c0f0841c00404d1440040c0b40c50b80c01c009442d40007a03844a8030002e44008254001200d0700c0081e00100d02240c00206418010b0407840d060311000d40b10134240034080700480c00c1e14001103d5040641c19a07510a13005021a916420300210901100400c0380c8240c0f40c0d0020407600141814481c2c4244131100000f60104800610348401928151b041b28500342c0c442d52942e0010580c05824840c540003051a0000407a01600305504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402274523 1250 402273273 402273307
    0x1c0b04061e0923010c090b1e03040605040309060f020a12050904020a0906031a0a090903050c0303090609100c02210412050a0b060d0b071b0b0117100b1e03010905030f 73
    0x2951415904243c1c2c1c0288864000c0d1900c0111880070100d01c0d5910100c1c4902381b29054040ea203603240c1c000100500003848901e911043c8031301c0c03013610f94000c003684030300c41915681a800c0d20500140e004802c010001240c0c10000c0300c2c1c06e181403e0550401200c58005400d0747c0188007001e00041c02844200700450349801181006503800142003c1e0701103190103e03d0840445c05944001612000d0000400d8442d078215013a04031500c05580c1c032404d04e44051703500e403902654480410311a242d032400c40510303d03109082d2449c4440c0c0040110b105c004c1c40c446c004001000d021000201c080c0400500383c0e504034100c11455201c0c401510b00f0012030f00c2c004401c03080190102e4041d4110100800000308031800042d0000f02e1402c0c2180c003005042600b0840b02002540246580c0701d8400000e00d0726000c01000c015911200d0070740710862603021204085903503016a440d48085074000c4407040d002201210414410041c0c004124040240c03505072865002d84004c82c030a280004224802800040b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402275773 1250 402274523 402274583
    0x10c090b03060609040e0309180709050105030708181c0306082103130602040b070809030129060a180e0603070f05090a02090616030305061c0b04061e09 67
    0x28809040d42840c0d4003043c01e03801140801d07030007940d454995001c0390304d0410544440201c02011101c01004d00a00340c0240b66003900d0031804144034080200717066014a05403803080a9998924640d965070f03040c2800e80b81c00705502510503008541c050103046e4803800c500507052405450200e4128038001c035061400100b40002e050000c8084011503042c081c0720220382d044a00c94800020701145410410024407039a4031103500d000d400100355080122900141c07841050890007007000f0b100f0841e59425440c4003507190103c0183ca00d401c8811460004090300c01e02100d440c2071030003d40c660340300100303100b4150405081501c200742000b803d46000c00014018020b061940307401d592500c03000c00c1c04800087e007284121034000c207480780c01e911854142d070440b2101070140f0040016030300b00903000b011b09039406030240803c12101440300c101d4001496000d80d01840317400e000e0340d803a155140100040b0309444810030742c44079000c142c03035003034000c82401d035020b5065000941c0004d418002c2c2e07418004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402277023 1250 402275773 402275789
    0xc15011502060910050c0f0a030615030504170a022a0901150203030f0a181b080d091e080a11090a061211060408100b1c0203100b03120705010c09 64
    0x140420040703031808661088511480040807a42d61900c440100e61b50040da0b20942da101d0004ca40c2042181d0b0540140c002c45514012040400303090380c104030151942103c0103404018941c00366180d044d8820028600d0017030a02c107486503c0720121145c500d4415112200089507404035101e04030b41780580c55940180414214244441200d00010391640002400340c0d401c50170a074002000e221441d00194113000f034454004004a65a2a02e240030300b8003043c54502c500074020001c82ca6680001d544c070400c60b0f642d102c1c60007507031038011240b11008910300c840362451080240000d2100040010900c0c4920901328090681030842c1809190b0000070500084142008000c1000003401c0200c00c0da01504442c0b200e00d81144940441c0c614030940d0300c030481d0761241007400d5240e11143c0d800b82264180c03c0b0f40f22100420002d6100032080701c0034401030340c0f6400944902d807150255610400c07131b145024007980c408045010004c041134000003010380746651100740240800c1d80c040003800c090090b032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402278273 1250 402277023 402277033
    0x80c0409020102100506010516051e030901090e060d1e0605070216050609041d16080127060905011b0f0c05032b06090b100c11040f020c15011502 64
    0xd500003e603240f0b20000f59110483c2d540e0701080e89640300d00101c800c0e035a81442c042020026602e0100d0b62001c0850b11802c1040e03a40ca0b1130304107448040122021a4416524020503034204000080d200c10701074001540a02d1a0b80d130500068501d402c2c141d0041490f100600c044101c82c1080f0059480040c100d40031500001111504140303a0b034000c030180c90040d03c2e51601e40c009140818000c1a1520500301c10b0b01d415407910000c0b2400007401e0300c2d030002120286544d140e030303106107500380d400c0902d03078018010f03448017842c10354400303d14a00d61241c0907545c0030849509030b4440300d00312101503d001489000380c441e200d0003260044c0f0010782480c22858a0f10440d500c40e15070326240d0080c1d2820149640b83d02d0f690301c01c041d942420904080010704010803010f03590302c210200810281804da40100a80c1d070300221b4250084048588aa40080050500e8040101000010403240482c0e07082c4590a2250610f96074040000078007011458040101c294108003041917205001c0a6100c02c640c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402279523 1250 402278273 402278291
    0x903070e0f0f090109150b0f04151502030409020f04031a071e11010614150a09051504030b0a05090106050429010c0f0c140406061b0201030f060807080c04 68
    0x1609070a07440010032120322403944500d402103024222810000d05500459540c0c41d01384d0b40c040d80714802516084400c401d1000c400001c0c001540c03009d441c064841c0d2070b101020480c541c103100e9044c418000d1441524982511041040c08980185031000c180401c040780600401513007103c4808542002038965000386403443d0b0003400d80800d81945051a54849610b0060038004c010841803098804028065191078510315207034000c200900034441c00e1307c6079000f001c10301410100d480400c3c0da90b417044211410b2800b8071040c280c80c502d001c00300d00c504210002c085081c988200d4011401071102081034240b1400d13a50a48246400180c890361910160982207442c2d01d1088000c0c200030440101c2685141d001628020040c5002901c6500d50190502c204a030700c0140b2415500400406407004c115182444222681c80c0244808036803a1081800d100038410203140c00c0c0c0f2f10524002c80e1201c03088840d10180c964541c48071086a0007598248005082400a008800801d4804100c2000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 402280773 1250 402279523 402279541
    0xb03040b013611040503010627230903070803090c0312030c07030c020a05040908121b04030b101503090b060d0f021c050a0c17060c0406030e0f07030303020903070e 72
    0x4084070107070401543ea00e400c440346200100548009203001802005903035a0368287c500190700044105e40b41c45002207500c020a8079a00c00c401080320301107101e002c003101c140d42c651450f9501410b442e00340c0c4001c1c4000030010750520700440c89945803e018003000c0035410b09242c9803646024042c1c403004420300411100003148000d8a40c100d03058644042d4980c694000f0501c0e407945600226000390030000200e0500160200511090300864413440845da51f122200c0e1000000c1271035600b05040030442080807502c0491240d410006200800b1400395440c50300104071003001210340007080d220a10003050000f420003c0b0b40c042c070b0a5404521140c0107507540305242a030480700034481c41d11440305043c41e004e40209448415808001c45140080742c3c10404032400340f9124440030143c18403000c21034030b900402c106018010640100741041d050840c10303000b8140f0080003002c903103c4c0c015000020002041440004c2d4040e440051b0789440e02414182484601c0d08075504c468000303824040109 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 402282023 1250 402280773 402280859
    0x905010f2c0d21091b09020c06060d05030d0626011503020d0510050c07020a06020c090f1b030118060503030307050405150d0207051b04090206070605100b03040b01 72
    0x1524030300c2e203500d1a07589035404076642020403040d200020300e044910b2082284483d07540210191029100c17005ca940e0704429403c0e0321450840851541000000c1001414910301083c0c1543c8200103072800d007202c541d88002251550703800309801c02810381000307141d01c1c0c04526554041800358001d008143d00000240608141031100a001c1c2014a07100428040b042c01009080b0f00901c00c05c0c003803400d10340d0007402207410500c02640f00b2a000c1000044503400096a0502d076140034018180540c0c1c2c104100701d5191009107a008000c0401d8584e60768002c0440c02140a401095141007650307403100c4040302192040c1d041940240d00410901c00800e4018042e10111a01250b0322403000762946a43c51650044c555080581800170400c40104003001c07403550b410314166a460490700504d2020407055a01c144d202940001040101c00e01080198201550013034005c85a100f000b03607507000420803030b4022201515076054410041c8405001081050703440451108001d240b5000003e030701e80c0309 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 402283273 1250 402282023 402282043
    0x5010e090903040e0f011a04080606040902040e030a02060907050d0309380a02251a070f1a060316060e1f02030a08060616080307030905010f2c 63
    0x4000d600009003120764104221405020100144031140c204901d814158040030b010310360400c140c50500c02d0714010781ca405d03078085602c5800146150303102c501c184001005c0781141a41c000da225180420410410001400c60883c1d5900a00d51803400300c00450410007a5000603110f1144903c50001007640544280c09031940c00c0f6103112080c000324144e000900c01001c0004890f40c3d28903800c108110000c000e0800c00c210394080d83d42c40600e490403580b6043d651480d13188c0c601e003102424000300c82524034065005040221607031420000d51607419142c1c802035401c540f003140d07030f1001036115100090701d250000402e800401203041c0000109050131340318000d14080010380c0e2014141070792030303564220120700d021901d17002010303042d1002510303648410f103044081a01007011450a0074254122800c0384002c20610803590703540e5458141c02d030300140862040603112305141c1c0c0454428030498000c116a4440003810381411041160451072800c240c144101c0b501e007071004070320800300c4d00d9110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 402284523 1250 402283273 402283279
    0x60c12071b080a030e121801030209040609020403140102040308180f090405010f1d030d050408122706090601030b130515010512030f071101030605090a0615050405010e 74
    0x416926810125002840d072108003403050318022400c41032014440043c428403400d40e5041c48014552468a5a615840c00420130325070400c20444044440032280c5c0280da01d414940546403000c210000340c10765a03203400800035154001410020000340601204d1038000b820000d41c2441d2450721018120300070503030540c2c12074100994810003903464040305c1c030360810000e00c840701a0401d418502d00030104000300134455458052502030b0400c2d41b0103044030840622000b0351400e107402040401924018204641e850018416490360200c4014007074421404500d0190307042500c0b0440154145041d010b0800c203801100c2400340c4202c000c1245810344c0e4015804400f50349440a030314078101e02070500a0940c1c01221540010058003000e22030403220300304c03020104510042001500e900c590000120b1031403040000d01d0005075000d855070809070341410002900b6a40340081040c1c00021144a490b081d507c94042c0401c11001180c1c007200403031480d04504103410140081c0c000401079210030301c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 402285773 1250 402284523 402284557
    0xd03020d1809050a1a01030b1f03060f08010b030d030207020906040e030f0c0705090108030406080f1b04030b0604111602060d090c03031d010815011125090509060c 72
    0x18458035007208500180035114041001e4a0551403c000074000303462098000303e100d00783c00c403407980700703010f011002107000745283d089460001c0000b406c80750000c440414183c84940004100d80d0a401c800300801000c40085052404902018101186000004207251041c4031540c050380310390340400e40c080c400342c0b00042c651303400801d001d01c4d41c0038451050103030b4800000c059450351f201048200c103d80c8103a032052035690305d8901c010b80324010b03401550700280700b500004c2d06090810300c0f4160824003642c415985609001040c5105502680043d103111500c401408480d08203031240350315003d8081811420241500340035001000c0c0198068820030001c29940349a468952002d03c00c690700041a102d020f5484c9009005c005481040607650040f00074600c0310780d40202140c0744202c40c020000041c0c940c01c0e000550710609050344010340762040d285d00310400c24110000c8044040181003a00819207440d90100c02d40d000103000751516000345003441201e903c294155040f404400746008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 402287023 1250 402285773 402285797
    0x1c0f09140102010902041d1006080d0f0e0a0e04030f090f1413050f0103020102210406320c0c030a0c060f120c09061205043503090303150d03020d 64
    0x3809130244030006075000c2d217014514040f200d9444480304040c3c4085050700e401000118188044a0041c86862480d4104c4440200341502c203a450111441c114201740183d00d80443c08102070065a4200341004c214030400c0c8000d05401502100164040349411a44541000c4003100449000d101d94441080728402c03114541da10702480e4103079510340da80100300c545030000421102c0e1f2400e120503400b60080807400c100d504440261080741084403100c1301c1c5814508070080796242c0014001040601306600c10082504042c0315488075050340c80b03421500d9404000f00507040840360342000c2d100741d02500305d0000040208010900316a01d60510f00810084103d080d01c8203070740929032040041c030304508452050b80101e012030030343d08103590310a2038080194541c01221016200906500d000c070448940d05407480454403520000400d1032800008403101c0142c003a041070342c0c482900d41021040003000c001545400c1a440021124601450b0058801030f480d10440400341082042c03084c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 402288273 1250 402287023 402287027
    0xa020a270611010b121e0a080f09010c0818040b010c020112021e040612050c0403110d3e270a110304051006050f011202030603160303021c0f091401 65
    0x202e00714280a17000c0e8442c51000b0562a07111400407491840c0180101040400040c00107055039040d0740c815805407510000700d8035203100790400d414060410281000c0c4a0006461001500e001d40c034181c2d040800060501c00c0100761803600040c581040070342e50001001d40e0b4010745030f04425030344180c0183e460741030005501e03103040d062031204c1c82080006000a849513200108400580e100542000907407160305070004a84038138071028002500241204400b4600545a070307004910404507603006103c0468a400d2413003042110391944040014002d651004040d600c40202c94110303024200d01c0d690310680e01540c440004846280c80d50040085c10030300d41c0ba07000b003014500351441c00d9201c0c501031030410380d80e0510b049842152070034903600141d60f040200703c0a4140805848011b00070300d80c201c049000303400c001c20503a45885040d84001c221101c662803075012318000d6003c2d084041c0c0020303816103480181144101082682c0100102c0d256202c0034001c150303014201d50b42240d850032401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 402289523 1250 402288273 402288281
    0x50a0e041407020303150f012a0c080c1f0c030f0c080d1e0b010e010c0809060301061112070c0e130512030709120b0c031e0a020a27061101 61
    0x1881c0e0300c550a1410321901d80d4000025500c100c01d10081714130a000140240500c111940060502140b0175400310501003d01c180e05c0c49418200c2821a0180915902c8003414454580d0040841d074014075494074450a04441e04114038166030685078402c00891001030401c00a10406030800102d140c4002400748280c602c0d0310b64980000140b5107421045410313000030700341903810303511804a00314001c0003682140605075139040140c66030010354540d10010b40340d030a0511001c40d01c5150420100e1040d070f03074180c083c5028080b81d54899550a24900c4510328001d0740380f442c5010440d0a111040005040311901c0301501c541100801e450307140d03103003480c8002800c0d0800a189000d400c6c038003d072611200d4040d500c12000c50352408981c69a50303202c0d88500c88020801b800700f0080400007070441c0ca10000440c0c2008014551140c1e0b2050006510380aa50544a46003140d80002c0c91045581e80120680c24140707988071000f0b40d40c44013150000d0f100025106030310071b00004101c3c60701e0245007940 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 402290773 1250 402289523 402289541
    0x22a030708030f271c05091801030b01050d0c09111c14060607110424080a021f2010060305070906150210020f090a0306020304060c0e01050a0e04 64
    0x181840e01c9040c80d80041c14000011600c12070070203c4185480c680c501d00703441124071030312010040c0000000b81e0000c0e1000c417020003104400d0200c208411080c41d03d820343c40a201840015202d6031950443c6050a01c42c00d040c0c1c4198480c0418101d440003242c0c8983c1030313804443d4400c00000d050040824244100d0143e080341208248140c003541070f660f55650008500042502400e0700b40b60303903140401c01c0700d01611b20003810484800054908a040c01c1c1e100701b8105900c00c0f103803000130001042d40444900c00381c010300720a801c405c41640c11806d050300319040d04003a0f14131102140104180c004d102c2c280c4c00000740356010300e0440c031512901080c85002d00c841c0701030500b03008403512401d00c1641c0e05210300c034018040d4030700080002c03070625690000d4101e013200c0d405080d5101080c8000f20107134120300190030745008100610b424950300d42c000d6000640c8100805078484c13815040c000b0844031200d40e410203201e40c0d0302d6030203107681e80a0116000103515052025010000d04041001400c50380 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 402292023 1250 402290773 402290783
    0x6050f18060408010b241b070b070312060803040e0c070c0902030108071d1302061b03120403120603120c0f061409070f080304030210030e100608070603022a0307 71
    0x401043e00e0506400014500780140c1d0582d031598041002c40480711700d14040320380c00c400d0500c070091903890303d41d01552041d8101e40072a038099488000e090180ea20a1108502090410300081e400700e03040d00400d80103041c1c0c030b40a1810039103059044e242c0c424008107502c69a0500250420401c0b121b07048640141020190454407581c56011b51a6900326500803140c00010314500100101c6150f400544200130711070540300039184545c00c1c04141d802c40345011902c04085001004844800c04c0500318904400c251100141010709000d810401d19191205029041460a0001c01c2e909240701c0141c0c4058603202d0052407580c1414600c80341c0900009103618201002c0c0c4081d80300c1c82c01d14030b008141000503158610740d80e5955141160f0f1318800c2d0f034034075001031000304090314040921180b00032070b42c1000b1074110825a001c504004034180a0145c003580c0e04014001240c0030004c0340301034030032400c04515125501160820041c0241011108407130032107a1f08003820310500654440542c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 402293273 1250 402292023 402292027
    0x105090f070c17070c081b1905040519050a050124080c13081212010509040b060402070c1707151403041103120d0605130218090402030c10080a05060a06050f1806 71
    0x107225115150700052915500e07a5890b001031515502e80380300c00550f40e00b008d00008050f14541800e010150200a1000c04413900c0302091001d0b44145000741442012609800611581400d14000c1280860f5940680700c2c9081491040b071a508842401e420070007e10074582c440c20710a614030b1142c4029040502140107805285100c42d2030764010307042d00e09942d40702a4507680c0350000d011380d5040407200075001d00c0202000c0741c96400c2c198000d0810070300820300702090b26101c4020031003490661980b44455881207104101c2c06000c8602026502c40a103000c03c0140d18521813182603010290024145403041c0d030100001c5c1c0c1c0c04000801c8000c0803403e6150701e91324800d090000411540c443e450166a0482c003a000001c0b0b1842107401c2d00c0c003070790043c42c403454805040c416003610003402282c1500c0b562881c4101c942e0b50168040082ca544d0340c1d42600c0389040c045100079a60f014000d1801001c01e000c060124a8000050b11541d5142d0003036952a1100c41c400d03110b800409204882e000080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 402294523 1250 402293273 402293279
    0x10c02010f0b0303190e06091e0108060301020a0c0206090d051207060e01050105100806030f0712020316030519050316030c0201080f010b030c0726030105090f070c17070c 75
    0x10341040215000d958420440818290300f4103450388102c0916404200b11184a410b8160094400840090f805840d4038141000440400c1c0c1a0040040310b598040000314000346035a0310042c1c295210324150000e508260031620080c106006a0a0081c403424001c07524179003507252440c40d504525001801c039a44a1502f07002d008203680f2a140c1030b2004c90920020002c0e014050091904958000d080c0c00d08551545008445904018101a5050140603001115018104000c0024055101000d200350403144100b40ca004260080c3c4400f41150303140c10004a00080350221a0540240b200c41a842451802c07900318402c0514510403e5141200d01d0b00b0f155100d65041d034114800c0e00c1d40041c40d120581d81d00c2c240c8000344038003001d40c401040001c148001c9000035210480c82290b030616040c9100e00d0f01821104000c181d21441400413004100b11325007140f081d9004a0400024584e6003807106c802400070500d03001c00b81c078015041c5518102c1242c103c0464010079084281c645100392 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 402295773 1250 402294523 402294527
    0xe0118022101091203200a02061302011233050303030a090c12080d060e2701060308121e07140702120d021c1b0b3402010507080603030a08040c08010c 66
    0x140c419800010b00441d180c0200300c06d9182d108450a9041c1a0018461035864600c00d50400d240e1070300c124100320300b00e03440c122000140e001c0e40c00c01c42c08074142001d1401c8800b54840d00d8070780c0c640319801080a0400d081006480c040102c0c0d030400c00324100844d00d03580c0b501307004c07800c4511644840913815801150b4018880382c003002d031010f802c01c124280283ea5903601140b82e8140240c8070290b000b03407008111035502081080c0700180e90545000410020307075a0710741c00c1107030b04140d00002110b0b84450820602c40078080b48a80d04149000340c000c52800c01d05001032080003e5008002c00c6900091407006660303d01103021940101c28044030f860310070b0b152009480d6000040c412001201000c6101507c80c052608001c800e05c03410200021552a070b1208c51040002401c04032441c0100c510b4180341145c241c414000d101a0000e010390340344040c800003821948003d00c1041041646404e1151956011045452910480c80d260900c2d440b141000611140c82e503018031170a6103040c00d0380315515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 402297023 1250 402295773 402295781
    0x60403030c1509053c01090213060b030c0d0f0c0201020706052202090a060f0602070810060608183f030402010207030b0c13090e0118022101091203 65
    0x1c0d204000c0c01e0801c0a040605509441e41c2500040090300310512071041e55840704c91004800c441403a030b0700c00c00351305c1c5a040980c40e410040900c03420f9440d804880250b00f0300c00d0300b14602035007803c0100001450543c817440140030140901d00e8111001800c0000c5a440390441c3d00100d001d00010010b940624001038003d5100840c221020360030100082c0c14030442c0059089002c4448120345182e560503400c200c0b00240c0180340f040c03081e42d6003802240211403226001d0152100342c00510307801c1d003022840d61070320500384903592540e8140070040c000325a1240e01c4c19085440e010807541034010311a022800c1c418620141c401e04440e10300a161060141100d01120b40440c640b00c03c502e203d014803010180c4801c0768045d01590150030200005440061896030140380c41000600380709461a00040190165001148541c0c451b80301c801411002c0c8500d00b20401c511101c80d5605449130301251250606002e00311280203e1703104215501000c1d04400c1d440303548050f50a50070040683d0280080c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 402298273 1250 402297023 402297047
    0x14090405070306230604210f030507021e060d1109090f15120d0c02030a120c06050105040203060a03171204060e06010605030405150613020c070608100b0702040b060906040303 77
    0x2d00160310a84070304100c08901c441001c4d03000e03048501c0d10b1304010740545c00c02900000e0030241200c507440040400d00301003003890640c2c400d550b15541d4030050300402542c4030010400b92200702080c420082c441e55002d040307c40f8030005880100c1c103195000007092042c011500055000180b400420402003000c4401602c9400c80c1c213100700610b50740c501401401c00782c516811080c0d82c0080050328030980100f0f000300c1034078802005c4580f00032480d030300c2c0007403001200050004140c06845107010400c035806541c2c00752006540c11801c51070140c00060380750b4000d10020f1f210091004541640541050444510a940ba00105a58186480d0580041090612820307a81c05030300000301383c1c00d00c138004807070050f500000100130f140031140c0c01c070760382103406040e40394841680c501044416032203001800c01604020f002d00720451074118041c01c01d80004041b01da24081510061003043e0105080d1050310760150340007da01005240841c05c1c074411455083c0d4045404030700003040540c820703400020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 402299523 1250 402298273 402298289
    0x6060806070e10050a02070b0d09021804021e0904061508010c0905120102040e0c1303230c0901050d0b090118120306061e0f0c02040615020c0d0c0614090405070306 72
    0x10303e080c60201200d4a019912544d4016008018108803005104000e06a0f1800c0440d000404203d0303540051081b501038404080d8200e01c401c104025031034006450704c07202044a04500d0f0340c800e903600260342c00d1402800103005aa4418100d00d071401c4180172203001d0003074800200140601d2a8000d403486c001403050a01c94180d5601b02a0381580c10b00a5804481074084061044e03103519080081c603030440c23210001d003a0000350000020808500c00703034041d25450a100f00f19070741c0c960030786800d02440c0d0b8143c0c0e0141c046400100459180c4400382e94803a42c12022040040c6c5414980b030303014100b03007007142803c182c07548608018808002112105207032651000c01080703030342d86002d6810206061920010b512741c01001070141d801803071305044481c550301d410103c40446900180444885800c0007035100101052030383c00310b40411101803c103404588004480c401656410340303601140c0600c608103e40c015071002e80c021450166902c46000420610141c03501600040080500344281c00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 402300773 1250 402299523 402299539
    0x1032003160306061a040302010f0e1017130b240909241302060906070209100503120c1c050409060305011a0f030c1c0204060803181e010c06060806070e 67
    0x305a41741d08400c0442c000f500c0707445410a072868005640c4403c00080c1c00c0705000514a42407000c0d610034003550130403002c0340c940c580c642400d501b075800181c02c024818508800e60915120204000001040c0d12010040000c0d44044117920900c0045100c0c0444d40d0f000001c0900740004108049040b031341c0703030002c45901d00505001c0b000d0310f4030114094900442d07035101c03407000704c0140c02c00000805a64102a01c26480c0c40c3c2d40d0f501080750303014211102800b061078440e080c840752505100300b1142e01d10500c0c800d820f003800009440d0b03c40d5602c400c1d107080700c0064040c03c24018028020349006013240401000095540d0400724007808180510030025604090444480e2925040403201888050b000703029441825007032101d0402032110564094000d8807072038006944900070a000740040c1e8010355143c00c1102e0702c041500d24501c003c1ca2045800070008030910b0b02507254460000401d181c24a503134441130520500900c803d41125040f40076407010041c100f0b411041d0795070501400d9510507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 402302023 1250 402300773 402300779
    0x8030f071b270e03070507090b030a02180601030e060a02070303060510080f06010216080708060604650102010203010f050103110909101a03010e0103200316030606 72
    0x1c0c8010340280140690030300d10815a101c01d035004444244001c08451000525006031100246150000b4608440680c011001841450f2440c01741d20b100b01c000341c0080c507460728030b40d00040301d000d103007014620441051000078150b60b20a0300700000740d190b10015560b01d400c041790410003a42c800d810940200c2d0800200140908010b681420507402c0c0c0d54465003191510040280e400d107014001d103045105100d105900500e8640c1043c00030b140040c01414141c0c40d044005091407401000309200f40d02d0010b050801403c40310070540782030b590940a000c20b5680d00200c0c1c110380b40e811180b06207900c2c009104d4107171000020000d02400302e01079585840c840c056004a00b41c0c4800d00824218a007803200400480d4000d800c2025070462100c203d030f0501500c007021801f00a01290105040ca107448400c110a20441203800c002c401100146451503042c0540503030040b80c10720004145161070108428061202c14503440c1c2c5c844000c041d030384001c00c0014203042c0303640230b40403e440c0c00703150003000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 402303273 1250 402302023 402302063
    0x9061806060b090d080a11070612050c03010302011403090a061a1201050403121107080304080a1409030607081f030b060114070f02010507051e1f090c03081308030f07 73
    0x3481d14154003c1c242d40b100031085e80c07844e40540041e2100d4041c17100428450321040420310846001e402035680314290411070041031025940050070707200001c04100014000360743c0c01045010b0350424182d10950326103c1078040c0b4034110f13011001504240c138229410b0b801d66400c28000d94512405c5a4680f14124618580e600b00d91068a00074042423400810f5494460590482c0100865024055060002e0b0361a02411a44216000c5401d940d00168101000ba01f14808008007103440e40c101e8140030708000400d58840d0081c080d0350034452184001001e00303001103003a07c03201061003a44c940c41540d03840c204840e00000d58045000c64840101301141a1243c410307200b80c141c0101e4003040072802600150303480c0d0306c821411341d00c0d40140e139000203040d500e03e5500340803640d0f0701d401404607070b064004060840d420040444003403424052004045195544c909094a400c55103099880302c0f088181059800035a1100045001c0441c04004510301c07800901403042c0140d2181030040c40c0103040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 402304523 1250 402303273 402303277
    0xf1e0507141b0405310516060903030e12030a0201090606050105160b180a0c140901030305030703050907052808030a02030301090209030709060b070201090e0709170109061806060b 79
    0x151506151482d108000780c81c00740c0200e9000042941d0341c11003140850380c0304107601c000742500c5d00305204001746242084010003154122645000120200d81c0c2410b40003403140078144400f074200072030f84003d8007030ba580380340100101c031090b40e007103035610402540042d001e4070054005403150b138500100005c055000b001100ca58400c850040101c403100c964524600b8003001e090342c00346544460008034009400c000b80e00356240120306000740903141070030740a249160f10b40014000e00040c401000082d0300703c0d080d660008101d05001c1100d90355500c2c0c5030b2601e807056010030b130701c0007151480c003610b146c109068071309803014a000c1070541504c0f03010f42d982d80c0c800e032a1403c005038410001000500741340e0b40507000c8c40c1002001d0703e18141d51441d2f03010944155410246218000107a24011581c00003400030051410311810070301c2e403402182c0035018001610407003011403110040440010800c1d4001158580e004101300f0480ca070f120720044100c103c401044903000e2810401141e1903d02c002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 402305773 1250 402304523 402304543
    0x1080c100c05030d0513060f0c1d150a050a0e0f0a060804080f0409020d0b01020c0916020f0303150a0e150625030f0e09090703030f1e050714 62
    0x460950a8940054211400c0d01c8101c03042e80c0358001445900c402180b03030302410380101c10580001119610b1800c0c800d089a601100149240b4642044204000c0e0004c1051403550307030b5072103008034115660340400c025100300038801f0800c3c1000648a00840e400c01d0142800500030341d50b8400081c0750b00c0600c0548542203c01540c00031842030b0810100784203e80c0c02e5440b0b0302c190811800c00c0c2013a02d000b00b99030042e80040e80c00540200d000000000c2c248254043c5000c240700030429050f140012415080010304101d4003120881030714626103000304040280f45034001c0480740d80b860000f10b454000c0c0ca40303640c0036118146105c4005040c14180061030700a40c444501c440d100300208040186981c03014480b0016080222001d110703404410130a41e0b44c050294032815482d2698201c001c0c101900034103c1e0744500c0690080c030440700c0001a1890075682d0500781200392000b259001e85540c2c400e83d103000242075812410b5a0049d600401800c020381c8148044141e59030324061854450b1a000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 402307023 1250 402305773 402305779
    0x305060109020a020703050a1511180402090f090406060501111203131509030201050723040506071e0507180e031c11070c080609011107032f011401080c 67
    0x540184401d207219401001e042c2c0ba83d004641070103659070390300d508140c42500c00f52000251000301c00c4181d05c40380120b01c2d0910084031007030711b0504404c2040c005549403c0816004907408502c00800342c880d1805005203000c0103101508500d0a07140c64006840306001c3c403800100661234804901000254015015a11746041411070340d8454414180d0440b20805450342044401c1c0a075404030b8901c520f00800d8001e5002003424505002e010303103104003141038003419000c44021540750b06030000a0314241c0c2c02c02c0354810381c4e07041e20b4207210b034690b0880d079010611058801c038042c0030030000141540456501c0b0030081d03441c203d43c2c00d0283c11210481842d000d20b800c104082048003440380c401c05203800c0a80000648081c01044c2c0c902d03c0d80065804a07842400c4800c2884071440c20410f156000c0003c500901c001d641c3d41742c47e1581d50003801e000900748200041d420a030b4802d81840469511100301d801c041c2c01040d40100360113441400b4040b02d41e80345040c000310b02c00c28081948014100c002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 402308273 1250 402307023 402307033
    0x306021c0203091b060d05180615010914312405060304030c080d020a03180302030403140a060c080624040b13090f09201806010c0605040302070f050a0305 68
    0x14a0f400001315940c0800e45611410422449003d00d595110780341c05a005c64080c034032a80040e000e100c1ca443c0000c1c000240a00021000d000c29030b0340030b00000280c0384141c0811008200440205113a0010111844400d0380f40c132014100101c81c2420040c016041c0040510100c0d40c0d041d400310820411151405030101c08941c01c0c0001c1c2490313802190054880e01d0f01e0019040e1607282c1403043d81144c08010301d1150001084856154035015035072030b0000503501b4166510103654041d651344203605c4010f224401449450920a405102d400401c0b034101000f4001d030301080f08024262542121554810071001c01d0f0f010010355040103000c2c18048001d0039910f010308104040030079812168811141001010700454100002d0041094400303141d100850580712900e06241a8000070b40c609903000c0700f1040b04021540c401000c0e0080000e40760641d14140c0741c90004980c03460307070140042d02450030081400201680050303040d0843c2c00c00301c0341400c030a45610820000d115203200103015903100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 402309523 1250 402308273 402308293
    0xf0a05010e0a09110a0806061513050409081210090e0c030a0201030e030705120703110f06130314072004020c060a050702010603020a0602012910030915060306021c020309 75
    0x8583c2c0f00040550144028000388030314240060f00e11180c0b9045801c0c1c0d9080714003401014144070207948100000c620590742402d102c80003820460302d0340d100319441280c0360b0313100c41c00703200100046884c0c020040c203c8a80307d2901c1c40000480186503c40c64914510302042c40c102403030085014042c1d180000c2c041c03e0080829001180984690084c1c00b05034003082082d0b0000890030000f6403444958160543d0b120221410050290342c1940c0002942e80c00290074030441040c04503640b079010405006034186014241021585060043d010348550100021040f00b880107500c100e0000000f56810090a80c00c0401444168000e04c074800c481c5034446404941c03038000581210b40e010071a4400066055038030780009618464a50000c00540d54491031805a5119074051641c070714260803810b204042c145010455502d0f044003041308160359504080100007040803010f0f0f10a16200040c40b1480d120305044009500400103408045c0d1003072024000c0c4101402542e100f00750540282c90b440300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 402310773 1250 402309523 402309541
    0x80706030606082802270906031203090a1406042303091311070b07080f071b0c081f06080d08010b0708070203060f04060b031c050c16030b0f0a05010e 66
    0x742007609140b80090f640804c4140146480507190044410800050a039030790705218044201080150380550401400c200d601e403030010700b50f01d906914540286d45d9544040e00700b41010b001c000000c10000c1300031144d119241d000504503003e03502880c00a0341c040003c500e1aa024109420280d041e900305005065191610902d0440d03a010709039000f144a507846c07400c01280e64070410040b00c41c0725140050100456003d205a0380c00030340f16406d8901405d0410010b41a0103c1c124510201884001c2c01420889000e081c5001404004101d4800000e9442c210100305500248040c0703441c0307081400210300e000054060000d200700c0e00e03800b8869091071407802d0340382e1040900b5160340c030080081d400141c4007000f60f244030b002c40e00d20799801400d151822205603087d94200c24481d40c8507050768007100442001c3d00c2c15101c042e0500590701e40c0900318540c2480d40c886140c0320b60340301084002061000c45a444e0f4881c9100b48943c15003607486101c0c05007265428040c3d029044d0120001035140c407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 402312023 1250 402310773 402310801
    0x912050d020d02030708010303120510030b0408131712092b0f030e1f120c0905130204090501050916050a05042c0703020708030a092102060108070603060608 69
    0x240020001600e40720b2805854810b9078000d464550006600c0f02c0100180b5501071240341c50100110024809400c1c1521000c43e241440d010280800340c102c80802c04101240d81140c8605902d007500d01002d40d030360307044030b1005102494420800d0040500350034490001c482100c0140714002c054100111203003143c1d82001c031007004c4501c06c00445031480743c0400c02c41d60074050294413a0340c0304645140b404060200c9016030032840c211000e12044200805a003114a8898100c855200040c0c199090003007205d100605500541d0071296414240340b440106030000d20540f0410302041c8000d913a02c2042c01105c100460f10118155940300950461034410402003484140e10701e4107a0801c2e80301c610040d40903c61012542035418075407062903440c41c41d403c802d030703000c6118141182051200d0f107824402d80b10081c881e5852640e2000208100f19488180c401010113a00241e4100703000c106020b03544140a011700103640c801c6010016013640b20703004280903220b080e81c1e000901d0b01c1d8124490242c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 402313273 1250 402312023 402312037
    0x215040f0503040b091905010206040b2724090601061d090703150902030c16050f010c02030307030e060103150b012a0c0e01081207060213031a070201091205 69
    0x140c115522502140d000c002800c050304041c41c000365141e0340c4204105804556414100f90318152210421084c1c0e0003082c41c0b80e0040d08000c450603150b58405820100065a0a840012880215001030403400001d00c2c914a01c8001d500001a820810342c44001e0610860302c094243c0d0042c80144101c5201e11000f11084040c05a400006060301000441c106002c48a10b00040d6983d13060701c080301c140743c0ca64002440307148000c600d1410b02d07089100c028405d0060b820650030344440400200841048050346501c0c0e104001c1100a4103108000c1d06c0e81d0042d100360001904003411100448004180c0038100e991114540d070080c1d8901b00f0610240c25440c1c01d20317042c0b01d5803480340a6054441e40040206090245c101c00100c0d80c546003440082039141c011148110700400140800003001441000040b030104100c0d442e04518540308000e4403c480c8100d4480d012034200204001458005502001141040444940c1c03170000c101d00300c8220b0b45001d8940d58070000441c0d80781e4040c000070025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 402314523 1250 402313273 402313283
    0xc0702150c163203060a020f0d060303030212070806030a0b04060e0f0102030109271b0306110d05092d0a061a270402090a09050115061e021504 63
    0x1008100c6601400015107551122040c0140700d8194103c1d18421042c10341c440381c8080c2140074420140740440c1d59400002c0500501e286d0001e007048950740040c05848410f0540301c0305101090710307454010065040b4002c1801c000b42d00f000811003050142c403a0034418440a0000d04445445031543d050300d51000e0f1040c1d030b01d00d568420844012105010300c07400701c10500700241e0340c0c2d45012451811511806490080c0740102c070340054003500003010004003d6004000740e9503c0130709101d202e8500140d60301c028000c51501ca100b50192032004050507405440d07410800c1103035030341403030716464519951100c5180000e84013149a1041900e90812408030200308075101c01030955901c500329541115400700080010800c00d040303140c000324a6200c699000000c1005030403e075002da01c0060301800080c4200c00e6200003811310080d03035000c1103d05400100a00034160000c0b9803814a2001d80a9240003a61311801e4103100d0280d064044e03041e41c00341e4002e000e58054150300c0a070181c0b003c1d1013161 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 402315773 1250 402314523 402314533
    0x60c030304150204120528030e15090607120e0a210302010e10050a05181c18060e04140c16050a020409051f0603120807020a051006030201080c0702150c 67
    0x402c0030700c041d207207002244618010280c1060000d00100e0091004110490382c03011f11085500182d4041d030407882c3d400c810340d1410795400d44440b10705041d00811150315000480844c020003404248036083d00000402d45540c0e668144a4092012814079406407601050140f2298100c0301c00c10440c12070300c0f5000344000540f059002c6c0e400da00384580764008500140c0c80e00184008445603205640c0c00407940c3c2c120130070b103c402260454680190b5110b00140c5400a104c8810442c05440c031594416818403c00803940d0b11400d0180251141d900c4040c09a03240450316580340d003a02c01050b0203000018a0b440c10015103000e401d40b2203c04180c22140350240360400030050b1114010f0b05445485140074184081e60400c154112400701402c00e100642403590030008251204130407015903a05240106140d80d074554142cac540854050020014803c81601070707103009040d4012405c1e02d100b40d8400c070a903142c00a0003c0280100580a0b61188116000160302c00403040141f1815902e4804c2d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 402317023 1250 402315773 402315779
    0xa0203250c0c0603061404020c250803030403094502070b0c030601110105060d06090503090a06020615041b0e150c06061315060f11010227060c030304150204 69
    0x25441c284030b50150f400300342c4a03c03050001c0c040104d807540c0c1d0844151421402c10061020070b070740c0c0d00032520502103240100001c0320900c03240c0d95620f07005800c900041301d58034103027490010074504491050b0820392850900700c006800440348500c90f54200e490b00311241c02103008030b00b01d01d03008400603540071650030480d01000411521110f803113034068101c2243c50780703400000500100382e8410400c00d40c0c1d1400c01000007990b0b60b00403420f10183c20080008400d4501c2c07402c18618030402c00c0590b40500394000c0011180d900082c01e610482007942651768901a203424401900d02d04003c0c00101c204411382107032100c0c070401030141c01190003010640400e5200940410315031100803040000d80140c8100212420070002c2070300740a0030708204008420711201200703402c107198002d003000c10103e0501c0d02d41c1c0b648200c06072624250303020001c5680d6821310040f0b030041075984031000307040394958041c290149004020b90310f04060381d0000d1499a62030f42c0c0c0d813103541c00c559208113032210b038244004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 402318273 1250 402317023 402317033
    0x5010207030e0a170c120c0901030c0801051e01120f140f07060509060409050901020f07080919050f010c140106090e12040e0a0209041103090c12060106170402030708061306050a0203250c 82
    0x22340c021070282c2240d42605003064910350075039000070285c0340760103850f41418008880b8014040e0460b02000c4c0e0500710104c407032800c0403851001322000f90006200c0c050a80020078045000034511250304211150290341316000d440d00d0142d414400d9216000b48000c20050340c0c02c0c0c02299101c40d501c000146058442107000300103400c5104182c4050802096000c44c81c18a90400e07071010582d1301e150500d603440c2400142c1344d0311802c900581004619108282088004400350180f00305c000024010f0b142c80e10b0780d14006101c0003031904039511a9003000300f12044450215000e40f802b40b910f4041d00d07920282e54001a5100510f004d0700a95103107018103041c50000065409031035040050840410610100142402c1020782841e1542007540104060341d0060420120708201003402c406983e80e50001a0400080390b124010394002d00f030800c40003160401495803401d00c80c00b0100015200c1030101030403400300b00c07001d04034503101055030348541c042c06181200d048124030b403920b9048419038031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 402319523 1250 402318273 402318289
    0x5090907060e040618090204140a0c022109210607090602010b0f01051606060801020a020102041d01030c060806120d320301030305030c040305010207030e0a170c120c 73
    0x16511640d000920300784092540008000140c000c2190103000607410106012070710010801d0001005948003c00d03011034840d50030100d0856043c003041a1030f85040070095000c0c04200c481c1d0001801000803c0e440810003002c06815403c2e41d24a40d030500e0800c00500200020f510480000ea1031100c041c0c0c403941c0410011144100d01940e124918245044006400d40d034080681c184214210750785101c16076480b10036101c07804200140b000803104281403100090490744c011040950001030042c0c00560150010001c071050036200c010111207440e85c00342145c4081c0002480102d1a010810007144a4000960004c000500c40311604040241161134028040c0a0402040b4583c00d050310418400c10108202c000650056800b40c4c04c5040350007052105010090030f12101002140e039214424042c2d60185600800840d41c485a40c10060222140004942d2181c542c400001c11407210034000ca1550342080d100614a0800a00400c104403100c9182d0348010311440b103039480c0550352644 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 402320773 1250 402319523 402319531
    0x40f050a0807030c1208240d060e03030618092a100c0b010b0a14070c0512060a0605040c021f0b192303031806040b0a03051e0112020103150509 63
    0x1c80140e0313103504d072400703c800d14015000340e01400011002c0010107170300b121407140f400d0a440300f0180c0c084000c000003601c180d5140000b42c1244e20b0075030110400c01c0004021402000c085905400b04509811140c0c011030003182c041200d50000c0320707082c0d04118034601d460710404029500c00e0424240c040403c1d1031840d580c0014000640b511900c00601003000060383c00b4020100302c1503d4803040c0340c0d0140c4907402610b41c0c0391410a0010301c08060100391040a80940720040c0300c250881e201214590313540034250b54092450340307400000205072405224a1742c2e06591130f00500501c181d0f41c858800511047e82084180c01d45540705866599614080c4013003002c901054440301c54140500c1412100320a11412020020230709565040d54001003a9401800c44141c1d0444c4a541c541c04104507006907841001d181001090200100350903400107840b0f038118203034000303050354480c0489009500c01c0c40303001c11814240f40800c0141d480382d000303a030700c0000c4181ca459080ea990701c0801d40ca81f80c12a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 402322023 1250 402320773 402320777
    0x3100308070807120206161409030105010f0602011803120b0415081011090a0b1b030d0603030e010206060918030c03030106030e0d0c080909041401060323010203040b040f050a080703 80
    0xb059020481182c00c1c91641c0b074200c5c4010807243c40c018031140a02d0a28100034400e0201c610b0034140d07104000703070403942505c6009c1c1c000d00c1342d56507a084140d0205420f0103440090350a010480400c403403813000b80c054450f050b40e0740340d00741e52804000d1b0f801000f508022030b4010307458940703081040b4103452040e401015120020008146002c2d0301e0340881c0e00300e80c8101400c40d01080812425178400d0058000d56811030a401e5640c01c603a011880364140c0c601c12070855010105000d490310685512600032603000340c0300c1416004980004a132242400c46549034000e44600c01b00704508698055580d0a4000c141100c0c41c0444030080e540c51500241d0141d00001d0712100390745584c41080c00fa0340c0c00042c003410010050b602603950150240104c500b1980100c194100003001d000c0c220300b2507607582080300700030441c0641345d05010440c0c2c2d510703c80304d4511040e44072403542d051005100f260720554004941c0201a1501d56802100039020702068405215624510303001c2110400242040c074070076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 402323273 1250 402322023 402322027
    0x1020c040908090114040e0c0a021005070216050603100e06040209030a0c0611030a0c0303050a02070f030c0209071418030309060d020d1107030c020d06150b03011d1b031003080708 79
    0x8800102100d40070480101c590100340401c022102651f01940d8009800c414000c3e00c600700c41a040b03151464880700441d09600740300600c01f110b80c000c5910034079444104a410131007511902841401d10068403000032600015508001403248800016000b6070020409440e021079200002d103081c00e141002e070742c6244031000411003150000b00001105508001a50501c840120040d062000500c4083d05064485000600828142d41102c2c0c8441c0d00c10344030300e003c1a403401d0080c007041c80ca41d402c038000e11042c00404c144902412040d60f2900d04001080d20b0180840c0403064001c40c0a81d107260107100a11507224282c0e11180980036003091150016290313425608035074280c03070b0028902c03045410104109800306e5801408585070a4054075241c04014052800c10020120701c2c1007410806442040458050f000c0030085040390b6584000d60b0b5061000c02680791945c4d03043e501071150101006c3c1c00c82c10030040c0c902031036106111001103c0940e50b2521810001c0c2e100c40400c550352640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 402324523 1250 402323273 402323287
    0x503010c0309031b03200606010314220c0e010e0a14040218270d080a0b030303061003020405131b0e1302070501020f0a0801083901020c040908 63
    0x2440345805040c00d80c41d0600c651401c58a001c3e12041c1d95140801820420303070010b00a0601078070603506603102c1080000046810344001c0e40d00c03010b0507039400b4006820708071581c09200707203008820f004041d0703848010340d00c3d40d04179540d40c1d0b4000c49500480308c21140b0349001440500d030907101402044506002c100307525000d0725441c226610540c0704207401890109001c00b507100d1030079000f174405040b0060038250320b8611603000719400c80521201d1f0a41150401c43c0100000f2a015005905540716003149440d010000004d85400f4500c280d0960310903c00030b4a140740c1000c0000300034240e81001803400f0346420104002e82c2d4001a200c111546a51511460040c25a4051032072001841d00c155815250303000560300c0070380044d0001c000303500840c607041400b400390b0498047c030020301503156403011440c0c0f02070324491003481008598040d41a245010810302401c8202c200001d0300445840c1d0a8141e80c8580007a00101d0a070440c414240d210b101921a48034032400d50f03000d0080c0c1916000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 402325773 1250 402324523 402324529
    0x6040203070b0f0301050108071806030c090b0f0f0714010e03040e0a0510030809040b0a030f0b060a082d0a061a0d020a230604090e06060409120e0310020a050405 71
    0x4095026600c192000c000403c00b200c0c2c070000b66030569800740f03030800d06922600012142c42010103145202904042c030300080540d00341c1c0c001d4a1201311901c400000f05d80e1401e4036651400780c002904800700c000c0001d50040c410283c024501d080c403c10781781c02c0124400c4034007400c40c2c0343c000c44040b040d800050306200340f01c4e4014400d035020892031018046c0b0f140c04007016104000c01c0c48004c00c1c1e0000840d4030241079450380c101e040705440c00b60140308100d5032402d04030b00625250009851240060380442d90a0800e00f080b07078140c1e40e030780d00200a1850140070105103502c070000300c10881140c45010901c0304e1070502000401902914011503989008130581d0b5a009a41070500d10840465280b10010f0300c4643c2108122407540c401525401628104000f00c144000001507114100180c0404c01c0246da42c01a01c0100913507044440340c1d07070717100248130444107404809030120480e90a054052449154288081036000e000ea90399034250001550907a0840341344e40c8089103010405020b907003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 402327023 1250 402325773 402325783
    0x1080105060604061b02060f0d06050a1409070503060a0504020d0f050703052707050913050f06060d11010905040c05040503012415030e07030c03031b0c1203020a08040806040203 78
    0xc0c0102d40040c685868600050280c00c4110088a00d072881e40204c0c0040d03591f590142c924a140101c01241c0e2882d40b800c00300010031150140c2032044d4903045d07000c6144924020107280880000e006c0c0c01071b503107524400381c035581c00c014035040e40090343d010003082ca41c840340068491011500c1d404100041030310520802d98200a04110030140f8100c104151254002c140100c0c81d10664a41c6510310500811a070070090305400186c1c1208910b01842104800000540e03039041c01941a9444601d49051031600e0b0342e0155000386d03010011595510103d50164102800684141003102061396100c001c503096502c200c40c0800840d9001c102000142428010b501462038443c1c0031088081c011101200c5c22445405a060f003500111090720040c0d0103940078908401e001c00480700056030b2480c000311540e504d070008074001042c00074500009920003000083c0c0d01d6001d11000c50f60f500f0011800468a00f010094045129415412001c100c1010041010703240c940d000d04039070300d49401414504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 402328273 1250 402327023 402327031
    0xb10120506040e0c060706020403050d11070812040b09010c06050403081504062301090806040b01030c0b030603071e0e01030b0907080f030a03051302120615060c1209042301080105 79
    0x6500305a101c0c100014086104c4010300d00441e416a00d40115080c40002809180c00080c0740784502c520070710081d50001c0403145d000c0f5074070046a00154449080a4851151281d41b686102c81404103015000105029104485040c5400500c8500b00d880e101300703032902514160045480c10042c840d00408000f20036040d10b00c02e48042c40103601c0c0001ca40e00c9404885600c0d04400d035004c4c1c2c007510680c41a0a524000d000f407601721042c0d81403d0620444818080c1b00c11901c4000442d4009500040d440c01d5074443c502c01000303086103514041254003c40005c00a02c0c0c06114203990201d080074812848034080d500520f50047c85141880703d01c4c0c0741042d41d800c10074450b803024400d07007201c5600100700c904800c8185030105c0e0f0b5880c4e074200c0ba118850107403002540021029a020241d640c00034100d481a03c41541011100345080c0c28000144070f045400c00954209404c1d8044484800c1d009040952010703200180e2203655859580160b0800b0300088440c1120314010061b440c4240581a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 402329523 1250 402328273 402328279
    0x12150a05030a0b0109051f031a01090c05030f0414070f0810021312080702270708010803121024020606040b090106030507020a080313020117010620010b10120506 71
    0x5000b019444001060030141308035081ca80c1c80c0e1000a80400210036804100000311010040c020348900e00f012542892003803030491009108000190701c00030380581c0c0c1140300c483e12203070700d140c48841145001400003082600c0d0f81d4891f000c01c4003008403c000d080001c048030b01800740c2e01030400175214100b0b155003042c900f0060041c03010702c80244c0c42c80c0d01e000444051280c2c00104008500d0810075501800c0c002950040201e924000260341e480803082500ba81c05188110320b40d130704a07080c0d030301d210300303014040e100da0050000d54420f40e0442c8103150450903861480e040b40765289007c1090340c84045822004440250074120700320340401c125030304940201c609020480300790000c20b2403403c051041e4000c244e182c13070200b84400c0c024000c20785903070b40010140303580e032400307108940c0414001082240052080e030500e004890400013460b05030388440c3d50748a07500400c105a468000500e03004411655a1030604150903a500b4585084000c220b46030006401055800b40003124001804240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 402330773 1250 402329523 402329533
    0x31a06071211123112031218060e0d022a09040507030309080601030206071203020d2d052511030c060a060617040b0703180f06181a0c12150a0503 64
    0x44c60481e020241c01e031070800e1490000c003207203400e080b42c6202d05900a034030458a0052650740c4140e078031469204541c09035106000d580c072010391082c1e90b185000c11200040c0c03c40c91480720010501c8412440c030541000c1c141111580300c1c00000c450100c1550115195407040b8800c00c20141c2241000008207500c0c0054069980b4540100301300d031042460040080c1080b40f8509004d80c02941512880001030004010160106030786200c100060503105081c8040c0c0c1001162040a6018040c07041e10000c49140000ca803100d00c3c0d0384180c0011100704140803000001181000b020030181c84080b0000c0000d0000d42400c01e0750208895a682080b020041000f5045071034101c2c40c1c207055003003940460100200c0ea90650210002c040c54a03d003608444030051031030a00c29015002c45240e4050740b0100201d82d1072019074440d00c0c4e120328006007412451b8203030301d14079045090350a6006032009102860075902d4800003404c020116080d0a4010f180748000d8103d09100d0902d001412058000b48 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 402332023 1250 402330773 402330847
    0x3180f07080d0315080102030a0b15070312020304141c081e2403070b0c15010503060412031b0f020d08100b1605070602030a031a0607121112 62
    0x2c1d201c180d8032425a0074144c0741c103c0d0401030400004450014440c1c100215180c0c149820840003410310004503d120350162420780440ea40c030030084500d02a4581c44d900b030700c1c4c08110b40740c601a406c010415a0000003618a00689620500c2443c80e10804591100c1e004010900003610184000e41414009042c0359950380100c02c541e00303880e0300040185d0030048a64064003c01055441e00f2507000c0d0980504000041c00c480281c01900b0400000d106580c40fa202c00c0d10030300c02050f4244152070f4584d204a02007004245078603015940092076203000300781e00c1c0b41c928401540e582802000400210341c40500c1c11056030506c4681404111071611080c1c42c00c2000d003182d5000746038050450004000500d501c0040e00064100c83c01c103a01c0003c1e106029510b00d4041d407280c011780c00d420007107800c0c440032138480791113080781c810100070040080c0d0521031a51a041d45500d09040c1801c140003111910403c400c20400902081d24940b1100903034841004442ea81e9001d0150254685010094102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 402333273 1250 402332023 402332039
    0x8130f0b090d1103030c0307060608060411010c0f0b040b041e020108071124060111010e0a08210901020a17040b0403081017010c110f07031e050303180f07 68
    0x2107004410454682c0d15031209802d044040320f6008441aa15100002c0d9080941c200400640160b82c042e03c2e04010055030307001d00c96262034003210020300c0703000e020606076007030741c0038401c0078200b036000e818030782c400028a5840946680043e0740507100c4001c404108010801c5000c0280022400c042844445d220300e42c0c006040310201400d444140310402040419021007007140c400d950014101703104c0c01600300041440c9442c0b0960b921400940445a042c052a205000d90a4880404001450200030070b0729401c80a03044002c2951090389000142c8250030620054540160004400140c0e9201d05040c040c03e20840d0803080c8100780c1d001c0c02004041400403a010b03034041d41500302010f0343e40d180c0d600ba0841c0d00302034026595a403803990040002c854154014903007a5102e440f80824224040c000503a12003014180040c030f07a10828003480000c00c42c1b01e401d94078069181e568400d540e440e50300c031411900120f0f080b080f0165101d5411a0349101008110b003100750620181459a08040321 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 402334523 1250 402333273 402333277
    0x703080d0c0c022112030c0d110705060109110c370b0105040b061605010504051009122712020406090608071505040f12030306061407060e030d050408130f0b 69
    0xe215446100d4084c0324440003083c80b002d030f9082d02e10008543d40780362030410b4036044c0d04010540e40c0b4291801c2c0818040700b42010444101c1d80e00304c401026075a107001003003006006690850f910f402c1c01803050141401040220650a000001c80503050b03079950703400078030790000b190510031201c00f1054641c408100046080c80c1554415940843c2d504181e40119800d4811084058100e800c101d11140510030f06520150107280f140c0c040d0796054502c2800e00b0f09071041031201030b24001c1d920003401900b07409400c6000d8100701220070311528651700030300000403a10b5540b00e0504880c92001c850110325061058a0207050407030800c001940c2010000380d130b2001d050145140c10101c5029516115000701c1c15100141000221400c20503143c019102107003441507000c40c0481c0c2856000318019003d5107054000054400f8424181003031f94851030b020f01624407a6050324041002210b169040500942d0311413402001d26640d210300910603424840f01d15400f510024518007014003011042c842 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 402335773 1250 402334523 402334549
    0x12040b030a1d0a030206070e010e0f0f09010b1c060b0306090414010207060b010206160e010c021906020606100905010e09190f050a0c020c030d0f110703080d0c0c02 72
    0x14558403070703a0340c0084030020154442d801c038450108400c080116400002e80c040600d1096081e9034564449a80c180c170a6010080828042100482c8100d103e0805034102e102584000307120060046018010680c609d500b038008030544800082d05c020000c0000c07040a0045e10564801c212140c030b0b000e00c1c2d60103404040c00d240e120320715500100302400708a1018502a41a51000315038603402440e0000040c0087e80e0f0301800f5018003c0000d0307985800e096000030006c42034a40441465080c40116038514101c101241d100d10031080d1036484201090a080c050102d540042c036141c20103004210300850312910210820070380c50424001070741d002280f580002c8094400d441103898450410600d801100c180d0b104203454240d00702102e5402d0f03003185000741c000707035010403002c107554104a0f1201286188180c040d44240c003844442d91242c80c0900600110f0325143d00d48400f03904000b030170414141d10903103910324041014540340c84580b003000707038204072800e0800704600c040e0701186034040158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 402337023 1250 402335773 402335789
    0x31204060506060c0111040609060518040e01020f0705060106020c0618010c0204110c100b0d020612090a0210020a03090e0f34030617010606021b030c0d030807111204 73
    0x5004142e86880e40c0094412200304c11000340500540440801e41a07007162044d600090007100000030342e18041c90844968001e2030340d029098102e51001d01000d0100c40a100003259400c0020181c0360f0100d9001c0c1400a1040003e04425450108020726000117200d26500ca048100402d004082c20300d600a440b81e9000c0c201255460300350700014000300103406189044039000201c04e05040e202060307031035811070105020880684004240460022903040080d0000020040d42c1003076441d1140555128031200c007150740150247e8040341a007180c12005070007580c0008503050801d600681d605000d070005e994140b41034940404001d40d17403e00902204100e149000030100300101d5005140c0820000c51442168410800c000500030041440344251801e05081d60340d40030305040c02020704558165004011241c0c0320700a4110844908203515814802c8030010f440c3c036118a00341d52a418080d0f260720b1440c3c03a041d04043d000f00b6040009811176007110041100302c01c11941034509841c081c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 402338129 1106 402337023 402337031
    0x150411010327030302130801060305071a030f07050702181f05040603050c270c07031101140705070302070e01030c060908120d0b1f09050307050303120406 68
    0x1070351440d50062600c01d89000f02e403094029042419003240c00d134100c142d551030b0071400c64079650304c21030b0300342c00c5031504000155200c005102c50341805ca04561440c540141c0f2105c401b01c00802d06070031b00602242c800c066454011012915a601600806007402d00854440c1510281503c2c00c481c2205414040b0b400e041c1806513601312640070004004071450601000320280020b6890780041208038001d00076032828454890054803036034000e540e101d1035410010092444031807280c0c52a03040441c040796002d0302180041d84100d6a1030900c0c0c0310310040c0b904a0070321450b0362101182524500020080c02225030200046070a00d848506409a0b02c05005890703401c0c6541486540c402480061039494454024550325000100401a4a40380f0030407e90340000e050800e20026201e01c04c24406810304122040140030204c0041d4104210220700031188000144010700407529 = true := by decide +kernel

theorem cover : BRFrame.Cov 402158273 402338129 := by
  have h0 := BRFrame.cov_init 402158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 402158273 ≤ n) (h2 : n < 402338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
