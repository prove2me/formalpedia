-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4891
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:04:17.58163+00:00
-- url     : https://prove2.me/submissions/01640444-ae31-4235-8cf2-dd56f3adaf72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 879496402 ≤ n < 879676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 879497652 1250 879496402 879496433
    0x28031209030f090b03010e010504020906071202030304021509091909170d0636110c210421030201240306112d0408010e06090607140706230103 63
    0x3c82c084a562200340e41006800244141d0341100403180045c000e9040c5038026003074044016240c41e0808035231707035035004902485070745100050b0b00c048104401d51602c1d00c0e5500d80c002901c001d003864081100080b03014038034024214000040102030b041c08200700c1d540035a0070380e41c12110410403000c048a16450316481100e006103400c1c00c000c408550b044804184502c01415141104c515a80c44140311081c10305881104082039a50b51510b04415043c40c000d1110003042c00140151060307003040c001354100140e1104d003420600f40405c0c00100c400e2140c0e23034011203060604c200243d02c6846c04a0162240c100207c0c4024000d801c020719002a40e2a4007055a10445061003008840300520300180622030106c0001fa03001e0019080040000c08040d40241c06a41090302c1c00b622150f44a083d03c45d01d60982040340e0101c000c1003140034083c040c1030f411284031318010f000028154602001c40c095080c015040395582c3d000c1c185103604c15616409030b17001c0680070160541e500d00740b40b0458500e018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 879498902 1250 879497652 879497657
    0x1b080f0105010e060103180b1e0c030a05090606060a080405030405150301080c0f0a0326040f060e030f0c060319050a09060f0e121e1902070828031209030f 68
    0x80101d15251b001e0700802d480721003d0260100464401d4848d042204409006288040c0140b0200322600c3c04a009162251103003170119030380c90030010410411100014004001500003000740f0a16584000072100c0b802110328008001d512542400743c1148290b60015a100d0100351030390b0507004020000e1812500b6480035242c03400d03012404e10521030700c0c60543c2580b000c007070142800060741d00000c000084092044070714403504003194950f44d0341e000d608461001c0714003400400160340d0003158050300400640140c20300700380803d55250b40d40594013900703100e4500070001030403003c00501500b04a00381840240038078140780d10604020b00d0184401e40d01c050820224541c3c00f0014000c1d21040d01c40031004080c1c5040c9048620381c030343c00041c0c0c0c00a0695411000c0140601000c0241465046004220450841d2907201902d070152a81c4800b10711340000030641c00c40c07000028003134505103c00d580f110041c911803408890101c0c1c0100f60f10303641803030240340d8010b00d64814000d6040c104a034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 879500152 1250 879498902 879498929
    0x108070605040302060a050c0109020a061d0103150306020a14070303090c0803070b0612030702042405151804061205160617011401110a0b0402150403020108041b080f010501 76
    0x350001c941078070440c000650041d02c20459814000d1046d40200860b8100500025103107050b0386c00130f081c100b8541d2007400003400410803921100341901e10640788aa003400c04020204001c001c1032880c00403480058615640032170440075507402100380361242c1182800c00b42e9200d6203840c1c00381c020210500182c07000c00e0170420100300c2270800021645001d070400c0301075000c0e55500b001c100040e0f5078404000c1c0035020a000e6080180c855000d96100190001401ca804520108400e1072500e01603200d00d1007143c480444001002d4000e003220044035500e030b0365615460060000c00c01a1500d40d10440030003042400303170800e0ac20007103486040c40380d13144040b400869503602d04845a1200c0705461984c81c08140c0100103c0720802d0885072040ba042c18186011004059481c1c1000c04015050701c048080c2810807046261075015040031840358040c141c103250542d00020122607000307000800300340359449134050b10480c1365001c0c0014409042184e02014042c444c05029010a1050740300355060b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 879501402 1250 879500152 879500159
    0x3010605090a1b050f030f06031006090e010b010306030308040f020609130b040e01020c0705091312090314190b060d05012d060e130804051f02101401050f010e1206010807 75
    0xc000700c850340c04841030440c6c150340700c411050462107005481a9850300c45c903555292524514010500206041e42c00007825060080d44030f82542e064103401c90404d4600b040c28400250008200d0703411541000f102c00d000c0352a4070126512348510035540364086054035480c0d0000c2d030030b50050148403400341ca080c80701c9810405883c1c00d13801002140c003800d801886090199040220481d544a04c0b03021006407051000d8a80600b032100400c65900020300320b85080c820b020404084044c4280d44e64010944104100030804407a003980d45d00802c0d41c4190004610b05542b41c412810b02c0310b8101000700718018061149803100c03d003032460000f0328101c901e0514040a00c5106c0d190483c1e10420542800350340f00c00c50910410300480301151104030030300006c601500d500c1d490180091100885088540070038202030300d000121308201c4031960621031842d14802c0040304c00c904554096034170280688040c00180d0b01540c11060540c0c0080f02c48015020070300d0002282c41c121400710050f40d51040c1c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 879502652 1250 879501402 879501407
    0x30c14090f0a020a05090406080d02250605071b06020102030118050603030a08041b12020406140f1201110706090b0603070b27030d02100609021309090203010605090a1b 74
    0xe044446210314040280020320000c040c0d001058180024940145084079143c00182102d1003500808101e40c0b021060700d10325901048500d00c001400902d080300b00c2c0100211070344840b079a000d110100180400d401040101841c0146406040401c40c02c0c0125202c0d04001d0003074009104450703414910a00c080c0702004644a0540200d01c00380c0a1403404020100c01c5d1026540070304100e4441840d80c402150941c00031400201404c480034440c1c411451500410040d02e006400070125280b120350803440d04c2da200e080f07050754540b06984c209194010511710a00620941c0006546804005412000c000003030340103550b02403040e013032262503031240810306640b60f1450041684148040000712065503216000801c454400ca0b0280481da80032004603041c61281c03500540545d00c182d07040c51441c6824000c080c040e1544c80700c02c605240c038929208080b19a039101d688419a5a000040b0a40d01c0a4001801611020f05401190705100c45144001c1c6683e04001c00d445840b448030344425403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 879503902 1250 879502652 879502669
    0x1e0b120a0f030c050d110d0801080c15190c020a0b031003031101090f0f05060a050606070803090708060c0d0e0c0d0b0601030609110405360a0e0106030c14 68
    0x254500028000010903070340311549010850420b500b400841c840940008004005802d0440260303a9540464081099010303e0003d50f0852102031003070340c0d4014040003400003040051050225691001e540d008010014244079114800340c3c401481000d225503da0002d0340c540710036100307032075000c8141c3d81d598501d9000c0c0402e0741c0f623140c030250350302040001c02d20400010402e015800000600100b450780e600032011050350080f54146a00f804210500005115803503002e0650a400d00c500d15013100055094805c20f00700400071013020000c04c0d4003030310802140c0040d11401044420505200005032266001070a003030307204c40d0a080d54000c0b00756002c00d00300c92200001d400d110214089a82c1c040381c001e80140010f040540d80e000009002c0c4203030003411000b8001c03818540c0c4e2141010b0a02000340a0103604a603400da13001004404c000c2000004102400d00030000e00440d112841500054822000000002c0d030a0070341c0481030050207107201c412a140140c1403070441001006019030f45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 879505152 1250 879503902 879503929
    0x15030705031e100f1203211b080604140f1603090b07020609061807090207210302030105040c091a03040c030b0c04151d06090d020402030a02090f03060405100c09091e0b 74
    0x4807a8a00081c00c0d60703905800411861f0801c0c40450400d04014000702c4030110092140b001541076002c1c0461410305104080040c41c0f145864040d500e805010542260b2003d4411412031303407100c0307400c040c031840703644884c688a62200d1080310701e0815100080d075035201036481410714065000802c0740300203550603142844402c40060000a031400c83d4580081d041041c09590701c43d8000b550210034601c0e40b802d143c0600c49078130016180c0d41000248012682681050ba0a0000c4d581c414000d100d4505011000e203901d0040d01c40d900d5640c1d26120490511660004100fa0150002d04c81ca501400000d48240c2e422000c05038101d241580048170032201090030f150448030981ca00708540d050100003402d048030050003003000c2ca000341d400b00741203910480b07000b662a030b400700da2908076140c030200c1d4184d110030440013001581021744039680caa91486c000d040c08240c0d01c04404a417140110714110041002c3d038404c000d03240c0c050030103103003261200300702440092a10f0411a4603107410302d5041c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 879506402 1250 879505152 879505157
    0x11404030918140a0c030f09080306060906190f230a0c030207270c020102070305030109090507120f0b061906030b12070b0a0e15030705031e100f1203 66
    0x9460180c00c98040c1c0c805494000c03003151600303490b29035500100207803030103090700c04e100003a00c00c01e804005085030084241000c440c1d061007440c0e004120a041501c0e0000400c807902941c40340d00e103000400a100d101659405ca0740d01284210a15401c000c24180340451600d54800e103400c6440309443c09010105074411340d070f40901100102902c90340740c08109074840d0049580701ca071141c540c8103641004800104440c580301c500003e12150380d0007401056031990009509010040c1d07000f40c1980014010015410340c0d07610b8110a20108021040c01081136060041c000b449a00b0001b030341c4443e8540541c0e4414640004c5000343c00d000308400090b01c042c0d06c0741d042d01403e20004070082d061444034158042c003440030318841d200b0705024080c002c041102416645041140c0c019000343c1c40c451f2150700ca08032040080540420660880354003010034505560f82c0e6070781c1210b1448075a20300140e0700444400104201584c2440012041561085034042003030a81d1403030801e0700c111102000400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 879507652 1250 879506402 879506417
    0x7050301030f0525061205060102070320060a030902030c1e0103091b0b04080d0f17072d020709050402280b0d020904050702010c14250605010801140403 67
    0x420300b20700d40840c04510031010384440e201001d40319008450503640c2c070b09020107a01020401c8582040c2c1c20014000c2e0b0000600c102d182c9900041e4684509100140c44000402106280030b00000d14a401c51000140074031b480b5200c42800800801c1c1e0702d04202d01900c0b5280f40d00d00e0910f800801c4002a102082e03200001580300c900440c041c11381c002e0100c4008a03150200c00310380c0740c80d40d05c00c0d0180c01e40e4490261950b14100b0010b02d001007010b00d110a100103a502e0742843e03036102c1c410139441c004a0b94001101d4986040c00c03164048042c0000f20f0441c1c040a040c030202d0900c000d40e20b040301159084840c0152120598403c54405880003540140301045c00410014000c001813010000e114441203000d40e00d5071210720383d510580d00c820050b0341c0001c12942516003441915040780e01c5d403000f00406000280054002c949040b00b00c2e60a80c00892580741c00c1c00070014819506500c0c1c03641481d64550b601d0080003401c028000d08085500700b200c01d0400c0556620a503101c0c030780554400d070703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 879508902 1250 879507652 879507659
    0x11010c2604022107030c030506040203061f0b1c1a03010c09050f0f0a0509090303040b010609030822050301020409020904060b36040603030e0f0603090d050f090405040b0a06050907050301 82
    0x10643c110003001ca038004c003040000070a0b00e50740b45400443c001ca025040034034040c130405040500080c2070080081070001d054090062030170f0000f06036100000300365640c1400f540030909400f09a0b203202c22490905c9461307441585c0541451f24902420b070003d100401c2900e8040d12281d074140211600406085110710041c03510304000004030b0790107030401d2243d644600c0810080041220071031403d80c400002d1200f04148441d80768014606841e00072043c44c2580e8a400380d80c4140c0896060711581401e400006124a10b0b01c00001e050040c000c650b00d580d44d88601c0301a402c4644100c0c8101d00c2c00300700144a14030981184c2c2d84042d541e034203001c00701c1b60f1104241d0082c000201e074100c1111a101401d403540310b0b4801c11011358040e403130381c40c0b51580725003c00c400141c000c00742034007801081c401c0c461051400034503484501c0d02c50422b00e4542c0050700c03039441c1c64040c0c0003030380e54400c2c240000d21040c0101043c54500464441c1e509122850f1680306008502d2401e40721680010801c00040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 879510152 1250 879508902 879508939
    0x1203090f0103110408030a050309060c090d030e0103110c0f060903040302010917190b160f0909090f0203010f0e1c12050c070c060f0e01021504110111010c260402 71
    0x907008120152009414079407605586403a60304540d87c03c0000c21800414442c210302c0c01c0003115449050551854644031914000c1514252014001410300103101c41d4402c042e8060341110340c0d0007004041281d00c1325084207015548184c2408030b0101070040394040307000702c0c1000c4100e80c152a01a110410b09501e800401c14040301e2900c1c01c441030340a01116a030400f4404280c0c8a420790184c036504505003441c01c101410380c1441012503050107000614070403c5034102200c1011660910300011b00c220050030a41118141054020340c5075280100d407142015890384540a1101d840c011604041124038034103018410407601c40000c034142403072041140304690031841d446005000900e04100b0302d1381d142c04e840000745e0003000203c2c46101000151a91101d0001e0b44003000344001c02c0740c80702041e0200c1c015030014201030070850705d1031aa09810390003420394001c80034450000300030034901a00000d040c0c812003000b85140c01d200c54400c1d08149000c008040c0030355002009141e60f031040c10075a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 879511402 1250 879510152 879510161
    0xc130e13080304140105190c0309020904020f04020408120414060309100c03110c060702010c09180b010e190f0509070503070c0203190c05090a0509120d020412030507021203090f0103 80
    0x440c1c0c0400201e2050030b8219080c050140039180f00043c900000c2040c0100c04107448c07070078001c6020103142001c840d0160352100ea100c1d81058065a01040324118000807902a11658006900c1d078030420b45030100e04480c100091080351840080d0f42c00318420701d0200030a034030065594141d95405038070b1414026926911550f1000c485041c006071264980c40c06035029040b011a103401a00200c041000558080c01111402c1465181240c801400c241d0383c06d00503d002003000484d1592409a280143d015100c50140d0450041ca100c4d503c50381c6401d06074020401c0d000f0500c0d800130040d000540b6003484c03815940910b8190711414210381c2c400300c0445003192010001d907414421554000066581e40304214240740c00782280484060400c0d060020010010389207000b02031500c02000749002d000716040c200400201015a5250414000368010380201d130030010007258410070784400c0542103402403041601c26500802c9070815035001540703c0c040d0070f60381508121307001d100c07114640c0309a02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 879512652 1250 879511402 879511411
    0x60a0f031a090106030b13030909050118020708070c032402210415230c1806180a060f0809211b25080f0c1302070203060c130e130803 59
    0x13a900e5501c0e00d031080402d009848400d10303040701700540000d0542c0045000b0280c00c19003014401545081e03098420101185408422503078045841400c00c045001102c0720b158002c910f0840503926030400611605501030b20a20b030191003116030f100032080d0b009840101c4c160740758804090f08104e20714415148000d0045501000c100c4080d21200c04600c6400100200ea9507402c0000c0c80e4134461096928005e48001c0e03580c0814401c20740004007011404034440004d40c3e4061f112200d14104c40d40501c500d01d216a84071460036004902a07a00c1321700c1c03001250302c6070b0790f03a410b540b154924652540c800e1208041004030750b1403031381c1c1c2182ca00c0e0b000300711040c0e1415403400c01c0d03806000c0b03080c108a00844030b5041425200b40054041c080030a5600c0074003c0700d0050308c0010500100b16a4403c2c000310000c0c0a044200c14070b171084c0c2070b550306941c041c0303030003405503030491400c42040b04081d4483c04c00b40c07204040341c402c0816022400150a8403c104562070f1010048840d212103074507801c000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 879513902 1250 879512652 879512671
    0x50708072102120309030604080408010606020f070b0c0732010512010b03180105100f05191a0d0e0d1101110904180c0f060320031f1d060a0f031a 64
    0x800e00a0f603c0c1049524031482c040c030100c54807142880c282d2400c1d80e0dd103234008411540b0994031118243c0c03002c14040101c68107820529a1405c1c11010346003807542c158085000071684030750140b540300d02c000b1840461802c840942100b000140c1c010341e0103000b03030303042c000c0e103041c00000500031210400000c50304500402c074031581e10610b01d0400c1e030940314101c940040d403000e18401040b01c0410310f0141e1000d0320003100c003c110309012400c0b0001c004164072074074034070391006c00b0001e00c40328642040300c03409240c1080501000f40c083e07070301590328000800c103400000e0190522a031141710601c6003100c1903115506003850a2290070421001d042c60080182c0310140030703141c84000844ea840c2c680000c10000d454950414903010014003100c0e05010818000d0003182050301d4404650001c4070f134800a4480e045906000841c1d1101c5100202c4e0407201c55034031022200714002051102982c07260701300311060501181c8809040342121224403004118060410a2401c0c00801c1140640d1005115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 879515152 1250 879513902 879513907
    0x91005100f080a0b07030b010503041e06140f0a0c1407080d02120406050708040c030f140d0203040311150a140d0204030f02042d0c0e0d0507080721021203 68
    0x44400d00c4190000350700000c03140c3c2c01002c01d80100940c0000441c0c3c4080d8600302040740b81e48800019141c0c1c4070080004000f43c000c030340d654070358003034500085074602c0c0c00c410100003000800540c0c14007248241c540303403425010b01e00002c45101c200d010b80060f40d2420780d1801d140585105001c1600e401c0440c080b203003070205011461040c0c0d45440501402010000c4c018054101410044100c40c0c000d01003500708441c132801c01c03000c10b400c4400701044940c00450342c00b141023141811100d2510101043c0c16502881c8075000300682c1c00405441070704c1c002c110940c1e100e1804000c20081c07074000041d03440c000500740001c2c61100e00a040c0c40c4206400550442d20f840e6603041c41c0ba08aa101350130448542c0b80b44207802087d410709101d500c1d05111011b10740040c2d025400b010030f440018080c68418a6034452074040002d40c89051441c1c0c6d8100040c100b11080456854003513144e0890b40070740c1c00306110300c0d18001220b501c9003850040c03500c18120088036101c501d40a1120104c00d015040a452004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 879516402 1250 879515152 879515159
    0x31c020405121c180509180d03330501110a060e0601031a060d12020a0204150e1f060c020103090b0a05100506090612100b0309010203040c0e09100510 66
    0x2030b1011448100819400ba2200c0c510076403015821000340d40d11401040140c10b84000c0110003503102d801921000c6550009075903804076007803014035007030000607610b0041c06500d0108603010b4102540074000440502c000c1203481d17000d110850417066211064503560308003002554081d0503015403005012065505800c00c94440e42d00b03465215a44070320341da01c07000040040c42041c4030b4401e40c0241303c0c00c209202d810184002118000c075050080d189000010503150303004d00810903165001c1d030142c02440303c4511074449815281c4d562060b240a00027180001e10328081007541801451070180e01d0b1401d090504500310740920148030100d06155469108101088589a8503803140c40c5402c0d01248500c2d0881840b070144071190310041c014141407040c5031650395803505403505204242050340036951044101d1914000a80c08070403240c40010030701c440d01d41d064004503c5035005410b44907140b80e480b8079450544038101c5d0301801035004a01b4002103400c140c1c0041341c21001c2d145030540314584 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 879517652 1250 879516402 879516409
    0x1005090d1d01020307051e01050c090105030a0c051c1a0f0a120206040e0c0a02010e030c0705010e060702040912110a1104021b07140102010e0703080f0f22091d031c020405 75
    0x3050388601e200340f68603210b4800707419009d0007226030010240b249941800c86034400a0b0803400701400d0184c5072a2101142c1142c544510281c50600250403002e10385094903c02c2c00d0000c2609034041c0c0390f14030a04400c0009400c16005041c0c414902a01c0e0121583c030b45100c0780c50081e04281c0499025204201c00600400c85414880c001e600980b50702e59500c03c81030b00603084481e100c1e80c07181d07280c0052005240350f000200c1c08200312071003801c1c80c2c00b04143c1600004d01030300c035403a0000c0d801490030100b0800d0103031106400c6078036040e58440e40c0d4425841180240d447c4208100100a8038100c968040706013055005800d02ea1100e400c0c1c15a0f1030a401082410038505821000c07a01d4929001c2d822650303424000d0500d84000c02d00a00740240c00c2d500d076445240309a00400c007103400300044c41c4040ea1180b00c1280e070552030220707109006650500c60114844103034400d17699510304018991355542803004043d4090403200c0010361401c81c44004940c2c2452410072200e0ae60b945c24040041e0a85 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 879518902 1250 879517652 879517663
    0x703080d15091b0305040b13210801050114042102030f150604110408030a180b031f27051e0408070b07210510171005090d1d0102030705 60
    0x600400d0116040e1640d03c0e0b404510080c4a16900800d4100818400401c2044403015048a140e01258681c450309040403d409000a0850480c0f00d50000c0000f032820b611004d401e040c1d420036a5210700b07903211034400078024091401400109002038003a19584c0c0010304088803010300c082c095440d02d9446224860500c140e0420b14000b80d06544200300031803a052203010080c1180710b510a00301030800074003079070b82e0048610000501402c0101072000f041c0105100e0020320b041050180d413841e014840e05a41c02c2511040303180c100101c50003051050075080c480c4040c04081c5031b144082c0308084040805410082c012440d0b0b0b6550344240b001480203040d9441c85203006141441d65840e46142c5809154030007030085042150454101103074031080198610b03468422030b400724507a10381ca02c2040d00b4082e5a0311200340b900d51032a080300301550110f102d540e1420004020402555101c220f00d488000c3c0048044c00180140c2c206180714030b12041040c610300c3e040c8100c07406c1880a9551600e000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 879520152 1250 879518902 879518909
    0x6090601110a032a0f020609210c0f010c12030f0e030a051306110a030302071a01140a0e0c0405040203180d0503010f0b04031709041116061404050703080d15 69
    0x451800540220101c0f50040c0481c2400e100c40d440313945501ca48a2982102c95410000d209401c0094010030b1961003d5140ca02c88010305007100c42d8140c0114201d07998250b0002a500803454900c025510b036004e65800103581e50001860911a1103003d01100240030b84c45018152a80c0d07204200702400c0204007a201b02003180d12199074404540c0c110720454045544260204070202e948414180000305810703503101d60506000d84c0b40c51040c07030844101000f404410141c1c80c2d0703c1000240d622901c40e0000c54807042520070506c002d455248041224004607828046d444081200700150b00b0150300850340501c0310908000303001000707601e2504100d40034010750000780d070210050001d10031a5200000520715015445e140524503a180e203a50060a40e10784600340c408507a0000a8072240c02600038450a8050f0b69a100c0148205090743c2e11550002c7c2c44240c90725841c801528503800386076000b2600f0500504035540741d0381e45c02c9165805145217140003600d900c2c14040c052140320605025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 879521402 1250 879520152 879520157
    0x9020a2703020f03010209060703050f090915090f0907050d15140103120c0201141b1002030718050f060915040b180306132a0902040e070f0806090601110a03 69
    0x10351a60041103010080400ea55100380d104108840c41d558480044070341a540c107040c120b4440d142c03020a0032190150f460415004219602000700c10103884410a1000c0000c80d0070561944614013140184030b011134441455030f01030a030038081494091003d802c841c3c418000501c181001e0410f01c801e54200c01d45460840c0402d200500400c164100340c800400703c2841c01c0800360b65141c000078600310a03800c1400340c1000001e01e8400e03e82c402900c840c15110f607d01114020b90294011800940c0210303807460006035a06041c1a140c1030090b80f480454070010100300c41e5051f440100f0210780e02000740703541e00201100041c2c901344007000141000f490341d00043c603140c00040c50300340103000c0c8000c4418800d4026100700b10030524541008032000d41c110125a03030400602d640d002c2d041c0c000ea0301302c5800003d42c10001030703155001d8004009a07102ca44191400e0744414200b6505a5044041440801c0314035000a074242002c2002ca075000c441407512144c4504a00c01c10350802e550940140c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 879522652 1250 879521402 879521477
    0xf0108100f0b030601111204091e0e10182301021201170d0f1b0303020c030d091703040203071802040f15090b0408030a030e01140906040b090a0c09020a 67
    0x40d81c103e02106d159251100140140310030b40602c0c0c43c881d1013240200200c99507120030300c00c00b0305a01c01c41305e408041c850341c00f00810038400001c1a524415440e041d02203504100401007030041c41d00c08179a0240e1f00c01c001209904542c1c41d410650100140e140900e03640c00d0002c011010740039040b5034020700d100000400b40c84d51030880b0700d0409240b000280148900049040312080e0321480790907074005212807010100c4903e1034228040d21030301210340010710010030100c0040d62241c0c0004441d80c8640c000c1c2e254541d04103003007030b0309010403034002e03500da040f00104000703014007943c2084109100c0c8000500e4281c07298050110400290001c0b05c00b07034440704204007520b0f08200a030001d40244192141068a4051060381d02c1c8110712800080607280c005104407550250812030310107000341c1c1c2c81765152038510030791a603c03607044a0a4822003414804502400b00126454200d0740c8c0083c44c206a00e0308241020008e1342c0042ca0740b40400800b445043c8611403c41302d0000c20300107040180c038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 879523902 1250 879522652 879522661
    0x30a02090a153c18261203130f1a19060b091012050405010b03070905060117061f0e03160b190c05010e010b09090a020f0108100f0b03 59
    0x3880b100074051940744080440c080024140355200020034900c1c06107182120503200841c00301d5070041a00314010050701c40c900701040007070001c0c504514540c03009200c1000045001c0d000c1c2c3d40ca0741a8010421082410800300e541c0711142e0a02882c074a009d12200c03c0c60500310f0b520301c41d40009546500481840200c14800708c40002c00c150751079106880014465142446031112840c03040702007417449880c02c080700e554014015100c0d500302e04a0124208482c0c9454241180640090034019109005210001c030708072000f48a140c7c000c44040e0755101c04000782ca400c14003000c5010b80480d610407600503200c518412084000d80e041c822643d07600022100c40070507d40340c41900d44200418610010b03080c084805610b06507030344000c0c0402d000010103501c2c00152203040500e84040c14550a10400d800e101d101504260800041595855030940d038020b102600d40c0680d4100961100442d031600e06107610507860203400210304001c58442903909c080b1541c20300d4040d44410107005002c001c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 879525152 1250 879523902 879523907
    0x90201030f0509151906090606090f060c06020a090b16020109080a0b1501030b19080c092802090406030605060a060c170d0b06040303030515031c05030a02090a15 71
    0x4001a0041d032814096400c280100c162134400c0c512020742a40040000110b000300c10710700c15281450291010416991a1024400505040d0140c21301060107160001180220100048203d036802d6640000c0c880c40d50b1780b4940039500c41c030400010130851035004140114500d00920305209069541d26450089100240120116610171041cdc0d800442a550218001c11080342d80518104030f0f151070362040d0320050300140180c1c4202c98101c60700d110b003010740c04000c0c0c083c0d90590b46820f00320b40200c204d020070040004001c50b0022869200915a04405024600c41a9420210480c05030814002c0404141181d48907402500c0c2d2544490511500d800e00c00710784806045549412450fa101c3e64072071010400852800401b412000202c40190600710792001d00c500000a02d40c0d80c0c1d4640d6400d000b000f802c4203403284a15020611105100e5150008464104030345a0340c0c52166101d1400d41998103400c0180b0319a07170f0766000c000c46901507a694050002900c41041e403481d41070792101d0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 879526402 1250 879525152 879525161
    0x16030504052101110301150e12030406081b13140d080c0304030c12050d0807021501140103050a0905100f090203010f0207140303070903080f0c010f0c1404050604050d0c030f0609020103 81
    0x1400322202d130810052116003141c0c00c3e0746000412034100701c045207450130701040d0300c1d0148a083e12018040400e000c1029580321951034040e020100c0642d000349120140d04a10744240b80075002001e404c01020089413418030140440703a04010500c0c11034442d1501e034109698407440020b866604001001e20030030041c040148083c00780705842c0b03034042d00d46aa44542e40e903480514042480380c103200050307c25208004c2c2d07030322911285e1400402542d480e22100e01061031094110b021a04060024840b00c0b054400c45a2554021000303048051600c410040140b210300826480300d074841c01c001c000742c0c40034052202d00051780d402c010380e10412801d21400301d641c0c8055080144c2c00030070a00c0103040c2e200c910030090f25042500c0c5a51069602d0b40320220344a0904c024a095080c00340200b0b4203074042e806000c0e00c6030103803903400381040540b4248860f403007107008140d4445010f100501140c203040d101a18450f100d1003604c2d491644985905002d010480001c88a00d5140c0840c6411540d040c010b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 879527652 1250 879526402 879526421
    0x6030312060b042303030415020604210c11120129090f0a0b1c0c0e0c272719050601020a020d15150518010b16030504052101 55
    0x2407143c02c1c03d08003074000d550704015094a81c0700c24420b0401042070b9030240704a500518800440c04540d1400300c1003c1d40b10340b0112002e0b2040711210400381988071501668000301004ca5643c8044030a403903132003414003a03642d42c0c03081e0000e079101e82110081d4003d00c00d6120030600c080c0c04200d008002c80900c020316002400c1c23036016504900034400ca4030303c1c1c074134642d402082e902008a0700840d030302c000c9aa00c1c003000c1d018143c0003840346509810b01000240040560703926840511041c1c0d540310100040b84514105000314116152030300c03080f03440c90400055100001410009100008000c13000080c1c803002c450100e07040080c0034880c4002012040f800512007961b1f00344294500140041d4903601117000282c0102280c0d00030001b084400c1109940f01c0403865000c1105401c000c0781110901018005c69000d45080002580c80c4d400300481c0ca0f0488080042107031812a88081c40e4410101040c1c044050100c10b00003c500703039946001030118015050404807400c1825030402c0d0030b5520403003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 879528902 1250 879527652 879527669
    0x151b0c060b030c1807020102070b0c07120201050c0d090510060b18150d181e02120609060c070c0308030a020309190302100e0f0a111e09010e09010f0603031206 70
    0x2100c43c1500d03100c00700c26000030201002c1d41e510940ea05803042c0c0c068850075100500b0300006004001c0c90400d11000791020901461a54440500d10041a8201d50042c0c4181e041e91505100d100c901c410160041c0c4020351041c401c3e80c5030048104c0b2200c098078926003200200748030102d4100c41254000100c00e080410484041d0717211500102c03001014030a0681c9071811a4451600b04c20741a81d8619505000d50b000d092041c0c514100030481c140003007106022481400c0568581d1112400003a0503405814250054250f6440703040340801113a11811007281c090301402130010202c0d000b0030185102d94030084015940c0d1500102480c100303030302000079040913040b04a078400800c3c0e00050110b204540d49200150400581d4141c41c81e0141000c0d440c4418801c0c00061380c100315044a051707159041c1916404070f445100640711516485a03c80c860304281d0060041018001c080d51b1541c015a180000043c4441c81080c503a003580c84a0300182c001c14401810050340d41303068400d9200410201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 879530152 1250 879528902 879528913
    0x3080a274a0f06300703030305091228021009060507140703080115090302040612061506050316110a0c03020102070807051e1216031505090307151b0c060b03 69
    0x1000007913282c1c4140c04620310302d066050b030031200910200c0540d1414100c1c0004480c1c100b81e6034940100501800c42c0d2044c4680a9003011900d60780032041a501c15820202440b030300c1c00c041c0c0888100c0c081d4451114421481106482c0034409000d100c0c400303a85000300c2000c40d41745001c4c10302400c0704003c0b0340680c0041e50f08000400c0466440318401d070645480303079042d0000e82c02d42481203c05100d980c1001e54014682400001d140203100608080c040c031810301403200d80e0080d0560748407107840c1d02c108804540c0400000310004a16900f1941b15061030401100201d8040e402516243ca108405c0300c02c072080c0c12040c015580c04109000c0100b02c541300412801e41801c0c0481c003c0445000100e4680c0080109500d41d6500c2c0d12a03a1842001401201c02ca09921b44450304180140c0c881520480f503a0304018030300394014042c1901c500b0341640110b240400503610340041c07044215110306903a545100102101c0c2c3c1071000d000a0301c18607a10b024010b206800d115088079840c00c10740340700e80d01c41d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 879531402 1250 879530152 879530161
    0x5030c0f090402010309032601050a0b07020a0902032d0a0f0e070e040213141504020a08060d050c04230109060503060106230403080a274a0f 62
    0x10050711560003942071a000c168982c0c0c5150039500ca0180815545051104000c0d0640050065000e00d041314012a6403440300f03640c0c1c003c4a10303142b05015000c2d411190088007801403103a190002c58002511758840400350305282c00f01d00d0440d40b10000c0c110540d0500d4140b10705500140a2000d0142c4448001c004605009590581c2c46c0751500c610502a03044900003020356561151500042000311014003003442c182036982a100000c50720402d1079800060342005c80e081a100b50340c10000542c4410180342c50300400c101c1a40a6482c0c21a041d01c00c884044541d40c07107901960400000b034103024841303501c0320a0b21698440341600000c806a1804500f00540e80d00000d00c1411104c40c7c0c01c0203800c95805068142d020030506c1c118295001001400004000700f20004050444041d5201c4404c2c8841d5002400440d4030b070001400001c00540082c400d40007054030000f50b03808149044403008040004400b0300140c004285103080d6001031086241103030f500c491035030100c0c280c00d004032189007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 879532652 1250 879531402 879531409
    0x402090a0605100e010e2e020d02102a02010f061205030301120305070f030513241101091e1101020604050604031b39060203070b040320010605030c0f 66
    0x6020501c2810800040b007801c00d01c5e4052512a100500064150401e0340301c2c1281307100d45150101d00543c11001e030074031910360a074030125038011041c4990380a0806c0000048440700601200c080182c0301004c2200b100c4e21601c608a00c15122545c1500041440301442c2c1e054812a0040da0200c42c031040045200c074005003002c012030707054071040300da005041c2c3c4041c10304030303283d01403428020082d007900900c040900da00503015007120361b02135102d203012640b40c1e8400c0360503083c0302c01c0202c180183e00040310846801521380049004c15180002007285c42c0340c44a00a9000c6d40b0303014607090f0304001a800a124040c0c01801d8400030a0008043c80d080556600d03035215002007000d81081050306c91014904041d50000c900a904610543c01c00149602c2d80e42c00000b000c5480d070103c0c80403042180d803216009401c002190740f260040c0d4100030301c50710750510040c0d0080089040045041444141c21203158001c1c000c14103070400003c0507424102858a40000c5114042c419241003030a0380c503e80d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 879533902 1250 879532652 879532669
    0x1a131104050d0c170609120c1b0112063201080c070f06060303020105062d040908161b0603090804051e03030c10050c0c0d27030602030402090a0605 65
    0x1001075804000c0c282190803e104042107642004041618024101c582d800f400200c81d8000c8080701e06440c81c2d40b0707201c91107014501c200114a003440d04044411a844640d0a030107280007401810030004c050303110500c0004641c501e4021b84400c8940c220304c001c0034001c000005034102005440345001c0c1c003ca500281150200a2019070303c0c0800151070000c003d1000c030303603644c140c0e40a4400d0242d1903c9141c0070307003c0c040807100c80e801100c0042d0520385030402001803007650784446960002c40314088060002801001c04190ba000b041000561915800b00030714081c0c5d180100c150030034007003e81c80140032a410302d51201c400c0600701410f030310100301c040b0304507811508112401d242e540c060500360320b0345006010380654980804124100c2d00c2c9404121040d800104400c200000d6032051403060f050f01a1002c0c180407607002007040800a0b025203004640000309608030400114400d11010f0040300503001190943e070040140011030030000d0910f07407c5036007600d040c40040d0804d40800c8905 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 879535152 1250 879533902 879533909
    0x515010c03020c031c18061e03020d02210907030c051513031a010b0406080a1a100503060f06120a090201020703050f2109030a24050411010906020a050a241a131104 72
    0x32300010503540c81c124005d80c12141c4155020109540340e61070300c0000b2180304080b264517040c2d4940c00c1c0002d0070006c004120350054036808040c01c10124200000e111110b45001000c000d402d4041004940810500ca450320003940300384481412140b45503c20201c07802b040c0e120450075102480140038250708941501e40c0000d4082d4001282100d50309019009504941d4168020b0300300b02c400115113074024000c51003100c0a8030418007100c000c10a03c00320307202d0032406140440b0b5400115142c0b400c40d42141d0403c41c01403040381c06242d02c9494941c10b2012045044080303502481c00b00010f88882015031292014101c442c60500703140501181c0c0b1510481001810f149427064041d0700f01d8104030749411700b507000417000c020624061814a07049a0503c42d10f9020131024400090400c1c0300043d011802548040607000c641d0381542c50f20103400003000340581c0710b480300b04c40020005452269180c245070076004008602240403d03ca0520f400c46034075010f8604100d0040002203104007200c0c101d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 879536402 1250 879535152 879535187
    0x31d0307050d0804050d500414060705010902090109020705060709030203031903061214010f050c04090203070504050405070302070308062d03010204030f1b05040515010c03020c031c1806 82
    0x200b14607050140906403c1c047c101d142400196441072074080048007007002c006800280524103119400c0c11410f40618400c05a680324130040d4400305d0304040303004e404454840c4001007405a0250300080056009800c81d4105aa01041c00e0062183c100503458028095081103c03200d401d540120343c8a01c240061410100c01031000c045000f4800d500c040300810a40f1074070b051841c0f503841c0c154441c0000f0445901c0070741c00c081207100351a03140d01c80c0c03074003440a042c0c695150603d8540248040d4000030304231014440140000115500c0710701955228400702c0d07070010781d5458285409029201c010341014003d08040e00d940c5003041007a8000360482100c030020900325140c40c800039019204680004081d0619590800100a49480c40d150f00300e0300403a110034556242c40a000468404442c0c0e600000300070f411064803035000c0d0041c60b08042c043d10640c2d403a880030001003442c1c0361000d2140f51451401c594140b82099128503807002d02e02480c240c1f07100381440e24030001c00030980800460f03e03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 879537652 1250 879536402 879536417
    0x12161a040509270c0102100b090105130e071403061003051207170a090f150e010806132412020904021908060a1b110d050a031d0307050d0804050d 64
    0x183d0b024a50014000ca0004802e4400f041c1807003540e4540301d001109015000d44030795010035102c806540103442d0304202c040c00d500c0060b844d25042000c0c4510341c04019001d80d03520740d905001202c0c14441280035211740458140b150300340100b41481c0c5003009001c8d801d11032007140c1c1840001c4c0040b0b0300c07614444021203003d0312007816003000200040d0341e0818240c8100c0002d11551500e4000b40c0101c221a80b0a0400900759642c0b140701c0002c81c90720a8590009001a80700d0000390b004a02c010b4004902820320005c2155030401c034000c46228031000324841c0e20002c140f0144403015119580030b0b117040c1c880b0754541616607000c201c0d5400d001e803000b4812041602c40d5514909c056243c01e000304056411103c0700e082500400b001440096074802c0000c0c255904414464000c00c4459624124580100b861204c0c3e80800c544680042c41c643d0b04058071140f01c00c3c240c490402d00c42009280d0384010310707659020351401d00d240020600401c000c0c801000d08200104801241c0d8040d01456400d00c80e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 879538902 1250 879537652 879537661
    0x602010b0d0b06030c180708070801081903031b0306030b0601051c0c11030a080f010506030103030c12091211090703050f0f06010c0c06020c130e1f0b12161a040509 72
    0x17030a01403d180030a41054250b6090565003102401b00c5000d40350503207511925483e200e408855030182401095066408210040c0d038503500c40c0214024907000b0b140000c2e40c0c00e0200e08002e950f100d8101008002500c0344418418059002403061308010300b400c10914201d1a41c10b02d032201e80d902c198135001190740308000e13085036000e6034080b00301e10340d280d069994032070a88030060305004007514244075915003200081958184072040724140d0750141c90700303401017106680d208200c50001c6081010002d039404005103107590080c503078030030502c42d014a02d40112810b0030f2103400c0500034809020981803400b0302c11001000007051717800c11410b0b8040e0126640c0d43e0010384075600711040042000255000c0010400d501084054180400302c480400d00304007001407605803115550b01a509401101c0e8210100d00b16000301d89000410f000c0100f4955140000244068203405944003242c000398601c3d0303201c24046a00c10050b1141c1d00c070021004e0302140c040c1900380287d00a090042000c00c0119 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879540152 1250 879538902 879538909
    0x30606200a0f140106060507150b0301060f09061e0501050403030f02070b030c04091a0f01030b0a03020d050304151107060f0c0605100614032419120c0602010b0d0b06 73
    0x140300c082c1c0211610a0303104091626000d03c51003200300c070314554603050005c50424413a0080f208220340111800c50302e04821030712000200700803000c45600d0b41d669140018a01c19201d2040c0c010320681c180080d80e03a182807003084500d08040c00001080303200403002d0103160b801c503040e00c065035050701d4441d10540c50260b0903841c160040e000800c0400001c42007101503134a10700148166080800140b00400441100f82c0c00c900c0c18480d01540a80383d4050192a94425803104030b907040000c1088900560300c0c5c01003465050b080800b03658540001405002108032000f50510001562070014080403aa20409803168040e0041504105451991541252141401032005074002a0802150500044640c1440618803500b4046146101108001080c1400340c3c0d00c6a0b4010400700c1c06e099040c4421240060100c52031640519018405940310862034600c1015109140c900c103c1c01a0609204001e43c5803680154110381c1400458401601c83e49044244180d011801480a03200c80000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879541402 1250 879540152 879540163
    0x115030303110f0c0309130b0d0b06040f11120f010303020a060b0105070515010509070314010306020f0f07060e150c18130216020406213206100603060620 68
    0x8490380f40c400071071084a10f5802200500c1009000c03540c140310010172100b424241d6603100e80c1e0b16400b286140303920740403440362506035900010052000070000c0ca100000001c8515a4807111107018010034461010800c001c00701303401245503043d02100b9032550f50002e503034642c2c0340d070002d20140d1100c2d14642c11f030b4016810303104501d5121040c1c400c191106e00649800e20824454244545801008191600d00074401c3c0101c0d44030701209440141c2c00c546480740a5803014641510301c1a04100c09407d8481300d0010b0903502c0d20409021441342c010b910100c1c03501d41d003c1c0740140c200800b00d06014900c0c0d9080104c40d20440c00300308071031b0b480101d00c0016000003180010071034418000604a42d409044d40200400d0340c2c42158200000da44410940c4003a0080f40c1d151a500e050303c0074030740c012034040860380c00c9040403144503594609403941ca2540c015100d8000c1e040d19805041442580c0696407031210240003146000c2103410b1400100400b140b0110b4414480406205100c0c455540c06118 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879542652 1250 879541402 879541417
    0x30601050312070c1d2a0a03050408040e1008060f1003031116092724020d0207150e060403140a02101505190810020f12070203030612011503030311 65
    0x4004400041001c1017103660048542901009003040713100032248003c109244d0340c502d07200802d42060b01251041c0e0080c44c2c0071304280c5001105000010741022501c250501c501e242c460034054540c0341017801880d108025094081107100941004120481c0355036400440740c041c42c011040d28405000c6d9410300754010507415805d50030050100c0d165509800041e1001207003c005d1a556080310621030101c51861001411008201c04080350071149a00748032003142d074248010714055070804d05a04036440b0410444011991507980840d00400e48141b09102c05504082c001f075180c81e0354010241d00000800c01400c9102040300c03800e0604c20080d034000c4140e070210400c0010307178241d84540041402e210b0329202c1c07628030951501c40c180320031081c8102c4194400a001d60140b0b6041c00d8040c7d005442e040c000c541d01401142d141c510241b11140c050794903600910340e00e041040034000100228105a0b100c5da040950400200d022080c000b0304594040c41c001807031056000c0070b524030f8403503000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879543902 1250 879542652 879542669
    0xd05060a06140102070305030f03071116060e0904021302031506030405071703040b030c0d090812010f0b0f0d0c05121f063608030403140c030601050312070c 69
    0x410030240d1051680060103031001000b8800003000b2000049a4034041400002d146800c28440b00c0113a001c1807010f550440d1043c20210100c2602d42c805619080c01030045003c0400400407c00c441a048080c07140c48e400c040e5160340070391900e0b40214466030b1480c28041d10341c0f5030000000b402e003c601c50072101d02d2200188203d5807070030310381013481d5180254040c8180c0030190751140f10080c4000811581152501c10100742541d5900d10803d04a801c1816007028880e00c0e166880006040c0748003c003840186c12402c20b84650401005202400060300014210941000f5030303c0c9000100041d6485000051000700c3c0070b00490204036000e000e905144a5030b90ba0080a20110145041c0040c17900c100803444500400e0340d90b01e044501006440282400390305d400a0b813140d0859034040014100d110076080f0342c841e03944801c0d80d0324603440347d8010354484100c0c00050311480d10510444085e004210001e000d0385d410140003d4454842008080484034002010000c001c0700f044000300038007002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879545152 1250 879543902 879543913
    0x5070e0f070e0f0a090f0f0e030307080703092112271b2402150402090103030c0c0b040609080114010311011101110714060a0e1c020c0a1e0806061e0d05 67
    0x1440348002c0d001c07680d881f2201030304110321001d43d0039000090f40e2041e1042c1d561103903251a880d0302039000700f941d51800c3d00c040e04527114105e10a014442c114203102d01c2c80d81d80110a40c1c40e08070381e4040b122048515811081081c40c0c0c00b022058032100300034400e0b042901040302440032102210f82520702d61146414040241f0b800b1000240d1241401c074240c015000c1e5159540d1a5002509a080466009601031004001800800d22070241030180520071820340c070666450344440d5800340c020394856400038802010a010104e000e0049094504002620b00c0c00f83d411030b500c0355146590f018000703040042200e0120100d82e000d410842c510202c1615107581c401c17a6080180c841d89000702048010700c034450101d14855880d1141c11035000b01d04026044061703014006c5000200030542460462050500c08080d40d83c40f410820003d0002000c0507600c00102480107605144941c8900291303040f480403c1400e4840e40014a248040b4501c90601b100120002035404001140c0140180c4102c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879546402 1250 879545152 879545171
    0x14090d05310501080c040e07030b180f06030c0612060607031205010b2a070302010e0103140906100609061d04090501050a0504140102090d11010c0f05070e0f070e0f0a09 74
    0x494014410782e4402e0362a000543e40b2000035220b40e1085220316100810024005108144a544103018202c0020a1104005c1e41c01e66401c0b04544240d4813400c82c5c0f000201404a14a0200b021744802c010507544c3c0c5003408280c1d00306c898a510010140da0103544002500c1d4101481010051440c405c4d81c01b04000558440000c0d031300d02d420010701908050007034282c0f03040303201c0303909085620b0f503030080c005004940c03c0d1782c0111404c00203510000e061644a020300440e107444400d030f42d07105084c5607004012510b020b494110b04c10000354094010320040901c10300803658802c104010404500c0703003a01900d120b9002040061440240182c2103518010900032192230030340081b4041d038015a41c20007a020103035442030803440b0b0000c14580c0303d00f180000000064102026000201050604100b0300c4010303107a03030003612180c1408850640151030306019442808540396005040b12402110600c1c1c840e401804140345801001d100b9521510801001d681d00440400038102040c824405182e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879547652 1250 879546402 879546487
    0x31608010c0306061d0d110607051b0a080d0f140a0c110108090a0605100305030c0303041a04030903020d170a020d08241005070605040f0614090d05 65
    0x1d54840d400a428032400245443c400d0507500c050650a016a1034102845002c02a8203e1203d078212504d60500404079040da9485000d0800f075809071015000d42001c4403081c0e4290b4400c00c1c1d05c02e00c1840e804100b4420340b2800a082c041d01d0060f410080a1211006000c0d1103100d000e4000101031040001c0c0c4074050f2744c1c043c200e940d9552040340c0780c040c89401c04006440030700d030072690000140e01c02d40001000c140a9001f8980294a1030b000d48a616180e8403598210b41c48804220700c95880001400704000300c103c140c0810b000060007801c000e080c1a0380003009054580720207445820502424014084102c9405280810411400d580e034074100d000a511640300c0100319012400070310006014185851010000710640d94410910088410410450031031000403201004802d015440029031103105d180d015a0003040c818003203001c00d103091825140c0c000300a0491900d0704013840640d440003d94210903400a05015844000c0c0c00700581d00651454200d04000ca14190b488200720b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879548902 1250 879547652 879547661
    0x110a05100603110d11102007170c0918010219020c191401050f0d060e18010c080c0307021603080d05010509090c010813060203100501111209090603160801 68
    0xd11a2100c42500c1100008002500401e20130150060b601032003480440c0c50142008040d180041c10010300b554801024050f610007030a01294040e0310646080c4104546101c588602c1e0b6410001414503e4412000c40c1c403108003d04290441240031030848401c04007901550100d400a01041d08104040c8100a543d0141c41c0c0b0a24010301b0b480d010800c020b80302c201c1c07010035100b0301c40300408080400703401103070345911242c0c40d109841c1d07050040b400d0264042c001c2c2d10040c481c580e800b041608000d4038541c0150105074003046560b1600c04800e5501f03400c0720304503503c1481c2d448034a03160340d10301e44168101100789071109054401c000c004000c10108402501220002d80c03010000c036a210814401d2484040e6119030456010315020b01482d80714106a0b5840541040f4484010005503604000d80e00300381c882408041d01c40c20240101d50b0b2000b000445c40c0d00b148002c1c41e1082c07429942c0380b03403486074001207405100381c4800908591806c21995480b07503c00c1e4613011001e6a1016407a0080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879550152 1250 879548902 879548909
    0x91005190207170f19060908040f0f1d18070f030f0b07020a020306010b070629010e2418150309070501050316120f0f09060f110406110a051006 63
    0x4040074011200f5980000461844103020040181001c03900f020218400e46000c0b10204c51040d241c0c003e8000080503940988010070410620942d01c90402c5600c44814809130440310804034400c400d51050f00800350655085031001070840b100400c441c02503800c10501c1d800003042c440c00c10900204000000040011150040503c0d50541e100c01808907111f05103004040c3d4507611801c01402110356a20003441c4140c031603500000d00c001c18a000340c685144041140f20040842d00480c0d016581065110702d4228045400c5175003054031420000083c50068905008828007090444080d503e00d22184007503c401000c91841d841c4d0308a400e17440b40d008842c400b905004492001035294081d0041c0d900030015041e07040c41c0f500c40b01070120780c8030001c01410203030a600d500c044403030124240300da0b503080001c01c000414190314608003103040d2241185612800d0f46042c01da40011003d1100391000d07a0340a1400c0240c02c84890189403070003a02080c0549140201a8801d1481e1215407005044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879551402 1250 879550152 879550169
    0x1080402010215100501121119110a0f12090f0b0d1824020c03030610030b120f0c03190f020102160b03010603050c0702010c030e180901052505091005190207 69
    0x21010081f02500c2a20b4510140d9851441d003030001c4140c0ca002c466100175005450714141c0c40000081501c189400148217042e41c00ca28910194403d00c0940f2191001d2089181018031200d880c1c0b40c1d0003100c00f040d900ca00204900041030082180c60950040c58103070b000115258a000c00500b049104080c684640603400c0042d400c000814034901e00998100e4004079004d14290355803101803203a0058030000c05410155980c002000c503588080300818160f002100406461030003614851900e604108054800d074088114030060f07000c5001c0c1074058070761001c5880360384c0c01184010b038a44030705607100d5001002e29070030100d081c89220010718102c5415942c1808aa140d1440b51130540c4680320010340041d40c890031000110340107000307400352424090b148407500c1d82c59001482d88031400391010a0542d444006000310250810002040413448140000100320903c001402038030490b40114001c950f0080d045031801d00032400c3d1807500450000031501490101c0300291101d0071401035021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879552652 1250 879551402 879551417
    0xc1020010e010e150a0f02040305010c12180b0429040f03030f02030c072409050604052506110109060603030e0907080603030f0318030c15010b1801080402010215100501 74
    0x580080019684480c0f07013105481100b42e03141d10314a9400340c840c801d80440910340800c40000040c1c002d110f124411580c3c0c1c0e9039203240384102d09400741507070403c1c3c298200c1611000c084401090b0001c48860b0419405070840c403001007071100e40311104031000011140881c0d01d03801c1200b8001d064581000840c0309030350030000900e442c141c020072800180d60341002404248035500006501440c103c200c1e09144800c403000111160768031056441030041120b1903084041031000b004000c00c241641c2140340c516159030f086e00e08030b41d8901d0000b00c1c8211010420344004210030030304294015020b40d40c01100a102068890074064052071508620500031240c500c0011000e03407050714458000d69000300554909298070920102c81c1e08090f252000c0100303200504400c00204000400384c250090b0090490032030601510101c1c4c1005a004d54401d0034204111014038252901c1c0c02642c18003420b0102981e280da00040303281c0415030f205d102c0b51071040000c1c014211080d411040c1103507000d07a20700c0c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879553902 1250 879552652 879552671
    0xa080d08090f010c0e1306081b1915050d0b1003020a02060a2901020312040b04020907030c050d051e040305090a050f0d03081f03060903030b03060403020c1020010e01 73
    0x500b01e444c51426a00040c07200000584c00e40340004005520a00086010400c2601d0308455802c1c11543c406184207001e281c2000b0300f05081c07a1845200301c4004040040d0f00c0343c138008995038000c25007600201044000944d8081100c1d00d9071041d01d030f50102820360211481d48040281c001c0d400720081001512612000805c810b445018881d09041103462480c3c0b100c101d04a01c890355109a003025065020600905814460700d142c02407042c0c0c064510010641004d00511040800180c00c103820103044c0403c170b84196800c001280e00880c0144c078005400d56440492655000d22010a202c0407000d60051005050b4400301232700c0d82140407a510138025039203030100030500c02136016007a004002010800d004c40d00031058507510a01c20b0140524a880803080c18842010607001102c400755140740140500da407500c43d0100e01e04096005000b14109614040d648842902501e0301c80c43c89146000c690360302c22400c0701a4100054040040c0d041414403c0340030f44502000442ca0350700e490b1072030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879555152 1250 879553902 879553933
    0x6040c050f0a05040f0f1505150a1d0109121202014d0f040810090521090a030f0506101503020705070b030a02090f030c031009020a080d0809 62
    0xc0700c06039401458160b03080d1030f103810310000d030044803400c22074030b0b03a1801e291100044a00903030003031001d60b004200c80b030707410300040007000d145142200f02d603500280709100c030300c03504255200c80401c2c04000040c3c030950386000403920841075400519403000c041c441c54040104004004c2d41e0100f080d0028007624000c1181240401d0340314500014865031160040c1042e42c201c0d1030006200d02084001c2c22985141044003559803001c04071301c44621000804020701342c818000c0ca1405520104103100e51095a12816034800b03200d10aa4141e4256849100c40c540d090b0003141d42018014000001d103d42d00d00b071030080c50021250a50b094042c100002d41045981c0a20030309032044460440c00b06200791000320025007010504907000d1140d80000700381400c860f400b0b184a001458030140ea0380a0000600074034060302e4040500941c454003141c09940c1c3c0201d8044031000003040009a0010f0600005d010300f4481d0348052020701070311040050180d1300c541010b11444980342110741c203030b1000c01c66 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879556402 1250 879555152 879555169
    0x5010e13060504020f19091401060c020909101112010503030a022d07090c0e011106130c0902040603060317090108220507060f110c0904110d05010e06040c05 69
    0x9000c00154060088002800c5078007041e00140054640c40100d0407000c00701e100c2c40740803141403808035805d8000700320220b03031801001d06000d0100c610080c85d501d03240000e041e41c41c20b40700080c0306002c2d000016240310400c1007160b60806da050701c2800141824014514180c0c0003040c41040a00c543d0004100c1d030500204070307250414641e004080710891040303c00e0344014481b100151030480d081a41448c5001001038201a10040301c00207403400b0403420140125000003500e5061103803170240007107480302c08500c2643c0902007403010034185840340740555000d110341e003019019500c04500420181e40c10380c44102a24070038800740310221240450440e140c0209104c1d2030004003940c0005147c8944040400000b40c00401080f0344104a80d0f621810100150890b02c0012602c607003201550b0f500824002c4004983c2c0c0240c00025044d9020556640000f440a080914130100d018180e85a0040410010340c100d8001c11030508030084550f25601c09840c1601c00402c1a00080f41e03602d8203070074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879557652 1250 879556402 879556411
    0x11030a06061401021f181208070f020a1203051b0f09030706110601030809060c0307030c020a0b1c090503070212060403030f0c02100f1b0905150c031602131d0105010e 73
    0x20b1760030b04482030410b92005000180210320402d940d000c0c0c0b02c000600c07440f503007400c5418203071034000e00d502e4002c4004200704d030041a00000c41d0321101c2c064000c607000c06c011260417010780c500408c1d69520b550f1140381000700105981241c103000503082e941d8161072406444c00d07000c100d00340c070303020f9541c0e010403078605105c1940384495400c4800108000760f2617800400d08640041e2005040050511a03d8210342021701d00350042005c241c442d404600d841d05400c80501101800c040c00c00301207051340f41084451500c510202551004850140882042518000d95000b07103e01207071034442c120251224001e407030450121381041220003003510a409150550411039008000e009240031007103019104140c22000c1d4195659170030b00510407100038000d240d101685400105c2c0c0c0c902000d106900401c2181b01c1c511420910034100800800300444001d042440d21140b41c001d01c0d03000083c3d00071036081559404d140782100c0c2c084003203071003540708002284c43ca000300910380e601c0201000010701100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879558902 1250 879557652 879557683
    0xc090b0102070e090c0a08100f020c071403250603183302040b0901170103020d121e0906030b01020c0906041505040513050f0a0b06010c11030a0606140102 68
    0xe005010340d0701c4041d201503101c4002c0c4100c07145c0c05080c00201d0010045600001000d8201c4042c045004041c0c0c040c000c1040e0a401c0d007145001d6110041d0754031580d5a0084242c4090311402060703141da01003086041c00300104002c4152031080700c28416a100c8a0301c03540740824140708172042000ca007600030558080e000805602c000c00f840c0c40e14885d002e8900c40400b006202803000804200e41840600081c00c1c199000030390303404061001400003142010414000030150005000580310014400519940210406184141c50409031203507100408a07120b807018000130403d84aa00c42c4003401190781c640c074104003450804004a807035201c4909155088003541010030640d04007540020b06a140c4410304a0200751510300203000c0d56004c1c3c1c2c5642c0e030150b941d00c031907060000a000215040410100420301c8203d1540c9407000e020004100b18180050340c4030890a0001c002c20f030100340f0400030305131441c65900746000002032019008001540d440041014040d5000050300201d104412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879560152 1250 879558902 879558913
    0x30703020a030e030f0a030e181005150c01020a02060414060f06010f030e010e1014070207060e01091d04200d0206090424090f06030210031d030a0c0c090b0102 70
    0x15201960014044543c0b01c0d050311603c0d41c41c07440c9031820f01411402034829078500361800e001c41c0401a045528008030980300309a0b07010b101200c0141c401c0141160829101c44071105407000038a001c60044082d84116035000140d0306030010340c0407034698440c82c89000c000e4dc1a00f6092070096813071204481100140c501000401c07815030003076000c00b140d503d20b407402007200d0002e420740c90309607104080340009030352042d00c204424022034000c100e400e11040410300090304e40261700035582c2d941c0d44110414800250000700c0c1591003210b40002510442d80c2e1229000300281031500754110885041d80d170b087d58044d4440d94114505004404c003c402081c1c1c0d80310b02a140c0070090507601051902d540660344548030400c42c46403954120030b45007002483c41c1c109280000e605d0907500200042d541c010f183c1001480140d0301d10b01c80c1d000c07801c8149400500715105003105c0078150707040c4c00d04180d18400402e6005c14207920014090300c1a119683c200960b594801c681019500c1190760b007070258028 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879561402 1250 879560152 879560173
    0xf170406090804050d051f020f1c0b0405090a0b0604020a2001090b1018020f0f070c030b09011d210a02030f0a0c022d04020703050f0a0c02011103070302 67
    0xd034001e0300010340210308051500381d0320030000e80f07080b0620b4800c8400d0782040c1c404107606245418034081c3d1410388141035140000c9540c0f14802d0307120706c582d02402045801d80c03441400d4036550100e4007641d00988200190300381140078680d2421070318411104501484005100c5040500a49001c10250740ba081c13170f03130040c038016423001000242038101c0b6507613907180000208240e10403a60080c42c034114048185410401000034500352001c00703071140c50040100d10000f4500008507411607a10104198032441c4038500a00c008140c1d503c05040c9011318014040301c060198031050642000301c01500c00721505100c80c0340c903400c04000b8803e03c0c0c03a0125449110030ba042005015001180c41624179124141010000c1908040c860034001030629020b80210f0401c038500040446680f00050001d901c1c03c4d030b00b40d070f01010504066003d2500843c4d0030b01018060405d8400c41140880c071952a600310140080c00e1b55500340c0264006004040005800e00c004001ca03210140c140d8040c0507001d00c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879562652 1250 879561402 879561413
    0x90d0e030601140111010603060905060a0c08070309020d1208060f0f03070303030902031528141501030902030613021504240c0203101a031212040602041211010f1704 73
    0xb071883d07203a0305018001404045c1d840c0c00f0311612000e10b00c1000d0000c0c0e0076030a410030b6442e00400402c0300751442e103080c00c0ea0414980200c64903920000720729000c03408000358400305c2c40442000800820030320b50144040011504000d803284501816500200c400881d1402c0200e4031810007101c40c0c058006c40e0041c03003c207103c0c1e009004868000b41c1201e0b240e080828403455418021101c600080075403a024003440c900982c203108070038031212030a2041082d0043c50307100c0d150b40a012000e80c0c4080f0800c18840c1d90090308a4909150000c0940d6200d10340f041524104605003c000c9102d5410310001849000020054030107552800e60807004160807401c1c00c41602110446410030304c0903040c02640107a81c10070400d10800102803000c102998440c3c910072542c1841c804592080e00b00132070b035955950302e50080c3c0324040002c202e008410b4949041c900028030603a0030a801001c0c50502c6c0c4418404003100f6051085800c1c0c0c0c030311102c54083c070412100c080060440c04060b8000300086000710701c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879563902 1250 879562652 879562679
    0x503100c170c090a090506010f0503010501024303210807032004140301200702061b0d0f0f090b030a1e0e2805032506090803090d0e030601 61
    0x10b2003a0349940c80c06403100e002500d1003100b0f070721403220f194a8108124082d6800705003001c0364556030502a00715410400040d48803010f80100042482a032103007004a00701013140701c10f00d00b2480d0402042c00107826070404903255603010582d102594014070903030790604816403031200c002c0e40d23865002e680c03030b42c1760210050300817334241003500e21001c007010700000c08020090008041c40140b8000c0c0103a40402d040c03c0d228880e0340c603800c20b40c5d00e0300850030f1070340713048100d880d91541113960683d901200580c000c8000c02040001c030140c451030b80b400380c010303411a02d40645240c503621103001092034201c084031007070350501500394004420b0000c104030101e00c4c0c10600c6441504800c00403580031030546a8121140ca9040e99055401303c40c80c0780344c404000e11900c05401100b2580c0b0300700e07404e540b14a40e9074803170001001100d5040c01020000c035100410b21100755076001100f40030008050420980075081900c5148032400ba443e06203000c2402401708144850002c0c02801550380390180350007800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879565152 1250 879563902 879563911
    0x9050d05010f02042705010b1c020d0908040513020c030403020402161704090b060408300a09031e020d0305030709120c0305150717180f01060503100c17 67
    0x1d40d02e40040796100d04450021380f001c0d000c00c1e0800074074848038605850010021364600e1183d545000018044070748518100c501825120b100340100c0d0101501e00b200a10400c80b42c4c0c0c03074040c07601d8004400c21524100070403c80384100d8101041d0007418105400f28802e1420f0404035900c00c220810040c01d023a005030076159040410b5079040d050a0b00d90b480c180c0c5640550002403100001d06002e841e480d03210b030103801d003002c3d1038040c02d0034180280e03d82e95941103a6088602101c80c4400d5a00142c1c0503141001020110a4181c59070115600545902201d010031209145914440c0c3c100c40e4240b1014000503400411500810312030340c4007070324180d201a203400304001820001281105131914a1110300748594001902c0500e1820010308108080d501280c3d2600c00704140b1400c554062000303507031641c20501d01440c0c0d4403004a1013030390f500c450200341b90900072000308404800040d070041080f00d400f9030031340d0400b00c4020007490440d01035440c24004264010442040580e201e58005e920 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879566402 1250 879565152 879565163
    0x80307022407140f0d050703110412230d0e010206070c0807060906060b0c07150503010b07060f020706050405011409030a02121606090f05191137170303010609050d 72
    0x1c00a4a42202c0700300c0e40400400174405403641d05010700f0702c3c0d242c41001351035400d20081c00c0c1003074200350409124528101d80901004504445100b418824006005d0a00d86c50022100040306c40d01c1e0140840c00b448200c580980a058001075000f0300a11a62003001d40c002001c81c079208950382c840000b0700303a46c00c0aa5030740342d42e8a80071500c0d8070342c070b0020160310301402d005128140c03820129807031000c5a440010100324040c4010004440c5020588200f99803041e0082102e0084000803c024015000701622550600d821f0006020f419801503a000214850300c10f10750384d400030314681c4d80c41103070000e10040c1d1082041b01c040700341c45000b90800d40c00030340418039500081d44802e003d235104080c0564a43c40e4241d000030412000308140201d4000c0d82c1180700c0ca0aa5949507515822a5a0304481c040d10840d40260f904003102498540344907540542e4074040c01c00d8407415680004580a0500c84e16101032820103003100010a60b4121880c80d920031658074140005d0000ca00440c0c1000c503030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879567652 1250 879566402 879566407
    0x15010b0c01090209360d050a0e060324150904150e1602062401050702010201090f050708010605060f16030203041215060504150506160203060408030702240714 70
    0x50752601c00d03c5005e182000580c503000c0710742c800c00518900030f554005078005410201060601804940c68190207514240309480705c8020405448040b003030400e0941c13091000040040d1402c2401496180c0728040d12032000203a1460203000403018bd03d06655003114092150154900c0e0607000a020200b6a52140002d10b80e41c08040742e0440069848644043c003c5005000e0030f80c2c1003000356884080c2c048001680b01d07054600d4110358503c070468074100b2900040503000d45e4000d40008601982c0b001d441c00a0303200c107090541d00d903c00d42c002c1c039405500708000000e1503c0c108050343d60b21020601c40a141c03800c210201005441504030460660005000014140e04112031801803140661100000005250499411100e41d9000284a1440c10181c50071611111600d03405841c004c1e10b00903a00e08902c030040300d2410014000030340c58825242000f0420a11102850207400d854086a08808804103084054600d60f0750040d03038903c40d1000900e525100b82003c41700142400038052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879568902 1250 879567652 879567671
    0xc0601090b1c06050a0e070e01060f030212090705100c17070f02130204030303050f011220041d190515131203090507061d0402030606090303031e0915010b0c01 70
    0x542c905100c907815280c8030356400400c600001103010b00c10010b080c1e90003400f000c90400c441c1042e0b01d1410b0040f0320820950100c9495503e01a03411a83c00700344120001c0c4c96860700034161a40c1c1c00881c000c140c000d00c1c0600c90305400500a184201d4260b1b482078031986030324400300c40c000703554205c10803d907028880740c1c1d104405a02c4038000c600d1906150007015940e1800c500300a005e54901a1400b118074803988010000c00783e454854540083c2c0c0940c00c02010288918448001c000c0c11510710b501034609032621010a03028840c2c0504181000180e5403203503801000320020b0320840300040d003250003031055020200100b40110341d0107219203410006000d05038850072038001c40c2c0030111021a588403002028008100560300080125117403c3d15500312100707402c2c4009406089090056401201007141581d48005440035440e0240480f5240d1500101c1d400c5207041c4a5800c114000e400340c04100c1905000c140201c4146504005050b40d9107441c0d000401640121100c04041d580e460006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879570152 1250 879568902 879568939
    0xe03120408040e22020f040605130e0f0304060906080c0403060515030f1f0b0604052e0e060301050f010e030d08220f020d02221e020c0601090b 63
    0x500a40c094000551100c0c2000782c0b680c81078401804c148800200d4808441a254000031074031319255058520304181d132100b1020038040d00e01a0445036028007001065071100021381e011840c905045000c03a010071000403501500c910444c0255000101606001d01c909030007101d0146d0000c510307103021071030956281c58510440d20290303195000d60f14503d2000c5068941000321030700c0745144801801818848410302100801c2c0b402140148a8444446030880e07650b41d0192030042c9009040c2101180304806143c142d41c2c8861110003100081359000a0740900c9103444039950a0040c040d00d2842e400c01080146200580102d281001001d00500055440600001d400380085032140c13411070400140d10390303060881680c40102c034005a02d036080864070300840003a40a405640b071803540401c03400840c1a40b1801e0320384901c8184941a034010781d030425404211100000309441100e08040700c020800e92051920b621075a0f48401c00501000c0a254401244a0070003030030203030070a091410301c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879571402 1250 879570152 879570187
    0x7050f040603021306023912061b030403080109360201081513020904020903030c060105190e1503010e1618050105011b0c0306061205010e060115030e03 67
    0x80c00007034000c1482c048072015280014041c000900140c50000c940c02ea540107ea220040754020001e40c902c3c80c1c443d80103149001000180c40580550510300d50000030a42d1200207840c420360b09000004a1f4002e4442c220659001d16071554810805900e0b201c981c101070688103440c00908202c0120382c1c04400c2030017820b210400080300d003a41602d0f00c0c6000240410344010600c2c0c181102038000a5040c0e6520000843d00032050b43d40180c4441c1000003080003405142d072402d805100026103086144000180f446c100c3d82c088545040415220441c0021421188a407000528001010510005041c000c50b643d0100c0580005007920240088a02c1c3c1000381c200110741440911050020161168640407020310078a014046540b5010000300104c10040340555512800380c102400c010940403c3d01c0155003044090001d0b5813100500d13282141160812a0705620b401844510400301045941c100c48100c003590420510011301500174280c3c3e4038601c5803501040000d103c18800d034001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879572652 1250 879571402 879571409
    0x1b03031303081033020c18102111010f050901030c020a060213094b140a0506100915110f1c02030f04050f03010b04050403030c170c04090507050f04 65
    0x508000d48421500124001c074240d130300020854005203074402e029229480c42d482c0c16500f04200c0005942c611070055008504e0f50024160f80c03a4a00084048814581e411440940a03030745240064164900541d007018241d8001c1010502c2442600425800707944000400307460b5006442c0744280c2d07a5103080c200e1380007140d5801d0190380c0d500c0620000b0010710480e40e0301021103188810302c00f0342c5415081e4403032500c0003200e151401854016440d215110f03600c40c0500c5100300600ca82c00018460003082c4900303c5203c02d01e14035210004e0520f240280e1030026a03900d0751100c4200c10704043c01401080200e6090700203100110101e8107100c5002c0081e02c2020304a800541004031400e03000315909050440101c0456106004c07141c03510f4840c00444040f0341044900c580d1807807920f40400c1c050100420010742c000d183c0b02c10030051580503000011954116071b00c0200d11000c61ba149130140300151001c00300008248000e00080500c1d901c0300381c101202e41086401c064000c0e01160b1164400d41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879573902 1250 879572652 879572699
    0x2040b1311040f1d181603050601140d20180f070f05070b010b09151206010e03010c09030b04050c120312010b0f03040f03110a0303021b030313030810 66
    0xc0070098640b1404422000e0030746210b410440420440c030245003400b01812401521030701117100340b0304007010060560849110445000c40c42e989080440e12103009105040c1d4a0078000368010107407a10a0b203083c100c90741b10480c203400d0030314030f5540c42c0d8005584100903002240782e0300200d0140d14144019110741d02e40003100a091800e5a00101006050f0855205010042c0802c0c0700050042c0c00d2141902c0d650b101e401d455214060001e4228400044204031008000a080351800c441c202d44611505082e01c1d010360b00000c0900340341c01c0b6501100f1000c005800c0c44401d1001901410301d0a230400c0c042c0c411580c0c1c001010300043c0390010706010714441d03a070000030b50f00d003510040008180100384d103089803418010340b140c4032042440010f0004001c401003440307034000c15000302140320074140c0749422200ca103949480d01178020741c007c1c071129110142c026500c80080302d000086910480d15003500d2885495a50707001da840b040003800a201210003410007003401500312000c05007410820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879575152 1250 879573902 879573907
    0xa03030506040f1d0c060909070f02190809100504061b0f02060c07091b08010302010807270f090c02030a111513111e150d0612020307080a03080402040b1311 69
    0x84a203d10700040d55410a008010a12000700c9940d2340d009440d911541e05c2c03d0150781203115503801c900301011607460070040e048000500e001d110202010b410024419944009054601001603030240194030921001620041420030050200d1b41e003541024070a0010481200d41680020110307000444d02042d1580b0a10081000d14940c1c0640901d402c0c03100007145840c5c1103010001e042c040c0502002e0f042c001900007103540548181482004441c054140303143c0304080f40048401c0c00340301e21510b403040006c0d00021442180038840d880c407021450b001103181c902c0601094940d0400e005a10425000d0445591f681e00b05280300688121050030f01c1c85000c018625010400071400c0d05130304e00a2402c0f800b0f4580100034480c100d00540ea080b2007850482240350350103100703407140c5c0c0c40c101e6400f41000c2d0001100108051a90b00080c0b00310180d07040d0949035909142e9a49038007074040c00040d0702c20003040140c1015440829410b178090424411241c03030314403d4065a054051a09002c0e800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879576402 1250 879575152 879575201
    0x2309130b070f092c1b070209060f04050f1006020f03120402120a0821060a0e0a020d1407021513060207030c0203061f06110c040c0201060810051501050c0a03030506040f 74
    0x3440000d0b4410001910f0926841c0c0b880700354821401b03034060090103410314601052581e80e800f00884c008400083c018016450010b081280c2454140d8031840700300440c100c0890410700114861400103900d030002d60420b00b4281181d041c1850103407007030313070402e00c0208038007260342c01400101200c9020301c2101d5910f6070f00e03868030904502e80405400120440e01c007404150b6407000c818900702c80e10640c0d50140c0303480300e1071884000d100300e4a1100590345400341d80c4a8480001e1040e901c00d82d80c40d02920002c0c03d401c104c20514040469464a444206121003000076001358050710704103000b403400314040031940c0d01103880d05100352604a013040c615400e06141614801d070800c0a45958074001344d08400d140741003580d900c044c4081c4c031b02c1143c031010341c15802c500c00d600c071400402d2400c0490300146c080c0c200340c9006100c180c54a541c04444000c10a0a9501802c204d40728170f4580f60003400e131140d03180c034102c00400025041541c09521042d06007a9a0611f00585440402d40404207001c40b14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879577652 1250 879576402 879576479
    0x5120109020405090a0605090714090d060f050a0204030b01170a0c0b030603120406020c01031e110a020601050301110304032007150e030123040c2309130b070f09 71
    0x8003c0c01c0c17000090600009000c40d8440d260801d8202d000e5061400320351100640c03280680c024611640d03004060300b05480c0500c0429001404400742c820410001a2038090568059201d640800b0f84041442001040728400c5411340510860411064802c02111540c035040000c156500075280210048107001041c0703402d001c1809040d00c0451003d1902d882e01401035142c146001d2010f05140d5280140140500e01c2c40390610715042c0d2613002c01800c441001d2503080d07600180003902c0141b140c0c00c004100b5040520070400799141b20301300c80d81590b8440e50110b40014454641200014040c03058003030700601006004060083c10703040302002415001c0041c105042c20403054030903070400009400884100324028048207003801c40e007896607940d06000030307084010f602402c0b240c003040d0100072011000102d80000c513481202c06895a0315517009184080700e2106010b01420300140c04201e110f40074415211901002e42000b10b0310304d6071030102ca40180c001c5036a0040000d0141120f00e0000d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879578902 1250 879577652 879577669
    0x1140106020f011401050f120a061409010b0906130f051005010f080c0406140705060f0a0501080f1e190c06030e03030705040506030c0909090109060c05160f0305120109020405 77
    0x10700c104000c04c50110054140c0001d0041882611301825411007041c280307468510846100c0444402226082141480c00c0c800030039040c0c00d00d81454400f000441c010b102e060003034856051008212409603100c150400c68825180644041f51543d14840c802c41c04d599405254805d50346280380c0325400303192a0016060750006602e040c10801d842c42040710a0000700250340c00d888103032904c03108503282c1e0b5007040e40610502601511920400d410045ca26018080d210b00c0b41c003910780140301d26607a5400041d520b82c2c07008101110343c0c01c4003421100c070a40c00390462002902001c1258080a0681d00d540900e030b26205080d20503040c0d2100900032a0307054083e14070a150f43c500150315502d00b100e0001d025016501610b13116a02c004003203004074a1130803d94141c80402040304030f42d414085c80280c02031200d040300f1504c45003001440c000a80c003c0c8241c1e51350100006110304800c2c01569041e2200c006c2e24422800c0c40028010001044198036401d80600fa05890041e69607007414100801c90 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879580152 1250 879578902 879578923
    0x50a0f0f0f0b010f09151115061305061e030106171b030607080109050a0b1c0c05060901170a060b1303030311040501050f0a02010b1201090b0109050c0a0507080c0114010602 76
    0x100d1304060103000350f8400010002c40e13010b0920801c692100f00011503400300d02e400720100c81e12900f1002c6608502520180d4082c403022110050f1080c4551800029140304a4100b584a2507018100c2c0070041140012004020003e0000a069498480b040200c1c0c0501560709620b60089001034440d101c0031680041e0700008034010b03d100e282c000d0008000e5401401900a501d4561001c11925801500701d00a0944001d201d002160105c44401130351911078601a6042d04081c3c100042c20b0912030201c80d0780d0001a580c1c110162003960100c1c45010f40900503802680d43c5003c0001c4010052001c2d1045890311120540e010345107040080986882d51600b03044840c0070441049245c0c0c0003412990800751410407252101e54404e030680c01805900f1b1140d4100b0b14603800380c4041030041d40b00c540164424800d280c45a602c032142c5604a078400c483c0d8418803502000940001070081001d010224808c0d00003518100b0710710161390035603d100601054559180e8014800c5c50740511880d17684 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879581402 1250 879580152 879580157
    0x9120601150528050715270c08010f09120504062a0f0507152102070512040b03180102181513150806030a08070303050a0f0f0f0b01 58
    0x880d4107051840d54001d00c0148800c0610a00040f18407205140f040c1e00e6155002c440c4040243c3c4a0031000680103501c000c10807240941c2002d020311248200b481003072402a0f01100c13070060b607800e1040d403904e81d100e42c210943d400103407140700289089090041442042032190041294005454044900131011402501303020703042c0820f111185d40300d216905040461003100c040098440d4007003115031128031003d02502041060340050083c00254403080302d0104519401e0511610000c46042881c0c1401c19143d2004030340006507d000d54025000503805034007a03401c407002d442d4200790075a10981c401ca0036050040300b00907035444c02d262203203a0344000382c000b9450614010800d4044001d10b03150107100c4c4444000200300c000d021400c0d01e030b070306040c41d1642d54101e0325003e444010005c42e0303000e4000181c41000080d034508010803401e018661042c402403d01038503a41c15000762000520006c0c05a640704c0340206035035418020000c14901c440800141882d500c200c680a0b10307051400c0740d05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879582652 1250 879581402 879581413
    0x4060f030b121527030919081b1f0c0302210301091a0603070e0a0b040b03040f11030a050109020f010216150c0c120b0c031005041128090906060f0c060e10020912 71
    0x718036000b10b60030404403280c1b10360b0b513914008a030002b0203007031654092640301d01e2903c180d00c890a420295001c4014040d4003150a5000003018600358455140032450342180c00344010081000039800c0081a14204802c1c0c0d44120900300c04200c00d5041141c0c25000a2583c80ba0700c0c5a6080850400c030103820380c0700c1158502410561009514072020300000c1c00011404040300074400f9406071280e007030200509803842030f50741d420403a020704211031069226040c00b5130805440c3d0300002d1116250494402d48645030f9190061400601e00120064824407200c40240c500003440c188008010300505032580000024904040500c02d40007040260080020400d00c010000d401c4998411200c04a4010609014264003241207000382c604000c4040715046529030040c4031906004400244c1e550f58400140d603440c802820b88600b4880c1c0c50105280380050904144034880300042c0700d010703410111340c5500300001c5928000040450604103680859410180d1602c601e140081c00d1203a001040b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879583902 1250 879582652 879582659
    0x204030f0c15030c09031b0929090610050309010e03030f0a050906101701090c2715090902120a03020304150509031002070309090204060f030b121527030919 69
    0x14031701517240c0000f8204009001c0303002c1e102c242c80d04103107024000f22401440101003140034860400c00050f207582034616549105070b034905203509418440d44005102d0b5120b5501c1b1102079900364005410b07010031395200d102c0c00d001070700100029030150100780c8140189280a030500030481c1c5001d0a1090035410071018082d021140082d41340c240c441112004581c40e42c0e0040c068010240040d00402104030340500054604502e0a02c064100c10303104415403d60507400203d0458070b64203000c5207100d0440790306020091503070707104191092007e004100e100707448d0f405013407408030b0845040300140e10024050240e515012980c031701c0712485090440c01d248c4044002900c500350160703d4107086d0740c041844001d00d88180a01401484149400c65840f511050011f00000080c850b60011070700301100160a41042e120000c0c10710601400703440e12540d01c108461030004081d01c0300c0001c01c1106010070454442031003100c60796062030002c5079078804140502400c8515601c0700885a0350512040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879585152 1250 879583902 879583907
    0x40b0f01061e140d06080304090b06250201050906220f0f0317070c09050603070e04150c1e030b2103030c090613090c030e010e1b040204030f0c15030c 66
    0x84040022400d10754041c1012a9140543d40106020310082a007080c030700081c40d0300040010f2003502d5003510203020101c0390b41d0611100348580a800c40c03040d5604448107a06d1007400003c0003400d03105240a40c81c042821000030100d0300840144d203480c86613000b4094440c81c401c041e04000341240000c0942c268507202c2d04003900c1034248005009ea0450b00000c3c08201204001c56881950012a00d000b082e2950a01d000821049410900900c1100004200501d02550581c8600c0d170111180940e285012a080d0203043c40c40c242405101da107400c010304016004034184807000719681c000a1061a0b03804018496142e1059164081c0c010f00354100000c9010044980c0301d2800711000b551401450041303101c5104084000d1030011014002190019150700401040a1142e80a0000c0103128494600300c80041c0031101007640402d0410b42100790a5038505003032071006200504090340c80e11003030142e0321081012140c0700398241060229203481510502d03d100f0707a18041101010682c0301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879586402 1250 879585152 879585197
    0x14070f081002090a05090405030414090112020402090a05040f0c080109090b010608041e080d0f060b030703090f080c0f0f160b09040207150c1d150702130203040b0f0106 74
    0x90101494001a01c03840d00d88400681303800804000e01102560b151500b07106880c3d03041400707114074811410f08424464134026280b41e05a9160440344406800564200310095000510058102c06020000600343e03445100b1a0b2404a6840300820001d6a03000e0040c44108160002c112036450a1040804a034100381c000d415100c1303070f080050543d10380d410301d04071607500050710604100343c0c403081c1c0c4100f195036005009440a449030030311454442941c242c043d2121400b90303440e01c240610000d4200340c070a800003168503004a1180c001e111203a141c00040f80d0229500d00000e034040c01480128038001c1060b41e40000301741000c0c20300024010059052550140310f0240b855401007501d400541e107a0303049682c0d2079445480b950040030902d03402c41c06030a8450711280815214213900a1004c400c845a610700880201404880c50000302c001c2d0198110540603600f1820340345442140c045140700460055000d2110740e041854030044180940005030000c4041000a5a00210344030071001c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879587652 1250 879586402 879586423
    0x10e07030f06020a140f130501020a030c06050c071e110105190e040f050f010501080c040b03131b080a021c050a11121b120304240e04020714070f08 65
    0x1c001d80e40e4003c0c1c144c1150061803524100607440400503914170b025042200030300300d00b4102420a80c0a070f9981c001681c032000440301c0600403560b501001000140039502181d445940c0d640e1150074141103444100c800c00009c0301c00d41d2494503101180c0103001c404501c1c09140682464030030710b4181c00f42c030941a0a02580341c2c01050184683c0080015038694102e001000b0420100300010300d070111101402c0c0000b0320400740800d600324041a61159401c0c119015074803500c50140c6951034818042264040b105400e4441c2c1c2c010101c1c140941d40b6203003410004140000081ca00c220041c010400c010910601c6001542c04909250000840203c0e110480a40103161f415003151483d000c680d141c0720303515101040e030007019080c180325050a40001550036042c0c60440310040040600381e900d01c594056071103162114503503980c1940e860f20b000403101100b0303d0030741c046042c507802184c1a0703042030b001140c0c2c0810407400c490061804000040040001100042c400380c5402c2240d0340300c07142c120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879588902 1250 879587652 879587663
    0x1060509090723090c03150906030a140708060106180506120a05061503010603020a021501031106131802031f031214040509070503060315010506090922060b03010e07030f 75
    0x41080000b403c40310100c4401e500141002c9024030f846106500380e40d004640c500c0c00802110a40c0001e4208640807030311880b130260003040606400d8865610780c5166104001c801e128804000c01c8465007800101e000b0411510bd0100084903002d81c4461080c0c0c80d00294040c40050100c1071400c41001015500180360b20070004550301c41c10041465900c0220010f032a140c0c0c004000141e96a041d4018100c0f01403070790a0340e40c19040e00105010700c00d070a100150502d40506010b05462811800a0108890600d03a9070807041d40d40078038804a44040541c480c074030380d021081000c01600014401c1040001c241011500d909540d1079041c40b0410100c110f0810080010f4560109005022036000d444001d044224619000c20b0040c45a0f1003228114028050120700203504494840d41c28107a8030000d120500380355290f8140004503100034411100100e014030306502c075819610ba0159140d001340300116407003044406050a50340e40d0300c488000d9030302032a0b08201041c403085032420000d9201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879590152 1250 879588902 879588929
    0x61b1409060a0f02010b041103060102011109060a20010e1c020d140c01091a01170304030c1806050405040f0b10140409020402040e010603200f03070e04110c0a05010605090907 77
    0x3c9104a0040024031201e6800601d421082940c10307044002861091809038028404000c131041d009a85000301440701e81c0115080c130880c01a1802134084c10300d02e2100b02d42c4242e090300000003250035100030710303d40d131841d400030185980c07011050840710b8800c01c0140010030503200c40790b40061821041c0b00008020900101c0c5400d0006420b401103031405400c80c40325030015030000f4403c800381e0b40a00c0380703d01940922520005c9014088196011203411294070011180351170103205680304445441d03003a8070707940c0c100814180e60724031030240038600940d4209401c1d002490903521459000e085a0000d442c1c0301401c001103030b1120740340b0001035420303900406c8450f038030320100300680603035001209c89030140400410215030560014034031b4a043e1140014500400c40030b00c1c0d0700d00c0b80081e2540ca2560400000c1c0e4418003c1c1004030f5000360103400010300944040742070f0310346e81002082a0782c0350405610786003800000d0150070060b084c1255242110305044068a581e490544035042c14100c0c1b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879591402 1250 879590152 879590177
    0x20d0503040504090303060503010e0c130203270a02010e0406050a0302010513031a10060905370801020a0315050a0509090f030403061b03050103020105041e03061b1409060a 76
    0x14401c0e100100005441403101c02da0618015010f0485806918000e6180032281c8122600004001492800280191940d40041c00300940a544028034082614032a80321a809074403201c00000b015003260805001480c420b032000514100344022124413a6042c01ca080c000381e991100040b0850340d09080060f580e16034003000361710200e00e40d0b2000d030106808801800a114070a81198407c0c0c0000001942441d21460155404460307800b034507400601c0e0317005110b0225035008441703003942800c402c035031f401c10010b500c50000e5001a8024400694000c06d289940075014000e8200700300484214003a8030340ad1002140b04c403d140e01c0340758480c0c0461404200e241f0401d003c0b00199003403180c1079030303501c40c2c580c14403102924403c1a031031403421040740c100c0300352031003407041a050301c2e4140d43e010300d050318003040f01485402000d18405280c005420010000b40244100500e00405d100000600342076280c2c05000b0102c68010b4008080080252a00c036590321800c42e01c0c00480380c10701c0040201c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879592652 1250 879591402 879591413
    0xe09160302160c150f030e061302010c060c0e0a230603061804050c09390f1c0e0307080a0f03090f0c08100204230612010e160507050307020d 62
    0x700b032071000e05501d402d00340c0410b1000c0709415440d4136404540321100c102e11400d07400c82c100d07a0f010f01074002e01c1d003024002c030b40d20520303248006510038014507090035000c0b42902d80c0c10488000c80891808900410360a10443c01e000c800c0d500240442c901c0780540000801c0010b4101c00744003515072103402d0000000d816555001d0403600d8801680480300503504d414070746999202050b0360418414483c2000040c46c0641c1d0020341c1d0304003075007080007044050912000b00e450b070f2640219076102c0c500c10f01c006203250003a030f00581600c070403038a0300c0b03a61000070000c0c503000c0352000680d84805410400900000c146440101c070b09011480c0f0300030a041c88071017800c030002d1030001030041c1580c000c0d5501d9801e01c4035003a1410251034411040da075803c569a00c00740308a1269201c3d80254007101d0408002d40c11410910314210700000d010589802d012001d400c941d8002600460040d60b405000c0c0320b106480d158075401d1b00c0000b410f10514062103a1283c507620300404000911400b10181d0760001c214 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879593902 1250 879592652 879592687
    0x604030503030c040515190c08041a03100801111204150f020909250302071401020c0d11070f030f050f010c0e04051f150302280e09160302 61
    0x1600034090301e88034206041d000043e580148609841000c41d13600038030000c4241c1007141e54800c03100d4525080384035450800d0398940c503a000140d41d450350500c40001c6a00001c0f0111100d0382c03040c10340c80e980345000088002c0b18401500202c8a582c908005124680700d03000441d26544e6a03d421880996100c1c03800700380e507140340314801d100b043c00c0038201103503840b4a80207018185002c88503501ca83e503640a1200c486004280b10b84d0030860010800602c86001e5401484450302a024107548076800f8605c182c01d907400704400452075440b105c400112503030302c0b1884810064050018002241c600225805030058a00010b0121070040611004202e800c008840344d01020000a001c40032010340c3c00340c485454258070b81d00031820040010b807511403001d08042003014404420030402e091094281100c88c2480c140320a1641c20454200d00140c0d6080701c43d84190800c801c035071000c891000c0200980780410310341c0e00074442c80b070503c400425074002e00d07121142c0074078006031256001d020310007005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879595152 1250 879593902 879593909
    0xc090b1213140a0c091d0705010507021c030c05061b0f0a02031e180307030210030e0a05030d02070c090203070c06020c030d06030b070305010e0c030126010212090c10080c090604 78
    0x920540f00740c0380c1000043c02038001101c40d14030082081c84480041450882c0310601e5482c1140c00655081c006c0d07602407400b074802035001818041c48114003034120314108000480550104a604e48503d0400400700301c6168448031034110040040d880d08003001d04c90003012180c491442c80428103403440380c400c105540345600da00c03585240500030082075903456405074409000100c1d071010240c80600700060340200b04c5ea8060000c0c05000403266085004104040c031103079007401400254000b1410410207468a900391003801031791a4840d203440c80361f081c000d41c040da42d05030040c4100441c0d59040006039191a0700301c0c002694452000ca41c070307030851280e002182e0300c00745444004070a005250603418400c1c04903171400c110603626441c003960703214011540c00000d6403081006000c0c9010304282d601030710b101145c0c8100d480d00c00e00c081500307a8108100c0c03203c6101800381040b803d02c20420042c00c40c00300c25191021408191140104680c000030851a007000d00022b94109940700c09040720000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879596402 1250 879595152 879595193
    0x8030a091e021014070b090109210201180f0b0c0c030a0c110a0b041403030415030911100212031314060109140f0610120f0c090b1213 59
    0x4828030040300040c4031a41e60742030740540c071030380100c00440780100040d488803e0304040044c1480e03815a1140e034514002080300302155224404d400004004c107010405a01403141c050b0090145460000d003110a00b9600501e44909150803602088422602805d481d070001083c0103e0760710744050504c01c1c818009001d245110010b00b500445070700010701d0711007611030078038101c0c108800400c0000f0600240130303100c01d6034401c110412143c5041403413811100300c06400c1da400c1c240c0d1860503039000c447c40b0000c0004039032110400420400d842d80d0f000080241100d029a40c1c22095500070b585032051a50f03030342c03401800030210302c01c02da0440701d00303121540c0000c8002c1441c0209108549401d020b2090341c400301d007000f59680b0500880d200040c4100c11420910f00326954180402001e000c445840d0000d05c800c4540c207410f105114040c000240342000300c0030500c444a01001442c0c2600790b4801c002d00d45060001c0129a000c02290725040358030011480d03a15211410500b42c2100d041944051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879597652 1250 879596402 879596423
    0x1407020409020915011101020a020c1905220c030501030b061002070515040f15050703080a0b120d09080a080307031d030a020601090c020f070515120a06091d070308030a09 75
    0xf502c2d558030b02035a00240e0301ba0b0701c07642012a101c08080c280d0140c0d82d00500940c2204000040604204001547c01140c100300840d2683d580e01c00f141e0f4100c140240b40021145007642a90710b00c2c0c0710f00503004842c54500d8100010340c9162103545100501509191248010f00844c0e180c01d4801c22001014140007000d040c0b03a0b1005086000180d8498031031a00e50040b49580001d08a0340548480c0c0c6103046521014500700c0d0b02d81d000c681c1564010308056034241e4071150100b854550780150042060300c507004050403801020b0140c1084681c1d800406164400390300040006e002e0420360b0b03044030840c100411441c03624600caa000a00000310721246200105030030a0b0700764005030a90403110012000c211445105800701d0b1103128038403066088c0d034482481000300707043c81040c0000030424400500d0402d401040c0c22550040b003500e050703078420740328041400624060f203d5800340803410b103074282302c11109141140d1103e41e1031002030b1115101100041c005004e5400482c0c0c050340c400d40041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879598902 1250 879597652 879597661
    0x71d040e0f0a020306010e010b03040b040311570409120503010306060b040605120c130608060f040501051509040212180c1203040504090206070b0c1c0c14070204090209 74
    0x103079504000441a842417150304000900c1c880740e17000d20380c11390316100011841c1d6038a64503203c805240190040f001c200c00b404402c6034100c411300c00b410f50200711031803007803001d40d003111402c0c480d11450000155241d0740744042c14800c0560090518404a01004e003000300c1980c42c0002c004180d000c4016040c43c0b00c0388120003185511600442c1a64410b50b8100030369500d50361a00e501d4000d6010310340104804104810f050307446107455030f038048120f01100d40707021000427080d22042e4031a0f0185010810503000e01046183c07280c0080c03404c1d181614200203a6140c200040c4140c11910703807658115400141c15803550711190100c03030f0030018407804c0002d01c1c1803c1c0b0380d4400c100038036200f00c80c0341d009500c03000720f80d8036115000100034400c2c40300030342c2083d042002700801020003101c1260b10101c10040280084e1184622034480d05507844429220082001c00d10903070188091004011841d14080c51200e5800c9074400380c00e1100caa4003140c480c100d07403001c02c004010024001c7e50150f824030400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879600152 1250 879598902 879598933
    0x40b3313090305031008120a050c07170123090d080a240303031b02031b07030203010c17070903030504060c060e0618010b030f060c1c050f1509071d040e 67
    0x46018a4910015002641e40e0341e80d1b60b0b07181c0e042004548240b5408000c4104100d00c02c0001d44000c0c400a800c0c0c90710b15566003a0802d02c00a084901d040b00c0c1d4588107071f038001051522544409441000000149203021090107881d42e0418400f64184200800414800c002c198404207103803010f00d17804601204502d0400109411600c0304500103070904005241520310a03c101da0880800d0b00154204403010240007001a0325010300d02c0588588a00000581c1d001d0191303c202d202c058035047d01c1d445206c000d1458000d0020010014007507031a40c1000002e6120003101e0844005142c2440e49110310710342076002d0103192076080481d20035401032107644101201c05501020343c442c020405462140103054640c5404903041c00742e90085000214070351158401041440e0041d013800b4a2080c18401403070448405403040a1458003038010000c120801003001407800030100c030514681e10f841e2070001e1200d40c10405d8006c011003003032020a00c640341c507044030288890360720548a00c1700361110f10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879601402 1250 879600152 879600157
    0x10603030e040c181401032a080105102109240b0d0b01090e03090d24060312030f020c0f011e06050607170d050906040b3313090305 58
    0x154400c5141014000205004613100d9080c2020385901c00e80f8146031003071a50480c0140d4000750705254603140c200c03198546901000554580d201401031448644000041030340c1d10581109001c0d00f9080c401701c60440e00404144050b0b88464440416030304034030194405080e040030f004088642400c0710304aa0040b2290840c086000b0f02d0301000021180010040000e8910304003602c5d1030305100043c044030340d140d04040c03400c01c500d2040740d281030260b8022503c18842181c080d201588041c6401415050200d0354040307009114505000c0d04c1e0464540030380040f0301c0150401032507601e5007040c600e06000c1d0103560884007904255100142c1c0c10080d075019009038050030b0321103144600c1c4d80ba11b0500922a0302c007511405401241864460746d40c0f0724618511014801022206111200d40345841c1c0c0281880398442c400580454106032501c85040b460181800f4940800503400b2980321085208150840d00c640000d1280b003243c00c8045015005030003240d0030301c07a080525a20901d50031500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879602652 1250 879601402 879601427
    0x261c050309010b060a090509100f03080406080105031c0c02010905121b042007080409050c07030f020a05060c09060f030703020a2a0212031303060e0c040e0c041d01060303 75
    0x284051410303082001082d1103a01110400311b01d408a0078451402c0104001c2d0b404042480b551014613102c2c1c42c044404002ea60048806100001c1c003806003950001c14540188800d0f0001c2c100c0020058403019404841c8002c00c041111810b950720540e07200c1c0d03001000406c00940266000451003400c15200c00041d18544034a028190320300015042c40c0c40f50300c1d01e0000d504503103070344d22848143d0304140c0c6d8803101c4140d0b101c07002880041041c0e0080c0c0324407400ba8400d03c1c18207a0b652024034000e0700260000d070000c010f540050448801192020070340715444442c01c2140c1e603454015000103011b0b402000e001c445500f00c04010000c0581d019802040c684c045521040030039012040c1074428450785603a0060200d01c2c0030321420040c06e0025140e80242248400c1d40e00b028006c0c1501203070300c0d0b8198002d484454460480c004c1c107a1003400310300b50710700b0242d03010300c02e4007071144ca0309684810504003e401180d40d1402c43c4117056820031030150201081000340606030752030400a1108585a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879603902 1250 879602652 879602671
    0x302060a0c140f0d020c03070e09030d020a02072c01050609010507060203040f0320070905070509031b0424030b0603010e1b1f0c1401020c07030b0906070801261c0503 73
    0x600c407210b400d0000401c11b040080c001d00404005040008008080c100908007244c18071050040003040761050024005401260303005090039441c2c00c015101072540740420100c400c01d5040b801040424409416040d10410303680142c3d900b405000403100b520030f4000c0038160500c088140810480d28030042c01020380681d582c0d080c8840941c01000004000c6036108940e0303170005104001901c7e131500469800102400d10604007801c6801081c00c1440310200d00c2d01048484c840b64409251500c140c11038407071036000103544640d1000b0714001c4040d1500001d08642d1881c1d00268650741c003500079032030707480007001514516070455105002501c022408284140c2c074840c04460842c45562110b0000f110655500f0403e17811600e42c0e90340190000310b80c4085540030011b040e4410004c000c01d4008511403420040d05140000306039040602c0a049401000100001049140101004912140040500f20070030180e100950fa01e41030312407482c4a5041044d5807034040389500680518410f80006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879605152 1250 879603902 879603913
    0x6030b010b12040308091c050a021b0607020f0d0f0807060507050703090302300c01030e0304151202070c140103050a0507050f0c010b09010308090a0614040302060a0c140f 75
    0x450301d2481c81c0c003901c20b880821140100020780420710030000f45800c80498000e44901c1c6014120071031074050540140c40104500040c5290b18503410000303030940d0542c480c00803100a1110001464611440802030300c1174141c41d1402e0415620100c0b1850741d503178020706003941d160503840c2a24040d0065601aa48031785000d0000d5095405207048035003030340d81560b42d20b01650441c0d0801040482207440d00c0c8a01001ea542292003032414103042d010245080000c0a40a403024001015104880b00c0701d5525001403008011a01c81c054807004040d10b54100960501c41c82c8600d07078000e008090010f00b03d842134941c0002d0441c174800c4941c041840a076014801603451181c0b4000f81c941c140d030000c0010708100b21441e5404031a02c09003071a02c4019001117500c10006c800110034070360a070400d440d502400108200d41c0e140101000c0018070007400c140050b181d140580c43c00c10301507448040c0c000c440004446900900c00c41e0500c001c10307448004074035091042818240e40f000a10303144002c600c40c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879606402 1250 879605152 879605159
    0xf0f06080711072c040c05030f0318010309030219080a081305060402010522080330011e05190807051e060c010615030203040507050a060c2a0906030b01 67
    0x242e0351842d02e0264003402440360600d0540081507407918202000640040c04200d0a03070155502030f03441c05140200c1c40b09004c14200010582480313040c64181c83d081e48204032203800034180030104607141d442424001221100e50600b6420046481e03041d142d0b041300180702e00c04014800d80540705d0089196101ca40e030703545800c981d0000503545600030f04103901c00d00016005612810050110f40380010031304404e43c0580c0749001c6482c4454104041503000454059086007a0034040b8080d02d02c0907600042c1c54138070310320f840391008060054a0200b10b00c00420091342894009260003400003824101403100e9100c2140b85043d42e5018400c10380c028141c00068038941041074050581c900d112042c2c0894a0104001180c0c1c01440661030325501c0e6200007540c10902419960000890386000d42e4134545490014180f400503041207218801d00310340ad01c44a907209850a007260b034402c4800c80b9000440c90320300d505034407040f640c0702d0122000202081c02006070f0400c0c03040380d205000c040c02607601d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879607652 1250 879606402 879606407
    0x9150c0901020303191509020304050609030720031c03020307030605041506031d0105041407060912030f02161205062410050c0307060b01021506100e04060f0f060807 73
    0x10344003449005078024404034242d035100400c1919105c90117035000886d60121182d410442e84d06610108a05901108010a0100900070141d214812030003640c030f400d40395507800155005060030f00300000d021214140d11600c1c1004111811083c0c20742807940c46110b00c0008020390b0084443e440020b00701140015507090500482d075403a000d0020300341c0c245060000880c01041c1580140c102e62000400d510201402803142c00e000300d0041440c2c00340c440841d180103242201645c001e10070003003034603010806144401102102543d06192120604140340700403440c106142c00204a20440c0f4000020a0480340d0041d5021038401c04c142d9007690f58100c0f070158101c034a5050040e14801c659401c030090315100c044070541e070065082090404900580325844c3d5001060300302d1394030740c0d910100c410355070301003040c01d0702041404050750203407800c1c4000c140c480200440c6803007400049403540361590340355004500a003a8410317140c6546580c800b100c080d030220a110b50000304020b040443e00075403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879608902 1250 879607652 879607657
    0x100810060807050d0503160605012102011b050a0c0f090e07050603070c030c06060e0f0f0712050604091a040c0e0c09010804030302210402040c0e030c040b060f0309150c 74
    0x207800c0030107008518684000d00c24000050002281c2c00d0204200c1d02d41060392040c180350880c0e01a8000041c29170401d41241c0041400d00c0d41c5100026000d41c4e00c0340140e0740700354210f000302c012424845450f081c900d8403601d880c4448200034100c641403040132800ca28080d203144210b07045804140072216203414019114078190041d070360041c5040000406141c090300e11500c0325803107442c102060b0b0641f070725a041100c0613500100407a40d095018010034090038108141c0010280b035180c4444d00706590044c0801e1018604500c03690348400000b24195155805001d080341c101d0030000c50842200309841d105913049404680391600b198020482c0002c0d41100340c4202e04c1242c0e80c92820703401c18010f403140d800040c0200c04054081000703c0741c150518081c0c001d00c541c1c1c0004111181030501c104002e46800b07008000810003051035540750b90782c00140922510400342d9001580c52050804155079205000790500e03070708000824400181400030b41c6040354242d200702074081d07840386003903141c1c2803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879610152 1250 879608902 879608909
    0x52e0605010c110307080d091d06180c0d0903030519060b1615111c150902210412020f0a080706180c060f0801120f08031e10081006 58
    0xb50020000b10006081000c0c91600d41d4002400c80364800c1d62840c050340b9040e001e101280c0040d0312040200102c01c0450710070b00011b007002c0050031a51401d800851401c0d0320b140c4091900ca03424402203002036540d14100d40d000800032a06000000060801502030300e070941b03c80986c5003201e515a8450b40c000c1c40b800c030958000400c19464108606d041d056454050316081d0b4403000144043c0840340c04603ca61405100d41520712912680d02c052a82c40707003440c10302c1c5903841e58100082105401c00303461001c02130fa91000b0700182c442c2c0d0b8210484610100c00300788404404190002e00007030001410045038110155400c0381d01c006855030820b0b40390010040c0080c40b0700c10910a41002070395a800c0402e0740b0007200c12a10200707006484555003141035602c06000304000b0130300d0300ba6456000201a0241c01e124000340200841c0780c2d00c525103400e550b0800380104402001280303000c00b40e00740e110641e40c080b80313440358503040801045100c0a568460192503101d00044504400c0903030041c1e0b0100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879611402 1250 879610152 879610157
    0x2040f0f0b0405030a3804260f0a0306030615180e06040b040302010905061014030102130b070f0f1209080606030615011107031211030f04140a03052e060501 69
    0x2103003959200d4001b02120440d5800000642c0104a036002c86224403507005000302003c0320407802c113402c20305000d640900140306002c1040f1080350000d4a90000ca80e2180c4401d04a20343d1010b0b0031100b140101019000102164185651901c1c1c11013450f01e18021b60f941254880d00320b000c2000c48a080310788100c10303008941c00030b00000c0c004c40c144081c80c0ba40207003e0b000220749c05140e969600e041810803684440003080104081c4080e6003c8061060990700c258001c6284c4004d107140400380110500c91490205d4000410784204a020380440b66001c1d800141414000000c0c0741a0a940120400300000550300e08000030300004002440c50190b0703009805403616840300c03088070714140015040203040c49a607581e804424030042090000550142c0182c060549180c400100081c0f40300a02104a0740709120201d2260107800880342100c142a60405202c01f4100106020380450780c0041d04074007032120220318a4003500d40031406001c00008400395801107011001c100c905d180602d500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879612652 1250 879611402 879611413
    0x60903070e282406021f0207080703020d020601050a120f03111905160e18121309050117030307050a09050a060201050603010507090f030b2205071418070516020402040f0f0b040503 79
    0x3080408860b1b08001d202c18500003524081c40f6444154455006d094100e00580c03104124030034495040c0080d6001d040f048400d0184c0c1854800d1800701c0f54000342024006110b910030300000c040c06444190340324ac40f0403055440341138041e4051001c81502031825207581c0924a44040c0f05c00b41c511041c03042d01c1c2c542030380f0241500d078900000003415401d080d40140d4800e8203001101001c3c20401703082c45011040345e8000d0141043c0142d07050f40d40c180d01a80302d000081c0d6654002d1900802074960200c80c9140c01a1140003000c0c2c11200000ca0340d00c201e030030108200010590743c1d81904214415074064000303112684482104070f411040d140303e08103001114280620008901c42c41e280d4100304030408403811071205000c000054040d4007412681d942c442d180400c10419848940b04801200312000c0c8222030007801e1541038090010214020410000790842030300680c40503000e034442d0090811515540c460405007103030101030049900341d103040034000030a10030394030486090380c001401509 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879613902 1250 879612652 879612673
    0xc0c080c0a1e03021909060e01031a0405010b060301350d030902040f06080d140a080f190e0606030c1903060b061603020318060903070e28240602 64
    0xc0c16a07901c601407000310b6148040010243e9202090250b00c08801080c4002840c980310340f030012a01564440c2c07513200924401000400d41d10186c00000c003401c40801e01d00c0d40d9451030410300524a09100300e6004074048000300e002c090140141002d102c002940b070901d1031825005103228528100911141d40c17048413011001c0703210fa002040c078544040c00107e480d000c5100200e090381e003542c0000d0210f5100007940c0c02255030180d62043d110480c211034610b003a0f00c691005000d100000c2801c50400644000300705c185001d0304c580c210304100f100082006e012500d49041e191101902e18620034131444902c0400c2d443c0001001d0101607082600607095441c517519003001d00442003c05901074070500c5002074446022501510184c82035002d103558009043c8440096980c50300d0300c5001d01c0c401d001003ca6505e001501c03e0170b4860340c0100d50041c0c0d5078082c46213402407030900c030303e001d103143c0c294900710040454121400c80014581c403e0340f8081d5214a0200001d058407440005a00040040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879615152 1250 879613902 879613919
    0xd02092d010f020f0f0a1b120f1a0f06040c09060504140111120406140c0d0e03100227030111040b03060109030c0803180a0b1c0204050307060c0c080c0a 67
    0x280c01c2c08070380e006030f48030400d90b11100c1c1c0c100060000e9034149500310240400800c4100314507004950300710b04403130302420b041282c00407250300c034180000c0290340446000014070140658407084031020410303220480c601480000664881600c42e54019401d00340b151800341c4c05050b20381c0035200c1c01c3e40c410f410940b03024045005245018481414003644070904000c5d103005218088102410340c3c44541e5451400c2001810f1826444580c4034407101401641c551860220320388000e1040f030f1401c11184044030000a040007200e118030034409100181440720700c56400e08400300d40c450f89005070300b0034000009050999406545081076850b0401040c0710310300c0c284003e941c000b1018500b500000d912650388490701c107004e401c6529640d0002c40c1c1e0301c60b00040c0b07480d5444210340c01e4852248017864000c405a0601a107403190180c0b20316080000076640c0380d0f0b8141d4004140040450b01119501c40c40034105c450032050a456501c80900b0210f80404000b07503c1d403441d100600000c1c40e451426490 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879616402 1250 879615152 879615167
    0xb0301020c15150a080f101a0111100e0717010e0604030f02030c03070c050301051b091509100e2e0507032025030203030d1e020d02092d01 61
    0x303c1540340310343e504a2141d1a01d50545000c1e2454000400819a02090031403904076060b050420315414500702140d500c00a0000315101c0a01303080200025065810a50500481d402424807051030310500b40501790001885104943d6040e00c0f91001c110500300b61420389541284a0006038061400b140002e4031642c1c212101510600c1501d0030004a50300950071680b003003005840340c028070001404686000c0c0704040d0000c034128031060150450507110710960141c0b010761841080a0304140004042150848140000081644080c0381d0101c5003d89021a441d0045001d941c682034440096100c400c60510b41c09101c2600400d08880382808690981c040801241003144124411032801e8001c2c401c0c078821a200b0001d000b807141001075402500c0d92440e450803414a90341020000b50320301104841e0064041d40002c211861060705100b00701a06080c1100301900c00078015105464583c00b8000d80c0f14203c800901200c906141d6034420381c0b62411460707007104030803111b40d1a507015000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879617652 1250 879616402 879616411
    0x80304030c0f05060402040507021f0f0b0a090e061b0405060307030b060307110c01051809091c02280206030604050421021c05040612091b0311040b0301020c15 70
    0xa1007000100307150350700c41c001c144801c401c44865003c0d030180011450030317005d510340c44142440207022109104407040c3c20f03040317840c00b4012025911006c2486001d041d82003102160005080d003080140e80f400c5a000400c0c0e030300d003024028001c140102e81d1a02d80410b11500707100c0640f801505244c01c10081010035800a000501810307034805a490080c0c0342c2c40051441030110391108025100c1041c5400d007422030600c645130400c882080003491881030182039001c540400da40740d0495564112001d89800707005844020210303c816503517076450398002082d401149650110700818080d81d01d50f0f00d9071205020b8000e40c800c0013030000401c10b04003584000d50141c0100c08038020300801c40441903400b06100e5180c001078001ca15604c0303142040700100102c58040d41b41007482c2600c1d00b4001000d90f10700005c441100d94540c0004400d1000b40101c003560303078103080e40c0102140d58070b180600c03215518101d5240290300f449042d8103a03181c10b10070364600324150405040301040c03840d04648000c10050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879618902 1250 879617652 879617657
    0x50c1608030712060b0c01060522050903040f08060106030612030e011b0803151905010804080a090b03280b0907030f020f0304030819050606070b04060e0f0102090a060e090408030403 80
    0x102c0030000c100d0f54015140240451140282d441b680c46002d5401d491094014901907002d04a402311600f0a02600501c2075559080c0003401c0c0c0ca9940c1030038114491544034011303004448501140d01040458454101c0c4c4141d00c080102550303078112040e040e003600401a0206008084c9034030760354001c4d401c1045045a02da110341c0a4950303580d401816410641e055000c410300d41000039403c0c1800d000501d800b80007441c02d1030b401031030b0a0000300000740040c0000c180c085e0204802020310300440c90346000d4516041c0c600d0f240d00e4010306440c40380174264407809141c0c0c0c401c84056500307649445000604d004c05018018180d40f0070405501824a10a045a00541c00c00403940032001040145014034440e5a07880040d0400940e03900a024541a840c065189000c080c420540e031000201c800741c2c2d80c01a1451442d0740c407814030100501101703800300e5560262400480e500c8506500514482101304d90341e401c441d0b190300b401c8800f400140741891700001d641000c180412400c1d00551350040c17292 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879620152 1250 879618902 879618917
    0x3030518011b050105011811030c0f070804080c0a2309180102070506040b09060702071401031803090e1609050607021c03081014010509010c051e10050c16080307 71
    0x208100c0402070310845081c3c5140e5540c10051140c09114a003005005e006004280002400f07100a8000c0e4400a000300000c42c40000d022118185200261000207800548041d15580e03901d0010fa2034004102c8124030440f8106000b10b9805000d4452060151040200b5800700308454188104c8440150145481d00302102c002c45c8202400d0008100c07580c410000303009981010315003004030081c0a00000c0a9400c201d0402c8201039002410504840b000708045003840d2001005030001c0904082d041c601503094000b640c1803503004110703681114000300d030f4030401783d8414025030300107604510020002140b000c4100681d10b0b100d006030040e94001012444042c440d18041c0c141c5100d126400c60101c0c55504c2042910701c04540500300030104004115000002700000911601c0f03858130300d030b05008449006401b0701c80e08000c0040d038000404003035000d60001044036a034961207166064a528200000124610b038007a0035100e05041010806000c0c100642e10040c29400c001c100c0300070407011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879621402 1250 879620152 879620177
    0xc17060f010e1e0f1804060b1903060518010b010e09041403310f18110d020904061d01061d10031a03070f0b0702061b061608010303051801 61
    0x3400407041e074104030580d116400100c0502406540104445854490300317080c800880800c42e01070080750b03c0ba41c05400080e070040c03500c0c00511060061a6824020b158002c804002c000079907105501440c0341d10284c24841408071815401c1e81e481020711400108034008180c42810a0030b840c80e0082c1c45041500300113072800300250320b9904101d8a4107110250544110001d015041d07040c0301c0780500000d841d00380d0707040c072141400c489058424160074a040005180326810380b544407403c00c809400c80151b40d40346920110000c2e40041d103410744158a840c00008201070803140341c80542542c1d01c8001501c1c0e1030700300241c400740da110742030102002c0a8150040b00d56a140c080b10b501010a407030000301c12081c00d000310760402c440740c0500d000e5801b025087c4039026100700300c032040700c40c04410306540d0b201610201c0e9060083c48910603034105284440c0f5406880483c505100f05070070710440700100b01c030700d90468a4410038030026011407003c010004600300380402c5042917120604180c00c00210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879622652 1250 879621402 879621409
    0x30429071a010807030c0b07080903010609020301090f0506090a0e07120302031b01050f06101404091a03030a140a17090a03021207051e0a0b04060f0c17060f010e 71
    0x205040741c1500c50307181c80c20280721401c91068050200c04004003c4c00f4115035400c240100d40740280c0040c8900451340300d0030000c49108a459006028000740049035950714840041c5d003003030142100e0030b81441d5900441001d50f2203618410308005010a02c15110440c01130300901e501c0107018510300500c003000c261440350a07030002105100e9801156220351403440c0354034041070504140e09990400c41402011504041c5c542c0e04203208403468a05c40795502c00503070f012403181440070048480802c00040d01c1d0215840203036818140d15003210044100000c2644a2141162640228043e03260b01040c0100150150074050390785d041c6165814440c120308814600212400070890b03100358000c9080603410300c10b011405259000d40d5090080e10f0b510b040e04c544256010444040c903610b00c00c5036000003002041860b03508100300d0030050500d810510701134070014402d018002e003000d070441e01652145500502100c4011440f9201c4e071200d030304100191744c003100018100211103080c60314564 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879623902 1250 879622652 879622657
    0xf06090a06050712090815190c0c060b030303040302100506040b09010b1b0f2509020307020a120206070503060603040201020f030309240906040311101505041508030429 74
    0x92035114140c030769403c0e1915800d0300160101c0031080024081c0c08210500c0f000840203070300c3c4800004ca41141c0e8418046142d5a10903001102d429800c00541c44c101c0c80c0c11900d44450180610006d0040c4062503090507903230701c0241c0d07000b1b00507031101c03442c1c2e0b40d06150340c6e00203a00068010400300e44151502e00080ca101000c0e000f030900c5410014400d42c019410359520451020309401030310300e070070102c60a540c0714861088840000182d851000407058400c100c0b0902a211008046403681007105000703648100c1013504640c0504042e5000c0300c940d000043c8a80708002e103640b8181b0350341d02c0009000154101130701c202d05600c51501c18030341201c000d10103148075000e550010000c9101c28200451840d0b110501011842000c1040c007892400101c2e0b5543d206807d07060450025604460303840c5000c401c00301012201d1301d0a0240f00c20300c0b05c001a5001212000c5074103200310b0111a4400c18040c41c90321800100798000c000802004c8000c0602c0071140d8200f00c007030031001000500c11062035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879625152 1250 879623902 879623909
    0xd0c05090f010612050c03060f06130b091e060d0e0f0a03210b1003050711060423031602010311040b12040501060e13030305151809010501080a0b04020f06090a 70
    0x250001d20041c40829808140d2140b241a59007040c0954144001128560310024100501900b0f20320024001d41d102c000071101482c405c2114200400d560308134100954100920280c41751480f1284040154000780c07a2640000000301001d14168080320340400410b2400102c1403036024407110090104014444080418001d44078100b0010780755250948090146a400420354075003001d4040a854a100c2640c045d1001c2c140050349881d011016101c0044200c1501024800c003c1004100400001403990000e107034001849803c0a0321011903c81c02604004100301c1c4804032041e01644c46030300300002c00da18021204e4582500d84010784070300d030f00c1801c010a030000c892051104005003449403200404252040c10954140301c0782c1a195508611409010591104045440002258200c00d0000030040c600404001c0e44040000d07500803c03210804a5440c1c10000503d8220110355202d0859000c1300100440c2e075940c0c204040c01641d0041c0c8d0350007503414042034125072038144440016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879626402 1250 879625152 879625171
    0xa090305060f0612010e0601030f02210c0f100806040906020d0e010e0d0512130309090203040b0403081501020d1803080708040311013e0d23180d0c0509 67
    0x501c1c3c0001481240301061407521040ea140c10703618141100c02003030041c1501c0c0d0002581c20325216500004109040030100d00d044c185130040181c0f041c40c0c000030040703210079041d6a0301c4c0000301d4010801c90301c1e408041e078410114002c40e00107860392402d46d004085003807169000500307100195414400b01d45e4000111180e80e903440c402038150400070000004440302c0352030072501d0a1006006880c0a140140c5003414500040030010100360080c03041c88090480510119181d20341810310000c141030503103041e4085030006c030200c0c1c1844040204050420030680041a801c510f0000442e01400c0b0300907284c622446d54100400011a83c40c000c2c0300d660b00031079a880e21b9034114108030f240898000221030521440c0c2502d0b0700e059100e0508179920510460640110004014160070144010714501c1031074021081501030342a00300c840d441c601045a00c80c20360400c50596034405920800d440f4954400e46054200e0350392401c0b9000c582560310a080d288812075a50300400c4018800381c2d020740c403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879627652 1250 879626402 879626431
    0x5061503010e010612020607060204050d0303050a0b0d0305090105090a030b07020d021006050a0b161703101a1e0d020f04061e080a0c0c05031b121e0a09030506 70
    0x8280c0340900900d150010150000c000c41d6162031550741440c0b80f0610028020a00810280c044c800a64107640003013002510040382441c0a181c010000c000407036100d50300d50700d45032500c03250741441100c0d008040e0341074458a142c0440e503001903850343c0018441c0303940500d400307501100186292001c140140343d1030f0000c10151640c940b010b42080c1c0002c8072078400b540380081c1004079541e41d80900040ba1039804d1a150b0340c8210340001d0343c03440418440644132102c128482400f00e405440110b10440469400c00721058407607408800d501080b603501004820103000030100d4403c101500003505002003152403500d514000300c0f60683c0c000203c0c64810540102e420010700b070304201d0380c1158001c02140b68000307138138001c00a09a100054100c2a5940e0344126084c2440e000702ea409082c160801c0480e03458031200c2d030250621140901401c0401e000343c000044c0392040300d5042e1b44111000e0b1480003503000b070b0051003850031b400c003e013a0810030500110001c0400d0b410300c5090302030000200c0001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879628902 1250 879627652 879627691
    0xf0e070902250b1b0c160e090a0c1503090b04080d050105010e1008090732090405061603090b070c0308060108090c010503090c180411091b0d090506 65
    0x100c0d01e11102040b00300003200303100503400500c1d030802c03c6921401c0c01d00c05141350840440c421856000d2040601d81c0f500c10700c00421203049144410300704a0342d003601d80b84600d50b603100d50a0345404e4015001408403404840510500c10820320300c3c40541c426140015004a030b6458141e0b51003020b40341511645400540601400203a004080c00340c5400c1c00d00602c07800b14040032542d00304203540c801082100c1040407400710941442608d004180c406c1d5900c04440c107000501c21440810302049c000745003420000505800d116400c54403d80d0890040c1105998a401c80da2501d04e885004404040d0f80381b4902c0005070341500a980600441d6980c007980e41984d00d801340180b40040e010606000317609040010b85000020711740d0840c0d0080c0b0f041500d984500c0c40081c82c058030714141c07a40c0007920b1020381840c640300e1103034584920f0060746c540400d8849a030074015814029511640f114484070240d505030069940202001c11042c0800550900580c5a107401d00c08265034a0007048043c00c90030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879630152 1250 879628902 879628927
    0x12030c020f0a0e0f0604020a0f120e070801020408190f021003060b030118180510110408010e011509060b040603051503010606020c18010e040210020a050709020a0f210f0e070902 78
    0x1981d00400c00d41b0214038040c9074000141150703552200e282c040011161042c80144515006a80c1c0100700c2c10031688036039201c0724900d020303411501034183c00d8400c0c0c0c207585040443c2c0800380c0030700c0e642003511a0b03138604594003807003180326500148005164907000001031740405e000056000303095501600d444042c10307006c400107641065881c000c1c120b0108034079401045001c510a00e10441c05400000c5180f1042e00b849100c1c0038980c001c2070355500e41104149006010b4001060118241c0d41046c20161140300c0f48040303a0180c010f81c41c4500040c00144076180c0243d00054021a05444c04101c00f014580000d007524403d41002c0e005030800f0403183c001d401e0880000d05480211103000010313605110a000c0e1401700140064825501103450f0032404e4000d1100f0300c1c480c0d0300041528142e5448020810103903104584200c0010302c07100e403440483c0d200703a5940e1010008500100700c48400303408a0340150859400c5901495507543c400c400b00c14041050200a290f41400982c90306030401d4070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879631402 1250 879630152 879630181
    0x12090b0720010c11040b2101020c1c05070320010e0106080d172205300705150a0204050d05070e0a0c08160302070b0f1f12030c020f0a0e 60
    0x781030141c0c100c3d410380011070340d0710309010402051340c000500b500d0807000205414110034071001c25005c81c0c6080c62000406400401100340207000700c0d800d0074141014810700b80000d90340d85002030f80501440e80001c0c8a0184210a0f1641203140031345011140382d040d08484040300707000740c607030b540d603904112401c0d080c0f0564020740428104002c0034038150303850800b01e0000900301020074a10001c1d0781000b403200b180806482da000005c40381c451481942c10f03d00315031a5542401883c1c44940107000c8a2030700e100f211540e6030700c207000d0702c01624191180d0b01100d80180040f03456039000d101c04a0f05444a10440304000e000340b0007001036a1605012102014010b4118074180341410760021300c0d030fa00b040c0590303088500d0964028141001c1d60701100240200b110003401c174a1440c080c0505110280303603c500a8100f0480001901b06804000403118141d114680e03402c0076500c20301000c42d00942d80d09500c039001504c1140401d1084c40064100030031500b10b40d40e10b00c854030a02c40d094120845 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879632652 1250 879631402 879631463
    0x809150c030a110f0409110f1303030908010510030b13050d020309090907381303110102070f0b0c1509010e0d1103041703070b0117250312090b07 64
    0x1e0692400d400400c28002c2d80c03040c0d010b408012620347c6440c0079084011400c4071a803d0070b02c5030840d142c8642540104104aa6100640014515a00c040790001041c0300c1d290140350b10007071081d0401d1031560b49804200300200b81413030380c609000740040400d000340078141c185d08055000e550b445a002c1c04001ca00080a010340d0301540c040312091000b080f0f08014144155015407901405010302880e42d8420103801203e0300031703180d01190fa00b18140d228940070055a2241c001e00080c0c003032500049907100400e108291400002642c20001800c050000b0890b160001c410b544045003401c80415200100741e9030505030380e5442c80d0603010b4101c01c2c0400070705000b030751404010507505028980d40d01c0c00350340100961110b04894506050390100300711102181c0c0070084825560f07545031002c2c00300c599928100b0260040c40907290240040e07034061480f000303804126031041811601c5140c24072071001070602c1031040220300400c40c04442e0b405003242c00d11415000c00f03038080c1d040800c1c481452055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879633902 1250 879632652 879632681
    0x51204140f0c0d03031508030408010609061202030601031e05012301230609010903050d0806010905190308070804051c02100302030c220f0b0405030606011407030809150c030a 77
    0xa800758803643e10720070315450b00d54051601160750070f400369981c006e00855512600242c400010300180404040d00a001141c07034064041100d5607803984030380d0303224612110082d41504000c1c018800034034081e54240090028244c00114040903603525421161807544503114500c401c10001c0e0141d15446031280580a04c10f6400700b0f41c0000c001d4001c070401102061482a040030800e91000e0340700340840300046411204451124a840c00040c10120003900d1707050014513115000f20300e0b0b060020010900918041c0e603c4030311869a00c85601c03603000301108440c6098104000916951001d1103407268541c0c036081000b03058264030400c075050342454241c000b031500610401150807501c0087c2d59a010302c0400c44e0300d080f0a02ea0034030b0500b03c2c042d0008010020f2080000ca640d24409002e4025a10305030201c81080d1640030041d00e04030f400d000b0302042010200100400030713200c0c5d117549030440c00420450b25000700e0340981007a545003c840000c182c410100810918001d20300603044800b6244 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879635152 1250 879633902 879633913
    0x609030338030f1903121d010501050a080706080a020c122808010e060301060306020c33011a070204090803060f0a080d0c0809040905070e010f0f0312051204140f 71
    0x85100135110b40924242030a07030400304c1040b405044c001d440c8001a490051001c10070202d100014844802070010b000800750704e008001714450030111010001d0362a800c0090628924000003103500034001081d1203980b0343c0901581880e500104440403c07042044041502ca896403000502e0800b01141c290344540c41103022071901b144c01c4408941522503610004030a42c1e03a2401190142016074801030641e032000440016101000c204030385902580005030f206851812a04e400000e00344541c409d02d480118010814910075444402d003000003414041c2c203000d145d1300081c003229003504040d100024000204440e40c9840040120581d0f000c80303144c0662420003405658840400d00746d00184441c1c00d4900051041640548451fa070000384244140551480e20a803508041d03c17407240210b02d400004103010000009031429543c5092007040c003d4070f5034840b1075040d01d110180341c0502404220a0180811310080d2502c80c90161841e80040c20401c101b40745010a6402c1a540c140c022 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879636402 1250 879635152 879635173
    0x807080103080909090f060a0b0a0602071505070c0902160605091b2b320c010509060d0504061e020f2d030a050403020d0c0f060903033803 61
    0x42100f5142d4140e0155540c894640c1d0b0310240314500441412209850701c2a1001c00500180f11b420210f0303908410340f01c43c100c0641d103000a0b41d4801480c0034084110203403091403002548640003034402e850113880c2200c001551400b007070040360f1100482100c0b080c66440350500740a00c50054070b402081200c000c2c100160691044414000c0c2c01c11428885d8400a58121050110041c404542498400000038542c25403030078805c1e000c807144502ca204c2c9020740500348401054400001840c0d04000684807008407a001140c060344075803403450303002c4400d005401c5070072224450180715603c212000581c01c21010a42401c07150300c10081e24045004001c1090542e40e280c00f66504551500b080c1e80f45c0b404802070f0501800d2a941404c444180302004015480361190070641c0030714000e409850002058840841da080748540c405440c81c1851136011001500e95804420520b01031702c0c000420f013100101c214a0450403100c48120403240f82504080c907181d2544500c8400d20441c02004120b88 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879637652 1250 879636402 879636413
    0x5161a040302030a2607030c0926060a0605010819090b07030f240501050904020405030d170714030f1504020a030902010201061202012102070b040822030804090e0a02060c0d0807080103 81
    0x1c006e0070341c4105a19080003d0525000c3e551039805001c4425100780200807252441868146000417850070340714800110313150307445501c01e07001641c4043e9100d07905659000011600546075590050f4910303982c0789250003152060520034080d003550390b0045500201d40040d00c007920704007000021740718043c00308600302d0644418420100c2e1400c0c24207075140c40b000e200150090081c4d90020781c040c050040b001e10095406034001c21900141c80407203000307840b4418215004000c00081140c004010004101c10428051946900503801c1c00c2072080080b602c000328090380c10102c5c041012076250384902c0d04540e02030103914060940d6403e003008050305074000070304003c031000d0f480c5860304010a00c0e000700b4087d60111500c2d01d40010580701d507800d040c03405c1c03a045c2d84545e0042c0b948540c41c00c0400d500c500c14084000880c1c3d0010555400c150900001600405070b003c0468440d2150072840c20060309c441014003402e901c01d8018000040d0303d00005441701c080188007100700903030f200040c0001017 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879638902 1250 879637652 879637727
    0x506030c1816020f060c1b0c150c030c0a0305040602070e1909140d0903020f0402070f030813050a05010501060305011712090105090d0c060f05090105161a040302030a 73
    0xd00758000e2400110600c00c1642040403581d12039090317000c0c050030486e601056a006258401050b62204c03840454860386517180c03140b81d9800c03944101d4982200c6a6004040050400d0380b400c00d0a4a1810040f4142246800306111084000c10000b2400f00f1200fa0103108610080c01c180d150186545030500080404503010840428203640e24040c840a0101c140c0410b41032121580440e1f800d800661800f03804400305107c224404d8805071a020b50038100b0b8020f803440c05901c44035441a208850385c0075505288014840130700301c1c800c096010f011610030090206000c6c010350001480f5410400010306031407050b0405016212202c0f92103074520f90000d5002e400c19124510750b9100c07094400104c613107119001302d280e4010f08907402e10f0140300c0f80e640c1441c111000d60b1501d15165a410707900307486a0248014140c00700d8001e104c5000b80c001c1141da5022a10701c0b030390781c002d501c1582d030392003092011060350250011390010464101841d0810818582c0340380c442c0e092242c1000c4118809803c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879640152 1250 879638902 879638911
    0x11100c080f090a0c0806010801060506041d041103030f0304060c0216091a0a06120c0f0c060b150f0403140c090705180a120312060b12070c150506030c18 67
    0x80c0000000311002d030240200a01544d02412614905541d400c040340c0d07501081c0648c4116518042000442d854000211012540395503c2082c00340c00e040121184050020400c0d58200c1c1070081c0d84190340c2c3c00340001e0500026a20040d81c5174105414090300303c1d48142c0c806015513201c4502400541000079404007151519180428070141500d19004d076141240040c0c0c1d00321030307440008a40389401400744000c40b03a10b04810013525035503403411201c0c0c506080e041c0c00822000c00c48000450300c941c200781d55982000d0f06420034000304001c904aa07901c0070301e580c541c407078002c5000d2080001c0c40d01940c20180c60400240005c00003000001c00c142c401403c2d540a03c0700000305200c81905484101002e110000c0510740c409540303420389d02e11f441140c030048000a41c040c207041215440c0703101d0f0405540c6243d4105040c40c00b40d45000c8000003014004c1c07018423045990300400501c117441566001c1481100200b981c0c1805401d15250400034001c0511810568000036651180c051309030350300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 879641402 1250 879640152 879640171
    0x903330b011403090a020405040f1b140609011809150e010324090f0311011401030807030f02151e014a0411010207060c150203041103010c11100c08 65
    0xb0f80d101c40030204e103001c07180c0c038000790011300b04810041401040e1300030610803030180903c0710500e0b40300303005076282e0b14007405020350100698402d400030b404e0030f8001d010a0281030400404100d01508200f03401144e0368000c00070161640310749101161450001001032450326803044442d419560b508640200308100e004031ba000710100e41c601c958090f04a10983c60b0400300114103100d460034024644100000941d4184d0308000710b070a1b605000b180c15504a0350807070003a50030300c0b6140d5002c880d602140c1184004500c40e4481a10311604d116038064001d40a0f003500100c1114020004281d403a01603002c006010a18102c880400308810745020650001c1e10b8035140a84100701101041000c0035414084084032908100c20003402016001a180302602124003065880c8412035500151000007003005d1143c8000780250032181c0c0183d9001071003000321100c039864040201c0d0844852018a0000940e982d04104a88006000c40c4104604214060000314203243c4080d08444024180200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 879642652 1250 879641402 879641407
    0xa02030406023106020a050a0b0c09130905010f09080d050702101104090506030c01020a080a120e0c090c090607110f030a030206010806160906080402010903330b0114 73
    0x2005080e50484407011049a01d00c484030301e03041d900e101c8040d070a03028221000401c003c04544140001540f02c100c0741d024004202182a40e521404003c90260250b5441d00f0240006540c5a0b10902d01c007a0360710b40007100098055046c2072041c02d4900300c21072410194905486a07010440000c2152541000100007107030984075040201d190515140172000c0c0399150045148403141d00c42c0c000d204540228070b0a01c05e58842c0c00030540c4512414228902680c004009400092041e9028041d001000d061100c91a04180c100f07505a50360440c08444903040306584440038038004010741c2e044007511084900b071880400200d0303da0f20038a100500007882504510304603581d040383e43c004145014007603491001d1580360180d80c911080c00707204843d0040c0300000f0f0b128070b421500e0030382c41c10300740d03481c03140141c075108046d5081c440141c026410031010141c0071000c41e40702d85030032400184000007480ca4000c00644410024014440d51040e18200000d00300c00d40c3e8801d15440c0c9030600e440c1d1669 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 879643902 1250 879642652 879642661
    0x170706050a14220b0705010b0603061f0c0203150a150312030e0309040f02190e030307021005090a0b0406090b1c051312080105100503042102070308040f050f0603010e0a0203 76
    0x20380340e40042d0030a80f4003262454042100f4029402030513445101e01c1c0280420b0400d481000010f010403699950020320302480302ca40300382c141c0c03a00b401410b050304026503805290b40200e41007030314210000d0702000000060002c485600c0c8180c02c8841490340c0c440204500350344d10514170031240080700042644417000180280c2080c0304840b41c1ca900144104400000e074421344c006504400007007010340304940400c50b4070798001e5083d9070100b88000c0185241a049500b0030014210311118042004014004c1140588a07940800f0141012401150300c481c07070010020030071031154018048255060180c211103640d000c4402580c5111060040380e15a07590381c0c000c0c50b40020000c080e1444030b5400f038020050303802c981d00605840302036869000803101010182d0340c610050342c0091660b96006400e0380d0407407649115070818840380c4190303043c0b1030b81d0751601d8a05070001d41140c4081244984104014905404001c0c4402d0040d80c05500b19031420f9208442c000c1d0040030300c0c98070754000000a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 879645152 1250 879643902 879643927
    0x602062703041707030b07080c120c0d0213090b0a0303020a140a0c030804031b03120c030e0d0507141503070305061f03140f09120705070906170706050a14 68
    0x1ea010300600480c030105607481204061351450984010354405450350041500c0911414480703100e000d2165425180100082c0b0b4410f0401c801450414889030074084e001419246000412004c44500c03905203102d81003507212400c4800d5000307003e01c103411143e810000250081990f0310000d402941000125100341091401c100110000801c01540c012010041120300c01c0034105490240b80181c074820002400c05000307901074003016120030034050121502911625015010070304c24030707104c2d22292221003c0f5102050244e01120307190404241881401c00c4500030030312031b0380d04444c840f1a0f1481300d05001a81e20000d404c09007007648680008521340c407042e000f00020b01890607250300444c070304000200148000208005c03800480400b00c0d140c40040103865000d080c030036024007010803a40000181075408620100c6160040782c00000d103411542c41548014076896022018114200c10341d20701b80030103500440240320381070042205d41d6611a0461100701d040700303241c070f90364058001e82 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 879646402 1250 879645152 879645157
    0x302090d0503041805070315030b09072114010504080912070b04090506040c140d0218030303070507021c050601030f150509010605030f03091804022707090602062703 73
    0x2030164840050001111305403a4010b200130f00000307800f040300d0380340e03100114203440c1141e44007504213130b224400f440802c4100c080c06070021034103411501e40326034505a06c001421040e110b180c0e0000c81a0100e0140f0a09000221800c03114000030046464145c4e1902d109024011000b401800c40c22101c00440c4010050100070b00755111841c1c1e111075a51f082c8001502040701e0003402070341030800b104c185900802e601c0c01014509000d840c100310205240318029000081d2482c0700c180c605011004d02d031000d01c02507000b2030340ba55a95a46941c1401401200c040010351b031071410311003e0f5000d000c03800c04540c40381501d1380076000d141d05074800c1c246406100c4141c130039241d0986c0303040c007880300654056101d501240d900f03801791140f429008019a840c0d0050041c801d070401d62408100c1d041e0010803482907031041c8014840c4020484001ba58006600c0800600080c080b4090601202d40d420003d10402092107100404030791402161b818801403418200440c031444401c80f0a180e000180117 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 879647652 1250 879646402 879646429
    0x7060801032112050a0c0e0603090a0b0705070807060603060c0809030409050a0902040e1c020706171e0c030f060409200111150f0c030919020d08071103100219030209 73
    0x3c05121904101000c440141840306422010890301c9218030610300f04582620300c00e14098000d480c949881e0f4860400c0080004e040008018007048070340c0001c0c0100e009020024000d80d400260b840c2585004002c841c00ca00030401405000c804208002c82c1c008201c43c20341e840c120f804a42500d41054a00141c00c003000020f60060a140007070141c02000140003120841403010134488000c56034060740c4441d024027030003002464158050019440c6002d4180d0001002041450a0844642c000509060076102d95100e113100105008a002100c8582c4c0d8000c0d0048604001034401c55403801c1c0e10045248a903500d41c07102d0407103e18168003c412740e184040840050311859892109144860841147d0000c0302194035008203119002030000c0ccc80c400c0304124001c0c45150b4102540f00080ca5561200f2a44404d1006880d40020710301c0e4060100300d403188040030124415001054107200c0541c42e0f0042c25841800304040c2c5465040d85044500000e00740140c1d91240300303000c580c0c00d0300400c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 879648902 1250 879647652 879647687
    0x7020607060b040207150b1f0c06090f05010908120a0605060a03051f090605031b0d020114040b04090c021c020c0103021806030106050903240c0f0c0708030c070608010321 75
    0x2602039054414942020105a0003160124230700b980414011100251010038600060103035000c0c2d40002d401036114880d29400386c6003402401c04643e96035800d40c1d1010004131014800416182940301c2c40164164201022040500c03065007480041100c50099889100405d521580459485002c104044125032814501c41c140152a241090050552486064001c0c80f030880b40040440035080500300750680102922620403194004503106003540380c0d500425107040000103404545d040043c00204200c90700400d90740d007074201c082d00304030442082d07045411240c1c1d5000d01c030503408528511643c00900f0010784980d12203849407045404406001d41000380000081002038004000d8501008220121511224050315074141c1e440840e0004408a044401107425055079401800e410009001c8560502d129030030541d14021a5503c841070a07000002c2c007134440c403c10311180c0054540d50804c01010f5146684441c039500c056a05a568084a80c6403400c1d0184101400c4c445002d030803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 879650152 1250 879648902 879648923
    0x1513090804140603060d060e16090b0112020c0d08130c030515130c03081b0105040f0308070e0f0402090123122206050601110f010501031707020607060b040207 70
    0x240351001080d401030107a4104036051200d55081494954100c0344501000b803d2200b40c05c07159035403c806030400074080c1940340560f0342411345181100fa0814000c0020400100b071480280c1c0c0003410710120b0b5021407603003500400005160140010340374000d40241d00c0c188031655504070f11903480d18060b6000402000c3c85680001c04e01c4000240340040300c0e03154121000345c0e210428240c180c5155400c2c020a03003c0d44410800104151901070b04403444410400a624001e15144508440c0d045400300c403665510080101810391001c982d030351100c003d00b024200030042800013503440034904030041c40b5680008031aa0164850000302e4031491541414014002e010000b00d00160890080c1546c1110100c00007803c0c014021100000101c0780001c40079400d40300d844407001390000030042c605010a82001e603420752010094220b04100b40c0c400015194154038008804034000c0025031309181040c4a4800035075100c3e02140d42880e03000000107107a41034140031a01034000ca0a0162044000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 879651402 1250 879650152 879650171
    0x40210020c0d06020c0609071d060a24030b0105031b070c1a03011a0703050901121d100b0f01211503080a0809062e0330080405061513 59
    0x403130b0042e108503101e50003942c41582d1188a8035668001d10300c40c4803015408a001d400c40484241456500f0201c060640d40300c258844031031105183c01d80d80e204460360207d28500319000d5051017451844038092030030310304d03605018516854003d902166045076500026040b010800b0840110b0000c252402c4d55400d04102902aa41103820901c140752441d2441340032401f56420050480340c6855040e02c80b1814001c0d858011101c91046400f07000100380d81e5a20074015100e1140c0d403206580100b001000c1080074001904243d80140903018040c2c4545408155642e800c403c0780d031064681e9071022940038141c0f403502c8000d420784140c01e0600039144140881803100305d0300140000101c503280c0c1c081d0340d20f43c1c50086640b88001c4800a10312031000c0c090252003c102da0203001c260440d15105a80151281c5480070030300312186507408440303507101e403a0002c46038840d074001c4842424107217001c0038601a10f605890342e80007084405a958003500741201079076440e1b400c03840c0c5081c2da81c04001100300b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 879652652 1250 879651402 879651413
    0x3071a182a031603020a1a1e090a090b0f0901081506010210050112200f040e0307020405100e06010f080601050a0903050a050609070f1206020a1b06060e160206040210020c0d 76
    0xf1400b0680c080c0031028008103268003c88405110003c1d200c5040d0b28081a90301c03008205910390400003001001040300c2526036599225290142c0405140001c0501d125000c02c2024400d046c012405154940d004010070b010100e2400d403032454450514242c2ea48010040741003643d0a030b60342c01c4a40c6486c0001c80c1422900030640d03030161040034200d2407040e8801e00d580f0100890100c8070f5104180c40e0802080d41000c0d0040401c40340307450100c1c0d08044076940040d00b9148125240342c115401e024042007032a450a8246811400a003802e108108480b10f0051000780010901410304c1000102094058410031040d4000d5800105407809102c0d00c0c5041c0d0f850346010fa804903014401d40360007080d10009150801c0c101d48840010303d40810741c90360380d40069042030150340103102c18039021003e214200f00c2c280ca60f103403207000c0020f402414809110003403880a8540a4040303e29000700d921302ea000511250880e80403240c3c91400c2c41c2d00c01c022480d01d40c0c80d031724107500410701c0d2001008004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 879653902 1250 879652652 879652693
    0x602090f0a0b070614040b040f020a2d0e0c0d0b030a020d060c020c0102010b03030d050a15180f09170d0b1011060603030a0c03180803071a182a03 64
    0x600ca1301040c0080540b114a08481d80404d44020300556801c00120703000607503558003454014800313131115180c1544c1e1014800b0140f100d8840142404420444203c02c040d0b0701d042001501c03108288083e0b605294014850500901c00400b0025664429078000c980e0304100d0b40c0c0e1165030090511030307086e02916018001d0072584010002520070340d03000154642c018050704c01c0f00d0320090020350800e007a00040c0400307814041e00341c80f0b849941d00a00700c04803644103071403400b0b44500e111044c00c9030b840c42d00400c2269641e400120590f0700e080038810003d46080d1104400b060f04c140515251203140c88134170004d01c40207400b00c0c1e210040c00b0a0040c16500611510302c4041d9401c2034030321940d540e2050586921581d1410f030300182b27000c0030940009007d0700251410562014500701d8183e1034001d02c620315800b0755002c0d135103018014507034103c40000500031644404546440e840780d1ba002c120700342c0d8420054445080300300c2d40103e0344c0c52805540c921800c04110040840b003000fa2410200c0d500355 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 879655152 1250 879653902 879653917
    0x40f0b04050f040501050102190c05040e160f0e01260714040606030207050a02040207140f280c090e010b04021305180f0f100b1306180806040602090f0a0b 68
    0x40448002000b8240b42c076200e4603049840c10323000741003000c0d41c0d001d0a280e03050b030868086074480710026000c6000c1d1076602c03901d080240040d00405204071750301482002c1d2081540101e42c0d010303a03060244407818680703411504441031040000d90103600784008802044c40c0307400280307540c03103400700c00180c1c50541c0c000702a280b4402d40d020014a501c0350022010385c8104c3c10054010f174408002d80b4018101a402000c90500468410819958042d1020300344446a03856030141d612280c0082040c00384495030590107194bc050312501d1440c00e5075000d007410214891680b0b0744e0381d42d4919162a00081d0089401084000c00444d41d5003e00d4620701d64424090140500860344225408e01c420340c500126401080307003004210b22503582d90006803038031500a001207148140d507080000e108003c400034281851440d2240b40001c1e080480003880782004250302c605500d400c5a04110000010484581060300032802580c0c58040c00081540004406903003038100c165407900240702038881c0c2c050702c4030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879656402 1250 879655152 879655159
    0xf2102101113120602070c080a0201030b040b010c14120d020417060106080c0a020307061802040b060a050711042a0212090a090b28030b090a050303070c0602040f0b0405 74
    0x20000e808072100c001e0281c1d00c1015188401107000340a01c892407640440c04610a041c058074044a0386d86040b203031b0709954401c150943c4203040000c02c543e014010562600d00a440422501000400003071465100c03040182074404080f4a0015850703003032088500a05654004c02d54800c80080d507039001390300a1040c41c1c03100c801501016110312020071554101e079890b94890896885070f140c01002c552240c0419419484104100c4c000200e0340c0c0650301510054100ccc0da2001c0340030340180415158400c200030301c00c40d42004000c11a076044000d440c1d00750b0300700d03800e28601c0c2d4514010070020f020740915181240d140742414042c19410000c0d220110085600b07860032000c054010361140e001300102254000100329061040d4002076010b500042030040c0301c2c0f08109009410b9a694500610701c600503842c8030030050042c44003031140035410414505c000c041301e0074191107194403400054a0282041540c1d44d642c41400b01c507805a030050800c10700a04041d564858150200d580684142c500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 879657652 1250 879656402 879656411
    0xd05161d0106050316050d06120b06040915090201090e13140616030f09020a080102092e0c020604030b01180b04141b210105040e0601080a0f210210 65
    0x201182030a040034122245070311414103607107504204200341750b01801140c0c1040000e01c000c9821194502451009150340e205030605a0010b04244491035001000c043c0205e00340685240094203443c0707981c450000525000803003040b180700495a01815501c40180400036000740030708086041000320300a44205610180c0310b595030000e644585003110360302c021034091072a6841c20f42c02a04003456000310640005110801903000801d07400300e0b41c00002a44c0c0d40850f00350002c0c2010400e0035203100454241d4030b001040c82e2022064070b000b48040a040081e0030000c07504544a80068030003175940400991203546e105ca030b85100c00313021844414038150503e42c44e03007a1400c0c144134641e07402070314103004141c603a03608407101503501c0910300b00751420004020b4002c0918003042c0c001c031145625940b00075194901410002a1809a084409180c210000400201e8800195100310a40c0510300c020141601d082001158440ca281391000d02505000e4001d5560f02081c080704240040c4000c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 879658902 1250 879657652 879657689
    0x5060306010e0108122505070f0f2409031a0603070e01060816090906060e100315091a04021b15010602030d0e0304150c11030a030509040207020d0516 66
    0x522400b400c1c40303000c00310b8015450703a850852090004021000b07108102035814004490020200d1554103400d036210b03000750406225558200d1a0180105800200e0b411158180441d4840c6841c2c04209110884007134841c05265502400c018401942c022032021008544c8100030942000c0450700d140c82802a50004500c42c200507050b14161074560703407911030340c1c0d40c0d2031200c0418219500030481800402400040e1100d0b09000b00030107489165035561001c484c130b4040c018644070500202e000e250a100e80d07a510300203d051070208070b403500800441e10701c5036001952211124a0448c0380c1090001402412100d000c20303060303c490f40341308205c2d070100300e80c02d0321803040c4842800b400b00140c104020b208031603412900020804185034007503910781940c0c0d900c0c0750340f508a220246800300301441410070611030348000d51902c28400360054501046196401002440307504091403003183e000c92120150748542c050441881e80c01000c443c050000303140000d4100d0346511503c2ca441c1580380503003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 879660152 1250 879658902 879658919
    0x2031603060b0d080a05070c150302180307060c0305070f080d0504050c0d0c090b011103040603201602150904090501020c010e0f0706082a031005040b01020a030e040f020d0506030601 80
    0x5429130030002c2e150900c1c00d0014100c41d2984070040176503072405110300201d8501d0900404403038140c0d441c1c0700141d841c42540c14121800801314441d900c03c2d0010101000000c0d044812a05041d616190240e40c2c1c1006140154035030340e000501504100010500c401c0b280a558001c50150b8000c004075003d0b4800341c8200302107812070060040081400340c000700080741e19034010794010241410310780b90100d0071408480c034642099008000103606d0b0382c90000b060008100060f0707004a080005403501307140048400700011550002401451085a0400680c2401068400c0e8560081c01072240c00c00604045010350030034081000d0651034100c041161074400074601e42502d0511000c0c28001c0c0c03400310180c5e0350f5080280401c3c140d64041c80e0070441a1300744030076101c0641140e1100c940328107006003100c00410460700414000d900c2e00d202800035a03000200791000300d074180380100d0901140000300b03014119441030140c03a140041042d03401c0b22207540125101360800d800722203036a039840450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 879661402 1250 879660152 879660169
    0xc0705010801050d2001020106031a0403090b12041203020d0f0c0806040621061d0a03020607260402030f010f20360a1701050f09030417070302031603060b 68
    0xc0a074248000f4202000e022400841e4540c501400001a015500d44bc0d51a05c115141d078060aa0081002004209508407007190003404280350301a003000031030a039000c0b19030005403000d4400c00b01290018200c500c85d40449082c110740c3c60060001c2e121401110024060420610011035014000150142000e1140404407080d946083c010854440344070340d142c20122a05962a6071269045a071400b1a48800c503001c14280005001c0002e01c1d0030028141600504a5410841660304254168580c004402040002c8040c3e4501c951280c2c80001d241200c2d00d05041107550803e6084800c050041c2d201c2c0389443c0d6100c07a590306000d034034071a103c41807003602c09006071031003000c02c800039490122511003003d00c42200840c010701d1481000620b881890b512815a803d00d1265001903400c0a0040301d0700550742e00039841c4141040388000307450740218080c81000e803940b02e9100300a1501081900001c540280a44082c10000c61f40c40702c0c542c5040c0419648d41d0300f0100600140d090482d41c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 879662652 1250 879661402 879661429
    0xa030605100c0803130812010608012309060a1a09090112030f0516150501090e0f1e10110a170615030604090b01090f0c09050609060318030c070501080105 68
    0x2d0740c100d070314216560b03c030050304050b01d11301000300710340c0d03101c40029800c200500309104400c01d00c00456140907802004050140c00c402c0d0500705000c040b81d86814408018110a80100e407414003030340d9400701145100324a5070025601c101588208aa515038440003410a41000e803402c50f40307a0307241c0c41116401111010002c0004840800342100e080c41040600041c08410003282242d0310b0f10346511810481c44032100301c41795968030040020031014860322a55481b040d002d0100140040070990329100e8802c0200c80030380900c0201000900c050002200911180b002004103c3c0301009a1007103403c0444d40c80c0116040c0c1107240300d00505a0903c3d4818480240b0a52082411070040c18850b040541260340043d12141070034001481c078114980a02140100019a0f16080905070160b9001070205000c1c800d010400f806161101012500d4245041c1c480c5981c1c1c2d10ac000008450800d40400c9034018000400c01c070001c9100850034604945003681c0e41e402598a41042140e00ca68920 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 879663902 1250 879662652 879662657
    0x503191e11061b04030c14040501050904020a030303050910020304060c020d0c1e290f01051c120507020307240504080d0c030e0d030c02030d030b0d03111606050a03060510 75
    0x800110b500c80c080000050350000a40c40a040030f0740c95031b4419448400e07170051781920100103807002d01c03801d16100325401440202d9001000b401d098011503011140c43c0409070030540c49800054403060108107510f1201c051032811580d03807500742054001404e0030043d00d80180030320407400e91406e2003800c50103106a000889640a0303490308111412140c1d00c5003048030150365240221001c1c00d41d10700004e80c4c116200400d07403030514186942000c880301c16007020340314154607641c0c5030340981420030100300a03600015030b039414074076001c096611b800b640078001e601d0301c14804041a2550502c0040300300e16a407000310021840c401400f0741d0301d40103a0285507402d5000382c03080c9050305c0c400c2c0d01043c4194000e042101d00d007030031200815038401c4a030b0300c1540419071440f0181c0c01c5090400c920800b1808a20741040117088585c00374141361219030000d002c000404050405041092049090703900101440c9480c0740e50710240541190012411040420700c1c0440c0040d040c100384424840d24940c03903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 879665152 1250 879663902 879663913
    0x4020412062f041203090b03040b0601020c0a18020d0b03030c03071704060e010c14010c020a170a0804030c061b0c060c020a0b0a0e0f0f01060302132003040503191e11 73
    0x19004d90201e40b01e180a9040100e200070000d0919001d00096002d140140b4942c05d5074076015001a180540480840b0700443e24110204107100121450030245160000c002d0b9540ca035011103040a07003c0c56070b200d9414000013800040c0208000018083c5c0da00c51203c1500c0b0300c0360180c0c650064040c600c40e80012618a017040d07101503104407510440d5921401c02264440d19085141d42100c5000d0160b0b001b41e80410200d100303001810340360161006030b50012915003500b03210010694100a4401400e01200d0110301080004a4219030200020315a07051054110202c2c010016001881e064400909d451000c0403403500c0803c00400554001072001c0c01a22419620001070002c11070030b096600400c4044100f1400074800c0d034000103640c0b00080740850442c010095403186480d1005009490032050403c04105225110030790150100c4660312541c450519a06501c01e1050b8412040d40900d60f1501c01d42d08048040b240300c080307080c0ba00d0f00d11070203401558000045244820785600c80d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 879666402 1250 879665152 879665159
    0x70c0302091f09050603250b03130f030302180d0b010b1809090715170c0f0f0703031e020c060402060c07050d08030a0b0402040b0d0b04020412062f04 66
    0x4104401d41180d4074004107151460202d5811104220720742002e03008507215014042c40d480c0401c41170a03002c0a03000c0b6032080e642040d81c2a07143c44018424180d203841c0110005810300c1c0039800e143c4a142d049900c41c8003403200c5150003002035005244000440002e00f50943e81410101d14680e0003660004010185d1f034200b0380c4032445030b003003e404540101c2480948202030744440203128051141030008140442c100110010349a00054400003041100c000306200c41801a0752250058564003007565242210900072090744914103800390314a80c0066042c3c105503243c0d100851168030144190400302810121005912035204121010343c0070314007040240c41c12800a1000d05035010494100c182da41000c102c1030080d0041c2600c01c020701008002c5500001d019900c11100102c508500d8142055000c800c1c40c0500d1070307260400b076aa00c102c00d00300d131907550448001d01100030b96013140301e4240ca4900080e14803822000c1c48280c03103e0008006000704540c0340c40040389440300f181003a04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 879667652 1250 879666402 879666409
    0x10f031104120302010b09070f170402180c0c010c020705211c0503100501020705090712110d020403172503031b080a0506030a150b01261b070c0302 65
    0x20885280a0806010000003500318002c100b00007001d40700e900003194141048003005101e0000900303000600402d50019803001740c2c04800b6103a04400080540e0203a01d460001c24881884a900e400d8040c4828003844000c150724070181000d01080d00c024040d05254003800c0340c44044034810250030240d031040502c030780b413480089801000c841d00211030704200c0c0780c0415603c81c0c503802000d1012400c0003041c8403810701000035100c05008280010910186080003203a02c00a000702510704000a1202100083c403440d0004801048882061a110310038588004002d6115120848002c042c0d00800280c500450060b90511802030102006082811200c0021418410000c604140d92040c0040c80210340f410424030303a0074242d40304016403404847d0f4804494003d00001e10a61041c8150700008544413072a10180e1407484010844002100050301c500403c1e064412040082100651014407600001441400320001202d5092441031040e00715109030300001e0440d140d4a08140007506 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 879668902 1250 879667652 879667661
    0x130308012606010b1b12041814040c1706010e13051207060b040524040f11040b0309010b0d030c29040b01080c01031a10090b0406210b010f03 62
    0x3203040020a0381e01407003200281c2001e80036080302c0c41c100c6020400000c222010903e400703a64000200030f1401001c11301403940745019030f00c9241e0000858040c80384514906411046400ca061802e001c4d0506240c50540421480b034081e040c0341000d00006c24468a0b0005108c604941c2d66400050454580807910031a07689000c0c0103a441c1e2080c054883c0030a0300c0c041c010100d15001704800078000c2044c100b00801d40360003400071025144070416680c45500d241852115540b0119000a065a0380f021114040c0c56141e0a641050801050000e0160342080c011407080380c00c94000c1000c04024401c02442d1212940e0140004046c95907030800580c1d0112840da074860700f42444961206c0c160303040481501c0468046803540510340c01041017000030000740207400002d003400d0061500701e81d45000300e40303190903105100d4071251581c0c040050241080c1c00203021030300125030b03403291101d00140518983c0c0c400c01c101c0c0e107121201c084e000f080d07512409986000507503c0c010f90fa0007070381c0100e0290 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 879670152 1250 879668902 879668939
    0x1e1b0309030b090a03021605060d0e0115180b01020d02060705030c0f071407060206060d0b06210304030525140112060602010b03012a0503070c0618020913030801 71
    0x2200d404008100c8040e2054803e203080c00080088003400d15000742400002004008a403024410a00040e82d074401501d00c003044414000500580c1c80714824050030001c00c1e443c100c1002c0d2040811300c90300c08c1d03411111580c02e0358800d012010741407004990b1891003610400040e04504042001548100019500204040c0541d030a007030581d20119500d03403080744112100f490440300300c04001c5043c86020014070702400500b51600d01310780460402e0300c890031300800403207001c000940c85666900b008070010080b41240d180f20108511001d03034a90050000751814032070342c801d0f0b8028a46070280c0584079400089101c6503507203011000c01008052000390390600c414900004d90304440752207524000c0c14a94004a52700401405050844001080ca09020304681122a1540140c041d411000c07d482d45015a07590365444400c0b074042900002c010b040905040010403141c5440341034900e0b00d070003110414000e480f04240303041002861032000380401c076644010040950140244604c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 879671402 1250 879670152 879670157
    0x603031b080a21110705010e0601050915180708060a2c04050c130c0f1404060806031213050108060d020d0b070e18070201240e0406020906070c061e1b03 67
    0x29946408184029111056540c90010134085500303024401c090007402204e02441c070140c01a54144070106d04042801843c580c0861448840c403d925100c10660608030f0726803c0d0290704500308510000d000b0082900d013a8880c00c00345102180f000510200d0113800c0e002201e0040074030300b550101c01703607070140203000fa00d079801841c0400b8010784910081181742c0e440080d0004140d800908040c00e07101104031035408000071208500003a501d04021981604c03441e0610340d5042d60b0740320000703250100030031310448607080c042054521940b82c2c0d4042e40560f0b100741c03200410f540e130b00c1e801c0c0030318035101140180d8808401562800452608001c650b00300c0345500d0300c0c8100d00341d00b10120311004900e80c1c242c8072690b5102d0400c035109034288201c0010032520000254011201210000521441e0242c084502514000710b800c1202c01d5040750b40030031000d41a00d80728009820003000c1340314240b180d80045105000c001c081c8002d400780518540c0710517110400c0003c2090410315460350042822010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 879672652 1250 879671402 879671447
    0x7080304061d150c0631020d0c0510020309180f06150c0d05090f030f060c030a0b1305040c0f081207052518061d09100f0603031b080a 59
    0x2030f84860040081408440080c841e80c14000450316503003400d80400c84010360140c10045039880c00ca11440c900390340496070055004000c1c142000c102c0403590181e503118a9081c40007103000c0d00400a081c0030300044a44040400c0c04e0105885541422103021500c070440d900010b941c0d00c2c12889205940c00c0d0b010055042807a029611b03031500020740801804580c010514400d0342c5050b600b44d034040d10007a8040d085c002c411a9010790354281c05080442c48050120001c0e412155940c003498038100000d2006400031045001d2200500c015a404c2d12090141a00804c09440065503a0201c611400081028481041b50f000c0143c0066408403484c0c010404600c2210380482010f140c0a10b12400226a50b4075244000c1001c0c0f0a0710b899410003803c0c24810088600c8140322040b4081b07000740d103078486607103188900f41480c0740a0a070080281ca05400302c0c078a103070785900c48401c2d82c0c840c0c0c07500a101c0c580c0c00600c400c619004900145400d208022003040648903c401c0da002c41c114071007062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 879673902 1250 879672652 879672679
    0x105160e040e12040b0c1c081617011d240103020c070e010306020406110a02010509100c060e03090f0a05060403080906070b012408040308010e09032205010207080304061d 75
    0x4641c040d505c01040200301144203c6011000c1c407041003600c01284100501c0c08550f00c016243d02c100405052044110030000d1a0b0207000301c04183c0d50340d086031106010756071103850700d00d0f814a84034441c1c0c0c801c00107034000604500aa401041e040c003070081c458905001e4400044000c0e5000030701c0559a8011074400040d98505000006c0c080e40c400c4001584075810000010100300e00c0a031031a440f036000814000150360010203c2d81d44800c01c2d1070b1484198240e500a8448505803035000f002c6a00e003212400304400080090942c0c100200d606404078480642040348001003401502c0d4402810401000001c140340010b00e1074200c081c2010b07041210a40f1049055170303092380100e20402521019500250007202c82504640244c00d00741e10fa800c06480041c0300d001c0501a01500c052010046030000710f00300143c911540224140382e062810b4010400103100c418490240548107510b0b000c218068003009640c01d40f4081d40e918519204401d14140d00641046d61050f0003050846040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 879675152 1250 879673902 879673933
    0x6050907050303030405070815011d06040612060f050c0408060109051b130501031103090c041d030d060509010b1918050607060212060a08070905090c120a03020105160e040e 76
    0x842c4175a00440180005070718020315a420051082c0100d4440b440c6440144104040203200300014a140300d080308050381c80c00049802000396400c07000a28454103203c404000c0f8503008148800348503001449241c4443e40700981c10300403401802002c0d00407200601c040000c56100f1980420a031031201c00700c44a81006410580c019448600c68240d40c0405001550301030091070400580e62643e00d18614105649540307406c0c2c101c0300c4a00c650740341c0c199510f814201c290751b1a00781d0f000009580d030301e1340c0302c3c0c41d01c400509141c0f003414083d0803124000240240408142c925081510b002e10032842c060090445826081c10700030510b80000500c041010b840d82c00c0a4014103100b00f4005944034849034503080904c50040103203106070100b200a000301200403c1c000100e402c0610046401d484218055045c506860401600000b0803100c0344400f00c40014080d101c44e0098008200540351142100c0b102e28500401002250301c04094840360300b01540a107440801840036110f6000304484c81 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 879676258 1106 879675152 879675157
    0x180b161803031b170702090a0c02031603170705090f0312090616170304021c021e0102101b14040503060a09020a03050111190c030c06050907050303 65
    0x1400b203c071111014203510750f00070011204110307000039169060304580000d038131414400020504401c105c1c49000c0c4424a0760f8003442c60005030524901082080c41030032000c1210b154102a0b82c1a07802c01e07210302901599541507500c800d40400c21140280251180c0e1090704041e180e00c040741180d90850700c3c030701020340303c03151102e8003507000034004840982d010b02945401003103000d41c07960b0f5030000c43c46a4821150784e0541800002d00c110728242d00d2030000d400110342c0f0f518481c840e00b0f89a00e542c0c0700300141304503100c010302d0040303100517a45441c040c0c007403031843e0214902100303030041042007880300301c6000281094070b0200001e94401000e06040d40d078503525202d400940d121889100040c50f003001c001d0102821580481c0c0072940b04507050098544802154240b040c411402c42842e51f0b007550303525074420015240c3c0c1004120142040c0000d100b229030005035904c05001 = true := by decide +kernel

theorem cover : BRFrame.Cov 879496402 879676258 := by
  have h0 := BRFrame.cov_init 879496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 879496402 ≤ n) (h2 : n < 879676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
