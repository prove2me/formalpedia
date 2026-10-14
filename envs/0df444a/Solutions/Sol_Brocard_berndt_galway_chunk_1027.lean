-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:54:07.72632+00:00
-- url     : https://prove2.me/submissions/0ab4a8c7-11bd-41bd-ab5b-42f29c530130

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 184532374 ≤ n < 184712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 184533624 1250 184532374 184532401
    0x3030806010909050a1514240c120d0b06270103110a050c010c09030b07051e0a050304050114010501050405060306060705011b020c0f0a05060a020f12130b0a0503 71
    0x103160182c1950303903603e0b4001c19543e0540710b0f100c0860356204103075030800c521802100507015031003200c04004811004541900480144202107400841140500401c0703c0121145101c0420448040c5610281d215055501280a850103180b40c09425040c506002007500c00d1600070504080c81c02d000c0301054101d4002c51000281055a1444581000200c1c0b13005030034002c0342903656580740d840705c01e2400e08450942107072509000915004200183c0701c40035866005641c3c1ca8641c0c0c0318019294010400c90003000220220040419120741d110f42c0400035600c034a000f80002d003d031806860710281e10310702c203019240c0018401c100c107004500b48000215000003019103801c2c50a00c0507103901d030031a448000103103c41003040e501e0068080d410084c424405c003088070300c004094850302c00030309108000d2240e140600e1000c60003443d00c80c024095040c0751340c8040d09454041c0484c16218109500001c2c00740003141d051000402c12510300c000380d03200c520303094450031b00d991030b50b1901c82c40f034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 184534874 1250 184533624 184533631
    0x10509150103060b010e03100b01080c0304080708180a03030e090708090c012102030708100e06010f14070f030905010f080121150f0605120604021003050901090b011d0c0a09030308 79
    0x14040c0011180d5180d840405c81d00b50703100180c400002780400d51100052581c1c8010749051080c060610500c070108184000700c0700741550041d0010b1717590303c200e541c803034060f0b117524010b03640014ad540340041459001203452034001400c90703502d0059070b02c0c07140640e0301d02e400b602c004a00d80d1101400940a5024000754560040e0200c0b6200c000c44200d0444c2040e84c0c012101d0500181102043c402e41d04440308080002d0020b56100032402e00d000030009046140b1010700ca8204a071200650301400a504120703515280c000034140d20030411800c0140410702140b20701400143c00401040d20144070314505d50517102c40407040c03019089903c0c60181c29402000080c2c41813850340700c241c4c1101840b441001103414000350301081d40340c43c00e42000032100007d0742031a1540c015404010040e43c0c0c151500d4119806420000b03000e8940102050040144903801032080c81020000300d0340540c848403c000104000d02240034681e61b051254401c1e014040c0c0b0f903800300d88085402c3c80080e003e2a0500d50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 184536124 1250 184534874 184534877
    0x12160e03011515140d05060609091e2410020325050712020616210203070506130b16030b06030c130509130f0507030803100602010509150103060b01 65
    0x4120540100080c2190701c03000e200360b406892007000304814406040c1142e10030b001c0741440c019010302c10501c68075500c50914619503140c2d81e4800a03601c0c0d41c0711000d0b00c070141009401f40e4118a810104100e41845625101c10854050170001b03458001d0b40d031054a101c000c070310440402e000c0140c280040d002e8800b04050540c0024060b4040301260030105a611000c00c1d221081110f600d41445400d00150341c1100800002081c945405a01d0764001ca50780001004400c81ca900a60709082e100300b14031825401d0f10140642012040795400809414128000c1d4261143c42d00c44032500c4101c071014104c002d03c00103540d00000c420070080075107010b010505e42400701da0004060006041c69004981c0b0040c8030300007003080e08440709001d800310042c1c8015144074100707041c0095510320100c910310f402003100020000721000c0000038000e4030000d681c0700500380e4880c10704052088850300c060103142d00540c41d010000c5d8410f480054441d10b031884120100440340d080d0b0f140c1c503000d8000c201b01a070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184537374 1250 184536124 184536137
    0x9070902093c061e16170702090604060509060d03021501170d0e030705040c0306080102070803010e0901090f02060c0a0b24010201060302031c120e0102090a0801021216 74
    0x9800c8002020b203400007400c929094840074000344108032606865846203005034000d00269140884010f8245112510b0070b5500303031500a00e6101c00c01ca02911100284003001807510801e035200c264000c1c080c01c40c42161010305568460382840100c1c1c81c14451154403c106001051840c2001502d51a056010740706840300c1c1c600302004a0b007416020f03441601d036884101900305100400f48100f140000061a10707a001c5054403000940c1c034000c6004175032041b5540c000c84031006002e507128400901800c0700954840005080c4429503400c2481005100421100002d4500006209a4000030341c0309041c50700f010300a4080c400e90381c02c114882e114611a4000c200041151210101d01c14000d2000103c0c00d911003c000c1a048200b40a085055a040031000c0c00141e5002c80d800c1c540f1307a40c085071094074221041088410212000150b4901da20303003003400d01080c0c4c0c190010580400c2c1962088070a80d40e41d00d0746800c034403806d810121420b07900004541c101c080e00060000e80001d5107080c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 184538624 1250 184537374 184537399
    0x903070b130b040f090b03010b0312030703060e012c0403020a030305190203040b06010e030a050c1201240302090112030c0b090c06181503240310060603050f0f0907090209 75
    0x50059511a130001034510a041c0410020b01125014070001c0321025402817145007840f4001c01e50310014291400c6a001d800b200207600340b48203900c11380c020503413651400043c0d40e4030031a210044501d0300114118165a1a87c0050083c801d00141c2c0141c0d0b141d0b00401d240912901c00700c00400010341400140300d1940e03032102c206140d030b0026600850192505120354105007001600d88840ae04e202c500039013014180601141001c207403020041400eaa06480400d80004006e0041c0140c0c5109c108420890001d482042051a007076400c0d64401d441d1062503980719001e02c00001761606009000403a0139510500080c422001690040c00403012649401e52800c00152950010703407004208240c40f80c408d00c0c8030b10f0b2030001444034511455510f840c0d0304002c81103c4640310000444400b54204400c000381d651030030494545064070490f8208440380e00c544004028280a80e025440b0032400300100320356011000159000e030b20042d0080102903c0c3c010620065000f1111450f403046001550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184539874 1250 184538624 184538639
    0x40519020120011e05011a0708040504060b07060501094b020909010b0306060a0c0317070c050d09080712080417030403030f020a15110c07060f030608030903070b13 72
    0x22034000b50405030000c1494000d003501000003d440080c80382d8403a013850010058480e51800d84000c0300c002c21815503556001703041861a42c07180d903012039002840c000c6d00003000e40044d000340000c1845000c0030311182e640c0e400c0d4941614a6144103148046100980198600f104903007240405d0307448149682040851209102900518804440513900081c0c07840191a0030359070140035080b405261415400c081c07022403041e0084881c59824040b00c0d5408174107143c00f40c0801542001d00d100c0d040e44c035140035240108565203012003111244110401c6042b4030b0302903513040703055030550b00052003d00c0c039113aa00941007441c0501070780c030074900300000300e04446441d0b0106070034010701c0e00031640c4030701d03610300281042c3c03aa4204400f190041070707502e40080c3c4000c03901000d583d40c02c0b10104485892400c4c01e0014070400650f189240b0440b240020703c2900080100e0200c40c0c252030030894280e64015450303d0f4890a411580d150704230b80c100344401144400900b0646102866404441c0e4a80c0703003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184541124 1250 184539874 184539917
    0x180e0405150c03070e01210b03101107060f0c081611010e0d020f0d08041704080d0e15040302010c1403040302060f0306031006081f0b04020d051503060405190201 71
    0x2e801802d09800004c000c2101d812118400c040282840c041ca00b4458030791309203948600c5041c9803a440c075210101d100d91583c0400562403031000004040106159094914801d41d01849040f581039041030706011002266201c0e501c82403000e80c8410700c0c150345da02c0c01c1c180030740c11014a0300c040c0080183c00400d811f000f4807a10910104010042c4515159200f002e480c0c40311902c0040884d41c4400280080d03140d0002c480d0350016807000700e41d01c0220282862140c1805960080c14213403040c0711080f036072264000b03100042c0c898180c490b041c50300c02d01602c51465218a00019001c84eaa8071008400903081090000d080c280fa14150303401c042c0c6035030018602c0c1e44a104041d440c42d4001c030910010345014010702da010092204204002c03403501020580311510214a03403550f00036600c0300310040800c0e400554140c0030080045588985402c01c400081c1030603030b24940c4e408005a21031059080c0003032258020340d042001400d600415020b1f0b8886000d0500f0308a04100300d00c01e055030003451b40301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184542374 1250 184541124 184541131
    0x90201030f0608070e010f0515070f0f1a0c030c0f030406060f030305030a0b031c030c09090608012702010801150c0c0e010602011a0901151103040f080d180e040515 72
    0x1400b0382401c038901701703200b80e2102041c0c0066495084003a800c118aa031084e16400341e003c0c100342e041d600d60080341081540344400b04800342442c4c0200c030200082100c601c030021700b01d580d52840d480780f640300e580030301855000440b9405107204081200030791410075400035651103071088002244c110748032070740082d64900d242d004a02040021003072148035491070007900352040b010350082c0002900390407541e5500544024110625a889420291b01846400144094550b8000c1440340560f2a4411402400f45258074040b024415020036a4040d00785600144070b0b1f0140d4410803aa400c0c02d075900b01d81c0b08500103500a021054050781300140c02e010b0868010070044501c020707a5890068083e084d2100728000031000d02c10842e0701d10045d44c0700010141565885402189110504117058405401d81006801144400f103000108202100d154000361000ae80944845407515001601d87e8421902507200701c0c0d844000c00d000702d50000c171580c3e0b4860701810480e00e2030000704804002400003038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184543624 1250 184542374 184542389
    0xd022a030c0d060905190809040f02090306011401030c020c091b070501050c0702090105060a0206150a05060d020703170f07030b040207080a0903111005031902071a0a0b0405010315090201030f06 85
    0x1402d81d44c00b8060144560200251003a040550040c4181d07078000081c40b602110622440d6560407a095a400b00c1d819901940005021604035584030551400200d00b480d0003940000d0170b01124000043c400304031501584405480d1569903114800d99082600c444600d050543d0001d00c1608045a07090082c0360083c01c551010540c0ca1600380140480d0300d0b816040a0700403581081407458041e400100703c0d0b07001500e01000001254010001a02442c159215a030300607004142051100703016402414160305c26250411000b150001d690351030882154800840c801c0300c0c0006401030b00a411050362600010030040c50500d031980c0d920541d402c0340c1c04910001303005450920400c000f129083e02428421114908182c100070fa00070500d00c0000c0c1000c140000300303040c1e0502e0700541c1e0140d460742588691115a032003035214408107d41012a84105841d0400b2540a030504143c03080c54182c1c2e0b00203015102040780e8002c508041c0c418501e080341010354800c0c40c0d01c1210750910807000500b414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184544874 1250 184543624 184543631
    0x14120a030804150507120902120706030608010c020d0903060f02090406030803070206091207171303240603020109141f02030d050c2d04030c06030e0d022a030c0d06 72
    0x350030036020100030f00c0d00c0120507034940070900c440310307410094190031a1002e0202254184817480441c2d90f030400b5004411191240f40b00116010f901130704841c0945e10098020891300c1d100c41c1c000c0343d40e4501e40e124040810000441440030170f515401a00340303c0c001100c0580b4010000e004034040303801c00c4d030065504013804403c0c482c0c031981c140704031504046c406004140f5214110001e066501c076200f0002c00804001724910400d806a07019254800b1102004044440c0d5074200005171941c5058083e0420340420400780418000e441948152501a900c0002890800d0400d110800c1082e951b180c0c056010301c40e0080303240d5003644540b801002c650107140c80b507c0d4070852000765a00680280c1003600d00380460084103048184070158801d400442c66030701000f0a5a8149a2040d90005031611588400110b00070ba0541c0000240000c0d0700201c03200d800f602c40b4105e0316440740505404c5e050329444022f0343e0780000c14440310408540101031b200b40146200c0003400044c0c42d07203011940e0544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184546124 1250 184544874 184544881
    0xe04030306051206010b04120f02060706140f1014030a0c0303020708121602060a05070b01060f080705130b030703020f030411011107060e1c0501150810110414120a0308 74
    0x4040310543c51000c10440209050b505141115803507000da0700503c4040c8147c001c5010900103403a0070a54100c2c3c000d007070340703584a255082c103101906014540501c10811900401d85203007050003034622840c10700d07403c0e00c013150a141014001c2c60702c0265081c2e262085040401c00300c0c5109904400840c442d80082031010701c4c01c0d075a5410600b8405481308828000c1c04441812110350720b40090b0544d0480c0e040e665502026002c1e5068000d000010b081d03c1581000480d035190006202d00c00c2020176100c484840da20321204440d94860600e82c00c200760705040d801c00c0a064070230059604602a41005401c1840c10303031011020b500101c030700f59602c059560b44003416503005100d841c15442e840000c5c118890500c02c01520459050701c8443c0507000200c4002c0c07820384044102c1c80c25950000090001010b03401c0342c00140d0f141030240780c800e4001c0700000049401d1a103d40c2c00105050f810711820140f07814041c20520101c0001103810498002c0a0003c1010a10503041e1a6100b42c071400e0240c00c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184547374 1250 184546124 184546129
    0x40222150801020f071e1403070b1501230c0a0804090e0a020102060112150501080a030f020105010602250e010e0411040501051e03012d1a0f01080901060e0403030605 73
    0xc03081e8003001c03050744100201110481081c0488100c1c0b50861740d050940002d6049140030720344120000380c9a010701300f01c1e1507004000440100b1120740600000c075483d4490844440038000702c1080240800ea01c4207840043c1d00340c0108020783d14400f0a0b241e0704112100360b015007003403240d500403078200d40e00081c02d00c1510418032450a503c20300304d004115501c0a030b13001035076511041c0124540c03802c14030000d81c108803030b208481c2a4481c01407000d009559403100301c9541d4916101048000c81c000d441001c0e0010f20502c1841d04994040d07000300b41c011003000980038136030b14a084482416540407001325003003440c244081c0c0203000c480703002d40d16072500741002c4910300c40e0130824510550816004001c0c80d5602e02c44132218030180100c010045242000003401000c514501e0ba405c100816a00146601441c42e030300d03c440302c100b03000e1146501000c0c0003003c64a034185295804804402d00700d0b0300e94481c08220358041c2c8680000100c440c0c61f00d042544071081110106d000a440d0710082c0710703e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184548624 1250 184547374 184547411
    0x60807080606010f08090115030305040302030c18070f020c04093509061c0509030a0905060f0706020310080703050a020a1d071809060e010f050a080d08040222 70
    0x2018484003070003182c1000e82c0000d0a0a458407840c10412131100c0108202420079441031401c140307103020100c0f443c1c1e034034030300030b41141c1051209900ca270041041c90031032400d000c001d04045c2d05030340c000320360746545401d01610701e1010000100210722801282a0b00c41c1c8840c0309004a40b40100400b5000302c10203000701c2c20904001e40d2208032103c9000c0740c03000e400c900728161403100404445940d2a04e07100d0501410344040030b80041d010505240c1031001c401d40c00304c020a405a21a6280c1c4650380e21070060044030301c107054480c41c0000d070420015021a043d54080c40c0c0000b00c02e000300400f199501142d40c074080b07440d04296410b4104210f103008614110b60008020884000708220780b0050301450020302200a001d1001c4c00b12400041c0b96002050719948041d2505401c100312481c1c94004440c1422400d0140301c503695180c41000c00c561902c1c5202504841114005000403550b07820225000400900100c0e0001c1d0100141008446a9240000440329000000940003002e460305c9a80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184549874 1250 184548624 184548629
    0x309010e06090f030405041a040f0606020607020a0804030602090402040810060806151c0303150e04060c0e060a03020c0a02040f02070303051b04051203130314070806060d022e03060807 81
    0x10755022903100f40c0300b4600407041c1c4049a000319000100410362110400564020021580e8042d1a00e021445502100e074040815518280e003254829030300e0610a92303580001cbd070005001c40c4024441000000e04540082c644001c0250001d81815030303c0481c036103003070212586e0003005921400c090091280400560798482c4a4080c00d5400c03500c044045038038800d055800b101311842504102e0107050103500f20206500c4102c03010041f6640d941003c1314129002d840485202e401c2ca195050b10030300c104a42e494022008100900e02035010b403055009600c4800511994015802e600016a80f070348550200900e1014000d82d5414040ca40142203410041c0b0a20194424464449501d4405025142600c10540b5010900270070011614918010020b9101c403643e1030f8013003c01040082c2c80724145e081041c004980401c1d03160254252604811035120740c101144c02c1c0c000000d490315600110300100005155984066481d50041d036200000380c4100120f901c50303030204803140341040030100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184551124 1250 184549874 184549891
    0x613080d08010510030209030c060315090901050c09120a0b0712050f0906010b07080705070f150305090c041e330302060d050619091a0d03090303050d09080309010e06 73
    0x340d030600f800104043e6040c07101c0820982e010400e00007a0b00c0411880f48440c034001c04903510781c07804180f1489000000e43c84c1e14010800400030440044050003118021125552aa42400c0c0318034103000850458602c48001c61040340e0310040401c020441d11401403c00350388a00e442c240325400b600660f54081d14032280c1c3c4a441080098a00c000b04070141581c0107001ca05944084605202c42c05004011020f0200d0003241c000007268084a08a44211480300307aa14000340001030083d01191012208140150840380d8104c003103190030381c13141420b00d8800714a079084040b1540304504460030385e2102140e1201000b1482000845220f40e2030352004070321034250259041d6408a107282c05241034880d071807900c80c00450825a120420801f90306ca00289160b81030b50f40d4103410002d02008000c60b0318101d4611410071490a00c0340d0032a11580d019122002072a00d50794040341c00340d102440c01120243c1e26820800010300038001540580e90090000c922448110000d030b00b407100107041d400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184552374 1250 184551124 184551137
    0x112406010e0d03020a081b06130219030b04080912010c090302120f030f090d020904080715060503030306010804080d0204030503040305010b0a05090118021b1b030c01051b0c0613080d 80
    0x60011358006910311650f580249400c1d251411083c003070086d4998801d100c02d075801020104901071030a1040501d880740211a0b07102502c0c4001001c006902e4680009405000d040c00020041454000146002000a00184c04140410f21840d08441c086894500018a001402c1041d4034160003003050141081010302010203501c034990795a841003410500c103000c00800d66004941c0c502541107215600500380801914003450200c4480c2d2003014129914030842c01c4206d2500a9413240340306440b80500250b01c0d60300c5120041da98000e000300101c42008003084540019440341c0040c0005601c12401952076508502d002401d49503295440b0b40070b00500c04c401c00c195034400c03503800c0c1150f207440b010401c010745281d018006445503a03540895141c82c0705c1e000002490020340b0740342460100000304080381910302090f40341c40340c1644003030004009000c190b514400070302c00300c18681c4400003100e02c1702803a40302050240d004454400e44698103170008000c2540d040c425a8081c45203460000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184553624 1250 184552374 184552399
    0xc0c0f05061b0a020c011202070203010c02340302040506040603021021020909060607030201090807030c02041b0f0f1106040c030b010602010e19030e0a0320041b112406010e 76
    0xd41d2250b041740d180c0d0412441031a17065144903213a044501041c3c000e03009214240c9180c2003e99600f4002440d4041403418400401c890511203060302040752103980c0b03000039a0302c3c1d80c007000098040900300782e03031103a551000040140d4408048101403001601c80d50003408080c04031051700300074075810712403941c010000c2e80e819540c1d000035144d02c103c044032000e4072403004d42400c81c01049001c5006040c10000500b8506154108640020751b5200700c1d400c5c81000d0480c0208800200d500540c1ca0102d07452114a400503802000001080792461070304189401d00c055143d80b5015040d60141c9400800b81030074070601100480e500e0140800e07000071700415014030401e80d030710b2640354000c99442c0c0f42e4403c000100b61248413a8211580002c18030801c0a0300d90070505c1c13602192200d0034207034406407219101d15007003902861041c44065964490070b82440001618840c0a0540070401d6004030f02215102884050300e2004070429010b046070b40e46820b100140c0304160300010284034420080320b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184554874 1250 184553624 184553627
    0x3060b1c020d0308040f0803150a0b0705060a0e0109022701081204030b04171801020d030902010e06130b0c070602071a031b0405030706020c1008040807060c0c0f05061b0a 75
    0x52a40030f50618106503990b0701c5060110b10600d410b00c00070640c4170b00006010312141d5103c101d9084510880e01c409840742c1d101803c884504c01c6070f20080c4280c000a000900c0f41082d030744422044040c0000204007100309a00080c01520703084049616015013494034911606803045c40b0b400361403e60020125044c1d100020305180c0a10701c401001089000000350401c80b103d901c003810306044500e803130346030740d00d00660b11071483d00c0103100f900501c901d2120390235061286c0508400180c041c0c480070812901c0c0d030188140c5500504512480125100d000140041054002c1120f10140f0f00035220440c00c01c5030081c28120381d41c4c0300e0319080c0082d584911034406880203d0350007490950540c0501e6031481c11400752801030317074001303079060203840c2c000141c0c250041204030036108109c9000300061446107081d102c6d408103980c080c080c0f03c428062100002d03000c2e4030081d078490b154141031110703160940d6500342009007007000b103407107401801c24030003503100e420041000c07000c03001c003010700785040c0c4c010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184556124 1250 184554874 184554889
    0x40302031804021207080a1a010909020906070206030711070902191101110d0e01060807030302070506030408070b0408070b0f1501031a04090803070810080d121503060b1c02 76
    0x11a01190244a10319000341d541c0d5504072913030601c15a00300751103413a00c4040600060340c01c6940d11920b5003001c0484402d030040031400d64a0090585806920505002c5404005c2d048400e4480d00400100004005130b81c504d405544221400d0352805d0310200c0720f20800d420009142d0140510500500811100d1289a10f2003289175076149005c0d0100081c0580f62800341080b075071070781c2007110001910b2075207503180d40000d84010010341c024803070903940b0171400d07544110501c4044c0060b040340d80c040c0035a10340b0000440c0c01c02d0050f4001b60504d0069160001e48001c151412540c8040018104003002036008c40a94000d89001c001003c9190007075121000740782c00d061260405650710b400401108a800c060b030401c01d0301500801c1030018a141074100c0341c0c0285e6000b80130540c41e00c000351024040784c03418003d41c0c1c0154003405040c0c042c0101604c0342c414041c0c0b99210749445110b4040707840b0510022800075406a00d010070003001200c14020030854881d5001c900406048800015803900d0340d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184557374 1250 184556124 184556137
    0x9061602030a2003070b01030b160914190801050a09030e04150e09120c0a020901080712150608010219080a0e070e0601020c1f02060622050408130306060314030304030203 75
    0x8960048842e0b000c2d001ea400c42c82a80b60040094810b85d0010041c0458044464401c416015082589420ad008242c80c640401d1007100c55805061007800c046c0e00300320122000c40e414490040800035114030b159400c3d0340b4100c801c00541650f0f03440368018554022502c3e414004103441c01c0001442c450f800c0300e50020280608a4240c180c0d90200301e03030003020001c241030f0b00c00e00d03a011703a15184005070640d150446007000ba4419120f4070300101d0070304004500082260505802c500b2018243d9030703280c1500b010440248043d0b5625140081c05000a000404514401d0085262901c02c112000b0f030a0030f001801e04070100d807501d0613440c800c0c440040c03a6402d8420b1704e0b021a49650760280102d03d00241c4201c4950408108101ca02c060301c14002c402c1924641030302034544039a030f41402c0c0052003032804040f03c80761180034040c08603442680e21041d0042d011326200c0b46455044100d500d01e004840c0d20441d003060741c8038810400e01c44000d41c02411071441d00301444c510704242c0c500a54034091003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184558624 1250 184557374 184557407
    0x1308090d03080a050c040e0a110f3c0315030c060c1006151409060d02040e0a0c050f0405100e1512010f05030307022107060c020f0405040201091802070b09061602030a 73
    0x180985041040509c0982d180b030108010740590300c200300991040c44080500c0107240c660341402ca0300000b6100003e1250050704e0001140d030841d60f540c0d0900c1c900c01c0c1141c09070754150140419201e1180c95590052040e420a40f00921002c1c041c0c24160040b6010399120350328400d03000c0c803010b0300f1991024408074903044040b01e95071102c0030040090005d2080c2c0c81d104c00e0103840024001140008560766611030640e010381003144c6400c07588140c8982c401d5000d690ed1520b401c1006100300d15180e050884200c9542c03824411644c3c1242c0030800309400860044003071080440c0c841c403501001ca80c464050000d07103494050b820701d0080400d54074000d070700f002481000c11040d219007800d1426424942c1a2a1008880102e699240054012032801c00b05074052a056403036150b5609060055a0065a042c0c0d6000c0c2100d150000501c001d140c1c410000710100e4080100401140c000c0c21541e00a02408014050074201001c060401001d4500040700703542050126034580c5800007500107100818 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184559874 1250 184558624 184558631
    0xe090f040b010501050a030b0d0309030b010608040201050d0e010b0d0501050114060403050706030209030a0611030402040b1c020f19080c01020d020a0809040b1305040507030b0a020c061308090d03080a050c040e0a 93
    0xc41b00181c0203001301c155080e0300001024541000d045d0301c00c2121080300e005d0302c00c1c000c0c2a601e811044441c21382c21680a8003042d810000c1c13401b1030b0750070f600c552220300e900340000904203a00000141c0c40c01d84500305480e281e4440d40140f240c00501909a544050304884d0649014915901e00f9180c0000b4031a034401c3c954042000100c0351400d1080d0540141d102c501004aa902104450095003059805074040c6180c0b803500041410400248841811103800d1803c4142056080010755190101143e8004101c411000500d04002d1400d20103800c0c00030140290400721000249005403401c000307811903020341d040c1d2000c5940407080301e402ca0829a40170070301459603408159950414507040040e00c2c648400c1005114010a07618140d070700c168a0348903d034540444580590040c4100c601041d007003a40403900210168242142d030030b102d003131100d0500070424000f804802181006038045585401000004181c6218042e8041e94260941d03040c642002039003816668001e0103c10b40d10368 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184561124 1250 184559874 184559887
    0x2120c0a05030c0a05070f1809020301060b21060114041a0f040603020a0207050301060f0918050a080403140102040e040f020102070b04060306080709060e0c0d02040807060e090f040b01050105 84
    0x40612840e241036411604603542c8180050a140d90713010721440503034040c040c485d4046282200034164000316207403014410a441060f14201000349104181240d0540d654680001c6042001c80500301c4290300c080c05242c42d0404586003540410010b04207410442000c9107020748100000076982a10f455040740070810080748103003d090720404015440e40700d4041000254107a06030000e0400c0243c55080c0d50306142d0f21004d060a880050080000f50342c5106024400ca00c02c5622482c1c5410f440080c803c000902503c4942c10145207500035540305500140900a208130700c1d403000d00044168000f149458500007003201c07843c00c042d00c01002642455440c006580c420000a0007809054210756591542da03c40640113084038420000d681c000d901001800940a104090031966010078405841d03485402842e501d5110310141e042465080c800421700c00c00410011000c2c0210391a405420408502008000c0320002c05a0b0b8070203410808000c009403103070180701d04551080c02c0039a190b00703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184562374 1250 184561124 184561147
    0x30105040f140c06031303030e0a02060d0e10020a0203070b010f1d04030e0a06031505040509031e07080307170c070515060310140426040506070807050a0b040507150212 74
    0x184003c659220743e0210501c515200d907070380030300132a0f07100c2c1d10200800b00e0100b4880d03444486182e0040d40c41034060210210440b0140c2094075140f184009855001d0885c283c024101d8110b01c02010069001041c0380d0300304070050301a180035200c00860080080d01c1c00c020748608092000b04c0203a482c81c420f01250030580210410b85070000c008010000d6030b07031130b480000c0040071402c0c09889070b500e0344180001d240c1018407901d401400402e0140d85800686000e103142800f2162080b03023141010000c01c00030402d801c0145005010030fa41712aa040a52500d030500007001408601d81c4880030004e0f400000d100040000b6680300f80d0300c0032101560f030000064100340741e401200000e80d003843c040040001107020880d100fa445a40b40b08051344c0003400a070b0805504600c00c060a010801c000d10952071b01d00040e240d01403240c01c81600d84140c3d40e80f21802c0819500080b0740c202c980105200070844107018400c013510307034199000d04005010000942eaa80c3c211442003a80e10f000910744580d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184563624 1250 184562374 184562383
    0x8070303140906060a05010302071a040c050a03030e040b01050406050a0804020616080903060c0c070b09061b010b010e0f06090405221515060c02010f0e030d05040503010506030105040f14 82
    0x58100250005a0b1428015294840f20211078651003840442804604c0f0f41c0a41302303894145070480d40013010b901c5890310710b12464101405c29038008003000000151503807030b0003500019600c80da89801c003020f0502c1c1888151440c01300c00d01d050100c144003d02c040790380541568031108451500010b1a100d500214145218002c003031402c0c40e0a0744d075140e040c00300b000000e080169060b8101c0340617560312040d204490060001002164004420420000c1c071540068200050b00914203440d2503900d4246c1d8211004060211005075180c00c0d0700002507801191580d140300d801e035000d04031110541d0008aa40c412080054865550b071408502c54200e1500340ca850000410701440e80b040103401c001100c0c100034101042c8186c109400e144040e1b80301c00c014001c860840e00c5440c403107541680113551120300350070703c9010462078a0000446580c100705550f51520184c032850f5075641000203160071741d8002001c143c041e07810b00080c0800102159003202009801c146c0b03508100c0002c141e1076090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184564874 1250 184563624 184563641
    0x6050f0606071b030501020f0408070909021f050c2406090412050a03060b1617070b0103140f0105010e01081006080c012a080310061706090a090b0103050102130e090a08070303 77
    0x1b5072001c03682c1080c0d43c60100041080d0340d500c13411241810340d204900419100d802c0d000a411004107201c03036004a000881e2848981c440c1c2c10600d043c020ba200c0400e1070030b0541901e2403000e25003001d08041e40c0c04055034054003d4020745101000d80340c04c3d1034035a40c24140a55800c00c0040025817040944d129500900146c5665204103545200720203018010b1080c8220a40350340180c03160111040e44032104858100d0750100d44088180c0c41c3d078030703030610b03000c08020000480e0184008150207070bc0284115406040056600c2c14a941800d080a1810090501d810802c07032038940140408100060131088205c424038010184c1c0390000042d07980746d070302e602c1080d00000c45100032030108881207000c0d52103511900500c06442d540c0da4001c0354298040c059141d24440f070180440d103641080c0f441d4030360000d0041400300e02801da56440340d00c0304009a1042d0390b60396010903032942845542d0800001004c2d64900312000b41805200c1d6a1240041c6030002d101041c0059281d00305130003a00407402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184566124 1250 184564874 184564883
    0x70f09030f08040509060d0506010308130504020309010f0b0307060905060d0e060114030d08040803040b0a110f12060a06080c03090c041b0906030204060c11030c091306050f0606071b03 81
    0x81e0422482c0c1009070360403030b000e01441030070f2402c0001c040b0700b072008a00ca0243d0300034008201c030380d18545480c040760b0712a81001020306607960011409886500066006002242c0001200403208000c8412100d40130001031003608040341c1001344961002514040c0c1e9402c6034001e0f50741c040180c1620017000391021880c181c0c06040e00001d486640110616070f100030550503906011200001140e0b016812140106003400034070109012803425124240e20100c0c2e550f00203004008400003410640003121f070400400400030313103009407114841d00e10783c0048084d0783c00499213080100c00782c4141d0f8020f2240d2146480400010345c3c03402e0410101c8002c9001800400000c0e2409060401a0340c08440304d83c0442c0e150300001540b144603100712400c4542c1d603580e0308030113110740c3e84031b001782100f9080340c031780c507100c0c000f8680e00560324408550b000c0c205039003e150074000b003403410400b6147c00030426901070450324200900754071000c0880d01d2066002000780c000070700081040302500e0080d0400741 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184567374 1250 184566124 184566143
    0xb0d0e1c020f01051603020c1203090c12120a0503040501020706051303020f0c100f0e0306070302130e061f1b080a020f03091804030207090e0d091706070f0903 70
    0x311800081920509258026401e94811804100b007803400e9500c1554400d14040111802c021301e20b01c6a4054540f2403810003d80c0c050208981d1750420b00d40058514441c140c00c0030704640ca15150045e020345010500074003411040f025094904a07034041c0c0003901c024482c00000003800c0040a40c1100c40069004000700254101072404a80848081608802510503107801007600000003130002d181040c01440c4c64040d2a201c0c408440000e03010201c40240800c90451440c00c3d0f80510400f80302c0d114583e00143c4591001c4061000f80015a20080710301d000782051000ea6100d20703655401758281510079004020740c8010465603090f441d0000300c0d005c1b0714907402c20208903600009120074822a400c483d526082a0b141a8480c403652400320740c040d4603c200419048404a2105e03400380c040d005940701c1540d80d0034a24240c810182820310700750010300c1110a0980c0101449002d000d0b42b641c400c0c8446158401c05503944401740c4000107101c11900315188461180c03000401440c0d2000c0c511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184568624 1250 184567374 184567393
    0x1030e0c030a0f210f080a0510180e060c0310050a0e0a02210412030b0a050f0d0305090a080a03030f091e0c0801020f03040b090309010f03051b0c0d1808070b0d0e 71
    0x402800380e0502c0307080014108401f00e1000889801414013443d00314070510480b5180111202032102010f146038a030644070740703c250034610140501c600c140c4207100c01907500e00c0d200c68200c00009607500725a101d80300156040c0092140019030f00c4d8443c03c00d640041e910210202d011405d005650072185580b401d640400003042504e102c6081615120b032070600c03000c00d01500304a8131001a00640740c0010604802840900d401d66038200300f0750090600920b441c08040115085e980c8540013024a50311a480207010194148102590861410010024403010350303111a50038040d02c12900481c40b01341180c00502c00040450f100500020000319951200c082e41c101140e0411502500d01e1100100080c41402d804000c60792a51030503900e200f44101c01c51010740c0280000341100e0f81040040d401500c44c440b1b480c00910b0411314140080241550b50303100100707107014058140321405140c070401c1100e042c0028004c000e60b01c04824030340e150344003c01c031003009008001140c107482c0700b07010f4003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184569874 1250 184568624 184568627
    0x20a030f0b04020f070308060a09060e092406010507020a05131505030a03050306060a02210c1e0712020114070809150306010f080c0d0c080601030e0c030a0f21 70
    0xc00e0a58214000601c071008008081204a008503000c0041c0c205040180c2000603114902c1190b0040380180303010015519800c611045030070f5608410030b030140c20800d0280c185000c1104000141814505140e026445009281d5900d40a42038506004001c80c00200710341c1e40e0b180c5400681000380000c6000c1c0d12162848005c0e19200d0140100503c0d906000b05070b500700402c95421454040c0c40c1e0070701c1c5403101d505000e000c1e84400d440900b1070248407500c011416403801c0489000c48406a00d98440c0c00c0b60015078105420800c44031400500b6908143d00c259010907030388103c3d559104505814000f5000580707421000703050904108000045c032b0020042c079880a0f003404102610f4050800ea101114030030944400d540362400300e0440351041107214450380105a02c0340305826281d0a184004c002036040e2900410001c0114040c1c100304040c41d64148611245507418400401000c1c441d000403c1d02c1e0402c00c00040c051136245020fa500b032044070f20103552a03003102c011b404141c90a0702070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184571124 1250 184569874 184569881
    0xf050901060f05041b0c0c0b03040f0b0901050906010608071709012a050d09170703030b0102010b0a0f09020f1b0703050615031b130e15060405041212020d020a03 71
    0x103481002c035200748011946003040d102d03000c2d03455810b540d984a00d004000054620303080c400021650301080c0c8102051900c0000042c42c0102d110300601d4564403500c0c50803042c407100041c00511b4981c58041041100310300001c42c1811a184d0341030124003a29100c2007224100f000b1000040c5424403c5c083c0f095242c0e0541c0080800044c2243c02014244080c00b8582c56090040d0250002141807041e41800c0710705900030300205105445803001000c44051241450b0011f0780d00b5008659070754929000740d602030103416000345003200c0c003840c107600b002c12218281071580100442a0b0b03011901810721041982201c0011a0000c0c0105030785a900c1c81c090b580725410302089a0078090359000c200305a00e108945c00024000601400c40c102c40102164200e0201c101c0d101d9010303941c0d131005503203407010b4071402040032501005071950b801c00349220b441d4010041c1c8658061486d100070000440c2201d00902d8004202d860241f01d83c400c804110f8003e0f0044070401d9400910000d110400c2d16015030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184572374 1250 184571124 184571129
    0x15090d1103010c022a031606030504060f05090a060f0608070312030c0806150a0e1e090906270a080301090204090b01030902090105010c030c05060106020d120605010c030c060f05090106 81
    0xc1c0248400341d422a0704a850b035041000000d107082c04041e16184c201000c200010741110064103c1c3c00405c3c4107102d01001030b20590008010030b980701c0078401482400c1c00380d001035100d419000c0c002c03828080740f0103170740d00054200504a2582c801c0580c408c5c0e84550030010050034030078101d4107000c0d180d0405001b95450800d41da00802c0c64030803400c1d595070045160511071840203068039540c4d00007014000c256404501da6004114110041c000309039690044812503440f906c50040c00342c8140c0080c03004038100038154115561008081064102c2240e034000301e03006003115100b4483e251401c145141c0300325103d0060030342201000200c1d88500c1c80c1c0c060800c0301d5035401c00f40300e0412090015000c80342302000c041c0d048042c441c010701c0300b94018a0107404662007450071405403115512041c1c14031038203801010040e0842c01202046a62144803422811545c410820042d45004000b910b81100000000d003407050044080c410312480781c0c010688591741c03a90a214528010400d40c0c0204030b1070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184573624 1250 184572374 184572379
    0x6070c0e0603061302100518040e031801170604020a0912060f1d1b240903010510080303041104110304050a02010206011203090905040501090c03300e15090d11 70
    0xf440001d001c00311101d500039106030082d100f600380c185003400446155101d10400c0c0340c00e15105510001c691598801c1e100402680c401031621000e9100c8201e004900c681c0c00681042503402c42c0e41c0d41c4000c541d0886400c080210380050392650b20386010b485010440e405003024000c0000c0c10024401642c110400700740801c00304100c1c0b9088d440391200d070041183c400800d568421003000c00c00c0c2c12802507251540100038030300d9041f0162004502450540303c4484108088041410b445a060902600d0b0304411101924081c15051500059070381c000240083c1c003141701e0a0341c070502d03038489910081400b41d400101655a18080c10015550302030308604034014894600000340d1a15981c0d411420b0f00d90556850344211329010001d4042c003070282c402d64440d581c410300107000640c0e80c00d001c4020361291418240601c00c45642ca80c201a10200f07410080d404003040e0030003942c1c0840c403002c40b0101110720408011500051020034020244507136041031032000305105000c5800351a044004c0c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184574874 1250 184573624 184573633
    0x7030f0506040513020112180614010608010302060d1104030b0405160503121b0c060408060a0c03230a0b04020f0d0e0d020a081b01020f07021f120b06070c0e0603 71
    0x1100184803c8420032190700303002807200144180150f12400000286044260020500c0c024000011701d80145900e01100c40c0e541c6e507400d18884030750700e0280714010030450810700c0031907245801040302481381520760084603075614a20141000d1001c02e94001d0754000510500c10300e800c0c54140e69801d0001400c15840c2704503500040c852a00103004113914000780145030800540c8254441d8031424071840e40303e2030240440c03910f02c6d0340703a01001c0c00082256800402040c00c080015104036440a070302c050070541405543c0b0b21034510b40600011121101e000c51070729135076040c1038000604008003034070780c003d00014440e11440c180c074019140c40340e01c44e04100019101c0760502542e840d0710341403040150300400141d0002ca804000600030030f00040354034410003105002540d00320f03408802541143c460110303400c0d066040c10780c2a01c0c0860b410205151402c620a00c01500d6140902c2d0400c030720940341e03960400903403102029038040310b030300c5040541216110044191442411501c06009104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184576124 1250 184574874 184574881
    0x3061401050f120102090405040308010f060f050304120c020307080309040606091d04020111061f060302070308010e180a08030f090703110913050a050a0c061809020c0f0607030f05 79
    0x5101155049940c014012800b0080031428094880042940d01c0305a550034014502103071a00c0c010b01d48214800e41c1c940788190704112901040c411941c02c010100441100d8a404064110b0122a00150040640030102c090b45508940350400c151009405000c0c40350300180919001000d000c0d6240100d4041c010742d5240c000071502c5a03240d105d54241c400d01410b0034007199034140101600a8010325010460f01c1114202900d848400d45600c501000d81b10709102d00c0e0103043c40303840081d110528047d072401e130307103914010043c0c03006028520035030206d0004107000320010f010342c01013640720105070b8020b2420341c10203031110b030000c440704040f00e20b007440002e070b9050b0080365007426640e1007118045485103800c1803046500d0000c0454003c241000301220101c0c000304410b12800d88900d0007000000c80a1030700640c903c1d000da01403000c0c000d843c445c40d030040d030303840e221803007910241e185c01600d1707052039030006141401040500029000c3d0740d0074420041e5154004036500311300c00206005a03103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184577374 1250 184576124 184576151
    0x20f0627010c050c0f030c0a08070311040b0f1020100b0414040308130614071101060f03020f060403210e100c03111018050f070b0a080702030d02130306 67
    0x7441e0190081694228071900c013568a0403514408800602030212540e503008a80840c01601d107a400070700c001d03405203008204020061600039503104040c0e80610500051170041504121048041071042041460740041c0314401c1c40350f01c10301c114088011000c0030350703042c01d075445131070016101034442d007460740803080c03803c05008440205c0d44041030300030b00d55900c1d1030482d6032880140540e002c010207442c82c1e1010611a0094501104421041650314200b0080c094414030780340d0b101000c07590401390100302c038118a021400c210394041d14174110032011203000980920540e08010214504184401108103100340c01146502084e180d1814520303c074020060218410140e150010303000700d40c0040024400c0000c080e1100d68035044441881c4000d12150075203000034071282c0c274548241c0340c0000b4807a00b041644032180c02c900181203810f0800c0c402d40b5aa02c5130b21610700501c0b004001140050f031003041210640300301028215162040c0c6206003900d13291511090300e1642c00d111a009004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184578624 1250 184577374 184577387
    0x221104091b08010b0f30070305160e010201020c0d0314090633150a090e090601031b030b0f0103170310051c06021308010507020303010b09010507020f062701 69
    0xa1510ba00d5108a6030b1810030029016484014420300440041c003203000b0380030100b44800d00c014110080313842c104200c0044011a002c00070414403c15003481d0511080a4000c0e42c0d8248a9080e480d021024140c0200140d01a200b40d00364100d00340318548080540584c16444800c4001c4412055000750300e580407220b9071440161043e6418402e01815101481820b015424100320801004102000c0910018424a000c10704007030580c2c000044490ba1305031b100d40018060910500001c080c0d0401121803a5600300c14000100681558642042c40d0f40e94942584000c0d0b900880307000c1c1c0c80c40c1c01c0006002406007803000701c5601203245c810316244500201a81d11900c0098085203280341ba00c41000601c402c00080e4950700b040041d103090110307030700380000c0040c43c00404803070100030f2812140b1400c440780204900110740060005201c0131800ea012203101050902c0d2071900c0f0795550000425100790100d4856000341c0c0020501d504200350100031044201c00030100c8203130901540155040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184579874 1250 184578624 184578671
    0x80607020c091305060907050306010f060e1c02060f0408060c07020f01080a061d060a05010305130803060a0f08010902031608100e10110c0f030f0922110409 69
    0x15070018003510010b414241e1841e0307489044059451030346942501c4050604509840d03003d5a07030402d17901400242800c211950052000c2c0c0d2120149500d0414003d15241805050700d20500d080500140342c503000300d842071502a00100056910403c40d6860a041d50140c8030301141383c06134800144a0107d0003080d10345064015010a91091101d001100d0006000b4403101806907210303404030b002290040c0c00350841510303690b0f01081d82840c10070000b0300440da80c0003d0405091004104001c44c02e0b0130380f094050360050b2159149e80758140011048052a000b80100304009034002501c0041504005011402034040d00c0d0407402c0003401a002071346c5405960340f00d43c030040b1030f00e4079207003507a004210755641e010548100320301601c01d800c00c1d5550143d04202d054004540c0c800302450a008a4174140720100c0114070704640c035503207a0304500407070a20500c6403a408100d4038040085401c1c405544640c500200038844415081c10181d8101e4040c0460043c07070030498001d40700e5a6004040d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184581124 1250 184579874 184579877
    0x70509010f03030807031d0c090c03010f0b0705010207061b030e1204120501091202060f01080303070f03090f060606080114030111180a15020109031d0d060e01060b0310030c080607 79
    0x2450742c00d5031030079145500b0282404080555403c110a004007040e84400d84880918001d001d4841c84002003245019024004501500040004010f001440c040d0310f0111110401110b448080d542001c5009028102001d004142800242c0c80c3c054144c0c003040c0d10500300d580b020002e10f03140341240c5507502050003850079084e80070841030002084092031224494812000480c0f6401c196840c014a146040307401750260b40240d042c400e02c3e014480c0d010b13014003031400055046162071240100203188600c0c1400915960b00c052078280070231050f0b004c0129412003024000700b80c0c1d03800014240c11003407060040c0c5240e02800503e1500c0e06009900c0044d0340f0b40805802c0c401c5030032000742da050204000c0390748042040000103450103003190ba1800080301d80c000040f075000307070304010b17140f0801034012212014103802c020606a42d248144808075421040000d9000c8d079148a090060400340c00c00240c000000c41000300207201c074074040e02034a00c650007a01815640ea500c0c02d41d154800d94602c4c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184582374 1250 184581124 184581149
    0x9080a050a080f040302061c0b09090a08070807080a02060103120207080c090c0405030d0507050105070903150e0118111008010e010e0c1c0e0105010501260a060308120907050901 78
    0xc0031908201c040d2040c0340c108280320f803030556646d0000702254000c2c1034405101094901c503141c0300043d0311070103004040940d84148203140c1102015200c0d104484010003101010442c1c00601900c6010340307010f26401184030f40c1c0c0b080c803014042d5407020248001c59881d44640301c3c450b801840841c206040350303001d00041180c0e849c51420000f590000a00351a070440e030501c80040d2950342046160240a460b80b10a5503481445c140310742520320007402d0390706000c2000002c20008000300d05a81c1181c07a1504c00148a071400b1410074054462007100031200c0d41044403d00510a920801084040c0210307004a025903050300241c0f800c0c4c3c424401c0c020713083c151500402921700c0003c03426500c045e426460740d1902d4040280c11460388010300030000256580d80144800600c2442078a0241c41c00742003401020713140901781c0409104407200500308445003c041048046e02c1d421070000f4551080d540703911026100803040034450b04840b03d110520410724009010b0070300c46c41081c1038814080c080c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184583624 1250 184582374 184582393
    0x6050414130908030112140c06031602010f060b0c0601300c1203030519050105150918180d0507030c0618062c0c10030c1b0302070609080a05 62
    0x1d486000342141d412910384803140c0c00002a00380b4025406005d42d400c0c034080e44412403c3c03521140341d02e0760700034009078440c20006050f81e81d0300e02580c0c1d2203940c42c0b04104820f10602c404034050300d18000400000c90614402280d0700b10f0400280c40d00580003821101c0036031381e40318401c11028580011040001100741d001c46410700c1c0e10b0301d150285003e90760350030186540c0c2c2c0403000c82070b038032850660020780c0d40c0c410310003020500d00b40362108807141041400300c2d504003000501075400502ca07055550100260354070043e21494003036000418001c1c01c2065a283c428071507403000c81d81d0858200a8040c50f0050b0b51658090340070341e1090b50f015070301c0c40d12241c41503694000074000c907003080d0104590340c0f100d440016928010803640613000d906000c560544049429030b00d40550846003540c0d00800d007a200e154a5205114800105515000c940c44442e42c1c0d06a42e02980550080104600350f88030704103140e00054444125107095444222060740ca450392510781c0c10014009040340c1000d00d05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184584874 1250 184583624 184583629
    0x60a0303080601180e180109051209040605040f02121807031203021909090e0a02091501111005010806100b180111150402040f14241c02090106050414 66
    0x76582c1c06101030500700300b0f103c003109184072120b04030313880401081d0800741080303581c100040e6000307407544407200240558a40d5994040c0c95280011800c2d140c3c10300840c45007070555858010100802c2c0240082082c84c1c401180f400181d400b103401d102000303c085010942102c103101088080400d0280588041380c1140d9410a452064007540000c05400b07226900d01181420000301660025848030079606241000343c509940c01c03008400b41d160440c280e02c00268a4040d2526402084c00d581e202c1e4804244006a8807110309034141c1c2c850744906000400402c446601c62410703510b442c022103106030340b0880c440c00d80c5a000d02407001d0300c000c2409400c11192040c1000d080b40d2a050400c0528a400884514138005101ea034028480c8102d2007480154100b511400c0b21000c2c0c01e1a0030700080c0a14601d0b441ca209000e0040000140c0c0a00c030501c000c450b43c0003407107a000740280047c44a000c800281c041020003c0d105a12409100000055035402402203804490031081c44903e10084c40c001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184586124 1250 184584874 184584887
    0x30c01020d12060e0c130803192303040b150f01050a031802060d0c1704020a0302010f03020708070606061b02032a060c010e0f01020c03070605040f021807020d0503060a0303 76
    0x40004025102d10004c109420040c0b40705101e240550034040e210000711170100f1038241c05610105040e0810000000601c401100810101c03805041030682010700040c551000700720711015602c0103502200744410000b4103000c81d030241051201000b92000b19504100b20f000c500c1c16443e010400820400e410580603401024040d40020440441c980254000c2152980107502525426507a101c21036020303a0071a154400d400c03080402c407440c03881c11343d01140f4905403d0002a05000704c6030203200c40c2c00c2c802d4040740c1800e5070115641c2d44803401440d0000103000076006400c08208841040c00c420744190725443c500c0394004004040302100c6010000d40c0e81c03100d00c284a0b20310b1500113981083c1d05c4000041541c10030101c0009000e0218410b001d0510400307403032049050740100840c9031041c42c00403d48000b141c2080000809450b20724111a83c0c14020f10000d400c120640d00095444048070341c81807040c10180c0a503101d100990100701c7e41844100c46059001c1035024081c004070f40b2408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184587374 1250 184586124 184586147
    0x60d05090a0b01060201051603150302061b0106060309020f040b0a09020306030106050306040f0c05010f0914061b070620120711060309010507020d110c040c03020417011505030c01020d 81
    0x41d50484829602c0b94060300d5070036000040940c0d1504140318140001d107802154070365403450b00300700100803000800341c50465480301038411200400c5c1104541c01c0e000809a00c042403000070000c60759140c4014020702100c960507071045a03101a400403a09180c0201020740d040240b00c0880503052902c0d0000942015110079050765030741e1008100b50302d0400c64140641e004400308000340c280ca00d008507100302150066410000da15410b0f00c582500075008105803415040361010100f0800080383d036034012890305c0d02d40c00990205c441d00d120004103a00c01951925584c1d52010040350714a01103180013030b501800654440503044103503480c808040c1c85424860f9000e5030203049000005000c5800c141c0d108d41ca103075960030901003401d404005803001041d050900c804a4180b52807543c1d2a260030340e40e05800b40e41c2b40e0301405000d92107581100c000e805441b41c5250404040d502c5a0f0003016000b0f207071140340e035400c040801d041c40c00213190354411805900034000b182440000f08c92142600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184588624 1250 184587374 184587391
    0x30408061f1409040f0809220e0d0215040224030406200403080c0c0603010308040e160f0e010e03010e0d08061c030f030603050106060807020d080f060f1219170405060d05 75
    0x28041c130155541c45020303010440100c8c400d1034030905940b1041504031b91840c0c01003c0f01d94010252182080d0300490282c190703912600a446240d56207002040e0b00c2c003e03200d44103001815a0010485130080900134500a60251a0070080c01c1d03d40c0403010502000000000c0d01114144001c00015007160b00a0030000c0a01c030a071425880248007003180383d00282c10450b203166001c00c0c1448040e081e8190b20703a125011610402c40030092003009003100c131000c0b5075602000a654031004060b40103500d4000c22036406002049064540c21805889102240c1000d0014442d0004107405151000200380202e10241c2c0115101da5180d4090301c83d61301c864910401d1640340e1b81e0001c0855000c0c8240c00003484540c8412180b490f00080003410010082c5248050054001c2400700901c000064141e10841c16200035500c03901c0540012034100306140031451910070301200008210840003d000340920a2107103840345040b0b0280c009850040d8020203070003040501058074001680d0300030903001000d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184589874 1250 184588624 184588627
    0x9061f0b03090f2505040c051224060301080607030e07090e0604060623040b1504090c0e090903160f050d03150504021c0e030408061f1409040f08 64
    0x40345142041504101e0380d2601940022a0107507040809120403c0d444c0540707004806402c2205010b890341d200280a085d00443c0e032a001602014069000c690741d100500e544604589481b81c007041d8082c0310300c0d0b040c0d604541445105203441c2064815039058502c140e019016a80d5a10340490081ca550943c0420521404038005683c0002d881182000d4006074060413452501d41804002d0310304a9108040c8130b00e1181c841441c50b407050f540020b51030b50490340490f801612200007140703050742011030081e45c400010009000c07403030395124010718030843d1500113200a0013010490074401c22180000c19800401510202c01d510014502c0d155101303d540030384220300d9486007131804103242c1800011964402c428860711104035940300040401b15002d514084010f60080041e542c040b60072580b00d0307100e0003104404074060094a01903c1d0603011144c051038100d460031003210808005041031403940d24003050f9514054140301540748042c0800348203840396031300d209202c2c642910a4884010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184591124 1250 184589874 184589879
    0x2010207080d0e15161d1003090809041d0724080c160506150a080309060708040314061905040f2a08010e1507021504110402030705070b0a0509061f 65
    0x190b9404c2c2c103009810b02c80302800d248040807006480d820a4066120018254018030b403c01d945440d4450512400c07032a0204e1351091034548500c140c09400303107840e4032900748100c03185c40c2d04019005c508005030803000c54030344070740c3c515081d2444c550034605000b000c0400e490403c04140240600c41c6c0041200c1201e0346041c224401040300d4104e60401281c85410842c140041030b12200620041e0b2142111809031083c43c0c00c00c1e0b15601d11907d00002c0c040c100200742801800002d0b403e880007103400c064824100d400210030b481e2034420841e1031a1140a003409000f915020602c611031090354808503004440c540350f21180c410748040d0007007100c41001c0c00c0403c45141103200c4202e0040440c5400401c240da08501c482c0d081c844401400440c0400340c00c00c2140d000d030300048804481402c821007021f161124182607070b030aa48204510f4000d130000061002040d8000300804d14140034030003c1d00c40d520350740784c001c041c0e45d02900c03122880c0d40018013086851962208039a540501942c0c15030307550b035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184592374 1250 184591124 184591153
    0x13080904090606080c1008180a0c060807090e06030c0103112a101b0507020a08030a02070317070c091109031507140406050a050a030603020d0609110102010207080d0e 73
    0x21103096045070350b283c0724041080504c1d803c02c440030080305d08a41032074070001c995900500c1712030014482500c02c0504511400003440900c6030034a91504007941d040c80344d40f01d1102901e000001d641302c10024494150010700100840c042e1402020002e0203801e00170181c10045018014081510300d541000708801c8032800e4109a0900e00184010a560349078201d0401941c10800265018501141002d02224070030311201e4015800d4206800c0c15034a9021742e001013644820b0680100e4914400060104400c64002a60354200c1344640d01840542c401400100ca050084035402000910b030300c202400104c0c10360b0080b1402001c0e110059061039080000a0314207480012100c4440780b5400a0080342c41e400010140110490101030740740c1490004001d0052050040c008100a004a042031080e4800e410040086030020140a9080c01d40e0906600504084000700c1d0b404075aa6030201c0294010700036200010b82120072142454081c00500014084c8982d131813003607006000c00103a042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184593624 1250 184592374 184592381
    0x603091109061c0614010b0c0d0e270403020d0f051617070605160e060306090c2208010f06210501140a0c030605040605010c03050c01021905070c050411090d050129040b040603020913080904 83
    0x412f610400d9241ca013010300b4068102403000d40c40d0010044400b40c10001190800100c4030ba8031045000d0f1449800c0900300b403040764002c1e040c03070011840c002400009100890f04060701a601c00010240001031000080c0d40401c15a0079098000e481030001032094039010214560141c00d4809075440d1a1480310b2045101c20780e01d0600310003180345001448041000d100e50b0412400c2c4502c2000300600340280d0300036110680d515002c80c07250925140c2d040001c29080b250f00061044c01920300c0d070422004040141035481c0c500e0002a14001c00003130b05151034000c0720216030b0188c4650038516034039203044400d40e000085140c9250340130401c5440d42504402800e000341307101e540780b03625482c070303860859016001503021034807843c1890702c1c03500d01c00503e4003242c00150301180d200c2d040d500540b400a0140c44005444c91014440344124207040d5010b0700d9095a20344102c6041104424040c1000b040b513281d404040e400111410004000c5506850104071950003145064100144a0300107000d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184594874 1250 184593624 184593679
    0x9050d0507030e0604030f121205010f060e1e01050708070b040b012c01090507110d0504050a060207120204090302030409060303030b0a0603091109061c0614010b0c0d0e 74
    0x1440c0054003806140d0320200e040307120300c4121380e0030b4945881c64940394003000c03a00a01420391495510921891405101c411400b409407400030300c5250380d548004070014a640c480c2002081c140b84e900f11151400c2c41c440d11582e201d0303614041100c04130384011201500003040440c1c2c0b6600403c001c601007110800741d01d101d00d110b5a0f410500e58144001603491281c4148144005000030800600511841420a054800324200003c540d6501e401c00c40304050248007004040c01420543c41e600c0380d0000c0108140c1d901682c603441015600c42c0c049955419034401d0000f481e01809101c0010301e4260003040a0754045d01c1240c1c2000d403610030520445035141d00803030100c0d40d1011a99010308040e0505d9000705441e040030405000d00d6103c01e8183c99014444603c02c0740c4010005040c3d40d00c1e941c1c03807200c4070f0400000381d0800305203252050090084030b41344601951154000500200050200c54164054a014105240d20b00b40c05880780403002a01c1d951140c40e0460000d034484000a209a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184596124 1250 184594874 184594877
    0x3030c1015030503040909080919080f030c150a110417010c11030901030915090b0a061203020706121404060c14091e03010b1215010803210a09050d 65
    0x24054948003040807185101104003154034034000c02c10100e000031040d1800c45860ba2030214000000b032418005512951542d507a010340c0502400100010340c1d00c8000a85140310300b1a9400a50300250176540c3c0503405510314150300c803660044035200d1100740d6640100c5d46e818080b0700c0c84c110008207561500b241e00090101d00c0089030240042000340285aa82c500605103170340c000e0314481c01d01da01c074882c01180e03034181601c8070003900c2006402100b02e100b51140310401c100300116483d2482440b4010749070794800c1d80c100140801c02242145a50903040c0d07041e00108541450a28142c54008420808007a1190380f500a052034000b50517480c2d218038498000043c40c00503489018144034903a02d5003c04c20030040c8060030f81d68075040c0800e0444405244041d00d540816800280900440c60096810191701c1c4c82d203281e11000040c06004d868450150b43c00390380e8a03100c00980d40d000d403282d200c6540c4510003140e280300b8581c183e03480d049059114041000e8006031581454140030449110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184597374 1250 184596124 184596133
    0x711040b03061e16320307020309120111090d030306090504080304021f0f11010219110d030506030309040b0102251707140118091e05010b03040506150a0503030c 71
    0x150030480000025844003031003020380044130040c800200820780380c0c412440d545221041070b40c5035401c0f0011010f140b0441150f515968684003500075200c1c0c1048849074040c60b0f15070a180c0d4550740c1030090b10409140306028504094007041042003980711400141c041c5070b034507070010601d5526405003500c43d80c01011b04540d00d0a1900c1400007440d0b03500e540982c2100708902c45048039078410850026409585018501c0c1013100c1c0d6610f00a02c9140c507081d414401090201002c0b90b008546080c040d904d403810b4400210040b08290107440c8112206079242d001008140500d18141d441140c2d0950103204582e103405003041008241140300386d540c03a810b1581c1900704100b04401ca0a82c03228402040500300252502c030f0719080c441c0c20301c05c4107814001c003d144070b000900300301000c80c020102290140000d1040e684644272100301c1c021640c204509100002c560540500300301c80c0100e5200d8004d10681c1d41c0c0d40b060342024000920b81e664805c2c0d107440005481d80c2c00308040d0402d00b01520151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184598624 1250 184597374 184597411
    0x12010510141e010f0306210c050105070809010c08190206040b071b08210103030f0806010f0507020907120e0f06060909070902090a0909050a12050309030711040b0306 73
    0x40c062203101d865074601c103506400501d492032406030a40000b014003130030110400000201c0c00c2d80070b0125078005a41040201d0340045010500100102e0154044c0d240031400b140c440004440038824003101400b601c00412241c00654811862003109500034645d450629404400c43c19800101402d0180143d00041c184001e01c0743c80c4031101e412021500307295040c00c0c2c04078003d0482e125080c04c094203210780891400e00307840c10b05822045903c120785a0307207159070b102e2401a00003c0c41910b81c1c0c00003202c0400051030303540248038181119815855071400c1030901d500b048103000e80140301030f04000201d4904032864219005e62901c45842001030121078115050385440c000004013040e20440c1000309200713080da0003141c01c405a94008002607580c10340c010206441a140d6031049620700d15110010303080c40b10114500110f203108005004c5044010101150b990006564591540e00100b20010002c0c8155031541e01007100580081403500c3d01400213401c220301190402110508090031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184599874 1250 184598624 184598639
    0x2101020a03050f13060902060c0a0f0308091204030609060e01053916030e0310090308070206070e010e0a0504050a022107120b06090909070501140408100b12010510 72
    0x2d050b408060b4510b482c00030f00d414010015403000300e1402501d102e56400004007035413188001c0b607000801040488010300314914202c6c0b82c015092b0816800a4180000700e500702e0341c04201d1501101e41c400f01c01c1d080900350740303545004241e81c0f1000c42c2c180317a50f03007002e241400e003e025a0b03102d80810015484444d130441c002c0180360040c0080c030112038030849403030010034074880261107070101074803d2461124032926041e60b0303071005407690588c90f02c107080f04000320b251660000d2603038a00c00d640f010200d881d2444180da4583c1d0076580e140100b03011010740d2a00b0351007070300c0540c0142001013581e9445039841c0c020030111402520344070f00300c6400007801c155828501d8910055078140b8440e1a01c14641800c000f000400b0850940307110548500d4006499611070080d1400104010f20b0910141071842486540c0c614620070a40424421010000042440c0d002e8604456103030002d403050030070340a492030081060000c2582c2c17010040e0301741c005080f02446150f105074000050b081d800d5041911 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184601124 1250 184599874 184599881
    0xa05060f0a0b04091503080c0d030c0c0507031511030114010906020303010308040b072306070f020a05060c0c01060b0a0e041103040503070609020f03101d03070503182101020a03 78
    0x2203030080e0124902000b0072241c1c1011942120000000084d030004c441c941c0015a0b250340d070004d04682008601c05200e020b01040c20303600c80c01c0700c4d1404c100c0302070072100544000b040800c000c2c00c03030380042008101148007407404810294510f60300040316010028a0300840d0000e801005003c011059000075558004102002400c210700041d0304640c5141ea540c049442203000741c4220300e50102d081d0341044060004072010101101d00c04c1b402c450107414103070f9602801ca031004000707844c9100202d0b605001081d41c980064001015100a58456200000991047c140301d00e0ba036603039806c001036451107580074009191469560b030803646018070401003a80c44910035145280d07020018000081d45c00403c5524655002c20007160340d00b21400010303510254a11038503018012008074521104090f8040202080701d003113488100620200300941d240a1540003c01035801048040901889092140f90039440100301c05004400c50b041c80c40721400000403068103039004a01c0070314143c0c1501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184602374 1250 184601124 184601149
    0x80d080109060807150c0602210405010f06212105040801060816060c0318090207021804030e0108150d110102010b04090c09021b120304051903020a080a0203120a0506 73
    0x9004003821402c0000502e4900394045ca00414401000031a00400003d40c050314254080f02a42d504845058209000351150454003150a9481c18902d40140c01d418070590041d141120140342e007520000b0b009200c1c074621124191419401020844030f90100c050080d1b0300b4070303519540c03035464034504042c181c01d40d00990020611074106040300016161070078451002c803400c6160001e607401c1c0c0c07820207403091800c0c0c41804040b0115503401041c0000c19400a007c0944241c4501c44288503c50254800c0c80003a54024001440c607088070305d980d803081050320303000341305c40d00520801c600c0100000c010404000040701c401c0444510b041c240d40e0203116010003c181580c051109101316510b8040030034160003840800d607400301d0402800200045140521000700382203e03000c2800011801440c0c1040ba03045500d842441c130000007115283c10a044036941c5500100030103415a40c6180980e040300c6a030008502c02405400d202090300d1250500030031842200050500300300303052100440305d12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184603624 1250 184602374 184602389
    0x9061409091b061804060b04170106140f031c020616020c130c0302301b0315060f070c0302030601060c0305091c0804061d090c07030f020106080d08010906 68
    0x120784040b2402c2c038002c620007480d44100d40c11942e840311030350b081050910584006410901c1c103000401c0d80a400c400410548406200408a10607112501c60985a050080a0088004115000c002d082194146004003002410346003c00111101c12003c13403070010b08003005038420414003042c01003142c46128801c0403403015245407034400020503040380c1e507640040d000035030b01c0034103c00c03452207a4180c9400781c01070210000012250b40708421038948120761045410303d4180840c0c14008101d40d0300c00100440583c0c541150345802c004071641d205991840d412410400200317110b0307107101006154091186401c500f10a083d801403514102058001c0360134454625034407000309412001391080700d441124030320410741018000b499030340070940d4002c1080c0000b09010940f980c206002c20100a012040d08850707005040c104103c0540a0300c80c10003d050812004010900c2541220103c520034000492520756500740c06290048010480c1c000880c0c080040c0301a001c40d0003800c0052401c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184604874 1250 184603624 184603633
    0x12030f1303020a0b0a0608071d0a2f0d1e05070f09050d0203070905011d0709030f0803060109170309010e04090302070b0a12020a0c030e0102210f040906140909 70
    0x240d07038010b541e400000c0c10160640440714001116139056401c001c014003842419034014581c0d455004a840300b8070304c00041e80400c0c90b400950840c169204090701c08500581e1003c400c1c01c00b008840040c0614042180000703010844495810320a001e032101d14281450000030010f1103d44240c00c40343c01408080410050307000c1880e040b90b00001084c240c03401110408d00795507a51001a00c1c1030304c0c543c40300d0380050820000088078407a100481109500720452040705542d03041003151079045034040180101c41100c040d00200340613102039540210706040004d00f143e1507030300200d2081c0d1500100b2420b5070000403d4035040d40e214035800080c000c01d0f02d0512401728a0764020b901d50340280130700c0040361804500e501086100350720400201c091141d0455480c7c000d40401000c1000210055010500510241071603510000321160350040109030340e1010140d040301c5c0001c1d07620000c014042c8543c14040400c1c5200a0320070580100ba84d07800c4142c01319070643c140080801c0082140409030030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184606124 1250 184604874 184604911
    0x120702010b131e0c020a020a0b0301060f0503060d020a1715130b0603031306020c12150a05060a09050c0304030e0a0303020709050a09061a0307150c11011112030f 71
    0x25000c01d5000364015008001c0b891500a45030f1034440b200c01116403100c40d00700789100310159000301d800c202807030081d9828068591522a54415844288501c1e00061404840103a44a1180c0b01a58008000400c2c40600480c0c2c0c0d000070703c0520b0a600005600c0000d0354228407201820004e1101d006041c0319050203910700411640000c212000d00504181e030b0f500c0006402c2e640c02d10464403020942e1120b20200741d01c0710030080d620720b404d80361940a800c00003060b0701c1c007000019500519014049841c0c0b842d079941e0b20720402520019000c11340141101e40e001c101c2d83d01d240281d9102c0c44040c1c0c00c050301c030f20380740c14010800b000701c41409000399086102031010942c04100a015070701d1040380469149c444000d000c008041ca4903003d440146440900300c0c0300d0403600e090f52400c00d000c8049408103030715019280d80010400d101c01000c02c6042340c10318000780301c51081c100c003104141840403c081440402c141495000c001039401e000001081103c282c00070403145801ca03203811080c0d2455030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184607374 1250 184606124 184606129
    0x30f0d08060321070f0f06050a060b0304020d4e03020a0c030810030204020a0309170301080703021507120504031203020906030a090609082a12120907050312120702010b 74
    0x14443e20403807082d6000240d00c000d0141403508800401d0780401d50840510640c2014002404151401c04880f4185400001d409030b104c0266805541c0042030810281142c0d5544003480c101c5c0440203c13402d40310405403d10b22801a2011702981180c1140040710030502500c1c40c6280c0d1800420040c548180408000c03681e11000b01d5980039850b05000b0b07560388420180148c4081d5603400258031500008008a0b01d0ba40360300110100340c071640701408140f02801d64500d0500007400340b1303840380d0f0040f00c0030005032801c241041740010303002e840c031468080140c407a0390268140d0071001d804954006410420030071304420000d0840c02e103280840c00e203140c42c1c000421520003d003201844a8542071241c0600101d6030110320300550004540d543d440145804001400c1550b50035174003403506100700d912900010501441602130800741518010440c60443d030101405440c40b100da01c250380c40031034180c03010408440300e5410240c4568a401c0d212001c0040000010411401c5904007101130300b00d43c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184608624 1250 184607374 184607413
    0x63803070f030b07020a080403060e0c091603020f0706090b160c12030e0309130519060806010302210d02100e010b0108151305040804320405070e030f0d080603 70
    0x2250300031600718040e100c0320000c92911b2400c0310301a1551170002000000c0010550203c0c00000c3e80c1c20540704c03042514010801c41e2041110071401d00c140c44c0f9a00ca0800344a68002e20750110280d02c0303a403e18140b42c40304411503c00740000c503150403840d07042c44560254090254240900740c40d01c1d441c8070110344e07030b070b0040500d00100120605884145400c007460043c000d59190342c0c80a0700720994030301480b041e44003070081035514041100898411072003040c0306000700340c10341c0c010000601041c0d28503030a000403001d082504542100d0034003081550314006011071445845958014440594100c080404403018404000c00c641e250013018065660071080b03c136030207016403c542c1d505842c0e0001103010307007041e8000801480c0c134010800c410407850704050403c0d42d0344152688880210f181881d075201000784411a583c2c0158030b904a46440d19401486d40b040c100e1602c8240d0070300d510086403800c04a0221940d694202d41161550b15a00a6100360300400c204d00600924541c202e068841 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184609874 1250 184608624 184608629
    0x30307050703120c02041e29210a0c080c0603060906010f03020f040b03011a070c030807020301020403080705010b040e070b09040911030a140d030203010e01050d063803070f 76
    0x65080c0e032400d40d4007842c044c2c01d07014034043c0c010704107020400301d006030078422542540110191901e00191400c951054846c1d103504440c1d815a041075542850703080210660080780d003911400c115800c2031a40070400d0044d5801c240c4030307000301c1550034180500c1c1c42c01d214080c040c07030703005982c14010410503030348003020f95411207800e080058801c22005000c8000e4410490926040355000500054903202c1100542c100c07040c0c1120188482c4044120400e0351094a070301a004000e811414008600c0c450b0040c01074034030080005141955a5403803842940109406441a0f5512a5008a542010300480041425510241100c1da040c04040102806040310700341c0102e603154408401c00c08004017031103000c80c00400b2540c05e000240781c14a80c585100012824600440080c1d006143c040d0080c2c0e0305030f442021021741b9507030a0000340f00c48030307e0526096a0071500d401c9007041d04041c1203042403506040700c5843c3c40203613814400380003e80300d800440313000e0741c0120700410410f11442000c000f03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184611124 1250 184609874 184609883
    0x1309110f0309011b17010f0303021e0307061b030506040501080d111608031b1603031d090f10050d0b0c0702030a0803070504260d08270706030b030307050703 69
    0xc0300d481c2c8114140c0101902c01c0c54403000d014841e81c07502c1e80e40c0c01280c6600410307410b481c0b0264aa80350103c03407541420303a102c0200968800309034902004054581c0914080314202201e00380860390321444240c5003511200d0000c1038140070400d40303055142c050301d940880e007030303c0a001a501d0700181c55510803440720b50300e0130050ad0070107030000e00e002840203000d08a4048880c1010a07261107800361a640107800100d04143c0391071079200f200a0109070481040c4c0e000c481d030341c01c42c2d156072416241440448c421400098194801c2d440690380c0943c0784e400303242501c244003042d1405511040451845400c56445040c4494084001960054140fa0b001c01e60401035504e803049880464500000d6071001800344c8404400c100c8040e070303c02c0c040d10441d07a51045030500d0071529034401001c04290382103c034040c0c0211520542950207010b201d074001d03082c030b0140c0c138400250440308400d045944e1440072054100318810440d00754140074903141c8013002c82c081e40c980305440c0d07185650303200c42d44030051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184612374 1250 184611124 184611127
    0x14041b0206190605040908180a0815070c05030c060114030109080301140a0e0403080402130b01020606040c18030302070e091612060603061103040212122208010606051309110f 77
    0x25200b80003500060000c0801800c14000e441d01807808814070b800c6207180861a0345c9900d00304003070749041c1200f2011070320141c000e0704441c40c07042c030354a040f580f00030401024004031104260000e0410401401c1360100e2901038407665050505c3c2d88025007541001d1031190b81810403501c00309175800c0032079046580301810159100c0d50100411501c40ca668008480c0100500c100402e054211500c01d2140b4400c44558213580a048450001c6515901c10140181d02000002d2000d09080d80144003050306400c00344240d80560504003100b422980003100142c004010802a00072802c04030340d00800c000c409001d00031001c400000080140e44103015240b03259102c800203020030b55101001554004509000101713456140205a600568049004800482140c0340600c404540303002c3c04103101500c545800030484008640010103030f22070188107280307880002d130240248500002003000b0344581d0340301c0a101d80d540300c60400a501c03085000c0d040081c1c80000e617411030110b4100c500885940c0703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184613624 1250 184612374 184612411
    0x3010f091d0601030c0905090a0305040b0307110105070f170603210405060d02041502060708070f0e03030d09031403011a030405031b101d0a0b13060614041b0206 71
    0x28203040325800c0c0c0030700081c01084004000e0107810300c515026201b20fa9020b105d1500c82d801340d00e5642d542410081c2c000340c000c0c4014808034200d040116040380a40c0341c4800e945034041c80340c600315142540c440d408501c81070510841580c0064540030000070443c68242180f0301040442c0d20742c4415000c40e0500e5502104036402c1c5460181070310301500019042e40c0d11a111400000001d5000d402881880b00d0503244071242c103480080d50502ca00307815680c1e501c0c191130300d60054440c460030402d44414003014041080c0b10f074a0400c042c0000d001c0440010440e611903045c054484061800f0342040e2140420051114680710450218042c14050b0003959076a110f0821030305600400c1500e00c210301a400703180083c54030001d6400390318082c0e8001041b4803014424034a068904070900c0b5178098021249031004103400d600c280750312403048450340e01ca08000b0340c2c402c0100c40141d04800402c8030070014484d99400c16100707100c481130702c0001d5401058031550004e03548200050403007a1106020990 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184614874 1250 184613624 184613651
    0x60c071a2502040614032802030615012a0f06020c0f010f060605071e05030c0d02010203041101090612050604021c060e0705030c030411010507020a061805010503010f09 74
    0x229003400d503a020034480c07000e592407031620140114410582c811030814801040303400039001607400880c4002e00911240c507912504034034440342d44e20310342034075250368401c800562010702401d8800d03203440100d00800c8507594000341204030b22a103107140c6044800440d85039140300c0340100b00c500d504092000c2d1181c00130b1600e04040d01c00e912645036a03015400701460800015044603107c400181001d01003140c840341d00b1a0300c3d000720440030b4200c44039079040c0051150481031540d1454010b20031340e0f14000d5083c13090b614007480c40e1000d50050398000200800d101c0d2007800e40340220001d10781003802a180960051200403500300340381d034480d0740b5400721705a50360701ea0444200c0d5020120500003001c0e99003409004050511411040001f01400030b600743e882001264032500c80c1d400d0080c116151915205560301900001c5418000c04011060140c1c0e2011000c20082c0420340c2c4002d00c1920358903440341d03540c949900c15414020188014460807246841d04001d0314080140040c210928802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184616124 1250 184614874 184614877
    0x60f0812031906030f0506090303070c06020c010b0406030305070b070c0305070b061f0215090105090706080702070308031302030d0c0305040918020d26090603010302091807140f060c071a 82
    0x6081800b0f26100e800810002e681030410b860034066000c0d1015543c0380d801050700c9120032511200080d41210520000840d00e902030503003c03d1039000064502802c40100b400c0355180e410980200e0380204200081011440000e58401014a07003c40c1e40703003250750040c0842c00b440c880144a40c4000d400106a5255500016030b02034000e00190811600314401940b00c101a602c900d40c2a0050000a00005014003a460050050134010040145444400c03038400c90040c0020086008810000010411100c00345025040111403c4a03d04803232041528118403402c103081030041c000c2040022a82100a6404441005401013185c00c041441a601c14000c81802036000000280c2841801040b081c018032110002901949128408050036100c0c0540e041c640e600082c10001440142800703081290803102044036200300f240032900346070901c401a0444494001c008030070780f0749440c180601100f080000c0d00c0440c50030b00c9040d520354551481d4040d04e40d4090710301d2000c200c07501e003510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184617374 1250 184616124 184616161
    0x607020303130b131406030a020a110604150b040c0c020405130605040c0f0605070c060e1203120f010b090a090c110d0216050a060f030506011101090305030109060f081203 75
    0x848101043d1100f510702995040b00c00300700006030310014086241d40400744003904010004040b00e0a41c1d40700325100020394800b00c090b2041000c000620b072680361342040103e00640c0324501c080c4007440355004080445224000e000d00c120f040865072044190005c0d401e0ba69250152000b00b01d0b0f42d43c452a41c4001820700714018501d0b03203004204000d208002d0061000d4a0201510b004035036541c43c021a2503001d0004094050343c40f04604000c0315005245038182c461020f0041d200c102142c0c0794090840d08200c00d05089010041d00f00164402112001409004081859030030302240c00c002c60110141d6004041f0260303a5141c1c0507180300c1c054801c0d04a01340d5035004680d080004c0400083d01c1e400c030203012074500e034481200032409250580c2120191401980c9083c1d4400c0c607444102d0140c02d001c2d20751414420741104228000c03a003030003180600f5010380c07100f07981c1394500b40034601100e21030342c0092003401a02805002084c40429005480b1245000d803544a440303e4450f020800e0100c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184618624 1250 184617374 184617397
    0x40221030d05060a0801020418090309050604170d0914010507050c040617010513020d0f0f15021c0903082a0a03050901050906070e13020d020309060105031018020607020303 76
    0x104400781c9204007a044144145410360300c0101080c0d8400c800d50903070289001d0480c01c0d0f007104003040e41a030025030184060900900d0900801941c4034003190f004c1c0d116405c000b0b0194034210440c3c02d918400c10200c0d403003001c24075041b44070317500d07210b010500c41c00600805410800006007100078072000308800448018010f0040003040d664802501c095131230001c0342030706035003090300051005a4480600a034260058100f21600d00c044c0c1c0c0f010030b44000d02c0c2c4101e44a03c1e00012800115140305148480ea414052006a48030602c4c10803000b5140ea00c464038080070304224040e00000d0f44201c4503034000000d4070015100c0c1e07103038000503140c5038001c8035400384d1030001041c25507607241e264010600408464008102a480c0c1d801c0103a1100d10848401d0045483d003800d000799803c0088000b1200c4442c00d100500780010b1800e40405d0364020b0b608a083c4c0e40c020380042c4510700d03050101081c2070380b901c201000050f003400c1c14600440740c0c007000640310b00f0001c200c840030742d14103004481884d80364 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184619874 1250 184618624 184618627
    0x140a050c1209010809030703050403020f18090606010215040c0303050c0a0807050106090b06090f09280b030706020a0314090a03020301050709030c0f0b1611090705040603050a060b0304022103 84
    0x1589038038001d94010301c2045000036450360104000c254040b00702c500b01034065692034609401e540900c0302031900c0d040a50b8004180d80c00107102060140003140c00344600c04003420043c140030000920303200301405191a030a041c0020300002501d07002c40c17442241c2c0e050902d01d4442c261542c4031070a0014800010744801c8000a02c8810844103621000a94107200350801034084030380d00380305150040d0403400b0781008401c0140005464410f2105034040e03691998503500d4400d10b8040102054850190031030642c0305d0082e45d45924081c030074000070780101c5c0b0041415004a40380201352110070211540c3c1c4060001c0d90891a4640076400c0000c1d42e0003a000f0300890401160080c0058540c5c40251000c000025001c101c42907901c85041c2160300c40f1908506260209603440311408014a0031111610700c407001c00c0d641c0d290000420301c10342d02502c0f0107480781d2800310003400355400100308070161458a4018000d1500c1e403000d07650050740503100311050030280301e851198403094440c0210540710 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184621124 1250 184619874 184619893
    0x50f0904060e0d090303020106090204082e0e0a060f0e03030f060a030b01060809070b0c210c01060303080108010b010221030403030e010614011b0f0b0c0d09060209030609060601140a050c 82
    0x4004c194502101c1c800d5008001c6255126002012030159015500d840d0304890088020b0840502103d105400045103031202105800c8020040f0b0301017084003540d6800c6603070301c10188400380c454681c8603100300000784207120006440c0e0b0740360f10004140c0104e901240300811101c0e1030b242c407008095a07005c3c03c160169615204090015101210038000310700c10018085000c43c0302c2801d0366080302503503004104c2c2003030341c602d004003c0352248080321031400c1c24014001985400d028220055009440e603507415414003241900b9240b59441d80703415503000e1040c0101285040051925010342e001c0340c3da0316500c0303500d01140582015001d507003240d070034440701084100c01c4080940c1c03428800d0701d44412024100c019031510b10007400001e400f1082e115650700105e0126100c823075003c2d00303541e40b051400050103510001c80340ca41d1001c1e175244d0790210f00c28480f0b0404210080e0020346401c02014140341c40c0e17000038044954100080b000c120f01141d003804141c080d6060320300c031003440000e9a02004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184622374 1250 184621124 184621127
    0x1709240423100e060415030b032b080402031c03021201240309050c100c0c03030903150e2503050a11240706110903031c060807050f0904060e0d 63
    0x30744140d0161040c6015099880c4142c02a070032040b403103c0152100d81403519203820780658900c00b51860b01410b40b64030b0b68004645c0c00744103543e01c40598018070000e0804400003505d90300340e107866480610103480240805641d000441da411000e51600c04000d00c2c40c1504114040d000d44210072401c0305000d400801d0550b1825526603119080c910184825800a01c7c102c003544c101d10000b41494002010600d5542401c9100300010419410499610155543e40641d081010b5000307800207408400140200324201d0b040da05155400c640c140302e101307a220030490b11a004440e03490b005940070902c2c00b46440c03110038488000d640180a4a08889043c20300382041403c4145052040c00c10101c201c2c0c004480003080f00503113046062590078180e03181d84103002458900101e2108610034030217945203980c200010300c1c2d40714683c0108050258002905801c0d03c030203030810200340d00028010b21854580301c400d05410383c4102d83c94869522a420f08000922a00340441c200f4064a80d0740000203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184623624 1250 184622374 184622429
    0xd06050102010513150902220204091b0f03090c0f06020604020f0102060f1b190f02070f0b0a1b05010c1805010c11131103010602010917092404 63
    0x454003a0028070813540c5010740703440b09040680b0300520703955410f0060400309900e68002c4504c1c0744090000d140c0040342d00042d44c0144500044c07401241e80019040c04200d00303600540364101c0c2c1e120301901c8160b0b80080050114030540d4000010035648803007030f4042c09958001a0000c0081015143d050b80e12101c1c001d465030800c4905a002d103082646004041d48006032a92048605500c038007800c0d22503205079420703641141c2140c0e0b00800103000035100f141410003c1c20381ca000c1c2d901c40c0c4150f00901074001e0f0a08103598006440c81138400010840f0100220460f10440c0042c50030b5050102100004040100c100f00c0140c5958a040c40d50300f07c280d00300042c040e0b1240018540d2444542d100011940d103c203142c4014042e41c4c0d041c007002c9c0c00f1305050883c030344600ca0380000803494903000032041e045500268082c0c40141e46440352030040c409086c1c2034a0028000f181305e60300e0310403440003140117040e0594000c0b01c0d425514079090122600503081d5405080c2d520b8255170003144010384524a03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184624874 1250 184623624 184623629
    0x10030e06011707060813050d0c02030606030f06011203021f0b12030406120e0f0a030e121612021504030c0e010b0306010e060904140406150501050309070e04020409080d06 75
    0x1030311405001045940b102c1044988460001000384500c42c20f0290403580e9050141c40041c2d5060000e9400001400a00c0407001d00802c070f50700c3e41003511040c0101403170702d0340250506010781c21000c8242c4c0141070200f122815a019045034030050301035450200d20b000c60880c0030102d402c00d84558004213223082c0d0014408401c0032510100c600c100c6051080d120f100c0c1d4030403400418034900c1e804001d01c200e500300d000c203400c001054802210500b030442d41000c4501800301d0019100e901002100c1c60300c0b009040114406400420650f641400c1100c001c00700d50060001406030070009000315aa0800440203000003100f4180d100c580d03c7c5816454503c080c001c203036840c622440042407114032401030340e108400580d6003041c410302600c141703c1c056000d0031015410036115080c1c1c00d25019040d640c90b00803440f81078005452a8211540302a245068101504002c002c2090084071640000c05205550611105000ba40c540b880020000c100d048801010004041400c0100c00300301da200104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184626124 1250 184624874 184624901
    0x50304180507090e13020a09050403020c13021201030b041b08010504050c0d150b0f0406230411030a020c07090c020d020f030a210608190c05100807050a09051003 71
    0x544800b031040c0c40c0004980209508039140700000342401c0160b1701a503441c40c0c000340151042c29158040c039000c1e2802120300360096440b4540140050038142e40c0e07000f413a01030060440c140218040d61100c42001071201400c40b00c45074020405010b106054454401c440400c64206155925050303070181070111019201c2c2e00683c400d8644509010f0014101c03903074401d885c0506c801180441c94020840c11888a400441e60301d582d010640b03030f40c0f040d000544101c1d100c004040d0f030002c1044446d040701840b01c0380035a0030100925000400c00c01500d420403c11400980c544c407281c03100c907117003090b075500c20310380e41e0f08010302845071076000300381410600702d540c0c01c0c2c48108810031203059507481202c003403c2c0003419103152003031468080340803404e140f00701d4480400c11550311003030383d464004100360310700721010104003403010011440c0202c00180003e6801e9881501c990380c02400c1c8034801040c90b800c2c0900060390102807845152001d0140900501448201c1c1d600c02e030040c000d202c0e6020110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184627374 1250 184626124 184626131
    0x201050315190e070216050d1406090c0901080d0503070507030201090501060303051218060a02070c12030e090708090c04050a140406050a060602070f051207170105040b010509060f0103050601020a05030418 90
    0x6410520209004144070424100f890046d85481e0920020344c1280c50151403101c003828030204a03050038005c2d036010702c2c0060010200c200e40c4604001500c1010780c4561ba00fa8400c510041c59150030006403984414141007241d210a035500f0240c0c050b0040d500b00801c10351030410013004040d04000a02018030402044a050750781b50005c407020354000ca03901d10039640c4014000358050740250000d148a921036860f00903181d54461900b0b00600c0d10310002c4011507400300c04140c007402c0141000fa44800c07a0310b4aa2041e040001c072070790b21209840444c41c09981c803500090303181420354020b0100c40062841c024202d2500d400d02030001e150607603416030407600300140010464400192507007622110b8a0120000380760008108598a000b241071401e40141c4000103001d100c404a404005401d1000200b41403a007440e0403c29158140c000b07510804a03d0309020741500d943c240c1107201c00d02802d0000d803680b541d8005034502602c07154014510305c80060003041c44070b00781d0141811002404801d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184628624 1250 184627374 184627381
    0x50c0a0e0f090619030804080706020d09292104030e0a030b0a020a09050303030405030a080c121f080f100606080603030a0e060f07030503040b010906120201050315190e 74
    0x4050606031010301035102d400200403640301c2c83c05040c0d020840f204034a002c1480d5540b0790301c103c8107030032952016401c0c0c0c0000008200d2542c0501c200c1100051034606405821b080c060540c00980c003203a503031188134482030070314003c403583c1500b154102143c070100498001c0480c01e44a50004044404500040f50807044c103200c0d040071125038041d29070242c103000581d640c14210f4002500584925820400080d80004040d20103000944c000d60164011b59079034004e900300079194400142074242c42000c02c0040c00541d040c0000c02d42d400c424544560420704882e080c202d01f4200319a00280c080740180c0284e02c0f01c0800c005078521740b0300c010020910035665101000d0361600d40440380580c041d042000000803842c0303c8c1800501c00500105035a0030610602038405842e0030640080b0302203000041800305100d0003010803401050004401d20020b410701049031800090008020706000e800f0010540d517100402c5692240000031300103000c44186c0c901058041000c1e845107801080e00c000c0030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184629874 1250 184628624 184628629
    0x20f07061e0513020603061309050303040614060f010e0a03060204141305010b0a0c050a0c060507140706090b09040b040e07051002060c04170a02030a0b07140c06041101090306050c0a0e 81
    0x21180f0600c40c0c1840034201000b00d80900010b688014042c65200f0840d0381000e916910318886c101529018000650301c0b07203481d1505908035101082c1a03201e981c101c400300034031b5030b030741d9142c0903807840080c0390403101e8010280125a00424a0708003c042600100c1c020a4155110b0a01400c0c01c900300c6da04141d1940e815520021110207003c4c1c005003e108100c0c0500c564055208000c070144650105da26400e1507031a1941d459149401c1a40010700006100c3e0601c801800c40f6140c0d00e1a03070000e4205903142141c00341c14161a485025028071000c1840c40d003980d035961062550070720207003080c4009010a400030f40c07241203074020544141e00f02e10420500f103100068042c840d00c2900c001c5450303c2d0034529100b000c5100d642480c01e003403282c000f400005840c10300520603018071501d05005241060903003d804074034a901d644051590030303c5400c0e100e40c400115250420b4000410b240380201e40c10040b03030003d0913500060a164100301c2404045c0e543c1000500603291681e480c10b0003511407204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184631124 1250 184629874 184629881
    0x302430b04121a0f06010807110c01080a0209091602070b04180b0d080a020a02040c0543030903110603040f030e130c0c050c0d0b0c030703020f07061e 66
    0x40458580003071009100c45140322030b0a01d401c50142c41907259103d0158030105402d5011912400165031036404d012095800400700c503008501400d0110a07140341c5180e003544d9402ca800316134100000309000c82d2645001354101e41134001d000d44201c40c01d01d01030720740d40040005880620014400c61000040c0000b5500580b019541d0403607100241c2a0380800c0d20014018982c60315038070038a04103141c00054a108002c0480150f240c02802581c00c0600411084071007a00c800018000100401c0d8000d4075142107441020b04010360704403000a50404240000ca0001c00700251402e08002c91801e068100d90130200b1a48913200f940c01c9000620240402800145d400801194003120510700081c001c1250301210364014000d03020300ca204c040b000007601c0314040e107080880c0d00240002d0138000140303c04055a68107a4043c01944029690104c141c400181241681c1d0000f00c00315805910a0b0111a2000c5405403059120401800c0020080070082160030140c0070160110200b41190301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184632374 1250 184631124 184631129
    0x6061503070c200d150606020d0f111c02100605030c01212c06010801050906160509031606080a0605090712110d09030f0302090f0d030243 61
    0x684603401d64280b641c620301c0320f9607030900740080b0304100030b51180a80c559503074000100c1d001c4c01c032014511580c5a20041140c2454001c4002c540241c0000d02c81181c008013590000d802c4d40c40d10b0b28045030b4441103107007031400000d10100a640015070500322940c0c0000d0150382142c040c1c0d002c0243d26038a904040c1d4480301c010583e030100f0900004002000c441100e07903080302d00110404220b03220074420700c1d503092840900b02442c0e500065804091000e003041040d0150042c1c00080015040001100c1d5690500030f0801a000c03240320b01c040c00e058802c60640d0451500682200c030307482c0402e40180012049070055500180b10980003545080681c044e0000721000501418056102d0150440c0c00610011281d00960b48070f079040c0000b074206900070b240039400c5007000105645c2c0f41c0b47c000d02185507150070808140c0103100c9506c59980b180302d540b110361030403104882d25101e0f41c0303410790405000c62000c41c80801c0f00d500048242445d010161380a01c8034000803140084800c010f0b420150301c90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184633624 1250 184632374 184632377
    0x10506030610180e0328020d02010605090103020603220602041a0703120b0604080709020a020706090806010501080406110c3f070f0b0705040f09020f0d05040606170606150307 77
    0x4900110f4950352603400100c0d4884010140c038504040284016250801e04a101d011030488813015060568184124407242070b9a10090140d9494100060000241800040d12588000011849041c40404921001203102120103031044aa0910000035041449010400260340c00100c1d00d0341c1e0b1560880d034600790306031100003c66500010003801030842d40c16a0307810002c10803002c41c5001e0704000c018010000c16001598420000704028203004c0b40c0c1e44200c0512201000074005218045940c9042da0001c0c60180728075603070303410118090000b10b1008004980300094550903400c005c00c0c45804210a42c181d8071a22001d00105002c403003079540c8511403c0c05044140303880c07920820003081e03100e019214025803c400f81d2503815894900b074500c58017203080020108000c0c2000048140100341030305e421030030451103408050b001d04c03c1c0c444000c0c01503922000601003009560146000d482a50f039442a0390000085441d566402618541c0c460b10b8000210304500030725800b280e1243c10603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184634874 1250 184633624 184633649
    0x402031b010507030c020f211b011704020310020f0d11130504111b06010801050a06030206040e07110f0307110d031b050304031505060f010c030801180b06030405010506030610 77
    0x192030450720781701c2c10001281e002e88540c074211801e40d078009035200000d40401011100050290300c0314685090b04034406040b22020000e103100741e8221800d9241150940c8019085540728400242011030a1014481882c1b000c69506004031402c00604528401804200090b40030701b00888500d02804100227540c0c40400c100b4866410182c1001c039401c9201902c90341400805034040202c80481100064664050030042112070000d005042d000b44030315404018690450b0041949482140200401d1000100114004a105c1d076484044408101d0a0f1113501744400303007035a200d07031000714281e9440d50802c480f134000389012401115400ea040d220009903181041c4420784500c02160b081c0d0745400b0078003000000c100d0f22982204804008440050b07a840c1c48400c200c00d1000b6039410034108100f59600b480002e4012944506440c55011310346250a00c140451015021404d002c6800000200601c010032505412440c0262012800d40b200c540d1480340e40340c1c56070128030034480d45c00319 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184636124 1250 184634874 184634887
    0x5041505090c0f0d050c0702031209013f020307030c11031603120e2404032708150106090815010b0d18030f080705040e011502010618050402031b0105 66
    0x202c12008243c65920b041039903040c6030b082d050040484004942103517042800186c82c00441c6024041c2090031075144107c01c2c18078154900003003c0c802d0303c1e0100e158000c040c240c0d84201403c0c188041d0000303101c0120040003003000c03e003007030044e410503241c400c0803c1c1004400750201d400b03a18a800160b407684003c50604c3d030107000e0742c091420300030400c2d03042c00aa10445201345000e80500744040c0b190400070105109454011918007035814504460004984180000698000e5400020021542304180c2e440a00c8604410091807a40000c8841c801c68400000300111240c02070b04850b007070348400c00e840707540f6044281c603600d41c0c0c15140d140c024144018041000110301030500450100c1e0b0021f6050f502d07104c03080c49140b0300c80040c0e0109016600b00c5d0007240d4843c1c0307483d9120040b07203403460925180c4551074a0004043c0036400710520304c2460340503030714400d51040000b0280300b040d404241041c541d014004000654050340a40030700c649500c2d442145042e00c00780164181d40e03843c940761 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184637374 1250 184636124 184636141
    0x3030c0207081b0406050904120207062c0a090603062f04030807030c021c151b0e03010e07180e01020708031503101e050105030604110d1410060504150509 68
    0x3d01c41c00d05921039a07031000404c42c1c0e01c481d680c00b88a1840740c4051a00c2c60031000001e80b8240842d0321a104114010f0b40890000101e60341064160b200034001401400740c8400041244c046070300112542481c0c10300c00024001e00c1e80143c1c2030020880d2000c0301c400003001c0c10740c40d08111031034841c00d01d120401081002400030f0004044990092814056000e066030014008143c031003100ba880e140c00010320300500854028041040103080340400c0a658140d56101d207080c00303003c10506000303e41c0c0403604107850039040080310f0010f907015981c09903194060300c0f0b5103a08000304119403c0c5804205840780c5414821207003601e800c61a42815944c1346610302046200128401d6014000c13080300404e201210f0050780040103408421035141c07011040c55000b120b1050340250f100303a216a0034003000c03c040d2a482841020140c03031182085005082502025490003011121441004804031114160364002c2d415a04211382c20f12808690380c0c041c40c86803485005040c4c0c089806000308a03101c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184638624 1250 184637374 184637413
    0x1002070e0703110a0815040e1c03090c0906080f1f0e01020c0f0607110c0907030908130303050a090902270d02040218120604030210180b07030903030c020708 69
    0x5035103442e0100314a201020400201e0300030900710008075880c5c5052040c0722280c48610740032408180c50402500014441c0d055444240c0f0410208040100b02c81f490841d01c03c1e0044010303a80c02820b0000303540e9560344080000c1a142c807402d141c2e405080032000018001140d81c60900620402d01102c1c01707130b04c8040c00000c03e441400704103650741c2001400301c0c800052119040c00c0c10500013174202d0340b4105c10060690102803039900802d4000f861500d10540d25051180e410038003d16000994010a160000c0305100e001c89011071041965000010554000010144041e00e0f58504490702e070340b1300381501a40501c4680fa5055803214514400c20060080080741c66400148078900c0341d115500030404036486184040c40c5c00c900a5140320640c141048c041d0310608419000b00ba0324901620025103a20390000d401025603100c0d10440200300c0b4000c211480e103904180908214101064098020808400c0c11004281008103420305d45001282d402d040f10740c030001810640100021902d280e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184639874 1250 184638624 184638631
    0xb0402040c1101092006120a090c03051507020114060904030f23130f0b1e0403120201020705010e06010605040303081801020f04030507080703080904090c090203090102070c051002070e 81
    0x1041000e02904110303070002d000b000440c40c010280303004100c800c140e205c3d0740850100e85840c0a50010031001d500d80c660a81c3c89940b20021000c00164080d80d480c000c4200c0104d50700140c60b503c1041d8404103056444480e40d401091603400811890304940300c6102400000c84255070301c44410000100800d00910312402482068038002e002061005510b540000401307803543d102035804030f25a808030704454040300283c42d0808400808030301d4000c10300c02c00e100c4c80703000b110703065081c1c56101901c84024050700d0283d80c7c0074282e5a8400e0070018004d000f07400460080c0c4181d030030b140084d9a0040040741c00d034142c490903a80c1e103141a09640b0140d42e60032003c0c0c203400c40240498608601d0500a20151061002c0020b02d02d65a61a5013010381c90261a40c11001d9282c001103c10000200b100301140c04010003500e0105101c441414001c41d0b903401e0794061142180000100b00c80c4410650060a9142c41451580660b60701d807024008040414010700015a001c1c03c0140300260007440825030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 184641124 1250 184639874 184639877
    0x804030308070e0d15020c0a0c06020c01020f03030f010b0d0902091e0a0c020c040b0616080306091e011202030a120908010c0314063106060801081c0e0a0905040b040302011103040b0402040c 83
    0xa107201e466a07601c002c041d8039071102b401030700921640c2d0720941e81441141c9101c01c1034002142103040c000300660520f2010f114220810303000103616503101c00780e60820090b90742c00400c1142e2529040d800343e00d600c0c11141c0e81d40c01d120340d03901c0040d501440c24403589401c405180d008000c00e500311360611005020505107164022801d0080004d149100c05141300d056100d45400c1d61641403080500104000c003501c8894070414002c2d440c500c40c0301d00d00c100c0b4115a100001c41100010b0703400464101551140c002e015440d5a80c0203200560300a000740d012148c551000708050211750404500311054001c4680e0f540c112440443c81c0c130701e002c40810a80d5000d08006440008540b10f680c000303542070400340c0807160f1312503004002440d0400e14481c014440b000c0588508038038041040c25403440c44445500b4400c10180440d80c0d0340300c045000029011150041045041c0380c02e006000c0c08086500b03c0c01582000ac8503441c151044080e40c2c01030741e101110401c1c0703465a50801001c0c01c1140c04100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 184642374 1250 184641124 184641133
    0xc0b0708070c05160501080c0c1504020d050d020105070f020f060a020904060f06030b13050114130e030408030702040b03071220091303080f0c0409050606070804030308070e0d15020c 80
    0x40480c40c01c0c0198021318840050000751245040005050490700504804520328103105081550300d0100e445c214101821030450070599a51001075a10100400082e0071840b03000e4240766072540552180d40249039035202c0b09600b94000c034089a0b15290112800d03046e070020404554034000716006008030342c0b0010000300d2165156112000b0518a59000c0340009448441e1b440d49410449400000072110120501c1a1b604141d80911201c805d000003070b006c0c41c07405041500601c4198040c006101c0350f9400d03a95a503540b0f0a2071a505d41004030300361703c5186810801e0206240005081c8101c80c040c84620003010761a8890410400b48854000340c4aa14003000144076900c0315203241c0b2078460301c140e00c000307080da0342002009400014807220001200009100c10025944103880456a504c900421380e81d130743c4400700301f0602808000902003039002c01c0210416801000091052b0b14666038281420b0f1072100300100d41d54115409850400d01e0800088425660f40081c180c0110100841c0e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 184643624 1250 184642374 184642397
    0xf09011218030f03060e01060905100315120204060807050108060121050106050c100504080d020a03060806011217070804050409020402070b09011b110316030c0803190605010c0b070807 81
    0x1080d005101001c110001a41003c90481d00390f01441084041d04604149004542c10490050001c05141c002daa201e01e014090300c06c00b0034443d8109113000300e40c5541c40c201155880ca161174801c603295030704034890303400c3c1940442c0000000440c001141c1051355001082d0329113000540d081a800002c1c28150100750603c01d2a04083d4098035008000940d1032566807107aa118050030310326901503560702c550a06060202060441f02070b03907240c0080b4100141d9800324400154001d0140c2d03845995280030740000041e4a5881221103906613001e400d1820080e02c1c0c1c042140d0701d9200c1ca040c0200302c2c1a080c4821b0046003400d0303002101d0039201401c0146410000c2d1a501820542203940c003036182e44031800342601542824040e9103101003424828145054051181e03141e004003066136144603c145c0300841498841c185503071005c0d8114800c941d07a1b00f00781411515991998a5004d0080c3c1000700003e0755522170401007090030740108a0580e2500c449004030f42a800150003c0304003c01c2c400503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 184644874 1250 184643624 184643651
    0xc0918120f07060605091009021c050c090301051006050715380402040501090b03070c2907090302013c05030405060606070b01151407140f01020f090112 67
    0x203211415500707250a4480c2c1e4545002c0341a80c4a0382c206900481c0c1c100144070080d0310440000c1d003a00d03501d4001588402d00700300018000c03003d4102d03101c1101d09040c1403101e40c0103944000e00c4100d0040d802070146070303152100c4420080244c841d0780001103040002c980030980900140400b103d4043c3c0216004486410030f150542c001e201c4e118040d0403030a111015041c11407010b51103841c0582c0c00790f00701071426002070030045061281030701d03c0c000080000c0c406440b901c4001845507100c4480304d4404481c100b05080d05070013120101032115601d0104158074003908001d0300301c95050750b850403100100314698001c0c80c00780750440310342000e0b09400203055090140e958041403c1da41c1d62612032410f42409844c00d01d0181000e409400204154000303c1c410201c03130340c1510f216800c5038a80b00e000c0401100c0c801d41c004020501108042450800c101000c20300f000c83c031284e40c040710701c00d070041040c00d402c0384529600c40c1c100d05010000f0440c594000c2e0b00b0440c0b01103118400040700080c1001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 184646124 1250 184644874 184644877
    0x3070b0408121611010627141e01050123090d150f060b07030c080f040f1701050906190c05090402040b19020f0615130905010b120c091812 61
    0x640520f0101d902c0f100b000007541c40036100d4407552040c0000d100962a024002c504a4a026442c00e5900e1151407030320080c100c1c0c2c3d0404650398003088881d40c56407030311280c0710f081204d41c0c2e0042c8800400c20800083d6641c410200345680c448d180204140c4402410610300d516444035008581100c1921038102c0800e030395201201c2c00a4514501003040b145030622101124069007150f04105c0f814880080441d900620004010340e21044503076841091100c802040d00440d0f101812322411080007040c140c03040740d10b0303489004580000340405c0d15100f2207662100412038160481000038610900c288199030080c114002441c18203d29001c10080401d003030b644250040c08241400150326032070000010805003a00100344040c150740b6024540c1580c032100b000e44500e40d40307103070b00404d40300ca40d55020b0b400d10303880c041c6c04003003121455900e00940a00740c3d408081c2e1041258413440e4590303070008103504000380001000144a035654000c080d0400305003445030042e911403038a000c0c184040c80b80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 184647374 1250 184646124 184646131
    0x10902040905010c0201180c0501080403020f120901080c0313120903080304050607020f0d09090f3201050a05030606150f03040c0e0a2c03090a09060306060f050303070b040812 77
    0x40000c03072114044c10010342035801c03144410100d20103884104e4003140391004c9810654000746041c1205840342e007000c0789000c0030260358001a0080e081e022184000a800811f10442c1c01c0e01c604c44590303a1454100f817540400c64000700d82d00b01c0049400d00183c0f07c00c2110440d45010300f04081d413070340c49441e0f070340e1141c0080310b046803142e220303209010102e0340400410401c41c0c0030000a154525985000800540d014800c43d0b11154031070501c42540d04403500b0115148410800d00c44200070303810000001c01c04120102146540c1c01d81c00070505080449040040d0348001d4001c007125110301c01400f000da1901c02c402c020440301400001516040f05000711302075030003a80c0c0ca1542c0303401e100001c41807500243c214220743c0d1416141d44030301840440d80f402084041840903d5000440c0011400c40c443c00d195998030483d00740010503082c003503501c81c4080d2030080e142000096190135421006c0c2966003c4d00782c3c5030340180554000907600a4280f0b5005110b080264113150244125418814040d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 184648624 1250 184647374 184647383
    0x1903030908010510180507021207030f030f06080a0209040c030f080a120213031b05060c010f0b03030f0702130204080102040e040201080a140105060a0c0507082107030509120109020409 81
    0x210040200510901071203812584600c900d2480f2031401c040842e0700c5d00c0d41500002c025499900254041e8007c0c014402100f55080790a546c501c05888c0007040f0340c140c03001d00e00105e46401a0944e000341c0318820b04007035814403002400d690826800f0400d404800510442e8403401d03611011001072180100c41036001d204011803602d0700c418000c003402c00300818250b02d130494414040d009140c03203c2a0350740100d03500030203603070140d60300043c84c01841e000a0b00455005140014210512001580400072408404038104201e00d0040c08140c0c0301e01c518021650455420b0000d00d015103811030015041a024210040c909507541424509980040c0e10890b4175070704040c20481556000f251556020114902c1000004000c1100d041e090006024440c0034000118480324a2801080b28240058112044804d82503480070401e40e01c000440058444009480100f10000d03901c00036900840e90546420781401c1400e01448082c648141c00d51800e5901da8400c1000343e20745105018031306016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 184649874 1250 184648624 184648637
    0x1103090a080f0d08071b02030a0b0405030c0106060c05030a0806191203080a0b0307060e010309080706090c0b0f0a080a0603060504031d03030a0504120c150f0f210b190303 75
    0xc00494904000003a00f5030410712030a081080206903109a000e000c07441c500d4000c481c022258000300340340510142000744500b1104042c4070034000d000000c7c000d070180c000020300c0080e844007001c030341214209400030001d610910140d80018015481190711030005043c006400c1c02c1c400001c0707030300ca03003d034003254250b0802c88054060607480340c1d20a80c070880021003809070500420109650b0041c2e03101d04000c00800b00741c20180c0d42c1c03180d0050802c05800c545a10740b6041181040c00080485240c12030340c2d03890401000a41e03412082c25100302c0103003202c01c0b1381400702400055500c03060007808000000e941e2400440011518810103000e54020303980c0c60700c1b50790f040001c5c1061411881003036100303034403c0c00840d0109510008643c182c80083c0c02081c407041052070491150072040d000102001020325111020342c2d88100f0381d2079510200e41d1200d4845003480380c103940d00300c0110074004440031200840c04200040d0f412958903182c01074a076151400541c171010102406940040340004c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 184651124 1250 184649874 184649893
    0x19020d020307030624150e010909060b1308060906041407030b0717060103110405040f020702030a030f031b0f08070207080706050c07210b0c070b1306150806071103090a08 75
    0x9921a0176018100d142000624041c1044003d540b408842c21b003100070042604060b100c96482058104010014858244000d5031074031410074440d080003000800c020003e03440024910340000301c46005240e008050800c0d501d81d0746401e4010100d0700d03c1d4201c203100d01d6200000140030b4110380b6100c0c40c95603980d0940c00820707501c000a030700c40160aa078109801c1401290000c0c410004032400c44908840001c1c282c4009030600740a07008020000e07516000d2401460241600640ca4401d1481103076000c014602400c040802140e21940c00702c4002540c841c070391104240980010b0ba0098801d004640c0c0d8180d84000261412500e0313001080014008116140c034802d0810514000e0280752103400d0404490741d00024a03140605409004200ca0340c2c040750004410008a441c000e03000388400e015840c01c690070401080302c48104960284c41d0140540f02c8010748071000054641c41750242805490b40c650841c1c1e896681e008005844c0400c1045034140c0c1c0c0ca2001c800014402c2c84042c215950 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 184652374 1250 184651124 184651151
    0x2f0a060209030d1e030209030120040503060a021611060d0c091a0f0306010309080c010e0d171005010302180405091c02030a0206040204020a03060308070f020901050301060819020d0203070306 84
    0x1d051020420038131803071144c041444500c0c2c01c0080d4000c0712500e00140c0350360904000030b000d00780c2d10500480080d42c0e050344180c040700c07841c000e2050321416021215161212030603e0b0403413241102c480d18510445100034005501c400c00e013403254600504890a20301c400078180111181c00103d280446d10b082000c20450707030301e080100b03c0c8500c40760a4600303091000002d1b14062100400b0a41010f545810085c1003103038070700c140c1e5a007990201c02080002309401080b595800341c45503103404100b5840c0007c00c0ca00000d80020320404030200c41025840c0f40100540c040d40107403003620b001c0c00c9101d00710a40d03601d8034400c69108004800c02018001d040c87c0c2060b031000c41da480c000c07046400400c0440140750300060351a030015815100140e980083c510214010078982d00000c104600c002400d07424803a40c42c54030700c15140220b845c10011f0341c3e5001003508071543d0b032149401c1078203c2d0410300e4074040199842148580090415810004103600083c2081150341040b1040e540c1c480080003c1e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 184653624 1250 184652374 184652383
    0x50a0c0201020705210f04090606021605060909060402091302040905090a0203120c030d0501091b030e0703060f0905030313052404020409051c05040e162f0a06020903 73
    0x1009103000851901c0d9060b00c13001d441d5003581042a40a5811581400048a0b03100c11511826890440c403a01c40703880700080303006070125118440051140229000d0085803000c0341c0811100000c2841c3d190001c440103100c0820070007880c00d5031050f401c4c02209000d464041c41003002071f1703d0040059859003041000802c80c0d034003030540d00c0c00b940200581c40050320005054580e50700b8098015846070b810254031441c4d8421440946119401c1000010303004030b0b40e0308580c1c42e13a0348a0541c00230508540004900301e500781c3c881d05040f6840301508001050907940701a840c444489808203250300c00d9101c1d6459a441680c41d01c2002c1003038504181071007400e0100c00200760010508030001030a8480c190381c111000390010380700f00e60399820101081420410f503004d194880940000540600e000500305405c10f10500041003040c400081c01ca5100d1302d40d61101d60a652685142010915900c0d05010070407a6614000c0074640209814048100110103c0c079210b002c0240c0d44080804c00d06060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 184654874 1250 184653624 184653641
    0x12030902010207090e1e0a0210030621031d010e0d030e09010f0b042d0b030702100203060310150905010f050f031b060d14010803030a18030c080724050a 67
    0x105440e045409040ba0030204041e9a40000d00c6c88104404a07450806400c5c5022460300079840038541c80360300300750384c0c244d08100e0444145038520f040101d0540701c091079481040700001c0004445d0078100000c009820b11544e108041854154450060f0002160300007685420a80c08654007070711035116440c00201082c003400d990850b80005624000d80e500c40f42c01036005441d440d143c800800400c1040154a400004000541006009648050301091903100b942e0203001400350400802c005100b600032a030045002500400600284062040080160311480c049107aa501c00001c3c2e201d02a002d2680681365041704150304030324080401c4070051001d600d0b03d01940180d0310312040b512204110f58003814007540c1440d0740701e0303044180c81e0042c52490312038a941e03152080007117602e84000002d50300ca1003030302600304050324030000662031400060700c0003000245060115000910b001000d08100342c440c190b0001100c0d603100b00300300c4040181c901c042c003c07a610801c10038411745130b000d000705 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 184656124 1250 184654874 184654889
    0x304090e070b0705120f0f120105010e0613030f03031103090c1e09060f210a02030105070305010806040f0c090603080c010b0109052121120105061908060d12030902010207 75
    0xf40c503596607901c945a0000e0001d0890200020403400c62035a000e01c00c41f82c4003040c141ca000c0e0f64101e9141e40c44c00920081c051140090700e91b61200b5213905042c3d04840d202c1070303c1c2012660b80b45c691b036079a40007800c42c04401c8040540381c4585202844010000d1401002c0103c06000c04645600910002819606001d4250a101d06002819448160080341c01520694094031031308961808184440b0080019070055025008070f840e00c650f000c110701403213030703c02c0300240b004d80c07203652040342070710002e00501c402c0da0013140210340011140c410303040581d4032920250310740f00e940c1c030601c008541881e4810780b403422000868007078414081c81980058070090030058151410040070600384889140c2110082c411942e064103010400c1120007550203402980e80e50606410fa5250704e540c04c050300440c00300c103030304002003218a040d0307042d2071811148040d03d410b20b50b178542c070441d81d07450064200d9401950002d5900c000c40c0c15840c000b121016141c0340882c205800d48002442e0080316807140c44e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 184657374 1250 184656124 184656127
    0x8160504032102010b120102040905010b030103110d0f05060c03090d0306150e01020705100e09010603110304030509041506021606030e030708070203031b060105090a0504050c100e030304090e070b 86
    0x10020303000802d85226a0300841e503151418001c090306900600ba002c54060740140781c19030020f40e84205400402c01d56000440c140080d913a18441c5009a000078000100202c1ca407898500380ca0606c6540c40c00858021145c0c000400c3c61070b00c80ca4100002913454180d2200000104441c030312003080341900c0381e43c2d5031800300080ca00c0d000310030017140c4004a0010400071201c9565646070f208200400c080d00c001002e1000c01c1428450142003110b801d0443c50040d0f01c542c0000604501912590300c09880010340c0905d1a500c80d50111426800342c00001c1c0c0c45a41d4000c201a0000950400000741216400078580150503c9510f24104082d9110b4802c1505101403400960b5020050721600c1d5409030520b520752603144006819030040702c102d00d6084076040b60442d000302c00050303407038100e81050700c410b4400c1d103848462800342e580c101d401a1007540520040c0c4010300b090001402022200d103001b000000440c0002800d613030040d44242041b40d100c8410301114a42400003000511342074036140d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 184658624 1250 184657374 184657379
    0x7030e01110d0e030102070b0f0709060804030c02010c0f23010501050f0303040e0907050303030705040501120b0609100311210717010e06040204150c061104050303040902030903091008160504 84
    0x20395400741024801d0401c040081d03c01c1c00c645007501030380c900948c007203018480f41c5410104d03909421001c82d11400010303200000000c2080c020713964035004e50781641d46ca4921100701d4005449040d06190200c603401c40341e0644030701103082c00c1d03207902c4404071006142c034001e000c01000700d09541041c0c0207244518030100400c07141c0d0b507001049a003203600c0c002000c0b0f407a075141d4480a0929810754000c507010702000040207545a8010010815078500341c84545108003d04401401c031440e02c00040d130001030400c03241c005803500c403082d021106060310703000c01c451110015045142d00020a80440071030b0409140d1901d0030b9410a490340720365a480c20038441c0c40300381d51400b03140c0c9047c410304e89030001520100e015034949404a501401c0c100d074103003902d1010508000c00ea400c02e004169283e510780310141910344240d1088804030ee00003030080d41411704081c00d210003940080d203c01c0d09440100b20f11a050344414440112610b210303280e01115280401d903109a441400e52000100801004103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 184659874 1250 184658624 184658657
    0x12110f0604170106050a0608070305090610091e0f0f0509150f090c1503220c06050f041715070216090903020307050708030c0d03020903030307051309060b07030e01 72
    0x2690111800c128100b60000000103005006000680141da003202c01114081030325500b001c2020301600240d07070104804d981e00c2e03001c50b031243d4040d902c034400300c003901004110500c000d400c00c10405082080300800810310b491484204e4805d082d03030640c282d49801400328480d007640310f840d511030a443d001d032001c1c699448003643e1005000b803440b0f0800c42c90b4008112500f5040090b241d40303400280c10714072401080700211f9219001140d01e4001240a001e40c82c55031981e1118032400b04d6441030100c803096050100a031010f4000c1a494580700c2001d0000080410f4440c1d0310880f540c4818014212454450318002c1720450014082c2e41554440c82c4800700e1100310200f00001c584070240000784480d01ea2500700c0c00e5204201006c2e015100e20000030504003004801806074500c03c604840b6007113041d81e425002da00510110751b5060304107100160b0014005c81c01800340b0112020f00c50039071344e1079004035400c035085c41d04800381ea4000030811004040e0408241842540d00b400e1600e41040a03440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 184661124 1250 184659874 184659877
    0xf0705040203040c0b04030b16030b0d02061e07060b01080601140301091d030307080702010c0207030c0e07200102031005010302120a09321c0f05071b12110f06 70
    0x8140c0690381c000005000c0c00b080100320006040c8002410f42d50702e40d81e00f08080e4480040d100d01c0e0424003c503040070086070003440368040f51180034212a1743d00040c0e408008041d00301e000341481c1c8291103007151604140c0717003000346262481004c00241500006000401052004001e641403014400717296004051503415281110002e0318082040b45200281c0c90403c0d190580700c4001d84404802d0150007500692060b1068040d03030300800079911400001c03030b901c2849100182c0700e0013088406000c4024201281540506070341009148003003c141c021406028042d07109070640d40c04401d005580d20035111600043c18246400d50811009082400d0041009090b42591565404500d42003000d041c40d0740b04039080440181c8440e100c4075484024410040032446c80c41c3c080c4800c0c002c40c40c1c40c000c40340f1078041f403a40d0f03034a45024068001560ba0754004003040e00c80007200921600c03070741520f0506001414200380e90b00e40807401450702211403203a01848910034176405c214040140c40382e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 184662374 1250 184661124 184661129
    0x100f020a0203030408070804030c0303031d010204230a0b04061107141305070e04020319060b0310060c032c040c0c031e031103010801200c0c0607060e100f0e0f07 71
    0xb0340003940c600f480c0c80c02d10340d80e2242d62720081102c180d0004c000185501940620b1003a40114031420310a480050b09908030f1046000d45507104a0503800c0b0001042c5442c0d0b402801309000d08005100d580b100c944100c0d0790031030f5200d00001603900f2a6900d4000301881120001d1140914941082e1002000500000410544103003455590310020341c426100b41131a10703410302d01900840d900d0508800c4440c0c003003451074038403021505000002031420420000c6074070458046041d92000b50414800f00c40308400e03210203030b042004c07203101d0071090410055051072008001c1504c501e00b0b02c0d1801071205844040419006010b80084440003003604094840c13070611507254001d901c610211000d03030003820a54481d448210004c400403500351b50560007103402001603622000000c5105c13185640500c510140e40c3c003950001e50070100303e800c103140902070640c820040400c01c0c04d03060010a10700300050008806107a2200f000c0443d80c0641d10074005140c3c034200c040c080d01200700700d0a650361850351 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 184663624 1250 184662374 184662383
    0xa0c08010506101d0d0309171f020901110610031103030703170a06170c03072306071112060106110703081b01020906070606180203090606010c11040c02100f020a02030304 75
    0xd49036561301005082042241e000080803210007146505009012841900030140030b094010b5072200d0108000401d600d00c000c490000400a0b0700e042c04020107500804801c17414070110b040c50000d420418080c10707114040a40711010503d00c1c5051418066184841903070191b041000b00d00301080c0c1c03100b10340200b1007a517458000e00e07032901300c4170000808085e84500c03211a0398101000041c00007103441c03424200b04500321407400ea192000085101403000340762588040c46030003400300d82000b201070a60940034241209019418201090307400c00c10000ca200c140e0840001407283c10780183c0035581000c8410014142e135401c664036601c95200350041c40c4889071364541e1011240509404844005e10040c100c035403110007030301c0d081024105c0c602444000304804c081c0ca0003041580c0c42580c2c461034104000f0242c60b00ca08005685088507120241c94071001c501b44400e0603140c030b008100340010554014880e9455090340d540807510403442c20b5400c94010001e102d9916800419290002d822 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 184664874 1250 184663624 184663637
    0xb090406050405150f0f060a0c060f0605100807030f05090a0312020f070215070812070e01020d09061809020301060f0e0d02010816050d050f04031101050405120706110301080a0c0801050610 83
    0x7050003e81d00700da03141c5400760307c00b070300042d0b481c0c80f5503000c3d048503440d41c0b1035141400b80106000500094031580d0246940006200e103511044600c03e170701c50380e08481c10b4180050f44e1203102c1c64042c29a482152510b019a02c0300049104050380101c41e0041c11a41c0141141070088134090344090748a0b020000e80724882c451401c200c500b0f91482202e0700b00341e00c218820703956110780070340303400c0103c0486200e004a02c00c00034000803940042500e520440359591030141c0c1604040d000d40b400085186400e801f02441900810126024401540030303000d5a210403c450400f001c0003030900b003040400328000c543c0c58102c200140d805c234038001c0e08030714a880c5000301d41145117021112809401c5008003040d06045c1805945804281030a0085000341e9504105003042d80360203080c1c400644000304168000c010700e100b00410f5402400c4810711807200403a815001d01d411400751782003a0000e000d00d4000072154020090b0000c031301801481014028010b52900c480010344003000307100c1c144140300d030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 184666124 1250 184664874 184664899
    0x1030501030c0506070809090901060323120d1e0204090b1504030311150103030c020f010810140604030501060e250807050d0f0e06090d020304080712020301090c0b09040605040515 79
    0x91b00140d5007155005004100c091400b200991b000e06007034801075030a1020400c3c01c03415a00ba02101e40f41090080000303100e40104108000f4003070344001000210165100d031050b080025110801e44104844200540c8644c10203051008540f13100038034902c945400550211088007082c01c0c1c03400c40360142056200308250480d5681000c0e1a00c2540c6a1034003a00c00202c209900200407040303041c000d440e600d64000038000151865181a0707803d05803915101700c10040f4807119803001d854500c01414150a0960f0385e03480901799410381e0040c00040400d00200020342171001c40e811030b40c58070028240d4641103403c3e0050320710f43c0e01500600410000007400c160140345600041300d0300d4900380342004519094210503803250303403d41d80f2020b01c0c09031040b0b002c0c0d094400020b6509540031034000e00482450841d411100301410502240c1554a81d175840021a113508070b01e000074061881300703075660425102048222001604003a22540c5001c0c2440b40d065206c0c1c00b2040e0884017940c03203026108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 184667374 1250 184666124 184666133
    0x30c050d05030f1612030e060a0c05040510020f060901020702011403070c08160311010507090b211009060e10090506040f0c0507140c010c080f041a04031101030501030c050607 77
    0xc940e03c0512401200020601164101c862801500034052940010081c0c2c0003a01242980c00e1150095411b0707200710081084c18005902104985000382462441c00b80d841000c524840b2031803411802682000c034090507151000e100035070b03001c409a0021403601c2415400038008515640401c3c3c40c6007404070005601c00d006000303075502107801011140e00c0c0d0030b40d60201020040301c0c080880c0069410044141c100703805000b05402240784d40c03210604d690400e08102e01e66085007003540c1c0c03c086c40c600fa040284007594070150086d0403510301400d585092144000c1610103660203d50a4036210003004540e0341902040820744507007032008281600d0b14000980900481c10100e158030345004413503c003c0c4d400074000e1505501c118040d2401040c003110039916a1003041c030041c04941036810319400941424020000c2c9600101c82508080c1c9a502000194080c0b000206000c8000541841400413010040c03500c1c00091906104542c10350381c0350702600313040e485594050840030400a0420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 184668624 1250 184667374 184667377
    0xf0a0905070e07020d030608100c030902040f0b01110609070603090f0506010e0105011b121407060912270504020a02070905100905090d0507030e01170709030516030c050d0503 77
    0xa50000d04403850781e07450b6a0480703200d041c01d80e0500007601c40c0a095020f518060b02489007140e590401600a8201c040305060180c012080804d00700740c6da8401080050f6128891078010300554000010303804642030001d01200000b0460061030791101c000c001900f00005202c000703517800c1d4980480c4d5010035140214180c0e4188030300500c2c902030480049840c60b54485614104c3d2000d0b031b04c400810000000a04540c0820741002d01910b8003550651015405400101504000101c42900d0902d040e140c5404a40d5140d004aa10580d49a07480403800d038400002c1c15020928108442007048800c0c4e002060f2130584119809960007290005080c4e00034410740300103003d44a418800c0b4075107a25104820b6206010303401c8140d1a08002c1000c030716000070142401c405684403e842d00c210340d00c041e204150b2400b00c1e00d041248410600c0a0b5403848a412802840c1a40f104254103007585403107400c0071070300b8054200100c2059802c10210300400d603004121041942d080c0040c0c0487c1c140181103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 184669874 1250 184668624 184668641
    0x408090411090d0b06010206010b12040206070c030f03120b01090510081b12011a0f030103080d090f0f110306070512041103030408070f0501050913020c010f050901150e010302090f0a 80
    0x1242603007a183c1800342841410b48148800d0f070035110542e0b200e8403510b03210f00800900c2c14522491800140060a08038020310035035010f00283c0e4002e030740c9c0780d660240e81d1071840822400501010b0b010700c02c0c000305002d20082070009027840b840550a081c04034001c144218081030411240202250780400785200e001000f0b40c81e44503141c1d68019a081178481c0c1b110038400c42428098400c001d0300c81c040c0c0c90040d2030052914680c01c070300d0b50b4a19201c40300c40d500031106c900d1005070740748042000525264910709a0600c00c8403940c0c511401c50401c014042440c1c2c150394002d400c0142000b5020390300c40700b29030745400c0c10040401c9035121424400183c40340c0f0003203035030148000600071408090000c0c0050480e820b20840a000303a03102c4004403614050000210340148400e211003001041e903402920b0204d0b0b58400001d000c0c0101c000103400e85000b6505079115941d12455a01c075090460340b048003030b1100c100121115491980071881110000b06810f01d008070000200300c1440150b04034101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 184671124 1250 184669874 184669879
    0x2306100c021e01090509040809010c03030e070f03200307180e061008060901020903030d0e0a0b0a0204050a06080402100305070212040602010c300e100f02070b010e040809041109 78
    0x2d84007048224104000c0c0100072007030104a408200203454500390300708600c11688908414106012500156610303003180c0e104070141500c0e140c101e05185020844d0b90001c1242c460b004072402d103581004001c4142c00e150b5890021f50402d8200520340b0006100d40464900b004401811901c0d2031002c0f00034002c40500d41a1030003003409011043d4016140002515000c5040d94210f48031840314508030320468201c0307034040d00300380414400544250702c103540b82d003c10025141e40c82c51076903807a41010001c845040c03405501107402e1100781843c00c100d901914480c00c104400c0d0406400080c501d8100d690518101a00c5200141e140741c8248003150010680c40030a1f9112a11400302038040c1c052b40c0341050004008075001e100b10080321858803140d035422442c05d0700d040b42240b00072000c0e0810000950b6544503040c05c0c8200c40c1c101e8400c1e6144240300c41001600c4030036600d4202216541039000f100c0e00301d003000900c001324a41c40c04541d1009000c840002d003200402902e44d010b402444140c65 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 184672374 1250 184671124 184671139
    0x908180f0a0317040b0403121407030c0803280c09090612060504020a0308070b071829040b0a0509030609060402280506070501200a091e030203030c0307062306100c02 73
    0x820080f02c8e400b44003985251248a03031010004000c0c20603025192000d4001801c0e8a0081f021880c0300c0001d50f00130200640072076800d0041078004840070014504a6911035444280748085540a242440a8000454244006858218034170005082d47c0b0001d440103170790360041421955140507030300055902c000c006442e00f000b07061004a040049409001050300341c03148040f60300f815440c54054614044040404080520ba10161240000c4000600f50002c10004c12558031000150140320b102c3c0d500c066413440544181400d10038064a03040a81e4040310900005a803186000985030b102e10b00e10a034800241c012142182c000b9620460300801c00080c080c0c1070004c1074200720b40c605001c0008102c114043d0110007c0f91213510600c0e00043c1c260704040c0450b070038140300045105100c2024100c9207403640c00082c103560101181820b40e9100007203110801000340203001061500c10841d036880c144410405ca41c3c0030004051a03c18038200c10410b0065002c1d240d80d040c0940c001d810803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 184673624 1250 184672374 184672379
    0xc060903191505010801020918090c041508010f05010e070c051c0c05010516080a0906110a0507230c060309100f1e1118060c010908180f0a0317040b04 66
    0x1040d4900020b002081140d007031100200b40308a05008a60000700003070120303020680341d01054180524084c2201b80c04d03004000d400d00b019078880c0170381044100002d0b92038400500c0c080d0000e08481000b00c010f184070381030000400c480402d504846604c00c0c00d41c1408401c0c0d041900d00701c0d00b8410364a460402d0600000064400d650340320381a00c4805100794002c00c296180ca5059074001e4040500340000282d003c40040e203c3c40b0310343c00228100c1d00c90b12002c00c00d5540b20110300c1e0303030703401160103000001d001042000034403075980d0303030103000319074000c0c20000c2c1481c14065580c480b545a4071150040d0400000715054a41c10080c035109800414800c10540c2002d05109000c2e00f9005200e0100907940100e0864150803846541d0809600100440c40e00b01c1d41ca9003c441d0400c81c040056205031300f80a4090003c9080c01031044c007601c5040d0340c0760341c3c0e90a030b5581c0840300364006e02c06005101e00184a503854481184003000c0d66082804640031003000e210f030400328451900f01501c20380012900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 184674874 1250 184673624 184673633
    0x30708040f031101030203281409010b0301060e0408120712181511030a0522030930060b030304180b040605010e1c02060904140916080c06090319 64
    0x20000e0300c0c80f07040001850340c00003004405030b000c144d64440444406101030000c41032200342600d0340b0680300c1e4010400c9030001c140b8000c0040300321144110350351104003562461800303124070000740580340780e1740080c0c0c00c16845803650341c042c00451100801e24080403d910501803000c150745908010018001c0d02c0c80407501c0d454000601c40c2c02c0f604104100d1403488c110140740140686d40100440860843c1e403141808405010301174950442e001c004140d8401d541e00ca5111194090700985510541e1850303c2d9a0860b01000c800c8100e07141c0304813088001c155880e182c1001444c680140d000725800720004000382c258465a4400e010000c0c4040705010302d0070094000c00110041154108001980d071801918464001c244082d480401040d04528002c0410b160800c0d03940060039080c217016240c00418102d4110180760b00c144031155080000b822000c10411481c5d800034014840a20716100000d583d9039241114030780700300b0010541e081e490b1810001404074400314001c0f10f02410366400c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 184676124 1250 184674874 184674899
    0xd0c060b2b060c03110a0c021201020a0818010204140f030c10030c09090b06070b19020304060f0c0c030f110f12030105030d03020408060f040206092d030703110d0503070804 76
    0x403280d10381010150183d8a000384104011040001481450040d80310300c02c4400140c2450100d80c000414840400784800c244054085207543e82ca40d0300c2103092044407425059002500c40440b1b070700400080c17010031800550411441c406541c14101e1801e0b580000b0f0600b0480540d07940c00612258071507006941c50f4000d00d80108554403070780c03401d1f500c0300e403030f24103445400c000030380c0044040007000c00282002144aa000034001c842014610201100c035007607a01c01d5801f0780d18280c4803483c0e2104000684580f03c5881c04034182414400041e540181c0303000007880202083c4100021561500070090124100580514098540c69000e81001714001e4000380100c501903c074800c1a0080b442c002c0c8203c40035101200010800399441007000624a40000c00c2280c00410901542c44543c07143d80446a03482107003201800070780340c491f99502913060914081c0e4842c0e8801e680c10008a0b825840c4490a84800d0300c0300c000c41075081c1001d500d50301c29404010951500001d0006040b0910721 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 184677374 1250 184676124 184676209
    0x509030f06042108010807030201050c0f010510030314070201120b0a03020d08130e0712051005030f0a0201030c0306420f02060a02270109090204080714030d0c060b 72
    0x400b200380d0f050528000f1074a81c0d41c24011a00c1c1da80c0592403d1000d907005402038032945c1c13a5102117400a00200001d43c0c00d50300d041d56141c05210440360309108054000c44604000d50344d94240a0400c0d1081e00000c100c1c0d1004a810101d0319603588100184c0e4550400034005980c016046070030200300e80c600b920080e80684032661406011000109500c0c04154240e4000c0c0e4180da20000c660420000640040c00701800c0081c84031810680003440b61003e0280311600810302024058082090001400380c034180340003a004c261501c9020b0008451344604880140d00c001005054243c000c0341d103d2848106909068904015000b048603640c0e0003106603403103500342c0d400d452864503910340304000d9010f000d002a10a0300c0307411600781c640701107600c9107074607140502d0142401950350040c0d50807a40705401c0150305030002e000500c07103a007100d030002d86c1d0001c0039402800c00a8001000405040c582d900c010728061b21406907030320940d01e003001280c65601600b0820416006400818405a141c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 184678624 1250 184677374 184677413
    0x1d1f050105011106070e030a02100f080f130b09120c06010303020f120703030c0e09160e0f090408370e041b0f03111210080303160509030f0604 63
    0x90004511540f151112001ea034512400401554179107a80540e54041c1c0030b035403a5003600c502c800030009a518140d03014480300c0d050315018642c4800c0103000303100c071500500c940400704625050000c40c0d0201300f08110903c0c2c200007211407a490b601c121a062180e01b5204020402c004a40401e040074040340c9641281c3c82030f021207a1201d541403082d0384803480407445841c00d8005101c8040400e000b50007541e4078940c245401c0c50705103200400100701500c182c4241c07040000301105140c4083d042001d1400d0510105c801a900c05041d070b0000d2a442e600420041039901c011880c41c16682c0da1340c220200d45070342112401e120100c8240d03040920980c115240780011100b20720322030241040c1c17260201c0030b030346041e10f001100c4100b0825615503507424a54000c060b5203e40078400712080341d000d402d06101150312401c10741800b0040b419100e1003600140800c2c0c1081080c494216005038039182900e4072400d2040d154401c02c00003a0520315019003020741d40c02240100001c21061000c3c013042c10004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 184679874 1250 184678624 184678631
    0x405010608060a1a1003181b050105070f080a11030414040507030e12160506041209170309130209030d03050a0f06030b0604023007021e030304061d1f 66
    0x940030740303c096a08010900915012400d02c402d01c40c1000e8402109241d4141404034108241960a000d5056a11825a109089101010f02c41910308004030000c05003440c1c50f9060283d2922841101d5500901c01000c03481d00042d4003103e07074064076103142c000c1c01c3d480c20b5a4945682c2e100410902c6801c607402d034403c600d003100042c0b109021748900d46420680d00b000301f046c1800050402d00c250310504026030b04007a15148000000c0d000c12002e84194460020002002c80e185006030003010250450031507071240c4052240c1039000001614595a0100c4140306043c810b103d03440002d04c2400b0130381740c043c0604120004c80700e406811040c000c0101130002c10034001156480421102c450000802800c08100490390505e0300e50054811603900c549030380c10500283c0a074840140c030441c5600e1300e0030540c40403c21019018801d000503007446001551001060100385034417440010401484c2e19500c04005141c1d10310074030984610402c240480d0b41589104404030000341e1141c1c03800014508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 184681124 1250 184679874 184679881
    0x60e06030103050a06050c1605071d060315040f12030209010806060a05090603040c0902120106080606031e181f0f15030f05030702060d050702010c0c0201090b0f0c06040501060806 79
    0x5109080341e04072034000c00a0000f5a186641d004080c01000d09022100b0b01e040c4090401840708060280351640302c2c600521105103814420903080f071541d040c81404800c00b00402815440115078002964011845052a580c4500d01244501e00c4a503015100038000e82c4400101d45e0182e0050821000980b00d031a2036503103120410590348100d05213080055402c0c441d070001030403c0e03405190011700c100d802c20581c544540500089800c80050081003102e100c00420549800003903c130782220781a03400b01d14525150b030f05901e41407004c10040c24884081c0b030005066115a4510100c10202e140641c1c1c1c0000801c00b03110001c403c06504408114078001c4012031504c4030348a02d40304925541c4254008628548a400903c01548070581e4940000c101480041c0c0e1000020700e0710200500001501b03041440f0001c0c00c60b50912190b5041c001900310410160f030b04448180101e98024500d940c0d44e0350010340004490150030340d50314207032040030300740420070006400c00001d0314a660200c0e9402e94 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 184682374 1250 184681124 184681129
    0x809010e0d03051e091203120c07050303070c02060c0607030501080d0201090b07030b0102030d0f0203011a161101031512170325171008010b061c0209030c030601090204060e 76
    0x828800700100462001c110700a003040d4802240c02c000440520080e0034811500e004c0f50703c0d8070b010740440e00744d500700056122110f4801d0b00381582110005000606100d0742e43c3c0d6507a43d9100c050321000902268543e140c5c00c541c3d9040c1140d141924507400d483c054140550003034007920003030066043c03500501c20106c54641c4144180e600d95600180d40c084642c07a070749402e800a080351160300e411400100400c4030520118004d020080d41010001a030f030b50f26002d5882c040190004801c1034040b010410360640ca08880c0201c4071450b0001c020300003020400b001a0002e0484403e40e68030601d00f190000b41c0302c04900d80e060581c1d03003e030045000003207400245a42902c0708170345407152a90020510b05031640700a0301c4800c0d6201c141010784110000c0003036a03040801c1154154180d0031405001d1203100020300a450a80b00144c403503500301035603000511084012149024405a0b0205240c0c100d5502004488007071000a0141c40407940c5546410b0040c0d8071034012400454106500d000c81030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 184683624 1250 184682374 184682389
    0x50705030106083007080a0203040e0a09210e0307030b010302040c0309050601120501020d0e060702010e06151909230f010303121a03010203070504180212190908070809010e 76
    0x4041000046130144440482440c14050050414214503000d01c003030030014100c00700618440c0c51a80085840d0741c80c1158059501d900200024001802c00100200092030100c032844c0c02203151044031600748944004940d00c5030390441e0325505200d000000000d001010500768181d038001d4400b8003400054860a03800e5412081c4001e100d94480f4004012a9441d042c010314401d12800015140800740245a426a454070700403c5c1d042d0010018400310580910450440b9164580500141d1809001c5c174030103a5401349509020b07400c070420341404a1040e4051b500a00b90f004800c2114024041d40030030b0007180b4107940d207504484407000c92864000048144d040701d52540d103681c01e40300f1040d145009030003070a86190b0521012201c080f070a513000c0c0082d600c2400d20341d4409488504e81190200710302018076401c003406104015051820b0803c102c41ca50060b80804002454070010000ca0010101802c01824070140800c101c820007188200606070694243e80d0139144480442c10030102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 184684874 1250 184683624 184683643
    0x1502280302250302061b01021201060f142b0204030b0105180112080702010e0a0b3004110d0503070602030114030d0c0b060d02031002040e0c0a1b020f040905070503010608 75
    0x4107040e01403c000600c0c080c2c006160886079000c0e14034490034404285400d9030003084d002c2d05400a5a00103000503640150041001d100a1409130b84060b510b003129035451060f401a00400c0210964610380f2051074106254100c00510003155030b69524204624200000e0140713522503018201c1400c2000300312a4040c1c1178580041c0d000ca102880c5641c0d200140d48000c2d0120f040c49030480700c4452030b03518401c07150020071405d002981c0e6020515a601c28003400425001c1801d000240c2d5a542e411100f84900d6000d5400303051600fa0101f40380c00a4072483c4130840040035440001070050420041d034001c1c604958035007803551510381c80c0c0010180c0301c442d40f03500880000e40c2c0d10000b02c0450203442280c0d0704000003600302220341e403181d00800e0410702400c02c0300c0d12072500002d04004049a485419500071880240355040601c1014001c0c130300500108000341c000c0088040c0025903407114842482404024010016405585451909ca40080c0311b40d500c00d500c3d100c1c000800b0900812642c15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 184686124 1250 184684874 184684933
    0x40b01050102071211061b0f07061e02060606030604090b0c07020f01050408190c05060f03040b10050d0b0a0204090216110102120d0905030c0105040c140102161502280302 75
    0x90003505c010300c0780c0c0d42c0040708140d111390248640071200d80424403043d500c000100014014440c20108040c0c11018001a0568100070b00c0b200c10301d41c40d5001c200550403003000c546281e0b4a4071001d001a010f080d0a60019201007204000c0c8010b103e201d10040003018426134589080c1c41c449001581e0714000c0d8414211207801c000d40f206080002d00310000d101c58882c0e4803019800b0b85920114100b17400105c0721140044000003400188a61415647c0e40310f000030100194050500000c071f6240200c82d40c0c01004410100d02154002c0e50f550140d40180600c031030300715269032899070304d40d0006104e55000d540c0d0f1419420010000d503c04620404018103050710540381600c5131795010024101100c0555407400b0a0102050300d10081c000e150145001d4400740c2051030820524540e0542d40482e5181550321142e03075418603800d2000d203203048a9401d40c1d01d0340a0300138031100b641421036114958500c108076103114095450b80d40780380d0410707034003c1d03003280e01035401e12281040c05100b00c00a1031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 184687374 1250 184686124 184686143
    0x6120519110f03010609050c0702040506030102090303090108130b07200601050a0510020a02040903031e0204050d0f021c051608010203102903010306050f0603030307080a0507090509040b010501020712 88
    0x329904100100644800b0040c000141407135a6880400488105840154103004000354120a40c5018061240c001c00b044000b1860030302064000b1382e59203c0c600700e0a040c4044c1c0d0300001c004900c0000341084181e005540c00006241c480d0006041900810461440c5c00c40c1000e418800d2000003105811f841c0090003d10070b05080004116102e040710014100b144202d000b1400107071214040c1c0440c07188a510086070710100b071001200901c3d0501100c41d61988103000c200160380d00d200200c0d03c001d40059822031041c1031400400d0000e0407040040c41203840c0000034008100c40090500b45408503148440c42e420b444183c002d00380c0c8000d81c0d00703940d4903c03041000d000da20300002510024031034440c40e101e9103041c6901e03083c0c42500240e20030780360310303580b10304122000f4170050609500c000110090740c903501d000700c8040d020600140ca203091841d540c0340003458860080300a131000c0e0a004040100928091405e2030b081c050074060705006000c1c800c0700040a0800034400d04020f80d01c5181d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 184688624 1250 184687374 184687403
    0x12030c08070207170111130819030801271a030706020a0f0b1f06050a030c05040e04140c030307150e07060c200d05060405151003081c06120519 63
    0x4413030114481c083c4021955803800000d68407803091008044064102c02c00755607440c6000700e440d0900704004104034400010b0342104000950103601c40341501c00c0d40189003041c2c01c01c142544031a440d8a512240d80614041d03070350f500451007400c0003821020860031903950a44603031040380c845503080c0e0700601e00005900c0703a1000030130301c400345e070791142c5059140c1d00c85000b0350103550034202090340b0807400308100191464031140d050182184204039410304e01d1810345007806400070104014000b48c903102c84480c1d2000c80d41c00906c421003003840010212520b070712540c100060341900e03050400c4500c078608454000c0302c880c08100c400c12141d4070380b11a8404070482c5c0f160607030325010040150240118001454a0b40e80b01031080c8035845c01170f0010026450146089844d100c3c0f02c00951a21441000400c410540d00000720419a64403441e04c6484064220f20b010201d0b81d032900c000c400c0c5051180c042220f070381140c0c1088806000c1c1d41110b20307006030508404030747d0040d001c5c040c0c003031040c1c032049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 184689874 1250 184688624 184688639
    0x807050f04270305130602010218010c051015050a0905070212030a0b06032d010b0d0902030a02280b090307050f03031b010209040e0c09060409150912030c08070207 72
    0x541c1810b5880e1034500403241004541c1025401144200c1c00310301c1c086109408014081155801707000d8034002103140808030003d5541200c11406101e04011080700322508105040c400704224129011007408007003080001c00000368000c1c0500380c000d10407040001441520ba0040034001da4180d005807c411a01b81c040141e80e44c00204608001c54131007030648196101c0d5002144101114509000c0303d8420002144000c000004512080d60054006000c0708000da811a0140601e580002400040038404a030030705a0200c8080c2d0b04c004040105038540181e541a5800b20001c8240d80902030f45130560451640034041b46240c15038440e0200307000500b080f6101e40800f490040484c1e00780208058100301c000c600050145503a500810107440500f418002c1c01d203000000b070007034603514170090003241c40210000c0645200740c5c0c454000034107001580d17a0000d050321514005104801e01810304035a481c140c0608440000d240c4003034100280d10411490b40038080982c040c00e24036142003c4c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 184691124 1250 184689874 184689881
    0x31e030603070f06050703031803171b0c01140702070605030f060d0618051603020625020a14090a060b03060d0303020c0d03050f0c040312081003020a060503100807050f04 75
    0x3064051003400c401240500321400c1c07460042541d59582561800a450000c0c180c8100c0b96201030819102035035000004e0700a5000001503403080315140703080c1e50b49800c2540740058041d243c80c00d0100060021003d8006411002e20140c00e1040d100340e540325018105d03510082449035200268091001c00c926040e500241fa030492801000c078030841146441e00811504483c80a00441c0b000c080004c040110600c488408044000f510b549541c4c910b40102c0d01900c140e2440710300e600c0d440c0c245c2c0e1400b0001d40142401864000d002c0d9048691a20b4801a44401900c400c520800c10a00002d5100140740580415684699111815038941c442880a8003030b6900003202810f4092240000c600c40c01c004810030070000d41e501040a08100016548003c0d0150810704910004c200c1030001c0b41c8610b140d05021500340c0340500791541c80c58102c3c05420303000d40009500c040e00581c0000c8295000d4003a500842c03811a1a9031019130758441c85a07a00010300c10309400002c143c640341c1c445d2415a2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 184692374 1250 184691124 184691131
    0xc050408030f0a0504150323012106060b040e04052b11070e0a0903081b09010f0e1509010813020906012102040306140907050a0302150c071401030b03031e03 69
    0x503d00d041541b120703981094100010b0103100029a100316207d140400107000d140800441101240075505144ca002a00c401000090320360030300301c40180c010004a0b0340400010140c9041e031039126911034105100107039040d9004d8a00748a020041940d01d03604620b4210284a086407109405c1102c0c003055648001703442c40d600355030155420000700c21200d10b84c040c1c414100004009071800e298034000d0b2800b103002c0e009141403491481400810124201141c00405003402c000048141e042d1045458003c1104419000314821218102c120154009801c0c0440700362558041c0780d0f5003081c0c5030b001c80d2074418003941c010501b9000c900300d54010081040507803048041a055140c00d08040310507603005034070803940c1c0740d640c1102010069840c0851600301e10014040d00c0d0b4107160000045900586000c040d01c1441c03400b1009101c42d07158800c070f40e1582c2c500c41c15121034075910030001199050910304e840c08a801c0a001e00788519010003150940702150784070401d88403403005441c103581c0004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 184693624 1250 184692374 184692377
    0x50a03060506010f170f2205011e15030206371403090d050a032c241b071a0106090801020c060a020904060302031203011a03040201080403080709170304090c050408030f0a 75
    0x1f0718210540b9041031f600301c90803d0040d800450400c4800011f0030071380c41000406c202c02442e0030f040304414908040d002d02201d404440d0245c884640c048840600305901e0f80c00b0040d03400c1c15117500c4001d4064038842d480f141e419207800702811842e000e4000148801c803401002a000062240c1e0f200740a640030706521000c3c0d00c1c0c00030381c816000c0d4100c0c2d8140844091302c2c4641601d00007c141d45801002a6669000c131000a0301800742140e144001452011b80b6441c1140407804031000b0311f049038400e80c0e54240e0800c08030300326400c05448069540100380100c03400608a05000701e200c00050086030840700c1418010005540c2e0070400c0030083d0060007140d42d120fa2500317000000b595040112108040c2c02090440c0d07079501d0725100c0038007210f408506500188041c410040580c0e00701d00340079805038240c2060310700390341d0f0b48604607941021500701d4803000d11600144412030100102070016500500c00c200b00d50200c1c02c1080d40e00d400355100342c0032144e004100441500842202601c400c0c8078a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 184694874 1250 184693624 184693651
    0x6040203061804050f151501020d090603052a1e090d030e13050108031308120426030c0a1b03050d051605030d051603050103030210090507050a03060506010f170f 71
    0x545c4400e50601c1c0c0d40402107241484070034140a003012110310340c0b42e085a0240000c040e2180c10601c050140301d854456001850b5481c40010090b00c10754003524542d0302510048141503101010526150f000a0000e400300d10503d00c101c03020b11012022030b080c043c03006013810481c07075a40c1e500311403612113107860fa41c2041c40303004080070100950041c54042d140c0040a90307220a040001c0300058401035100401d02d82c40340d05400f40441c0f1b080121415510441d404e0080034852401110940b8002a003088a900c000190249504008280c14007014840d004000040e1402228882d00304a107000190041c0c100d081407140701406500280060007003c081c4884001d400d1300ca16017160444071080f0103103500ca0782088028841400000620f16060401f00580d5046441c000e650714031009400032a42c2d41c0381100020b00400300043c1c0d0003020018a0361440a4907450090301420007038a6607030103d80d03001487c44d0b005004802d8078034034151441058050340c1d2070b4440d0710b48180000e04500b2040d0f11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 184696124 1250 184694874 184694893
    0xb04020702030d0503040215090604060509030c1009090b150d1d0f01050103020a0b0a171306060312080f0118050c04170d1e080115020c0a120b0604020306180405 71
    0x2410320848000d1949504c5580d00c0740b5060040c00000c1c3e11540140410709020400d042d040c0d03a550043d581510000d00c2c3c490340342c0302c00c00e010902d040000c0d0015940820b41c400c81c0501c00b503100303904409075104140180f00d640104414880d5480340d0790441841000c0c1801050b0702103029901050801c03404649000450300d440b21014106441e08050400c0c5035110b02c01801503081c41d07104000101420b0700038500d07000c42103200502c0da1034135094804804d40c2c02d60101d5050004000031007d40c40d000f8500300180c42c4e0313038a0420740c034030038612004c0041207107600020b203000d00f0070b44080d04130f032041100d400304418003580160007400000c100300c140380d4080c8004070b0310680c519116040100c44000601c1040e44200010307011110f01d22081c003081e2181a8503135131040c4e10205442c11594602552142200c400300241d003444034125206820401d80e50340010500400d140c0e01100a00403082c1c581c213500c6403414041607110840c0d40c590403140300016003020003946400140e000d4010030aa481044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 184697374 1250 184696124 184696129
    0x10903061a0a090b03012909041106040632030c0306061306030504030e10020d1b050105090318040516051c180c050414010b1e0d020a0809010b130b04020702 69
    0x380b981d002075114564800501c4801d00342441210f1a100003007925121640d000c41980c660400205110b501503014003004c0380c10401e0110140d0494400103001c20346443d00d40c40010b080340d2469188042d030a4405040c20100aa40c0194510542d002000e21346150b5681203665081e40c03000d44400d0b0090000c001411902841e84000700c003800036503802003440d08242c00c1c01032606440f00c100911440d503000921104e5030700010a20b40c6000d0a0510307071440e115180c00c0700306620306048050134950030902085400d12012005002100702001103105100300201840b0844004448105800f100705207a40e00e254010710180040103059158403200640c0d80744100283d0308c007662203410f5038075006041400c10040c2c03a41c8001038002903a04001800760404ca00000300b0040c03040d50001c52000030111081ea0650070350580550f52200748540c0d901c0321404010080d07002b02c03540c4001840c448046100f030141800351801842009214062100e070b1315800500134041750b02c90f20742c070903130070099600181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 184698624 1250 184697374 184697389
    0x1602040207060e0c18060d02040b0613030318080309040e0307050d0806010e0402031308090d0b07020307020a080c03060a0c12150312080106020307030e0a08060f090d0905010903061a 80
    0x264403501c000704820783d4450700c8030301c0c0402e52500c0e10320420303001e030b103075420101811811a481401180caa0840ca00c0a0000c94000c01c00c15200c0d0384c0050000a1aa940036600400403044034440e40e6140c0321070041c03002c40003042d0307164000c55405800811100c0301c1c1b41303010b8000c01d14000c102c10591707113024643c0d510540b03132039141341044d40410042010003440350307080800183c0e22181170300c096103186001c0e00500f2186107140c2c0e00806840300424003040d180c40e0dc0f80d103409099400700079603140c0c0c01d0150700a0741c3c9411408040344107030942c40010030b44201c0841e04000c8408060b004003d035484901c810809804c84105600401c2020301959138550300030f0260511803610040f80461040c1141440c0d180c3d900d40c02284000c0c484c1400040050725400030803944d401e0f0f094588504104d010354001220540580d0028038907118a005000c60396072039942c401c1c001c1d00b800302282c0404d0703030900301078850200307912038a07011620714076003000030645681000c1c213581e4220b0001d14050300710f0000140c80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 184699874 1250 184698624 184698637
    0x304120c1502060a0e03090109091d030315030105130b0f0a0f180203070905090d0503040f02120d020105090c010e12150403120c0c0f080a1103030c0a080c030f0c16020402 75
    0x140d002c1001d006400b5582d101d80000020040702840c075044400001900d4a109c51040580441e51109140c0c8000715210104030720f22100000d980d980d040940a982e80e10710b504c02400d229518110215104c0c03070007620f0079500142c1c00203045200d0743d103254600c8481407009100502290303c8080c9841403907140e114040c084200d014030516001d006005062038000d240e004680214601024848424400600c5a07407a0b241c519200c0c0c0e69a41e2442e11141103146401c0c004e421584042c0010b9603800c02103920b8200b8003c960080000d5580c0d200c469030340300410074415002c260301d410a640d943c24072001031040100d20348103c4025518405034014140012102039000a403050240f400f8110103002c0c0c200300104501e024401100d05440d0310388021b001c0c00c401000d0f8100090306442080c06981c0c3c814034000301c4000e40c0d0b22840c24070444a80f5500c00c0480f00009040c017000103400000700c00c05e80c4d000e0340c0001c00d000030642e1008a1365440c0e600c0040c114903c1c02c680c08a00006960303500080c00c3c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 184701124 1250 184699874 184699877
    0x31e0501020c070806060603010b1b010605060a0503190501050f0d050f19020109090606050d020904150e0105030d170a0c091a190503040215031f09061706090304120c15 74
    0x3c0c0c2e94a031034082401c221020f40528400c46040004000d070300d40b54000e81300d80714419541c001aa913240e00c0c0700c038014062135000c990482c1010410068240d00400554411100e001501c06441070a04911080b68000d00805d6032002012406100904003040281c2909100d20216641a0082c51845141c4401c0b203001d0800444060481811568481e40c80700043c20018418050705040901c007902d18000c56130f400c0400303603000c22041c50607038558000c0440680380c85500540b10351a5a0070941d051300034007905020b0311805000c0004107101f2407080c1e00360b12401c49040b00310f03110840464060145c0344440410000e60b14070104028617200c19201100c13008030490350b51a038100300b640000b072050800321014850103200308070251f26082c0000040d0a100620941c0d00e030b6884000d411011088502c130f06500f00c60a4012a081c10181e0026081c0d0700501c01100d4443e0b4203010302a9a0740c41200e01c4581d81c0c005102c204165040000c15021142c811444201c9840e00c42c040a44010180b01c003800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 184702374 1250 184701124 184701133
    0x100815091618030b0613110d0e072c040609080406020f10050c0703031e090c08010b040213030821040f020916050a110102040f060c120305060901031e0501020c 70
    0x32001c1d008101c9000d0300d00003035180c2c11100d00d1900c9406581c00f00500c2140102109810784a41c14803d074842e46507040d1141440c2d07196015181040001d1140d001c100095200301140803a1708441003541141100e2908050342517200198412440c00300080c00490302240c0392102400002c401d0405080503000b558000e00c00320b940304a0305445c004444801d941e40b1842d2606102c101e802070340403144803503014200403d281005417048a00d144440c1c071005860f41c0744c44040010002d000070100c00301c422600007030081c1880d40c0204412446038103400030306a02200810000500301c0c0300a42440b01c8400364507501c070a5825144a22090219411a500e002d080100760452800c0171940303030032542e143d0791041d640c0c1c003c3c40090f06a2140300d91180c240681e914241d0420720f400d40444000e003486a1128140680c1c4a80140440c0122181250001e031000e62003884240f10f441000c0c460500106045442d910b55196040701e40f80395044240801e90a024043c08074009000901c8040c0f418001403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 184703624 1250 184702374 184702411
    0x160204020c0316150c1b11030105010b0408070815071b06020f0301180905060a0207060612050a0507060203160605150a080601060f0c020a06031107050a0602090f04090210081509 78
    0x180c2d820310096180e58072280b8083c00c5d00c0c0341550000b80710741507850101e6942c00d81c1c0e1550500c024405011107070150705608020000c03032030b0100704029008803040c860448045c1c644134800b4585841030504c0401640d81400b0020312554030444507030140c04003244400005900c079440d2007090307902c5485189002d6900200400500300700009800710140c1e860341c00c10140426035116922403c0160603818801d401007812000c2c440d155110304010a41640074072400c1d121460120388480c4070080a036110b00404500056460021045680f600c1070034480f40305000083c0e0f1010000c04002d804040410140c0500144030303142c600c440301c05000d0060007400158503100c8018001521546a4420824801e0104005807030b040a25015180d581c20089a07420300031040ca010b500a00c000038101d445950340c0c141c2842002d90080a11400c02e446664416a80c030043c0426100901d0000350419140345000c011903103c2c0301044e8100c85005a100b6004141100140c0301d01802e5038103220200c0704e42241e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 184704874 1250 184703624 184703633
    0x1090504030e0f0d110f03100f0b0d0506061012020307020c031603020d0b060301091211060c03040b1603060510031a010305061011030702090702160515160204020c0316 74
    0x914100b5004a80340d441d03054601000c6031540356801e00080c0040300e201d81c54402a42c2d40395522140c2d1901508803484840590031035805403583c01c59994031546000c01c80e0000303062686e880301d0660b800000920464880800340000e40c00803110040030030500c0340706034054601600096000c1c0b5944c2c4d004141003c0032404060409500328003540e40041d400c0010030040e160800000c2030786401c00304500c5580c1d60392000c00d02400b41864000c2c556044095894030042e00300180801500c240021241140d6070042e002d000740c8415070300541049030303610000b10310b101c58500080c400c440d1890085100d03982ca101007095220140c0300d00003c01d4650704014500600c02d1070240c8815001d04e01031200f070500d02c2c081514407131030a6021003048840d0786009841441042104c42440d8090160144c47c030300300e6002034540c0310724a0480346440c42a40005004d00e80130726212700c0d004031080e246141c5508518040d038003000c03440b002c0760820740030b0000c8078030381c207090002d010650044d00d100b081030411440e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 184706124 1250 184704874 184704887
    0x91e030114090a0303090c0509100806010501021b09040204110f070b09010203040c05100221030609070f0203090418060c02010b0306070207060503010924150201180b1506120109050403 81
    0x10024012074162040090321040003402020007601402d001914000a0404031031031701003600400d4000002100b0b206400e428a00751000311060b91064550710398a072001242c40e65248118284a080180808529454484249900b0901c01400052401e00603c25599140c1000300346042c0c10402040403000d1003502454281c0c0280240e008501e540b600365107680503010b660044a0203040000e490a43c414001c01191591441050380c00102413007142600149034012100315014481c3d14010512060082407504141c0c10541c0203141010341c0e4000b44002001c04450f220780000500000c0004111288540010303210b5950020a401e80c0c0c590a0502e000806015141154030000c001c008441d0302c4800d6a06542075a075003c54154544030300c8403155410424020211140d206002401c0311030341c44103400c941c410741c0091044003a41000c1d10700c08502020050001980c0c3d400248004c3c444070501c090385500105014140a4420820070655800b41c100c18000c41e96035060100385a0003c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 184707374 1250 184706124 184706141
    0x51c0507030302061006030b031e0f010f060f06030207031202210f0a060b040308030103150b03030c0604030801060c0f08090301110304141606170402010201020903030c0703170304050604031103091e0301 89
    0x18217008c903020042c04265180340600d4210303260800140783e0301070100240002c0034450b161900070f006603d5801304000081c0818419042c440c0c5038010009802c5000b8000c0d94401a015200d000e039408400c03c0300400b03036001504411076085900e000303058480d1181905801148040c203012035500d0103136403880454503e6048102a524107000420000340fa290841e41501e500c50780200026541c00c1c0d0303013005416031b0030841e0742c075010105003840c500000007201e91046000b5070b5102156640c1d400180c034072544148c005042c51040304886404690600c00401886c2c0001e000091401c03001100800641c100f594211401070f001815804628020030501d10300d01943c0b00c2c83d800e0145080805010907290039402e1a02d46514030008056a0007135054034100580542540e648261032240a521814140402c9540c03440327806020101540780400c0c0c910950f8404002c00f41c0b0b86071920255051040140b44041c584004c2201250a8481c00c481c41800300c5c0803100d445518016400b01400d682000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 184708624 1250 184707374 184707377
    0x305060f04060308031f03080c1f050702030904020c0a0611040806010605030f0105040b03070515040501140a0206042d080d140609011421070303020d030902010207051c0507030302061006 82
    0x960148007003412001204d1b008001c1140c0d6106440500307800101401d840d038406040507201140d10503080402148030030b0300c0c1d410f00c0f000341d03507145030607095804454080c1c907010010b03402849610082c1c14594000c1c402c1c070840904907000c03001707a5603411003a10505507031032420681c0400e00700000c41703040007114050300d40c07400d1950035458041042454580144a01c500c501c3e112040000c160b103007445804054603004d811048014200c049440003684103209a03400500726044130410f600c6c51805a0706101c6466018102d29111611034002c610610480c05903000c403408030b048940100c000e011107689100740b8400e52229185074401c0d04440020b03155090000404080080d2680c480c501ea50641c0c4450034000c14208030340b0041031203496810010120216450b501c2c1c07041400000b118400c5a101c6e031b00b1221030b451190411000c2c1c8040c400003e0150380a16400d02c0b1038507090850b921242c0090382d0745402001113842e81d9140200e00d50058015800c50310500246000e042e4107403020b05041d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 184709874 1250 184708624 184708631
    0x1b012708131e080622060b040903030203100b0c3409062d031410090605011703040623071a011e08060406020c0705031b1305151306050607030305060f04 67
    0x401d1804c401d174010305420880191345401d0740c1e41004482d901481885001400402c0900e0540c6006002540180c0c0c140000040d110300005044400300c04460600c00c699015005040301600051026150306003034014402e6a94500b082d1520600c0440004040780d100c042806450250040400048070709a040c441c01c400c083c2003195141c2c40e001500b140c2d07200d00e100c540541c80724281d9041000900000c404e5a081c09214000d01880f9003041d4182d6014100d00c400110341d441226a50344a14428640401c12544019100c1c1001c0b188402c4c02c2d04004645c18503100c0160b407011110310044d51030301c4002c005400140082e880940d003440d00c5e0142541d900409a0400140715503520000b4801404580c00081c1031700c218500b88032070130040c20064100d41c20302d400014041c00210b030702c3d8206030140c5d0b0030356100075501d80c0501480d8050000d410410304024445000e1000c281140541851724645031040001e40d6103c0c00001c1c030040b4001d035000585414080b08020355007555040c0e16100324103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 184711124 1250 184709874 184709881
    0x90c07060b0a14130204050409240519050702030405090901020a08010902161506080f0a1202010603030806010c140609070501030f050408090d0f0f06021b012708131e0806 75
    0x40806060010401140c24038501c5110b8030043c0041d2086d0b410454125042a081c0f0302081854941040b5003170f14030b03540c0764001d8003524800b8200e4400f19841e6081c801140c4c4e0364000a0010f07440f050b0004e2542c415245019241d42c04039503007080513039042c55641c2d4005000100035502030842070141905010551401c0700d22404118003424000c2c0181c00d00403441c50400700c1030004c0e072100e0018540841500ca0001c00003003295101c0507181002c0e80c0c20140000700c00031035841031240d50700f5170398991208109a19404011101e50001d1041207034105d0100004110a901c10011103100344103800050983c50704000006064034a5201d03980105400d0505010000f02c440703041e9500f10b0000c0c1d4400b0400300701ca00345000c901354561390207400f8600c072802c0d00e42442a29002450b01c000b0a105005000d00081d079424221800822005400b001c40d0f003c060711805098a0341c0280e0b03014810700d50424018100303014040700303198000d8415124141d4100901454a07010301c000b0200803025003403030324 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 184712230 1106 184711124 184711139
    0x50108070504030209010b0307030e01050a0c020d09080d110304030b012c0f150f03070e07090611030403030f03110d0e060c040302030a0f020a0302090c07060b0a 71
    0x1010180000c825600503821182241c1d800341007400503a1a11414004941020705101e0405450b800702c004000390900030a070042c88041c0340001d24507041400130b80f400c0307002c1c180c08081c4500110200130404000c88c620044110a0810a0070000010b85041c19882282c20050040d500c5200200351000030089107010004265a41c003199072004e40454100c0600315001e41000008200080f0003120802c1000302d0628054004029240c400000904200c11900321a28640000d010800e4171030b4448505402481c607400d090716584868411592030344100d000103018412072040000080384298080314001c000582c1c1c00f6201c10703420400b2800361510f6440c2e1714452003030324089103048142200b02c074200c0e5801402405400a00e95813404100407912041c1c7c0d00c455181c20010140e140c0465441c881e90166200079961b000034074200080342d44074a41d42e4020054502c050001c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 184532374 184712230 := by
  have h0 := BRFrame.cov_init 184532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 184532374 ≤ n) (h2 : n < 184712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
