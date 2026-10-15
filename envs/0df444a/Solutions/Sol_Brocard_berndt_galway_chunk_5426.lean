-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:49:48.849411+00:00
-- url     : https://prove2.me/submissions/2cf85058-095d-4ec7-96f3-ae080ed59622

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975719424 ≤ n < 975899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975720674 1250 975719424 975719429
    0x601210c0902031614220f03050604030905041815180501021e0703080105010e0d060903031d03091c060b10080415050925150e0f040501030b0a0203040c0e15030601 72
    0x38017560003c00c07000410b40604072644540418003141414210003100c2c0c40a00c1a42d01c0f10702c507020100008020003030302192080c041c600a523605413915840300c082004452a030060809106c1c0481200710008000b642080d08400800700002500048055000c00b503965040c0d044980c0d940c0015604403190036961440c250361068100c05060454a40d4058800304060203200c0c18030040d9100c409440c1e961907200403000341c0c054002d110060f130a10b0013402521240c514803400e8810390001e440c0d0600004240d40214400402904195030162704002002d01c848200303940040e11307034101e0006510b9545235004109201d9640c00340f00d14043c00c1c00254594100d001307455090402050206403400015400d00b820244021074000500b0801e4004051074942c1c0304c907021601c004502c14404e600700441d480c0000d004d035009403410911004010440750f0034000141040d049101240c2c00f03032a02c0d4007656103e0b106514004a43d5140e0b0240400400c04441d590620001c0c034902c0001801e0500250b1300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975721924 1250 975720674 975720677
    0xb0403090b0403151a0a12050c0d0b0f073002092d0a030f0b06131518060b0f0f091804140a0b06060a0504090603111206090601210c09020316 62
    0x45e08541c0100168403114030b03120307030500c1c20800301e4140c0501809000030145000028642a205030641c0f40641c0000c000321034040b0621039007400601c40d240a20304504851020320350424221030000b08000800000315820042d1980c01d100441481c1c0315108011030b8407148403070744032100613412103200a06982005090007030310781e15801c00020304880d50151201303034003458400d0180e40e02404219140c80c24414150b54906114038143c841d58554040002e075024029121105c10410401c1810f46200340305c0c240703002e50b0030480200002480d034050604800581c10440c5417074074020008826030a03450b003807240540354034180002c0000d06d05140c07002903041809400356401da52106040c80c2c0340244050300a840c00200d02c10210701c02d03c1224060a100242000801d459040050040011a00490003808a604540c6490704002038140c8544a2000102056820040200c0e040707080412103085050300620924000341e00c0d1201100079096003900141c40c1c1c0b61031041d132220f191402003681b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975723174 1250 975721924 975721961
    0x3141f0b07080906070302160e01090f1a0913050307050105070e040b01021b040207020303040b04150504080d0e1302030901200423030a020d030c121103070b0403090b040315 76
    0x80003460b080d056900e000390860701d40d5119203150505a0500d0b80001548143c4444004007040186400e0b010a0586d19903c070304219080c01d003d000c80448003840f0b11141c106041811001c058a86150010344c08881807010500c0490030380c2d0f0340d501c1c41c2c00900d01140c00381d454004014206900241c541c07000c6000311010b010a4403000c0010352141c000304001e040c4030031140caa00900d520380360100d5001320b038040e040701d9071541d640118010301c6d001800740c0340c3d10294551a8000c3c480c8148191020760702032902502c1d84c00f00f00702040d6a440c0b072150f1010780046210110310198002072001d1743c0b003280c000001049882c0e040c9200480c40e01024020400d2540510080c842d1044460310340d8510383c000303100c2c1036880c0311100020349801d00603940258008505210a02050b900107c0f5410703080c810324941c100c0044420040d07950442500c0d0207409940b05203d40004136000340c03400d0343c000b40207051001446403038007241c074031685c01a081566020a071002c0c8a9001c080351203020601100090300d030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975724424 1250 975723174 975723187
    0xf08010302130f1508161a03010e06032a120d05042306070503040f050d08070609380a020f071506090f1d0a0305160303141f0b 56
    0x71403100b540310b90070a285076504031580d524692a4404444c540445001c1c030303942c40d03440c00000d580d98506550f00d0788601000c60b0014501070380c070f101a41d00b020210480c0e0705585c20400200d44504c00280311603490301c41c070103a0030f0b05444400e00d0b603540d0704600011048500e240e0030601030075180030040004540d0003c802d8211040d4403009880603030f40c156100d0140004142040d0120010440c03003039501c000d00140c50320400c000000100111364141c030318004600d40d914108250700380e024502801c1844100007110001c0c0e13041d40241041842008400b940028007420788e145643d06800b50031a070f20140061004240e024400c45a004405120540c98035001801ca071103603025058004140405003c2e00309804c441c503402c10310103402d0300542004603900785004040034109012884c051520109400070342107401003900444c0f01c0d01600c03500e1511050700030b98030404103000030607800c1599460b0000d806d1844003800350300510300400b212542e40c5200004401c141540c7d8400c00079004108440d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975725674 1250 975724424 975724429
    0x110406030c06020615090114011403011d0a0c0512070507050706200f0d0e060d020d02030601090512060712022505331909050d020708030f030f130b0903030402010f08010302 76
    0x121815a23640300302e5240d424542c0381c01a5821a04040002c068040100c008989211503280050f035003c000000980c60780c640c801c0000440c3c510040f5680000c1e001c006860b05103d58004154003c1580e20f48a450803100340c50701424299240c008a0001d483c0040e85d4113401c6600303c03803101c001110405842038140001c14a5550040d41e9642c03001c1c01210b07144480566035040541c4c540818001d01599904404a030034402540215400e90200f0991000400c480c20050054143c000c0f11800420320ba403900d01c400d981c501440e511a0740c0080e020000015004112442c03031801010022200720100315a1404d2030828401d4000c0d00c1500391500080c9030440780c4281d0324802030401402d80209502c030b5400314924640300e80481c40981e8100070369001009000901d0560042c45a4283d558454807513072016120300c5101142001c00c4428004103200b8051445c80719080300000d00c00c0c80340ca032001d0342d5121811070111901e95140c0c2000c010802503581040046d994840c081c03510810b10b41c1513600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975726924 1250 975725674 975725689
    0x15060a0b040b043c05011403010303050d0f1506022b08070e210309010f08060609042307050c0c220518370c050d110406030c06020615 59
    0xd500644941d040405004041c4d5007881508800c0c0103003100c807400c079500c5504034055040d01c00c442c0040c014003030903064010048207807410b03a0307030680e61280b9000711a0b030320002074001320381007200c0e460340c52140b0081d0000c411005402801281c02800450b070008411654004010a003680340c1801c1021001c21550301030170a80e03110916060140e0f26050000108500c25103100d02890642458168650340304000806049800d80076a607044034007101c1407088890f101e00351002d5820040174406003c0501c2d1580250040b11003040b050070b0254900202420805410b54403c804a07100056031820700c40180109401144180c1d0342d0249840c1342403003c81982e400740039000d0069911004078460040741104801c03c520b5035012111042c2540b0158280e034600b52101e582184050301d81610440401100001c945812240e408466807615041c0b00c150842a02c0c201e4a041e01d494100c9003950303c91003844041c5016400044050741000b20181c0b030a40c02402030128215600d1000405545925 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975728174 1250 975726924 975726929
    0x2010315261e0d14120a090b0a0924090803010608070f020115092301060806010e030c100f050f04060315120b06060c0c060714071205061f0815060a0b040b04 69
    0x260007482c4901285280713890b80604228000682c24000c10700078910303082d4000030203540c002c3d0907110084c0c45442c0e00340c00f10303800782c10300400040c0e40040d02c1c01821184018820950b5000001154a0760b10ba1366038021548260429000b10f541102840a00f40d8000b10011031148640000c202105c41c41035140c1c040111885100b4600c5c1d1648406100110355681d100400780b5200228005540c580001170440c420803540300c2c8c00241c03401c0460880303160000c2d50442c0301d1800b81060170903090310001110740310f030359100b40350600c101040050b4207420340700002c200038001c40d41d000402c0d40200030450b01c0603402d030b4007450900e40f0b0190180301044171840000c1e003080d02102c00d203595504400300c060a0074104210a0350100010596500380710b8602d0400072400d904009441c84252035000b000a1002c0c486009080c6502203400154020301c401e0409001d104104414000313a903070b4907062490220781c00e0500520241e40c2d010700c2174a00b808020b07040542850380509082c1800c244c401a042c2c0140d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975729424 1250 975728174 975728177
    0xe090a05060c1b030d09021302041a07140703050708011a060307030f0b100804050105010b0a0f08100b0c030a020f1b0d06020d05130c14010c02010315261e0d 69
    0x7907030044003814000484500010b60f01075a8a500440200303100a01e8443d2040e400707000c000000102241040c400c403819521203030550f00c0c1c00c00e00800e014159400c0440101e40206101c0d0001d0340d90001080ae00703004500c140001c28050b820409610b0a40b0307080480303618042c00c69010f80490790b441c482525401021303883c00203aa003201c0d003e010050008800e8481d0003003203c0105800c80e40c1d1200f000c40c45140200d000344600e9980c0c84281200f403090f944132030700050b04030891520307049c41a5410790304504001ca40200c100d03181d800da5485035201e49400c04880d03000080d075100300d6806004160301c0e81c260744043d0a03020310083d042544071105d41d020354811007120f0401c1042001e1581030301d8900c403400c4001c011034039042d5258132144540d058199070005091100040b4040062a8003888c0d01042c0d45040b20803005500550250848a82c190300380103040d4408115001d00144a01900c2000250f801803621404880344c140345d88080702d4204140300143d101c40b550000a0205851080c0c6e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975730674 1250 975729424 975729427
    0x160509070f030908030a021b031305090a14010e180d05030703020d0e010e0f1204030f0809040f0e03031509040203210c12030f0f0f0402100c05160e090a05060c 70
    0x7038050480082180280041c001c2c4404000e20200100c15405850211548001000301000e000c400aa4900400c00102500004202c1c240414145041c0366904165110000b28441507030051b20301e0440b400360000d0460248910802c14840f00c03144104606000020140c42d00d0038004070000c10510000340a41b0501d03400041c0c000345021b660b4804a940c04000e4020031840012250b055240c20341202400350b14800c40440505040783c190445046a5000003962a020711a0342c81d034031290850b100d196072060780c808520307107445010b00992445035041300240d42d036807504c1207010fa0040034215096000d0458603041000617100040c504503941030900c540740c8004200550005544904101c1841c180186800e1240c02c844040c040c0d401000c90a1580c7c6c40b5945600d14010172881c01c45040191107810004240542803c0c80f41d081d060f82c0302d20340240d4294440e12a2450b0100408281907042d5400e0b20401c5200080151541c1200d50743e8003504103600180c4415541d46006046032401c0ca00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975731924 1250 975730674 975730697
    0x110906010914010c0f05030a2604030f0e0907080a051315020306041104080106081c171009060b09090601032f040e07020105190209060a08130f050d0216050907 70
    0x203084d81d144429800703240302c0d1010030940b41040d00c942240017000e01090101d2a0340c00c03407480702c94507445900c14035142c0c0c0b400b030b540c1e40c1c40444860600502d00014812000c4131032246484602d0214030807003850703c45a12900f0304d841000c0856100030b01444102d060f1a0000c0c0009814004038683c405c45c1010168503905d80747d00190042100c2c20a001900800140014010340117400010441d0306800c25207c1d4407100450401a8900040701e41c40003814203040e00d105010320403400d503080310100030300722005a1524003000484187e50004613152400cc6250320061a0542109074000b20030718040c4022000c0004600d00e1604800801c815062000345041a083c60b65040d900200f42e214001406030038240c2020380244025641c00000021841c03200300d040380715000700d400082e4054082468203034158812951907c01400c032101d80c03040346417041c02194180e1280302e41140250007a203903504401c00080e1401d45801140042c900f40300108200b00d035141c4002690001d91420490403400303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975733174 1250 975731924 975731927
    0x5030a021201060902190e0f0d03030f0e030408011d010612080705011e0603030e1009090e030c071508070305010312030f0b0d0c2d06050f12090a11090601091401 71
    0x20864206034442c92000c25611025200b201000021b62100d0b12602040c1c810002400084450f400030a6002240351030540c001902c2544a00c02414402c42c0004134076051010301415540950300103403090f9121068440808100380d04108039403001c2000300600d038580094414501c070780c3c0c1c1c00580415804106041800000e400c045500740c1841c29000080c14042990710050640b40420b500269103409100c030103003090001004161655110300300f2180c40e001044018016015850043c0d01090041108440003080322001601d14035524082c4d42c0b40e0501c008140d594002d15a40c100350174080101301049540f0011969611240b5011682440801400024006111101d0b4010080080070300c14001035071106c00035900d801000800002450114156440480c408540b900981440411030035000308014005070746004c10301d50800c40e5081000f501c0d500c0c00c5440b01c1d0b41c6d070042941281003000c1c804035031b50741a0302152480001d00708400000c098020a00a036001c184cbc007420f2003102a07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975734424 1250 975733174 975733181
    0xd1109030c010f022509061401080411040b06070b090d0c0804090510210210021501120f050f0609010f06031524090b1806031c0507080301060f02070503010605030a021201 75
    0x449030345c54280ca0042141700407181c1d01c60911503e02c80d03500e0075030081003040b2000460a04c0680503514509507468a1700c42101401140c88030540c03056480031000200e898020107010f9090042081300d0291925002c0c403410020020700c080c00b013204424148002400c00300035201544d01f50000014140e0301d08848071900c104d1900042c0d5030400c8204c0141c420000035942c11a411300c00d40720602010078401c0e00360380d03541c9803c00110054184038018010440c91104410826004448140340e400c2c0546400d8241810340c54a511290850000c00c94914024050317041c0007005e195040010380e281d031300c40b203030003121990082404a03250071440c5a031610341348929450001d4064110321013a41c5d00070344401461080002d6004400340c054034500810a4001d003403240c1c4000c0e0161801c20079504125017001220758a85081c0b0805006460114190001450103041c2e540c807a070701c3d030340804c010285c50000254410340c4280c2c1460400d008a80700800d5801d000b690581d07070b1214801207003880a014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975735674 1250 975734424 975734443
    0x507050309060d02132909031c0c110307062703120207141c021323060f10091e120b0f15091303030e0a03050d1109030c010f02 56
    0x6100407504403010421039008000c4001405410382c0311554036031401c06c015000ea07107609103240c1003030300400304c9100e41c3e401000b444600405403080590500c02c12000c1c1090791500a0020741404001c03410030540101450320840202c0c010a0400d160541c020500255600c08800c2c0c00f44031030402400c0c21440070102c0140d42d02545000c0d580030340b024025669241e612501703c9850304141c0d89103041c24440c1e6807200384002d04014185003030058083c05501c0a24850201210b99600c10406036044003201c0d0349500d1070307088192003041c20a80200524006444042e502c1003e2071941c031180c140c2c0051844007110652030440145078500440310f1a8003205912040700b060344070750301c0400c000117084458803941c8015901c544030744402100305440c990038110550850304400c085400c075079206c030221425610a00d800f29101ea180024182001c090000072408180081500310b182d01c0f450140f0780e440e4050030305150400c00040b0000703598401013104241800703846c20031400c00e14401c2c00251034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975736924 1250 975735674 975735679
    0x1014030420030f0d0f0306030c03030c15090605060915030c0f03072c0903130e2701050105030d03090c0e0417390d1101150b0d0c0804050601060507050309 68
    0x1a10003c0040a40c540400c080001d001411092000c1c103201c2c0244140f0080d2071701712101d0070010f8155034041c1d810b405000e40c10348a02d48e402a44424600c1240501c8001d030344140c0e004540d40c02c008090080c103034000351190810150a25000030543c078009030051003480c3c00c40b0844000350002000ca8101242038210b00340101c1181d179200070940c0c0e008620b131000b0070702560035140ca07510303841c11549030700400c0c1d034128004000c142d041240350090908260044660030b200e2400300c15040590b52004508032440f15281d4403030740108102d14091001180f800c0b41d605040c004005280d0b07503505403044a004080c40c1e40c040c030300411700b40105078204802c6040b80c0d28403965a0b201c89e84118800840070035660201c0800506400c15403120101d0969401a111004140c9180840000c0e240b03100f2a91154405640c2d41900b00c41212090140400030700341c1451540c0d039500d09818480968040780102d4082c000c0300828800041e80008001d0b0444030286002070b25901030386065415813003004462035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975738174 1250 975736924 975736933
    0x12091104020f0405030d0503040c090213090603050f100e0c06030a0b0d050f0706050720040b0306100617160503090c03010911011d01050a030c1110060302101403042003 74
    0xb40c1680001000388252241142100c0f01c044a071102100c0700d100444000302060407807102005140754503000f900c4962915810000510b07180c3d201e480445a0341d074400d45050b400101c12441880040c802440b150b030303a91800740704080301d10441d19503e43c40c0840c05401194004000740142200b0b0703006030386141000b00300f00c4145100382401c99840140703010041341400340c2040051420b00034802c40d6510759020301440c8041110281c0c04103000703038074040150031036100c14212406580500403e841b0f40594601048668182400202100321a1084880da44041e00502401c000e04c030703582c104200198584240e0369501e40708070508011110041b241c056003401c0e045000c204200d40010b0a000d42a42c412002164400c90110a00740d00381c501e902095081000c140c031580b081c0c0200e0250032590130080d480b0141030980f40c0c508038020030625559a501c0c01c090003149007200704244485c00c82d25121340003600300314030150307284800392006280d20072044000080d844180f0004c41600700c000c00b503c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975739424 1250 975738174 975738187
    0x1315112d030a09120e0f040903051b03030a0e070b12041b060c0209090d09261c0224010b03101205100b0a030f021912050c010905101209110402 63
    0x80d01034800081d04035580e141210101c4d10b413502c00c0c83c54003510900200a41c0d607100e405018480200030400f029010090108960382c461541d19040e00038091045001b50ba9a142400e82401101e1100c002c0b1749958111004c20400440c6001c01c0d2420a618401500140e484074540404609a0302c0c0c100031445404d0100085c074660054003043c0d916000b5a82d1280940d00c1c140c10b507460340224003018020400c088014888590081000700c43c40e5003a10f20b0300300440a61161f180341000c0842c0440c0802c42401e014220b5942c1840640b14108610714100e40b40815642486110801405005410007001c0005100b04040074101c000401c000300c921213580c11103041c40ea0312003c0c1c031200000d03206e007818200b80d0725003407924010341200d400c03e100c182440c940c0d600b002007528802040c401c000c0504c4a0105495000010200300780388500c00030008404c00c81c0014290401e650b104a100320b0000c08880c007915003207280300c01020032203000044d22400c1407a1100d03686160120f140e801600c0807601c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975740674 1250 975739424 975739441
    0x9032509060501051c0903120609090507060206070816140d05071d031005090c0301051e0109140403030e0115140a1202010c1e0b1315112d03 62
    0x1400340e5210000c284109500d6000541e441c0c0b1a41d81d803d518070620441c1210011540d601000040340f092a1050881620b800c0e1041660000d40116001541d82c0030401d040107800c119120082643d400941036070f10340b0f104013901c0303031030014011051540b000800340b020707d01c60030030300000048240c42c040e25904800c0125004100c00c441c114045106103000902d05000350b1240d40100c1d9004004019400b50300d041c04000d08400340c02406e0300d05c200319110215582c20b0103075901c242004120200394800710314030a806244103074031035298076191401804545204080f03072a4041d4041c240401c0c0302d81211078490051a086141100c01110f584001c111035118400c000f03083d42088401d80a884c2c0c17a0a070419108400b144000c1c081036811881e84002048132144022040e4824540d0812440949510020ba4002c40d5100b80800100910004024504089100704103168008001d010f03094405a0320034410924040300200b100440e0b03258108100c03880702007aa01c005580341c0c880c20a403c0703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975741924 1250 975740674 975740743
    0x6120a0f080405030f070311133207110c0d020d060f0b040e070f030f050f10020d05010806100b130807170c060307050409020a12020a2c090c0903 64
    0xf040c0c8070740074002071440802000201c01c1705a0f908035110095141c0c0c0c500810050fa61070741c40464134141c0740c0c0c0c60050000701000e40c00e0321100742846480080b001c2c0084081c2d28a000170444000c1c46030700803d0828110000481001c3ea060a94913135000205500016101c0071101070001e00c8141040303c01052182d40e0f070046106103009403414020090504821620384c9040c0c0034845015640500030004100d00700d02003110359020703609643e055680d0420031800e0548040e25022141e4000880035401651440786900510a80c405080a0f0604400700304562030f0b03d200300217481c640419211400030390170700600700810600003200c0046a50b04ad4621214040d641c0f01c2d450780c0945014181d05080c90000c4078031410040da545860a818007582500a4001c50130701c03c10001d042e41003e03100351080c40104854406502c0341482d00c0924041e8006020311001405240188020580d00a0301d4203039629070891480e00c000c43c0c0700c207503910200b86010034064100d03002c40f100d0034120302026a20038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975743174 1250 975741924 975741929
    0x6040f050a2903190f0b1014091509060a050322120806040f15050301150605031603270516180513120f12021306050705010b13020a230306120a0f0804 66
    0xd80048a40e402c600b0107488a503500750540062300c4c8100090b900724030f40b40300400404011212014244011000070402d1030300714040ca60041100041800441c1c48000640d40900d0f40318030700060800c90316a00c411014594020794020b0103030140c0810360b15a2990080c4081d03200f0443d082001203d008e2084080d0a154420706010754a00460081b092540150060541d0700c95125140341d03450340c0c10865a400c0d43c0c0c100150400d59110110b06a00c18206003403424100c40b6400d812030403226040c001d00b4800c4200e0441c040c4111342ca410001640d802900031031150304480006030a81c0c40501c82e0700348041450008080d0742100003420302c0c1c40d800460300f581030822642c9100440001c0010341c000c078818001c80b1020f905000204200b4948a4402003402a10510001c100410388902098024030105143c0c1c10a60b004076222003007540c4819036000c0c085030083c242c001000460a410000d11001c0c011600540324000b555803071180404c030692016510684e05c142a100ca814221400d03081030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975744424 1250 975743174 975743179
    0x8040c15170a02040e130303090b0f160206040c060e030f0304090920010e10050c0604081804090f021c0f0309032a0902030603010b06040f050a2903190f0b 68
    0x4001007041480c141c400c4c0d030141d803000b1062800b10f440324100305000f0002000300b2410943c40380c17003500000d424501d10b20300544110035140502d0525403091551800b0b05c02e00c50701107600180401020802690391a800c882c15814500050760700c0d000800d0400903204000d840034880006e00180d5071450ba030104144601480c1240448198043c13864916224080d465000624100b183c04240c50114044400d01d1201d0800b035250036841311003103003050b0048500f0b41e40c4007008103140310000759030803900351000001c0341c2c20000282e0300d40d69028080c511b6000a40103100c0c00c0d0f405035501d05907040500d01705801000300c0c3d0010040b841c2c0100f0301603090004480341141c4071000031248501c0110040306034207148500501c0b90038409210000e4200a00050703043d900c8183e49005600c40b900184050075001c01c1c8602c200e0308007814001030506030b901640c0d041030000c41d1000b000452009035101e9444400764a42c3e42e481d00b20b80d2030344a4a8050500b03661038a02104181c10045641c08541c548009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975745674 1250 975744424 975744467
    0x20903070b22080f070608060a081519062d030c0e040c051c0f0203071a041a0307050412031205090d030608012f040308040806150301060605090108040c15 68
    0x3c80e88829200d0101c03c0081c1c0665020200903c54a40134415480c2d100382c0c090040741d4000d948600d41032402540c031450100b40e010790030500100310719010180100f00401c18003801120b1030100d840211041003c80c0000b00401415814864250040807000950300440155500b90301d9110110015100351421140b0719410a40007401c2d06202c000c0713140045003110720b0000c104642d1640071001c499400304982c14007075014041034012007103402c041c04040c80b8a01a442d02c3c2000045111300f1407071600381e4440d000600811614680c0001103c05503198062607050100103494180e8084004400d1040268141410081c418000295801c000c50050754144552551141d9145c00c0300c103c5520000e0200c0d55603080b800d103044440080b409200c0b42000c5500d05640c1b500d4050181c3c1040d000b050040e00040c05105002e00c03440200449842c0c120000c0050b00d00d0048058550722441c0c8040e414860054002000d011a11035034400400e400300e5240201000182c004003400711084e4407000c1d1a51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975746924 1250 975745674 975745679
    0x70308033102060703030209030c06030a09031206080307030c150c0f18061e120c02030301030302120301051003050a0f0c0302031b0c07050108060d06090f020f06071104020903070b22 80
    0x10901018501c60740c000e010b8038a040741d203407801c401950191144607010b105010314051641c8a400c02140714130800c0b1000210b051041c6002000104080b2a034030300700b400c0c004180520040441203d0900d0380c94203101c039195070b131450244004490b4a0f400c92503540751691001d0f100350030070030402c2429410390303a42c111080401500d40445000f0b024040010303074003405101d050f50355208101441306a03410102109a901400302040d148240e403104010707000032004104040c0c040040d0000b400030312903920706540c101008184807204814070141055104c2011030034029032984504a01d00780c00009000703603c00715070060069413046e10090550307000c88a14601000c0d203038090303034045c58591001d0405985081e00444010034098000782d40300ca41000301100013446413054004682c1b103509054000121070040080c0d407102c050341c071030041c0300400500000504071a1600c41d01c071700807500181c465000c007000c40e11b01041074111941c08000014041c000f000c0303078450000b1910987c2d540f41036903074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975748174 1250 975746924 975747001
    0x312020303190f0b0301020304230a1a27070608150a03080a051c0e0c04020c06070f050405190e01090603020d0f02010e04020d091505100308070507030803 68
    0x4800c45102c40860311005070b4441892441c0c02c003100303003914800046800425000001e0032a88180d0303085845c203005c00c018008816140e43c91800354880b800282540d800780c1d27101d0b0710310800110b11014080d039245001804401a082074203890800100c00c0800402091800a40c0d0300560f008800c0401c5410000031b0800520305041b048e100805040038018034510f54179840c0c9a003011000009010341441440b201006074001e02c1d000e02c0c2c9039040400c17941903100620341851030140303086010b84c1c010004421108c40c001051030b0081c10340c2c601035060309103901c0700301c0307050181da005950b0040c1400d2201021740986150b0304280c4511081c5030301a660394003611012a507452100a4200240c903028102003006860356000141c01814412040600000001d049038009a500060a81d4614900d000d002c11401070b6040c242686c4020046802d2628061400002c42c0c44000c025120005510003000300604c14a001142c5c0b00f105075882e03060140945881031403a2a60042d00061541140c45c010f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975749424 1250 975748174 975748177
    0x81b0601060203070615051207090f0921090e090c0901051009060f030b06070b0a1508060610021501080601061202190e01111c1107030812060d0b1003120203 69
    0x761800d8005601e400410341d01d080203000340d0380c0528440080090002401d89400c49517104c82080351014140460500e0f00c50800ca4a0202e0340801152400171980001000701c000715049400d80c0b282e07118001d15080c0d0480fa4041a504a24548600c8400340326176500002441c10000c0c0040b1041c1c1c00c81d0307032140e0034466041d038a801d80034006041c1100400c0201d00401800908022314540407600c0e5641e200442d02c59030001c1c104030b44184000042100800a511509400c80e04000a40d402107140824407a070b6a80040d0545126913007911340f442810b8000c100b044498074842c0d403011b802c1d682d1640d05a403a514244243c41c0410342d8042d840c00114031500c01c0700d802d604102c0d14a003904840e0141203503010400d040050510861294140700349608100008401c4004640c4401d06110b0042c0108070f101c500c06818803d611001e41480080c241c1004c1c5e8814650540918403d907440030001008980b8220019203484064802d00558103140140641901c2c024240360740513040340300049a59 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975750674 1250 975749424 975749429
    0x9050d120b041413050712050604030e010804170d021c1a1915090b0739050603061c03020606011803260f0c0f1002030103030f18090603081b0601 64
    0x83c45554030019151a5041d030b000c034109800f41d000c85400540301c18524107200342d0314400f43d50360f0380541d08000070198000d0308801c0040083c80c000e241402c0640d5081d0026880c0817140031424808609009000300b02d5040c8c0e600410f5000420120700705580401e0010140c0b40c0720300c405094031060a00c1c6506000c0e003000451050501e111503a1032801048001d104400b01a0208100aa40c030008000b00d80c0c2000d080c0b200e0091070305441d122290b468524410703041b0170b8105040c964004500c040341680026150860b8010780d000c6950399103100001c2d200c40c400306244c0c181440242c000400340f6a0020307001c2d00c50017003030302c42866502040c024411501d206100007040c0c9003040d90205a66140d5400c071590350000b101800d403c00f01410340b400d600c1d4103c4009894258040c46036410103500c00c1040c0001502400400c601d0b5504640380102030142200120b001c1c8404004940b003d0714011440f00c0062107586000c12460342c90b4903200300c03039912100350303601d1504185075014034a40011546604 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975751924 1250 975750674 975750701
    0x30a03051206042003070915050f18180906060a030f1112030408011e05250207030210050307030e0d021c2601031406161209050d120b04 60
    0x6000c020051401d645400400480d003103521003101109610711001103003580c0864402c829100d240c0040c0003030408015501c210354a440703c040d220550f9411204840118114904055a0ba5204007000b2001002810380e0394021027030102003016041d2901400d030103103018106503800c5460307480c10451201a2408040c08034441e416000c40041c400035071945201e00050310030b640b12040d05d143d841c150f070029841926280d45510062a016102501030019070302d09010400050614000301120040048803992641001c28100b1200a00801445001f594010031400c1203100c5008000c042e50410744080c40440e0400001c685031507008107034026a03082e5540205490401031500c8a92400654815070030701901441c8002d541d889100d01441183c0940d442d01c185500d140f8243c541d41d041c0c0d80564041d600325105100c54054100c145810200071454159198010720107020020801e10900603e40d101d403070b4000b4221030300b11448141c0608000320401040c06094180001d8401142c007101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975753174 1250 975751924 975751927
    0x10b15070323130e01081b0f0a0f050f12030307031523011214060118030807060605090709140d02130c120f02090f120102070503030a0203090706030e0303190e010c11010506030a0305 80
    0x6044007d00701d4484c80404006000401c144414000b10750211055000540200504503040c4250b007007a0119010b00a0300b079030508010010011032680340d0001a03d0003003015114140b02c110060400781d22000f074a110241840031020b500d00152041d8080785605011900c00118607032100c255114010310076290030390400059941c10011980144204001a050b442247c40030012503280c201404440b481098002050b81c1401c0801ca8012802042c520402150400c280000d021070b4404d4081c074101621150350a4a942c4001191100b0708521074541524001c0030840d090b902103d088641e66420340c08114002412650005174485c040e0502e41040540000d203038075080c082ca1114004140100060511007035540340c0f030450388241c89240c3c54079004030600644041c05c0c010070008000f20306080000145520078140c490000408540c41c409040b4070122040906400089903150004001c0140c0050350001500d02640200403039551742c80c14001410170700380010200c60700c980580743e8a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975754424 1250 975753174 975753193
    0x5030108150907090e0a0203120c1b01020c0d0308060f060a050418141e0a090f1112160e010b090a0b0a0c0618060e010b15070323130e0108 61
    0x70010094054002d508502c035201c030002c0ca0400c14031070281c1d44480304002d884804054010503161040200902c84408803c025294901d2800503081081e03070130307503800c10125689600041c0e0500c010010116000710182d1403039403c15034054509440b90f0011101e02442542d01c805000190242494404c08502c0c20801440080a5680070312210090810049a80700c183c052464030701c2c0055401286100301c1b400c0002c5d40d42c078190481c643c8812481010020703160302d519809200032010300e01400402c074403018002c850312424198018255000101d504032611120000c009040a100d54100d80c44400c0012491070806011160309031001402d54080d1401c00c2d401c1d400c56444491000300344505100c001e00081c3c0d00d07018021a400b20790726143c0d100b082c9410302906850003920400580d925055403554265914501010f010079152005030301c0d82881d18003507445025a9640c0c4982d45000c0e00c2c514424500707600141089400101e040040301c0e074030700500204a2003801601e04980091250 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975755674 1250 975754424 975754453
    0x61e0807230705010b01020601060201090206070221060115110106081510030c060203040f061707051605120306040606110c100e101713020604030b06011e050c06010605030108 77
    0xa4508041c20030116440351a29803024010aa00c080011151a51640c80e07080031507805000280c0100380500003400002500d41c00584944501000280715079509403114668450400e0340d6001a441042207405a58444400c43d0344800d0144040000840c8000a2040f510060007941c08407206140240084503d0a10723500c01000d000700300a00420242d0000800700d9982c1003124000e00c0183c001d10313501c0d802c2110140c651000358012005029440d01540324184100e41c609034403000f81d150007915038490207080340c1e40810502c405031031841002e00c0303043c5600401d00294003a410803101005025651507003999250060525405d0310381003200c040d0818280b102c0d070720400c004246409c0e039480101c4000100424100c08414000642c10400100e08100c0540c1c3c03603820441417a08400304480b02e0b400600c1034031843c04010540c03040503000c10b00781e9000350501e0a80d98200f40d04010701c10003003030b802400354100c2d000341c0005204902c0009001d600880c2100c1c1658461000b030b1105d40040c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975756924 1250 975755674 975755687
    0xd0905040612081c020903070f05091b0a080621010b191a0c010221240a03060e01020f03010303081f0608060906031e100b09090c1203090a03060204061e0807 69
    0xc1110180ba000c0086c024140c1d014000c0f5000b51118007104a81c003410003051008100c8000c004500308840d07140c1c88250502600145d80d4548031a00d420800c60380c600000c03c0d640000e49507001045400c10140305c040e90419004461030010a4480c4542502811250390325130203103100b103220050944641c0800003135400010b00d42c50080030300140c070323000c1120151245200c030380d01d000d420a00800c003031044901e84001d0300090105d402c060f03084a540160001000d4900364800100240d0b07941020405074082901650040d41d02510f4150b129a034030b090140110200302c072800b105103603d2202d04120100f4101500c16101555240025992800284400407030702402c0d1a42c9481001901082c80b00001405880c1c0c603009809410452106200801681c0c038062406214189036020003e6000b40001e02100100e81100c80140c0b44100034105d40c00c1d0311072a18202d0f08582514008001d1220130340062044501c80e0359022803241441001c1101c40e071903001920001101d060209403114410342 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975758174 1250 975756924 975756967
    0x1121040303180b19020c0f1c0609080a020703050d0f05030411123c0c04020f040801050a02041703031b09010509041503111f140c0d090504061208 64
    0x84460b4486841c0d04126030310b90010081c110b0020200560030742456410b000218801030252512203421400c50006a000181c42e1051002180c0450110003407000c035801c455001034118403031030756404003c00025100e08440c042550b00e403144c9406065003e03c2903801c0c1c1c1da540d0040e81e400d400c1d502e45545e01c2c2261816600001d501280003618041039400c2480f40b0100032074001748a111000106400303030804140b0980160885010341400861610301282c2200300c10030445005030307115022030540d16240180d8210b10010340c83c00c42007008101041c1e00400c1642c00760055404180d1540d0440ea03541e00c021200d00b40089603844001d20940d5145d009013002e8041410a54203102102e40864229007031113235003800400e451f003410424000d032805d00e81d0100e40b09481003d010400d05031101030609103404c141d0b0400950004041320340301d4200988a80281c41829202e015044181c01800c00d806401518451880c0c01d800007411944014a40d07034407540240030508121146c0e9880da410b04221 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975759424 1250 975758174 975758207
    0xa091a090d14040504140105040e070b12060301060f0305031c0501140f010908010c0e0a090e0d050d110703021b01020d0c03120b09040b01140117010504090f121121040303 75
    0x1800301203080d580d107020380c041c481d9502041006c075603d09001c00c03060b1511481c668440340c110b6001031290301a04c0081b15808920801d035100c003901c0e000080784c01403003503600210b46001180da0101c00c001c0f011000304640d01e03001c00148140001c124000f000c4440a1041c44058295854454142c1c2402107188900710b10504004001c0c82c1e0302c2d0241e5082d540e01d1507030345001841c400c429480c64540030340c00c0006000030400810440c1e00c00503031380760b481c0c06110400040c41008500035403500459008400121210340006880f42028540a9903a20740001a00d000203420ba1000c84a94400242d131b0605002039501d90b07003068259141a10b507030300301064407a5115101c0070040256181d000c040341c0254480c9801501c65890040a4003000d09480302c4241084100100c5c42e456042c91601c00781035130700440780094140e2142c500300c81c01c601d81c0d10300103116410303410403614640d40002940c950508083e054034100800b0040c4204c105403000d5034844910310901c002d0010034810740d0038054000f0603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975760674 1250 975759424 975759427
    0x4030903140715110f070b1b010212010509090718090201022b050703020c0a0308071a07080402151902010e010b01140421080f0702010f0c020f06030c070b0a091a090d14 74
    0x42850604094154007c1c60b8407500000300035450200f0b1a10701500c403130750400210b091035110344a50040500600ca42c0d84103c12100100740030f02d4080c0806002003001e524610300c1419034007000da0103400741d0002640035010b10344005602e0b003c120390a1081240d02000480c0c10311a214083c3d5440d000240154110321410201101c039844a0001001550194403015194101c901e002400307480e085c001c000c4100e00c01c42c248250240c01216075908154111181404030307201841051041c014540c00640c00f48080e00411a02b580641c00a9801060140240300c0c03412040010340d06002e488600310790b115010001001018180c400488514100030318000c0f41c910079071078019184e08024001044090009034140466070050110211040c40f400c0c050140c0d0702c1600000d0401e54000ca0f00c5000b01800800581601010030440c1d502c40c0d8050484c41305801c203100c5240084c51001000c4908000c01c5010340c04c458021341e072443c490cd6118001b00200c00030306c5c41c116401c2410610203414041c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975761924 1250 975760674 975760693
    0x203190c02071d090f07060e13020c010c0810090e100f060803070303022d0a080705040f0e010e060904020901060e03100501090f05150a09230403090314071511 70
    0x100008180da111080700c6840d0150800e000c41c5805c040700b0042d58071890340b21503c00c000da5078002c282c00800c2c0c90103c0d0000d610758001682100a8412550b0041465207404403040020390041760300d0340200b8000c00d10940320354a9080800c100d0706504008101c50740940540c406032803c40d0051031031610b00e100041012551100b0692071900000c3d01140480d0300495060340880541228441080382903e11a01c08560301c699211140b08101c5034400700700c3c42100040c1180e025500b1a002001103a1100c5025540c0b100c000d8140304c0c4c20b005081070641c1c25800b091003032801c60842070107282c0061a0510f00d0f46000420386070034000084090705801402c1111003185100cbc810640200090000840c41403003400c1818221503000b031043c00008955035600c80c03980c6418003002e040c1c03035822100082e08a45105214a041000d03090101488594020802090341c8104c010301264426020301c0c8440720b02e50846170311940c1d10b014402c0754400003402201d032540b01e034000c18071200d070800a5400859 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975763174 1250 975761924 975761939
    0x1b0d060b07031106101406030424060e090a02060405120a05011812141c1107060204150e03060a0c05190905010f21053d090203190c0207 60
    0x81001c84142d02041e0209010107000384240006076011546054982c202810032100c008240d4401c9205405040040001400c104a83d0390036251002d91a88000c1c0c003103400c0000030082c04d40342c0550408201c111001c2051400f0010300c280c000b035801040541068100002d10209001001c0410a680310b0414201e01144080c82201c00c1c00c1c204d02d001603101021780c28180b084450041c602020080e241201101590b03139581510070943c0082d203021590405280712001510544020700607061b000a911000c00403140d004104440040340300d80000c083c0c120781940c4e20503201d0085c42e059008000003813407007030840e4452100e5040b2400e2890a220305d507206010000c9480d2114404100d50100174003066800401d43c8080180070728214900701c3d40389170440784a4600792810105a40c540000c9a0003045d01d000c8000c00035035801c2c01b403000c50b031128040c000ca04202001b0104404d080940480e0f00b8009000f200c2c4074811004240e4120521080100b0041c1540b030400303000c5002e120000301e2002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975764424 1250 975763174 975763177
    0x60406090b060a2106180605030c15030a0b0307080d080105030d0e0906060d020c0c09060d051c1b030e0f271f03080403060c020106052b0c09020316081b0d060b 70
    0x2400000da08114131b480b161030b200221009500f18610070344c030618000d81c0540d1075010046d803080c440f214040d04e9844004480b006440743d066003940c54080c4030400301d0300d90000030354038800600b05c2d954680c06076030b2042410703100c4d03060b51000800541c94401120b080e0902c00c02d1355402100c0a042d1900e0641c9500000c403c98000c016040925000240700e01d01503d4400c042c41d0700b01e4812101c50b81d0b510310710f40cde4040e0340c0d03c0e506100c3e88420034411850454207000b031002035009240c000c000d0300d00c49264070740184a002840d10381c500c41d0030f180c03407220040e04004c040e048400205560203a0105200c441000000d80c00610071b085001078654805504031326410143c009510071100280c0341d81c00c6103041416036403412049811680f408000f04029901d81c0d91244400c50f20b00610b50306551054003030491249841c002410b100807250001400402940c02140324142c004644001d0401109046440d140c0640343c081c01035501040c4c514581003010020003000d0362840e0300290170360303071070118017001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975765674 1250 975764424 975764429
    0x31608120723010c0f051309202d0708030103110f041a01020c0f0303070f08090d121e081f2d0902120f07030b090f060406090b060a2106 60
    0x30b6946562500400681010214a030030036a07040150410246010018040700b0704d1040b1b0091544031060406212a4100003824041c0065002596149060060800c1d0004803102000c3d803088524440c0d00081003500313035905a40c0c003024203460f60346551039002c1184d084203890740d442080e580b850300d066903861281d4019584030003400300400c6983d400284c10301401d1038015001d8101641102d906540c08022141d0880d4032225604915015003040d00f02c5003ea180390380d4000609400e20814000c0c0c0d03504403a4400f140303a035060800c1039070703901080115110004140120f41090041189415888141c0f00101620b50070303022841d81c1d035003c41280700300c440d030640880038190607805a040d41d81e014a0024049104085d8540135005116114014004050440ca550780c200480c402510035003000c00f00030300007006442d00c4e00300240c10504030a02a2010b5214601d40030380010006150f00072218000c400900301740c14003100c1d000aa0348030450b020800105031004542d10000034151003000007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975766924 1250 975765674 975765743
    0x80a2901091b0201181403070606080619090c0306051e0109020417070602070b030618070e1002012a0903080a05030103030320092202040b090316081207 67
    0x92801410002010070b20101c2d220904590510412014884914491095142e030100d00c108584600389121825402458001000c22b8240140040c215900081c0c840c0a5090020400d40e20909210031100715001c600000305030003903100081020442680c00a6401218039212091500640c2d00070f08443c0400d0700701005a07507021505111002d0810344030010207108400400030b00d41003110103551484a0703c42c00c40c0c01c00300040040d28540310f45610300c3c4841c0341e03000e1342c501c18100000007034000e8280c2d15056001d91840b5080200031441401904a540611416a500c0111090b0040168248044000113000c612000000006d00b030324004c1003c040241d84013a100c1d41549801801d40b07401520754a0b060154052100c2d040c040745044662032082202e01341d283d1103202d0a00d020380c000c40d025680b455072000c43c0009200034800020580007204800361820603d02c040f22060070405070155a030a0303408603480703520382141c0f41c00406005010342a2505051581864240803401d40c0e4002034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975768174 1250 975766924 975766931
    0x20405060a0c0512070c1a04090905030a02060c2b0212070c03080a020711011b0203071d09060411011809052805010b0d09080f1803070906080a290109 66
    0x40900000f0700c016103118504c8403c01e0300d0404551648840d0000f44d00418419180303014900e103c103d40c0d50100c0b4010300e103101c03043c045d0020904000c0e03100c0d0007401d000c0016004030f4000942441e540700886800101108010200011083c941542c0342140a040600d842d400c001031000340c40d03029550342c825181a550401c60402918005024500103450ba1083e50b00501003000082c90b6040810754030182880d0135075007c820b120801c2e003d0360402d00080c1d098040d170000482c14041d42110302001c04591400d0459603101c07440c00c1640c50344110f8010b03040c440000003040c05588501100009446202c250002c61030315802100111002619034500340d03100301c03c2c00d2141d10f5103001040040304511000300219850884440002d00c500107042c4422a0b03156070340303400c00101105440c140c0d1401c0b021642c480c01541c40b24003680e4200c01c0e801740319110340e01001401103101d005080545010201620410907565a00c500302940070f0500903c3e01d03c60301d4080060074001000a00030000300e40c5c0031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975769424 1250 975768174 975768197
    0x1f0302040333050c0a0c020f12010b190305030306041d0d0f14070f0219090e06070311191b0501090f0b150a0b0a0905030a060f05010501080f1603020405060a 69
    0x214003100382c0c14a075505040c1044100050b1841032402d503040f00b0300d2414030410956152002440d4005074801196100c42c4002150450000550003040e0b02e0070140e03020407402c9030b1180d244d51540d05c07910004007560300810018a490070207411207900e8008201c003d00402012040c61810000711166141c009031115840f100b03847d41c0100110400e50713091500314945100c82d04c40f401645000c210103805a424a503501601340c0b0300702507a0004242041d41000f18400800d00d040d200d940a40303c20703000a00b4021100c0600c1c400741c04071882a81c0444108451280800341510486a2004400600d405c2c0c0d2101d840032942c280607070f5207024464040600440200d103010750f080c0c10043c09400100304c80d0700c040c00d0b02d81c890050500507140c11546403a1111000107040354034260300d4010035054003461030103104111542e000035040c00f445960038012a80c8560044464190071103100c03c3c074200c0704003c1a041c0600d41c0e030b17090340c0c9110391801603d0300f91114041401640440500ba0007d00e40301800c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975770674 1250 975769424 975769493
    0x15062212061b140922020c0106080618030a12020405040603052b0909090f020d0305040e010902030c07030e0310020a0e09061822050a120f0e1f03020403 67
    0xc085200700c90921000903080c0c3c1e01428000c0c002e01803030714002c1c5401c5041044e0009164a205000d5042413425035482e6058202c1d00d020b0a41e503c5490710521503980818114040c800b40000c1c9488154025420200c05010840b07002d403070015a003a406900304030110f81512603004000266009800070100d0324032508202c0486030984c2000f11030003c0040031000a194402242800c84200d20710102d00703000b0ba400d0083c00c902d0a928003e42c007228200c00d40003055000b0b00600103c1e81050007101440e0307a10f00030141a480111204240d0850801803080060300445264003522405403c0f10100010b500c0040d00726400140251b0120b818420b654a1070300c3c00d480c007142d100c48240e82c03d4685480340111507040c000003409408001c81e02c10741d030b11000902c2c620315a2a00d90044111969000d0b5820b2481d101600c0491200018581740c0c0c5208550340155100e050b8180040c2c03084040c8441c503022a03450f007915200340402c01d5003c1000101103904102040071035400e10700c29058501d1030040c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975771924 1250 975770674 975770711
    0x1030c050306070f020303010510110d0c030f030203060f0621010e0117191106070803010b1c050f06151c270c0302100e0301051503061506221206 64
    0x8001c0120300c1416007484d90b404000d0b617045420a8a641004075480182540d40b540c00d0040c003c802d110342403c1004003a03004100440c0c4900980301e80e07035180d0703540c5000ca082e480115080354000c156020391589604016000300640c4400d011060504059440c090813903070390a038000e008480d858401807040e20500700720783d03554035090001092004068902c3c0002421074807009400400d160b0388880440c4c84400441c0c0c1c0d025402140755070380b980c40d103501c40782c5500304030409005002c1c8001c00380414801481054041c0c40c40e140d0280c40390b621401001086140700902030000103027400711500c1d03128408404104141041070104084c40c941400c03d44c10b0b0034281c1500009500c0b04681c0f404a9400c1e061354084da60107035068041085210b009440320350100554540541c80d120802002000781030445140704c4048064036a20b4940b0100c0044105912090301d40c0a14100401c1c4140800c0c1d50101101440303051400224030f41d6a10040c204043d00c1c82d00766003d40d03d40c00c2024842036142c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975773174 1250 975771924 975771931
    0xc170306010c02210f0714190e01151e0206040209040c09060e0414010b1309060b270c09010219060b180a0f0207120804020109030804081b15250b01030c050306 70
    0xc00803c00341d80350410241031f8001ca0703001540144214071607000381c01402000b00b030181808958030042540c0d03420880b609080081c0c0c41400003440c1e00c1e44800c00c0240d80080d0485800c850307000300125200d0360200884440050022a100300b844c40001481030100d007d80c90040c10389803401803081c40c082c00c010078003204032418041242d2600307000f88525680c0340300b0324000964441000841c21041d2030088000c142a00b243d99102c170b5004030702c2c0101c5101a4107030300384580d60048141c2d1910b03120420302290145504842c0542c21a961055000c101030b400708000500415010a40c5860040860aa484c7d54941c100105011743d0412008030307014020300310480341440c1d08518040d4a07441e01164000b0b550440c0f020003130803201140942e0702c0703000b006002d190000521b654490b5030303800752556410481d030340d04e4117003580507078000d240d18003840c2c608810740d00396030018030303228100c2c030b40c842403e9490042400440c951044c41d404240c1c5030345924041c6101e1040a0341c00e80c1080200b40c6803030f8009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975774424 1250 975773174 975773203
    0x1060801110705070623192006152b1b0b0403080307050d050c0c0d09030b040f03021009050114090606012010110a09060c170306010c0221 61
    0x40003220b0000b100007540c10704860b460318003a07240003105132070440e1510f03110f80300c41402040410601c64040c01000504981000e83c0c980d00240c0303000b100d20300040901094800034030f811030800a24074a81141026042203801400550003180c065a010740d000c4a2074014401c200a00003400100310580003565035a00420a003142e04070b14054081030144554007004009100c0400803e004501030801d888179100380c0700f07007480303145003070000d24429400183c0c1c80320342446424142c0310140d0081c202076040c0ea805c202800801e96a540707585401c5c01d0b065000320118480e04a001d08011594841e404d04940700f0000482e224903083c80c03807141d642c0701601940d5550442341c10b01405a03000701a5441c15040720669414178940b0045c40d50402c901c0d020500c5216007004003481b0010f40d001c00408071025180c9a00c8141c64640c4411035101007240402448072440482c0c0802010442c0d011756440a01403403c0342400c0758990200302c003640800603407401c01c0780f2080c00348030307004e81800284c5120010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975775674 1250 975774424 975774427
    0x30605090c0d0207030903020d050c010f031a15040e010b22080309090a1107060203161e0e0d0f0609020306061017060d051f0f0c050307030b01110f0106080111 70
    0x40c114080301c0d40700b0700580e4009664001110410180101a038100440d001003d4910410701b9041103a00c8a0401e501c060000d09546c20f44030a80c1d000e8402e080f8a02e1201c20070b5051003086030184082c10921240381c0400d410180000070b04043c1c2d284400d07002e801409a2561078448007181c6180710f00d07200d00414281543c0c40000e000c00c4c0400401d50b051a202203c10804c645ca88801c6c8100501031200c0000a8040000701c02d8184080d035001903025151000980000c1d403031610b030860ba00104014104450080042410402482404c002040e4500100403807005002580c5010054005c12805c54003e43c640134a5019441d080c04003070350209041e20410400c1c0160341d1b009206d403044c1e010039800c046058001c640d00382c85580d170b101c007400d50040880b000e1161231f010303244038003046803a850b43d40c3c1e0516140c403818225600551211a019494007400c0d502e9410040e03020b0800d10a041d410081c8100003088140d400704030588403446040000034549003000041401c1d07452149030715064000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975776924 1250 975775674 975775681
    0x106060309020f0603100902030c0903070801090803061306050d110102100603150e0f0f01140c040506030c0c0a050d030c02070b0705100b03030d09110111160e190203041203060509 79
    0x11950322032a1043c0085840564a543c0c2d20301403090b0030b0300f0b42c1000125038400b00810002c00100c41c01443c0c620740031011525115602d486090a86491030b100030312090301800811414200401c8460f44010484e2020500d0307a110b00108040905440d8151043c1004e40b10040d195601031000c03401c40e0070303c201c05001060840d2030350950700c4403462511508558402c60543c02d03c0c2d090080443c01e0150a0a480c91040074a00c038501903c026a0071058112140f400715005c402d020b4100c6085601c050510b50440d0345024845031242c0200c141c00e0014000c0c1c02840b0000380c028030100e0b070340030707007a40703000800d80000b600c0245400c803a0341211418036000c0054801254002a07104c5802d404a0700100340503000c0404241103018081503840a00c0c10140401c007005448003c260f006282030382c482040342030442119503142c0221220380d40754059013406001e0481c064000c0c56014030460b500400a078062a06141280c0c01200c040d606c03a040d1a031f40050f040c1c1d050080034020041150543ca803401c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975778174 1250 975776924 975776929
    0x90111030a0c290406090218070c0f1a0f090705101710030c080d02060a09021003052e0e071403070f0e0907050c1614010c150e0f010606030902 63
    0x1e840441c082c0500341840180a0b16424691414861a50f2100044043d0030a03180c40382c041c207840c0d40704071701c40c001041c0f04034032420203100100d100328040d6079003081022054440c02c9039807428040a0b036040c0c5026611008412440314100e002d00e441090307000807803038010549800c4c01c0864120358404c640180c25221076a0380702e143c1890030740a19489500c01c0c0c03201d182540c4000000e500c0100f61600d001c030000340d40c0d400032810212244564082c2d9042da80e958140f1021540c40002c002c1d40041d1100303101c12110712070b501c03281e40f010340c2489410b010401c3d40320041c2520040d140441c014203410a0610807203c0202600b6045605400d0003c9641c00e460305001f41800001e0201040054108003100310501c170303c0010400241c007818540c030505100000400d960700100c800c1861b0310962403081c2c00d40c800b00a01c8801c44003c800d44022481e001401158442c0650788107a0309004c460071600100640381c030401c00002a204010a040310840c1611030940340d030382d8402c000789071824040d1750241c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975779424 1250 975778174 975778187
    0x30203070c0503011e0e0c031603030207090b15070606170708120c030708030c041a07062f2101080d11060f060402032502071403061501050a021c05090111030a 70
    0x18255085c0100340003000d1030141c0c1c540b5000c0d062041c1d051062214003da0300c83e0408029054078040d509440c00d56403110800b00c155244503205982280b0060508202c200400004d403040328402d0300b0200e0200c0e681e0001000c48144200c066404d078000d080c080104281c00c002080310408a145014140340030004019202d004003000078103034040010001c0c0c002d084450494002c6c0241c40014185420360b8107510300d442c4c00280080342c50700e14101880841807030042010344481c4a0880c1480c0407003516801130300030b40100090a180701e1041d101e00e601c4d40700c5140c1716406002150014803010b240c000b030080c18200100d846203490b402400c180101c4981001c5d907641d1000050740c0143c0c0e00d85402210340080c5041c00743d10400d0342e00080c0010880c55000c14081300300d031940b10b1101c03e00701031502050740303480095039281740d0b000204400a00315401000544407000090041e030346c2004207c1c40c0141c03001088540500007401c0002e01441a60704500b4049031280100000c60400c1950031000c0d180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975780674 1250 975779424 975779471
    0x6091b0e031c02160e0a0e16050f0a030c03080703030b271e090607140a0806041112130201031d0d11010f0e011b0201021204060504080412030203070c050301 69
    0x108200d0042102c0301030b0081054004e480c0d0800c4980e520b281e55001c0070b0400090544030138a0003401c0140408540c0340c0002c004001001800c001d100003454201001400260554603c0d00090b18000000106141031003400042d8000c4141a039966000e10b0010122000901d101e40314990507000351059031181089291140300800e044000741c1c4420030641e800c0d48030032600816410b0614104511141c01103130083c0521016120000b46034019070700501140100c0b0582000240250300054032850107800181f403452100034000e280070410304203c032014000f111490500c1258021503000c55a1601c03c0380320014120b0b00c00382d500441806019283d8840c00c0d00751080200d0410324441c0e41c0d20030b6200618200003d001049443c05d401001c602030205031140718031b40400c40c1814000c3d5401070084440000940b0101401a40c1d40d036950801020301600c00e5410120611021030100350362110b5001c0c2d81e000360007c540b5200686001007481165800503806641010809420351030040280d061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975781924 1250 975780674 975780703
    0x200402040605032208190906051c020f0912060106020d030207021003020c0c09010f060206010f03030206070f02120307080f060409022110060b0405100f0206010510050d06091b0e03 79
    0x204100340203089804c4401c0c010b0060b14002030011501c4110483c00740700345c0001d45846000c19516001a10280258a10922070245255031410040f4107540201200490509880c0c104418803012950400034844056078650005006000298041246506821440c50150300d032142c2a4041044941404031400030705402107003000c1c181806000d07641a034000038102046a60350b6040040741240e04ac450340d000350050380c001141044070108071009070f0b80c040e0000c011079210404100c0f0000d591014400031070080c405140c82e034221890046009411507500c2c40190704001c052007400348800f618240c42280340610241c0103880b54000d55a0010310700c545100d0590001280c1824602001c2d00c1c070742020b192034000703d0700303004020261050f1082900c1200c2440003921003990401401d2007104050380c0300900403c460310780701d03111800c0310140b807610f1401c1c65449800f500542d070554104004050703c462a5102004000d40143e00b417203050300d04074154001c040082500c44070040c58812 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975783174 1250 975781924 975781951
    0x2031606020904090b0601031d0307030e19080c041a180a0605090103050601080d020f0601050f060d0c0f141c02030406021b0d1e0e04091e20040204060503 68
    0x400d00546070705851841c20080d005203c558260315000550302ea048a036203000c40d2800e01041c0c888400041000d100c645150000c40c41c2811a480640308400c0c24180b05a003ca5017602d17148074888030342d4446004050100003070400c40c0d040000c00041d100e01c1104034101c510300c4a510081c0e0b66540540840005010149110340d0b00c81006030005000a508019003160812000204100001a92504a64580c000d5400101d40705070704a85843ca40d0039003400b140d00c00c0e0300521540c509540700904091004026915082038a22104203640e9005410b00101e081011603130091904a644880d04442480e40c0c01e01d0b042c03034615102c5140045028036804240e000c4002801c018865040703545031007104a54080400f00121201d503100f4942c0c02035000140d01005694a0721202c21110b0040991902e8010b0040c19a609110007008603110503030303407140b80b10347c01f100103080e9014070b0100c2400754103000620759504618450205000c10014000d9104110821019522405480d0003c01021045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975784424 1250 975783174 975783217
    0xc110303360606030615100807170a0c08060102060c1e07020301050c040306140402090f0a0b1005040501110f060723040b180301090209130f051c1209030203 69
    0x11040310101c0c1100300000c1122501c1a40c404400050540c40749504500700c0f022a500c0b6800402c1c80c06403286840e401c0160035002c100c8090192100d16803180305442c0c00c0044c1b03905184d031148141c0e01075036405c0415588640b82d001c03180d400340d04a039001d0428001062581010b852510980c42245458000481401d0318901e442908608130b856981c0c000b80280018200261200882e03800741c4012900700d442e00d0720b0315141803091410f0310302c1103400504640c3d966541503c0e9150400000302003459646d80c0c3c6181203450741e11008107004d52100313581da460301c42d0304050024042c3d40702e003601000750740c0c0401600700605500103101d5510000d6446c202046c40c081005924100541d291103107850326010801158500c0310030b001d050201c000500c99031030080000203050880c1e00707020340130350040700c0c040020300c42c4260001c071416014410320100c0384108458071810304254281c2003212007034101316040e5906607804900468200e1487c201000210600c1e94083d50303d1180c14440802281d070003800d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975785674 1250 975784424 975784471
    0x90201050708070803181f0b0105070204060906090e0106120305090604210218040c0b0915040e04050601081615210905070807032a17010902040c110303 67
    0x103a07110a98451042038582c4031034904800790307410450344920404a410300818a4400002c5e0343c0c441898410047d812541d024a051070140c0f8000190303906010040002200603244c0e8462040140128003002617058189070602007681c0c1070410a03d61070307041003402e000d00424803850131203d83c0c0c14103016030380da0b40c102e000c04d1480c0500d521951350a444085281e00c1c650900c4071803030089100301c94100c41824442c1c9035840030002070b80d000d440680d08140a009401c04da100a000da60340017415851810b800070f1406d03441d0b030702c83c0e0808000c4501d92418041003180802440d0702420021002c0c04140c510780364020280030440c4201d881441e403e41d0101d0056020340d030081d40340d09007081081c07014210b56003600b0240111840032074603442003040c00298200041884c2b000e4907072180078000e404101e61f40240803144054000307080710300c030b8010005840c110f030842c44901c1e000c018000700320b03c2e40b5401000101d4000501d0001440b02503070144010a901104803903104401454500b50072015003079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975786924 1250 975785674 975785677
    0x50f0412030e100c2f010e12010c020c040b04051e0c040905070c0c1514090303090306070801090608030307080601031a06030a020c0601290d021e040303020d2109020105 74
    0x40c050b822003038003c0c10300b004030341c8076018981d0a03009850580b0650348104034045035031545020962500301c81888682c8540c411018114110700c01007440c0300b1341e07145150003401c44030003800860241c2e000048800071800c1c180500815180122010000c500d4000c0340080150f68400c44101374054200003d460200b0903016240601920001040507182c90754015018403034042d42501e642403540d20002d40c0414003030602ca80c07090103545101c8042101790400e4600e03000414400d525000901c60022252401c024180c82548503035581901d6514151118003214a40d400c4610309070810820408030507080180c50750040c00030321b000a8644840c0d4014600c20400558803a40310300000b0034881510100d0b0058031b05032009209482c3e0a91b41c0304001c540060342c0c2500c003010030307000c4d0381110b980c0400440600f40c01c110101d0054541003103050303030020700d0500303001911080c04049024000d140d8100582d01400c1540e09150b002142c220340014514a00f0102d0f50101ea030700c60b80d00034210b910600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975788174 1250 975786924 975786947
    0x101d19031403040c08070f0e0a05090714031213050a06021c08040f0501141609122a0618050316091d1f0c170408131e0312050f041203 59
    0xb019680030307c1e120480001e0590781b030301c900d44045a00384003040c48208244503a9000d820300000518840b07280030940d103c0a140c0311801b60f030501403484254040e01d091742c020418808041e071503c007424100400c0040e08076980c1c200e00115800260146070f8603210811071050303907a40d8205101d60b69a17610748801000c0b00700b6801040c075401c000c42c061001c0c04600300d42c0c0c00386c0c00180f064108290182800c95480c0000d10071074040742e41501d00c2101145110701d5200c4682500c034840d04407200244401000910b090707201c04005010b40f072500000740c000001d4000503010031400351055500e4480c04c2400c079035484c011984011703680c4402041c1f00035490a48850384504e0416100320162001d09050004041401c0e445028100541070074894030603001100c2c80c851a6040c81710036100c0307441e840025040140c48410781800c0540c0071503e201d040d420009100c00c100e02c200409411032500205a100401421090140901c2000e04588444098500741d920300c00c0d981a0250340b034141259030902d01c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975789424 1250 975788174 975788189
    0x90304180b0429040e19140307050a050a030221032e1202040506061204120c14010e0d030204081b040204051f08060312031503101d19031403040c 64
    0x1503d18640481c4800420f4031140300803281008000c02d2100c20303a89510495540e82044051081080001030700e0306c0e42c0760b40030303030078401203e0900c24156207071880c00c40214029203407540060302420030141e04000407480c0c0b40024031a841000c81810000c440c50101601110450200800c0001d150103501e41001c4c0b88603483c00314210a41d17030388803031601d625000001680030303a040c0ba00107a00c07400c2c0841118400c902c40d880054059480741c48a0002007045500482000003d681100204600700c980d040c52044c02000001d070070981103903007841d220313402140009043c010303c010024038001058501c10f03142c003162084e00c0c0e0401000000d00074816a004258040803407050300c06400c0145840416140c11620740c1d00454541d541090faa41ca0300b5072031030441000c2000001c00c00500342421400d02c100141c101e81810420045030425104214803003118014407040041d8100c100300942c001080c50508040f11003581a00c0c018803000e445800d50340950301c0003020504200e0440c18080080054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975790674 1250 975789424 975789461
    0x1e1b1410020d0618180206070602070503030a0c0e0d051924060f0602070f05040c12090516050f090412110d0206060f2e020102070c031109090304180b04 67
    0x1a9001004241c54042c4d003000340d5605680035a881824070a40030101c40030030715039410398615400c10103d070340086401c0385c0d074a80a001c0340f8001030040010354003038240508042010041a600285100c2c514810b01d80329020381c100c0d0101061001c90203000c6462032640013a8080c91601f040c00d40d0f14104100002454082c488a00b000080e40c0c3c00394003641c070401900a00213503138103812aa81d4038140107045107000e000d00304020742d01d0164000c0d00000b0b0641017543d100d800c2c0c00d000c0d500322805880281d6954100000103260700017a4000c81c800b502084442c1c61400000e500418210307100203000400d43c1030800006007185000b180000300d10030386901125110000316400030346444003590103602a040380740300b0544a00d094801d601c4e1a01c0606140e5000c55002080c1200e0b10b1000409442595420051540819400c201040295028108030000c00d2807910912405403001485180b0f0750308140310512810040c000d03800c0507080303454004a015040710000800500250f400f01803040302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975791924 1250 975790674 975790687
    0x6120103080a0206010f080309040c03090b070801051c030e04021303020604080f0d0504150f141b0705010f0c0b0417071203060602070b09010815030a031e1b141002 72
    0x4070360004198040a65080d1010b50740c0c2c07541720b8040583c0700c2c069075605410600000910742490f80c4499111846403801258020f07503915142107611042d12140001580407005024900340305440d5025094054031513000d041160710024160f5008848040c03050380c0018043c418101031030b40110145400a12090352141e68150142d950348030020307403a4190103015400f1105078014000c3e2001c40f806a00c0807400f819031305808440d031410703c03900c1109000803540c5107000000c1c002c0162150700101e150f01c20034114600585d5107405013a6012a0410181d0030700c038040d4a40c04200708490039445192422a45c03500e10385042d031424140b2511460910100e6120103000030f600300c0404111840e20300708006034071000b04a8480f070711070040c0c0e500781000304504400395100c0c8200aa1222824020b806c04001800c00a41005102c0b0300a07000141080b4803c01c800044001002c482c0455040000000708000c0900d1444200244041c2545841154041c100790040c4030594039100c0c1903030115078412 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975793174 1250 975791924 975791933
    0x219060807080a050631020a050406030612020d121101050a0506040509060403091401050d0e06100f0f0909080705060103140f01050c09280303020c130212060f06120103 74
    0x8104540700800106800082080c3c0456031094900501c405803030580c5002c05062400034400c01e03e150040707802501d04501c070701652584041c0c801a10182d0b50f40d40e480389800002016500c05802400c0d10308000c00708940140d459000110126034020044c1c0040e09c94040151a403610300c40603c4855424a02004180c50303d591196200e044121000c0141d034681d80c00c1c00c0d0380e070b91003201c008020030b090040a02c0010a5845d0344080a081450f002c1e1402e10345030080d2040d9840080904400d51181051049541f25050351202800c4800c0644101320328040b40c8405018180c8103401100c0d80c0c2e20050700c24040a60100da007255000400c43e80c1c50f5959180191420764000c0520601d40140c60301c0c1c0c20101d034180240390050842c40e1056040c030001008004852800d4048500310b180c042c9600f6800120740c441a070010742c02034003d0300940d0f5489062092141c56080a4001184100300c104460034580c40035a420441c1a100032078042940400300e207041c4a4490305a0491640300700000400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975794424 1250 975793174 975793187
    0x601030c0306180203060703150f15030c020f0a081608030f01091b080a0e0a0b0405030c010c050405030a0605150415050f090f010e1e0a15080c0303070f021906 70
    0x403445182c040200d1a102401c468022259542c000c1d0f05402041c0401c40d080e20a4010f0000030404034101402036640d8500701d2a80c0c20f503507015401c801c0c0c0c840c0c004a481c2d6050f105000d185000760004d028080a845602078440e46800d40051940d88003040c19400c0141c4448200e4a095018040301e540c1e060464081280c84030900ca14070816003841c801e41c0012010001a1401c98006c2e12220b2603910394860020103880c070314000c800c1c50310a0025072008555040001401280250040c40c0d550b0a845012825251607400042c14008104001c0001e070701e00040c07600c0c480e03822860000d942c0d00c42e00b40007003903130b5845050107a1240c1015000724400d40c1000074071044450843d425188640c40c007040c002c01c100129500d6030200d40e520010403a5007284540568014000c10044214901e00313407006d203810000346d0759070300b066079251340182880c07004a4004001d006204001c001c1d003405000082e507039208400004010707050381400300f006c41d290382e00011082081e1200f854035047c0c0701d01009222 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975795674 1250 975794424 975794429
    0xc05121905010305150106090b1e07050604030801170610030b07020c030708070837050307020a060e011b05060c0706090203030a020606130203060a030209070509040525031a10110601030c 82
    0x41601c0c170000064203900592400701198500324286041c1152600704031100e4482c10808c001c0031404010317480014030309000092140b440781d00c81e41059410840720a041d8086040c1222440d8440340503c29003268040500007180c0d4000c99082c869034a501041b03080074500141c2c25014800c4032004204404041410420356034082c00301d0341d044e0140f02400710b9958400f102c0005d500890304208000b640c45012842d8002c1c01002143c5c5000c582e80d0125002101e9a40103400142c02d600e20682d05607030048107040300c0030416040000f190400d03120243c8941028000c804442c900041c050304000080e00a200f40c039400800fa2503c038800868080e494000c00c40b50248548c414101801d00e070112882039a003d0900904400b112a06617824001e2143d0003502800920005002044040d65207005d074610a40d08200f50304a01105060580f001082c0c0803210000d15040c030080c032610260200c4072914000b8201c0e1242c003402003c5c6415910804c0382c842c1014030b801860008000d000e16208003108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975796924 1250 975795674 975795703
    0x4141504061d03033c010e220c091d0102030c0408010b060c0706030203070c050a050a020118031109040602130b04050f01080412030b1c0320010c05121905010305 71
    0x30b400e00390318081034480c80100c903101e401100300d000d2141701c9050020244007108420003150602559002e001103400d40903403084000c0c4a80000b000b1520000145800f0801081c1ca200d8070ba081003030340e801071480540d000b040b9110b07640340140030601d0b51042d801114520200d00031036481c10300105500b81c1d580b05003c1c2d04815824001c901d0700c1c500300382c401c90b030600d0815801b9200c15401d1540880195202900710005c0249480e55600401c0b014400f8a9030307148100300811890340184005000f1a038600c85118031000805020030204410048a05900c2c804880c415036070794031860031500038002c642403070b64010440300020414a114030001c2050b6001215038100c5840c42c1e100446450400702c40c0240350990b000030114000e4080c0d0170552180c1030017001643c0000d401e41e1002c02959030780e50194005401c6171175064030030344840c02400704c41a01400a22110703204c2c0714081c000d07100703208411103001501400900440040c0310301c04400d005c005414089540d490801c15a280005410080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975798174 1250 975796924 975796961
    0x60b0123270303030708190e0d0807030203090c011b06051303080105030102280e03031306032702010c0618031106070905030622061d060903040803030414150406 71
    0x451103a600700515640700c000d0045255665090007202c4003280686102e10181100700302c03450052460264942280c0c44100030f003504450610002d04103a8060112800e240c0704000b844500940814442650102801c1801d00b603c10048244079a0180a901a26142c60311052041c956940c2210190741c500075540d110540c4d0302e03201054200e108140168403035003000c001100d0304514003002000c156080703040036001c2d0520400420305603800301801601200b80207000384007141e011322a1040d05548410002d600885602150840c0c3c1c0c8000b10207810700608101e10002c1140710703003100344000410340700c62034100c050b071030003400c1402445200f011a009540002d800c1c140720b4021042111130080003494585c480e401541c003100204441004d00c01030180208002c0344c807600031103400d0400c3d2031030b6103a0b04025901042c14007102403c192144d0b081004108086000082642d4215401c0503810600b220744020151800c070200c102000f20500e50300401c418031056a026036494511070049a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975799424 1250 975798174 975798217
    0x50a140909010506030703030c0f0b0709080f071a31060806040e0607140409020c07090605010903050d0516210f090609150e091f0e0c07060b0123 64
    0x45003030b0f5004851241d01039010000400100c3e1041400c460010300500e9080300c1030806444100c10f0442c1107600801043d0080410003c000b400c102c2c0d08220720289002c2c01145083c51001140a882154100c0003e203010600c000c000340340c0300100d44c020702042820340c2d4070400680305600150080c4910001300e00d018000070f80070b0516000d10300881e240c60002d014240e44084060711050b84880840c28000303424400814400c00342d100801c04208520014000107103046441400e1f600203401c59070403c615a00100001400040c43c0388032202982040740e00c030000d981c802608003000200c0581942144510340030030740b24003400c10306003041c03958071000d90b02901c2000f6645203c0c0d030311407400016444141000704c062000e1b4040c1d00440245082c1507100e44400000706220b405456003814500c8a441003854000244003400c003c148480c00301c200c9103402c01c40094140a003480c09403910380c07034049000080c0e2040e500318050116441d400140101150078800043e000182c042c5043e01682420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975800674 1250 975799424 975799441
    0x8030a151202090a061d04030e060409150501050c120906090a060503100e0c0717191e0f0801090b0f0307170c030303040f150b06070308070806090103050c06070c050a1409 75
    0x103520540d5161111036881e04588840d40301b4202c8014015420000f292020996541d43c01c4010001060803a0000c1000c841c1e4182c407041c1c044c00360f800b981c1030000c100300701492110007081c03441d0b45036050070842d516012080080f034024803d048410364000c1e51403401254258205010714060005003102140c001d8940008075071540c02078841240198041c0311040c0014040c8000390b25030700c082801541041000d55801004c0c00a403c0248045181c843c5c2c0c180b0340304c16034503140c400c4c08450320740880f21810440c0054120070041c052683e01c07507140c4050340c00a40303850b80d107002003c40180031260643d9440d00304503a41075200c4440510f9018540c0ea41d145450000140e0b03001d40d400644c00b18030100b5a41c1c41040003401003184080e034a48a500c819840e42e2940041e101c068080c1c0c90300030080c541045c0080c0b2039032000b810244a21110401403002c12800941403650b002c1c10303500242d032011141001410018150301103584002e2980c1c0104040008280c2e00403141016103584000e41c450281 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975801924 1250 975800674 975800681
    0x80a180506160516030206011a03070e090405010e0f0705040c020615040213080109110405010501030c0f050c10020f0c060915060d030302040b0c010e0c030c030a08030a151202090a 79
    0x4000e486035218902040414620a882100004003401c115140088444411030b09030050001940560460001009400b13468043c0000d07008009001c0d80c910314181a010f421450801100ba0150380c0b0040054200442507101c031800d402c804003100c5203900c0000c040b540d10601809214002c0b401d00110282003070000403841d000d10b00861013108c42000b11010700000b50005a0003821003c83c0010024840387c080c420091714500402c401001d03144900207101c15200180d00c400d04040c03600ca003a188007940614401c1c01e051092a100e603541c00e03a5504940b41100352200900d403d480000c0031a00110b00500804d048102d1005031030304c47d6103d8800369141c1c0c04481920945d50355210018030f1501d045a2046405c1c0e03c603040c01803e103500c07001d80d503407130707402140c010052a95241050703c01ea40042040c0c00300d11070110010000880e00b040461b071940c0b8001001401114048086192441e40d50804180f0309a0240f104542503924103c44458a001e4a42031780206050703408500320400358003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975803174 1250 975801924 975801971
    0x201050d0e3f03040c030b010303020601030b130803061302091012050a020a1d03010212131a15061b0f151005181003200102010f0c0c0b07120c080a 65
    0xc00d41040608519240006070780010411540e0050410010000547c0f1690035800b03103009038014640780d811842d040f1700c036240207030a40c140b003e00880d1081c0090140b008581d403040c41a03c6002c09020344102820281c0243c100c4a9400240c0446204000381d0081c0c440a100d00003420074012601e5040c00720007280b1445410380c00040318140710a00c0807174808228001030001500042ca8099030503950180c031003042d070300402002c2c0f4441c101e0301030189511525900711401c0804491a08208001d0307a440e0a18a01d07060160304041800c1d8000982420402c600c01180410340e1900e0308411a82501c90040038100740c42d4000800120300d903105800c0e101c0c0c060f00c2d009420003001048100c0d0400d031050000380909510015100040001000032001b482c11075001003846420069034000a402c0d41c0c1200400d0304d041d8079169440c05500d500002505c07019400c80038104142c1c4034101700b1544c419054510021650905450007241a88941c10622031544280100251240207241901d00203089 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975804424 1250 975803174 975803263
    0x15090e0a090302120c070b1b060c222105010b030d030507020f0a1e1b0b09010e09060604030f080c120301050109140108190b03070b0705061f120201050d0e 68
    0x2c0107001401c2000b00801034003180000306600801c0c02c00506140220491f100004d422000c81c00161a00300e00c106400111407103034801e01002c0c00c1008a030350108141201c10fa24040b00d11810cc2840003e5000c149043c0d4040d0540e1582000101c000c0d016090964140c801071040241c048800b10000c104455000ea0208a241c0640b102d1043c60300c02900d000c00c00e80740352040704054401b10300500b640c00c0050440724503050300c80e0580790016228034140d800300c1c1c0c080c0c090001085225070702c4008403000e4941c000604003001c01d50382030860190003a501740c0045407041320b00042d00401e0030005103040b58401d0340d07815038140e202e0000031620007170b5a40041c0441e481034003054080320f000700307c03645803646590009181c01010000a18207a1103520560030150700080c44024440207104080c0d00c641c3c0300d580c0142421004013584416412031107901e051030100301d6003030704580c826011103c20b003454803024800e840da0300c415036031202c490014220007094280c3c403602d0003004c010042c070748a4140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975805674 1250 975804424 975804433
    0xe06010912080910110a051e07050d0813150c061b020d0305040311030703080406110306010f0302070302010f0219031406030c0103090c0308030c0a02060a0207080415090e0a090302120c 81
    0x260140401c0380d134601e500d6018816060308091844a0400c0070310081801100101104050044c02a00c018080c41942c40a50000c603002e20a80d00e5140000e0045503003c0350b92542d41d1032071640115010000d0300282c109286000800144661104914400c940540c01c10495a071050803403c01109200d402d030009a0840342038034800c0b50003540403950090007814031200301c0c1130b050400342c10355002840480c00f09454205102c00d011841c850039a00b65030140e40540355003020000a0110200581200101034000030740c0403c1501c00c1d0400b102d1031004900a6448590340400406038080032503000740001c1c500b15406640e81c1d04d45070340500a05010300a404000722010044001e8400100300780c660a40005001002441480055209109012001d5240d5010090007800d02c0c501800e6090454010b104050100d01448102c41c1103840c41621400f0590100d00140c5001c00a544404080b01840041154040c2c4c91b4208418841c82a400d40d800e4400f841c0004040d40505004804198071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975806924 1250 975805674 975805687
    0x9030f270a031a060307030501020c0f0c0a0b040b030c040906120b2a07051504030504030512070b010e2a0a0207091103010303050913051e0a09051b13060e0601091208 73
    0x1040d0110344c0e0015005420349109079102e07160f66080e40e006c10714400c00d9070b01c120369006401e007040c07100200c28001119549821807400e0300c80c01d200c1c0900d010b00c0145000010204903c070401104407030040c0035000342030003180c2e550080509040810b8800f0707118440ea680005060124114042d20388607038070396090400c16090301400d1031903004854112454480c10200826180080402e18820361003961440da03103608514200381841005603103080c0500d01402020b0005285403035143c156204e00b109840b1999078600140d91201d600e85081005001c0d580040c6202c44401c0020103003070304541c080300d02260b610440741c0104c0d00d8206082e65000c3c1c060005000080c403d01c000c01048400034540240105070b04802c1c400c6078019250b580303107507903c0d00071b10b0018090560313526070041e0381c0c0804100702c100d241c541e15190b28511401031182904001c00356015510704514031005001c5010402000c3d441e06401241180c007134a401b80403034860480043d50540d0028030410956104044030305200707 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975808174 1250 975806924 975806963
    0xb130606081501090c050702130e0c06041203030b0409080d1a01020c2b0212010902100f020307020d030203161b05030c10080403141908071b030809030f270a03 70
    0x201c1e00301d0071406c104c010005003004d6a1420500034440780f14038000a0707444102c140b010316000d07040c4c49881c0112400e110410003120210040c2c0d0029400d410086202030402c1c0c0050004e05821100800320000440c0500c284131560f8050201100700c0401c40b2801c1144100599071105029500c9500034030b0100b540304c424248002e00701d40c4001c1020048024001540000c4601d100802c0724003850790764038404805d6180082000e02d0300700301424500b283c0205004003c3d00d034071403140041d0254858443c440d0425200b0000c460004002c140c41090f920160b1a00402c3c41003c020480e0482401340c201048a180114040c0031120006041d100744001d0b90805860144000f44240c06204001002d030300e00f140340307400070980d42401d0142c0b02c3d07007201503a802411685020704010708021110a11030081080c5c0c815503d41e2580500385620180c3c0c2c1c500c01503165220b028919940301c400810b442d401ca10b032210035000004200600d08410000300d4052001c09540c0e4800507024181f03201c032159555 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975809424 1250 975808174 975808181
    0x91012150c1806050403020105040e10030203030a050706060509011212030e0a0305030603150f0613020d0213050a080f030d0903020f01090c050f120d0315030b13060608150109 77
    0x184204080c80362000c19100c120111108401c100001c5441c1c1030842c81541144207210010340360300c0c2000340c10076007190002003a90046004810301e441281020600320307610341648100540e401011295120002000100a0340100004664060030300304003040500d000c0c03507030301d040c2d81e0040c0e10322008c0141921250010700010385030303000b4076903107a0010001d420180008508180651103c0b40c1d01e01b445030902d464980f40c80d84406c0b0a044900620001511001125401040469448003c4228016500003e1180c1e01010480324800180c03001600d81d070315505c00480710229101010140d4130200d00d600c400c1100a000401d410401c0889074141e829808046a03c0c002d10490700004c481000c0d040c01c580704084261003e10512a00700b14078a045045417a4841055555004080402400701e958080103108581407646a205a5601001c0103086900641d00841865540c0c106146440c078280344201040d96800d09040001c48c001c2000910480307407480303d1020621582c42c100c0208002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975810674 1250 975809424 975809459
    0x50d050306011b0c03030809010216080d0f021903180305030f0c070b0a05190b030606040b040b10030b03060a09020f130204080f240403050304061e290910 68
    0x52015419451401074500b0b41643c44082c4504041d1a071581141405070a542c00140507000c20b038010041403019800700364a000b503081d0b00c45619070302c0e640710711050310140111a405451041c4081105985a21412841284211310f9241005120040070f910041e0080c48200a800300300100017055901a400140550098045461604021048d81d40d05072040e400c0d0703070711242680c603a402d1100701d220565004c15122640601004800c44001c0482d8403803500070403082c41160303a9880c442303a5031100d40111000c1180240440203102c480a0058010315a00302070500034490a0700141a05149100d1001095001420082ca10f445203042050b02034020380c0e60b014154081c8000507411404104140284038a50068415009194031908894a800850f4600c00640c00c1c14000030030740150440e81c1158000c9030204041c440402c01000328100020516031092610f510700c0c00c07044409100201d5008500003401c011020700c1c003000380307250041e1000c500b4501d408004020f2040600040d046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975811924 1250 975810674 975810677
    0xd27030507082a031902060601020a060f110f0406030b22020d090c060215250c03030207151a040b10030c02010b0d0c0f080714012a080405040c0903050d05030601 71
    0x49012000a040c0c482208143e55107415480031079040f549000c92148048015444d10040070709152a10000350b80300c0745148081d00c62a40c8284241c000c050b550460b02c1411a4424219600e1410324100703081d0368040d00c14200082d160030030151551502024410190f10902490720440049109000c000d502005c0014400d661300e00355180050f0b03c3d80710078802000680c0183c90902003a407441c1860301002403141000d4180030301c215040384a0040300d00d11805640c5400b800c01007051809038000d1080f100045c000b8000d842d0701100000e00e5030880400310302c00c035005880141c81001030100b500c00d0b50590310b074020103044c909400c0511a034011202c2800520011410b0345001c1c002c038810004543d03085c1d0f5454201c5405010f41209190040d0003030090300001c1c54018500800503510705003504a403810880c00c650344100304030911400c811840e0301440c50102c10000c3d8549640623134081e2107110f000e1824121000003031405071400800302e94103d40507109080c03581c07000725050b80c0000c110700e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975813174 1250 975811924 975811957
    0xc151206080d32090a120f23070803030a1b1d0a0512031b03070c1a0c031602040c090e0117011b1701050a0b070f110301020d2703050708 60
    0x142580754004182d0303c03070b84410031103561140900180107000f081d0760042191440c084a0710000120907900c1c0600b0545c0000e600000c400080001c800110f0183c01182018031a0300381c04945000d01000a50040d48140b8041107004684444031121150403800000461148445481152200c40c00f003966900300a01411000c0e07200c000050f12120302030440b0201d9400410102101c91803141400c085084040065091049982e80c40040901501550809101840201001803c200103071078110aa81050f2034613605452240410080c00b04001d0b8400c40c117015482c0380c0790307002d030f07400b5015918000c9810800f07030700349500c481d440b40004910706125944c542c814503410750896080000251140e48405102034013009440705e800060304254072507420700c030040000c41da01800b12009141e00c40400161440d0a0402c01c020110317003100c95805500010741082c2c100910740c00105002135000c0c091801c42e080700340341540314481007002400f003a0100100380210f4294070280280700f01030724448 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975814424 1250 975813174 975813227
    0x1060f03080301080c011809090807020a030501150506040f0e04050c060a02070e0606030f0f0402012003070314040602070b0c011e050f13030f050c0a0c151206080d 72
    0x10096401520100c0002c4014004410140804048000c1c24603040b1100c52032240d101050400c2c80c03080341301c585d40c1c03481e0010820859505807400690003c0490046a5507400c5c55400f07421818844080d03840c8006c4003096602c2c26a06031130a072601d030b101c401346e454141145e800c01204064400d0b515442180701e941c1969035118024501401c507603019151003854150242c0c4188009800783d441400d0a2080220030f00c644002998022100000e810281c0c69900050320301110034616804000e445808500414030004001c042e014880c2e070f034001080100c10842000c5005a008000040e08040300c1000307110707640c102802011100c400002000754441007502c00c01d2105295001000d501c0303908001500c0990070b4032a50181000d000203800040d00d80d0000c0a00d030403041004103022000c901c3d8030911008011050000e0f41c8544500522030f241d020568040ea84e440da0000083d514610300141941c0340d0049000b181e40090041c03641011004058500e0100359420060805620800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975815674 1250 975814424 975814439
    0x50327100606080108121c241401030209090106210e0604021002061302060c3a1103030103080a0e21060603010b060403060e121b0c12030711030106 65
    0x48400d10561840010322149000409070028005034040d001d5504001e040c0000c01d461141129048280c10000e01e0003150001a40e60003041d45101511040c2429001c00074030900c5c110503102603e001240d8801c0b00c40c034140c01181030740304940c28290000b000c0e5004112040c007034405100f513007011142c004c400036020514903048a8450300b94141e20b610040c01d010039820a9420b003c601d00d803602c00382580380341660b05001c03443c0700c800c0001e015590006007103405400c2840540041051140140003c0310303003030f81d401038030780510300c070a201002440819400c01d40503400f20328031200034401075802d5a183d511665407a0300200c0b5001e080c0100c0c020180b01503511001d08001c800125241d820342400495486442e1100040c0118000c0e0300d0207604280c655200401d840031268813140110704014507510383e60400d003011207a101c08540200c0d4104c242ca05c540729941070003075004126520140c0c544e0401a9180006600011036041006a000440d40640a0b00c01d102c9002c1d0021074040d135105d10303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975816924 1250 975815674 975815683
    0x1406060403350a1d01080403021c090b04080601030605010e060d1704030606080d030e2116020d0b1e0c032a041e080102070c0b0d060b040b04091803050327 68
    0x244140001c04005413080b0501801c0b400300101c10081c644501d8034503140e40e0203952100c0e0929040e8002d02d0a40902a8240c409c18005016014400e5010380300da07650032201b561000280000c80c0e000d4245800072801c4965114501e1290400400140d581036a0362110800c1080504007110080e5040002202088103800703884001c001990003400d441c0c2003c1c0e0010f003120346240191100d03802a03402d02d400c1d50212007a0a001500940700705a44946c6190422480030007940700075046146440c601c400e10544224052055070b041c40b00b68241851400c4507071045c42c0880b8a1040c9400074004a51000c020407449552402801440d0000804144021503190800c2c0e00c101400c00310b240601141100c8a205e540051440130029030410440740c4c1c42c5500e41005001c3c1c80008000407918054100d00350708040014104400322642d100d0700c0b801440c03419402401440b11060410703107000001c11074002d01041168042c0d44040c1107442d40c4000a0701403485034032440c1c1c1d2907448045441402c40600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975818174 1250 975816924 975816937
    0x10090b1902010c0206070e060c07090f0b1c0c030627120e04110318190507050907020a2a18050402040c0212030103032102070303140606040335 63
    0x300003a10a103a00000d003500c4003110340204541000d000d110003141c01c00b000354003048040356400d4481030090112490000182d018404107400d024a81481404039070006c448100151041411581e03003445102d8520f110303540040020310390217400c0000c00c070b203030703000341d540c030302941c140b6840908100140d480b02a2800070680d00c5054821403c1e80703071604003080908031401954184100d58071414040028040141210080408402110800b990a102030084244c088405004085840c01c02c103035508581d000f500c0c09010020080740c02103000190301c150050b845541400d004042e0a0700344100e815245c0e1402102002d400007245042e141a904100952040800071b60303440d0500400040d554030300c01c40425500f1102c03c0102d18a01c030000c5030f040d00d0f05400c0c030b840a4020207c05d01101c0c0410200802c24a01c080390000400d64142c0210750600810807071010162290303000c0040c0340c42248401400c209a51110300314038003003421101401c03aa681000b80131144e905e000f9110550015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975819424 1250 975818174 975818197
    0x60c03060d1109070806130e06041203062c01090615140d0f14010b04081c0e061b0105061905010e0f19150e0a031e050f1b0f010e10090b 60
    0x179410044a420b000c070b0141c0440c0701c455803d000c013a49042e40192604805480030b40061038440228101d2402600702c03000501c611826804640c0c01140740d0100c0348038030300c18640c1c810119000000da10f2483e02900050b29542030407014440004041030303411004105e4080c5640c030b0180920b448800c1c031031203030220710810f03620003003118420a0460000784005801c02c4141500034402805400c1d00003819100e45c5003120f01c4040d0701e80d00c1c0001030300c0054000b1035481d88071100007898201d892a0a00380168600d52000a03c019129101046084c141986e50030700300c060480c07010411580b20340d040b400c2e240c101900340c1080f030b101d14000ca41c0b0206419a0a240b01c410010104001c003074040983c2819049440d0201d4080303141e000003001d8803c2448040d146003010290092903c4515a16401d169805422200704c0610790300c0194503018070302c0001c0c0e10b1b0040c440e0440348504100c81881402d11050f9180608141240e040207a051103440c103503030401200580102d0681080c030300808405060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 975820674 1250 975819424 975819437
    0xd0c2d120c090603030503010317070b042a05030c19080a06090c1e03080705030d0504060e07120512031012061e140402101101060306150503060c03060d110907 70
    0xe4140300c916004180e11141c2168a0424200080380d8003c050340e06607640180f0428007076100040c03411441c010528040c014207000030a00042020011681c0c4902c0b64034054590b9441d0031441c00c0101c1c100c548952030b010b40000340c107425240b034003444801c500850f030007610b00d443e070325000385500e010104502240c3c10b660780d11840050040041001d00109030186101807100f1000e01c03050f0b4011554800201010004100300042007014004c2d140343e00702d5038408000d18905800e015020b400368801105c103e0107a4a0040b03440041c020612607580c1d0810010100b0080d451603c0400794030040030102c0c0781c288031401040964031442c24144075405204042aa80c10500106215420540c4103698091405007403000102303000c12610f500c1901140d440c407440040301819110f644d42c1400a145c0e55180584c08000c2005991040aa4070b2846142c440b0260311141415515913080d0742001c95042e0900025020385016985956103d1041c4110039007112202c0104d00404c1082d01c1c0103003c1080c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 975821924 1250 975820674 975820709
    0xe0621060d1e05150c180109121110030204030503120601020705030d080a0c0504060e12011e06030b0603032503050403330218040b0a0e0f01090b0d0c2d 67
    0x3c200711a103488044c52030008090f0030010400791807807045055600701c8545000000031140e0298404070020140c00d42480c45c50030807468192401400480301c03e1143c1503069808205d20720078420b540640358044000c624200701ea140c0303611000c000500140c1144a00f0402040c0340d02e09100b0080e81030010f407101443c6061900f01e80c015034444e0705144007082001e0004000722a401251100d0382002075502c44481040011a9805408000080b50f10305502491240d40159150322100499004010031030780c030388444040544a1003443c00c000d60a107240300018600e030780c0711080e905032244a41402c514040d80c83d41c4260103d20f15041505100c00c0c0c0e030a0440503c14010b031441d074094000304d0114a00003211a0600500720b140000301d0203603a440c48000c0071034992200c035074080e014041003002c2a113030504841e828007100f400381e0008182800301402c0d44ac1440c0c0d40d4a400554000c0340151281e081c07a0720f021070545141e0641103008901d41034150078896201d41040a0024038800586195 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 975823174 1250 975821924 975821933
    0x90d060c0f02010c02011a010302071b080a0203010501120f150e01050c1213051b060c19050d080603030304020f01120903180e09070909020109030c0906060e0621060d1e 74
    0x400c4600313010150390501c00342c0e45d001c0f01d2521102c1000c4509081c01604c9002900b09800701858002d0f03004034460702040c022450710800034001c0e0466100310b00030302c05aa02c03071406460350240310400501e1451041c080c0c4d400a01803000c1a120702004c02c0001449620303210096003528810b807403144554100080b100c0c07003c1c02455940d03038800040100d1500300307421651210b550381040034203281150407103074407260b840d541d01c000c48520034042d0701107a80c44035945620209040f1100c034203c407240700d01c00e040710207580240000c0348200740040146081d542c650b02486002c031080c0c00c80c00c0c10404d0a013410300001000344900222280240d4030090121903110358150000240d1f04815160820441001b031500d800041030403d803804101c01060505e82440161000107643c1c000400c0c1485614010440510302e90000e41150384681e24200c00f81001c00500455125549143e44604e103c10050700c2c0c10030440b099541c1000000d00040d6425069031186015005c5c2e9910f6100c0d450b505820040501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 975824424 1250 975823174 975823181
    0x60b0405040f1b0e04140a1a030d0504030303180602390c191206021210120f150903080a0e0627070e0a0b040c05030c0708090d060c0f0201 61
    0xb04030754008104600026190f04243c08000d80c1540400003580c0900c241a25160441d2042c246914200e58440c10000d18103009094074601003000120100c11030116483c001070b094000045540300c0d02c0ca07007401d54504401515000390400c035522080380b1100001089032001344402601620700d101c0304904107100b1054220180c0d10754840340c640c0400c07012188408039480f060034a0484016903040d48a1202100c000b501d41d0000e010086110424070a0048a80082c2482c49265207040c3d0b05950f1085c260180440d540103e102c58611100b660700003421200c09541c83ea809071202c544901c00c2540301c801600c91140c821000100310100f0712214402a0007840389071b0100c0006401c00c2d103007003451401a6140c0702d0141040d1b540c0960b5880e42880c0c00e02050024240111400c549454028060400303070080e191a94041c524000c0030040452213901544e02800a00311043e240c582c9603121030703010f50441060035230700403c000d0742200010207900c41e00700042e0450721000715440500d60045d084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 975825674 1250 975824424 975824441
    0xb160b0106020309150705120c06070f021c050307110d03020c0c04020f0a2616080630190b010303091a0f0318120d0c032007030c06060b040504 63
    0x81d58018420803965903205440300d115015024101615a030013814031612300401c001006910110020700640c0010b03001c18900e20590132511440c6441d08005000c80e51100040810403000c45a0040155858803440085400540f5860151101400c012405041c11822400040403a41c00644e040940704113100e05003080c2004c0390210b01340312011500017141c0c4030310111a02002009001e450358417869940382c1c824045010541401c92030082d104e916200c40c000c0400c03005c282c0300e100140740392514140341060a440203072000d40d0403400700c1d000182130940e01e030341c5091801008052000050311019105806000d03001103d1154514103004d8134011194114142039011880d140c054030481e0320460310010004120710b0380ea555502100c0c0c0d10b010340c088001c075041c010304440801d0600f000c00035050020440c10200142d144038030058040b540101d1010b000c072100c80010a4506124501802040f8020f04000186100e00c0e40d4190072070710b050b0800103041c0c0000c038050140c1e05041c46010300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 975826924 1250 975825674 975825677
    0x71a0313240f20030402181f1e090e0a050a1505160e06070c050303030f0a1d120c0313060801060e060f07020d060e010f0b040b0a03020603040f0501060b160b0106 71
    0x1c1c004680b28003001ca00e0b004260f450641000002290441d250013913080c502d950b00c0107164040d03003407125282030501c8240c00c1105a07482680310220f41807000720501c101000f45c104102040c0c0d89810000d1001d423260243e1035100c0e01403564010045541888800c1c50340e0701c289048030f80d104003210300d6004c4500281881841114001103080032641107402e26040c140c00f02c41c02034503218540b0f442c02d0020910780010390507000200a00c004404041c0b444c1d070007956008414069400c078034038024900408014200c0460b0f001442034414080c5000040511291413000d40e881d0900740c00c8041c0600c07109a0103d000540c080b401005401d600000d8020b02a200b00c035282c1c41d10180f0380c051a80e6000d2000041c1c45170a11391004800c0260310b60242c07100d03600758402804a0b2000100b10402010080c007098041c60402e50008581c0c5000315a031803d030396006101c07504548590700e43c405216007601d02181c1079982d40754049649558003026041c40d1f075040c1681c00038404146000c000983c0181c8c0401c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 975828174 1250 975826924 975826931
    0x15030212090304030c032015120a2007080d060303020f16030804060806032a130b01051c0902033f03070507051002181002071a0313240f 60
    0x4c0041c51000c2c001080f81d410914030104440c2020503281d0a07004035810381e03400402c42c0c3c41800c1ca281d10b81d02400d4202c00e0002d03819120f940d825018019150224021000401d02c4030048420111303000141c5a200c8c0600380d21410000200c0c84142120f0b201d8000340d0140e807000c403407940001000c020420800100028001013640b4550300d84605002d94080d400501c07001600185403510100100e03030000850880381d070008100030844448500f040e030105070040410900384800395086001d00141e038503040e518180350000032a0001041240c000545000b943c503241d04002581d0100300e00c100304010b40e94030100b6040c080b1010070207004000d0801d100b1030180c4180071000368260301603e602c80024103010707a0b12543c928040d4104405c1310401c900483c804903104654041003803021218442c2600d81c126010703082c140070390b583d8186104101c20703001100404010b0591007005183c10040c0c1c980301503403404166580b120365071001500808150020045180e400c03006000341c5403116412071003003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 975829424 1250 975828174 975828179
    0x507020f0411070c09020a02010c05091005091503100e06040c0c030509042c0106051f030f0609050411010915020c06070809060c0d021209091f15030212090304 70
    0xa10140c0308980c09074851030b500c1e1030101180c0c88160480300002c0d400300c3c1c440c036a10b44032900500250403d01840300150b00c1c0c01148204d05000d07804450f14030200500e180d00b03080319080211417561180c94825080340314507994030700c00c404110145025081041d881000b5604082c20b40a40f500c0060080c0d00c900e0801032505901e542040603440c19036054600780d60780d04071030004280a00031101d061702042102180c0003080d03030521484001302c07014800081c0590b82c0e1ba24100100200e00414044c5920101c1d4201010700e80682e010003215002e40320b0200d1102e40e11800c005c11140c0441f01904c40e001206d003d41d51a6071b00089107405400006d80b0a8071815200308000d41c0c40d02a85071450007030000156903000e0101080c181c4400d4400106181d50b0b82418019290319014460f2402c0c001d84260654603d080c810007050352130310300c0e0243c5801141d54444410312203115401c10050b81d490050580030604c1c0817251a801c0e21420580c81c0543d03a08840280204c1c003071401400c2a0700c903007003807105 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 975830674 1250 975829424 975829429
    0x140c03062116170f0f120703090b07060903140f040b0708160f05010e1b190b032a07021c050708070e01150e01021f06050409080910050702 61
    0x241040303102031a038038400d032001d84203440c0e1400c0081d0304003601a984448001546040c0b01600700c85444000c81070740c2d665011454180d03691681c841749400980c00078041e80c0b4100c641e0401404003a03011780740c2a20750b140e40f0166070205522200b01600c08544a0381c4035020301d070704401e1421000c410381c03000e2460a03803d0642e105550043f03024a1240e004001031010500c1450003d403020049640d8843d414001c003840d091541100c90201161103500b0600783c100910b0020911400d03c55000072402c621661400401218458020fa403c4140c44030842c0071030b040c0c107403101851244001102c14519040d05200007000d20b120940d2540e1080f00811040700145c440300b42c100030b00c407070b5105c440c02843c0851400909051068118100601c07030303544001070109041140038100c880e0b144420384a040d00381000c4500b6445882c110740036900520150b8110808200c82146d84560440c0000e5013546a800103001c1d2074046074280c2e0300c0c090108030780381c052410300701c043d1091072a81041454500144d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 975831924 1250 975830674 975830689
    0xa0c270909080403020a1202030f0a0f020f01120501150e0306010807060302031b0d0504150b15030702010f020309010218101407060b10020a0b060d030801140604050d06140c0306 78
    0x3405084544440300761040005040669000e0f40c1d000b0407070035030f96032110241521050440400e910034407a10440d0f070901030001c01c0c0005550307009048002d8200740c5409010903180d8001903a41080444e400c810344404452003900d0180c4004001d2100e00c136150705000b0b0406402c07050071813107134100c000104082d0740c0c001408021181c02e81400f580780d40c0c0d10703d030340824080080c000401404c40001d14003101d1250354000c46c402c0748100607108046201405030300c12950442d036280d401c89080700305480c0d4488040040c541c814594400802c502c200501c0f84c509030f0700180e070400101c0c3e4000c1600001c0810710120101003610548141c00c14002d0003100811580b0302d2042150031007000600141481600d400c0004003007800381400d110000c00d81d200a655100050060701c8000e452004030b2803e1809920795061181c041da60703000540d08000b22184039520070000c240d400305081000141d0340c1c4552102e400000e0048000150103110f5071203403a0400f070020003800304c16004104001040e40d5454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 975833174 1250 975831924 975831929
    0x80706120b180a02040608130503030a0b19032102031201140613030f02030706050c100515031c0e0609060a0509030c0405090d090b09010903120c02090a0c27 69
    0x4021407403030414808151581c40104900610409900401c40081c0783c64004000311354a981d41d52446c0d540c1c0d08051240c12081ca034009005030010400709240300c60071340044054010050001c1420f0b900f01c0608c51030302820343d00484e28001c1000071f01410007840000000382042d1400510b00c2c104141c9843c0c41c00c44414041c0c451414190080407405881da5819541c00004803c81511110b85a042902015031070603403ca10910441c0e0000c6804c1e482042074403c9000c910004081c0a02c50055000c060b01c001800305014034030440d141c0f00c0c1c1d13540810240280b592039203014046103040b110020046110070520a008000420200c0f440d5101e400c00c80d485c03c40741c0e14181e1784501410780005d081006e010b50a56100b0f0508042c440c0901010540c0702c10a6043d03224001c201e41d8408140b0003601460103100d01041e20080204041100e90400d400319400519242d40e001000e13500140c42050b0a40d812040196038a0043c3c03c480d820007900c1c241d10b1480c41c0306411031b1107102c00c03540d404009070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 975834424 1250 975833174 975833207
    0x409030c0b0a1103180d14090d0224030603160506030f041a070203040504150315090302030708070c05040b0927010b0a03050105160503100504021b01051807080706 72
    0x40e400100300800c941d203c411000010015941c2e6810014801c624115100c1c01003100c0f802190000e0300b400b07001380610455039403214046400e11241900b000b00d01401c1490903600444080b2070007144600d0640030504210600b11901d80b0b0b1708140e02070503e49255012003400840d2000d1f000c4c0f103180d61740d50030703030b9032001180c8241c07212a80ca07071402951101d031030b98a41a0034040302080c000b502c0d1300031014205481050358100603904a20003170031042c510300d01c4040c0500001c43c0c80e01500c028a0b8000e888481e01900441e8648801075481813001c2e072010308181d40c01181000c0c1808280f41c40d00a8640502c003c94484245080c080411032010000b01080c00c41c8050420f00044058801e4224640b640c20040c203c60807941d0301d080081c081c100031a15200a011240035160072540104162401004880d16003040207003040c0a110095214101c030a4000c8200b25881c03c1c0c440007406604d2040520901c0441480c0500e188646000650b4210a0558001c01e100380700c01c5a000c403038a5007007040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 975835674 1250 975834424 975834443
    0x3070c0e04060207120804021f080613090c0308030f0601030509100e160f15090b070b13081603021e0c1c060e070f1a1903110a02011a0409030c 63
    0x12403401100134071980600800384804407640c800c5450b0040e0000744180d0080d00c03c0d0b89440004003480326804c1d41c01c08820003140355000414198280b82c00e82d086c0000480000240340321903621401003158060307204845d200000400c104100040c10360040c0c0048003801d05025900300044081c0d01c41d00a020003400d0a6a101040c02d1054000c0164940107400444150300301038446085961520290040302654041c8981e46400e40b0311400e411001ca4600704056410301460340d07102d801c0598094801400b1000d00f0100c01c000c904060010003046c100c00241143c41700720351801074107000c21034084280541032904186030542c0b0107c0d1005049100301ca0303123a8007000030310392440c0117110054050159032270301e041800c10b4480080c01f04290340c54000d07036610b059600c2c54040d030754896a2219241c01401800704000c03480035a064010410b10504021400286440e040101070b0010f100c00d0005039104c007008070400e01441160b420390351040d41c2c24022001d80b034034040c05011040701c3c01070030f8120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 975836924 1250 975835674 975835681
    0x4060501200c061903050906090309270a0b12160b0c030d0219081006021515031f06060309020f06091f0c0b061207050f030106080a08040603060803070c0e 68
    0x905001d102a4150020301580d01c3d911008039107030407213100301c0c003040102e0b25050105002c907400044841c03103098020003d61501d5608000d01940404809403020040c08000905142d6840400482e2150703040c1280021030410b400100b0818100c607000200041d081810b4980030181c2d804008030945801d403032607543d203076002110203146204500541c992544046203900d000c403029450320104c1c110f144e0b24090f85884a02d4100404240c0348a00c0015901915441c16010240c0b49a10b501c002000c0d2280c2580c034410f400710b820311124400609a0340d420702000308444040d4480d200c040d0080385010000c81501381d01140c1002180040b492141c50302083c0b0784802e50302c4041000a00f00ca41c245001c10310350b12031002d0203140307508108480e5540d40b0000101c00b41401645140552502001400158604000d2040d280310110342150195201c41011940b14010402903400d58400c01e000b41c2d640f4503000c402000c032101900a900c090300100085400f003410300c070440e0b040c1e0b0a9060b0100f265107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 975838174 1250 975836924 975836987
    0x3161b0204020f0403050303040804030c1a070b04030e060a0f020d0504144506460303020c03011a0a1806091a03060604200c071a1804060501 62
    0x200e0303000506c41d11002080208002100c006882100d21030324070510b4ac2034560b01c2c000314600321002c0e0800024014008003000c15025076200d9002402400c005100c007409101140385907203c6841000420f224000c088943c0380e041111040c42112031030304d18101418078034007403035412201858520400c00030141e80010b07000d0014040c0e0056140c0303500c003455044440342c03181c44031a21101c540d04044400c0014814148030002c102c80c14140f05491009001c0d41310041e09006403e0321a01424100a01c2d445a0300d44041a000140d4041c0d001085030a40c220201800d48850700c40910052040400591184c0c039582e08000c2510320519220410340b8124140d04010030007a030007022041c0c2419410001040305201000300f40c0c60030741c160340d0281ea80000384016142445032001a0796018100841c0b0382c081c0ca405411000307002030594030340950310f1f0740c80312150400c44030701c00c400380000803491441c81c803995040282420641d000d0141c04c1c03510001a04003411034400080700724801800f1138402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 975839424 1250 975838174 975838177
    0x50402031012150b01081003021c0209130b1003030c031b0c030f020301050f0405030f0a0c0b07021e070f0605030a140702011d0705101b0b01030803161b0204020f 71
    0x248560a440800401c0780e00300f40c102c01c122414441241d503d803a0300383c0d80035441505228403c0c4030711351002040304e14590030b020300d070030003124907440d86042031001c8401030381e40710311f0a8001d0702c80c40d45082d09400300b8100000c02000140440d1201a001001080001d422448150001c0d0b054140804045008000034140700c0c2d66281c010410002c2800100030858240d07400a05035009034000c025030307503034032100311101c1c00c2c1914080c0082d0300c140500c2c04c041d0450030060600400c0c526200d8510910396031100c9520030305542d0500035800c1250f41d103d06441560242c2d081426503c01004818034200702044100394038012801004400800a45507988603001401104100d12040045241c0400002c2c020012088443c00342e07004620413a0811400044003019144010501c000c0f0001c4c904040e1071070030710710707444810021400c00607001103006040703e0790003540074208103607407841c1522040c0c241000d01038a120038407004840d91900e4410581c2210f000c03650540f00113a0b81c00d441c1c10140f015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 975840674 1250 975839424 975839429
    0xc020f1002160c0b12150d02040e12040906061e051e04230405070507080d020a030e030a02011a10084006060602030906030a09060f05040b180d090504020310 69
    0xf80b6094000018900c000c1000170308030710341944804040c2d41c50341281c0b07450f8500784c010306075400700e01078521202524066101507541c02a501c201c8100941421080d00f6a42140d4001051241d42e00c908100d01a00110001820b40200c061408804000070002e4544c1c00b803044d1003071000159000c0000c00c070f000003040f2409050310480c000702010b424420740081103a80c1384100e0040340de01000c140311030b004a0980340c00780d0340b00e0021401c04444e44c080800941054540004140c1c503500302160441050004001860072503002241c56111490002c030108501c1e2800d80c020222115403510841c0c1c0724032401e030001101c0400c0c03148000b0b12140d0903042c1090046505078280304010508140411203181002c85200754070500002d5682d810580c0c60380694158960000d6040001031403241980d0300070710f043c1e07214036000a01c1a82d80070300034084a030200c0f812a01410076109101443d140740035030865109008000707100c45814184001e16a440c184201ea01950300440070030300300000080c05001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 975841924 1250 975840674 975840683
    0x1509130b040f09051b01140a0e0303161b05010518060702030a0204060f170a1a0711070303170a0b010912080702040903180905070807050c010f0c0806040c020f100216 73
    0xd03d41508040703441d030260f42c020408020354070900380c0265009004100c004c0750690449800d1514001c02911640c40000405034940010031400310103084c031086411240e401414a06d510070300d61000c003c1a030320283c000d03d040c00400c1c400201910950380e84c40003001c40c2030f0f0b0000d41711034a600c0800c4c030703010150000a5005080480101d148110b10950704200d031203803840c0c400040402d840c451313240c0f00c5414010b0102c4110005200340703a1106010240c100b055031034008459910b541d4214100809078004074005400d65143c2d442c950545c0148581100442004000080d01500080d008200d1845102e4400200b02c900f1000e0103070710780582e0035094000e44140a00513603464000c01c01540040d030141e142041100108091105121700c0d40301c0c0d412500d4a045607143c10384250380581001c0f0a05000b50f4850210301c02100480c090980380300c2c800c0c0c90351149420050f04010a640a41c81000f045600a41028000340e5001540c82c41c05004207100580e00d51544807199086802d240b000352 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 975843174 1250 975841924 975841931
    0x1c030b0a0e070207170a060e16030602030105150c0a0b0c0d020414121b06160503160501180507050904050a1e11090402010806191e03021509130b040f 66
    0x6226040d910110311900150f030940f55101e03103d4450f90300c002846040b41e105940041c95100008031290300460640641c1b404540b0400302d80d4401002c442442d41007211703e2500400100080c0c10b00201e030300c080b203001a034402d041102d14030041e070b0741c1d41d03040401600d0704090b1404a00d02e84c120404030740c0c2d007409142c4290359440d00c0d124050b28046201c0500d03805800a00c0310756840070000b01d0803500d031509100070001c280100c0d40800080d030304480c44002050b0342e409500700002d00b04100504e00d0f04009015031031030401a007070142c02c407460300e4800748101800b9030159000940c0801d10105440040f1841d148544460a15034542820002e00500c906210104203448138a14515207140d07502c2080074603143d40016003440303264441a60001d001c100d0880c041801468102d14010b02ca02906541080a41d500c01032504001118843c003100f0030745000040c015800c010900c2c0400181d400c0403145440e46000c0444c2c11118030314a5100d45a56920541690b95036541011411888111060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 975844424 1250 975843174 975843179
    0x6030507151e140c03090307050a0312080703140f060f040203150d0804031b1406040302010e01080a0f0c0e0114030606040302100c061e2a03020c0f031b060a020702031c030b0a 77
    0x111703980c0c0d02440c0000d10900c03581c0d20000f010314040034181c00396940494010355580001c4400d482d0b200340036040b5424951502d040700d2442c0311000c3d583e803003040002071200240c1410000c0c007031003883c00340740d55008a00402c100030b51420300b404256000700007503448085810860910388070074012900001c081601c00300c2d6040d00c00380c2071541c1000740d804000c42c4e1062060700c0c03c10011507104900c40280800ca40031101ca101d580201520351384810201c030081038505903034941400b10b032610a00000490f14510301002d40b5603001c080b0105000c084582d05155050050010300913006500c0000d1140548042d0307880c25601c0344880c05031240d40031005000c9403640304400d010341c0240400300302c07245281aa02443c41450b403680340131407084600c0c14040401070110224060342c002407208007240b0404500b8800d080c420001001020301d43d003c012420a81e424940c4d090030000380c00b0f140c25600501404001d650003080c00c181000f0702581901c500d41000b0810fa01400301e11100a40c02400c20100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 975845674 1250 975844424 975844447
    0x3092a031b0e01080c0a1a0d0c0302031807030c0b03040203240a110702010f08060f03060c2a0d120608010903020109060e010c12090c080a0606030507151e14 69
    0x82205907401c000306800160388518101c5d945103600da0005500078094441040400403100d42e15124400031140c1c186000b40802c038601c10b940c904280c000000b13500004200c8414840c0c801c5501501181e800340c07440c0c42c80c507101d100c108400b500078010701c00000001326003150307404c1100c050081d10011002d0003201030302030320344404c2208036101403140d1700b88103441152a9900c400c4070120b0381d05031903039a13840c8840502164201002812550400d000e0022030019036000c0242ca44111048114140d8881d5900c803590030a40901c00c02c0424001c40d240b040c8036044e0042807801c0c80086918017409101882800d08000d1711003680001c0165180160840c1810340c1900003120b8280611010b0024081c1c294030036089a000d030171604005000c080012444007051340243c82c2a60040c0303031002010791030303112850401a03002d0702242c0c103036541c510030030411a0620890004141c401035009145242900103802c01d03c06050043c410708100c584c0080c1c55009001c42003054803109115034548821049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 975846924 1250 975845674 975845723
    0x30b0a03050c1008070807230d090c0b030c07061104050a030b040201020d0807090920040b0301210f1b08071503060b03090c0913061e0b0103092a03 65
    0x451809a0001d07210003d0150041130458050106542c0d01d4140f961445421180310005034104540c007603011680018a180300d00c0035204140c04c800c800100c0303280c2c52800c00500c05d52680048034145051041286019228065403d130356009440444e66200002c1001190308c141d400036603200040550100902800c1100b052095100307800712001c141856005455000c0215000b00000b11104014008140550004803400d00003404426040311804a4000960060b0b0461490300c40080010424070070007007607000ea4041c00043c0b0005c12907850301c0356180040d400750050045000700502030110070203140120300401c0307944181d4108644403440451415829200301c40000e04008020442c8181032044030f02405070003000349140305412041c0001c1181c014a0f00400c076140b0303940701022850074081c59501d1050110940b00300c2180ca4a15021036a01d20540ca0405190480e8100007812800d8400807813030042480480300d15146003580c06800b030719000201154000440003880070807525 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 975848174 1250 975846924 975846943
    0x80105310219020c330c0f0d0804150e0a050f0d0f080c03271f06080a0308011e0b1612052106060405060a0c06050601141801030b0a0305 60
    0x950200d03410b6140304102e0707031000314002c8140e0008a19024441191505200c0302e0340d240c40140c01c900c441000b0007110000d0f00280156651604041d1500403400c0c4148180c42400f0480c2c2880300e03441c146615404406030241034a80703440c5650303011100030354004110b1400714581c010102c402c0008141103103622101e10000c3d01000c918107858204c2c45600906840780704200000d030781402c3d50f5500074030800e040c1c00e00d40300050460038004031411084007408030b14003403007500e11540890303058018002c007240c0e1702c0c0d8025007250300030303859a00000741d200214504460068980345008010380c08000d032110240d80c0100d00500303001590200c1140410b10303a2607400d000e008944c0c2d011001c0b0714141e440d4490142d0a4030300041c03821003010400d1880e1121368101e400035240d0b81c2080e45a00c040789081e40525000d0f008124107136010410412507000c1c0d00d500c000c2c207107410800f6000d06100c2d042d0f240299800d22800c0c80c0304625004299101c1d50242008d4000142910410707692410159228421070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 975849424 1250 975848174 975848197
    0x606040b0609130c120207110f0a030f0f05160503030d0c020f0703061d0c030a122a05010f1a090604090b0408040e0c2502010e0307080c0f0f010801053102 68
    0xe0b1282c2017100c1152003507400706a01b00820341c03a10409802040b004202c004107003688203484040100200d54004401d11545110b80003200c804003030f50070102c0c070300300c0042910349807403003408018003443d280442641c1036484080340104000041078416170038500c41005504207445203080010511034542c0081c00c1c600034215203080c640180ba0681a01d17841c0301d45109804d68040c02c0000006151001d204004410ba4030344210102a0040c855561040340640910a0b40607100c0c407000b03001c02807043c4140c103000d40c2000c000030b482201014180b050114801440307210711200140c81511150409503009501c040800910314061400d02d0594101c2e0003418551010500041e201c0c00f0701074111690301020302c1d00d025051203c0c166000f010207000700128100902c00c0c0c5032468540f0200840c00107800d8440160564800c0c3d070045c01221441c010702d81d4400c4424501000d001d0342c10080c0da03410340b85d058650101400740d81444145030100c81c0b800800108003440e04a014100341c1d0302801406c01407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 975850674 1250 975849424 975849437
    0x30020c0f03010e0d08090c060403121e09090207081e0a0216031e1505150f011e052505390432060102070803030106020606040b0609130c 60
    0x314241400c03201400b0b0503402c0e5070720003d12084030724040d41c1c086501010031000c540c1640d5945d40401d6403034000d80c0c4102c424a0030140c1c4000041d800442342040700c00d01a00c00d80041724a0301e802040b0400910030f0a5a01c1c2d80004c0389c03001d002c412021201c000700c40d03081d042080024107107000d507650b01421190f40180140100c84640c2120340c010f540889400c000c4009050603c030719030820300712540c202200e9054104010344105400c5000b443e1154200003400f03113070006c541092180b5588100d030180c0c1040340c80d84296500f500e441900a00308807407840c05944070307a07403102910f0100402d4450b60404410804a88042200c005904481ca28100d15840e88098021001c4680d4100c80d12507816550883c0310400c0160400f80d21a0440c1c030004c10041c1d020700c1c4a1441c202003400b9880e00100096006800c000300d55804200820060422900a619544c07602d28020b4031800003070583e81c45a901d0b060583c209980300c4080c2c44841100524070740c072030b1100003000e1000340101da0120010940c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 975851924 1250 975850674 975850699
    0x201120f11070c151d1f110f0f060a0911090c04090c08040503071403040b0c01060905010b0310092307030c02010b040605010c03181e061101020301030f30020c 70
    0xc2c00d030900007403400980b10044015032803480001741041442d44950400300490005445c4001c69401003000c80060b201c030701700c3c0c0360751691030340c100b188070b0400c41c9590b44101c0034641d01d20000a5090b500c48051040012804080d20b403a025480aa442144d840f55041c010f000164407000020421107148500403c50320307206c0c040039a074051084501400c160024041078004c03039040d0400c06035900c075100c242c0345040d03164880314111ba0443d21030303a0466035407803a080c0190300540c8aa98054940c04424504515084251403906205406028000ca498501d6441c1480c564500703107000c80d4882c2d020001619090400030300411508041c3d030015800c4c5006416103043c280b10741429100306070f40d1421b580000f13840503510462020070501001c5602100020b41c078201020606000b2000c200410b21549080001024030b044030b8101080ca034810001000001d4040c1001801194446118000342c0c0e80c40303004206020080c0c00c2c80060640801c1504405a0301154152a8000482d4800351101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 975853174 1250 975851924 975851939
    0x60f0f030311030405150d0606091815170312090a2f0418021e010801090c09090603350405090405030d0e0609071707050103090c08071418130201120f11070c 69
    0x1180c4bc07048441a030035030704032010340e0140b9412a128490400c14584c8031b055540c0034102a02d104864001d88039040031484c00d144107410080c10307070850703416001000c60205545130301d003410000010300303980d8800c02c0c28900c907680d8501c0d0000700114401002000205240100c410210704043e2040b44030f40c900746144c85030000440c804071400001a0341c2d003509a805c207a0010010002d4004060034404006e00001d258405800f8200140d441015103e19510070080c00c04150038070b20702c04480039042100c00b0704401c0003038015a021144101c0d40a00d4136200c0c2d082c0581948a00001c400400b411b05e03007030038126200002d005024000c444101c0c0c241d56642c00245002c0a1340e412949901d80218108016540c07094000a0101c2c0c003903110608010f42e102401c81c5000c0c03483c2c6c4803030110510241e282c01e8600d000c00e8140303401442500e102c0760600c3d013011054104112290009e044c08100b840c0208225540d0340000c0724040710740c101300301030b4040350352400711a001140c003204c3d561100d400c00700e43e03003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 975854424 1250 975853174 975853187
    0x70920160b13050607050a030603020901080312010b031902161e020a080f190309050607110102010507030218010c140d0c02031e120702150f030703060f0f030311030405150d0606 78
    0x443e0044068501a10340d1841210300764070603050320081503160070020000d40c1e1041c0d125030007480614015036441c204c412051030704034816070000030318044c00c7c41008024060135281e41c0c40480000e200507942d46034105e600c41070981120001d4500207a01c1c0c00c450400c0d16080da905039042c000c603542d51405070380d1001141e55506205440009800101c82d95840702c081300c074504043e602c0790030700601103519280458050303003065605a40344c45c50141d018641d560203109041e0010300500c1c0c03d610b08940002e0f40e5454041c03212040781001880201e000903c00045038000748000e149050300d0002c1f84403a03000f044c549810324168401c3c0603101c01d4240701c0751030703015a108984440f00a45256521b501d1481d0311904148426038004118000034002024010010181411501c000316201d0030070440013801c946090300310300c215021440d07083c4075002c120280f8104072a814a049499000c1e015046030450040d54840b9400c4280200030070701000000c0d0107801d01040c50102080b10350350302d100440f00bc = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 975855674 1250 975854424 975854461
    0x60a02030606160f08070f0c050105130e100302060a030c090b071106070812071e030507051e0f0f03071701211a18011409070920160b 59
    0x8040104059103c1009040c0f00303140183c09a00c03c920340e03500c0754945410340e030300c0824100ea003850680b03004000c1050000d80c410180c40d0a02c0d02d241440240100407003000d2280c010841006c50301390019400c207a540c240f441c0650303805840c103500e8107541071019003c0d00c8001348a4002c5445048040768000d040410b507000036810008914203c0180303c107010b1a58409901035552580c10044c1c0304140216108aa00510740c45e92405081121426403401c2c4112a50601013010700307040500031711a0f8403005071030051114054140030202e00302164a80e61146c0074800041c5400030401601c081c0c50305015500c100520344039091078104100320080260003d02070f40149184213082d0f550004044820040c17102d205a603a9000d09a000345440c0c00150300322034841d01c032804150396034401032003801030f0f1051082c9018018580e08140800b40c2c4c81d01998000ca0305001d949e080d40031001000303e0165180003005c443c680d07690740030319420f2000c070b59109042560300080500101e20403510303c18941c100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 975856924 1250 975855674 975855679
    0x6031e0102180f06180126040c09050709090b13060801050906070c080304030e040603060e010605010f0c02010915090e07020616090e0f0a02090a0b18010801030c0b0304061103011403060a020306 85
    0xa403d1005c040300020340c2007203008604101c030800151216102e410118400c9501100f440b01840ca444e01c2c00c200c0c1580715401c4040b1040c100710501098681107403445094903e5100f01048422400022030102d1440c102c8181039241801e40015a4180640c0124029800d241c1074400e183e443c400280c4090400003001854041c0c1000041c000c00d120380c048035031441c1e004001166040c0e49841e403500752030301080c910004c0e0359200810049507800281110b018040c074109030350468820340000c3d01c00a442d1140e15119161589114200c41c4102d00400c00f0701600400d2620074100114029510b000856020300c95900c1050407000d068064045001164092102d0560507903840c1d00004001402414085070250240410380e03040c1e807000c01280c00b40042101841d21204030781a4048480340000d52141031200b24001400402d601240010039601c00241d019034a03140d502d000d8006042d040d015003491000440040f600e46103804402405005c103e0881d030070740d215904c10b030040b4030081d0350055 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 975858174 1250 975856924 975856927
    0x9041d060606040302011d06040302310506220f1b090b040b03150d050712061b1b030c050d0906022b11010e07120215120a0506031e0102180f06 63
    0x1f95444800041842da183d40030b0010350400d0703585d50114070710140354403624030180700c059680103a06884145016002030400414042820003c01040c40c1d580342410100d44102d05d0003007100c0c48115500140001c1d840321008019070b2102980e81007a014422048600003402030b040081c0c00074038030b001d0310195160030b00c00e0761564440c0112001071514039505c05400401c0d001c10704000c50414070054008008041013404a42054a841c500b21003c000c140036004040040b004540e547c041e1806072024010841a54000014101038614222110307000b01507100d001a21401b41d070b40110020212147c0c0e03002c1319206004403401c10a0002040680701401101c014a40b00841c81042d800342141c08007400000c038050062440d03400c040503500001c901110403a800c1d021801d03c00300c501c0781c82031140002d5040c04c040c0c01c5030910800780541300314003042d203c00114105a509006c00001444004947c0c404c107403180441354081d4200c102500081100081c2c1c0c3c0a150405480c0d03000c0141c1c0051001d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 975859424 1250 975858174 975858197
    0x30601060305041e032a0c031b1703210f06150d020d0929240306070e0a06090302010c060e030c0f070e070507080d0b0609041d06060604030201 63
    0x110010a4010420742e01c103400c081311110144c01c80884100c1a80c0241c0e11303251160303950419a03206581d81007900002c129900400800304004401500a0340e42c040d560308000c0d00140455411540d07250400c00d10041310103003400301d80380000010044010150440e01400c2d507094040c0642d103004a6082a805041d840060348502d40070980107882050089403a0500c02c0340440a0100d070020000c031001d241e540c480c000203010341c884007044020040031448100b01c051074415914030344d0140001950022400c810201d0a00b120b001d4010700c82d000d42254510303d0140d0004104801905141d030003072140041c04512070348602c8000f4182c9070184c42701c0407500301640d5102d001f8250102058001d00007886a5000124148202940c000b1200004e281e20340c14030f124000a108003824030380a001c0d04001440000720118180d46403015070f41400582189031801040144c42034840701580726280c090121a00210308100031441411442207405a035100c0c2e082c400c4a2056000280c042400201c0d131 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 975860674 1250 975859424 975859427
    0x423031b040c08091903110d1812080a232101050402130b0711150c010e010c08010902090301110d060806162f06010308070b1006091202040b06040308070c0b0903060106 74
    0xf0f800180b80b00e89098422420403a50701418103041c890070800080c82748141007100c58266041001504a0200c1444410b0407556450518454008920140304003007490070000440058050f10308412684550b9403910ac41c4c01039100f5203542c4203e01c0001398840004152814603200b0340754880c01c030002c082c41c864104180b102080c1c102c00c03000c46201c402024003113003540300c00c9060260f1011510a15403906242c0b240203003500c00e0a0210240c0f41c1c0f50003000241240e004410604607600c1030303001651900e021012038007521f00c0c0c2207180c02600700040c0c82d12441903c4c0d44110129031180e405c0e1440c039120301c501d8030741601501d20403100040364054170004480e600800c03100b0414030000c00d00614400c8003c1c1030300f010001d80c01a14112004075020003800260b11482d58422010b40300748040d40c1c144240681415440d004005403401c080c0100c20440d01d07254081c1c1040035000380401e86803941d03072078550001c2c0d008a20848441282e08800608101030b00180d40c01840b005001c2c004c240c0c03e1050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 975861924 1250 975860674 975860713
    0x60c110c06030c07061e050103031b230a051b0f0d050a02090c0c0d05090a08010e0607081b1c06080d0903060903050d09030905030606060a050423031b040c0809 70
    0x4080c1c85d00f42d640c0907510080b074030503403104096004200011945625608000d819102d031200640c04035081c0225810008100e60880700381900d41c3e04110400203490058940390858100004040307208006498007100c10b1080d2620070032408036800e111030032a141c2031003032100301803a00801e990f010210020040c9070604c20f15034440300ca805a0f9060240c1c10590500e8120402100f8010a4000600440700e0800e0700c110405041450024000381c80d00030a505d0750b4540c000c0c524410040c094021554a4843c0845441c04003040300c40d07e502c40e20b03025201c0d600300c550806507910403864045c000507108008101c01942402c3c0d502e42c802d01c18a192210b50141140300d80480c10020100104d10380500c0364450950b01c46c1c0255075140c01d00381014141864140041c194034800d0f60184038140519500c4401c840a495660381240700000d0394465124621401842a0f60700d8011721125641840c0030074410300d800d00d81120b0512600340d14800c04d84005005a80d0920035400141c0101c24143c004032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 975863174 1250 975861924 975861937
    0x15050402040e0d180509040f022b0503040e0901050106020316030315030b060f1e1306030b0403120f060501051633060b0a08060108040804030f060c110c06030c 70
    0xe0000ca004003010400908000c0020b441d2808261420701340c86107100080005809080b054070400007508090b01c9554000700e69040017031040c03020515540b40f5070301c983c066214420f80010760901c01c92007480c100392207800a006054203041d4010019250910501455040b00e0490700a1840c1054102440c40010048070042e818151180000503402168032410402580590719009007030501408018822640d00d1149214001d120000406100d0b44140f03408a080b0480b044a170300c0c080035800c00701800c002e03803018201d40043c5040000345500040d6a200020401c90300b0010041d4003024a400c40c0c00b14080c590000b00240802c1120311003003560410340714050151000100e00b0404400345601c10325810584400d5140e0dc5415100c440380a004c01800c2e03d501c030541048062040240100401080c8038100010900401c0c1403007480d10480c1c000e0351f003250032001075040d2810024013034003521000b0340005403c2828030070321280c042044a4031050081c9510b1464482c40804081600400e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 975864424 1250 975863174 975863179
    0x90a030b041b0b030603010b1905040b1201090303050709080d050702010f021603030518010c1703040816051c0f09060311130f031122020f1b16060c15050402 69
    0x10802070402c400d001c03110500410b00881101d07034070728010b010b050031b442d105540f83d40078003203894441d0800d15403e065030042c0c0d13000781e03000103000490400082d50140d11034041507555180200c21000d266064000c035116210300d840300c401d070591714902c1e196910014030484002420074001240190304c512950013080d00e8610441d0942c01c400846460511a0b40c2e102f01c0108900003401d14000708a444150b012090901706201200c100340ca918414a9440c0003002e02d02d800000000c0402c60041c041d51801000e080010210000a203030480c3d07940d54100041d41c2d03410581e504905958826400201500001e959040d0f410745071550503009090015294103000c40c00307122800c81c06405108181c0180001c00d5264105403071424000000001e4103807050003180c9041c131800a841340305c95601d04100c0c0f10345006a031602e280f0200c0c0840c0c02002207074107800c02c8040801c0903c035000038100074442c6890300004511543c4070000d5400d9521030a00818080c10030b080400042e1141e803240340d000307001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 975865674 1250 975864424 975864443
    0x1e0e0c0d1d0604170c030318070312170a02032707050d06090614330904050c090903161407050307081f0b06041511070f050312090a030b04 61
    0x190800303042080240144411030307001c1010003007480041e04a5200804c0030802c0c075440c0003e80c03044142c480c0700040055034a400b458401000c410030821007800150b4010790030b48844503400380b00601e109140507050f8a103103080d1000c1620a482d9108803402000b030586414940012a144d1091a03004801c0e031043c10f000703091001915071111100c096240d4400d003000605140680740c070740d040703031159964080c041c00301d00c0810004810b0600307490611011154014044d01161324a01503100c0d8144d030b0b00390400701c4a01404100f120024418503e02070484000c21079640d9000f0303040e0350303009580b0a040403941103032504001c81c0ca80500e42014803516010341e1009130300c410100346010300c10790041450f5800742c4c0c2c8180c115044c0034010008608030f40c07803d00070a807030980051614003850141001464080d0114004580180350703041d50313141540c007660421683c0704280c0d103104105205140c041e014200400315414103680c200c4c0d031980802000d80d500380d820750b2545000c600000f0002c8440070030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 975866924 1250 975865674 975865691
    0x601030f110336030a0809030408010f0b090609150415030b04030e1203030f0c160c09151403060c031f12120f20070504151e0e0c0d 58
    0x14050015403080790051107514241c00500540f042031140750740000e40404004080c00d0451901004441d00b1920900d083c0f4110b4070b511505604504c2030345d110b0106980303084000302d41d40107550440c02c03640e441151514015594442400005031045502038803020004000841a00d41030b444120410550040145015100c1d80c8a82603800195015000b20344084a80c076464584090007006100d60080554194180300840002e600c4018000c071651503130110303980001e810034180740d000c460340025112400a0351003410301c0080040e00c0144410100f40e4601180c1402000080c205080016000302641d50369042c490b0a0b6400c080d0201c50009043c0b41889803001d5a030700d400e400f602c22040502d1492102d45030400040b92000d445005102420f002e007c00603400003800440d820300300600203540500b101d10682807003503607080564014904a005080f04100c91000c00c140e41c034004614841d0509010030f60a500c84a20171301ca10511140c0005183c2c505140c050111840094008141c460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 975868174 1250 975866924 975866951
    0x2415020102072a050a1206021b1c0e190302090619080d02010614010f0c050c031005010e0603070b030705130510030507021b1c150e060414010b090601030f 68
    0x81e80100c1c0e03103a0082c3d00442184071581181003807009010494002c06518a0082241411004240c1c0079145a81c04903044800c040d44171003080c0700b81d2114090b90441480041007102140310003290000207101c048503000070341000e03140b202e00807145502030300b640c40c6140d080142412000305070b41c3e00114891583c102e0403042210f100040d103217800207441c10f4042079400a003103420b02e91003c640d840d1890002d05d075a036040f08503030041503064503120401c000c50b0308000d0701d010950488203804d48120100007091310000c0e0322460584911a00d002216100c2e01c00f05542c840d610300403108405010408150b00c1d6001d500200b29a6029045516189a4030800220317080c521081d0720000c00e0b2520100581c43c0d0381800890154880b0805c0c0f80101041400420510001c0311a040280000d203c2c0b40f03424807541c1091060000706011051100143d00001c03180c43e03200949048030b003001d22120310000c0020601500300d010fa005881d6100668554004501401c0104120f144145ea603104021201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 975869424 1250 975868174 975868193
    0x20d0e1e1302090d0812060103020a080a05060f150a0e121213090f0e06060a080d0f02010b041d060c120c070602070506090c1206090a0314160c0306241502010207 71
    0xc0e4005c401654540c40b02c030403036a04140c001048241050710411401c40050340241178241c01031903c0c2d1000400340c0d5240302150340c401c4400c00641d030100d400c00d00002000141c1005140154066071071200d0303020140c05010b440840418045079a42015160901d007403200d201a000c40412003d541c00700301e07680c014217811140c19448801c006601c6100103101c4840801c486c43d0401c0c010745150054929001d03241c0d8680c0312101866003002514414040002e10075041640e403410001c1040110080e81b407900c03130340c002c0b140c000c01c0034502a070000104040c00400556004506100080341175688241844440340d01000b42200c10b07990038800724010480400141d80324590308002484441c4840040104044038400310000c154030403020040d140c40080b0306168000d505044c20100000203c3c0c1406040c01034440c8203159640c1c00c4c030341c4c3c0700b408000c090080450b070107035004000070781100c1a10340c079920004120182c035034110300d4204509448190000e04041c1c1c284001402c0072560340d0f0300f0004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 975870674 1250 975869424 975869449
    0x21503011806082e020d020c0d020c090c0d090c0305030a08011410020307020d140607030c1806170601031b02010207020f100c08030a0615020d0e1e130209 68
    0x103107075407910090070007682031040001402e006002002c00d50f00320070002c05000018212603103425502004101d1104140d010f0300d03401000c0711400e41d155051603003000d03616050000040018851038003904524104661514000c100e0f030341c109854941c3e0f94000e940a40b4405a0849424044a8001021940910140c420402e079540c131000954503002014080401d00c4843c04d104810b201d0020b00001d80000880302929819544814503002c2c070309010340d03c6c01d055491010907002c0c40d010030002980c5a804121000f0b12910f5103102d802089103518128030040c003820011454a419020603540c0e1028140e5121b0014500480c040d4402d00054540c0b1401401160160703401040c4001141b0b40b500c00800d44800a0302c0055600110449c014040c484904001d000400004003148403c445c0e170300000060b2035018103007030103048400c900a64074031420062074000394035400340a4441c940114454102e09012500700c2130212400d0400c490781510361480e04230a9801c0103688026210480c03103840c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 975871924 1250 975870674 975870689
    0x40b0a091701090c0b090d0b060a0504020a120c05070c0e0603011d0115051923030304230f060a030e0a0203070f05212e06140f010801140d02150301 65
    0x403064598031308190045005d03000481300c1c0d070040c8102c2c003c80d200d0850b0f0302c060707640110349400540c403408040780e005c9070f594211642183c0002840421281c028a100401d6003458400708401060b8210482c0c540c002c10310020214440311070f04002c01709104940d1504543c0060002480e444d05818405600c1c80e0b4503204650759450702c0c50a5654903442c0d00c600c005100c1501c1000c1c556403a40603c894803480350155580c40502e803c00d001c0d0b101d04030040c4c1108200c019003143e40c0d0301c1e00d0780e9031034043c08225040300318039030100380111b1080d06001200000303402c0060441130510300c0c140c005402500c2a21618062440350101c3c1c1c00140e17400704043e40c000c0c00c0714546104090704080038090990030055000e81c10854a0001454540000a07000186451203100d41000141088231442210b221155081c01501300100402c40c01481004117034844411107044d0a815114001591030100921603501200c00c11103e440c2c0b6400c01d4562400403e1004250707501545404c035000d0300c2a04281c21514 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 975873174 1250 975871924 975871931
    0x903031514010e01020102030606030a0e031201030503091e0f010f05120c030708061f1b1506150207030203060109050417070809030106061d01110708010f1e050c040b0a091701 77
    0x40799604070503081000c1d0380c01c2c4000d52540c80d180012401520010b031a042c14039a540404800da81070510690f4008100c48817100d505503924104503542e0b810101a40707100d12200050003426500d000e00c41c440d40e540c007825980508110f000152014600c00c1030500c180002006425212040d074440391b0311507001c2c000071540700e0074480300080c51080001c008500680406200801851608140840c00c90f0146041d1840b10709013010350180820701c0500a2809010440090000ca142d4114900342d0707a0604e03043c4001d26405500b01d998402c28840030750190403040044c00742010039000242d006001d030031402202003c015104e18607a0008030291007441011403408003601d800c0c081c01000b000103103004240b01d06807aa0010441c4003a0b03200740c1c18001d40e070901c00d5608505000c000b004068140080188a5903060510080c0502e072042d6002a0719080b5001380c101114030490780034220080c1d60504050074542c1101d116440071120741c0c180b0804440014178441d42010400c2d04000000012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 975874424 1250 975873174 975873209
    0x90f081506010c08120405100207031706011805060c0f06040f1407060906050c010605120a02190b0403140111070326060616030c0c06030509070b1c09030315 69
    0x40c4901a00903000c00e041107100c1030500c011410607400c0c3c4540811035a81d11119031101d20700345144c407100c1d003030600c94a80040360300c0c2c0c140b5402a51040d030440140c1c210090300d41c0d0f540011600301d0401d440c401d00f21410481c060000f410444054000000c5820803111180d01d4107001500d00704086030200c54464201040e80308101550242e9481c51002c0b4009224403406c0c408058034403c8640210030400001140d4512804800d400120007030001400568817400c508507444d86498640354140d01803c2031408901c1c1c843c00703c0c06400210341d02410418180307401d60340d0360220000303401140942d80d034903903400c94a414050070050201620a880d95a440700c04800039606101c0b07002c0152600d03d101c1010409a502c6210456a4005a011950342c03100b400340341c2a0f551114485005e45080c804640c045495501a81700a002e02100002c82e80510394441c9100054801d040164994101400c9520354000341608195090f611034100421000d52411a40010100c5540054802181d41090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 975875674 1250 975874424 975874453
    0x5030d0617100204120314070c03031d0108090c090c0c060106030204050117060a03020103050c04080f01020702090115020d03050a110309010f150605040b070309171606210c090f08 79
    0x11084541c0e024805508162030500d8581c021112801c000d807e0098072441c00c40c56914031001c130303001c8541c020442c43c001c0e9124200105080030503203150362034410700084a6034540c000c4a04174485c1004400038a030450f07805003803008018001d401c20300384400070701c118030340c6040a2000b14041c2c02c40e65001a1114a440001854800c85100c2c81c0c95600c1464248005502e455844405503030b020f09000ca070a444005202070144900e40c070956841c010030700010b40c0b00c54190000c107407450003150120398990301c0c1e03042d10913071050100320800544c1c002c4080c80b01c154001d8000640c00107400400103050301140b002084180d00849800308542d64880c20800684420701c90202041c44c01324010038081d090050142240c07240d0302404124142c04149501058841c07400d0740043d101812500c440b241071400c02c140e8809406000d03008d40000c01b100483d9842c070452004402410010194024444000c10031000701824007030a000c000d90904041250046048150010440380c8003e01206921240703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 975876924 1250 975875674 975875683
    0x2309043b060420130b030c150d0911040603060f0e0c1c031205090d0816120209060904060e01031709150c150c0c070b070c0612021606020c06090a0804060c05030d0617 73
    0x21207030322230110b429200c0002d8585000781d8085105603038001442251504140100513501c480259116051003004800c00410350480b0484074603e503000c0c008140403007601c588540c142c14a43c0e42003500d011000d21490000f43c800340400b4000d040a444003c04803242c0b005444044460912039444803800c0030307d069110748180e500a80e107410005101141040050100c80c503100d0b141046078002c80d41c00820340c1c4082c110351242e10014420031041343e0740c9000c800607207802d00c030560b007003901018541000c2041030304441022600828101400d003155026025a0b009041080302910514400e018801d40c1c181c0c4660107010380040e01c40d02e0b41d011051481c0b50600542003c01c1300d8009200407000202e03d52901400e4890320300b0011440411000c01000a020342d06612107245c0082048100340902c6500420b4005080b6055542c56039603108000d680f83c80c2080000d008203400c21042103c0c41c400c02d02c001c1020701c80c3e8252031514041010190a54001c0d0b0400340c04200c0b1170303040b049800360801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 975878174 1250 975876924 975876943
    0x42d0302060717011716090603050f0d02060109020d09060908030603101b0f02031201060518010314150f04020f030901060f062309043b060420130b03 66
    0x30b480158448401507929407054188912a08880f40e006090455401841b200b00c0100c50203020040e1280c1d90f00804003c1c10403880709031064001c8022452480001050b010002002a00100307066403030852007000a41c004141c86004551750b840759400124a401084009401501c1043e00c0b41001001c0605004044000303101d014944079407a441b060300c02040c0c800d04031050402c2607011004e0b5500b642103110740e8441e48990340103c80082031554002000c0d08000c2c00c8005241100c01119005404903a031241440900e000c011000a02c0380d500b0505041800c0400b900380c030004441d000109003a6044603070001040741c2c0101c100208060701f4410003008140858400c200300380341400142c07a09101d030380d0403802c0c5240c0d02d130b4142820441c802111388815000e8010052076850110041e0201a161403501c030f0603541000b06084085000e8500000c44204000342c201512a9529814141a0f42030341624075542c41d116900180d8075111500e04036143c0241c00305a0700042c800301410214981c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 975879424 1250 975878174 975878177
    0x21315050f0f1c03180b1201060305090a060c050c150f22030c060b0619020c010f020309131104080307060612030e09130b0106022121042d03020607 65
    0x518a528076035429101c501150000d5403e000d40000e581411a14800e41c810b54810440c126900005c400d5540d2005000543c80c0000c100d0b03099032503a500710140e40040c1c5040805500039100000030450305d60104401c103a283c14403e14143c54000000d0a19004142c071710b04806c006d40070001c07482540c058003903210005400802d0348620304802c9020000c0e040c407010301000101d0542d98104100c035401030040c0360303000300a01d8031405960000d08082010b040030b0720060168040d031014650054032090140245a000355007003012010606c490781c5503944110240036181c01c042c03d9252803020042c4090500c240c043d55841540d81000d50a0314040c0c0e00446112600300340d440003081d400b012104031040202e517508410341b504503203044403000340400607003641110000010469000101c0c004802400c035290a8407c0d070038000007929000d8051404d141d200560b880f00c041d803000100595106124a200300c01310320500480082881c60420848111f01a44055205061b0108100c65100010703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 975880674 1250 975879424 975879439
    0x40501092c0a0204180e07061b0206030a0b010f0c0803191404081306050909160e1e1203030105060a0e030712050a1e0c03150207060e0703030e060304030813021315050f 74
    0x5980c03240d5030301c8887c0d22520341000400c0ca1504c54a903050041900c101317400401c86038590034014900d50041c846c00c03089070302140302e501d1003d45207406500c96149080c0c1015009081d07655000b000000742880c03448100b41c45550f251489180c4c1a04076026010350700a90500b40c41c0c505886003c040300650741c2003101072200500c226440b9655044400e0381c00101c0d542034407c03075900840180e650124000440b54843e2a0b4608001d00f01070702c4e10241440c450031108606007400c8038404603101e11081c0152034100008201240d10b1501419655003c40005411140c13400c0d03452030207003901d00304508121029007140c11402c0138400540c42c21541010741020340c00c030f0b4011a0342c501d40720190305c1c0300c001c0201400d00d40712000c508065066a514917000f00d0180040150070300070540345c0003240021000b090890320452510f06040064901c90b551586503601c941d100e489080840303842103401240c4c40580d02904107202211070180c40c0035070140e1041c10044900302410031001d210511301d0540580791 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 975881924 1250 975880674 975880691
    0xc14041410030f140d03090c0b21040201270312030b010e041a0409080301080609010213140d12080f18030d021b070303080a050c040501092c0a020418 66
    0x74181d101d0802caa41c004140c5840f1000380c6440489100c407258800110300032406850b040b2500354001241c2c1c1c80c407466080f42c240f51203801e074040b24010092140700e49445105030240d000f42d08081180c000b401414686400411952061410103840360420003110143c5010010461100b2181070140d03110308060101085180000748801c031800010340c800c40e11020100c08048003401d4220b01040c02174018005d0702481d00f02404564000e10030301e07000b880741d00700056540106100307886036946456840c1400a00d05881021120103958040340c2c021180d14405d80010350914039065101d100e522544854605150030494889008200d1070f444c4101e01503510009001004503001091003041c0140c0b2580b8076092968038865640701454a846030310804400d044e044090144150400d14007800349036950f00c03640100b4042c0348112400302c1c80503001441140495000000360703d0900c5081c2c01c8059104810040d014402c0e680c00c1d0f6030903800101400300c149404415560714002000a006000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 975883174 1250 975881924 975881941
    0xa02010b01080f0f1e0a021b060f0c070302070b03041a0f091f0b0316030203060109150501050c0109150b0f0a08030901031d0703051006050d0506040209060301090c140414 75
    0xf0f800400071842e0a00800000c3c5c0d001d040c0f8400702c189640085a01c800c140f81269110009500907101601c9100d0541480c081c01c940000e6007e114441050052744c407a11280105c4405421401c001c07000e5005200d40841e203401004090352040d4041c070380c1400b08050704403041c3c40008000c0c100040c01603003401040f89441c40040e17100d0410390041c906c0d07003114241403101e0000b0015020020f500d030244c4054804190441300050042d24002c034141c61269913680041000c80c1c09099144203454056070041041798054401b0309012100741c4d0000c54181caa5545890b404104180c00058096551403a005070341007108181d0b120403415124444003900b005d001543e640110b50080d030400d6110102ca9820325800d00710102400300b17a60844140c0c50b182d14107107495020802e108203901d8a020400180d900e4070700c080154045e0001e029020b1522943c0a0100c1982c0080c002a050340d00c9402040c001280c840b503031402420045e0003030f01502d01400401054030035200c1c140301902e070420140070111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 975884424 1250 975883174 975883201
    0x61b0e030d0503130b1608070c20131b030b040b1e0f0d140d03020901080a1104080307050f010b0a0e180a06020414040f051b1308030309030a02010b0108 67
    0x100400e0902c90b842c0d03680c1050000c42c1d00c0c06240020440801e42d418480002802010034040300302d01c1d101c07034840d031340c60150460b115203c0500180c42900650780360000841d03040301c00c00c80c0070f2000c0c100444408541605000303940403400900e900e1a103401d100300000b940340c842e8000001c8116018003000c0c07807030700000d2101000116048605c1c06482c2c4046016074404807031414140c2e003d04041207002d40b60130800405c1c5101c0ca2110300901800d004030040c94400d20849240d40c805848001182d150003c50000628070502c5195a00718200000324007101d0030400341052078420030081c84101e0707600042c1400e41d403480c01028040c080842c01802016480ea02990f882454015180684104030b0511303131030100421800b420080c800a00400c0c9c0100d20400d0b008201002c2c1c80501c421045210400d08071002100c00714400100d02c0c58403c03941103c0b2009255002c11100348600d500e880344151401c41d8002da904100641c00016072030201602070096240064003401e1070480d07442c1050381c14051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 975885674 1250 975884424 975884443
    0x735070813081b0a030804050705031501090209010c140c010e180106052803050906070f090b07020324270318010203130f0501110f0c010525061b0e03 66
    0x11201003895400d001250f5190340004020030110307040c0382c000e8100540403070015901502d141c010300d0741c0410380c0c0c10f001801c0030980e2450291400243c1c6401c030b0080085d0054401c203810488803070700c00404100e11850010041c0c02400c007402000810000242500940440f664020508500031000215400b200241120a1b45c01d0665641000f4101800b05054140b03d58040800e046400228903a25034803840c42600c8050440d1003a8444200c10f440710144054200c0024803200070600040100b00e02a115191001d0f0894042040f030900c40441d03600c042e0600359112204008001c481d10551181e80222000d1000744e41c0342010000c14180c60340300e40050720751403022104000c002c5901c00c00407a1240c80c03029080c1d00c0b4031074a0342600c0058031064410a80011400000c01d007c0b00700101d00f503025007a00c0c400418441c5540710064815401c905207518803401e1080c40714180b90509401c0391100d0b40308440000300260101c0c3d00030303800d440c81c016400030170940d9140c0c1003c030707100010000d41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 975886924 1250 975885674 975885683
    0xb07060b0a031b030c0803280c060203040b1b13031101211a01090e01030b040303110a02101a0f0d020a08030a1d030c01020709050735070813 62
    0x50300d000500200c0c800100d6940300030728940740b201036502c1044402410600340c070b00c1a202c80881d1550f5514003662030050608007080c1c7c2c1d9075a225140495612180c504151950b414409101195503c9400c202d8004171000c0c0d404991000410040c920440c04000c4d6910103081001e0605210f03071030104400d162030200824600469042c0c08030740e8040c803852449000304c488010080f03040741480e04060218401100021100d1528529207076010702c0407101518804600c01c1070b0340e03185840340c8010620251084c0d00345a0f9690310ba16061245000510034070b07049400400c04203000c0c160850032200c00c0d001107581040145d030424055500d02d103400840300022601c0c588205100d00015010011640c000e003002e120004101107019040381c01f9502c048507050083ca1858905428075071540948014180181c01505092055034010307402650024103500e40754075000d101195100020260000000b40711030400e1000e519900c250038101d52140303580c64401d40500702044c5d200080300d00400001c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 975888174 1250 975886924 975886931
    0x60d12080622020d2d02090d060e1f02041401050d110d0b041805150c0c070b04090c021204150c05060709031401090807120314090105150108010b0706 66
    0xc0142e614851544540da11003201e081d00030200300c241c00000e600144900c0e00741070428071100d803d500268030700500e8100801c5643c020a21260440c0025400350040e1688107140c0010040070401034443c0d2503040340110020826201c9018011401009066119407090300400c002d11440300080a000944202802c1075034446d8802803900c1d020700a10b4805528209000c24440c11088054020501c00715041d0340c00c0050500c06091200c0f00710f189000502654050400c0c5043c4030000300c0f055503c030710310840e2581418002c004007810004140e01c0703000c6951010a0030702613140184a00140c801150000b040071484410085085009910404140c9110690088865401510b00c200070f19031000540e145441c21070400b803c242613600003521140807000c00d034404a0300501c81e50a2083c0c0107402c00e41090141c1d40c134517840319206000c01040627100d0b0343c3e101c4000300c460a15405144a0000443e885c5040a06190281c1045d5422810084044010442090b1800880703154079004840030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 975889424 1250 975888174 975888181
    0x41107080f121503370b070e0102070321230301180513080a090305010e0102071403040f12020604050904030806031c0813170706020403060c0302090906090901060b070515060d1208 79
    0x12101c00ca54221050804200c0404004021081b00500d2140c141c42d103800400b070401c900120703a02e00c454000100520510000b0024031180c000c03400720b00003100c0c80c0015190006030600825450f1030400740145480200042c84a0703603081c8480b101600c650380040043d4540b00c05560b00350314400c9005007524600040700e200151181030081c021f1900000244071200c5510220783c002d5101d068240ea082d1828050802c1440c1c1c044102c0b0b044518900c0d00504150a001c200b0040440d051000c03079101000b000300061300d407582c2410f6031042e0b000741c071000000e00e40101498104400045902d0500341c0c15180c0c008400c0c1c21106441e040b40d44010140c000307182e04d1400600080384020720640b03d89010460000700180b03900140241c80c4500c10600000c821003c040e006ea014210203148d209403104000740ca2800c1000310194840084000032402e203540b107164105980c00904140c03180d8203c10100940b2034000c1401682008050350880b48107465030310380f00c403c40500511107042080780b0010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 975890674 1250 975889424 975889483
    0x6050c030304110f0303040f030b01060302030405120a020109062f03071d0303040806040803092a120c0a060504140a0e18070305030307030f0b040e0705041107080f121503 75
    0x21000701c0b03900902102e648540312300e6410f07080b11251004503034804e00040041511072081c003d03603014130350100c006c2290f81c00e07082a07400260441e5041c10115940d81e000c0c00003103000740c000e502100680c00c40c56501541401141e11104400318485660042d0800a01040c95030050100300b40020101045092402520009003544119031140b030003840360b2818071091041413001140602d05d40710440c2c00c641103588511220000b00b2224181c12138500c2c1c501c10550805071240d00303991243c030042e2030582c52918005211900a1340241001410205d024480c40617600c03602040b04904444c3e10746198a06036102e0a1241c000740250342d0308607080480003543c00300304100c001469002003030f6610380c948036900900501c40341084d0480382c2c3c1401040d082504041c805d030809003600303078068603a0034100b01c1408041c00301038114844840081001c0808100380c400502140700c2c032110080da80d050741601451110001900d114000040d100704100f060750000b43c010b50070002c1c2c45441c02404040d610 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 975891924 1250 975890674 975890689
    0x80712111c0801090b210601060f11070b07050a060f0f1a031902061606020d06090e0d1107050913122c01090503010e01050601020106270e03040f06020307020a06050c03030411 77
    0x1220b005215603416203550700f03603007c03401605881099603407c8058070041e6040f9410a40e41c00c070240b06402125041c0b01010151000341001c50084046541d4810682e854004903525911082040da50340c00d035000700c01e80c0700d000b4078440c0b0100c181a0b2034000300c1c400000703889100d01d03d40f05044085218111046403114400d4401c4890308507089840071182d8203008029500003803821000914120011420007014450401c4d40b8030000c009054110141071b042d11500000e216240b4544100d450010b21aa0b4554900e44210300a500e1209122120b02d85a24a03491800d09203044c001d400c0c0741e80124046400e441200500c0031591507076004003600050702d11007078076003144da0103500b00000c0c5141035005400c0240140003c1c0e000b00701e1255141031041d02e0801a102101071514103480b03082c80802e940d0841c5104840e4181030b80d1238140d81d4009504e542085620110268001248800540ca80104128020400750a200d4608440302920136102e01c40140010310aa0908030b003400345031511007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 975893174 1250 975891924 975891949
    0xc0a03090c060302090f060c0d080c0d0903090503010e03030105090a020708160b0603060f070c0b0406180326040f1e0b090114060d0b13080712111c0801090b 69
    0x30001c511480c1c844000070065030050424a0260303906d0400001c442c1004421540e1a02c65540600541c5860300c8040300d9800700900084030910b07003880401c10b101c0e140d11401d50154420b0711100a11450f0405050035039010380050711480d041400100174a480c0c619071035910020080c2c0043e90f540d614a480c1209000784942d54681000701100d00c01006111020f00b4000d000c210308440740d955404400c4c201c114411144d150024a1200c03583d4001001c42003407a0300548551004608510a10b070a0b611700c02c84e005081e07000840b905680402c01010a5070310a803001ca0b280a0112403402e9250704840f07401018005007440c002c621a0011220500912a8283d070301040301c00325070810f082c07607070302900007610079609078000b04001c80c101d03240c10780a15141640c080118038260b9141c00e0000700010307250f8015030f210307003081041c0c0d400130f52500809240d44034251203074809a581080c540f85043e0040712404c1c49a140300a8124030242c000d480c1d94111640600301003050300c00070000c03c03110710340302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 975894424 1250 975893174 975893183
    0x3070f0503070c0501150303110c01052217012a050301031205120903130e010f050904020d05030703030c031d070308030a0216260418110f0c0105011a120c0a0309 71
    0x307040d41101c1006e100d00b607012a4000d50394035424060034840b19407941460401a40411001c1180110080090100b040d05901d5070010128003541d13100000c111200f402002c040b1a550780c10316991008200c00c1e0b4800010b201c456030030281804c00400341092106010181c40030444902e1440340070310402c102c4850b401d41403041442c9042c40060141e80350088178200150345200f200102e20812401800b03412500c3c40b6906814007440d20043c003c0044029005981020500290102141c0100000c1114070312a641c00100c0c103000590040c1190903400b0722075403000e1804080007a8510000c1c8003015641c00030070b403a03030301d40311001210020311410100070924482c0d4100f903000d0064460303040c0d4004a41555514010b0504a4003a00c0c91040e80580b050504101c10003641c0c1c00c4555001d5107460300d0b01c54000e450040901c950603029003099545504681d1110b0050020750851001f0b60b45110f04017002e142032a0b4881c5900c00840401801d2181c804000710740e09403001d120f0742000381ca4030b802 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 975895674 1250 975894424 975894431
    0x2040c0c060609020c0307060c1e050319140406050907080d031b0c170c0307140606031b0d0222050118060b0703140304020a08010f1a040203070f0503070c0501 70
    0x20019162504034082500c40a1421000048151942c000c5500e034410340400386142400d00e80d00c2c0d60080100b060b15204021303003124540f0f0700021b14060200d154080b0b844d100c0c3c4074036254020340718078844658540407840c02d0046c060400d4074001c40603900b207940040c2c003081700c1e83c0d10480d003490014a6802014207105010940c03031120b4042d40540c4402c01d41c003c40da0306032052904191a0090100c41c01401100c4441c482c049095034000500220308088040d46d2800701952a884084150710491028541002050100c80e01d010480d0b1020312034003003248403001c00030000054a18403e1304010f400b42008401074000004a0885d940300d085504000b00403958445941e50442140002c0e1400303414034084022908450389001d030340009506a849000e480240b00e84452241c001400403600900c83c000b020990391028005d0300c4a40410100c0001d0381401c10314040d42510300c01418902542c410010310101d9540100c0c1059030f038082e401c20507900c0d129620221f030031034245c8034060295480c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 975896924 1250 975895674 975895691
    0x3130507060c0c0509060d140f1c12050c04140a090e0706090e090a080c0c130510091509051305010606021f0218120c130507200604021c0204 62
    0x42003500100c41a0240f0030703985005885134144082a00140d401a41c000c0c000c21104000440f08020003855280142c295000d01c102c030705040d8a80a160000305009607070403200c5d652055071000500b200d09011140030300480c10326840c00c40c0325100b1802603881d1681c402030080d0003503c1c0c4090003001030604031410840761021304d503100d0311182c0c0c0740103202c0015440307000043d41d0822204460701505221003c0c3c4204400c550350110958072481c0d91003124000c2c0c134041000380d9104105081c40181e90140443c0f41d261882c1c40c079a00c203800d900400f2040b403a20041c02c141d4212051040f080d201d1043e000540c58440b0b100300402c414050b04020129800c3c040080741403540072400c00300c81d2295000034240c42d1055003140e401d901072372445c055903a04444490302a49494003032140030103028001e5610180b000030100b041074015401414403603031500248500c0781c0d8001802c23080b50800c0040c4c1c40c1da1007200031405441d114041c00c043d05c60f03241c43c0e10068119066503c0c10040650041c0100105803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 975898174 1250 975896924 975896927
    0x15010c11010e0d060911030a03022503050a0c14060f0906070c1802090f090c032e0611060a022502063022080f040906170c04150303050313050706 64
    0x2505c40b00864400c00891100755040c240000d408041551507006000380082c0301c6950044002076020030800301c8130202d0f00101007a014005c00b44000e001d2844600f0860802c0c08a501416070708400a0280000b00542000100b8040aa0748100012a074180d660341040c107114600d441e20740c1080d503040128280d000200c112907401070042000035500011001420000c2160502c0c2c12030301c04610f54010400108888050b041d0500348007181c0c009e080124800c80118040a442600000041041581c0001402000b080081da004440c0c1e9400c1d03152409041d841c02d1242d10490210720720103014010f00b03085550b04002c0c0c6503060100b18105800344204c0e010b0320707204040b820329460071302a0100403861030304103203401c1044000030007541245480c01d81e59941a07544007211310251500d00380008a140805030180400428001921401d610100007031241485440c141d078511551505401c012422113942d008021a0341505019807a41c1e02c442c0a20b08440043da802030160184075804503c1e203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975899280 1106 975898174 975898181
    0x8040b03091c0504081b15030a09060c08011d04080a05071b030c1a0a020d0c08130801050a06080102160209270c010815010c11010e0d06 60
    0x40c1c1c01c1c2d03020301c0400b075180d000c02c000658001010402a43c003001000000d0f00341d030042c0c507521003860000039907079a44890b041481e080c020002511034038107a07028412154101c0000c0c00122003100340100280f500340513031450b1088480b07400c0710441404c1c8155120301e1703101c9146072900c5103c81c410740742500309600460b04c601c0500c10b00d500650003031485000442c030560071004558148030043c15030483e4034407041c115840078041e0402c21741d40020001403110640c2400001000c686c01d00c0201072043d54030805040072108000542c16a05600c114070561455404000d0540c440440c6d900b82e110b0040c640b94071119080c0800054a09071092540100c1541d0600254100ca0391362030401c0310001d01d54241ea500400c802c410309503004007140d68000320b15030305601c0c00d183d150006401900442d5016040306a01980c0002d264010040140d84240051a152811201d4a8440042e = true := by decide +kernel

theorem cover : BRFrame.Cov 975719424 975899280 := by
  have h0 := BRFrame.cov_init 975719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975719424 ≤ n) (h2 : n < 975899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
