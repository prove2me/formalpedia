-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:45:19.683046+00:00
-- url     : https://prove2.me/submissions/cc8ba4ef-61bb-415d-bc5c-a315b282ad27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623741007 ≤ n < 623920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623742257 1250 623741007 623741009
    0xc1b1401051e0609060f010c060b03010612060e07121e0f030809010b040e031c09081308100501050112020c16030b01080f011a190306050a050a0c020f0a11041401 71
    0x144041e803a82100202c00107880b80004241500c0b8101d45420450551181c81c0b203890004000e08081030684010f10b442c00242680314000c070b405610306140054500310003107001005034010541013001d03241d401012503c903010f9010740300601a030501d880f80040d141d0310b24014141200c0441c07008806540d5280070030641e803840b06030005030040b828000160310a00c500003203007404813001c0108025405545480707006030021103200035140840d513100035a40390001c0d51003030351100038283e480f802c942c012030740b40e0440e0107004c08910810141240c61581d5100c1e0701c0c1a140c05850306405100b441d204a0f010b0361058680c82d8060280305400c42c40f008612240ea00510312074042e0020540c1400c020307034504100e08150850f180e06004540400303003191250b0000d00d503400e98241c00d8100101e212084400c0143e0f1004007502e14140410a6480ba641c1c01240114607002080c8000b1901641c1240c1d500503c141c00240ea810204841d40041c8850140c2525480c1c01340020900400d5604032403ca0002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623743507 1250 623742257 623742271
    0x120c05030402011205040c0b0c0304080f0102181203030619090516080c090d02100e15030a0c0c210905030f030d0c051e03130605040f03020c01030c1b140105 69
    0x441440304560f0002000345540c401c07814100401c6ca0310b9100c2841505491255044007a0300045241e0444003c0c81110040c2c40c08070b003102e0340340b140111064001e44c0040e40c0c420f54841400304070189031400d02c201d011049a0500107504507200d007420000e0f42d404414000040050346a00000e054049001d080d1107040c90701c5030b480b0003501210015103500c5000b800490019002c201d0243c03075581d00900d1112035501500c103d8080d00412000362070821203161281c0d807044800591098940b04000214820107402e1003d20aa0f004084280d40c8400703901c4008000040c03603606212102110041c0d0100c40401c3d10b800c14089641c0d030042824411010311b10141038000044e5a4040032460107100403041051615611f04405039014418411519400d070710003c00020100b40c0211545600200294001c401007240e82464903084d001401039040c118094011078400ca0510b40c064491610400c0c2c450301d441000e01c814080510000a84410445504401d0b02e107080c00c04000344030380342c80752035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623744757 1250 623743507 623743517
    0x2090a092a0f020d120e011e0b0108010501080402060315060c1b0f0a050909101802090603010e060a0c1b12021204060903084603020c0a080a120c 64
    0x80301001692400c454007030900910501400d4102419400102d0b064240b00920305011100c0e4100c40d49000b900e41d484004840d582001c000300a0640c4c3d81c00100e510021038801040309448031401500c801500340b0a85000c01c5c4810300113405810244000c5600440101c070401d41d0361040f04c0010312980041d0310b0008a6844501d01d02420300d945081c2043d901d108403141d0001e5511100029030a2034603000e907502030300c41d440100c1c521580401503907a82c001d01c00d43c2030103030b20300e2601b45444030300c481030b02130340303d00310601c0070030607504041c4120244040c0b0704003c0c05082d5541c2d00803402400354000036070104480600305042110791400300c8810f1900c202c2c0c0b030001c0e07440c0d41d000081ca800406010180a00e8040104110041d0440d8900f4206c96002180d16180c02c0403031110f5640780074042154540d11500014031020040030081050103a5003400b0300c41d140389912100328201d00031400200308581c0a01469400f00e00700c14003801440256190029036054580c81e402e00340d076250003071203020034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623746007 1250 623744757 623744801
    0x1030813050306090309101103030112200f04020a170a0e06010509010806040303050709241b0c1a1b150f1e070923090610050a0302090a09 61
    0x80841400e00028001107008004908110228540341d11840c007009100d0340d107082d800382045008002c0da2125981c2035040d00d40382d69448a12850245041c07500b156444910f0407000c10202d10100ca024107000702905180c003401608080c00000c2d88200b0300c0005200b02014020719840600315902c1c410501d40c500400c46032440c0084524090042e00010310900c000d000510071104000343c9a948140c00d440e01041545440d0320669410285400c00d0300d10441446035442420920071104441b80030b10f903a003416143c68041074030042c1c510b9190040c040706c41424200403800c83d81c2104204040c40015052405001c000344246c02c3d28001c0c00e08145402c207081c41481d075030850f0707109940410100ca40c10000c3c80c0242e00c0d0060820280c6c500240782c0808400710b02c000f445034801d20080c02440c0d8200d50018540304440085d01a0350b4501842074000000040701c0d414805400004c22190b501c60038100000c1c0c5405030b020f5042011265008141d12000040e000b0340750241c01801c4501100030704441e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623747257 1250 623746007 623746027
    0x604110f210c010c1a130c170708070f030b09070905040506010e150a121a07180902040302090c0a03090f0b1609030b060f0d0516050a080d0e0d0f0506010308 69
    0x5042c8000d81818495400e01c8840801c407682d000b601c0403c00640c2c148003665440090110010560030040d01c407141200e0085a100ba20759003844081d00c050301127944c4c0541c1d520029980303000307034004c0d18500d40b0000c00404c0024020b07510107412258039801ea454468848524100b194011a400d0381e0075803089004201d0440c0c580c10603034100301e07242c03001100c07400c0e218042800c0c004907201f001c440b40c000038403080510003240020200c407110b0055202050070703c0b0f58018084206841c13803800c030740311400c17002a0b03070f0880740701320360407a94041c000c5039050b540c007400601c254103c21a120145900c8403400c2000808000600b540680310fa338640c541401e0011640c1d245040e20380400046c00000001880031a4030b1903d50b645c131440407075101824043c201c01240343d0030855a07006200e881075858516140c1c2108580700281c4070141c80310b860203603a0301c6403c0e40c0c501c40c40520f4000f1440300b10030183c060804007004200f850041000303003c13415903a42c80524001e001d90007034601e003801248440351 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623748507 1250 623747257 623747263
    0x40b07110603042402090f100c0215090f010809120c0f0a03021605010e0f04020c03160b091606090b09040605030d0c0b0901060f170a0c0e0717090604110f21 69
    0x2403a003500400b182406506d0011074111f800c0030300018070504028440860707184c4210340c2d88880741d0f400340100700e12104400d2064416003110000701e00c100920007449482d54411002c19205010b4800207060310a41c0405c80b9450345e0181414900740c2c05411035910202c041000402d610510075401819084640f00c0c2680500304150840b43c10411007000540e0a541da5130119419040c01301c400503030b00c01c010312440b4907500c00c07400c03c0881c1c1400101c018082c003248110451041c410442520f22840340c003500c2003495210b0740641c0c0c02146240e203051003c901d03d600603014008000d0400651640c4940010f458044642c82080c0001c54071128442003080d18404184c001e0340c0f80c40240000c0c0c0c10440041a031009070302070350b00466400404402009810082c0e40c50580d0007100c05203000d6142c2662450b040c1d41151a080442d001d0940c5034020104402100e11032011040540100d85469503065818401c28031115481480d500862035545d8501c1c40d07111840c40110740c500d00c42504030341c0e1581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623749757 1250 623748507 623748563
    0x7030207080d03090510051009061820070b040206040b0c0c10020313031106040b030c04240c022713060e0a02090103030c05031201180b090c040b0711060304 69
    0x104050604d2580300005000150444807800c0008001c600391303480ca8030030107048055601004c1d0590508400103003c1414801540d402117100d48144011101410044100960480d0a03801070000b00003a4011804045032250014401003985207055980e4100300700981201c00108402d400c803421040c50b07803034a4040307184400840e002843c2801c10300b00340c0b644018068840500744200d102c1d4201c1c00c5d40c0e2a0383c2218040e104c805000c548034202000e58900b19001801550744030900030688200340d80c01e07103641541c4490380c0d50f00d5040784140c540c20303c000003101420400d4040359490040890000c20f2030b031544203201d00b45100da101c1c50340d41070150075190480b80e018069040301d0100b50141c6c4403a4100b506403070701070a11a4003041245003035441c51051042c00d4010110321000410401000b1035010b80c1d840c081041800b8861101003003018000c000e8517013000404040104100c0003440c10049d0020398040d81058011060701c4010403000d030b008440850b44500001019241449000c0f4125 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623751007 1250 623749757 623749783
    0xc03071719140402010503070e0d0f08070210170c0d1503060506180408120c120103050a0c1e06110a050604050f0105010e0c181f030f060b160b07140703020708 70
    0xb80c00d4240341e000a80141303c082c18007010051a00e009400c0c1e03860740e4903980c4050754030000a02d40f070015070606080701c0e006070f80b0407441128000000203034684540904034410021031001d43c85ca440b0003218502c681e100d013031087c1d2003035100c40b022841c440c88811000e0045008560110309031600200700101040049040c40c0f5651015050201042c03481c41680e01c0c0303114250f8021120384a440c000e01c45030144440c1054951200000407040140200706049800d00c00d10003042c16944507501a8800400003542c1d041070058200100250b5104102c5104807104640940c4c24030310f49502c9042c14a04120381c16166980702d1815840808801d00c1030f5801401c008040001c2410b01c240d07030231001c0c40384190780c180d8480b2000720780c1c07541d0390340d4450240291981644800a190f8602024024081302102140950310b80000040c080071150700f00d40c000c44885c100307101d04100c10366070700407840000341081c3d003008681209140c3c616441002000c0d0b26000303800502e403940c5032000c9030346418580d290503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623752257 1250 623751007 623751041
    0x207211103160507080a150f09030503060f040b0a0603241a03091204090f0b06041d130b010b0d06091107201005040306060911030c03071719 62
    0x10202a031408010344000e0642d0482418aa001600305030f0719250361500300c3c0c0181d0040e041e800b010402d443c0781c1c0002d21001c1d5803040c4040c84602488604581542c00090301048040001481e246410003040300c8010005000040d01502d034408500c3c0e48080e43c11040c0804c0d40d40c064241e1080700b4070494000c00d0840f01145241ca820b0100315180c0d00f44100040c2a10030002c0040303441208240a0903480c10f858a040a480b150707200c0c401405800c03500151150685840504125800c0c18030444041e902e01905880603071100c00c1c0444008907000b008900c4c0301c1c45c14400f03440020b18501d6080d0090030444519515800040000c01c1111010340c0007000c1a4540781b1211102c026280a45800d0b030f81281030a840ca00550700c81004500342c1203030301503024800110309030f6004c3c0c10001030803d03031780288000c2144a031240b51240855002e070a1022500074180001031034201c004006607400401b80c40c00d0450340307811a4510780680e0f0140d498059442407129180b105903024441d100c00c82c4041100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623753507 1250 623752257 623752277
    0xc04140103050a0b0403030908070b070e010f0906180503070b03010f0e070c080f1201240e060708130f09060311060307200f03270102061e0712020721 66
    0x2e1980c3c40d0030b440ca00400b000c20400004013894080e5220405e4503030440001e07650780b0390a1805603020602121000042007402c03040080952003803200c3d00200620b62600781542e400d1150684412003a21030742484882c0c41400400c5039141030000c50b004020580200703071654142403201c0140d0f4250340200140f00ca84808000000e94400d00007101a07800505a0740c1d03444440c00a00e626216108804c1e241d40700f5480000b400b01041030702840c0b500001d0040c0048524000c1307084410080d40c810039079105200340124008a0766140050800781000220200401c0e0744051805403981c0307581c80b54006640d1f03107008000b44440382c490a0070302c1208503402d0780b45151161002d44400c1d1034102c030549032a81088081c61102d01004114882d42525003180c2e04c5090f00090307074816480d5044071101c00340400c0702d128825400011498010f030030580c5c0101c1c40070b0060303507080c115070701c01001c1204000d05402e0801000c803181c4001c25000740140c003000c00c850810300340c2c411034061800d421010000c0c0c0000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623754757 1250 623753507 623753513
    0x506030a03020c01030209060d0504050c010305060a06080f100e01080705010f0e0d1103190516090501050d06050a020d181b060c06180203030f0a02210f0309010912020c04140103 78
    0x2c0508480c0f0302400d0060b00c42c21404082241d13402045d080000f09807034030f401d020500800242c400d031106400d98007070009a41e01c00c24010254890702ca9000490b00d0031010980c3e400640446550294010007144000c070741d501c0000c02e010070281e01c043c0caa500050000d1083e560f000c03503981600f4825050103000c80d840180803507004000320390054070b071565990b15058241d40902014503100c81e8821040e82d0380c4101d041440d106c020b410595101d601c410b100010b0610400d024041c100ca2340144011156403007900d907180580401014400d801e0f50800081c0c4c1e0381c5400340700340c10304041084450741c18004545020303038003021200c076a6861141c600400300441544030b4880d002c450f60040d4041640c0050700303240b40a21000d0702c0300960600010404d481d0710641e0b140645901c00b500e031308469080c01145025040109110191180d41e0703010049400411102002150044140d0000094481464039084003d00041e5540001a000b11815114628080c090010b9111400f542c2194a514640e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623756007 1250 623754757 623754763
    0x290409080412020d1202100501080105010f0608070507050604030e010f020105060319050f03042718020f01020f0d030e0c091003020103110706060e0106031b090e100f0b0d0506030a0302 81
    0xb2152101e001100d05400382152030b11a40c45408030361241400b03020001c08032011351106180780585e00c0c03041c81c2030300004104805028050495030b460000c10b1a550a00b4022505c4100080520040c04400c001540000304100225031055000c2c0e41c900e0b01c54490700d80010845002038140600310380c180b0040c41910340d00402c1208003074003400501c54051543d881c00c0c1d0b0505490070a8030b8080d0002080000d04400d4446203159038408010741501100d041c00c440314103c450b1041c0a141c03425492000000605100020b895542014012a021109600c108502d03042160314a90002601c442c0d40c14180b05042110a131203c10440d0711604900d0f2160384410806810701c0007a0400da212000030503120b0343d410482d07200b260083d80600115445809400300048280300c1c10000038608500541c1d00240b41d100c0d60f140c000315a9464103043d00e4051112010440070748529118266040005132070780e0394151410050440048054070340c8580c0801c00c007103900050045009800080100c0000781e404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623757257 1250 623756007 623756009
    0x606011e1e1106010b030619080c0603060a090216020f01030603031b03180602160605040b032a072108060904150b1003140106031a0918012904090804 66
    0x11403249000305404141160080c10841e0082c00c40d001d80301c0040741903451000114031031101030790303402d034056160403061050003100d10802001c0e411084140c4000d00e410401160032000003071540109903140d90442d0700b280e0180d0070b00020b02201041d008118203100c5002c80e0306072000d0034100141480c544016082c091005c6184070402c400e485158101030180310280c5d43c400d0380d807e62199098503508069610243c042c1413030360307940490f400020300304d00c224211810786000c1007419056403114464610180d096442d203500c00c00e42c2c00c3d0b040c942130182c5009440b15500800c65000711125040d00c0401e1000c2c0801e8040801025004109250701c2d240789240e081940f021040004090151054004110001c003066108105030020340d11903030715401201d0f40780036400d0551411b907a1000243c2c11240c1c8540e070000c00c07890310a45c422940c0b03000c01810758440c15650b042e07124100100465421a160510410001178903c0d440781c500c98003080b44010b40e460103070380c10004162a500c89010314007031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623758507 1250 623757257 623757287
    0x40b01091803030906151d0f070507020f130f0b04050a060b16060b0612160c1523010b0c07060806060706050403020c09010605030901150b0a050304080412050606011e 73
    0x4d0b00c41180c10440740c1c1d40000c0305210303019900030350a40c580c3e107000510701508105981004070340b00802c07041c0e20f9441c1014002c6800c0e40b2403a1912416134240003202ca4002e0b00b00b40d12070550144e10156070814040c0d40d03580700391030310001042c0894104000440b1009004200c075603140190a1080c045044200c82414104501404e40c00310280b60038800b0300711214111340c000c01c0100e0380b00e04c01040c100c110340c014925418035483c0710710030388002c40b200001240080c00201e08003801d4804042c09501c80d40807818081d83d0a000600e0300707a20403a019a00382c2c0309400c5040c00140d00004840144402c00190030706141401d81402d22400003403440c0212200642411350319000f045c100f50081000781040c02c00908461081c0d039488001030007907002112100885e508007a4460302c04801c1030100e600f501c44041a190600707041c82000c583c1504028401c8948250070400426944030718004001f485124078001c12080c41d05038001412004220500500344044040b80315010740c0104040d148281 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623759757 1250 623758507 623758511
    0x30e0601030b0a18080a0804020a05010e0d06020309100e070603060816090b0604051306150507080d270819030605030a03080606090604090506030d090e0109090213060608040b0109180303 82
    0x18090031303460494071025402418500006008521190003003042071140b8021580756440c55503880064542c5908030903100e60000d40e0110490015009030301464010342c0c0402203414182c02d444100b02100c2d00044900358030b42c012081082042e505001d02800380c02c0c014050480246188003031070f140d2001d4000d065540fa01c0b00c216013966140d2105072401842c008040c5006201c500e0580d0b001022039004050206500900301c1c0c90860181c4115001e84d544141d00d03500d4041051445002080c0e80c0082402e4089252100050400d1003400c11042c1401407011682e10034003c2071034007510036140710420a040c00c0c4030702044607550205034a9012034040c1071200e510f945035000030f001486001d2000c0e61012002c00c2c08503d00e0f0090707126510a0401790102e6130441141c500c00d40c2c8164482c810308a120000200500c4071422907000f03607828501c00380100c0c1c0c103060400f000301d0a41d0b031103800880005140740100414481400700c0c82d801090101810056400407150300d0b441d04000a0024051503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623761007 1250 623759757 623759771
    0x207031104021c050f09030f070b15100503150904030909050703060512100e0c0603060d0f0812060102010506100815011205090606190806190207140607030e0601030b0a 74
    0x14a8a8040b80c030b0240c3c41d00d100c101c8003050301c05402d00502040c3c410a000c8051240040c552000c00021210302c0b10400d02038a0801c10640da0b0100e0782c0c400208448403190070311560224036110144114001152070300c2b03a81d180e1500c0c0300e0700940e006940c17004502c9208a030061001080c1c0200f541000d817204500041016550040242c000d407546a03c03003038002c040c3c050700c0d000d01c030004180700808a280d26401c0c4500c00d0b1812007140c2c1c900b03200000700d50001081000c103c90340b074040007120400d80710b20000001401540c0700c5c881141c004140c130300700c191390b074008000a541c1d0a00c02d181d07114008403030000e0690f00540d40188040401000000b1515074a0300c01c43c1c0aa0080b164a121480003171801e018a207040f841d03003900d501096601c40d00507400c242001c02c0d0310501c0d81e601e8044c1c03200e0f14000c243c2036856003030307102503114803c07021003100358204000d9005c00c40c041c42003039450038220000d00680c2801140142141c2a00100c6003541e04403000503c00074202c92a5640c10440c01480811300b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623762257 1250 623761007 623761009
    0x306020705190305090a1413050403110a0516050102030a020a030807110a0602190801081f09060212040203161410170103030207031109040f14010e1e1c02070311 71
    0x350b154154a504100c00614402c00c040c0e0000092103088000d48074107885e240d0302d034184090307400840449540807400284070f000c211555400b613a032241c06840c024404075011200c1e00d04114140905a845401440c4d081d45810010b002008c02050203200452804000c00e034000d407612041e8a0040802484001068410744a050340c481441c02d41070a60f900080c05103440c400030360124000c111111000016040a14000d0b070845048618400c0905041316012100050701c001e030380d10080c1455540c1062801190042c0f019114440744411001d5050400b40109854a0703500c42d542055050340000a20800300300203201040d103041541d40c8582d486a0a501369460706103c507018008100040001060550001e292400c03240607284a24030980305005200d242d810485000c0c00380e1588050403400a003080c0c5a48401d8040710000296105801c5112030a22204089418081103070319020721200c0d00a020200f565044840c540300190400400607456018920024001030000c0300c0710407607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623763507 1250 623762257 623762263
    0xe100501020a0f1712010f05030105010503100e19060b01030b030c1c080405120d090f0f03230303190b040212071209060c32160602120403030506090f07090306020705 73
    0x210005007400381c945442203000158640c01341f10740c21449008001c0010582018400c140c1038841c05005001401009400301000c4e18508400e104180302d1352120202850080c03083c040168891100480d607004000001400c0d214404602442a00f1000040c0ca50b540ca0000c0206048035401203086000c00b581044091406660702c055081240700718074401e006000704124070012030175160074585035181d01e0a43e80c00d8403a40103a8288100c98401400840e0418411480f03182011050135603a050705141203045030801d0780d0482c00c001c00c2d42c880300c0c000078140c0134443c5054000d4400718101189682030040c00704c000303410710052107501310800a032040c540e00704090b41034002c00140000d8902000080c00b41485c80889d01041200b0304c0007024145200000850003080c00c900d590030300321100c1d800700920310003080c115407a0358204480c0b0100e503004804144190b001e40c074002440e160020502120706001000400000c140c24200304010350444440e80c203072038112038016100c002c14600145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623764757 1250 623763507 623763533
    0x60f0d0302250312050405090123100203040815060901050d020310090b1029090105070c0b0912060c030a090312090c080706020705030a1416030c0e100501020a0f 71
    0x850b1070081011009031201000103042203a100d020b00c1000442c0d01c2c0700464140c01030380161503100004100410030404204103402c8008240b90b4a4411200c4620028548a4546030301401680001c141008403010030f00000540c048182c00a030843d02e481c41c0041e280d031005000d894400c4042d0421078040d91010031603407000403103540f82005820070038100100b4460f400c0301c111010f02850713000480c50000c50303110008400d100402c4116101c0c0c0341006010103400c03540055040110501001021450f00500c9030b008120a5010680e2154920148500c0b0003404c03448000951184040c4423210200008880e44428126000107101c2b446203400c0310003600b61b88007a41c0b101d05010403d001d20403a2140c000441c4c0c4244120384044d40c3c3c402c0183d0710385103180303c1c465054229059510100d80702c0d10390180380e41e03039a00c290780c140403503000d80a500403180e400035104d5400c070100134050070b484250860340042d444400400014038140000355035240840c030003081141c07075a04c08000c00005042070302c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623766007 1250 623764757 623764783
    0x3070302091513050a0b01050702240f04062a121206030804060201020d0e1b1207150c03020f28060605091e010f0602030901050307020f0d0e18060f0d0302 68
    0x121804101c3c040300001d054151000ea031400e141446682c05903004030102c074103c0d03602820540e50b15143d03080b00740310701400c002d0b25000f07820104140e075075000c45003000b07001415081d22001441d05500792040c54110071908540468400344c500e10340442c442c4480e60740c0c01162807030803600301d4103082c400d600a00750b6030307100034a440004a008207a080c2c040d0090104654011420050749d0700b090001556040e1096a03040c1062100c0c0e00025141080b041e218200c6a40b00211400745945e1407041120805481411002464008488041540c1403069007110728001c0014001c0e07902e1a401d550701c2d04803000d0090b006000d40704040e01040b0316500038400070316008100061500c0c04168010b500c0c1386503040128a0044007001040041c515001d2005a880e542c2c001e42c2448030f50401920181c0c005003911081d84a1105002d803190004c01c00c0031072103407003035540300e0785004d912061103034108401c20800c0c41c030100a02044026215a4984e4017030890403503075820455400e080c1a82045240c503528 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623767257 1250 623766007 623766019
    0x2001020409020d09020f0103271a070f140408031c3804060e010605090307090504050c09090c09270a060e060106050703080c1e0a0c0b0105040b030703020915 69
    0x1210050383c0d501801d0322a0090364666140f21903007004500304e03403500c6a0052850707208482142e0001c020400702d18406e114003504440400c0c0005408500d4604031004000240c0306000252600e0b405181d0b4030544809160141c101820410119140e02910f1308010010b140c42e68000c0c010b1a13130f904541c11060744000110103a4612000380b2018040758200c001c050881c110340c09080341002d11072201101c60550390300c0b031540d00303000d81200e06a01c1010010742c58403820b440802c80c00390358407580e0f009500c00c40080866950388401d00c00c078980005d0031040701d500085034020081c0c503860422035100d030003803940d0291611003220386c503010120580040900e1050800303401c2000002d46c0b00c000c2c0e00b000403084540076a40e49500704e0b11485400401070004000350040b83e090b6000401521643d11004100c90b02c60320f0701d00668003e50010003000c40081c90300702c000c0c41031040100c1407030b0142074141c40501c032013007000c0d0119595001612009018204a100041a90003e1501300f90030948c01400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623768507 1250 623767257 623767267
    0x1005040320100f02070312030908180f04020901020c0f190806060a121a0402130c08060405090601060207030807061103010609091a0a090203100806190e0607200102040902 75
    0x6001c03000026105050098500307081c0c002400f8011078101100d00e03582d60080c4956800c6a0329151000c2600b1044024542c0300c5090b03400290013800505441c0143c0c148410054400004015403084400c01740c0b400790744104410a1a81d07400310300e41034a03160070b0712202c440b80490404690b000720440000502c081c11038001248001d0003080e0240940d0045441501183e00e0f01102100442144802000460b10049000300d0050500616501c180010141030840c0d6503e0402030949851011010000d20705004101c0d107840d2078810a5005100300009140642c1403541c069682c0c00503000161081704045070340d004024450700074204d00c030100824103490703507541c04001e00f103424107001c1e00c0c030b2146c140321101c1c410320700944191070346100c020035000703e1502d0560302c0e50007035001506a100c0198040030104d45041c0402105014504580b030340101c00d0a040001c00407246100d1580c5c40325049401800169680071600038040a120070050400000c94941c490080c882c940c07096141d6800811 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623769757 1250 623768507 623768543
    0x30c03020a0b010f0602060c0301080c0d0303061e0302091003031b020415030503041703030f0105060f1e04050a0b04080d08060a080f011a09070f05090301141f050312030610050403 79
    0x21481d401c17600590205d84513a114501180c400b400309000e540400e034001c2d081d45026103031050421510030b000e0704002500380d40394125801726402143c1515030003481e8490070011410320742e001c2603200701e00301c400c01c00150455500600784000d41a2000d039206505280e5400d540e074551021200d0b00580540051107681d80c40c0c003503180e40103803140070000f02c1c4829404c0d80440c00401124481c0406089540e180d84c20002080825001400d085800180900c50301201680d5034218003002c1007102d1010b0b0300c0340e2505040118076842e03070b0000400000c051000300030340100015254072071122820144015500d1201080c0403010640c04103a581c454000c1203404103406601200d841d0218146a040305200e0f4401c0c0481444141ca03ca00054116030b506e240d0303144124068042450014004200c400304410302c5c07905074505480c8440880405290a240d18080140e03c0b0010201a005042003454015a6502c00d000050641c1c2c0106070400450038502c0c49101124040c546c8102490007141141c0c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623771007 1250 623769757 623769779
    0x20a1b0c030203010c0207060c02100504031a011e030206031302030c1309050c0a21060615020304140a0b160213020c0c010201060e13060e03090a12110607080304030c03020a0b01 78
    0x71009900952805445204051010031810161071207a242c1d00d003400495803c1c88200520340c542481004400d200c0800080d0f000d508881e001d00000c82c1108095040004401c100003485415042c1034011650420050b2500d1040d45c0e400480111010080c0c04540080f17800e28502c420f14030f50000c03820181109801e40d66004030b030914010b00071100030144801c1800000c1182c3d0007134100001040d042144000410802c00c1c1110b4400c690100d030039565004410003c0300d008490ba400b40e0408039081c04070321030380c1a010511803000c44019241900e45002d80303499124040d60120742011202c103043c29915083c0722012801d0b012201156110005040903448c3d82c03800c1c0d149801942044400601030203c1c142c81c90290745817030f4001402030305d00e98807400201102981100720f40014000c803140c60750303a40e803a44001c040d1080c180002031110700d01000c0c0a04042c00c034a1003104180a000e010603035140607264001e90609140f00c011005040903450010300c800300070b215400d641d001040c0034880d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623772257 1250 623771007 623771009
    0xa0b09060a051506030109150305011506170c0910020c0a060509100c0506070507050f10020c07170312070e040e03180f060306041e050903130b0c060109020a1b0c 71
    0x1c24401c0010f910703000048058003403064021a071100381400140b000c4000ba51102580c14003251030411244c1e0f8a0342e41a0030741e06a80c040c0080c1c010120f00400003143c1110554114001c1c1507501061031030321800f5045030780145240c0f24000e44564400e503440314020003000f004121b004200c01c228030360f5401c006002da80100001030290903005e44049070180a04404040c0319403110241115507075400d000c84440e00134074804c0c2c0c0c1a1142086900c028441070000490103071a8200150742d03140c0d07000809240038003d078030000700d0f00041c01d5645c0d2030000100641d00181e5208e03021943d20740b03907044116840c01c04010082d51240c502552041200800401040d82c8040700103031a007210024000c1041ca10080e05034541c10500810001d641c510380369014028502e6a414108055100c6a51080c11210220384c12034443e80300280036070a19046242803401020240c007054544040808119200d1506202e4200341036008524a56028041c0500c0f511035964125099200c030307840e051a070401d2100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623773507 1250 623772257 623772271
    0x133030308070521160f210609021809071e05030709052805011b0209180307051b0d080d0f0b03030703050301031a040b0103031416051c050a021b030a0b0906 69
    0x401520000d815010303d003030b002d4014543e00e4038a800034504441c0c1070b000512482410300a40c0d00c0c2002710f0080d010744090302c858004041c1501020141009000700448003a011006100c0074902d0240001611446200405c0710b900c3c0964503920f421074142c500710501d0b0030985d84100780c0c0040c9188090b41c01c010820b0b000c0d02801c00e14a85640300c0040d10070311411180c02c5400040d18503a0005400d00c503451301c3c0c000c0c10454054203c1000f503204541143c110400444060300400c0010000002c0c0c2c200b1400e04c140d040742c03c08510405560303400000c0c0b11744807440150544030b0700b42c1030010703602d58004802c0e142c0c06030969036208850324009020b80e009000485a2510782c210802802d2040e6001500c25540714600c0c0800da400c40e1020f4505092142007096884410044000c20315040510f40075420710400c020021b90f11800c45584100941000181c10060b05101d40040940e00080b4616050124100c09421030740c5100401c0c241800c441c4041c110350686824803a038208001041c0380b003000c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623774757 1250 623773507 623773531
    0x7080723011d10180b0408221d061206010b0a080901020403050703030c0510062601090c05041d160f120c05270106020133030308070521 60
    0x20040c2d8004000403404104000c542c4922000310401100d40e0281c42c0f041c42101c0c402d00f041c05141e654100c01002168101d40a04003c140240c01e020107116a242e015a98440c240c6c0320f03810000d1443d00c948418207200c201d04048004a045900c4104207030440050a405860f01d035a140c0040010a60050400304002003003c000286185018800d0b90256a4003801404015141d610b0031900424a01d03801e81b9240107001c1c00d500310004502c00e1074000c00c1c01c9010003d16080d034151800070066000740019069041c01d244500090700c600a800c20b64600322800034005003240c81081d19046005c8402d0840d04c07403009221200051170030124100c0700a85007501500361030700305580038078480c18002070102c2c1c1845014130241c40c0c502064032410080f6480120100c0211b103071088001e01c2a4050320150b55038031080d007072340d0604042c2000b4101c000804000071030b0307120b10413010310101844064104000b03900810200c511400840e0102200c0319400840031058402285113184240c40001c642c5c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623776007 1250 623774757 623774771
    0x15120d0e0310060503060402042c0106060305010b0a0903060f1e09113f0a0606140f0609120c090a0c0f08040b061e100806040612080304080708072301 66
    0x114250103990f05448014000e0982916907509100c041c20080d0b10140c8213031640e00740c01c842546403100c604032107032000b00013044e40e61604002504682040c3c105800d0140204076110806170044000003c0300d6114070002590090151510001d02c1403840c2224101c1441d5079010b84600035800c040b000d07502440081060380751070401c1000d0745000510004141840c1704041070220889101040c01c5034482c0f0f1a60800c5240103800360400400d070004640d0700b50b99a4044c0500b007500c0c22211031204042d9124000d50602d00005000340c020800424407454a1281d0041e88880c00c3c40380c0c8924043c09005085941441040c907030250001d154000000b4881c8160390040900c1a920380340030342c0e0444803045a585841e8180103c4a0000810310103904009400d0b03c100d071910012244210f19950312034900f41030480401059a180b45c1c40391265051440e025008141854116604103900140c1981d5620261910308142d0288807005080304101d1450140c007070b00c61006c40d4982c2d51900000304405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623777257 1250 623776007 623776033
    0x40e0a05090d0c0201023c010203130204150506070c090b01030519150f060201020409110901080c03131208011e0e07230a03020712030606050315120d0e03 68
    0x603482264065915804082d605180c00d00544102400e0350040c81590b0000d8400b02040e92128019100e04d200b000e5154824940c43c41d508059240c4030407124029851400c02528030178844a644402074411030359400d401d2004807840c6841300050202400541c0c403841281003020203038841e407050440031403c00054415540c031070300c41c0600c04c2150843d8503030f200800b401c1c030a005104000100842001240001c9100c4806585540052625500150742c031803c11404000340c1d5142c0b80702d140036040500002c002c581e04852883c0c0d02502403030b54603031a5526020510001c1900320805080940310058a0744143d03440308009058610780d00c840441051089081000341e000c0b4442c1c042d450f4020070204042a100e82d8803501943c0d00d040f0500c0c48406044518519a48038480e08000709500149400402034039801d448001c2066007006c01c0341526018000e40548030040050075034181241d050800c9554510340c15281c00e440718101c4030b8801981c60702a28003640801928880d101d030106075425 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623778507 1250 623777257 623777261
    0x5010801020a020d210f0906090b10060504030b010902160c08030a0e09240f040e0a030813050d030f110c07090f090206120606120709050112140411061e040e0a 70
    0x40080300c41740b026035081c03400d00c0070f100900456091240003a201c166903000724809012701c0c1841400340c40c00c1501402c000005c80021711196014009001c000d00013003010542c00c11542e411035002c1b032005640d562051a0b0360300340c007524440040c206107071244082442c1400201809503500c3c0345e02c0d03440903020b519081100c64102214001210103034400d02e5500c0c681200380e07600031480050024461140701c280041d054a0003070b0098826035000607460800d01d07511084c240e802c1110740c1c0f214a0070a0080c4c0781c2c02c2d21000b2105150003419255100d12214103035541c031025640380080825034440f11989070301501c030074141c03240b124050304200468400c082c5610880d65000e40c0100203920708800364540d1148920700a2801e5800b14060140d91000c07800d112500303108402e540e996803240d504100c005041c80b0014542891641c0c981103080108160914070207812540000072444030f20168000544244911a0a8489180460040115002c402c6d000d8010f45501c121813021a940d00344000c42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623779757 1250 623778507 623778527
    0xa15091d090d030c0210090b0a0506040903091205031e0c06091b1302040b121602060f040b0415240b07050304170f030304081207031416090905010801020a020d 70
    0x111a4010302480040300c0c1c025449001d06180d51300641d401b006004142c00211240c00d03200b074031a03030521010000d80080a100c0c8661241045608000c20300c0140c50083c901083c2d800b8500c150b01c0121255020b220b01041600d509990010703503c81120383c0c80001064580050701c40c0940d921030b150104101c8100403070416403140c87c403046c820800d02d40c2410844404210081c580400e54208004210306181c0310080100c140b29046160031810306441d180e0b152a0809500b0301103401010034405120f02011003507801c90742104003600303152036900380451224240344c0040f00e180c2c0f0300300f0b03062a0400703940740d201070a803c07071014503080d0b03507880c060221103115040000f0000d0300204020f1043e085880019881216103104540800c9945810a80746610549040e1072408010403611414556032a4580d44038002c0d25083c13081a0784009a01e080c00c801412070003d140080c9803880e403151060b6a0100184901c020504c115651100024003e501030400b1700c0040c0202c1000102040c012600e0307003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623781007 1250 623779757 623779771
    0x603060105031c2706140301320901090515030303090303010b030910050c03100803090112020c010f15051005040602070b0f12040308090c03070501080f060a15091d 72
    0xb00c1c2d10307000da031181400c00941c0c18981c410710418044003845210041d2900c04e0a803160300d1009415810008042c010041c40e00078000e02040800040c441a684004c001a0f000d01100b244a2a014003003051a001001c014005410500f0340f400010100301681001c0c0c041c80111f01004e40f1046071805154403840300319511700e2154401c1004007d681039000080d944000104281e640c03e20f0030201034010f40d074056840ca1500d89010052002812100041c1c6c4000c01c06c0394015482c3c030322400300290001009154125403160b010400140c1a0001e420800004002c200200301c0703403642203400324100b4024007602d400740906080b403848950180044900344c03080b6400603c0380e149880b1106041394050140d100d40d810b0207021044500202c0e20b01c490080303200381c403804c40314a800a5100c1c80c200d6241070292080d8080081008980d0f045906503810201800070040030ba950f0002045c40c003600e035402051081d9400e60488403881d0300034031035070603100b115070407600d0340f00000340701241220300381c2c0c0c2c903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623782257 1250 623781007 623781013
    0xb01120c020a02120c150919080613140f1b01080f0c07030c12050c0f01050606070b06040e060c12010e0402130c12020f04030507090513291e060306010503 68
    0xb4000d85018504904100c80359070803034080d11030000c04645030310000080c1c5411580003103000103c9242c003200b6620b644060041c4140c0305031504286a0361080301521b284040440402e0000610101076140031010000400305c810b64585800c15940d01c4008000d40c091086e003080c1d4039912503105005150250075840c40c901f01035121424102c9070307544404422411302660050710800030340c0c640005820000280c0b501341d120090542801e0600c80c0d400b00c0d8415991404040111350ba5604007038410094000c00b01030000d1b991070000c200185906000c500c060300c80c69041000f8007e00c48001c00301140900104001a41d13205d60840c904070041d140254842d1351b501d100c0c14000b480b94444094440a40b40c242d51100083d0b20080880c0e01a0541080420700041e040c07040c007408122480091608020070003c07403426600c051540b41e49240010a103010300c03151454101403c2c4035039020102e40780354502031400d08981802080e041002e500a00e0b1604c48001000c0d8500458224106c80020740a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623783507 1250 623782257 623782273
    0x6011e0c0c0504090f03050a020a0f060c020610081209010e0406030f02011d030606010302090d0c08162301030e070b030a020304020a060e01211e020331330b01120c02 73
    0x400d487d16040321840c0300461050310f22a5021401620050b0036031070050600003441c07a030004000341018801001320060784000c0e201089480e500040503180614500c40140d203038108040100c0d10500c04604480d0703c01e0402d07501005201a248031050080d00c03d880c0c200603e4084200c0044a401040b580e40d415004040000c4a0754043d800a18220500a14240300c1d40342c181d0300c02c0b955541a070015180b550002d00c6042c000d000500050000e014401c6014030100c0703080300b80c4000b0511026107141003645a04858100c54020840c081c080c00e810004103440c0c2c904020824001d40049400b6841200301a2001415500030f18400100c0c40041c0d4070604012003658061411a000004013610300342d841c20303c074001001c02904442486039030540503a490900d00d0f40c20141c0c4003130704413444650f0040e90707295403120600030b5044220b80d80001500f02260600302e046100e40d0829511a406508010070b2482c1011150b221040e000700276203c0c0803070029406005422122070701c52280c096401424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623784757 1250 623783507 623783513
    0x101107090f0e1c0e010f0e10030603051204050a050d02030f0714030714060d0515030d020604150e100c050d0207141c050f0702150c15090a020a03060506011e0c0c0504090f 75
    0x800001d0210314145040350f03807490345c0413230701022102c0b040b00000b980d145401d00401c00705104000f040d07055a01d000781450700304400a40c045006104041c8030307411084003601103440c1070046080080b914810344124664a5011b1002c07400c0e03001c62036101e40a43e44000c211004c0c10b016203041a031024026a017060000180b5500802000d090088021402c1c0341d1740049950070460040700002c5540503007000e04062620320300d40c2004903103000c8540d04000700300c0395207180002d440c4d080350f038008001b1441d00e040c1041640c1600c01e9004014900d400090765034240105121412900c4805e80200c0300308041c030420383c585100b1502084000603100b00a00031514041c0e00140c9911030004002ca002010f0700d8600d80c0e110b0b8450308010320240c100ac0705e0700090b06000e0b442507034001081c1014100d900c02a9002a1884106020050034942c0e1400411040e0740300342808541d03090f0308800d100225808900c01b5111901603007040340c00d00612900810107091601840e00a030740d001c00c0950308403425507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623786007 1250 623784757 623784767
    0x1807120b0105221a12010c050f18090403050901020d030b031b0109080105181e0d081e0103050304170a170306131509050108010b101107090f0e1c0e01 66
    0xc052030329010f1940b640151840c001e20034000c118019444011004a0440c02d202a18040f8201d18103142d141c400108040c0b50010100d804424a40e00c101d03a46440420b040baa4030f441d00f05400740c02c021590104001c05030804000e1558500907003c070380c806110224220291004e0340c44042e0150010312400c198080c028042c10f00048050414828032503e5510103400c548040781c110348200e20a00418001107014031031003003214a0000c50024480c0180c0b00c142c2d07248611017541041001c0303080010400c1c120306441080c11045c081e000031103540e490400c1640c0360000d000c3d20a08540d00c0645079610f01d000911041190342c0308010050f0005025020b030507035080181056013020210f0803405003265588109120842c00310f075a01c210349c1c1030624610031914143c1041403141c1c0761840080d0941e4844802201300503080c81c0c480c0f034208003c070015003400002d900209103d400c102d01e80c0c81c41c600d2030708090350341c4c00c1510840f003401009002000c840d01c46038542c0b0b004101d038254030001d254813031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623787257 1250 623786007 623786029
    0x901020f01290303072406090e150709030c050607030509090406091104020406051206040b0d0b160504050105030114040213170c0a0b0f030411091807120b0105 70
    0x500680e091800c103514a00e0075114000d610003600c65000201e0031840408595581d44240240d0045081c40c04030b655440d0880c0a070301502280101003442661002c59680200d000f91030100d02c2030288501110710166521030081e100100d40c1d254000041317200d4811810744c3c0c21a6004400b111610b850842403021680c040002942000b80801600311507490307a900543c001c0d807081400203800c9845d0309000800e6515000d08510a500402007002a241e006082c1c8040a450742c4030544a0f031641e0b00010001e00c4002c80054000c00b040d6410000d0150700c0c5401c46c4100208886c01d058808042c001301c840c1c2c804c5001e0f550100f4010710042c401114010425010424060300042c40c00620007103c41c1034030555400b4141000b541a040d2151040a1000d584071600c01d0b589440002c0c2043d481d10501c0c055001780840e000c00200c0080c0c10f00542c04007100001002415800070350500904144040d4000010103041c0c5c07190490003c2c880d21002d416001a6070001b18404059003044200b01200441c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623788507 1250 623787257 623787259
    0x1e010e060d0e030703030e06060f01030c020a060f0b03060a05160c05070e04150b030d1b0c2c0108030703021507050903070f14010908030a03150803120105120a020a060509 75
    0x60000d800c0c10341c1c041c03149803074202072000115214059882e008050f6041c6804003601038101a0911119407a941d41800c1010024280401c4804081b03104030f10308682d04030068400c50a0100131070400301c2c143d01c0000c100340164181c8503507a40c0c801a81c1c049c0c0700c041d900c0342000550943c215081510920070480f0070380c0f1074010343c0d100d20360b2030b00500c00180c410b079804e64808684c2000e8400d000c7c07207841040134600c001c5d0041c1c48403858560000c4d01c0f0319031244645440e00b9a0b01c0700f40341000030b40301440004e030124003180c2122a40404555642221801200154404000c000303d0301642c00010f84030200c0d1f040d070040c810f82580d041040e08845024190310140b0000b0b000c01501c5035001d1222070041c00c003480c0b001d065185003104048032250000804c43c140200013005109040000c422101c81c1c0e40c080c14045803e082940310341030804016440b4120318000803601e03507036429a02410074102d441c120303818a0100e00c2691442d88440d0781210003540048481420000140140058016044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623789757 1250 623788507 623788519
    0x5030304090e0f0d0509090604050f0406050a2c0d08040f080a09150e1005040605040b091507030203030405070603050606120711031b0f0a080d0b040b040e030d05061e010e 75
    0x700703e03880d0f2890100700700c0200010680200e1408050b080800580c0d034080000c17603003406a401c0454940500c0640a0400b51480b5110800030f0705050081e0401185416036400d000d541070003030010300c0715140a80038113089a028141c241d02544c2e10034500303980219044820068200c4007070781d945069038403a00c204420700180b513000144070321160b003444c0782c828010b880d80b10481c00d81d641000318220006074010240b10040c0028001650700c14280d038142c43c41461107603a51051000050b4051644000341c00c2d00801c0040e220041640c00b1001c0c5d4000c3e840b9030215503031691180e005800b610300031030702075401c00024401c01c404401c0c800312141d00b024142c180786001c00c160080150955000210714400844560694403c0d010108000c0545560410240c003150340a03580394001841050507107003d40f500c84210480076542d0380c0c012940c003400104108200d01d414041ea0392650000130540003880e00e000006410340c01c1ca40c00d10750341c400403800c9a50050300d000006450074500540a1038101c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623791007 1250 623789757 623789773
    0x60606310308030f0708070c110301090203030f04030c05040b010f030b2116090207081909090507111009020f131508010b10030b100e0301090614190605030304090e 72
    0x21140d012040195001e522000d40c3ca00d4103410280310258090110802c100700b2400f080020342d440312102d12440c2d40b1001d038850035415000040e024003442345c00a036050000194440307114010070010004caa11031040900d540c1d13591000c01040303814a1a410f408a5181178000c2d8010344649e000d14104000145044040d100d40400d448250301c184a0750b0540754464031444e0040018403c000005002c1544190702c3c14803240d4400c1346900078540404242c0080c10311040c0d01e0780c000c0d00510080c08241a04020b0381c5000c890041003041c0359851490307507008501900c40301401074060400115005450b0710f469004443c20701c1039100c038520040f40c00743d40e5841c170b02150400f401d40b690300130000800041100e000075400c01481048602c2d01f0300525280c500d02e420103880d0f18009680510543c24401075a00d56007003c00e01401070b080000384040d02d043d4521410a080c80d117a64014200d0411260994000700b01035012a0307118080d1562552007032108000c0c02141d60810340d041c81ca0f01041e12202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623792257 1250 623791007 623791087
    0x1060e0402043305010311071e0503040306110403031e080115050403140601060e22050c310503070f0e060105040807141806061602031c1709060606 65
    0x1000600f503020219503a0120200465a03244c05902e0b6141848604680f4200390f680e03502d904850450300c2200f05207010780e071440610500b03205070340086411400601c10b00003c41c5c803100390380d0311500003100498800d49403550b03003090740d640740b00000030203842c1c0030410f07402c02c0071031422500715120a0041010400003c0005a00c101c1c802d406500480001c4c507880d4140080905403903c86017002d030140b1280e030040520b58440600303420030590780380310014403502c480007070761058854111051820845007088982044030f58080141d416400350780c02044c5510fa10403d500c5455520440c2d8094440350300034840b2080d00c403031954000405060807851709a45400107410406150f008219510050300c4c40120760502150703d000e045800c02c00103c40e4a00100019000e0083c006460885503088450908540702040807801142c0114800500f01158440c001e29048140007014903121692000c10310700200092406d004000c0101050305000303881d4510703100f6450b80300071003600c064102e420840d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623793507 1250 623792257 623792321
    0x50109140601030e0f0f030c10050601170709050604030510051b090111030723060a36080d0b03010b03011416050706050a0e010c0f08011a0d0204141201060e040204 72
    0x10310280d01b0080d64480381100c0e00c09042c000420388000300c090405041101680e40491108401507600c100c1c00203035255910b0890f28501c05401c1150840c0740050f0100501000041094180a14800922807030380c400404a040304c143c1d503881112108280400040d41d8010303410513130f1401d403aa040b0b030b080011680f1003041b40b2400d90403c4403401d5150f45007000300c00c0144800c0b50300440c011801d1014440c1a03108000000440540240303403100081010f00341c07030300d0301d1a004506800c01001a201d400104d41070004050500c007084c406e62038460149014101805445015842c44000c2c0d00740d42c8c0c034094988150079040b403a0070b040140400a03035001070618440c99026446010300050180b0f441c005150850b0100509003081c04090551040d8940d0320058980c159181c1100e844104400d02c1070f2920710703004a2030503034501400442d0114200e0b5204654040502c002c403060312504802810a80c202c034124051031718a05890340004003d41043c0d0031039052040314941d50618803d40380c0c51014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623794757 1250 623793507 623793523
    0xf14121b0114101a1903020a02030910050307020115031e0213050709050f0607170904020d06030807111e1c050a05070e0a020406091205010b060a0503010504050109140601030e0f 78
    0x1d41d0142071405001c01c80140705000d00e00c80101410514151102448052051801c00401c081540024801d22a00e100307002f91a00c80d2800781070005034007800e0300050881d40040b0350f02c600562801d9002c2402a20107a480804c0fa5000010881f0000240003c841d40c043e2104007039170041003c0c1c9400d0038070081d6100d00c1e4444d144580d11060400d0914080005000001c591035205000600c020000700d4040c180c054881044102602d81e0358010344081000fa0007500c440300e13155450701c0b1002060044010003803c0b00d602c03841104060b81054010880c034440090740c0c3d000c01e261880c060b40d030203080600202c4858000740c2544d10342911503944940c078003281d0440c00c4a2540041104210f6110300049485c1c0010702001d040d4103103410080b004001742c2d0903109928817610580280b0081c07010a40c09008a60005018265640f0040302c3c044c000d40d10038850390340103524280c00043d40c084240302e04003220f804500890f00b61b881705001100540f1907948c150015015100e02c0d2001c80c18200b204503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623796007 1250 623794757 623794771
    0x1018080906030426180103050903090f0312040305070510030204030b040609030905090a0c0807020606101809140405070b0304080708070c08191a0f310f14121b0114 72
    0x980e140c40144443c0140035a02005e581410300f804180f01c100b00011054400e43c0b030b81660110080e581c0d03540000c1c5413103081138080c0750200000802205200011605070240c0f0310a450800c603240c0800c41c00c8040340315038032028190788112004607000816603000304481d14068074004000c5501c86002131402c0c0015264071a441c0d550f10800906207400c0f90100b640240103001804181c642000030402104036169030100b0409034040000e941364801d0744040c050070088408108a800c10b03004101c103c070742940c00b99440d10480c440054640125030440c0d03c6164800780841c203092259991754110341240c081110f00c00b01740c2001080240d01041500c0020340440d070080c84070581410410080020807603085c464020316410808240c109801980e00110880100c0003001144611134007941c50200102c404400d12003000d038280b200c100b41c004400c40c0602d101c10b240302c0343c1407503040d40c6098000d4005288141800710108800d549207a007480d800b0040000314200300407088500703095100311964 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623797257 1250 623796007 623796083
    0x190902100c110415150210090302060402090f191814011a0405270709110415051206011112031f0b0c031c0e0f10180809060304 56
    0x14207100ca40c2d480040d00c400b003520100030900c02c0e600380011407089400340130305140070301c0da90201683c42000310b50300c00303000190b0402a010184c5070003911104113450591007410001c02085a0580d00008030340100c98006c2840440820700c0d10440c090b20f031002d0001c0554280300d00880200d021b4100461001446800005448a40c80d10188401c42d200e008180a40d2400c010410404901c4507104180611000101105044030589620304800c1d40c00107404c031810031403030007048060703d0040d00a490000c6c40c0080380e402905000c42e030b58086c0441a91809407810040b40e01c95001d25069001c050640307054400c8dd810b0b10b4402d804650050ba25081c0e80b910200011202d000800c00e140003902543c2e800500d090546145c1598900a40d02360114014400011000d407440e66409030b41865009010307181c0380140040c10342d840e0a4800000303040b4a040c40715a600c020f280c0c1302011001d0354001d00c4142085407000500001e03800080c82181c42920061914203150480f805110890f00300d0b94030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623798507 1250 623797257 623797277
    0xa030f03031e090305030406240b0304050d050a02150c040b0f042606040605090109060603030f110d0c060e010b03070b040305070801050c0d02181c0605060f0919090210 74
    0x3408031018550100240f520800c0c0c4000b0760300c4811a0b4115802a002003440140305203d9030050b100f0401010282e0703034403000051000000000756204601580076200c00c1000050142c0e0584a40505080183c03c4901c20003021010401881d030424900e00c20701e400c1540350900c050481d030000030031204511010a08122507101c000c0380103540040e0403038880070000c1a005155850001601c01458284c40b0000500101c000754405900c00750806130900019640e4103000e841e0200c640c030600c0001e91034800c0315407180000680c2001010040d03517510008007042d11100c00809044c01020020354852400c8519a5001c00007400a40401042150307103038694079010f45824603d0b80000314603414042040401440d0318155a00d4901d441c2002d40c1c0ca000080003100071819180d032555000c211003c0c01e03e00b407400ca2042c0411280310306010082c07038480004000061004035901940501141c0c0001c81840111501c454041140340020407500784590008100c6140280441d0011304e5480c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623799757 1250 623798507 623798531
    0xf0b060c0c0a08010603050601050d0302010906090c261b120a29010501020703171306090f0801050c070318080a1506090b030c060310030818010e061c09020a030f0303 73
    0x42044020f15600f0003c000740da01e5540c6d40d60729030005104a61040c0451414041454001e4100300761003540710001700000252803400c8480f41d241d5000720703610002080c2c0162951081102041c914061180082081a00c04891280d25000024141d82c0011608040c0c031a800310421100c0341d44d0788a03100d40e03d00b000440d809401214180d160540b88245180010056039030042034241c10380741c0203140c510344848001422021072280345491420a58400c00004407aa030106000d81130b40c1040c160300f030807140d40e1825207080e030700d040c1c60301c1d00100010054180001c3c01440c16404dc0b100c10402800c0c00707607440d400350b4100411100140e402c440e0040f01407081d1541480303414040c0c40b20182c02c0100b00194001300b0360f03c15840d481c0724004c8a0000109040c41d40041041d802107a126903455901c00350903100c6042c1a01900e0311070b002c50540040c0380c20518005090b1609000a20485420594406c0c5030b840605043c00090b40c100303190050100103d44c141d465a07021a0007078a000c80d100c10000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623801007 1250 623799757 623799769
    0x72c030606031603080d091209051c0305121003120f0f0801030b06010f02210c0d0f050f03191b14090109030803061309030224010e0a0f0b060c0c 64
    0x2003950b8031a8110300c0190b041c10032509504816650041582500d980f1413009182c001d050300d02c130103401c0d1001c112900010a9202050300c050390019100080c080d044610010183c60003c3c2c2c004001c070f0002e0100389116181d10220940c045081002d000ca0950740e500c90880d000b0000d284500040d0500c0480264603411424028202142c0d14002c210b541c51501c0d00e200680c000780c42d0a04101200f4005201e2a02c2007044c1880c1c10f42240c5a8490780c074000744891102d5021312440c124a018a04e10078201c140a0078403840010219242d6900d801044020950140c0c00103120782d110411858410285205601c0b48128005800a401c1807000c4c4001e030140100d1402200b0b103c000d0410171081c1402c0c0d0340800054102ca81c040180340d16505c40c2400035101242c00f01031000c01c02d141010600c24140d0000748a0114007010030010812501d450410f60480024080c500003401300d40041000c40031568170221065141c0e0308001071540944000850a5014034010b4010340c0c40640c084170185000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623802257 1250 623801007 623801011
    0x1805100b2109060609070c0f02100e0103110c030403151401060c021305070e0103021e03040b0f07090311090405240601020f01050423070909080d060501020102120f072c0306 76
    0x100000c00c2d46240000c00140407910040c440010003d111a5282c1023248007450b60340c0007a8000d007642c00d51494600000c3c5818010300443e400039040200821030100c0d410200e484940081e405149040d003940c6820b41c041188600ca03a059070360b1160602407801c0d9454602d80038000d00d030f4074020103124034010001003c1e030a0041007013540ca44428001c085400c1a902e00380c2c10000e00b005a240c101030b100544031036500280412800c00008100300800200e803500b1032003402c0032454003140d900e6600c0120b4500f0300324000200407035075490700154603190011b1243c1d0f00600c1038084484207203050340302d1100c0b44120038070044030000400c1400003d41e014042c4220030003080c0c00810480c6455120400809800802e441000440b10544034203100e0500c0250054206140c0c240981082031405040d6503000c0d8801882d501e2038500040380941c41802115403400318501c10781c80c00c3d110314042c280e0305040500b80c00280001981805030140009181104448401114034654541041458109200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623803507 1250 623802257 623802271
    0xd05062d070c0b0c0904050108030304020103060807060212280f030e03160f02040605090c1207080f1f09110408010605120303240409050f0c0a1805100b21 68
    0x41402000720707142d480744040041c0354200c0241a41902c88500e40003840c0708404d0026001030900c000440e9881c000401075009a1007a60104403081e070307952170252150445e0003402d005070040003800c1c400c0501c02c0098681c0d039034004100c40c0603c1c00946280340b1141103500030030104600102070309510307805101300c202d0312080d50b000c0c2d45807550343d0001d07c0210481040003400c0604000429056448603403040008e802c0181c0320640a0404803108106034208190090541484d1000105810300c1000700a020703618140060945484545070355000000314042040303824514540041c00c01380501491010008544895560b40d0501d24201d094801d5a00040d0142d0f10b01c001e1410314000010481c1e80c0702502c0c1070300c003d00c0340e9194200380d403004070200d145038458103103204401130100101d94001d00d158400111031032501a401840301400c604e01c030700080025510b04d05400300c0b00d90b8020360b6000f10941c50086505480704940055038104283c1c495680441010f05015540300d1b0b50140e800900c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623804757 1250 623803507 623803591
    0x103110a0f0c050f1e011104150e22150b0a0207170114100e060f03030405010c0c0305070303080912071104020d41040f030e0d0506 58
    0x11814805009501210442000c0105800c001414000c007031007140803060181e1305445803070b480f880144d542e9003450701c0c60f18a0b5500e0118070000e540c281c02c04580403501200f1281c0484200410181d4002e0400e890032500300c03840420180010a144280c0404180b4800001405801c0c000c000d80c0100e11301e0700170f400900000c100c850300e800d0300040c2c0e03c4121080300b00e001801002000c01d10b405410400c6180d80109219003d110f554801c06410106843c2c03080c2c0140555954401048002c4480d584482d4154004010034000395100d81c00401c280d0380030b5200b8444c10b40e5665640d41c600f644d00e5009800103112201031007543c141c2070091810344894842c00071304003449522190041d000381c2040501c90741c1d0014210000c0501038104888070013404800c0e41128550b0440840aa082e03440c1300154070304602039aa03102d03000c000c807c82c000c580041e40004400300b0760340d00341c41c1c5408160b94603900c0711050f803590300020000c000700e51180f00110907850070000051003111594031200a81400c02c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623806007 1250 623804757 623804767
    0x10605120703060504080f04030c1703030708010e0a0902090a0c030b01170c0a030f0f0c02061819031403011205060c1206091b0a0e090603011803030b0429010311 71
    0x507004280ea802c200009400c0d100d07440d2140a42c0f00d101c800106ca40c13008140002441504010b04049980e000c0f07919107844803900c1e04680301d220171614038010400d484018401444e070000243c2d0702c04624980055003240980010354810400c035007090aea140c0f03a50320592601c5c0d05000d0080c1c10327082030030900740001c040702d0b80c1840800300401e90b0095490226403016079510a030092000c80007801001c001c80303c8101d01c0300340908a001c108402602c6002c2c04138100d604041420b501401a14019081c41001d400510f8000306001e0310503004c2102088640614805100041d40240162142d25110101a103840c90500300000d017003154062040c051400001483d2050070781c040c1d41120030348020341d03941d8908841760b540800c072042415000f044400c5450b0700801c1c010801042152a410b040d0380360001c040c00c0c2c0e510900e958400941400202001034001d03040310000900042000c1446808050701b00040c501c034865000d99454030924501140d6018491002542c0381c40f01c01a00e41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623807257 1250 623806007 623806039
    0x40f080f0a080a0c06150e0702070509070e040902130e1c030504082b020301080d1e050915070510020d05090604241b020307031b020d0201031a0301050a0c02010605 72
    0x30f40103560340c080030301c440c0c0c200110800c40d03154050031080c1035451072002c08607181d0000001c611001c40e603000c0540310341c1070003242628148111510503011592401c001c4607000040c0f01c00340c92400000c0760805118041c50403000340c00e004844601d41c144006110030001107a842041025000094040c14582001d00000c10035001c100c8070140b40004128580f00b0881161269080c03110400d401940d2020001081c0d41e000841d4040c0921043d0782c030910f2850320200700c0c0107030310609a0b02c100810410400355085083c0010442200c11100c4540c90500c0f42070f803038040c100807001000d0000f003540000c0b081c111800f503100e080d8000385054000c3c002c924182c0d07070724644101c041c1d443c3d2080d01019140c0383d24105060b0003030040d1070022210020108500c0b000030350350380c10103138044000c94090580b0049a900074440807026980050681d07000d90941d4006400a104103a401545404403a0751030902d51000d000e00b500555411800003035184224000900311000c03a00315921440d9241030b48480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623808507 1250 623807257 623807273
    0x19021506060304020f1c060204080c0111030315210102040302090a0b0907110a06021303110d0308010506090a0308070c0512010c090306020c07051c12030e060a150902040f080f0a 78
    0x71060703050321003074a03013045c2c90300044680000e0010460740158403c6124100074040d0050f0048440e070600302c8100000030030040d149030302600035001c8940c0c4144001484112004003144401401621460001180e045420102080080940c0d026900054100f0440c280000031a40c02141c511082200031020710004108800c050a0b0708208a00035021000582051117a038180d40d0f80310504555440782421410000b41c0240b00907200d1844e607552042803400d2460320801003c3d855950700380c40707a080c1010010250008510700c0d4104003d400b01000245040c0000c0003454045d402c5640310350310b82000c00c0030301c4034401c11004890341001040c04055410000302c4040e294020805606c0b80d500c44a110302d0055164031840d804003c0d00b88010b01d07510000d8488486500816030900003400c5c00d070040d0140e600900c41d061240d4820310004d07510b00681e5000d69081d20a4a031a03004080e80c1e41021b0050f030704283c11005181684000c20004014100140354a40d41c40402903d00180c983e250408 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623809757 1250 623808507 623808511
    0x23417030f1602031605010209060d2705061f03060204060e030105060123030c0f071212020a0e0d17041e12170315061c1a03100c020111190215060603 66
    0x1c17001d1710305045000c0000a4056401114001c2d0440c1d8841028440401c0038110350145030b02e101018001c19010b80303030240c03484102d2941210040059454290140313111441c14501580c260741103040110005280e40000d00090560740d484121380751440040508440f0013030103260521001613031910b0f01d0740362440c0107400f040c88001c000d034a07a03880f120054118410004000003000c40001c81c0000c1000c10f5040c4542022642e6810001524020481c0200d01c5040710113400b08000700d07403890f0b5529001e400603510070301c6121102001143c24803000035a4005030000094901c410f141c040c441d902c1e9484200042440540d05a01da10458a40740c0300d402c940400c3c0c02c0742450000018006115031120504002d0000d040c8568900b03400380700b0148280160904480d00b800d010922400075801040301c0f028860007009480b00403102c4c86000002c01c04444050199501c40000c144542811809004402c100241c4610201c100c8207000307090451202c010700d400301031305080c0300c00c61300c451081e25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623811007 1250 623809757 623809777
    0x60f0b1801140103110f030718080a020906030a060f0c0210020717030403050c06130c080c0a0b0a020f06180d02060106080a27150f023417030f160203 66
    0xb08410002004034040c00f0101003504400c1d000003a00c0240b401c1060044d8400c4a043d0b48204c1d0756000350003900005401c0d486a000d0540c00700d54843c01601d007882c0016080310004086810717511140d40d07031b142074404400302c010384203a5402e11000c10580502c0782102c03003c241c6004505d085040c0d80c030400320500981204110301d0300840000c0402d409030317040703e09903640f080440e5114500481c0c80540c400ca903850454841e264070b4000500f44a0004046040302d0009200c4101c45090044d0a030700d035000b841d034880c00c40c4582c6c5440400d0f0402801894040d501d0845420002c1201160840c40c0c1003008151800b194004c40042081c10742c0144003a8010b810f60340c000c80c18500700103c2c09043d0000b044203110794900b1413185000c00c04d000c100040101080002400720382d0171611200c0880c041c644140030b21101420085224201502500c00c49501c821025045000c02d42c840c0200e002c0d0001034448075000000c2032280c9030400d00c4105a224140315480207014003113a03c000c1d1a4064030b0582 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623812257 1250 623811007 623811029
    0xf030a0c06051803030a0b040b04090206030406090c17070e1008070308030426090102100203010f0b0306040f09030c0605090111070b070210020307030204170111090d03110a060f0b1801 81
    0x1003503d05105081e8032503418583c0045a442e404c040340785400410708004034522591419906030440d0409000d01c0d04100d03002032045045613580d440d440041c210040089422884c1c0010218000031003612007481e4001c0d5400500009092a080d1032800b08003030b0080004603100e4408000300c3c000094104196544205170301d4583d01c0350704e005c004a03a504c8058980c0c072454012104000804440038103008a0700b6400c5504603444807184000300e02c001c3c0144a0140903440d028811040c1c800010340c3c1000000d040010181003d0244e5411140141b0044000032112603511040c0a4503001d4150000e0700c02c0b000300000000c600014140d031044030b0008003161004000180780e2802400000384050b14020155964076110700000c000358410700400b090003d40c6400d0003918141403084049004600c00210300e05461030007004602800072404034100035216a0409100100f0300840107181d20031000400d034440c41a4042d402c1d200c00d180741600954040c000361084841c0b1581c0d07141106c6180400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623813507 1250 623812257 623812261
    0x8091003020c0d0f020d090602100b011407060606080c03010e01030b0601120c0513081908090d120903120302030402130203060d0503161101020a050319030b040912020f030a0c0605 79
    0x5402078051022220b980e40038881003030b10070640013548150714442e1039003642c8682d1020042030319818101d004080040c1d000c01202081007050b5031010780b030900305041c16041c0b8081c1c0c0309061281d42c40740380d0803207040340c48030b01c2008070b5078002c5080c50b00a4002034413542150f0501d800c0c004030110510004e00200a0b00300801c0282e4050013640303401e84401c000610a00d6013511018210768080301c200722204030403440010310142d010408460090b92010710004000c0a512071014070b80107011100d9100100414181c0095008450000c00e1b10103074a51640c010324601b0a40c00c0320480540c403009040c0100204401a07681000507650f001c04990016160385501000c0340ca01c03c01410300034048c0c400001d40d01d8001d2510408610280d01ca00c04580200d82e89000490f160300c0340c1000280340d40e10a000c1c0c0074408181070449800c450403440c00290ee45100f400240c03c0d512006800d4824840885081140070383c10300c4210b441c2205507001714940404404010103c00c032541002d042d030395442c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623814757 1250 623813507 623813539
    0x103020306221b030902030c0f010203040e1923040311070503011a09011d0a0f1118011e052b140124080c030703320f01030809 56
    0x181d01041590090b0540c001032440364030110007010104020b0b252040252014082680729015000c4065805400342038015120341c00e01549924007044941540010b200c08601556501d6149104410751b4128a0540b04c0140d20032003105d10001c19080c191410119052021600042c082d0304141e05203000303045007204100d8039041c004282c0040b82d00d5400d00100e01000800700581d500f08040031200c41c170362641d9952860b901100f8464402207900b582d0800600b0380800790340500d00d0450648008110316140700d080d0001c0d80e0010310036101d0001c40000e070182d2540c5c410198020014440501495616070010140c81400b8002c1041700e8803903040a444005111000c0c6071080f01c800c00003d0005003614030b12103e200f103090003901e18184e5086000841c545001040080d13040d19a2140e0016494a000125641e0b00c001d1900061645544801440030728400e1051003003400d01ca0310400c1841c40c0a404080030394050030140902149000500c0807880d11001c46502800844d09204600d0000e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623816007 1250 623814757 623814769
    0xb070f0e150a1107080304140a0806010602070510030b03070b28091202040603080406080f0a1b03050402010c0b09061b130603020c1f0b09090a05072709050706021c05090103020306 79
    0x1400c202c1c5d1501011a0008031101d00750015007030400f04484014a0540301d42c0d4540c5d07100e409208610040c1e1103080c0130401401d044040708560000c61078085074902c201d0000c43d04c0c1031a50790086004040001e41f50318401e40e450482c15141c5c1e269011181c0c00384261200500c144950f001c0d005500b095007920404564584c0d2144c0011980505400c1e00c0e0355454501502d80700c821a041451152101c0009000f50111f01c40c000000c0340d981d000c80f02d80444180218001c1c200104200d05116100e48643c01240b08487c0705441200002d00800790f918191012078010504000ea001610300c1c280038009040b91841c0110058070b1407441c00503102d074002803c991400c030000e01040800b14083c8030b94402d000454000b081400383c19104500c0644840c8032559892031035010142c07140d00084010710001342098046010b04505140c021440d421600d0450304860098800301d80750740c002d520400041350140107481401003002120112900d10f031501030302c00d10407181c80c5030405a0010024034617603189 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623817257 1250 623816007 623816009
    0x140402310501080d0917070b070606031a09010c031802090a0222050411210603100c03020c0c0118090507020703082209110403020405040f0b070f0e150a1107 69
    0x220424401541e581c43e100b6150700d903000801c00003450742c100100d4034009400d10340290700c448034001d00c0441d00c0c01208040301c0d0410403048038015100d19001012a072010b880010701100b002e01010641419410203007103c03401141c1c42c00341030603e40d85058000e2025100b580c440d030181c2d22500241e0301c1580e01002441034030051400c402c8404205c04105140070b1031142960701c01d80342006011000040062079000e000d08001d140901180190001965180c546801090240032182c51001100c000c0094981000e030305400030358041500b6040070820041000582000c1c01c0880c0c100135130320503044115456014000c40c3d207840310041850780344200000703c015030b0000782c07c41d200d510760000f0707002001e420307141091400c17041440400c1e208240c3c030611107200214406549003520f103078280805000700a2041d50740e81c07900540e900108489542480c071800031540c40c0c0c2d01445400001130306008505608902505901c01c512611b04c1983c400c640c60380c155400d1803c0030a8844070807030314051003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623818507 1250 623817257 623817349
    0x901030f06090908031e060913110306150901091422121707110705010f0c0206030a020a1d060904050c0c0d230712140d02040608060103140402 63
    0x60040342a050051300005140911004146400a4121810489164441529469404843c0e040440c0a0203040441c4098691085910080001013000003a05090307040303a100b05010080702d07030901685010340449001d4010764004002e80044c505041c0301c031040060682d140c01070a1440d071501300948c0055032305440d40c07181c20200412001c0d00014802124a1005180d0207502c0c0081250a40140780c0a05052101001000c0c01442c047c01140d07002c9040f1a080b043c4900c1d04001070240e180c40c001144106003818016903150040d12004007801401c18484105a86100f0542066a600380440300c450f0b00c11140030407680c582424495440c8076803d80014a442820190054190424961106a2903a184141014408442c2c1081a219954000b044d0002045080c840280603d0070071841f80510027481c0e05016410311120b0490f88140c10640110700200100603083d039140c041c507040302000f00c08100c00780c2015404514200c2c03508a60b540b0405910012000c4d54854410214019403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623819757 1250 623818507 623818511
    0x40c030204093011010504020102100f0e03040b090907020a1703041106030403020105040204051308030c0a0311180a0617060d11180f07080403051605010b130b1e0102030901030f0609 80
    0x1066078080b0f03035189050b4100c801103100c6416800410906105d028441c80c0c061b0094041004182050f030000d2062001a1110350350b41c0c048140603540420140001d132400104940c3e80c0d1554904102669000910500455215208140004645c203000b0038481192101190f00c0c0d88031440c04e01222108000e07000e400c0f40d804410401459070542205000f00c1c000c2d034041145855101000390100100380e00070700404002c01c0890b02c451440c0c0e000348203020203032400090140400c00702c41d01d550f218201c00340343d28a03c00ca1010003842d100d4140d400528813410101c14048070307844404003044009141c0c0d4444c22201c00f04505200c1c00b50789189035420000d240c08541c0d811140c010104c0c44041e101d4400d015144800500150700070f820a0b8095901511036605103110103003004003500e02114226483e54940360100d1032601d072001c0c2124201240c1d40d01048060400b020302014400c250952498035040e000360b03071b5030f0f032741c000c021a00c2c3c48200b07181c08542c0781c4003c078214010340040d61040c1d1880f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 623821007 1250 623819757 623819813
    0x140a0509041103060a050103061a090f0901080a060f05150f03010b0a0f060e060a0c0f03021507050d0b04110409180f05070509070305061e04150e07020d020105040c03020409 76
    0x2c002d000045200700301c01c45440f04c419441e140114229902c60094035007c0d80000e20320604200504c01500707050000030b042d580c09240c5200030604400c1c0c00c0c1c0c0411403d510805113081002801c1c0507808c61800d05c80d90411091401311015004c22082e5584c1030b0017081c0c00105404251020b4011114801011b0004250030350381d400000710346030403449641e00080103515482d6181c54084100d07201c4845694a0600000e9a92912a59124401001c0303080d0b2107000100c0204010752606144602100d46555890344001d405007000d03120200c0e4458403903840c10500d48500d10148082d18141c5840e0080090580a40b0084914000c403da40281505021001803c2080400030303540301684c0c410703151501ca0340c0b6507842c141c090300c00640303580d80e000c882c214510003104a4084460000e0708003c00200b420150b008447d003010303540ba00070801100c124400c01403007580402020410303407030910080000f81380c940c40340480040180070007480b50b501c0301e40c0d260512810000305034840310b4606441c2028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 623822257 1250 623821007 623821031
    0x110a060906020f01020906042c04050304030c170a03230c0307170304110402070f0f0302010509120f040b090102011d010b011209080d1e0903020601030c090507140a050904 75
    0x42074810303080144100000c2030300307869043c026124880d00151120381002d0501811840d02e1146031003614807c00c5890b03c411071000c0c0001d6090045000720003460350b03507096042010002445802445001c0000c0d20310b06010320000650021050b014070300300b0b0310f001040c1d00c030a200c0a19006903914050005c030b0848e64900c0d002c8002c000043c440e0080b0405445e40c241501c10358002150098846145051000f040d03003060b400414080e841940c09031070000c000d030b0781c40c5120328a441027070300143e55401c10006035000412404000001201e0843d040c01c00d035440d540c805204070f0141040c4c84401091110450f4000d40000008001214085240b03485042130301d8024004e8002e594009240c00e0b10090031116288144000107400c20542494020307010100c0001e0b00307100c005240d80c8620403854a012014a10503119114401e50180c0815450f6040103600c45005420207042a46010140800c25030040c684210011a0020701902d0b42002c3c50165010700800e5562a0400d06211070960a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 623823507 1250 623822257 623822267
    0x40f0501150e090105130c0e04050709021801030b12071211030303251704030806130609140906070e010f14040e010314070602120c1c030c0206092107110a06 69
    0x1c50243e81008005681c1c9582c00c000d04002c5461001d004c1c1956000b040c0001003202908552040c00703101100e4110703950f034210a080341d004025a02c2102c0c0044008889980c0c1030281580e002005c40d9051181c000c1514401d071103101a109248009900007e103108200c0d4034403946405a4008098a48900c0d0058082c1352010035091540280c4909007154403416001d20a0780705004000740c210285a0348a82d001d84907a0006018a0340c03000789940e000d2102c900d10b01031080030b01016500403446100b6482004201c10303026040b41c00c140c01c00030070000d40e1580f100e0442c42c0d044003481e00300a00005075505a030800c1e0a071100704148540043c0208401c44030ba292541281d21030325141e422403001c104141e440d0040781c05540f00503042414980c048101c400081c03c00d4602401c16942c00506020041a42540b200300340000302e5100c81c1304448a90f01404850360195001d406403850104603109030140c40c484d110f809206100200b4014244000c8014038003d004002d016a0009900c2e1000504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623824757 1250 623823507 623823511
    0x31104020904180c06110a03140f09040608031306111005040311010f1508010e060a020a0e36100608040c0806040b090106060e21011815060f050108040f0501150e 71
    0x801b0800250f0100030300c14002590307102041d0180d40c1c60341c0186051030784020560011410541c001d000303003c0041c41da0f4440c03050344000c0441c3c00007945e03680364400b403034000300602da4081030610840390240151104c020444821009034000d00150f107545500d01a180060140f40f862013561802491003260455644140d0080320702007446a20103603200c0c2e44601baa221203140d1005504144040b030703000c2d5203940203400341d503e41d400d002d00e1802c50a07000c1460900c0e0300c01d08248854208081002c138001416540340d42c103c04c107a00a80624140220b2070860400340310310420007030400000b6040c02402000342014004000035114203090904101600d00f0b0300fa00d01c2d8659510b010700001d0032070b001c2d0f209280303220300203030200d00f9a00110300c00d1601c1280300c0740138101a54880e00c0190458014948403440e5610644400020840501d985002c0306ca140c0c00002c174890790705e1024052a0f8000003a564401d40c480801c41400c5820b03d042c602402c160340700e84040003161301e4045107007903805185034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 623826007 1250 623824757 623824769
    0xc1e0f080901080a09020f0409080d0c05130503010207020d08131502011b0806030d08090703080406020a11011d0d050c06030c0c16060e090403020111030a091b031104020904180c 78
    0x11185440c0e13400c4200c01c031030b02080b0007580040000e05540281c00d040d0003500c11030b03020b262190b040000c05074146007580c17480180b00c40000d038000740c1c0190030f003400c541d54800b81105034000c5040007156801314a07410480f42e0061701030703100810f240000340440d03d058405800b59019101104240441c080d0203403440341140d030140b07108815007032180c91040c05070320f04c2903a00030018686440d003410140d40c0c208003c1c00c208118000d101303000c0046286035004000400580d80100080402800d254580907281e1a003181040508414540c50105071002c0740c0110500700c40d403e102c034815143c11840d1560020040e5088130b0040200044418a8400350031805102d900b59403d00d2074200740d1415540b618000d070008102c0c207409000f01810202c0400b44c0c445e219000001c0c582e500281003049076081103030201d91468650300c036441004444c4041814840001905030513490035541e40d9210b0103080306106001c0d50780400e01c0d24640d551500b200a031041c481819004010340307810201740c104102c0c0140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 623827257 1250 623826007 623826017
    0x8011a220b0403030309201c230a0203060a020310090f0e0d120608060c04031205042102040e0d080a0c02030d091a01082a2e1b030c1e0f080901 63
    0x11041950321440348070009100a04010200e4914111440012320220b8240c525500000c2c0700c00150180500c41c1c0c050006070b100031f01d011003840c4101840d01000820b1944510300610600c4503029850369030006540014030702280d060900318040c40244a1241e1020ba0340c411303c000074210399001800d41080a400c070000707010490300c607580c0c2992a40240c4900180030401c00c800c0002c01d04001419466221928120f4901a43c1380e100c508604410000b11780680762400f1020110320301441000da100d0341c10350142402e00741000d00649421030040c01100820384840804040c54402e000f101c03c20404031400b00007002d42c0e0b00b440d17480070203401d0b1401c44444402e40080785680d0005074080c400d501c2420742d03400b80c42c410840c01302c0742049a42d00681101160305091700f20031003001400c040030f64500c2c15401190019400601c0c0c4095440000704041e0310070740580200368010f8000701c50300e0b0041400400c185600d41844100c6080000150000181c9071119080060600061024800991364 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 623828507 1250 623827257 623827283
    0xa03050702210403060504060902030307111816230a0509030115080a08130b040803030a050105010306181d0708030a08010e060f130b1005040608011a220b0403030309 73
    0x1c00780121400b040340d40c1d030a050500040000030125000030b54428450f4001103000c20300d650100b85507400a9908a9071070005201c1e4103160301b0105209402101d224010203107c1c102070240e80b00c10407402d840e101c1081403032940300480c00345807003039170400c1d01020002503550400c4800017411500030740340462195007488845046913405522140a0310520409415141d01d107035280e1600798080004d004503100e42d010000b4000c001c9070080c01c01491203a004e141d80346000f54815088480507007002c2e06240c40d0a00602034244406014142880412030005048400710800c0c007104540c04080501c0b8481c034a00820341000104c050000310207140c8a180316a41c80e494031703151561044602076081242200104100d2130240b0310f411030140040c50000750042d1650200f00d2034681002840c02149000500b000100d40c010401d81c01420709034407000c0b5924070624200d605106100c050305590f00c2c10854212000741441d44100100700b0070080390764443e1740385005030280082c42d4080d1004004592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 623829757 1250 623828507 623828533
    0xf070c0c060306030c24080403020703020a0303030b01110105010b0328050c0a0f0912080906070b04030503090d030603050d08040201180806040b07081504110706230c0c030405090402150a03050702 86
    0x42e2000d403000ca1b40c0340032551010040c400321110f080040040e0f08520540340d0010260700d449080d00090350181d034021030340030b1414002401d200419400315040780e240c1801007240c0c014071002d07a90030040d1480c00150070719000c01240b2181e00c440f0b03c070011070707841c000078005141028030091124070700d10380710340e1000031012070295003028192003844481c458040701d03000015942c4c40140b1961000801e514240045615581e45011003150210041100001800100341c010860301c0c2e2441442e00d41440414115660701d5140c44810050100f4429404c4c08102103a0050142200000c940300841c1c0e030050740e81079144c1d46d521068a00f503884203010400b05110324850343c001417083c190f820b00040d01500350000d010007807100c44a0703d40104c0044c40800300055440c001c0c100000110080c18040e403000b0341d028804550040c042101d02401003040c0326481c203001c0181d03000c48070f045440544640d80da002081c00e80125020040701c0b1f01e00000e01c1c0810342d030103900c400c0c09117641d03600700c5401810043c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 623831007 1250 623829757 623829779
    0xd0b0f030313060e0d060203070e120c0112050606090d20010c0819090504091505010e190207020102010b09180c0a0503070314010e010903021011040e0f070c0c060306030c 75
    0x9441c0d4554200540003c0c40028025040003c031500f0160180c0c0c5191180e031642412a0010b580d060000703240f40a1005079031620340040d8007440000f00c0030b081c4c4400c40c0000600b418800c109056030741c0351030301c001030708a40c1c40009440b0740700300c0a06545180c40040c500005520821000c1428500030050208465485481c41109903035000d540c0c289810f030024040c40c00112100211001c01c6240f500220b51a1228010720040741d01c1a8000e55189100200d10010750781d05130442004042c861040090300244a80108800000b56100694502e882d0004074050400307010500d4110701010240710322240c030500003208209001098400e02018071003044a030007818880c0962590000c601403011400f1101854640e011036400001c0383c410304100306086d030308105020b4001d60048070341d9602c10030150007102208030080100324030301410b00414065403240900090b0103002c15038000b410307113802184054590717904106200c11007031f510100100a8100c1f400b0848000b181484001202130b102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 623832257 1250 623831007 623831017
    0x203040c170102030f07080a2a1d011b290a0b031b040f06120c0e15030d1d0a03080a03060602030c030415140310090e0f0d0e0a0b0d0b0f0303 62
    0x20382c0d00303208152181c9030100c400c01c4c40600250348c0d5035951380c40b0504d580e40b0b1304200c8100da100b5994048503880000809042411000d0a221241240aa16920581c0d21018120500d41d02c1c140002c40511750f42402650700d103660b682540c94070a40c1c0d01c03107800c0c08044070410303200394002c40050004864400c00c0c0b6445120101c0b400c90241040301c0c410a107441e09070012a40904200720004000e692049864100140208103603042510b4040030702060080346811540141521010103030245e040c0d010a541d50a85c00d5514104a400c84040016501c0202d84041040006100e00c200300d0307d0f4148550294822074041001c82d10b003000004c0c071180040144c4185014007805541082d00e4006000c400d824210540010021891800c2001004240256001e8403500034001019402d20300154200c4044940c082129448111074003880000060b08040e004424901041c07010844804141c1042c210b0f0800f000080300459507007100c404c0b0758031003044414100c403401c244862440130300d2346130720035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 623833507 1250 623832257 623832271
    0x105010f0b07110f0420030603013e12090d031b05091203070803100330032d1e060503030703030b030a0b0f160503092805010203040c17010203 63
    0x703c0035030344030034504055480c2202d072003d480440c04001e000400c01c41c02215020100c5104008424040141824030554000007100070408509000c0654035040b41d5a8501200075460301d541400c0300a18096010364000e00e911045090b21420031040d050744444160b4565000645815801184203403083c07d41c0700f64140c55103607a49440d20f580300380011050b18a0a40c100c5100030800e070360014034404001d602c6000700840c1412094114138080991842c400480244444240d04100711101f100b0104078942d41607040016041140c44010104040c1441b010000203100003034007a01c2182035080b02c15081c0c0760303400c0c0c0102018651200022500e04d800b4241c0c2603030007440380000207806544884c1107100001c0c200d404490950350350021010040704c60421030022241403000c11504401402900b86083c101541103250144a40e80d13102c00002c1420300c58004010039402d1112500c00c020031068010001350b5413072825041002668990b8402c01880c1101e100b00710349200c6040c8203890041c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 623834757 1250 623833507 623833523
    0x13020d0c18050a11090f1507140708010615051b0f010c020606040c2109021c0b060108162006010605091f02070303080a1401030c06170f0c0304081b0105010f0b07 71
    0x44c1034400d00c00d0801c0c5000506d034000342e03200c0b00100310100503005818090712070342c8154101c41401c02d0703007070a002c0e681d40440d405a047ca0402d0003017010b52840c0301c0c011200c601e402c0d43c5a02c0c866600511107030f80f0241d000c01c01d001d503500ca90814041034112513150015a001c41d207051316110300b80411109a52040b00028001d690940124003010074400d40c8190a9200030507401c50640015219141d400c00c2c1403020208161050304000310200c606500100c00d082050a502c0c04040c503400d1454032406030320411080b4150365441c07101484045480c00b0a140803180250703125a4080d045074440a00e0510130200001c1c1742b960031820034880ca01c201c4456014006142c9181c4e8195044c100103000100400d03156010004001403101c40c2d140218002c08102c100c0510348040903100303a98074100100104004c80411203600518295180c1245008072095030300e40d0355080c0340340140a200c58080c42d610822071204030340141504018103032141030f0300d5404a642d035881e0302c0c5160310034048001d00c80b10b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 623836007 1250 623834757 623834767
    0x12060b030a0609110307060c0c030b0415060f0e07020c011d0418050c031e10050c0408010219030c0908070e04080c0a050a03020601050607050c0411042d090902060313020d0c18050a11 80
    0xc84d00032f072480e00320b4441c413100064121403403004003c2c2d035000c2c0c00200c02d803942c119081042200000020ba00810240058070b4035001c0e50f00002c202200c054501082175064507006d0309030f03485c1c43d48154040d08401c146103242d210a032520907110703a40000c0503482840341d12203602d075412000300d103d1100c00184004020302d5500c0030300d0720f01408001b40703103084041090100003030a042c00e0000b005030300381112211041000282000d422038040b8164103040100c0b03100203100f80200000c44c40240e50744810220b20650b00c928099010b4403c0e01440945030298090002c10841d0019004d5000c610a400f41d42090381c81e5010f101d100d0203088000380c0554030503158680705041507408103030480c102c070700c00368942038850100305802441d01c0c02c82440030070b117000c075440d10a4107030042a000c0c040b9424140031181d11900003920500010b000740f05000366001d0b04100310750fa00103000c4040c0c2c4c0e02ca850311a00664403010904010b5160354464452801d010000740241600c1c0b10b150a0309407140c150500744 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 623837257 1250 623836007 623836013
    0x1031508030a030207290a0b010e090a0510090213051c0c0b071e030e010f11070f0503160e450c0d2307030503030a1b02060112060b030a0609110307060c0c03 69
    0x50b148000b244c0c0d050154070240b50150b510344c130bd00e180c80b4540080707010405051580b555001600070b5031016101c0791050200c01920f10740c01000c441102e00071030310584514040c58041e0f6464010b01001420060225400103000b140c10015180301030041d690304880302d288070150141d0010320040140025031203210b002e201c0d8002c281d0002501407074900f191600003207160035032521140381c1105c99400c807014000c00c100e1400b00811031041c0500651002100d28003000341d40e034002c0192096503c0100101c10142d031082c42c013450410550603681031f0120700510b039801c0c00180f03000b69800c0481d028842201902d0300b803842c00b1041e89070f4030061103800002c00ca00000c00200d400c7c01c024138180508540000860f6080024600899456100041403041500540003003c3d200e0180404d542000004114089001c002418240d400c0200420050741d841c00003801d2284a82000300390300d252403820300920039403a802e41601002030301169a41910340c1420341e03117002c074034800620b070f4800030f2428000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 623838507 1250 623837257 623837261
    0xa14130f031e1110031b0242061c1118101703130906050102070e011805070e030a03020607121e091b0605030f0106140901031508030a030207290a 64
    0x44d14486260000781340d0016012412040e28000003800142d0090b902204042640c1c40c2c0104000f032020f200701c440b100785d042c01e0202070720408800f0189100040c00940e454a84485108200c00300e03c0122800a0140c501140c03109000b0100034001c1109040780c48411600d200e415003da903009280d038816600d40b40c0d0100512610803581945030100303004100301c18800c3d160f10340251200d01e0f0040350711810800024a084041e60040d003500c098100100034000c0074001d0284401410071740481c1507034480d0b00503201e0f480d8400700c0c41e8151107000030746000e066010840600880031581d6200c640780c40500c11800386c583c1c042c140007592000d6100018a9600e5501254202e88511050206121801c001c640e0035080c1d0780c03101000c550004204048400945004c1d8013610043c10810040010a81c801c6100e014440f2a5814159039035401c0680614100b52903008000d02000c9030783d03406408000030003940040c5d030100c5118424102180300da0320b0a184012801310031580c0243e4656480d506400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 623839757 1250 623838507 623838529
    0x5040201030b060408060a2412022d0102120c2d0a120e0d03090302061e030c04094704050106200d050a14130f031e11 52
    0x105050740c0741882c081d50703141c1c100548024180c80d809040c103460301c01c50407016030303082e010406100481541c458400e89040d0856a00f61544040b01130100c0c1001c0c808a92003099a080c80b414000040c0008642ca1500390140b22008900ba400d49520300c1407414000014040da404c12540754014401002c180900d00c800c8800640c0b160740208a002010103070035080c91011101510b03030701f0011100180054000d881da600c078000c1961508040d20240d100200004001c2c04024892800018250300040c40800005800c0c03000714203056076070600b012a5800e0b0ba000e44078698101d41404001c500c042400a95840c2c0350071040300c50505150b811001c100002c1450f083d00002c905c88601c022256280c2d481414040d10058880418180c00909010008004109052401d40c022044e4441840d8040c086d507902200c1390900c0d01c40d43d0302c0c000b03452800b4021703518084203144e408080040e5512001c80c442040328029030040040304d9602c150400c00220546d406400d020304142c40706068103003025016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 623841007 1250 623839757 623839759
    0x70203041a09040f150b161713080f210f03250534020418300807020601030f0611070b060a12020f040e070b0a110706030506010210050402 61
    0x1d10700b20503580010f080340d890407031044c115595940f040481220b1500410702030400f040d0528200080c444585400d9510040c0080101003e001214010a00d400544241420180851410316245c1c01e41c1741d49c4015071418041c81d8410001d81c200c000e4031503a154610f030201104c1d0b00c0c1c9050140b80359100786510107000f09582d075501c2c0000460540c03042c2d000b81d211401c96514241c6d40d06440741d541508420b000714000b9141500c4103404882250021500c00d00e95040d40c001c1880e02030b4241c0030702020602c9101034502d04030340607440303c0c0c118030740d24001c2c0960b09100717100a141d0100404850003041204e801000d03a20020060021460810b1600c1c600ba106482c08240304080c240c9030450341d000301e0800c441c961580d1040c0100ca14201d059000500311080a10810604c981c00084440040c140600c0c041c030383c1c40303000c0c914112061284802800d84005800ea580340742880c001c0090a11201d2204180281d80d001320300c1e503219020322030003182d05a0042198039006810400180f00c007400407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 623842257 1250 623841007 623841059
    0x9060904020d140c010f11030a0c020f040c02010e011a09070806130c0302090f0301020c0703021e0603090a03090e010b0a03051503060901090b010911030435180907020304 75
    0x40000640c2d660300401041003c80280c8200b20300d00c1d0024011410003c0d4040502c48000c070306a0300b40c00000140d461115091404a01c1d0b50720b5800441e05e003414002c4203541080c200840d00d030b4030a0301500502c5c4d906402d0300080218103054be100d0000d07220301c60145640701414170041350b003161017a180d4540040001340020100402c19800c0f00c1121540314400020940104003c0c00d03610742405010216042640254608440c1c5160227841d002140070091081d074400640c149010180d0b0350000b86203001074407850340c908020b4803881c0d0fa12103000c000c400080c030310400855100d1485013502d0484052400301d5003821491902600540402006004284807018201000d96000c10800d40a20503860000800451905112100c000145c21403181d19040a40004000d60320a044039481600500342400702d910081c8940302c0030100907061a112401e070b0101d554402e40203401800c40380d0241d541d221158140c441446540f0104030391079400b50700180410805161540f03071042c002c2032000300f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 623843507 1250 623842257 623842279
    0xa0b09010e07031119030308013602070215130302060715060b0a110c060406050a0c0c0905160206190b150408060109060503280827010219020906090402 67
    0x1c00c0d0316084207a4826504400d0b010010740c03440c01c00b480c40c9504900c1c07140a083d01d443c150340700a06031890610907504078202201d9003956104000200740d00441c0ca0085214030702c0ac4c1d0030305800180d004480b050340b0566400701300003003a1140b0002ca03580c202c44041c54140c650701e16000c21240e500040300c10345020f80c000c241c180e844000c41c0309a40207820f15209060315009180d00050081d6900e00e400003559000031120b070300aa80f402c0c1074404403101d900d03165940d801c9a1000303d4032310f88400c0700200800095100840ea007441d6811040c41040c103000d2204240e200300b90120fa4030401659030b617080e0920499040e000c240680c101c11441d05010f04601071454080c021880d1550250f800000740c3d4000d8001404103030369170b00640e40100000c40042c0004101c40241c0e01400138260364951103d641d620b0350300b081081c01d0081d03400c4261100d401c044050000300702c041410b0704070b18805005005890722607400701da450340300e030500d076801a00a41c07140d604c078030621660f800041d205336030084255807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 623844757 1250 623843507 623843531
    0x52b1101090504140910060f15140c0601081501030b06010e2d041b0807030507020715020f010b1005040e0c0c01090507081c05180a05040f0204060e060403050a0b0901 73
    0x681340c0001d810b2041d0f0302c0e14a006110b00c0c1c103140c50101d143c1c22140c20000104211031114803484180c42000035000782c4001090000d0b0b030584c01c0e80c042c3d0741e4204004106580d40324030100c0c145040320b226206860701e0f09441e001580442a00740802894040150081009540300780c3d0002035001014041c651014084c3301d5207000588a4001e849020300c500e07203005591b0400740a5503001c3c104101c80070300301002620001d00b071420000e040408040d9501c0014600c1482004407200400c074080c403481e01c00a000c40000c0d12901c81c80310b4642c1543c200800d848643c140814450300160103561013500340b600b01901c040b603801c0e010700100c3d8240400d100516940000f803043c0300ca45841240207282c41490880241c2c1846c0307802c1020050640b4400810302ca00350850300b1039001c803403501007108414440800080c80f404541c0c0203150800e10740301103802d800d10b0303684c020030503034465807540c4400d08040000c202852043d4000140960015540d400010b125511a00c0d0001c000074008201ea9852007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 623846007 1250 623844757 623844761
    0x304211403042303030c0c010f020c180601030e2b020f0d08190203060906130e0f0304090612080702060c03040b031317030906040b1b0c07052b1101090504 68
    0xd0090b9001280400021810202c8500c07200f040ca48182c2c013550420300766480d0b0700e8584410510b4581441154401d98921f03d10030700100d080740310014000d1140c5480e0142031115280300b00c0d00135003c286070008804104000003101001490b100c400780d5014507002c1007148842d44018010300540c41640202060b48200b80040c506460303047e82d6800092400419200c1016140300b00f40c485a4810424404d20b82c0b181e86a03c0d030b215500ba40c4c0ba24115400240300310007048080e00f001d800e40101c082c1c03884a10303804001031046401c03400042c0b000a807030b0020302010218590008040403008c008100041c02d00710003800099078440152418165200034840700780e032044650300c40300300080710210204601e2448503092142c021124a04508c0c05408003a40c451380a44007520262091000032080a03680c145840100c0703442903400d0700c032803100000a035900b038180101840380b46e01d903070004413506011149001840c1628082204640d040d02c814202c020030400e0b0034101300e05a000403600741c030b4034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 623847257 1250 623846007 623846009
    0x302070b0a140711070e1602071a07030534020a05040c02030d0504080c06040305070209010b0a0c02040b0406080a080c010e0a1a251d011d06091809060414030421140304 74
    0x8a0014500051408802270030002a5000001c807402e4014a40e12200154010f441d400350381828440c0e82c541c0000003420366100c1045c0b065080d10303d82d5101c02c090104000c820031551340f0030350702c210690b03890b00d0401c029500f004801c030006910034808070720101c8070358201c43e40050085031010318051000c0c1ba110309000c0c0480301600030035800076140c011030800171500c0740104a290344080c00c1100001e4010110040c0340b4001e4801c039203c8403441003640e5103601503401807251004a80040410b03203001c210a40040c40b007070000d54608902e010701d440001c5055524960310407003803c0d00000e0340101403140800606a040d000c1e01e00d40c00b1244000b140504506540c0d426112140c5500403035041c080b200300e103003200e0b0703041101d48100352460504050381030352120b904941d640d4075901074501280e0f5680407a0080642662250280001c6082c0411b00c07034050b5020b13960510f1191035009401d0340d00e20581c03251480000181104003250350a0307404040645e0300c12503441540720540c1c5005031641d00a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 623848507 1250 623847257 623847271
    0xc0314091f0605100f090b0a091401020c190302040e070510111203070c051c1d041103010e010302120a0f14030c010e030306010323040b10080a030302070b0a140711070e 74
    0x481c1c5019241c003500045006c0041c40c0c4001494030700740f9070200c018019081845850810841c214019071302d0703802845412201d1402805003d0000c0c132184402501952a01c400c1c1c2c001c3d0310300704c1211190307000829202c0a440000d0701c144070341c40051a0407180ba0720318000c000100d00401c0e0342920a41142c1008501901071655840030b94421414094108090b0816a440790041105407181894010400c40d9224155440c04407100c64500c020034080e21020800c00d5001800100200c0d0407250800c056050300d0080c0e80c00304030502054045541c1d488010409403803040703800ca002d00054880c078190040340000b601507909200074038050038203444040c404090207410100030440b055916104000704840d05d40100d1020020240c041c00725000d0240000d00880780480010b5400d02d1425590002052000100c40d80480d181c1001802174210350002c58214410f04089501c082c128051410340d10050100c0550503190648103955245d2116604070540c05020400585445044009072017202c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 623849757 1250 623848507 623848517
    0xe010b0109060e010909020a03020c06010b070b06032103040320010f0b01021504060c032c0106050406031a1503010c08010302030708010e03120c160302010c0314091f060510 76
    0x4489000940042640d422440402003c400ca0400c10f80e400742d070380011103c0181005030340300d03268041100680314210307410109100d5607000241040707106e00107040c081c0c09030105403401c1c0c60b040c0c00c242e01d41806010030807000000b4002080c00011003402035401520a0902d0038030404200440149900000c001b801c5595486040e112072150a0103044001582440a0041886034628074841c1c0304000d04050400e41d9200d0508000780e000768004046118507043c9903041034200d0183d42c040c81d407100000e00c11942800700c002900e042c50b01a82042d80e500a1b940524000804002240100b00030300b1080001402c041e81c01c4103880070712625100302c1143e0b46030200356042d03005151402a69620445483e0301d410510405490080107440c40076004030110310b819200e1082c824060300841c840501207001010052041540540c00803104200300d46084c05010801214480510381c02c480235055600424400350858442400020210311609800210301ba200d60128000345001d209842c0891 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 623851007 1250 623849757 623849771
    0x1e060f281107061a01050d1a0604030b0103061b1d04110f070209060d0308061908060c03090118020622120b010810020702030d0e0409050d030b01030b01020312060904150e01 76
    0x1245501982c540d105080300da82e0b06a034400d1340000e100b40705118001043c1d5658110241502c3c900d1807034035103031b80b00041100e82c480d510707401e20140740b003000e02c0200c035041d203048050303615040d5018114a040c0443c0c7c850380500d02e8031141246081d1200c460840d405544d810649c5c482480400c00ba02010342ca40014a85441640c4180030b0581e0024101a210303540e08140c10000903440071802d43e10907004e8500515016080c4031180e0ba800040e0001002070141404100040c90040c01461141c51118024800004d01c10b0140d004444200300103500000c04101741d0b007101480242521900d10301c04148050683c0e46c4071072005240d40123074119040d503003220040011071810000d840b2a205d012104514007006507002980d66100602220103200c0070a10f000e00907038645c0d01280c00c054201055841c03e254a5200a008004069513075000c24075142c0150000c1d480003003541c038844041c1043e407500361101010020b4a450040c012103c00d1002103450350700154601034403018a0340d0600201b065 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 623852257 1250 623851007 623851013
    0x324060702012a0c140117010b0c0f030705010b1c0506010902030c07080708071a13060b040b1e090702030c0c04110712170a092109050a0303021e060f281107 69
    0x3016500308954104100160f4060b030801f080da000c40c3c1100e43c2949501c0d611002541118203224282400c401c40c0d00000c42c804c0103114044d041042c00381c5046918031040140c0080c00516401c3c1e400000d8942e52100e03005001c95100c40c2d000710b8100445402e518100703101951800000c3e4414002190414004900c520400c0010246216254511100c0111600c0e04c070707440b4014410b0081001d00455291040140b8a840344d80c810580c00c80094200c418010702d20040c003440a8603404680e00410740c090016040510110a543c2c3d920500005421000c404c041000080c0c4610141c110700400108603400024085105518109803a41c548010540326a20402585c50300141650001e07420000b440c000522120b520034a59100a9410400c100c5c581a0407100b1200030340003590008001d00c1d02006041d00050401030a40d03201c030101030305a5640c82c05a442e03481c01c3d10701201e014500700c040361243e44006d183d03c00d499031120030191002010807950040c1c46d10346201e942c0c5140e000481d5814 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 623853507 1250 623852257 623852279
    0x61303033201061b0f020f04061707050907050909040503040e10080115030b0f190e0a020f0307080a030521070908011404050309040f090b0901020324060702012a0c 72
    0x10f01180c1466041c141003c2180d040011180b20b000f8142c0d0011000f2008540c0e0b40c800c04041d030a0b014104104007a1035030700501c1c04041c400410440d902c00c8a10004182c5040e0000d0740c4503c2c942c4c1c3e500c3c0e0800e454201030010001000c4d0040f81c2500043c0804030300c003c0074650b0329104441e031151042c4410300d003c0d00349084132a41600c4054000751100c050010035a030342d080c01d401c030482408040040c0c0d0340c64070a100702d032590452140c609040140c0000381c1c0d180052026901c034000c071405603980310080c041690760701151050f5030264001404600100b4040c10107054101c020420710320b10384a030001c0f40c00464070103d46400c00b0540c5e003002800034400074480c440c8802e6000c040c0d80e28a04242c1c1300c1031b6590103855406841140c403081d284000304081d13004801003079400850f20419042030310b4910f010b50000c4861105902890245013007e41d001c0a02c00c0028a001e081c092400403a0b8004440182c62903140c12251551035104074003032150440018429402401c18202990600e031400320 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 623854757 1250 623853507 623853509
    0x212060108090a050d08091e0615040e0601120218070f0906020102071110031d01270b01231c0203120c03041818030e04060e09061303033201 62
    0x401a0300c83d0070754100007400000c4240c0c000c0f20904000280f03a032010000b41c903259007a002225612800850a040888000f90480c000d086402440521420010a0104840b0032040f01c400aa101c078004000b40010b800152580a0000c0c0890308030392a030b030014154071281070b1001c00c005255400302c1c2d03007440d6021034040040e05c41c0b0b20080d403811180e40c440e0350420701242456849546052560714526004ea400f040d0700260200ba034209903d00e005226008001005011000c1c0d04d032041100c14031401a07980341ea0640d4007410702426039003415002440c105001c5e541a80b07186c03a0300189020350f0384100701c507004029000c0f003003c400003141c414141801002d2000114099040c000c2e42482d50010003038505592411003a005a025000314080280c20901c03410800d2a0203105044103041d40495809610740003030f102480000d03500c22102803a0881195601020b402c50300c04222401700c000b240c104403030701070318021030000c2452241187c0000707440d0303451a041e540e00c0141505040c0b07100e1654 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 623856007 1250 623854757 623854771
    0x206160506070c020303221e080c0102030f03010317130e1b16021513120c05030604020d081e0d0c090e070c080d14070c02030f060c090d080d0212060108 67
    0x3c1c0c0191459012070303500d005d40a140c0180840406410081d0080c0c0044400101004c3c20602000014a0203102d03000c3c05a0194180f98000c105180f402c1f54000400c490140c80b8021910713185a203151609a0350a105818441c11402c08010454091346080c0480c0090804d4411070341060914101659500c5220b2410882c0d00394180690b444a0558030309103030750207405480301202803149866883d064414480e40300c0c070740204a00003041c0c5410b000302c8810a5403041c0c0700d41e034940d51034104042c4d035440115002075111200545030130029070800b000d0424141b66003407030b0811040b40a0726000ba0b41140c122104c803541c1d141040780a46502900c0d08004104081e08403072541060703000100785042c114400380282030000395190202d03025522018800a81c03080e83c2c1483c1c248508000c10106001400381c3c46807040c1844600c618002083d00c90188400c240c0c02445c000e01d0606020102522039001d882240e0148042c0a8100346030008080600c2d071000d2466a520309070b0009005201c01500071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 623857257 1250 623856007 623856017
    0x717210c030409050f07110c060d090b0108010b011b0b1302040b04092004060302031011040306090b010608071d190503030403081b0d080c2a2d0a060e0703020616050607 74
    0x10f47c451140c0402e1101c0707881c1043d00d4180d50742d00001d00e03a002600c1454002003020100e0f00000543c1c10043d841b8620070b403826a00c0c005c048000248030751003410561409400b0850213004101c041000301400040700d84007920104044400c100042e0454401201c280e5400c02c400920800c21440d24800040000701154100300032402c0d600426600e003607501207420543d550710014420000808190f400656006805101111540c075282079292000c0c0f01c0c14000c519802d0108011a00a206124160320748802041181a0907070400200159000b1205e000b2122508045100d0314240001c2c07000d14004d0955513a103c21800c900100e400d10b01c02180000c1d007282c440455140c1c6c1c0000d116400c5500d1000003030721000200384404481d41c04051500c040c0c4c00c034085100d4800404200c61410004042c900803121164650b004090070028500c103c81d0b4029604080000300c0e90303406428480b80c10720450b04980e86036808110141d004144e5a020402900d006504000080201030b0b4850317414544 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 623858507 1250 623857257 623857277
    0x61d0303070b010e100f0b28020307060f090f020d1b0f1508041205070204020f04060309051b0f040e01140123010f140a0e030316050717210c030409050f07 68
    0x411b080d96003160080002c1008001514115440d100c00c2c003104540104900042ca0030003070001a5680d070215500702c0b0f14604040368500309000c10b2086c0308c121608000e0718100050b05508001114411071022980c2080b482c032030b595a4004120340e000136244000100c401c0a051581007081c003080d200c02c150410a0040c100070024800c0d031010320004146081141d19001c05100007400307070064405140107244007060001b5140d5154001201e903034000c900f5a010f20415600040d1440042c01c032498002841203614019410329030700040740428844000901809020f0303400c0070b101004c1c1c3c03003016040480c00009144403c09ea12104a4610900300060303850400c85001c0d01a17201c40c4207005000d00b022502906550207080075200961300103054907a11880080c120342c800c07100305015201072140600225200c50302c052544070b41c12220008110411001c64442c0c000c8141c202d500c8810700c03083c400c151020004002a1014044000c0082414a4103040c0c800030b5800042c5803004001021003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 623859757 1250 623858507 623858519
    0x102131403012c0a080708030a1820011b0c150f09030807082a0c0409051b0118030605070f02010209010c03030b010e09010905041e0c061d0303070b010e10 68
    0x403c0d902180c02021004440c00b0340900c100e07003002090540906100000207000e410010000015031069103051801c001c0e442025411342070b60044d000f002010441e1401003518081aa50114000c0a0051401101000039144180350a00c0402421104000003600074091400e00b80c0f08904241170601e040e00403103803101d9000300a010944005030518100248000c14041502d08a4503c03c0d25500102c3c0d08000404003250030707810380220850b00d401201c40311100b13032910740980502e0f0354004000348180300300300014007c0310055078403460510103100d4004218046408a00008500403000010103250030480545410300e008450411a4070411819440d07a1300000c02d0401c090300351600099503070011005071182810301c0c861a9000d5240000040e540000c3d070040c034461881065801080c07056010100f41c2c940f19048001c12008440e002406414441c03502d000c0c5e602504030018888a40d00c2d0701003030650b44454000d4074410302050041c44242415080984c015880403145038103186850 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 623861007 1250 623859757 623859791
    0x60e0402030c0105030f0c031009020310090e0c0a03110d02090a050a0c0804150c2307060605010503190203090304050d0b070212030c0f0c0c06160308060927010905010213140301 78
    0x10658607c0c941c020000c5050034a4103103606000d000812021980c174200b640a4512110443c07048100c15406c144898603004404a211244d45001510760b403412821580c9590003032180c021140e03000f9500f00c0c1d4000260761000c005902815912a0009041c01c212603807005444240769036809001003a03007808001380a01900c01900454040700250b01d92504904a881034924115400c64180c4081d4140c00f00c1030340303801420118803401082216654440044d541404211244400b103000039241c50100744164006560060b000b005507450542c07038100160300050441400c0d984034640000700700c840303901081510611907421250b04d00390301d01035500980354450ba107210b03070f4103100100d41141c400c10704100d8100070320001040c40303443d06000c0e50032801c51135200324142d00003a50500400c541d420052842c501668051480d5044120903804181b82210440e000100665072500d50038007040c020302c0603005044840d0480440c6a00e40b80000c4103142a41d03d030b081c401c3c0d140100d0715075018924 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 623862257 1250 623861007 623861011
    0x60307061407020409200102061509010324021b060f190b010e120102031b03040503070204181506260c040507050705030a050a09080c030c0f040f060e0402030c0105030f 74
    0x1c0c0381c1540c90314a8404940a000c0c0071600030b03c1c80041100316030a4444010082004a0080c2e08981d86a62040d9000c0e0000c0e2680c0103243c1c22904c07590051002c80c8403e110740000c010710540708070140c690030f03401c03404a84c404003a1110042080000c03929010042c49010b0b0840343c400506070300303410101d01d020074031910b5442c0c492040c0da880440740034503401051091a0391000030080b2024022070308204c1e0103076208075071b12a658054007038100e40b1021400c00f81d034007172900840118100310b81642403000034196050714001210b100030071600002c01105205a0501c81d1110115030545800001c10000000640304d07041d9020703144803c0c02d0184000341e0349250a504690204035501e079041b082d42c07a4851060084d005001c0001c404140f650418010841ca41c50340da1a01102651107110b42d4a03003005a05040d4550003002454449140c8070b00341c016140381c020000031b00e4140e41c20304c2c00100c8426a0210034601c0c2c2e0b8500b0002980f07001e0080c2800310702c0a0074400c0c5503280144007600c00e5a80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 623863507 1250 623862257 623862287
    0x90a051f180504110d0516020616050d0504030207030b09030403020f060f250c0b030c1909050319020a0905040804090207052a0a090606020c060f0c0d0c0b06030706 72
    0x200c4150340103482401d003680d00074400548100141010729001c85195401074004450b403a0924000c1251042e82c50020f400c01042035010340110b84845400d64051449043c0800c00c1207030600400c03445081d24030401d0b009a1080d001400c00c0c520714030f05902180300081c00d0480e160000d000800145e213401080901c0c1620443d51035030f5803100d1004003045130090000c50245c551800c2c47e032922030b045045411055038010b0519454403543c0f1144002c0310303c0201e070381603030b80f10b001d011144802100f5066001440303d1824030740001030311400401e141034a0300c1c440d4810514122954802d40c207102500310041c01d6030341801d1116142a4444a007644142d11421558076400580d2400307020061280741c0050750400300c0070065203500f03411104406044040203202c2d0100c030500140c0802c041c800d1004460f0b030364014104e04ca240310700b04911030704100032a10b1001e01c10072030400d40e84428003c2d40c4a0102c182c403030f40700310045401c0090102c031000f008980654403010043c00000d41285215042e801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 623864757 1250 623863507 623863517
    0xf0105030a060e01060801051008060a050115030207050705150a031a060f0d110706050a0b01020d2a020316150c0203030d0c0c0c24031a0d0c0812090a051f 68
    0x24a00c0c83e550b006100c0f551000085501e04400e1000c00c80240c20403104a035041804c444980d210200320314121003080c802d4290300028103580c040d10070301079005042054020825504129030743c80c045001d880304221881b461410000d408282142c15224040030a40c241c40705412800c080d40124280b403081d0f198080380403002140d0004035501c01c0d0031803036103071000580c0319894000e140303000006001c040c2c45003500d6a040c10f42e00e80c0c0c06e510010710251040610383d1050003100139600704c4d1401c054512005240e20b2203500340000545c504100d18a2a040c210072203205091401c1840d0300c6c5010800c000c0001c02c000c00000f0409039800209580c42550102d80006040c611a00c090f03030003c01d04100140300780503180000640005039589070111180c4055100484502510203c0440b8000c00c442c6c00307c40007000c0c41908d103040840358800f50b81d10440b9405c0c20740f5200c40c41c0500c0d01c00c0560201d05c401200090406d1941000740080004041c2582c0c800c10354000c840540701c082d6800100801041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 623866007 1250 623864757 623864771
    0x702040e03041703181009150c060216110612072d02070303091e03080702010e090109052d1b040b0412021f0203040e070201020d051e0f0105030a06 65
    0x40c080c41110010980d090030109014840c0703010a850750003c0a000144046600381d8007440c0c181040079942030b0040b0384e52006203d00f000c600c10050801003002c8010800307402030a1001408900c003c1081448980700b590080c01685481500ca90031001030700d015220a001c0c5858250650401e99009885402c0c078035100c4d020800c4c1d45034071007468521884240725289105802c40d8000c921041a28025640e0120907030725203591042d18000d10070f9903605c10014102c2003010621350740c090720b810b51051405c6411501031000042442400f81c002d0b0244075912800d01441100d0541c07500ca580c8480401c04c8500c070044181c0c40083c0d10020113184a0500c81e1490441144c0e0000403140501206074170345840c0d940f124505080c01340581401c9008142e44100c102c0d540302100d01420314540785078002c6240c1410040c0314409200003030640d1041d076409120300c02d0b4600050123001c0c480c13800342c400321a0910316198503400380700d005883ea00310141d1201c018403a5031404586910141e80025022820b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 623867257 1250 623866007 623866031
    0x1080a02130b011b0f060506040605033c030d0f09030c030c140d09050301050a020c0706260c07020f0a0f0605070516061832040b0406090e100b06070204 67
    0x20640c43c6008103404e5005110350000c000308a030f04070b50058010702c0d0810080d80d4582c03d12044880034010980d050f40859600108002c40150003103071014060507243d002c81000548001d451880c0403580419000030601107102c813524456000700940b07403141800b9400e001c3c0c9000e4a00f40404401408001d00d0410070301c02d04c040680c100c0301d00c80c5090116082d80040d80d00003081d600b024040c0d41c0c429404c140c04620b0b54007e6000b40d030441c1050202502500e40f40c000e06517081c9161142a500031009183e84490302c07041480000c2c032a6175909030f415a0b0301441d104126016a81c0d850071445088108010710402c000950400107803040d07810b180390f450000f030070700c0361a01c0412801d0350448140090041115030303001650481c40044004602041a140c1c1c03001031004034403291207039220146240440040e00441a24040c2d141d0203400001d0f003801d0b09000c207007940d0442e0003540d0102d460748180060740c1c408005203221003402010400002d0005030015510b032242c0301019202e15142c100740749203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 623868507 1250 623867257 623867267
    0x904180203281217090106061d090c03090708030a0201060302040c0302120f060102120c070f0e01080d08040201030906050f0f09010c05120a0605101e0e01020c010f020f01020f09040501080a02130b01 87
    0x50014a4803016245c5030403241c44e8081c0c580c074090500041c00e204008103001c0c81c0720550b10340c01a4001d00d280301650b100f176002c042d01c0d04014100080d0f0300c64040e0004194105000405904030591b00121301d071811801400240da01b0303000c0c000304040c4104000044500c184006d40d42100c0c10b802001019124440100e14013a10072409043c10b40000580f90b9408c1c1d80001d016088821034400081c01d141e941c07518001088003417080c0a07464004210142000b4820070b030303150307109205040002e44103289407070302000c03a40d040303030280c84040303141092100e54201c02c104180d00c00602c40080c880782040100051050083c62080203000c0702020210398180083c0d0400406020068500c1c01e0b44547c01c84002c084000384556444400700300d9840500031482203149282201068008210820f0908011070300e10303503044518811801902d100b0380346e2940c01c0c001004614610407400341c6070006074007004100d65044c0d00c10345a035806508000010707111f4042000420700d001c3da000030444041c0c03005881c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 623869757 1250 623868507 623868527
    0x2403010f0204120c060c02030a0605100b0d020318300705010e07030317070c02010c02010909110703120207030806120f01050a09050607021204170309041802032812 72
    0x940c1800450049004994141d00c00042401820400c41d071a83da0f02c0d050710b00850243c0040d405810a4031481c2c00714810340c1019030040a40c402100f0080c1e07552078000b9203900420b42d034502181e00003042c4403800036030702c0404000b10301020281502d0b00c5182805034445501803c0520200f60074000740d43c0d101440b1088c0da180b03540290080c845901c0d007041c0a83c46051a00084000c2103000742074040d00007491591138815000ca071118590164181c0054822201402d002c034100b00c261800400e40070b055006080c0054034964400380c5030310b40707454080d00384420340602d260030510600071280400c1c0c0c084000c03900081c06072546800210f450341100c0c1000888200401c85608083c1804034640080d480441028055400e81d4031940b035081089032030307910540003070381d403080240000c0c03150782d0a07556507841c404505402c6a2500f40380c00c02041c1640d2074409548a02c2c0010800c88080d1f0409104c02c5884c03c1440400f070a8074510a40203591240d03401c980a0644000078000c5040c0c01e0041000d09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 623871007 1250 623869757 623869781
    0x40614101a0412080703081b09150c0f06071209080901033201061d090a0f02040305061314061021020301050a0615110307060b030715020706020105060108240301 71
    0x2082da0215060190b0300d82d21461080f0b00142801000070368814002c0b400945800180e40c4440c43d1056082c2080010f108144002b40c80130f0042140d000949010040f0f840c0c0d120200002e00854900444042c040c232854404447e0124109940d000000302c18400701e0384800c10900380010014002c035005e140c200c0007040300c203100c910311000300f8000500420b030040c100e03401551800f400c0c0031504902c10549900e02480d54001304c40d08082480604550003000078150f04150040c14039503607890b0945802015501e407103c138400e0b203100e98140031070001c4904401a40b103000300300c142441c0c0603c44404055120b01d9690f00b001541085040b545112007401d85c2e42c000b0000c2c8054180a2441030007810036228100307284c1408071440100318000c240b0b8031034002c0d506024504055041c1c903982c0184c044050f80701d034980034100d40400c1d1040d119180c0b10240e6643c0d40104411810600701038210b82000c1c00f014140484a001c11043d5102682e01400035500ca98100c003010003008007080c00b412941d4010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 623872257 1250 623871007 623871029
    0x20a020a0e1b0a11010c0512070f1202070b060f09070f1101091a091e030d0f020403060e4611040c0302090f0a030c0e10030f030305040614101a04 64
    0xc0f105035601c01500b161308112503000300241c80c14414191110300c2680c1005c81d01203007400001e06100d008591003150041c80782040300040030f544071090100e92240314200c924a9000d410301c4501c2c100f010381c0c43c1c441d95048d50100071f1030401e548081c1006603442c6001c010003182100240301c0035400c1d0000c481c000d900c05000c01122120744070030801c25804a9080c4481c3c821804001100480080c0707009969100c000075618099020340070402504108200d50242c80d000c1000000150061290f502d004074010040d028614200d400306890040304a400016594900e41d407848c0e00041e1052603030602002c0401c42600b030202e18100c00d415402c101035640c40303071600c2d9404a285816400800700404200c45403606944541c0401007000803c0c0809440864004404c3c00300c0e4400010803038003c2600c5001c01d01503075a80e5209180d078007002c02c0c102c00103906c5000b8801001030b03d000c0d14270b81d0300d40d6001c55440b07450324111800040340304c0d110303403610b1201c2d1004040907120514100c802900c04042c5c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 623873507 1250 623872257 623872267
    0x91e041e060605090603280f020a06050a12061505030703151403070e01150c0305300124050313140a030e060418020901050d050405011b020a020a0e1b 66
    0x410780003061a0722071607000d003041a0014681e4a80419406041c2108036042404103650080302c0d04c07008480a8104c07040e41d85081680e026030b9a0803003030360060406607141c540d100720b1079034000d1800420302017800840d400c081c01400208623403031700401428041e1405a4807541c60a40c12006001e4802c5040550360b20184003203569500d00d0b074100309075074054048844265840820600a04003481001000268406a043d00e1031080c6503601d03142d8000e18000c1d042c4841c40360308641400740c460004540480700201c518040f403042072140c0c0142081260510000f0507003d058070f00405420b1100e00f0064000300240079110480f03102c0300d4070b0303800680921700c40500d100020350318281e611040d00801c06010520081d890040b04960549030360204101c00110403c1c0014007a42085c60181c0c1070260920101600c1000e07031092912540c02100007062a00303001000c480d080e68a00c1410045401c070750603000160322071081003000c83e21800c0c011140d50351441c2c111103885400309440d450740f90001070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 623874757 1250 623873507 623873513
    0x30e0f011407050a05010c051e0a030e1603050d0906080a0915140a050a0902100c060f05070507030e03060705091e0405070c0b10030c06030c030e01020a09030c05091e041e 75
    0xd0003118440c861170080268249500f020307143c90058203a0500444541c07010325620001000280c0360400041c10701040c0311080c0c0754000c0c20268000d503181c9e401881240200309000080020220140003410130b0750302e1a007016030041c10480c0090240792000d48440c46031007001900c0d2583315109460080412440d40e0160702183c00410a42d083d019007070800c030200b2401c0c0c0c80c03031049540d060781c0108401d41d0306900110650b20f451f01d00c50b0503078a01d0b607121106103080b03c1c94040c092040d4140d9565a540381020329010300410882011513001e54130000411618a03004022200344000c01c69890341c0854254000d40030055a000000c0e40180c1818248840d0640001c2800300d540d105401030503440e070381c0c9002c82082440e148009009100b01240820540303000f40c1c8424444d440600d400328041c501c0080c0542680d1103103443c5000103001c1e001c10810700c0003000120000c0d00085a9950781400e041d19007884044468001408440c0c0290200f420081c07079041c00e00d40008258200c41c601e0441e81 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 623876007 1250 623874757 623874763
    0x21f0204050f060901020c1203040e0c0901020d110c1c0507030825110f0118180f0603050d030c051204080d05151011100e0303070219030e0f01140705 66
    0xc071425000310946101d45030380d441c000042d59924001a0700078014003190f803040100784003081c0360606090108000100c0c1549124510510800900e01c4c000da07a4110780300020303d0122035071030410810200144600d0307150401f08036008284801c8a180c0503821407406042d41d080ca40000050092083d510004100050b81c0c01824803500d00309002c02071200a8a510945a01443c1303004000300c62141c5002528a4002d0340280c07074020603d03000340d016001200f00c08950100740c01c1154440500c00340e50040181e2405403903103400a40c0c1d018801545141d40f40b0350395840754a242400d043d150880044502d01c10001d44401446a5800c0f080b170307060600704441554050610b00c11105c2c200300c00901e00d4401c3c0381c0341e070b217000002926107101f03460309800031111408403a0130640700d03014007920025025154010340500402340b1004c1c699a0401c0000640707030280d60407102c86060f03200001c079808260400040e1803900010342e40d2951840024004803800c3c40c501003040f804010105068080c01000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 623877257 1250 623876007 623876009
    0x10306180b030d0207150c0c053d14070317041a070305071e030605030a0c050f030c010210020d0906020f070b1b04060e041803082a1603021f0204 64
    0xc2d0180c40000034041012a11958240100c50b40701060020a503400c80c0310340b01410b110ba0160355103c4169407202c00162580300d61104950100c0303004071400c011070300340042416079140f13581000e1aa5904002000e0043c40c0510401004a240410184181406004c161081a03441c00d0540c05520386850511a07401c0f0b150015689803408400107003215001e4880c0134010321498681ea03c100155140c00068540346c07001100415484400c0080e144d10304000d164041c1d40710b400e51003402400c1001340245803041c440014440d80c003404042c0181e0341c011502600100c0303030003800740e0782d00e810a0006028142000006048600c000f0780b08005028060103000f485100b000d40c00c1c02c0d82c4840c000d0716509e410343c401c1c3c5c40111204000402602e4003450b04070240072009030002c42c407190392008074003452002d00015400301d44024108003800030400074020464642c0c418001d00d0100001c60b911450240e00340e21004820071a140c00b05050003000488240c104150081e5820110700d0b44031800b941003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 623878507 1250 623877257 623877259
    0xa03050a0b0a02040b2b0507110f06040b07270308040e0702010b03030d020c010b130c0909020a0f110a052a03150604090c1208031608060904020f010306180b 69
    0x12a02044480156000322001c03030710030300301041c1084206c0550044140c00034400c9282c5500c019030350301e0409130703900510780305a00c0c9460301d01610481c1c031511410b080c0341c0f060300411600035030100000280e10161142d0820442c9c42d00c19140c02d1a00070190707050301c0e4410800004405a54000104443c40c4010404e40360b0b60f10742a01161520300f000c2c2d080e903044500c50740e4550014401100400c500c0e6003c0c0480384150000890007610800c0803560f4504070f020454500c503290341b4400e0300d4503080001c4d41c00410350707000304528003401d604004050540100e4900200030700858a00440d000030424000c94541040a9400312001c180c08503c59050481c040c480000c0d200403014198940481e154040e01e25005c00328905035101d0b420000181f51f20172003100d5180083c200410a03107040a09081254490501c442c2d0340d04048020385603140c1020051005c00009204001c02501c0d00245a41c000e039058441410003090100140c000d05010b0308903603240c2d0640b440840280110341c00013202020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 623879757 1250 623878507 623878523
    0x6080603030d0e061e1005310b030d0807090902070804030b07030b0108070e030307081b03070302010501051306180b01050c0a061a06070b16050f0a021e070807030b0a0b0a03050a 78
    0x181e00032a008185411120640946e44030309007041541068442c004d010004c041081031140e0102c4400a81c8140b1340c0503221985a4441510425007000c000c1c68980030224100310426103042c070402403142000b03008150466802046120070003d5242c01c0e1006554000e8841c84035140c04100140105840c0000c14002260003010036800c81c085c00200004c103074094061450b020311510b6440c13865000c02d94081d200741c05040b904011030b4080c03000d040c03524841e600200c4c055140030b0400240001500b00304818906c2e220040100707a00818070310000c039010160114000246c03000584580c01030b006105c1e0f15010315000c54042095070391001c03100e41d941078205c110010b0103000f48442406460402000e0080c96804141c100e100c910b10034030b00725400d1812a10340940301e003d4020381d40243c00102e0159010ba9079107120fa501c031000c0c0040403040200205401c514003801c26503036020740d01c40030780107964000c0070400c1c80419401c00290290050042122107599107080d07680c60301c4400b42601e50301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 623881007 1250 623879757 623879791
    0x1080303163b011b02091302060408030409150b07110424170f030901110c030a061a011d01030902040e010507111515090603011b120f090c06080603030d0e06 69
    0x1d8010140400d104000c003113030301ca010350745601380282c0b840c01030000542100241c690000581e18000100040c0800380065602c84d460400840c0607101c000c41e00c44c55440071f08606220071030701e1609581c051500011420f940c180c8681c00b007802401c0c0f4103818200d1745000d101c20381015505015a03011607034031340ca003281e011a922a846031205075100c40320040750810498404290320542103449880100401d039903080505200080c034290b00454110b52460301c1e0180303540406c1905014920401003800c1044601141d00c03442d0030343e04244001e0350f0605540b000210159100c5900140384503111200810aa08142e030025040c003456845144203882001c401c0c00700320544069050044002e40580e01c3d101c1c2c1700800308010f0840c001c0103960503642c0d5402035001204501c0800c0c0110b8140d4898210040d880e440c2e40c0c060701d8450300c0c1112417600b040189800a101d12442e841241d010b4a01090b030758444070002400c620070401c000a0a50500c003c680050201103031860180c105c0b1356480c8501c3c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 623882257 1250 623881007 623881009
    0xa021201060203092803140f030c0109030801140a0b0d0e0111130501090e0a050415180308010603020f0f03070c0506040503040e06090903073804120801080303163b 72
    0x80c9041e060351790701c032584da00070400001e0114060030203000704103800d4901514036000c1440c5542c201320150301d5660b440710306643c14550805641c5000d00660420b07014400312310004a40d2400f1144512550200d0005007041c440d00d40da0b00103048100e03507200902c030320340e01243c0d50b0581c0c1d0030840e80201c0d030b40b81e4048001000d602800355039049130210300800000e0380e07820080d83c0c0181030080c01520800f810390380b00c000018181c03040b8580704200c2a24410328801c1801d009000034070580120061520400c01034986020504c10b40c1c0c2550344000381c9075a03030b03a1091000c50721800030030001000f40c030441d8188400c020000c03006e081900c190000d1401699902020804114020344525050340c0003003245ea8041401c130119500c0d1190b0007421039460b41500488002400c160904589a456004060100b0800210b8841140d03062500d03080b03c5550414550039200d00c03025050026050001c040042c0d1240142e4400e00e0f90410801010324919006c400c0360a00ca411544456038080e0390b208000349 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 623883507 1250 623882257 623882299
    0xe0901050a150308031b0d02070c08061e0916060801080f03071509230f06060f090f1f0b072609040b030a020409110307060c030212030a02120106020309 67
    0x40124103150324007299185484211091740013034405600100382c500145016041d141c000d01540b5a00c4100595412042c2450006a540d03030f040040e81d50801000e004101407440c0c035000c0d0807824002c1044840e1144e03a106440c1c00044072b840c07501481e03031002c0095003e401039245412508040103451100056852494592080100061151000c41c42850448400340d22078850148680c2400355600c4550704e115401c100e8034296402d1a50041451030b400c800c0600400d034001405403150140201000700141c0320f44001052400ca1050340c01c00a02d03643da0480604260200c00c100944c001070319007003600410390000701c043c1c5505000c482c903c0c20b403100014004034408502071a441c01c080c0e03480c003084041c01c003085d260707a0b0510506100781c000d41e6451050700401845a980c0362003600c500010325060111139413040341032100c0310180a001c01c0c0c011400b1030f0311483c2014030980d01d50714059640000d0041128000d00c4071381840c008074500742c0000003400660000c07904018448028046501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 623884757 1250 623883507 623883521
    0x3040f1a07150e0a05060603012f0903030d050a14010e091222231009030f020a031a0402011805030a06090302011b1d0d020d020d050f03040e0901050a 66
    0xc4910200030714400302c0d000441a074a498003548010410001c200c40d201c0c5441d0103858182c0c0c1a404c0a000e2154525091240c00703520105410106c0c3c200d001d1105907a0118112121180d0850001800e0304039940d00744102d0760700541404080086080c007254007001002041d6501800800740000440c1121003620840c0c40f50401600814401100e8622601c8541007100b12000c01d81030101240c088043e0b064615002d440d030801100c110104002c1c049001510500790036003e050102101450070f40e01c11014001d89410076001d101c40302081c404101c0c0e0080c01d60001d000001d00040c0d05600101120030140224000d9a034140c6112440d071708085404450320401d0342c90b84c40075240c3c1c40000c0158205804041c080d0000003595040d680e011400c0461a002c2c0c82c002801035209188120340740312a0b100300c100c0030784002c40b90001c582d0200300f1b42880c0000c0648100412260041000420002c0705210784002080d070307403541d07a91969420f02a034180c071010f80950030030000510f2607000740720f501c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 623886007 1250 623884757 623884799
    0x10309080a180b04090b1e030601030308130209090a03030506010206060d150e0706050415020a02130915020a0203090f030a0305161a041211010504031e0302091203040f 74
    0x600d07100c10030300251074440c1a1203038010004020180040d40400c144060401045140170204003c1120010405040b8801d101d407001282e104095444a0324000764943c152641070400c00c00c80c0d1114607a0501c2440402c000035801150402041440400881d68a120074843c0d10140650748425005903100d40381150215007204811b1072020201c0c600c0c45c00000c180c030026400207070480d500f140080c1000790b039810050204100040400280640e84142000c05140344042c0c04004050750000c1c0300901c5188000c020030b0b80b68600c5c002401840c0c98549007581119074115600c034002078001c0e40300c0d04801d6485100390f2031310313450480310b042c041080301c945a419a103051401031260040201e03294140030695699040507403011f03107051141556406a4003403405c4410403146a40002c18400d407051034044140d0400c401c0c0400207400c150050340d03030a0794103e00c1c02400c0940074110024051180300507482420280c407240f01150102c010703c2640c0050f542c0d04c0300c03180c803201c4040040f201da9080d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 623887257 1250 623886007 623886023
    0x4150501031a0922020a030b040b0c041412010f0905010b0112090506061516050a150b0d031413090506150a050901030f060e2401230306030304030b04110906010309 72
    0x1e1605507004844405101410440906101c0700c5d00440c22a0409410440c1d0602d140c0b820b10050004803529250300802c1c500c0101d01c4d09041c00b1040c9a8222000d02d207500400c554111096550400c0d00401034000c12060b00b001168080d08040c1d000e000c4034008a40803600002c4481522030860140c00070154001c0300038501d60b01c880090050400e140c5407000900d5400380514a03501c08181040800307503008e40c3c01020340300c4490034001c0104000300c401112030340c6010140e0728075854a00c4580c006941509000da0024543c0700c04e0201c40c401c0ca0010151111401c0c4041303400c24541c0d1140340140c100b66508140c2e442c1d4001d43c0c84403441511200b8011940600c4114525031007a003000403c05602403010815a643ea10f01e9624000f06944070404441c22680c2402c81c4103441d00b428103040002d00e0001300044407401c0d40b856444442800d80c41c0d2417800400200c45482c100101d80045512190a241c50f203090306006a1028040c05000d2090010202040c590342c440e004881c603c540207500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 623888507 1250 623887257 623887261
    0x30406140a03020c07090504230618010239150c03102418180f020c0d02280308060402090a081c080609090a030f020c04150501031a09 59
    0x10801604072090900070141c0030000b07242462001d00210000740b682d1040868542001d181c2030743e00403108070b000d10030910002401011503030001405a008141d100410381c481d464948010f01a109064654405282d00a0814882003420724106696503012001030702c0c5407004003440d501d44295040c0101910384150100b03c91240260046030030004000b81d00303c0e070940e94036940401c030481c0304400001c0b190400e001440309800c03c030341303084c61026440c51a00003410311004000c1e6407100d0807040003c075556100c10025504580c125182da160b00c0041324103102c0c0d00c540082da12030600d078036211441c0300c2d030f10300212004030a0007010300c10750300d82c0340c1d1300c441e968a10a0000a4101c2083c007940460703091030000d500c0100b44408407070f4004080d0b5040a182c51040090180d0704042d04840c000c500800400c1140003004c00c1e1104c4043c0d04d403802d0780180d82002001c900d44500e683c1065441864000602c00071002c0045507001c44200f0b0f03c06200d0217410043c4841e01c111a01c0d0819007085203400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 623889757 1250 623888507 623888537
    0xf0921020c03010504390308220506030a090303290a08010b0604180b090c0322052503080d0507030c02061005093d08030705030703081803120f0702030406 68
    0x44019400c1a95141500c0b550017450340c01c0120b480c070364802e030707028000010444027082c60540c04512650440591120321450315010a00c0d622000f4a501d0070310390307100b0368681007610035041840c0441744c81801104145100f450320b90352600b50380486100d42d005d43c40008180406000701c4405c000c0040000e8181071800c98204c4400304295000780425075500700303104a680d10420018010803001c0242a241e1801403041242d20764112891000646403104a40004034000b8400080b42c9400084020802c5694150450302070303141c100501387c0201040c1100302e50324035807109103e400c0595060010b2409500306030388641c0b09891081024804c1602400300f81800c08015406c0305451141c05003204030b4944907041e030040142880d40d043c9054481120f640c00c0c00460b0380140004001442c54010313181d5841d0341d24401d0501c006d041c07180a40000f002d8074110000030302501400c100b602e039642013404001c80c001108036444180d0610200207e05030340d01c00030a030b40541e02c80385c841d0fa08100c0c280e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 623891007 1250 623889757 623889803
    0xf1812061b0d0e010507080703060803070510091403180a0e06090601081942090510090f200a05250c2718060f0921020c03010504 57
    0x1040740c0c900e00e521110b81d80300c107560921505d407103007003d661500814203058500509441c000e40c8900d0140d881480990302203000443e9140504503c503400140b0f800c0d041c501001081e68101c50b040d600d002c042214840b940b0030b50448102c00408581401070182c07941c1c1803000d0071000340e540f107401030801d000050340f55001e4640703960092410080c201081d40c0541e811000d40d803c0b2110440403c101d038000006920f201c480c0d0b02400c1c100c4903180044444903969040b0440034511900c00300d291070fa40450040ca51210444001d04003034841406110998100c880c0030b080004101e905074004900440f000c1c1a820043e0345034946103a8a0a1418000c4946c82c001c40003c0c0800c2a9084100150400050040034009006110082484001401a540e00d0007200c80c03105941144a04041241c2101d00c00240610074043d400742e400109a03080340c2054008040c1e00100030b2403042c82003014000d0241071296801180040c0d13086902d050040300074540ac1e201e003550014101e000000d1040321400940c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 623892257 1250 623891007 623891017
    0x103150e0d200a0501050907090e071518030501050f040506060d0803070f2a0308010f14040c030b0a03050705040b0319060c0c0b0106030c031d0607030b060f1812061b 73
    0x40c0b802c48141079415198542150015241e480175640148410000c0715000d005501e451300350301740900b03207142c40c00c0d02c19401000543c005c00200110365200400c810005241d0001541d0402c00800c00e9141040c03500790441020354050320a8810b80b00001d03002d203001c143c1880d41300d520070106410341d02d80400665180c82001108401e100c0d403041e1584c0742c90f2922a004403442c081058401c0c1c0010f56007000340c0040e006070040403454032440c405004403000856805200c90094a0004403107a11441c00c400070700d840c2c40010b034011301d075010000600a000440300169142200c04210541c0003000b0141c1d503040082e110030701c501040c110307100030a40d140e03c2400541d5260802c40a07026880e0b90b80d805004098001a01281c1e6541c0e4820744c551703061003000070480200b805800550400c403c0141d03666401400c810416407074400d8001035840d40002e4880101121140035101c8440c0002100d0754004000480d001d12007100702e02c1d0103e140042e806004098022203002c800402807001d104503441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 623893507 1250 623892257 623892317
    0x1b14010b0f1e040f200310050312040303120f0e071e0e0f04030e1207081c0c150f180203010507030b15090d080409051905010b0f0c12030103150e0d 65
    0x160b183c074040460026600c1c07410810f240408207586e464420444c40640b0f0303e61700120b0007503100e814003140c0c140c004800c440a0343c1e003604100f115003070f600d0282800340c81c40c100c00d198100e040542004d5010740000c3c1171000d94a10b400b8000c0c4c0b40701c551900d0740342180a44610350798081202c010544080400b190306400500924000f1807040a0402182d01450396691078066079021600401041200784525a02000c05103811030315848031480c010000440804060a12519005d25070400382556000342a5108040418007140d101d01c030080308950800301b41607000b9420440012115842440740010780100244804000301c0078401e80016500320b81143d83d004000c000085000c2110f100180c03008041d100800b103090701d0154000320b40d1207a25504030302407900704001440014000003d680c42001000c242d25101d20300380705110714006112002d00029000080040b05005504072a54400208801c0902020510000007a07659541c1d003030003c000303080940c403014814841c12034140c102c12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 623894757 1250 623893507 623893511
    0xa020c070303031503020307030b04050106060903231f060620120d0b0913050f0a030e1e060a0509031c02030a0507080d2c03191b14010b0f1e040f 64
    0x900c91b80400d260803c20703082592000307080e000300000c0150034040d41024102d5072401c0d0b00c480b0300c0c6613992009c1e2080490b041800a00e0003504001c1500104507644941d480d15056071800c09100c0383c00c5005020350b019000000d842035820030f030490207003c9180b01000001e00141451850448810000d801c1f003065442040e0310788054103c15940c00d80050300505a00c0d8442000c06818642249000d0320f0384040b06550304085048008a900b03e1508903848034155001401048508141c0020100d025022984104041000003409600c100501000b28095003141c0350500080d140d508000f030b00407920700050b0300402034500c03000d1290020304a8607200b00b90150401d400c0c5944001a140d0321803500c1c41000181c2d1a90325031050b100f6040f19200c14000c0078600d0418103129100220700749090140521440d5501d900c0082e25032052881d11681085401619141480c03d0502030b10894411510136a400101e003030b201d140803400e40922902e8884100710f245400414040a0400362034072642c4c1c4d035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 623896007 1250 623894757 623894759
    0x110d080720030a08073207060207080703030b06030408030a021605010f0f05060111060a0c020c090703050f0f011d04050304081902040f06060f0e270402090a020c0703030315 76
    0x1011824250009070030040510784a92461030014a1002d0003408041040014040040040001c0090700107540030000b210b1075090140b02400c03928400c44000900c0c1070720020f001000c0c0003084c0c026101c410311a0741c09000900d2020200019804142c5000d05046001c1020031015410359000b01948100c940e0f20150340c1980c2d403030b00c0d4215039200e040e661100303443d01c1e0b820240018500c02d00b030b400349003401d00101c07100b040300d240e031f42d18600100500c4480d55105180c44c1a50f00030008051200b1000f070203400c2c107143c42c040040140005036004220200c81c640428110721490007024141c450740003140900040000711a0341d81c0030007400682e2180420040070561a03010301c0444146e0f10b403140c007502c0080091050004551b801b510f08540035107030072000d0040d641c0c005141001c910703070361901c0311070b11204d44001070721000d4107562004070160461076003442b66289641e0611a50084881c110715585201c1c20600b40c3c440c1d507450b49400e800200e400e01c0080d00a61180070301c0a40c1120034401c7d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 623897257 1250 623896007 623896037
    0x70c0f0b0a0516030618050603190c1403010c08070e130e0718020f271e120705030601060507061506050309190317040f0605010e090d110d0807 63
    0x48429145060510748030001c12000700e044200500e80e5508500c4c040081500e024408400c02a1200c4c5071418552a00003084080d601081002407024001c19901d0041c1c5107407600c442c05802508c51940d08080b0020440564601885080148001611784004a907580e1500b01c5054030079008482e0f000100000f1464080368900c1100840918a001444900e0030141d0b1503007050040702017102e207030b4010402c40c03181000200079034484908040d095007074034035a66507951901503003841050f04440031041c03802100860655080d100441910a400c80091b00711105d41c9403d41d07402450380603800f1400401c00e0300d10400003000d07502e028000010f4070700c1c0038242c212511a05644050005030020041c403040000500c0a41d1350807050080c8851001144d980180412211101d8012081d104070b0000e4180a10440e40880c4240c1c0000708008a68490401c070200c04410307910800107100d803a184610450007991036428180e0b03000001d028034552441d00316a59180100410304005900c0c00711010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 623898507 1250 623897257 623897273
    0x11409031504060f0608030708120705071223031611030c010f090203070608010312050304150c121b05030109240602060601120c1b031b0c030b09010e06070c0f 70
    0x10b14031521001c03441d240a40080c009841c0c040d009110503810030050000000c010104940b01c41c812868810607e0342e402c40180c42601034054041d003403a041c00707c40780c2402d034010203140c2104082c00007000d0001c08034600b48080c0c0070441e0480c521829045a003401380b07009001c14100f41c80c0010440b494001c033030340710074251000c106a13211007649640183e41145000e00503c40600311601c0c12400a45c503649504083e480b18070741c032109001e00000418203000b0f10103c400c281510928080c000c0e81c0b582c25000702070300c0c012208a40c80515002b0841c0340c6a2560251448016142e81c0d20345c00c50f4244003071b0030000e0103000c240c40d00c2d00d414280540360341d5480c0d400090091109401500b00707448c0c0440050140100030400c20b07107071864075a81000040e08844003071480301718103032690f41c140d00c0340c43c00b52082c6203400041c0c800400d45440c82c07000c02214170100000e80b031048219418680b40c1d01c544500380c84503146064000c2d044000000c410a1040070702c9d03c9514010141c6800c0034082e504c42a003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623899757 1250 623898507 623898511
    0xa0224070f06061703030f07022a0f040204121704030b01030f031202090a14010c060609020a090905040804030f0602090d140f0a02240c07120c06020c0114090315 71
    0x1e064440241894103201041c840c20001380441103070215941070700c00b025070b100e110040003407021912080109641501c2040104210141e00080c070201724154066801c07400185011240304075080c0405042c10305050094400307c5400303c0d101c1c00c52520558950315100402c4003844614034003030000101061a1003005030003140511241040c02d0306034100200107019412510010500400c001011a102c6000c03100841c0c0c241044202420309074070048960316031040c809000c590800c000440d070b00d412a4000e02c4092955250035100d25071710b040c41020b507102158042d2504009000410129000d102c446902c607205000c014980940d00d0000b40d2482e803501800d0b07880120085031894584410452100c8141310000140f11019481c0c0c00990041c1080f00102600c03e50384050005100104d000e07100c2300c99104094454143d00c41c25261041400a20141c400d02885000010f2039070022800015054069459101c100040f0300000c503540c0c070150981e41c1500c6641001e450207908140071038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623901007 1250 623899757 623899763
    0x20d03030b1801080307020d0615090b190308090103021e03010f0e06040e121617130e01060e150708030403350f1302100807080a020301080a022407 65
    0x140c400d08007018451a04600030804282030b0a140062101340400429640714690468943c82d55880519006024080b0301c2054a540c0090200c04580100560004146981e0a585c44e841c02074461140c9513651100384409840c00380e0401000d9115482600101500d1003001c00e03851500503d042511000d500036808490a00e442d0503080c401c510356207000c1c60304000100c80c180000000c0724101e0b5102d148101c8184440800000d1000d40c400400c181040d119400080044d000b41d880810760a083d400511b05585403c41c3c00303c04140c000e4924a214181c0710f50b80d032000c3e5802c1800c4288204008101e220341c030807035401c0c400d4400040902c002503101e035202e50b849030040c03008001c102c02c8000c800000031440b4409081d03025203494504420075403104002140051986510303600d41e000d01c80c40b06001c3d4100c6102404001442e400104890050b20165919185036554121004c00c0340800c2c0504c00e0340d50080030300720380985818820041d6000c040c0c21a000e020302d02100100c200d61040341d0071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623902257 1250 623901007 623901011
    0x1021f270303150504060e0f040c05061815130b0f040e010612060503010c0e0d060e190c14010c020111150a0b09060319080307020307080d090501050603120f09030a020d0303 76
    0xd001403043c0e0310040041c00291401e00405080000707044d4211402403460b4042902d40340050107000420481e6030040001400c1d6590395101070320900189000405c000b0b010711200030754a00c51540c0d1074116501045c00708600d4018074180070701118580d0103146e4a1808400074000820304125410074103000f0209500c0742500040355418841c10349410760b00030345c800c1c5d04d040101030145410518400c680a411180c4030840021440c01b4401480c01c442958510320030010311000c0d210341d2005076441e141c02400310124495a0304241d011001d01001020300149400c04150019401f50b0240f008000741282a200d0b00300760b46c40c41c086084000c5410140782c640711410100c0c1420159040c1c0d801c500150060610761b034004144140c140720380e02e802865144000300240b5154400d0081e01d0100b5031040740039564a101c2182940608500716096450354642004642ca6140008100c0b00d48421203481030300300030041c01c610140780c000900847c0c05020f00305800e00180e44105030540141d00c65140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623903507 1250 623902257 623902271
    0x31525200106030c12030c0c0605040f0b030103031b0302030d050c0a23090139120305040201020c06090d0b0f040b0702070b070b0a0b060309150601021f270303 70
    0x11014040000ca4042038030307494440705102260000c4008000c0d83c01c0054107219241ca9450125102c0c3c2d00001d01410b0b810403a0f90116010b940100244111390170225074101c1c0719181c98600d4000e2001f8400100800c00200f0300c19003e5070004c4110001a001c4d0050305d007000204100d41c8183c0740708a5042e8410309000400c07003209500044801803080400952011403040041d1a542d1440b031800c030031b030510084050519444007041001101c0e207424164521070320790f10348280d1034810682c130030803103d00d146000d202c03ca4901c00d00c141482342c1d030160300074050070414205200c95948102541604010300ba5166400708040d40e02d241d01542c8010148401c45c0b40a082040100401a0103401150482c190401088030404240c07000d581c3c02085800003130b242c2964000041000c0c1d084c2d00d803c808048104881d840740030510000c0c001480c29107002c15960741c8012a22080342d40e080d8070221507003511030190309030103a1044940800109050404e991915010a40381d480b001c4101c00094413104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623904757 1250 623903507 623903537
    0x109030905091008071e170703021807020a14190515090a170c1c030b030d09061b0510050c0d1802090a0203070306031b0501031802031525 61
    0x80040d4403d00d82000005a68101000e6689800c69031145a818440b07030040d01a9810001d135020703009040a841c441002182e081c9000e49440355440160303c5000c880c644580140b003010100792180a032036000d425503104907550072a4040c455031035425148070300c9002c4800c45503010000c410350b901807401091060744070b00d4010b0351148010f181000542040c4039540018405000d00c0300840341c100c401c59150125800a03501e08020290a1a400d50203070445140c8540c051380089015182170701a611032070b121000a4034041754601c20000019034141194401c41100c20401903074a214a007506c40d000a865107020545409680c1000350400000e42402e60403024400d002440d03503289418049000b4035000204084c000a00640401b900000020301c024440d60220f405560b00407144210040c0c599002d00214404d4042c85000c40d140c0240b403400041200420b130080c59004004001c90081840395852102d0041c003031001101600d082c4050400801003260854051562202903000000d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623906007 1250 623904757 623904769
    0x1c0c0c05041505130b0307030305070b07030b011e0c050d17090a0201020c0d0f02130204080d020c060d150b040b0304061b0e0114160812090706080411040e0109030905 73
    0xa809980300e240341c80080100840368042c110101c410031140e00c22081c440c11000f0015104071056103905014024005c0101600440030300b0000340210101d210941e102502503081f03403016007103207000c02c3c42600e604440004400111041280b5442c01c280b118003640e4540d1b103054000125040801d078905905072040709140031540e4007002c0e40f001440c00b4003141c1c0002c0d4480441e00c1e0528043d0700c80c45102014060303030701c4a4122035a4054402c0850b07030f0303128801800a410600682400b400cc0301d40754681c140c4001078a040110b8000c1095180607054070250006118514040e2681d0140c8080080c80d050318501401c0103100d143d02090741d130b10b02440e0600c100e0b40c0100c0944140c499021131980e0180d404045480c802d0000c0c2042c1820401c000c480b00081d0190340b080c0300c0d04a40e0740800d0400c012010340548800c1107030320385031802c07070710759100664844405001d0400000c0e096000070300841d904803295601c118000d000050707440d101c2090282991107920701074001c900003480821943c1440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623907257 1250 623906007 623906009
    0x20c031305011b030c0f1406070804020a15081f080a050a060615080609100b071a1b07120905060c0309010e01111009080d181109070906030e1c0c0c 65
    0x3d82c8403a90204103a8020b804c82483c284080c00c480034500c1240d0401101c102d9103d124004e8030210754892401c0240103050f80c104035002c0380200608000000c40840c08c07002d82200c1401c40d04e456400750f4503001d82c10300030b42c1c40e0200340c904090002e0b0002140041404610314080c041c401500950143d0304000051303460941c8204928840b105858a50035032000050b5009101100c89030542d850342c40400d82500500c1c2c010000b6940e0000e81c09040200e00340074117003400c04400e80381029685200340442884901c0aa84404803001c005020004282980401c1c0d4100c40d4100240c40035100d030041403598104445c2000c0316480000c0d49052503812414210308142d00b440d040c08054034003242640ca42680d104120b10720b50715000003204000c3c19209981107e00003403007c00100c101c903d094115401d000d002542c1d07405810465568500300411810700c140c0c425160986900d10780013084005060746400001240180340c0c100301410081c0d444a02d1900c01666035800b280ea403030501e0009500c0d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623908507 1250 623907257 623907287
    0x30f1b080f0c04060c06021c0c031422020603041e030809010e07050604121502030c13090207082b0606110f070e130305040803040f2124020c03130501 66
    0x2050008201c2c250307000d20144c005c03650101c0c0250700c030a56012403040b2006008603007a407450400f000b40e00401c2e4107a002c00c040c00c0c1000d404a41c2c984641c43c1c2c0300c600780790304008503200b81103604400015003051002950010b03c00c103081310211482c02031300c00e2421840303d0200d0020700c0e280103000c1a81c10902400252080800103406800c1c40d003000110940b0540c4901840e000d01c08a07071009114041c440125081064241559a864980c0d21481130303902408840304005240e140c04a4500c00510035a4007490744501c140380707440d102d40b00c0c40d07404003441440400d00602103811764085412a0080d00000c00311a00c0381034014001083d098107203038094042040170f5102c5601040182e401d03840682c0c02c04002d0085081003041824200d845105517000b01402344000107001442c3c00151807040100c5100c11788a14402205001c40c420a909240016003000f9480045511246512050544143c45824010310b0310006007000c40c29a002551111030159904000b04200e5030803a402e081000f030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623909757 1250 623908507 623908531
    0x6010e030f01110a09080105100911121608010f0b031b1b0705010201060501050c0a06020c0f031204120e0303070624030b0612060403021f0609110d11090a0303030f1b080f 75
    0x81c01402600d85250503102b40e0b8800c645480d00448910300b41c1741107890580c49000c1e000e4213441c146043c0208a042c0d45844400907181200020310401c20a07510010780d0740612909245072a1010101009030210807284030003c0308115602d00790460b881442036900c0c40b4000341102d1480c000000e0300f1a050380d8011030600004019140440e0300101d251215aa4401001030311100b1500001d89020078a0004035003510000801c04407080e03500f40058442e61044035005418000ea2500311080d50a101541d0740540c800d211003000a11250007420b00420000c0c140081c000e981030360003403103642c590b20030364003840d100b01449001d082503005400440a0000144424101590f0080d0b6400446424400700c1a90800c0100d10035084c0d007041303000381010401806008550705a000307890340184c120400861030268032517141031040040d2180c0c100028a822100e40c40c5440035030140c21303440c80d60042180d581b40c0056140c1e40150320940d141c200ca6948003034030300d0f2152000c008004083e02c03c5c0741e010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623911007 1250 623909757 623909761
    0x50405010602030904020c01180c0906080118021c06050a0b0414040206160c030501050a0203250504060c0f0524070512040305070302100e010c140405030606010e030f01110a09080105 80
    0x1d07030004221007241006032030043e95403200c000b44900420000354540c600380480b05a110130b0016038910f0b14243c440f1700f070080019541c0c070407001d4229088400b1004000c000358040c0005894100407404080c1c0d1000100420780100c1d80d2041e044400450780707214a25524000145a4202072144500c3c606800411700007604094002812030b0065801d084601c41e5414001c0b0100b0a80d218007038000e650006c0240300a040416203c000b07500101d849124010550400c03c0c410389074004120b0207040c20b03850b40e600d4603042c1001103d003012170003001c2d11403828010810b00010400c00402441c41411000e100603040748030341a020204001d050801000070030b00100341883c1c1c01d818501e402591505190ba40c401e114070301607092060401d0f82d1460186000400c2d45c5403041900949007014140c0e8407503009040c0d031003403050203015078024a601a0310101c006241540200c00c0040001801000ca40e00c1ca28401055420344050003080c0800c4076000c9104080f96800c440c460020380341e054001e001038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623912257 1250 623911007 623911019
    0xd090503251e030c050a060c1103030708040809030c0303070809010e1e01050a0c0605070c050606010302130e06150a210603020f0114041d180606060d0b150a0e0a05040501 75
    0x807082e240501a41d800c107692000400d4055000004000ea02c2015210060900d08143e80284029018000401c4d9941013040d10444040100c92084419484084864440351036580711900525600ca40522070065090b103a580c04202901d4094481c011180d0386180704400104071450004007240110202c0d91080d68540c1038040141840e00d080c64415100c0c140c0302000c98000d1032026029217814036080c18800c42c103510150a0180c00c0c000c1007116500d40303566004408a204240f50301462080048e018130402a0402d801500181e0080038150030340012002d560596020206890100d50050054048061924541d0080154400b0700704242c1d85150080381c1081010500341c4d0401040011103201d180c18101a80c02411486135181d0413017881d540b52078418503056410444400b000511701c0c0d0b00d080c0c001445880307000301a10003400c20315502c100a01822054407100c1e848420f1095203026a2404400303080d42d10000c1d60380400b000f80200034400541c06540000d0f0040781408010b01c58 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623913507 1250 623912257 623912273
    0x12122106060d020703020304051507060b0306060a03020d05031b0d230702010302031e09030c120a091809080313021309050d050c0c0d03200708070e04080d09050325 72
    0x1541e048030300540d03904c0951030103c0c1148103d800c6254840b40044064001c40c01c0303600900340544c8111020801c0c0380c25542015540d510807201143d00404001003032005080c840405881c0030302c61004c907420502a10b5030900b207111142407218055011b000343c407000e541d01040000a0707400c00104000c8075242242121210310941d01c0c080d041c160004003080c1803a1b0250340352041c20101124143500c1d8181510402d45990150540150501c42d0a5195444002031030441c4c184104ca6242d20101c0c5141c44070404030700f0380c60008454a2036032543c0d04400302d031509000714400c0b20f2502140f8000401c42c07042015901c0b0020500700c409140440410000f00001340a24130010b041c244242c0740d410b0400c0b101e25001d54010480c1d048601540402c1c201504880400c40006d081156098101040c04d081565191b2909c1504215807201e44100000074244a9254019001341078141c81c24907000f55080980310103100403a03080d0b000082d0556401048101c00a450080140504440c103c03500d400700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623914757 1250 623913507 623913517
    0x402100e06040b1c0e0f0d050306090601200f060f011d070e0a080f062215110403061404030f030b2101020c19020a0b03010b12061212210606 62
    0x43c07451000115a105541440001c1d011402490018131011900c849003589a8803084100e006510038014a90225800742043d41d200c1e010150245045036296001150758282c1c0d1900b6070b0310620390b0429084a01d00c140030b016814054840180f509080100321114a20416440210600c1400540c072051403070700c00c0310303a8110320f040ca4408603030409074000480c2e00e80340e075014010500c00d28100580c242d0000c80c20b14801d001c0c1650512056180306140d42c92041c2d680002004001290040c0f480c101450384446061045a4101c0d82003548a03a41c0c40c0454220620040c00264180b0810013016070204000c2c0b034040709843c06024241c4841e01180c42d0720b01d04072104909983c0d502c00ca01c5110401d6054560542805040350303640020590300f4141d540b25541c00381d004103c000c0002c00c0290390401140c0c12604450f4006207807034000c0c0e81c4a1000d400203000d503036120107804c070110002c0340e00700642c031310450381142c0d29907450203210700402400c4420300029111090f07120801031280c0da0001916 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623916007 1250 623914757 623914769
    0x170601021507091706010806010b0405030a0305031f030b19060614090301020d0204170d0503010e06010806030703060c03020a17040203030708031005040912110a081b0102041502060402100e0604 85
    0x107a03480d240c8082d20300318200e400c4030740207114801303c2031320b038140002d6500c0c103e554071002d4600701d90f2511071110483c0b086021301d40c1c241d03120310213190020b03203c0d1005551000c08510b10000c041d40540e49510408010b50094448006280c10300242c03402c441d03031001084644170000c001c421f150513400b900c3c1c1601040000c1d800b15000c500c8a680d80c50039012500f031401c00301021542e031620341c0080e002d5400003011000c0c0c1c0380310780d0315861500ca002d0f9013100c1c145c40d81c47c0d40c1c0f000d495450600464130031800400d49905401011400030014000d4050040e000c0e0040c1c50160b03c0781c41440d03004041404025807103c030054410117000c0075031230100450300c0d40f07a00a5112a07890340e43c1010200321007410f80c42560402e203494400d006020040491202c10a50341d910807200d900c90000c900c0e0303103202403100540000d2041100e161108000c881c04014507030340340c0016040c50342d1005800c806080f103030015800743c2c1048c1c007080118500720120003503d91050030300c1040f4100d4140441c070320b40142d0240b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623917257 1250 623916007 623916043
    0x30f0b0907112401060f0306081f02070c0e01140303040e07080403090e0403201606050a12060906090b10050a0c02040b06030a1506050901021f090b0109060617060102 73
    0x14041440c4107018600c5400f00900c1c44070810500401c2c95110b00c4000d22032000061a21301101d1a0b042c8207000307001c11101f4050003094071100e111544120308100490000d01e003a405c000b44c1c400034041c111030000410080c41c0346401903241c0300e0300c200542d40e0140c5241c4a50400c20084c440d440c0185012500b2201c1460803292a595525080d0303200b0b51250451104c0d5001e1208103c10158400f000c80750b944c20030b81d40100f01da00340e9801c282d0b4420b40c2400540c03003c440c004003840464460360103849800040c0c50720149880000c260340c0d003110300da0f400c44601561a40c80038481c80c4134a020308000709000b0390b0788030550100200014010701400c9104000c020350030041c141596141d4004880c2c2c940020f08840d60390400c16032030382c003d0015100c0400d140c040c0c000c000503a94014030540b101c8840680282c0072101220454001d0940f107900c00109280d65106c90b2130103d2402040c542c081c000744100060a5804c100020700104802c20380b121401c0c8043c0204200b0340d0b4081088104000e8170b60320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623918507 1250 623917257 623917277
    0x306040608070f0302010e04090201080711011d030c1b010c1401020d0204090203060330031906080f01050a05040312050601030e01020c03090a05030a0201172212030f0b0907 76
    0x2401604040e4014180d0348680c140100710a0310020140b001c80e4801d80700d800c030040d2820140000d41e0b07910b400c080c1c080f03045200040c040030302034240060710352805000020002e61018811303080ca8000004001c103544085108002e00320100040502e021044042995420300b01000911028420b0350040c90b0642e543c0700c14984807002d4054035410174991105540740c94071001d840e402500100c5030716201e480703010b9922450f0b0700311031905515034540081691903540351070f22030066903202500101041009000500e60100c0d2071148902900d04400a454019403140301103080d030304083c11103101f81c1e05e04428000020f41100d03031188803801100f002f1889645110050380140755031101c0014650000508412148011005001401048404a00258541083c1903640f03850303d600078042003d00000d412001118058a640308080034403c1e15984100c115005040d01000d4007160a040700324150160942c25000e182c14200400c94200000041c44001903c0180050548828490340ca00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623919757 1250 623918507 623918509
    0x62c01050f071707021c020a090b01020f0a03110d08061e010512150a0801090210080405070f0b0307090506030403090614090a0b0327060127050a0e07120506010b0306 73
    0x1034881994002c030f480c0003031500300c48a418095010000480c89006ea40d03900c66030600400c48000c1005401030301501d038107820b0420300c000801c100003101d41944201810070a1600d800c10111000521980d550380010400c0c001c01031030001ca05d1401c10034030060600300711071922851490300318200010540550142d035040140c034644603007692031a44400f00c0082105a02800081805441080d80c266004136074600806e801ca49603240001e501c1f000d07908210307020b64410404150450701510540b104180d641081100c06e03122039000e124525808020007116582040048000f00000d41310140b4605e07056900800d0f13903682d03010701d40c240945c0c1c2e1002d0f0b4603480000280c8050303140c0a40305a03011074070344035120a10f4100703c41c0c001800c003e00303030340000158103c064207807503001c40801006240d081c03c540390b01a49000d920700f8490400c403a101070783c100e0280103c0d809417060403c0007664180a168490814105800660100e401910381100182c400540541151034070b0040d01d80365104d0b60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623920863 1106 623919757 623919787
    0x3080307110c061e031803040305240103030e041109040606120c03151208160f110102030405030a0303021c1518060e010b0304021810062c0105 63
    0x1009000e41348070b402e40a1070700040c1c4502c04c42c0558842100e0701c0d140d138001d03500c1590141e105d42211804a0410484034001080c640321082c80e540c11620050040401c0310800d80c02036a4410b6070b20501211038081d900380c0340d0010018007503a03507215401000351004168403188540703441c0ca8001d00600034818159031040c031490f01291301d46008031413911100442000d550100b0f0400200300c8000e109585180030341e20810081424800078148800051131011400d415548204000c0c060361780d0010300768820692600c0c015030b030b070078590b111603502420316100300c103805051000b40e100a00e9150160010b4410400c251080005c1031074094040d1691440780c0c501301da201314018030800100600075544640090f110703014022840c031070042e501d40b04071000c00b40100c0500042c80781c3ca6100c3d01030030228011543c00116080c00001048440ca02024002d0600c400000d1055414801c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 623741007 623920863 := by
  have h0 := BRFrame.cov_init 623741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623741007 ≤ n) (h2 : n < 623920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
