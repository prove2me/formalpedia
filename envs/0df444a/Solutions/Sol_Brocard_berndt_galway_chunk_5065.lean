-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:50.524081+00:00
-- url     : https://prove2.me/submissions/47ee7319-05c4-45f2-86b3-db5adedec467

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910791366 ≤ n < 910971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910792616 1250 910791366 910791397
    0x703050306040b06040512010b0a141c06060e010b030618090703081b0706050c190c122f01030e0c011707030e190b07090b0301090207020109031506031205 68
    0x507450781480d500c0080302c5000206503d007032564074400500c600d050700c103511010341d440d541039080d1420031004040c080c06130141d108144108800210b408030980e0b544001002003144050380c1404050362000c1d02401012010151942c0c4500540986d80d2042d92418061440440c00aa155010203401d03030117281210084c050b680d20359103406a09030071211107131613011512544143d1440c01084034000404e9103494168892143c0c056072820114404c03000c403908000c1a58040020380c464803c0000d503070301c40300220034158170743c2468244181e0161055000b401601c0081000c40e0b00d005040d085204240c0e0180060b8403080da00d16228440c148425000ca42c20a1140d4403040000303022541c8000c60340350020340d241d91010403600e44401c90b103c2c904480ac41707000c800c0900036180c480a612400a040c80c0340510714016490b041840148100240e65502284803000c6a100d25000f400541c0c00203112a00c039082c02d80114020201803004603486404542090001c600031020360b14030800c61042c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910793866 1250 910792616 910792621
    0xa020d0903110f041409070305070f0b0a0311090307030302100b0604080618030c06271b1504180501150207060f050a1b141015030807032303061507030503 68
    0x28000b8a02400501c03c0e80310f80c0b1182401701010764880c0d101e10504e00c2000902d0258550b040c400d080003580e03000000002211001072103405048411140b8030039607031078002000b01c02b03181e02456a0089043d195854020074100100341070b40002d00b510001c5824404001c11400c9030b0802c0380500c91031041401c2604001c0003e000000c14803003602d811070300ca506491808101300c510342d042a4044034110020b001444112110b1103450300c416030720394460300003840f00c09841800404809107900e1403038424940c40f01d03c0c4480c8525041030b100109240c9120a01c90b10120003e0405070074240200c0d511301c0404100c840c0760074800189807084480304e446007c0c0340348000100b244c00780c1c001503008080c408039845c014a20b003000000003545c18051420b40076204140d80c0700c14141222000140701d868142001000b03031002e41c6281030210303030340580303d03954074030751498140d600e412101c810110004058202198544910380214400e060440f0f0311117912a05240c00090390080c14005800680705100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910795116 1250 910793866 910793869
    0x161101090f02130e070b040e06040b010e12010e0d03020405040c02060c04060804110a15083615010807032904080904200702120f0d050d0b0607080a020d090311 70
    0x40d54189403210402044c0f8083c035046551030702280f035119010b9a100058100112411a441c880d086041144e09000d40c00c10030380001e040341062000103119031100d10f900c0c1c0110409600440c40d071290300c000e5a0000c41400400740003504031b8881c0c540203a0400c50010740c800d1011401510945070041c05c02d09103405c1080031120090001c000300c80c10611694000c100b69200c100754401001c00007400355103c204408018501741c006030615020001051041c03246648420031001d0710880c2d40b00002c00c80f110315104c1880c0490194050403020007100001c1000400490028156401804405440d040e0004c0d544040c0301070b8520710004452480124000450103c0140b0712114010404030b0111180014490b000410200c81c61484400084003000c40c148404105580d03001040a856003004038480f40f80c462035403102420801800181ca51200c160651241c61201c0d800340205071191560318102805074000016540907128904d80c09201c80d200b0340380c803026207620140101448203201c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910796366 1250 910795116 910795129
    0x10090b0c0c030d0501090501050f0a08030406050f0409110c1605030705011d0405010e060321070b040f1e060f09020109090f02071e11031c140c06161101090f02 70
    0x603003145075000800001d6034010840c09150b01921401c1d10020319540b5000402140d2200741c26114002c815900c810001110003000303070380403502c0e03600741180c0d1103460400002c001e21541d080f61044510703168400707058041c00d0026004402c60311080304c9201e076103d882e60104051034800c42d541680105002d02c0355522170f21440035250303402a62040b181e0a0480010180c800076003146120320411820480c0d1450100416102c048031050040e6030b094503103107090264822004c0c0078040004650120b810001000c6030198151b4110040c18072541400518146810519030705a07074a40c00c1134035400d01c0d00c2982c810402c15035416194000d44a16200c41c13003004d0207030010701da251254240310440200d240030809482002c02e400d51818048054500750010001194407607020f644022440c06200f80604003010604425044c0b0304405001c0480d00e480300e100303440c21b0b84424000d000901c1182c0550f1240d0003d0508e0760748508461250b280d40d101c1c04c81700d100c0070180002c24881c0446000d8180f01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910797616 1250 910796366 910796377
    0x6030708070323010e010902040b0d0b270307060509150105010f030903020705131d01060b030a150909030806180c07030e151b01060f030f08090d060f0e10090b0c 71
    0x7111100f951070440040c0c1421141d61880814269442d00203180840c6003900c600c805c500c208035841011140180c94141c402280141000d40c0d42d582070300c84001c80b0f0180d4800080242d0079404a0755641c001e0b2a0480c060b080c1510402050f20900541d020210401c01410b410b880040e91281070345c3c041c400f0101e010b01018241a000e6006130030002c1090380355410201f400c40840c0d04040789080070340c408031480918403840346006902d009024020081d2510449401040716103000c141060f01d800350342c0c0ca40703202e90320101c645854500d134501055009450b1501c980e070103c90440740c2d0048584c4100102e10111810300c004c500c10010f44e000a4050400c00440c1000500140a002c40c1001c8085032680701c0c14031807103c0b14082c10203195444007409904003030301280c1c504022031490755450184c41d5011400003001c1c3c5502241c114155242c4004041c281600440c090040b203000440820041c40f9421000b00d1601440000b94400c0d02c8501418031999400341140005546400c5200001e0700700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910798866 1250 910797616 910797653
    0xc031e0702010c0201030518010e0c0a0f0501081b09030706170907050f120109050a031824030209060d1a0a1d0a0e160e0a050109230718030812060307080703 69
    0x8d8a41c12281901d0903ca8660488c3c2418010315603002408104116441580c1c420440c500082409105599120b0451a0002600121044030004005080e08071b401010425500352003500c800046803948443c1c10307500f1a04400c030840203600c60f008099213580e2b843c0115500200c00c84d01149241c01d101031412041c000741400012664450358909051016020055001131906965898004001c504c210700424a40c10400944421f242c40d40c2c11000760a070540080c1750703000c1010841910743c4c100311200d80a01500800c01d4452420081040d0884600d00c280900c1c140752000c524a100c582070280c251011000b401060ba55070f02081c00a00100303151181075002e02924841c03400780403207510020301300d5005140180c0c54070303c002d1402c030b880590191043c41e0601000d0500a80351030602000070341d125061180a070740e450310550fa1609500c0301e400d28225000400418041c0e0a009484020511421010141c0300d81e4209030352a11240130348005508654070400c0050480d00104610401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910800116 1250 910798866 910798891
    0x1a010f05030a2d0b0405030c061806061908010c0903060515090c030a0b03060405010c0f080f0f06030f0304090b091b0d1a0406030f03020d08150d0f080c031e0702010c02010305 77
    0x3884d41c6120a0f181d058400710f8950384041038a00003110207004240d80861500e07440d00f030490741c42030341b01c0c2e4880b000b400082c050a01d03c407099914030b9650303000744042c0980c00000e101c14200200e0080100300140b1041c0d5045140c00045402200d050031140705180004190841c3d6031034104000c00c0550010701000c0c1c1c3c495660107441d201c2d40301440356074441c5d03008000001d5800e0340154090310500505044008211100c4100100ea4418180d000d8028288a00484455481c2c0380440d190a01740180400d80b88070101d0b00040f540c00b941c005060000307059a10038610b845808045c211907900c8481d2074018201405112401c0d84a0303405858036040c022070140c4050b003800041421900f60380c0040d50598407000041c003e054040148251910300752401407020b24101e007030f5400c1c8042c0d08260394424444c0c04c03603507828090060709040d20150408401d0f0382e98443e007681c8039980e0f800302c0406041444070f0170401040320880350070345c0c88003a01a1941f12000241d640118010701006114503181d50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910801366 1250 910800116 910800203
    0xa11030705090c040305281533080c1c06180b04030e0f06030109110f0408070e07020d05043b07020f06041115071a010f05030a 56
    0x1030b9490740b40750041d80220f41e2141e42d00d04500b44242030026407240014146030b00074002c4159000f91450501d070a0304030f400b254020140b0380c0e41c100a081a24500280f000500b0340c0d2012880403580d224203401d03010407090340070700c3e0f90340c1038262100115040c840c1c1c0300c07180d081c2100555600d00d001248883c80340c4400203000840c240882c51b03031000d030101a1002036062041108058102c0740749521039a00700d818440c0880d82c0c40018509100500580d2010ba40710325111244890351030a440091110b407106607221a11246100d0b9989500e02ca401c1c2c1a04e840c1c00402c00440c004507802100d680d01350b0300c1c5880d043c207150703000c0d42d011610f040184000c4010b010943c001c1f0401800307a1010380203d451030b82c8504090500a2802d412001800f0070340d0413040c188030014902d00008010001c0595019000711459940324501d405070f030b040904030000314014000e6921a0342e00a034103a03074040923402c140507210b10505581300040c60b0000d195810714110380549164298407201901c4a1005406000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910802616 1250 910801366 910801369
    0xf121505010b040302090603150c0a09031707030806011704030516120c06050a140414010b1915081611030d060306020702040e06070c06050c1b0c10030209030a11030705 74
    0x1548264406201c03520042810320862800c0000e0580081c41140140b012464400fa00c9c40c4640e0050030904040c200000c007000c8060080040d5002140c0004602480004a003600710150703008200032000074810f14001080d540c01901c0c40c1e0100e10440008410560b590340c1d00b41d419900100010300311070085103107840040c0e8413a40b0b03121a08200ea9a2482101080c030740b03207050703403405041e03c1586401d010300c82c0180341c000d08055034441c0c1c1004140305205400e008140c010901481940e4001d4607002d54403241c0142001c1540c100c82e0030852032005000e2918080303800c7d14068030390342481103110a01c0b00f8038a01c120b1088005006510560303151071140c0440104580750b5910841d032094011800d00c0541c6050300c0713016076002d254009440d9a26240b200100700d5030001c000146010354031008242c1c941c41c070a0aa07801ca041614182030313604512001e06a41c1e0101c032440300d20805101d0b0800469034824002d50302c1c0d010014008081c00e81d1284c0e144180750404118940d010310800d80c0010700ea = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910803866 1250 910802616 910802621
    0xe0318190801020c010b030d14130f0b07050607170112020f06030a2f12070918020d050a060312050d0e06250221070f0f030f0f08010f1215 61
    0x7011000001641e90080c4034040742921481426640701ea044100481e00c0940c1200c0c8044603200e06000031640d0b41039447c0041581e0040d034100001c1503082c44c5000c2020904170008007000c0b802801162101d58920798111441c0140d07802ca10804052140104800c89032071140100e018402081d0310040e16044003c00c078160401c840c50700c076640d1a0410401554100c0118208034030012140b01019000310310008240d2003034012007a105a911300004440c50700c00e42d14000980708a1a84d504450010747c6104040c0d00070404514041c0e00d400c010a25040d944d200324006c0301c1c2d10800c10600c1c4000c40a003901c1c0c0d5000040103086a6480d407065281007041802190301c02c00584001c00e4403600c2603041019840b030040c2007503095510100303040c004413140c29994945c80ca8614503007a50303040d45280c4949041c6039070340000c029500d00440c0104058110b81100c00c960701c195101f010340d1102e6102143d0341c0100b0b20801c0030814101d5810b12203480d98241c081001801100801c28501440008504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910805116 1250 910803866 910803869
    0xe101d070302090d15060e10031b09020f07060605120705040b041814070501080106170402010e060a021509071a0702120d05130b0a0f0e03160905010302040f0e031819 73
    0x500500d92800402040000e100790b82c01f0f85100c00d034000d40380c40c003805020240340c0140005414a200c11400000b50b01010104001500c08110195110030140020310310707a81060b08101c80540c100034010400c0d082030190090040d0910004042042c03404041c03000900340744130140d4015446c5c28003c000c5040410311002c03441d03c07522024016074640780802d41000e07425000181048401c40c0104401603004440d648940c2e544a05612240c0750362006a4003040c60076aa150040c4012403007014082d00460342514045140001900ba45d43e44440252140900d0203449180d60200030202d1075811040d0240c0015840a030000c040c80723001d011443c5c8bc0002105407030b0001040041c07500450b4001c1e9003600c004026050220781080c0303003d080505403440d2001d070b00040040152940d5403598003005141c5800400980c0c000800741c5541c2c05002610b002d0100340c1c0107a0501c04024204140c6d071280481c41c0e4000d00c09035052021041e62407104920070000700c0e0b032001d044091440c1c6895030002400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910806366 1250 910805116 910805123
    0x337080309010c020609060a1104150806130c0c0305090a0b03090604060e03070b01170a1e05010e030301050d020112020720040f0504020a120314130e101d070302090d 73
    0x6499281ca4034007142958203807060401150050030900581500000d81650805441d00c0013007461314180f030f42008540140e9028032821221404020301c034039000080c15008003001d84550803410170704141079007501c10600604000407031303418041380402c3c401c0000d030400503001000a40310903902d621020481c0c0040c0c81044413078001d03c06210402c110742c40380007446d011040185040030020340b1007410100051003011400205511591000c10301800141c4010340d00c491421891485015941106101860300300e40a6103401c1000344000390020030b0340d0403503000404103d1a8641a401111403004140ea1203213034039002e000c0d0340001114100322410b0034001c88400d14042c0100f0007040183d4441021002003e45801c0501001da103c0d9005441540c40707081c1ca01d000c500791464110380000c3d01441201d606940412102040800c22200008a030304544900b0103e40b100300c111045101c0070320442c000d40b1100201c00311048403030701c5841d43c000c1c00c40c2030040c28401c0c140b01061907580d50480c201c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910807616 1250 910806366 910806383
    0x190b0912070303260606040302010e06211902132606090114060f010801140a051c120908030301030f02060405040c1205090c01021914100c0905010503060337 69
    0x5401402c9410100340c4c001900714501401c505045c80421000d1140c0e01001c0d041141200d441002510342ca41201c450041800301034584400911654502601c20346132030700300042c240329040341c0d28218000e81c2d030392900f0000d4007822180780c01113000440082446603801c184800d4803155030303002c0920809108801400c0042590301c038505842a5001c00101014400c0c0980360125615903407000b0744a0545040d40d40030200d0020681c0002c070422050707808550300070780005544c914250350038458901c8a204e18400948005171040076a01d00401b030141e00c03503983c0140010030200c3e5190458100e828005400300c0c1ca01600d500c040340640707203448070000104508048240c04441540b0440b80e2104420014100035180440000e4482c1100901d01d1400095441d240050241943c20b8481c809929005c50b042c403014a4208030103404110300c50f1f0003203a0390210000d807550017041101e214030001806403400c1d00c2d22110050040c0c00074846800314a070440000010410220480303903145000e00c444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910808866 1250 910807616 910807637
    0x2120f0f1b042c1606030606050a0c1704031104050703050906160302190806010e060306010e01030e070504060627031a1503030a03021201050a050f0618060a0302070b06190b0912070303 81
    0x24a05003c000e51100d0304062808074100310302359004085d11036411885c6010b00d281e25041c10300f016a24108050100c004000080000404c40706040c21030130f143c1c1c261018089551050000d800301c40342150341e681c00e60040030020f0901d0b001d40c2c2444000e01c00d0381c00c5c014101040c3d000c4425461103e0840e400c0412550001c4c410190303040b81d0072910307810701224640c0c594540040000c1240c4c40d580b8100e414152140c0c1390980499060000c1c801802c006070042100303d0f6a004018804e9541080307418038094040305a031a4104240900c0d01a01c3e00011513020341700c4e511504440c0c00c4002069038030400c5480b07289032116601440108030b90f00003941c02684444860356000b14035034061f88081c3c8038000040c41040385443c0c0003505c0070701000c00c8940b252241401c80d45002440c8840d0161031303004800080c011001a050350280c4000d50003040084803035134524050018541804042e06203001100c6030410581440400420750f001015191034800d0b49015400d03440c1200540040707006c1514031a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910810116 1250 910808866 910808893
    0x1a13050d1d0d030228020607050d090b180913060504110a080106081b120114150f01080411011106090304080f061303030c0c02120f0f1b042c 62
    0x800ca042007012100081d100c00340e540d0103980c980441c079580c0f082000e003d100362a180d5030807030009145900601410396543c0c131481c041b40c42d2a4505928800305005a0001c141c12040c00186c0ba220f502d40c0040c0280702c101e0b03108204031144002c10880c40304412550b190006030150040701c0c055807160541c0818140b209040028210485e00018240d07850320704208681440020703914406002512518140551040490890003d05544084560906a02c4c0e0604c0d18202e000a1090180b46042c00e00c0d851800e0810400e200032400c0e960000d01124003003070218411046c4060380c540d050400e11110040b07001202d00b0140100ca40301a290000b007810419400e060050140b01c14210020300000d240058a140c10045030020103400c150765011000501402082007990713080d0018022494018034100d0399a41d0f90a1076101c10041c011940440704090000442820209440090300109039a0780140700082a142c01c0196407400310040d107280840146038582040b14446000e070030b40322a10074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910811366 1250 910810116 910810157
    0x9060f0501030b07050a090b070f0c15020d0804030f120b0409030309050c0d020a1701110415020706261905040804090b011e050310081e010f02071a13050d 68
    0x1030103d82440002c20080f103001364000040419030f8002809149c541c4e10302d08001d01c40301e20100340207040d8940560003203000300d51900401c442c40102d500b00e9079400c0c6080000c84140070140c4009012411075007021070a01d000c0c0b0f0700340d40c01d4100d05030f001070501c6403800000d0507540e98400680200390b50798040700900c00e0510005c07510150940b401c9046402c0c3e035000c5a140032051054000312040740e205001081001c2d00600444483c00710074684451311210643d27248910103001e8800340c85940350002c0c0c0f00e80241001c0c01030b6001d0182c18458890000c162800b20080200700090f100e411842c0702405070f440b84201805a0b0041140c984c80c2c0e0b041c160020115074030580c50605100441504800d918007030512281c0195151a00940326112007003030001c0d810741508804110b000d6558450a00c02c8036805003036086010744024440708810821b09412072281807230291800442c96510f880d88508411860b40214080d4144a4111120f486490800404428680000384401040c001d402a00d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910812616 1250 910811366 910811371
    0x215190b03030702030627011a102d05040b070308091002030606030a021b06041b050603040807021207180b0a080c010c030305061c0501060e10120b0a09060f0501030b 73
    0x10340055140001940001340d0b101401020ba0500c025904c4c06a0489108507d0b0304200c044008024050100c03010851110004d44101d0380f03000d45180508603020f83e1040c49000081101e4000124914100c83c9040468046410040c0309000e8204030000c5c4d0a200700c0c008100581c000e95079488181080240c20741442508000d4010072401072007808595550034085030342181071000700580c1d94200d882c21742c4044d22010032140403400b80c501080284a10041c0c8000c964003024408003c003525802045504e01054501401c0400b0a118800050828840452800d12035000f00c41a0f40d035510019100701c0c1d94800080500c2c0d80b42d003007064140c00c0400340e50f009000a040034040c0308a002000a08010a10300041d00305902c40001c1480e9465050303000f014a03000c0e4a00c0710b407501607418080d018110b87d118003504410a1000160004d00103003400d0159400c0c4200306044140710780f10b01031100409171107071071340995920201001503001d1140c03403000034a110010541c0d43c5141002071025100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910813866 1250 910812616 910812619
    0x90a180b120d02071e0905040501050609160c0b0c040b070f120801140904140f03070b090d02150604110705010c18050a06110a0605130c1208030a0c0215190b 69
    0x201d242200070380d000719032102560004400c000d000c032003030345005c480042c4960000500a1506003400240081034205521586c402e8802281544030030004040103a401114440003408500c0b0a50010700c0c0900659002a41044518141500c52000c1d615560003450300302c411038100031700b0504010404824007000d10040c03c15201c0c540c94021b0005920011150705031280e82144001000c100c040b0781d14040110190080ba030b5514084840255641d004002c142d5030b000710800010300c0200e00248001c43c40c40c240d4007600b51201003002c2c465141c0400762055900548800d861103003850300502404880c3e005500204242c00481000380511107420a0300c203800c0521102813159844913164501251800e00d8050382d128419040303942449a001c0005100a080900740101d103040001c14a1420f805011410342d49503a42003011181119150014081402440050a540a29403150301c1007003460050b04c00004191002e0100d0351011105007500d4042c002801460000d98071503001031040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910815116 1250 910813866 910813873
    0x8090f010c0804140a0816150e0307030c11190e06011d011413090b010818150c1b01150801060308040909020622030614061005090a180b12 61
    0x20407200100340c481e0041c0083c0c0002004280205516810000780c3c0d46a9044001680c070781c1c185814802140281c00f03000d4581c56505215082c0541e8144100099401254020762420321135560940307014902a800b40c9100754804415400c1c0d464601c003814059a080200d200c515041c511200304201c0c0c00f400e1181080b2604441d44422000041c0800d10880c007402d0689200604a90008907446856450000303070880d600c1c0051100307012740102501c0602601e0b40001d9680d0500307040c88900480c40380054503404158401d0900c1904a6095080407807080418505003c4800c6241c83c84a25503c950b0280e54480c41d5141c140e010102c1d0030b01502000c0002d2040d40e1550b290440180110f0160030f540079600c41c1150308560760401200e44403040c1c204401c42070014900d1117603d03500c4911003615080c0c1084006650100c954181e28403a035402881520503d881c10f20845071504001c04a0f42c0011600030089400141a006444800501000810355111513002c1c080c03028001d541e4800281e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910816366 1250 910815116 910815131
    0x12130f151506020a030804170f0f04050a1a040b03071202030907050301060f0605030a111312020907050c0d03050c090415051f1b0206040b0c1e030408100203180d08090f01 75
    0x90380191400e07000364010b1581d16003000c48d0343c048201442442c0c01d85c2c424080020f810044588140040d0044510440e000d0100c05c0d994141104081542880c40c0c480402c10003090115901070380146400c020030386013510341e2455190000c800ca900540303030100d166100100c100801d2800b401500c0c05407640c10900300303205140141c041c0550101415080240703840781903298010dc4510103031070f0070501300301c0580c0c540740d500c0e801e410009601c034904ae4016408100082c88143c000c42c01c5038820a1010010700002d07007001000ca0080c28080d10321600d800c4104059201580c80b4020140700d02c09000c8010b0f00310307142038204007860100c040844240380603c034092026030340041e0355800c0310043d8501d00c007003d281440020f48910071500506618035010a048452420003d86045145082c100300b001400c840d18003942d40f030040d4802c1c0c41140e031012400214441e06900519004100d842d8940700a60040d16894144134406109000040104c010442c128601701300102d4440c084500800191 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910817616 1250 910816366 910816373
    0x1608160c061d070f0b091c0203030403031e031503030e040902060f0a02011406010813110301091211010e07061b02030f03360105070203100e0304050f0612130f151506020a 75
    0x40c01080d1b042e038400c44001e91404888030141c40070958499008082e80d0ba2161645409015040798000c2405800c22080c00107403860f0003440b4048904812800034015607107160340407107000041c0702d8042d40080c0c403201640d0042c0c4880c03029190f0903c10400d050b4650807400d000a00312004041f903020540c41040501c001070f600044401c1e00001c0100d480311704c550a03814022900d0704207898098140d8a803030402010300405c0e00c2070740501d41d00c0d982c6980c1001000c55801e4240c54180503481c001d900150000c001039801000400036085070f1002403080b030f20245c6c0003c5e0402c0c1c00e40410b00074941001801850004808400e09280200a03810008a0020f00d0020b150403070b40722000350501100103820001d6540802c401c001e00034a0700c13403d010180d4040e230303400d8036034101d845810701460800c0c0383d443c6640340c44010348600720b00501c640c40e2306644a03000c1f40c421400b03034881078841120150b110701c0403503030011541c6890420f100001c070303248402180740a140703031055102c80b0441d0050160840003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910818866 1250 910817616 910817639
    0x180e1b011704020f150c0313051e130b010e0d050d03110c07030305030705071b1505040b09131401060503010f1401021506040609180b1608160c061d070f 67
    0x440a41785002d0064201e0140c004e01c1c4a20004140f50b8070022072a1108201020078034001c3d5501924070859090303040c00000d11000301d910713149a21090041d0800300650340c5030b10030307000080705262144181061002203622205606400e540d1b40c0c120180c448c1c1000e030540102c00716692072024807450302c01142003480e155182800024204040007002c500b03100d00c01c900b650030b01074000c1c02e5501e0480d583c45010902d0380088c444c542170003400080301d1440314020b900380c42c12035035502c507250318010701441000404903204100584030755640021300030301040301820134040c4c500c6844003517483d4140041c01048841d140d000d21101c40404200715181e0740d0104003080344440102524030140c40d40000a0050240c9402c003002c41407619500c10b40280c90711841d140420b00440301024552034003001c00c05449031001c0c080000c030310030b08040f481411091022000401c0d00746040c6010121580d030700300994643c110070144130150280b20651669050004400411410b144203000c0703441c00d88248030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910820116 1250 910818866 910818889
    0x60607030e01091d0a0b03060c070f081207050c010e0c3f0304090e01020a0c0b0705120f161706040f02040807060818070609180e1b01170402 62
    0x8116081c60610000d034003440a810203810403c00c080045500c00c0c00e5034501d83c0c01180c0302103010b810b00d0081c101c5824003092450040030920321a92505117952282c2c3d00e021404002240da485007003203c0d003601e0a04518507402a07815680d6076650344826040740c0e00751644125001055080310f0406102da9840034a038050040109480c0641900b6000708030000c1050420b00d41d411003813035060324002d02e4002c0014001c0d5020318104000710750b81000282c0c201d00403030815a0100d004c040c9850040396140f222113610801600c0c10901d0a03002000f80380354050280c030043c9902103890140258400180c0580101c1d050038504007419401c4c182c031080c4440d0005e40440d0003180c5e145162200c41c0da640d0101c501410a01007103801845c4d880e00010103030207080301d45140920480601035034000011480804440b80c56980e010a2401c00d2408045000b1082c07086401503650b070442c01244800348410a412400c1001c214030018141001401c0580d542050084100580741040f006a46414030700741e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 910821366 1250 910820116 910820123
    0x6090607120b130906020c251217070321020c0c061c1103040b06090c030c2a07030201021b2b02150d0b0103020405010f0309020312070f0c0509060607 66
    0x41501800022a00f09643c40320386041e4141040310440c24000d054000b400034132004411103148101c00c0c9104030b1030740721116010f060320714209810446100f080b11022440b074003c8001c0c0d8458049031408800301e0f070003040120080707810a1004007000d00000e0201800b0780d8140b200358540203451061940780c00b00c504145124020202d104a510f105507813000b840c241e03100100704039940c41c003200f6111542007100c2c1100e096849000240641c200880c0c01070107495080000c60941e154200190a00d8102c404c4c085840c0c104c0c0b294000c080d43e111072030000c1048e200000381001c6410f50000908101c0501d0011003411901ca81c14425521000100c90b03c2000319101211810380c905050a41ca43c1480700181d440107812012441b0320744284014003e182d130041c0100114100c0b24015001d0340680c2c4143d0b404201c0c00c0c410791868500070b41011105510040c02e82d2a041881200550103070403c002c1544d400d81c1c20803000e010050b80ca10550080c0c20100c8080241d481c0071000551141714040005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 910822616 1250 910821366 910821371
    0xa080403050906041e050303072d08040b0715051501050309120406020d110607052215020114130b010501050706060b0304030e0301050a151707150201060501020609060712 75
    0x1000e2500c00c0c0c003501c0300000024070442d80c5a03a200c000c0c494070342d007510b000070038007140701800100351400104946c00250b101da81c284050a500c0c802e000801d120303454140860002c2101900014004001440030340040c03800c1a0301d450490900c00382d951140010b00b400a860103040c0101d111140300250001c50091a1180c2d0b00e6070749c1c00302103040044515920074061b8022501156040d008a00400e01c402d02d542c41d4070f2806e514484040e6200410703619100810410050110143c80c120001e001900000034102c50456440086600d400c0e1141000e90044c1d540781140c984807503030036004940021400c4280c01c903080c1e07161501c120b59401071203860306002001039212b08000081e00030000400e400c0c140307a6100c1c41c15080140c0080c0e0320010461103035180c0300010f03604607090700c900e51040c0c8c0984034007030859042c00d03811603e0507204c144102042c85803100005030503840b200d49084292603a4008100e0926180019140420240458840c1d0f0131410400c00c030b182c3c4c4881c2540b90b0300ba406202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 910823866 1250 910822616 910822621
    0xa08100803090f03100510211e02242101140108040302150f0403030c03021207030b0f04061d0c031603050a060b0c0f0606060906042c010306090c0501080c0a08 70
    0x82c94990f03a2056024101d00b03160070851f4450a03902c204080700d40b0a00031643c41c00803000240ca1500c1c500c000200301c42d1546062104405000a00e0f01c051403010b08440b812100051018451048104034003541e079400041d41c500d200c00c8012500d901c4010b82a11501c2c2d9410f000780b080540c990301c00e289040248800000d418148200101c500b5801e10703249010341410b010798031544000040702c2c00d6000c40c0c10000921a100c0c070130305c201c86203031021a130154559112444100c003e0154000c50389d40c825036070085400e0543d924032442008001d0901c484c9000c004e0385021b000081c90043c9140540102841046a03020b0700c0c030380d8500e074144149400589036a1f00002d85c0000c0540f0b0300701d05000880814208684d000029803050f407003000c00225a10303a0740c1e01082150300c4c401c11041c240c01003803c1c0020003501c1c000106001104501c0f00351000d0400c0201c0010300800401d901c113881490b150810081400340801064014203001e05e81906585051140d01d2424881d500c7c0c43c0d401c02151400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 910825116 1250 910823866 910823869
    0xe21090402071403031f0e161412042603041e0b070806033715020703020d030c0e010e1009030519112718010603080a08100803090f 58
    0x119154194030a10720070180c40401019581d0350404c5469011254030aa08144181c80154841b4110b400051840e842039035180c40b00e10013608003243c0d070740c1800b000d0b010321084090b200d0041c0c500280c50345009180c03850982080403003c4102c0e40003020b003010124508045003a180200c0f039206820031620f0788075091541e0701c804604841c801c060a07004010f02804a80d40d8400e0a80d03000f03900880441e4240701c1c441402051140a0200442c02c100e41003000349001c0c2ca404032071522035805908540c5414407800c2c0c0c0707001aa8000001100140c100402040360203415200e003504e240503900e0100d505284000001c3d0080b0200111a8442c2441440810825114000c61005180d21201380d9500c1078440c83c602e42e52840b088000c58000070304880d40881402c0c029201820303450b443c810220f11040c0b1980010030b151001e0003500c038007000d010059005034002d000391401540704015442d501e0b074401200408004002d4100c8a000c43c1c5810100603c0301c3c000181e030181c0038204c44c00103041401c0350 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 910826366 1250 910825116 910825121
    0x60c0201081b0a2703060203070305090705060d110904050709080715140904150308090a1d060904020319030504031208090c040e071d160f02150c040b070b0a0e210904 73
    0x4c0000d0305140c010107020040001c00d8001e54007440040d181804941c903806102d0340c40703051070300806400074401d10210610001d6604030244002003044202d00c0e0038000b001060070b0310011244039020076031102d403c220011003000100014000c400d1418103000c101c4030010b0928001505d0700101c5032011514480540c0d0700d90000c84c04400301014454256030b680391956142c0c00c07185441d0b10030402500005081c4206080800340c80d000e2101200d4640c1da00300c200052954040c00590305881070310105180e895503141041055800703529070a03100c61440c03600fa41c030404c4204131035080050980c24030032804400101904081c2045401040482030759450b14605040c035403141100d0071100100d0613080540d500c031903005161301c0980c110030700100c100c15981e8144484d0541c0060380101c00101d00c0c1d11400300c10740d400010401096152660300c0ea0084102e401882d0196444604030081c030021700107900c107a28502da00701c009070a0701e2a040101e6440c40e8000c3ca43c403800704500107801c1140e03035540d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 910827616 1250 910826366 910826417
    0x71a040302210f0c1f06030f020d051513120306050907110f3003040305120c0d0507050c0c03060105030a140316030908010605090609010627060c0201081b0a 69
    0x8481c0d0360f07100c2c0c5030605007503540e00217a41079260944166404078404c1708940191b5050b2a00600b82c250740d01050b40c207000c42d807010114107980f0b60080004002411244180b81e07070088000c200160146156401c05110020110b44d0f10018180350a504020b251103005040754460b1072400c044002d442d1503110a42407030600180040c02c0d00030455a025040e0a824040341d5200000c4507101c65140e0380b0b0b0401c200c0d0f00c001e0b10080e0102e2410b118802c8139800c0c1c06240e60b40712648008080c10020466a058107440c0c0507900e0401041010070042510b0703404000b841d415850850050006514110109840702c99105003e000140043d610320100d40303040040324202080c003038444030a0311150078000c1031902136002d907042c05d500303000000070b09140400050b805000001e0001003075034070b00102078400040d505a20411a403034040d030148104030001484009042c140c0703030f21031050300318400140f06d800020111807d4100c0e152425102003241816200c180c4400d0030030004c1185080402914043c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 910828866 1250 910827616 910827637
    0x14130503073f0f060f0c05120c16021002030705010216020928153c08100c02150109020418090c140109032405090c01080a0c0905030303040503071a04030221 69
    0x8280c85041140d83c07000040c035a440c906042e103106915013030307509041c500c20001c070451012b00d100c0400b005480d00e01010480d0680600459140c210240c2c1c034982a03822211944050a001c9001041903040c0b0f007031030700e521070300054010012440c0c0d4400d403190350350b5611882c05031907034610706156001545c0394014040c029075000045645e4006c00c1c103079070900c0164124600d001c0030b0100548016048440356041d0703900750000d0f10242d400b4405030340041002c4004842144548081c600000495902050203049880009070740c0b01d00b00385400318403048280c01c07580c501d49000050b4000c80d401c1b90680094450b007010381420741e201c050040343d260103a900080d045514500d01d1141c0c0c2900c942d0400c087e40c10a250600031035407904492611f5004244d10035001c00c00000c001020140a9070200400416909184003900c1c0c56001007842c0d0341084a04031040e80c000981c050038400e0700c1c000c00741d2606002450f00010b1600380c0d8020f4440c007111201c03a4042030000c0d00c01c10301c0d1452000782d4170304505 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 910830116 1250 910828866 910828871
    0x51b03130e1021290703200d0b040605010c03053009060609070806010c06110d1a04050a06050d030305060f04020703021606020d14130503073f0f060f 66
    0x400c02c034002052901e003c000c8a1208008149140603000d0104009040403501120102c13a92054400d80103490580c0d80c500502e2007070040010001c1c0c06030007a09601d14803150015032800030106001c2203d071541c00280c10f00110122020009130b002045569601d80384025041100d64507071603801300c2000100c00342204103003e00b0400c0880000178074030f00c0b43e9030803a040203190725108010ba071059000d40300c1d1381c002070382d00d00d01c080400d80300c0d0032070ba404490360445940741105404129048030070f010f841030098105014460070a2a0501800303403c107401d44010080d080c640030014940c007285050060916481308001210342d51002480c2c205082d02501c25555104a803900035103503460140a00001000d05c03a022030014030001d0f07e034806a810f07844007000e420004080c880141c2001d5a50050b0002c0d210010983c2d03201030080708024040d400c0510400700643d050100046000101e424400300519114032064600010503402d0300d800002c18595901c80b07041820140c45002da8008000d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 910831366 1250 910830116 910830149
    0x20a030b040c090b0609010507230a1406150d0c03020d061416020c0f0a050604151b02010e012a05100b040501050a0605030c0712051b03130e10 63
    0x154000150711482c810101a00c0c90741d115481041100e10514400b50450014002c3c0201940641c0082c0b50f03160160781c40044c4e50011403003141c901a00b640085140360062800713182044842d4420301c2c035030010080a0400b500e80b640c4030341034108848240c14400e0885001c4102030105441c0f41e44090750300541808002020342c01c110018042c00406203150020003800034147c01850810341c0c1c44444203a015001d202980d01c20030001d11400f0550756072114500e80000340780e60315100280010701044500c1d5100c55000200500f0349416207403032125004040a075140140c0e403018002030605000d091403100450140c103980401501070041e42c0074004141038120a1200000d01e43c415101c41480c00d1043c600b0031020f000c192a02803003140d0f004825044240422805203001d5a400b00c4c102000c1d50078220355844082e2000344003401c20021038400107070b07145820003030403080c5202272800c402186000880b42c80540c050106102d8070481800200c0402c515160050904004148051203110b000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 910832616 1250 910831366 910831373
    0x7050c0d05180f0108060910121b0b07030909021303080a171f3006091a07020c13150605030a051303021f0f0603140601060201050603070918020a03 65
    0x5601508590b01c035600707508445840c910f00119855519601a134407034805444810078400b91150140064050000e280300100c0c0b041d080034a00d0f442030703008401801c0c814000d0f2082461010a0341c20860f4858001c002c0750020a40050101040b02da11a000696030900f207580c0035003120041d00000d005a40005d0003204442c2c0c000c1a45010503031211200089803141e010342030342e80342d00b0903d0000d0709031492001c1048120f10a100408010064226a02600c10700f0b11450024920f00045603060740d14050402841144103250141822040581ca002d04203040040d5a44210810080c03042d401c411580e11405c0f1180c10868100c402810000381c4030f6295600a0115001240c0404c00140b83c0701c0040c1215401c60025644680c040d00a0800c400040072500f00030080c41d00308403045c030740300c0d044034508110398443c1c2d200542c0500d074100070402225503810300b400010713404002160706001c207200c2c0e55074000c94100d040341d001c03a6001070303000c41c9802c58241d00044844040d502035035602001090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 910833866 1250 910832616 910832627
    0x30b10050c070f0815100e040c08060c03270a0203061810090201170c040b03010e01030b131113090b01060c1401050f01062a080a0e0913080307050c0d 66
    0x164001d06054440c00303034460841d945010074612680c0c0c3c89a00180d1860443e078030060206030409000609500f103992a00341c0702d510351030281c50442c2c0d00740c442d90040103103240900080390018401e03001c05103581450b07101d544250101c1084140700b4001d01c110351010705030812a2000b00741e4054156001da140c041c150030b0070346c0458007030b0466901807001c0011060f18507105560005074161990728151000d01d80000310b0b810014045900c4510030400402c0095290010314001c0140c0100300201b0b604500d444c103000a80034040140341c10b40000c00c800011007200c56507198200507500121829126180207018160070803000d13040c0b46082d800495280c0e840f0741440c01550040045c01003d88292a800c1d089480803900720b03d160f0650001400128400e00396184640c9014981010035851000704194060000400f140c00c11800a41c000c8499041054825440c0040343d07080c829140c08150765404c2c200481c0004c109400000c001b81907580218255000441040201c0b0341a04820401404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 910835116 1250 910833866 910833877
    0x1d06030f0a1101090806060d0b1306140601091202101d120a02030601080312060d060e0102030a0b040f0902010210020a110f07030c091b0c020a0503010f09060c141603030b1005 77
    0x16640e004c3c0418400000207640340500e50240010390380c0441d076100c4100141000d000454000d01c00c104a402080043c003070050002c1303100030342184904000c2e0001d08541c3c0c081d409040d480321980d40c141d025980b040050f0310700090f2400e000e403494050203071181c07100209a81c0c1603030003480300d10005c4440200281c0d101e410b500c2a811903005076264400c10b581ca01901040308840481c4000044440c201203c7d02c04ca024460030001c100c41c21040011400c0e41c10407282d010310650764100e4040b181c47d1078060405950180d030000c210070aa1500002d448400d281c0364140e44a400044807081c4910a1071501c24501a0708203491401607800200f540340c072814031007580e4100c3c0b1928007059400b414860181810106070000342004110308040c1e6202d00d40180c20b907448103d4035000195500c0a0095102141013000001a0384000d86032000882d040083e2140030444007040c0e08419241450850300106154030301420004110b10f400c502500c03500a410b178015aa144240a1150b0401c01810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 910836366 1250 910835116 910835119
    0x9060518060102031c0f0c02030333041a0f011103180a0b0f0c1c0c032102030c040303021011041208071502030a29060705010209030f0f06010602071d06030f0a11 71
    0x118887c03618080ba82d03400255400b01c850701d200405850400540140c0000d91198480c641c4a030034100750000e007c85861003848403148820340b0015091b0f1902d00483c0086480074288a0a075003e0500066640e0107132050f841882a007100c02c1d4501565503212005c02020310f8246682c2d85c4150590400c81c0e030b0460a0854443d11500d01400030490803520780c4951a84581e0310090b00c03403090b841c2107032146002e0102c00103860310a2803664031500075000461059a810084130365891640c07900034079004c5003101c200c41143c41c00190001d102c900004442c00c4a10304591043d040c003690418280f0351281100c0140740310b0740f00580401c2e0060607005103110316141a401c10848620388480c0710090000da400045010392400c0001603450410003614000d4010400181031860310000302c0d01c0c00305217000203149580030b451403210160f000c01109000d00041e10150614034680021103040c216500e00d4428038180030700000700c1549040003e5076400c3c1d60241103034009001d9083c5007000d206e03c902d085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 910837616 1250 910836366 910836371
    0x10206090d120b060d060f14360a0b13020f03070302030c12070201052401020601060f03091a09070b1e07020f060d0b09010605090d020607060e0a031809060518060102031c0f 76
    0x1610983c10f011449104201034844042d56400007141c50004e41d0010240d22011240f0f4880d01c2027000d0b408040f031040c3c551000001c0d10030410010072550454550b06601118010051035010a00d04002c0d260002a9800e01584988814214103214090100301000c03041c1c1d000708010a00c3d9054024a004040000d4914003030b16841c038882e0b400314001c5071802d0150344170300010003039030703200d04003954003a605807034005940c0e0425550b00328140d8070903507001040c00c5090103110441a091042000411480c0010b0789880340420048044840c00005620715000c0032a5450540d00e03115000104030a00a00955581100300c03034401c020484150042d0185800400206055001d6011101000ba0060840c240a05103500300100b80e40b2403441140c0c0716440740c0145460000c100b101c00d9402d0310a0302ca0a4844071600c041c000030f81c8607540141540c5003800c4040110ba00c85400072217484c06080b0409840f40d40c1c10005034914440c2070400e204e80415000144040c110700c4c0c3c0501040da5041105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 910838866 1250 910837616 910837619
    0xa0210030b091302011718010e0109020f030c01080f0a09080a080a0614010504050409083f01050d02090702070b0d0209010e0427290a0b010206090d120b060d060f 71
    0x144180c0f03030038004000303020030b03120481c5800340791203007445d95400b0002c1002c84d20009100d42d603070f0b03080d1074440b44000426910740b12034000b1850800d1900059140c29001407801c010701c82c00003032042c44060021140801d1190104080141c00c0d04001c0140e0b4010081170b07610340d0b01b42c07001004d480d01141e00074480c501c6c1040100b54421084160101c18205030354480c1014140700c100710003002900d40c2161002c80070014107004000c1d1041d040c05d5960100c0c06240f9031040803004983e501d41c1c94880c1305880740c3c16030050100e5074507070002e825040d4050f240b0f9140c1e0740e034102069140c200d094020f0100c0c3c5001198022000109030010013008900703030307550300d10000400706020948000740259903038100790415240a10141c00043d4040318000c03d8403241d000004034054208030180f12521280c212440100240500036028200c1032120038130092003d49007129020342c45610f81c1e02c404c030801808081503606204940c000c4940030900400041c1d030307401114000b1000b010a4481c05a01c0950b0420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 910840116 1250 910838866 910838881
    0xf02011101111801050403061113080114010603090201020f060903030108010c0509060a26040c0504110a080f1315060f051002030906030c251e0807060e0a0210030b09 73
    0x102c1090590a010941c1081000094482c8400140d04140c0c10000140700000c041807050141d041e0400b2004241076840b03d1081e4900c00d0380000e500003000903814008004c2c9800e00340986541100d40c2e62500007809078407403004070304040d00180d030009a8803810f028400d1880e80400114105c91070308000300802c0140030420390720b07030241d04501039010b0070900c80203141e00d000710241d0300d42c26000c4c0140c802070000300d00c0c2d00c0c148110075101a01c0404441e0703400d0044c0d0500d8410507006142e00e1000b141099840030b00104668002001c11076050119408561030012020010030a50740c482c181500076480c034200040181a035114020314003a02c4000050142040541380c2d030030401c84e5019510340502a000e00000c0ea2001e0030741d500c000c01c108502102c40d04902a006c090028003455000b000c5a103080003103021401411240254403803041d84800241d1301403c4589490b404100401c03080b84070f51307059003082d030503000180d000b9020b4070450700075503030503803144c3d1070240301301d900040c1d0780c64050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 910841366 1250 910840116 910840121
    0x1d090a06060809010e190203011e0c031406090a151a0903070f08191a040f06050109050c0403150e150f01060513030809030c060c0f011a030c09090102070f0f02011101 73
    0xc0c030040142c1203900380c10681b005280c1d802c5650b600140c00800c103500d003000301121000b202007485040710b0703642842003030440d41801091282c0d030b4000c070b26504900780301d00003c01c0007034050200c05115603990103a0125440501020340209801c0000e10101d151050318440d4580c8038030502031084c0104a0049081c000040c0f5603c1960140d01c01814603c3d149645000642440241610950041103031014191084141a4442c51061801203944403181c917101081e140d06030844012070b42071200704810300070008161400c03070780c0020801074180000200003005124103090f00e07a0600a03544250325450310b00001d20301650503900101410381c1c0e9000c0c02c0b559170150307600c0003003802d080e4501000442c0410001d03141341003009060710590360700c000c0081c0b03c541c015019000507403c46400c1070001c81d028821004003604181140030a0400000080d8440340d10b2034141d03100f400c8120100701581c0095058070a1144c0c003840e48403902d444d41c10203401c200c3d00640200d00184442c00c4e019007869060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 910842616 1250 910841366 910841381
    0x1061a120c030108150c19050d0507021b06130f1d0114030c04020304230f0f2b020a0c08031306170609060d02030105040605180a11011d090a0606080901 67
    0x1007000c1c5c45616010382c00031008010142c0110f244203c18402045400c0c010300854504101940b0313256519070341d941258060701c3e0002c203108255040341420040c142c0300c88149481c001c4d02190388039941c2400040c000680c0f041c50704078111881090401241900180f00745880c68100010b0402460780d0740d002c1c00c500d403105541020342582000d20b8810701803e05801864005124039402450282d081180c0c000380040601408207540c0055207031512044240701401c14501039034081c2000b000c00b40c1c180140402d01250800015030454101c00c0d030540300b84a481d5401d64824240310416030f54102050780ca4010051488007010345a00018025001c0c80c032505d520107600411f500650b0750340013080400310740103000307940141801d02c02c103005179001e20071a80304904c522000651400c01212004500d65000d6500300d00e17500c20090070f00070070006254002d4254091034042117124074074642c1c003103014142c1102c0340c00141001c18001c000c1e0181d00305006075061079641480355950a00510300744c9011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 910843866 1250 910842616 910842629
    0x9060314031611060f0307020109030914010503130c0f060207061b0b0a09080c0a0b0406050912040b03060420120c090a031104020c03030726190e01061a120c0301 71
    0x142d1a000001021050892040440281900d050140d48210590103610445114005035968692441050b403c0310600014040b54400c410a0960200010307001c2d00c4081d050b822100503110140d41003042d07802c1010040e04041d0710420083c0e540e0a0069900c0b41340780500000700e4603c1064221486016071a01c03407c80e00088075448946132006041c0c0241481b80040e101858104001d8903509820090051218807131032840069140600700711048450140c11501d258000040343c801040034003090380e09440080008554030344521000400501c205400194203a0744403507a40404240c58002d004038007581c501e10700d941c0e034540e00300c07000390f1082d0020183d111040210520200e400c90102481c0700c0340c090401032030210b50300045451501304484010005204a0000c410002e28240403440020004030781200307070410000581d0000154098a080d16a641c2040c2000501c2500450010088408018440c01c84070300324800a0340030010144017250b009000c2040d01c69031108590403202c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 910845116 1250 910843866 910843897
    0x3060a03021207080105100311040501050d0b2206021218030a050c070b0c0c011403060112052e0f05012604020d080a03090314030720160906031403 65
    0x203581c00c200300705480081040052198400c0450964402d2050900841c60000c42a491510b180b030311500d094520707c1d0350360117582020f0040003140c41d016207094035590b204d0031642495813500d1140c2114485000100710752001198440301b402101d9004014032516555030408586c1c804030815800b100b108041c00e0150310402003455020300c224090141451036030700740c500b01a50742d600c074107080d041300101e40601c1d00407000b81b000c2580c018188a10104003200c0850852a1110020b80328800302c0c23107500055600d960018031805030808200c0042414101e103016001000285c0b540208964083c6254040c1c81c00340204481d0301514014901e411020072004920404010b25545403a0190040760401020110320300001d10140c0501080100d903940003a0036069400c0041c102c80b602034130740a95075001c0003031000700da070702c400c00c0300b03501e24943d00010f80c0410340d609541c68200140054030b8540300b0244d003ca80e040294000008803030140f5116000d09900c0038095441c1d108400e2407201440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 910846366 1250 910845116 910845119
    0x503011a011808100f2f03040201030603020414010905090f1c02240a0c1b0b07120c02070312111c120504121107050f090903070f0507031703060a 64
    0x184a0b19150702e11000c01c21402c50704580e9902c1d410f250250141c100c407512503d5550b130700e803400c089203d0041134170380140c850302840c0301200c4801000b210282c1c2c40310346150700000090035039010707420072402558040c1040103420032403940006042020f010300c0e80386900300b1010480544000403e4000c425071440500380d01902d04421514106042c1c08010a5001d40403103030f100707801040000044611820f000d95644e10348203050030119080c00e4250b02c140800d0b1b1500c0202c03005400e80010440303611880d00c4825444000040d02e400710740c0e0707400394030b10ba040900040c0c0555011424074100c82c450503000c1d040311074a24007602c07440c000c3e4524260980c011440315028501d026550500485d00d400d240141810401c1c880084d981c0449040d124423514482c40e01806910601c00000c0c1d044000160800905110028505041c2c1c2040280721340316120201e1203100b01070003200c0c40590b204201550003c15494400e440740c4d014881941c905a01c030340d002c5121190802207a119a50040071900b00a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 910847616 1250 910846366 910846369
    0x1090c02100b040e0f070801060f060e040c0210060b0c0c06120f0421080601083301050c0106030609051009111203071205190509030d0e1203180a0503011a 68
    0xc041190000f0f40c819226a00800c8404090205400d440d5215026151060034142001c2c259103440d40100f0400c000350000304481c5170300075031194002504441c0801c2d03440d034145040f40780c284a03031400b02c140e1740b9044002500c3c0400c0001803d05c80402c806442d0069884010080300c1c0c00303000c075989c102032500e00004809e42030710b40700c00d98003e11581403900c0103c035400080c0c40324002d40180c00040f84000e014007101c3e681003041d95600c00e24a0110841640142d944903c9040e4095100310926131540003841503a8001c6068582a101e07020081013111b5580c00c001d8040c0044980a40c1c15003c1e001c403200040b60640108142c040c0c110798a4003002ca280e205108400c80b4840f19600640400d0110b0f20006006507000c0c511098a40c0c0ca084d110800b514070659101c50b01e030a41d9041c042d00b0014540b254802281c1a240b00c03405040800944481d4070102d250b00000340c2ca072810501000610300d15051b1a41032803a00c50740d081d2004980540c4a60605081f00d0315209469076840d588500c05007a07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 910848866 1250 910847616 910847621
    0x70602130b0a1701182309060f060d02010c170f1215090420010c02060703020d020c0a26070e01060c0605010e0f0a05040201020313030507030b250309020a0b03041a01090c0210 77
    0x2580c06c901145900c020894024110150040d90900000d40080f02880090302c82d112140350030140440740c1c603001c441d507079002070203e10740440000c0c07142201a100d43c1c00c5120840640300b440c14501d0799655141845640381c04183e05c101c0d03281c17102c0508110a45840d007014286588159445010041c54841c40480d0219100702c07440e819040000054454006880d500d000d07007003a5102c0c0d00286028501280060304041d43d4000e647d01413a5009820092604000111403401914013804d00c000c08260341d030700b81080c0080e0401a094000c4500014441d684101410b1455001c1e407000c00c0981d88980384942801820340c1c21440000c2880c0c0460802c03d41640304907005841401140c0c030b807086601c3c801c01c41d50b1403035205807502d0300001410000d0042140c1780710b91001c6030a1700403074403a00c104007519008841d00108010150b513035118004640798040380c070000d003000344a21a00d0f440c0c07901e0030026180c0d66005042e0a956141c0c00040c45029a0243d82005d85e07507034001d45518101c031100b4000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 910850116 1250 910848866 910848881
    0xb07050415081b040b07050f011a1c020603041407050a1a0318060106051e040501090605031b04092304080d02070c0312020607170903030c070602130b0a170118 70
    0x40e148030f036440704050b0b07100480040005000340d40d2846d4407400304d070a002c0c2c2000080c0b540e0581e164144818107650001c0181552585502241d41d40c02c2c418034402142c0c6000744080009401441c00070503c001e014442a01c1d5055507489400c46111540340d80900c0443d041c18864103001c03118800140c406000100c02070f543c06034540040841004ca9009140d2500070281e1150020881c000381e1080c107800051000c0c03003c85020703800986000c2c41c2000082140b50288103407010000c001c03022401802500c0500084009000003190311983c40702c11440081081c1041f01464501c01d002c100d00400c01c036507015118640240c047d80c00c01ca0345031040800b0354400c210803104110010004000220505001000051a03500420052a1815000c1c0480029220014001c1c0c414810080a41d0000088075401420b680c92035032101914a45000a801a02c031401945004803001040098810000c1c0400404660710640c41d9070740d04503c0b10344c40c2000e0060340c4890301d07000201c40a02225400980 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 910851366 1250 910850116 910850131
    0x150106050a0e1f0e0103150905041e380a0e10090f020f06130b16050d1e052a0f0604060b04050a02090906190b040b04030b0705041508 59
    0x4944030741d400001c228140800c0c0b2500c440d4051035000c030600d0340c403800d410008113003800d08001c8280c84001000303d16403607104060806842d20005020040300542d201d000c8031120340d84403c862510f1810360b65220751201d0540702c0300001e034924441807441c0c60080c0180c041c0500740f0391040e11100d207080083c2c02d180551002c05d1050040c60300f45261544924401c40e07004004400c0b100701d103841001812003044c030440740325100c00c4c08406440040c11659004841700d050440c1d540b05d1f5004521003081441d000007900c58020b09004a03400b0790000c8425a03401103010500944222200c010b9440d40154010081304444013074500200c00c017480d0030741100600709801c4403503070010415810b181c14402c40e0704561007038031088001d003581000e01810b50801291102541007484081c0443c010f008020482d9118400002c0320056a481500181d1f0203080c40348681a5543d4503020800340c2540684012036515058200003803409202d002580d0a0b2640e4015031421404158403c5940b0f000142803c0e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 910852616 1250 910851366 910851377
    0x90b0c1f2a1e021b010c200f04060810050c040f0b0913021308070504020301031515080f0c030f06040b011505041e0302040b030d210207020907020106031202150106050a 74
    0x1841540c1c81008516860099600030311103080140c10700e01d00c80e00e09542035030501060052650010b1241c00756400d00100b0a01071f40131040001700000d2545000e07010441e00545080740114a140021561903029a03040b04203200c292541d1406d02c4403845140701d424008150003000f80f21030344141004082c00c150080c092944803101642c5041244d1100006498030204c00404004480d401d2110b0f0b8000e000c00c440440c06c5600d1a25003100e050780000d840c0700c03102c0c1d51380b4102d000c41c4180503004002d420450200c41141c1f04044001e96600a041c420070302c688621105a4095040001c0407403049620494941044e46010404141d88002d40c002205104c402e110101381c1400b408200f01017400c0821243c6120703495801400708440e951004175002c2e030441c03040801000d4002c841c2d13410080041100c4004da40444400100034040c0450080d03000360050144900d142c0d05411010a507030242e1b00c0c0c0a29540084416a1b0b10340d65400455209200c0500402c03a40c1c1c05807002c0c254417452030902 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 910853866 1250 910852616 910852637
    0x91a010e07031113090c02060901020a02030405270a0b0f0a0f050f030a06140103060c0807080402010f0c050102030408042103020a152c07091a0907090b0c1f2a 70
    0x1303004906800c1d421140f00141c0d101c4d0680d00040d0b04000e40303a00880f0540085280c10782c41c0314000d44a10a50150034080c0240c0c044900440018490281e014550044450314070300304600c0704005000410003985c400c81c844100c98440d03252180c100341c04c0b81d541c2280c3c40da54030701c1c000034000c1d10341904111b1580f500030420ba80380411a28050700e08541c50000c080031442d07046190203001c1750001100f031710070481c003d001c01042035007100d00340e900140c09003010b09543e03207680011204052840e4000f007240d400841032200700300810b400341081e2100c00c083e01503410590313812080d00212880e0042c0c0180c3c0141d844401060510500b000b24040c894008101ca1269000c0c030380700440b003140c49200c0d0101070b200e4074103c00c20504c41c14014010f1860240581c24140700f01c40c1c0321786d40801e0000d1140c07500d07801185000d4015007021000300f4041e2696a2101c030f803031440da40c8841d861b48078413050b40c40c440301140714542e540c4203120414030f8003000081112141c8003000d440030f00501da100c0600c0682c0b80b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 910855116 1250 910853866 910853887
    0x120908090a060c051b21161e09020c030729091e0d0e132007110d03120903030902150705010b03030304050a030f050418091a010e070311 60
    0x7800261080343c48001503c0340038900103203000100154809410b10580e0346034220b81c0c0b182c00107481c2c0c1107007083c0700305401103d0140314148621140811800d009010b800919010707038603041c104c1000402420901565900030403401d92044c9181111070350010400800082c2840740c0359444100085410560ba880303c0d1142c1c0032211084e281300030f541c2d01c40303240b1488517a2010310803540040b004018182d40c0d040700001511901c120725074580b1901500012400c840d41941c8180200580000c410000c0100342c4007141e80c0350b00c4681d0581c1d400c42185498000c03030400c00301e21140181d240e91019061420b502c440d40c0100001c0c401101051780342c001c002c1c09a40e03407840300403020540d090841d030745243c140303056801c48032640c00303182c043d400501c10800459404540c140c40305d60103080802c0344060124085130707141308503040041400328030003503480b40d490183e001041c00d0344500324601c5140c0c5045503078031a001c804d12070502c80509075030024940512030340101c0020500f0b500203034103010031200c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 910856366 1250 910855116 910855129
    0x6030807060204090b030f070b0703030209030a0b0106121806091e06050a0b030c0603060d030216060503040b0601080402030703150216050a020a0605190309031101091203061512090809 81
    0x500c15680c494010a00b484544214884c5032082d55044004012005101041c0364403902148290600300342e001c14040c0a15001350100d44440d100203003a11440189440c2156654501b03000c0c0c44000b46d11551000750443c41c40c41140010030269600c814110034642d600c101828055600701c2d08a40c110700344842030b101b40c0410a051a11810020403180350507000c00c401c60b130f14120481e01c66400103d281280703448003030450b81c00007800e03141030900701042e003826403400050b0084282003410107179001404603840b9000e140124400c294032a001d440303a80c0116000c21041e1400703507040e00288010000140412165a20796807101400741c100030414a1048012401d65020f444030341200241b1800c40c64080d4000010300458104542800c40d00c291084409a0207040c207000d16a13911490010705024103809035488440b10003d221034451850b00c0b9894240260380d8102107420000b000c180300500d4014402c540b80c0d19590701d40704141c11801e41024040c101001d88035408104181101516402c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 910857616 1250 910856366 910856377
    0x4110d0f14010f0c0203070f02090903071a071826011b02010212010501080415020702060906180415050d1e05030c0303070801060305010f1203020f060717130c1206060308 75
    0x300000866040210000c420f0324030844c801c01c119002006190700281c42c860381c180319a501a40d5041c41c3d95980725050380795104040000c0c049040385107400c6410340d0400c101c10700c168410369641421401e20309154045941f140140000010740b241d030343c0340d680710704440764101404c880d001040d01030400140c00060b050078122800141d40009012403e1080c85000c14010700003843e06008524154513500d1480040c02a24903286030002004010b541d156000e4400c00c410040c03501c4c1d92418420a28400d40c0034560800303000b42d007031250380c103500058125168122100074000c0303200e0800300d80d2102e0101c0c0d0462030bc059103507080000107011681c1003000d4803101481c1e10080d0341d40d04041b8070180c0500303016400b0004060800005001020b2900e2542e01242c450b92030380902a010751805a0408104544820307130f41c0700c0c120410907050740c0304c4244609644040c000c80b40c0c54460800d000d82d409201c00303020b0100401007008226203003031010020152400382c03c0001d00ca030344980e00c088165108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 910858866 1250 910857616 910857653
    0xc0615060203120c0c0d0c08090618040e1209121501030606030b130804122603070e060c0d0c080d060e0a05130b04080901090504290904110d0f 63
    0x81848064240e0310007101360444443c3c134a0a003441c40580312950364140c1030511000b0080801c900c0302c100034220b029070350b2068004000d0358680507104d5865080405c40d009507485281480d90210100e2000315810740740c0b00b2000328507803400303240105000d007210250901401c41c0c450400b4a0005000c41078506028503c1100c010440074554100316005020240000346510300c00a200800201e60300100c0301150b5022103141070031112800d0440000e6003d8030142c84076201000401001080c0d140110302c95491600c038842030005460034065280200030128640740d00c103119000308a03000c1d0303601c4a416071051589c3c0346058000030101054401581c020344452004201b80b08069156009055000032003507504400b0444941b90034400c1e080c00760002d00138980000c2d0000702c0d6480794880c50042c00c40900203001c15440422000c0c0700008840c00042280303544000c840484ca000d0003094041e680100c00c240c00220b0002c108000b000090400b02c40440b01b1540d04000141da0501c2c0c0c1c2c1d5480300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 910860116 1250 910858866 910858873
    0x7030c0b060a08060a0c02071a1204110d2402040506041a190c020103110a0f080606040506130e0109110304030f170a050412111506040f0504051e01060f060c06150602 73
    0x104100c06403811030560000ca0450b011807200c0201b84609e2800d41d03d040c640c20301501d04580329400d00801c2080503a9070150010403020008090125407a51904401c1100769030000890b81e91180008034003450103400e9001804000410549007149800c840c0d4241c0b260306c02c1d01d0200301000d0300300204104080d60011403a001d8150007950303054880c11100480e0a400246400c4400714000c04e4010b4416402043c4070340c40021070385d19200c84040d640036010151520b42d80300d58400c4903421260b960303ca904071014034440007081408450080242c480c4203031403098103545460794150307130a2404449440400518803460f10301141c00d40306d428080c0051350030000e00790401d030071302c3e1a41d424030754245414010850b010f60030031040000d00c410b06c203056101c1d035541500c0d1800014060080c50702c55031586810141440284107010540c0d081c03801882c1400c080f0400f1070b150b00d500340c50306031040020f0350300304c2c80c2c08000d401c1c003950700c010f54113100b01d400090140301600a40780c00300c840c0d08520010392 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 910861366 1250 910860116 910860131
    0x300d0e0304030b011d0c03040303020c2814070303020d14070f0f021e010905040b12010509060f1003020f010e0d0501110316171f0b12070306060507030c0b060a08060a 73
    0x1407240c90045405c08503403013000146014041c24600b0700c0007400c010304041d80001c0b1000704d00804e0210202820045005600d1420754010111444030300780001d0301c403112641c40800045100040843c02c50360705170007811000003541800e40344120040c02140c4a031b001084410b0000b80d002010110f945c0c46818440ca8241e20740c014400111242d24030b0802012004501160300da0b00048100d084803402c66000c180c44401c003000c100f400500c20441d4900c0c4d0309020902c0071104000c6103007807040b54000c80300754140d41e8201e00c04248100030b20010b07401601e004130340100c0394418003112441c07050143c4081802d01140c1ea0745400c51b14000b80c662111040401800510309601403150b4500000c1d01d400913540341401c821001c9420050982c1c804035502a51228400d00da01515030000c0005540c8039072614001a8041108075040300c640380000d281c1900402c81a00907002e48040a8059460898886450751521414180688403a920003c0d56070001000c080400942c0d12600d1407290209900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 910862616 1250 910861366 910861379
    0x8041a0a02040f0e062407060207060c0e100c0305030a020417070303030c03090515090c180702060105041a100207050a030507030b18060403051623300d0e0304030b01 73
    0xf05080e0b00001546800002400481d03540ca8200d2882d5019614100380c10003900c1d15410021b202d550300007820940041298804d00c48254801c00c9502f40540391440c1107007002003006140040407c200002c21120361250300404d01c11000b556004628210040c0b80c076071100e540307400181c200c80e010601c0e0790001000340205980f5025982030343c100c0c3d08041c45144030680c0d40b03545480004504201c48906500041d040101c10003445203a01f8010b000071024110644210003125411507034500507120320000040c41c0d08041c0f140401d20a14103078241ca0b5540c040013003000e282c01d09402c140031885000b81c04a0b10b5996014104019403081c2c0040c4016451491710b0400303008001c00d5090130411100038401c8160f40451080c1e4041c3d0326241c003545e180b4414000160b840044070f4040c1450403a40301040c2c0c010122071001c4600c40801080300d8400f4062801c001e4003003120f07248008a00e800c403268401600c880c1340940701d10095441e000c80c1400740055880c0c0717542c025034402d031741e114444001004038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 910863866 1250 910862616 910862639
    0x40b07140f0a180614181804050f03031e130c0b04080106080c0f01120609230603010e0c1003060e1f0605090d0314070506010b0a0f02190308041a0a0204 67
    0x10302c0c025400840611316258000c0c0007a92040704038070343c0140015510a01000000c2d0005042e800100340d02c80c40745e00420b12140028040b42c01722202e129281010f680d0b8400041a42c0c4604040c541c140d01a00c040c0c03200c4180c130752018190002015204411800084840031074801802c005060583c0300c038030704420300d825a11540d00030f100c40d41090058000a172130707140e200144075400b030810003800306109c80010001d0a0940c400354031540b60080310030030300a440c007140300b0048150117804c0d120b4543c1000c250884405900c0440507034050440d040140c01c00c1001074503010054200060a0b81e41c030408400042012203820424400f00101841d101c80589009000307130841e031804505148040d00800c001040d1080d0103014071020b01c1e1440d404150403401c4034002540041654540d59491502d60070343c3c1c000c0300a420120b40818680e035081480080c07202c0200c2003494188540d41090307103050b9515031003d041034418403801107161070016042000640200000400165035500d8428070011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 910865116 1250 910863866 910863887
    0xe06191103010b0f031b0f09101d0f01020a290705031e0406090f030f08060607020109090213030c030c05090a0c120b0a15081905090303040b07140f0a 66
    0x1000d001c0c401401540c44010603120040c1a010f81d2550302e882d082d00c0040c2c41d07031014680b81c2404c40002a40a52a801e020103044240da003542d04103440010780e00251801b800191103000c5060711f082000c61145070486480c203c83c401030040d1000c400194072014051281d00c201001c164000b411142e000d030722002d1035540d0001051a02c00c0c15820b0469001d91100440d0940d240382e81e504401080901115038000554140c0c0503179045440c91940c074000c3c1c00c10144003862000f2640b070700b00145c00342c00d190f801c41d01c003158142d4840f0210b030308002c3d030710009401c80ca05a0040c805050b50110010320320602520107540131300d607001040c84c6800c007000120600140001011410b100d4000001e9070031504850000d00020f001091b8034207004082801010541d204410f1034024182128000b604030984902403004443d224100c42240c1e9070a02c240c44058417020242c1d0300400c00034021920780201107800000c24585090300c41402c0108501c04d80201d0559204590000350043c881d64102074101d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 910866366 1250 910865116 910865141
    0x40f0f0519050c220b0304030f020c1c03120212180d03142a18120a0503040308030c0403060c0e030c030109030e120c030102041d150d080c010e0619 65
    0xc06440c040c01290310354014051901c80c5a958840ca04c1003070428940c440300503111076189161a45450704004081803110104c3c000980141c16551b40542401cce80c0da0a030a0001c0d03c00d042003150590f4048070000500c0342249a040d60a0003802d03050801c0b1841580144044031b010880d00d00c00e0300f0802c0c20107280454100903d45803079a81d080382d00c0131010495014018a04000c01c100c01c9490031550f040c10b4a0b07032140b24010000324558401408120380d4003420301503401c0d404401020a186540f403804003400751256100b40800c0000840c0040195400300d00c0c0c1400364205070781c031369801c03050f200681c0043c0042009540f1000007402c0810200306666003c400038481c005032510060468010000c105018075080506022403400410098405202c064002c56907503540b079a200300c29844411072425290031160201c0c0710480c00060402d0300722002010700e51080704980d43c41800e540141880d0340655214031199048220500101c1d11030b15154500034100c880c50280e4604891500c035910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 910867616 1250 910866366 910866371
    0x1090203060a06030b04020702041401291602010212030103050303040209241c0b0f070314010608010b0d0605030607080415020708030a1a0a09021801080402030c010c02040f0f0519 79
    0xe55a41d1a0b82000303c41c22400c0000c0c440b0030000101e8040e01c90020069003207401c0c80f0207242900b41c55000181258141281000141c6030701d0304400c6030441d6031449203022181807082d500c0c0d038003003195411015407050044408a0800002008568209a00689854002000304415800c0810080380c1c002c6c414603084005101583c030369600011011341d030901404244412010113902000e910b07900e150400122400d521b010540390001060490b45078001a08005107983c00141d010714050590300c1e59114001c90303a0902c2507a1489400c048803040da802e407102000140c540301403040c1401116250743d0f40c1143d1629007018400c3c1459000311244180c81004660041158441605e0300840e4400c00031441e0525940212098240c1c1e0302c0441d40036034803410015101ca031031340c0104440582400c03c2c89c03d0858020041d105501e00300c030043d402d50400310311440c0d15031003a20140940c606c010400100c1e024840160070850300d4815888242035910024003890501e01d404c03503064405110400e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 910868866 1250 910867616 910867621
    0x180c031b0c03030911040f0e19020d0f050a0602040806100b0a05040905190e031c06061728020403030306080a02150a1e0504030b1501141803010c08040b01090203 71
    0x240740e040d594401504259541c04140104820b02c004485030490042c014081c0c3e100d11800d850040403821030507105031280200100e03001c0d540d4840428226001064048800745645400d0384001e9002011900b600070440e400d800200b8906c040c1024103041d8000305485d140605410a031a28560040112005c0500c92116910b600500b101c040d6000200c0100d45a05d440100e15081c1c8503020030000c209040849000090303e000029001c090300100518a01400c010504400c0715018000e42d8001141440c1005040140030015a080301071200465a01109181040c2c07210b21003915002c0b07520340018041044c0740d4540206400b8000e41d1001d00420700c2030340d002441c203651a000c00c0d0240b44000c00c4184003e8028210304418401c00c400e88000c04940311001481035000380012038121603920080340212800c1e0103041d440400c11385070042e503001040031038200c0303800c80c0343c5a14810800c00240d8100d40c42c203008203600110f090b110311885040c03628102c2e800110507000700f10518414801c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 910870116 1250 910868866 910868921
    0x11101060806060f010c0b09030334080c0904090507050111070f1a1903150b0306130203090109150c20100b0a09140403020f160504050709180c03 64
    0x36207981100f411039141102c50f841c2c1c00184c0f141d41080001401104540e0f01300002003401000561140e141c0e460100d04580034036449811812510210300b0380350032640c0b000d81604d40140780190300701007101c4050b810101a400000d082c3c800f01113045441d6046401d08018550300010b0252035141100064076501e03040c03207103400400c039a41c49441c2610880c4010141e443d202c900072074912070000240020401c00058001e000341c2401601c851410300c0190b40003d120303413031030140e81c05448001c2030028809040e104e81d90103500b015088a159540c0c032010300d000200c01c1080c00031200c46410001c580c0400701240500a40d05401c21031101d143c59606421810f00041150501c21303074030420000361b1515101c0441c01c29420380d0800349506103481151523003110041e00c03851042d4400d500b261105140e182190307071103a41310ba030f401103980780c42d0800b88024505604207662008191a1080c0407584c0d0b8642c5410000c0c1e40c8060400340b43d9106a4070707031a035500d8012a0404000010800a000c95011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 910871366 1250 910870116 910870123
    0x2115091503061b1b0106031203060b1c0b030d0206060315010b0406050a030f020c0c0f030706050d0f0f05160201240e07111b0117040b0f0403020a020901140111010608 73
    0x140803c08030039845000414501680d41600d40e420b400740d910a0340707042040c10343e900828290000751017200c84982da10b280a07104e07005100c10746101c80d54a9040007458400603c80712003642403081e04640320740150210f600d0800c1402e52603030440e0b00414484c00c014060600342004030010354084900100144844a0702d44100c0c2c0880b5218601550f80d041440b02c00c81c0104041c4005800b101c1c00000d9580c2c507a500001e02811000c030403a004100c21400d00701701070780e8030b102d8890301d400301d0b009000d400c0340c0c00c5103903004400d0b00c0d100410224580402d4041c1e8011224100c0783c030000d441008804400f01542480b42c03101008895007900c00c1248580c028040d05038580c03051205c1183d01c0380006a40c10300c2178021182d601c0d4140d044030454100a4440a0002d540b440514001200e00302c3c000016915401030034022a003290f4039064a4840da01c24605100d8010002d40c158400c1a0b8540b0050b11105421402081d0011303c40400c055480c4c001803c052455280300301580c14400280a51b07800070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 910872616 1250 910871366 910871371
    0x608011a0a080403030e0607050306010201053603070f0b0108060109060302090412230408010e071508091501030c091113050f19031406070507050a08211509150306 72
    0x30b007054161a55149001c801034906442000914098a07040c0540107030440c0107103000c0c0000741c000f07000c5aa01c0401d0681140c031600c0c180900706411a00302d0440700e0204548440c0d0b2035122041d03031720b44101611145030100105504943c0d0f0b4100f80010010302c0d606101c0f042c0548080142800804d1031500011240140900050800b444201138015414060040c0215054900c200d1032040c500c1d10003d803440d0341180c440d200c6a5403c0481c08003c5d1400440c82c03105490700150b0744c1500e441015406c540e40d52004003d2410f03403065920000400482009050096108a906007022418805145c3c2552500c0150b0001644188104e61006581742c0106056407416640400085040400584145810f81c440d64100030348103000300034001200e030343e817042c110702001b00c41da00c1c0c0b50792204035460702ca420720142180c0c110101020001e01c4d418028403140c201e0802140455a68403000310705590181d801d9000342c0400000390555050040c10180d0012400819002146508002c2a10b84000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 910873866 1250 910872616 910872637
    0x40f03020a080d1d041d1006080a261b1b0d2402090d030305010503010c022406131d0633041103040308011a0f0d050601030e0105100608011a 62
    0x680700210310540305c90b441200300210401d450210410b0407000b00d03440d00c10120300b458050341460300101e0803500003e00c07165841e9024030440041c1e418400140340d00c05041071071002c51201001460300c0c00e00640703180c540c0040494081c01e45641c1c0e5120300c0f8035040c1840300c4140136070003407941d01c8003090450a02072520996500307003461070001c0a982500078440c101c1900c1d07100a011807081c0130b165069100c541070303a10640003007114218402c801d82c4c1c1d0b0f446d501c801080903c2015a40c80c252602064110707049040508090340d0354101c1d100420942e40300c194080c4200b100c2d40d0418070b4100b0204111134010034070b03000e0151040f05040e41250102034100414040c00288031907200f803900c4950040682c02d10008015031641083d01c2c008107038003030a00c21a024201c114070f9000340100c0880c11a00480c0c07400c0d00f2189405001c84140c4054480280f1240c181a61070080044811081c003c1600c107c881c10904019142088006491041d060700402141c080000354044041410000c41d215040c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 910875116 1250 910873866 910873907
    0x51e0f101b031509050106050918041e030c02060f0c0c102a060228050a0206072d030f1104121b080336031c0c08040f03020a080d 57
    0x3030000101c40f04165221400051601d800014155808005010110030403110205034981400c0150584d01d0705030380c050020711b00b15412080d418500b1008000d05480790410030500c0c1d041d070700041c0301500407030040c0f4031140c80000c911107400014000741208581c119805448011150001805481960030008821000401116450815201c2200c1a9500c500199940c01503e01d900c1609105903041d00310790344070030182010b2140a072098031400c500c2640109450365400c541103804040e090b10352452864030b599280c0791008a20040300110340c641d1408184041606011011181c5003118400b440506010a010181d5003a418222103904a80c4541c01c0002c800c0001c03800322144c0e030246016200004410340b8400000c44100c8110540b000701d80c103480c1203e00c908901d0451a091154550071035007964030a10a80d201e591821801c0386048010012541e07034030346c0c02d68402d4000041c1c0b0300f030b03401081045250103c404000740010074050092a02030f0000500012120454800d00342e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 910876366 1250 910875116 910875131
    0x10b030703020c0102040b0c0712171b0a0b0106020c0109030b04060e1603110306060f0d170904090b09071e09050c090907050d0516020307020d051e0f101b03 69
    0x140719070107440c04a44040b00842d03585549462410aa0f40040b6901005004084000401600111090740310b650480480100012040340c1016580d00100700d1140d2040c094039044240d142c10003040b02d145224044454180d410108082d25000001c11400d042201240302400000e140c9610b464029502c03160205135440b40366071080c1460700e4080c44803903c030a103403000424422081540c2d40c10b804203400b501e12a4662405114000c8203070b0304071035004641041504c0026003070325a903600d4016580c002030300b080e4018000509403401e40c842515264a0744013801b085040504c194002451a84186011018410784119501045205950303156070b950b000640038403a07074030465040440003000501186061000a0010f800404651701c25519240004802d40080071060744145482d4005606009065080110700183c00000726064007a039960011600e442100c80900380400340060110b0702ca448180c2d529151803002c824281c2c505003050200580c2c0c400c0180050b450700740c41c0109044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 910877616 1250 910876366 910876381
    0x6031113053102030d0914060a0e0910030c0f05130c350a050106021608030904090f060e0a020117060a0e0402041d010f150e070e12070305060402040612030206010b03 73
    0x1502c0c40401940501a00c0d1114580e035034085002000d40341368001e08081c20005006018190044c0c41083d0007040400100580514017483c40660044150060b81c0060383c407607840902d5001e541d401010494101c090a01082ca0b1400c036500c50901454401c010b00b11000398001e141580f0a01b400c0925601c034000f40d0b00110b141680d000c80280181c0d044c002034185410100300400c0c00348200750040c050814510580c0ca54a0382c04000c0b9841c280084d402c00201008100091240c2002224200c2d114034060380058201e000350903079540d400c800b42607882c030340c1e00015048185c2d89100094580f444002c00031955030f540810020f9441010307014810f030355107202250040518504603101026200701d4005409815000700000f102c4114042c005c2488004425030861081d0099001598461001038680b5100d44a00081e80e50010b0540d01c52a07130401010341001d500350001e5603540c010030104415424a400780400820384183ca0307030f198491b9610025190101030081b0b4428840010205600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 910878866 1250 910877616 910877701
    0x6040b160605070c0b15010804030e0d05072c090d120905012a030915020a031e02120c0405030d0810050a141201051306020f04090603111305 62
    0x1010341c4003104010034103020601610324040d500c002c0724000d6100000501215030340e000c142c4103490607194040c280d1102d990a88200001040b031540046015080c0d00c007043c2c04000a40040150b5030a2620400703c20318584c024900d2000d01d041104545003d000c4888800226024900f00c02d140001105c0017440c21701d0050060950301611640c00c15440e4100b000d084e45529003072190705002084c00311000388040e01036608080c0050485104002042c184c1541074004080b04070492030b0025690710503218466107440902c5c484e2032244c1e070205000705040036910525070000074540201d07060034034000000796145400e400140c101b09554002c250301105c6041540d0141030010009600d058a03403d118a424400540c05481484c01544400d084e0006101e154041c14003030540304a08003e940702c4c2c40180d4081004404114002c200010b1440032a200d08000341d0f20076001664045046403c0013503043d01030883d540c0035440c00c1c090000b0411444c90841c0480c2c00b8003404904409000b07600043d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 910880116 1250 910878866 910878907
    0x2061308071e1b060305070516110402030f0106020105010f0b0405010309020f040612030323070f11010609020418060e060d1407170d0f020d0c0809030709020a120b06040b 75
    0x80544400c0c080400c01c02c0e00030006210583c4222512200b6070f6802040b0117070340041e2822008a04100300c80d0f009170641c0a40701034898040c13100c2c1719039210b429021608980c0122000744032501040c0044c4074950342805028010904c4600c0c682046050005e0600b50348a00c3c420309040c1540c2d042d46400b15100c0103904c04804600030000c10003a90784042d0351300c804030b1050741240020329288054001c80844001c0042d84680006503050380e60b95240151917203002d070954401440705200401402c44000d00400001d00208070015840303e02d441d400c200005500340752050380f142043d0b8180308403120034080703c0d4083c204a801e10303d41400350a00c0c4041c03580340e030565100c034051090007095034007001d12409400005002150003014200600700c07905404203144a0041c0c101302105050a03106407540c4c0b60351802491250710301030020000074607003c0e0310340c080207803181c022510144941d0410100300362500354000502140740b208000601c54821030143c0c1c001024040384105e101c500440d460304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 910881366 1250 910880116 910880153
    0x6070804050706080c193b011d011b0c031b060f0f0f050c03030a091109010b18040e0d020d120b1c06091a06090c07050c0409030e030d05040e070206130807 68
    0x142c900c1f4581031180508070759482814469403d49004040f07540700f20804200c48201e108001d900811070300045a15203004485040202c8450204e100840d040001c01c0b030040d84038002d06074504461081004001050b41d03c00c005116890104964240c1c00001e0600c003440d1600d00140c90a0000741709407a02e004140410300306200c08020003480d059507610044806000f81c0416056070418010030000b61400d02900b54851000c0c400f9008207441d40040d8140750b40024400304901400c0c0352040e10f05089c0040103001607005800c80804540c001e510304c012144441c2c400d10401d4107400104485185141a01c41d2420b40c00c10300300d0134009154440c081c002e600c0f0411410004c1c0441030038400c00c3c8203880b018403881480010036034002c1048203d800495100000c0c0c180c2c0380901e800c210003090804001c0c0c0078002f0700040c488440d50306118100080c0150780315241c881c0c4c2003040c22030082d00000c203144199172180c9d082c005400000082030031145d6200c1c0409030395500d40c2c6071080c0160440445070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 910882616 1250 910881366 910881407
    0x1e05060606070b1b0c0708030c010b030a0206040e0421080f060f010e09131a040c0e0f070809010f020406031a0406030809060309011401060e010809162606070804050706080c19 77
    0x12880040100040920300427000091081c0c0c1c4040d410140c960303502c2d180003036010100300010001c100c6c0071040c0c241e0150040c03040003c2040ca24072204200001451900000b585c06000c0210040b650541d1540100b8142c600010f94000c1c840084d0100e11074030301240c4102c030740000084d2181c0d1084150759251350f0010f0501445030f80583c20858006041e02c2c1100e10a2001101081e86802c1d440d6aa118525011103600d190700c802c00103403800340004d009420039540790b20b0048080300c00ba00007017005060300d54001810782201701e0850030000740386400e03c0c8154105902040811458001d56a40010864420782d50ba202e00d01d4141c01000c04981c0d1000443c641d10002a0302030304069224000d0602f0f0722240e02e11341d00c3c040016240c0c01080114469004406414401d031a003800c1c6040d0001c3e1100c101c402180c503080c103180c0c82c1690071a60000041d046404110402000b840303040c00070321682c1040d0119082410824116002b01e2002800c601c2c91800720503031907403081c072202803800400003da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 910883866 1250 910882616 910882619
    0x9091e0606030308090d0207060e040b0a06020c15070203030306060310031e02043e1309050402040b01050711040209010c12031a0a12060e0a1e05060606070b1b0c07 72
    0x2102401c070511058001c80c2d141c02c001340c8944408130714921142e9081e401740905034201601560240b0000c02d0290b040f50351030200d50036948900e06050090030a0340c0080c00903c08040402c200202d03c2200301c84e0000060005800589000058030307040032003291415101c4d5141c0d030b200c42c542207542d41b003e0102d04c540343c846d0305d45c50001d2030820f00b00f9009031400d04c030301c44921025803481c0002d00003c0781c0502500040000000851500ba201860b10358092031500030380f010700180180c0340781c11212205540d0402c2c40110300d0b00c1d10411300000e2082c00c150781460b5813922200d1390589001c440501407a00001c850350240e1180b8807015500d03602642c200b2050328002c0d030040080002503e0380030201c2503240d200070140340901050089441c4c1c69049041c050480ea144006042c0d01030002402d480750b05100340000b09100c0b050a881034102c1e010401924080c20b005142c0f580250040740a501c0c100002008913040c6c18400e80e01000c4554040503000f0302a4401405128516002a031801040d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 910885116 1250 910883866 910883873
    0x203030304140d09120209060406091d0c0a0b0a050c0a02060a050304060c09080c220504052b0e0409390e060102061807050d0b0106030f050606030109091e 68
    0x10450501c1e0030718116040c0c03440110f404d80e0400824003800c00c4000549011000501d00302550f15030006028101282059a03a100a815035000d020101c4003041d403056481c0703104030104015803201c1c600321100034001d0310b400328000b194492542290304000001440f101b50b0320003040003100c6035070301602180d501d5400c0c0c04011300503003003034800326103c60410585044541c0f18209840130b4641880203090000544410030540c0440300e20f25481c101c8010255480c2200944280c40c4038500071700190026500c800340b05081c001b000c6058039681b80b402d4061501c3d50354081c0540309070010036200081c0c4400c2c00d06110412001e441103a84440c840c01c54a030030345803098080040085c62810310101c01c2519110241041001110203034010b0748000c00080700d104900003c0d514400600040d217141e1038980000c1070440710056015214507480e1001040700c41c0c2d141c428101c4019520404000a003000c0300040c4803848107210300103146840344440300500c2131a00444103080044c800b10b004401042c034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 910886366 1250 910885116 910885133
    0x3030e0a0c030b09120f0c190807030f030510050105160b0a06080f0f030307032f04140409030e01050901020c040218090c0a090e130f0b012d05060a03090203030304 72
    0x1c507040c0c100f80010507030b020344c0012502e45d5000d42d11407150030184807011900c5550001070418540b442003400094900795010b40044510380038a2065640e0310711404d01030079000750300b14400300301031134501089400400304440200b910000d18200e50b842c0d042c600700d020805180ca80103455078100c0400c2c0008165a68000c608031001801910007100c0e1030b0041a88130b026800a203c400e8104200041c8000d101ea4061115280f142810008504050144072204580d401e0561098030380050140154040801c0c10619040219018400c0301d4403513130001c0603d01e4104001c0d041c8100820b404a49a000348001421901c02038411500c4455140d40300002c92030301c030606405641c554010802c03c1d0401000c0b1004d901407900c407442c0345890316605030b10b01c3c8002807004400c50000c0e0484000100c8410041c2c00c268041d6424014035410200324059852158401010402e10f030182500321001c051040021900100c1d140d584030052424194003a0482d400029810300000082000f00300149 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 910887616 1250 910886366 910886369
    0x1116030c060e090c0f04030c0303050a021e0a030c170c0c0f27040218041214090114030a060f0803220e061c02040e0109050f070f1203030e0a0c 63
    0x355041608540d0310074065a03020703181e190442d00440e84400055150032407800070020407061105079894aa034a03258100d0301d04a0b0741040f0b00280340000e19a00b05903040006110606001204402a00d180311032540d80341d20300c4000405214000b14150180500c4003010114334142e251a02d0b40c50083c0c01000381c07100c80000440740b1681070340c0700041060421100306031819071088030441e5404a0700368241300429005000301e030b1010f0b040380c15400e8070080064050065104940740d142c1d00146038001b4203c208030b005040c4090009101d841d180e42e030701003c1c0b050803164070070740d6071756a4844503041400340580c0c0d0002801620400340010300381c54004000d00d040c4c00f03c00b110031200b0b4072144110200c001e485c0716138052000c1000210303425140030030a10020600c84001907510310f415074042400e640e14040c04c0e1001d40d540303040c07000c2886014404540647d020300098014a0f0170003080c85901701050103405404080b510180c001c0500941c0040c101070a80400c0700e0710780000307140446983c04203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 910888866 1250 910887616 910887623
    0x1050c040801061e0b2b0e0c040b06030a0902010311030429190509100e060a0c0804200307081f0e2b0c060609050403020c0d050a030f111603 62
    0x203222001a01040101c004c0054a10703c500c0305070b10f0f03890f00941c0c00d9550452000c007411100ca894800689913544008020440a651004911401451075440c109589450218000d500f006102c08a0340c1d40d500459138001044080005e111826000490042241e80354007000c842c400000d1005120141c10f00046402141d030040c1c0d81c002602144c8404144242c42e01801c503c18500d208891800941182c0e0303100540c3c01c00c07144070813503a40e40131068442c8189451341c541c00c608240300e0465200c2c052034110074118102407143d403c190f80c402e258a850207030700000d20b0305000d840508075601400307480c0003000300c0021a4610800920440d81003444c03211045180d07442c15200041a110204807002c1184031042903101d2850f00343c182000035250f10034440e041080079401da20000302e40d4400e90000d0500d11600050600d00343c0ba001e40350030340d04545648100c1c00403024000040001824000b10350b41803030031014692103c1e20580358000d40720350350f9055000700d03040c89441c1418015000c048030300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 910890116 1250 910888866 910888871
    0x3010305250b0307030903051c0b01020c01020d08040b150904060b0301150815060402190513050d080a110123041506060207050f030a0b09071406030f01060309020d0501050c040801 79
    0x108440507091440c020310501d00001014000554000d010303900280086000c2c0c14030340c0c5410841c40c00b490b2204054094140d00035540c0c5800c1c0c40799681000101020300080c0000d101002c00d581024015402c02800101000b4070300c0005425007202280b40c0140700d10103001c800301d41c101032a14402030b0240d040b0540c003a6190855551952010040781001c441401001d480e203000b40c84e50110710b400c40100f000303400039000c00400d0809045030b00e090600c84003681d56203413a511074441c81d55000b0900c3d0700880c840c001d9940c0c02d401049042c011204101160b040030104405000c4086000d80301440c00b180b500d00c031080d46800c140100c040c0b82481a44105159000c1110722070102c0115105400b640c0c2c0140c0c031624007441181450314540c500304800404880d0306002d00c2d994841110f00441d0620800d4016440c200403403c60342902984c1e0b64001c032103d50861420328149540444c0502c101c0e0101619120380c1d0055445070007810b02103540180013408039107007a07002240340c0e074054490400b0642c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 910891366 1250 910890116 910890163
    0x1110d050c030c1902250f050406031a0a0f0f09031707053004230c010f12090b0a0b1203130303140c03130329072303010305 55
    0x1c80080700e00c00d11034000c4a5060052104c83e100c40c20358100007003410f5100d140c0f5800c040c845c824600725040604444104072260a05620340705e85c0c0c86a5220b070380102d04140041c00081d8000030700f02200b500e010300040c46030b80c03500d00200280c1144141140303104d1601d091182401a560070641e091406038454801203103000c034420b1030703030181103034450000341d401c1c455040d030f001415003d4200200c8150f030308421840d440000c00320310300b82920101d03510b00c01f8922a01241e120904100c0c21041800d001e0401140540006442d1186180307012040080811003005000031030303440003c419400023490080c91801c0c45c026401043c0645510f48150003090b444081070000204a9284c9048881c0c600d610500e59603040c1c0300400b00101c1061903240600c40d2090380d98040000d03113427903a0240301035840300d07240d0b040c2501d06110011800030f90144895030854459590311200c1d80014041c64288000c10013551035041c41e501520070b42440f044000000000d000001134000d00c0700050100921142 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 910892616 1250 910891366 910891381
    0x170109201303021f090b0903030403060e06010e010806041a061f0e01080c160209041103060703150501050a270f2601090b0a0b0406050904080a0f021902130204050301110d05 76
    0x1d10361080c11300c0c00100f0303140007404141c0103d00942034a1101500312400c00f40c503513035072000b9550140662156580290b004100c119900b055650050401c40003605141c1890344410f02e01801d168141984003489001188494580c008603850f52507070828100e448c1e84503a5402030400910140381c900055000d000300e8038601c04042114030341000481c00d5020b1000c03590a0110300c02004001b540e0425544907500306545040c04241c0c480c01a40d640001c1c0740e952411031100c503034480c1d04150b040107003c1c030255136815080f02c0c000044040c1841200240c50040d00b203003c11a501c0e0b0001406000e4200e030010f60401c4400200c20114400351400150803640c2c82e24074203d0b01c10703200140c6143c44210105401c405960301400d200c0c00058400700c0c042c0c1d142c0001c00c2d45000c00340c4085400200004105403840c0d80700e0010114201c0710310140c03081d0720100110300022410b000001e8461052034003030b424003000c554111002408050300a206a0440ca5009100b81d04804807140e0386900b8400002c424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 910893866 1250 910892616 910892659
    0xa180e180f07080c0d2918030f07020d050c120115050d03050a0513030209010f090c0c3f030501032015031f08010506030d17010920130302 61
    0x39501500e004000b036408400030000c100c459410152684c8030800843c1100165201c98007001a900c004100000e04005e00c1180c1c480c050000860b2507500103001c809d40a40e100402c950a958040b10680352035900c81c00e12030305002e0030304200c90341f1044002809404200640103001003003201011004840c0c0e403042805050523941400900264042103908030310360246c8080c08a2400c0c1051140c4003580320f42c0412a00310382a005103c500c40f90060030050001c0c00c0c0582210040e03145400180302500d5a100c0f6030001040d410078010309440ca0721601c80c1e48021010402800e0016081442540c00c844040c000705001e010030317240301c0c0380c5540350584202d010f03188005100018122440f609079028410f00f803508090a4503868400d500d41c1d040c640710805200c2406469150000030f190f04068081510341200e100044040c801c4445001e81045400c00c2c01c2c50444e050b4040c040350384480c00b22001e41c8540740c0c880a200c42e1002003001d003815402140760201f034a10035240d0940d16002116800386 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 910895116 1250 910893866 910893869
    0x10060e0a08120a0c1a0f070c0b06010e040209041404050f030310061b0503030403120605030c1f0c02090f07030f0522060b210705040e030a180e180f07 66
    0xc05a010b07101c1003a2980032403004000741e48541c03408003807154666039a440340c1240c041300c003410341001c1c0c0140810002c4000e4020303084095414050203444403a5641405c0c00801402c40d030500100c8000c81c0d2072070300c40350101c41c480d06005204015130783e61800c401e030303500c1001c0e6400d40742481495142000e200d80001140c0c090303041ca80a030100c803443c0003421189406000340c3d201c03428540f40c41100000d14100040d600807403103501d5805d40400030750074840440c0c00310380c0060300c207603c0200d000d0391540301c8e032054080c1d0456604031007200d0b01a40100b50707201c42450b00001d400414001c03c00440c004414140c900036060b65801f07101d600c0b2501d80d01400d645050341c0407421130440007451104005618802d10400b4030a520102e200202200040d00b5511919900d0301a4002e18403448074078601030004402400d4112420000e0b50181c90035240d483c001e0740410800d00c0500f03203180d034413984260721a100400c42d41484200e2813070090307c640c801d0301e44004180302d140309803055000c039000301090000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 910896366 1250 910895116 910895129
    0x70201090803011e0f0b0c060c040513020304060207020a0b0a0f0e1503040201140307050a18060219110319110103090b0c1b070b0403120e0f1509040510060e0a 70
    0x900750303424805210710380303a040d40b00c81071154064071000640030145580034008091486c01c044e284d810500c0e000341442030040600121140c1084280400d50720643d8032243c1c1d84c100c0800580f0707941e440c0350a400034400e40b20007030b40c0064410341c000303a1400c00400a01c0025242e0345c1e0510380000381c90041d01e600742c0d581070040c1e00c82c141d020300c040d2845400c0003655110f80140341035000d156607005079503050b510665030f4100085000a4800e40c0c030b80c00402501041d5803a01140c0c2c1e40d1481c01030700035219001e41c2d19106140c0420100b000034800c040c00050301c00701004003601c503c4220404075040611584100b2182c08203e00071500c000e42c000c1c0b0030f00e202590851751943c020794401c03200d040300d540140052581656124072140505008018a00203400391880c003695031420741c1040b2000d411720740511c4007001841302c070300c1c40c0940780c032014881d00d04c800b555120360050303d1428580c4c55000d030501c00c540007490f010401c440240b0070040da608907456030701ca90f41241e000f5420302c10b00e400710f0701508 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 910897616 1250 910896366 910896383
    0x4090b1f0f03080c0c0a0806060a0b04030c0504021b030307080f1609050f030a0c1502060f071e0c0f0c090e0712020f0406050d14100902130e250e07020109 68
    0x2003020528001c01800888072000a640b8107002c0280011a0080d80c0d1f04a480d0300d5000208004180c00c1000d8243e01420051100b07a040514580e6500210307907aa0040740d00a0f500410b0041c103603901d01540002a1580b401500c1d280d151003540280184000c580d18a28003100d403010a07010342d40c944d429007052540f40d41d1401d0144c100070900c6141c01240312010380600c29a4144004990360405040141c070500c0c03103590801c88840002894405c01070710411402c021074041c000030a801004036140e551110202c1c9405c80c5000c4810340702c04510000103825025101c141c4000c004c1554034a4069600303c0a0800441104c56001a44d0f9000e60090403c4254001d0119000d0300c0d00710601040f466004001003801e64071080496081e000c0420211440200c810b2525a042401c0c401540d021076400303c208400190307034001400c00400b801c002130b502503441c2c5800c0280c0d80240080804030031208102c52042c01105200c50301070465210710540c0d0541c1002182c8428818040c030313240340e500860705 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 910898866 1250 910897616 910897619
    0xb060a0804020112020f04050f060a020a0f061e021c06060f080c07080f13060c02090a090611040f03020f0f09222f01230a03020904090b1f0f 62
    0x380d03101500a0000e0b41800f1070039103982e2001259000410300e00801030000c0e80c82d58608010b201160100c0e4484070312401040c042000e181d82e0006915444030b401110865409004c0d050200050015003095400903260710051501c1d1401030b001000111100c41c407040c1c1d68456144110110741e41c6006000c0000e000c0c0e101d008130b00d84102007940d007141000302103901c3d0080a0b520140503070312030621500700000204078580e01c6414844900e0003090503080c0102c004c04194000b400c581d00040500c403500b0b9403000d0386821300140b0b6101d203030b41805a6140507640c4d52540030240c0040c1705440300703e11a140c9255121018200509803640440e00900082c80036110811a2081004070703000c0020b8524800c8120f2001c21810100703c0c4400d4201030303c46035002001c004803076417600300c45801814000c65508280000401d07031503817540000e20059071500d0742040801100039101d819900303540f05048c400c080c0c003803010031400140198000144002f501c200c4a40d07903a40003c0c9071140e42c0420380c80c2c810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910900116 1250 910898866 910898887
    0x70b090c12061810050717011202090f07020f0706113009180403080f0a0227150c0f0601120f060b13050a061503090809100207030c0612050a0b06 64
    0x203205008641001c04e952250b691241d841e4100c82084071840c0c00180b90609410a0301099a41c036809010001d000c04104515a00401c40e03101002d4000c40c40c0c0c001060000b41414428050910b040c3c0143d402c0c1c8000a5071188010024049aa000c0200b03001e07402c40a4404501d8075441401d488051201460b8107294441c0450a50043d01812382c00c01d9464450710390402c0138a075040d01c900d20980b550b9405003000e00580343d4401000b403100113031920410025040c800000b4440306040d065000013481010f506c008604020000280c1002e00340b000300d605100c9850104000442c0700c04441251f11036030384c8003840c210500446601404840140300301d2004106c80d83c1000c081d1000c0640b040d2000980504614200c5200329001d81e02e4554920060107440304045030072011464919040c4207500300b50300d60300f56907caa684401d2250003901d0321048824000d112a60003190817400e00c0790703030a64808014000c020843d409038030052410300002d889040d944034655440b0009009135007000b86e4440d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910901366 1250 910900116 910900141
    0x2010c30030b1e01021c0f0e010311070b041e0b0906061f0507170f0d1518020304020a0302030a12020d0816050c1c0e030127020d08070602070b090c1206 67
    0x40c03d441c114000c52044441326400d010f9803180c00e500a40c0e403a101c0071001c4c032005200700780b0b4040c1d2504040c02c0c070300c2c21100840c0c100140d489807070304204055555192894105100210380145151041c10707903a5041c240b00000380c0451142484d2003c0d100c3c90390718501003020103004130101802144110802180c4984508082c01e40d56210f80b808a900c0c4241f42c02d4103409411072044030008102c00610100701c1002c1e402010381c1a00d0b0304603003106960400e40301e00e40504072100d4840c05550302200260a6540e0100b07607200464000c3d040d1407a00720700e0305007840919030a80810000d4030076441105103140c031480e0000d100341400e600645035a030201c2d10880c1d850340044043c044034413507441443c0c0da002e2003903480201c03840c0d580c9465807042000340070700d420f40c0c440d85c2071f9800740040d500d00c1c0c15010300e420511044482d4102c3d00c0103811100d03031419203d00d015800e0060512071012519004219400d0304041c051545e28080b0342c05158410100009a0524604080960050008200700d400072a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910902616 1250 910901366 910901419
    0x62001020703091a0409091101230a0e01140f1b03040501050307051b1006060e030601050a0302040c02072c06030f1507090302130609060501020d020a080702010c30030b 74
    0x1c91362415a4403212a001e07218402d00c1550040082000c070b000a60f04039299002c0c0f41b41b00c02045440090720035454449001c0d94050700d0502005d089071800c1030703201e42d40c60300b03400030362000d8943ca84824000002e040c3d00448041e03540d21a0305940c2486040b4008155411a20140c1d549455607551200484842d04880400c0e805600e01c0b9181d90411642070016280d8080c60000000390a49081802403810702d200c0345090084d00309100601054807003110003000d50340c0644000c110810100c108071f1418607a40e103c910110940004e500041c1c0c408120500007048080e812036582e181d0604151b203c14043c0a6840180d00441a0300c17403d8480003142980301506060102c41d0341d41c1c0c3d030003081c101c2e40c40f000303204a1180d50b03141c00e2003002c1e01840703030700040c203005c0c1300528260b911440c01035510300e91440082c10443d00410020116071060b5020a4481e601c1542000802510580c0071040076498070329404100703081131400503140c0309109003130000800901c42e10051001140c890101c2c0581c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910903866 1250 910902616 910902659
    0x41a07171204170409290f0102061b0f0406090303020c042306280e0c0304030818010b04020d0c020105180309130b090f0f0c03040308220c06200102070309 68
    0x510001800c4400c2d4410041c0c0600c8500011b0340045040c0d802c1014101d1b10f40100e0b1103501616010140740c2d0780001d080c1e60010080c0b0044002858404c0303002c189006800040022010002d004104582d1003946501180d00c40d800729844510100200000d8902e44c10f203010b400025025551290000d0207481c98000070050f0025244200d00401c01e6814400747d10300f000e40c25000e034000c000003010030075469488603d0503000f07810f43c00e00c0e54006012010283c0600c0c0001c8540d00c42c8055441d0a50080c500031100400071541c0f0300d840c0d002d44001e4100700c1c00450140d4a003000042d12032007040c0d1a01008a040c2c2c01031031030b092103801040105100006000300190f560060303403803a03840b01c1607000e000b078421040440062400d10054510031030014128090244180244400650000001034008a1030b008100004240c00e1140d91000500c0d030002d007a0300595400000d010b80c0180f81003c8034051004164520824030a200303090b0312508500078005050b02c842004025404903c4184c03c044 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910905116 1250 910903866 910903913
    0x40c09110a080a1d160f0503060c0a08090106080607032c100f060e040b0609240126040b012315030c07060606020714030f21041a07171204 61
    0x20240034051402c400b15185c80300f104103484c400e0140d22803041407540107041c110010b182034074061f641f000700c0b4050102c0707041c10300c03a0341004140c19810030741104000e1b0421a0842c0d02c140b074041c0c4002c02501c8607100019406040c0c00c0da04401c15094408001e980703102000803c800c1620b003070100c00400710700443d03440080c1c3d100e00c0800d1081400f101a8041c83c000d201b000740d2070400307404100484101900030903040c031880050601e03d40904403809400700b02400c0148507044d014001401d0704510f500300c007201c0321109040200b0401c0c1007004905a420b81014500340042c080415040c95208980300c3c0e511141103806103a03400303501c400542d0700c2042440290700340426581d841c415107159401c40310150700015824001c0e4940b003404501030240840060043c03103204188140c60f1925402c40c0186e151880e2540302d108600141250002d0240030b0001c0f8010100d03042c2004039030480076003158000e1562144403148031030f5000341c4449105000d19204161500c0d540c030000002c0342c515030841c010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910906366 1250 910905116 910905161
    0x27010903150e0709200a080c0a0306150f02010e030705150702070515030403081b0d0e120c0f10151404060e0f06150f0d0b0315040c09110a080a 63
    0x100501801001380074103074003c9480c0924503008150107040c0e810b0810f5629050100c07855180c4d00031900c40c1c0082a00f031314143d540b40320080460161425410040c121155040300190040d80042c0d00000e40099038020801c409400804588a00c114800038000e81d00c10b000404040c0030b510402c0303030005c26500403a0f008985ea000458817224020599480e03100300801000f00b0301d600f1a01e0b2a60210b0070300041c040c1c0c05a86403d5030411300640d00c110103181d80d03c04169242e0102008903405e40000c0000c602c0e200d240704050541d40d240380e0307030311104e140c01404514082400309024900039000d2400d503184030941000706043c00741c2d03c00808103900540b1482c00081d0101021202d0780507886001c10795129141101c04d000c040b15907204401c80c2e2a1041050854850908003070720010341480002081072505840003c0c80d040c003240c00303144841201c0003400b042200030030703c5904032403e508052102071080c0305c0c848242d00840e1249004031722090005211040141e01240c01c810010082c4491302 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910907616 1250 910906366 910906391
    0xa02030f1b0706020d03140402010c3f09080c1008090709050f0105010f0215070e0105070203010c08061509010f05031f08011e020301120807150c0201022701090315 72
    0x40072940c00740c40943c100f4120f245c81240c0c140140e108110411032141502d0401d940003c0124000801c0035000c81032104031a071885200400d0b1004001030150341504c9402420b003040ca0074a29421004040341c580c40d0000358191010820740d80070340c0000c01032008412420320a076542e2800a0400c0385602030a040030a04518605c2541c2c011441e400c107004a0b9070614001600c84c46500070840250342c00008001d040d262001c070f0b82c5034070801c01d15160604104d104010307500c0d4050600c00a6065017440c4103080a180e000b105544943d5044500c1d000d294941c80100c942071040008031070005000c00400310b049801040155044205210b1041c0704428184140043c02a0381e000021326944810100109150318080c21101c0d601080c0c0c11495540740810303140a070090060300800d445400b094410074000165403044c081c581c072900511403901d2211009000758440914620034050110100c01d130142c0d8210414090030303041c0c40704510203040d501c400c088031340c0d280380b03545001e03854070004040ea = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910908866 1250 910907616 910907623
    0x2010512041118240301330e09070311130c09050907020f07050d030302161209150804111309080d2a0f0203040302041a040605060a02030f1b 62
    0x56020703a01d00801d039100c51080101c07050140c1d0380140d1124401040c0f011031041e0001040e070071107131107030740b02403c425400100b0702505000402c48640e410741101c01c218140d441040b540034010240038001e05903111000c00300c0900007619404416405248103000048010303502c08da01c1000200f6502c1d080034250000ca0a8410810300880000d202010030402400c06503030041e0400320328006044005141504556202124403805101b9410362801a050500076030440c0c2c2c401c0610075510200e90100e0030807038030048401f52a071001800c140c00000c0c1002003130b4005c2d880070102e96280c90302501ca94503006000e00045074980c3c0d203d40d8281c005040715525200342185188502110b6031181000440c0100701c44001d09150110102d881c8130410a5410012541d2900da10f403c20501c00308195600728614042c43d00002d4200e807408042484880b80303e8043c540f80d0070112400d0204680f40d03000d002c42e60048810480240e84140100403000c00f4003030103460b04147d44c2514403000030660400516 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910910116 1250 910908866 910908871
    0x611030a0b0102100e0a06090212010e06160905010e060a090b04080f0105100e0c0304031112030a0c09050a06030e011506030c020f0d0c0b1503010f06230901050d02010512 75
    0x240c569030703154454000d58044c000e031800c0d80c42d001c004000000424500903103075030308080010507069448403013204540c0e9007590a036038200d40c0e02c020044680c01c5480b4a0741c1e410143c900c2c440c00310f410540c0400705481503104030282c443c1a5981d26403042e1610a100054002c8003140b803e0004204011078041d0200d0042c1000381a480300078046580c0d04411642180e0000c5c011114810b6005010700540b0029914036800c444440039071030b6642e03150705044991180d001c4882070380d8020b40c0098104151404040c40c080e0b0701401041055164400302a030b5007440600c501500502000420008503000b94000115080c0301000481e5104000904403099162500f003000860303a55040c0020080d41080304980b0100214000c0c030344628199800f07010b58060740b01c01010074065000043c3c07055966000154030f001e01400034400e06542894030360162540340903107000519802c0b940420314520b030307503e40f03410034000c1e0915109074240001d001c002540c03481d0603818000208880044c582d0b5a450461 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910911366 1250 910910116 910910131
    0x605091f0503060a09140408030c130e0412030e0c01110712061d070b042106180b360a05070f05041811121618050c030108030f07061103 60
    0x2e0380ca103802001c118141680740c00c00c0390410314100200403070202e4200c05607000707500012251346075543e085010805110b030100c100d4101904100004000105c0b03031082e8041e600c81c840440045100c010100c04403444042400e903507510449112840713501a9010030f400003407030800d80310015250701e071207400c3c2d000026003100c2c215a180c1c402c0c4190020401c2075000f0034000405407042a1400c050790856015900034441c007506110070030219254840180a503895105005002e613030061422020940308915041d10404d03403c400085d0200b03407414200340422024210380340000c002e000501d1042008030b020382080c1c45440100e0b00070903030400c150f070000c001c0584403503100d03400c00c0144015a011144212076400e000e01c504400182c0e601121189d0501c1559503141e000e80300c0c403400b4905224024900020426820b011440c41002a5034003d188030900c0d051069480310007081450b4070092140b603d882d04103100c075590000744c820040c4071040c060503000c201c054465407500240d510a46484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910912616 1250 910911366 910911377
    0xc01110a0c1103071e050f0d0f030f0314011205010c050c0a0b0a062d2102060d0b06190216050303040b0a0909020f070b132102150711070b03060a0605091f 68
    0x1000940340c464809011f0306c00643e100d03030400c426a51015404508a10001c092000ba40c0400900d248213138400c016102c8000000c242d556500e00801e803031445140c0c07066500703500300ba2580302c8540c09030084aa500301207000808800300c0c19110804115030142083d00440c3e2501310006141840c2d01c0071a0910003080000381c12500c11120480d420711a0764003517000c071407070320500c4015070303902c40031180c082034040c0c4a0664407205088020010240d180d0000e61041c8003091402d038400c80803034051128521602140c043c059840c08040d1b03800c0c0d0601c00c0310f030700d82c2c01000140528456203000d802640240d05004940382d07110302113407059030011801c01380c03107102c0400d400061025241c001d5070028032250052010040b15224200c000394045000e2001c109800003503461140700300404400f1840001e528100c40c24072060003015920000800c1d4528460800701043e8900b240e0112070260070001c0008107490315100080c0c4049d040854129408038401e140505070303210070540c00c50494660ba4a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910913866 1250 910912616 910912619
    0x7140c1b03101a0909150115110303040503030402060906070606060203130618270504140105090d050706230a140c070839030c01110a0c1103071e 64
    0x1894030b400c4201c2a1011140e05022007203400000414454503e20025510054569155003855240c0b0003212a0030f00302440002c00042d071040040c004424000c2243d8414200c3c0700d00d1500319651380020740380070b401c940007000400d0052802a0007002250310203041c1d5401c041072502d9501c00c46200ea03124a016800000d0b07002c000721100264007001d000316090003140d0001c03040c0301101c0b03035205008411200d803100210413070b002c4c000c8240041202030388200348a0b500e0039281c41e00c04c0d40403a200c1c40b0503640c2003102241031302001050340d121011896841b83c1c01c041362501c4803030142003622161840c08030410501c9101003a00a03145114103242c0b0804100080344144c0b90101c01d000a0441748090414000200060450800c5034203651510425041d014071410482d015022624041e100c4100035038210444820007001600b1415411070003040310f00c007482d400c2c3c401403165101301400580b0942c5c1c89000919408900b240c40c40b006404c0360842c5403103c00d41002d000054030300b2104c1c00f070b00240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910915116 1250 910913866 910913869
    0x21c0303050a06031110020106090606110c09130b0c130e0f090c030c04022503021605030d122c030909010f05060f160c030c050319080307140c1b 64
    0x2a9a4008142800401c0794600d135031100143c40040591952103030510300c00d0704006174130035041000070b001c0a08040203191341c0d0324005404034903011032101650207052000d826929124000504c034000c0151815002140c6075146040c00000400d0300444890034461a01c4801900c60b44001802c1c801d11000d28601300502c0040804d00010700e8054aa400f0850080c0f0030f440100f541d0319501c0080d10090303154130050200300f00710302c44004090341d420400c007140000d0640c0041d500e010390b45842d51926105486605164031001008010000300d00c0600301d1108103299540100241ca0320030140380d00c01070103c0b1042803ca000d41015240591001c14545000d00d010f040c0540141189010f001c51a80b034040860030a0041200190903020007245907864000d900c2911000b09a000ea640a90309032645460560302c0442d00409000740b061031010130392480c07101c80410420303420045e194215a908403049880502c2013100c04403c40c1d00307200760410045d0801c01e21208001c0b00002c0c1d426402442c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910916366 1250 910915116 910915121
    0xd020705120d0510030302071e090c0e0a1d0105060d18060b03010606090e0f06030f03070f060609150306020d1e0501030308130f022e0905031207050c0409030c021c0303 74
    0x84c1004140c00440e0001c0001903000a00d00007111521150704c202c1107014148030388144465841388154508218000d03000c01d130711007289100031008035000100283c55403030b0701038a0f130024204440145c0540d4014820380c68014054600c914040d00d0110781140d12040c000840d8a0018044407410f803641d4001c0618076082c05114007401301c45ca008004185881c52107140c41d540a00a208503004040c082012910148803040038440c403442201d5440d01d851518008991074400c0075a1358501d0300e4004111900c1d84e0155031035551084410039400c0c1d0941e1a810001e40c0900600c80313080b030b03032044154541518011200c20078580d1000004141d03256007030140003800e00034041303483d81c4107110140000503107210707580425a4050781c11032904501c80c08910500302c40c600d018442c010b04024021303a1f8660203540c507400e59070150280d0320420000740346c40c4298007803100d0040c00c980051100d00791a0509502c03080380c4500034030703201c1512009600850070155206030781c080f80f0004103011606054250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910917616 1250 910916366 910916371
    0xc0806040b060a020a110d05150a180206072a03050c03060708060105250206030405012003060303040e0a1b020303070e09011401050c011410031a010605030105060d020705120d05 78
    0x2d9400707501e0212071440094440d486800020500b1424089180c225210300c003040c10f61982c448220344060341c44448200681c10101c0e80c43c0c1000e400d01040c006144548816084400d602809071810064280c1d03c0011000e8142174035894001c0024860455607505444000154001e130041d2400d005503000303140c00e200300204540c060100940134859181d9101003280d01207000ca842c1c0c1407142040c11401078055150360400795101c000442030005012066000c50040da6003004114042e2251400d681e0a40c0021035038658990001e11080000502011009520060819002410313070f10401c0407031884141d05280c1c0340107a001000308094540c00810b286001003084a4142c11907242007030b00351031900030701180b504000020800e041440d2094106400101c3c00f11a40e140c6450222880161001207100544081000801040c5400680e400060680e110303641c5503072031a82040c043c40919800001d0ba04085075080002c3d80228105210340300260181044083c0e0352011050391380c0595001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910918866 1250 910917616 910917619
    0x1030b1f022401180e0d030b030c0d020616061b02010c02070603020304120c11151908060d03270602030d0b0103020903070924081507110606060313060c0806040b 71
    0x901551141e0405032002c0b141150810010202600b5880a0704000740041c031300640200d208a5150021068050300080b4000e84c0c1a011954403003089010012503111501010350007034001c0081700c480c2e10b0001e525920b10b501500000c40c0d0041103d44806144281d03080f40310060f503403a1b51100d010b80c1c0c103014040051407585800e40c10f6040a13242c600c0071982c2c50304c00701c0900c00510703000401c02c0119101070080c1c4c0c500400c2d44d20031443d48202482660302c00500c10203240c009042c0d0046040c05013605e54060707040a461441c80070030341c1d42d041d00c3c006400003008580c03400b002200c40c5024041e0250f41c0180c081a40955280e200e80c0d503456050b14060640b00781070500502c0000d425843c006040c40407280c0b110320205050b82c03d04002d0b0030303241886205803002882c4d8600807030746c1031000a0180345003130074211060f420764a08204171603115180300c00d001d030f80d000040480c01510300100515040103250f0141404071125565450403a066141404081284a0b041043c907140c984640080540e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910920116 1250 910918866 910918903
    0x6020307031b080c1c18060507050f030a2a020c011b0b07030b040b060d140106210c0e090f071211040513020d02070b0103140a2001030b1f02 62
    0x342102c060000c0da0020705004a105000ca017008408095412035004c000c21001d0801415003030400d04106440c2404040e83d4103810301c0f000c42d0307080d44284100e94101070b040e40300e2810342d140c03124008040c10300c0da920040031303204012a110050500c1d02030511041100c5d0018503018070880d00140c040b140c01c0030b40c2100b90030480c00c2240070514650320745a01401d50f1600064211704034002174000e100c0c14982d03582140c1c000ca00c5000701300700c03988600c807030000010041155071307610707041180c0041c2c80240d44440a00b41c3e4155950054507508034080403400c0d03060808a0f45021804200c810400300c5400100040c2e03c81030144a9404c00011502c105524100340048000144401010300c1188581809000d11400c1291301b2103855068070405011103106558900361810030000d81031081c0410750300c0006d244c90811088100180484035540c0c0007101c04140c0003c031103116001c110741400581452f8642d40703200025039841e807030308220381005180e52480540981d0024640a4160f441002611 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910921366 1250 910920116 910920161
    0x2190c05060708060f090a09120c0b1617040809130219020a1e111e0a0801020406080c09040f09031d0603040c1509170309100305190e070b04030602030703 68
    0x121744402d202c0c08960280ca03142015103c83c3e801c0750040880754000f402a9805490944103640d00c111004015030003941d01c040309840b0b015014100d80080c12a02c4046510001502da600060040d042c1c2d00c98098044242081c0038000404d03092101050400311039a400035440020301e00a1261510f00011032005026103802d556a00c4001e4000103105886100c15450510800c012a40d020070208070140c030340340b01c100055000720840e0000c80c10883c85180381001c00b01c0c47d542c2c141700b610304651041c3e450414645901c1d50f4941d1581c13143c0d04082e00035883d6280764550714441d020b036002c403510036500e50800c09940400a402c0c1a24400c00700c1c071170a000c0051002050709034508030107803aa8071400c0c10714214148402d90712003016a01054540e4005145c141400c01c006c40940600d0700b0985641c1ca04c5040e44400310100c1d0800c944e196881050341206070000c910640c0065031114807241103440c1a51a4072031240c09400c207510448910303400008000b100381c2e150256a007441d81c0003c8080e01103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910922616 1250 910921366 910921369
    0x327020d021201060902070c05030706081030050610050402072d050f010614040915091b0803091305040201021506040f05040803040c320402190c0506070806 69
    0x99800680c081e106074049881d444051800f940300c10010405a14215965852890225404a024418948680120580090946e02031803443d8820302c038282413282c5050820761855401076103520700c1c8009007400ca0348840301d407800001d1104524020001482c491404181504030701e00315402c881d00407401070115000142180c0a00700421003611048520311000d01c3e00e00d0700780d48007003501070182c0c4100c0201d50140344c0103501c45400c0d6202c111610140f00f41040910040d950304200050440c080021400e031500c4241e403196200d584145000d5030b41e01c1c0403100c2c000c06c0040903001002d254100044d0070b0f100385031004031080e8910400c4401d121134034060300041c0d03c8085044201c0101210f28000580741d40c0c5503884200c00a11031340b0108980e0400307007003000454104640c1266010000d000225075038001908204440c1e194411001c0b280441401c503c0c04071403c40c0d4020341140d001c0c0401030f80c00b2200c2d201c0015005240d0740700701b140f402c039060440c03515070058000804e02c0052010711030207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910923866 1250 910922616 910922629
    0x70e010518060708030f0703050105030102090a05010e01090810022a030412150207080702101e2003190f05040b18030307021e03101a010f02031603032702 68
    0x3030040300710241040d45024404200719204140c40100300d400000100b0514105100c440c2c1c1c0214086c0da020480d9a894105150803071113603d50a59014440134400c020641c0f0071200e4103824030040c941309408543d03c020030b03443c09412000c24003000703070003041158102c0500b0b40050741c43c403206003003140d10f00c45400002c0d460303201d0b03400380c600c41d015002d090005001214805001a40703009400b1075640a5509200740307103030480c0750200c0c4520300400381664030301d115aa00998003409404e40c010840740c00c1d0015140c017018405805c9150030410f55241070b844c4240098400312031a0089100308400300c1c007005115808450300c0d142488002e100c1030002410400988540e401c1c0c0c840c44980c48588a40003c1c514040c50300000e500020204c0900725442c1d420524100c10b40b41541250480c0e03842c00c40007001d9488001e0225442d0b2a603801c01400d56118001c0000b00d60780354010389182201000e54221116222641030b00481e454003130f100928820890100349540011042c448505110390000d0324 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910925116 1250 910923866 910923877
    0x13090b100816050a031b080703030201060608280203070c06090c05030c120304090b010c0501020a02010b01140f0306091e090a0203120405060706150504061403070803040806071b0b040b0a05070e0105 87
    0x11000034203c500701c1285114061b83c01600c051801c444016550b46002800780401d40070704800602ca150204000709007102849c11540022244821840800d112000080d00010484020001d4075428000821110300c5007070136a0340181040f03030a540c140028540341c8508500303000d00039610440d0f9181c0f82c080200640f8151445800c01003202e00030040101c41102a114000e4100e510000341c050080e50154002d00c0d119600b0703250440802041441c4015501803400400401141000020220b181400b0416400526250402c540952041c000001b02c5000c90324100e040e0320842d102d03801c1d85403c0102610000d0650b01d03036407406040401003807036801166030040c180b07600c50814000710b120035544440649170140040159650302c09050316694500060180a8020213102007540c101c0072003120150f603000b0f00244850344804008070360700302548142d0700d2020a0f1155890009040c4126640518011484c03407100c2d0424511140031180042c0c100c00511900c0110303920070740d81003c1030300d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910926366 1250 910925116 910925123
    0x80a021512010e130812100b0f041206110a051b061510120e1006141c05010209130b03010c020d080117030c0d0504030b07090f030213090b100816050a03 67
    0x905841d0139050350031808241d1002440300d5004a010702e190040b04136010b1065254004e400480c96070707400302c0f020a03c50305145c0401100c3c00c01050200100784a61190113a1041c0780004203803018543c1c00605810900c409000100009900162420080e0407100580c1405001c0e000d01e007031007055207261010940c1198004c8410f0320301c0b9124640104030300049001c14400a10868030210030440d152003100d1035009006240c0714020070101e00c0c94030a0561510050b040710159406102c600308200d8000740110f0311590200450340c010f44803d041c041c0141010300340030444110072000c160075680c80001c60720465100304040f2200e681d2007150ba034116010300c4102005141411b410b141584541511801684200d89036407040301c1c1c0c4140100112405100701d0303401d07500c40d000c00315110042403066880550030030f02c0500151410220408480e980d0500004081c103081d681c8807282e0703000b00e4511030030703650742d00040140800602007541d07158100c0c051404414100000194903000e503001c090b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910927616 1250 910926366 910926389
    0x91a060a090c05160302210f030705070212031201031a04020d060b1305090a12090b09044107020a0b13031407081810020d12060f080a02151201 63
    0x6038a032a0043c011201e60b010395100c00118040f40b414003944d05c80040348280b901d81c900150310594502c0c11025541e001410380301c5680703180c0790110129140d400284083c0d9014207400d00d110441e000c104010250510038048410365036165041c00800ca42d4418041041380008408220041c1d842e94410300c0710310b6010b000003c03210354403000700b4001101583c1034180c0914001c00c1c091103c0c80000c1c110b4549109010b44a40ba00407038100306d4840d0514450312802d01001d004c0050300e4585034000103518102c542d01501e54030a1010442c001039040c030501d0418840098000c0c03914120701002591020150004010032901c95a034200241c8004180601030680c03088020201b40c03041c400d8681d54800035501c0b80c0c42b011141044a069404000188244111030f050801c15062400d002103003403180343c024022403103038ac00301512840021842400013503603448020444550340c40d041809410450b0040c0031400c2240b05003d02d03e034032091344500154040c4130384982c1441042407641545d100d41440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910928866 1250 910927616 910927631
    0x615070615051309020f0301060e0106110a0614092e020304050709050f09010501060315050d05010b1201020a1101090c0302120a060507080402010810060801210510091a060a09 77
    0x100d40150740d858200350b0703201c00360f03d5042003c420385401c40724016000310350035a1110031705402c0600700c40d2a0b208060400240c00010000b05009010045504031140240d4516072a103070346100846082d070342e0050500b0044010b01a601600300600414101e081566020500c400c04a0700c4a0b008604142480c00e0707000800901000010b00c900c2c2e00074041c07a80c0502540c204420b050300208002c4507817404540c40c141c00056894442d01a2034075840f50210806015401c0000b0f10030354005000041d07440c0d40d01d500c80c40c0100d80398070003c0c40d003215020000503160240000d00a0500400081e91a02603040c2000100070401550f03c060450b981280c00b01020302441c442c0c1400c0c09003104015000381c0c50103040001c0c070358010800703610481c400d98484115584101c80300b44d00c88118041d400c00200c0c2100140240d48520306407540800018400c1e01c081400c690316145803d0181101c1c0c202d030f86d1222500401c0255514050000f41d248c045620b079186404008030721016514403d0156080c0c40d02c88 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910930116 1250 910928866 910928891
    0xf11161e0614210a051816050f0102030724060602010501150507032a0627080d090503043807020f04022101060e0438180f06150706 58
    0x310851500e0f0145000c0075a1030640082030040001712001e006500c26100c6001c903900c004100910010340050180e00d40c00d05003001c0c0800c2c2c07103070038403c6030540c403017009080d01140440349540e40007940c0c00c3d05188a0080b840183c1c00f51040d540c03203e0706680c10500107200705249004400001003561030082c0d00d0b050603042c1150401144c00e001c40c00070885e00e42a01180280308182e12072035011386000d200d141e9800c03e101007249155920661801d2100b40c450000450580051100302017040000c2000e5086849450460380f003540401c44100b49803103035450b610200c1a20502c2840d20000321070114a1004d402140744c401c640b8028031549145130204200d0383e070759060b9202040442205605042c1084111089040031f00941000c20451301042070546401e014000041d02840b40c6503194051922402030100c109403550f00e0550300f500301100290310b0b8561101c0c1034a81110303140450b81040710302d81e9500c0c00c0103082e40d8040c405982c0d492551120f100203c0e061076a2003600040c08160400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910931366 1250 910930116 910930147
    0x21b06030c0403080c070620031b030d020f130909051c090e0c180402090d0f080702030313170a0b042013022115010f11161e0614 57
    0x80005214003008030780d0b80c0da21280090480103841f00c6417501c0714600d81e160742402500900e1038184030181e00c01c10025400c00804180300e4061240042140e080c8500d14004a0980c0c0240d4009150300c4404100181c2000d02d001102c4002d00a211040002192903201c50303132901045002ca40c07803849400c079170615103442560014000e00c00050b6403d901d00b000300d80c0b070860f64880c550401507121080b5401036945803d06c201e070006507000b011071801303804982c1c6149642d840c2c5601510404d6040c805540581c90600c011f1000034484171010501c0c90400c403804c41c00c488440040714450303003c801040c0000d102e4a41c07040c0c0003a003003006018070750b03034404400000c0d500f59035003260440010419031140c0607094010f015800b0321201a81030701907980a65900b4400210341031000c0a54100366131b541d55000d0041002610207501c3e04810284c03a04c3e01d40d515148213600180c201d80c04200c4100f001c0f944035103052021200094035100701500d0034070002c1030701351a081d62480d180d00004110342e00e1500305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910932616 1250 910931366 910931369
    0xa0e0904051c05190e030601060c020a0e010b07170408030f161b080d030e0a033551041a030105130b070c02040b2e021b06030c04 57
    0x1070046811400500000030804e400105030303c1d0381d8941041e40070700fa040c003c042280401c03001800a0075568a400802c5440d030070101001d98001e0070031743c4080b4260041604042c040d0411494155951800e4509038112050082001c0c2d1481d0003480144440400401100c0042c42040c09298462003606c0e4080403403084040028140312050b003503807031510740c90074101040724004000e807044481443c100f0b42c00e59091180e0036017940c002a03144000280070380c41c80d100c1441c06090460702030a9500c214003440342d07107140751000c11031000c041260304181e0070384485458031001003d88550180e07240103400b103c02c48070030910140324002880700c80ca56030726030000c00da40001c0042c001600c1003001900030004002e43e0074040d50810f0005055000100d041d60340c400e80c043e42000407966900c408031104614507000701e0b440394403014070a0841d40c4030321407000100c80141913002c13281140007020320b03090f0007907240308291b4025003075002d61800e150503c0d9100d200181c485664a60780e516a414807807259 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910933866 1250 910932616 910932643
    0xc180402030a09061a010c12030b060307020729120903091504080f0601080d03050c090618012a020616060e070806010f0e0703020703030b03010c12060504020a0e090405 74
    0x200c208401c100d041d400109050b4018a4100700708511445e018811852010b600e502044000c0c82060003d008500309044ca1f040c00c2c40c0004205401c1e100241c0c05910071744011005920810041c8106501410580141030500550081000300221602194060164921107680803207000611487c0144110741c2c012000428011413000d02141e2000c0030380003805070545a11420654134159500094880e061740d40b0b0070002e11140351884001c402612000301f0100200f881031102c5240350305c4013800b03044217241e0290b0116644600388001800300020105c140c4001800303a5902c0c100c03640140504405a070151482c4d03580c0c0401c001d0403040d40c402148001c101d2450801400184400800c400c819500c1b07007429529140d0382e403550408040d20380d005250555400c0000300f8201400b036401031110500c00d00300880d08542c000c4c006400c490380728a680010940307603541c0c4101d565242c481c0703101038607048130218102403403641d00801503003203175001328020038080c0c0c04201031000070002d80e1904c240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910935116 1250 910933866 910933871
    0xc04050112060b0a0302030c10030605130c0f090f0902070507051503180105060645100507050316020d14030403150207050a2315040201090f08060c1804 67
    0x2500c65485a080480d0780003510020300d898512015071511a1900381200e80080040868003400030401c1000c4612010a0042c144e0724180050340d519440c0c41000300c4d8800074130001d4000d1100030050910711410304540704211281c24140b00c80120005401d040c5c035828000107845501500d401450900300b40c10290b8800400c04c1040303004100e1800543c49040070a400c1449481142645801da034800d44030942d12103801e121341806a0058400c0026414000c001c111808100000803020001d1208a150095005a1510b209030400046945c81200a45015843c10341c281d00e0b40ca40760700855001d41114551750614000790b50743c0e0240301c48443e4004040e218180c1c00c0ea100f559481d07022b84811200300c0d9104006104405581c402d03a07003c503411070040c0c000b4200e940d640c60321010403040300140700d210901c00ca1b0000c0c41c040050700f0410384600100703e4182818000501948080d91000203041c0f5000d07000e202030318010071400c8c0c000465505054503144400080070380030100c4400a43c1052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910936366 1250 910935116 910935119
    0x27010507030f200309192901030c050f060712030b0108060a0602100e01060302100302030103020102010506010c020915011407060b03060f0702030409090302070b16110402031005010c0804030c030c091a0f010507050c040501 97
    0x13605524002c001c150241c0d1f2546040c00084441c004c0f41d009200141803503080120402c4035040c407800296451100500c0d1528120080d82c0718440090441d4040c1c001070b55940706000c0558110501a8004104513080642d0515050f002940c1d510f0b000b144050403510745420003403c0009412a602640d03004004040015580b00010001d400900c0b043c0e00560a00700484c000c0e50043c41910940e41e006841c054140d9103500144078046000c18a0b01d04001c608400b01416407441c00c060400c041c0f0801003c51480003c0e010145418400f90503444800e400c0380c10312070791580005c121000c8030710606c004035000c42c45080030307420819907a21000e40e1140000b4082c1001d9803a50300b8408603840340020101e642c4000041c8012400b00321030588891418110070700580d07002c0d40c040c6250364032601c0310a01d080c1c0c6940e07418180038282d9001321460b2031204400c2c01003a646009900d51404001009120314051000265440c1e81110b08141031045c0081c005041c010300b0321154801400c0035000780320310b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910937616 1250 910936366 910936373
    0xe0607111c030507050c010503130201210218040509010b030304061d03030403030e10140301060c02040f110a022a060903150108060603070b0301150827010507030f20030919 76
    0x140d004800417105401600da02189641c050b5040d2801041d020820342c060b03003c554015500e8061300c0c8418001c80b200081c03689043d00d1240014090043ca40c0c043c01d113400c2400080c442583c50140800c40f80d0b906040111400c0c0e03d00206540484d035152a089009800d001d00500f05407148002c2c8a0b01800005000300505030041d22003120060156881c0d40c02c0c0036280c10807103a00c2c058008a40401c58100010015244a03101184000c1d0000300b0000300d00b4282d0001074111810b4000509044101060035060f8540601007542c013814a0340d8500d10000505001c150804020400107104001c04240d070001601e041111140b41d1480d01c05000095071124640b5990324000c942d482d109208118021801031481c5040c2d0781203543c19642c1c0854412007980030713500b0340d100800002c8410161440882d0303149920721b2069401c03040d2000000c06040050000781540e00d8011000031007420a12114031000041c0e254050f60303007001d4807043d1030b6115208403d0409a24980401c40c816200c94000f050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910938866 1250 910937616 910937627
    0x150201020910020c010c201201090302070e0f0c030a140411120a080d051b030106081510050304321005010807080304090218220b010e0607111c03 64
    0x40303510403581c0225504503000b08a82c0ca4411154035800100e11032094000030f402c0c55041110480001001d0a0940c2a000804d00c082450b04c207003a242c2c3e440f2180001459010302c00b84018000204d402103151524464040f860103014100c03c402c07400000c001081070006134060101c0381c01c1e1181c00c1000341042d0610400e43c0500c034040b18407a024440021103c140000f83d0507402c5940640f510f8108205c14100344000c080c010001490600d0341130000345032552010095003e0710709901c4038090b5003801c17211300c2d0500840d13140301d42c041d0b0902451130075401e40001c203503503000382c5c0700c61070102e01041c038800b500c90300c000c003030001c4000e03400b00f100c4884004000c078100c10f00c8108200304001a80c4e9482c83d59558100034482c1400d640c00c200400c0c85844003135002013050080d01e003c40c0e90f540d815038001c0b4111403450300c003080307564400f20262540c0e9030b21800742c1340581609103014542c0c0c00404000071014452400010b1040d4640d0900d21b5054031210448002506411519044040c0c1820017501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910940116 1250 910938866 910938877
    0x606080606090105040c0c030c1e0308010e0603071a0310090e010b032407050c12040e0115020c0108060f0d0b070e03060a051902070303021201030501060807092a0915020102 76
    0x22510502e00089a64286886008103401240d550310303014841c140c0301612400307480360307090b00d4150141100d8500d00750072081c56481a40b0035075400304258540200850030840240c040c5100340c009003810000c00848550b441c1c0002d503207004c0ca541da500c0701c12034090001496481048654182400070003542e90652085142c81410ba049e10100302515440c041100340760010076400c1c243c0360010a00680c40b80d00034041d04034240d811294501c160701ca64080ca41c103d640503055070040700c1d0061051141403009108841b02c0c90005002c80303d11030300003800040009084034000c6500c031021144c2e556404c0b4840c542650000092031440c01c01701030080c02400a8000d6900038403800740461000800e6100380380c41601c10000c80e81444440d082c004010b5841080c05504140d020300180380088038806000c5d000b103105200020380180b90641d840d00300315490b0300c1440030600d0800d644200c01040088141c05039929542d19410402d80c00c000e4907a422181c121070a00c3e1001c00c15610890b405500424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910941366 1250 910940116 910940119
    0x3010b18150103110a11030f03091c0201090c14010203040e1611070f1e0e090a020a090b0306190e060a0203100b030601050703030e120a1d01020303040c150302070606080606 76
    0x35072025a500056095484031412408182420400c9940c060311038090f20000d0f02a2100b5640b4046555003902d810f0382041c0c07030103142c40c1c0103416a40030503461509030401102860009000d4000d29407105a0180d000e44030308c44918212000802c9103038400c0c000c490262901d140da4082c14201000c1c4505507451031880030000c2990020607181d155400100041200c0c0ba0103a0402c000307040001c1722090f0664460500715000a44ea404200007906010a511800b01c0000030420700002d801081a03a00035544001d4450785072641c4000162008189164044400199545541c1070380400300d0042207007550301007803805010240480d075001038000310b0040312201d511844458591980c0e142c40d00c400d45825002c5030b01081f2207000030b1302a4210a504481000c142d800306002101da0038050b40c080b4a58000107001244036440041c5074041d6540c55071405c1c40114198501f96540801010709405000380010103240c941c02d050344070fa0100d59060358442810301119030760310701c1c0b1380c5d40ea00d059038110f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910942616 1250 910941366 910941391
    0xa020115120c0b07060209040c0f030c181202030f3004062c0312070201020f0a020303030f090309150a0f030903080a0c030609090503040e0718060e03010b18 69
    0x3641440c00d00740301c81080d42101c034003940640790070030648580e804003d007115016020700051069583d04d03c01c200341d5106688074142d02801102d4000c085800701c1e01014144100c0003850b0045e82c01c1c103003410081d01c019141d50014001d02340006441c01032100509502c901c949200644003048441440c00307074010404541201c00452000120f02d4080c0f801000d000039200e60350810300d0f03604482040c084c0300c06811240c2004002101081c100401c1103555031026800050250465904000d83c0e06990b01c4040900b0070382030141d001030348a10003c1c100030b803200c40f034001040060a0600850b0781c0c0e21002071001402c0c260300117850b1540c1e000840150081240c14500e0309645d80640501e600c0107078076035106902942c4000c4003000070483c2c2610502055550900800c5807003991203042c04140c040c00c021034035185800b940f807061190044c924400c20100c030b034001d000c070102801010306685070703810300f40305d040b03081c001207401083d10356900b5500608000b4420b2003802181e100038020329584c46030307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910943866 1250 910942616 910942619
    0x30e0706111906090b01320d0605012705040b0402010c14150604060e090706050a0c020406171e032d03040606030302010e0714060d060e0103050d0e010c0b0f07050f0a020115 76
    0x41115003485296075015030980c06650380c07047d01c581c1008180c60300050810400d02c05a81300c0700c00b00c5509070800090325402d00300b10095010604400054010080d506002d41d00d03040d0b80f805501000500001d0521040c4002c08007004541c0b051418003405840407180c404040701c80440211405658880c0078525105c0046021000146003c1c40f401b03c443c000e02e44c0510b4810201d400da4071810b240010014000280001651603004810051510700034015276425080c0c41a0305003c00c220030308103c01a40203508200e042e02105540300364a0b01307000000c1d4a41c030600c01c1c0745c1c014084103a004c10600c00108000810a035a40b105043e01e010b0390003005609001c11207155140310030700a94081c0f400d002c0b0a0301c182d00e4000d004000c076090800011440e542d46298110001c0005e81045400340c1241501920040e48032407130b51403c803401d28018849003025262240f40590180c81c5441101680740010b038454002c030112682101020340c143c0e40d03002e190000034000d243c2d42c00030700006c44036108e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910945116 1250 910943866 910943879
    0x10912030501231306060804050c01020304030f031103071707032003090909010f0219020c06030f011509030b36060c03251d01030e0706111906090b01 66
    0x1425041ea00102c0b440390076000a0103005196900860302c3c580d014030303024100d0200c10a1800ba21006007203544502015045c0352170b10904000b07080080703030704660041c0030400c0404c00c85c0c8240a030064041c100f140d03043d0703a015030b0181580308801c0c0140201d515459603501c09a8100b004000c024001c1d0342e4103101c480e0700444c02d24668040030149181f6070040c0b000800c42e03d000486c142e00115100000940c46010310a030707900381d070400c990366036042065a820141503901444010440c1f901100d60311702c0c61606001c15100d03040180a2140706212561400300707001d016020440c041d507001a65a9003c2c0b07440c5c2c00304540c1103010722400c8100100340f1090700c1203642c180703541681454207401400c050790760b80340e840140342c00041c02e1040510804041c240321401d520b0b0060080e1500f55074120104034001b0301e10203c4100e0320f001c0c0b41007501d0b00c0d5007000850380200d0030b4000d0b01c0c160324052600902c1d8948251401254003102c0d402201e1031104001000440c0d803000a44c18840c2034064111382c0c0ea01c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910946366 1250 910945116 910945121
    0x20307050405130911150702030106030803190203060102060c0a0c05150907090501140616212021040515040609080d05190c0f1103210f0d0204080a0501091203 70
    0x1200a01d030201e14085804103107401c807401a41b046112103c1c90a14041da0002030a41da029802507030122800402c0c8413040c0d6204058201340340103154250325508103100000d40d1b81c1030007012800c003c0000300f40398401503c1074030004e688540080c00c441c1000c0c41342c642c1340800340c03064840014038403c0c9100041e800026010b158103c032050001845c2020000041c00641c0c0d01c111488031600340306180300c600050401e080107002e481900d80c3c0060250301c01c1d00282280e130b5100c9503052401b6001a506003103840015100800d1824038800c803000c004084001030a601644d000710b503202040380c0c80d03990a41c5600020780102c0e0110741d1800e1446640f0740c52252180310070700c069400200c0403c4866a91040c400001c442040c00380340141c465816a113070030341c80314421503085036200e070b1802440c00c0c0c900c0c0030081c040c85640c0c000807000414001c1010100b182c41810380c912100c1d000415410f80c4080d071941a43c000b4480c120681d28030784010728003207000303040801c0111440450602d002c0045446813 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910947616 1250 910946366 910946381
    0x6030e0c0a03060b060405130209040b0d11150c010606051321080c121602010905062703100608030c010f05010e010902031302061305010e03011b110a0602030705040513 74
    0x54803001e25203095858100160001100190700120704000010b020740b41c0d4100b000c0c1c1003468110058403076007104100029166001c1d0801e1080268069600220f02c001e880c024100780c0031244212000c0d105407000c200c41c00780c401194641e520300702c000140c4580080040c5001ca01000051485d643c0f03544443c100c2c4c5510010190302c2c40740304580c1d400003402020040c081490100115030b8513012076215821140c2c0021072480c06032100ea00800110750708842c0380c40203040c0840b0142d041c1600803540030701600c1c05101001100032036000000850b10103108900e032002d8225018414551250403082d82c035488030013659405c0d880c1000052041e540740c401d05040c1d80d00c14000c0d01050b4038040100c0080d41000d01005854420714244100581d01d06004040841287e000d40300900c0c80c200001d0800c10160f0030b20380c0a80d0500e0001e0302000824421007403042101d0400051551486d44118504154804001c18540c800400e03c000745400c03030013800c01c43c1c03000c41c2c00c0802c3d260540204070030303203503003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910948866 1250 910947616 910947619
    0xa05120f07081c0f020913050f06010f14030a06060f1842030b04140414070f0306060e090309030607050f250203060601050c1b0d06020d0606030e0c 65
    0x1030102000107103011000708030741243d0b0024032004200712040c160031549841c40f4001c00e20b40c00141ca0f4114141000f404800700d407040c004020914003405c0806040400078505410029000a003000903801000704148100d580003a081d1685401102c4a0017015140119008a4500c5901303460007840b03454041700b091450520404181e20b003152034850084840025101e82d0715428420658868891031102071002d0b8000c0c0d980c404da0710f48005404c403601c01640c41e000398144145024008154902660441d0780030010341941901c400c42903041c80c010b41c20075400c03141c0d941c0300041405010b400920a580044101c1c50198031001c0c1b849581f4401c0c03035502c0341c15410490018005900842c00b400001440c031090a18000c0310701c90125201c03c0340d501d00c08241c942100303003d0a50902300310f01035001c1c1c02800c0c05031508042c900455515040c1081004017626460070013032068980394003444286e50710090940d00c030502c01304120094241400380c00002481c01c035884081850000385103207070020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910950116 1250 910948866 910948897
    0xb0d05130c05010f03020c061608060d11090c07050d020114010f05090403141c020c06130803011401210b18011d06040b0904150b030c09010b07030903140a0512 70
    0xb910006482000d0109509802d142d070a20000c032100205020851048200f04041000b0124003880a0501c1d0b001034000c0e4002e22600760b030b290003e1421480907603030b9401150710003602d0f0345841d003070802c40c0304e07101c002000303402040c400f8507071550150000c0380c405030b25000d400340c50703030702ca6803410120762061040e242c0c41404075000c500428001d100c440100d0800f440a0b9152600c000ca103101c54060b42e44000d4500b6600091b80030103108148001900b180c1c00048080d407407561521030304031078001809803044581c92161200c0280e070282d0380004412540e40f01c2c016400030750a41013001448646041e034007524820391031010340b040503481103069031040030000304401d802c0c800f43c0d02c18075001044207800a90b64201d11542d551a0250980300f1b9100f00b5984811030300700c15000e4143d804011a20780240d115500c1c0d00100e655001d03110303056034244034a03161241c28505003240c0800c0c25500c040c00f03080c0c8503a640034120001050141e6a503000d20101c40c80181e1805039803210340308a940ca100b2050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910951366 1250 910950116 910950119
    0x4151d0306041208060406050a1d0c0405060403030503070512040807060b101b02120a05031308010b0f3105330d021305010803040513020a080a051306060b0d05130c 72
    0x50013000c15540020001e4400180c0c1516003010680d0803142c1e82045101d50395150080841c00024003800742d0251403944002d06286c90a8013094941c00350307000060901c103010000800c911300ca1829205004d049807912200d9060504010741a41d110210130385c0c0941c1000c01c0e407149401d0904480414035a1650346582440f1036800c042c441ca000d20008917808845d2206907a28840200003007402c182c021000740d661001c04441884507660f2651100d4090790402e02c04e007146560700c01d10b50150032402d44462459074110404610346080315107030816030307106030180c40441c50320355070049100d002100800d0030360b4410201528848030b22000120381c01c140b921b42004103401c150034000c90151010700604540040403140380c1c10345109030415502680003182c100410f01e00740301c1c04040303000440ba045103442c0300e9480003000114000c1040107516248c0c0c0110384114007240d045201c141d0004820060303607440c0d071146c1e0800e6004211503903817a4141404948901c000001c403580b040ea00c040b002415a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910952616 1250 910951366 910951403
    0x9030314030f16031d07080106050109060f050a090909050c0108010b04030c050d02041506031a0604080d11100c03020d060e062b060905160806060a06110304151d030604 74
    0xa030052202c4004040e190815034415000b517520424000b40700e1006000c580313040048440c00c40b82940d020034104007418008002071038100c0812080c500ba035142c20b0755241e02c901000d8401074810341c000c010f50303441d016420051000200d0740707480f14682641c468280340d0740c072005462580220f000c003810f50007290204001038640754000f0304e13219101800118662012400c000c40014295001c0008a61180b844031450b6594018404906104a03201c0d814141000d1003569150f00e002040000c4c0642d044410b00896804c024803002c8201040081c090001034150040194202c4690440414204007001c540000e0003c5841e10404014044515080c5100e0001800c48000d41d156030810861441980205d2124000c1c0480140a103004107001544d0068418000c002507001080a4000d02c00340b04007607071803408000444065141142c1001103d0701d80b1801d51085a0000705007600b00d00808080316002101c64900078510b07034070001030581725001c2c151101022140100b05000310305184e40c0c503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910953866 1250 910952616 910952641
    0x50310050901090b090d08061507020f130e0f1635010f090b0a0b0a06050c0f10061d060616112e090308030c030c0d090309030314030f 59
    0x10018280002c91540896180c2200c40703074040d1070341600c9400400a81c5031403a0401f42a91708110255110100c488400d200090305000e03500300284034202024046460f41e90341c824119046060610030092500c00781d224540d10800380780741d54410300400d002083c042c60401000704c00c0710f5200310009100c82140200000ea07601104800f041850b030b024201d2191407092040700100fa03859040060020b449050096001e90014465059581000a1560320b0f440f10200700040740d1082c10a03d0f180c2c0f2200d0030160400403006d11046181c42142c00000d040c100712f406c000304640740c001d201128000e802c016626041800c07034000340c02650800140083c01010031600031868090054010300304041c0b40065003408071101c01089184840208845210039400904800c43d99400c0590721180b82d50740b454510b00000705551070041300440003a0790141c0f540122110139401260030000c40c442c614021300480060301080d0000381181303038510400201103049900a0680c603940386010b94490310450b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910955116 1250 910953866 910953871
    0x303010e0a050702120409060e060d0c0b09030a0f0f02181e04030e090f100b070203150603030903120a09320613030c03060c090b0708070318030614070905031005 71
    0x1103115540c580c505e5454040f0141000d00b8405001041c0780c1d02e014859002c0314009403103223100d12001e0301d185001a10080b1201304507010382006948a800c007a0000342081000c07280a0f09010040c18000100840301c3d07280c41c4a58400c45d4980a49175285034802c4003980200c45480110b4226091941c0d034084000c001c6a000b486841c01c4800d101035440860f403060402e42c3c80a99841c1d20106101b00204c04400d00c00160550440c2181408181d0b000699252000e440d00c4070104c50041c00b248164a0070b204035021007001134221551448602c1000035a540600e41c80000200d8100d0702141e00c102076200b08036440101c0e0300c2c810130a00395010a1622800c011115917104404001d0a20484e4451203548001d5006266500d000c92a60504d0f400340c8039003050b10303420800402414407103030741c54006a80e001078001340501e0715901d6502d01952000a14613940c44c19a0640c2000001c00c0003540001c251503c200702c020401e5213801d01e09030f64844260003426810f4002e942c04015190705a44140e9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910956366 1250 910955116 910955131
    0x4150c05071106071406070f020d02030d050c0c070303091701020a08180114100501090506040605041e0302030102030a0c020f0607091a2701111203010905070e03120901030e0303010e0a05 82
    0x1440c00c0c06550311720030800e41d048210b020681102c0b040003146500b0070b030303002c4c1041e4890000c0d0001104400c402500c91041005e48101d40b9a190046806498540113440320842c24008482025403203040c0940310701d509100303a40303100401340504402c01d0b4060007925190b900d80e40f10300307840e0b841c1e0424015041c145402c940d1030665a400c0310300e0f4050140e60080b402624940c1d4214ac9081c10030000400100300c2e50030060213000204000c0050303540c440120347c00c64001d5a40503100c50000081c12840a1896001035855070010043c0308450115600184100c04103400720f49012400708041c0e0b4851104480c860040f0311048802c01401680181c4e14081c81d541a001d00e1804056800b0008010074000000c200e1901c0c50200c01c00f41c0d41c11019000a00c10b12000034445205003a040101922050040441c2a03403200f0104800c00d0160b0341ca2424680c0080a58407880108a001111a0001151140060f00309007160b10a40f074080211b0f4161030712550890400d13610710640e05e0107400054000d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910957616 1250 910956366 910956379
    0x803040f08070218061002030403110d020303040b070c090e1b0909030d140103140610050f0406090207030c12091202060307180b030a062c0405011e0504150c050711 72
    0x401070b9602161385010407030351040c0000c0c500703089013444000034100d4800010b66000308000e0001c203402e9540c00a402c801115105510001440030030b041d8084d581c40b415444a010a01c00c04012903800b01c0401e59030301400c20003046807141c0c5041c1e070391540f0340c0c0d4481026156030a03010b00380c201100050350000001c4100c038a8809401101411207068208105010034450018020890458000c0b40095114802000541414a80206400c43c1c500c521032044983c06d8005409813504e400120091041c0c502c11034a0b8207081c10003624120b100001201d140c1c40716000c22a40d90300420941c820307611802c4021150320b00c0c0744e0030322540d94000f0b000c84c805d0280350b81100c0803101030384a205010700f1300c50f1039681d200d0401156007800c1d292240c120061110b035034901c1e9900054008440840404c6030348440b250307a04c50b810407034014481650036400607404040c02400c81596504000e0055200d6200454010b105030100c50846001c0e504000010300100164404070b14030300b0320301010060040c1341d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910958866 1250 910957616 910957627
    0x10170a09080c07090f0e161e0f170708010e1020070f060c031b030903030b060c2a150a030e0d0908211c0204030210030203040b130803040f08 62
    0x2c0c1071503c252580407050050711030710718220441c851302481c00a0070b5070b08024143c0003c4010303084050308850040c1c0c0c180c07071303400300c4521149401f098040c2c0040c4500140d01400c03a8170349004d510140c9010140004d240310f40000011003000501c1800074006000c805400e0340840ca01e144000703402940188101c10740424600c580d00c503026002032100030b00c41d18165604800c2490300c903080d9404517081d2418985000d041c80c10380076440d002a407100c0340350303d80000c80004514050380241045045150040700119200e6260b43c400598503d64064148004828025a94000c2000c2040d0703160240c100201c0501d89050501c6030002c0d04000c407480c100415071034401003540c2c1c0382c03c1c00f60700b43d03100084038841d04001422081c41150b4a44ca650144400d082c2d08220a40801d40300c1e5400c0d0344801c448685800340600816030560700615401001c2d0064440c01d00c0006010b50030030303501a51900384120104070030f4445039060f505030561286485045542c0e5444200820180c800c0a643e9400100031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910960116 1250 910958866 910958887
    0xc0d020d170306011e02070b03040305070b0c030a0f02040f1a0415080a05061c080901021e030d06060804170a0e090901060603060b07030210051b030406020910170a0908 74
    0x1565950201c1c460016860b450a83c0005000c2e1001660041a0001c03682c2c070f2036040d960101c0e11000750781162040700d9807603c0d14941116180703d44000601000d507030070107200070155038200135800307000081410300000b1855440d510884c031035482120301e040169074007085101d0303c55594200c00505295001e040555070b15601c0c6120340d6541c114000140100c08004400003140300d1290448002d840e8449000c403040d01c142c40d114403040c8040e00e4000d0114004440380e10800072170507210740362000a0510b070700301200c80d580c1c0e80042c0c51610f0350a080c11804200301d07104500d00b6104270380005039444140004902010240d200c0724910040010300081d4136a0340d02c41002d4103000f5011503000050892a081c00101211803d400070340200c80200300c20b00120381e002404844008a40300c00280c0c2d40c07a0801d41850480442e41070030f0407000048108010301407035a0191500440c26504403a0004144008035500800310150300050754003200403400b00303032260380810310381440f0340f0700b083c40c00c0101074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910961366 1250 910960116 910960133
    0x80f1003080c0601030c0e071d030c030a050105091b240f041701151d091014041416180e031b070b12010e040317010e090607110c0d020d 60
    0x802d0301d101d0341c04080100108020403000b0b500400303010100c0c001906003050014101d101d1034560291101203140c1c2c81e4510b0f503007404080000c42c1c006080354020030842c54a14080d040449600d440760045401081d00c5100414144c1a40100280400c0c1441c00d03401000d060000031000c00c000c0f04c40d0601c8150906590800104050551034658103400c4081c0d260503829641800c1840c4000003444000f00700c102c90f458030a17a030040c512082d000d40b9a1358000a1450b12400381140c028441c14034411041420140c030000340104e00642d21701201c7d100380e441450b0395014151b02c00042440401d01000450072105030034180f4400c802d400328222101c0d107000741c238507003091007139800d0446000400205100200220f40051180100040c14242c0007056040040014807480d484044035900140c10140310344600740c02003030400d84501c081c2d6102c9044480c03040d0704a55500a49c0b145101152026000d03072210403404140c03c00805e0b44105c1e01090102808072404100c3c0c10a0207444001c1c00100f110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910962616 1250 910961366 910961377
    0x3030601270329100803030c0702040906230f0705070605041b090c0f020a1505070c0c0308030106030f05240f060301140319050a060504031b050c120d080f100308 71
    0x215034958403042055045030343c440e0250102c281380040784400c0003204c101005495000d80105181500c0b42842d0010074082c04130800003c03c024074000d66204501c0340101e0708094a00069404401c0d951010740c0340082e030406481c21404a901402000300050f5aa0001035002d0711503c480c0b421a401250340c40340403603080e0000c0000e15142c59904e010340d5400f5411800d280402c0c4001c2900e040e0a8450700901d221602d1000303101c0e520390b00060480c0c0d0080e807611544960088a0100c090303568180b01001e0340081c041c600009003000401d90840055006447c0101042a109240c040700f00030781d040b02e44a59103003283c005c400715103c00b10b107549034400b0b035000b4042054443c2801d01c4510416007010319581006201c80d082d00c0440011641c005841c242459100f440002c0035107950809480e142209000601c440ba151517440b4104040070810f00200f49003560304c4c006280b43e005907642c50300a0404160300080f882d0000034a4030410022060b08280d903030060441007512902d41701c0159006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910963866 1250 910962616 910962653
    0x7031205250e010206070c08030f0405160314070b030c190306080307050a0c06051207030c03201207140d0f0207021207030c080a080d0f0e10090c08030306012703 71
    0x404800050f942c0501603a07070300c4602858080d00f0310f1400e6840074203e00000d04000158140d07003000800b000f400b082200d400020804d0195011a520310f001d06d00c207980c50b00e021710103001d50400001c00700c7c01c0b078060b0b074060961200b5640c01d000d1403d044030540c0e8000720415007015120040022040014801050014081c20151516a82c0ca0402d400401c4869004500b0401d0030840f480d00340e81c924030078582100ca149000b0401052084040b40603100000c0c05c01c060000c980c0d08001c1c800a40b5006008840080e81c5c0d561103039403500030903600f000c206048072014004c02c0000801d2800e0984c4030000700c80340750b14018200061a00071031214040c1056a5055510664041c0f06100240748000300401d0600c008194100d029641c007140360041e032103c1d2101300d80b1011030b01544035130760b0402c2082d21ba14200f2540500c83c010710210203040b20100555048003800e0022400460110072030f0301c0341c0010784400d8002003449a45425003681120718103015007100d40c02000203891018150b4216030f1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910965116 1250 910963866 910963877
    0xc0a091e0c111207031e090302031608010b0102060405070603020f0d050c0c0f0318010e1f1d0109080304051c0503030705040e07030b0904261315050703120525 70
    0x20b90b145494649943e509111a070031906000300c00c002580300c50480712440102c0400046031103001c20940780001c2a4000960500413412f00302d000041603506203084600034002440300d00082401640c60320b0059401270180d030090750040c02418041d070000d0011040c440070300340c90a900f0504120484600360f07032244601e0000107003000341510402c03850404000f24806180b400400384c0b880722418107054031141c1400340d01440c00e03070195102060114200c0c0d05011010381c50020700300090000c400e9031000400081d0303100e4000300d554481c1c00301c0015160a0300047d45420b00f00410020103070580c0f41300107034104030f103001000084c805001460145025841c1d003901e450501c1c180742e000307c100030724882c100751420340f0508056407040f9103180c10a0700003584220403c11030032003130100035040c646110300c5040040c00703402c50741038000c0c070b4000c03030705075501c0d00d0090b1503486070840d142d204001002c1d001511a0380c1350f0511a2031a80030940002100400c4075100d00e8012500002d602003c00f107101046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910966366 1250 910965116 910965137
    0x51c0510060e0319200301020703080115020c0d06020f1308010e1506100c05010b0a060e0f121203060f1c0332070203010605220e0c0a091e0c 62
    0x580141c1062000c10b8110050b08840c00c0911407100c10b084955000340c10301000d402e07110008071742c41c00d00c0501104040d0095550780d90f2420301502c0c141003071081204883d48a0007045041c5c0c404109031034078003001012290900d4441c0c072048041d411043c408a040002007082528127058a0070300c20040820400101d084070156113001c0c00c01000d900c84541003100101080000c1d5100d5a00107401c08450600c0c20802ea013905045004020005030240c000080688c04500540c11804c8000207980c2102d0041520101000b840059000d41e08a07414582c441c2400c401d4400712440034560106e0060714030528a180d400014848464558503002e194034000224002d00da40011691806043e900035801c1c00c00c0c1032140c400090494a008210314007001c41c9034000c640e002e4100030024680100303213801b040440240090114200c0c01c1c01c2840a2501407a030142010228946002c038400800c10f404c400d01c0c01c140c1c070029100c0c3c02001c1d45804c021600300050310f40c480c4690403403034110796030b00207520 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910967616 1250 910966366 910966379
    0xb10080618190309051002100f0605040e030c030a0c030c0501050f0a050a060803182403090d020c09130501150b031501020c06090103020f0c03071109011508010303051c0510 76
    0x585040402c603800c1400081008250091869402c031101590400c101d801002e10032800c000070980e9040740d0600307000d445181294150040016034401325010040385071412803140c2c0d640302c0d402220149400078000640d41600490b8500c12460090814901c440181d41c1c440342182c1c0e003200c0982480a66506001c40100365110b80f582c06101074804020301402c03c110f060b500e015582d05070ba0921544000c121980d196150451100140b400c4c481400100600c40c00c56250000c45480c9070394800d100c40e8941080c40003804408640d80a81040e8084e1501c03006440160354a80c8195280e640742e003917090ba01c1200740c28110043c04000390580d1282000c0c1824014401c221403214119400750290b4025035a50b40d04644103040b09007001607440383e9807205000d290040c0400c00030b4600001c9100418015400e1044030000c40032240b000d101d0f86c0f10100c1c0305d0f51040a082080015041d800144000f90040c001800120740040c0095000803c0040040c00d4070700840d04001800c07210300082101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910968866 1250 910967616 910967623
    0x9060f01060c03080f09030c0f01050417130311010e121506100228170d0b0d050c09040c05040e03040512010216030e01030207230601090e0a0b10080618 67
    0x140c8124076160b090242c15032002065240080c12664950900704003086200d181001140c3c01210440b050317481411440b440300740245401c490a885001010307200022200404d02151007000c0c44000a445460654944c900c0300da44902c406414005805000211036a460010251189031304c00204130059201140c00050880a0001350007812001c0c4546450b60b0041004030061102c001c0c0d109100c0c2059040c60122a030714540506001c6040640701c108000c000010540310204100c14072900251205001d6035035115a4040d020380c0099091013a2441c00c030b01f12941003030048500141907910740b40000c0403109180e465400c207510000d020071a0307003081c2c04c1c1201c120f40f013a4001c41c2883d504080740038004c1e844820040811000440c020b0960b0f0090303050f41e0280b500060921580800d5030495a180c1c07a685040c0c0c55603208040001520480741d00a6500103100398014180340c40380f650303541d85181d0010f42100015800d40742e020540946c10480184510681c1101e0030004001100080c02d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910970116 1250 910968866 910968869
    0x50402040c0807020c04110f030702060a0c05040e15010903052a0a1415040f150201141006050c15090a0b01060201050405031e09040921020a110d0507090509060f01 72
    0x240b24a0500304425030380c021409021405003a41d0104034046100150316944c46080e8401054441c04014440d8240c0e00207051403003803030f1a840401000f50380c80e20544043c041d51142c0510078084400080d07101200c1c034689100c0140604007505015107903542c013414160b803e01c20381d149002c0c0b6540c0200c190301115403042da020007900c010b00c1d21420140204010031000e03089034010340003550907801d044a030700201c030020482c84028449140d1a420141060850843c442c0015820710501d06071450f0b4040b81280a9580300a041001e545802c0c001d40ba00c2e000050100e0481c0a40f212410206403400602c41c0b00d40000c070b01608410740d283c80c0000d007207001038001030110fa140504001c00108000110b03040f90b00342628110151544000e01c20f01442042c001070b401600b04072040e0304000560b00c10101c100030b5000038440310f11203440100d03903881403554050010b04c0c50301519810303400c2c0780300100381e018020000e07606490340302c501c03c9041c4c420a450a04659020804020300e01d801a00360030b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910971223 1107 910970116 910970141
    0x1112040302070e010b121506040f03080909130c180605100c0302060c090f0d030e030a0309030c09020a0f0810120c0807050301020a0c060c02011107050105040204 71
    0x203440b00854491035480305401d8002080c20540c010681d11a49081d618000030703540c030500b0001c804200030510a8000400b00f002003145041c1414004c0a940655075003982ca02410050003c0d52200801c4001108102c135031007000121550002d004850074141c078010050034000c0e00000034620755101580c4506800f030b84070300719500038983ca54070a00035000c0d81c0c2e0039503800303800190500c1042011503221805c1c0d11610b001c0d141c10007407c01c03001d000707182c40801c0c1c080b088042840d2006008054010442c0d00008004111161302c120000c0c160b491825802e0082c0030030060142c0d01c01000660038400d01d07030001030044000d83c0240c03006029000c544200c0da4800d0600b20030800a0707016200003030285610101e642e08050080303450010031603548030010071030742d22868003e103c650400f0085548078822291040c400401034500d107805400005070b41d061601c104022184402c9508 = true := by decide +kernel

theorem cover : BRFrame.Cov 910791366 910971223 := by
  have h0 := BRFrame.cov_init 910791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910791366 ≤ n) (h2 : n < 910971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
