-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:00:33.435612+00:00
-- url     : https://prove2.me/submissions/c9f0b0b2-123c-488b-837a-a2b67e97ad80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 456115107 ≤ n < 456294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 456116357 1250 456115107 456115109
    0x302060316051e190c0506060d020a080f0309010f02060f1b0909010311010201150605161703040312050a11030619081002031b03061e04020904020d0212071107 70
    0x300079054000e140488502c03074026a903051203c1c0c4500c80414030711150819040c2c200e4022540c2006504000e01c6419209000091816820401800281c2c840c1410b004e00000103410503a04003007018000900c000040000c00080ca50076405181c03644800c0f4001085a0b00ba0300701c0c40115441441400880c0f101c0350300a5030004031036a0f00c840360041c1c0180c1c0d68040d0240200b41e642c403143e100000020f108602c0405000b1241c00da00130002e8800d9030003808100030b03160240000141d8240b0090715482211031190520358054100801c80c07022003d080c0c50598000c8030118001242003079081503056142c01219000407441e0320501c09140a08491402800001c10711881004160442800c640304981000d0141108109461072011651804806980b0554410b4208443c28201c00680e41d0340d941502d0240c480100304490f00360602102c13004042c1c004020382c0e03001c1d41c03c112110342c030742d6584001c0000c0400706002503101e2411081c182c0701e05000030b094400344000495450035614011807444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 456117607 1250 456116357 456116371
    0x16060816171f1512110705060c09040b0901060e09160c021c0602070311060c310b0d200406020d0503040614181b011d01170a020306130603020603 64
    0x144840b800c11181d0310008006900c090b100007001c841403180690720505011112404c00c01c240038508040107000a02d01c5500400b80203600040c0108150062100040050203070003030001c9007224245000909040382070b8002000715900d040d000c0d0090a1101c0d52076400701405000744c88140000902401855506030700a2241010782c4000c5160f0146044642910350810390843d107910503481c01410508500c02e6605e094411140001c6001c2c054504a490f00b82c01145541383c292100c1f20f81d0741d20382111048000d10790310310240202c2e00c440e81d20b000e082c201e03102d000c000c192042d025160320291a503950074050046002c001c1840656000102c083c0300d040580340540c1d0700d80d194103149009204540201d480e200e184000e01102150402c0c50340c82600301c8400fa00c4201c1c03801140040d0f00c00301c0c003072400e000c00d12409505000b142c1051154019a106051810a035040c402c1100c16602048840c0c1caa941c0d03000c020b10160b402d004160f41004450030300e0810560341550005022030100411503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 456118857 1250 456117607 456117631
    0x603051f06050a090f17070f140d0203030702100305060a380c0a03020109030e180a050c070f06050126030706181a010602060619090203091606081617 66
    0xb02404034030554648000304604452908621b4403074a080c00005241d5039900b0041c070920b0030214511101c4192102262540c0d00320488001c100350600c030180c174041d041664503020512034040035803503c0310075100e42c04a41e07034001221700d4021f04200030303004650402101e0b80c065800440d0180e68418001120009604e0000318101c041400700245100e0301800541070b010710601c4000300754054000740c0d01d452203512418501d61051081c0682400ba40b00b5409090303019a010901c0404150301003608000c40700825032820321180c80303903400420149800c4401c656524010170520510129081080491001690504070004180781e0717603014a00703000d4440c907501d02c0c90b000d008001c0c007405c8081542c002d0420120409005d407100714480244a024054054400002c10b24640320b001214070300e1522008244042c24014090029000101076400e688900c83e081d000702000f441d0b070103000348100c0e69403100d0362400048044480c545480180d042c82101c607034903140f641b801c080d0694030038105289 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 456120107 1250 456118857 456118867
    0x50303030a181b1a03062101020405063007080f060109050d05010905061f060509060906040305100608010216030318140d0207150507030c030306030c0b040603051f0605 74
    0x580304040e82e140c80c00600d504180703c1803124100041c4549422554407000d801d10303110040d100c0b008540302c21102540e021444500a040301110031800358551a4040c00041c1000d4550010684560040314051008441d0041100e83c4c40c81501c2c24505406c0041a00d038a40d051035240a00034100280c04803030000880b10016181e03910985000c001020003d0514039580c1c1c10382040c0d8000e0100a4054805d40250b40015905041d00c0300b0b60388400c03001c0c540c41d0141502c0d000742210b26402041d14941e0000c0c080281c52055624000a00060741c040d002910350701680700c0240d800c03100d260748400601d900500180410070a182c00b441d1009426040c04a41121000001319955080050003080d404040d0f100c0c003160400041c8219462419400b211030f13071916a062060181c5030070340150f0000c3c008011880000303220f08000402035101c1d05000c0b13880e94a81e80c0c0c14092444940201d2500400032908100311917050040540101d010001c0c42d01811701d8190002c814140c600506040c4407001031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 456121357 1250 456120107 456120131
    0xf0705010503090a0c0b07020f0909210d020703020705090a0c0909021c11211b090d0c03030503060f0f03070b03060d051905240703201602011107050303030a 69
    0x100d00f0060703481101c40501c2c603203590301107100d5082208181c3c040c40014122740c0440c1011b01500b8011000e0a004000d5000c0d0740495003680b800203004244811410b100b55200302071a80054200c0358402c1c0c0207080628180000d00c83c120500508420802d0700301a000900b8a4006041c030099408a041c091389e911441000181c081803001c1c45020f160b8038100c0e0240b418031201c8003030f211600400d428000c42d91030550725420b1640003079400103110181400030712040b032411070080c40403010141818101d444d5a03294981010343d0b030340c401d9001c91400401c212461802c0a01d01e07020b030804942d010003905504000c60350700c0d200c0d400751400c8100300001052480e960b50303410800e0f055010003100c21100d40c1c42075952200c0f4045000b01e8484c85041c6101101b4412000c4072041c0c6202080a00d0a40c0d075064801c4001d00b282d2090310a641400281c10307406441807400405c441107203038402c2400c0340c403280f0005054002244407200d00e608020b0301804650b07000310403a5080340014001041d1002c0d060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 456122607 1250 456121357 456121363
    0x92a281802070f1b05010e010e040e1f0f05010509011412030f071b0803090105030a05131403190302040b07020609060c01051003060b0307050f0910030b1f080f070501050309 76
    0x1480250100b02509034440420102c40b10a040813004210749614042e075540040d03816003894903420f17001c030322042c0e070b0056242003c2d40844042d181d098101c0b0003c03110030601c050031601c2d07110003e10181d158052064040d1180c003960740108000d0311415810740c03400c582401c101403125811485121132070b0151081d01d80420503600b040048100d505d5403007100380361010100c400c00c0803200e510100c1d200d00003001500030007510700c40041a140c031843c40e0380e9150f14030010503008000700c105145408044020500e6960003110442c1000002c0d0360310346641c00301120109807042c00310304042c0104028000010340e40d043c6e5040c01d905a840684401c20b40e00040d00b1402003c04035503c0b0f40c07030802080700e00040c51800c0300c100c0e4045c035810032044403140c040c151201128001c041e04001c20111b070a03140d007401ca61407039002c1d00e298505000103440303a50324110391100303603252610300014884c2d0343d003035503410700d48040101138a40040c0307802c1a4840e1020344500103031107014103010000c030000c3e0340c00000b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 456123857 1250 456122607 456122617
    0x10f030c1205010b090f0904080f130306140a150620010e0d0f17090309090a0902210d170a0e0703080408100518100203092a281802 58
    0x162100340850768442d60b1320169130300140195445110341010442d000d040481000b40206e42103038210340340035404480f04420360300120315043c072801c65110000220311030f803181b48000002c10b812230940e4100440700806440c81001c2c0f402c1841c100300020081c0300e8019965498820f09291200015990041154010310f4000134081050003003990b0446016803241c0b042980c0c0d07215846022420050700300492422004960203209503008010015052800070325142c0d21004c103000c046000d503004e9001c156440c414091101c01c07020440e8402401e55030600ca0580640c40a151070b03080100038010030074000c030000d0701800201c0c1e07461040c030421041c180103e0b00550382204401d50356a658034805560398895406d0051b9042c6450045030884082c1c4002c1d4002c00b5142c0d00030802103184141300c0780254005010811144103461003040b4052524088000c0641918007440c80c0b030b036048082c40081410008032103403900c034103412603503c0400d2400e544141c0d441042301c0f5010a007441d00c020002e01c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 456125107 1250 456123857 456123887
    0x20f010815040b0418061d070b0702060904110d0629030402091509010618090b030d1d0d080405091e0c09041d061e07020c040b060405040e2802010f030c 67
    0xb0b4220070b050021680080e08a100a02c411f0101000b079070301c4041c0c4900c05400361070501c0104106c001c2c0940381031400340c002c0441c02040029120740c29120054544d03c1b0710300300c541032038442c08100f042c1e240c4102140d440362459000103141040000306203c8a110081000f40f0075410080840d600418030100000c4103a0301030716100c10b558592602400e40f040714640c007000070361241000305084045000e64460201c0c06002095022242e42d025a02c520b1080c000008041d8010700c1820180e555000e4858801e014460042d52182042c00340000b420000f130001014002a00403281017100c54403900c2d50040c0c41500340c0f0b440c1d5001030000350282c5001524080d02201c10702c5914004140410280c3c020b107140144800038001036098191b01740710480340c000241e013154101181d18105608400e094001c010609850551904006011201c109090304100d5000041c1da0710026034000d60000c881e0544056809016a10343c0002d20000b6000c0d4000109a1203c203a40f051500401c44521007180d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 456126357 1250 456125107 456125141
    0x1b061407061a09250203070201051801020a0203100917070203030412030e06032e030b011503021b0606010908061909020102011b020309100302030c0f090102071d0103020f010815040b04 81
    0x700080d00340c84c01c0b011003014000740d200902c4c035007400f58000030480b03040c00e6068444a00b040d0040d40c046095109411100d410350140141e5440144d4003846500301d895041103001400c1c0103903003000403140c4c0c403203448400380e07000800819000d61703000000e660880c0c8804401001182e06403130219000442c000c5c40541041001c4184150340e5007824180c01a000000141249034000c240402201085403001401e00c881580043c000320001d4115411001ca941c10301501c0c100780812107010040010888065075081402407143c10342e40050020001d015060040500b0b0812140c1011141040440310701c419a942900b5811a4000c0d006103280401c0440c0c0551015001940603440e80d0204052504c14006115a040410f00034400d032809002070403951420f09500088205003130340148241410340c8642000001c18034079120081d03140d0344130111101441c0d49580306004030501c4e1510f03154184108a01040408070020940144048040b60301180b40b20309680498000d065050001d20b0b650 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 456127607 1250 456126357 456126361
    0x40f08030406030b04020a230c070b09012309090a0b0d060b100201020703020712020102012a020d0309022d18060306060d020603010b03040302011401031b061407061a09 74
    0x244010001d00100c81003a01c0901c04040d0309400c200407072140c00001c0b03000c0f4254101c0c3c42400da00307521a401c0300d100c2c900c00c220328080d071250046140c0002c581c40303151202c0000070500565680121003507042204010110092580350588050794002d080b041d50062420700001500742c2c1d100d4100904082c4050240204984503080200240c42e0703582d14035005141d69402505c40c50310510032583c000fa0198044d000742c1d402e01245544002c0c2c0044103030f0456480d40607020f08405070044114102e404000354070540b502120010b402c11903481005014145010224409a100d20281c010703584014410321000c0705910401003000c8100b9007991341c00a8aa84026509070200710000b4041c000071412112143d950008000d4907060002000390840410310040040102040145400c103109000101e40581d684240380b070480c40907801502c08800701d4240e50b4060803203080d6600034221610f085a803a0030503481c9403d96100d0144001c207a2545c400e000c0380340074091134810180c90790050204540d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 456128857 1250 456127607 456127619
    0x30f1e020607020c061e070f0c06080415110909092b08010e01050105041214060712150f120204090609060b12030702100f020c1302030a0e06040206040b0a05040f 71
    0x40c0078110b5101c4054032803891400f0452074000260ba4426203151030440c26442c15012204040d0800e04085074000c011208400000310644091340240540d50f840c0790700c40ca4141030641c1c1250350400d8802c003051070054480600303512a411544817000555600a4549078210882d140034044204003c84010365102e2030106a85892136050f1a141c60355240d44c9a40c80e50340001c0103100070300ca00d41c00300d581040b080000042014034251f0f00c60107100c500c4079142034a10100d00f070803800c4549000044504041000e00012403041040a01b01420140c0c0e003d42010101c00d40440d00d0f01a940130381401982c070204542d902c0d00070811050340000f0a00907800c0347d1408002070904150054401c890000d9400012070340001a55240341e0010911544905042800da851071018a400c0c0704500804045c03030f04c9529100c4498440d02c145990069591907c00c00200446c0c0000315040900d80048080c00096540e1406881c20b40d481115480d81c0da02100030709495502c0f6a03803200030355100d409000141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 456130107 1250 456128857 456128863
    0x7031107061d01050103120323010e0403090305030703020705091302030a0206030a0609110702120d0e010c020619020d090501111e1507020102091306180c03020408031818090703030f1e02 82
    0x54815140c50502c41c10350151503014401f030445002d241049c2450700100141103400c01196045400390906000c015220749901d42150b020039000d5025a0142204006a00302640d800703601000e1407881040b804078640c0043d4072a14000310103840340d000880400d03a441d4003039022030020120b007082080244408400020f03181c000e10360582c031a14901c0011000ca8030042000d11520805a8401804007406001510701c013040c6201603801000a100b00d400e00c02047c2004001010140c0040c5401528100300612069042d0415410000e1401040c1500a00013403003901c0010133020200034941c480c0e00482c0f030100340074114003255249505110b41e5940650003842180c0c02076482d8440345400312400d805440151103a400059030204104000c5881a801961440b01d58a4003601d440c2d0b641c00e0711481c42e0814010b8000111001c1c1d80d441c030600d07001a4008103281407008081d42e40c0f6221008613243d0310a440040c0900007240c00c0c000c2c3d050b224030101e400c0c42060301004103801c2180180295 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 456131357 1250 456130107 456130133
    0x61012020a02061005060a091e18051014010e1302071e050601060201060b250b0109021b15040f11100f02102c0709090f02030607031107061d01050103 66
    0x140201c1300c4030021a06041c800d00301c0d20907900c3da4882c0c0003054502100030000e0311004000000c01c0441c64000720300e9015948100c65109521040800c49043c034140350014000305500c44194030f028012404440d0b600328024603c0b002d400c0b6414240d07261004031500c06442100402490040c56248084050f0380d2005c0c4955418000c0c42200e81d96a00c800060307080360324500a01903850028028440c20408441103445c03a4144060401050761b156660080b096101380c105410064020072482d880c0403c1b1443c01000d862450003d00a89422418040d56800040c2000e04000f1140c2c4440051000d98034848a5404010b03040300c0075000809401042209207074908401400b030260b082850381c045004030300d00e100c00b070384006650b81c125903180100441c0899043d076580c0651000000e01e4125882100a001e014118800c6a02410f00c101410b01600908000a00d80307480190718009103840c068a0a841d0b001c0c400081c200d41c0d07034120b502140d514450f0800c240d0300f8000040f0400044071911070b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 456132607 1250 456131357 456131371
    0x10e2107061e0306060207050f030a060f0e010b0f090403180f1e05010c0221190507060f081509040f0219150c02010c0813080f2112061012020a0206 65
    0x91100000c40c403c4068404c9803040000680c0142c00a01541c5400310b8401e00d81c50b0b0050844a211140395240c2c41a200440a1081103656072541c0f182c084001380185601000200c44418074400c2001c006254121f020300b001e01001045403d040c401980030306218040c1c0044809980c01542d0307894646843d6402004608003441204000a001d50141c40720800c05a07000700002801c040e040c050301c1c0c0049035601d0810743d61040e48030580b00382c2d42105d0510342c0705016501a103c191709007030010b005483e00030070343c0d401c000500d01089411030120200200140003161225400c1d119803d02c6e405807100d000e8003070340c480380780700300c0d4003001080b9100342040b20b800c02200085d0000941c002d46100f181484080e002c104004c0004000885c17400c01040c1c2c51032101280e0700d0480c0c45091603454000c4c000803541d10b0742d02007a80b0710384400c1070083d6200b02c0b403641d800c42440c0c9200404060000c21700505001d0040340254a480040303400743d10000c0200504040447d03c81803d244000d64441090f5000c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 456133857 1250 456132607 456132647
    0x1e0e0304030213150918060507030617070f0f0e0a0209180a0504020f120c010e030a0503030103081810050f09180a06030611070507060815030d05030123010e210706 72
    0x45c510080c3c003400d81d050005200d0100e11004030b0700c0d01e40103410002c1c20001003654031080890040301000a6400020003440108009400d008605200d29403d42041042074070a9030208401006006900e92000c00c0600160301c2e88100d0b0080b0303444090074100c3c00c01884a41e0104184100517a1203284100e0088a81e440e504840344140b02d00600c81d43d0030410b154000d0310340c4c4000c6501810460070302940c0541115074100351511014207540080e00104c443e404001407952120300d1407e50000780300021201074564000c04c0501400c14070501c51f401d070841901081c8200286d03078005801d030700d4544100610303001c2d00d40035070124010718180c00304a48140c60402546580304803807080d2441540d0010092551600f066816140300070000c05145080076000f5000c82c460302e0900c081415141140c9031161a54180f0038182c00300c2003414114000c8540c02c40e5103030700580c0d11040c030020190302612928000c0102e6100880c5d03c03140e0300072040c1c2a11800070005100ca40c0141d00b402100008440c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 456135107 1250 456133857 456133859
    0xf0c0b0708091b151b0102031512010b060d050c0c0105041104060b070c0905190c0806090f0405060c0309011503050d0e0105040e060f0117070305191e0e030403021315 73
    0x10780160206405401c2c1c100116544041c00f413a00403006100ca0785505c40b20180704015003a005082e030f413084400c0002018000b040032100d080c41da0492001c025200b0082c400030a80300701044003400740d0369110001944860209203000d00810450780380c1c02500009001514040c2004910341c0c403602c1e80c80d80100d1800c80700280c50700c3c800d41a6148030303600561070940da03031800c11360304003501021307011301041c0100c0103644603404181e100d03603840b0503402e80384d940b203500e0444100545540010b00401304000d150302000005100880e085a004414190468032030321014203850043c1100402011801051b56000c0240140059607820451030366440a0202800d0401101c460243e0710584402a100c600030599901d0b020b600002d90550601d00b500d4840100c00d0719500380c4c9800d03119100400d590300306200e04d800030500d04001c0ba1000483c180504050101c50300f40b4a0340c80184048441e82c1c40d2504401324400744125001190010402e405601d000f2542c600108505071240c2e20813002c1d680 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 456136357 1250 456135107 456135133
    0x3030801150503010510050c03041706060409051e1e0303090606030109020a09020c01020d05040b04060608010b0307031b0e07020f0709060311011d09070e2805010f0c0b070809 77
    0x110000201070740da48450469103000140200301c5116460b05080c0401408025202e581c104040c1000340000030300380c80c58600b559182da0400902a0140340075a0622003000c02180b0006408164210241c820124030300000105904001446c200c04104140e00071a0684007000000518014900700d0700303442d100d444950801d402c0314103403440290003a110103810800c941003940034001514500b0300140c80e24000781c4070501182d8003118102c560b2a550024031080c00031500c505006000c50700c00811500c0411000240d4551140c84010959180310210761190310000c1c5002c80102582e010340b201707030304003900060344441500d191000c042c0705400000520354064001d21003104d401c11240101d0030198001110119001340a0200100b103045910503580c07110b03400103103e440d0740d80e10310459003a000204018080301613422420080440400103c0403003001075001214002d00b03040c200899450016910f422840d240600030314101410000000d0700481c80710310030700600c000d6540c1c3d60350040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 456137607 1250 456136357 456136379
    0x501090c1b0b0412090902070309031202060c1614010c02011d030f0414062208150907060c1b351b030c0301052a041203080711011503030801 62
    0x61018000307031042c90108020502e5240c52601a07446490304c50f8086407182c4100c01030f6800803004500103040d0400400c02e1108000c41210102c400344098000c40c107150030035800034004c3c58600c1c80072503031407030f00706041100030889040c508003110000d008491010134080c0c0204521810103044001060b603190020380040704441c09900307802440c0d410141400c50700681d0880b00d840322500010104644040c5551011040304030081d042112065141842c10a50510480d0f50405030801140414010200004203010003a80e219141101040c5480d041180f281081e402041ca03a12100d590041b825050b1a040310b5410114140310010f4120b124204900e030451050741d80d51541c02940310300c80d003400e464142e6806694010304458668202d070700020f0840d801901c460380c00c0b1492130b26408800a0b29204886041c0c110403029040c0751030522002001d54096200404128038540003881150081c0c0350441c1c03101c4a00000c100368003000d8401043c4100601003a404180c002c000010022401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 456138857 1250 456137607 456137657
    0x610050a080712060302180709080102130b03090a0f080c0c060f03060405060a090c020f0709060b0a081b0a02031b1b090a09140601030c090203010b09060c010608010501090c 76
    0x265103592481d603802000700c81d40103d001c2542e05103901e03071400101507a00d6541c1c0d90300c0030042c941001118206020040c1c07005c1800d07448090300c2d90050010b0210111070228020444200320041552951800121800c200c44140d000b0402d4030044003050a1005202c05414007000081c110340a9001c43ca042015900500030a80c0c0c0a4004000140c00c0d4106600482c0d0800c0c406003042441a0b02e410a100075921000e80810059102c0501a00c440e84100102401001041e43c104980307420525002e40b180324840741201408050800b04020912000501d040d01102081c51901c0300b1540b0002500c1e81c2c010101d210302e4a00e12207282040101c041245c030004918030500340d00401c0c0c00402d210b074007400142861400307581c8446500103c2c194800c003580445030300e000b034401503065242080f44680690040492140f050005010001c0e0b0304040344c40400d41242c003a80c864604503900ca02500300d58020451035400d01c800011088215084101c220006441d04400501a1994103112041d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 456140107 1250 456138857 456138877
    0x180807060509061902070302010f0f0c020105060a05181b0d0501060f031b03090503070b04030c2f04020d1503060c094e051501091401030204020d06031a061005 70
    0x34000e2002c04d4404260f00404140703100740000314940d21100141c504480e001d0500c03000e26600d9801e9401c040707074284929030340f00a0448a07030561074100310105040e001116112401e1080035404114040e0212854103800002002c8031565416104400e0703018060078030809000c11103403106424030354040e000b1102c1041d4043d0040c0404a040101107001c0d041902013601c10780020042c3d240400e4604016500c581d0098480c400140700620740f0030310041134204001c030041880b8541c4040b900c0c0070104d2200000307003201d02680701c1d1000340108004100c404140080170003850800001c00586800c2044c4020302c039281c03040e25070354462600c2d04403844203898544603c0150240380522040401c1e984842010000114901103402c900c00c1044048810903160340c0e009185e180c0c0c1241008804502410050340305109080340843d42140400060100034826600800c6440948003940e002e03400031500b06c1d2901451861050741459041410b4420702d0103100c0136889107214900403800c031064075607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 456141357 1250 456140107 456140131
    0x20703110303040f02100509090c030f01051e0103050c0c030a030b030c01020a050c0607080c030c01021210060c03081b120a0c170109050a0f0f02030a0b010306060207030206070618080706050906 85
    0x2944c0ea08000b54515280e218005200d814400084603803034550446104407034030200c7c560341e81481d10000c99a418160302041c4515151841c07681032281c032501c4c07641150400c0c00e022403251504072115901c0d0140e20300100ea0ad100202e0040340301a856009400b158800350f042c0c0d03034410850b0b401240c48082011000d0010390202c0d1903c07a43e07080941c001d06605001d0100c1600b0848000d102c82d046920000c1c402807241e40210740d80640c514801e0a4075000540540719a40481c03034140082d21b541280706016050240480001e80001081840c1f10813001403161038076980e10b00010380c402c1505058844104007071030581000c02180c01f80b400ea080c03c0a401900280907807801240c20081c200080041901f03d40300c10604401e515180504200c6210400300581c07a4900400c95500703e4448060700d6042608115041201c640c0200c0d0b1107041c1c07030301a501299604013905143c0c0180660380c80c58680030714100d21400600c50842c01802c0001c0c491501800140c0b03828051a541d91815242611082 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 456142607 1250 456141357 456141383
    0x90a110312070b0907090c1e08011401080402130c0201060f1205151e010b030718030822031e0c08060603070b0a020f2a040501032001170a02070311030304 68
    0x950000c103540d80c0402c203d0110b4117002e8860824209403a0040000c00100790740c5450030000028200c1100041d291615000319150b1400640c0d5400c102c040d009a03040c001e060020400307544030340002d5080301c1c045410034040484145002402040c040c07260350380b002038a46020a011203014031000e031140e0090001d060b0088455100e4580d0390024090342c107e650003c5442c444009180301c035a00031315098401545a140429029258403811a4000c00c0d04d00d00044c00d200045104080c1c07010420350318126001220740110325118145680c01c06003a424072240b00818100500300c401880c20712482e030443c0060341d0f4500f00c0c0da40f48c0046d2840342d8150440c00e02400510f00035070280071010790714411241c2062084140508007030005022080041e582401e581e420502d0100280d100c81d070039917041107a985151241402d000e120700f9049000854510780c0d42c0168803030500c801c103c01880810004d0f508100c001207000f50305c82030045011800382c800b102e60400000c41a40d124a8001001079242 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 456143857 1250 456142607 456142613
    0x9070312120c0509120a0308070f050c01020c0c011107030327090e0703061107030e04050c04080607121404030f0c060f1107050c0a1a030a0212090a11031207 69
    0x2004141400041052400d14110303503103a42c1c00741c01d4040c08640c0320580d803462003406100050500c1c0400b0f0302158440b80718080001c1d84200181d901404900d03000c0092040008111824445e0450242c0f084d03001284013046194041140150008242c840b014040c00a1007415200c08031440050003244101c8217000003003018001c0e4245c800744119502c201d464407000c1080881d2400c1c0450070555000c00414000c100d002d111b2041c0d80649010071508103030303860360020721801c244040c80d8051600e0b603011803508c0d0300440c1500c020340340d1101903c04030300e8490720007800d02c46401071100035141800b81c07044800480c0300c04039005a030507960741e501115182c0313000d5441e5418000207d88007a65000c004601e400b8038803600381400300032003600b41e03144a60300f0558644108140500c0c81204103c6003008400c04a060b02c40c1c80001d0200b6480d101e9940d0041d0f00c00034011031511101c503442c49400c01a026101058001e10070b803048000300a60322580301456030ba030514005034030022004008840c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 456145107 1250 456143857 456143873
    0xa050112080a02010207020d201e060702030709061d0114010c0303230c04030201090906080d0f02120a09050301050709210c031e0b0a050c090622030c0503070e090703 73
    0x2d400b5003400058a452190380c0800c1c20030b0304901e403e0700c50144001c0d684017145010484d604034040101d0b060800c0c00c00c1d046205800721401c0210502c0741100145010031034905210b1075000303240604c810800b1550310b000c00c50a103400043c00a80d0302d0700c0c1000101d4000ba174101010f250f044c040c3d61b0f12038145a240d43c1900105404111202e00d41c0d80000d40d209020107402c0018454421070160a071694514030014118603115000704030118104031062294000000f840d07100000146024420888136080590a001003840c50070b661400c000307056510660050042011504154000c01c281e50300c2540440c0c841100d03009610991210040300340c0342c135101e45c80700c0c0182f50049149000b0700750b0329502d00040500c01c1d038510ba42c041401c0f1501080c0070f10813810a1384008510020f008602c3d0180c843e003840d200d280d03103682c070511000c40c12460030038a041ca0010501644005520300980700d0038100030960261081078400d1150481c042088020b4452107401a9680c0004004450a540da6442 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 456146357 1250 456145107 456145117
    0x2040506040212040302010e0c0405011d071e030203040c0e0405060402060f1201090c03140c120421020109050f12120406090807060c03061a0316030e0f030904050a05011208 76
    0xe40300e40c082c003d1901c104100300d9a54029840b9400006134403490329542400c01018940d1644160310b810010421041d00300d41007540840c5030b260401940c1e81c1c2d600306039a2900710303020380f003504034655100c2500702da015402503000340c1c00780d09010500e1b030780c80c08094a514400c03236006100e6080341020900504125019000484d0b490403240e040c1400608020003040d401d170b003c01c007102c1c1c0f01d41c1c40c4030306c850f094031900b0782500511404006610780281b50103458402d41280016519891002400344820010130b14514100441e0700104400030b554024040c1030031010607101c500503e45601c40d02d23a0006183c03648025001c0b113590804c0c40c07170050100c01201c001c0082d210745855441d2a00000c0b0920300402d4181d200b50340010300f1446001c13000f81140c0d460b030812005200c68444011810034070100b602d6121b80704140c1680706c0a4485402c41c0900010400c081030352042200700d03a440c1c203010019180d00387d030950f0100801da07240581c1a041d01c000380b241e803c41980114100c40402c0d00c14001304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 456147607 1250 456146357 456146359
    0x11404091e0309050612010e09030403020a030f050c0d1101080c19030f0e0303010b0c12250f08040b04080f03190815090c180f0906040905100906150b1602040506 71
    0x6443e00355100c01003841a88228140100c0d44101d00042c40358a99550b05150007007589001141800c0c10f40d804036850014174000584805072081e000b00410604000b107542402028050342d0b044001d9180c480f007811f80d0105031034041a1050000381c8051070080685464021004c11000c410740030360400d50040801c0510001601e4030740c4038000d09480100001c0d0b000300206a4842d40e075020011a46003404241c0c51101d01e0700344100f000c0040440c0803114a482c0340080c400681c030100350391800103540e404855004088031800315000520b001d40b000600308980300701c8191042010020a240c3e168811110301301d902002d922110425548245080c550014054415040704041400001e0b0003010403210a8000c85000130804038900f01d0340700c8140f900070281c88034881d140d50030001540e00c040091a803405141e031502d05d00213011003040355004403031004008000b03242407814010301038018501004078100d202800040ca0801c01d03012964196500c0c1a41c4181800301e50170440680b0b0043c100c0c3d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 456148857 1250 456147607 456147617
    0x61003020c060903040f0803070203060403270e0709050909251a04030606090c0c110301021e130807081b01030b100f02010c03020408070311030f060f011404091e03 72
    0x10386151a0708109040c05101c05100550300c0c1c51130404c480c1c0c012103c41d0806003494005110350700040c1c600140303840d00950715052240071a081480454817190000540c407040070f04002001a0380a2541845030284d440359640741071483e2680107000d14036005075020b010b0ba80c44121341c0d420f0304142c83c07100e00b41c1500c000045040c440c0d03503000000760060340780e007a40c1c000b00e4001400c00c01c03c28182705210080a8070f01e1709001d21004448040c182001582c0050000c1c036601040c1c080c140c0d020341c12100070000e20350070f05810030f003000c1140185411040c10100205a001d20100d03108400041000072205d20342e00030100c14222580780140458420000e0307051589401c2d00e5051a680c1c4002d9504550455584800400c0a1100282524540c070003600900d03104220500c490240459500300741c07600008200340c04503144010a1602010300f00305c00040c080e413020b12060307801d2000303014100d409501301403400b03100d100c0420084031000c80009101c3c940c100f034400960300b28480000c900d04d0103420700b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 456150107 1250 456148857 456148867
    0xc030611070212060106031d06072703030309050c09090604061a06040b0c0d110d0e0d060e1036020a08060118050c070822050406180f0506010806100302 67
    0x41001541031486114140d040800184046c035414401d002c41d50794602c882004429126900c00d89603800940324008121061456030206071000d86e00c160f4400e00c15250388170141c1d4030b080040084c00c640000b100e0900450303400d09494540700388a00d0040025402500c0c03151615641c590040c00000c0b40c1c803040c04220041040c6a40d126000f40001701082010b00d55244404124981003c0d117810200e4248102c0c600c00f40e500c04000902c010345c4070081d05005c0501800503001800010b18000010b202030f05250780030805160220707900700001c041c41010312050035105c40180250042c0c41e511801588101e200c04d622103000b02080c1609400074155031a11601c90703a40c1410250242c0000042c01d034100700100d03030610284103880d4841c0c005000d09040c248a582c56411512030315540c3c044400c2a01b64040e0700030200c02c2414001d2600030010414140d07560010844c1e40308540e82e10030201e280c4442ca0704c5041540c000d0520a0350141d40e4504595a5102080300006046540c2820560b003480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 456151357 1250 456150107 456150109
    0x90f050610052b0509151614040519080d05031902030604020903122a060703020f16120306050d12050315061201030b01050307080304121a07030606080903070c0306110702 75
    0x5042504505100303c0490145818010203160a42c41945903004001c24010408403c00034851001c1506c0213140241c2e40c12148850040c00340116001940c1c0324004101c000f0003003501c02c41400850301904155140100080300564450204403a408a581d0488241801e281941d500542c2e01850090006082c0300c0180007207480d00300d01e211030845420000a001d1140c0001480301030b5903541c20300300090544184c02e2002c2d03c2e0030015160005268002c075112517514400c4064406884001107608000341d100d041548403503010304610300200780b9141010032a828200c00031035003550442c5c29801c0c000b002c2e550440e011b5100401c44040b0494140c00c030032032a59a0801458194429401018a035042d800c042e2011601030f07200718030a5009000c104203078040401614216003041e42000e80e41c26031410403c1002e03154403040c15031010b01004005c03016070594440c0c007d80b00300380d171280b0703a540d603000405640381300305440a00f000102010400001702c0d141c11441a00c1034408085040040301c1d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 456152607 1250 456151357 456151417
    0x309070b0f07230f031e1b0303040b010311150a0806031e06010306061d0a1a15130b040f030605190c1101050603070317031003050f0106090f05061005 66
    0x100c1803201d008140300c0342d408240400031501124030004c007952030880d0503413112400800303603952000c40e03e41c082082031301d03094003810500204000c001540c2c2c0e81d180c13034176102140c18400d01084406681524607540c146c240241c08103800741d9031220701071400d550b8030801d4580c030300020910340d414031903420606a4000e20300c5600e030300e01a1000043c6015415460400c00342c0e0b5103a04209010550340c000b0306407a510302d0380140c3c0c0202500400260012a1800ca80c0503203540740840c941019070304040541d9401c0070801040301002050186803031a4980d41c520245116078814046641001001440451500e6000b1380c2c000004c000c00c46c0018401e11041e009558074060208041000c442560701402c000303008165110b141100178022b82411580c610308600e40120034601010008400140011044d40003400a59040390480e0f42000400440501a040034040c0c0040c01381410740190001066000d07003405100001d150f040c071040134041c221100d8021044141c9030050441c0d29580907410f070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 456153857 1250 456152607 456152633
    0xf030c0c02091008100b090c03060604051201060302060f030a0507020f0d030e012a180f0e070516050c030c061903020a140406090515120f070c0614040c06050309070b0f07 75
    0x22000200d0141b5000c0100107241034024109203030454100208502c9550f0101214142c680480b02140d030114581e10b154010075880d04001d401900000700303100ca408841d0701840c81010704c0c400c20300c956507a80a040340c031215044000c0307105074010700680c6820350180c1c0080322030042d40c0c40000384150b03200361000040c6445031038000b8100c2c1c0400300d104025900800142040402034150f0a039103140c50392942d0b62006c1d520500110140400216840358441c0e0216407a41d201800d03e010500060b040c03258666152808032442031082c151301e8215818100c1c2a1441035514018001c4a807114035015000b0750700004800007004142d01e540218140e040c80600050b085030340e1a1104a0301749000c1c0045114003548040072a0010320058008560000080c2d602040041c212030082e04e6101e0241e030380680020300186020b00f80445401c4954007000e00d9840346001d0905a0001c03075490b00e00f59880d2005450108694100c1c950a00012010700c0040c1402c68001c10074a18060403500c4504042d180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 456155107 1250 456153857 456153883
    0x61e03160816080a03031109120d02010b0d03021c05120a020310050402070809010e0f0301020c031e120c0c0a0c090c121104032d0506070f030c0c02091008 68
    0x19180074003014a080101c42d0059080e10001a90b190812416580d26600c03504000c00701a100e145404101c484542601e004040c0038090145885240f80920b450350021403212006610700f00d100002031410f6203e2a45003505900605036548a405500200c0303131000d03503100f0601c403041001e20920110607440d00d208002040740161a4104055110180091603010511880c014002171300400c407440c0442ea1404404d08081c011031881902103040c50144950090b40b40d44049110f001c2d021011004200b480180b100c20140c5030b201c529120841d008075803043d81d00c2014040010384581d00c0714010032844a0b10340403640306548960701c1c0a21004070760008294982c0703800c0f030070038802d41080510000345861501440504003260259040c0e0280d4440605541c1d0740e1a0040c616a440318554900507041820f207020b821a175050030366650800b5640140019190180454001d01c02c2c4210301c0c0712000c5588100c0d601089400b088a8810f0203400d80402e48000d510006208404104e041c1c1903c0d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 456156357 1250 456155107 456155143
    0x6060e040503030f01120812100f08030408100e031204080f0a0e01020d03140601050702060c0307060204030c0e0f15031507080702070806160c03091802070b06030114061e03 76
    0x2c1d111382012801e0300180e0003d8000700c8032903643d8001981c02810ba0f483c050019410340c1540d92a170034200e05580580d4402000e140200c00301059910011000340706640000040310380410304c81c0c002c101201c88075226210160400d00190300240d220344c2341d0a03003007030046240d6402d00d1007000703000d80e042e84000014000314070101500d41207945c06000c600741d0140d0a00b0200100c7c464100320b0721007d0001020b2a0410200044210455803000d09896600030440c0403a600c0741d50510700000254011300054410141210300000c15080d0034416503c101244445040c880c0c44441d00200495407884076164903000e04d2a210311101507459400d40b20742066910050369080c001c0001e414090103801284c3c05400c12010040034101c0d183c08031014032882c0c68800744d074084500317003140e039880d268020041c0243c0202c0d5144010ac525005084c240c1d000310100c2c0030341e440d558201403c94000000c0148041c41d41c0000914500d0300c040c000c01c0841c208845100400070f010002800c050464405542d091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 456157607 1250 456156357 456156361
    0x308040806150d030c022704060605030c1912020d0204090f15230c0417010603050d0309050a060e070b040803030f060906091303021c020d030f0204051c06060e04050303 74
    0x401507002d1440c054040e20101003554113500c0040000c102000c0280c001c0402085800c0042c0b0a0001908113184185035a0160b0400c1d00d41103001d01140e100b2140b080c03154580c90320b80740c5448803009c444000400b004840040c9030803041c12248410003420380c1d100c20b0f0281c010000d0f0f00c690190010b01481030400d4454100c145c0b82040240d00c0d002842d010807441c02415030102810b082036600180408000c925441c0d40e00c540c181c002d845941c120b20144942d6a942c01c40d01b410540000b000c2c0c034454815031301c002e000c0000c01c60458411040161072540148021f0000c41c143d80e00c041920920b13082034854040d203a04009980c0c0e4081d03030040480ba400001004a00000c0c1ca811581089085450821606205d00014003c64000c0c10a12200850590306010140208802c1d5150004c0081801c1c05200d0030501944170031030b050480d400b00b41004180100d0a500d48211303420740e1001011030b2810814050200c0518680003001c41c0d041d5903561000c9105504003090900c40d901c10b0008664034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 456158857 1250 456157607 456157621
    0x71220060f0703080106050c100522030f090503030f0f0307090f061d0f030a0318270509070b1c1404080301031208040f0f0f0f054806040308040806 65
    0x10320050781b001c0e04024062100456118000c1100b0124082d50000811b15440b482c1c0e800d030307c03442d85004807423140c0384a4001104140c1c001802e410340c1e28060720f0b41c00d140d9659000345602ea214404808564403800c10241c0c842801240181d40c125246103000124961244502c1d0075502003504144045105130054035500d0307a0002a152105c038054998061150a40000c40e5440c0100c03600182402601d54403080c2500504085a0052200141d1803800c42ca0841a14400458016180c1c154504050001d64140b000094507422103110340d0240d0710744228105031806281c200d4040104080e200c00108100e034140c81d070114001d6004542d03040d80d951640c0b0341199804c411214000500c98030358200000b081450004006041c4c0042860f140742403a40303001000b9015402c001022000c1d20304000090003000200601c520380d031008003944041c0c61862006900c0c03620311082c030440c02000402c8110003030299109910702c070041c0411f030906444c1d5594030f68582058018200d80da00c00310802c80d034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 456160107 1250 456158857 456158867
    0x70605180709060807030803071202040e070f02011a100507080d0606020c0102150a1a0424050a05030c1e06180a0b070201051e0903120301080f071220060f0703 70
    0x20b0102810800c822032905029a845845c0340c440602010300100c001034141e4028000b00615081441c011903440352a501704c0703452010709840d08400140c2c2142c48580c2d543c0144a04000c580c040d00300d40c0c505002c83c0c82000409070011107840204074090010f074000480751400380500003110a0040b5001d400d0000007440c00070030300c0b9011304660000590042e5107000f0000309030020720a9101140c0c0448800c0307022140013841020680151600050040340329230b910007020340c2c003010144080010343d548100103a00025004080d89034011400c10075941c0342046003c0c110318290303840e40c20b99000c05270005200c1e41000c040c1d50f2000b102e24000d2492840c20600800c09814034100240c1400385a0700020138900503c500046040076102e001e034051003808040e01c011003001006c641783d1403164031030182c07070350028442c651991162428203c801800810034a0645503005210101000907855a003000b0400c3c01d5899100340d14451010007648524006043c1d000b0380465544d90f8080070724000f08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 456161357 1250 456160107 456160109
    0x60e0c030103080f030603120a032a021209030a0506070903060509032502030c100512010b0a02060f100b0703031d0705060d0e010609020d230f060d080706051807 71
    0x442140030001440001c482030295041c50429a03400341e104e0392220701080c5040b503030500460581d6008500c3d41d128550541001044220b1a0176110f00c5130451507008004180700c00310341c0d0150300003240000c90b5180c800090020400003c00310340c07000d1900d444080c00c181007070b80d450780000d040b80300c2441440914081c0c2500110640f0080d440d0800c1a803110a00020814803480e074a556000341c40155507042224a80c1c002c002800301d07108650a10300034000d544014081c24060f0a80d82c00090500d20315015102c8202c415005012503a440e0101802124001082203400301c1ca15100402c2d40c40104015041851003a00c001510184c409a00402040d00f0b890b4400c91380d01196050000c1e8072000162420101e6458020541d41da280f50600e014007019040111268400700360041d5000d166009000c1030045a03c11307464003400d240030320074a414210307100c2c2c0d5007209410200d81c4e5802c243c000414500d0190301c01d00d0a10302c0c42d503030741c00c140e500607504c0b54a0910403184507649818103001440c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 456162607 1250 456161357 456161371
    0x906141b030412210509060711071412070e0406020a031d0a15020c03181c08040308030a091a010306111c0c030b03030f03090c0d02180a02130306060e 66
    0x50440c5410fa64903092900c0d4a0300749020400001c06484448225402408a0030344100b0144031074980a002590354280440f8004005003540310903400306040410440700f60380c852003011000f02481400e105001c000b1701091015403003030980001d80242501c0920307004900c680303000359496030f201100074160303445054062825001081c4c2c600386aa4005400f1826980c000c14481c9100300b0300c03094100901031017110305103e000009807090307035180c41c018056000b00e084840100720000c0e80e4580000480c1604000c102140801060022562002c00b941e0f0150320034001084680030b5646071508020310010307268074843c0c0000180700304400c0340504c40d00c2c142030b582c09a06207d528a10707106180100300101051a6450f0b0f4503101d080d100313800c558020640a01120741e5240311100c41200ba40c802c903102902c40c0503c6045c1c0070380d8070b004100a6810382c0c000709507640805c01d043c01d00002c4040075001e0840b00f076080100c07003030075440c0c4840b000055003c0d410005174146420b01e0300d160400c00901003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 456163857 1250 456162607 456162661
    0xa0215030a05010b09030d0c05030c0a03110106090c0f05090a0909030305040c080615041d0708030301080c0d02010f18051f03050a09211413210302031606090614 71
    0x1c04172688001503001242c2d1110700d8002004619418004d0840c8aa0303004032106002d80161031040c9a003013141004030103610b04c0204401303a40c50b03546600310ad5842c081c0e07000081100728400f43c03462042c030140038040401019804066900d105820071161082000c50201e5210001c1000303104807854090000c0c11b04101406c41443d00c01896100e1b042d03030030451882665120011000d0303401042007610702e00f01102c2281d00c000d440f002410795a8200f40b18a2850740f1500d80640321504040655000305a81a1660303018030340418800c0da160310094111169501d8505400100d2b640c1e2000c7c44512002880042c103c25002e900004081d100000e0645207003a05280c41c1800083c00944010744c1340c3d4815903200c18105100b00300f1031781c0c11054072560044a0303003c80c1c5101c003c04c070780c901d20040b10b42c9030080d2070b0060019040104002003402019015800501c40c03180c000d45003800704a0a45e03c1060f0003c3c0b80f0110f560703080112091748032100021100c1c0820091107008004402c600703c07089040d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 456165107 1250 456163857 456163867
    0xa1407121d060112050f010908040506030901020c01060b0d0b0108010b1206030f010903030605040b1f0513030602070503070203070501111209060c0a050a120c0503090603090a0215030a05010b 84
    0x2015055824000158030350a0740c80250088540304104040c074030200c1103050300d0b900d5039241c0c003074000c8208605060b00d01e0b02903070150350f050034014804c20207a5070307004020a0030b01d4a01801c0110681000b08003d546540810105044a070700b0310451014112449078552551001949242182c1040f501503060003000340050005c0509079098905401e014000c44045640d200046030805000000c111301e00e6003023486110806815030000d40560302c080d0380c20024001a4010040c02448400d80a11901610360911a10038070400c018000d901074002010052942c2c2c1e940c250807a4407101083e9415000455000114581840582c0c0204401d10b00754003014442e000c0e4603140c20805620032400032000845014030303290f803815602002000700c281c401440241c00d01035112035107601c0494070300c6180c5d40b0b164012030140c0441c0c8c1409400200642c1402d00300410700a15500c0035059581c00d00c100460000140e413000c0c07542e079000d2101c50a0350f449040100d0480b069071010b82001c5500441801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 456166357 1250 456165107 456165121
    0x609050706080c25060b030d03020c150402090a09020f03030a0305010f170d0c1e06020901030606030516031107120909050a090210052107030207020102060612070b03070201060f09050a14 82
    0x58131000e000c4142d40b4074185940c6882c0000f00b80218289406000d810b0b485201c00d90107501505029000f1800c0d41d1010000380303c4110124021100290321610030070129045440301d502c035140d201d20281a42201c3e07603601c4c00085c5590402d0149c140040d46500050000c0160034011000070074405003240001900d4440480d100c01d6001e14000070000c21030159801d2041c140c1c18200c004400300081544c03000c050a000c00a90302860900d80800d0404100003407061103032249a01c00c00740e9000180d05268164030407000740c80c41c2d81009101032414011030707000c641ea208840e1114482a15281c24040c601a200700a4500051110b000070745006083e0700580c56181c81d9a000c0591031801070354414403c03240201801c0da003600c03036441e21140010841502d40550060010358003d8080f01d0b420369680d010400c1c2a07030004001d0303025400c11141004008500740196401031380600004c10510b40b148aa160380010741d5010710745103620b820074840411320510803413071000f94401806000d464040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 456167607 1250 456166357 456166387
    0x6010609061107091104050301051b0904020d0e010507091d04020303070b0a1d0d03060e090a06020306120a050705130e1c170906150306070c1704030609050706080c 72
    0x1c86080c091001d07030142d2084400c02404004007602c002c41c410400240612074402c02500140aa00c4c041c1d840c01010a034483d00704084403d2141505107041d00e485509024000650489000c50090a403650001c4408032000c2c0201c0b4403c416a1350f030015490700d055107001044074020b0600d801d100041e000d100140c0c03804811514543e170082c200306480d48659000d800200014403085104101c8051800e04402020a1060750342c2c00503076040c00703c2c83e143c4403508107110080d541385c0980d9200311178200024900b90003450b40084014907140b200d141c0d0000b41410032000010450b031541084030705002910b0700301c85681c240220403004002c0880f2000800707980315107072209802044881d000d0f1422051040711286201601480c10000d40d00345050880d50f0f501083c1c5070303805500c6d80801e00040328100040c481e440b44281c1c1c0d07109060b40b412a02d5050b403040c1e101c00c080421413400c010120214440d8050462514424001005828601070000f0f11078080035003150303035103103042080c000001215 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 456168857 1250 456167607 456167609
    0xf070504080d0c0c05090709090b0609130507051213031d0904020d0212010f0b040609020703050409090c150e01020f0c0a0509131a011806030c0902160501020d150806010609 76
    0xb40c200801d40c20f0031410410182d00803544095440006a0100480340340c0c090b07403081c00c40e14a840248401c1c081401008100d00480c50090b40041030215400c1101034030750461070b00301d143d81c04d010346040d0100801980b1200100d070304224940b00305a052041580c0301811010200707841100010042d85440002c419280c05040a0b01c40c0725800011411b41d40c5000d415407501c502803008000101340c00d81450090a40c441440b41301d94a80740c0c000400c8602802143c88407a85617031118a41418440c04030010000711000350340c000c11000011400c0c9111a206404050060304c4919004a030031000914108003031410441c80c0c0c00c003040d029065102ca940d59002c0d244101e03448840340d07032426894040d0301c9800030090081e04a4040460010504800c0d0398161a00c8010021400303001965140c29581107200040c0700780032080e810815401e056015000d07030b00d202c1510080e1725880752100f0342a80c124a2035401655950710080d801c1e011120300c082d000f0010b0201070a042e44c94a94007902280781 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 456170107 1250 456168857 456168883
    0x302010806040e151005150405060f180a0b070b0a29042306101d010503192d060f0e090a05060424050610050f0d02030a050f07050408 59
    0xc40f45409100d00c018040d55800e00201000e0768000c0ca8202086208407880344103440c00303070882154000c00c0078003c004503001e031200500102c1c41c1c000c0f044400e1080b030f840b0b8212800e0b851040d401d1000f0642c0c4a0340c0440051280030403082c0c40e28070301e0400354116080540540703202440d00142201426100000c02c1c24903c0c444540882c01c80b040300818041c4c003202100d0440004074104903a170048410400c3d9001e410b00341c4000008900000060300c1144015880360050703c1142c02074551396105000450f4001c1d5400100d0480104848402082e595010095407005209034040c0f5402031594000003004000e501090180700d1404012008041c558016100b02d124100d000a4455200300310f8496000da201040320060315041c10115848500300980340750244424200e9204a00d25001e02030084500a2a645081c83c88200a0b0fa5690008480c02d514500a10400e5060300d050b1001e14400d20708100003040e1450b14100414181c80c008180c0c1091101c1808148821400061260b802c004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 456171357 1250 456170107 456170111
    0x20703030e1606050a172508190b0105040801020a080f0a060e160c050609030a45080f01020d0b041107110402040f0b070516150302071b0b04060810030201080604 71
    0xf40a2041b00c00d4000c03030062110600903001801074604000d9801c0024a0040506841c1441c0101080314446005d0751a003c030810385620165040d00164061048040c05040080c80c09030b80c0d018843c01d80c2c1002c07a03064040358205080180000101d01c2d00c0340e00c0031007168100b040b9070504100701002800a01698481045000e940d2a001e00070882003030320302e411100b1280301d4600a03501d56501e0340a040014000760050503440031500000840074131041c0030040e41a00c40040c6203080c01503003074401c100941d0300074181c4009400d0800380000c4a18000d5040056507844803403a07410309888007a902c207406140760030a0364010300e070110143c81100d40d00c050901c400f40780e08000980a805190000b1441000304c2c18000b8100705800020242144102d041d00c14080021000c0303000d00e0010301c03850344800b0320a1041c8030880c0c0300c4d50081840074401c607400f103070303000521000140c450308a40003d00803100c0000d0038480c594002480e1a40b1035180e015034154182160700081408001400060140d0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 456172607 1250 456171357 456171367
    0x1d12120f070602120106020c0a1214100e010621050706050c010e060708070e03010b090105060d0f0606090503070e01080a0201050f090301050a1d0109020d0b091501060201020703030e160605 83
    0x9a000072600c125070024000d54441c80803240442e2205000e1180c000944140702403041503052034817011044428013107640c03803000342c00c4d12802d00c24091000a00018010307031102d42c28006a910030f98800700c0b144000014401d081c141d460090780c0e00a5200c4102d140361407013100c001000000c040040d511540303412a1075155403c02903014106122447c4400d003e01400c20141c00d51100146224600960318018240e004206260032503d40c0002640c000040e03100500007410f041300108017814480800103400100703225200d00710340503508a940000e4501208000b40d141c01c0180070040d100c0b11502c403c1a516021034240c0d03640c1e412030004c1c1808800b14a55a0044140d41621400c403000b07002400340c0d1a0070914000208482c0b0700d450504041106403940c90001445041e45840c1d01402425000e070190301c804070789803c0208000c1d9144160001d00044d0300d104115180241810b030009a00d0303160368139018040d070356544c204020552003c40c0700c03030140d5040f8000c0c0d412903c03103041041e03583e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 456173857 1250 456172607 456172627
    0x702132f03010923010605090a0b1215010c0602040905040b070815010f03021b0d030e19020904060b0d1415060f01080c040504060f03060509061014060909071d1212 72
    0xb42c51400031441d00c8046044c0006042c5800c5001005c80708803c071550700c7c21a072540c3c0c0d001d045005214403900000d000000003550b0b03100845407940105014101499030035550794404003039030300941007507150035143c1e41400100190151107036004800c90415031424a0070350400d103641e990030364541d810041129000c0702c0c124041e07411590003421000c00c03004205001d4a003607a07182043c150000000c3d14003250314000e01400b0070135001001c020b0800c0d0b89003ca40307400700310426034050b1040d40c2956a540d48461141c1e0340d528041e4059100300c10300700001d440304900c9030420b4104014844001c05103420820150740704280415105001d003000c10140d220041a03403c213028642101750020b00d004400300d11042c4064452044a21850091050b0754074400034584462013a00c15914040c500ca40500060740085032082c00044041d02e2941084100f400280c3e2400007686c0030004180340d00300080c095038440700341c030200c02d805403065001d40648541e2244d48444038980e0420340a4082407040031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 456175107 1250 456173857 456173891
    0x103200d02160f050d030c050a030e0102040e040b01030b10060915090e09030c071e051212030109062102100c231606020d020a0b0c0702132f030109 65
    0x200b004528240761461441c03070a0000340c0800300b01030301d45100303024032421180d2090140d00c90040c42d680d075481c14403528110170340c06010b1142c512211550244000314403581e800983d18800c3d07014107004441035146040441500170068035120000c03800103020b020080d00030f0629011036902d590554451200c2403812a0001c2440e0000880c42d01c8440622510000c000302404083e80501e0946910641d10707124076084044400320303c421034441807000c010501c1c100802156854071702c0150f940009a0012920081e03100740c10100b00b069845c10306005514640c500055645211585020891902c0d00000c10464039803181d0303010005240000410030400301c9c1d0016451000c2180001e00140381d03e031982d2140c1e02e58002c141c2c800410240011841d1000480300c0c0620f40a402900307080c10241c07100202c4c180b0081034500071040800c0080700585800c14900504540100b000924000c0c009006c4a9800c3c21803810404400b0709c410b25049002e846c04030b0703045842a0100040c041d80238148410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 456176357 1250 456175107 456175117
    0x1e1221110337031a180414030705060f16020303071202030a0209030304030b0604050708130f08090316030506010f0e16020703050a080c0c0a081c050c010603050a060b0103200d02 78
    0x9982c480305800325100d034041e040b240c6110a14080f502070494207a041c80442c9100c007a81d0540c00d0490340128004c05c9105084c480e08280d41d5013642d18108054540e01d00c1e1000c290b807030440c109441001c200881d0459161809440000e04c091895424461002411107a1004160302260381c004081000c03028070b47e0440d0300c0a407010b0240c90f1078130f9880c1849d0f0840102151041d009500303040004a0341407080908130700c1413251401042c0000360948a0312510300402904a42d040d5080015143c280c2d402c010020407802c1c9a015003c0190031071500600f4460103a020030302242221809000076008114415808011005040e4081e003c1a004030310f4460b4603840a0000d00401d012030060009040080403a068000121020400e011050200c494554407402ca096006803946000301125181040d082034074a20f003250a080c54440800e003102c0c840e500445e03450f88000c660004210b00740c000d01a915900742010401c0b00f84c0e881c07880034900c000c900941411480024003650380c1200e035065075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 456177607 1250 456176357 456176437
    0x90b220b091e10180507030e1b0a121509030e09090604061b0507110a270b03030702010e04020c2503110f010203070b0a061e06030e12041e12211103 65
    0x1814198000e006000045003510030940220ac2000004c01e03c0c00b040850281c2503903008101c01542403c1e001000000d00d9070501c04c408010013040d05081980d24140c006000b091464060600d41c1010700e00f59040310f8100405071a0140d55280c05203d05400c80143c0e0382654004140c12050240500094200203230b6030004030303050000750360a2814030b181840a01600e000d10320304020b81c450038401c041c0d80e8081e81c04005c0c00a00340c1c01d0b50a2240c00e00d07070064260000c4100403104d0549540341442515160365030074800c0c00c01c80c107004106210203d01000002c001c240c1c1d01c41e0700380b483d900c0006d40302d209480000c0c2c0000c2c1070f000440d007000d09584c407040044c98003a91907031046903076070b9840410b03c0d0244a0180002c0c00d0441010400301d0100c1d02500b000c1c0204207140c5043d103000748100350324040c04246901d0000212000444034584a0350340700c124881c0400c00c1000b20b0300b0000f0482041141c00490801c0900e000c8140e04100000c04c444030382c005c84406c40d50041108030b42c11100189003540b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 456178857 1250 456177607 456177613
    0x18070501052d0702130204080303070509031507030c02010c0314040303110c0d03020406091d010504180b100f0e073c0216090b220b091e10180507030e 66
    0x10b081a01c10300984007441c0f00701e404c500302d51000c010311000c1c2d018034020015203810800108a409024400a0138980009000d84011880350f00701000011001c442100210f911481d5400c0c01c07990a108020910320541420401e0003c001040c8800c5440140003c0031305a1f201040a01480c1450580c5e01c0440313284115103000f6002d0034014041c0d08a84102e101140c1900004a0022881e96034440810710300485483c2a0b0f180c902000003416000140b0350301c101c8101e1482c00820150241a40b181210f82d00d5070a0045c6083c080250403401680103a45000c145001d0040340399204416117800c1344182c003141250a2078030019580c2030000059108003a440ca0510090705802041107a1a83e003800c0d60211050b54814400055940116803144c1c4441c1003982c621004162020000c90342006241c0000d480f1030703180c045989000b0035599002c1418011840d28200c40d1420426544080c0c0340035103a12007440c00103907800d10007122620701d08294a071000280407510039841030440e00109012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456180107 1250 456178857 456178927
    0xd0f02041e03020405010f0e13110d21020a03020a1202122106150403290c04030b28091103030a030c0912030903020105070f150c03051807050105 64
    0x800c541c000490302c4200d0155080000005124a146e450b0104a62680c02c54012680e00c1e1105c0d84103c0100d100f040303c2e014010951250700780c89200c02085000c1c0300b8001c405101c881c41ba03809400d80011040c000442d40007203040000658045030b8111820b501c04103440d0391124000060b410420ba491452007500c1022640356050845c900c0c00d5034520700c0106030203009031944028840c0030740805080300303a5007200b00070030400110131112417100c840146330340c0b40800c261040004042072050b9162045514003003010f0041c400d0852403503422121018240d4040644c041005d0030400c255440e50307003140c2c0e44000c0c200510512100c00c4100100040c01e0b642d0b40d418810340903005082d96280c2800262841e200464102803d9041004083e0141c440c41145407035a4011620347e40610002c5801c070004100c600001000c000d40382c1c802032241c0b03402140c00c2e406100001e00b1070720001d160b05001d882e0000e102c20390389004103280c002c2d580f0a1070403542e50003403000c100ca1001507855081d031120135865030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456181357 1250 456180107 456180149
    0x90203040602030414070b0910090806040309031a0717131a071403040203030d050603030c01060b03041205090a0b0904090503030a0905070b0c07050f0f091311150d0f0204 75
    0x200651290f0305c43d1540502045504100c2d0f80c2d903039018001c00c00040c00c1000340c2e410516003036810062006092400900c200d44551100c0c1c10070a041e103007200402c003d40c3e804d10400c03e0613040104950514118626a40f5245200a1100d1f8003855042c03801108074000c51856810a0140f01c401e5810031f0380c082c1c140308210440b002c2071400b110410000b42e002201100f410f200310301241d000e160014011804c1c00d0030020103100516019007180d0707041c44104400da68501c0c0a00500700109488046d0035241d1805003080000c91201403d40c01c101b11007080214125910280b01c00140e4500094040d1220070f10702c0824010085403101030442c0c80b010041004540d01d54200c0e80c42e162190082ea01c900c2c1c1c0d2207040015a005160141c242a000100c00340814285802a0110480d005001400d00d600e184080341c1034103c1a0b800484500540c0480d03000e1005500000c2c107410004c1c0c030f641c00003010540b108904c3d170103a010a0f50b101a190808030054119540540300a04000602c000e07040003c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456182607 1250 456181357 456181361
    0x9060507082a01050106020a0308181e060f0c0c03070f0c320d02011e021603030203190f052d0301080f1b090601050304020102011104080f15010521070902030406 71
    0x7010450b560a01c000420100c3c80070806085413a8141c4510540b034a0303241035002101c0500c20002010700c00d0018a6002003e9903012072040030011014041750304064241c4400c04a005040310605101000398502401000049904643d0004104c02102d46c440c034101c011b04599600132103503d601429402496117402860051845481000010000208c0c043c091484c04a000181c00b190a000c6081840e041000b44001302e0141881920600790514800d200058540d820a800507032011030203207440c0204140001c1c18010134103140408002031040200944165040c0308034001005900072900c03040d10400c5082500c0c5500900d40320340e12071045e507580e0200c3e5240c00c002480341072422804044000b03080704c14480081c1c145c004a982cad020055590758800707403040341159a21410342c9140d500c1c0b1005080079200b21806818210003140c401840d103103814a6188034920740c9801041250f640000b101101c100d4000c0008490707013140f00007030030450180e00142c03009000108000801c0129 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456183857 1250 456182607 456182677
    0x150b07060c031109042c030904150f0e0a020909070c0210021218030c1c0c09181410050f01050102120c03040905040201170901020406141e0d0f140906090d0906050708 73
    0x6407810050001d004032142c0003101641f0078bd0002c1c0b41c1c420014403030f01d2800d84000e030380401910000f500c0c20000c0d4012504a08003211048006503000c2c000004614007000c1c10040510170380f0062120305046945200c86108140b00031601c4022100b40b1099a03c062001ca81e4ac41d1008003519020f003286902c10f01c0100300603c04a94070a0240e1020401d1002c0b88120315402c0c3d41e143c4c4403508081503641c1d04d074a50740007403180c0d0214403078101402c2401840e400743d02d10459080001c600c56509d02400a0b00c0d180141c4110301ea89202404203010302400001070740c2c102c5004641c04074507502c540c0010f881e00c420746500081c0c110750400400282000540051084900740e80d2280c03002c1000500300d24003230140200400e260403a0110148248440c07101038042e86110399800920107003070842a1044800a010f031401c0c1c4400e8408012040ba010b00c001c07940308001202030651209580c400816940460042d242400004100001480040c0c4252801011000400e00d14201041c107205801440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456185107 1250 456183857 456183859
    0x1080607110304060509010e1309030206060d031b080c07080607230d0c09170f010b04020c060c0a030f1e0f060803040315150b07060c031109042c0309 66
    0x484021400103882492200070408078003020750700b058100745003103039540d11044405040050042240b80c0340d980c0c1080080321300340c44450024130300781d4515010f4208100104080d00c17810310340c00180301180d0040c1c61500c0d00b080311031601c039000c6594030f00f2181c0d07030003042101e0405208821010030382c8540090451b0050080c0e4807a484038625055449412032061141d4003c104800d1001c4000d900d1160000740117480c480c28200f0307403962620308000101303140040c18049a4011102c1d002400c50070310030328280708411341b0294503002820004a42c0c4003409000e040380b0140002d04201c0803486075000418092003200d0500141241da21928410220340e07000100440c9403001c2c80380c01c080940310b410101c488510186046c9841d60321003104420015404a203040e4940301c0080018041850003409000c00c00804c98481c07555092a000701c40c03580e41d07400141450f000c81a0340355801d1600340e89002c9812100480c1d52103207142d00303030802c00410389245071030440301c03280d100809400300c00381a190340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456186357 1250 456185107 456185113
    0x60103050606060306131d030a0905010905121e0f0610030b0603060708010b0f220e0a0e07180e0f061815130314031f060314150d02180108 61
    0x82e1001002101d1005455246d400101e060704000440c01c2500031100903a01c2030f416072005e100307501c54a811940805940000903004010601c001c6da003208010015080c16125041e6041c40c01a132982e0b40c0c002a4940e8404142c5895403180394241017092404413906030060791454140b24902820300c0459000881340805500b0001d0076a00340041c402d44120415621540300ba440d10500c1c2030359600100700e001c00240200401c2039184514804103150f1180800c9811400386010a2807c00c01c001030003002d40b041c20803403000c2a0603800030b0712109441440e084150900f410b12841e80052103000d00b03114090047d880048180700c004500c0d50320800b0540018034101c00d2403600c50380c5524404a540c0c4c042210100850b250b15600103030319496038400d041842204440c00701c3c07100c1980080b1641903400902e00c2000143e0381d2440000d00c000c0420f070400b400000032410541c40f030440014a40711b410708c611800b4007429030f034200d000e0794065005400e03590441d81845c01c42c48516000d021b0030241d48 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456187607 1250 456186357 456186361
    0x3020702270a1103090a030f0c0b160315030c0303050a170901090b0901020c1f0905060a05160807020303041502090411030411010903123b010207060504350f0601030506 74
    0x42e20383c40489102d4550701d005008050103d64060700d0361102ea0400208200c0e0001c0900000751100400710b0180030b80c880d0654a82008840c001c094860048010104018100d42000001c840e80b600304c040d41d83c14101b05444c0c2c11048001c550f80943c49030040d58201001051014a000640c800030110340290750112850b44c8120029080c0e12a100c2024125442024441c1071690f81350415640c00030701c000c011981201e151a00c602d402c0094924050b216901e801f03020404442c4510b03e07c3c4a4001d00f48403010303207440f040203510703404010800ba04c411402170081203100d003a64125036120034014400c01403165410b000c1d145542007100e00b101c41182c00d441200f441e40c01250003008580d400000428650040201161010308544241e040003504092411071607000c00c80720000c07888000091140038a48100080ca4050b166105000b807040800041c003825940000e000584a103483e03a03180a1080700200b09a0702088040d1410207026410038241c3c18040428101d0403640030b0360468840ba = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456188857 1250 456187607 456187631
    0x40f0509060705180d050c030105091501060c0803010b09030c0a14040f050c1c0e01110706141005040903091203180608190b04150902030123030d03020702270a 70
    0x138030582c2540b06070450520520452850b1215488080510031000d45036109207800c00300b8292141991a01159040760712101d8500103c41e001c94010401880c080e196900f05031200700f0a8801030081107a43d001c0003071007841d180c80c00c0021120b000005008081c046595007002841540c0c10180c03288554104001400004414010340d402030004003505c1380740c200322640a10a90752584501c0c2d00307007500c416459049007028420040c48a28540e105540c4900918248048654003004c1c0900c0380314440610280c2e1922003910300a5403002c2d0740c0000e45441c0c5050903510248154070514910b0307080502503041691140d00b240c1c119500c1c444418034240c4518003524100001c8510760185a0001406180101e09400581e00c0c8403000d030000440564000100e84007045541000f044981c0000040100310390341020103c60701c440c0e82040490003c070300700085d1101202950311003016000316a040035503803128000040c0d0505044020b00400040c0c1c0210b40205c1c08884402c0160301c1d200d494400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456190107 1250 456188857 456188867
    0x18160e0a0305060a051b0307020c0405220201081003170a1b1203050606040509160206060a06120e070b04140906010318170d09030903050d090b0d0b040b040f05090607 73
    0x81c1d0707500074040c00980d074942c2d0311100141402440c4410b8040f44202907140c52200c3c0004500a02a50740540701001a03102400305541004c1c01b00f03000540d9038001d662500d03003901d0b0b01050342d03542460444a180c84108040b46007180b9500007909d0f185866041c401c6040860f0002c240003080d40d1513107000100010702881e841c81ca05034000e41a000101907a0301c0e450701c21303445158000c0e401400309040503190740204480d92412982184640540c42c400300b2240c1c1c0400c000c40e4000002c44d000c0742a6030908200a0500b4968004d510030ba07521000d0303e104e041e1083c09260080c0943c4035040d52240d82c2c3c0c6284100c80d043ca023014a014017091030100c0c0d46035200c2d008480d044401c2d12030211740e120150f5201c1c040e101e12500010b0850380c09101c00040300c039280c000c808640b4080c1c1c0d00d140300c450441c100281415541c0b10401c0a20007800410004801c0c030106440c1c00301c1c200c2d84001801001240460054041d46210700d0340b0a02d486801c80e0242915070085001c1c401c080b08035806a0741d400c00c2030324 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456191357 1250 456190107 456190109
    0x50c03011a12030a0801121b15030e0c010509040f02090904030c03090815242d03031207050a0c0b0708090d0806011b03020c0402070f02120d050703080618160e0a 71
    0x4c000350103000140700c49801d40c00f030180e0151242030500c43d410740c1c1c24080c1001d84019000f200712941044141b44255615020710000408540702600e071640f01c03800082d009100c1c4990990182d81c58030311040004401ba41500c0c4110700160056485290a240c020a028240c40044020a9820b000170076900310024441070704145042030000340d51601c1c50f00140403581ca80c1404441e500200920229031a003122080070320800e400381c3d2205080e4000c90b240c0d003821000b0041d004c1c0c0e1003800090702d01120f4800c0030340c003d003840c106030355110780c00a801c4420b48003184000e130140d07221006020245911500c0c40344582c40c218241c1c3c05a0005d250100c42101c0c00b61507644c00203507088403e8551050b400941c44084e4441c0c012151143c140074046010303030700404003e941000c80218104151b0801961010240d0f46c1311001d0400040e0003076015009015000024003040003000005840703450711030000c083e1402000c1d43d2000c920300509035401d09014800341c10000389030074a081603075041c54102d0394 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456192607 1250 456191357 456191377
    0x7080706290109050d051e24060906040203040f050f0606040606080f070513080f0f0705030312040807030903080c1b010203071a0907051008070306060e0616050c03011a1203 76
    0x81c940e5803a060411117048a100410f96403405040c2c0a074849540d100804104000300320090b03d4080124500d007414400c80d080403c40905c005400c00090b56102d210b82d42d4442c108850042e200c1d280d80c10101a41c408000000b8058440c0c0341d43c10441c20800641c0d0b52003030404880c203020b61511048101c032941d2040c0c411221403449100400c600b14001c501078040c011003000e218074150354a920807480c00300d803d40f8441860b0006000310089003010701108014003001d800031890300012008001100400a0029040910111700d060815100701060801903420088454907803404c0032005441c0c07800108080300c02c660130a00d001a075400130051f5051141c004407e22141d488061a590484100a240c50550f000d0008049170994404601030b490701c3c4a503941208500e0310110190072900c69410450500c42400341d1007455940b4541111407100d0f651050038610035091034014034001d0815022580355082001040103031250000014510130115061122086030034095500d0744194483c403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456193857 1250 456192607 456192617
    0x11728020a051c020d290a060f0e0412050f1b15010501050f030a06170d03060b0f07110a05120f060606030402031519060603050118060e0105040b0105070807062901 72
    0x8015240400000349154041c0b0034840f040d481131941d006c64020b5400c0d0074110725003c101072000d150b00d54882e9401510202c2010071009091110034405a00c0c001c0000380318140200d000c10740380d4420303001c1d00c41440114242c10b40368150354820010342002c00300845403c0c420307225011240074440d40414101d603411784410785080000c509800300d50740024016440c2680361440040d991102103001c014102d01070024110015040350000d0641e400b56102224021060200404c4001c640085580c2c86900902d14641180541c01240c401141580440d51207170104500b5510008045080300700030b1005400d440762070b510354003005264002030f50040d40651060308d5a0929a0350305040c0c9070001d440074141e010100c8442c0c4043e064800035002500040c0e1138800400c080101000801001214a08140500c1e41010391801001d02c051051501c210345415110281c1e034082c2c01203440b45604060310030303583c6810341040d4000e0414a10716030191510b01d002100400400b07074a08102d81e82c140d4607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456195107 1250 456193857 456193909
    0xc030e180c160c08030909070e01020706120e07090c02010b0d0c0509040302030c0a030c02090702032d0d02040902040f05180f06041103070e010207080a0b011728020a05 74
    0x300c40525000b02c1000220400b4041200000c00c1400d003000004040e04c80c0115134078503103401885564440500400140200b10320000c029070380125a41c5e06417a4140307048170b102c07403051098070090402940080d9190095810105003c0310719000b500094005130024014512500d0a0294800a604000e400483d96038414880c0340780a44005400030b000707104076420300c694024000c1c24494030510440200d002800002c045003070104000740d0041283c0081c2d414018640c5040c00c4107800b0707405a003007014041d0307281100410101c0c140c90001610340021500e0725110310b00400258494054610f0810030b02340f00086503c1d1034626910000351290640310f081e100c0080700011180c016040380d0f4029282e24682290b00c4004000d90300c204da0313580d2002000c0524034006801d20615402580c42a00000c0c80c00d804500c05040750b030b0445031505000c1d83d4403c5d4071500903050001c1c01b02400f038248070b00400060041140c0c0d180c0c80010340221144c80c1c5680d13890040080e1a004540022114401041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456196357 1250 456195107 456195121
    0xe10020f07140114030a02030f06040b090a090c170a051204050303070813240f0216051c020301090321060e0a05041704060903060b0315061504080d0c030e18 69
    0x108a146100c0107060409100040700136410540c1c004903140c100c078a50100811031070714030568555400074000e65040040740b61072800b10303034401d10041003d01050f803031700300360010803017400e07083c9005000381044851030040014685445200440080d626440388070401042682c0700001c0358200e40c801401586001d200350398104058104416901810522500004200342e5001609000720221208048415603640d070140541040c0400482158800c403600e0850034404642c0ca410360b00c048885001c03425000240300d00810403094000e4055007440405400c2540003600030030784140c0c01700f40085a107004402042103860900c07440c800c1ea9607407130200d048034510380d01c205c0d0428014019445429107810443d0b0155100703608c6840002c0c0e24010810600c5102c1c468490800300071005406030350280701900900c0d06019100c613108001070310800d04010500c408480c0180001c80a40d010300808400203480441142130603070204210840d00e040794903042400314001010490200c000b0385541c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456197607 1250 456196357 456196379
    0x1091a030d1d150910170721050c0d090819080403020601060503090a030f0e0312180604030f1e0f0b271b0d061407030e060f07050702041b0e10020f07 66
    0x2003030580500400020340e14801140c0b42c00176101e036807d0349030380d0829030302501c076001d40c50404c3e034403070300c85030326020902191034068011140700100121011400940500f0040e18070700c03808041000a1441e0380d4121103003604160440d00c036034003e800399002030f0b907541020b0300c0c9880304407000611500509120340c0040e00030785e03111500102a1401415041040c0003181c50414074004040d440c00c00820102031000c543c2541070391012068450074289451940c1c2d52001c004060001080e035039030781e1812034080340d01c1086401515000414941d00d011241824284908140e481441034800c0740d0180740101044203000003983c642000900ca81902020380c084401000d00119078400e1203a141b0750f01040082c02840d05524240c4201d60403801c0028019080302e0850003402e040703800180c10404208032030128107030b00c440c0c2c5080c402e640300a5172000070002c00c4034100d011507801a201c0120042681302418102003107003583c040201d05d94440c8207a81d44c0341810340203082c55001e20310038010f000c0b0300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456198857 1250 456197607 456197629
    0x12021303020306040f0606080a0312110909010306050601030b010c0f030f140d020310050301090c060c021f0521090a030e060c0d050d0b1801091a030d1d1509 69
    0x601460482980300d034002030030120180c6040e14424a00c0101500348040d81c0700d11402000c81c640282071300d0100d550054040c050600c42c6481d074682c0c400107000d08a5581d03007154480d0740000c01000c2d041d07071207141990007000161003030342c00a4030309603c60340c06502912600030450740107030b4400c40c01615580c013100d0018503107840001704038000d143c00401c2c9005001814030314100c048056220320b0003501c40c0d1030308601540803a20983c100f03030086010a04051803141a0b50307040ca0014502280c50003c02d580d1200720521130884014084042d0165038814040c141501d101d40d00503981026091900c02c06103005d4483c100950052000040082c0c002c0300102d0241001401803402e184684405a060004040b504001b0500004016541101a100b81300c42d6000c05c0b6060014001c490441c00c414074414005d2840d80c1d55180d818088081d443c021030300c181e003130040c1111020307140008010300720700b00280862501e080301c8100c59a50710b4104810601103000728207060600e884142001200e0b520 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456200107 1250 456198857 456198877
    0x9070509120715020f12040501090b0d06030f0c06080a0e0d0e1504091401090501061202032205010f0e03090607020f12010903050a08070503100302100905040204090501051f1202 78
    0xa50b02000074908100e500b1560070860940181038905d002e00c2405080141209541030403030010042440741d80e030020700d14020388a84210b81601c4000c58580f030b9008000c684c0015107003182044d0fa1804000140313042c102503840c82d95841981d9202c1c8440c1800b0f0710380c0c28007400c50980010340d46d42020781c070440c0c1005840500604114100b00f00a034208000d92060300b1444080340c581b5244908090b14141440c01031000100420856152800040c01e18004150b0741c0e855a40000200c0c100c80c0ca40d27040d40444001904061180512034503045000740f02c20010751640e0750030541d0554000078084140d034000d02e07028001925084c459400c100c100c04444200560000c85000382c2c41c01050240300703e803441e61003a01c2c0c496880c80022400f401d403990040c2072004002c401c208101e01c0300c0a000d41d080460ba41500c42281481040304161031341155038108070340040c404180054002003540029040f1402951614140c220126541e08a409118456804038034140c00c400340152260f801019400030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456201357 1250 456200107 456200113
    0xe0a0605090313090605090916031b05040507080118060f0515040e04050703020916231b0304032913020a03020409032105150d1103010e03040806060907050912 70
    0x2003c0107400c006542e40104184a41c0c400c1c050000703060031540710f030308083e44d00001d0403680e03403c11130f0880e8200280001050041140c2000000c2c04504046001808004200340250314001500a0100600f4452110030030240a000c0300d1a80c0341c0c1c4101415034502100441d80c09050070140301c0190410010751071418010031000440680c88c5005034007d5100b440603000c62851401004440c05018020f01040c42c15140540c000540180548d000c1c07001c403600d4041c41e60215403200c50b00b0b004002507400b4a40b11520f10003290711000c401001924442c0d103030301c09011502c80d14211405140540c1003c507040710000b08072510380401c141c2c06d0203072000b04800a41074880d40031909844132024214041000b21208003541421501c1d60030354014441410480c62902342c005d000c00355480c4900b507000d8080e4038102401c1c0140f5117841141c1c140094002e001c0040c21002940d5a5807040c86542c003a4003031a8003150035032503c01d0140b401808a42c0e60709080605103801c200308100040c0820003588 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456202607 1250 456201357 456201367
    0x2013110d1410060503150108040501090c080f07090203040b070c11130207110d03051c0e070b0304121403010303030f0902090a0608010c08010b0a050a020f0601090204060e01030e0a06050903 83
    0x140c5800740c80d008040080071000e0340e0400c012840c0003051550480020301c4001d00410201108916819091a80c02d10b44501e2503121410b10a0042a20ad600a07000796441c58002c42e80d6440001c18a01d0342e0081002c03210302956032411007040740001d1740c0045c0900d42e110041072070316100f100802c1800340107000d18414016034400044544800031a84190690046030000500c02000069a56071a00340d4110016142a9400500a100d10502a445840b108000303a445241562040000c0c46119003103a111380d40311140380c01181c008840890f1113024000241056030f100700220a0386407111580035046908682c2d058028000c00340b082c008080e501c1310b00c440075a9500620a0041c450440300103403941c2802d000d1030079526500401801c0c003045e0300c0100102490001110440079052602c99201c0420900c2281400400582d0011074401d00c8004a4a950300b58010403c03a0126100d80010300c200030b0040d8252490511110078941142380b400001c01e4154018030361255044041d2803500d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456203857 1250 456202607 456202627
    0xd110d0c020106090c030e060a0f0207060207061a0307031205030c0c100504020a050a03030e0d17070b060f04050405030a0815040e0102090901061b11010207120b04201311 75
    0x982210314080c0060791100810400c0e0055441001e907000380c103240902080014031415070382d0b1400075001c4204142d54407000c41c4003986a60585007810303031003c0250b644440904100018082c01c03125003100608081e0048002c0c54001081c50483c3d034858035a500d00c0c4203a01e801e840c650030041a01c0d124401c204581200c4030030a100e0031403a501c01e800d00203040d0a203401400340707482864100c00d0003682c060302c2c28400300c0d4000349101d091240446450048800a00d803000c030004411a200e4041080801d20342d0030400010303036107441103a098903880000060041007201390352054a010b0300c1c0740c0080000d025891310820b0b00c0d44c1d0211039410900000f1050314080340855001e500220410313517001c511100710b4906a0f100e60300512491905e80d0190156817240140c0ca0b010040c01801c50440390000d00036a4024042035008125688455105e8002410480078030f80044034201c560004807405103031606844d00325071000c0f40010f00170f0982012020107043c020b0881000204e100c110503c003050344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456205107 1250 456203857 456203861
    0xc060902041d070501141e090a1d0a1b0806181602150603071e1a0903010b030f0d030e01090524010f060c15180b090d140d110d 56
    0x58004900b008201d44092a44035081010a400241c1004500e1803640800301540082e1594905080d110b0b2109010402440d503552045601c41500704c140c40900042c0501009011084450b200d0000d4141c0c1e51340504200c110752184c02c40c40c0d50342c1107402a00035011720a00f2020b0744007102071710a54131402900303102c0d07001290490346611205040020b14072425410310003194262845032140521341000f40001340c5480309406003800c1401000b11050340140e001c24140028846c0203000003290a00561700300e000d501c82581c00c0d00039030902426a6984c100001c030581041f600501800140790501c0b4100c000d0314420710070040759034880c65508003203502405010665444040c1c03405400d862126200100238050f403141c410449040c000300aa160422070a003107460f4412600d8080c0030b00c81010400610010079240150b0031165420b908205400c0d01c002d016030031100450b100c4021607841200c110a07400b100b0341d440b5500b8408680b1408094129403204412443d074103003096030351224401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456206357 1250 456205107 456205121
    0x1107030c0311031212010e1503120306010f0203091509130e0a030f05070c091a0616020f090708070c03031e0c080105030c210102090603090105011d06180919050304050f040e0a030c06090204 83
    0x2b68200000c2444003542e088803070640202410300103113041861a60010344200c2039004121440800007840d5100d598510300b02c000329529421081140001c447c412035030b5004141800c070003041d442c901c6220400d001d2010303158aa94003281c04258030f8103058035007015001843c03400300b4200c101c2d86070008540c0c4543c040c05907a0751034071080003200707140e004000c407030104c2c00c40450040c10301e2000d02c423000b0390001d621a8002030030b0404550303580782d52030220002c0c2801600f14169581d990040d17000c5201540240310380c0e0f2010740e5004000c0e43c94400b050345400200e055507030b1001110f400c8941c001016120420112082000182000c06840101d41d03140c2c002c03200c05010380d550300c00602c030f43c1003c896079031150545561600a42d2401e5030200d4211008090144144094900041c545040801079034982090725004400b5139105480d010796039400c1802824418002c0010710500c41c14140f040425080101004000429140d00c0669403622000005d42e460b07500c500300a805030b180c034002c1078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456207607 1250 456206357 456206383
    0x315250905040f050f0109021c0203071e1709010507320406080a0c0203071104180507090212181f0b06070807060b010c02030606011107030c0311031212010e1503 71
    0x20135a4a05420341c11403124058118080d020300c1848109080c00841280100403000d004006a9030349940b4420b60302e007190301c8040075038074020401d12041964080e00303210301210441c0c030240c01c0740c403440402c3e42a5882150706600046200324034654581030540b034444c0c451002100b407020f46200304040d15607940640c001d000824210300034030050b000503206a2582060311b1020314180b600c55500d103d404c00110380b034148519260607006e51045600d408105004ea03000f800c0311880c03a51001c01d00003075004820128a1058004000386041c080c105a42069035080c0000d8043d240a82800001036155a410010740a0b03640c000a240703a01ea060003001c00354000d00351981c607000e09d03150050a030b980d024046410000311881d20001a200094280c0d00080d00f4244100383d4154404601e24100050b84080d02c42d1b65102000000e01408034480f151a080030340666143c1e14159440c42203c1c444e92004101d91903050004004140c009480380c2d402c07440a600580c020f1419000080c60940103400d14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456208857 1250 456207607 456207611
    0x1c0b070806030d030e0303070e0319060c020706090503030a050304051612120512040213110d06030605130c0303050904062d052205070c0c06030b0315250905040f 71
    0x30110900c1c2c00c00071640e888107546000d0182814503940140c032400054010014403100030a40c000f240e406008808240c4540102400c90001c217051550213080c200c3c5400d00035008008010030442c0c81860007a090b1400900150b2500c0c080e4181120940c1c8002c0083ea0745d8000c0740d58a82582c81d00d07903590030003450312405a5501900c60b052402010841003001d81c14081c0800507118000088508075500c2601140c0d081821500c104152014042484680418039800901b8007100706103580000c007030301e0280038100003a0346c9005d0164000c42e0340c00e401501034000140d0400010388107800038400c221015002050352980c855552040c1038026615441c00b5113207160340702e84030302d60106800042c1002c035241035811060905d26112407000309000e44002d500d400000e003030b681c020075046800951140c60030f01c03000e50f150401002081e9a501c078a120703001c1c1085140150424402040c05071000c1c0104800d01c20210034281000c014203202501030003080d070400110343d0780f80d104550f1402941480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456210107 1250 456208857 456208861
    0x70501020c0a080c0706030c0c140f01060902070605060907080426040303020a260d0e0106030209090604050d0212270a1401140f0a0c03090e010b04080f060403020c1c0b0708 76
    0x43c1d41410317002d0300a030301018500308a040c0d41a601030712809003903400c0072190015019800d03420b4141000d850f5074400e203608001000611455960081a0725030041404100703a480324070401100d80b84c2a100c0d0400a0700724008500480c210f060a00c0d00d20308000c1034a02645070b800d83c40e2034603030001d41c41a005600800004030a10110f14910700d81140002051403102548001c0084a401203550303401e400740d51a8200d801440d0300f5070121000c1d42d0001c000614a18040940c5541c460045604485500440e00c24014481c0000785110710a455502c4207802e29684881d4448069210040701041c209900d00d451151346a0280b60300291020b0142c034841c003c0c040d000034041400c0076540c0000c0364010041c402080241c942658841080ba15001c90100c0e0b141c10104e8002c0000d801001c0300c103103a800002200304c101c034010300c1100c5400e0103540c00c9164480b28152101000c0740c0190140e00400710760003807881c108019541c4c503105126110316003441c0c0d454803060a00e044a08c840030401103c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456211357 1250 456210107 456210127
    0x40912020610050105041e0801090606060219170906120414010c020613032f070302011d1003050901090c030501050708011a040e060406081501030b16080c070501020c0a08 75
    0x40915440004802e000d5101898040005c005204611815840070b40300c5000200c00101d81041c00c0042c001400280040509814600014101842400c0c0075104051103004c41130200030301995000d4000b13114503080e9140703460303041032644a40d0003240d000e40d0400040c034200a510503414084c034050f484d15200080340242031800c450407a4010019580321004004181d25402400c008980d4180340422076003603030294400d4000300d4200c001c0c25541d0703c117046400e92440000c2d00030031a4002d0340c1d038003038211048000c0240119804149900304007044160307007a0a00030741015400002c004000112850561140b0305044055003049856944990a10910650100035240504008114400961105003000107244207910910000b98084400140d040e501c6034030900081082c3e8080d1341140313410300510810b24409001c11280704403460041a080105102009040c0742c8644079510903480c0d1403401182a00446401c42e090340d000c00c07400395400000c1c010104018411058291144000a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456212607 1250 456211357 456211363
    0x702030313080c0a140d0201201b040b030a0f02210106080105010b09010f030504050a080c0c09160203070204050a02040308040e010e0606070c030b0601121a0102010b0607020d0803090a0204091202 86
    0x7a5103070307114144c0204280b000910b00c214080780703440c04940820200a5034401604c1d0364010034078808039400c004803401c48a07440032418115103a106141c44e80403080000421003203c1000260b44d403da0b00480204000482080401d01140d000031b045910136120180361250315404000602d0b5141d44641080111041c24001d050241010103a441d041c00c0d040c0e8002041303080c81c1060758042640314400326007800010310045002c41d801a83c8103903140b00b42a0348996032007c0706100342c010850200050309850300b0f410808258481039002c1c510740a105e07000c01001d0200640b40c90355081d800c010000c009050b4000410061084180403282581340640c441d611910080c40319000300001c010301000100400300703103800d5031780c800809455034440000481e41c0400c0003d91700c005a14280040300c3c03911003520000800d9609a009100d00d613090030601000c0c0c05000002504603910f400359a000031411070145a00c1001070003141c90303038002c54001800342c4e066404181c1c4c0100a11410500d425818 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456213857 1250 456212607 456212623
    0x9090604060303050702150f030c0c0607020c031f06170606011713020d0609021e1005040311061b07060e09220b070302040806250206010e0601030b06070203031308 72
    0x44504100c00c5181d62800ba005110b8404024410400034900e034000040c0f01c010f840340d00e238078058030a440b46840d015002242c0d0120071a41c00030702c50500086c010910000d10b00c05d081501401034607109020019441a0f8078164000fa500d041e15000d010a103510030b80f4455015200d10781c000c000764180580094884040c081200781010799010401c030301a00a00000412980d050340e10050408450034a03900034482e401c0002c0d8481041030100034400010024180300500031034500480951000050300c007840b0b1840010a100d00d4000344881504c0c00e54041d0620360900618404900814200e05040c99410340003400442d1882000c000182062004264800c08403840300072094040c10ba90b8090003046440103020021103400202d85034801c0c0c05403001002c4800444240d402c0c10040441c07004082401d20341d81141d03081d0b883c1f041034400950b507412103007580e0207000d00d500c8034001100034000444400f900000308000004c0162020001030480401031840c84c6030041c2040030040c185a41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456215107 1250 456213857 456213859
    0x606120f12091a0a090b07050a02060a121a040e0109031b0c05030a0507090f092604050a0b030a0b0306041a1b0301080307030f03110f03130b010b070323030402040507031b05090906 79
    0x5224241c006140089c03400e090580440c1c2c060385500b01044201e602c6000344500d000218201a400240d0b02507404005511794400c0754203004800b001d00c540c0c0d08035100e02801900040b41002112005c4002032a101510780c01601c1850b64141c641c0b010900c0c01199074012100c5a0000100b0411807003e8418019407614a401c1072041030884e496581c10103481860541c9001d412024508580e200e01003140c00504028002040b80d0707640e4002c462007504211403d51425003400703001206442d01003041c510465000c04002f034560880408071036001d0000705481c40750702c10000d4489804006a01940c020100070000b50f46e295078510b0020041c0041c140c00c41e05041c14103074100411160003003960b940d50080e0702166100e40d10500c56540011000d5405444082038000204d04920168010419503000b901d6454901c2d4480401c1d101c102c2e2054407006580500344042001443e04e90403054125803949404100c2080e1107500c40c18007034803800210086000050590201d0a01038001c80c0e20900c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456216357 1250 456215107 456215129
    0x61106010e011401090510050c3a030905011a0f041406150d0c02150f010503060c0a0c020a2408090304120311190606120f12091a0a09 59
    0x450500401c0305a40107004115400c0304107444107680c1d9203c0c1e01400002c046c024841141c03401174240117040c99000300c144400f203008022241c0311403100e00607060341910301d40d00031130076a104001503820384240a08a5038200750b284c00c2c1180200d41c0900074a0311800e01a5100002202441c0800414646510f0744501032420302da0154107040c000400c00c0d0f4070080036101450202c982901b0010284074440c1c440e80c020b40342c43c0d141015954001041d040c030407818200c0600d5515410514020040248509545640064000f4080d803251601400d040111406c0028400840d03a0000d00000b0450300502100380019800f80f07980c0204003030b5107584007030380d003485681410400b100984074400c5010301802e50714202c850008151203200414070401564003910201a80703000d22041000b4204016102142054130115010056840b140d4104e58005444000402c03e43e41c1c100380003072a62020b406000e10143c00044444210701144004240010115581c09541c0c20140c050705c02ca4000340c200d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456217607 1250 456216357 456216359
    0x60501140f0d0303050601020a02091504150305061b0403020d1101180320191e0b16060f0e2e0b0901270e030a0201141915080307080406110601 63
    0xe00e502038100c2c12180c0501c4c01054994415005078600080c110000f50094a064100041a80010310861112004840c240004c0001207035102000c50750b800f014110782c0049000c5141c00c80d09400d002c1920032905e420900b0319540381c00182c803444002900303503018808000b814506603840303000040a030123003600c072401550454850524002c6000114510740506000b1080a0355480301c103038070b003605880c0080c00c001d901c622144d5088aa24810160003006050005c180511414245d07004400d08007005c185500c5a0340314200030f001d034201e00704061550b40f84000109042408a20b10300c06807101c0c0700c00c80009200a140c00c0c0214100d100011703030301c0c0110085080d9a0394170041e0440c2c4125540c04004c4143c48510700140305012078118589203801440070401001002600f6041411340080281382d48401e41d10901880890f040361080b034a004c90464103000300d0780702c1140d0045021a00712840c1d150100546103512240094a40f08070204041001c582e00c038a01d15800c060340000361880d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456218857 1250 456217607 456217609
    0x110a0305040314190c02030f01050916050a03030f050d151d010e070c12020705180103021908071e09060308070b10080c0103050411150301090e240c0412060501140f 72
    0x34408003000008200a40b005c0009641d400c01c08000401d00c0103000304000d040050045907202207423241e041074080b50081c002130b5480c0111002080381d40685800c805000707000b03c1107540383d0140d03901650700c80d5109000e00c24062501c4100d00a458a155090b0084415102801c50134505074003904803603014800700070740240d1141034032500c250301c200d280800d030a601c4000d138109070780c507003280b41c10900340302c01c0110807901c2072510307412039009031184501004103160103565540c00e4041d600741c940c03002104005140c855504141c000c50034000d80a801e945440340981030362a0707688160740401e4003140c03000900145140312074009256458044105141c00f9030140c9071009442c105040c15a51f000041c00c1c040006910054881c004100d40880005000d281545400038054441050701c0c1044401891900248a0701d54084500754550303015081044000c0381180106210b13035a042c00e1100054100c00c009021108520810012070301d9030401505220094920320b2040c0325041d000c2300d551003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456220107 1250 456218857 456218887
    0x1e14072a030e0a08010504110108060105030403090b0c1f020406020d09080714120a1b06020f03070f03091802120630010b030313080d18060302030604110a0305040314 73
    0x3145605040a22454507144009010005142c1c409461035080408001c06c101c0350591980380c240003602c0d083e03982e40b40e5400449040c04116801004156031401c04e110404410001d4420010180c0464190701c4085550b000096510b44842401e9500400c00340441901400100c078002810301d000300f40c030792404080b16a00c82051052500080e480ca50324040e6441d4051204020b003011030032111010014501003205900d041c0c06440001c030003031000300b9103c0c07011600d0880342078090011420714180c0d032102009181c00c054102c052080010f00041c0400b84910880060a20040700580394201d4004a550406000b440103100d1207a205001c00b0b040400080c07038641082ca000c0e410050031148594600610030340103940e86c544004500035002603100c40d00001929140d0043c0d0320301460303105058450841c4141d0076040280c042800380903483c440e0740a5544400010008a025848414510203650040f8000780009842d03104100505800107400516084107600381880c003141c811001403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456221357 1250 456220107 456220187
    0x3010e03180402070c0e06011218031d120a060f02090a090c03090c0f05040e0f03070b07030921021501032d080d020c0f060c0d1e1407 59
    0x1e001000700706166041d1107503030555403826406031104019985801ba9910214011200180041c0c0400050710000026000b441c0c000d43c020041d28000500554081d60401c1d000b40c0c0e04860036260b41c813031028076581c00c2d4012a141701c0c8003000d041150580e003050700170707549401c0f00d444100d8010000c15a09860710280c8500305d41803042e0004880780e00b020201c000c9e044009014116240301d040100703840c101190300004403070701298104a00000000142d4466080c0080100f140c1c100b440642d0110b0f204166241d0300129034a00007501a02c103540b00d004052045010401541d0030002d5015010340400c00ca1403500b142130340005166245d07584609101c00120088032080e16401d20000c840c0c011030b41d05421540d84005400d45800700c0d1600500290400c07494080b11b803154105852a241e0041482d40c05603c0e82401c2c5803a00c0d400c0001440904989180c0645d0300f10b83c0064032120385074500c076000ca030f110400101c0c551030500c688001c05410b00c0704002190014150f003450050600e400241c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456222607 1250 456221357 456221377
    0x91507020103090b070522050a030303110408010221012103110c1309020a0f0303080a0903210b0a050102073515040201020d0504050d0204050417040603060e010503010e03 75
    0x6a488846100403000b42200001c018104403258043c40111508500908441d800c1c90790800b08004806c8030800f500c0e000c1c0e01c6500d400c13a00942060000c07074442c0d0409083c2c0a4845040c40c60180d0382c403801d41c03c984c08a00c21a5448019a00103440a2082a030b240d0040c00d5840388210b80c030314003d20040b107100d900d240050a008c01b550381c00c00180d50602c251341032140000d00c83c040c0700d0320030801c0801a180541089104845110f800b240c075520358542c500540750140c2d9000031302d0b6111085940101905e5a0580502c000700140e440c01c0e02124401d01102d0104002c0411240e0f0040c090140d113568507044076056400a040c103024040100450b00008081d206100d8001c80c0c880081d0880e0104e4103101c280700340584846401114488608180903d200380e0854010b001c02d1102183e06025500585a0000011800c0740161405410694125001e0405010414035002040e81d031070f84203074000703000b184d1a070404200c0715a00c1403101c1d005007000c2d4020f001055603120740325241e10440f0410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456223857 1250 456222607 456222649
    0x40e040c0623191223010b120403111203041b06030b03030a0e0a030209100303090b09060406030c030609050a06030201030f05040b060d030509030a06060509090c06030a020a0507050a12110309 84
    0x700c3c82c15072290041c90010100c0c01c10030002c441c4074061150100940201c00c9220300800c000024070082e4400440340c02c0454074000b616192950b940c205d640f05000101000b4500c034107032100c3c55000b140300046009030f2103001c1400010448100d0001c1e00441a40f09005040c5018149501902c0c080b003200c4000d01d4601e81140b101e241d0b034002a8206406400c003135005030420b400c02c90300ca14000010800e03280a51100c07101640d903162141c58902c00d40070641d8209800703000c10400e00e8043c2c0c002c107060003542e080100b41b2640f20880001229400c8500402164a801c000c10555030180709062031a1400c0c0000d00c240e02d42078441c42010b070b0000c3c04490040704190694424144100c098680600300141500c41d02042d90a2050107450103004040c0304000c036001291011000046000c1d4044c40600141d040d940c8081012000b0740100602c4010302c2004c10600c00040c905110302403440b84101d6070070600896003500200b030b501c607210030039020f54030411681c0900c1c0c0c4ca034010406407a00e14010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456225107 1250 456223857 456223897
    0x1006060e060c12030f0415090c06120e161409150607080708070b010e0c0a02070b090307080a121701080601050607030c050a122601140402040e040c0623 67
    0x110514122240254032003a0720080284401450005005c81c0100c0c010150000d02011303001124044840c015402440c2c0300c0c0095040242c3c9001e0803545550070200300000601030004a020360401e0a00416101010309a01301400400e074480c1028031001c40544800e00c2520341780c0c400250218480034814803e00c001708001c010042d8410881d018180d0050b0055240c542a1034003400c1c055081c0507114400d0060f03400140c203080001c0a88030540620703801040c0c0c2501d08006d08106500c94488503130540161480440d44003800c105010390184143c00304030400381c4001008201a0415881c40c42d45a00c0d5001000681c900040141c152101101d042c1e42d41c1d0386625094820300600d1070000e0040c01071140440c142310190740c0b928841c004644070400720b505203580c4482c4031940e004130f03140c070740242d00c0050000301d40940e4030210524019100500d0251070383e16010035030304c0890301125200900c11081c00740941c0803105490402011071400c0ca5200702030012010ba00640030350601b62a8881d80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456226357 1250 456225107 456225127
    0x809040209060d0905100e030307030b0415060c05100603330f02090a0e0910050912040305100b0402090d0605040c15030b030f0d14030705040e0106030204081006060e06 74
    0x30403140c40280050000d5a103141d420100300107000340c0401907a10b8041d0701307100c1211100e640502107000b844170b4061461a0380311a070a074000c0c134041c90300c1e5420a03581d4a10085100c0d81e690200c002c4c090381d44662140c0602490047e01d000e00809c501c4a0b00c509140c03081002498400004020261159004042c0c20410041425601e075a800750074a090400f090004540b94590003000400390079102e003481142c80d20803208503003400b50f072401041e070302c40596000c07030b10b5050380919044900081039401034224440c054855400540058032039811002c0500601c0e0390512600d5803600d4165429801c0005160024034840c2d503a00c1c0280c2030b0780d15040002e0802800102d0b030300150003a4924a601200d85000c01401418a02d003c58024410340c860503800020001e40000d001e500c0784c1d00c44a503402420800003460700302030102000d20034140000b24005e00083c2946020300880d5600503241c03840c1485032451701019149504040e441e010041c4202030f8048508100c248082d1141a81d902c0100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456227607 1250 456226357 456226361
    0x2d170c0603040311070314010b0904030813080706092f150a1b08040f090902060301060f11060a140703152c04050606210303011e080109050f0f0d0c080904 68
    0xa80069007030217012404410440138450003004207641c18002c0024004200901a1051f420b981c042d011501e0040003038210800543c05403210f0b4401c0e0744850800049503198415604410030403600c0e0000c0d085a8140200b503846103105440e048100000580c98a83c00308001c40c01640c01440002000241d109282d805005038808076440318480304010041810603000c0b642142c094900b40b0f002132940020b100099006070990684c004003145d1541c0d1030302005994445500003008180510030980144a8130240102441120407620204044282402c1c000154800402ca1401e05180015104008043d201510161414544c030962031040c03582c0c0466051110455440034142035808200c100100880c804d801614191880e07040070f106030f2084a60110f003103150118980c03041c001080f1441c040304d42040c4142c1e0300e040602040d6201c40c2d00d1829141c5801041d1900e03400742c40101001d4000f004010383c0d520600c030213444038985c0c04030010131107002e03c000640111008a0340c01d150366555 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456228857 1250 456227607 456227627
    0x60106050909101d07030e01091e0f02180106020c1507030305100b0c0f071a0a030207030c080c0105061306050d020d051006060908120a0504030b09072d170c06030403 73
    0xf040141c0284c01c3c61428250a030007140c05d100028200800710a41100501030405c40c0c80d8008106610200c42c10440050b0703141403030040ea214000b1604040258407841100d1800b00d1700301c0d031090015070400d0f4010340b510210310381c030701c1c003601c1100c1d14400307410070080544010590601d00410326440ba4003800b1f59011140d0002041d481c00002c2001030a07000046107081c00343c501d016552401e079600d48006480c4a0401c003280042c60820030080c1891282c2d00410080d8401d0402c41c4040206844104094001e82d086c41c589a660340280b080c0352801201c01c42d020f41c003402c2c0611103a41418040340402c25014002030080f5020b11100c0e003081030034041f81f2456038010004020700b59440e4001050403119128800f001c2c042c401501e49035031b0303140044421482840c0c85035483e1a00d1680c034403001100c02010741300305000e611400708414101d86245003140b000c01442880d00200c0720400d40c00e8401a50001d0710907103640c4022658040085a04980c00004550381a265521030905403a51800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456230107 1250 456228857 456228869
    0x20409060e190c080c0306180f070f03021e1003020f0c25081204050d14010f0b0f09061f02030d0608030403170a0c081305060f0903010e06010605090910 67
    0x1c41c1c1c2c142ca010b008048088101601074014410015a00c0011a4490060404c00c40e05504445d0000d075480d942d00326024283e448840c100d805031000aa40c5034103010058200c00d640100384003041003503180c60400b40382d1251282d0540040340b1680400900080240c9142109140d00440d204045244450a80300041440d80070358081c0d40a40001c034a4008441d200d0b051105035180010502c0e100000340c0c2100129000c07200391416041000300580b0420309401150400e01c466640903c9040a0041e90b054203a43c42d80401c050300c009017005450001d030310f001d030701900711102002561303a02e80500c2d880e107110b20b510065117951903102c102e0441c4281c4ccc040b020014245080004c01407000802041168000d0038400601c40d92841d0030725062203060b0f896000a0412043e08010035078002c010014000b403680500092682e443c086595a00482440180c803e03005c21500c042c1c0c1428005c02a4070804c000c0a08003070760419101030254040c050207035008100c00000240a61451034440002e444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456231357 1250 456230107 456230113
    0xf080601090509010308070605180c0d11121c0f021203042307050103050a062322020304060b030c0303030c07060618020d0c0e0a03021302041517010b030c0403020409060e 75
    0x3c2c50b0305150320700d5401041f0488409140a00080001010f02410154004000040c0811b40404020002c0c5035664240c1134030520304010100c030380ae86c2d503030310b030500005000e04c0a0050380c03540b03070740440c01c60600054620a0042d5141030243e1540c0c0842c42a10018800e01260b84079165801d02d000c080036003215050391a000804401055840000c2003812600309036000c0c0216982c503000381f01590780610844880c0000084c0064070000040c110310f0000700080e0144086021030400411420701110501018950004c00d1200f0300802e40524420180168010302d50043e421020039524840189141451000401c01100300034494000c54000c1200740483d402583d20300354100001c2d071000780d1001070030b45018860004c8501680c901d94440c03000070000b051b800c0c915001c0c80100c000a851907840c056003007001140c0d041c0ca500d154016020745545400714400c090a941c1e01c0d80506070001d84e03552209104001d055402c580c22501945d60554010402401616025029090095000c02c10380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456232607 1250 456231357 456231359
    0x15090601050d081b0102120109060f030b0402221a150a0212210f0a051608010911160f051608070306090f1203020306040c03050115110f070b030106030e0309010f08060109050901 78
    0x60a02543d230580e000414200443c9a50300419202c0c5016407000a03c0d40c00c0e05000280035140011801c54078810300b461940920809020207402c4079401452040c1c40d0b2420401d40700f03141020160110f11070310610f91649444a41100a56600d0ba80006891800400100090b0035a058504590086c0c0b042005c0007603800d100c0200c90412a046030700c3c0d6085450140001e1000c0040d041c10240e1117820340b03824989909101900b00034101d2004280c107020010440d110110b0102d07030000c03400701e0050b8400354801c2c00d20f1a1441c20961182d01401c19050340c11000d002c0c5960216a01d001c0f00d0b4001c0340003840203414030380746a4078801c240c00909080f10460a61203a507806400440c03060104a4042040d4017100c030080d411a502805071140840e501c085414846001d010004841d05d0490100d0b00b144c0411011503180030007503045034450000c003100400610b0740601813500c85100e0440030b9414010308000090241c09409094020441c540b800b15000d640104002009850054000c4200b9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456233857 1250 456232607 456232627
    0x30f010f021206030a0b010b030a020903060a0b0102120c07120201110303071806020f0a02060702061905090f0108090c09070513080708060f040c0b1804050915090601050d081b0102 79
    0xa41049151141ca881d0240003d0018034020541550041d40b0403100c0c0c5140c0d0a0a1100e5107a8000600d50007031268200f22401141c1e070704021075481a00003640100d49081504c000908044003a25501c0a200003030081c40c1c441c40e004201901961401259000442c1407400104d420452103000d0768024000001070100d1250703c035428080030365500f0084040150340b0102280c0d500c0d51814110a5034001009a60061038940b0090821038002404942030110820118948051350aa540082140040d11181c07600b0015840c584644007401c1c003154602e48030180546130940c031640f103449031103c0d80000d10f003d80250150b40c2440b40561f007003404503446091083d0b403482240501c20130384c8036403800281040420105540303c0c1d9440b100300d20310341d854115144132903005041881708030014028141a81e842d42e1041d1842000c0d41001483c50564406100d03400390030240501040c0d40005005200640321b86210103011b551180c5581d540b00c8080b401c220003110240740841c65540001108100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456235107 1250 456233857 456233861
    0x4060e061503070906050304170406020d12090206071101030f0e030706150b0405011d04092009040305090112060302090a09150605150f070b16030f02091806030f010f 73
    0x12a20007500d1964810103000d0003a842800112940c0d0f0004020f10414050f040c440c070003454001d489400ca00300b404460b10b80b01c00840e04190000d50042e030054000e090748aa01c1040592030020101041180ca0026008160311f84a40c3c40c0261240307043d000c40c034200ba4485e500c000c81c91001204104404c1600d1209240c60303074000d5000b6240742d4100300006001a41a12000d0200c500e50107001c0d203014078140054a51030f00005400125021030030884c41c1948982c00f4141842e4490254100910700d11803815800164410000e4060b4000000300000680c00c201211055003007400c107040859542da41d600e000e030440d5000290015824024000745000356084641c50911402c0400a0840d01403c140c084070031a101e02c03a4414075001501001c0741019000717200e4000700c00c0301107207403010359260401c0404050790920800d2000035410400e0702d038076100d41c00500c1c031180c800f91318062044001032682001440c0c8181b1807490400851043e940411001a0004080d4000c0c000d1626003825400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456236357 1250 456235107 456235111
    0x60503060111070e1b030f0708060a03063603080a02030603070807080c030105130b040602130b13050a050117040b0a14040809010905010906080411060c030c060a140f0403030b010e04060e 82
    0x200c610402501445d89480803400e6030305c21f40c1800c4c1c0c40542035079184012202d00801a001c0c9400102950f00800424458001c40d000003807142c850040d00303440351404040b00134118003030220020310304102c480040d91200c040c6401204401e405a1251a04000a41400301c254419003e51050300d02c0010a0f41c404201d031002d00000b200208059503d0801c1d0359030200c61000e009140110540000c0c0005503145c0c09400f100d00028a41c1038069150480860305910801400005c80e4500400304400e03c0c2c000030300c2d0f010704800e117481e000a8200c0c0814941d81200030b00001d200c5201031300007440c2024203501c443d284412038034040001d8205400d104100394010011a40003070000f20001c100c550040c5116400c5820a41d504030300c42c1d40f15103c0198400d03081a5956000804002c41d0a10120130400303010903c1103100a022213041541600f4221001c0d4200c02460a030040200601c40c1406404194040d8240c240804c0703401c1000300403962250a0340d50668000d01e407140100300000c81c14113140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456237607 1250 456236357 456236371
    0x304060822150c0c060c02060a0509071512020f03040f060c090b070807050f0d030f0e060c040b0a020a0209040605040209070206060616030203040f06050309070b090901060503060111070e 82
    0x6004096180e2031204100e00120016104075566409004080700503805011002a0384c030300303100c0c1046295591800d90705040114401a071050060204000c0e1078401c4982028090000703040703551900000c00204281d404280c01409030600e8802da170460107404a4003032107403450140e41e50785801c3c170340342d68615400786007030300c00e207203810282c61610340030304042025900402c51003803c01c00990f481856540c400c060032900d034040c1304010705132404200405981040b280c0c030049a1802e40b1440c04084861051100c40c07aa0700c58014041030201c1a000c841c00e451140d140190b0312180100701360314190314a070b0025005102c10b0200000d204580c0d00c86030080b0f20032201901790391111001260303600d0381960660341c0140d0803c02ca40d1400640b511315a10070384240140c9080a07929900c500303140c00a5403002d004241c0000800100c031100740401c1e8050850360042134101030314200401d0068105001e840240540003010482d00ea0155041c3d0f8a8800d800d0100d452207902d0380340d1842c075108180c0350301c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456238857 1250 456237607 456237631
    0x80403140718020c1509010227131103010b0304051615121a04480908032d1602030601060302040b03040f1a160e1806130e03040608 58
    0x244104203040c02110740b0b030b13280384006000050503820075403455400036010800941d030800407003260309049990044c9181c0744036045148403025000340201404c4100b171180c0d00a15040c8940607042054040c2d03410354290140c0c0d103440b03907207501c0c0c050b18006048545c0c519050010400244201407044444101d401325543d164141c4105070300c0f4800d640c201e024400c0a00070800b400b884600745a4401d40b403021a01d01c030a8401002c03900c0701e0100314032050348007280520411250740540d000350050f9148620600d08452001c2c6031a003070035124007030800807103128800480581500c0383d01180030f83e40e02d00c007505000d85e40c103524031034401c241c1e450002c100d010740036000c0006040c074001c0c400e83d4112075007164254650382d20383c4e488582da10810070048460b800b00700006081400441c903c1c1c2d20400040020110131001103c024081101d081500c91140d80c482d412001081100003056420500c140d45400101401d24840d8015001541388e0b102c10f03110125002a031103a00001842c003500a81c980 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456240107 1250 456238857 456238889
    0x9090703061a0906131803050d050c0301050d081305100f02060f1614120c0d0b03010b18130204020a0207090f060302010c03120e030d0b011209031b0804031407 70
    0x141800c02440078589941c07064240001035850300b070a2a2160b17240210590002d150418003454001d58142e00c10250001070020841c1e83c0901010700c100c64000012400442c11580b400c00040c440240380200100300520204003900302d1249010120060307c0b000300940c901c0300204030f00074a0881c02c0b03001070300180b080401041603c000d440040380154840e000c0203044262000095400b000740d099200507581e020408940201341645216011f0400024642d42d503010361040d0005070f0304800f140c207100364503003035001c42030340d90b10b028072158031040c0c1c2103000035540c1e031040d024a944101140030b904140005502c0244590102d40d000075507048c130038104000c0300c8540a041c01c490080c0402400710b010340c55002c0101e40540548080c2c8005003401241c0500d00e01c035242d00719045100f40300d0031192613600840b4150380241d403224241c0343c2e18604200481083e18002d121141c6250780b0ba0881300c660b1231500034400e80b40220350265800405100c00c050031840b041d903492440c5c1c0b180d0042c145d07894013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456241357 1250 456240107 456240131
    0x101403070c020f04091e0c0f120b10080303070c150c0302070510021201030b070201021c0f1413030305060a0824150a0b0d1103180c060310050f0a031b030201110d02070e090c0909070306 81
    0x203841050342c0740d807401076007035a078fd0361025a10040700740e07803d440c0c031031503545228800091801030100c0300c1000d640150700c84409150591074440d52414184070390340140701c003001c10f0b02840c008904680d0440860102c540f40e41c80181e0091040c615103580310360128584603d410308035042400f2421580c40100801e1043d0100a0a2110161040c409402c0f0f0260802d020900c0703038211346e07001b09004201018040d604c2c403e0328901740a0400750700c1100701d100c8003441010000c4003603540c00b4414491a0181c5d952980025200c80810700400340401004284a017005090394041941c40b01c00c558041d07a2401c00c00c64100c440b645030a00d00e100f44c41404120f940606000b800d5a00920300a000082451309210420403c64203100c103c9800075840138001010942414043d442c1c51021716050740214154000105221030303080d82c20f001548008442098a50b00040302030071640184107004891711030f402154203055600004950200e451402d1104200002c60002c00303c1e80300b25410810310041071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456242607 1250 456241357 456241381
    0x62a070801060e0f100e0f0901060501030501030210180504060f21030f1b060606050a0905060c03091c020406150e0406060806101403070c020f04091e0c0f120b 70
    0x1000303500811954002150b02e401c0308424850b00610140700d00c3c0c41680c1c07101101d1b04064070071039080c0c5443d600801400743c41c0200b80306000c0589800e180a020315819600400e100c1c0000b51908400c110a0345401055007800c80c07540c401604c0c00800501090350382d43d1481c8024002800740044401d8201c412510030224440c4943d001c0d030340b40d2100c1c101c0c9900b1110640c0c0c003008010724600e00d050060054400105540715000140040d031701d800e9120184404020b040b1078454000300d004030410060075520010000985100c00021183d40c07146100c10341201d20312501001c0000c0d00b09040c00300c0452040700d60404000401120358500040d000c01d807082005130340c214410361000c6010100801c0103030521441c00c06076458181407418000c0062509400345030f104680c1d26000910000302c140c02c524200c801c110085000f29020302a40003141c0b2501c103442105d50340308030420340d1314101d00e08114429800e00010051442c4000e200d0b80d8a207003440040003614001c60305040280700241013202c100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456243857 1250 456242607 456242609
    0x61905090601060e10030e011d0606030f2d01090606061b02090f1302030f0106050f04090c05040228030207030305180c190e10060f020d0503070e062a07080106 70
    0x60354a84d21201e01890170720400aa00484800c1095156200c0c80a039400c24002d02c1c503508035004141c1858441a0036450511748050000d500c01c0c2c21241982110580000c1c1c00051030170805480404240c080c003803040750b01c84a08d00204e4650a0450a000b8401c040d4481c40449159848102c9180d10040641c1c0841032480c0000390b110541d0000f0440e0613407075080007607110491010102025407242c00103440c2c81102114a0401d84d19100140100c2c14103451940c1301400035134060008800300c1e581ca86d1501c056010705030049501089410340c544c0b1400c98a4a00b00c5900d0f00b81032614414907004010350701900c42640070170300b004003084244586009c84103604c03541c2405085244142010004c0e8402c90541e0202140d82918000ca8840c2030790510b01c1c051a2102816842185400c801130016000061140255005a0040c0e54056000001c50303074090700c0391504024460f4a4000030389030b070103414003404240b103000b14020101500d1840d0050703060100c0c0103c40e0040e0369410014207913045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456245107 1250 456243857 456243869
    0xf220c1d01061b020409081c110705071a09090f090c010c051f020c15090c0604031a0a060315020c0c03010203010807090504051207030819090b0c0307030e061905090601 74
    0xe10f80d0740307070003a9048000003648a48002c001042800c0261540e0394150826001a001e08042041d549000c00b10f900c2900c0034403004407035403402c0503400e880f200d403a41d0580c0705451504111000c070210215012086842071039005003400b819041410550349070305022500c00c00181304001c000c54056000c0c40aa102140d8890020080b0745030059400d02581c1803a0010b01c0001d400b0f020408101c58107115200400e400380350003401d186000010607162241658080740034400410013440030603418403001203c0040da9041050944602c05102c0081405500c09003c00300c8103860111044842e4008110403081c0304200c03041b0181070000c1500700d2100380b080018543c0205130400410700780744c100755401070080701980d42206084210040e154483e080c06c03000038039900c00300851001c0340ca0203860300802c2d00b502001228403503541e11926100c050015004158044002404544031360000607200021405403103244c00d101800d0744002c1860440c0742c407a01c0c1840b002444140d40006c00354121a1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456246357 1250 456245107 456245117
    0x30b07081b090d060c11010c0509010e0d020f01081f0f1d01060912080c01020705010b190602060403080a1d030c07060216150903062c0d02060f220c1d0106 68
    0x41ca03581d844c00a15101844405100d00414000074028082c45044040b40d081c1c1c662a90f2000fa0000041101c18405c1d007007882000e01c3d6401c10b0261300d03881c0c2d03004180502803c013841d06031103800c40451203800040e2200c6d08011500d0010035409640e1401c04100c44407114036006d9100d240d00c00c1d659070b503424000c0a001460312101008520441d00501300b940f401044560318110082c0d900909983c00401c0c00e8400da9145c484a0f0f00c2c5050982d51110100c1d081c000ca541000e0510344000e4884c1006000903080100143c04181c00850741d42c00303545002d000e00140041844030311a01a03da420007401c185180c018041e0014500c1d00210b44080c0d115280c100503043c00c2d080c23002c100b007404403140d9100704000c0d24075808030000c1c40d14400e0100c00e850800140c1c070110540c0100503030040c110701050740607802c440302c83c42074580c000031003d4200c0e4203041c0142e2196604c56800c02c19411064400c3d0b0100c08498a14050003080c0c04180c059130410903001c080000d0f40c3c0c601801040c0280b2801300022 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456247607 1250 456246357 456246379
    0x906070c11011101091110020a050d1d060a0905030c0a05030619021306020102030105040f0902090a1d010c1e1107030807050c09151212090d0804030b07081b09 70
    0x207054044440e00780300c05041516104103580850303401c5414501046845114a842c4280c03585040e008000281401e84014030f2125640d036902da8407104095442d1b010301449015600440341c03102c40303e074440070780a0003403919013110600c01402641c142c8540c1d4040e020740c0402e1002030821503000010340e04098010700303240d210070031358480310030001c520f2810095083c41600780b00740010899000810305a4005a1a541040104400c42d1002481100034030710305450200113890342e1504036880001d941000503031380390408660403c040f40329440001e552822400e8018141c0008510929a00307102e0355000c1c41d030100ca401d407a1850070703200c0e2007815804900100001944100206921132164080d21024071903100880e4a412054581550102c000f40c001111800d0407203264200210000003007032005c051040e941c0180c49100c8010b07000c0c0c1d004001070402e00805004540081d50f100c1440840f034a00101300820444096412060b41c204043c51010030b215075400751511072000504600d840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456248857 1250 456247607 456247613
    0xf01180512031603200601140105070c210615140d08040305120417010b2b0f060b03060a0204080319020109050609030a0905092224060501080906070c 66
    0x19114004990a2204120124103584a24503c412440c800c0e201e605ca880c00400d1100619034101880c2c200561214004001c4802c00c000711101c0544282425640d483c000e003455281060160040d030654602407004c0042200400500d00c02d09001e14001c0000305803c1d035004291019074410561104c460010445103850280c0100d416544201e002da40760940e0b03aa2040d04003080018416a8640c02041c10054040b40c4482908001c0c0244000c0006514001c00900c1341c415141840c81c0a00c40010074162141590025141150700800c442059400c41d14110000d01100b0b8034507030183c025135000c944c200820780262003c4e502d5141c065402e050084034030b90000410320065104664880d0b105201041c02480300500a4414002869592142c2c14000c0c017507030619030155001d0140310b0100265500d04254215100b0303101d5641500742a00c60070721740c81d8017000d202e0008044490410b21840b00c00c0d1640040f00700da0080e26090010360310f420b401900d840040b40d00710007040c0291446000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456250107 1250 456248857 456248869
    0xe070212040315150905070306030b1503070e06030a0b1302100c050c060f070b180c0118050907050408030c01020406030c1b2d08030a15030c0e070507021e0f011805 72
    0x1322181103403480c080581e240d00c040b00340d45056903407001080e600c4400f40305120b0400e8070745d80d00c0b01580c00440f00404420000c031b651620b0074405c3c00c148030300003c00300310700e0b503014020041010741004202e002424100e4560502200010f03040b0712035000d102451051500a10020b42e036690440d0103011540c80b00802e01c88650300648100404410400070000020000c2407400d01038182c0d1070a0940c01a62001c19515017664a46418148115150107511949140445c80c0c1503480686560b071464a4000b826905030056801c845514000400c0c445030104055002d8400c54101c1c0d138081c003214403118001e8030b900c088115848510740c007940030040420306100880003031607252590400c031107005000528200442c03070000c44000380004140f00420303186d406800d00c20a00320300e0403400246580c1e190140780d40f1301d104403103e00c83c514000500650040782078a0f840b0341c02810032015a418030207411070103800350b803019100d800d1600140782c40794810390300480030b04000031403000e03260f05080c20011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456251357 1250 456250107 456250121
    0x1002070503041203170c030603030a050705010b0a0308070303240302041a06030709080610120209040f020307030f151b0309080405120f0708030322020102030904060e070212040315 79
    0x40c00e48410000061051030b0b4900e5080c0e494040e540700d9100e90190000b4844040d40508240c1e400641401030100c00d60340441105d0440f441414466030333441161a02e603014040354845107030700c503030848400000c0c044a00c004044040c8266003c104000b04180c110440c40582d100d10001c1d5010301000340010308241d80070f500e00046003100511001411070003e20150300880d011400200904020011000f08000d00b58101002e00300c5180003904040213900079184045000c1c1c03082c0078540106091140c1c9a207000d00403a0054140c0d5000364036402d2410341c503091428200d840120005504c3c14100c1d1503c01c050a40f400b0785442070188408003021006015224403d450000301008006229590440c0d6040704210550142060811141c3c00504210b0280c0c4040015001041000b074003003418825031900d00d0b0340348002c001410703103070004034658040c00b50001d8100b07207814000700700020707881c07001486070100b6401c81355803402114101d0b040b8007840c4402060301003c81400800100c81e500200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456252607 1250 456251357 456251363
    0x30b0442050925021b03070b0a0302160f08070c060e010806091503060a061d040c090f0e0102030906040b06030c061207050c031c060504060311010309170d1a12100207 73
    0x1000304140d40c80c11480700b01264071900140e0310109010305c1000803940710741195801203010b848503a180810001092090242c900c04145d4005110350049102200100020b604498a840d040703080f440c1490032944055420f03200e40d036040e0700000b0350030311440220310000c206950f0b07203459441d2482404058031000c1e10001c7e51070b100380c0c400022500d00f00115446220508000f11320300c5c0c0b17407003621200d00b150f2801900c801040b2078100000716104251003821100000c1e030002c1e404d500071303000700001c0c15410010000c2e9400002400204040000c0d5a80904d0084100c8141d9032120810140e03104207000d16550015803d20039120545c01c041040c50340b0501d2410460701d09201c0c41611415035212842e200c0d188088010003039101000d07407040c98040c000a0307804015013815912070900056a032203403241010f403102030203002c100282903d452039016490409403110560040b05002e0102c103140c025105200c03403071a1486180c020f005500070030600c1d0242c0244440b440500300070f58040c0c00e00b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456253857 1250 456252607 456252631
    0x2030702010e1f020307170f03190603020a032301020c12031e131101031e180618020306060d08030105120a05100212090c060405010f030b04420509 65
    0x243c04540510030709500c03419400d50145546011514103400c44080414a102d01940244110071000581d2000c583e00700500001c0c88481d40c0c050418140030b0089600001d4010808420020410440209002e441403802c00385980401c4d00d00c0c40c0341c1c201c0c014100c0601e50f81c1e1201188048514040c00256000a80d194484d107041c066108805655017084d10054407081440400005200282c0c1200019031024030303003070200e9400190103198444045450001c0700303984001d002c406140e45800907404a500640c1030000010300c09034024110703c400000d038064050b07400041c403e0305d443d07800e08000350f5110034442c0c1180d017000140a441481d00510451900c960741d510030100304108840b00e0200d491480140c0d03a4240c04a44444960001d024110301d50301213694188141e48481c103403000da4000f86000b004030900703000d0450190074000e02c0c298125141c109070010840c9000c80045040002c00c0940400e41d601c180ba009101c0d601c500700103054200d200e0141700342d03c2c0107902c075604281c0100603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456255107 1250 456253857 456253879
    0x50f07050c070e1501170601050406030f0e0a05010608010609140f0907090212060109061e030c030b18040303060e16030c051b07060221030f0a02041e05011e02030702010e 75
    0x1034002c2c5000743c1d9010022183c8a911309003a40e40090030340861552902408014103004001802a00607400759909064565600c2c4550007800c1d8403902606005004450141d41c10f4200b90740201107034080c1c0e486130350903c04042440c201600403503c01c03586a012104480d52107032b000030011180a0419000c500580030005100000c038000344c107481188043c484c403035051941c005010700720b42d40e10160900c082c10003500000301104a031031880c906c4a08001c6040d1420301401c4008110141825a000c07502140841c2c1442c0806856403050348130740c804101154441038521301d0117030b08030790107268a04401181c1243c0c0c1d10941100b1380b010b01e01c1c109542042d0581c4001c82007500c9800601d4010b0f40452801c002e150340c1001031034449654070a40801201250701c2120092000500c40700c540242c2c8008642c441c0c2241d4126002042c0d00120b00d0a51614900e10300c40f41c0c24903101d542d0000302200070801c0c2c809000c80d004a1000d8040e0021880c00c00786a0045d50780e0040007054941c01201c40b90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456256357 1250 456255107 456255119
    0x10c020613050d03110114010803120402041803020303040507060806100f121b020c3f070803041e050108010501030c0c0b01091e2705030c151801050f07050c07 70
    0x10f58181040c42600c442034550394a482c8907003100c800c0e03038000c01c8171100741d170041100050120454010901411003c510780e5224004240039200ea10409902101c900c5024000d00d503000c03001c0d6004501c950240c40215a44800c00c840e4075405a650a5000e400d054614100718042d00000c1d13403103080341c200030712594001c050020482d815002044555080d00280ca4000c541c140011104400c1c1102d41d110034504960600340684000103d07403040808560320144000002068219280541022110a02d880d0180c42d0340366005071186c01ea46c40384d0424108665400c8075180c0e8295501030391010b62a0b8a0900110003420400603d0403d20641550740400b083c03200103424040c001d4942d021a5500044411400300c400000c8000495440c181070090704060550a254481c10150b1000c10602480c0c204503040d403060404984191148200003158903ca0383c2d02c1d5441484440c54003240c8180d0f1040141c01e8960403103d510540c040e078000990030a0150b40039004400c00c00c0115141c07961150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456257607 1250 456256357 456256369
    0x50d0b0d060b100c0c05100509030607030c1b03020a030509130e060114040204080303180f0a0f020f010804030210050702010608010e01140606130b07140a151109010c02061305 77
    0x1820507281c45880340324034005400c05011070780024000e0f181c00702c0d040a41380c0321303158000c0041c0202c81c415100389000c81714580c400e1050b00c0004070003c003504d41c107003081303034000e0000e01000b43c7d41804a0540c5001120089003001c1000040c1d8140e00a018152500d0360101c8169005046003503214114209402c81040f8601c41c042011020384020080b0f54100003c1c0d00d60715442e04c000502ca140104403d100c1414040140da03006001c541c1d0b01d441050200101c5400c24800d840d509240e8030410b0081030074800e4401f03246141c070b40207803101d00d44141c10400444200c1070407540540507900540ca00c1d00201060740c051984000e40d4400003075280d03210407015083d503c00001c603100d2070791910107a0a503000c41c0d2509980042c011100f561130040004039100007000d0034403506000c0c160215841050003908940c0c0d01881917001c040d10350f5480b90b4070b000d1025240c1100450f9089107040440d40c45103959108503030410700140c403403100d40186030f404c00000d540a2107c111104480140c002404e071105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456258857 1250 456257607 456257629
    0xd0b010c05061008070f03050c060a02030708031e072f030c0a1b092a051213120302040812070c0807062303072a0804080c12060c0901050d0b 62
    0xa03495000d11500c2e102c049490f003401900306c180201c15842c0200300140c000119111510300c1075a1541d1070700ba1180c8160b0460203103d802601a080c0001000904d00040c0c5c5488030500c01c030f10100285440b040011512070203000c1c01d9100e803030785441025000800918400c0c03800001c0740101c900d031500366491141019041e00c0212820038031400304214501c80da0900c90007405002404001c0011406001c002030203403644191912070102304401c91072403280c000c84503103074a2104400020700b003600804000e2244a00107960301c2c8982d07144002d89a01c40d008a0301150703400002450244d00c01c0d51500c241340e100c04401c50310700c42e081c240026074240c2440604000d100c01d4841004005c20791581511042c0e100e030300c12110901c01c0041003c40c940250903d0142460200c1c4010b001c043e280e25441000c5405201802003003002c1800596180d0010700003d40310004c1d80c0008440285009440c1d84900517680080500814003152100307510550143c691003031300312400300c0d03c609200301240141d615 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456260107 1250 456258857 456258871
    0x20c030405090112020a03140a1205120f0f06040f0207320106032112090809040b03010e100929040204062102040b2b0c17030d0b010c0506 61
    0x8081010401d034903151800c035004110a8002c01c0401c038055001503070003210383c00010303c0d906d0015001424540b0030001c03190388591101000e0031603280c05401520390f40218140345a42504400000c000040203941a40141c15848002c1c1700f98461100b0400505109074442083c81d03401d000403404070380c80a130300704c20054040348008050100341080074420500d00c0d0301803c142e070404508200142d1210081d55404001c20001d4140442e83d10f001c6a841ca685070121210500340a01c441c1842074041c001c0a00f40011a420040c0c81e03402c505150907102c7c540803152080d0032100101404103017a4000401c1d035846082c0c0100e440c2440c00a00042c0c40d0b80c04000c240d00c100b01c000b04421414140725500c003401100c0c140e982d0f00001c40c0c06200270014003182c002e006603140d540004564480340030380070740400350444590b9003d84286840030104c86042c1c0a44041a10707410002d00da2a14900e440d1020f4480d01c081d51a2070794400c4520083c0104601483c100041d00c1c00306004103c0a02c005405050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456261357 1250 456260107 456260113
    0x207150b0a080a0b07080403050d090311060105010f02030702060a0c0c030303060312050423030726100c050d02030615030c0705060108062701020c03160636020301060504020c 77
    0x44110920503080340540041d0b1080d03011607041008603103860314050744240c1616001c8103944da285000c030317000c0c01920780000c104c0341400007203020150004101c4280e002104111455aa41c41c401181c00d0138110041c400540c0040180d030002d03051101c01084120070506090711014490b64401d500c101c86540182d00180d6900c3c000e01c20040507071030380c0d11983c1143ca81182070508242c0c2003c4183c101c0201c14160b64860b2070501c005440074040c100013002c6002e0001290400c05290044800c4400c03070343c8080e4040d441242c1500f56540c0704181890299507034031400c07c83c6100c24000254009840c803503024010304425070b500c00a00008501c6500e03446205500c41846291980c0b400f1f03c10380104026420180400c000c8810170302c200f10100340160140071300322008411050092103042c4106402e030000256218408466120014010b0310540c010000a07a184000946503c064010340300d210b0f407521109106a42105406010316000400000344d030b81c1d0b1000090200d03403000345080e0340c1d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456262607 1250 456261357 456261371
    0x7050708030a09050406032111100e060a140c070302012a0e030105160c0804030c030f021f020c010e13050f010f05040506030c040c0219060f1a030a0b0604020715 71
    0x5a40880504003d090070742d406c0c00314600f0b41da03c0004c500101541c0485c00c40648229904241c0325100748030081c0b08280035900c00c900600706c008007a2451000c5082d4a00c0343c080840c4e004ca4080c031580304405a089004c1e8560340345c820885260394450b900a03001c41d92038014944070703014103915210b0100006100420300700602080903120002168185100382d01d40001c01a006200040d04100b1003400d02d0402510340c0d0318904541c072800780343c0000d03002c10880d000c00300401c03229040d400c4180d80200c98940d800c2000c4410b0452488d8055006d80043c1c01040e9000070f954043ca03e442c007000001004452000d50640f070071803c8030012540c810303080c541c030401040021070103d0842e029007001d0b0b60901041c5041c0b40402ea65500152206000c0da0b560b42c0341411641c42803100c041903c810080441d980a11400d00c0c0b0050082500c2c6522001d140caa04003003514001d030340c6820800805809041c01c8603103a1289000c2030310003050b103a001034007001071000144414030020510f119054001480f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456263857 1250 456262607 456262627
    0x170f030a09140f0d020402092101200408150a060e0a0f060b04050306131106030106050a091403100911040204030311060108030f031506090d08090111030405010507080c030705070803 80
    0x91100c41031543c014840280e00c0112502e4115680024540544002d43c0d44c00094000c030b00d94450107a00ba1000c1181c040d5500041c0d04107400a100c08401c8000e0300010007440ca00a0807140320354800c004055010034004807100e402050b40560203000500b001030200d5455054180a2004989454580340d8412500b1085104c0e031040c0c50203001505982c81c1068101004203130794400c0900350829400c5840840001c114007a800f80c00c1c2c004001c0c11a03901ca5a442c0c401030001d0304024000b6000c15014080440c8905582144001c280d070700900520304500040ea00a0092141c80340030358003903d0691480265448500003400150301c01d944540700030704498001e9051a506810005041c0c10400c100c0c12800f501d0f600366900001c204844241c001e04d45400103a1500c02d04c52615000710f130240b5520103200261011f80381c099000e8a4281041850115042e181d202e103024060200c1d000b8016080170503a408090001000351104813444c160994403918544005948040c0140d40006080c0301030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456265107 1250 456263857 456263879
    0xa14280201140307021f0b061c05090111040302040f0e240c040608160203070c03060603051c0f0e0f130e071a090936071e170f030a09 59
    0x14015002c6070050842c202000c0007034a600050301100c8445185440d4000e800c034140d0700c208130140008007031030f54510710003801070b01d42d0f032a688113683c0452808002941c811010300070003080c20401c202d640c0c0f9050a5508010080c880170f1945529070fa504d05602d54149020850741d0340b0500041100006c1482481901040040050400e00c070083d003484208505a007114645410240c1668020340702c901050040740396000c1d14001504e2100c80380400024021107510640c1528050002e403890408030a06580383c0c0c1041b49180000070301c40c88094401544641072441325020010015100382014100107030070b00210200d00d940786960355020404d99502000300340000c00011060141c00d20440c04079220602035030728010b01804901c0001030142c402000800d103d9603445904000132609040141c1d0900303003200340780381c040c400c8050104071810004160320b441c020882180158038108801c40c015460303140e920b06254800c905403100305681c1800a482d1001840d070742d1180c402e14021500d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456266357 1250 456265107 456265127
    0x20a030e2d0c0d02060c1002121602030703021b0411030411030721060c1b0c091a0901030f0501060503030703020a120e100e0102031905090906010801080a14280201 72
    0x140540c019030781e0030b0503900e0b00714100342d225404403581610f45a281aa050501d001a100380303009500c0040d085c1030340301c0482441e41c000c01c3c0c482e40b0088668034040003665280304100025002d070380036046458810013500c0d84501001c1d0042c101084020320842030f8403194000b503800300e49081c282e0001700740b07030300301002010010138039091046510300d071982030b10884150600c00506542e86908807a031601d8010f21410b2001988901ca031480d80c065414102000c06541c00b903100d0003414280d00040c0032802c3e01e40040100030013040040903920b540e89565440080c0d600c1100e40c2c0d503c41500103255941800a0186a406500030b82405c903458941865010036025009003480ba0003103140340c2d0b43e2a40300114205070800d08103c45000e1140c030040c1e185004160380356420301c407140c0d402c0152940c000c0182465000c251080c030001e8076140015030b4902024054030800d54080a569000b148042407001107171034900d4141c40990030441201648002008c40f4203903500c3d28403045604559001e08044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456267607 1250 456266357 456266443
    0x3061d011701140a050603071a03090105010b0901120b0f0918010e0a170711030304090f060504053d0b03041a0f06281512020703020c04020a030e 64
    0x20b44000070b05051450f02000e0b0468910f15616800103129803420840b4401030300a60f150741d030101809008590065101311051091942401d00005d4070360000d00c107440b19444161070700038100f281560302100901e1011001c1b50701c050044444009600c588140c0c0303018204001c4840044044000301070309450081c0001e51003503009611700310204803817601080c6450618403005a03581d40904196854a08551342c860b814040040c00007002035496004038606810100c003442410b5032603041100b1908115500059000c1550000c0b25240e4001100c603901a01d080070b10051400744400b24030424400d400c080b0040f90000240300a2050320301260b82c581040212805c10b03071804440f10006a68081c045e03900480405010440035104400e0440c1e101c40e40901c01415140d480d0f07141e00710342c070001d030752000460364452072408150424000c5400054040d0010180480880e05100082d445044800c04066580c01a0301c500c0c8420311440300701159042e1813071040c1e80307a08031401d00d00f402c013441c0c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456268857 1250 456267607 456267611
    0x606030506120712060b06120906060f01020c0d02010807050c0d031d0d0c080a02030c01020c10060807060f0e0a051e10050c07090f1103070c0b0a1a1003061d011701 72
    0x4002c550500c84c0d1403d41c45a00010204040408a000c00e803d0f008078001c054054202008001c4000c400060307a91288800b04c030802d580c00389120059856858404000d034001c030034200c000c1d0155000e038408942221a40c5425407502e800892498141500301200b4400240c41c0c02c554040001001540035441d0710340006000640301100f0058840380804c14002c0c4042b80100d92085154028401e540003032458600035995800740c1c6400c191507190300816070f081103150000c0410280b000042c44400d860351515042145849030509464250038018115884600c21401180644661120340700350300300721103110b03c2d012190b8104084800580460810480c00303004841080000042440480354519800103011100700c2500000d05400303480000403041c0041440324241d80143c04500c0d0501030003003540340c0c0c0c58022506007038880d014803211626003a040c0d81c00c038503d03140c91040205115410002480d83c2c0c3d9102000c00e03013025111000b0720f044014010028180000c0d02000440150710003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456270107 1250 456268857 456268859
    0x140a08040311102c01020306010f1d1507110102010218040e030f03040c030b010b070f021009180b0112140c07032c0102190b2806060305061207 63
    0x10200800100301504000e40954203160b482414048011400c0704003009010500456490100b01c0c4039100d01d040081400b000b05605807a818070a69001303501c140e4a01d0010308080b041103c50324995245000031031400310a9182d56078a80445182031001c40070b07070381d4403001c41e4240b02c002006008040c80c10b590041001c00034050100031b400513510300403100000c0701d4042d20300031032450041c0b02c8440d92041001080c48248800b110500c811a449968107200c0c60780c03126403a106d18028083d00401c1c140112202d1001480c11030500b000b522414617010b02080c2e40c44011001030850381030010089580e5407114541541d225824190b41000c1400a1050000100140007075500040c080c035204080441c03510201846010559038106010064002c02030300c92050741910000800702c1c80c098071807132440d902038060710400b04406c59000f010400340c50fa00c461032442022284200320f610640c10007051600081e1600c90314001e8003546c1c1c1d00140c240707810b0043c481e042c1140d03201d090b941d610042c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456271357 1250 456270107 456270127
    0x3060b040f0b0907051e220812030a0905011b030b10170c090a03080a05190318030f0c02040603050114060a08030d0c050c1b040b0a030201090e070e1e0114 68
    0x5260b0046140d26000c0e0ba101d520000071b8007601204905054400ca0001d00701c180000d1900800c0c2c0c03803a20385901c0e038007610340c1c40c420507640f91070580e20603244400c00d00008544141c01d900c099480b40c094400820030111062071410f0f0355891502481c0400c0c0d503644001c8070303401c0c401c98848842859040400c8410201c1c01080da5618004004651441c40040c400000d5104c62032070070000c5600c450140d0300e49420000c0039240f50420450f0312800a4002d04406901e0702c01c0c02080900099000380e07098041391074600b1180682d41c0c990100901c101d240082c001600c80b417003040c004501400000502d9250341030251400c0c030028044601c5a600030400f4410b0440c08000c50308059048030000500103001c940c15030b500e019024480d01c583c007a1201c45038010b1104c1d40c00a500311402c40781045043c0c05001008003410345400060700040f18164244215144011029004041400d007688030800d00800150070802c10b0103000001100b4404800c0c6650f081207400c4c0004045d0001705040400150b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456272607 1250 456271357 456271369
    0x1050703050d02031008060703050a1422020604050a0f0f08030a021005041a04060e0606040c0f0305220807171204020918010f0b03102f1303060b040f0b 67
    0x70b00303540c290f40000840c1c0e0044808000f100180042002c2d01c9152800b4040640104800c403420a80e8038206002c1c881000410800180700312040da07500c00d642d2030804c452050504150704200d070803410400011800d41d030f600420400404481c140d03000c20504040c03814828645a40c000c074643e41c014007026078000e402280041d0088620040003403181d40b6800d03c0c407052800c40d1400c8801c11203030320510051019a81001b42905041e60849244d511400140000c9030040c000d00e5001a018000301d89895200b6004190814600106a03071042d04244901210a0703001000300c03805500010b6401c104000000b081c119004049044c0b406c155103000d50014007800240024401e420b80000a161382482c4a0b6a035a0010404020441060800748010003440d420040ba0b1207440345800003948131000d03001c0c02c0310070040c80c54061001810b44030b00444420310a180f100c0c1da1141032001c01400c200c40c44c10b100056004200204161703103002c06100c01c44802000310903c0707905208110403191100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456273857 1250 456272607 456272617
    0xb03010c051b0c3601030210110304080f07030b07090806070c0602120a05150d05190804120b100b03040b01060f030207021e030d0f0f050a090305030d05090c0105070305 74
    0x2042d8080081890211850912400d226141d0f807000034100e021a0040485010b1440c1890240c41100c1c8107940c22101c0c0d200d90b900b440000d5101070906034038064607218105c080d102c0784125003145c0c00d06860310750250800c041249030305c03075951155400300240001c58241a41009080c100314852600340b04000e916110000e225009010220315404c0411205078100c03540004450410308090401d81b503a0806040141c401ba60071a080e00100250303494100003284102c0e030300c10010100300b01d209090828882142038259242e030790602000503030078140c01c11303030380501d1086c1c02990280c07034200d90000101c0b00a403ca96034040c1c0030300c2000002030b90042003034156049402c00f000c807c585d1120440c040d1069410003034000200b42c1103502c400c1c410b40d0b1340c608580011403d450801d100d143c4100d0b00b2041003001080069400540c552502d4001c0300245016041071a0000b0640d8032600d8052031a0300001002c4069950380007045442e1809000801c400390303007489c10714a8440aa14000d05c13034022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456275107 1250 456273857 456273877
    0xd0e1c0204110f0c0a061a0d0210110303010605040f12110d0c0b0412201c03020709060b0a09090c200c092d04031205100b0f0d0b03010c05 61
    0x5205004152848503200f682c00c039403840c008050341c503294203034242d894164600e42120028245003035140c0024400803200f84d10035018041c4040c1304002e40130003140c85144910082803001c00e2960900300715060000b580030b49941e84809594a00d403070600000d0900561159a4480340301c40441c00041107108802c0ea07111301110000e021021604084005040b2a031240c443c54800140000e1110070510600441d1400340c0e0181c10700c01140e251200414200107d85544450f0140d45400761071b20030450240c009000384107c86004c4d485490410480354181c1140408404c003040344440580c3c48800b000207080c4040d07080c0840340703400d440030b00b03000c011400384100e950090b099011404c0b420000d0200350304d8014500348072400c04420400607086441105c00c45050096082c1c0c1c4072050500310980031300e9150f56001614040c40034034000a100251855080700000766000859031000c0c009040034003031400501d07a60781c134440000012100e0800041d406641400e42e51420640c014094540c1000c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456276357 1250 456275107 456275111
    0x5010f0503150310150b1201120303140711160b090402071e0804170a030c080304020d020d050c0103150f0311032416050304171b0f0d0e1c0204 63
    0x301d03401c5210000ea0140b42d05a05032096160b01c4110750b04580041c0c5124020003c4c2c1d9641700d0f00c0b20303401d181621030008102c0e0090f06000040046003140301210405902900d0001056005c1c01070700501701000359050740003d400f07000500c603007500074030440030100d51004000c00c80e9440c0803c000c1043c011900391034842c660104020091180c0910013800c1e00c0e003000b5803121810024134009006401c54004c25000b116041d4807841c600500203000b02485815440e920114003a5039625003041d44010030482e0840c0000860034016210340401c40c0c00144a07501503c000050440010304a40c0824880e00305002001020040d403031440c40c90308152600f00744888070b42805500400e180c48185440549400030321a14140214283d41d602c5000e1044548001c1c04070503c20012641d1307020076100030b8851280c25480d60002c80d001170080013490741d402014045019814070160a04410251408a507082060b094076540d034050600042c28008941e501001c0726401d0000810007060040240516 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456277607 1250 456276357 456276361
    0x91401061107091a1f030c09030b010e1306050702060105010f0c020117040501021209010501030c0b1213052d013b1c030b03010e010b060702090a0204030204090507080c0303030105010f0503 83
    0x848642d10400400c01c051703c000900840d03900841c4014003c0c4002c4ca00085c5081903500707803680328203940011241c04c02e01140306a401c11032501c00b0258058655540076545641240000d0490700600780300c0d05054014003590340c985000500f418086000b140100030b03910300d01030300603031b0420342a00742c1d0301d062a40c0c441e40c1e0341d540c50068028400d28001c910b01d06550b804000b07502d181500030a040c0e0f0b00c9040700c0e80d0f4040d50f0f0080305e250380c0942041c0401080c0440f00007000c1d00100d1403038050042c0030784125864540b4030071000b07021403460090001d0240c040a004201d01009014084140c45c4d080d00011421380d008410030b803921030f01d075130502900c41081d8400b0b42054003000000140c034814a905404107003240c80c081c1c000d0074400c60b450f01075420b002d038908136807206205001c9141c0025103800d18002c80c0b0307801c104090000429181c0d401d6070901c00400582c5451044203183ca00c5400100031041c2004e0324640b81c8080a13412907c41c1e88100700501181e43c0c044440350341d803600ca0828503103903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456278857 1250 456277607 456277631
    0x4050c061e210907150201060b0315040f02041d01051002030f160605070f08070906120c02030708070b040506010e010b0d0b030a0222060b030408090f0112050109140106110709 77
    0x62850340c10079030700c01000b010a10091580208201d811140c113103a8440e101c0d40c8200b010f03400e80d1002c1c8600218000c0034400240303502800d400c4500074100c001c100185002c00000440102d80042d0030282041e42c0445905400b50f08010580c0d014100803100c076040e0740c4042d030703000f5039034030a5071030b1810f0a160110b46101054403080c031500b1001d5001c5000d00c09842c004000404849281d00e407200082c1030000446c080e240a202d0130000e48a040c0c5e900030200200151050180000c0310325607045100c10440e19000c510118050001e551140907005581d0521742402441d0031410b07041816943c2c0c00344010400d56a002d412519100341d40c10001c02e60150201c0004e0400031407100194104022102c041c2c50036070600c16010607059011001c00866440c0e541c150b40790b02044400070210f000401085107186000356060221030014035206d4450714190807140291002070707000c0840c0d2a1200316111103480d456041074050700041c64800a02e4a080203038540d5503000d8891703c1c074900c1e0b613062504a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456280107 1250 456278857 456278887
    0x501021018260304030f120c08010303080c0f0c0601050f0111070302130b03030d0c020d0c320d050c010612031e1209051b090621010f1404050c061e 65
    0x102c995400b0300b190b12403800d420b02800d646116103608000a58141c406032100d05a0b202c4c01308610020342d1524480c0c1c0c03d5030341c240c1c0e05179009012258a008180300085183c81000e004200c1d43e64603201800c4594545002d001d0280401c00c00141409442210824210800500202144e8048409414105e062070b42400240a0f1549850b010f000004440140b90000d800c01a10380342c0035070032200b1420a0090480d240720f44118018000c0344644c0d124102003140c5000d17000d04a0f41d0040701260380c1c1c500000207240c80c484a4607200440c0d40415003850b007480a00c20100100112851845203d015580003002e80d540b903c404e010314000400400b005030b10910090030402d06003501000030301c80720305156640305c4003a030072214040210b40301900c0c24185078110b0703405100045d0400c8884450200340310f0b1440c81941207100350703640c0d400b50200300301e40901503544044003c1c50b01030b6481c1814100103061004266840340148020040c00300ba021542d8003402c11106061200c5856128881e40015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 456281357 1250 456280107 456280163
    0x150c0503030f1b03270c0303090402090f10230a0f0c0f020613080f0c01320313030806090105030705060c120f03180c09060409050a0204050a060501021018 68
    0xc0f2038100801004103120381c000758015580c05042680c941707045911104c80c0d840c240650740720707010381041c03084548605190300139010303805005010f840350310841c2e00401d0210303142c0002000001c5400020790803003055100f103940c50540c3c03110b07694942100e00318060f2800c00c9841d42c440030014803111840a010448400c0368030705a0040c80b884d59040002400071608143d4094965030380521903000b2481c0c03900140f5440e4801e0180c49a0010402c0203e5111248c0b00b8818075464280034041010000741051000314412420040900700012503030030000d00540004103924000e120324001400160742c0001d01b2401c4038800c0364429038401840c1222410141e807a40c06506000020409000351041076021f940b06030080b04034140380d00142100d1942d680d014440c0c1582105042021400c5400d15030044400e841c020402c80e201008a40d02082c03c1b40c0e41120031182c0c088da900d100340160340c3d0521020000e1140350400744140104006095030f2003d8a1100401040e8205540c40703000c4800d4100742d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 456282607 1250 456281357 456281401
    0x120507050f150108070b2d040306050a0218030a02180a021b210406080c0904020417010603050d1404141207030f02040501092f090d050106150c0503030f 67
    0x58500d4912400815803070b40a004500307142c014078401203000001c8505450702403003003c090b84001c0d80c40c0c10409420400c0c1150040010300d0400021001c82c0c5075000b082c0c085c00f00c0d01e50040c0d44d032140c0119800b200c0070742c0c0045407090708101508009130707171580c2c01c0040300340131360791140200e40300d2a85c1c400083c4540804048000301c1d002280d040c0141c081460b41c4440214284145c0c0b07102c60219201140c85507018082c04205002c020401244a1201400360094003410041c54152554031501c2080000118815240c5d1607401c10700801c82d045c881c0b85584031540c10001015000441c81c010b40c2c0c0a140644d6034044000c2a048003e039481c80d402c11901e116a0040d110740688900b0096070090720b40006070b000394103000c00054440307894071401c468511040300018243c07903045000c120445c0d030117403010a00007080c0304040c1c00382c0d00d2441d06503e1500c40e034000510f0910b030030310801074403c0310300c1520140120036201401142d40031080b681e111002c40e4103420360303a54125210207144185c405032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 456283857 1250 456282607 456282613
    0x1030b01030216150507141605070b040b09100206090a0308040c0f03030801090c0c030c140a020405190f110403170d0c0512250f0c060e010903110a120507050f 70
    0x641e0504c00c9110301c021040784401800d12566407860820f8034401c5d0014903603442c4541c10000c01421040d9068403585c2980b00b20261203010ba680d00c28610710340c1150300500654400002c0301070462901041541c1c061555002520307441c90220115910f54407202c1d809005e20031a100020204048580024043d29145140381941600e03400c000f00504401d000e0388609500d8042c000644900491042402c1036150303464900009680c0c2d601d032a540441180c100040c4198600040103070341310b006140c46520b10b40f006800000055500e1020741d000143c1000076035103803041043d03007110008202c1d000d40c0d40103454513282d40314003901e0040a00c10b10781c0c0440c1d032615206003410101e03805001072202881040c2c0d2004181c0320408022082d200208698090003074503181d144c0f00d0750150010420068140c203224030074000d1907c0300c1064541c88400154507956403030ba1802003507040001070300c440b000780c03004003c40ea95941d1102001602c40a400c0207003c000701e503000c2007100421545500c1036400e029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 456285107 1250 456283857 456283897
    0x120304030611120f090c010f030b030708030c071202150f0403050d03050106030c08092508070b0d180f0201080c09041401050a0b18040b030a05120a12050103030e01030b010302 77
    0x4079020640003e040c0c00980d5400740d010408003454009800c1c01012504060b004d01c2c0e000e170b401560383c1c0b0012407000c814141c4448410100d5942441404010a407100180d5500c0c1c9020314058203040042c0c101c0700171210301e50084405030721598141d401c2e044c002008982e943d00c42040701c103018001d99000800c01d21447c001d0408007541a0401c904031400c40d2814001520b20680030740e1020022100400b480d030241048008503001c0240f00c0d80c0c0301c821000040f0708142c442041504001c41c0e41c221446501001030541c2c0307580304a200700c41c41c540000e42c0b40c4001e0340d00d41ea1078255100100704081d04000081c4042144060741c00100d901e00c43d001001000b040b9602c010760340c48081e09219551103001100d00000314402034108441c0e4038070041081c1000440040304010081c9618a02c0075018811007001000003501000010840c6540b02d55003a2210b03800328000b030209280008030041e160400004000280d040300402c9410402424082024010540124020300513450044a40c40365019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 456286357 1250 456285107 456285131
    0xc1f090c121505060619032319110d0506030c130b0f0303030903041703070c0e19060302060a050a032c150f04030c0602040b030711010c09050306061203040306 70
    0x186500d403403290034079036100c400c0340d0341c0581142c00444110ba08040200503c4d019071070000683c142c0c010b92810002031012007440441c4442303d04002480d42c54502d00c0911440400070b0100c01c1000304010000d0101d80b54002e0084203900411446030786280c1c452010a401d03607424001021010b8000d450010700c0f0f5032001540000d0031120340090700401c0b120f52441041d003408000c0b644100d0405005600d094a4420f10011070f403544550580c1d180014000e0800082c030a00c141c00c01002074a6800885081c00e8013201012a90301011000182c43c00d82d0030001038072020150b8500000074149a45c5801090700305802401c2505440c01c1ea8860801000c0384d01100d40210000380c0320380ca011640d0999071507424144020056030010007400030385001070002131107101101b0407240302d132401506041d910202030601d5002660201d01050062140005240c4244249070010b8690715046803410300d894042516031501030b010b02d0062601003a24034004008104450046a0202c41000180d41c841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 456287607 1250 456286357 456286379
    0x516140c0a09051b0c2e0b09010509061201061203030b01080c0306181510020d1818270c0302100804032a0f06020a031805030409020a171e0108030c1f090c 68
    0x203440000c6e120f02d00030203040d181c03c0c0042da01c0d041e64400b0b0301c1501242c452104008807840e441301045955901c45c0408502694a040002c401a1182d2404104202584000341c20718900804c1c2c844078031300078420010250780304d4401c102e12126524403071211384c440706041c3c0d100c0065050780a130880c0a28003d041595400101c80e250100c50b942e800e040d0038508190700074292140e120300003100401d000840700c0e1060643c440081c040f0802d55041c62070042405004038160415030031b596100780c4060400035414503641641c0d055005150200c0b0501d401d90300035240c0401c00d0501a07444201a6500c90f65032071688488440303030340107a090b10005a003807612001960215907180f00007801c0030309414041d1880704400751202e5110020b941018100100b502c0203401c041000810050f6005007140040c0100100760b01031a04c6812007840c0c584007419004c803845040c1e1150342198820080c240d46480040340c070039078121420301c0110900703a0060030312001d041c40d07110140c1454580100002d201d0107170 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 456288857 1250 456287607 456287683
    0x72f0a050718090305040504020903010b120c1f082a0d15050609030a0605070306030b010305010209030d051e1605011103100603060e06010516140c0a09051b0c 70
    0x700a031080219100852181601c040f03c1006000c54002e0005201c2445c02c1e8000d0714006c03c01800000b24a02450300090032078505000c0030801c1d030042c242e07a51680c00e0151800c078004010041101c0c1ea07442c9200010514200107161018500740d4600002c10512032110080e4010489129191070300101c01000c030040064119280c0c0101d1f1107440003c050034003405603490184001c0c00781c1120b41158032034101501c0001c3c415030030556104004400121040251800b80d0f018400060719625200141482c10041c0080d82050180604c4103441001c0040746030364505400300c0d5020380725143ea0f40c8416071258081c0c0d0050041d405c200d64050348020150141d8403e031040040b2a051507035450f41070303045402c40d009175520321030450001402075024100801075031800e15110411806130b500c0d00d60507082d01c0850310322180c000c6035500600d0700c0d05440c0d900180c120080c0030083d506015200305c9000c031110f2110403c0c4980403607846d84c505800c0c800c0b4202e9400c41350904071119048a001c41036030b002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 456290107 1250 456288857 456288869
    0xf020909090703020901061103190c02010201051f090e0c04090501050f251b0b07030f0e032d0712120c031a040b0a0b040b0c06070206072f0a0507 64
    0x30300d0008060390740008500c0c0480380c010748160301903420114221010103110120301054070041002c440000078850003002112502e955492000c0710603c002420340740090310701e000c03000c83e6241d00d00640e042e040e200c07800c65a004030009660080c2c09201d03418078079500141a445442c00c5007180030f1140641205101e0002110340140c0c9564072200000c041d108030100100b40412030b0041c0b000716000381c1e603045004441042d0070035001040e507541e02100e00c0032100503000a450300d079021807441950213807a182c00d6106010314181020380c580304a1301071760310101c0100200d40380e0034101095200d0341210310385074003c0d55001414021500c0035001100380034a00700c00502e01101072240c18031a100324825074809101c82080328900404000c06412503805982c0d2003816008005110f0403240010304c01010240103550302c0d68600d100c01810039a00425440564100301d04111480794440000106400e40303010403845243c02600240c2c1c035405000b500180c620402d42d0071001d00400055400880361 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 456291357 1250 456290107 456290119
    0x250804030201110d0801031e02040c1215060e100e030f07060e091608102102040c050a08130f0c080105040501050603122703010504080c0607230703030f0f0209 70
    0x80c520b500c265442c4e0f00b5a89941c0028855001071000590188460160700318405a603540501c00390005002c9541d1440b0010118203d00002d50801ca000d02560303940211211400a1303080c5000c002406900d82c2c165454820068002005020b9005143d50a0750709070260481d020005824107480d03407000c4078040d040205e414480005442d2a0042c001886520084a0940754250030ba400741c1d1000300103440c201d040c4025440110382d01d41e0301010303280c144114441e4414481b030f16005000c1200d030210300e0202001010001c2e2001c0075001343c00c080e00b0200760103034540c0492081c184003003489104c0c2d40041c0822880800060120720540000b1b0043d030048000700801d44480e4109aa180c00c40d031410804000300340b0810840d208106010826441c3c1c05508602400c840d0380020b00b160000c480883e5000004561003500403020070100d0746c4500075081c0020060840101c40500412800c001541b07007400141030001c0610941180b061b50201200c18007d4007a4014420302a40007141440d00640b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 456292607 1250 456291357 456291377
    0xf0d09050d0e1e0607050f030307020106030b162a0203101e1b050a0c1406040c0906062a1a0910020702060306091b040308030a1b14250804030201 64
    0x228240d80074003002008540c02c01c20490100d400d02c607864105e450190361a009403218003248020034001107120300019400041e0807420f614129114010140282c10b141c2c0c014000030400e0b6811880f18062803880a4200942c03c041e50b515007020f00322190025014040c0c2d00b400120010b42c5e4211045840c002072760000410305000d0070b01c003107485140094640100300010551998010310003404000c00c1c9103000002c549180c1c07201900e40204958100300307540070f03108200912020401000c080c3c180f9a43c01e0142c1e502d4000010300c0c400104158460003940441c4243c424a0704036038480045074848050525002601100002c2c4402128004168022200341c040021020b1003120f54580d40100030605544486041c86150507000f0000f03d00d05402d0011b91445072142006000118491424640d9a15003d49003905544140810781070b124005982180da0380d400081400880d01803420070358403000d2001a043c040c94149441d0005000500c60301c1007444110340080003501d000b81ca40c10402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 456293857 1250 456292607 456292609
    0x5040b0303090109060e0609191a1e1b0d0206060307050301060b030414010e1507120c02060a05070e15070b07090f030b060d06020a0e040501050a0602030f0f0d09050d0e 74
    0x74842e52080500240700c550040c0700c554001e1000c03510440c070181800b4184907802001c0780540c442c2106682075100c102030100031420341a8030031084074007030704212410148924901d4611094070000e03200c00720404140034042c40c01030f803100061818034108403003103414100000f03912207405031035090080c0540c500104941c20140180d508aa02030740a03e46950395036120400403003151514000d1a5407a5011200c00c00030070411210350b92800841000c50341072681c0041c0c44901c0e02421a040e0340d0425074020540c2d50003041403070340b10002d0f010108040c2c0d50440f0441e0368200c000003841d40144405800764603902c86070003402c1958402c0002540c2521042010b4603148164400c02580f042c03491010300008e40d41c0304c907964004c8006071004010300c07070b40c0d07036040705907048000180001a4119040e207400e140c180119401000141c980752540e41c20008002e480f849440c0d140b400e4080000307581c0020300524800c0f80c80500542404002e0620b140c5091522440500880b00003c1c620307500306489 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 456294964 1107 456293857 456293863
    0x60a111b0c0621011e15030b122103010b03270a0602070501050a06030213150503060109020a02070e13030309050c13051801050c030117030d060f05040b03 68
    0xf10742c110098001030405050b031010103140510f6048084040000b0b20729015100c80034400305510b41203401c26005041c20340c50143c0c01c0255130758111610303c00850701d481447e00c0005040b941c1018180348003a180401e0003011107020303080021402c90b80107007800014941c13103d00c40c24408901105000d0500604820540788180c001503407608001c820301c03d079544502c9016040250b14150340209a180e1401c514a0351035699541c0701b1070381c0e0119516114002d100040c00c03544d40c1d41e12541000065000000c1d1f210162180c61004180021541c0b01136100315550207540c0c0041900f920128007402912001762224020001c481d865a203980d84031001d0340080100c0443c0504140320b5040700c0d03ca5102c070100c1143d01d454144002c00f007445e41224111951400a0070b1014501400e00e07046109200e802c06505207000000101d548000b07010341d0446000711000c00055113501c4c185a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 456115107 456294964 := by
  have h0 := BRFrame.cov_init 456115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 456115107 ≤ n) (h2 : n < 456294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
