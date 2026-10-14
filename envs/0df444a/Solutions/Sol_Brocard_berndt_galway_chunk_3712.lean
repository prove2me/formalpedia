-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3712
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:30.754013+00:00
-- url     : https://prove2.me/submissions/9ba0b670-d750-4ca2-a462-dee55ae3af65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667446043 ≤ n < 667625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667447293 1250 667446043 667446067
    0xf081e070e0d14030d052d0a110a210c0f0c020109090c0f0909020310090b010c05011104060306140a1707030515062d0603060f0901032603090a08 64
    0x482c00c24064aa1001c0e0312010003880720000040807028440c4004208590f1901d00103c0c06000f000403008007103410f0500d201074020031210294004400c8040003401c1c03412581e981c10f15900c031b02c141030007003404800d40402000800d520842100300d094014070054401c0c030780003854203c1010142c000e104031000d01038256403260403107901400b8501c0c0104103821440710094410039801c451a400110440c0020403408068000d40c0c1c001c007402020240c16500300a10100074140e0030a00d0f6040001c01450180414000d000d6801061154140150745909006009007030f00c0858001400f00c101640000030301d80c40b04030040c0100c445440300c3c803030700c5030b5504c03c541e0030024103074070162070341c0310300d90300c1500d0750400c409043d02400c01120034801803040600080c3d0003000e00401c00b41e504039a0003405449041c031900031a0300241c002d08482201b9540000520f00c04001e802c1500c1d140e0711131000c0c1c07084903501419605081d10070400c3d642145400d01540d90381c0c2c80a000b0003880d01300e0108090b00c03010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667448543 1250 667447293 667447309
    0x10906020a0c030222020f1e190f0c0f0b040501050c071a10032a050a0806070305060310060902180904081b10050109090606060516170c0a030f081e070e 67
    0xe0318940080d5940e00a9587d201e03415001007000203086840c0c44607400c0b0644079042220310801503109850000b050300e03203050f10801c1c03188020303100384280d09100720300040d480355519905c00c0c0300b69402c51740790600741045421520018104203654004000e80ca021440c02c4c82d95021138a501c600840d4241d6542541482000040d800208001c0300101c00d480c4882540d0b01101410048081e110030a43e910343c100100002c13140701d682c40c543c0040012905c80c5200b5040b9a91168000c0e086441a0041741e90103800c4800790381c03012203103940c0407904c11840405848820b24204c3c00f00d60802d52400c05031100d0150b40b14a80030002d044c43c0c40390b1200d1585905000308020f0481c00714041265681d40c071070401c0500104a4115843c038034000003c80c1850042d820350f0704000072003070f40c0081d441c000c1c0c0d42c40109604e041d00d0312421100c10b105641d00b6080401074003418074841e940c2e0124940e401d64000d05100340192210003c44d80006022000b00e004500f45503000340c99145c034403500f0101001040a038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667449793 1250 667448543 667448599
    0xa0f050c060c1b0d0305030105041505130617070605030f090c1801050907090b0d110d0c110f071503091e060c0e01020307020a0e04020a09020403060b010906020a0c0302 74
    0xc4080030a00c0c007030180b8040b0301000f40030340800c09400710a14010401101c0d0082c001c00401107442031005000d14102540540411801000c034200e850752100d0000d0a1002c00341c100c13920042c0c4655040c0107086c0111600c00c03100c0d400b58014654103041c40c90280003404018500d10301e4214250024400520400401a2010014016011407a840303581c0c001c065200340513050045001c000440c0401d44a54281c4040304c82c0f03640c0d003e04004000384100080d01800c540500046004d200c0c060741e03803c0d20720501d096544152500718a04006031905402c1039401181086150443c0f8010083d842c10151080081c044a02e0300040e034018078684925454031040c41080344040401003841004601d90014500e1892601da2030103400380383c0012a82d1b8803034184001d4014401980400951074409140d50b009031000b00329214a40d00d4040304012608107030f209803030254640b203818607a56000407084002e845584050503410050342c4400383d807124140300007402100880c854150fa1080500131180e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667451043 1250 667449793 667449799
    0x708130f030c0302010e01020c0109050609040905060916151209060908030f060909070503121b0d05090414040b060907090801110c0d0c02010818100c051c06080a0f050c 74
    0x8441e00d070b08007444070a400380403c80c0854138180890600358000200d62001700816502e100e003240c01c040600c0417036000150044e4210341c4410850000030003e0106912402e4400014480c40c500151441209402c1c1d42c054016002c040c00b0740c8881a500c026007040302c80034040301140c1c405e42c44c50301100070100d211000d00208004000d01c0003400c103010101c0c0c000d8a04490304691034442c0503429403910020722800e9819131249d401c0e042404541c0c00a01003090810500f00114140010007030f09183d20b962419000800004a00c203103868244580e9000c0182c80240c100c0500d0300e555000101c00010f068680309040803000205240e11400b0b507007010b0700c0302200a021450004040036021380042104403100d0060703015201c545446680ea19800c1c540594400899441d09801000300005480d1f554205000d0b0065240ca4110180510b080050b0180d07111540c81c20344011a6114101583d2116001810448100a861000a6030790449508209080070000c200e1600c0791a228007401c100790 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667452293 1250 667451043 667451069
    0xe060c0c0a08070b061206132004050f0f10061202070f020a060509040b0d0b2202030a0803180a0c05060a020c1f020618071413060801050a06050a050303070813 70
    0xc00c00800302ca25500960054420f41d60a64000a54a4a07044116001a14545104240c43c080384400351064420800c0b224482790741500200410103a038012030700341203c10320700d0303040c094601110501d02d98446001102194500d0900c040100881c146050500c65542c000c40e440052005400f007000400f0b030300030040030105a503a000900913400600403644500e1074299583c0301d03400e20758210b48600e64030522040d03c41e61503010100c4503480010880748581d4102c18542c0060710100101200140142144c54403840c00d4503010101410104100901d60014111400090669082607041d180c0485200d03894400603441240391203022030308554810b070090030001c51118252088541030078282d00345c036550b03620001000c00703ca90a144684c455030001d80d08202a0710507416200165000400d5007040c4142c41c00c81c1410341d01c90b40c11050403039640d081405080c9456100d5840148402e9842e5443e0914103000607883c2e00413500050304282001174039501407241540164041c002074001c3c80c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667453543 1250 667452293 667452307
    0x2060112140715020f03040e0c161e0c0503010e10021b120705070e040b011a040e07021605030f0a11040209130e071a030a0b010519080f0a0e060c0c0a08 67
    0x140d60f04003054952001d4000e0b40143c104110700403040314252031107121080740f240c40e5440140400d510001c03401c140558035070040710006041d030340080e00003501d200402100c1005410030790b04504990707021910903858024401420040400c402882c4140b5540043c2c4950703000c1182c280c540c00f09000b100c86401503400c0c2500141e0803030060075031203010701c044855103503d8900d0180c8005c0c003560040d02c811700c1c0b8401040349600000d1a042c0e154141c80c0c089051035900d03812401d0600041da010005a00001c400411084060b203846004010031002007051058950301c160b04d41d140081c0c09845001c4842c000c0309903840d15011103201d00b07006001140e1091841c20318000810451140300d00e0b0380600f110020310002c0654102c03222944075075855146494002a120041c804c014440d418010f060101030016450303c0300504010341282c030344004a2400c0340780035088000c0101a24105464500a000701140001d480c5902008003160310b9034418054003c036107080080000140006030010f848 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667454793 1250 667453543 667453559
    0x4020409022704050601061b14120a0e132003040c03050703150605010f091202030c0a17010e0604050d0f12050c0d0e0f120a0e090106080108120a020601121407 70
    0x20720f2040b801082940c030140d0700c40008a4840c51440b40b4402d52210010fa14404200e0301c008208104004404442c1c0d046180c01da1007103650800c640d08130224200291048076410100b03440c050000c6114420050300c8004640c169496065281741a0300d0207001c40044c0030030061200b0600a180c110b400c480c016940d900c6c0008900c1e0159070742400541c20002c00007004d50188281c074510100036112043c6c05d5080250200c1c0c1072400c0141680c0c94416560084400c1c4c880113501409840041e54001914401c00f0750340b403d4682410642155621240c1000080740000c070749a2408100c624003903101e18203071401124140301003e1a081c50320729103000d2000012a810080c016510030b040c0500c04c46c54080001a03d4101d800c1034503085400c550318410a1001100061250401c0c50621643d1910324102054040c2c400340c10400100740868010300c4803c104000764181c2900000c0028604964204001d4a400c41803059030007d118540180c401c1101c241d58824000c48584101c8084503510150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667456043 1250 667454793 667454869
    0x90319051005090c1e1e04150b040311060c010f1b0e0d0b09010e031c050c0f0703051c0e010614030a08040e040807021201020304110f090402040902 65
    0xc035201d12810400480203503a50140501c00c80403407028150342000501400414071a2001d500c000c1403409031000c40d142d0391429900301c40e140b20f860808640c050b42050101300c40803030260b407503412503080d4108200d5240000700c0b019694081150542038201c0800320312240602c4d030104030b0300c1d404c06400452074184ae51240d9000c04013210800d14506c03c0c20b00a039003030840240401c0d04403c4134955140400c010560084d04032414100003d41c0c1c0102c0045603065400000c2d203811545420048585503400e6801401e80111121442602d05640102c911407948180c0d500182402404205042c1c40c0c40170640c420707000384c1400c005020a031300e0b0011845c024030030360041c920341c118965501d0303040c0d080c00503085017850b52200320240340a007440915a10124000d00c02c8640440420406005072102040c1444096415002503140c0c04c0c24500758160043c1400350341e0140c0d1600b4602d43d581c1d555404030680087d019100001c0309050750010460f14008401c4030f540043c64904400c06000e65900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667457293 1250 667456043 667456093
    0x2040f020c030324060a0509011116060203071a01060c060e030f04030b0412030b060a0e120d0504140609010f0e0d140a03030506030105090d0f2a020f030f0706030b04020903 76
    0x14131440b04c1e2822042008a0081c1c1c94902d001032410310042c1e0712940601c0420f48142c08190840304c0030030000e03801c444c41c17201d1500a8001604085902c10410000481020020900644001d000d6040c050000c00542c222480a4a25901d0f240c103000241001d000310341d8017041e81e81c240307551140c9038100b850640106545c200d80c24802c00c00341c480a54824800c400d074581c0000c00c603d2070a0724a15080b1040b55802080da9480720a210201428a0701008a040b01e4500c0e80c42d290384451070001d0035586402510200d40c010786d820007503109140e81c8030020742e420181078204809206041e0020484405000000a0a00d010350b09000d0584200127001000300340f29690a2209954001c03d060903504291070104c2d451380405040c0740602d01841d1900c8001c9458500341c001d190905682800d510640e0a09803500310070290f00c1400e60a003038420551414040c0c00801413480c60551255813a800c603c031380d808050355030305850200d569a4049401040004003101e9100d45030041500680e12244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667458543 1250 667457293 667457341
    0x316120914060f0601050313170a0201061e03020904060e0f01090b100f210201021002120411220e0102130f0f1a0406181d072303010302040f020c0303 66
    0xb000240c0d04010070b10103a0b105850603500d160a41c0c840404000285030528421216000003001180001c21078001400401076180d00200b4020310342160b0401c0e500103500700c41441140030f6001e20168840031409904541d003d5000903003125804905414004062010f0007a5402c1c0340595052140716080c0300c1c05400001c2c0b0001c4056a56132041441d0316041c45500e55070340295821480c2c1003982d0503407090050040c0142e0768448244858002241c1c0070060805a1120754410320050152410440b6502c42d400c5da81ca00c8000b0a4060345a90a044071140603101c07a1200c01c0003c0440080d01a1510030494400003903101e901e925801c2c4000e0454011507600412241000400149882100314030085500c0007510f07003410030341d0840e90000341c1100c02d07140144c050000940d00c048c590603078900d1000c15109500c00d00300040d0080070940c040c07520b0b0300ba0480032440c0d844440555030449045230f03412200000c1c4860180d1498020307001d8044416024007021042001403c29040f065801050107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667459793 1250 667458543 667458553
    0x9060304170a0f110d0c12021204081c032a02070f032a0302010c06021e0a0c0314030105010219061113081002120403030f0915091509080316120914 65
    0x1034102c4d5a078070b42c1c840070b660001400d50f41c1802c0c0400c0c004442c0035880d00c0188152045440484819142580264001c0f0655407007a80300342440585456007581065083c5000d00202030704952501103100701c401c2184000360090080301c085802003111700000c2a0032500304596950742d05020f01101ca041030403501000c07140b0748070798200c00d200002030150380d03058540001080305500c0e03140094001800110180c20f100c2c90294040c0c84400140c08140340507a03c01c1d0203580d840c90000d1840e4103a00ca880d240c81800d00c01448142e03000b04030042120044403000b036049030b0380d00704100681520304600302951000141c1d14042c0d000709019100b540d80380b1741201c00c0c8089a00b0384004910805500c5843d0140c40004940003903c281c00940c16162102c0020940c00d11503111f02540c0e40040d80522100c42c0c0e502c42c0c00c6d0800148004100711450300240822a80002d500c1d4204103110081001240c1c194a00d80d16040a02a55002402c208c2d000010001120030b80303001e44582015400320500b512034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 667461043 1250 667459793 667459817
    0x901050307030c031506030813080d081012060f0e0d02070614030a0506121209040e16061b170406080f060f0f0d1505060907021209060304170a0f 64
    0x1d03014003126401414034603070500e59224110107840c1606061403070750312030030004003250500002e445064801010710150a15140b00d02e840c00080c120010140203445040024003050325034000c00325901ea8915210021040c0340040c01028001c0910f00d010346481240c01c140e200008120036641e01039003c54100c2d540b50001074541d650000303003004c10700804100042e840712007600800d411500c042d0419403601c05950362181407040766001c1e09003c5401090f140d02626107800f1b4a14048030b92000b40092442030a0518004011402008180601c4010314000c02648003c0680c8803500070045846000e162980c003c6103601034480c2e50300190048001c0f65004c03075841c440e00d020b56002084000d1b0b8a49030010b100030755201c455610b40c002040d590f2800455120700da81d100185c4c5207170300006d2078541041000580c1c0c0002e85070a0071540208201500811450210340c0c29800840354a41c0380e80d15480d103034040e1000600b01c02d21080c0d000c2016543c00740c1100311507803244010f84601c0c5040038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 667462293 1250 667461043 667461049
    0xa0902120106021b0d030c120f0201050604060501022a061603140a1e110111131e030b0c07081602130b030d030e030f031e010602010213170a051209090105 68
    0x11300190805001d2075824a420ba103400c2440c0c0005a05c00e041409500b10315480391900440c0320544680803409c61840e4107000356083c4201036005900300d804106990520300002d5071340701c0d0441c40f03070481640b5402c2181840c0d03100c0c0c1b0240410340300401041e07071504840001c000d240e28001d003c60100d00c0c621140c1e24a12910b1007030fa074081640c2d50703c1c1d8091106040c10710f4200c592040c005002d100c01e101c59161658420f0203400301e502c81c09807083d0313035411602c6040b0112000355404910549a100f2040e880c80d01c040b22110200c0740c0082c3c0c0380b40c0549400050384c48510500c1c0c401007041c003001545600c03c4407040c8803100d03100d00803a11000c15005010184e030a90b00c2c4a40c14030b038180c00000000f65554001e40c880381d40e41285000312814001c090041c00c8041c1d00c1652081074845144008405240e131030004a4098800c520081d420305d008415205464211405803070409924850b007041c10a034108040c1c3c03001e41d003000031103000203141000846103600586a040c0100c02e00c03000407480782 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 667463543 1250 667462293 667462303
    0x51801090b12060d0605070201060302130204060503130c0e040b010303080f09030409230403050c07090612020d030e130501140927150708011706150603060f0a090212010602 76
    0x503003507009891500c0d01c0012000440040140000da22030501d403065000301d0701c24071070f0354072680141d000080d4050442c01040072018025400c082d080e4010442030010a40c0182070300c1c3c005003003000400240c40b0350321740b01c404002c10350440380840c44810104414400075604950403a40030b601c6030406516034405143c9040002c482d010715a9104000800004405502020403a6004112040f0360510104008000c002c00e95080d0005030010440c080212418028500244242d807420449146000c03200920041c15440c0071b0b01c101612043c05050502940300401110030007000c09007052198200000100f400303005901441c41128000c04041c200100c00078000c859006d00010124070404011005c0e90504c4c026118901402c043d00c0540603c9803003007405201c803510b42e100c180d81458071250500340d19030942c14940c2c0c09001400007104000c81d609d40c0248090320029643c1d60340ca004100224581c08905400c0720b00c10350009184441035020700034044043c03203034580780d90307942e02d04a81d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 667464793 1250 667463543 667463549
    0xf0a0801092d020d15090209090f0f0f150a0f14010f060207030c12080702030a0506061017240312072618130203090d03140c04060e1f05180109 63
    0x1303508410000840c0c50003182d940b000c08115000f04c0d440b1815804070388402e40035111403d00d6032011540704110b941c2440700c00c0b0114120802403540c900040301855840c00140401200034401c02c0100341200c829070001c0450800b030140600c1080c03080000c20351511000d108076540c43c9000180421000c1c40407505c081100d030040c0315003804908142c1021605040d080088400321010402030f00161418050824040e0140b405003c2c2894004140486001030551500c200300d2400d0110b813890f04e61031030481d0010480285003014204000f440d100d6480c0c18a015503041c030072260380881c10160000246540c0b48100340900b07007022003001e03520495021034807c060620b000d0100d002c14201406100c00b03042c500500101045c0c08030380b0520200ea0003910701c4d8480360043d2010412031038240c040c660445c248400301c102146411041c0101c940030b41c0c01783d181007068030040d4031069620f40794010b4810381040e00001c003900e60340784044c185a1050081c3d13a900034412440c002d496011f2740c2a0030403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 667466043 1250 667464793 667464799
    0x302090907081f23120106080718050c0f0702010e1207180b0603220c0306090203210a050a1403010b031024050c01020d060b090f04020304020607020f0a0801092d02 72
    0xc001c0304030303600590141040044540240179140e810481210900803503009100ca40e0241c0030b1281080b14100910000e262509402030401061152034090f0380102c5090344140148140c032407045100407a02440c07910718096000e03562130b550120704000858090f04492044200c6400031b400d10103a401529450328050f0f62010302400014211181c2c5840071134546204140601550b180d50741d51400351009030030690312203039180860070071130030100001034102105810010781040c0d1410547c04070b10590f2682002c022010580c0000c103405044004d0b80340d030b401805035480750f07110409503c85400c12038000540504d00980052040d0001c0f11000d54000040c242c0300052072000410b4600f07900c2555072a01542d0b003082104401d9003180708103c00b4101a0f9102561402c0601c1003101c08000328440030710940c8100141310043e5141001c550086606a0308010014036070b500084400300580e004450355401e00144004200e400c19140b150244114465140020001481c10544c00302000083d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 667467293 1250 667466043 667466069
    0xe03010608151b030703020304120e09040602090406030c0b0a0f09060207060804031b03020703030801050402120a09020109150507020a0e0c0d05060f0301061e0b19050a0302090907081f 81
    0xc807200001d2503a00c0081d60050b0030260803203407603200f410b40c0111202c20000b980441408100241418144c0c102c034421b02e080e140c200d00c10000218441e9001d08020040da42c00a2100003d4869801110017141c01544160400f9a02d051684483c0d00847c4400c0c0060311951107404154002c080000035656594020800a41407050542d0803000140040e001d00422043c41090360244020200c8058842da010700720061075807502406040060b00102d1042d40103000101810f402540f07020790040e401000810742e0300080c00141c4584038a60000c8681c01c004020400380a03400500400d802407085d00e140c1d620320303034031010000904030a55107644046020000050741d0314568002d241c0028008080c00b141821940000303084451982c011045101100d458100300904048558010b210101c1c215240980003111030603030100c1c103600001805030105001c1d00c428401d60585001c21805000085c1c40d05102e132000c0c0c84410704654860030070fa01100000b18040c002441c8004803200802281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 667468543 1250 667467293 667467313
    0x604060906030b13060305030d0f0e0d120b0d1b090b090c0d0e061006031802031e0c0603010f0305010516020c1c050109082805070206090d0203011b0e03010608 70
    0xb0080c00f19412070315071008240202031508440751040d04010b600c620010b40d0384401d00d407000700c1624a0420f40c09441450321000360444c96003c40c03c110f8182143ca804103122001c103490800421440030380a40200420300c4800c00c03c503403680c0683c42626a0032a8501140d5100c4044064514200d185908406642e0110713007264417840c090705044001c0100801c0702039401c20509d28010080341c81c20241d0490080402019403d07110354102111082c5540300040031039004a82da03262007040d40c103010340c106840a000007106000c018095140104800c2c1c1c1d9580d1241c4030741005481e030100340c407213501c4c000c0803899a0030300c1c8080c4640f450060f0003829121500b94100301000400b128118460703130020500100085007031040b486405d2040da041764840040c0c080c4021b188509012074101071405000e020002368001060b5040940d04075450707956416004003045031a050550700940541c00e000da021104101c00d14240201c0c8001da0b94029100780c1603007090709032a43c0d4494410070b500030050324 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 667469793 1250 667468543 667468547
    0x1e03020a020103091406041b051e10090f060e0a0b180f01020f01050a020301031e080f030a060312030506091b03010b0c0312040302011b0f0210050619080c040501050604060906 77
    0x413900500545007404441201d580c490305080003118115a250b000074503070b4007403a0030522003a002c0c0100781c070507550000d076105080c8c5591072425000d81c0314001c1c3d01000700301c06200710281d8026040b00414038811550312100a081d0610320380219200703517003003800070455034000e10584901094075046041d4989a120a0198400090710031504500400c001c529084809004150150244000050740c940c518100000c07128200c42040d16010001d1410401088200d02510700651004008039500e85600209000901c180c1d03100400905060510740c60b282d4055000030700c01c00f019a0307169450b560300b01c05012100ba0750401e004001000f4001404890420030103000f03100c031008112440c10710030b92448041c0e540b0071501140142c5d100d00030714010b09001280202181d1482c00e01c4021100449400307034561107000c1245070000d648100080090b51000c4040f9590915200303040a0241c0320b00003161070714a44941035006d242000300020310740c241803040750b0071242650340b5003008a0800c07100b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 667471043 1250 667469793 667469801
    0xa2c071e0e01121401082e05130b0703090611040506040e191509060b0f040e101517010b0703021903110607111b1014190201020301031e03020a020103 66
    0x42604100c41030030f00b01011103091140c220701c1003c2034240200381d80350030f00306440c09a52012901170f101d034031401e40200c5585206d0b50f48a41c1c12000d00458a65118040742c1041d80c4607500103044041d1110501a5a98150340109500d030b002c0c800030b2040030440c42d04800c06104900c60640c10103030410007041364001e640c203c0c640261440800d802a044280b00c041d05582100019610104410b5410440380043e882000f00a0540c00001c07414070042e0b00c40c224482c0118415181c01e1030040c0c1c005001400620041c90150201c6012604071803800c9800800074000b9a083c0241100c5050001c140d1185a0b0241c40300a541b5a000349140f1103d10b03005190b0201c5c61004078240102c860580c000d006040c84103d204042c45e548102d410b141d440307900342c505400f1081d00e0420310741440280c0301e641c0fa01e0300c2c0006001514204540c0b044445000000617115007050042d801d0a803030000c11000f503064009504881c0682006803000e6040000b0b485d106050100007800b5034480034094005500a0704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 667472293 1250 667471043 667471067
    0x604050c06070503040b0a0e030706080c0d02070807020310050106030606021203071b0c06021f021e09010c0c030b06030d050a052203050102031303200a060b0a2c071e 73
    0xc1031324205566079413051103c2d0011070010340401d0803100070410a003402c020903401020940b4142240b0b09016241410500c901c00507110200e0b000180d01007404a03035000c807850198068100c1d03207866860040000101800e004171000039080ca10f0000e0014400154440c03640b01004903145035444000041ea50840000074030350144181c841c440c0d002c551950260030040400b074001c0e09480400f40d010f0541c0c009140300e0a0345c007501c14070021220f0319054030490301402081110680e0355411000682c4c2004241100600038100b8020200070090603448082c00341a040d4103d90246103449400e07a1180507107003052000400910100e8050050801906a003c1c0d07001c83c13008411b074498407100e09992080743c9008202c6582c1c1802000c1541c0103184d45aa100f90181e40c4c80e41d400c44010032621100c4070030000d04201d0300c0c0c0d00510a00e5643c07002a800915207920300c1100c84038038250700020070003486a4422601912000568001c3c012507100041405000018180481c111800d03120101000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 667473543 1250 667472293 667472303
    0x30b030604030c06060602010e100203100b0301030c083f1c02120c070b070c08070f080306090907060c06150503060907060206150108010b0c100c09051201020a09032d08090907020604050c0607 84
    0x31300005403000c4ec0b0401140614015801c0c000b1035803d01c003143c0e14040c8010002c4003145500c002d00341e0301640c600312003158007104203824545c503d1180b101e4034070b5000306a9202d25002c00311240c01c1fa1a43d150707000701000c0c8000c41940b2b02591f1610442840c0780a1a10040d241e86000d90004040c0740c40382040e25100c5100b44c803130500b040c403140c464640d21040020211220100001403011618040540c15801a0b22070001c0003442c2c00d12034014100300c00e40000502160310b0700000b100203400014a2030103004080e023218a549804040076070388071000c0c4145000741c05203074007180c00d0700710b442051000d040781a12090a42d03442c2400344400c96104034051242c0e070003030240040c002d91042c05039030500c507169954286100e0038072040020b02c2000f0250b018050384100300e85000103800520000499410040340c0c00d200d65800b07422034040d0600303200901d109403640030041c01c1000f03203c0640b200d203006441c00310181e83c90805c26a92001c080d100070b03046a200202288282c5420801400e8080c411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 667474793 1250 667473543 667473571
    0x131e06080f100e0c0d150f06120905031603080121020d0602070213051009140109050601110d0f030f150e070e031504210f03020a030b030604030c06060602010e100203 73
    0x20103140840c00c205481036510004c1c009104810100c09010700f180c2c03080b900e51950103440c941180031080c1580c5100b8502030000403140f0254a000d80e91142c090b05400c41e00303899442c0b60380326081c900340f014000c00700c0204548000108417685c004103405820b01c041d012100c18070f0019004c100c201c41c003044040703403456001c11103900140c8a020714200d074034460b494081805d0034036045a6560b041c2580000320040e1502c40c1d40f1081c1d0905202c0c0313504450305510700003580e403655401224008007003200110103100d15000b890310b103a84102640e50403001a03a080103850100c284180640343c50030703194400109074038818045ca43c10b80c410706802c0300890502c030182194a40109042a07050300d01c1d41810940d00e010803050103450005001ca0080c1c0c03605402c2c0345089044c000c0d000603501e0381c0000400d035000c038000b661640030781d118001c5040000c003101c2884c980f03494010102070900c030044652a003010000100e0038014000d0602040800c0c0140807040d443c61501c0c402508000d100014110364 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 667476043 1250 667474793 667474799
    0x703030f022106010219030c060c0c080304031701122001050d14160e0a15030603060203131a060a1e1203020f0d08010324060b131e06080f10 62
    0x254082032105401801001e2072149406400a400e203902c20448100c000844c10311000001c0d441121008c0482e80b188000450480e01300b42140c01000f001c0d0001c20100c0000244010b042d0000c40d584000842417083c00000d83c0c0300c0301d000c114013140c004000c00b000512850100700d0252810840714031281854100c0c14560003084481c00d0f2540442c1490f20402e240c1e0a000c00c1240e07104018040103035500f01841c0c07910b02d05010030304030700d80b9200701600c541c509103000c035415200741c004600464200c0d109544905242044d1810320082c1c0c1002c072005a613042c889101c541c030b0308127940d1049800400314000a49001400700401d144625a2460380319818804502100741708004859140203a0040210b4680d00400e00d161085640d0303004141b00818004100107140c0080f14810192040f03484140c0d04422403102e0041c0000da0000c1d428528003044180340d4204100315141203440e052500100c10407081a9130601d284240a4580065010400036810050701200340340c200e20503441d95503031559 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 667477293 1250 667476043 667476067
    0x11d0703050a0902031024030c18020d1a0f1807030209030f0109030f110c0d020609030a0609050f010609020c07050103090510140105090a02090108061e06040e0a0e120703030f02 78
    0x100c01c2240b50b815641e50a05011f422040c003481940c10415a41f01c22010380c21501c525010011620450107417000000421000260035015590788454480060154003504240940150b01000d4035601401040040303418900d80f900e0401020340d60151100159281c40500702c0107903209482031a094800c040c900c0b0f6100a0034414000e80314065a181c0044030f01e545002070920765400170800c095030001d659040c4650740c0c20424885282d0485299a03240c04040119041c054030040c0500020318000e042010300c64040341c604c1c0e0099400000300030f03060700ea0304441c041303000311207021016a0041d00d045c45594005c0e4400b41100e4003c0b400c582d826009040d0010654450440400340806040010081424645003860b0051001c0c1d0065041080d503500081180200821062082e1414450003170b0014030105507841c010405000340d1f9640b0f4865641514045050f83ca6440c13071441c14000d02c1508070003152101c0e182801505141c034041060f1011409885013138825409a40c0c01c106c5050b11754 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 667478543 1250 667477293 667477303
    0x1305070e0703060602031e070c03020409050601170304260a080f04080d050a08040b1506070302010911030601050d06110d090f0c060201020306221b090806011d0703050a090203 77
    0x2202000d4640c120749000d000c000d0030344031294058020b6620501504810b048004240810441012082ca84600203810700c071520301c1841e8006900541307043c0c10042802404201c99059442e00c0b1034044444039060140b0743e486c4668458404034881a151803154841c0100c60515003440c88011034004450b143c903084400e038800d02105070719400010342003240301c400341b2041e05101c205060090030720504c11005000e8800042000b441d4108000029410f800100d0313000d84001000f44c0300c00d4941000e032801038002d100042058400300c0034583c0e645101d2400150303807416544050820718042c80b0540c0c3d80409080310741101d0300300c00401d0000918030213181c800c01500c94020261000810118246840c102d0300325006801107900404c1004503580300c00082804c0c20408100c00110a004800c03214024008120b1a00304142403580c100c000039405030103602a6080d51040e100b950b661407640090000882499441c14201d500000380c0080c0280d1099500c402c0d84080840c1a42c0141d001034148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 667479793 1250 667478543 667478549
    0x3080606070614011a040b1804090503040b0702090f0405070510030902092517010b0a14030103080c0f0705100f020f0f0105091015051903060905030901170f0f130507 73
    0x64400300100590221101c80103172a0711140d18003883d085c181180c0c0045442040c0307403039010303a500e500c104110b03445a510040003682c000040d2030300c40c1e846540481c079070360203140c040e8454000600820382500f8225507040c02036510030000d0109619040a012100000c44c140d00249655042c1890142c4c8510b450349224460051030041040b6004400c030070102540362003082001500b6800e0040030007600409410369078049925500d8082c0c80408a480c43e9211000c2c008100b008000001048100400b42001c40e0401c01030382d650f07941110f81c990399078081d88952a0321030740f01e640e00b41c0418010340c00d4955400d02841981c0500b903d42824510389602d060400d005031395200d0401c01009801d010003110b4002d600e5081c0099100218030000c1c8a030f00d80546403040c4a1503501d02e0140f91056a000d0085a1120b030512078100b56042c003e85a401010646000c14544011560401c00b401d01043c420f10401101c00b02c070742ca85401079400c40c1d0005101c0c40454407411012804201c040000e8002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 667481043 1250 667479793 667479821
    0x12310305010c1b020a0b030901021c02070c05030f100f060e070e0405090c030c15120a060e1302011e140705070f0b03040c03060b060d0c08040605180307030806060706 73
    0x1e00786035040b0081c4202621071400c0a108030f0010980010303940d19421000702d5020f0721099417243c0f680300f800c0340244a0160b180850b824140c40340b0300d100700aa0041c180c41c1d40559051000d07199141d003456291a0440d035010300a412244003511000599888248140308401d40042e00d1a12104d04100040080c0c64400c085104080e01108500c2d050103150303803042d00080034281031070028010036076030310006c1002071084d003016001d42d00d90b00d1a9400c0c7c80c0c1207000d1340d6100005003000c002210045c81300307016600a43e40f01c08005000851410150030030940c0c1070f95414040b45d50204040d49860050041d0820001c12441a4070240c40e038002401a603405000031346103051802210035071504480d40130b10700c0c0c3c81050040002040052030101c049942000006c26149524070002e1090710400342d0380f401551a040740c50108590040701d461282d0f00c105001c203c19190b2001d54000d440d03145458010b00d074005c0180c4000a0300c2402c249030000070290880e41000c49660ba04000d8405601c03007412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 667482293 1250 667481043 667481051
    0xe21090a090525090608190603030917070b030408090114030a150e0708041217070c03080f150d08040b0c0303040b0a020f120403022d0c031231030501 66
    0x340142603d0300c0c95000b4440d40030b04510860720715001618582c260310075803040c85440400100c01d480440146100c0301400c003400c1005940341d14004d0644180340c0680d429110521040c3c4640c00400154001901c030714881c0076007940e8699891840329408000068100080722403210301106081c000f071f5004080d001008036010380c0f00400c88082c81c885a0040d0b011201d050240401560000843c0390000d42151008680b40c0d0440c00641310400700c1d0350310701070081c03140082240c1190700a115010062007943e8400c80b580351403811083c0300d0b1064602c50b0015002d10b40e250300700e01c1c102c411070310018464880700c0d0802e80d48075400951500040c80c000c002e1341000040000b04285e940703000790300c031900d09401c50a02c4129040b801d518003800c1c1c0800c060045410101c0c0134980208034900410000307258490350014060310165450b01149040fa500b44a660b000c00160320780401d5140d42496a804454200904241c003441210300781c0704080381c0b03c0c44401003030030214401d9032139070007542c09003001007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 667483543 1250 667482293 667482301
    0x1b050c0f28170c0d170f0d0b010e1207050108100803070606031a01061719050403021b1215131202060610030203040803280e0c030609010e21090a0905 66
    0x2010840d80c0c031405403900320890340a882e540d00108100e01c99004003c640e505c0c50f551040803400e03c20561504080580030030b021032202c030660000d100e16030b07080e03888107440d24420b0103124a412000040d04016044510103104551041a40980c0040301c52902d020321a0355000d842d0a540c44000141c0d0030035207070316040c000d210f01844100003504001111050035803400c1d000070004001491071031050843c25011030400c6481c400b242040d41034a8008019070705052a001e9540e440500d0404d00080101c11001002d207000e04000c0900401000985040810300100d4507450000502c4c0943c15096a01c0c443c010441e82c500d10582d0b02c001d1740042250781002030400222040c20044082014010402c010004940c581540c0c1c102c0540c1065542c1c10104445513501c1e044c00301c0d80041003524221030602d801c000041d0440301c11206605841268448000d003500743e61008051480c2c50b40710325141c01482a6096542840404c601c20846c00c2c200c014002540f0146541c2c80700e03e055484d0800c2c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 667484793 1250 667483543 667483559
    0xb07020c0d050a051b060301210c06110c0609010507030c14071d06060a0c020d0302011e09061a0d021509090a02041e0311060d060f060309031b050c0f28 67
    0x485d86a25034038020801e00c50307100e000400e1032205020300d816082e15a007402c4072900c3e041035a10b19065118060b84110342d02c40a00400d00010a14100460b20030440c0100b443d0612000320380040806030b491034506100c0d500c00782ca07890f440300c2044840a8117000324403d03c28007444800090720818103800005c8011030230b4607039440f4001d01058482c401c1080bc1c40c0c0b140b07400030380380109594184d6448130140011b0a00380c0c0106124071b0364201c000e00c820003d2070290400e60020080920413181001144c0042c25030300000205400800d400c02c1c8a00000d401520b04100c040d0760f0348804a0109203402d40074404030358140001d07190381002e150041010b03ca4015500140b40ba43e2058444011103640380da11846050000001c00ca40505800540d01d1001945508400d0203080014405003201d651400028001c09034901c1c1a8001255005001d03607100c0c095801000781d036008001400d040c0310700b801700030461501c3c21518be804502d180309802a488045c040300e91a00941c5c0001120718949500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 667486043 1250 667484793 667484803
    0x303020a021c0503042003010c031d060c1b070909030e040506030a0f0b060d0618030f080f07030c0309061515030c052a060a02180603010e040b07020c0d050a05 70
    0x248008540c20204065040e40c4002071340d5200784c01210441450156103070030741492400c00d20b0207030154200030011418503007503041290802c012025411700c0707100c500d110300e440e4081603c14450490040003a044011000212680c84252180580c0c42640d41c81c805001207071140d1104401103122420303100303124941171080c0d81d40002c040d0050a05807800d80e580d04036240d002c0500800301448070002c0b4426455040701401030304c1c0c0c849010002001c04400c00071041880d072100320000b544190b1404400c910a09826000d549844401c2c1f070540c6503e0f9040d030291107101d990004142d40d440392400440c8e00781c001c9210100072038000c001c4840c2000800789015601d941600113140c1000d405601d460390290031616800d81649004128510f4861103e80600320182080071a1181c5020b003d0810000c1e401046503074511140500c5204032082842401d020900c07400000c83c071054001004a04071045c0789a2081c09441a960300340c0f28440080c11111505005458a50088030003408001e01049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 667487293 1250 667486043 667486063
    0x806221106093f0a060c020705100504031b060507030507020f130506040c050903030406210e0601181104030809010c06180209100503071a0415120f0e07140a09090303020a02 76
    0x3811081200c80103e05aa50f5808102c0c003c0460395640300c500b561510a000305405044001c06568074260940001011034200d4001514174060746006001c0b5165010710000841d000c2c0e03200c00f414800e0944007542c498018001c00e0f60004501500c504140e9030b58400842c1d482001d104c001041e041070800d01040b03994880030141800b500700100040f41c0d90010644084403c0d501d80311000b00220300300b0900007110112140303501d0382044800c440c0518041030190581d80c8003c0c00c05803501c2c2c4c0740782a506036540c0c4220200f03809810001800820040f00043c1400101818102d440d000e49640301030440c1c000100e6181c40d607543d520702070214a00455065008881203841d00b010905000c00031b13488944510450000307c0340d4405084000d00860180d500425498241565003608102c0c0581846200842c001c681450202a103d01800d01d101c0e21030311038603140c01085154105164910f00c522004101d5602c140100340000360042c3c10300540414a110b40e80140e160704038640041e20781a1204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 667488543 1250 667487293 667487389
    0xc12070201060311040b04020702041802150a0c0b070c0236040b0604051305100504020f01020105071202031902030108030409060503030c0a0f03030e0a0c080622110609 74
    0x850030808907a40c0c02d030b598581131044400144100d88180002c009107c0d0300c0009401c14180b00d1600307061855850b81c04880f60081d2204440e140340d280681d08244145520f44021421074900c4c880480e01301d19945900c0714040c20081441000e940000f602d41d1a0400e0200107130310b04600c1c0c1c7e55841d1000b100400310248e62050081c0c2401c156859400c95000181a28090b0303603120001019903602100702084503030071800381c40e40242840c820002824007110140d004c0e034000743c62840d982d4414840c45104034450b0342c83c41998200040700c00c01940c409403440005a03003c0c0d50620b504616071000b98000c10140d802503581e81e10301900c50045d5584c0e03511003031194006000300780c0240004214510903944c0f128000300840d815107070a60040085009242c06882600078400070400c1c84503400c030a0b2412207044600650f10541c0483c0414980740420039440c54504a900008030700489000048030000c04240c00c0c5140130001ca1170110b078841c040990703018080001d0b011021182180c1d08018004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 667489793 1250 667488543 667488551
    0x91e0f090902031b04140109050a0b1203030a090c15110d0e06040b0310031e03030b040e0d0e03030c0609100c05090607241d060a1406090a0b03060c12070201 69
    0x50300001e40720b005502c0061822030a4a04c000f2241d81c603a8028600b6040c1130b00d00c0d0001d540c4034043c007402810100c07800b02409242c05201c10040c500710b030026250800300340c000d520f107980381050417002c0c0944100c00c6650703050004002c60031186410030600044410307a9400500000c007100c040c540002e045034a018480501155202c0c0e494100440e41990001c150b0305640351244c10146500440c80e500103450707521258101d807a581c81504054007598003950b828410b001d6400c04200460b004a9580c5140764414a200944c0502520003805100401000d070707030420a40000003401c000c0100e031450301640240414032031500c0385106400100c0d110b803421340d01300317541000800c01d80c0c4500080980710701c89501450342007540d100c0400440c501d40c00340c140803881076101e52400051000b0200f105501500001034120030b03161144050840304907207490f143d80c84150500c80c540c0c0024107000391445d01d50000a00c43c1d1401c0140d00e003c4ca0303085918960b40c03001541e0158100f28007519080440e410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 667491043 1250 667489793 667489811
    0x6010b0426070807030c33110a02040e070501020d0f020c01121b05041403031602122515030c2001020d1802090c04060519091e0f09 58
    0x45032074204000504010510310071488a0700c1030b4a02400765020051510481c000803040010240302a4101c580700340c00440103030448070010403001002070316103a80400c2c0312004105144521003821401c4094001d0f14075801c90341e004102660041c3c0ca0120b4254002c5400300540c0d641046101c1181d591494150016800018001c0d01c8030710460200d410030269010308061921180e0042e107030150b560201c010030014004002d01250030030304c01c4213075103007c9200907541800c001c0200e481010000d8120302c8240140d50070080100c0310000741c0c00300351045003410016110a40003800701e079500b5140d0010407070b00d03003001c0c0c410034000043c4a00c101811f002040807070b0f980000003c0c240400c1c0c07031142000340d400003003038600a008110740501d00c030b42440c0d80707098840600d0011184071802031b902c066036a138840c041010319220718420000059001c2140704c102c01c0d0300741300884501480346005c1030b00f15628107050803611941c40700916010349000c01004007040000c170b503000500940f4010b05c00c21032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 667492293 1250 667491043 667491059
    0x140607030f031d030307080f0c310b031305010b012d05220302120d020d1101021306030209031501051003020c10090f03020f06011206020702012f06010b04 68
    0x501207040703905254035070f1044501c00d05007114080525922204980e142c1c942828000c05604040c1c1e203c000034468040400d82d50441402111000d81d11b15040c1b480511410107100d036141e620003148040c55013003c07004603501114800039170040d0b00307032200340c2c0c80201e50341402403c41c1c49100405052007000d490346101e04c00001d1408003003424052a060500120003000d841c50312441d42109401d0884a01c402818002d4440700b4003528001e8807803c21031a1030510003030303a402c0c901d509080540d2102c138500d5200383c82018042d1440b0041c4001500382420035030302803096a0f4a802c0440880d1700400c9111a6040401299080140341c81c40e00b00340e5458030010500e4414030728103172410582c001039407100d0048100030b00204090000401c014885c0c19050803007059004040840043c0190f0700803079005140080d009040c0c41250707141c080a0358603950354400950041901f20306110300c07621030748440358501041c030100035824000d110818a0320282617041c1601608400c48001c814801071100d60 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 667493543 1250 667492293 667492307
    0xc1b151110091a04110a0602011509060806130303150b0a0806030c0a0915050a030308180303011406180907051902190201260108100b100c02130f020309030414060703 73
    0x20003100310f01009900c03030781031202141404011864011400344400030340268154400140310031407500c5015500c1c0ca030051841030782c10324403403900558494000b040c83e8070040740f0600383d968400d04000481c00207071551072400101c035502c260f038405804140d4505550b04074094540c8081c00320013a2960769039001c002030007040c1c00e0003401e1425030f0b13403c44100d5108411481078081e0070000c009140c81750307481c030700184495800c4072104c2d9074503c0003414400203d0004207030307030585000d81909041000800f0502c48203820000441c15210308040c0540003d40b12500c400d0301604190344c0d011313542e1904820304400a070b104812801194800c030310341698000c1c1d0441000300c0c154240780c020801c2402c03000c0c06851a00c4206109502c4501d0340001032100000550b0006c3c1c118054014040032072141c003000301a03082002240301140503c01201c00601d42100d40464480502000152400e07207118410100d0704220b40e501e01c640e10005041c4007000210b44507003904101210403910303100340c66070018060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 667494793 1250 667493543 667493573
    0x10603050a09020405040506040218041106090d12081b0408030d020705030c0f100b0a12020d0804120807060f0908120603120f07110307060c1b15111009 67
    0x540d9100419110040c81d00702d403980300c2e00244140190708141c01c0c441e48a28060b2412071080318022840940143c40d0403510303100700e8004140e14482e500d42403d000c03032984001d0343c01d58000c041c408079000040350380310210043d60140e0349015030f03481c000249104180e214146a0342d0315005001c1080014400002c40b464490b07614405038544400345061071940c043c002d800c1d800b501540c40c41c40364500c0005001c100b031313600c102c1040c09162001d0090021900440c001c1d6403a0030495081070300941403100c071780215140320742c100515007035072070030809100e81c500031089855640014907841440624040d8030300545100340200854501581c5031a8284150741c103500b805e0100c81c0014609a40601507107034280c4590b8032859031a8200100743c4c0203544022022140c901100d807521030103050019021054a0f0300c2e0321400100306060701c0700400c0713032400202207441820741200410903c0d8402490800c840140c1c0350140403030524860b10b810500d0a00910018515050310301000c103c60f40066554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 667496043 1250 667494793 667494797
    0x1050111071403030d05070503040c050a030b0f04111203091203040b04030f0c030b0703060503010f05091e1207051e0d0203040509060102150f160c02030c1504090c0f0f05120106 78
    0x2902680b880840d0950094801c00761103c4d140030100710400750020011441140b00c0c460420f0b0303242d252420444069100e000c0585044400e4000842490010b00c400d40c00c136000340c444001c01d040e01c900040c51481010300060071a08082502e01160400159074091001c0c1e00303000d0743c101810186c54070300314081c0784000b030f201021000d505418484510741110183d81c000c448a466460241400b80240030b088c071440d0f0185d0700c2d00d84460301e04c9200e40700b014006c001d0880607052944072480700f8007000c0e10901e100c0307000340902d061171054089110001c00c01c2da88658040d01107900e08404140480c2a1144804601d400c69034140104c10340c080211030a0b42e908852025050311001c00403483d11440c401d0503595001008240021a0000d8510394400c0c0c161603144002c094450000700c86400460030025010785c4040f075070141d10310f05880000c0a0312903040704141000da6491400d002e0360802b008020200301d403030340000d07001c80d4030035251910440310707080691a0410407440303481000320501c03030401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 667497293 1250 667496043 667496069
    0x18180f15040f230304140609030c09061908010c170106170a060b03070324030308010e2e080111040305030a03050705090307060203130501031e05090a08040306090201080105011107 79
    0x8125220400c42101059211420648040c41c0d0b030303d40d540d80c0107010700501a05001c84003c2c0034540707003080301c9207003001401400d11200d1400c24403106100240105a200c404030015514424981d0b0364070b4001e1040c84000302d00d0403c28180a0606101c0700501c844100486c001441b4175500802a1240490310f08030800b615642c6120364401003042d50030420840070000140100b095068100c4030085e00400340b01c0180841400f4070408121107444020007046840004012116a4030300c003613440251551609505030300300b82034a00383c0342031440d0385a02155460062044800910031020240d408241c501e01d042c0c11a100d1aa60b4010340d4205002c054030390740090807151045003035920510020b0111a0315607200c24000e034403078000e03125804004a04250001e00b961103405020900781248854414518151101e20040c240c0105968a1032003000306000002c0c038214000c06c0114003444c0001001035003071000510038281a8412410056070b04900d0515202c080384000c12a110085462 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 667498543 1250 667497293 667497323
    0x60d080306180412021c0c08070510090b100f06080c03060301060b04090c0809120a0804051906050406051b0d15050d030908061b0706050618180f1504 66
    0x3070800b11081030807088001c030442800304100381c0c0c2091800c642a56001d41e03108400e0300e1070064203d802d51246a000402ca100300e2004100c4400c0103100c4203004130142c0d03500448590000c016121139600c1141c0b40101d120400840600d2004444050a05000400425440c00800400551010380300324400c031000808907078156002d41c800c10041020094054440e540c440014000703015018140b00416a00c5000880202d408165500d8a0383e820021504010107000121641c042c0100112034501c5140f050b4440310042c8800518014810000804c1910b040c1c40c00a060f2900030f044104842c0c0c0e41d6242c462108008016038071000215880010100010103020346071406a9210030742101c4c5076550502072691041440084e1a07820044030075645400143c143c01003603061285910a40900c03183c4001141600715640164000740b9003001c1c01384036030191001e1407064514800541c841c84103005140c0017400608107504c02d54028024460070b031b545d0000e0b45180104010b0103480b16402003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 667499793 1250 667498543 667498549
    0x30601081512010c030b03061b07031106010b071208040317101e06080c03040c061b06020a0f030501050109240212120402151c0905070b07060204030c0509060d080306 73
    0x40303070460328000c081c50140d00080b00035074000e0808000100000b420500480c07124200020b0441c01948100b039a0f280030400c002c0b035800e5030340084004a082180c0c4d090072aa100204003e00c50181c0b5072000441e03546d03240303803411455050504600d081406074280c100404039070085801c041007020048814101e035541ca61001c6203102e650807a440ba0190540f400845207103070143c44003645e24a44500c2e00b1521500703413900b4540801c50b4000c007000d4000d0010b01c0031174810004002e09242e030500d18000d03200780e0390342c200507a04101d202d0000a010124203100040d45406018018a42800d115041c54100f10800c80356000482148900e0b544444054854a1007007141100712100c0000c03142e201d00480400240d000ea0030703641030f442100d040f00d00e0b4900c00804000c43d410641114060746503100f101ca0000c0103031a0154060f945401070038000034010000304011b25040e4496100181d4030b509500e040e0801d00042d8000c14018100c03c03040055a44850181703100d46030300501101d4880d0ba8181c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 667501043 1250 667499793 667499821
    0x10f06053d17070206010b03041b0f0602010516051c0519050c1b010b0a0509150307081015060207030b101206060311010e090c0f04080f0a0507080d0503060108 70
    0x16100d041034070702003800d0302030380201c21001c1240800250b800307940b11440126175645080c015010508010030105001a408040200a9210181000c0005943c0300f07a034030b035445481d6203c440940d44031410000550101c0a000040c01580e051980c240b00781d61000c00c90048890817860b12560392100401c0010000604202c44240031540038440b614041d0b02c00d050b0b0780c02400010207110300c416003005c007000c418043d1303d20900001d0810b1381c0b628a072604007c0a083c1c0540f600d4007010b140082001540c03800c1c40309001410710f9034000c004e20000200304204480121180001e03a1800340c1d018004d45a01140c0b07401102d40100103010691602949420300c40c0d00d581c004e003440c0c00968117403030070803d4940114045a018981c50800098288015100031002c040e0451b407100ca503d00052504104001501d090004800f94030708046e110b80000e813618500a0400500340d12817a90740080001c06c1107181702500091000e41b1041ca41041d000d00280005845176040c8410080001c440200d0948 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 667502293 1250 667501043 667501129
    0x601030c050910360b03060f040902040216060509161a03071206080105060108130b180c0612090d0f050306060a1106040c0302041a03100f060509011502010f0605 71
    0x2440310512864444d1003c0c01c8807840d201101c0c220503400540d0300c400c0c0007683e205103405045003443e480004200801003980307990032a84503034240300700c0d11425005081002c91620607400059541400c2c0c80040c50401804192005049101801c0c000d612418500b1907014500c4a803c60316525881c07001c1d1034401c000750701001c4040c540000026054415040380e401002c007038071844499101c90000c45841d000f40716014000b0000b0001289101401e03084c0c1d00071040c810703000d41c0c042d00d0451000484650000071182c085070748043c240006a00148441082c2c400f00c0e0900e81c1c1e280c0c0c01020301030421300000b00150b10074000802d1099126020b06121a8801d02c01c9050f00c229182c03502d13200a0040c80b074001079000e140b5043d0000c105804403504402c01c0c0200070001c1500c0301215002d0405040350704280f40c965520381c00c0c009001d40380d4080c40340c041c2c0301ca071079070711160318003803000a0840b820746404640700c41c00c1900820103a129190000f400d500705104036003031280d2942071180040000c0c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 667503543 1250 667502293 667502327
    0x70212070515010605040305151504021305090a0c020601060c0f06020a02010e0708030c030904050402130507020a031115070c030221040801150b04180608060f0f0601030c050910 78
    0x2803640c0801c1008152a103010b05840c102811607600c66004865502035400001c0460b0300200100c9884581d10004992254901c18000303400854035010a0a9030001d83d0b0f041c84100c40c00c101409a4a45150b00726405089110304114042114400941c5c2c0c3c00e040c4211000d2041240c0980240720a54101004503070304200c080d90f55045c49400240204105030241c030041c018050085013608000c0101c1c0c1550344003000950800003407004000007410b01400c126445420a1030211900300d95000d458416102a00030300382d20806c508018101e101d8200d02c18034541c000d91180e040f0395050100b02d64000c500c0d444c200c070900d038092906070b14021501c60b4020005542c883d1400403212100b000300300ba81c0381c0f14000d1200071a01118080341c40340600545c00e4801040c8002d108a00481a4080d458803451002040c895502c1d05503604000b4140c940319019161300042040d80f1141180c0d6580105003842d00308051400b421004146002d80e0300464415a1000b0700c110700988070740b000b264441414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 667504793 1250 667503543 667503547
    0x100515040e04080306100c0302101d010c050a090f0806011401030e010501032d0b07030e0a0b04051612050c010509030f01050f180607021b0a121b0906140603070212 72
    0xd00f403041041c0c00c11207105100d5154010a40c1e0a64498450301400c4c55040e0001c1940e03145400301417010303104401c07040605a034480302040b002c5c0024069205016410340b5080c0c4c0e240305c220f5004240c00b0300f9030400040f6090301c0e0320400c6210300008000341110355000d080d499911b10000120043c00e5a1070106000b503081000120511400d00c84101c294030701c5814000d0680100600c1c4a090226120058030000c0380b000002e0019010343c02032111140c0c200300f640c002495039910044004411b4078140c489503c02101821040610241100604419210024019056176405555071043c01d4024104800031411901d1514100020340100d81940000d004504c1c03d1015a41c0180040303c991001110600311001414130104005000e08144d5029001c03100c1d0026440c65014091580d5a0308280010b20001d07100c4d82c1c01004c1c4032028800d00315440205c20704885108003492603000300340c01138a0b1401c10011080d2110504000c8202640c8942d100d40e10102c069081c400900c0764030b82c1e03540f00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 667506043 1250 667504793 667504801
    0x2070b0411010f0f0507060c020307170a0e04180f020a09090f02030c090603060c030c0708030702030703030608121608091206072607080411031c030f05100515040e 72
    0x10601e00880000030030f988018540180e03c804680001001e581400820002c04c540c402249154000d110320b0100b90044074506140303941ca40030105038003040755100c46800305401c40389542c40361004124207801c0398144601c6801e4505603003243c00414004100c4001104440115201c044034503004040c05407042202020702c0c106680001501c440c124400d000b005080d0840740b408150490080e0710281c003d1046540b0708640d0103c6600280c60841681d030706008050020700c20800441c401d0449074080d50b150100c0d03150140c02d4400603080a000b07038100600707003101c1000010a0343c29800446071032102d6240369080c641081e2017181131003500304103600c21003c0010340001d40240030350411768521603005245452081c101130048800d810305200c81c030200d50550b103d11003198201d80070303548680c40f035040c00d000203152842103c81c200513510000c0041c50307107503018400e030605141c4184003440186072006420169040300e000f164415541e6040b03050072038400c00240c40103000700210f4035155040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 667507293 1250 667506043 667506053
    0x40317061504080c040b0402030108120a0525032c041a060f09190509010b070555020103180609030801030b07020102180402031810060e0106051c0c0302070b04 70
    0x4e214800c0f800f130750400411011600f00341c4210307412118064050406c00016407030300c0803140e1211680500300007092115003562800d55080000c028444e00340c400b01e844482c0b801800041800030020200d540070741903060460341d003010100038814211400500b1064510081422641c0c4021543c1c001e580407500e114610100d400903c4406800c503070302c071150b0070780403000380020341d1038040c40760412064401005441403608c040c0c000944250700703813800c0109410f01500d0380030b018120000d0755204203c1c0c0d0b1f5503c0e042c000c0c1420424507000540f4a507440984050340c0ca03411410802030405945c0c00750280ea0062540110032016230260042c4854103260500800110088c00140c2c2c0c0b000b040400314003d64014800c03541c02000483e00b5491400c06001000001d410041503110703d8440345924814606041c0900d0b44180c80c40100012010700302104c01080d020142c200c4000d03c00d0410042000391030180710810000302351000401d20b040c15000890217030107680341c01410343c0402c03028442044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 667508543 1250 667507293 667507303
    0x60e0d050618010506030a05031c0209040203100302040507030605150d020403050f0f0d030b1311040504020f0d05130f080d0f020403050c04051b070206090a03050a050f0c010804031706150408 84
    0x10403508004d01450700c82c0380416840b42d1030503034010110b5000b00491604510510f486000c0504841c1005040c40c00c2c800101d4184d82c0100e59943c0071802d00c501c24000c42c03400744901504403c06242c01c01159080002055410031510340d5103000c8030000c1030b13141d40c404043e012603015561180c20b0340e4242015504156440404d400c8111a034059a071049042c81d00c2841401c80c80300c2d0007800401e00008010502c00209104806000c0500081002282d03035283d6000410305000d2120344c4a940f003162060060440350050a1011049614203050001c5000f210141f0b400d1500484003664800f44c0c02e210304c0040501100188001d400894000288000814203510810061380c061240b80d84800d81245a40541c1005c1c540c032060070702c140405424010040d0800490103071601d140c142c0c49031550392038016660400c40300c0e07902c10790038110320030014011803002da1420300304071040d4245070340c0250521000241d01445040381d0000501c0750394651512240c154900440c0942d141d0700c0d807074415110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 667509793 1250 667508543 667508581
    0xc07060c020706090902030c0f090a0f270207020f01050d020c0a0c030b0f09031e1c290102060a05040303140a1d12040b030c04090608030301030b070f09060e0d0506 72
    0x822801301000550001c075008a0344143d005c40f1250b8604408582c0b0508a5000114196004019a240403c0001c650755211000e001040c4000104591500c240c0002c0c115a20081202c1c0f40148000c50040c0c4480c444048205424240542c80d00c0400c2e01c0c4900178021841c0300c5980d8812840c840041c812500070040c207880c0154000780701940d413001003010a44065902403090b0b0300400001c21003074880309050a101c41c60327140c3d4a19045560b9103d4102c46a010b84a40000369548001403084000c918681200070400c49021461405040082d442e250014101c1002c240c0300c50004081601c40da101a0000783c0d10b0448003414140128071100610210003c030b51428a880350b030b100104070014118a004c0e640c3c0c10224540740c01c00d0801101c0350000b4140544144081c0300109401503c5d00606001d090624015603c941c5503040c503840c0048044d000805101c2c040886410707081c1e010041d10182e840138101114040e030143c02069501d4150303e40036100380075a50a0043e1284003400d04210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 667511043 1250 667509793 667509797
    0x804061707111c05070602040f050103060f06020d08040f02060a0c05060601111002130b0c0a12140d0c09050301110d0c020c1e030102250507210303050c07060c020706 73
    0x115901d6800a84207000c14007080c40199004103644501030304100040110700e506490b1079401c0100c690780c4d0a0070303a007140d006401c01e100c04038800d01c903650b0b0512a000003400c0341c0401c0d5041c54501140070b51200d1085080008000e0b00b18000b809008804001d803403501c0e0302901c0595902c20300040209044d119040c00c0761f9501490707020034419840303440b882000241e40405000101a0880110300a40c4003001000402000e4000054a042d61202800500e000312000c2c1403070444070b01d04a00815260b42c507d0090044490b0803a40d00200401501c6003444001400207032180a41305c280c0d03501c94143e00c52581582000a5004504005009440c900c000c000c0c0500c09050108801d82e210886241c40c643c0200c10b1005640d12001d107440e442860600c003400061801003860f04040c4c0b6400300080f290a036490b050355480400c101000300c40c00902c00c22070302c900c9401001c2c00340101c0002c01000942003584501c04507004041080c01c403198070b540040e00300209800f41ca4081e440d112a0b100b0400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 667512293 1250 667511043 667511087
    0x61a070305034c0b0406051210030c060804061103010b16020301060306020f0418110a23030106052115010c032a0209010905130201140d0507020606030d020a11100c080406 75
    0x5001c0c1043c0017070304d080d03580750b4440c0c03401c0054840700789074050801040c00f9240c448080000005c102400c10b40c1018141a60303960007a480c0504001080d104010900d4442e2042000104120030600c8240c0d08085c1c40da01000085080c40c1c000680544941d130009004544005003010825005000800440b4200003100308000d008401a0081b185c4400b604505003a040045e126030030312620030186040440c0d10400c0c070000d101c402008454200f40c020310701007000040c40c010303000d25020440ba072a00c903034551b40a031441c2039201c04800c008281d10140c140004407200908150042c0c011400305000c0d940c1c00c090310000303511604145026090240d00078880d40d400031404603c0c3d402800e03c511141c603590103205540d9801190400000580c20243c40c4003071046a0100b411230040e40d0094106a000f00300b1810b0100c03c060402c8100b620740819940901040d030001101d1140c8440b004a007150200030032400054160354001c50541e0003482564006030202e2a00d40040c8600540224900f00503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 667513543 1250 667512293 667512299
    0x30702010e010203060913080f0403050a0309170a081e0711010306061d0d0c0905042003031314012604050d0507020d060902150d061a070305034c 64
    0x68204e11013507564940010f291400a0000720b14a400c1d001e1040c45404aa4906203c3d951540804d40060308110b030701c0c1e04041d40200505900440071030140224a02840c5608124003200303640c1c002c541c0008107100004103581002650082840c01c07140030340f00403655502d54a24280d10f030410442c400c103010038035103140401c805d0310540030600103c03500c0001c101c606100c842002148942c00c07208950210280340003040c090309a00070a40180d02c0343c0d0200300e072400e80703503100341d64445807641d514089d610034000c15041156842e540c0c0201c1305c1820382102401d50b4a801220000c5074901003841e0728810601c00210303a5122808984030701d000d001921000c50022070200c82070b2181e090069031000c0c440c040d00300801c600d0b41c02103008074801003400900b00c15107220044070b030300404041c210460b42d40c072041002d070801810100c20102087c103803518001d802c2d60080c0050202038141104200c04a030f4444001151004c0c440c440c0700c03050041440d4400d41c5c0041c5800804e40d03030701e144c000e4031120400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 667514793 1250 667513543 667513571
    0x8100b040f0311040b1e040f1808090d0b04050307120c020a090f0b041b02010b030c030613030e060d0b011b05030d0926040815070e12031e03070201 65
    0x180e4140d551002021001c1031841d124001c0d400240b40340142d100b941c9a205c40216a41c45107440d80490700b0054504c90b80c004441044120303100f02501101c0c0700d0403c1503024001c80c02050f2a42496400845943c07104080e03404112289000c80700201200010820b1000380440000a0700c4243d10680c9207100c190742d0b21074204c800400c0710300000e4102d40621802d0182038080e41241d41401c800c00f200040302e0381410002002c0e90006200315442d00d81072551601890b034213004881d07400d0400d4008125980b0300e01c01095641000401c82180180100c50101c2014400c0703486440381c1c80010076141e120061404014010840f881c0c410f804103499981800da01c8410031203618806800001030f40c10000c861600402824070040106c0d04046d486a4480c5a610b8020040e150b103400c4000351034640f03041c40d080d1480c000708918203c80600c405002c0001050340040751812601d415034111007000c8170707500d000703145020b208414010308a0795890704041e070784608007452103402d442c0d00910191080a80c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 667516043 1250 667514793 667514797
    0x50714070e040b1b0313080d0c0905010e01030908090d080412080406030e0a050601030b0a15080a0203010c0c0c05300d0e04060e2e080102030f0c030601050a03050903130608100b 78
    0x40c250b826134207000190000c841c0c403813034608045c041c4404900d800704a010a00480b900c030480d1402003281c42c3c4082c000c42d40d005202d41c28210b070a003420012100c480d12410701c5801005800c5102c3c01d200740d860030820a424007582e0007003103101c16002203041a4505102644c015024450000307160118009650b0000100c0030420b68001002c0d0906034295190b0740700b01900144002c2e01c480d00d0700c6000034401c08a000c0d0400070009034000d82a181c0d0f01d48100341c21b580202241c241000f201180e0030b404034007815061070441e94111071500300d10703204d866105140110741600140d400805450b6561690b0041120f400302e11555907000000e4280c4e1042100701c4110b80a05101c4031844000180c1c030054190800380800c2031070081e082030303c0d00e003c40d40c84800b800b80c1103001165004808c1c016015010f60a09400020000e08e803421440e1000009140d03014070510070b0101912000462841c10090044458885403840b842d80181d4458402611944095440b400c544c2c1d41c09000081068088007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 667517293 1250 667516043 667516081
    0x129040509130203011113030c080c13181707020301050a021c0e15071812020f270c071b031a090f0d08010302040b0109030210050714070e040b 63
    0x1c100340d466210100701c9468215500c5049030190340c0c610104036403650040103010080c0741d001401010504502d03012070b41c0901c1d90721034892903000c1c1800d4001684c54030700d0005240f801490003da08001c00c0c00c00b0502086400e40a0710402c8101d080c4401c2d91101070007440303014002e034024810354842141c980100e201d07501f00030503507004441d418203c401ca66040313403003440c840104580c00c0c00809001412050300507070b400b2000c030340003a020b03112080c06800c00070300410031035034030f0382940d03100350007260308c1150aa240030f10a018403a444400048038510700b0000242d060350500341c2e0314018001c14490740c80882c0540e5008185444028501020784140d020340c0d90001c80c0004020301e82902038089000a08000e9071409141080c017042c4100f0061180f500c00c40e50744031703104c55165006000440c0c1c04095000c0c10892111018030150729000006004c0d9482864181c6c1c0e21951814003082032003000301500d000d8022040d00240b4501d04450383c1d40994086c11101c84942c44660441144620b005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 667518543 1250 667517293 667517299
    0x31115060f0d050f01020a05120907050306010b0d090c0605031905060d2402031311041b0f1412041a1b0d06210b0c0c030d2301290405 59
    0x7110303240c1d99040c41203041051502c16030888242c0f01419582030709907005524580300150b804185000d4014403002c1c6103400c41407800241055a06000100c1e0300e510050240311042080050840080711a170b90182c241503400420490150340c590720020311544c800e0325250802c2030350001003880800c1501c2201d0044000802c00001c040d080e0b5603012114000042d0801b681081c41e4200b14102d42c1d40c00158405c2801503a8017481071800d1900103425522110400e02079858900021203840500c0b1010010400c242041c4200c0d2121324011101c0030800803d4400e001c030080380c00d11300c201000c840300340110b101341d011b03500c0c260340a021004804811100203805021110b5195160301e408030080009004001c07000c10059200c01e00c502d0803440d03c00070044010604521710080c00401c240040e00a803040c02564a805104222035550b80101c4903030642c0d0940e01c003888881d903403504155403c2207608007010485980d45801151103103c804001d54004140844866080954601150103540000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 667519793 1250 667518543 667518559
    0x307020d09170a1202010908030907060306120f110303040803130e06040219050f0d05130506241201150f060306050a0f0608330a1a04150201140403111506 68
    0x84d241c0d91384800c202e405460940d580c074000d80b008078030300707000862040790500001c120007468002c0003001ca50041d445889140f4008150100040c100b82b0f034482c0460300b007014440f0030302c0d04c0b60020781940f2480e40300d034146210004403600e40501e0400c101040750708540c400303e440d69401e01880160301c034864500d0b2640e5500741c0406291805007010b0b14103500140000c41c00c00448210303500842c1e0059030b11b07203021101080542c040000811409a005034011010401003c010500c03007494003c050005110b803401178005104280f0945c4180d09200000d60726082d031542d44c180751445160140a02000242004801324050910f007458500300e414007010300300c10324900340702210910405016408000b0708150b11141004601181e80903179443e06a071100c41440030020004031030110350147d18035003a11071a01d40015615401d5808581c50001511024030007603808034010980030701d92840d101064410300c0181580824403c100000783c07000c0310001501e0328485000c041040f80d24980c0141d10b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 667521043 1250 667519793 667519813
    0xf060318010f09061823070504060b22180902030c180f01080708060c07151b0e0307050901030605040f0f050c01141903180b0a050a1104080316030e060307020d0917 72
    0x71010b5980f01b0100e00009680410762603100043c203a501360707844104080b40100b602644075800001c5102d54444100020030103914042c2090626403000300301400e5282e80710600c905640f41480310344000310009000c592400403070050722a078a0400d03101d01c801e000c00600080b07400c2070006101b0f400c2d50880801000c1b13a60711050600303aaa0b0000c08112400341e4103003e505803101c02c602520304c10388481d82c1c130701690b10b8034140c00030156042403820354400d0b44111000c000d10b403640a449030540303820070404580386d525400c21503905400184002c2030250700381c062030140900807600d0000420b00740c3e24000380401001c8001414080c03851003c00d800024800310800d40c0c000d034091781800c400c10705624400116501d440d0003400c002c851210a0640307544c104040348905225400c0d880c0c0025413a02e00f8141403803c0a545c90182e1300200400c00a40408607081c14090382c580d41c0c20741b800804140e506e180c041c0c0025200c0c442404c508010944240000c20850382d11102884c4410b5240020300c40340c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 667522293 1250 667521043 667521083
    0x60807020d0804020f0109030503070606081b010c1e0b01030809031c08070c0c0801020f0903070902070b0123090103051c020607120906021303030504060f020c0f060318010f090618 79
    0x41c5d80c0011130b05000e0310352400400240e092002d092030a0003040b0000703860386130180c164100241d200c40380488011840e06d1503c240c1c1c106400c01030068012089400085101d120511003141c804c50140145082000000c200600301004241c1c0e000e080d0240c81098100c0c2c14800f1202c2000190031303000c1258240042ca0280c46060301800d40c1e4001c14128901c16544d0b00310a0172a03000ca261008034050015040d0005d0908100e20001001808011840c1041d2a2100700c6041d6041c0a1542040c034100c010606c80d041e40000007804942c02081003440f541d4900e0080d5880200c6d501c4e41c4290706003c032503030721842d0020403840d02c103c4140d103449203104240f0305d5a80041a46031812503030683d0074400d62a80c5000b0f0b00c4050f001d50300c00e88070940d0311800c05101030304002c05c2e0f45180c070455100041c064801d84819900721034601d010340d00d1540b039454403e00414403115a026498542d860300076003031a61034051b00a408400e0181d030080015070400c400e030807480c4400b41c801501c40722040b0344500c1e21035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 667523543 1250 667522293 667522309
    0x708070f06110309010b0a0816051203250b0603010c0905010e1903050a030809030319091104290103050f061c170a08070c200105041a04060807020d080402 68
    0x5440760381c000944989050030040550020384400515030341d070304803030140d600700309800002034207043d4010b0034403010303d0301000d00410850207002d020386010780c2c1c031010411081040d15413103015a10200048100d401190004a85a820a035210142e11012400d2420f0600c0b50b21600401035a030b5200c418241030040d21010b08842d150307900000c00381c01003003007081013003000c1000e1840f56018001080c128203000700004d001412481140d0001c00500100743c0540310001c00c00f901120f00400c0300070f01410042c030018881450380790051f0500e07c500d80105c1c4101c0d8001f00340710385144007400702c0444800450441d241105e44460034196a00420321619180d00200c0c00c0e00040c55059a410b041a65420004612582200900c9001240c80181903400031030113036101400d480d0244940c2001e40707034410500551520207121903158001c1d1071031a403042c07007200d002d0580d8406420042c2c81c541e11081960f44603116080004040301c000c80c103050302c041502110340e42140c0c0c0718213958449400300a420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 667524793 1250 667523543 667523573
    0x13140904060c17010b07030f020316230d090602100605030304030f0f12020105270d1218050a0b07030b060d021810030c020721142817070807 62
    0x11200b031000701101c0c3c0b001e440c0500d01038484601c034280c407020286000707071140014261810942d00103004420b100c0c881641c1c452003040e00015112402c0c41c1c046020185445000c40d8214240910030003020f0094100210000301c6030381d0380c2103a6080f4484801441183c03080c0c041c069064200300010804104203101a4485030b008800b146100c415607a40c030702c51200c08941c2e00c07015035100c004004108081051780c00101c000c0b250442204074406640d6034562988070649810300108074002c100010550f408a032000c00d940400c01d00300714a80c1401e9613a1681c0f90030468442040390000341c00c2c1e80c8280200180072201412443c107000c1c0c41031000020350080c998040b4411041142c04485581d200d4000c481c0303c0c0b0035100001e04404001000f824002141c0080da510760080d8a10540c07207000f03464000a0a410a80f4500084507520b080c50502c0003801107460012540b415810191070714031048481248580c40e1040001c0c003010b80302c00741d0f005001024000328401c1c8041c1010801d00714098800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 667526043 1250 667524793 667524797
    0xe1627021204031d031c260c070c1d070f1b06050a1803050f09210f070f030f0803070309200102070501030902030705190e07020313140904060c 63
    0x1010118040c070500e01030101d9050b030014601011103c5550038405600f01e01000c180c0207004503031007060f008143d02e045920031600700006040b500c0d91b00040c4240e103070301c0780d00c0c003031114280c80c20403411140490704628801d541ca031918240001d03008c1250004104030440f220414140c60352210b80543d860064000c00500f44070403034080407420b80341c000504005610900340040c0c0c0d4140410790300e089620112080c1806000c1a5180d008a5003103400e45483c0e01214401ca50b403000000d01064000301700034030641c010300c0281c41040312500042003601141010008031112203540f0420051403003030910020303084100c0b0f40b24030000b0a4810008540c48550341c01d000c00c0403e01c0c7e40d12070091650600003c180c2945c13100c8925a10341e81403000c8002000309203014032102015070002521556903218032442140c980c5084003281d0f03460400d010003045414480c4031189004900030352a0b0340300d4aa032002d4008950004035070360b00c0094001101d03042c0a007280b01a956584d8660008003080464201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 667527293 1250 667526043 667526047
    0xf0d0503030123030a03090b1b0a05060f09060f010303032003070f0e0f0a0e04050a020d0f030806061207030b120712020f1c060b0d06020c010e162702 66
    0x4510100019802020900700d880800f80a0b002041014507a602025120340c000700d07844004070342d10400c4038094503400c03003140356241d00900d81030001003202140ca003514001c001040003405000b2072600d204002da10030689255a40409240e11200105ca0040c0d801e6400e200600219100e90f004c014a10b0002118840d11101610000250f03041202e224001640d03c080f0303440d11310381c08642c0da00044025242c0c20b207428585400640f180101d8025686030300010b0002030b00b804000c010380b600c0250060680c03180e00741241041140416180c10079004150908003040381c50510030112225202d001b10440102d46841d10110060a17001c10902d83c850341800301d80500034028816100104030340c03030700601c12040a10601444c03464000d40580f0403403010107441818540010b050010f1503200c440003481c40080c40006080088112000e08060310101d01b0340788209055201c007070000300000c200c2e1941028500010900708607405220450203000c00d0315a400c94044081c41580780300c0000141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 667528543 1250 667527293 667527319
    0x1090e030d06080f07151d18010326040b1b0f060106030606090503060c120c3f190c0504090f060e01060201020f04140d0f0303050121050703020f 64
    0x18090300e005400803c01904440701c02907080b44200202da0051070490301503030b28914000c030040c000d06c09000c2c40039103204908240c2c89040e601c200b01a0f00e00454a041e40125507100d0511040b014104509024407401400c400d0300340c404e00328140c404640c500e11069117094000498405084052006814988501c4800b40e95001042c0019800381c06e4a0750006511032a0040c018410107140d44440d010343c1040080c88000f100b090100c80c82d000c5141d015043c40d03107900c442038480e841400301880845941101040e440041d040e090120320790a88840c42c0080d40c00c40103801444402d0312210380c00c01e82c03003224204140d829044001c1c3c100d41402d0640c200740da10394a00065401041482d10169502c16042c001c030018034810314050303c45807000b1800c0c02464600e140e0301c1d1240e8081c80d86142e5920141091a90380c003d03200b14a41e6014030444d011050034980034018000038000d41a444100d046041c0410013013000c0c0203c1c40b074005008011035031568003401122403454030041c1e00103040903429 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 667529793 1250 667528543 667528567
    0x106050d320c0a0f030203060403180b0712080f0f060f04140f0f130803150f1207080d0c02030c0609030f0a050f0c06070809040f020d0f0510090204030b01090e03 71
    0xd00c181e40c4080141240450003810400b440449420100d901c10000303d00340301584000824960055060500d05940d0000c1ca44051002c826544a2980c004001448c002040300102d030030140f40c012912141c0700d68480b1a214620440300701c1e83c2034800b80c0c0240015000c1d14181104000111002d0000100c1c0ca8205a540062070341c100e440c0050b41080307034140460300040642d0181e0001d84d01c60107110088455442500d58400a456080c90302c89505070102c65a4a0080018070b225008000c11800781007203510503295a9688984147c50080c0210114000c0c0560078084189a00401074401d8401d417404018140c1c001030403442e01445030641c01a4a03103020801400304500690040c614403608881c41450f080304441c1e01c0b401840c09000d05000140d4510945403050030883e030100705003031482d803004001d008140c10140142c0c141203a200c500c6620b50301083c054100f5071049050706840b049400700368031031480010700f109520f03001008648400c0d407150f4100c20200c4183c3e464400d009002d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 667531043 1250 667529793 667529873
    0x804120308041e0b0f0714070311010c09140402130b030c0c240105090711060705090102010609020909010e07050d0207030e010e04200705070306060b03040210020106050d 75
    0x31008150150240428401075918044904902c052612620f14281d9501d02c5220009081c14694031050030105156500503521800c80c135001c0c41c3d10300e40728005420000c01007810b2641c038050552811074a0000345226140c0801a03418198140c8101031101e01444003d60000d4500c0d214001c1000001c1204a000300017140504820540d40361a880c2c104001c1d4200342c2030040c0380000000641d05a8101d440007021907046840840d83d07107400750390380d510030b07151260108910051801040d00f0884003d400a02070929000c0a178000c114481d1174840000c120700c80c01c1a4650300a4070080100004101c8009103540400c95292190601c4134441c0c09000780e03003142c3c50440204640c014210500c1d64410b124989100301100c00740007a052011104800c1c1402c681c0c0020b68010002c3c1701c00511804124003c0256030004e010420999188a1000c15400603103049109860310403101803924414000c160640d0b90041c20040c04100310703952070781d0115081d101ea0405030303600c0c81c01520903038491341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 667532293 1250 667531043 667531079
    0x209090103080406090f0302130504060902031e120301080307060c02070306151401031a010509040908040e0f0903070308190f0513330e030417070824130804 69
    0x14055454a0a0500150805d0710b40c1d004031180d1a1400c00400c05683c604070100480240440c0004141e00d95040c41e00182203600e0010f9018822400c8001104100380d140c02c0000101e80f0607503500d82c520500c0039107544801e200d0304030641d02c240030050208503907500042022203d80102d424a41da00d949a00132342d19150900b003600c80c1c0f00d150400003809030051515142d00c0901c1d00301b00d810600103403541031000754410141005408a551b0303105481d1944810302903600403403003903190796542208194100088070024220f005910220740102000420354810650541303c41440d81d6600f048031203131a0030369a01080446c2c5540b4000050040c034032882d8000c1d03410411590380048a420325400c51109803d00b283c10140101402c50046003c03d1617800300a05030a0100389802c07103590852442c040c5801c808800301200c40940000800015040c3c11a0f0011003a600712400c00b0415030380300d46426410364400180301002520203803002d034801c0c0440c2d106441e201e05158036204100080383c8000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 667533543 1250 667532293 667532303
    0x240d08030a0b0904020616150204080c0a0b07053007050f0f0708030a120b0907170a050610080613020d0c02070b09030304051c21081501050306130209090103 69
    0x5206200c060750140c0c400b2408255104405810142d0101c1d01c81d2044400c41c1900310b1000c80f04808101c2c01900140300d0640300d520544d01c890701c5103000c03601c52203003003082031007981c000303e0020f60710034900309842c0055003003c080d003256840341042011080070100101d2012000c9400501880040e0020b4041036004030028040004050b02d100c2c903001000035000c01c258003084080280b07100002c02c9401c803c003240781c603100800030300c1f540d10050507080100651102208040091055011456046041c0502c00081103a1035214456040710000c2d01c86542001d0400e5007540120300030384682d500280080d108942580404020740126000410000c0100d512a0034200b5043c3d810040c04001d081003100d8140381c0100240040d980c2e2040740700b0140641c0c4042c6441d034250f140c1d41c60425240d41c101e509200100034414010080711259094079011440041c00b0a00000c11541d412954180613191140745880d00d83c10896540c1d180c8620400d600e0702000080500c2d19190b448600940c880c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 667534793 1250 667533543 667533547
    0x91b0708070f060c212a0206040201090905060d030c0f120906020d210c0908030c0303011a070b0402040509010b15070c0812030109110903010213030c05040e06240d08 73
    0x9858810f05403140d56200404000a0010306000312105000c480d4032615000c00010b01014604820b0200c040300b4610101d000f065184407444080e00801c0070781c4501e1007617950f0108540c07a407010000300d0b00141e039510b0f0840801c08182d40040d0188050344041802071034070780b91017161a0380790302680703c0c02d0508100103014100e04202881d01001541042d000d90700344244100000d4100105000c04101c00e600350315150002c0050150080101c000a45011816a1342e98000c50180395640d501c2840741c0f03070172181400f0400b252a9403103410b4480d5030b54040140f0046445640030080a45405810300401d55a58400b4084690340d12181c40d0141c00b40128050311505a41400005081c0320792104080c0d400880f0f9030346c038002000c001c69054950802c0c000444a000b030000107514050064a42e0305580700254201650900205000807603201d40d1840901c0c41d15441844282c0b01d1a111604290340244040380315824882a5404000c9100d040c64040d0034035070300029407088095038181e90100b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 667536043 1250 667534793 667534823
    0x1e0304050a060f110d2c0303060a050f03031c02040f030507030203010e010c14070318181b2a080417010506030a0b04020907030f0213140f091b070807 66
    0x64000c0c2041c00c0c010440400c44c1440b842c4d40070f2a6803184510003501c5950b039404003185603414083c4802060039001094220400a40c0d029949034800d4460600c50664040001090301d8510b01243d175140000d009542013241d000100c2c104075118115080c0003940900c03001c1115a00025004000c6001d14000d084040c42e60040c98219010100c4482069050002104085412505204610b01c80c5248940c2d21740280c00d044580c4807041d860b002c051112031100140a00000b10062034411400e0020404910001d43e5501409203500451000c40e0302041d50414140c40c03641081100c03001102007514040443e580ca40859000d50080411454030562003014040d0903c1044da2044054009192803925500c1f00d00c4a0000100000d10680811000035a09032080d04503020b1355142100940d1501002c0641c02c00d2040a40030304403481c48400c1a00c0706a00c2d1400c40d84004c500081c0501c0c440351500c1c1c0704d24503001020707070100010810801c481c00000d00798a00612107030340500c05070200341d0300f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 667537293 1250 667536043 667536053
    0xb0a02070501030f020f07120507320714010318170a120b090a05090a06060b040810180f02030f030a0504050a152a02130f200703051e0304050a 63
    0x20300c1030b08004c684140f00014500ca440001ca445c003d811452601841f0100d52003103074603105450008100c016490009400340ca0a000b10b407500ca0b41042001d01000d490402040d500e000030b00c19841c0520016803184003a50280d4450000c83d59600c0e0700b00c1405031035440e40d45d5011003c20354008003134000100d80d40031035488284500100a0b0240a103c401c050800040c0070350805070411a613103030fa8102042030b000d410040e130b11200d0b60004040c44002e070b5a5403a5102d40d0002c0c8284000780c041d00760340400c455420700c036a0998040319404801641607549a0030488003054030200d80600c19100e502c42d11310b000300080e11001403542d48440d540c60138101848120542c6a21054030224005400700c041904119142c0a501c001c040c0c281702203100071007100340d10500030000780d002501c0801d004031100382c0350400045c0c1030003003000b1b1021454101d031102d600741d80903203400c110101c18844000000e1268008111400c2061040044050b0540300500241e02c01e4600311060b80c481c243c9082041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 667538543 1250 667537293 667537301
    0x1804110a051503061504080c04020d0f051603230f06040e300304020f0d080d240602070602030a03020c070e0a24061b05120f0c01050108060408120703060b0a0207050103 74
    0x5d1120b0f0340b0350b00300381c42c15103803d559032111120f00c1d2069401050009d0b40540c641d00c15402000c04e80c1c002d00090038400d040000c02d0340c4c1d20459100080c2425840303510720900819814403420784050354041c1d80c4e202c08120078103c00103056070340d001e13807680c1c10721500c40d400300414001211046404030b440701b03000507204120501842a56800f510a00810001d607a812a040c07500d80700c02c2e00c01e0070a1032040c0c5405081840b50300c817071205d200d1408040000d0301d10304400c0d0480702d058452001110a459030300507039490302584100700059004001085a60340700b5009805480c80714400c5513401c42d204c6d0a44c00c55410101c6550340e07400c0c0d03908800f140305030384403584c6030f190480000400440303801c000c030040113076001c14604c07104c112900411004114042145580010402c44440e48610400132102c40650010020900e43e600749000400d01c0703440441c403140501e9001014900c1c10342d112041000d003d03c0108a90281940c890002611913030b890010480304a29a0142c0481c5d400d00b00003504072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667539793 1250 667538543 667538569
    0x70e07030501030b06100905040e0a0c050d0507120c3b092109090103030908100c0206040303240e07092304020f0d061e051804110a05150306 62
    0x50400c1c00400c0480d0403454081d400c984241c81d80840024402e500fa01c440809900c066001031502115207802c19012a1454800380325090540e049a134840421400302074180300504950014442000b84401c0c4100c41c000c114842c030007012140d0390740d01d2001044030145060321074000c2e60400b007170340080c400352015004040d2640084228148081116618818100d0720500349050700c0740c0e0342c00440c0003000d64070800402441c03802d0668403403a00034104141032213000154420314100e00210f10740d50241203400a9036034001c1a442d562620101c02030102c00e004103104140f080d44100502900c60b8420015090403103980a45081081c001018607100e80d1100010803040c807040c0703410702104013981072150750448026840310043c8082241c640f1404e040d00d03000f1303843c1c6800012801c0e88450406112850045155540e554400621034000d030b50f10502e055000801d80010005011107030f0585030418061700014940ba00d03038003c10070b40c82200003c04851100442002510702e0400ca801c801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667541043 1250 667539793 667539797
    0x70c080403050c1f2003130b0a030c020a0809010e060c0a21210203040804050910060f0507080702131e0501150c0201210b0607060209090c0322080c0d02070e07 70
    0x1c40000c020001781030108421000809140320401a000c3d514204262498841c11050002d03940e99107295007022a03120f007440300040b03420000040c0d003050012404010194110006178602000c003401180c540059255035079109105100c0e00302008030800203495030921030400d0301c0d240c105408040503040c0f0b41088803010040b440c07890303840d40d03d81000d084414100c419400b5031130741c440d0300c0c1c1304031613001d40d422a5801c04080d1082100c005d0180b200b00f82183c00d10b03120591205001541102d46109244002e00017030030400086c0010700f410300c0e81c0100007031102e074000303900c4080c00403e1403503900c508a00d41032192900010311051003c0042202c40b800a42426900405a81e0001c1d00092407001006003500c2d140d0010101070b203d81e04440c80c2c000e00100890340d00c0784d09141c2034009402081005000c3e050300c0f800550070340f03a0366046078000d4002e1580d10081ca0807110003003504001b80b0400701e500181c20f02c80607001c00c60810030100c012446402402d5041e04240324280719010043c001b1342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667542293 1250 667541043 667541089
    0x1005071d0609011704050102160503030711061315060308040f1404053108040609080c090606041a0f03040f02090a0c051917010810060824070c080403050c 68
    0x85030f8000522445a119891300c403036503561a401d1444c020701416100c907118074456481d8100300301c4e000c030007503124511584030098440585511165030701000c940c072500301d03150035503d00701161100c1040803000c4001c0342c01080807030300d0341d031603683d0364100d41e1200d02952141c40c0e040c0003143c803240c00c0565584041e2410002d52030108141c8203074000019880300c54030400da000d50248642800d50661554102e02603a5486650314401454034609208401150040c00d51480c0c0030f00d08803024900640d001040c0c80e04280c24028607002c1018210041c004245040180440c070400c0c00d0050340c49503000e07210950348221140181b00152000400006c04180ba002c142260700380c01c54196501c0740250741540700c9820000f1700030750380d240501800c3c0c0d00c02d040003000004c00c600001410400800740d250180081f07540c4d00f00196079507021060007102c00c045406101c034107aa0032240f141c0d01490618020350140340c0d944400866501582040c1e460750008505581c0c07901300001c10408118100301046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667543543 1250 667542293 667542307
    0x4052518051b0c10063512030a06090501091b0c0b0a050721050916061202181c02040c05090d061d01140103021008010e0106111005071d06 61
    0x104081d4210346090450060100d00f544212004100884000c0c0c00da260030004103403140114085804a0340410980740c0c92005001c3c4001500c1440003003595259008040120031030030480d180f604000c0c100d1040507590302000880100b6030192a0017050dc102001584031288012000e00d0a02c07044400c041c00f000400450000304100c204075441400b0f01d0300003038144c0796001e0071103581500d10340480c1800c114490282e070503a80f0340e020074084c10100c0200c1d100100001092208140c0c14441c42c0003041940031881c040e1412500103122241c40103071003a920001d00700000382b500e103042c02010550704030541902d046042510803d05040341d1421320504091a0100048018079859001420103440340c4000546220b0301c4100c1d10544441c00003401210001039403007103500030901c0141d110310011000580c40d14000d14070b03030341640c683c00f50039810b0f60708000c020ba81503e00c160520215115201c0360110301c0e52144030310b0340503641c990f4901001c40c1c2000905010240c0c030170141446000208903030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667544793 1250 667543543 667543561
    0x60504120f020105070204050f060f040c0c02010804020a0803160611040b0406030c1205011508060613120f0209070806012705010e0105040e0114030f0a0302060408030405251805 78
    0x200a4a50301c1060310303564940c0741c401200c15002d1000025005030908050082040d161010307a44202815241c90003021040e500704025241c0c100140705c0483c0c42c4034960b4016511488440307a221b400681302228060391421001e2a550240c205001304d02e5030181d416081044600600d8008142032030042c0c01d03d07007032500d5102644118071812090681e164040c80c2c0c90382c042c2600c494000080304003001250395442d01115020840f1000c44001001040051444d01e454000e03280b0680f21004004c1119042444078103220b0800b040644500c00034065041c01a502d034080507204804d40da9401c84039040550000d8840c0a10510340c00307561050130212182d0f41038030900042254024a0415080440c4000583e134612964201884008501c00040303421114859650b18004e002e900711031203194925001602c0b800c18000040042e04500c020a0204603d400a140c0140c000c105455401c60341c0c0d402c540710458603040e41c201400c042002003000360150088030307280454840080c0503520b407554030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667546043 1250 667544793 667544819
    0x6040c0501050c1507111204030c1a07150f06080309030a080a20010207050c06030c0412110904060e070b0c07051e03060c03060406050609060a0309080d060b070507060504 75
    0x144904101c4085140e03080365104000c40780c0d81300000b500004003400c0606004100040009a103450b1341f180703000c0040e40c50120003c68044981060175508000d06005440c107104081d6151601e4600c1c00b4002d407004240303104402c1c510f2080030000095210742c400344007000d0ba805940441071917001480780f80002c0d100803d05404031540034588503900c0b80c01e41c0c025a035951f007882d8442000000409801e038200700560042c2401170080f404c0b12060304c02131301000481d1108803059148084144001c110503102411240c0e40d00f48034108600701407201101040c103c1c10201c405035410b50f1101c06c40190180140b100201a01654003000e1500a0000c441c82c0d4580e914483c00e07008188451140784a00f54044c640e50745d2030001010b03078855041807200c01d0880c0e001074030000c0c86145401d200042d5031414904681c01d00710302605071400d1420601046e4028a01c040051710400800c00c506004501e95224550140c100c6c100641c2d10340b50a420958581041c0790804414007008101c00c0c0408910284 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667547293 1250 667546043 667546049
    0x230c0906031b04110c0f1005010b040e100306050c030a380d05030309060a0606051e130308520309150905030d0305061c0602040f090c08010806040c 65
    0x10010350088500c202082c0140146110403d40b200f0120702d81790480004901d82e00b4440b9080100e0708500700c4041400121030f002e1080e4800c6140805c4200658024020415405622903040c90780d0242d8030b0b1103e07004e032001260300c1e1079427140020401c1102c83d110304c5455981e640b521842c0743c0540b11000c088101c41d102c295407101403800100903201c0c60f0f81c2c40d0181c0421308d5106054070386a04013014240d5030b400040d5411b8054038100640899207034410019110b1001c100b03c0c000b800f88511140800d5281c1c080c3d400089058403468010003ca52084001d00701055803a450310f1024906407901440300d482c840090480a440f03054454000e001140b030071240b166664040d6440240030b107401d6408104a611180c2c641c0c403400c1507441040e030040c41007030880b8019401d44064041c0c0040441c11607808640c004c2d84800b101004408c00c00d140c1011481d81e6110b64001403610f600e60b5900d41040c04030742d01c2001c80c25155056070201e01e51102c102c1f0f00604d0380000401d103500301030390f600c8154a81c1d40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667548543 1250 667547293 667547323
    0x30d08071b061d0f060c031e070201090f0312060e0105130c02240414031c23010f0303030b09010b030f0a180b0a0c1803020609030109230c090603 64
    0x1181d030350610510f80d020b040788900340b0300100c0341e10306040c1405031606400c01070300b10a03001d98400544004041c800f1248110002d01c015100e442490826031030001000d428582150b50fa0414a4002580800f8132140503010b03866125007040558800c0080d03a20b0740d0015003084004400411441d00c641c100380e5610f440c5800d01085107146500102d2800b20304110a42103070b401000120088850520391500442c09010014141264100e94640c2c902c26003452020a0314018900400303801298802045620000c1501708001040503940568540c00e030450140a080c1500401c10507815100c0c03041d40140c04e07550701410b5890014078020700d00008040c0580030783c0c135030000b600042ca644d201e01c402c5408030000704040c04160a00c105003950880c1e400384114940824086503500a56000c03c01216000315070100c203080d0340c2440a1500314001454240d9200c00c250400207410300c08101003c1d450030404010003000135941440e042501c2e4409005182074024020283c0300407502030640da00c02c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667549793 1250 667548543 667548587
    0x40c1806030812040512360d0f170c1506040908041406040506030c0a03051005030a020f151b071512091406180606040b01080103120314010f05030d0807 67
    0x1030a00c0343c01c00c0380041c4918181c00300007a20660300d1340b28488004101580341c581000308010360410203100450541c1e451350044c0302408e00c1c800600e4526202c01c200c0e100c0d080c0f042001d15450b80d420481d0304000c06130340e501e8005c003c02a9003600921083c6038008800c40d401d0144d003e240d211082113104600a4908100c18015100c0141e1585005c0760300178500070308215540e1034000d8211425030440d549800001e410034022810100280e8501c9040d500300070080d0041403469400c0004940f01c070000c031a00031040848102e2400804006130010300d0051030800c00103680160040d041000700d400148203100d01d0900c00c45c050754050015540a002d030f490014400c030385400e04800c400390001013061144544010429851144400c405030310614404640f41900d42c03404003c2507a070319070406c5000480100041000c2040014088244089400c0019400c2c08002c0c9901c4004002d0300910742e6100c0c0d4000c108206e003420805600454424600000507007410940149004a4031681446802032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667551043 1250 667549793 667549801
    0x406080f0702010917190804050601150c02030a050703021f05030c180d0302070603150b071b0312050a1103031302130f02130503010c11191a040c1806030812 69
    0x1358000710b100340d0880c2c4e000310b00c194520002603143d881408203980484046ca40c07001907a0040c400c850107113074044061700a50f800c0102c04058020440c54220030001d608911343d01584090025402c0c160007140600651400c500501c842e051082c2c4a8504c22284006280501a400000e0702e4120311122091503a071a03c110208280d0991007201c5e82d840086c45800ca4201a00018803404a440c1500c0500100e40751a015246182c00d43c0704900a8500401140e00060403d120451440075603c10900d54cc0340c60382ca9144000d00e0300c2d649000850400602c210360190400c200103040402c54009616601d003050184060b9400001c0c005d009440400f0281d071160f480b03811480948620900c115200d86607000070021040c032034441c860095182c80c2d58a0340c12071281c052030183c250044020300b280ea901c0e01c40c0d000c0614219400b51180794581080c640c410f24040011400b5901135022000e03924101320070690002d4158a80300c172101c0c9800002c0001568040a072a0b80c50720302264010f11380d075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667552293 1250 667551043 667551047
    0x6051503071d0f04020d0c09080102040b09091e0103060b09060607021c080f12040c2c040203010b04020403060c030b030f070515040801060605040929040213032103110406080f07 78
    0x384003c2e646602030300200d002d480f460903580c0092801c3c8250b5603075800142e0b031401e400d8201e100f00d028078500d0640030418003406040c16001190060180c510004d8801d22050010340c001d44c080c0c008446240d140e901d641d4040c94103080950b001501111040c1c40d00c030f041c1e40000c0300c0c182081d042e15000c030384402c1c2e000140303c564000c0da261020300840f400d5031034a60340c5141083c03400c2185c0c1161030031311404000c101000d0390018a01c1c007003000500411102d0b0000c01ccc0031410000108100c1e419922805c007070303803143c68030300182000714812030020402000100019058500030b60085009501007014842c0c00f141c001a800c2c1151001d49050071075a03069644407100d0311607500044135170740c05c044e000117401d540040103104071045e120040290104a150343c3d07440480f01c04803502d9141d0540c002c4000c528141c2d0007825648030b01c2c444580e031299240d9407488060f00410301c50070340c0d001206401c090b40340c140c016140300e01d200d0100141340c682070038001742c00518083c0c1044040010200003d01d01c80c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667553543 1250 667552293 667552309
    0x40303034a01240b120c0706020c070e0103021807020717100e0f0f0304050102030426010903030b030d08010302090403230f1c05070f030b18010906051503071d 70
    0x4450340e8001d12400e40070101021941c03400300c00040450910f03000000d200d544150550b0b95902c413a81c285159502d40040c203400f03d400c030020070b854032a4204a03008064008000e00001050340740603510180d031450040080400d0b45105404110610008202e8419804070303850055951032101400035001e0400485d01d00b21b6a5011144080d00d01007181c804100001250b660241d0800704440c41210b45c01501e58484c0120f1045501581c0700f80002d00007031604502c085122000691680511174158144a00b560114202580401d5030717904100e519080c05e2229001c40300b0036060074003440d451036000c00c0031310384010f0005d0200004500441c0c031000910022400000e074410316652074503005611a0f80e17590041c0b1180c070503c80e084851040c0e003a024041d46118040743c2d01c0b2240801810302d800d90260060340e035071a0b803007007050000d1400400d081480a02a012240e4001201030404040c050007114070444040c1c540010f00c100451340f5441070103280000303003c003039481c010017070140450114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667554793 1250 667553543 667553681
    0x3070e0a090c0306050105150412080a0c1b03150b030a06050604060e0405062502031603030e07091407020a2f061206041a03120f090a030804030303 65
    0x100803075a40001c18484c071600450306944c011280107c0c042070600e83c1040038070840c441c552903440050b52a801003190755000c0c01011046050030948ac50559490b00c1e420103904640c12030381c4500010a00901c100440d6808270081c1541080011100c10360009607955502400184142e4952001550540316a01701c10000d000d2041e8441150500d803410340d03100d0108944900410068048101e84240300b41a4801c4450321038015500d4a05a00c010010300804520107a0515441d4030700c01d85481c808011805c014010982c0c000380d0b800441000d80703403452000c0e08990840d4408041440451032600d03e242d0000040e500b10250380e003890800070280300c1e01141003a4010030210340c40340200e0031006880c2c4183d80403141000304035a01c005588040b40d4104050350903070f101c0e00341d415041034014001d000d107215030181a42468030300740000300c1d811000d030400c45652102050420806816020301ca80c40341c2c020041540f4041f40c14650040e05415070004d94841480010749142e1140107040300c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667556043 1250 667554793 667554803
    0x304110307060801170c1c06061a0406020f0606150c01110f0c0d080f18120304030203070506150d120e040f060518090601050d02030f010504121b0203070e0a09 70
    0x48a592550081c25850091040c5808002e03580c0c205c01c3c92100c040340004810344000c0203403c003606281c1100b81d0410401784210b460507038900010603010744c0ea5680200c40c0c3c1400c544540ea850402c50000d04180819801c00a15401074003449960b6407070110510445060000043d190840c0c810a5809400e00c540403a0003410700065100c84410700c00014510f507080704007180c21158005100300c40030102224114803201e040000300700349070740f0150040c0d220305d1050304450030710403148a0700710554000d0300c003100541d000007820720801c80c0602203540d0000944181d055441001004260310b407012030001460382d6010f103c41520140a1092041492000381c0f0400c190103030000580c0007441103002c2e15101d040000480d030000d9411414861040d080c22000c2c1c240c0303074a0201070051085041d601240e050141e845030601110003442a24801e82c01820700458a00d0000300c0503201c0e200418000c1c0801d88031010400250b20300140c44002c46214055240c01c6a80c0c810000c80100501000204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667557293 1250 667556043 667556053
    0x201142a031303030e0c0907030203180f0a0c05010906080604050c0d0e1609060b07061d1218090601020d0e041e0f0b06030f0403030e011404030216050108091203041103 74
    0xa145141c01042c25640c8203850801207400d42424035030351150a21041a400890040000c00103482500a1038001400d180c05415821400300f0741e80c20010314241d4007000b035122640410600408d13400740c2c1c00414082c02c2680d022418050000c14810008180c54081c60300e5502141c86400c105040b201c51880d401d03400c0248a6045100540303d0384c8058050541d1140c0c004040b0b4000540d105000c00c1340c50000815242c0007903552500068440a081490070580c10101e4111011040c050007000f40110010240da0b6020103440c0300342d440410622070b0249026804102035640c0002e1600100c0b070031814802c11500a03280082c0c00f0707000c0a000c2c0c5a440c802d50f0790007140c0d070031907400500c8100c0807040144500c0520600b480601e000447d44a00710407498000320340800d010384d2180304002200800450016401c1000f00302103031050341c00310011784c8040400182013459540840c0500402d00e00603905080041203195190b1002c1c03040c4181603800004241000b251004520b00c04801600341e030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667558543 1250 667557293 667557301
    0x3160f021c02100f090501031509140405010507140906090a080304091a0d020a030807420506010504140a03060e010b010206010b0708030118140108060a0b010201142a03 74
    0x22014840c80000c90040c414680e0043c54903014001c1000240070640c1c032020001c1c6088011400742008040d00c0607440008032000c01c0c29000d0740222003d044a03800a0b60480c2040c0c41c0c0f030390840300000d008000300b060500380e0b80d113480c007800b045510324641111a035071615811000174158803080d6000c4021480b0008000490440c1074014214619400c20780c20007803c01c0c2c10a200303149103049802075001079501c1b030070f0001a002c3d0028184840c0107204909000401c5031a8058611840c40c11b10710303130784034807408040c4200981081040d00404900034041401c0171000a0302c507026034010484030b480b400c25000c41c3c58507089840340095411800a000d0101d40d07a60140c020a50f04140300e0040c0140c2e0700201c1d000341034004990149038002001842c586c030780683c400307007081d25002c140c8070107466822641d22207800040c001d0207408d20750040e080c14108000310b5004c030b5000d07139034160540e41041c0040c0c039290f1310400520b40c020301200000f41003034100c0c40a14110150300040c2c58401c403002c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667559793 1250 667558543 667558579
    0xf040203010f0614180f07030c051611120118080c01020f071406060901030c06080c0c1614120a020f010302070203030c071a180d140312101703160f02 66
    0x490b40b9800f094a210a2154103210b140c45c03400c0041718101d2003082c62170082140a40300390f019007179901c01032810a08201c0c24040340c9508140c0c081c0c06840c0030300f10200c210010714050041c1c4000c13225007002040a40d4004495060a109444002c1d000c01000b08845070150420340440e005003560170b100c44d9403940e462401c40201810200184e07081d00c1a100064003604103080540d050300e401203645100d05141c001c00b02d50101c0014002003214409000b00712600b0700130420107548054034514002100c2c00c101108114031540d583c0f0a00c44d04505140030702089010170340091464064402840d440b41c41d40050300070740719003040290148000615529544e102082e2075054032800c14503546100d400e0308403c81c250181c102c5480b00800d0f1811001218178120310f40b40e0420f031181c01c620094103007628485003143c0183c0d41070901079550500b00310700c0c001400c1032000642803007a00842804a220441c507a24003549145400386414191000140800521141070451b8000c0c48407854040180308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667561043 1250 667559793 667559819
    0x1c090801020d05090c040b0919141303030c090b0405010c1e05071d070f0804420c02061605070b1e0f0609060d210503010609090b03060f040203010f06 66
    0x1d8054070700917407082000b00d1400d405083e5424a00a00301403558a0b003641000001144441c80720240e40c0e5403104400701881e01030744e14400c0c7c4d9000c800301c942d180d8908010b42600c1801807140200082d218040c0a40070050b400e03207041d6023080c41c0c150800b1040c3d14107005c844442c0300c0740410f0a914030054004001d000503025068502e070400c28002002252821380982078180d0340074012400035019540a144103441c507540c802e0044001706544580000c0c0038046e21103c001d1600728200c400700040b016440c4c5428136116516180c010040c6205541c40251103040152031520350b07aa6000b07001d02c4080c410401d48003e41d8000040c1c00345802c4c1404a43d801d441400d9141d01d6103003c1d0300c00540000440c61103184992009403071448555686c80070450740d840908001c44142c14990388000b500014419a5034074004aa00d600c1d940b0f50400502801403803036944003880b0141002d0406001d034501280d4a6041041c110200416448910003e405002e00000040c1c40c0d5203020000594110a020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667562293 1250 667561043 667561051
    0xe030405100507030c061a1e12190b0603070f0b030f0c19050a02150901140115021c0509030307062f0313020604031209081606021c090801020d05 64
    0x107194644080c94500540b0301c0e006620001c0d020805101301d035008180705802c0148012110383c8140036076846440054600b86070300b54043d00c0f284100c0403045207810111860700c414a000b400400e640441c66078070300907030800200000c00900c80c1c000420382c551010000540a00542610030f881a512664110070380d410441c1c100100034030705808200c2e101700030021213403110500c00c1c40d5505400e03010802c0e1000d501c112341c2a01148140f910324041d00f60f00014590141400c0d070f001091300d190341d51841401d220103070000402a1009403c4400840d00000c002140d03503550846842449900e401c1550f0f035004d101c01864050000040c2541005110743c0034a00769440e0551698101e16039400c2c0700720070007070319071320740e801000400104542404016003180ba02c0c1c4010485441c0c1a1a6551102d0001502e403222021609250042c00448014000030070814544051080d4042c64040000e5039038011450b103011810032100b8200b081d40c07003080780c00040d0400718000e660381c00e1144600002040d00311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667563543 1250 667562293 667562299
    0x50d30080f0a0513020907140c0c10030203090d03050c0708041706090c060414060408160e06030c011e030f0204060203040305120406141809070302120f0402012f010e030405 76
    0x1c0004000228a100e03850081d1001c140d0507034044a55400c0c0b0458110180c021000c1c00b5101c81e9803c04159440c009004600c01940078258120040c4284000b51000185c3c080505005104109030324070f00160040301c140440c82c000c03510361500c0d44e509509119013040505000c0380058045402100901c07101080c0001130308948a40e40c9540300c00d40c039120100c8000342e004008000400c250700801c3e0310341d4030004004100e140340664814505142c00d1080002d2544046c0c2d01c0410800240d100014a503c2002176015100300f00e01540004c0140b24150204c090300c102041c4900800c81c4254440300182c1000e441c1150740d81c0d20b91801039030703a07003051204a815101d102500b000140d1010180d0301182d0007900e40d0410200c0e0711344c00c050690051058040540303c1c80140000507a680c0f0704050240d01c113030f01d0040c0d075008646402c1641100050002042003118014040141d0f03002103031010850f0740100744101e48101c070364202d002c100c00c10304412040d800e004040790584008401081145c00403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667564793 1250 667563543 667563571
    0x309060f010e01140103180b0601080f0408090409080720031027050f01020a0c03030b030109260714030d150b03010306021303020319060b010207050d3008 68
    0x128a500d00b4000e00014031907400040100d10528144500103d40c141800310344014100040c40460149600c11340e40c008540003881000d58004180c207800446411175904580b400d602c542a2134441c00d42e00c0341c055503131005400c040c051031500359260150b00120364000300d4402a00d5503040324501254511034042c01d0050b03203036190240300d80c0b100301d40d81000350013241400038501c0c5404403829009907024050314880c29407080e4281700400019405480f07000007a46a800c0040c00c40e01420103ca000b689404000c03c08a20381c03040c1d00215280c1d450b01407200d2443e88505803001d000d4881d0042105500110340c2c400000c020010b40250390301410100102c1c0207030000c1d00c0d80c07010345100b2510852408c00c0140b0104076290000c2082960032004210040e43d0ba5000c64580085c050310714a1101692650348108440e5028916059500344001c10402e400c000018410100411006011805041c441070070f100d5018500c4141c0c0b02c0c1004d015a04c031034841e034043d10207401110139070440b001d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667566043 1250 667564793 667564801
    0x212010c020c0d0218100b04090c03050606160f11040608010203040b06040501030c031104060e1311120d0e0a1517090a0320250e010906062106050312030906 69
    0x114896140400c1e400405c5100c108400d00380580c02d400001e800381c001c45103800c90204001e040600248010300c07130000d00142c2800d01b4100101240c5020381051322a510030409006031508000200100542200d01240944418a0480c0202c807000b05540d070003500385000002d003c036065000d148a5401500c0021080e6611420401158006d00008001c10700804051010804102589072141c0000c2c0000860503219541d4225035002190406400000205001704100041c020b25a140d10240c40040100341031103251b603141c11580600c0420841540b200d004141d594a0345c0000501e0340c0004044040c000b40300c003d02405c0d002c0d08820304c001a8401241c4801000104042c1d042d0301951220581c0350844000200342401a036100b08070b10036800c05458042500e001e5103500b40a1541130311840c2e140c0000038642d0302c8141e00c21305a02d840d00b81d0803c451600300322030002502000c0e44ca46640455020f02d01c005080c5900141e425114001c185000d90280300020f40c02500c00508a0300d0640d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667567293 1250 667566043 667566049
    0x7120c0515040303111216021002071a0f0d0c0f090b041208030621062e0506130b030709050406170d05031e0916060c1109060d0212010c020c 62
    0xd129040c08040079002c01042011a104000d034001d00d003500300558484064a4101800c00c2d0030144c0103505400302c0c003040310218581a01c407410b4500032800506403c80c9000e0099190034030f080011540110001000000220741c03c04481c4c0a1440321400c12030f01c507501000400000000d09402c0c0880c281e5203004c501003280100781e9013126070600340d058000070b15a840b01c03000e8002078003c0da00070249180300143c1c00c8400c00102c48008202c0028400c51410860032255900e0807212003000140d000c5800004200c581906004d960081d502c140d91000540a0580f5006080d44500c441a101001703208210f030380320140c501151421941400880e880b00140a801350704d9100d1083d260b80825484d12541e4065000386902103005a1700310a0011400d0b0498030070f400c00c5444444640042e460900512020711a000c05400e4500d80814050042c0e42c40940013000c04500b24030618040e03001652a9484920010b03407943d0151020301d01e0840e00c5a11806003015045440250042c0351040030581 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667568543 1250 667567293 667567309
    0x1605060708030604020d0b092e050108160c080a0f0f031a09361b060301060804051006060e09011512020705070b0708180d030f0f0c0507120c05 63
    0x1900482050b1950310f0300000c0000030b60000b00e0702d01e5080e882d4070036030b05256603a4901d14071816003000300c00f41d0742c1d0100c0340100c8906149442006034054a040038080c42c1d9110344210391100c440c40c242668407052120070f458034001c0d1a40202108400034880101e0f9600c1840e00c546400e05c1e4a5500c3d202d561a20140c0c1511901d80c0701c3c0c692140c40e1064480076240000943c0c0d00900360740c015080050303100a5040690000300c00040460560f80310040500e90100001d007403464082c0018a00780c0c0541e1300041c014030042c440c517020081864081000e00505100c44041414404400c108a582c2c032080607101001e2555410b1168240c4000020031800b100c50000b0706072129621403a1003c0b5a80b01d11000f50450700c801e0b10540314140780030800e00503c1c002060f0b442e0141c80904d0700c03034607030140c400c00001d0380c000c1385030041c0c01d0a9019400070381c10283c1c034040350449041192856003d140b0842d103c103009007020700240305004000542d40e400c0815100b4850107041040c242c541c80d841030107508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667569793 1250 667568543 667568557
    0x3090614071a060d0b0114090109060e06010c0303020c01060611101401060f180306061e06020d03020c190b070e010e0604090b010903060f0c0801050d0201080a110405090405160506 79
    0x14030007070b01c490342c11a050703070410300e5000c03400604442150700d180d103801400100980100070520385050790a00c4c4d0386024800390380142007040050101038182408403a078844081c24403030500c030703242007000209802034050f40d000700303c84d41c020041c0d165907103c0244010074240c0401064000c03003000c00c0e402c031458002c14021321020110f1030340302d0740780000486444144c800100200300c509003e82d50300c41003800c00c2e10010340c0901c01c0402c505082100d08010100034500782d4010607200c0204200c000d40100348040400d507142070060301c42c0ca00080c40c2e4100040240e0365030f50b540c080140c010800078001c801c50302865882e500c00305901c0c055801500c0c42c1c91051031182d07100e18103200401108290780c010300c14000c1c040c07411901983ea41d6540d0300a03125500d50444000362111081c1c0c00c025444507540b401010200e0f01a92540038030340020b0400b10002d840c0b001c0c01c680f074002224504480030300f00c400601d40600340b81c0c01e41c81c0c20b00380707262140400d840245280340c5144000480e450918151100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667571043 1250 667569793 667569803
    0x121e06030604051e0f100204081504030c0201031a0603180d031e0203090c03030f040503120f1602040e190204050f0f0c031506040605030a06170c06030a0b0d0309061407 74
    0x480c02c3c61612104140e4804c00c032188061140400504106606002441107060351110142e11203007000d81040c1003014201e14030762508c3c3c03418100808a035001d582c1103066502820002086502d0280200e01781c0907503070302c003074100c02c1c00400d02002104030040303a00c1e942044801d54a00e8403403e0011419030b00004a116030b800107214112901d9117030381d0f0080d81c1200011080f142406d440300042030643d040034030004148075000c80c0c20031050030240691000f0340141c403889417903e241c1c42628500e6025002d405a25444c1f001005411521594003504502c2090750803101200c1d10312007420041c010884049002c0e9050401240c8030f020780a05c010301541141891104070b5445400010701504003c022000c2005500e92034101b0313444600040004c0c0206549550392403074582d81d090145c44c00c07580003220500210f00d500001d0359000c1040c0d00e842108032402030741d94a841102e10083c180c045815640480d05440060070544c129090320112a41d0b40c0310449992141810062180500c81e000741c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667572293 1250 667571043 667571053
    0xb040b210105100305090c03010509060f070e0a12141b03010f0e0a03050d0b090109050708242205011401021504030806100c1205031503031617121e0603060405 70
    0x100c01e0281d00500d5110400500307c5010340c01ca4000203007500d0040c0c60240142d04403406010340405100c6403541e001d42503080205c008000c2c0c01c003040f000b41e020321a801900c4484001c0004025003a041c00100c1e0140700e040b6058490007845011440500f0300910340b196103003800cc01c9690b8854000e40303034002021030241488480546095400d640648000d422044e603550071206960381e44880e0394003802c0d8050340012940707013074040940740402c09002520101a5008010521b221502040440c902c007580c0c50101114411031441110143e514080b50681c01d001c00403c8403e0450050580008240e0850791a55442c0c00d0510b000303034003658040c00140b201000910b00d4144102580588811b0745090051a02d50b500c60044400400703a48400040c0c000090001160b1080014140040b00b1000b9600c0c100e4008d80e64051080b405000404941d111081c0d03203c8510058161203141545c50f02c00855840c2c0000c840f0f06094409100251420b00d50001c552036040000c0d11354801c0758044001d007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667573543 1250 667572293 667572319
    0x13050a12170c2b0e03070302040c11011803031b09090209011209050105010510050c1b0f030f0105060102060a02041d0a150303110c01020a0b070503100b040b210105 72
    0x1d480d15260016450808400300105141d030b0408014a0b030800101c40000c200480704192140c510303407050781c0d40404100364264a50803039a0081075980c11a41d04a40004107104c1c80354081e5032804d0b84105000d025480c1030640320403000c0300c94080003058401d07901002083c0059000d61100851145100c000600c8960103001000305d540c0101044041410b1810080c1c40c020725800a8807001081220f00342d449070010030050612210030750103541641842400c100c13120171543d607581c07000402c0f06d620484850b80b14010f52a84030f02c8545401d0b0141c01c1c1d84a0890000200d4068803080d1402070040c03240500003600d003415403090b034003036460788100e110007840340c05007400d4001da0140004844a0b42d448140d0480014a100c44000314800e0700d03046140300381d01c0081811f014044c51401c1c15034201e02c0481001a03454103116502c90100d003460380d2a6211851906c00250098114021051000401052509800004e02660308034086030304410f011051703802c03040701e0081c4620398018a40c04805 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667574793 1250 667573543 667573553
    0x307211b02030102040b0403060b0f010503011202011b0b090d140306060706090228090e0105101205100603060b040c020705240705163f030512010b13050a12 69
    0x40040d070004001600b080e03120f030b240340071030f03807055008403181d5903a8560114a820150b00c89550000242042d0742598989500ca07610031058610003410409072001e205c02c070f030100510225015800020741210303071516086140e550810300d1000c0b0046501015202e200082600c1180d10440c0f024100a05101c0e943e601c00f009410100030490307100301449000c480214200d04412000707400c186c132800c00645044028811102c00401c0d0310b499034144420800c081804940150450300f55410301807004801e4103005041c440e00c10044480b013410001c001046c4211074025030101c017403c5a04000311801c00100381d030380d5007061181c2a01300e480d1443d01000007901115070f0340306448409081d850594542d13030b040d0138045425141d03041c10307200e080140404529003030780210104030b02881c403403c4501802d12000ca00e400402a211001c401d1070349800f010701c00c5054441190401820030b0301075031a0103064000750856619528810a0a5130020700f51a060403074800300c1e2201c1c00815007a406a40716 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667576043 1250 667574793 667574837
    0x90c0905040c031e0614030a0b15030a12170f040b070315090e01060f0b03010b0403080913020c0a14010614040b01090f0311040f0c050a081f0602030721 67
    0x54105250344d5640c5000c10007440481c1e82c59811010b00f000400b5810000343c6c07000c200a907155140607038404816400000c41401d04a40c004030746c0c14080d111041418000f0f403401c00c60900c0140b00241e5401c00340f00301e58001495034114107490349000c00c0d5641d1404200c0c9807031011280540036040940100b06403034029440700d05e0000c0058400c1c0325958540741d41d0400d5541011440f10f01e695101d004002300c4203640445809031a41c2403007203285500d4116608201c1c040d502020f421000b0015003098203a4560109001c400b014590540d110580600c0d0b054440d83d82190a136601e440c140004005140c062045205031100c980b40c00301c6020003802400010000500c109050010550000c107035060329020714802036220360020340003440c4120600082c2c0702e005210404180c1003000e058100e90f0408151844a041c0e490840040d0b40c400024a00d00712000c5000d01611911000100c0d6103a804002054140c2c0245c1401a030304650017865003540c2c4000a1500014864410f400903880c60924 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667577293 1250 667576043 667576061
    0x15080a06091a130b0612190507050d0c05040512030306010e10120b060c0f210a0c02040b0f0616051603321902030c1e040e0109060204060206060109090c090504 70
    0x440060a0044c001c0440e40c16804507001c074120b400881d040180c0032529400304608408615070500c1681040c00001d44039024212408030101d80303911141a0b0f080c0300d9015100107101c018000040140002400c3e07444e6882615124001403000300102e010f810544001c144511455951451a00890101000a000100c11940d2008040243d00b04021040010f8440c8405e8031000d01800b4804040b164164030203c006100c41c0c60042c040d100515030415050313040c0c0b64060301c1c0400c0c1c4101c174400003040405401d181079480100450400701c1e000c0c240d040104194803071340440e42450062284e80c20b9850aa00c402403200d4011074541c0c2480c1c1030395000009816500c5010040718803074104190400b01c40c8024400600030320032175941907180810803d102031009603400041442102c1d840c0004c0c5058a03826030103140c03902c00115400809600013985039030410402c5480d00d4231020000d46441090321118001381c0b140101061941161043c138403400800e032140340b640f40c90902400b0103800181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667578543 1250 667577293 667577329
    0xf0b070f0206030903030106201f02070c030c06030b0604050303030c0c03211b1201090c0c0203011103010e1e01030b060f1e0a17030f090a15080a06091a 67
    0x32200c9001038484401450007040b03900d000c1c2da00da41c10007400801c4031085200e4400a154010718504c3d101d00041503002d8110759040a182079420031880f844064814888024400306030882e00106001c0e8109064007610700550b004c0c020b81036503000b08440d5004502403140d041c0c000300b001c1109064044020711000800c0c0301a02d041c900c030b50100140240f0103105003906005000100324130694000300103166008480951403c0c030014402c6108040b505000d2440c40c203507280c00c00400d41c0d0045081c00c3c0842d50003002401007500c000c802004540080c40380c1451030007550082840c0c0b11201c0c800000301c1c6005a52203807503030b1a5407100035200e500980110703042510111540f609849140c15842c00618a05d55000501c1030340c0c050007162991948841303c03e00030000e8250f484400442100c4e0b00340d1b502c0c0400e1307844140c0e03600003854508582d030200c0180013260300c01c8402e480d0000400c44c4100c1210404120700c80e61031680c84e042c0c3e407654690310007246914442000605d4802c03901017a0358020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667579793 1250 667578543 667578563
    0x20702130f110d02070302190503030402090c161a0106090303050a1d0907080f150321221502031201050d050109170d18050a0210120203040804030510060f0b07 70
    0x56200006240c0c0148402250f20390002203a000303241c0c0401621030f03502044440ca01c0c1c070b10b6254035030a07120701014100030701c2000d1a1020a01e511007900c2501e40c80490903054001c80c10340b0303103810310440001c14030ba000124034800000038600d0140382d0b554202d82e056100c2d82e140200d143c0040381c2512181d03500703404006098400000350380300c3d100c046205000c40c5d110400c460802c04020300c0030303c00003081d8201101d035610200c0788548012075100c0d01e603d82070031001420000e10348213202070f02481040800d03842e00c90034000000c0424100c640d048030019144401c4203036030282d04988030301c00c040d03d85003d010301d00010001802d03d403842404c00783c010400021030103140d5945000720b08145003c0000c0c0c01002c1010b0300309540c140300e0017001d0f00007940f51806011461b07951a0b00c030b07450024003a00c180043c5541074495400792036030301000401880111750780d150a01e001005900700b40015070700b0344925010700410b50700c00d00c84d110030b8030800495200c83c64a45007501c41c441e44222030481e8441e0711 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667581043 1250 667579793 667579811
    0x60415030204120f0209060d050304062604030e1002011b140c0f010b12060105030705060f0c160614120412050f16060506090c070b04140d0801030506070201020702130f 74
    0x200c182c04074014804e04640d5051403c40c0104120000702408192092144410540002e40000304075011103642d1704141c4010a040441d5260103a0f4640f9a42e15018482007000201503000b4203501040e0011140340400f4841010120300301e070780b112100803108051f403800800c1c0b64010711540c042c45981120f000e02e4800306501c0c441c14031007900b80c0d14030140e450340f050b5511858546e0f516100340e9940c400905a0750302d4200000d941e24118812980541c0700026008140e503081d0080710030b0f44080d4400c80c3c220310705030f2041802e800140d21810000030541000c80b16409071003000c40b80c0c0124000300c01030081e1250b40301c4022280c00ba400d041c0501204000354842450060b015004004204031850403007486802c0c528140d0710010003051203402404208164601100151801107801180780001170340e880c070700101520b8005510082c580f25510b1803091082d40450742034107980c4030310103544080d226080706a00341e0003217000c000d601c021806941410454141d00110017805034107408507a000f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667582293 1250 667581043 667581059
    0x3120c0f1305010f110c040507030e030408030306091003121107081b120f1b0625031709070522092d081206041e0204030302060c09060415030204 64
    0x8000d0381c244070300740d414680811440d80c0011498906a00504140780074094600200303494004c40c82e1102e1085035640003040c402c51090b07025620b6190322108aa90f40d98541d032416a8981084813881d2060343c071040054034120300850107808a17548500001d03000c880420064901c180c18403080052031281c48400281c580040080480c0c201e80c040a9203801c0ea19541230099080c844504819590f1041114010300103000981c8120700e0340484d030b200f1810610b030300000e030b1070f2041012030110741210000038074241030f50307101d40169103210b9101c1c034502d052654202080b0103000c4401e080c458100c030904000ca42041e1342c462000c0b8550700786442c81c50b146c1c40505003c9441114007541d059a603082e445502d50481d01c407103011295000341c130681120080d03030313520301c00e10401c01d581401e90290000329805403100d41008210f01d13128075188141114460401c0c00a4109100907401440f0300c001055059441b0710440d207050002620251529007468880d18558107050500400c06508000000d5480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667583543 1250 667582293 667582297
    0x3061305070903031806090e10091517010b0f0411120108070510030614040b040b0301050103061b0e060304080304020d0503040315060e060d1101120219031b0203120c0f 74
    0x40c0036502d403145182c1c190705004040c2c201d1010004405c1d5201402800200e80103890402111080c90b0582880d130b81e004220384220f110b650000071605d041c001d001480e82a00c1d8404001d9428502c200c61114a0a11903e401c0c2d0f542046034640001c4600c00d05a540d04043e00500006241c051003245401c50b040319458500d0000d900c1080260000302040c003041c44c0c010b156200d40e42c158034092040504000040c0031100c810501d540c80b8643d0307410181030350344941d000502074840003802000300d583c2d40c2c1444005807681c0d4410201e00c00c040c551515005008410303203014030398080c15803811607503036a0702e5814550020f001aa032099002c21a6000200100014409140b00b0f20030740007692400c0c0710000c1610180c0d082000e90fa40c2100c20480c0035201c2ca44d11389600e5801181108141d8000f41c0141c841c05880107043d02c4150001556079141e1500106007810000f05903820000c1c0001807158100c850508030340c81005070020815258001c0c1024489600711501d4103110745840b03010142e4101035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667584793 1250 667583543 667583551
    0x5130e06180c071b24090e16091a0f0c070302030303010b07030905010905060d2d021306180314010b210c0603060a0b030903040b0a020f10090b0c03061305 68
    0x20ba030000340c0f141040910b01e00220001c440c0c11540f43e000c0d0605458040e2100c002e0301c0105003400c82c042c20244a80b0410900000704490000145242002c803442c2300343c030384e6800c04140481c1c1c00b4000042c6c141c42c85400b4230116044080783c2418803603054031519280d8003203200510700c1e02c508180440569000d00c0118007c0000d200742994800f40743c68003030b00c411145e6000505011206034100403948401003202c0b03030800d00b203400203440021020380340070200c4600740d00d00c24145002c100e8a120100e5a004120050301e0380c0d00c0104150365085e044074030250000118081841c0c2c68010000510f20350034408056101d0740010915480a40205140c10b010403e2220300301903984c2c1010f108034081c80700107a050f0003951820303c5d6161040100b000d0b4680c0d0f1080b01105e410004c0010180403060090300d014054025925980703195241c5c00a688181c9810000c5890054a0308100d81c10424450168055484042059255503845a4410a4000403c0d00ea0041c421007013114403601144240c62103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667586043 1250 667584793 667584811
    0x50a0203120d0b060304031706040933020a050a0c0503091c0b06030c060f090f090a021905071e150e01020a030e1b0f0319120f05130e0618 61
    0x403101ca070b400a80c03d039141c460109018003010000d0002081d408a40c1e1041c0142110f5420043e4840401040040407580ea001d13014111076410075500b244068281e000140c0082000d100200d00002d010049104407403120010a030308001840c08035004881c1c1031081d40c001c03c16242068280404908080075010300d4024031200c00c02e140f41040074504450390001c00690090018040c0400490340750300c40c580595800e02008108840c0598442101c0210040e001c2e08000c05c900b4075410303640103908801030300e0460020307086541c202d441c0710320190780c9050703000380249461000c0146900140c0f01e1520007900c1454841c1e403517440e0a10140141001261400300059452050b100d00070111841c0c081b1003501070b0000418400100d5400e40ea195030003070200c0350403600082c0c0c400040d00d01685042900c2c82d100b42c0d80da9000a12019600c003114010640d10307045040440703884115103510a100481020181044092184d81402e070f9180e0f41c0201c018040207281c6007000a01142d0b00012104800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667587293 1250 667586043 667586047
    0x6050405041d0a0618141b0312040605071104090c170a02090402040b060c0d0201090309061b0605060f031e0d030501080318010c0606061808071d04050a020312 70
    0x39a060520840d1401e0310300a0154880454542c40c031a10354518981c09082d66444809515442c030a0301c0031030b0740040d40300081c18502d140b001c00c1552199a40382000c0c171000d058405906c1c65040100d402582400300984c0d1170b1074141800340030307501908035103800d9658503000c0230441c0701031b201c41c440c034505070f8001d480d441000d51030065250b00d2500c0c0c007459840c40e03070040ca007400010380310804c116802503811103000c56100880c0020880c28000c030075001480d4032642e4258607403a5019884425032902960b9004000c60702d5079401c2c0e8001c070401070111000600c0703101035004034009500298018030700806c1c041c0303c13000790350002c1d01d42003100210450340c0c084c2e06e0079000e07240e004006882600c40d850034140712541c07401411a449000e00d400306001c2d251680115244c0c0e078030030721b120083c0591140d42004599200c00004081d1090012050004059520040340c10340002071b901049649506011241242e0000340703a0f120000548101c2d01c611820500000603a01804051020003d04078041e07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667588543 1250 667587293 667587299
    0x30304020a080106080a030c02040905031b0708030301060c0f060b0a1d01051c08070609080d0504024204050603090114220308060112050a0209040e24130c060504 71
    0x10462540d42c0310300142c0c3e2601e003003042510700c04540c4007600d0340c140c14840480283c500209000d00b000100061840c000084c000710410186110210640c0c0b11408465903140c03540744c15a9288000c1c007802c0d0104100701048000107801c9031300015028030414000c0341030203808002c00c0c088c0d481d036000140342c140c41303d6010070800d41c186030f1540100b40890340340c4446803021030740c07100c001540d05003c0c01000b800580362081c058a508a48102540320f00c0079030b030790088480d06c80018442620100c0c070070f0310f18000358680d04000340041c00e00040d0880003030034202c1195040211141c12034101002018050100103003d0351b9104c09988250040300c00403801c49072030058003207038510003480c0303107213001c4520b000c2c0d0300b92420300301c0070091a58503090045054503410010781e242d10401d207000f4405800c2c2001c000180c0e0746900500410b2030305a03414001000c1c010803a5845d101406100078104080a0125400c0761a411429800c01c00301a0842800701c090384170714461182c681c0200000c174100240c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667589793 1250 667588543 667588549
    0x90e06130903080910060f0b0a020f0a0f0b0916150905030f0706030608060405030a1b020d030f02070b280c0212060f010b190f02240f0a0501051305100e0903030402 72
    0x14a040e1700c1503820030010541001d03d01c55100341c1d107000381c82c24001d02242444065000b00200d120700e83c4118100c9800c200a49040c600c05c03c03480030219040c05d807881c081800600c4c0020580d0851280d080e000d40624180703160714038405052071003c07081111043c0c000849032020721a02401e1400070300038044003802c104018013a1801a032010205034040f108003c0803407000300541d00710007041e241130022341c80096042030552100e07080107544641911403020400d6080514070560701d855400f074401c0240e4400c0d92004074092000d1803491609943c49081d24105a190200586006030803c01102c1c2415004601510a000c41d8180c080d0f102005000d4540d021284050040c480741d084540740022a400c220004400034104600380091000c100e90124002e000310045200d0f090320042c44201d02c46415a0203650680f4a039018880f01c00201d0040c01060003014140c0b84003405152100300701d5003803c03009240041003140e031070200087c0461030000203010140120340c031800840c3c59041038010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667591043 1250 667589793 667589803
    0x108060c0702061c060312050a0207061d04050408041d1506090d02010e0d021005180a0302060f0a03090c0303050316020c03190201051c05190b01090e061309030809 72
    0x140400d84420301103400165249001c8800200700b40441c148000e0305801a440030780500e0708010034504c1941c80e058241d40e40080a00041c081d15401c4482e1940e86075400e03140c0440c10f90003004c4141d8103c402ca021420036802a13504548030301240303440c295a420700d032a1000c49001d0007040c80c02c50941400603007021148103604055003103444a01d05820700300000c0c40382c115103400a06101d441042ca0381c181d5110540d46084a8001e0030098070714094510060940c0c0c428040e00303824140d41d083c051280d04060510b90103481d400b4100030300d840780d00c40d101c2003150450300b0000b0030980c80745c1c003100014a15810710401180300b51200c985904041003403100031403a180b03c079411580302d040702c480d00e5980010700c01081070a400141550580d203000403515407095000c2d43c11132041301204454604035580c045440b4000c4a40042650031003254803809441c036203165180003403142c02050105542240340d1541112000b031403005041c401140b60001d03900070b18010340c0484c4510b010002040f1040c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667592293 1250 667591043 667591051
    0x141c1506090e0105041a120d110c1503090f03071a060111060403080a150807050a15080a0b0604030f0b01051203130b0705012424120e030f070308010806 67
    0x10a50360726401c080d08410440414456140308a44421031040120360030351808190713840152141080000c4095455039642c1544080c1000a15600c0e4910305000c01180b0040030f024014807940c0c15854010100c211500050300440c1980558013450441c90001c00007011400d201c2e506d80000103201e4402e85110040c010178280c14000b10b003500000290f400300e000c56000f649800c122981d5200c4020306001801202c1000d0a50b0a0007074011403100b01c001503050441d81d0844d82c07962499282c403030000c2e0035110b24080d4804114a140403a084403d03a8021411221004d8205410240e41791920b1a50103420102030300c5a52180d00184404d060145400c0d00b145820b0008502d400d01086896600280d9442090080d0602041c1101009800e4200f000041c108016aa4403101c031084110b8426002c0d10400d402c0f0b806000c01404003c0800759400b4981c507040c2ca131082007044000307011000e440d119051081c940000c2180b0745c0013200c110042c00e0300600a50354003240398101108a882c080d00a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667593543 1250 667592293 667592297
    0x7090b060c03071209050409080c0d180e040f021503090709021c02250803011503061401050c010e0d0c060e0309091915030b06011b0302030406141c1506 67
    0x800740c28002030002c229001140d218000414060030307890220380030f24480e00010303809030500800300103100e4040042d280c1540c081d4140c078184a05110151060301011885956041d11120200140000c00e0308055000c9d01600b094503440942da800128008020205101440b802105220709440e04211032000340c61032020845ca030948000c000d520710701200385003e0f0455000100d1a000c040048148840f07000c07214a022070b024118603242200c0d03002405001599036a2820109196100e806003400700c40e030f152030051300e80003020f00464aa40c40320320800382a640b0b911010340c600301d0800500707070b8003100ca41d100240c3d51200d140c0318060b540741a415907500c4d8810300c1005a166180802c042c2c0202d1807048030781007407209408a1024000b12641000c600c607084900000380960f15112610a807000d90b5030070700b040504407446c04e010300d0208028006234800d01c4280895401001d11444020140040a0403d14201000e00002c0203550703544151546410307801012000000112000d40b00354 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667594793 1250 667593543 667593547
    0x2041d09100e0f0307240203150603041e03031a040204140910080703080403060e0303130204020c010b12100c39120903120207120f1407030507090b06 66
    0x189029a841c1c1407002001155580c9000100752032000300880d000e500555010740391503006070f050a1403900201c41890040002002014203602554400c580c03251603a501e10340658444a402d00145403c02001141c40401441d11540d481c80c490b46400b0400703220740d0300401d41d040341280089030520b2440c48280500c3c010b00050203144400d8188401450301561580c5442e69140860288203030560700035099400b402d00d0200c14001e01e00010001d0b01e002c0c503000e005603000d41004c07503039030700c02220781880120300c000c10680103107881d400500148100c4000070400c0f200e14000a0769504003a07114000c140d10608580c400c880e0b0500a0380040511410108004007034062a0011640804906001e00c5200c032000742001080c600d00182c080d4201858151001c0442d00140055140380002e80300c00200704402c082d800c0c400100101512a0010480c01c00c1032250746420076880000d0045907050001c400182da0384a04000d8107000314080c000420300301b454802d00804a409021b5424059070341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667596043 1250 667594793 667594801
    0x201c0c031e02070312080901110f07060b01140c010203150a051503190f0b040f05011a032d15010e0a030b10080105010f051305070c081b03030a02041d 66
    0x34681150311901400d000d60086603078031049061030b20f20341005140341c40340703d007001d855988101002e100d540410001c110341030b64540b0303403000c6028012590b002950104509000562140c0100c4500d01041c14000035001d403c0d01b8144854010350004a5117030f5010040000319003040003480381840b0103541e16000303541800e010904c18060a9401c1030100400004a0086a0b54003100e0f05240d100c1c00c402c11001403400c144801a0242801951050f03051480c501440081032003094100c0d17006241c650780545100b825800180c200512800e811082400c2e00c40c0014051642c089a134400c444207070982d0b20703144125150b11a0364580c0e5904225000c14400803644451010b50180c036000340042c029503031421451a203909240c5c0141041e542003500008042d0380050344074054a80441c3c504180a80c403001d074100700c4200300d4420001070040f031002c00100c0c00e034000400d801c08c3c10306007018488000d0a0950f18650068400c0108181e0000e8100b00012100347c9090444008186120960030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667597293 1250 667596043 667596047
    0x1006090903090515030c0a120203070806090f0702030405010e0f0a03080a080924090a120203090103060603020f04032a0608061e01080f09012007050f0303040807060c201c0c03 77
    0x10006010300d20006000c0c000280143e51785000348c1008503080d5900d152158004000d81401c1d902c0c40d001c0c00048020036890740140c040d661042c0003036030045007850b00e00b0004407103406900d0750340d0390041007041821159486011883e0041c42c041d045050307a03418108001090440b00604200842e04220010444030442b00d440d80701c050000c1c40e40900b141c445a221500788400400000e052071041000d20b40034503000f001422000c0e200341ca08102d20740c0d4070300c001e070705a00c0382035102c41c0300c040100000c0c000100881e041e01002a03107500142c041c501000c604840807084c80d00701001094a07102048024130300602902c80d8500510030b0600c2c4609084006131812002421960307401c803a080008a0805095200c80c1d209040381c03100c1000740e00070b0380071040c80c0d1344545000e0f1075900840745071402c500360000450b801140e000c2c41880c0f43c042562515802000460401005c1000e42000c410008800000c4010640d020102a250726200300032540741c4400d07605207031810b0061f64000800465 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667598543 1250 667597293 667597297
    0x15060d14090d0f090605130b0c07060212040e010b0a05130f090f0603110d050c220e010606020a060905030d0c120b01090f0b0310090207030c0501050c040302060415021006090903090515 81
    0x1e40c05c1d00b001070300c8007103618091800e81c20541280c480f05c100444c1400d0b200741d00281d48000c8840c55002d982c0c441003600c20920051040303004060011000100402c000c040b880c0c010701c0b01c210280782190402030100544090740c4e83c980c2c010300203c0700d040340500040329640b0408a107010140003c00045196640380e04480300a203001d64070651904107824140401440b8040c0d4400c1c001749241c204116000740c00d8010b1408031504200b0302c1c03820b580044ca1503014404e4009603a011f0300200316040441d50b032580078280364501190306000c1801180c0b11900c00d4000d1840c2c0000503214600344500d500c4140003160f8a4004460400c000c2c03240c00c1129031980d031103540560301040045607981d81c5a19450080484079413000318820720010f1600f0505900901102c03860344950024441d585600024149a000d40e001c042d503c040c1c200000c00c108a101a1249014441c50042c0d481045d5000382344030441d1120350042c00d11a40382c61b4440e003015404001030018140440740106622142c0d06001864 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667599793 1250 667598543 667598549
    0x40f06020631050f03030c040f050a0302310c080f0a06060509011d0d03080609010e042d020d05010c0e01180b0c030f070c0906080a0b15060d14090d0f09 67
    0x4050392246490900070144420102c41d000c0070112031b0389051810245140b03074040e00c600848211294000305903807905080030703400c072030700200034244035202c3c181c802610400c01036161140650341e9126003944411070143d071048a0142d1641c0d411468100d10340010520000c103a819141e103880424040d454008013a56004a0b0a03e0720708146091a1a02d08100d8410381286901c071904000060425500015440c4141005d40d4002496661042d41c900ea5807803e8070010101410701c0c2c0320038082d4100c5507141d0700072140846000103007291600070801c15450b07000262a10394640c80341e82000d80c0c01400e11201c107030080c86c0c10308100e0300000c040072807045540500c100b01040040d403d076a81504000f601c004610600b030550b5144031602d02035103100141d1060344d407800d0518034009240354001c0b034003e1760607400c00202049907480800205258480340e850701d5006a06000c02094007002d8400c185540c4004440c0900604052a040c0c2c54050140440001c01c04940300002141ea88000b6040c11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667601043 1250 667599793 667599871
    0x1c030906051303050709020325021b1804390e0a0b030706170f0c12220609060e07060c0b19020705100f060b041802090303040f060206 59
    0x15101c0c2200d840c8a01810b035071020344184500240881c15003402da006500450380564896040c81d28581051218000061181f01580007880205406030403801d40004d1104020310b0104201c01c0320300c290a200106440a85010407002c0300181144440796216014480d61881c20071103c82c580306c811351403100340c080d03054101c4008000c21084206a0415900007400806942c07a60b1b45071080108044030650a1414811002d40403440c00b200350810140112240300031186040f03914904e06d80541e401401c4040d0b14070403408051246c5100509441c500d81c0305040209130ba102500b0118140c5502d4451100c1d150003045003003002c1038010001c248442d501080070700302c0341e803030300703100350260b010b0380c864220190000512a040001c04140c0b040c00d012818400c2040240411900003150355901a00001400412007402200003004480c10784103482800545803003a4200440e045420030351040e030007000f2030881804956014049658030044030782490024010181e0019040700005450701c0c0d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667602293 1250 667601043 667601047
    0x12070f03030b04022b020408010c05120c280207090c05040e010e0f0609151807020f060c04090b190e0405120315010e1c0302030c0d0302180103110d05070e1c03090605 73
    0x700030170181d0180d500411501d4000c028a01c2c034042d014019900070301404082c0002000021405c8400705c040c3e40c11200388100005a041c25026141048203046000c03000b5032040ca000080c00c490140200880001e06a2310380b5140c52400116030001c2c0010781080a10b02c1c0d03000200300d02c0407910f50b003080e84410211518003190319080d603407032081000096101d402403c1039401503c24400100b1141c0107011b66800c5a10790744082036840e442c0e6109645d0003962074410001046524ac4680001c01c00c81300c010460140d0320b0340d2101458071840d40d0341c01840e03003640c40001c1000780041130101a49612108c201e841c80c41c5006402c030b803242c1c0007805080f0b042c005131000711034281e200c04801490000840490141d860303440e0030040e41d2038120b0211000e0074801c40024041d003622a00035500014050403071180412107042c01035010b0044040b61025122081c02540300d8003206018050144800344c0f503007140700c19064184126020130329000c644600c20280c9420020790f200c40240d0441d01c4078a040d07a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667603543 1250 667602293 667602367
    0x2010c170c0c0d111c29070807140f04090623010f1e0c150504050d2f011b0c030f1707080603030d0c02070f0602060108060708070212070f03030b0402 66
    0x4114142c4175140074082c110040e408908042032061724007845c100199580d1400e41d6214800c13104540d0481c1c840002036140745408114400b0240075041c0800411340107424151100030f110201c460580c019650003c0b4a005a40c501404601040b0041030070301e170454070701c1140c1c00040d040a5842050034210513440240c00c4010b4802c11883c080f480d4041c070f21607003500010041078013400040c2d80541d024005c140011514901071510f65004110161500d129281484c400e24454425640702440340d54a0303e00e580c8010103407030f0010900d0840c9480d000700206132420003c181e030034008102d60034000100c440742d415521191100340d1002d00c52030108540d5462601007410f41c000c801c40c0b40c5150b030a004980d01c4c6075030007060002c10388402c6071a4001e16640c1c0c7d07108030703540d25081c814801e16403c4003000c0340c00c0c6885010016801003450040710051882121101d001d40d11061060f10305c40c030008805020140e1601400710394603002c0344c06604150710a0840081c05104a03942c0c500942c400d0703201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667604793 1250 667603543 667603579
    0x31b0d0522090f1b0521092401031407030c0302060d0902060309010902040b04020a08070c0503120103030f0318020901050d030311030109020714070305061302010c170c0c0d11 77
    0x410107040325002c14032036045424561030281840300c00d01d44034250140300c00281240310f10b0940e501c400b5000110700da0320700b07091081000b503580500b0400c45801a009451070306041540b01c4800d24601130f10b21001356165080c030042d41c800341d1310201d1554000d0741c01040031035098860042520f0301114869520f0542002c24801040c400740020b42144012007080403980042d030040c68110b000740c800b4413516401c4030400c4124440c80b00404007043c17005011030a4540702c0c107100300300e940c400c3c0112494940f00010040e01ca150980c812400511114226260b45515008411a017122120100035031000c660004800190500444d070240c05000703204402e040c441e400000c81a0f03040103034581d80f961210020400b96001300d00c00d81e8800f200c01010b00103a07400254010072241c100c4080c001035103500703102d10744c00710582d07905a0401c001c00e000d00b0007081682c030810104140305d10070681e0700c81c40c511056081030b100003175007031207141d480140130f0108a60641c0c0d4580c3e4501260300500d080070501c80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667606043 1250 667604793 667604857
    0xf07020a0b0c19090f06081b031308071b170a060c05090d12090b1314040b13060f0b070c150c1a0f0a09080a031505040e031b0d05 57
    0x1c100c0e203e211840030f100c0c0894016a04034140c4510717801241045442c1c24080c2c6000c0c0d400e64400c4d58200041140c2d41f02e640410015581000007131240d4095402035840711642500b01c0035050b5600012030890794403a50442e162a0024504e91040d0f610b001120070302c0c103403144004c5102170300c42c80e150f19005074154851003c56241d29402072052100541a0815081c4294a059483c022865608020030110790020903990804091601d00007074030306111500d03401101608026400c40e417140690f514559900c089410b180c101624001200b503e4001c1c031081f041599172107644440c5040100a0118084050000a035005004a4201019540b0040302d1400b000203025192400540302d1595460760300255a0244031076400700c2549486540d10316048400700c4100810a08042041c2c1c60381c03a010b500103188140901c00c1c1080d4482d60b80b0007290689a011030020145d8100050032403001c01d41d03070752100300d40c00e5100080808880015001d0400d00c1514510000750b11010610541c202c00400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667607293 1250 667606043 667606057
    0xf040b13021906051b0102030402060a050d0609020c0a051203060d02010c020303130f1403070b030403030902010903050313170c03060106180b120105030d081611100501120b0f07020a0b0c 82
    0x2600d40402e42d5662009206400c503c1d20301d03000c888480c109800340c0105009617801a600200407524141e400e40b0140d03074503440700c0a0010040d407109000114844244003500d0720400c1170f409080c0104c070388d18180d810500c108074401030100042c014814036131600c0d440c0d54501d0f40c0c2800c0080100b0384c507000207444c60040350f50b002d03816103280401003090b0041007203c1040b16020440420400c89079000c0503100e103e82d00178460054014400100803034880d400c07240b501c90040c101410302a480b0384506041d6405404c4500e00c0d0a00c01134100806030300c1d4040a65400140000780c98002c504400081d110341c410b1089504028402c2403442d6003080fa450034000408006070010366555480302003122180c42440703054440d0141078180345405004442d02c030312030303403030202e4520060341d41003801c1e681c02291a40320100361244400034044074003a8483e050180900d18685202d4510b28076041d400030000520020240c9012000e1001294002440760152a0b0007501984165280f003021125802018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667608543 1250 667607293 667607329
    0x18030e0906011404150c02121e06040b0a1e06060525122d0e011709120f040803030a09061104030b0403120f050f060a091802130902100509090f040b1302 67
    0x8a008011200000b50f8113600c0043c020000e42700030100d40714141c8590049901926100c4264009030340d602003a440600203140c0c1110f41e2a00d15211940c0c8030440b0110340140010131000620075040000c0409902c001c61020302d00c0c4100c01320190340b00f06080c1000640c0b0414008140b110240c904445031403c03070032540c1225040c040c01d0039000003c2c0b901c200020071501041441c29060000b60704525010b01c40c24256006280903900914058881da2043c40740410b80d002c12300000c520040144005d6000e0001100e02081c89400c41c01c0400856511102408289008010400010b05000c190b0707940103401d0300348400383c0c4c1c114400d42c0010301840c420301208a85030038100142c0400c15001e96014030829a24400c1103501c90f00e0140484011070400851101c2c2038200d800185042e02054854140328038011403102c1c81035021442c04c003040a01c40021884c08504180b140c01c2078110a94020f0125001144605260701c5041c1c100801901120709490400c01c24000d540300c411100185101030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667609793 1250 667608543 667608559
    0x3090703021f0305060f0d0b04020a0f06080906090c0913032105040311030918040c09021306020d080105010801090509010902030f0c0109080706200118030e0906011404150c02 77
    0xc80c2c4841454142d4001000121303140c48007040d060304120302c4003401d059002c0c04050f80941251501c0100280091040707a22034203083c004106c8429041400004240c03a456041d40c5003004c4a2690400303d000300002c0c2c0591001c00010610350354291034503007003c600010121841101e0500b00c840c00c45070301c04180340c0e43d181c1c0230024050403d07920880c8654041e9403200740c050800c05603143c580c801c043c00681d01c04002d4008082071007240e0400d50f081441a20a401c0030ad54075240f08090360810607440381d024800040030820b5a40500c0f1244900003140b5102c9025810480040e06607041806401d40aa81e41c0d030000f52061000d510150070113400904032220146180340d040d56071240b407404d00740040c004000000c1c480d84002080c0307081d540305494102e071106011310a0b42e40d40c080841072240c10343d00c6011544c2030b40e60301c040c0c03024424000c1c0e0311044c58034040b40911482080152140741008811a0221174650882047d102581c07040c0d028007400e480c0b448401c440d586e0407004040e50002e64 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667611043 1250 667609793 667609819
    0xd0e0a03120b0109050f060d02120106020604050d111f02130b09010e030c0603070302031e0c1201170c011115130b070c0515130f0c14040905120309070302 68
    0x76200400d03601150009002407400840110b03518040c612071650800020908051503140c00c4000d0003900507003034001400c01c115410000307120082a030203c40560480d5041c0b00520909102e10465081d4504104d9650101e00c03580965804100402d0080da41c071f1074600d280402150380443d44241e42103207414450a450700c105901075071021101e1404245114629405800d000c01c14010468009000b141590f860541c25002b9501c001c0c94403886a0444031a4442d83c0070b202c0d00b050141071032100e900c1e110160034510380290481a08000340c0300c2d60030064030900303180008222000c0c001c2840c000520380000041d9514058030308142501042d108001c00c4144003101c51801d81e440e000c3c0141140c01d454800065a100c21405801381c0950407148031401013000040d00181c00001821284881c4001034840b50b140703100c820011200e01c81d4141c020009500400312400f2030010403201048005800e9580d80d46e5190310381c1003410140801b1000a1f4424814004040255005404104801c40b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667612293 1250 667611043 667611047
    0x18020d0c08060117031206010507140703020f0109030b18011b030915060506030103110a0f060c030f0e0303092b0804090f020a0819060305010e0c0301061203090b0d0e0a03 75
    0x340354000c9880a11030400001000740c0c05031542494443c0c1000610710b005521400d03662680d1009280c81d041c041d04100000000f1070740e0101c203160309480405080d00f5401c44c81081b5841c0059861941001050001403001c5002d02e0780c001c1d040000d10070f1120803000e000755a00d0252284120f0761102ca40000355260501e40c040e040026018414000940b00e205421f0f5600b00719122405201d4000c0c4042c030040c000035252050010304214000c0021102c50b54802d0485c0c1c420344182c0010b00000c190136851000c05402c181010700172110340c2400d001881846000c81e5407401402070080c801c0725000c84800d00340406100b006506929100c1c0e444601003241090440350f0710920680601910b0002c003c609800300340300b43c40d40203038140d031484524fc43d20744004001c001081c000c80300d0b203a0755000000c0003071400d204045801070204060306901d44c3e002c0c201400c403100b41c0c1c80410001c1ca41a101c10009a00241810954949220440c0c0340c41840601000419428005540900c280000242416 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667613543 1250 667612293 667612313
    0x201021c1d0306160f020c03030706020901112b050403050712050f0d0804030e0612040b06030d03061421190b0112030f030209011b0c1a0313020418020d 67
    0x80c08825000c06034401810505030f035120215202c0c08a64042c1c0c0954050f1845500541c140306440c0c411100f03840720240c002800c591240b5030403940399034000750714111541c100008000c1c2c0f01400015102c42007580c62800360000300001c60130f0101c00a4614440030f00c2c00344e010740d005160403c00700c4000949810180da00020740304030130384446c45003002c4440c80300310015034014084c40da540d40341c0540d120f5580c19940306a002c503003194021024081c540740404001c800c1031041f8042c41d40381015081400a1608140c40040300130101806c0880030f02c0384100c00c0c0c010140001d0141c44004c8884440401004002000c0c1030021641c0076455458108901d03c0382448141c0b8010200c51301d036640d0354000a14400f10403107001b0003150048001036030701800395001d8500c00d00c040c10043d00c1c00d1011990055034258401c03088800207250141400301351301c0740079558105480d120200c3d1035802c0c00c22000103000701501000b8422521a140001d05800c0800c40c10350b100c0d40035041c0c001d880d540c2d1800080c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667614793 1250 667613543 667613567
    0xb0301080d080c03071421090c01030f0c020a020f0a03050d0f18150f03020d091401050105010c03051206040f02121f120305090d02060a211e090201021c 67
    0x20101804a207060b05a0000c41740107034180e4642c061108004021a40c2c41d80250618400e9203950f080366544280340444c002c2d1141400300040c211035044d11002404131012302d003002c00f947c3c1ca440030300070010303400103103002c12660100c0d00c4ad124501c0c2034000417107014594000030040d01549041150030360f0800c0a80310700f0203068403281e41c89044844144203407180391113448140f40b549540d83c0000c601604503066400168600503207000340c0c190140d41564203c0d6000c0712105262450708920303580038031949015040918181c0c0c649481074400410b41d014804040d841c1c0c0b401000802d0155a8541c407800b09034259960654803200e00781100e10a194044860810040c0811700555020890503642c10a646807907064001c1c0c500281c4040350709401c01030380715400000c03400b28400540d40e80c10113054400120b5542d80d03d00e4805006a1484900000c00018014141160000f5900b0070717101300f00c5014040d1000081c50f007140e00040745020300e0070311408078034507840e0180486298065021024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667616043 1250 667614793 667614797
    0xc3a0309090b0603040b040c03170d0501080105010e16050403060f0519050601050315030109020a0801061a0a0203120c07152903071e0b210c160209060402040b0301080d 74
    0x60140e44003070410a0380d00c50942c0c80c0d448541000050700090f03029022940050040741c0d0740c0200c6840c0d40d1501042c030003035805031522410218001d030f0201c3c00c900a15014051a5000744025450b1050038145520007038001800d034451102d0056009110317000b6140195000703d804c0c0103000c108414030000f85130540d542401c20003442044103240610340943c41c000c401c1070f91900d00e103030341d0390781c502c1e0004001c18000c03070345075490b0312124000da030321f07410080040c1c0b400c0c00000034041e15022889080020100c6a0b09060600384800e0058070b0300401a20442c1c81c01000c0c400307443d51104084580d91060542c000d00820a6501d000d202c461140c0c490245ea1100d500e0580c03034101d082484130051060b00110542c1a8850700c2c0030702145006216041c4400243d40c20044602d481d0080000340d03801030744800300e0f000600c0c44005100300f041440990030040030300c0c10902d01505603281c0c0c00601803144003c1e00230348a1001082441d1180c0d8120b6006026030000103807a541c4a14950740c5600c021124140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667617293 1250 667616043 667616057
    0x11509060509030601140d0605040b060a06090e06010c110409050d0206060a1a0705010b130903030501050d0803180309030706050c1006081f021b0a0506180c3a03 71
    0x30030034080c40807503412040050003000ca42e80f034603d1104816a85c2d4085981104040d29840e00103842400307558002c40c41404540110320300702e002d10800310400d601040401001400810150f01004c1c4d155400800a1a040114a8050a144d5103400070b801500e80c0140c070b84110107041c45808121019400710550136580982c44d40700030004800b05900503105110000302d80c0c8194012400700a1004a21640c0049004a030030000613007443c1410410080b1585c83e591402c04040d4144500760141c50226030f10329919060391603500c181d000c014041c1012011210000b445800c081041d9203607800001c0c1210401921040b005109800c11400c0121522902000d07044068041c000c035400d440b00c034001820545403481e00c03020703a10001100120031550130800244c3e48440004000b400c14110b400904003d10340340303402840d000f8020224034003c0c1503441089030b0030740040b0340c140000741d08550074035600d2480b050000c0c0701034902040e031000650300c0c03507a5441c00380c8026040c91143c0c00ba8403185 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667618543 1250 667617293 667617299
    0x30603120e1008061302160605040b1605030c0708070501090c1221140a0509040f0c020d2d020304050928060b03071b05060a0501140321091305011509 66
    0x70b950075800b520842c0c5e02010554581c142000c02e903014240940fa00701074102132105581365042229002d55081d5080502c0600b00400b86801c0100c107165161203207005490741c60901078440c61805140e10007400810001402c4003070003001d402030002d05030802d4019255680e1400403002c4c1c001d0809007140c4003034001003122206040800c10401100140e1661100302146020074002e540c0420343d40c8040c01020300c001920303074a840c440c1c440c1c80c802450b000110308106507000303403828964045020070807600c1e510805c2071408511402110340342c901c2046a0740c0c42c0700c03141a07003140115009030350050880f004200c803001c3c601c1c1d1803040d00511000106146c00d40a50090107a9401e406210a031010801c04038240706e22a242c2c0f50094032881d40110101544c554941d41001000d840c103600c22900c0b0001400f07800411048151f50300300850007418090701030380410740b2541c040d90320f480e02000c0c08101c0b081c041d10b031074070f1088025103500000c11203580c540542411410091203640c0008440c48008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667619793 1250 667618543 667618547
    0x30a03140c060a020c0c091b03180609010204090e0a030e040b010905062d210c0705010e0a0203160807030b061903032f0309090702100e49030603120e10 67
    0x26401648d004200303104051035201c1552007503002510013121341c03c0b0a84030110084003401001d000320615030016035114600440c080695110040401d455000f10384d09900080d080700c00c449100800703550200d4040d80100050303541605a90095810050000350084030040c1c0c1488491240c0718405441d02e220301f01241c40026008590343c031118020000b05415880300782d1500b0590080559040360315082650392180d080d21b00403440760b02240c0c0000d0890b402c5103024014100035445a02c800400d4901c0d090700159680103610000d040c8401400210b035282e00c03248024600c803002c090b154203a8994a10f002001071440074405010414141c1021030480f081c42035070625007290500071814171010400f044244c4401030304000c29032241028603043d90301c5600400c02400b0700c500241c0490340e1070001007024002e01681441603144000c0c99185000c01c003401c2090078400f031000707034000d01440c5a001d400031b02283e0400760684c41340c0e01c0000280d0703500c801c003511028029524884001c0c0c0d02502 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667621043 1250 667619793 667619809
    0x50310020301230102102016030824040b130525030516030e0a02040c020705030c040606140f0403021c030e0d0b070c05210a110a02030a03140c060a020c0c 68
    0x1c0e1600580012200c0b0311110071540001f240504407900101c0c038105682480e4169610080944000310200307910a014180c1203031519510200f0419550010a00c102c2040422034610200c01d118581c0c8100c2d8490588030f22409007445110785004122302e05140840041c01610803408011000b92641011003091013801135601901c41950850002d40405605801901c0d2207000c840d024800e4001000c0541d0b101d02a00c8000040c980190506a0601c030138541400281450a03019600303081c0204101c0b0b501c080c205d41135501d888101502d904034624800407611031540042e5010700d241c1529104248403040c5104894840d880d0f00340d080d2101c00900584e01c81c0340b8409030400c1004400540c1240c0202c18503000284104151400c81948070410340c80680d0134410000d0089011500d441035a800c001c441490b130380c000000b06100d015560001e40d84001d0f2880060070014410482c0c0540008207041da072600e17540c0e10a80d4694a003a0801000130f400c1141d02441605c0350124201c800c0c10400390b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667622293 1250 667621043 667621109
    0x124050603010302040506030307060c1d180103080a0212040b040f1403120c0f0102180306010806010e010b180405090d0e040207020303091e18160e0d020f010306050310020301 77
    0x210841c2181c1ca1a000c020040a00500716070301400104525400103400d4030a564005041d074a80403101103e84210715140c0400a4144c2c0c051420101100c200324090000541100c2d80442810303916030300c4050490a06803c00c581c0044040d001c40e000c1200c8080300d000c2c10903209510800401280e5616481800c01c0303038110b940740c0540141c010b0b40d0380b41c0c0540006080407005101107808000100b0211400c81c0d1042c0344003101c022809441c011680b074148606401000c8034070040c541c550401990b030140260610400703041e848005404a142580464000040d61001300100010324200c0307500b54446424110400000e81201040205480c082c825260308503005001941400b02d0304080c0700341503003505d0982d0080103106640c020141d9865070402c081041c0000a1040b604100704c51030048810304881d034050104500000c4000d45842043c0344585404456050a00e161040103030300828142c0c0040d90180214881c50103101c50640040d4129a0250f03480310b0303005000100c204041980035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667623543 1250 667622293 667622299
    0x30b0a0608060a0b1f02031c061703071e050a0602030a02030a0b0a1203140412050a0b0a020436112203020d0b0a02210402010f02070b0a030c120e012405 67
    0x1000c94510f917011052608100c3c0220300440e8035004045200390b40494000949800700d9440755018050366001103803450003001120025070410059648038813508101c2c0c07000d1203525450980ca5020301c00b04200e41c000c1b090300520110b650741800c40804010350f0007114881002818843c00700200d040100384201103031410f01480c078805c10541c3c1c003220381100c07402d90003c0c010024072001c102084042200c01c41d4520070070042000131110b01d000c02d92000d00420002d46140b050104010071800341e810710000340f42c8485c2e4009001d01b912101d1004612030841c11b800a4a0311102141c4d20801c170000342125072260781c01c501c3e49022038071080020159408005d40002c500c0196200140e00410515013140c2c90001c003504211403080010032616800d00c0010040e103011040c0015540c00c0948080000c00b948040c241030b0342072800006151042c43d000344201581c4aaa9040103807180080304010b1070b180e5400d2080d11020004c0d01e001c0c00c0311500072150451100e16480b4400084015203044079009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667624793 1250 667623543 667623559
    0x60307150513030501062c0118090201020102071202070f050307031109100905100f050303070b0103020f031603080a1106190906020910030501080d020a0803060415030b0a0608060a0b 80
    0x30003800c4840740c002400721481c1d81000740e00440041d0084c0a4800640b00b0100b00b580c200e140e0f000c4480c4002c07900200d0880c288040401400700314a18080f88064080051000c40c88100b140f0040b4028841c10001a01c0c04e20801c40c50391007551b010030780c10b044a001e4403442c4605e68030385003015110041d40c440140008200c0c8080e5075035042c0340f103d2a50024400040050b03440da12803115054030300458010302e0406407070105116031001c1e038072504080d0506800a600300a442c3e074450225003418000640b250071091248a15694100030070500742100401c19000e02d80d49103032400ca02c1c3c100303001d04404144c0c2004404030451001403ca8880c141880c1d0b00d40c409418032141100401074000d05481e095000c11200303c10391102c59445540d800d8603a0009481e41c540340c910303410001004045011900701c001000003054100f41513030b4100000b02d0b0000342c0a2126203c1c3e030240e0640740d0000b88128064002c11440080550043e0111142c100a03034400b55039400c03406048030480704003071b0b0340b040c56 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667625899 1106 667624793 667624829
    0x8030709120302101a0301020a080610030b010207062715170c07030e0315040f06050109090206041e0503030f091804031b03050405061c05060307 64
    0x11400c1400400c1d60aa07002502c44480700602d20f000d685801100c85400e140805100d01114005c0086540729441b07080130b17001180454031a84502800c0020600700d238002e0058510115050340034090060074581c00342c1d803400000800c2c11528041016142004000c025154040c2c0040c08480044003103699006221b070210f00341d1103040e041c00000b0b1080b026890800c2d180b480d503141c10a01d407100090710100c0c1c542400c1e2001d0424868086080c80140007114450311205405201c1c02d101c103a898010341010745540e1039000750403120400c020072805202407955900301c080395030607075185a6124002451904400400c103800d80c0001007240d414603004021044040c0704c1c00c04030701c25103007585015145d28015501ca8840a03c842000c00400d4800d50840d0050b010040c407140c0c4605010301c05144144008100098444c58903020911501d0001103040885145d6a106048420 = true := by decide +kernel

theorem cover : BRFrame.Cov 667446043 667625899 := by
  have h0 := BRFrame.cov_init 667446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667446043 ≤ n) (h2 : n < 667625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
