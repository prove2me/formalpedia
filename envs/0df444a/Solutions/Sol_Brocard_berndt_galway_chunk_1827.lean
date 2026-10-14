-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1827
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:12.76596+00:00
-- url     : https://prove2.me/submissions/4652b764-4bea-4ca2-b76b-151fa083740f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328417266 ≤ n < 328597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328418516 1250 328417266 328417277
    0xa030b07111504240e030c0f0f07050d030e27240102031210030f05070f050a0509060112060b03160809060601020a0209040c0e0c1903060303050f090607121808070501 73
    0x141c9480030341c600c90341585400056601c401c980140001130011f0310100900c68043c004c0754554014052030081c0808203501a078020350020400350391a10700611001e81e241c2490848884401c0c0014030390301042d5034000d904003030f144141e0420b40c0d8039142c2c0ba01c100c9034040a010f014035103000702c0d88910359081507070b4050392080245c2c4c4810a5010078190740190120b050400050f10383d41c6181424020740d030125060b80c0410f40502c04c41d800d14000001415040d209442c44614140c0080d201c428041c00a9051018021103d80d102c0300c00c0c0c01c002d01030025020003a9981c01c0214201e12224402200440080d100700007246600d880451014020b520503030081459840c56000c1000025014004179054402a10001001042420001c0c4a0052260126129001c0e80100d030842088082c040041603d000814000641c1180945a1908081c59041e44034048200031904c03501c01d01b034028120722400481150407650000c0714010304410350b0842c0c001c060382c2c1c0c0c7d1b1155990f289405660702048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328419766 1250 328418516 328418543
    0x8041706040c120206190302070314130303120b0301060303090503010c05070507091d01060608160c0c170724140f0307080c070605040f0c08120d0b0a030b07111504 72
    0x10307a144001c540c03e900092600c0d14190940603400c1034401d03130159080c0400d4002c100745080c140c0000000d0b00814000605a140491200800450500e81e004c010180010b88103401d641e4502c581c0f1111110101034020403440392241005024002c50707106540c032070740c2043c010280440c4550155880325911000814000d0709100c9800e01500c40c0800d51020784c0d10000ca110040a0240104001010180c862444500304180942c0340041c0044c00c1c0c1c010302c441220200002181c8590100c02c954180d08042070b000c08582600c0e050500a40c443c291a410560328180102003141c01c02c040384180352149070881c51a00b10054840c00703815014411543d06000254920b070141481550004400d409107141691980d41c10040340c1c000d542c241c4881880303042003810012a001d2400240168500518070340300c22411420061241e1007003070022a485411442d9540c48842c6100099540680e0000d094504040002c12080718841d038400c10b03104000ca0342200c0611900c040e030141d0b402039042041d61 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328421016 1250 328419766 328419779
    0x5031314060f0f2215020105070e011209080919080c0f031c20030a0201050a06080703230609100b04020708030103060905070315020c0c030c01020d0c03031808041706040c 75
    0x26040f11340c10400520380c200c41c03510819000710800c405401c004000484092040034002e08480006080009104040550b00310390b80c0c0000c02c0303099101e61313102c1c0410164000e140c2010035008c1c3c0c40000350080f4903003041e0b0460720a0205070320142e8000310121647d5130142810401210728040d06250036421050345e96861800190380c0380c43e1488a806d0540070f85a614040c1405900b85040e0443e01d40c001203260100c80d942801801d420811421080c06081d04041c1c0d1203480b00d09611004080c2c5d801c0c0021140140140100050788421080030f44a852030429202c540700c84d0550341c403141240c500305181c003603882c2500c2521504c3d5001081340b13003903a085684481c0200064002501d02d4414800000300280b0a01c0361010f25241c81000982c035075064000e4249045140786000d4801d400c20507246825981c0050071071018207091509a58480782c84c00c09a004140c1c401c83e40d0310720080ca024940522a003407000700222036a440c0050903500c50480c10507260030040d20024526004c071031042201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328422266 1250 328421016 328421047
    0x403030f0201020c030403110925050a020c0a030b060a08060c090915130c11060408070b0606040f060804030917060106050a090906121a07050901051605031314060f 72
    0x90803140001860808060195881e540041d8000c41c2c0500546208400e2414150034503034108000042c60004110012980b04e409460301034007804101c2c0209800318007178801c01601e00007450203000c014656445c0c0c1040200228205c0740c0c0c40c002c401c207070400036948000049052007180702040703403414880000c0401000300806800036800c0b1941d14003c1c0c0c07039603413068540c2c0356001d405200001c10158003003001e0311924846c0306091480c1c0080b0100400b0940740070031101c20680c00300f205026965990001140d900441c0c00c101403070080300030041262500003030514000d0b8025103d482401340c5d19022842c40c500381c0c503602081500000700400216000c0c1001c0d125003c02b0b404c0240340c040c0c1700e807144022038440e40e2040c200707103000420070014040c1600321146034500c021001c240c9031516600180c40c6100fa0010681002000a0b44208020091601c1e81c042c0ea805810740e41e80700b40e00e00d0300c0240e406041c01150002001e0921040c8a454420103e4950103a0301604909042c07400090440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328423516 1250 328422266 328422287
    0x6050f0403050904151710271205070c0f1d060d0f02013b04020a050406080c091c060b0406061b0c0b03180601090b01051818131a060105040303 63
    0x18010191800704081c155000286d00300c05d4500c0092601034440c21111302581e03900c5222604003a805034002e4903042d1414040a01d883e000380811081040712072080720320f481254405400e602d018a00400c028503014403c0f0200d03070b40203212007808907140305018000d1105031f0329150f00800c410422000600c8001c2d80001c02401410224035041d03500004801d541082d200f0303295901f0381c100c44c0c0c14020040b220000e20594080d90210300300f01001001400b58415030003400188041440003da168020408031038000c0c60140508007a401007224001441814010407900142040c2111480d41018460001120f07031542d1070301c3c40cad010400701141949288140035035400d844240049110a84400254003908840045503060b600030412142000f0068100541103410f201c00c848141e80c0c46829103416041c0420302001620f80100050a44071904c0c0785003c00603655020056060840c49080600e180240384624a10070310540c1440090b400300e811501040c8244028400720303210700c070b8094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328424766 1250 328423516 328423541
    0x80c18010c02090901092108070507050c03100f180305030601030b0303120c040513050f0105040f090203100204050307091b030c0212030a0c030b0f0d0b102106050f0403050904 77
    0x30180080c035004556104001c03128403241d80c0d1115420306c1004020b07600c030316401c0d102c5149007040e04203180f002402600c0140c581c01c100000803070b0103424014240012641c03800010b00300c850309075078600c1c1e42d0080d2080c0010402074130314100318151144d03007204401700d8056041c0d50352484c599a990052d002421301840180d0548018001c803540003100c04030a50090550045440c2c5844c40c0c40c0810981d6511425990002d038100307010f04c4441409600d1080c15100112000304001840c1040103000740f40801019606104000345048108425401402611019800d030348030300b505c8d0304c0d45030140c4007094149401500070782d0700722a80c3c61182d03000f5840c20307000740305907580d03a5548100c1d040715030000c0d03644468030740c2d46400d0400059007502c01c8141036841918024443c40800340002c2d580400c241014080c80122400284601c807074080c1800a0902c640300144560544020255000c030700500468a5074900b01c041900790002c2c0f40202e10903036040c0e84084c41e181090b414030024014044403803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328426016 1250 328424766 328424777
    0x6050411090a2c04050307050d1d01050a120f0b1e1e0f090906090d0c051c0e0a0b070605071827020a02100c260c04030804030c0602070501080c1801 65
    0x1003d40020944400380110f02981c004c5464080c0d0341880c500708800c1c1112003013406138240c402840d20544070050150500d003400d109445840680d416038100385800062030b03103a0300c0c040561095211b41d903c1029010340c2038401c1141000c030071040d00c00700703481d400325260700103441c0410303501044480c1c3c15224182405052108620070b20340101d10712902c140c4441450750014410400340a4080084001c054642d241c4403040421a4480b02d880e80321b8000d94110425504174500707880c0c0e0155449d500400c01c080c5c144484255600f16540458014020445515003000046140340748100707240c10818680c0c11592008516103111b42003101310740404031591440400341d440c4844590310250420038400e402a040e04440121800c0c1295401c0c1d2109080c02200301668001c02581e107054400319480c0200c110032900d80045e8940d042c0543c1e407000b054481c0004011040202901c040021141aa0226840182c407400103455618044904880800d0f05220101021a42c162440302045060421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328427266 1250 328426016 328426079
    0x30e430b03040803041a04020a030b0603071a0406091409060d060f090602031801060b0d1a032b02070b0d051317181503010302150f0a0306050411090a 66
    0xc5030494004440a4031101c8012042100f800100c080b42503140c1450b00f20180c1038905940020400e0159000281082d0081000580ca50f00e080080801070044001e088010094440c07105d50780750f01078041c440004644840008030702c04c01030051403c0400080040c09950346203014410010701700070301662200c2d110190704402598a00c90780c1c1b40903024030b01c050395a02d406d00080606801c002d803a0506a803500d0740c1000300d1003c02007691585d914025005c100c46a2010403a440e40d00d51961207a494014180034140d184004505540140d40424403451100d00315070090380c0b0dc09030352060072a100c00410011200c41810b030b000b01d91000c02008860b2040c00191140c40c0c191100300d040c15220100001c5200514036000c4820041400445900401d03072810520038040d400188802030040e03030410014814110f100041d50759444640620940303910f4420b00082c05850584a44d5006516081c0461644000c4004403a4558000b0300f00c40c92207407414881c0160440c00340041b40440120501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328428516 1250 328427266 328427279
    0x1a0309100c02030910110a0605060a091a010318030507080a03062d050d02130c020c03030a09050405010b0702030303150114070f06150807090207170a030e43 69
    0x12911801c1a40e402140c9900c00e241c140300300800c420013160144258010010001c2000049109080ea80100041601d8843c800451036400d29904094209130030b09072172540b412402c011802451109a8003400085414088074100e10038142c805400250100316030f10203d800900100f05c4101a45000114142d42d140601c1011401440083c6640c0007440200100250070301050090300d1308845000120f0302c95070010350a014034010202c1c1168a840d4040c4e005802032002401004002e000e9990b41c0181c00001000c40145001f12791140f40340100210304440384000756500240c0c040c0041d403460702c0c1c5881982800c044002883d040207158103580802440001c017803d9802c1c4a154400c0481083d89440400d840d40c00000c1e4542c003004241c2044001030015060084607044c0000581d1101c07681071001c15940071166010031000c0003d00300c81c8440d4107510180d141404501a9032451507445c41c0405031222140b08d50081800c203400202100380e0440203901d044691420040340749070b03146c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328429766 1250 328428516 328428521
    0xc060f0618071e02010c120b031204060507140105130803150a0f080601120201050a050f0409061d0f040305041e0302030607020d11070501050304060b010c02030708010e010b03071a030910 82
    0x21402c00018441c45440000301d414003040d04940d000d640005e1140520100004100e541c09031641c86044d034582e003c00c1c9032a1003c0c01719841d810240480e07559525160300010f07103503030b0001208a50801c01d28014248400c0103108240c082c0c00310341007140c034804c8141c5681c40c0a80028209028a11025009a2131a0b848540183c0100500c940e41301c522480c181c0d48034146070f0160b119040001d12440410010b03a40300e03048a00f104080e0809c10317220308401c0b44c07041450299411800982d45461008107070352001455500843c001034124013160344e40c6c03500400f4014400c0d45d00030041241400203000382141c120700c9041c0742c0d43c02c2005240c0300d035503900004d14002e402c0d90441c016030021203101403400c1e407007120b0210b81001d80000b0300c030140ca0b00700000d25a00c802400a010103641c2c2904074201c1e0b20171108036008540040440c2d40182d158400d80d4002c0624820b494455881c104a14140341030204000d0225840c030420501051200d0640f05880c0c3e000800c2036195000c1e260403941041c2951 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328431016 1250 328429766 328429771
    0x1021204050615030f0705090405030409090317070e150903240106020601080a03020703081c150603060909110405041110090f0501080c03060409261e0c060f0618 71
    0xc00c01065141082501c0784041c0103038550f202d010350800c4071041150440045d0f240200c60702a0b0f481041c1e41d641f410b1490440c0690b4102410007401c0443d40c0c0b06055004111a1020303011080b054400e4a43e45c1c0c01ba42e02c603010520294003d0050410b103541e111044024003c0908042c094510344981d411003520f5950501828a2040c6c80c04030060003800e904022450251020b80002d0001030410b49010b59a07030b500b0f1000508400300021804800a5100e01c1040d004603231503014002803441100b03014007039059001f5500001e241940c001070001083c09a540e28581001040701c0c40700d0000103200140400078401c0c0d1380003e44410040c80c13500c031070b4509642682140c1d140c404603030508502d44c80000c1c465004904100c0c0380f10520070804044021290441e0044400180501d6245020301401c00d0400d68481e00c0e035006c0d100e0302c41d0146540c008044550401c9a500c80444c0138031545c107494090030788075418a0340150005400000c0c00d40c040740d00024010402c0c4561216031100d00407501c400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328432266 1250 328431016 328431023
    0x604080706361419060b0301060e0c0706110a02060f0702031611240703090801020304020a060c020f03060903120610051e04091503060f09050d0e0103060b0d02090a0b040509070e0301021204 83
    0x1840d2130b0403d002092003040082d58044009120b12807801c17100070100342d00a400080d104000142c0305003088516444020a588070a0065884a1a081010b5210481180c003003a80b030301c1d00300000710060310200407503030b034140c91040014540d009912011a408241411241c1250b036403e40400d041c015806480b91000f1398644c107954514041c030380100880300c2c5910510841e801403007032000507034070440c100b82501c04515010420200c0c0e4000a01d074220b108030460b8160040e5810320042d204080001e1400c0000d00f540940305071941420310400d40c0e4225004400520180305010001080a0b034203141c44442510385c40c103081d1a00451000c4600000500c00c0d840c550007420010010a40280160b00008000401450300a901c9458035843c0501c0c2c202d04010110080d014140c1c001d500841c0541000400162546040311481009620030542c2600c01c5081c83c40019588070600101c81c15500007401d0300405840c1c000040da04c00c600c0c2512194103540900585e217140401401e441d129601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328433516 1250 328432266 328432303
    0x1140a02310303110604030818030712090f060c0c0e06010c0503190f0806151b010e010603110a0305070501080a060e0a0f0608070605070b0601020f06040807063614 72
    0x15501d0041c2c040760040311300c102c940d00210208408290051035261707004c11090040c0e01c240641d11081400c52046000052124031a1011860b403141d0046c00403040d51a5101445111500c0d004152816207241c1c40080c8084040d10341801580c0c03003407280700e81100d810304140c810700700c080d560070382103801c0201021400340c69010100705c890340c0041e007522030700c4440c285251181440c01c0031458216003078018120f250b030001032450468044400102e86060010000c00c0702c1e220324503d13280178002e68482900d22001035640d046107441d1007143c11080303a50020040080d6840c2030010340c1c1d034003001000d00c105580d96501c00100c0d000c1c49400e00340320354840d034070005001022185010441d5040e802410241e44441070074002150000100c40391640c122402c40101c0c4e4414004034604520722041c004603014003410321042041a60182c070505115540a0019210313282d0311950304d0420400f040b540d44c48069840022000e00c50602c00d6550184228103804842054002e15001081081011039407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328434766 1250 328433516 328433519
    0x9171e030105010c060506010207120f110306190b0d0606180c0e01020316291608101203020109050303010b0405031015180e0709020c0c0301140a0231 66
    0x104480400412581122400d41d414000003c0c4511401c0a00815442d6104c020481350ba00070020305000b000c2c0d04580b00611011491b101d0350000c00028111401e511407560b11009290105a1511800302c040f990019140a540000068440c50402d16084a4100058004a11740c1e01410002c1c2c518217000c20000924480c8078400c07580705400c00300070041c003880304030b1032680c2c04802c03504040300b040a010012403050904891035032030759142c81400071500c1810765074003c00b81103c511800214000c0303031000903801001e803131354501201c1100400f2001d100074469820008002d500044c002c5c1700000d1000140c4d50761300d1075540280c1000214440115080095140c1000140300030408168103004002c130b4094a40b0301d404103805045141138107081301040010480c0d01440845d04c102c0308891100d0f980b001514000c0d402020380311414052038103581d00d28103050040c21081004d40071001c1095031000e4605000b50005450101d400d00030045001c505154000c0c8180d0f2600040940013529 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328436016 1250 328434766 328434787
    0x8130312030c0e09190209010e131509020f030f04140f0705030c0406030b0c091203040b040306050c07030e13020403050f030c0105250318020402030a05040c080102040305030d020901030917 83
    0x9006181c807840b458448040140500e0804c0c0030104640c80444056220340c2047c005035a2248003a22a6401a110030510550000300e03812000d1420301e80080501202e032650717140410391146e41010a80c80c0c404001088411524040e00f40d84030340900190a0740e0a0300e8044541400340b0b50b0401442c2c0d41c001e00317083c0110300d402d00400980e0007046408000c2245169905170860000909a0301007040200300400503849184040d00007803241020b4a541d642c07641c00b8141560028001070740d00030702e8000001d00059042d02152402c6070903844804030032441d40d04000000c0424803e00b400240c0038040000000c0c0704010742190b480d0200c010f5903d0708540c1c0e07401800c40d0001030021070740203105c0d20b99030f65000701c5003110100200b103407070080380301140090300381050340f82c051009402c00d10000800c81c05028a90040380100e20030100d00f04a5980d5140440c00d0b4050ba0002520035001040107400012040d03000f0710305c050041c10302243d01881900c40306600b0b00400207100b41c0c3c1d240003850704d00c0c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328437266 1250 328436016 328436027
    0x110f18061f020a02090603160807060305070302040308221e081b090403111509010b1f0203040e041104020a050309010b100503010509040302010f02180114070f08130312030c 76
    0x1403041c1000e040586411000095981da11444080e004203019004101e00ba2070a200e22500c04500e010702c044201d82d81d13a450740c0d90310518425580084e2030400880c040030312034000c580071240c002c254141007070240504240c8000c010703490044c4201040c00005a4450300043c480310411000745003004240c5021141420908810f0030f140720f011180700301042030303070310b0320708403904960189081214140d9034264149000d100310341c201d5010940c1d03003c104007501c0c150008010140c0503034a61a00c42d00406d0b450202c2c48030746448002503082880144211261403500a81c010300a281507507080d070303048000c90203e901c14100036001480c00010400b4401d0240a051000c48080e54200400710b101c40c002485408107001d01c9101382c1c0504081018103200f50050f6510309401a41156281190000307044515082c0701010301181104040180e00800e031400c0e100c0311a0440910005500710b40e4522445510200102c03003001c41500c404400700300b40803401d41504400d520005000310508001910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328438516 1250 328437266 328437289
    0x30705120c13020309030708070501020c070f0501021005070909181a2e0b0a0323070f020f10020702010207091103060405011401020a0305090102011103160306050d0f110f1806 77
    0x102d600420030310180400020480c0c0c001c40d00188080d482c0c10743c920f4a240640701d00614540c10744200c2d07002042c400c2080041c40c040354026000c0303910800e41102031000b510000c440100104541400800c4a80741540203240c000344081040d203203800903a80d501c00108541a0306e4030b50315841c8004c20500c40241c40081301c601c8200207008055550131004c41c0345403501401040d0a0380030100750514018080e800100340c540241040d8441b01c0c1c450700d140d030b01004080720340000041c000c0713503507002e0240003141e481031038140c01020304aa40300c4549210080e5106403c224114402d402c00042e502c4450300c00c0c0041e44805071450f0ba0380303003888020801500c0d010303040498403800704284000c10786e0300056811050340c0c1c54140241c4442c01100181d0041500702000a0141400420410f2008103942002c031015210380f01006501e40754401d00480030754043d80181440d11110040010a95140705142c08580013040881c40d402d490700070540e00d5035507003800c1000d912203c090100510700300e45401d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328439766 1250 328438516 328438549
    0x9051809010509070305070b07020f0907020c150a02211309090c3c090603150c0224041506031208060103151206020c060916050a060f0e030705120c 65
    0x702c407500b176880c2c503a250b500c0c502c900f0480e5240091315004649845401c075800e141d00910280003447d18210182d1281c2c18008240d100c0c0540d00c11a80c00503241d07405503942c01629078010000140703a600015001c2600c60000ea903003840602072610703d0a4584c90400203001d0701c8101088034012442e2003100c14a82d604804d04443c04407070540c11003202d400b41c05464a4103400e00d144502c140600c0b01c86080929081200118100b04012050144034800e0405009030180d0801c80c4e4842036070200c2e2909400000b030002410b061070030300e000c03e03d02404183c01600500081c0b41d0300b52048041c0c001c646c0e80e640200d40c41c4c07c0d010240c00701f44e031f040920940c0c810003e0a0170701282070490600841862140146005604420600d609004407a415504e841c80120122002400d042031170565401008802c003000c002c4e441e2021072203040c43c451b84012104186c4641c040500e02c0c0b01d095895822040c151900751280b031314005400e0f503503241d03081040307016a4050300305a6654428003c10b1503590310400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328441016 1250 328439766 328439773
    0xc03281b023a1d0402042c090c060c0304150906030e010b150d06030803040b06151e160b010f060e0a05030c06071b23010f020604030f09051809010509 66
    0x20002c4448140200401d00040d103000b14100f1000424030710589600c0c45040c0e0054404140130444900e016940402403002101454550306020390144641c0d10890343c08030282c005401460903410000058142c00000341c042d80d04080e22100022071f41350881ca0520001124000d040141641521600e00c000c541d0100070302c0225066004101c0d40028441c0720f001079013000070140d00580c00d41d4001405507600012550340c0303050a04000c461018103a07405032064010301c88100388064480c04684080000741c0d2040c1503d0016050001290006100e0100c1c0079855500800000e8845030301c9401380c680c41601106080c1088001041c2c0d0001401d1580295041c80003405651f03130025106015840440e030340c03039684019107031140c00e48100c0d0318400b035601f0811002013160710001d0071041030300b5481d200d45800c05c0401c0004450480d1450002c402682140002c18007080c0325541c842420406401c01501a0f90740d100410014980c070303044005151090018058905420700071103801c0340040004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328442266 1250 328441016 328441093
    0x3060a030b060409050615120304140d060612030c0b010611031e0f0a0c02040f0506060909060f0d0318080604050706050a02010b180a050c03281b02 65
    0x81040008a40000341c4012010000500b103581c0700d4104400d001c1e032000568406082448008040754600340807a4032030300c101d100708000010008292401c8505ca020000d0300c000d1010244100542c0822041d625191141400301340c2205580748103800ca8442ea49100750000349080c592804901a00184200508003c0b250300c100c00003c1915090103204000011400c41114001110b1041c0345503d400100d0100da4840c3d42e581001c0051550390080c1e81c240811043c4100c083c0403100f0031100c9551200091043c0015814064007140e170001014054410b041d00c00d200240d110380b1101e100300d000608890500c54091800c682400061412400030665814a56501030321840c2034055402008000702d03074005034510035041101c000d031002d40061500c1102a8981c0e10006003200c64440c07480c10140416941a42d140842e8403642e0110402c81400c814a0020b0000c43c11440c200800c06454104840b015070640c030032440900d009030010280920115048202c44034a03105101c040d4824884 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328443516 1250 328442266 328442269
    0x100506040f1406040503060f0a05090d0c0305070212031b01060b0c0a150908040306020703021b060406050a03020d0509060f07020109020907080402030f061f08031e1303150207170306 80
    0x15070341c06840045104512416900300814080c0c0119030190b0740c548507107020300400c8424840fa0600404a1141c02d0200d0742d034241034182c1d54680480c51000042620801c8400700f0300c10740c05080d0051008200c120441c0c40805102e00d0f503000001c0c0640e039000c0d610f0a070018241c0c01d11038403005000140391a81407140c0409403544031091000301900c1046101d2541007025580d0f03000d40059131303001c3c090f56215510707810304174000e4000c540100d01511400150301c0720042d0f28214000713510001020395140034200f1504581680124100c001810740a100c11080a2424040c0328890b410440080125280c034010350a4102c4001d4424010f40e450301f0300003c05600d1360042103510040c10300b0104916142c52003c00e103410520011407840d402210180400090b81a0300700e003003400040711200c0c40e0758807000d14a45078890802c1688034541d1400c41d021101c1c6818014214840401f800c619403d513882d203c9a50f91002c5190031280c10754002083c600700600745c4214400ca580c0c84200c2170561410340c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328444766 1250 328443516 328443539
    0x4090c1809020313050a0609060b0315040303020c0f030c100606141801090305010903020d020c0312310314060c040315050a0f06170706081605070302070905090610050604 75
    0x481c0710268001000a010803079a010f07203940c1982c04411520300d1091428000014515840c04407421402d004400e00c07586000907403921190208200d140203504c40303680030b400941c40044a400c1074018010200384000003440600881c070380c00d40103420114050082e001c00c0f03d046400000070f1241c82c411402c418030009064804010140340542d024a0701500140e0b01e0740c9103a84010302d5507003407051080405502140c19928450fa58007160322090b4001e041507110002d2882172109214284100401c2500700c036403c900118072084159551004425041d074030700d943d03030403e03594920310215804003031070b00b0490755031b02c00e014404403810301c2e0550f5643d01d4240c100c2c84040032505d0302c0f0b0000c180e02c1516a44442d9940703003044010840703a5134601582c0c649004002c0410b81c0c500580c140003440350b0144900c68482c10642d0264446641e2840c800c0d00c0039000b0b040c05a003140302d0100c000c280c1c8101c6100310744c0240c2c4130710020f04607450b00f15264038182c102c5070002d6000340d4040c0000c0142800a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328446016 1250 328444766 328444769
    0x60810060e0c1b01110301120501051008030d05060409080313050c01080114010c11090a090204060b030708040f240b09070f1e0c0203010c0c02011b0c12081e04090c18 73
    0x400ba50a500710100f422a0251928140c8940c130760100000005e948403507505d482c65401d12031f8000744442d50f0742c1d0382e4584800005206002e01600104039900d940b411551103190700900c01000001c00c0061500e0b020700c0c1350802c4842e00f0321250050103103803c0c40710821805425242c00d01e0714444542c1881d02c014009124540e083d4113102d080e982603001c110f8001d80c0707a059441c014140d40e0075132800b40b030b070350026044030101680940e242c10004120301810f0000c036480f8213056125171546403215600c6940705001c0c88000d40e10201e0003002d0385440448601e84442d00c41031400c010030700881070801c120b44201d02034074810a100790708413016416500040e201c4459581c01480b00500045244199881122603900035819417078104200741c42030b040308102120f98000c1e40c440c0c100c2c1000f4821a003034000382d06000303020500ba44008010101881e0003040826106411442c100b04500c01e86458040c000190a003080030049000d00c040d000d41e2042c844505031074a488003120395000c0c100c04010415 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328447266 1250 328446016 328446037
    0x24031218040f020409180209180a14031905070c15020c040914011808090f0105090303030a0504050c0604031a04080403120f0e04022a10060810060e0c 66
    0x42080e041990108003005802032026000b0700c04203030a20500d40081d84240522800285010040742c00751100e0480d0085460b4080d005403066110b07100ca0081c102860800c2e001d0320702c160400e400c00611924a40c2210280c444001c42d1038100c0080f03040c2101900074051001c1050a11900011a4130040c120084458400308103a2000489008a0514030042c68031074100c1e081014040c01c22940c20001448200b4140c020803000501201401c00d030b580b88400640000011710100f4624075040d914250b80010504005180c41c800d400800d084cd001100d14a10703c81e0398108100901c501406043d00c3c00104503821403401c4d0566480d03034a25560189a50503052078840041c04108400301114040c43d0041051000c0403001c080003030126000d118000d0008000c51140c0c440c0741070900030b94081d940c40c080301554504105250310304c019a5202ca9899520942403a07420305851480350720042c01c104409480008a09101c54054581c1075108d0781c5111400d108215040f0758000a45900219 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328448516 1250 328447266 328447303
    0x20403110f0105181507051c090323151806011e030b0405030706060b0301090f0c0801060e130501060e01020f03030403080f04050a0b10093e160303052403 68
    0x3e43d5000c56440170040e58191942040010301c0801d001c0e000400c480d45100381103070f0210425a26070304882c10000351200502c1103c01d08841d0b4918001c802d5403000328400c050072121201e5003920501100d90056815038410f0036106421586214144a01805841c1c00442c5090300c0003403000c0550903081500c009429110280f011404214050044449042e00003100b48a207a40b2030a5071080c03503000703124890701c0c107141042d04c00f0b070040e0324000c80588072413980b58400036a02e003090070346814402605141c0c0c410718908030410003980c2c1f03110b90340c0603022941d100d031100180359001a203000a50608119194030a004000009a02c03280d11603101070061040306182d1110301c0c3c09443e01c000113030010450300791001044050f4040001140c07c640011030240300302400c204e171480040c0c00c0220340318a43d0780700c010700e1701140e00d014080440280b80300381524a0b00c1c5024000c0755000c4c3d20352000b00c1c002a10740d000c0c098500d588400c119000065902000c1c0e012901c500081c3d901c81a500018282d400d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328449766 1250 328448516 328448557
    0x5130903050903062706040305030c0c01021902030a09050a03050a11011412040c0501051908180102130e09281a130b150102030301120c18020403110f0105 68
    0x6100c0d01c107407400c0b42005001c81d8280d05001c0922840011000300380170b40042d010420f240303003000010341c0305c1c06076030161211840c54031030100704030181d401170100c00c41300e40d0201704c80ba001044154681e205840c155000d16100e1510103002028000c2681c8090311900010700144003041012540d0341030150712603840d00100e900c030030046c6e440c400e200751240204100410000a400030103245244100d1040c40c030f1600040e00e41005440030b0142c200340a4603000a20784124015000c2c1803102d80150940c80240c0110b0340303500300340e42603902c520036049140043c2002000722101c0425500d400200c0700015142c05021a14914480b0418404014030b800382a0101c2d818841d09030301201c20b980aa00b00340b200d030305c0d003085000002880780c90704549400d03000001070700d644540062400121310590103145140d00c0c1c541c0d460518560f91406842d6034550300d000150580890403d5090003c0725140035880d80d103036041c0602100c550a150500038a184858035860742c0e444030445100010030310002409070f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328451016 1250 328449766 328449773
    0x1107030c0b0a1404080a020102210306010309110d050309040606030b0d0803060a03060501081e0303090d0804021f0216050603060901050d060f0c030b040b04091110030e0a08090108060a051309 84
    0x703603e80701101c802c800a40803485c00ba001c55400d174080d0007a001c45c5c09218090804411030131380341c041d5a8171040c05102081e801d62081d080070118074010200c180e42044018002483c1303061120303049810784d00000f801140c60601d0300443d0300a00240c20308101018580020900c81c601070b1354020400680080014081d590712440c1c1e00c00b1b59001a001c0100b076171507052250b65800c41d40c0c6004942c40c2c0c00410400c0c03400d4004200da10030482403000d00114100c07000309450303010303001d44100e81c03000380000c110100420881d605c900106040c0e00414054070018548107415250380c010a00401c8100200541500c071452078034119002510780444c0100c60742003110040c1042d95080d031010341000141344580d507058011000c10001198108105907421041004842c8203c40c02490090043e034007481d94035060555012000342801d0201d1528030720b0303030058201064840112120b01c8041040f100b035503404554581c1c040402d42e1411102410480021741c10304440c0440140c66440b5010b10040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328452266 1250 328451016 328451027
    0xa08030c0403050114010504150506090d050f010e0607090b1e0901020a0b0f151f0507020a081c080c0a120b03030c0105040b0a110319200a0206071107030c0b0a 70
    0x31070f0440c0003003061001200c4548484031081c810300d0300c13503070030001c440c65100ea044201c80119000141120314000c205000d00c8403c01e02204140c820740245482c0c244100400e000da0400c04502034090100c601c5e001c9400f401c4980940c1210381145c2e01404043c00c04040415204a01140010519142c055120040389009141d40c1300500c00c0300560140261001c01500c454050500d21440b103c1802c1c10400303200c0f079501c013010410642980d01c40520308060050700180501d600280443c8682d503119030446160009444096402e02c00003111100410703882440a900980b8000300545418424040241000119000300c0c0180703a480701105003940e420400c03142071807000c8000b8031184c80c0c9810305001641080760141c10060030b0820806a0402c4442228456250142980003098054030004020648000500500c0240a1070504000e00301800350038114810380c01403000c0d181c8404000e012076100700c030b0403680750300c400f00c14800100c6100604054500c40240365450380d90701d0000721b44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328453516 1250 328452266 328452269
    0x101b081b0415080604050a020a0512100503070b0409050f0103120f0504171e010501120308040804091103161803140102040506040f0618060815150310061d030a08030c04 74
    0x8201914010711000d540103c00700b441554101c2c0c04001c2543c4c0c04214000340c0c468000d20314009582084110410049940260380120f440c409030540d96455802291800215400c4220301c1f06001ca800c11400801c0d00034941e004d0320000c43c610165145a8800e041542e4140200003400f1242070402c01080c8140191030042c507003a900c0e2003440020b0240d1750b48a54243e4400b04069161811000c29454140560360407602c4075000e80070601200e0701d040f00d070f580014004544c002c00800001803041114003843c140486e41150302662400c00c0b00070340d04055595011030042c03180800400c002089081c0c6e0300f0080300d40044401084070098cc21301d07402441a5080a0380c4924046400706054010011303e078151030031625800004402802d002d8140304403403227007100050050b0b00080010200a10381204048003174520012500403400058172900200c6480440c0b0f08081000c0220f654011001c0c038640d0049038110b40d030054880013082c0c48102c1800050b0103258000003040d000700341b4034100c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328454766 1250 328453516 328453529
    0x405130b0a1508100b25050703060209180106140903011b110607050f04050d02010309020d21050301140603100b0c0a060501050303091e041d101b081b04 67
    0x200708030386850603044450b400d218914001400c0400003841c050f07203101080141d850007030f082428034107a1540e00c600120f0028041507107081c0802c462000032003c000004c0998840e40000d42c07203540c25420311a0451409081075000d0545a0040100903040302014042c030300d008407802e95a00b48080440e0240105c805900076014483c0102600640d1028003280e175100c81c0d8081d0340c05030712040700803161409001180e0048a104000c10491032404840d0341c04030b907106050200d000009500000c0350340084400550b41003e9240e1103000d40e014450042443d004103042c014115418044510900c1121080044c059007000002c80c0c485200d001030b40c0010412042c00d1562000e140745070a843d1240200200c40c85407d00002050b545004820f032494200e0180c01200c0240c0304c20b410318007240820007896049551342d403821103240d55000d0304081c40e824030700c020105c4604840c4e50508560681e50b454030b809550121800131a80d1203590260403410300c40c003050303071503006514082962003150b1221 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328456016 1250 328454766 328454779
    0x20f0c15011401050307090b070f05100e10091505060f030d02010e19020306042307120c090c0512040309090903020a0c0b0a050a1b020a030f0b0a02040b0405130b 71
    0xa854046510180364103039020480b050800c1040000156018001036409802080509005001c000005005041424040d07800d00b0707281c00c0c2940310281050204400000e28a881355400c00320004104130a55a01040c1c000801c40040c00341c03a14003081e080701000700300c3d06407180d002c1383ca107035500c00b00c228244070020f0a0f50f0b5080d01041c2e029000304440020b001d4907004107950b01945c40911040c01240c00e0b00a00a0710362540c6981e1106010742200c807994007641c480a290440490301008400080c284040714141c8900032424a06008501c1c1d500c101c14280c10089a414403650210545041c03151b05024001d403503c413840d042d0342c21001908a07094452900490310103040d800070308440041e010324004e100243c3c07500700d8000c682c89400000300200702c0c20406103040603c580c095a8010705c0203260341258426a0340001c02c8001c0c03903401559000005d061241c240200340344403541094500b00e0031440e0902c0c0601011050080e8410107104403650102171403801d04c3c50300080700540008010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328457266 1250 328456016 328456033
    0x4050604180b220e01091b080f0d021c05070f210c111e060a080103050d030515011b060f06260601120201121a0f010314010306020f0c 59
    0x88050200080c000401e070386003000c61448070303420a954400070aa00096504642e1601c040c0d989000c1e103c84030000c6007640d0b9034031481000c10002584c0c8a510b0b55100c0f1490031103403030031070301070300d03044100345000c509800c07803403001c61080d4001a68012905607000c0d008040c0440003000d650340e000f40d400240c00b0003903642011003005a9089000020316150b520b00400c0b002c0240101d5503a00b00104c020001440c03081d007120207281c22180c444da0950f0106d0b05901901c100e44c003060042d0803450b09400420360040c01402040340c03d229444d00340f40c1603d002c122502c0c1c05c7d10f4801c7c0710310050600c0e605006d1640380c509009820f00d48602e103025040b280c188a031030101180d680040a96101c4c0e0303605118070b050b140800012484000c41c42d8072025008010990900c0e02c0c80e05452403a1004a06011201f10124500350990145e040340340c031030501c4c0164a0340814207100caa040399083c07030f5040500c0e0104034210a50108005070561781c12041c0141c941e400304008194510903910580301d10320a040780b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328458516 1250 328457266 328457279
    0x20f182d220605360a0803090703060608101b0203030f07140c0a030e0d032a050f06060406050a030b04031103040506040e010f0f2303120d0b01112404060204050604 72
    0x11203180b00345400074440d0f01300d521000d02d0f410785060310021300640d030848010300011600d06405990442e41100584c1c0806640765a6541103502e15031000e41540c2110111000b00e17001441000342c03802c0c41011b14486ca20078004000e4403840000c10600d09034441402050605102d500c8060407040314404299843c41440700702e955801c1c003024128002000d420005081c0c0c145075a900b004a941600d400034803400a000310030340d141800300000040c3d481130f4038178008100c041000d103001c405554054005070422109000660306660006801a400c6010410000c0e1207101c907140d12540500e404042034440201c140d0451080344e100d00c0c1c0c0708401007000324225000c0c01500381210740c00320341c3d401c8155444c001b00341244d00303521540800301c03802180c40c24144400c1d416003c0c1450010150b50410707600c2e000c07039540f0307410402c840c0c9207681c0e460100d0940303560001c1105c400d0400b51070003401c113012009030911a80c1d201408c4045030400e10008602084081d4042d50041c1200410075910b8030344442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328459766 1250 328458516 328458541
    0x7020901032a1212051303110303090a0303170105030c0d020609010311041508060f0d0b0c16080a0818071202030309030609010510090213060507020f182d220605 71
    0x100c054502c0c1c2c0540f09284e083d68014030881e0000d0807440d802c2e611403469900d23044000c04014440c83d07054041007003000029556450030b02c015500c29203d84040c5099110020545078051b00040d000380d025940d0000c036a41c030320007411510342e4100c1c1c00c0c90341c0b400c2c6140102c020300400d4402d1b081148000c180403803501c030552426401019250748141305595540108074406085044258010140040003004103a40040c031a5005005044091400c21401c9010f089142085000d4900d541c0104140d070205900c000c03110b40040408203104a2038201d500100d0710b4040b54030810b03070b00c294140d50700411510244252201c981004003521094540358050501806080790b206007100454a0003140408442c0700f43c1e0a1501d500c88600620b0341085020766182d072240109036400a0b020305c00302856541d40c8421030b010601c401d007441d051305145c0e0442080300003455401032900f41d403140e509030000c190500075900212907088990380081c0202401800c204186010700f03843e040c00100030401241e43d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 328461016 1250 328459766 328459799
    0x1e040608010b010f02070e01030210091a1b060f0a05070201060b070c0611060906041101090306090c09060b0f030a0b04091b0e060405240307080d08100b07020901032a 73
    0x1c4e2a5003030080381d0540300700c0e11114980200c8502c80413000050025041102c3e80c1c21280b0300c0c41c1444c1b4021b546415a4840044013416200c02d081ca0000f004101c4104450107100c80103800c0000b0500c90800d101d81540390600103116110465503000042e4255100350031140080c540090b12a65422541c00d108440500700d001c0c15003c140c0301e410000d002580050705a20554001024181c552150f681d010f0701040c510401d581041644640071012031f41c0b51103210980d13845003142c1c100b42882c204080050300c1090f40182110303501840084c02c00c0b0240360131aa4003d10042000916902c1100014000d040041001d030400c02406c1007050886040043e90b01501c40a00a0b800540d40381810882a55030484502901c1c8003060744548480c6206546800e55010040540fa1281e841d940b2a500d01703600801000000f4842005000c1292404044c80000d81140c113800b5103085840d8002c0b40c0c100d40306200007040040c6414202511041200103051181c04240485020b00d680d0454140c0c1c800d1003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 328462266 1250 328461016 328461019
    0x4030606051f2a12020d23040302040f0212010803030f0c0f07030e0d17040e010801090203060601050a050706050c0919060e010c0f05030d2f07021e040608010b 70
    0x342c4010307421241c541c000240590240d89000310a40242c0004202036941c4800d581110040031003034001901244030070f040688164000c003907462090000074034003030f10005c241075441c4a68404e14420110701d401c40d02039030f07019140815040c182031540f00013842003516284181c003d10b400803480f28400300056004a006848424854441144004580c8034800c1c0004101c20104102d00020340114410350070303203000030001d800d41001611004059604031498032031012000900b031141ca440b044010303002d0b01030b14000300240d0001d50b0110b55141809400039051001c085540386841d4030603400c40343d0940c0d00c04014009410215840c0510f40c201c8005039118001c0d0701d91a10030482c1c0440c1980888842e80d40e9402c041e400f0300300560707004001d403030241c410725440c001203008624100000c004449044c140000e408469200302042c0c1e0340200450102403043d0510041c603c40ca80042c1c0e030f4043c1d0116080c00d9001c1c2d02560383d08100e00c08103030042e0000d0600e800000c40500641c0464140c400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 328463516 1250 328462266 328462279
    0x312010801050f161205090715180605030619030605040c09050402090601050c0109050a11010e0a0f051905040e06040c0b12010b16020a1202031b1c0510020403060605 73
    0x880300001402e071081150181002d40a00e0001101c0d06500e01100810300f2581c200000381c00703001c0c2c40c458240e83d02210800403aa120100c20000d010340c801e0034100400151070204003411408440c9188a081403050508004021012034142e6842190b00005002d80212505006580340b80203c00b51500319025500f000389804006142c0d030075401440e00c182c1d402800e02c41e069460340015a0103130095440d00400390340c3c4500000001d2010400740103494052912082412486d400041052040146043c060507480f00c04001c48040c9070780050a4945c21680b07400c0d201d241030f0b0340f50b40c0e020603580f00fa98418100040c00111101c08a50785010314000c0456828040d16440d00c0a028407035550802e0500a2103001001a100b19201808480382040240c0d0b8580d8145c1d00018040034a6800c25210071186075812011841c1c20004040450b10300e20707440d2603c0c404000000e5002c2a04503100a88145071450242044814410500e885107807180840d101ca0f12420040000e044c6806806d01070078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 328464766 1250 328463516 328463519
    0xf060117011503020f0d0320010207020a05040e060112030e0916030b010e060405060310080604080a0f030920010324050111150402012106180c140d1104090e031201 72
    0xa4030511244140d13a005003400b085030302c00105010201e68080c0068040000241c00f00519002040300e081d2641405c100142e00d03205a801048480c10740c60b40582c0c443c42c501070401080980c042281c90464580e070205a80a0040d42015102d10002854981c1e000e5411b004100b017504001001903403031225640c08003ca074030320350015140400780501b0294003a500380010000c5151000007150301107100050750381c01e1503aa144052030300d0400d8908803421800441c0e03c0480c80e91200c03803c4195000c5240070f1004800c140c079120210003094031400001c01000c4d4150350583d001c2d4021401901190710b882100300304400e81c03d52103507080d0141c203000030b59410084490314400a08031005c0e07054042400400c1e11654015102e803100401d40c000010141030020f0b8590307005101d864020491400d2520116000b2a0450708494800268174241301d5108105808500c0e15070685210681560000500c40c0031540101f440d40941da0103041c4140c1007a1403ca80c48001001404084400407150261039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 328466016 1250 328464766 328464791
    0x207061506140c0307080d09020108072a0206070b0f0105030d08150d210906080c071a1911040f170c0103020f070b2a070203100203090f06011701 64
    0x66521a003400540030010381c2200b00032200003441d01c44001c40480389850041d0b5615846500311381903586646540d043e1a20035545c00410065010105140918480c0c89007180c000703184103560600d222980301e0300090005c640b105c0381202c8189400001c800c18034509610540f070300d0310703007405810700038022036007841c1020b0b00408189005405201d500c1038a800e034039007803112616482c642074a41d1008040c01e40001c490005c1a1006440d090340c840111505001c0c02602e29280a4100801c0040c01c005080105511000240f2400700c040c501c1e000c03035118074451000c14140200742c039401a14100c04141e00c80c008000a00403502503a0030004103a560304120f01915070101d06241c0c05811450301d46116601c258005d0244000030790310581400050384501060600840f9400004903842004407104c0300344a40a00303104020040686c5040216800300340c6400701c0103804a09290003001041c40c1ca1700078401300312002210000c4031060340c1d6883c0040c00c481541d001100255103442d4004621 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 328467266 1250 328466016 328466051
    0x290318100b01120c0512040606061b120305070e1c0209090c0a06080403051b0d030b030102030705040308030402031005040b0f010501080c2b06090f0608070e0f0a090213020706 77
    0x1504416119183e4801440b00c0d51800382590350410020041c0c01c001141500ba070010300f0300c0c09640203020009550341420400740c2040700a1104070b4100d41d00f12200000203402200ca416802c1e10b81c5030200300c41d02c6440003642c06420545165030f0020380c081641c0070412016200350804c90003114140c0d61a00c030901c4068845040366260b07900107484690500c901c1d4010010290824860303e0b29916044240000700d6880852403c00f0300f050300444c0880301130307a0741402201c0d0002e500706c00841c99800c00d030002615522403844024601d144c0880043c042d9074040c0002d0001030708201050007a80f03000c0c40d202a8208080740c001c09040851000480c155204643c40c0d4403449280101c0340c503254030380540440b056003401d02c54003c403011103030410812009000d45401494281804200c4900e0071511000762040341d000850300740c1c4482001c0108150703500309113800c041c60810005c202d8480b174402c0005441c050340040e410503090341c00068540401ea004081c0c0d14050541000408000c0e10402e46 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 328468516 1250 328467266 328467281
    0x309060608010b2706100e0603040309050102100c0813020301060b0301141810050609040209040e0d090905063303010303090302210a060b0102210a090e040c29031810 73
    0x180d03c4000340c0040d41a040c986c0300c282c2c2e07a0166080c04031050a003000001c0903036004840c1280015903e5008203c3c55804201840340640c00800c240b04412074860010034110004116504c0c040000303c900095440c20347c81003018140c011f20f010780d2982c5807005281c100d411560094060b0b078001501000e003205d003a1541d4000e109560202c2c0c031940c944401c01615400c40004968415420000c8605e030741c1d5548100011402800013411101071012006009900140d00203000203042c07a0800400f59a8444048000190b2141503a21241e03502c5020003000c103000400308030b00500200210074036070403160150840740308031900d5000e400d40c2040c035000c8265007024400c0640c082d03242d1100080e01e07a0031201c0c4410341031040f00d1303030002c0d80c000044001303458003000d4040f0700c0c0001701500722a0b80145183c024040740e00d0400d0040c00d141da2000c01808280c072466580c4060b0400078501c00c081c980e1b00b20420001440c4064590501c49500300c00d5884501a0414030304c01c002c25a60500c00e80d014891 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 328469766 1250 328468516 328468579
    0x60608061c02040507260604270807170a0c150e030711130c030504140105040305040911090d150c0e0109140a09020c0610060806060a0f0309060608010b 67
    0xa40700c056990a11029080c050180303010701c9040030002404131400320320b01c100c01a07512480321079418414140000c49881d041c442c01080031883d101451081c2d0815148002584041c1650340c84202d404c0c40f50700e51490303842c2c1c2030b01c000000685488841d03224001c0049180941d03400607003031090994120496a02d50b501848030b0b04244821808030b4194000079400010240a00d643c0704a03550500c2e04450906400d0740100356540305000034070142c0c0c945003002550f860020442400d05450242c090701961203451005501c0b07010742c1002050840658210100191501c802c1c405a85000718814010f220550a100d1800c1150340d03a40e840340003401406030042e1900c03542142040f000080c822500c3e00025009043e2490004000c0c28074070050101c0340008001c1e010f281840e2003c40c40b0204640d10060030001c440b030600c2115036441040342c80c10700d554100008505042103054000c4c0a481001812007442e0100001c0c000c0741c19000700c40400d904559040e68184998070b001c00343e048030213102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 328471016 1250 328469766 328469809
    0x70f050a120b0301090203060a09060b0d33090b040605070806060301060c050c060708070c0b0a080708090c030f1609020f040e1f0f05010306080a020f04050c041806060806 75
    0x1060302503040c0c0c001e208404020f030010070151690f80201c0d21f89503041c1c0e20041510303920b0803107205200b03162203949058142141c90110013402610744030900b0b164a0010f615922420440d8140b0040d501d41d14044445820424480080a820101c05080b001c69081d50307540d00f0180028806481803400794400c0400a00103070540e420100c04440159054404864a2103409030780000c41e9a40005044000c2c801c040183c0d03600d21030b2a20f014400459840703021501c009218001e4a5600b008201d64001c186241080c1c81e6941c40010600d8411124400c82c4c1500410343c0428014502142030480724480440c80b24030280c0d100c100038128400c1440300c0070482c109100900102c04407000a6411001e43d00d00c0c007940d800c4c200002a080800c2c0c0d40028104240b2500400c00c80d60103015140003404500f0141c1040760f95500421040c0703083c0d207901071040390780e14000f402c07003501c4c101594060660110380c081248010f900070f038010440c5003d01808a540c2c01c1c0015824a8181113000c031005d00751510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 328472266 1250 328471016 328471037
    0x1150c0f0f023f070806090606150304080315040b040e0f0105150d020603041a130201090609061704080c0a080706110f04171009052103060f060306130212070f050a 72
    0x65083d050071180c0c900040e000f000c1000419010410503a0301912082028080900f00300b030400800d640d01d41068645140705008200110b0103403400d484d4400e4180c05a0740740c0b5802200010b0040210700c09450b4000e140c80e40403481c13040002626150400114000c22850303d80e01c506c0542d0005198680e90f002c4001d05500c80142440750142d40c10a109031480300d001166a9441e5140007422100c22601000445d0080c096681c05807564004101c14207111400c9420407100500c20076100e241644140c60000c00b0604006c401401c84a004100758191080c5501526100090b94403120302910703004c0c208a040d04400030307410100d0700c0801a1448162403d807500c503542c0758680805d8032040172400382082e08600441c903400f03800d031010312850160a481c0000000b54400c0c40705000c102504500a004020355a25405402d21031440100d8041d0b840742c0e1100c00080b81c0312403130032500c6501c0d030011900069041c1c45910050168025031280c0780d02a5008004841c140a040c03401000030b46034010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 328473516 1250 328472266 328472359
    0xd091506050d060f0212010312080f070f0c1407182703080a06050a030c181a010318060608030406080c09090f040519030207080106060e0901150c0f0f02 67
    0x42006500503405410180081c42c550401b401c240c1c01603540d149d081d00c460007650350184901e41d22020b0000384090328104080003c2c045080d401418050240140342601030022803403504074100462000c4035000d0b44c43c2c174952040e014444030b9460700307241440c8003000c0307000c00c51029800c0100340703941e15801080e0544044030b407982c010300500002c0d0364a0001244a40f5202c0c0903001550103401210003c52801041601c441c240051280070186480000b0b003030342441410321841100f00f441d000c209158954400020191001c400811403464040009103a0754007101078403c9400680707403a0080d54802d0050300e030501c070b41c1c160964810503c1c40059000d282c034100b02034001f4040d8084400703244205c1012041d8100041090300942d11410741002000b0090081070301406051070580603143c01c4001040f005581030054072480c000c030144030344040c1d10846581d62807903041000c100300d40c00e29003801d04003404032170701c2a406901c0076010150300203a0394401c40404883c414001c0140e03103001c1f1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 328474766 1250 328473516 328473521
    0x30c100e12071d1e0402040c03020c01060807080705030a03081b040503030705070302040b0d021f030902060703030903140405180c2a0706030e030f0313080d091506050d06 75
    0x14190364804845001d070034100c1010000c281c050109141d101c0c42510100c2c90707204010f10010301c01038056000c9001e601c032000541500c02d0700103506071001700b400f511407401039010740030300840300c40c9940c0b0f016000a8007510000d0910112076a6000307a503003ca88507000d041c1c4030002c02c0303c060082516038001c18552041c003a06000401140a1801d0402e500d59000074110f0340a0a801c1c0c415030300403001401546064442c0905491044a4500b4882070660101703010701d550403100d40c844180d5a0f080a100741c0039400080d2401da00500981d40c0d0701091030003030003c1540440c141e00003560001c1f046d500c0d845003400c035020385e80010b0001200412800d1000700d0540c0042c0209601e1006110070441c60b400041080020152400003000180d440d045040c075050043d40068100340c180005a40750070404012200c05c4004c8840c1c20b9960381d560b8150840d0700700400801080d070903000503040000800c5074030181c10b00388030b404d0b00060283c0e8101b0711425a0550b010743c03075010360800c400800060055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 328476016 1250 328474766 328474787
    0xf0e060a1a0303071101050706020f031e0702100e0f0607080906060411040e1003150c120504020a050d0c080307030806010e010216091d0a050c01110115063c02010605030c10 76
    0x14501f003031401d001541c84406030707006480d5010f500c14021052005c45040900c81d200d0b02c401e002446052072601c964025500d1728076100340801a81d1310504080603100c1840140c0303107110720030201c0c0c101d4100711400400354041111140c0700d43c003500000c1003052403d0b015540034403400d80d0107241024200803180c01c9001c0040c00b0344654441080f0000300141403c3c107881e8100d0b48080c00061140500342024181482948407030500c0d03840c00c0300300b00040c3c2c4c4841c0540c05941d000e907142100f1b6a824600b281010145400202c4644000700b0302d0400c05921000700d0703114050a98030301c3d03108001c0308016079660700300008a1410490b60310301448a00486d0380256a00340c41c0520745c50082606050307180c201400700409407a1508172a500803070a507008829070018520303090080001c05c101c0494142240410301811040015001d219818400f0554440070500910000400740c9141d0031400c030705103c50305200c000503500742800010903144c0403490140141c0b0151a6100407a1a40300803121411807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 328477266 1250 328476016 328476019
    0x9030806220903050c161a0903030c060a060302040e0c09160203070204090c031b0b040902070809040c09080705100801050907091208031f05010c150f0e060a1a03030711 74
    0x30440748114508a501a0741c0500d802500d810740e89841c00300b41c1500304179030355403150207221240204100c0c072403900480155440c190140d4036156641c1000107421071280c90014a074900c81c0d0024440301e196594400300440c4d01c00c450800c48030010b07000041d00c4900c1a0bc1c0242e005175010001041619184240307443c80155205991078150b4942c0041c2c1100c0e41001c041c2c481d15100c007403e00030040e0103000110703006001c0c504480000d16114a030b584612950060080c0103801060703600400000c0415141400c0d4001c105102850301a030740108080d51038864120144643c43c40040c50313040100d0151420542036a40390007aa0070075080c0300010340041d011608202c40800000f9044803d58809100a4841d0f05050b91360b00300743c43c0c1000301041c50590012801c280810422483e80c2201014941c01c1d40010748100d2000300c0002c540041650445c409520350a0030088020490045031140c4601c840081c1040140d0105c84500d08403429405040d030140e10402403600407682d681302c0c0c461803810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 328478516 1250 328477266 328477309
    0x150c03020f030f04030506070201060b0a18051c02010e09191d010c02150105040b01080103150905102301050a0303050708070501110711040506011209020a03021011060a09030806 78
    0x12001c01031840e03108442102c02060045000e00401a080c04250740100d090320082c40f2860801003506081c4c8100312810090010388810220300c003801081250040c08002c002c61243c0034051155a089608940200e00043c04041d0b031850782d141c01c68100b40a00d104001214100c0d4480c5000402000c1801f41e4100c0c2c1081d0907968103401c00d01b401040c0798121683d014080b44025240818642c0340107801c6280703e1400c3c40c03c81c2d402660300240c0076045075000708200800781ca0803103640000700314558015201e030003480080045a0555004400780038004000506102c038401c0020462042c28001c00d680064100410004603215174081c0c02818003c100c1c19103018065a1a142141c40043d151101e041d40880c1034024800a20f02d041080704041d9001d200600c1c00e034000070b00800d880c03001d45107032950f074100410554503541000805540d0180c41c1e44801c510445001c3e2050101540d0941a449003100203034243c0c20a018803100343d64580c441141e1620390408202da001c0026811520364003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 328479766 1250 328478516 328478533
    0x150606090301091e030f0c050d0305221209050414011217040e04020901090207030e01081b0319050108031305060d0b031b03010c0203181e1008090115150c0302 70
    0x1d0500c0b0385104e1032141401018628002460080d141e440c040d01c4060030701c805d0039074110206001090000c821401c500d80000c031a41d8440740410361462860804007064008201b04d4104400351032180d1411a0507150900c2140e9200c08107c00c0d11102800391a0052020700108005100080c0100009104111010158084640c900d1181d0010390110078400c00301d1007400203508180801601420f0540400c0d45000e980b52005480708141c100d41c1070400500c100021400781600340088080c0c4105000180c1d40e0030a04409040801c1d03146425400354a0030000140352031002080313030040000314000ea2681454001044060340003a020362041544400c15002c2d196001c0c01001c3c40340e000c0241410701840001c0515085a0704182e409040d944200044010148501c00c000c2d00400b0443d0b84148240c012207c5c805510661554103070410380010040c54680d0b006000345200d60741d20342c001c000c03852a52284001ca106680324052001e40940060200701d440f800706101c095000c0c0c01102d0018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 328481016 1250 328479766 328479773
    0x150252030812060423070e0109080717010605120703200a0b0c1213050603092b17040209010306050a11040602031b0a0812090718060e060315060609030109 68
    0x1a4850031003442e80d00c0b801e2040200c00d1409114941c40700c064801162082c0d0b200ca50008481013014014600b131021100042078540e02c501303039000241c0380d40d8060b20091907950103204c401191441e80d007806542440804a00760514400c12031100b6241d90040c81080e01c4c580f28118400f001d030076015030340d0101101e000380c140c485c070100c1d80040c010105a1780d550303100c25800380d090544407c0602d0524804100c44c620150f11840c2100c140c070300071985107a072502c50024061502003841a0482d0718001c10f40d0050080c4580c0d14444007078500380d00c0da00c100d00340d1044c002c500f001d011100203600021520040c030200351030782d10841e402100c0c10400117021000e611042c01642140e80400b006034400140103c1d610094440d011354602d8880041c803480c100c0365120401d6000e4840381900c42d0140340c0008001a0040085500a005070718504082e01c1507003800d20080c0105010b40030030038104a0214070542000208003000c1c480403203010b9150b440d0341d820003c480e484911031651541d01e030b00c1d01c42d010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 328482266 1250 328481016 328481033
    0xc070209043005070302010f11040627060905130207170304060213030605060103060f080c01050702181e0f07020a021201110d0902030c0901150c02010915025203 71
    0x2d460316481c0d103038441c885860b0003400d603500c070190315401c181030164960b800c6050380300759030545075182880c0b51107400084c1c01580031a50005d003011200000c903000036586401105d07040c00d403003040c2e601410300d94004000d5000c0e8441d04c140200b1141c0f1220384a8410400040a1030f001482004003514248045680404011050300140e440300d9440c1c080c80441d41c2c1501c902d40043c400c0242c030754007140c90700c1c01c003980f9a00a51002414020f00040c05ca04540c0c800c60b404401c2c460360344140216081c04504d2551910790821040c1404e240980070840310340140450511030a003543c002c0590ba0400d600740010054152400b8200b5034a03002c007480341030311003000340400120245001603642098010140341c000034511840c0140c0742c074801404a601c1d1050117030041c1d5aa421709401c030580c40e100480344024550300035a07540000f941c20038480d950100f201001c02c03081d1801000015900205040500d07406080583c0702001d203211441c000c0e61008005408005605131010038990f240c546890 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 328483516 1250 328482266 328482353
    0xc0c01050a06080c100c060209040216030503071d0904120504080d08041b050604140f060f07050606460b0a110325050f010e0a02090c07020904 63
    0x1c0c45501c9020501c0016410007181903080030884841800c50017800000c0c000200032280030301361580004030080c0c1a180c9804459220113042041682a82d450500034001e8105071038080015100f84502a061402c006086080790801040c5100301c0d1100c0c0e03980a90a24682400810700906002c001042502071000b0542c0da501e5880d001c043c2e203064602690803e000304d031080f03291490303048144201c0c0c4a18081d542610401c07803455283c0c4007243e00140038540030158990344072000142090180280f50060b08400b0320500440c3c1c03007619440f0400c070b0048001008107a44001c80348107140040d507101d45c60b82d51a031148201c5001c00d00c501014211000c4207402400d6410030004074084d4095003c036200c2400c0741108042c5042020300300024802c04070224402001d1a10a020601440414400070410b0100c400007000a0300c3c0d4481a15120f80c040c0c90283c4c03141d1401000520207082d15011904000d0b401042c04a6a0b903030380d503d0880da00d032032400e1002c0c0c0340b01241c84460180d04030100c052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 328484766 1250 328483516 328483531
    0x20f0303040909032d050a1e031a040e0615011205160215010b07030309080c010515120307050a0b04050a0f03030501140d030905040c0507081201030201030e060408040603050c0c0105 80
    0x1c90203040c4c100030303021848400412040644010850414141a401081d024141481c0042d0b5a1200140454104071030380c1448808000b0295019081a0960710925803000c2403008150340e0b00d072310720070402140c001d00304142c5143c200c174000806411540b840e02c01440d46c14188031491407400580541110411075540c204030300c0c0c2811621050b40c040064080140d001400504150304080403110103000e040ba0050a158891000380b04004010061741c5050340340310020850707443c040c03030f00340701102450400d01e01a00d041d11402c1c070030740000701c100d4a00e1170b00100203150604441e17030750003000078006005a03480e014034025400019480b02030b601c1100c0c000d503404900d9505001500c9450000003102500c0380882c0c20182c0c000070340018203941200e404680000d031300031900340b05648511800500800ba040d0008001c00020080201d8034142e90003071340c2c20442d07201648000e40cae40d0b10007600d013305080c0c002e000400446100e500101d600c40d2201c0c014a04000b04402101e081d41d5040e207000e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 328486016 1250 328484766 328484771
    0x60203070e0d0f0f0c0e0a09110301020408060105091b040605030603070509131b050a0305011e06030f0809031c02030705010c021c18080a0f1a040206030a0207020f03030409 76
    0x80e001d51080940100500498409403010080d80c1c41030109200080010522114440001c043c403034406602801030208840349441c910741009900002d2083c4002180c9042e102c541d00780f4241014800d071000d4074010001000c0700d900781403c000c41900c0083c000710011130007902c040100c00042c806840117101c20340300d140d103a04180341054103012682d00914000c0c440304042184901156002150094000b840e042401903a02c1c0f10445a090079000981c04c4540114000100b060561000340702000c1c0000708004030108040c1784099480c0ca00c400351048ea240703540040450049402010760010050446080007020b003220028088000801c80150b000801c00c8003e0100c00e0182040c0381107648090b04607541740141c64104220701c00741c000100440790001c10070307400340e480389400505500749c101e034121419450503c10126001c3c501b224080442c40100003003101d00c100a9001e03d43c0181001d056969060302000290001c40c0141d0b4405c43d520005100d0340ca007400108040c011500c4d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 328487266 1250 328486016 328486021
    0xa050703030b0d12030207020f0306010b07060e060108061f03230609010b031c0201063605071409010302160c080d0813020904050307120504170a0c060f030f0603060203 74
    0x160880321141e01183c0102156002a0005544510b1045a51046042c0161289005c2c0081041c03000f8103a1551f40521071800003190071501e02d000b901d840e51050f0300c103000001c081420661181020301c140c1e18180d0001c400308403510012820380c04114180b41d000900e1a5070323a100c10041c881c1070315611a641100019010340841c0c18444544d010b244140203120400380c0c10007195881000f80d0413200040915080041440c0c17007034008100420349500b000f185011441c1234104d0b90341081da5031a0300b03000140d0135a4041c081502038644656896220020b002c00c24003c0c18200c0e521924103a03041550800599040a04100c0003075107c074001d0800104481c20002145e141c0300c4216000401c0c480e4200400a403000400c084001c20380c0d0580e0100c07030316200d51401e54510300400e103006020125030305003540156882006002255010090140d00440140141e0745405181d80003421508101000b403180a0250002c0800c0105614000580300380000000d0101d4034240c0003154095000001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 328488516 1250 328487266 328487273
    0x6060904080c010f1e18021207030209150102070501180e2e060f0e150c010e100509120a020d0e0a081501090c05041d06060f030711070f180b0f060a0507 67
    0xc004841c110075110421400021801007051b5500000380280314842d60503c00b1201042031010400440e4050b001c03804a080426095140c1d00c4000c91f8103005120b035901c005032540c450075058140400303d00e00100c0301410244040c04001000380480e0381c8498005002405640031250601031401118140c4c1c440750402c0d030018283e21030030744d100c8204a00c052199045680d1561000003082c41244813565660341044c529024200b03226810805000700d03884880c0c4000c06402c4907115220040036101c0c80b450329402100c00c4d00450400300c005a1103040c0c1c2c1c40000c2e000c0c185040c0c00b00c60080000c42190780d6076101c0c0e858018501400911900e124004002c80b100c0d9000b1401c07a4007203424100d00741824842c28001c00d0419840020b1450f100e0b07004034200b0340703900046131040c1241b81059507480c40e000c04040c10b1b000010445001510030307803100248801d850248041654010445030b240c044000c00e400000e84003034809154842c015021038610b55503180024208040075807191500e8640314103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 328489766 1250 328488516 328488551
    0x201060e06031f0603050607050c07050a061e030b1320030108030a0f03060306061205150411150d0e0706110304030b0103031d1503160504030506060904080c010f 71
    0xa000e00c40002641052241c0c075900420702d024009680664803080d80d845400c0d103030180246034000f81c1a0700034a070601c2650760b4014010300f40215800c0460310080c1c2c0e11024050368207403610601001517034000903503941800c621004000c1c0350803071402041410b40c0c200080c00034145008602c0140e5512051403030361078002c000300d0050401810300e481c110761610503a10f8481c41505c10f01c804101d00340c00b241800364002d600043c05903801c42e8007008415250056207010440005007030305c1611801d00d11078180c90000300b56601c11540840034030714440c250340a0020450740c00342a20050b050612103902a44401e1003560075074050310000f04601481c140c1d014014400798000d40c2c809070410407062000c601c2070b881060443e64075161454080001015040e503c51090544070741c481e00442c076a02101013000d02030b50180505040702e12119040e02ca082c0c50501c12840001c1103500803200007589842c2031060241d1140c0580869850305000500d1b0a00b10340000c000c060000d5540e0000b04030384c09122 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 328491016 1250 328489766 328489769
    0x150f1b0d02010e0a020906010513091a0405130c0b032809140613110406050612070e010504030209041e05060a0c12060303021c020c04060801061a0319050705040e040b0601020106 78
    0x103081c204c3c0094000c038140010007010345042c0040001e6000d802180c14001c01c0042565007010050103c5e00441040c80d0400422187e00c00d60a09020801600e5122998080c80b44d01110b041e980c1c5161024100c01c41e0001066107090f1440c0405400e42c0c0c3c010b89140e9600341142801c000380107500303841c0514a641e1a0000b401031039100e1810807552007810503544814941002d051900d008100c00041c0103805180c01c080e411903004102600e44d640f62080c640d00405068171400e4001c0b503494011105802280300c06503109480f2000b081c0405c0034540c2c5000c60703150300340c401c2521100c96100e80d4689038003501c8045d01c00f03960302040e0589940c021032808600301d04c0c181c140320b1585941c074000e55806082007402c414405014a047c081402004042c0c50b0260241090192640d9001518001c3c03072648101c07000148000c220b0420364418004803403256041300d40c2c48403241d445101a07001060010800300a100040001181f81201050f004c2d220701d00c580c0c584503003490124002030a44a56 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 328492266 1250 328491016 328491041
    0xf021f09060507050306130e0712030c1101081504050a09020a0803040e0105030c1e010e0a060905011116150516081c051005011107090606080103020a080c150f1b0d0201 74
    0xc0c411300095942c0c00b4102c01f201c1400c03507408900c1500da4150503041c03544907407110110884400410081540110101c2c0d000e034080d002c0700c03596151042c010340303070b12908403019000742d00c021118040318a055400540c1058020360006680900307a4007041c00404140c101c0000e0750b0010a04109000096400c0f5025041c21387c003030400b0b0100400800e002c280c1c002c1c06030070b018513900c00581459100d200790020000000704215802c40d40c500000d80b402c00305014003800680101080300310110005003051000322020a40d4698614200360300c0309200840388043c041210801000f408002071120709010f10b4080e0030100e54401c0d0031001e50040d56110702c00d00c1c010b241820204601100640e46420031182d00b03090007540006000412030034100b0342d070843d62003c0e14041c40400c600e50300950980c1070f244207903401c480840d16201c4007951405078048490f484210f50b1404c1d401043c81e40c014100001c21626032504244103800c0e28488a5074880318400140d00100410032500e6090003a600005035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 328493516 1250 328492266 328492277
    0x7020901060c0b0c0c0123010918082203060e0c0913020310050a090c0807080c01020307170d02071a07030b0a06020a0f0807020a030c09110a020d0f021f09060507 71
    0x8699a071804540701c010442013280c0000708250407510030a40140001c40c2007140c030081e044850094014445501f809028101e500d001140c1003500010342e10000840c1d0044a1182401c840c02c1c0e090094845810070080355000c100400070024030140142a6145545006000c04c41900400d2041880c001001e2821007000c2000784800342e00c000c2048401d00110750000300c1c441d901c00c0c58000140010003c010100c8054550001f401680815010181d840da00e003940d1400c840c0302c4c0120307034078001d10300042c0880070300c00e9401c0c40054800300181014403145901500f403043e43e8644a500c40207040c9070103400902c4500b0048442d41c984a03c2c4502c0390708171814154241020402956a94811340081012100d104088180320032076003a2012191b000b0f0107810401d40782d14185408184c1744c0709440005080039441d4802200000640e0074501481d8000c4c501040c200200310740d102e41103807030282580942d2182e1100958244c2007003002d20400c0c1804508034030346107400011220010845070801a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 328494766 1250 328493516 328493537
    0x6030f0f1e0b09061303170606090d060207020a1d070f090510030209010f020f0a06020304140d1d0406142403070e1207121b0e0a140a0501050a05010c03050c030a03020702090106 78
    0x21f80061004003503d80c54040310400c1ea841c0c0c004100148550b60245501002c51203600003000004c2d0001c101d80c3d0301c00e4030422021070307840d0f81100e94181e101c42d08503088286da0380081d02d4948125402141010245084201c590344c1c4c1d00072801703000602032000d002940001c1e00804a507001404d09038440c43c60f1004110515483c512103480c0e92000400808080c0c00002180c00d208070318407a500c59240c180281c0e160301502c000003400010a10078044c40b0180364480c03038955494907103e5001160806001611101d40b90f130100808500c100d5101c5902c6051440d4280d80e00c0c000c83c016510030100f54a0f42621011102c0410400304c0000725407403007951011400744500458004035094980c3d1049001081241c02400c5414680341a00710702d040b40134140030801031400c25048a080b51055001d40d40e4a6110011201c05880003405055040205510104119440b504803800e10760f00926145040c82c0c082d99005041d0341c8444400d80000342c02003003103019498070425a5004200c18102880e086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 328496016 1250 328494766 328494773
    0x2040e0708031e04150503011a040e150102010f05181207121b06050405010209040b060a02070317042310081003080706020904090b0a05010906030f0f1e0b090613 71
    0x24400c1501044000b00710b07540d03142c080d844100035100034045d1017403078142040c00b451006040340c04c00d1040e01550740021156952070311072481114140c1d280c80d510481503984102c0c511031450f0814440381e04643d80e8000822a481191040d41c0c05009100c0c030441124007072080c06890041300f02080000301e0410008070300011072014000100314020b013010200c158030f0204000007058020b0026040780e0511040108000341940200a2170200301c80130040c0c071030340205110041c0210042d03040581d02100302440414840c9200c005041c0d40c45190500e40794403603440082c40b52166004080a2142001030720f01868204070316100d01a0390700c0d0011442c40c200c091002144510310005d03086280000f40b240c20b01c038054040310007010019006114405a0749480c0284a0702200c80040030362030180046148505070013103500312a003040c0301181030201604c4400300c101501e10101c4d40c1c0c0003440120a00f4988084a6a10301d5000e00d010308503603c1c021b50f441d41414002009600c0c4001042d4500000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 328497266 1250 328496016 328496023
    0x90606030d022104031514010603020901051206120307030809150609040b0403090e01061101060501391406090f0c06030a0f0f020313030e04020f071b120f02040e0708 73
    0x1030590049040c03c812841101003201da210310341002e014184c40208101c0f0314170450300f0240100c8842e0402441603a81d5980072000c0740203801d60140090300400607003004c41c10f10001d45800010080c007a40510809190b560701c4d40e400108114003251600d003c004c0044e9080c40140c910070080d46500c1682e10b0540001341e0394100081c00108040b07400c101050506100e8101c202c007420001c1c3c0d48025070358481c4405410007000c07600c6010f0710760920a000c60154441d02003000d0382005005204190001d030741c84502700084d08020301c100c0f65039210641012801c0700b400190142243c0d400340c44181403044010381090b1060116a00c035030f00206049441d619510b0407680c0c45665804000340b4001c1c0301900101030007107001d0624505002006005a84551042da0021a840303611013008800802081c082a0700801580c0601508117210900118085203c501811001d044a18441d1500d0315020010115511802e0b55601390544001003117040a22441080b130a01d00c00800c5024035003484240d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 328498516 1250 328497266 328497283
    0xf0d0305071509060501030b070903031409040b03060103060213080105040b070e01030f0624091401110a05070b040e06030c210a0209010b0a02071710020307090b12090606030d02 78
    0x82100004580e410b121a00800004071124020b0900424580c0c0c240840903040070300003035441d41c54240c0401c0000740a24400740840c2e9160700c0d0f50b42c591100100c00c1c400f54101c1d00f5080d40040e12070885005981d4280100b0b03000c4c6100d03000068680682d25800300b401d082c0c6401a8406d60f240c1030510012902e00c1c88840c2c2d001c004c42c54015445040e0340b004030080c3c0b0012800100541c00c0503c0420400d194104e000051186001301d81540b15142c6c904850590140c854181000020245584107503c513015034500f46090400729091184a40e03a418a4004154404020310101141c2031103489600ba40464004004130000c14a061a80002801030340302a0307031f510344d01041140200368880c0140024a1020307001000c0c0c400c150783d26408124140c2c07007403140d4001405040804210b619800001c0360074003150000801210440003500d01c000d5001800c24410b101c81044006000320700d000013403202c440e10104108030703400c28015043c03410350080c1c00700e446908410301005202e03a00058600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 328499766 1250 328498516 328498523
    0x1080d051608070606030816032a1220010f060b09030316051f05040506070201090506130c0f080c040c020613080d111911031314011e0e0901050f0d 65
    0x540e03c44a5151020090080398002055640d011610701c1a01b4140740700350b480a8002c1e124a4861204050080504d0f000d15012031514040508a9008107503001c1028880c400345080c106818020321514101c58010481c5085c000c1c2e4583c442007108807058004d0304010888100da89040562000001c2c1e143e00648007401c86006c40402902c06200d42001081940500d90010160101c03440e400c00d806404111003e58441c480c5e1800308030400d10500ca084511a000703005045203440310780d8800e1040713000e038105880c0d9620b426000700700c1c2e01d16000f6590040c01e1203c000c1c0716003248401070009648c488010790040d5002503041044c911502000312070216401802d60303550345405022013000b400d64a901d00720704040819203281400340c125800142e108140c680070201c0401110442d603912a100c42546400601c00003000701d0380030400e046c406503005040c401090005000c081c803404440241010003d941515408194107000c58141e014101c242c0c2c0040d28408510301142c403030100d150004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 328501016 1250 328499766 328499783
    0x1051c0213150309021804020306010302090702100507081f050a06030c1206061808060c1204050a0b07081b070c050603130c1413020a080f100909050601080d0516 71
    0x459120444110388002c0c0100e80c000d00c04900342d03102c0080042076410022402000564403607000d540400d000107125613070041c0140410781c00e541c2807060071400500f80c1e8041d4031622030350b5403081e951801103911441c95030761007071143e00e4061106503940c00c492412000d8445201803e201e40d4179076071503c3c800d4622604000c00c19400c15141219428400c1701d00c4191189040004200294004084c120001603040f50f94400f60315015801c3d1034410607612030711369070300030030000c0718079100b03d801a6072003801030007901c003c4804e03529404101c0204407003003000108080100085465001801c201050001d01c030b40781401f40da540c032420060340d40c2c0541480b540b004000a510f40d1101a00d0b9844a940300080074807180e9a1414240c1102e800e043d05480340200b42e03514100d0052900c00c0d203980180170f550720059502d40144510501201400034007000030021804100c885d020b0240c05425031040005145640c5011720103410110040c001504000c010001c001108280c0704408803442d802c808803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 328502266 1250 328501016 328501027
    0x80a0509060c1c050a0c02011d07030204094b020312030901330518040f1104020c0c0a0e010623090d29100b091503010305160501051c02 60
    0x10f5446a0408642d18115043c1380421801c401c840d0800c0d04c04c01180c1d0024050b114140c9000741340300c075109c0020041940200c0c0c08102615141d00803006180c06401c10001440e1501d99a01c442074421504110318011171001807a5800c141710340c2d403003484c1c29010004ca580c0443c0c0c00681c5841d0079000840c095800400841d850000a42c09600e114540c5080010122101d440b6524200009843c0d016601c0501310000b4071800c00c0001c0222044000704204585da031641ea4003c001280100241c0d02c04405904411203601c40384000d000c01c020450040c8107108440f400c02c0410030181e002440c40c00c03000401000f032550842a07500026108079220503908d10340480c000054007075002125480049640440180139022800c09000380d542402500411107005401c03c848506442ca071481007a010400c019a10955000e0201d1481c01000c46210328014500d101380340d0401c0e0820740381c0790882c80c1e80c04100f00c4803540c90b10040c1000e080881c201582c1868401904031007a80070b03034400360002030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 328503516 1250 328502266 328502287
    0x1060215041406070206010305070f0501050a03020711041107021c0308071b02030607030f0c080118090302010b30010e0c041d06090102130506162a060e01080a0509060c 74
    0xb0106042500302007120200d2900d181d0096490400b8401550f140c000c400d00403a01c0720041504400382c071703810303100d40c2e14111350904218000c0d48050030541b018014070701e182119a5590181004036104280b00c9034680d000c1e03004000c1c00404c150070792064058003408a00010f500144031742d6203e02641400c02444905101e9194411006100258135000d441c040251958056005011543c9044c1042191441025003661000028002c1108050120042d241004002d40090784c40350f100344008550100c0000c00f00d1042c0c0400d0500400c0100500460500d10210205103940180c2d000000e100409104608507114100c02000d103001c1c0e034541c020040c101d000c05105002d40c000d00340c1114690315100c002613000790008000f420303840b40008400102c0e4a0039400347d5000742d07981481c50b150481641e1f9011001750b00d040c01068510418040103d01905017440500180104d0312000d110512140c00140204001040d000392540f40c501403161f04000022550381c00482107400550320710030000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 328504766 1250 328503516 328503533
    0x10020903120f0f0a080708180c04021c0e070602160f1503060305032106060c030d050718061205072a1425080625090504020f070c0e0106021504 63
    0x3004801e1841d00240d03208484e40c0c07018044c0d2203042c0c0c603650590b00d600e441e034034030300050405504004c190b0f0020030b00423458a010790060010320740488115900303103a0400c00106648855880251941200000300b080d9901441803400b600622a0764181c01c40c200218500c9400031401354070100364804180d9215180a03503c540d01840e007000c00c42e03444100460310b00420209608684401d60301040100d60715090072000d503818101710601a604094003202c4140040000401d0b0b0410800a001a0140d08076894114405000c1c00d50710301100e51000030b03000e000e0341c0d406810b0404104207191003014250030510f0707d9805641d00000d810a040d01b80c1400d01e1036003c5a00006a103000304119190360f8007280700300c803c0c0140e11107000307191150b4a051446c1c032142d084a8019104200206407000d03032008203007200002c8414100720751500e8580000c94100d800840c481c43c000301c1c0001303010b010b00c41c2c106083d800810360160b81e40c0441d1305108000f500d8481500341c40b0700c1e80c05100c01241c03c200041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 328506016 1250 328504766 328504777
    0xb030a020d0f02130c02030f0315061606050601090b04030210210b0a0e07171306150602060604090c05010e01030204050612040b090604030f140d1a0310020903120f 72
    0x1030440e50035141e582032641103a0711440c01240b245010306100840020280503c00010b200c91b0095070428104440c04480d56100501d103003103800503881d4448080d41d0b19009440702a00001d0403484804940c5080d9003103c0d0003a0007541032102d405010000b80900d00200e505030b0b41d054036083c0a5a50000303080c0d60b00d042d18411544041c0540d4035443c0d00c50b519502101c03440d90111141480d0741e41d81c00001c450b091003661a88000303a1a070603d0344031045e912841c2500000a01c11300700345400030380c031010100c552440000c4819009040104040c5904010198100804035000c0100741615a58199030282c6485058148440070a8844003603010354141e50003400041c1c0301c650349103003901d00c003091100c0c110384c111000f079199808903500250000d5210b11569241e01c4000c2506090380c420385282c0c1e40101d81c003010070010041c141e0003e84601841e8540c2582c4542a91201c4241003054103114041e0104410140305000c85c01c011340c0c002600740320800380c09196694a07081d8422511a610030f8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 328507266 1250 328506016 328506019
    0xf01241b060b0a05010309080d0213090509030405011706100e04020705010905030a0f1110020904091203050403020d18090b0d12051c0902060319020c0a050307020909060108100b030a02 81
    0x8503003020092007002d410800c2549000c0701c04500c11030f11540107500b22043e000c80076180e15000e1103442042151540106501016000c6032450300d9034071034844044d14401ca40003c0780707400c0480e0800c2507503004017807400c84240056943d4100e00d440400b02c0d81d6083c0109103e0104058034020315016107659044404494004000780a00300042c24260755030340c04041c030f040015007071032940321217280f15a441038200110783c00030b09115004071506c800690045500541c1c0300342d841070b545000904850502c80145410f03107011841c3c0c605400c0180c20000340007050003d01440d40c0c1d917000c071300e080e00400c0d2003070f110001400034120000d6001304488500110b1700800c00407104241c640441c1d00100a400b0b1100001d13132801d0754032002c07c0c0b43c80582e04013441c020b40207001480441c41141902405103c0c0000802c00103042c4001980d040749440c00b901c10589490b00006216420343c10501d0080c0c0e4043c003110300a110652400b010031303681c2d0040030080098150b0721081505159000d00030007101ca41c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 328508516 1250 328507266 328507307
    0x4030e010327060e15010f0303080a0f0e06060310020a090504180b070810050a05091909080414031b0d0201080901060b030703020a0f020a030801120f02030102160b0f0124 75
    0xb5180f030080b0090030300070382e104036a1003054000c0305982030408205040e18016030341c84400c11b245940a9440c40000f404c02d441c65500d58511108800c0e161044460540c3e04000a20860170981c00340f505000c103030b0f000b031864030740100b042d80c00e4a03401c51516412102d041e0390006000c40011258003040040c19001800b00c0804000d00c0704c0030f0303170081d80d0b24000c0d00c0110019100503a58010003110500b00d01c90360707403c004210001004105600e81d43c0744480c800d401c0118403070036140e544044035402a04541c0300404004000071080c04c081000111211401861010f11110040020140e12081200904002041c400034010344020341040d4003c00491243d00d40f03038205140080c3c040c0d08840711520000e40c6060320b54060034400500049d4036a05038031540ba45908201310450141850582661080c403500c0d49140183c030240b00504040c83d8401030703694100000d00c1e20710070203c1c0c050140e21070310154030300500c04001c80101c50070704000340880129000c68060010f940e412596004c1007880c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 328509766 1250 328508516 328508591
    0x30304060c090602070806010303030506062b0b04090b0606160c0e180d09051e0d150b060c07051e09070206061302161b0503100204081504030e0103 65
    0x20312a00440080c41040e100c004095450300800c030b940f4045445440200da124500410120f0300075400301c0e810950140800e468400c210103040300c062000c0005042483c2e2000d4000b2006030300d03101d1017000302c0c0100d8041c000141a81c55051301904040d144600c24034002494818801d01400c0c1c40700710550200b40046180e035103800c01c009107541191003011058000364140d40c0d01c28003050080b00e02d059070700d03030840c800d080005000c15012040e42040c496031a8030280d8031683d55a06000c10003511407d21852a64544c1c080502903d81c1100e0740d40c017945040c4961800408080791038010380304165440c4801d010b10070000321866100c2801c0715001f00402d014080c1c5582d020a480380700e11010346420560003c616041001ca10440050340e1142080341d00c0100060084090440c091034000c1d4161515511240060304014002c160240c0b0158001000c02c1100014045802503268503203074540030b4074007503c2c05468a4007540c0440e04040c0d0300d42101c55001e666814107083c812422102000a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 328511016 1250 328509766 328509773
    0x51803041e0e0c130b160b10081e010b060405060409020f040509010602060a05070f0c03110109080c0a0c0509010b030606071a0108030d06080109051509013b06040c05120f030304 78
    0x2d134850320580c3d140031281c4c400413441e121400d003101e07101c0ca40107460b40c0d0040001d440e1690305000190000c581e1a0004000142100781000140b22188920700c40c80758424210820508580b07076040c01a004040500c0f0411071942d601054030221000c14402582e00d648200100c0000d110b5500180e511074100c1c000031031910340c0050464410509103c0800c01d645805005940d151200c0a400e4006400c8030040c0000901c100c480c1120f80e990300d800404c0d00381e415515010f094001880300c40a0380c1c004803003030701842821654400102015034100c0a80d50510f0740c640202e11005140600402c000a011020846006522520110441180b41082d61030780c001d2506e1781d02585a081c03a69040140c0850a85818800e603d500d0b94490014003a0f00c010256120303185100070280780d441d560ba10005401d2202c111402002480c004014020900580c50340c6031204050303c000040c070b40d102c03008002c0040c0c031050b505404e8402c03c50b4100882100e04410618050b00e07901d01c00c00c1408044140800c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 328512266 1250 328511016 328511041
    0x50f0310120b010302030105060901150e01020a0c150f050307050409022d0a030b22050c0403170909180607030b060702130504060501121104020a2709051803041e0e 72
    0x51380c0c0b00724000d00981d1900020050b903200c0078040d4500d00140d00002c840f03914061681d1281c2d8a0060040d611920040e4841c10056841c0e0740c13010311004480b102500c4100d60080300314501c0e91450074010b0031414581030091190165018122420394000b4840c04034a25820640c070603217014001e94441d260340030900700041d4200340d04180109081560142040c60401e8401a401800241003031001800310008005040c2c00742881103040420000480483c40d19240c10170b1280d0205940395541600704144600d00070700518101d0345d000105200140048041a010f4010740a490085000101e040009820f40b04948c1c0c000d6000030041184100b01e0815005148124080c01c01000982e0341c1e02818090902c10440050201c07480c03d031a6022850282c1c040c240d01001340c503240402032080c20b0b00c07070f0503002d00034107038010300003035000401c50b00d05507004042c1e00200200c24103001054006003242e81740210301410004001d94440710015901aa1081e0001c03c04185c00d19428108031a10010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 328513516 1250 328512266 328512269
    0x90f020423012c0403030b0a060e032b0c0305210103060b0d1203150b030a050405060a06080a0b1b0a09030b010e060915030f01021902070e07050f0310120b01 69
    0x41c14441000042e10309920090b081c1c00d8812002d002c0402803103140761204804024411014140c1d40c84800c00c554503000044070240246071110800120a04100340c0340280c040303003031180011440d02650161003c0c1d0b00d0120320140034140301502d092241b50035200c502590041e0700d040d00000000c1084018507a0b011812203006c0c5200308420800c038400d102c041c51203910043c100484a200f40c4001c6442540140c0c1e210b1412140121965103503102d0106c1584181d07912800300d6224000d01c403c0c418103000300c50b0000c070404402c00c4003505e4284642d07100d94403c007024200540d0030b00040d150f11000c400041019100782c18080e40e0ba00c981402074082c100a02050756040c1d080d400100354241c04211130750043c0c030002c10f0140995517411070680f040c16010016a0140107401e0307030741000a4240007034103950031b08c1046c030b42c8001e00d4520000e18000003079200d800421529401e014455030070074211070348030540805040d0350b951511605812003e00c0e500600d440141d01a001040c800030348010760 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 328514766 1250 328513516 328513571
    0x70c0522020d06061202040807060804060e0106060f030f0c091a0409090302070305070602070605040b071a1005030f01020f181909021201060206090d030e0a140f010e03030408040306090f0204 84
    0x36095200080171354100d0045008031405580410014000c0354000c0c2004c42d0311510444c0c000c1102e41c0e05001032425144030341e2101c0c0100c2c582c5250002402d8050299009200c0c0d030580401034a48142030091800303c1d58810b2114a141e400514014070201804440103030614070802d0100700071a10b4000e41d00c2034075200681300b40c0128840420340c5032000c206042184c2442e07071500d0615041c15010b43c0c442e8004841200d075012044480b11148550602c0c07184941a00003200450034502000d05082c4027145041e101caa034410080049500140800e43d2995503480f07010f0b07211501e4080c0414407409101b40c6401d500c2071220303c0020b80755060b8004129001007040014040d0341c3e24070307090384d6031207081d1905407076508114411200b9501c030f0380c006000071400c0002ca0f1001000c94503100c8254111040c170022503004807000081d80c003024068030f80e00b00b03e0b2000540c61480c00b0b84130311005000394003000304029110070401d01481004001c500c045c0d60000c1c01040300d50054802000c00150860200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 328516016 1250 328514766 328514777
    0x11107022d0f06040305010f0c020709061d040812041202100b09040b040c090c02070e0105030d050304060f06170607090e060d1506080f0a050111070c0522020d0606 72
    0x160322155a03080702280e454018012024854481c000c100c488010403044076040001400008080b030024021003a1000c6c110303000061010342c080f0001c0c2081c11503001244c0c001d040240803c8402c9c4040305840b0300000100c101502c03a22a854048500d1082e8400200900c00c000280420701c600050018118041070302244d03d084003150165040d42e030740a0185501031001d60000703012440c0703403000c40d034481e204282d60101917840b403406d001111850128000103903c02c0c2c03000c0c0421100101c40318050a4114020000f803948000018a903200042c401004940c9032400f500c0300c6a9190400c001404250000c07103001e101250185548000031a09070002898012000034806000b5441a0142e10081c00306414070405032104207014038220400c44070241e030360500003200390003442040031104200e0003a12840c07600c3d003004d900303480505141e10714070481084404006101002500300300c1d9401d030b9004112040d40740411000139020b241075401e01d0b0000885c02d58001c1703070380d02050a4030010345a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 328517266 1250 328516016 328516039
    0x50a17131e120302150c041703030105030c150c06012408222a0f06050a05070308061c060507090603111b070b1206100f09030308060103090501110702 66
    0x2007207030303506030092001c0940740c0821090140c00240e0010004a43c00307801100d906074000e641c1100010001c4a58000120000c1024840080c500400a42c0b81e114003000354255410403002948903a0340180039442000440341c040c00612041c81603c020b0004002500ca066940e00c0324142068030105c500010300280c03202c500c090900410707020303018490b40381281495078101c80d2040d405041c400010350b845071100c00d030b500504111882c100b0740c42e500301d10325a8610303140403414030310100303141c0111041c080709002003584994000d042d02c1c1c12035050b00d0a0300440c9c40e1702001c501801344250451040c102c85805030414013049412484c0110141c0d0b4660440c540c1e5014105c0c06c581c121034a403101d140301000b0001d0025004503040d441e000c2c415040d1a10300d41d8030816215a40d201c12081e21990b0045002c118091522803d0808810250f04224101c0030858400912240003400300501b40a03071341c0c0c08034500d40d10960086030b4459010000308550803412421120540080d04100d00c180101100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 328518516 1250 328517266 328517279
    0x12903070c0602031306061706070f02030a0503100e040f030f090f09091403070b060a12050d12110a080f0c0705030a030b0402120a050709080f1207050a1713 69
    0x440344552455a500340c0807003101c0e600c00c006540064100aa03102c0414644c0f00442c41c1445658001c001890038100b081d0f202c0302070301e400c181c402825981400180f070340c0120740a0b004000c6501e071940500d0103d40d030303680300341e20942c80340215000ba625041e0044204401c11484c0c59003560114001d80301c425041d81510021100d04129000d80b0400300340400c4100420303071003500a00c80040c0b1a03d2041590000340038440c0c6540c014860940c1c80745c540c4d80921a40341001080d0130054514640180044051038132096078414aa01140e820480c55a034207101e41446503014001c180c40c0b0780303030a5030340e848001310017045850151109800c1450080115000e44140c00450710701030742c0280950304001900ca4140d0041c0200c02d581034005408100245000020b001014807a00300d01c400081c0380c2c2024200100341643c5904942c103664444122520185800184000380c0b14900807401d55500803450543e040c24582c40000300f1408462084070205040d0341c0c0038086140034015a114040c0e9200c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 328519766 1250 328518516 328518599
    0x1309090203074b031e0204093503040b0601090f09020a02120c0a080c070e0c180301050624070204020d0506100207030c06030b04090f050105160e0a05010e0a080601 72
    0x3400f0310700c0200414410400128000c40360b001c02240403104c1c00081c40320760082130030b075031401504903040720190300000414178030000b03141580a00c500c801c4d003a508190320182d07514440604094502000440000c020783e2054802c480a08410080680190350f038a1800002e90030860151000d03005100c0b00115100c038280070344a00140903c000c00c1c100806840c0d04010350b000d104030ba07910303000c2c5190106528090b0208180144031105113075607140b90f80030b001e0448000e07003800b0510036414881070000700da030780c0300030030324038844001d83e03145469070b40c0d84a044148140c6000035001800450039081721f204950120344580c105503030140307003000c0d50030080741c0340c10f00c07070000500c0d0451401060200c98070984c020b51800700043e0000030414400c4e11002c1d0301880001c02114945c0d1140104034954001005001c5550014101224841015000204000c40a000300ca041245c006411002035490404400c024042e10b81510380a5031180b00c1d505100c0d0a14007141e200f4031907051044400714112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 328521016 1250 328519766 328519889
    0x2030708010519181b0905090d1b151e09080c060105031c030b040204090f0e0c0a050a090207020103110c1605121f02041e05090a02130909020307 64
    0x41e4424442000560705d05009809041e55824040640076002c6203a40241c0304a40c000d02e49100180b040c081c4910300249510a010820b020800880d80c000c00002e04e015920903104140795000704041c0d914000710042c611030030040001031400d0040b01802e00ca01040140700a05011044e12810381e221340601d80d03100c0c00f50b490403541c4444c081040060300e202c0ea001c81440040103001501e4690340318409000d035007601d40106c00b150b0307442000c01d02c460b60400144a5100c41a07825442e400d25100008803041074610415080a0300014841e08580c401c1d0b000d0310f120240e00d64016102c2050703294103a980d0103900344046c8500b08640001c00e20345880340c0002c01c040c14005c0249504801c3c0c0f4024118030301d51084980344039800b0f100210700d0403040c64a83e0662a10620042c605074034000800100d84409059407218901c1007143d60300b2350702c811804100340c41d0142404140341c1c28610102e80383c017034140c0c0010201226201001a1000342000d0603c20080c0c0d000f00729600f45180c0030282002c0900d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 328522266 1250 328521016 328521041
    0x1020601080a0605100e0103050f060f01050a12020612010803040e0915180c09090d140403111507060c0305041a0919030201060f0b0405030d140714030702030708010519 74
    0x120010790001e0301c00c2d00015407100300c4000740032401e503070f44c210600b606d0030030380044800d03030803442100c1050301d0200011036000c40716460503a1594941000304540c680180100820701c0842c020100035510f44204851107001d68003024a00d6694407104075469402500851000201c45004030701d00d0301000505c40e030344450030441407203245c54100201d8045803540311081c0d024000d600d4940c0e0341d0781c1c03140d50103031003450108040c085092003e04020b00a548a04420f00840000e00c01440854400851070541e81c2082c0c4400c4c10b03406400103482039500804200500d854107001004a84544c0b40c0c0180303026a1007082c07000e0750812082c0d01500c60280803a48407100d40c0c4a4019040c13100c000300c0c884030101e400f03400009946602d50b0403101000c51280c200980c40710000a00f00300f0307410104041c080c9049d8518200e400004503003c1c120080c0318240019109800300660141c44282c18004c5850444d4018121034019584004160103042c045410000042035060400c070079061600030746801030003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 328523516 1250 328522266 328522273
    0x117150601090b0901110a03080a0b300f0102160b061804060b15120609070f050a030207030504090f0c120e280b01081f0c1e050f0a0503010f050102060108 68
    0x2c05444041c19001300c00550304114480c24032800b402c80600c070b41c440c1d26002c0c0e40c0d80941842d110a00405951480300060300800307040034145600300c48100c810140740c08841d459085020001581d0303207001d0fa150000840c40d4800101040c00987d42d92810321060b100303031444001e55490000700421000081c9040e903048285000041c00211158040703036910340002c00d4900084581000c115040e0041c0095254450002d000d22080e0300d04658107079803051840c500f581b48c102c0481001021030040549a0050640103d20841018065070540d0040d00b41d0450420a650101102a000e030640210140100d500b1030044d48012005020741080740607000014440400c1d281c20003140050170750300c00300e010a1030307a00c400b0005003010348072030081000c0c00007402c1d0714005541410280301b000304004140c500c0c0c411041030a6070000c800600e40c1e088800040c840c094181e80944040c49503418240d4040c03c00102c034401c0c51381050185041e6061150004650b80e21800160303030303030340081c0201c0c0601d91 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 328524766 1250 328523516 328523519
    0x1201080c060406390605101e2106051609050a06021b04060306110301031a01030c0e19050c071103070e0f0907081b1206070f14040509011715060109 65
    0x1d034a0240e0f500d152094140c4603a41381c500e0824002e62000444203691038400707000e2900d064400d0074000d8110b00c0018440f1007842d181c0d00441c0400c6104201203d191244645603095040b0714080d80107412500512441c40c15000c40591003000000703160100d18258408111420b002c41d00100351241c50300109880003140c6501001c0c0c40c800309259030302076160b05001c000a0290300410001e500740c00d02c11612541980b4000440510b0030449a8802c0108001000880c0030031030900c049615000f08000f40d5200d1040d401100e1421841e18200d003030829050201c044a8240288012400383e10001e4145070702c5410551160314621070791203542000f0000c030701542e0300b030005250000055007c5442c40c41d5500102c0d4240940c1c111b0610201820009003011414080380800001110748060800c500d040440900758021103024241084080500e6564620310401201d01401c0020664465582d644950130f050030840c01d40301149000320b5213642c15108082c50002d02546058407501c4016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 328526016 1250 328524766 328524797
    0x1e02061306021606050d0e03070f030e1011070b030408071b1e030b0105060a090905090c0111150c0c190b06121506060d0216060e0d230c010608031201080c060406 71
    0x241007d129850341030104202d00c034009080e81e0400000c80d0b2003611058024a105020041010000c54101003400030305c4126a101c0d13a0080391410a031104e00100c2e944035107032070500f01c040303000d00d80c0c0c01031400e02d43c0d88045403824100e5040078202c40041e0f034209503500e0b2940d0840c1e1310000c5e9120003410340300640d0051180d460520b0107000800c0007454503034241540d64114009650701540c3d91040350704041c40a0095580c40f00504110f01d01c440010710761000352001c1142aa44020483c0d00c04041c0070901004036507090046985041e0340c01c2c13001240203440e09110350130790b0084e9810380c4100390440080000381800300c1c05404104600159a1140d520841071010a80c0822000030b022a030800004044507010040c0840c42030003902c00184400954108a1608101c1000307003003032003c011034a4903031410807030310580a088540016600e882400d160b45002d4041500302c403c442c080401c400b403000524101d0760b41240c0e42d2004540344080590240002ca100390b0294000080760480401c442 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 328527266 1250 328526016 328526021
    0x305041401020f120d0b0411090112110408030c19050a320307020a050402090a050f06070611030a060501080c070f03170703060302090604181e02061306021606050d 72
    0x108506006684620246040d00c3d403d14202401007402000c01044040c400409486240c40016041d6400c02c40f842445101103450701540000a0400c1404043e103101d07405160040d076241040700048503100d648640902d910b07500001c8509845200b0300d003031780359925039406841441c540c0180251100c01c00c0d64a03000078134480311242d110700e02031081e0b006103031f115086040f41030210400c019544070440b0744100040c0c400254019841540103001c04c2c409903503403000c2d0400b00c82c8200d41000c600e030340005c0820040d009001010305510300d04520000140ca059009512410500c44100201511040107441240f415a402d041c020b81c00d001c010000381407803594211050107400e02810030022402d0f88045c80034102c1e628000030741c03503442c100110300f84000b085800401c00c031424840140840c0e111401194549009024885034190b40b064001c14461206012a00a80855a201e111800e00b900501c42032003500014800c06070b850208518406440d82921110380e1524541400150540301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 328528516 1250 328527266 328527299
    0x15030b190b0a12110301050906070309110d0606031505010e0c0c01020d150810050606030610051603030510051c060506030f1c030506090106021203071b110f0d030504 73
    0x2026561005581d00a6440e0002a00280003916411060074050b1502d05410660b10108502030f80c100001e10044110100c3c8241c0d2107040c0340703000503020000e07042901820010200060b00452202410300070720203c3c0d08000180c1e13000c2c6400244504d1064001d0381200e200b40b0032140b91900c5040031601b023400c0c0e00010031000729440000350a102482410204032100103070101050f0640103001c001409040c8020001a02d411408001e20303d0f000f4007241071803000821107403203085039140c2464036038060f00a0301e00f1078031201c0c01003000305c211b440c02030004c1101b52181c103403503124220005210b1802c0d4006080f20800001011000300305581e80300003902014003015410300403240c84820351a401c02c4410034241c100100f40a14091461020b0201c80d80030301801e002d608041e00520400c0d800140075410040040c08455072070f0344003402240e01640e2400d10001d03003c003c201c244280701d00d011130911090f804450110801c18000200000c405c0e00840050115201748403c204951a440d003405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 328529766 1250 328528516 328528561
    0xd090f020612040203010f023412050a0909090f0311070b0703031a0a0e070c0804150203090310020a0e27091b030c0108040b100302060c070915030b 65
    0x200011080d80011090380020000740c401041d420704000c1546002d0007030044400704510b045141084a00300e02c50820881c00450144101502c08012550203618035a0355042d04400078111054003d5001400340e4090500000081c91044010880d04034511400034410b603c8001c2440e80181603500f07544002928841c00044d01a040c000940c1d030301c80c040104405171003607800045a44142d5140ca080c9805000f01034080d240c145000d0240c980234a010070b400075000d0500320004401c2d89088402c034811904214038803004084030003001600080502405030342142520805460500d01c10224060000c40c48000380085200a00b01e040c04a0720400c0070500c0b0980c60015100803031030201802080d10105420b5000c10f1104c44240042c0c9921890040700f1400380052100800000b002d00344060005045d20700d1020106039a018070102010045601030880d58540329030000d0b46440300380c43c1c40362204181c2440c01041c1528011034ad6a400e890b40301440310000e84469518081d40c002c0110083c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 328531016 1250 328529766 328529783
    0x30303091c18260304080a031101020f0a050c030d150501030f0e100b031c1806080f0a0509010b0306010306020a020f06160309080d09080406120e06010e13200103150b0d09 75
    0x3d00c0c80b0024401040a0000d0754000d004900c080d160050968000303690768481d6034410301010000401100448150304140d1038125103a0031390b519518158071402d00400901441e0050001203c582c140d000c07002c98000f6201003203000303100740c1e540058554100c2d0b28003d5400588060040c0c0010354407c01241402604032401ca48039154250840343c40030b42444046160221840745941d9000345410241440d07240c962a6420203240b0a440000003506a642041d22400007502e0708009602801c80d2a0000b0200c0c0c405503900d040c010300a41c00220b03a80010b000d00c2c0880c4001c2000040c7c3c150180d402408003050001c040349045005000c03501d01114603140c1000143c1c100c8002d40540588140110700340da40d0350385060300141500b00c40041c6e1000d0203080081c040054480880e50504440c010b00c00140541d44608504464000100c001420203903224002140d480780307100b120902800a803003c100c0c0704080d1a1404c4413003281d206512442d2000c01800c0402d101542003170954a01c54000d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 328532266 1250 328531016 328531079
    0x30b1e01141b0102030c180a0b030106081305061f050301060303020a0822030c090506042703050405060f03010e060d0803041e150b0a05120a020607020f030303091c18 73
    0x2d040c00c0ea072050301c0035a00c0040209003052180300e40070040c24181012554803140901c1c00511900074001442110180031004002030080c030000060130900c15840380070b517000d03441c0c80b14404c00ca04401c1d03810082040286800808c03d03003414071844c0203403a010b4006103c0400e0554861040b64444601015245500748040d107000d100032600801861003180307a440e6990030140ea04d0100e50000342001d1140d0705001030b40b40103502958415120140da6001d0000741c84003420241e4841c841da030b02258205d240000c0c49103002000c9070155043e110824103c40301501c9400412408845040d80904081c1040020034001100c1d07615139000c80761000f120890001c0c09450742c410120403588002d882c0394951001d0007082ca0300f21040f601078041202d002464145c030103842581c40d10040002409a100003544009564031900c0282428038001d0131203540780380401c44a5100d80020142c407900405690245c08054000c0c850302d080640200100c2d04080e10f0000074004d011028035454002c801d01c1c024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 328533516 1250 328532266 328532317
    0x70203070806090706030c080105010f030207020411160507081b100311030106050c060f0103080406030b010c29070804020d0f03050c01050a020a020d0c0209040201081f06030b1e0114 80
    0xb0344110072074806020b010303180240140c00d503202d40c0180c0040254003401801a82c0e00700c001d4051021a6190041c0c5031041440410000c01134003101000030200450400d441420352070050407000e1043d025140d020f9682e244241d51a028081c051711500c0304000d41c1c2e4014103040454290110003854007061940c1d0b0a502c6038000c1d402038005100180e00042e285015070010426290003205d030140c6011a580b41d83c071490403d000e2070003000c0030903803150010005a803142d074221410359000010840c0005440d031000018004e942102c9010041c00000561094050b9070101e1049401a00c80d03605002103684154681001303d404400b849000c2c450942389110034030401c0e2048001c03041c0140d83c0d07040c03504043c0ca4116084024400c005040340e190005890f40b2982940196084c205550262122004803459050f00c0b2803100034541585c1001400c96850703080b0001d07468040d1444040b0384c0c101c552000b00300e07054007a43d43c0800e07000705003103550180410040000c07216882114101581404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 328534766 1250 328533516 328533523
    0x40209010e10270b01230d0b030609010e0c0d030e15040e040b0417210a02091c0309060c020d110f100207031407030b0a110f160b0117030f0702030708 66
    0xc0549280f507105600c0921846051151680c031030f0f003d00341000552200001da114042110304001c4980001082c5070702c1d400c1c49034000c01030070b90300142900c8452501202240c000e1040c8841100c89100302a0720310f08908051140044042d0156684d240d18407000d41480201000740843d400703251400c2000103030714140182854003d42c415159040320f405c05041c000310140b491001d42400c11010000420020f030500f400c1c40c01c840c049601c065107666240404d10090142c40c1e1006c1d084142c03080c921034034003510b42185094a200b074844110550b25910129040b44a00400940005030086c2410104600502441c96040010526280c1448280102c2e454049008401c005a07124940902c2000980030400341a00d1102004142a0f40b031134450010b88840a01440c503b15683d40d8030440010041c0110341c5c1100e200080641e82c2c04005200c82c0c1c000b00301640659841403060004190800c0c0c000b5071091301c400600c001c501309050785079800c4460b40f210104a0349032282c500001140c10050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 328536016 1250 328534766 328534799
    0xb0304080d050a05010b090405101502031c201804110d0b0d0302061821041707050901060e0402090a060c051002030708160c0605100f0e040209010e10 66
    0x984080d6160000702008005507071002c1d100c64510f508140051000000d900287d07640808102c1d0049a240c4070342900010401c0705800807031210514007a80610283c0010082c81040d680c1c0c0070510f40b03200a10015012940c1c007580311040764000701e192601d5251240c0151400301942c11404c0f103411105800582142c9105031200c045602c0411080c01c5040c841c455542940802d549071b5100342e555540007500d1f80d000030614081d2404180082c043e154040180b020040700e0000c000d091805c42c00e660041d103810074410b00780d401c0340d04201001c1703108011501e00202c2e000500b00d01c2d2107900b005402e40b241e00c5000780300740d0059402e200a0b4074540c0d40010030402405184c842c01640d00403810004c0c1081c05042071101c90a0042080c482d125500c050803030350191000c4401103400c04414411609001c07880b0014107614180740500100c508810b03400e6049491980d080d081c025035036585000c42440445001c2e50000400c001000300c0300d1004c4809900000c0e00c0300317407000d01c1c1d258035412401e00b512 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 328537266 1250 328536016 328536023
    0x807062115090b040609060b09121903050403061113061103070204090609020405060117150d061508060106020f030d09020105040b0c0a11040e0a030e123909010b0703090b0304 77
    0x40e042483da80c1d041a01c5003401500c420441402004e0a16200041521400d8002801207000c07402d204000241030003142e0042c0030550401c442c942d10742c02c0c0140a0f812501081d07555a01e400841000e03c3e401c2c404072941106000c60008459181c04030644030f40c6100300d81801680000c02c070220069503540b0035001781c00e1013500c00081010080c014001100c0740108280e040c80128120b9009100c034000409502000300c0350f46407080d82041001ca5602e110010009046504151000c0ea0b5505040995000d0b68007950485181ea0380e2140d08994403400108c001046400070014070091000701e8119000780303801810a18507095441128081c00d5018403115800c1340c0140d00410704014a0340c21104050500300c0c0c1c1407148c4079050b4019601e8840e2118010b05011764060344240586910b03100c01840c0721804140d032800d100001020000c204882100140c8040105406422071200d07414201554009030076914280e00b05120f041e110362040000350103025810000150041442004502c5a0720 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 328538516 1250 328537266 328537271
    0x11060609041415100e1311010207050406141305070c06270302100c0203180405041716031b1205030901140c04060e0f03060703200a0509010801080706211509 69
    0x42480c4c010210349038940003080801c1d9403900348104413001e014120360707158101c400c201205010000603490260035a1003d90403d0410100250700e4001426041c0708440c02d0300c00030f01c4c07200c800701c4030b00458070101c60340c20119210503080070110305540c0c0720383c00241603841e08000b0440101c0c5050802c001c800300450041c1d00c12446500b1700c1203140a0100e989403240001c50030540c1040c9204d0704800c80501c42801203a4440008040c00b00e80c1070001e6a091031601e41c1a0790300c0c145012000040c2403480d055020031504111010f00c2c0c5000c00780d12001e541c200040300d00c0d40e0383d4140c0032035085c0d002508440d210341d214400108400c000702032690051805c003540d82d544038503014003c0c00c4070b030000c0840d0b03120300000b52450071241c5000c2036284c1d20042c54940000e094400d01d0241941541c1c1c0a2880c404d200c01041c943e00c80c640010040c00100026214100a0781e07031920f01c00d0f1b80b40000d00460000600420303606a03e11000180301d04c0c11a0203850214103c00310045500400070ba6034400744032140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328539766 1250 328538516 328538521
    0x9140f0a090c020a170c1501030b0c030a0b0a0303230403021e130204140a090c090b1e121e13060209010507061a09100501050f0901170f010e0711060609041415 70
    0xc01c100b007c00300181441440c4d543c550b00d15190040071100050441501d000000b0002e05003070b03001c0d84440008280140304052550303d83c100100340e1213504440305510300d0710801d0f1140c1c404104040d501100e82c01440308140340010424280f032a500061121340142e404a042e00c007440c058006000548100394074084042080c808101031003240340d0000d68000d00d03009604c88110b900803612019603619802055403001000341000c141550402d00080114010803074940c2046400d4009006062101d002111441c50740c80e540344105c000e51b1030600813003050120100007100c640140c40e203407005041c018141040c1d43c6079002a00c040c00c02e800c140b121441d04a2032940350061050f50003600b80203090154a041800203003181c820402c080704104000324070144113038401c424960b001041e801124025050900700c0c045442000c0c003c40c0b90002c01503001800341441400c1200058a000009041607120a000e0100d01d1602410030380d44503110b08801d0315110010000d503010b01e1410000c2441e2031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328541016 1250 328539766 328539787
    0x915030a060b07030e0405060102070803040f090b0328020d150906050f06030c0d0215121603020a0c02040509070e1e01170d051b0a0309140f0a090c020a17 68
    0x840558014000e201c0e014080c00f400b01c0d6009442048160042d1400a03031030f1103180050346031002c198802d01e05840000b40104001042d00d207100115110b030305081c00061155400c00d9111160b0143c0003142c4801d440480c214601c0340c0300e0000c00207002814900349407109071551240408107180e41070070584c450a40408118991041c55030025610341000f01e607007000c0000035124180a00c0c0e1601c607221000e806819541c80004011121301490f1006a9408a400340e0043c407000840c0c4010b040780809540d01003e50280c0210b8181c8038407070703540e095810120780c2008024000030b401c2c24075030b05c01d608011502842d2202142e02919031009514074202000c007071901030040582114044020091500d040800000341260581c400380c18444e440e5261502402d061038104d00c102d06840c80b03503903002d20925820076002d8003a200c001c0d0313000020420320800d001044007425160b5801080203102000484015803044200416070b00c1540d000b10308a4a48894008400c019960301090025411a84 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328542266 1250 328541016 328541021
    0x3171b0307210c1a160905060307120e030c0703030f111e0109050601030c053d0216151202130605090406050a14030c31060b070c0e0c0412020d080915030a 68
    0xd50301842c181b910542018041905400040d101e0000e01818000d03183d91140b07245c214101d144240c904803512100021105542c44406101c01e8010070903c4078608526807181280c014481c400031700900c104811603e1828182c1403500d04001c0d255a1079485000140c003d102540c000c6001d08804000ca0f401c1408000d0320514030050b0790318803010010200304c4502c101070130007100b817990180ba098403504071000343d081044007100110020700204000c1014000d01d000040b46440f43e0703590004001d410b0981104a11519010040003032178080c040109501c21303801008407240c0a000851025135402c00301e810150f00c1d03082034a031406802400b0085040c10132600400100444015100c1490035507011348042e010f0101000a442e2441800303500c0712150007620080104241140c0d40d071800c0c2c02d0041c4014402e00903112210710210110398246104401d840903030b44c00154480d00e4214603801c010510885a10031205510140800d49007030ba01d010006010f900c814084e1503691030075a024004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328543516 1250 328542266 328542301
    0x50f0f0a02120406050403230a1b2001020f01060603020306030c0603060d0803130f03050a02070e060307050607050111040b0409050105031f0c02010603171b0307210c1a 74
    0x1005071052003490350080c1c82010090b000754200780005001d40315820100c031a400c810100d0118100c1618900030841c2c800e4005000c000342c0d583c0e56000e03d0300890880f416400c5864400b40c0355041c0c045110561110300c58034a50340390b20500468102040303214680e401e44003030780d21402c086540442040034908080c00355020003101200da440c40d501c0c1000001d0300c0d5606401c2c02824900700400000c0c1c80d280c040b281c0c1250304d600a181001000e400c2d280013030859210854002c0140210040020341100f00600a0300800f002806000e0181c01c000500c070451700074650540b4651f4a818840d03c212420800400241c8541c0d004d86139128100304560040d144107a02c114001d40c4403140214003458070042c1d44080700c40c061404034501c440140124090041074002520364009400103910449144008000c03000e90050800b00c071640500c002902c0340521407000c2c00c001170010480000d42001c2210204150107820040780100494464a0303040b5200c242c5c4041142281042c000044c047c902681d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328544766 1250 328543516 328543531
    0x1a040c020d08100303080106050307031806061d061003181704050114030c04051c050d120b09090d05090d080c06070909020a090509090106091a0a05033c01050f0f 71
    0x80310b84c915036000703095400500c951801c00502002040c502c52007504002d907800326454444d6088003040c1803142c018019440b501003400d0764240310000c0d40c0003240d81e0341e100f1180203021001c60805124158040c2801d0400c15004d48020782c404400108240b0b441c00b110004d95601e10303215804c10001400300901c0c144041d0040e50140108864094000202c2c0c0a0740c205495030480072414400001c44207102d21401000380c0103898034404826408960a04280e00a0005200d0440d44c0720500066002c00d0321f40d80c1160700f2500000400314014402080c42400c003402401250030903803111f1030203400491107900a6044802071284081e88000e222004d09031848007186498603000025017250098841d142c0514407120014058010079400301005089040e410710220004014020402100d8403c161180c020f00c03001140342d060000300c003101c1c11034508032189888802006178480003039100300030114006d01750b10040c500e2000e00500c0d020b000912900091410a900440c00c021001403500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328546016 1250 328544766 328544791
    0x32031f1d0a2a050f060708161e0203030d09111203070501050f01080a021002030d0c030f0f0c140705280b01080d0f11030c01020403031206271a040c020d08 68
    0x4040e040b500700101d0046030821112080f0302c050610204000e4020800003031322650000c50081c406450400d2400030301481007007038411009210042d8a00c03244140710203034055005120101503244039a200b210068000e14920041102c1900011000500780001804980000c20b1200400c002406042d42264803c01d0412880d03050148480e034820b03098070007074802c0c40c40c50a800b013050300030301c1100c3e103680c54200288040400800090090210100e0b5000032034030b421000c000c2c2038a94812503d1206455440382e84950410355010620380042c1d2064400d402800034440d80d00042000e04014482300103400d00c800f05140c2400354201e50140c0c0404007980003201040300640d4440f00c1c4031440039280c2000490b18aa181540e40341d03001d81910440300d984000703004018141c0100c0000d20500340e402d0b06010303031038aa4054101180c5504021400529101030040121031395411051484141c0307090740c0094212407000070141c0324160907a1000da04203000c8981001d501c4001142e001c032072068803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328547266 1250 328546016 328546073
    0x313061d0a0e060d0c05030115030b0a020306010f0f0311070b190b1f090302030304030501140106030225031211180603040b0610021632031f1d0a 64
    0x205280c901c003e090910900d810322401080000c1e0407018005080080d00030000000701c0589068812468001514840d00d42c00008000f60124001c0f01d10a402c1a510301003034003082001981c8580e01d03640780e942815194290b500e00e81c031a01c40581803143c000c98042d096414084e00260841d43e4003240245a6030404040c0384054075080d005142c3c21006000440c0d509981c110308480c40195600000c0d4140000540081441415080188028040305201406907a2044144d04901c102003000c01c001c107541c400365600d034402d48818190700c1e0213800d100100c1750313407205000100c0c0d51f20fa44100113041d020645501100792070440131700e0808203407921031070f50030680c0b40e81d48080001052644980301c01d4038007801d520310a12082c40c04258000d03104001c16140e00344c0c0fa09100359840041d182c1307082058103029440c08030303045518000001e400f914100d040148002100040030251b101c0031b649030100d0381010601640712151091140700030304206100e61406050701000112400c4852480154 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328548516 1250 328547266 328547279
    0x819050a030b011d0108061206130c0501020d0206060607240f05060f0604030609081e09010f0521100f0f0e0a0203040b18100f1b02011b0e030313061d0a 67
    0x1807136081d03041e090070a04003907030b201800511582d000106071103c0c0d005032000e1111480500ca003404c00d2500c00d400d64661507440308012a07840492404c20f000585c4850042000b6041c2100241906d5001707501389066a048860601c01e444c0340d003150300d056103075181212100c1180714441c081d001a021101401c0304c1800d07800090950159000c09010b0a0742c455600c1c007086a0311080362848402c1c000d50f800303200e2034a0001a581d4000e01d00d03090214019956420403648200c04440900f00c020007444459684a1040445034200624451103588580004240903c4104842000340030055005a41a062198041c01c000c4081c04086a890060040c8000210400449907102c1b07031524001c401d0044006016184c860100c0140c020a450488076a170303026aa90008640700302e9100c0d00500500d1216001ca089410a040c0703100c03001000c82200302018407a5621803510301c4c0041c1124102003100020032141c10041c0c2c06070012982103025600d40d940045410020900c0031100c0d102828907004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328549766 1250 328548516 328548557
    0x2010f110a17130e01091413030e010201061809140d20120d1b1713020102031e0405030f19060b0613030507140f15070819050a030b01 59
    0x14001015100100c282d001568540e02c03e80ea4a0014120b80f8041d5581d12400050b0302c0e803084c001d00e14600d0618401c2c215039041c1c07141440c0154580c1c40c0301e8540c900c05031800c0300e09140d0501a40d0455483c0c410000c3c00d40582d52011403020035014000858550300c0c600781c820004002c440e02c04a40056001da10507503080a0304034030284090442c030500b03140c401400c6041c03a04108414030460360119009031340d0b482c01c2d8003480c54525580740440c00241041c006490400c20600840606d80480c80090901c3d8610311b80020820301c1801106c5c1044003441f41c00c0c400390b0444500140e54040030504001c4c5203401c102d8491910b01c0f100103031680304941c0034985914445030001a2031551522a82d030056146d0344211011070b162910b140c0d03006603c915000d61124001d200c0c10000000580701c1001d28580030b6480503000f88018002400b000c1c0c06c0c03510040341d40058209545049060280c1c401110302d00c80d061740c1051140da40c0541e184c1d110b03070028046611208205041003a5005204036100909 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328551016 1250 328549766 328549783
    0xc23030406050718140117061315050904080702030123010603020f1c0c0306060e061204020d050604050f10060803030a1a03030706091403030405060708040602091c02010f11 76
    0x18001044683e2020300c281c03081da00d82d140f82d04203094000d000080455802000c1d100e208070136a10348108604003001c1207441d4500740c41d583d51100000c503041007008150303440f82654280d40c5c11003050303003aa40c038001f4880b1901260b0594510f480003407100d04518017840b0b84154082406503a0354521203229004c651400305004000c03e00d0750006080941d0150002518880003402d1a82c0901c030307040b642e554000c0c080c0c0040e41070200c6d062000102e0020701808a00e100301c030000e030586090821049003d110800040d02c2a81c026050034020700206d4002e2111a100e40c1c0500000c0a000010101c33652400c203c140c45101d1749071810748140803c0e40c01100326a0465022040800d004600c030042c509a8030740002c00341c3d458030002841604000c0c40380c204d49802c41c083d030907100c103a00d00e1050040d100d00c0119030003002030704090002102240200c100d182c00900441c80142410b00b110701180000881070701c400700c7c1144040660045683c441c0000403001e4082ca001d42c00c4c0c3c003441500e0b980d40c0008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328552266 1250 328551016 328551023
    0x180115030f050106090c120b2b030201060501050c030a0513090204151e08012601020c1e0c090c0f0c070609030506360a05100203010816050102030a030209030c10030c230304 76
    0x2d680242c00d4a643c2c4041161035200108851607490f000c0280310711b540e11009d10300b00d0255003402c0c40018030707600400603a000d020f04a000785152404501c0101c80d0750344626503410b44c00d400c03144086082d42c044c0c03010700041c0c0240221186080c03074880c03001c0c2c8a8800b10001d000400d607180610120340b5404803856044410903480e200f40c40b0400500c40305000d210750010f07546ca40c070104000020303100004440c0800424000001d180182d42da64440d00e070b0411150f10780e00004450701041905c0e03191001041800d0110040f18140002c1c40112804c180c2c02d6030107240064000c100500a010040c090103030044004a02404102d00300d08a400610302c0810030300601034401264201c801c9814800721102d582d00600340c50412503802030300c20080d0130a009280a91046a60b01d00d85a0301c00b203444400c2e5103058001b036080500c3d000e0120084c0d44007884c09038040c0154070700c0c00c50719120103042c2c80c0b200304140c9010802144111000b02000654010381d0040d010001048942e01c201804480d080f541 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328553516 1250 328552266 328552271
    0x6180303271e0f0203010e1c090803030411030304030c030615060809070b16050102120103050c0303210606070501020a0e0f0406030206040504091a0103050708060c0a0503180115030f050106090c12 86
    0x294107111007961080c8a0181d00741d401d041000a403034401081c5d2307030004100ca690b016243c040c4400d0440e20010300e80a03604241e4410000301340030a82d4141844208040142200e02c0c10b07440c1c0d40d913503008980a51040ba940c1d42ca0303030206080c4126400e1110302414281c0780a040c0c914011810513515000c80c070500100040004d4054950071036000d080405a8102c8029582e400749000c00000480003440251414020f0a81c4030303000749400700840f050040307003071792000f030202030803008500442c009809568410070810441c2d0028400380080c040d0300c04c180c0c8a1818812a1006003d5038231041c20900d84143d107010f01c10b100581da6030b000d8034180c036030541e40094105510700c3c0903c51642120150701d6034954a000020810000103040000c3d52070042c180c03440d079118440459518002c6040220204400f400080c0103d40407815070209240301d2000440d00c0207000f125030b070b08920540c2047d680300700b04095000c103000e8240100001045802000c01101c203076034400901c010440300c04c080d41c458 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328554766 1250 328553516 328553573
    0x50a05060609011202090402040b07050c03030c071716030302010c02060a1b120621150513110a0b0a0320030402010e0d11030102030a09020f1005030109090618030327 73
    0x3101e0b815182d204001807c2150303141e841e20554189500035842c01c0303401d0302c180c039070b207905074100442611003415407034008002007400c1c410711920110032201641501d101e005c1418141c0d200c04001e6100460181e000003444d081c04072002810150000c001a0005041041800d100c5680c070188110390081072401d00c164103200380b00f580180010354050540141c013520744419661403c100f0b440c4103441948001110701d011412a800c0d03032402c5510300d45d0400c00b841494082000c0e070900f0718200d1801052080082d4640505802507000942c080d00013a0f640c4a054104600c44410321010450603003045040d03213840d5000030000d00c0c1080c0c846020b1021103000004001c5400d00030071030028001c00035500c4e864450304181c010200d504069100c1d40f000c1c02014043c0c00c1c40d000c02c4214150998919107141c3c03d20080d40c02409000204448281c0c0d0b030380030000310f0001243e505103264030941d408200150402c8825464942e000c4501c5140070202c1c0351b400c0000c40c0c01c2081d4040d021010216180039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328556016 1250 328554766 328554797
    0x108100605092706030615090402100e0a091e0203010810090201020709110306040513020a0317090a140a0f14100516140d031107020622030501060603050a0506060901 73
    0x500743d000d0162100e240031443c1140d24000314004034801d090a40407585135030758610f10040c4031491584c09541042c0072102240c01b50800c3c0300c21400d01e0b10035092220000c101080890000183c5503c403807402603950012001a0440700002541501822002c1d41075504160000f80c44881c54640120210ba44209203421a4000d020000c02400301640410456580c028171a1440d40115203452003945800002a4070341e840d8550a40601e0f0050203a901040c01c5075075400c19031b08420516010302009111013861903803402903e07030151070a5800d03406914080414809461543d40284031043c0d0444401d001c2683e000507580c15040d0100c90000c52000c1a5405407103d110b40000d070000b600c0c03504040c00030700401915120184000b00c04030395400322040c00850448014962200c042c6008000200152900c2000340c1030305902104000c4420302e0414220032190380340e83c000c0300c55945801c001c00c40e8a805105090b8044000c1806100514102000410510400d0708890602c00018228a0314 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328557266 1250 328556016 328556029
    0xd020f04090f02100207140409030807180503070b040302030f030a0f050d0207151a101d0402040902031602010b010903020a05010c050c100e12120906030a090210030911010810060509 80
    0x2c20380181c038900000000500c02921b5038940c1c080c1031101c01076105601c0725803c080c4500c009058140c0e492403941d4035001c45c1100c02804000300c262400301041404191a03500b1301c005801050210442560b03140f80d4410301d0309114491250943e0380d04207000d504440c90300481d80e0070585d5101c0c504070799502a103c801400a0190030405081c0c800d0b0056038a000a0307066001000036000c803409424146101e01c00c0007034581d041104200005e201030546032895099102d06002280300500244c2480e8440c80e0342d1703040703030421200351128400c80da45125040e502803041c5e0003003441c00e2800c54083c504540200d40b01403601e20805040144040c41a001e01105020103008140c0003440808540722101c801002c1501a8842910036020000800421500020f0300303816540040c000c1c609240d8031004024140e040100b00109003900d4000c120300582c0c1e107080d03400d1174090684001071080007074180140c5243c100301c00c050520080b003083c011301c180030703860110890f41a480c1542d82c40102c135011580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328558516 1250 328557266 328557293
    0x40e070c0507030b04020909010507050f1c090807020a2103120207050f0d02101803030e100915050c030609180c030303010e01080d0206131b0b0d0504050c0d020f0409 73
    0x281d801a0440070003080541364030746000d14022103c40e41c81c1d403241c501d22402ca690548114010a80401469019003d106c0c080c0905020b150040900d4403051148481529070b00340e0119034080f800500761045181940c080000341000440b0384024030300c03074404a81c43c104860009000d2048003040305021000c0e54040740c0c07001e5409025582c010114400542e40c03400502000c038090301582c0d210300080c3d1400d1190401c8030742d10079403c409040c201d480507070042419181c0800076000f40f100c2b0b84a590007500a00d04024803485184003444281908003088400107845000d9800040060001a690f8600d00d641c01c08814070b90355901c0020500311a10380300b04001718a800d408040000141031004a2919048a0181082e41c20b03240503100308917201d02c8200c842d08440c1d058a03050401250041a600c410b448024540c2c3d55071603102c00c000401a00b02c5080b080191751103500304010840c0c18020141303036940a80744c030b1b520b51043e5030005030419031251000c2c4c016030703840d400d07407040c0550401141c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328559766 1250 328558516 328558523
    0x5120906040312020c01020607020316081e03010e0402010f0305070c060e071505130f0807090f02120103200306060d1709040c08010f0803030c07320703030206011a040e070c 76
    0x20100711108000394852502c0ca2046001d402380900151000c0e0000c001c580903a03010204251034034001c0c1d0744800041c5c10284902c6c941c4824441c1c206c1c003441ca40c0b8000d5028201d040e030f1040e0035151034800188880600f01303094041500303080c00c0c001410b030420001c005480d40f00501240410701c0081481c0380054030f5200d001d01091941a140c12180c2100c0145502a80501c40d403a407103441f41e03001b0441200320302c1107103100d51044000b003022188590007046201032801015140c0322a031703849852600b1082c0c000780c61500d948030011480507a14030007801e43d48804d6018011074a080c4c0002070200c0d03440400030700650103401070928215090001c4910310a00103104028600c00c119004080b00300034000d12880440c4040301007020320001050300d1054890103d014035000c2d06554510104860f400c40048400c2c01510340b04894071404540030008032018010b040240c61424001e03d0400180e0104582c046003180c80c1d21400001000c0f902541c7d201950b00381c10341c9070800308803284111080c014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328561016 1250 328559766 328559783
    0x10f1217161514010b09030309060a0e041505040e010614060d020c010c0915110c04091a0415060501110a0303090203070905090d1e1e02030d02120609070c051209060403 74
    0x80888003a5403007951000300f2118500126030302c55032980701d10f01c00c806c01c0d580c1c164418401418680740100040180c43c3c524507040108082c0140844c00380c403504101c488025040500904c41d03810f061151a42e005a40b20013800038600e0250000303924410b003d0710b00d000d0200080c0c0310750202c1341d0b50125020301c0e8001001b0403c500701c0c090000c200c0c0e1414040e80c0216a402020681d4481c03241c44031585090a01c405001e0340d40d0b1307180c100800bc0068460031034065605032007440c985490032145078441c50145a0041204055284117422100260085410300260321007103c01070f200004d0006d007042c0d050900082d81041030000030703e007a50a43c80001d06030705050030800d4400c4041440c80110100b6216884521580c21054140e2134040c280c142c0041d201c80c0103c6150345906c011030b403940009005032403505a40b1039100083c1e901c500f88405a400c041010302c8500d0401d1800c10341d00c20303040e01e080e000040d015511251a0300803220b03204040c0a0101d90082195104001c5500469010800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328562266 1250 328561016 328561043
    0x30f06010e031f05060a0f060503010618030b0a0912020115052b03030c0e0409020f040c110f0303060a144f060e060f060708130e010f121716 62
    0x410380039042c11505c103801240f00e003800059000000c031302901661048e4441c181503130700b098001c481200061030035403a50302c40130310000302143c4031140381c5000c1d008614000c60300100600307114000000c0c036030a15085a241124600007201049903a81c1920022a844041d1040742004e401c020901ca0034041c054249020007002090b0301944501d0f444140f44d1900b13096006d02200300000c03501c4d03202020390409a020f440c0800ba140690080d41c0d910b80c9414050010510040754624010707208411280035070000003031140e42e10301b03d20742800412420300c8140020070f01c407000c108050f0f004852032444072030300c0f103500d5101d503a417400d44c082c0030306040c0e140d0800110180103041642d6071a000180e0f02d61604002082070300c05280780c1031003490080c2c000340f0741034007500600459a000da20140c80c1640d09014201000c203403540080c0043c40b0301006072101c1c1d41000101c00d00d81030141c0c0410b1151000021351000205008001100000b07842d040b240c44069090f5040903100c02c0d5a0000d0502614148 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328563516 1250 328562266 328562323
    0x1080a2a02070b0909010b1c061e050a0602120703261501080405190c0504151706160807051b0304060306080c090c070f0b09010b0f0402030f06010e03 66
    0x210340c03844080a60884404682e03401044030b0500c503000101340c1241c0c11400510040170720b2802001c2c118203905001c40146004000e0000700c1d40c160304281c2910b8103601d85002c052400945c02400791008032196400c03985420b002942c0c03454540c00d0104054404106441410700860780021064100c140c0901c88003d202c0094440714401c070791320350b10403051802c64103a5500c1162010710480d48880204078582c82c3c000041301d1400507002c02c4509143d038200100c1d203903d80340194001460b01da0130303070540b29040c000654044615660510032541c800820440b031210b00c0701e0303041d40440e55404c2c14845500c81c44401c45940c170900103800c400313030941005054072800000042c000c64005642c200b1030b058449400c15222050486e1459001e4451004039800448200090000c00e00c200076084031981c1030707510b68415485c200d070388440a95644058950509181900d2500a0400c4a00318610b03c0d00345d9804a2091014001130304000c681c5404c181c090b1030800c801103014102d45040480f8051810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328564766 1250 328563516 328563581
    0x1150503071716060f08090d08071d030328050703080411010e0315041101020d0203030a0509070302030d051309020f071202013e040608011a0f040e0a050f090a0201080a 74
    0x2008000010741a100213041f03148042401866041d0603138030300b100c0c1c0d00d030400d0403a04415200c1c801000b00a0340d04c0f030402e181d5020001480b0145040038a07909041e244429111890700142100c1c042c0401000b50800007a4401c0081d980f00d680121009000001d02e801290024551305000b0340601c100d00c0700700402c0801c0c0014610882c45458a9080c40110b18012a100e43c903001c2c00001690090010605c8440c264000710340c442a803030708540f01c0b1130381d03500004d00d0320010b001445c0105d240090f07288508400004540c0203400e0442095290140041c1400068440c01d00c01400034010842e075141264802c5d004007440710302c242050075001d036001d0000100101d44140869090390854a0101000b080f40300391800c0300c040382c40300909a0718040c46200600c0c20030301030804d911000c102d2021001c070a00058800b9080e03c03800c0d1440e62400b821260100c960107044145e2416060041000d00d00380050f07103003640c0c0d41c20318001c84140c80c0c4002a001428001d904180c40c07240508600c00a0501c0342e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328566016 1250 328564766 328564787
    0x9180c1805010929030a08120f06041802010513050a0b1c05060604050108090a0c090203010905100506090f0402070609031e030c0206070516050d110115050307171606 73
    0x1020108101d9aa0380c54003000c889800044c0704a61540d4010008001200d2000303010441c009000c0c0c41441145940c0c000856001d50300030400c400004090000045000028643c4070b02e00303440401048440c00c110000881454000904100b000284005086140c800140041101400103403505450303090f2440c00703801028003081110025028100030310f04034002e160088002805a0340f40500784401140c02d008010310428503031048001c5076000803000310009004041c4030f000103031a94102070000040d1540076005003141f0341405d00030320055803a0012988081030488803800724900c4500482c0185c000c450700504058074060317aa0341859080081d110030035483c003598038810001114241e045071081c0503a0001a881280000d00e0300d4040c8000700201405000050030b9035400d81e881034a010203401580002800c03c0d481c50075024400d0059414800c4054000240c1e1410200400d640703050030700c92030135078500045448e00314031001d02036218060100400c0ca48159161071010340082c080d07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328567266 1250 328566016 328566059
    0x211006050403060914010507110f2802011103030f01030204050c1c051f03060b03060c0f040e060d0f050f060a0c08060609041503030f091505090415050301061217030f0109180c 77
    0x41e410743c20a07008001c60302d4460500003200cbc030b0302052a50608103c2d04002c10004a0500c000c849041410b186c00300081c3d0320030885c4514aa809606501c140801d0703c00c050000a56a842400700304015104d039180e1828481441c200003801da9030740c1c48032400b0031207040500f206601034a080441442601d42094101e450254222000d42d107030400f46000a1060500800d02c4610601c4140710702d0381480e103895008a001810b018030320326261114007580c0304a00c1c003121070360b00020a80c04031a01c18452254049040c0074200a60603404001a044180c02040580304100010b96805540d4451303100d01c1c03070710324078824a4540355102d02e0090700141c10307024140f006c0340101d5800180781d00141f141c10f418000d155129800c0802000600c80500701001d0b0004515030175803000309103504c00344280b000600031690a24034040345800c00301418081240c04482401c4100304100303a1190440744181150000600003400d95011528100795400f100b070000c0c40342c0600d210004a8040705114410041035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328568516 1250 328567266 328567273
    0x717010203040c0e04020112020901210c030c02010e0307020108041a1807090917031b0a0e1e0306060d030c0501140919050c0d0203010b040221100605040306091401050711 75
    0x13214001c111200104450003400120b50403200510f00e0f4684d0090b051000041c107000c00719800c682c0c203500c00c1c0d5a41c0890981450398890480c00c0e860b40c180541d20b001400c81c002002100d205984460301c1c0e1141886c080d0500810701d01280c00c004040404124030014042d80c0701450a001443d1480500d1580c489445032160780000b14409469114248080c0e512488401001c0c4011807002010f400003407940403074484c81214001d03404091402001000a59920501640b0340c000800c14000c0c4c11444054481d202c001a08206840008036644c1004040316407004043c9907150469461120700f50081c055420b00445040c1484500384090040c0204c40698031100d02c030020205a0608100c0301a0450b8040380c40e44a180c140141103004a50014001040c905041c2000c54103903440381102d102c001c900222850741c0480160308154006540d8003010110618140005000d405a40406011039689610190401032083d91546252240c071000740400d05d013041003c2e06921501809852900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328569766 1250 328568516 328568519
    0x1e21030309010203040c06111c050733020412080715020d06050f0108190e0312010b04090e1209062107020c04050a0c0207031506080633030d030e0717010203040c 71
    0x41c007840c1980d403241c40040044c01e0913400d0f81480300c1400d00327040c100d90070700504004510100d00c040340c41042c0480b410400c5005800591035051031552002400001c2504c14030050100304808080585c0681d0081201900d0315030350700380200008104015014000c0c0b0001f081e45000c00581c00c24004c0751000c4540c2800501294011340d01410f013203508400c0415801c0b800a031215040e03010122840b000400c407400e0403001d40440708064801c1e0001200c0d0080480c00304100109805081440700140000e40f100d00c2080304e14a810b170181c00d45981c85002d000c925041019110b08580d2400c19407240203070524102114080c0d282c001001800f40201d00301b40018051203483c2c02400310200c041e600030607840e4616100e02a980a044034100071058443c1d4001900e40410412030303002d0040c0304010424060300341203403581802c943c2d003400c1e00f20000c48460101c039900450b0041c02c1090030708020072070481181e026424020030340c100c001505141d040d9000b6440056010307510035449260794100e0301d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328571016 1250 328569766 328569779
    0x807050712060f0606140a0c1104140121030c0f02240a020f0106080c06030903041a13090510030807050a050706030b090f060918070803030a0e06061e21030309010203040c 75
    0x100f00c0403d0030000d203c20801f03246084d2042c032211045074084c0701810003810801000405540030140859525800e220040c80300240c00c52680e0b80500d03032007140d01512003160790054119403400601400c5003118000c1d007415511902c0148002c0e40c0e00410204147e405198102000d4101c80010030040c868089500c0200405129440a69644030006c080784100c00082080c55440108000020300041c0000100c590440d03030a1005d40c202000703440e89602c28012840c00409172580304103503c0b801c00c01071006500220402c2c10035240c011405507500d40f00b50504a02d415501080207046200d01e81001800c02d602d50b22602c003045c0d00b05d80f44107c1d42c44100e120041340c032094480c00c4c0d00c007007640040340411146c550812801042c45058501d0310f65200ea800341903030400ca03039035040c8989408261549480500c22194017100480398507001d0307401040c5c5e503411202001440c07401418142e0991585010203040d62500311601c4040b00d42d01d01e09070600b58081e401c19141160104c03544540407409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328572266 1250 328571016 328571027
    0x207140c0123070204111318110301120218070503060a091a0906010c050a12090611070306020d0603050307080c070f18051509041a060303090303070807050712060f0606 74
    0x10601c0d107100140d04046101d580c2c030507036010f07030380490b4810f1b070362141c10f00c003880000f002e80340300b600103035008200782e02e800c001070300c060380c03640081166a05d0718041d0b952800c050030540741516107648499a19403841e102058805410100068004884c8810000700e654060025841103400b611709006055540381d00c0701c1926465070f80c04e0640002d440f00c6c00c10600701104442e501810514201108808644910342003600b510800d0790103070782400c285264141c11001500c01064903180c044800000c1c20700e8162142d003240070051859400107640b029000e0107811540245030081d0603250381e2080b601d4445042c1c0c0c003250b03680145006010b000562001e1900a890440d0380145250b220203403101d03050001880000d00060310114800508a585e84624101511851150111000c072645803a82e121320844000c1c10ba03440707544104804200f03524017009480759035522845081d150b2046103070090511906030043e410101e1700c4803400003403128a80244454403c083e03400c000054954504035072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328573516 1250 328572266 328572287
    0x24090f0302061921020703030510030b15060f0406090810020301060807121104060302030a0b0a06120515030109030c03030b01021911041409010609050c040602070e1003060207140c01 80
    0x1408001480780b0140c0800c0d44401c90821000c1c1e292032010081c080701314580d004c5108044240e0903502240c0c180c10550584a955003008006108583c12450b40d0b0310504811001820005400c83d1201d004041d40c0b6100142d60000e2601b19281351a55203540005010742071a204440d410300c900080b000764039000c0c1c404c4905942d107940d2039074a503564600040c0ca11032060001c01d01c800d0340e51981c2c0d0f40e132181c1c500c0141018010740d81e8056a24240762030306500381d501c0550038138071400340700c001045401e0b003041c2549901c600c0854040350558406841c21400302c5500040c5416500f08041042010350200d2140201842500c08104d10400a4012640d4070f20400070408103180b08200c4002180301c44000c2d0204e1480144080307144864040c940720582130698114132113130b4443c2000e02014415005580e409010350a6071400c107854824000c0d07644400c0d02ca020800050100450040104134a5a201941e0414404d540c0c800c03080c46d110440c400307030001a00050041d41e009250540c8646941d41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328574766 1250 328573516 328573519
    0x30506061207030501150501120b130f0902031e15060607030c05010b190812031603021608071b06050306010903140a2a080a0b0103060c0924090f0302 66
    0x199980308184000948868000000c51203401c0c0000300044090195440181d40f0b20386024003280f030f110002d09048140c2403c1d8001034280302401d00192101208890408640800850740052513207440e0f00400c005a4041c0d010f01401c6412004440060548030b9003040750800c40e0b00080840c128a404054203540003030b4419400c0050f0303800710380306030341d40501c05020b1400003a50100420005a8900c081c104400d180000204100610142030111030414410a00c0803881d41c90204c0300390440805a0010b40241640480d000c0c401c507a014010400e800c0e030100810f0f584040780c1c1820543e5203104250361110303160501000c00e44034400d0060364014401a1a074070b06103825a600c2034101f911118651005104d401500001300702030900308480f05804804c4926880054403219400401036040040f080d40011400e400049111461504503604000006000d0811240480c1c5c01c1a20344d01803030080d9040c0b00c82003030301c050540e440482903440d91140c6030805d5403031140500103404da20029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328576016 1250 328574766 328574773
    0x1081608071a0d0222080a0b04080f04030203150a06150c02120c040606051c06030308010b0a120c02030909010f0f031104020c010606080907050904080f070f060203090f160305 77
    0x1000400d040c0e464024079a42d880002500306524829400c049810044200003122456100000e40701c203a01e8013203020340f00001c043d01e02200c980d203810351403402c041c00c020050800046c080c500f203c048030a4401466004050701d464401003144210241c100342c0386401e0302440c0030360000d40e01c4031001844003403444644a04108401c283c00b0401d4100740c904069510740540c440800c101e64492040b40003505294844580f24202222075004d0540005c0306920881d03e0f0100510100c2d8000c40154110f40d0710900d0b140c0d8509100b60225401e5a41c44942205c0a0a00d0002841d00d500480a0a072560054480e031040741c0e030720140c8a401000320b11400b440d42550354002e2000c0750400d8004000100007030409450300300d00035030361403c540060780a00000742440081c00f8049205005910042a040b646080d035400c090320303030700480e2089103600c0510b850001541c10402444014944446400c00c0301107440c0d2814500040e159021880b84040900840c000340d444081c0c802e07041403d494102004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328577266 1250 328576016 328576019
    0x240403080f0403120507091701060f120501020906071406161e0c02030a05011d0105040201090e060f040e0303220b04020d080c012c0129041e050108160807 68
    0x101e101c1070304060015010012001c0b030391880319034607010b854000d04807039031010780c001d1400003180381c568034946c5460f81c00d90514400f04554030b03400e0b1f540c42c02c0e80c444140e8240500d0041c03030014024030540142d240c02c40310105108046c0405c0c0280d1844c4001c91f8000c4e6444c503076030700d20400840360460f031300c010106403a680e20007002000c1c1d0100e40c1d078606041c01c04a03e0a207107038002902e002c407514230460b0180c6d11100c2d1820bd21465104220301910024028006800c09038000b03085c1d80c1460181d1404041c50318001074a0b969000184500144040c0040000001c01d03603245450382e0080f01c00d40c01240150003074842c014442c281d0b5500d016040b00980410707480e146e080002c1c90f070b001c84090301ca221087c804807104a8080c426170300d801045900ea85654a182c07800340107015000c46802d03083ea490281c030b82d4008a031a1070210540c800b0b032140681292000800600105444802c611041c06401001d81c800c400d6588114182c81c54a0101c4a1170403116014207000c1845004910007a0440c010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328578516 1250 328577266 328577281
    0x1002010209131e05010803180306010311010c08090d0606030b0919170702030d021501060f1706010201020d0e0a020405010f0b1e0f07050a1103060907180e03040824040308 75
    0x1002019442428007000c01c010a40c0001054600030f070448031b1a13820000300e080c0440c4400d250b0500000f03040d0040c059030340c519180d02c60f558035008030540c180054100c0d0740c4100580e0104440960100034050708a420b0320b030500c90001c01c003501085074042c00150103d13003038120002d80d01c40c00c001c004003000300360f0006559910407480c15154002c000c2c0010700c0301d1001a6000d001c0715021450643c0181a4018807452800e461041039100344c080c4003900100d02466030303000c0f4011865044c0012a14165142c3d00c004034020310520150050036480c04021003840f80f4040343d4810858001c45043c442030740c80c0c1d440b041c01e640711440b5640030700c002000006c07429080d8103405d000340b0f28107a0110703007080c0c0640c0c0c04c0d407100d6121840803203080d041100f0440400071820601c40070040e050f40180210704e41003036015038942e0703680a070041c1d1070307910803000c01042d1182d000700200250107000c1e40c0c7c49031350f1441c13102ea5410700d5030420a000c0f03020744281103e2160301e045141c82071380c042e42c60001030388a40d07a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328579766 1250 328578516 328578521
    0x6070f1b08090303090a0b0c0607090302210a0503030a0221101a12181c0906180807080d020d020c060a0c021305071215030c030b1e0108060105100201020913 69
    0x240b94050006000361038680c4d0360110301c4001060076681a40d525901406618204040244010705010400c107003800944c0b103120305e0325122080c1340c40080e00740d01c400d1a40c40c50401c0c04a8014450700c00002003040100d40750b0003420112040800c100c800d04070098500c00c520204460801c0380b6081150200700c410001014030443e003448540503480c1501d007103528040c00404071035214018064a902080c02c0c20100824240003459048401940c00f8020f80185545040d10944d400c01c843c80418003500000d4640c55401005440100d550b1650390300761080d142c1c0c502c8848c0da405409003092851302d480c00440c0c10b80121000030415032511800480c203a829000003075003640c2000d45c07045100441d1200c6d00c070b400d00601e02a1625146905220211402c0c1d0b90b06045001200c0b0141d4010000268800e08050507668004082065540d80301e9100b15100d010304068015030542c0c0300005012000890a03505a0300e040d1180d00348039034409070681c01d074802c64410a4000c9200c00b920621140d159 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328581016 1250 328579766 328579777
    0x10051608040816061b1d090a060902070f17040602030418060b070303050f0106090f0b0717070605010303170115120608010e0321040b0f1e070206070f1b08 68
    0x107104690414070540f4020742d0780311101d60200e42042e0b45903842e214484600d0b9042d10b0403800c03490041d1500510881da84001d02180e0b603028098003007078011403c0c0c0c000030740115000d0103041c282191580e00c1da0502e040b1440c00490240c0b0005800d002d04003104040004030750a403161600114501460050b0120000500e0010050341c0d986d550740100b40000c40f10004c0010a00954000c60b10741801942c8039400e400c180d008005200740040708202c1c030303203c00e401b0304d080380ca01c9943e558070385074541419219014044042c00c02d20364001100010003213160301587c141ea0003550340e1485410114103201640c02c00f03000d80303030200c0c3d560000303521041d00c03884500700f88104880012a00554601c001070944004900403003040e0004609120103000208070b490103c40c020750342e900c4504041e10345000c000740181c0820b030070004010010703030000301e130071b1120300050011400c100e198902440001d40f03a070f1040e02c141c0c0000b4484e40440d46114411082e4050300300990700d0f00e00c500d80301503981c208694000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328582266 1250 328581016 328581023
    0x909040b0618040b0405070821030a020702060f0c19080d050403020c150a030e0a2103020705030417010c020106141c0b0903070c060c1a0406020d050a0c021005160804 73
    0x180d03810080007032902c4820301440c0304208855107400c0528040341000110307000340b80e10b40e00c6454500e084400c41a086c2059140010045542c0c1c1c88800703d00001c2c0c851050003a400c8040040c03ca1a42c81c2208000c20800351480c090310096030b64240503007552852070034003520140090100c0d00406200384d000c640c002d482030049070010940000400e007000d0340e48284d200618000700c0d074026025011700130f801c0110426405400712000c255101d8081c806c65904121142c584800c00329120f60003070303040318042c5412100310f0780c07503558401e040f500d40305401c0042035440d4200305681741c1c0d581c0140944400da648006a00c8140d4480c40c081c0024484400d9252482401d00c101034004500071028032401618544080d540c0c0b040f0740d007891000c10076154030180800c4100c040d0040400c20800c0341ea601040b8510f01c3c01081d4859081503000b82c01858070b075405c403c1c034100074440e00b45001ea000c0e00322400c56409807001c940c507a0404008031103084414100c13500300300e01109078051081500c80c1d40b2911 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328583516 1250 328582266 328582279
    0x26040e01090c0e03161a0f030f0c040f090204180902090411010201020f03010f03051c05030105010c060609050a2a02100f060f1d100506181c0308100b0909040b06 71
    0x10101c002450050100400020100003000500c9000011b43c002c05044a000c2c140c6403402444014401c07051000500c1d04490901f03540100703620581d10350486009008131003c025030b81d600ca034440070007036009214000e00617101c4000380703402142d00d00601c804690001d08203460703031ba140c1e00e58180c950081c03091141155401c1042e8414041440702075400b80099000d41c00010341103262561800030880c6c0c8181402c02da41c90786c0c404d00e6910008807810341d4401c0c82e20381b0140009160a002031300664010000c040d08150404c44490100d03841406014001c0e03614914000c1c403218490140000380800c040113030001c1c004080c1d4095150002c24000800140002d511641e50750784856000c482d4001c4c00306031040c10440c0c1007000c08140800c1e0017a500c0c04400c2c10392494080000c0c068801c0c0c80105179083d401340c0c4021529595800c0e0710140c2c1542d05c1e001c800c20f0740c46107402083c4c941c048a407180801c0c14042d0100f010f02004080d5082102c01400c048038a49403612100c10170080201013942c03112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328584766 1250 328583516 328583537
    0xc091a0d14031605011d01020c0607030b0a0302100f1d061210080105012c070f0f020708100903260714070f030e011b030e0d06020f0726040e01090c 65
    0x20f1140c0600300040c06040002030810401e01034401068001031901002da0040c00700090329000030541c90b1f04800c0500740080c0d01d0407500e02107048910035600280d0f000c0841c2103400550364001905040c0300c0055600c203807160411842c0103441c42001080c0a400503000d106a24036480043c0d406500022a411050f100568440c1c0c41801c1d5402604002015001041d0b07280515928003591550141003041d025041c0c41c0c40c0b8002016058003100030000c11000444041e1028001d00c000400341100130141c1d010f40e500000164054007090394102d001175082c04da000e290752042e149114a80d000c44800100b25110580d04498001c0c0da8025003d5100f41004018001a030301c0225010280c400d442e072222413840d1714000b41c0400503405802402407051481d45d0300180d40a44020304421003129444806009400d1141c024000d0b440311700c0802900090000c184001c100c800561890495114404100c034a0140e45241c004c9224120045804c900180b1003115950401040c0d1402e5150040205 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328586016 1250 328584766 328584787
    0x10519030c17190609050613020315070e0301050702070f080312010608100e040b06040605091e0702150f2502030306060f0d02031003120207060c0209070215040c091a0d1403 76
    0xa048250b04490711580d40400b01700b082410701c0382560081601c0b4042100300d8054000c2034036103c00d420795245a034aa440000c40c0b2a0064124190f10080900200300a103000d0001070f41d00d201078003d206042420792400911140000700f2114804288400100c0c164601031040d203503444068211842d1000c807110214071520008100e5105078012040115141000810b100444d0516040280204480c000300040548040b075002000305030b01191070300075524050200e0401203c50b200c11150403e10781841800000605058003070308040742420070340c0700000100030030190b1204d0120f0150f0000e0001808501d0114080c106909524144070f00c1e0880c042612000c030381c000c450350500903004c3e00003407040c400e45d000300c030605521130300082c1402400c1c0f40c00900740c0c4900c0c100082c0702e08941c200181c4024421300c800c241980c3e8500e00c40c800f40c101031400300b6541086000c2c1d5a07046181021040852181c050340700650f00b4064001c8900071a240c0343c4400c10581070301401070600c410040c49604 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328587266 1250 328586016 328586053
    0x30302060c130e04170c01020319090f170d0e1c0201050402100825031b030b0d14011d1507020109020114030405010b1201150909080306060d060306050f010519030c17 73
    0x2110b054000103076a46822b403031180402c1c00c0010300110040c50449160002124030656101c80e503049007000b00506a880d011081c103110300b1150329842c17402d005609000f01c0d400031301d1640c240c1800409020089041100b2800c0f103008540c0a50b0200c01c140c841003d450140e40825049020300f903a41e4451949031107044983c10a00389000c000940d20300400c424000c120b10300029014451809100780050000010f40b440c502d035001500f0070130184101442c0700070075400100402400b01c0e03064081c240e1038600545a050b40441c0d005c184c40031400049400d441849480d6401d94141c50b0403031640030350042d44059810060040b1210343da940380e54641581d134440740301f803010445000815044082401134080716181e6002580c01802d0000340710000307801078141c0394040703400e5a04a031950440c213186405020b00e07510140c03111340b81ca03081c00003038032991101e14140c070000e075507100a849041440c01a00c044a120140502003410130902c00414900512010700c01c1c00001c4603580044083d20341d08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328588516 1250 328587266 328587277
    0x30b07020a051c0e090903030106050c0109120203040f1d130227010f1a030703020f12070503010f151d190f060e0a0303020a0f08160c030302060c130e0417 68
    0x40600303480c043c600500d034484140750a1480c1540c0c0310300c00f401c109014035982d00040c02010280100840c803079050102c254000d62949400c40c4690302e0b80084048041e460758402d000d2002c11242044003c101b81158076541c0301005144119281543d90320764445d40b840c0c5070a0780c100e03402002c0641c4507412807400404451101c204131034603003140d494a0001c2c02050880d510040d00d00c0e481c003d800ea1110404001d903a407154280c107026030303a0703049c40d1078a542b54032501e04002d800d0303d20901481440c0c2e0380715000d075040c3d594900d1540805901c0b0140d10a4000c000a40400090382000f400c0801002072011062a68005829030080030016041110f40214603049904007920040d010411694405000d4458801c1600d1080304131382035807002074803442c0e504405070012a00080003010480c402084919440c2000074880448406151100e01003046100c03d800601c641e2000c030700b1040e4940111101c8002400c0240349007450403005a100326070040c4250b03403117403100c084008013090000003400e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328589766 1250 328588516 328588543
    0xd0908121017160b13030503040603020c0c0d150b060409020c1006170337020d0e01030221090a0609080301030c0806010303090902130f0801060801050f0c0301030b07020a05 76
    0x16800303810040c100d001940b500240e540541d0100c0b048210541d40d0b1500442034624500c041603442000640304001c10306240d00007001c41c030001400052640d40343c1d01600310b0f0b807410781c1500c018006150030010f4129101101a200d2000111b10a60100c21513000c0aa003101c058550343c10180d90300024030490700001c84c040c07600d03003000f400701c1c647c09514810a4040c010701540380d1402c6116040d219600e01440502014110a241035040b141c090310600341030f0040d820000314640c00c0140002510f40741c054407040040340040042108bd58001e000b61040161710050704080c161564449802c5800003030494007040c000e1428210121702240a00c120342c5020780403041e0750b94914a0f002e5200c6a40c2d9110030703210f4000c2401400081d42c000404000c031030003c50056112a07400440c3c559900b01c4e503001d00c00300c00c034001002600c5401900420100c0d80040020810765954048100354098100c80800508004000600006080f040c08980103003151040301e508840c07540e202846c01040c001c0702c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328591016 1250 328589766 328589791
    0xf0b0303040b041d04030813030c020d03050403060507030606021207020a09091a07031a132c0c040b061909090501030c0f1401080a1d06010b0405030606010c03050d090812 75
    0x902c00040e81d03031110394450140104d5036a003032a1540b40100221000b074280100c9100d000040400e01d071142c4e246190b40d42e00140303d0240d680e00c1c0e07d000340c81c1d5406840200d403240c2c2440c4c0000c03c071601900c1110304440094000e0201c220b940401802c80c2c0c2c1c05010201d8cc001c0d190880850380c043c90703201c0d52542034071442c01000868008220b4504101000340000d0405080181800d00c402407207c4183c030510050f18a20101d80c508400b49014002042c04078040c07208040005c0040405130290302c80540000d070076124500b05400c14042036910850455401c45010480900f05d20386c849011000284189400301005444003a0181642ca00303900956031800002410b020710050600320b400140f048540090381811310500103084024010403032020903603290300c0303c5000303041410740c201c840103800265007075503843e41070390b02940e009400303098003e10808000a01d1540101d807024092500358552030f0030702a46207500c5011703100d00e14049606042c18000000340007012540907000340c43c0340303201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328592266 1250 328591016 328591019
    0x60303020705120c0910030506040506070e0411162102030d061512110f0a180b0928122001030b130b150403030903051c0e01030f0b0303040b04 63
    0x74600100c0e90059486140114842d041092000078864000901507501d412159100c81218261a80c198400b400034062a02007000700800440c5072407042006481e883c05800c2e0300c50a00c41120410450b41c07016840400580d10456052084180414462460000e00e17610305801c4080800c00748000102503400030a90b000c012526008081c041c01802c00702d044400d0034044000c00b481c0c18600c041d0a0390742d035080d014400c00141e000b107903107440c0b080c01c0c0310341d541800000c01400003920302140c8058007041200403400300c0c0100226040c00b280144000b8890075407084070049100c01883c4078112411000c0e000a0984500c00c140340c3d1107029081d00516400310419090b481208046018101071400044540076138a12071a165601c0182c2c0c8002200d07680c100200d09a840b11002e44510800041000010590310110207020307a4420000d9944234401e0301e60030110300300460380202c0820420284945154405d5010062a4013150b8002c185000500007182c1142d000c1e070401e00c012040050b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328593516 1250 328592266 328592273
    0x90a020d0f050721030509011215081507050318070e0a1b03090305190311030a020712020604050c041802090f0106020d050906180a0f0801020714030702030604031b05060108010603 79
    0x1080d000707016405040583c9109460310144280746014000d046c85004a40750700581d2088040c030458200900c0100002c0907042010f5031412064452651603103c3e45804404a20300c85035680c0c092140d03612020f00750740750010a000c00709021600fa0400e4031072030200040c1c401136404842d01440300c40600050100c50404258641e503d1001c070101072600700802d1400103035204040341c2101420a0310101d010240f8802140075042d4185071050f5488044140100103266500034000036206100c02030ba1310b440c2413030680e01c5020444016150f500050303e04820342c105900300d021040324609071f02d030400c50164002a000502522548051007030500188031154041088a05901c014100b5038280869000010414410195010f00511800f102080c1d50340b5170300240c0340600301841009840307135140c0350014000d400441003074480c90b2400e80558540700307011044442c1d0340e030050042d0401e07658541707055680500b483c181c04024203103004543d002c94130070300849000e440440e0002c034401c2c1c40c505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328594766 1250 328593516 328593523
    0x919090f0501060807090611010e010f02131a090409030905040c02060601091221180801090210090e071103130909020f04060b0307030507021207030302091e01020d08090a020d0f05 79
    0x20040f809014421043c005801d4021100c1411100c107450310300c0b80010500708080c0504600742416500350300b40060880300328119000f8046003480304085c0c1010581c0d941604e071194641400310384480301c042102c031100d0304280d0450b051700e40c085d0418910055940d804181101c00117a40c910068105d04180b041035030b40900c020004010340d03c4010541d04444c2c94070020030340562030f2540041d110a0381400e40e5402403406c040d607100e64103c0035007150b5a50b01001d010b0104440c04030b1080100314100d410081c000c660010039582c11401c0e00c48a41e6031400e060301c03054407104018007644014841200c078081081021006042964004140040c0900c1801894940c1c00c172000e04c030703504002042c40000540000e44e5403000c00d900d0003156503164144142e0802000f0105060307680c4001401c3c905150701a0000d0144501c01d03101044581d03400707000d0500c2e56515840380360040e0403044030000f40521400c07070203030082d94200036101540303440e41c0004c3c688000300d182102c5014915820310103103c000d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328596016 1250 328594766 328594769
    0x6031302040f0b0102100b030a0c0b120703020301030c050910240e09042105040e100501020f150a0c110604140f0c0a15030f050f06040f0e030d020919090f0501 70
    0x2c40078468440300341e00107034450550070003e081140e17403004114403698003003119010484e00450840311154070340b080760426500a03004030444071215800b0031a0b481c400c1c803c60303040f40c0e04401c4d250205801d24081104292003d0700340c9948025104000c0307424103100b84080d42c420700a01c80b0030200003a40704042c041c19003210801d48995041c000300004200024001d429010000a82515602c170301c09040d10140146d402603030f80740c80134204001041c50710704610070a60348245c00302c3d08203904400c803260395003144043c111046054000403070443d440c135811581c443d64240c20403103010524030f5200c1d484c0c0002102c0940d00079140103280c8000303010a014603040e44a84001030b103010540040420080c00340e6100d510b034060048825103200601c40d80c80908200031010040c0002e00b003030b03102e401c909402a21894480c615014804540340300512480c0c1c4201c01120255041840c2089007100030342100441c2500201026101101075469001442c041e001c40c0000103420240c4031030340c0c01240c005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328597122 1106 328596016 328596041
    0x601120510091d0d0f0c021302041505070503070308150d061e020a17040320010203041109060102030928030506161b080a0903020603130204 62
    0x28070161800c03a11812002d1051051502c1c071400d810802c8000400aa0301040e040d40c1518010702c00b10b214400b403400d00340781218140d004038100c01940111000d00980c00141440100d111b50b410030302e502450300e003103414000300f135030390035075a00c1040c10140a20141038000b692501c0c29502016402c50040c143e481c44a5851400c000507001e005c00030107403120951790301060408648250b444101702980c407803180500c3c000b542c52102c00064005d0702082420702c0110701012030103154601c44024900016501c0c074050410290341c4500d0141c03984980038203418091a6a4000309854440d40e0880b036070b45451584492140400c2d041154818203010340b1100003050100104100344510380c200342d5468035100d0130804840d560300465062101e00c0c0d4403160302002c03850002c040e00500c5d0700c0d4206039010300c0d102d80020703105800440f01031360848031035072008007142854000e1034000c045c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 328417266 328597122 := by
  have h0 := BRFrame.cov_init 328417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328417266 ≤ n) (h2 : n < 328597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
