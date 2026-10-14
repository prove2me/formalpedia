-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3804
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:43:16.976982+00:00
-- url     : https://prove2.me/submissions/8abdcb49-34fc-43c0-8c92-5271cd4f0c62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683992805 ≤ n < 684172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683994055 1250 683992805 683992819
    0x90a02160b090a0206030421020c0108041e121101050c09032d01181b08120a030f0203040308100e0108030909180a0c09060905010b0711010507050d120b040b030c 71
    0x80c0c600030b0309000006403150000d2075543c4a00b860309103081d80882501182c40d8055030500032150340350000c02c0071041c0c2d4005031940c080503519510303407082e01074407415103c4808141100460010354034a81e4004541490781d5190034a110301a4081e0850b44040c000c10007030300051181030f5880d6400122030b00321150403402d10b5050b600e00a511400e081528048113419402c007451061111096541108118000e810ba40c0c480c00c130808030303c00e00000c00e00a00e00b003a0002030441c498003400c40000d14410b20a0702c0c0c00204030241030112012600183e80841c0001c51050501c0f00169002611201034078a2151208555240c00b0040f5030320b03c20041500c2c0200d5419000600c10381e601d80c940c64621900c4419900101040c0c544031203171611602a01001e903140c100042141d155500c034160684415444a618021241d10341c05440318a01c481c0c01d0402c04204035a000045040c0301c0f460030502c050f254803c00c42c0c06544e61406880c1650001d81c0190729003013020505070360001c1c1008146030252928 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683995305 1250 683994055 683994061
    0x303071112030f04080109031b0c03122706030c02070f05100c0203160302010f0e150706090c08030301050f0d020d02010809030f04060c021002010e030417011506020c090a02160b 78
    0x10b0450003400548411920003140000e20464103401107080d40e0311030b688011b00c0039070040e2071082c102c4003424060301c010260304d41400010a02c801400600340382c3c0c01c050f41c0d44c0c5941c00d400d01606000c10250410a0064a010002c90741c1500a415200380c260025101003400e00e1100703861000c0d20f100d9103126492502c0143c0f13189010b42c40c0301042d84c3d0050191400c40c0094603048070010640d00c0128001030440816111035480b404915548090003030403551500070280000c0c07007580101c4002d4030029034540045c000030b4603e849070002004400051a11b07589070900300865485540641030080741c0900012005a82d0030854500c1c2d151b0900b0120121340b915440c06165018103107800349131407000140418200d0f0850500b507075440c402c0320180080c42017600708a0030707134081c0800c482046e40305201c00c0c0164081c101d16154821900303000007403018038802c200140d0b50322941c0310f6005600b012a030704009082c0309401c44d80c0107200203025440d002020160100d00d0611000282c41c0c0d00c428004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683996555 1250 683995305 683995339
    0x40f120b04060213050a0608040c050402090f0d022107150c08030c031806070909060f0806071b05070e010302011d031902131103220305090108040501140a0e0c03030711 74
    0x307401c0281202506c000d00c490344030440a04042402d650603a038440c1c544800240f00d161074000c607602e8440240c4280391030008030061250752840e00c50100d0307000e8002c00700e07002c04003a20803c13081f050b43c01c50010b00041d807400c04690220324590102000300f0015408040204640c0c0f801c0341e412500d03105409903240e0f0b98038551007202141c044c4000b020301541c010702140701e500122500544101034010010b4540e01d11040d84500c4203032080060030f400c0768001030303084c5010310040300403c0c92550350f001c0501580d60300d141c18064241c00403052701c1c000e6001401913582c8100415050029a42e48403403c03103140d00020f9a408161906107178508101e001d01045455124401c01c0e2194421404e025580b20220030780c0c0342d030300704031211142194106941960340700b500a22000464141d1076039031070920690011907405000034400e40301c079921a104420101600d04c0003c3c450000b40400040340440400818101240101c40510a034014013114001c40d89513800d08203412402c4501c8104841d043e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683997805 1250 683996555 683996587
    0x11203020a0f201c08030402190e071d01090e0612030d02070201030c08010e06040207081611041815021b07170c04290123040f120b040602 61
    0x8001049a801428501c0070400d81c80c0d444240d00b8020b18941d00d03443d1222040c00620403603040303801c2980c030907108150041780c0b02200968010780041c1280c107104003600c0144e6111086507121411008441007080149540700180910f03264071030324012403162400000800181300d6014038842d4201000c00329985690b203400d42c150f000340b8441601c1e01d0b14503013040c020081d04082c200f41c2c00f280c1405000c4407030346c0c031409445058940010103140302c0d0300c600090100a4020704001c9031400c004028100d100200c581400c1d403918410031800c17130018100001e101c151400c09040c801c110751035104941c00204429401c2c5144000840010703180c11040c3c0b96584140201d03180404c0301d0007905000706014043c5642c09030109a910f04541b107a00100003400b044540c2d001501c105480b00e6013800232454000d000300340700040149003203c000e585e1486206131841d0600480016141f0004041000c003000142400080ca0507220901742c428080d10b0b0840004801400100a20350000382c000004d0030020f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683999055 1250 683997805 683997823
    0x80d0f0b030d030501031406072a080705010504020a08070b070611040302150705010c020d0c030e13180b0a0219081b0703080f0612030409020f1225080601050301120302 74
    0x604070390710b9029488001d4020903080c041542e4880070701d5040e40e03907603e00040c2c850085115903212520f145494003040005000c030f40e501859012241804004a620340c130140c01154000e200005147c00c0070f00c101309645407180e001400c0c40d0000b10b0100480340110b02070f07851480c0c0082d004600490350104c15149032055400c025440007004c44090114103c0c9005081d015115100030000130000c00400d0380d079082d0301800400002c801c8030000d4006446840900c0720844060a060401403461124001343e0340d8000c103000c0c810501c3d40c03458081c005054130450b0071a0f500c180440c98260840c01510301c0b9203141d45401c040c404d212010680f080382e010380701d8000a26041c07030240c40c0d59044c580100303403100540b0b19a5030f5102010114a0700e1808540e403032007010036400110714080c80c214104000e50041c650002c13040900340501213104483c0c01c649803141c21124040303040d0307170500702c07074480034a4100c00010208142d0f04c0420000703036080780483c0d066440c030154035807217007115140403854407004d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684000305 1250 683999055 683999059
    0x92401050a210912030b090615071202030a021e0606091e0406020d1d1015050409052521170d0614010c0213050603030c031c060909080d0f0b 62
    0x10910120201168443c5400502c03864103854840d00034003080382550490702840d54080c510601243d81840d250700118008080a140242009559190343d01102d12140f100b10140e000001d10f4030134580d05209181c880c210901c2c00d00ca84418407030b003403903480d900103101c2030080e025540421959039010201d0410b44c00e4051420101d8602071820300c0180d00204034603c216401c001d4400364641c00e8040744410300402d54014030600f012800d4020140641809601d19034640310000b14054550340202c00301c00e070288004090b03112000086070030414150f0401210121098018017650b81000c1c281001400c0c0d0110300c9502110600700142c5c1c40500710305103500490001003c0e200b69500ba080036081302c0200e541101014549401922983c059030310003035001081d40c0304140780c1107440e40310703541149002d03003140c0c200209458903d107580c0c04100707030304961107503041000c103a01607074013901010b000b1001041c09000203da90f014114099818030308a080d480b6800c40540c025280d111905202c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684001555 1250 684000305 684000347
    0x31801051e0405190b03070f23031015020607050705010f022206091a0d1104171b0f0f01030902090a0905070803092404030804060e092401050a 63
    0x11820000180b940a8802c0078081d81c0760000d05200310710f64042c0d5000b280d203010015441d40c1d403003003011292000260090801d0000c22001c00c4204c031000d501c0706801d540f03240320241d40ea0515a00007401150207034030110720b580044040e413040700d83c045070454110015090041d1102c1d500c0c034086014107604114044002e1010075a41801241086940040280d00d000e25412944500003154801101d0107201d641c00010348150301c910442070002d09079121900300004441940c40c02d038810316840b0b84d20201030f02c489900090030222040c080c0d450320042001c11209001320b0f5201141d2009206050745108101000102c503299019801c40340320f0540c0142090920b1601040b100001d14a00205452501c140b00c000b249001780041150700403500107166111700341c020707101e4640407650310a9010100c2c0c01440300000041c5c540700540085c02c00ea450701c0e41d101c0c04280a0040c6407034000c01c0c105c0000c041e41c06244042c2e14100c0c01030024202842c010350f407003a224506075501c61245600c9102080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684002805 1250 684001555 684001597
    0x1215170a050d08041101030b100c060e01020307020a0311060f06010c260406030b0901141c06090515060d0c0311010c0f050c01030c0804080a030203060d0803101403030a0203180105 79
    0xa4044543d030703c2036124100740103000301c840c0011411201c920301c5040e04810311900c54030100340a415108102442080d021416250008485099070030a50310040582c0c01400448101900410003212140c0c04000400c01464004001ca14000014211074103005414044e035085c4902d00704028680c00d084008540c942e8031a103c186080d40c4a4494000000e00e4005901058588a28114100c444c2c20030403400140945080010841d038001100b425403030490028000200540602c040c098050300180045141c960317003e42916400400c0184115036000281000408428650302940d412204602c40a858400142c400c40c10704840900f0320b044054249041000c00a50036048050a90301449240c41041e02500c2c031070001c0d07900500b44a414448514814865070107150711440007071040000c4041503d82800c56030003664150074045000d4801d20104000000000c412001640103601d80b0000da03000035203c0c01880981405501c0040c1e841c0c180c0c1c0e2203001070310b590030602c01c00101698 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684004055 1250 684002805 684002807
    0xc09041b080703020a020a080a030213030609060f0b03191b0e150a060f180314030a02060105011407030305060316061d01030b0d061d030301060c031215170a050d 71
    0x3841180000724598005064184a07000b80e9024000d6a0024513514103540d0703070350400b500414081010598280100d0046885106082d0021402a030000072078034a00d080c42405d9a40c022803a0320402d040400d15411a10b00084001080c039620090104036601e51912824884440c0715040b4010001c02d000714014401c0308400b40650082100f0f2501c160361034061001440b07031403185402007201003000040e135600860107241c525110021403440d40b42c903942c0e02d820000d0300034200c07881503001080c20a421901084810302402c000d0800c075010b21100f4400750302500c11100300030308041c0c070340d000f007049501c080010301031101c00006090f411a03142c91004052818007081748082e41845c00e0002d1a650013840303000b62681014015500318011500d4600140a903503410f11810380182c240785000000900285000e443d190381d0b0044108024140144407020440e80304902a02d03107004881d4400b61400e41d4000c83c0c2d2104d552800c5c0301c035074102c001c1c02c2885484015201d4060704181c80481 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684005305 1250 684004055 684004091
    0xe0a090507030f0b0a06020607200303150306060f28150305060a0b1903021605011d010c18171c0f0917100b0a050d080307170c030f0c0904 61
    0x81040903000c10041c01001304101010701c1d42e10030200540c00a001250000703200c1d51885500e070003e1b107800c14003d54050b80592a581c0206e402440f0030443c0e502d000c801d4582070220035084101101c60240105440c000201e2800c01a11000300802e5820b1400c048131200c0e103440c0e80184a01011041c40c0d41100b0000b501030101120340d83c0c03144d19510008185418510309884802000d1190042e18400c0c0e514103800a6021031520154035a40d0341038030000403024006e030300311080008001d150f101c840120507030958144071142d01c18400e41c545150b05254000c1c0302c0908441880017240000340700c0248103803c0482c80c11203100018601d202c00107400c0d4100310310f0950305640d0303540c511990ba910b0306030102916002c1040f03803164011138200346d41309080350444607030307118020046100d40d40d4810000d10703000031101301120b200c6404002c00c010290045001d82c0040c0421503811054909014114107501c00108050900219040403407841e800c4c603c01d4400f080b6000d401008450301c18001234643e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684006555 1250 684005305 684005321
    0x603020d110315030d0f05121005100c1b12020906190314060f0402100e01110a03030e1b0a0909060906020408010e0f161202190b03010810060b0a0e0a09050703 70
    0x4c2c41203901c900545c512076504095903802c1c50b5180390a207a026580800382810140210313071040090b40c00801c040d5200c6c4407848401303400340c850311000c80062030004404030582e410105500c40c0781c8820041007000c03c040145486d4100c0f4421140d541703400016401c0400200001d181d000341000110070008221b000c030b03180c40c1d424021908241d40703d04101044800c1100d000f500301c140b00540010f481c0c00f40f008404482e2050505030310302e048102426241c201d900005a000940300c03400c0030100302c802d01c61410303401c108642c0c04c0e144800030408200051080c2c462101e40d299120041c03414400c09030700c054002c076403103e000c2d0b43e5943d80700300c0c2a000c0c100c8400b0481440c001c192230b4491981c1c00054141d040d00f04562901011840c0c1140c610b04002407860581c0c0105061210520b8210740c0305121000d0810468020740b00c0d414a44402e1804450f10030302c80d0080d25084003400003031242010744111002d1850414a0721400710081100c0c0c0c2040da029010050520f0140000550142c1000c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684007805 1250 684006555 684006559
    0x2071e120306091a040e0703020301051501091d1602031c0203010e0a060510030e0f100c02060c040e24120303150910050909150c04030b010e0609010603020d110315 72
    0x702c40e11400320740c084034442c03c06034015540b1a51103041c2414960400081981e402c025a814250381c7d40200f401d660084411601009544034004c0e003030b40c3c00c500c5120241c0302468403808414000440e80034440c2015004081e80380c0302c841c1c1160080e01c00c004441800400c041464484500000b40501a400070301500408000c0c240c00951903400e180700e25811500001c10403103044200100071340007800c0902d00c103004d901070890100f0500c4000c001e2340d942490241d00008000c006681c000f41000c0d800f0f0500305407800c080104019408400325500d4001c09018011085044060f6042ca00c600400301420380008a034814481198004409180300345e5884101c44410602e2104010890a0464500c5142c058840f028809410117030006a4403005580031100030742d10840384810301d64421214866140c01c00a400d1041128100d100c1c4e00401030048444810f050110009441d8141401110105640460500040340e82074009181c002002c03c90a0303501e0500c95051550b9103040703a8014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684009055 1250 684007805 684007811
    0xf0302150606130e090102070c030c060306050102030a0f1b05011a010806040b0108011203110303180c0a060c020d0c090608061b0702090f0a060b040b030a0c021f02071e1203 76
    0x1810302d060800440743d0450300ca0445112a038140b6182400c000d0000d13150074102c1d94244800e0700022926040c10001d540180002602185000002003c0d9440360b08100d0464001748401d50401d40c010040c0e41c180b00d5603081100842070b41040e0411890807013140a8455070070703ca029454021001c61a91031032400783d80e14400c1387c0d0b810050000b9100241906400134016100420100d00f020349580c80c824031a2030300b010f003203014200303039451a001074408150080e540d4400111802041040c401441340599004280c00c4c0b50250240280180100290081300c0300d014500c02c002203910380b036014054480301004035641350400b0b69540c0350112240d800c05030742003a0781e4500c3c0741020300307440c0a5540140000556985c4000040016002901d0b1a641c1621000042400400540a032000e861120407440c1c0f6031a080030350506843d20364000109541000c0149540000c604506000c505482d41002da910f40c100d190048031a007440e001c0321020840700f000002004600f0130b440c0c01c1181c8555040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684010305 1250 684009055 684009061
    0x4032f060708010b1b07080313090506011d04020309010905010203181e12070c0e0109051e070e010f020c0904080703021b090106030e1f0b1008150603130f030215 71
    0x50b141c00100b80100f0669070001e012802d0590000c8060b02c2c0180d95036015216001d548104591031034001408517064107040b65010300100c04c00744a595488682442c00301d020241d01420320001d40450705801740220303000400034004000940050700c10651050086540346070002031a142c12003407003403c02c29801003940c04401c0a000c82182d02c80311403000c0141c071482c82490b4254119621001c1c048500801d680300008801141c5940e09000b099040000308841c034054107100006000b915420000c0030f4913a051103556980325207800c0c07002c50b00f802d00090718040c41000741e1910b514803603a154000c0520003008104054040a8106140700703400300d925110380417201742030005519200c160001c0107400100042c0f403203900401e03032001c10070341503c1e43d002c0d0b200001a000303d900800602101d0b01e468400c255420041c00d510318401e55440c103278050f0704101c00d48240155124104030701c0341c00080045803840c1d03000710003031600d154081401c1007407454528001e500c1d01030034844015054090000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684011555 1250 684010305 684010307
    0x10201060909201201020307021b03030a1202031b07050c010206090a0506040b06060f0d051b0c06060d080408060906041a04020f09100503030c0c030601060207050d0b04032f0607 78
    0x244003000e07510084000d5048544103218611441c200043c940c4142c18442c0e04610441c2880198015002a4054085000c83c040205400403800c6901070003503004006411259a103c14008140d440306400903030b072500e4048200700410166009000240d00000d4802c1c00c100c0001041c0d03c00a0f82038099032010780e0b4600801e030302c0388440700001d082900804006400a01180c121075480300c00203103c4c504155258100070403580010001100066540c428440c8030084440c600903e07507503c25005181c000741d420101d48800002c0d000c603000741c0519030b01108101101d801c1d18044e280c2241260713228540814800d64500042e01e0a03200403480700c0d000c0c0c0c8800340320440c00b40700e681c0103403100a00002107820300400400041ca00e0141109c1c0b0b0f07001040d2030b07905000070005215000700420301f981c21601010309010b41a440b21065500050040045456050701c240820b40c0000004481d40c0e0381d0b081c15a071910440005000801001014101941c8444003d000101c3d00710112400d0b40d4500c24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684012805 1250 684011555 684011561
    0x2f0d090801061d010e041a041103060a050c0a0c02030c0415090509031216110f030403030909151203030605031006030b07030911041808070530190c0209150102010609 73
    0x120326000d214072540181710b2003103000e05041d00030303120b01c0c42c0044042c04800059948001a034088440a60400209007940b83c10004542c0054003c1d07810402c0b82010440000c00d80704040005081c0a1072122007429940d051022822441003c0e03c244000c000c3d9041c003041e60341880c081c0080c000d144c00082000c0640000584115546a0f155480280c0b40d54040c403d1b543d540c584a50100070f48140f0710001c0c2c00c001d101140c9042c090000960b00c2da811841c002d00482407039040480c080d071402d0761619610255a845008841901c4442500c040c5541021005000c0d940c014a415200c2c404000000b8501c0b6404102164040c008801c5a511121007c4051b60800b100140000032815403180107442c0581c400a10800915070040e00164142d640002c1a005180143d90941240400465035504e40100c1803220300c40001c1c00b1054051071a4058143c010805400140c10000721440d502d14081d42d4004402a0024040f2081d071078400b00410350700e180d0740d4400d4015420428005000c2500b40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684014055 1250 684012805 684012839
    0x51204170a05120f1315031109091302060403050730030c0b0a06031e02121c030510080115090b0117010306090204230a0501050603072f0d09080106 65
    0x4041e014851403e00c8188103a041000300d40c40c40001004880780c003158000c600402404005203540044019007030150464100c5844c0b0402680200030090103560781c0d4810541c840350030814400c06c24498000304402d8010364200400610414501041081381801c20660f0f01c640032240101e40c460714800d407a070032482c006000b40411800480c0b03000242d02424590303844014602c00080269907900c0340d4161071590f0070174009039441d034a4003206600f4039081030840c52403264018001e010100c50005041c001031360440c0e00709643c400c080b49240d001907801c00010040070000b401003646200c050791268030340e84038400c049481e01000d40340c43e50160200580180300f410340c80c8480d0386503480b49005005041c50481e40255504601804030148100c4030100034072600d103880300752030011250f804a8406800981c4201d0041c001c1002a0794050f180b4102c580080f100d5031100900071221010040000d2042101c9002d1001d5148055030b028042e00210349c0000b0003485030a41c0c0320002c6407081c810b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684015305 1250 684014055 684014063
    0x12040b01150f02060609090c0d0305070c1a16030e0405071e18060309080909130b0a0203010302150705120f07060b0405071b03140d0f0c03050702061501020307051204170a 75
    0x180e0019034545442e0241b15800789103c026a0f200d100c901c0009507010712010341c12030103d00003160100034409000340c0140901302a15526015800701000d8072418051040426150b404114945080522550000b020910040c02c203010b141400e07a406081503200c1d12011040318001e1403001011407144881040414440c204000c00c0d0381010b8088028002c00c0005961034001007001d02050740b5a060194451a00042c2030440c1d40018907100c0c0c40080082c0c14520018010b00060000d6501c05092101801a03085d005d941d40c092b92800700c0c28000d00f000c0f1101c40c003001082c222a1010b94800419056104e00420400c85155400b0001102d1050302c04000040d00501c5215031000c914802260f82e90107402d207991066541c5840c520950300c90901d00c1009500eaa4030164040c076540200304c034034003813402c0a010a1030440340c0250380d060000c180b204901804034152849900a1084a03400d40d0490299071007207410a04403803c07a88140300b1240509890112010f141c40d020a440c445141c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684016555 1250 684015305 684015313
    0x303020909101a0a051b010b03070801020421020f03060708070e0405100b2a070509090c01140904060b0334090b03060103060503150f010914060d0812040b01150f02 72
    0x440c0c003c1d01c1c0c1a00b01c20301c10700a014013002849025200c580051409001040011030320f408039500303250500000d0350040032561700500003032043e8101d400c043c1481d1004480441c14074100c03400020645940c08404503014094002800810340c1d224a055201d00060b8442c92058020142400211501101c403100b070200c4c8490140400c0413202d000b0040c0c08001d01d01c042c1d01c42070f144040342035003a020705d90110550002ca03082000d4282802c04503400a00107001e840103641301e41c00138040e9404140c0403030b02c4000c00a010b50080e501d07540102c0252000007650b40e00c900c0c0c030003402c1d841003001041029287c032026070813040c0c540e5100100c1c440030850341c1e114180d1500e0301e24441d14540007c0c050300e050588654020506440c2084a10013003140070596420a04100016251000c41a00001046410882003d41e80d00d140290150007480607a40121810712900b030462650280400141c50058994140424047c0c0b01013070906a0303d42442a5200603400c4000351800c80101d41c1c03420161700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684017805 1250 684016555 684016589
    0xa0203071206021e040e22060b03010f0c051c1107060c02010b060d1505010e06040605030a09060504150b03010203100509090c0406090f0e0d0c020d030e040603030302090910 76
    0xc1100d42040545110316030141c20a00f0382d8403515404c2400c418419200c2d54040360810101c0901a2a117800c22911910b800346124140e8440040d00d0313030080e01510458a5145080342c2e0f4034254458942d28810420070400080d840e00018456031013181c3ca403841c0080b03501d00008819207071080c032008140210a441c80c010841d51000080c0c04100c0d80c0c641955601d40704605075841d90300050040b6141c413075000a11100c088903035151601c50303400107410040d1408014146444110407030b001d4a0385401c046460782e88216900b0040c00c10340380c00810311801c2400307010410085150070290300358031000911112504000f0b0500300e000072203041c4000280601e00b00690300380499542d07084403075081942d11100d084404981aa009903004502e21541c07064a4000d403c1c03d441664101d03400140a46000403034540018249010f501001c1e214010004291781014059070a403005084050400d10817180d89050150081d00010f0743d460103010b4401c00190b1207040241140242c0d035128041c074039904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684019055 1250 684017805 684017819
    0xc09091110020a03231216020d0e12070b0d0e0d03151203120c050901020d080615030c190e09060103020324010507200a050307180c09031a0708090a020307 68
    0x2410742144a0f40c3c0c80e021050106241d02250b0007046da0804981414403d070500e5201c40d40c003c00d030000e8003c01c64000c0303d0307001c590542c0a600703c0710503001100d11401d65956a040c03203040a02035030140310400b0001441c0e0540100d6a004000d0780d0341a4000d860b42d8901c016000c1e42540c00c003a15081400c9165401400000c1c032078a14075a265004e0314100300f288264608100880319185d100802051000c80c20290960381081000c0c400704582c170b0008000d003054400700f0801c20201c00101e411590204c0010429000881540e10059490300549405501e000000c1e1060741c2c04006680580301401c0000c00f554002d000301d80c013030701c8800c016404c00c40304803401c0300c0001d405644060400c50100f1983c1c0102c2d461809403003140d10a0321501142071840c02c02c000d42001c0b00e501c114020741004104100120580e005002c9101c1c51071340100e07881c0c92282003100c102c40c5a81000b8042500342030907240030602c0305c034858428030054a80c503071541c9030401c0d41d0390348a68480c8025415400824140240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684020305 1250 684019055 684019067
    0xc0a0e01030c140a0c0501051b1c09080a09031e120806031603110306150907030b03100e060711010b060708130914041109101202030a0c09091110020a03 67
    0x40c162400c0f18019006402c25199980801c207084009a460050310b4184042845415009403484850b49401c500c0d811144910340201441080e410f0b24060310000031411641010000781d5001101e503903a1041c030b940160603003080c0d0105907804d248912490b0702d00c48840102c5009140c1201401400c24000b000845600400078005030b050f0140b40003410b000c0b54a1000304010358400e19074042c4000504052600c0c0041c01881d102180c01c500705022010b4603160355480d000481231a0129003066003d0210389450b500d030001402c010b2505843c400d1030000854418011182075540c800401418107081d400e840c29425815407008041100c0000143c40c10014a800c0000d40038580d0407603910814801262240152401041e16060410041110350318242503ca00c0840d070075845401c0035140350b814052140101d500d0300c0082c1d040c640542d607081000360480e0780e0099215000c01d854070464005001010022103550f12520b9100c00e45180081007903103604a80c1d40208401c0885480840381 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684021555 1250 684020305 684020321
    0x8030d060e010f0510200d1103040608060d06090b0a06140109030b15010201060f03030c020108071407060b01020f07080708100e0c0409140102040f140d020120070f18050c0a0e0103 79
    0x20300c511283e05850746540b850500903121080c1003d000f01000c2070340c0c00344c044231034101256003a4008100900199800644041d0400c806440103012001ca80c6412001041c1c0da040252131381c81c20300204060f84e151504640c040d240d100169040300c006a00056035621003500008001d03210540001da1080400c0c95424191503051002040340761b80c2c5c2c00b222810744450780059000076080e00c5c0b01800d55030484120b50f04028103240141d484507551041d5040d602031340100800c0c0c251651840502b50f0320810450040e0110721094400855a0318a10b5680f80003501c101031060003a10205000700719644a44880c8040c0e00300a030089541034000c000c01401d082c00c0440702d51009500c1d900e1003d6003440504050143d00c1c0b40d9120b031604000d004038480e0303121113138a8811034070045e4000c0140d0b400082aa000ca590950720350340d10020903c2241040c00c1c9411107800c01b6040440060000030800d00300c504543e41040800040d211512108814071070805a03101181044140200c50751080e442402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684022805 1250 684021555 684021557
    0x15010810050a09020c16030c0b09060d140106030c2a030c08030c0309060c040605180604091e0b0609031513210f110a0b0c1308030d060e010f0510 64
    0x44056154000200e50500d0b42d0403000300558082481c0ea0088001c00200c00c04101d001000303207500d480d40d600d10503502e4031406240012580811000183e0320307014107940d001000410f040c401e2410032586295244024442c500010382070030400c0348a04d0096424101c5e90160340b4081e845580c0743e40304181c8030a2095811420006500742400200e540a0040d50041c040c00415a03520f0810090951401e000500407078161203040104114080d0003600322145001001e0303600c03802480382e00000300d00d800f0301d0384141849402c14480884044542d1075403107449410380303420001c2041d004103100141c06801840380c1c242e4080c0500380d11000301a6407140d801019000c42100704005a41d840a0100c1c3c116040036903000c2c0e4420710b500301900b0960494031844189024086513194548507a40d5440d60701c4040c0c00303400c815012400c0300d814002142c4500583c2c06c0721034001c6a4691803269607500c000f050040b018506100410580c0c00344245604070344170a00d1707001e401801d0200300036094a5080c0090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684024055 1250 684022805 684022831
    0x2090a0504110412030807020f070e0a0f0b040608010605040510050906060c1f0516031e0b010c0c1203080a09020d030518090103050d09080705060a030c0210050112110405150108 78
    0x1400c4001044c40a1403d4800e5860303262604190344087e01e40305c4690451401500640800c0c0034240310060704980c840c0c4110404540c0011200c1d0350802084080e05454115007003000204491005401080485c2c0c000d840030040c60b618110180c0c090002030107140d5100900c0404600700b4a49003000e0501034a110040d03403012191091004c02d10900340200700386903921881000a040c07501d4100040103941800d0501981c8040c0d20700445c502d0044c4d000544c5c05035286000440350340b1032065280341aa01080d210946511400c0c2c0d44003403028000220006114200020b0480030117019840504e64054102c034464400c0e95801d483c1c940083c40c01549040055100c40702640d01e0109480c002d500520103003550109181000b000761203160003034849588500801c22461b2142c004442c0e92000e00d00d00024409020541242070090f040d414035640c5003458000702e00d09003c2882540480d105054034140540d01a0a02003901c0048030102002a101034103002a5406a4685680074000000718 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684025305 1250 684024055 684024059
    0x90902030c1605190606060305070c1101033b0607050403050601030f02010c06020d05010e07050c0a0f210e0f0a05030a140309060c010f24060f0e0904030309060f02090a05041104 78
    0x84c5130100080380d0685405894010030042160513114240d00301d045072810045801550f15000b0306140505c9002e0304169407000b02c0d4040080080251110300c4804a034617404040b0100a81030304050704160303c4450180001049003280200c0841d01107913400400b40400e6071954131042d80343e070780c640010b80c1800401070940c0002a0144000e144051850320009490350500246150010b401090701c010720108020a40b50302e0000640c0014840e48603110204404031403030030a25210020480c05900d110402c1c90320300ea241c02510034560004180c4947d90441c200004014180d041846043d0705a007100c0a284042640240c5903c5031241020480386410450000701e40c80b903121044c144a181d644152a00da070704082c2c06442010349646240c000c0130f81c20a1180b00c1d12040c20b100c0e00c000c2c050fa01000c1141180580201c0001000040584140d4034141c103024000d04001c1c0d804407a0240b501c4481c403940b07d07051080c2c601d1136a014101e03a14190901080c0b000811110014440b1a1818400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684026555 1250 684025305 684025333
    0xc021918020a020a12080f0f011a180d0c180504080306010c0c0302150417060105060406201e161a180603010f15090305030a0807170c0a090902030c1605 67
    0x1005d0500d582d28a081850a010541444000035095007040e03c12030b00104490f007a460710180e07507658135846d8503035515814040300240ca46902c0404e03801900041209040c0140003d000003200d80b100c403050407002e0115480b000310744045130300504c50202400400c415501c1a5032901c0510311640b642c1280b1a1650001400d00c9039810030b00c0314015000400307000c0a00c001c1300a00d81c03055540010000343d418000000d006d40254007030349041208445e0f20703642c0840710105112801c0f1450080e200c0c201d800303c0030150001e1412000030210711404d20304032092407120070740e10122140c0c0504294500700750082d0011503440100007042801000000c0f1a0b00c6e42c91500944c024003500c4069a005454070070b8144d040072803109400d0900046600c01c20128401004850004d5910301c0c104440303a450800030307520111104510b02c080d0b00407504002d80018150014480c1d01031540703800021613a03526290013607100844440d80480303000e004400c0804446404060300a01c0344086d60016041e41c0341e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684027805 1250 684026555 684026573
    0x10e0a061a03060a020a022e02030c0418090b070503040b07260f220b0f040f0609300219050c09190506010e010e0d051c0c021918020a020a 61
    0x50070114130b40d800510300301c02c2c5404200e0189040403940c0c3e00c1500c220701c1c0001800070759447c01c010119640010001d010401c2c08001ca4028145040d425094410844128802090610000c0305c2000200c0c01190aa9000d4400c0c1e91081307510410202c540c4d56000300031180240480100350321031032480040b00d0001c0721780130054820310070b20b4944039461516008140f50324903e9850348850206420710200449c203080042c0e980010140007001e0161a6890020100008020041c00c02ca18180b145020010b0100c0b60307440079915207092030b80d0103c4104010b1812a00b58104401580c07001001c0c20569840c4081c5415035801401a98041c0c0c00c60300119840000403134480c1400b20540c80c106a00034498400d0f02e0f0490420700e45048500301180019245008a600c41482800075585034010020704103c204120601c5170b1444081e100c03a910f02400c040a0200201e1040161502d0003489a8600c881203084440d4412a03105140303038000c00400962241d50680f00314002e80e100d880116030950 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684029055 1250 684027805 684027811
    0x406051311130608100b070302030d05060d0807080901030501091a010c050309090c040810021303060b281a030c031314060c040602010e010c050f090109030c03060b01020d02010e0a061a0306 83
    0x2072104d0320303a80b500103c5c052058070b41d600b1219190b2021301c005800702e50700005560070302d02d04000008139515034500245136a401004000d0444100040c0c642c00c001a410180c04505400e80742030090781d0700c41c00250207030307007001955901c80c0307a4400041c1c180d503115032200000e050280c000e41e480e00743c03034502044c89410304507250f110700700d4002170070080f50000b008850ba298040020450501d40701d811000302d034444030300c00034207140e80741e1051050075a1811320b111091144090f25103280000300480052140ea80c9c4112034443d0002d104084da21940070044a01c50105500d01610310f580c1c1e100c20700311118060100b0743d941301403d0b020340c0021000300700f002e0046140b041d0850b1a91715001c0300900f0346121240c9030107140d0402e145007644540010a4400d45005036a103552142c0d64003004a41e044141d82c40030707000c113812500010034407807240d00242d100803013a03003a99500c0c80d610703034141c0c20385002d89400c0780c1030340c8281039040100d6541e0380000f48010903080d449480c144000000707403502c41c041e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684030305 1250 684029055 684029057
    0x22214010f0302100309030905151b0f0c03010603050706081b04061d0d0302060106030e0c190f0806100506030403110a051605030c0307140a050d0f0303060504060513111306 76
    0x9004103006504c2c2450300d4444414003460180701200c007d80e00100719500510449024440451075101c0c5490780c0c04c1031710348c10034803a4004017803509138895480d5215420b040c003007418050380300d0724540c900341801441c003540d4100004245030b43c0380041c00c407074000e03009058910b0048041d039051040d8514400a000504141c0e0340d03001d20340c0c10710702e4200c9000342e038540305813060011006510009401103000303411244030742000903914a02d880d000741460080c1e40d815038021032102030321070050000030b480c4080d5044c40c41007041154803003420701c0c0c1d03d100c1520861244586e01c04100700c580340860086600501c01d02e00040d4903401020554076000d50342500b00c035950054980c83e030301c4083c4000c00d0001800100e0041492405803c0840e40382d05480c007500c40300c05400301443c1415200c00802c1300c01850302410403000b40c0d1aa0034030b400f88501d58103081f00002c0c201200043c0602e850b02945050380c40041107040c089400e513001da0000c1014a110317184050089c416640124005282003004200c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684031555 1250 684030305 684030329
    0x2150403051201121712060904020301020c010c08010807060807050d02090a05090106110115050f1e0d0804090b0d03170a0b130b030c09090a0210020c03010624020a02221401 76
    0xc0c518080c11040366a2161030074805042c81040912030043c59a140c0116050b1400348d1030392924004240640319240380e4542e25800c19941004003507200051604039204030023074601d82a268041110748003401d0307480c4e400044e0180a1101210419801000401c1c80140922030240e40d50000c0b0345408401d900c03040209a09540c0c42c2e044440078042e4018216080804107146402c01000401c00c401c9512a5801000c607180a404441c0b5001101840160b000b040d8610342c1450b0304d4000d0941d4450300070543d40e80e0400304683340c10b0800443c5403007000e500d81c5641004442d0302c1b65852902d003009203080c0080e501c8440b031117000c0d02c40d0300101003050401c01c000b084894840c400c1c1850020707103042d00c0c0d0255144004102e038031040450091502c5604071078090000320003020881c0350044d45080182c0c10352805c030300042c00c440140c80090410342c0c0c019850050021a24050f44c480c40c1100c4007941000c1040142c00c03000990f8103156404211340d400c00110003142d050f82007030f00341e000d03086038210b012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684032805 1250 684031555 684031589
    0x30c1c0323091b0102120c0304030b040b090f0c01050304031116180b151815030903040608010501080907030b061314060a23061e19090801020a02150403051201 70
    0x4014040011203071115100d0f140d50300d40800000356124114184086003050100b00c541d0761200a10444d402950022a0346006041509100c101c8286c19204090140300d198040c40c540b04010900090258058542a0540daa01d840c15190241c080010305005d014100310481c030450080e018038090108205401d0280781881214001c58007141c000a1240682180c40d02c443e0289100b00c42642c000c2c0088400c4000059001c01d4000c11046446980d01c0004020018034050010143c8115100340ea81d0f8081c40e6070300c20054400500903101c405064001280074004580c50841941e04144050003064601d80e010b0720180440d07100c0342c902924040903000744101481c01000a0026200021500f000541645c4034560801e550600150045101151030f00c84100004025901c14500290140d6076000550000b02c0c4801515086800b1401c0c119011482d200148203660080955400034103000d0488024200510320041003203042041c108800c48461099640c05030082042400807034032070b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684034055 1250 684032805 684032821
    0x1061e0504090507090302030f011a04020c07270b0409020906121f2f0717090405010e1b0a0207050405090c10091a0a0806060a030609020a02031803030c1c0323 70
    0x10342a09c0c05601c0342e040c1102c040e800804018440c034080c130201d6005990b0180d0328074140c02c0c03450540c0603007080c208180c1e4140152030000441070010060200400500031b450080008880c00902e01a4201202c04006422428200840084801d080d01182c020b0300240400780d02c1400e103140b00821064586180e810890048145d041c507580000c000e001440c07607501a502046d0181c18030280070309110031580d241c2c201c440401c540b40b400c00640280100c1d80c40d01404a00c0c0078040c1c030700c500e402c003000c45400309003119902a61041122603000d052201e14000230040540806854001c143c055006021266550b050403040c0b070b04459101d940032076142003140b041802c40c0040385a0000e504025111302d4680c44205d2642c4450b04a828a40719480c2200480c003c00494200710361240c400145646120f0700000a81030011600e4403100f0042e100d2014580c490003140c10003502a80092140026100044883e1100d0800c614000a0300b5901e083ca10092569411910b0a40410001800850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684035305 1250 684034055 684034063
    0x112020f150c0f07050913081201030303060303081b160201021009030305061c08040b0c0c030a05060610110c062b0510080d120209030102040320010e030601061e050409050709030203 80
    0x4007a1800078191341450140824021040103055513414501c030203444040100140646507242c80210710400716685a00d0b0203030040c0081d00080d8007080f4060002200c140c081e1400303803000306200b03e11034101029000320f40c40308514080c00324107501808030084030144281c482e00c0c400c2802590f020419040c42c00602004081a540551008801e8140040480c0c610001c480441d1000c5d018940d0740c1204429807400c0c1281ca845807a414040d02c480c40090107400980c1074026002158580322001406c101600c00c2811400105400d402c58501a4518503102c03000d0304074070f100c1c0d19820150b207105c43c09481c0c020511071035810400c1c0d034403018001c1800d080e50068014204100042c4190354100f000903100b0b49031810b5440d842500020120075940703003034042d40c00455101c40740364000d4405c01c0414425482e060042e9000030480040204a4a00060064100d1380640c4031074200c840c20807840a41702c0d100300040400d01008100000f048003103445020b11030002035551251641c2548101820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684036555 1250 684035305 684035323
    0x4060f0b010503042f0d060e0f0a0302120f12011d1303122d050f0c0702090114040207021c03030b011d19170d180e0112020f150c 57
    0x4202c010300402000802100f5160700a4120107070101c4840213040c3c101c400e003900301c003072690440690303482c0e8400c008a641002901c020400240c0340c50b4049440000e46c0c810b1411030280060744041110340e04e007028080140342026445e50080d161400741c07000c103008200d003a07008a50413440e12050394080303c0300c0940140c02c5440f40250441480140d20002c04050140000700e8000303550703004441d6640c0603002a0160080740c00448191040c101141d0002800c044484001405820001810700808901202c14465000302600c1169081245141c540c3c4021189150065801c10554025981d4820040706500304c00c03a1254402166140040070340711503228840c184055180751009008c0036001c010710205050381c0591450148000800f4000081d6000c000c4001c403241e1041d01e15040800d50120803c4035440f4101c2204451540314584030341c0d8424040e821101c0e1b4014401c02071030b51501403015000800d00c410340030070b101c00203240402c140301e0703604002c600140314881900300f482103481c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684037805 1250 684036555 684036557
    0x1050c0313082d0a020120030f131703041211100b031002180a15050904110712210204030f11030304030c0e1008010b0a0b0d1404060f0b01 61
    0xc25410048600c080150740c0d108001d004800215410b8019188024141d202d0300e00b06005002818556a1448180d03210b03960410055081100c89032900c1e07000d408a4184498000d072451840d030b901c21843c1c21200020345400d5600010030102000310740791280a0b200004011849079981c2014907140740c9074121080c008060084011103124014004205a140b08140c0c4001040e001c1e078203c00603040c00c15110310108d00b94804500d40d41030400d0704121201d0540240ca0800110b911080baa00c0f59184803130364400060301c100021111420940c110030142c0c0d6441c0c05c09420981140c0d210000c1d0034050300c80400140404602105200d00400800803560346c4000c218a4641140c55402c80c2030804030020b4002e40c0c03840c5240b541620200304642c01540c010740e0038900c03180c65020210079400c050301c030758501900c0c2d5000810092810304c42c00010900041c8039211951601446261a4202150048800b580c0703848199010000036007040c810b40c440e1400103814141c0c9010181141d4007400d40074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684039055 1250 684037805 684037807
    0x30b0108100324020c0a0b010e3102061207020d0c260408030409020307020c0a051c0c170102070501060b07030804031d060d0203040c05100f03050a11071401050c 71
    0xd100d42101d91809880c0c0180ca941040a110307010001c600c403840a62440c601c0c4001000800c50300c011603008600340c811881c00c00c269aa400118110100c1508d511603005c80c2010081510000e00c01030b5904907024800c60208426036070005810394010003105015080188200291503505203c40b52802001e0b00709004001c0307198403036a0300030071502000060140140307201c2c0c410f0682caa0030f0300c0080c89007000305c9540b9911401100080d410984850380588120303c1d1413011841c1c103203441030a440025101c00d0040d0001c1100d50000b00115809540180c02408003046d02ca041007854107001c0181c2c4c0002da038622540c6020350031103c0e00d61012044000900c10240043c1d0b011513103035041900743c0f034650603402d40d112007404021000c00750030794440c10000304600c221005030055440360380188030340780000d96a9401d000b507110075035004c400002c8aa040300c00c003036400b82d4082500003110401c00100c02c0559501111203038450b0009503050340e41100c1071f4088400c24010302e90300c403030780d04011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684040305 1250 684039055 684039061
    0x221415070903110307081f0b041e0b01140313030207151e1106280e060703090c09090b0402130b011e0c0203101a03011802040b030717010606030b0108 66
    0x1072080309a404000c10038082500521a282d6003040304070041d104400a0310120807941a28105c40d80060814059582c281a203a120528092161140000c026070112031144d00e40146040108413000c040c6061080780300102c6000100440914480c580040c3d0303a0309042202c0c00c0203450041598410a10768007800c501003500381c0d00c092584030061100d00e189821070ba01d10b0f020313110003600160f50300c2c00d44a11000c2199411080c02441d80300c620003040b5001e10b051840c002d4041d11013158020031355900c02000f28522034400d034040001d02d0b0245510481e1240c5407080700090700d00411094419000c44002e000551515800710b0311b00e503031041c0301000304a10410005c1c20035100c0c10021030004580c564942c1d03005020f410a010550b81c0101912084e50482ca487d04c003c188902808150001c0c034440b22109060510840d003405590801c0454000c41139800c101c0036003c20800c86415014442c40000c4285a000010f400000d8200020507107505208000f800c840039504640d040040354424 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684041555 1250 684040305 684040307
    0x1703090d11010504030629121c2f010510030b0c0f3106020d090306020313080a020607020c0103141f0b040603090512070b010e22141507 60
    0x1034540520351104124800c0c00e803a000682e05800341e42d0014054906049445c145120340140381054110640d035000b10407002a418080c031200810900a42c962120f40091000c40c08844403504a120a180105400b07101e441c0741113000c800b5040d005076101088601400003102030040710751248900c61050300307181c5142c980e04081d4001600401c0072501c0040e4020341c201540d000c480248140100b6458510841d00343c05031552402e0500300c0c04998000c0300480d0341c03840441d6842d4010101e0307031441103442c02c640340c4900035803001c2d090083c1080c2c01d5a24100259141d4094058507000e43c001d02228901050081c0c1030078091000c0c3d6041625080c2c0d82004d0f080b408441c55005107845080c0801395404420032810741169030443e415074039000c10300207415039040d002180360394460400d079074038a80c2d14426070516010300e000040002060900511a101c822120b0b10383c4426505044a64a09500d1314240070401d00b59058a0306008843c00020700f080800c0f04954444245140400600d01510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684042805 1250 684041555 684041569
    0x50a030f0c0b070e01080a061401050c010b03060903070b0a060e040b2e06090b1312060f0203150306090c13020d0b1c0516080705010c03051210170309 66
    0x905004400318210822449150404502a0700040c4104181030a80c03002d042001c0e150034440c0001c0000c0c0c00515a02914014681101c02c0529206420808840150743d150401e1146a08030f40d40c4042050b586d0303a04015007406544201d024607074409081c01c12114010006000e1101c0c1c5080040c104840d10260364065032290b08a0090801a1100c1c0000300410011054140101001c240003d1501080360514003c9550036100c0094096a85400d4403850180c0c3c40e0a84448141040030010707504131041d81c40106125150000b51070940160b407400b00c0c2c000fa1421100d48901001e05140b43c2420045560404640401000401c00700c10010365070804000003441d0258010502d54801e44081e040b1a1200d08014400f0b210b40703281180400326400c80003000d44061040001045074480071900700c02c103079100b40340070740005824500192109041000300314100201040805128280100ea150180c014000380c0b080381460300600e41803014114044501c80d41080041182990f2144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684044055 1250 684042805 684042823
    0x90d0f0e0f06090409060b040c090f030f171c180b0118090f11030d081e070905190f0602070605090904080f16020a0e07050d0e1606090e0a020705 64
    0x450072450a070504000c1003440c042d90032042c0d00710b401c2002030810012107401031982c07042c0c03e44040000d00b00c00340086808032054402d806600407102010310104540b2140395103402d004806031088035202111110a0703502c81c8101c940e0790684085403010045003400380e15412500703642a54180c0305c81d074454115141c012301c20000c11a004100a42140f01c507a0408205103400a8031541110100d00782100054080c0a145100f40540800b81840038003070105c0700d015040d50b0030464050810034400c20003050300600302109100c890540094690b4400c0c031407500354118243c50b1001c803440d020041d5514080b42e0401c0095401100b4140000c660020036240c00000448041e400e0380c4031070508020364850b140e0401901c40001541c48125a0301c001d200304944e100b610f03030a03221a03071520181d200520135100c0d000000d804010329050054a40c05c036540c60552841560500c1d1200700744a241e86c00355a01040c04140d000c4c0d800c1003d411403010055001c01c10300020b504e4004140e860680302c80c1d800d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684045305 1250 684044055 684044059
    0x20d110c01110f0f010207170324010903060c11010c050c0c150405211b0d0b09120a0c05060109090201020334060911030f0601060c0809030d08090d0f0e 67
    0x80c036000060280300f08007058101211400307035103100c044000d00c14041c0d40040400d59503c415294421181d582c00001c0301c0c4034603452007424a8214010a4400460003103074601760400000040203c041491840b810b0981d1885848407111005903030042402d58103240d01000034050b0074094503200520228903500d03c1001100c2c5010f1614050324034010754000c1d500710b56041000140c422403100b0354034121102071100301045400c2d210406c0052801e071044615a10b800c2689104040009105001e09680182c43d800c20b07078110580091048240d5000800104d00241035030301250203000003884264050215000c041c0f2120141e500040c0d40d034424241100d010380c01c1030494111000c103d420764001c8400c43c03100c0000040f07907400c100b00070307080070402502c0c0c007040b5211044540c900019600f005c10102d0000d40341582c641071082d0350003a007900050350004410003494072141c0c1c0500803041800090b40707840c2111304154051078034010000504030203112042000500c0b44c3e800450000600c001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684046555 1250 684045305 684045317
    0x203060f070f0e090613091203020301030302100c05070201030b0607060f02180301230705160305130603051b0a020a020d0605040b0705031b091c03080f0c091e0102191101020d110c01 80
    0x6c0f00400018402d00d00054032182480d4042c0c5074840e8035400440c100c80c003950840e80a0040b0101810803111a840e03064003244040140500550007504801c03444000244a00e043c0551174440744255100164205a4942d0010301300e45102c90110500f4000f1505a00030460710703610808800000d003414480f250240800000a65174900c64022146040100f00d0141085856480c0c007a01c01c0d0014060304101c3c0001402c045601031292207003912a406000300300c03c400710211010075030b40e13014954020440c01080c41c2000961034203c80d040400b88502d000044915241c2080340390340002900450410208000384001c06440e10111580e0408070030b0030f10341d238050041c0003601661040d9000800141210102000d1540000301070348140110701001c0c0e05036482c0e42060510384228003005510540762042040c00802c822070141b4090b0060044a0070902c400000006003d0300f41c1048401068100c040311055074180400d02c1050307a80e042441032007031580d40f22501c42800351415810460 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684047805 1250 684046555 684046579
    0x70605090304050d0f0b070512060d031206060e0411120403080a060e0108030a08010e090703150609050112110409031b050a14032502060313030c0203060f070f0e0906 73
    0x40600464004020041680c00c2e0001390f0f2404007020710302d00d43d00740c85846100001814460141086564509181152a180750307144000c0000c05d40301a2001d6042101044010201344441e106110182c0702540f55500c420007114204000d5402006040349000001d01c01c048511401401254100d0741c1420f02210300d40d51114090f0041c0031075440107484503c40c40c000035680e03070084010802e8810070b5a50400036038803045c0404601d80e09560100740d81d44011410004500d069203032407036502d0200e001044045d520f0300340100742c4200380c0144480d218240e140c94104084008001000b03034080c0c805000c0d5105a440240101510b142d00f104400e102c088a603082103400c0c003040750201e900008126084002d00e0390b055803600500c4c040501a00a61203903141e176601049650b000d03660060a003403a6585103121525403408803402101441814010040181c2c1c3c2071001620039940e000d41a8950301c2c0c00d0000411050384020360340e003402180711851000b03460b811110350340b215068a201401072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684049055 1250 684047805 684047821
    0x180a12050a02010c17030117010e0604110411091302250c090e0c0d030f0f050415140c070803030601200714060f0d0c020606030318010806010c060f0903180506070605 73
    0x10f60003001245c49284004004a04441c40c000d0801046103488000c01400030200d480c01c0e55100705850150041d8410f40b40c81a461819801442d13a4100559145090512040108048141c07907181c80603016000b01d8800c010b8003200791219151011440c111411040c1038a40c80403910440c002e03411003a450352842089003408001e007420706903019110340c181d0703072881c01d0041074503141400c850001890810080b00d000d03c680c0c12751f002d45074410720446500c042e20070261245500c10503103c08030301080c0301410000e0070034001c81004084001c0915a2894a00001860001d21120118000004150050524500140120a0326111094401080f0b03440300068042c0c01120082c030689400001e20003001c082d15041102c00c010140c0880e178503520740d4400c2607200d004071413524031804604521001d040d845500c0b41078000700c0c1030400754074840141c0c40303030802c0c0e40c903a602409205480d001c4840800d58040c035009a100e0003041030740500340c24400000c0035441903081c0588510340700d5010504403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684050305 1250 684049055 684049073
    0x30f050906220b070b2e0905010806010e0112110301021b1b061207030507090b0415020706020f0d03020927010305010b01181701090602180a12050a02010c 68
    0x80a80203051035115080108441001081104482c4010100d9480001c0700e0b4001c805503900968400b0212800359910140701c03e1860b41d100d1205041e204029000c2040305000300d08a01070514000c01288540c1804800b502c0e00070180e010000e444c0680c3e004200e6980d40f51002004144e0104030104415004400a4060701900074102c110420070031100d6540280003414001b220b41e180e000321f415051540c10444c803801494500404040d074400054000c9111754030450740b10754182804441913443d000c00314030790b4200381c0040e02015904450210159010051140206560310040001040c030b161196101c504107003e000905401040f08000c60f40c03941401200d10300c0e244140042120983c001e100030050130310090300d0039460a45510000d5215454040c1e444040aa6080443e80383c02d415125075907c0c1034000308155038506400000131064001000c00080f1010140c2c0703d41440c1003084060550b82c0d000343d01202c455880300b40040e9000c6041c050035602401c282e0900b890904001101c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684051555 1250 684050305 684050317
    0x60807031407030c12050705070f05030d0903030603020f0d17130b1908010611030a080613052d0f010e070c051504150e1e0114090303010503061b07030f05 68
    0x1841c11410000c055605a00c5405a01c3d0705580d1107568202c0500024200d400c240c3d410740000c0e90800030a0041500300e140400c03032522504c1100d107040d800a040004841552038103c00203610b0762010010340c54588450220810221010400140181d9034500d0141240145030540400482d20b200701030a482d0412000f021030160b85c0d40c0d074560321000b4000c507110225050012405080010813218400d001d0111010000001585003880f241d20944191b00024403459000750568030140d81201c140c001d03035008526800c204030b0f0701c0c408005805104080ea48078010148003007400c010f0245810300040d0f0444510f04a003c14079200d05d41d0898680c00d0390030020b0142e200e201c8010700c001d41d112801d580316600038495030302d64a04604003982a00d171801054807440e40150340141c255112458122281c1e10b6407800050110660300e0055000c0d0001c40301030300541c05c0071004115606090086070381c02040d0380c0329a60012140080b0b03441c1801000006400c20222850501c0e56900640c11030744 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684052805 1250 684051555 684051581
    0x1504150308070b010905010f0303020a06020f2a0c06090d0609030c02060a020304081009020d02130612060501032a06050703091a09150c03040303030506040902120d0e0a0e0106080703 80
    0x95505450f040903c519070082c814803141c5440c02000042246400f560f4005072581640030342018840e545a0304040c0d085130b2080e42040c1810086880c0ca040c02540420316904460151008400342280c40c900703160311803400c1c07405000300300074030303000350344d5900c01180d0301984182c002070014114201110044100c02d0002e40100f000220100300580000103881194080c1e070464602c5000c0c04e4150081c2d45000000942111104e4094401480c01c1070b26544200c04821002804940ea103400759891a0500d2007070740e00a6030b80c0014818000041c024240b081403000c1c02c100008855100e000c6143c0a900c0745808110002c06d05c60f0425205481810007854202211520014059060141076001000e050322504811484000c20251541074500003035201c0081d5061910b0350724103038050080108440c0d4000d03904e000e07140c0140d8500614580184d1006d00800000589400260030010845280381c822009040c042008060043c10a41560f070703540b403c103005480704a015030140c0300c0010702c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684054055 1250 684052805 684052807
    0xc3b04020c060a0605150f1b0316020f2b03020c060a26010b0d0e07120501050403200703060207030c0501051602010f021204060b0102070e15040608061504150308 71
    0x160441d0000b65140030f0041c40004105103a550001c01140d5091480101d00b650001e00015201d00303e0744015261a800e40c448000d80c040f8a002e0240c1150f10604a07102c0706007c10340b4080035030418107540300c0820f0040c1e071908482080c48a40542d50b04031a49034006a101901568042520920030741c401e88201074001a16443d1400e0040d000103452440e080c240802c0c045003d4615080407c581c0c1200d1144d034103d07241c2001e030070503070f0090306984814014901c281d6a00050901e0540c00c0c00f100c0c640034000005090400303150052400b0b820303040c08107001044480d004500c40c03010031003a00704c07079120000681e12000e80c035007038460a02840740500030b54a004d04100700da0003400d04441e14004294020008801c3d0403050300124060244003010100400001070009000c40e4054491309005004031800b1550390360500207108002c0710034a600c0c022a85030300c0f4240c10a80a224080c0083d00058000c5107004850400f016075200d5205114a844141c0c4802118090303242d440a907800a07809 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684055305 1250 684054055 684054067
    0x20d021614190801090b0702031309051003210e12280203060a0603021f1b05010905060c1e0702030c0d1104021b070e130b0c0d06090b0102010c3b0402 66
    0x83c0c0d000300503144007507861043c407100062a5902c088101c81030962000e200c401c001d810a001a802088020400c203030f0015481c01c040003152002c00c1c6881d450b1022103d500d003030700360071000505101c00d03030110900822040400e0400200040744400e10052401d00580801313035903c0305034000044802012303400d80038060501040710503507002070090f24000d895000c11008600d80250040c0200d924040000b03a52503040030072040c0f144c0101607030601403400410300101c140c4034941030240035201408041c5e0000348018100c0d0300f046500d22a2400421003904110f4030f070300402d0b15900820700e486e2003400300b480c1450801448154031040140050011511000845071500031040450084580c501c908c260000c0c806e109110350320b118424a200d00c030b5844405650340030b000700303010345602c844e10400d02c400c0480a2042c82050000c1240d000040341140000001900f120488024541000b403110b1510a5401071111201c5c44e0496821002a5051001d601c25007104440000d02d40c1c828000900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684056555 1250 684055305 684055319
    0x1e10031116030816110a060b030a0203010c2a0c05042301140109140109230d0308011706010f120809031203010e090307030f0834020d02161419 63
    0x782c50300c6104d12000c8055500180b1506446451a9076203c003040e9001c0300e0118000303100c80c0c1051900d2540079080340d0441c0759550009096660800c001030019000f601080440b03024041c0f8512608604080151130307007459110055402c2141c005c8601580d1107060b84044080280f01644850b105460682030550b1510b18180d840d0303411807503060005815a401186c421516981d0301c20404058641001c21480d280700c91503410000440d00c4421000d0340140d0907036848400d80011000d1299441a009605298020512603a100c0d034105850748008014029454003420803030a4410030055483c0310015460144031512031180c805825000d62007090b9040740f075500103141607071059041d01c05165218a090740d0303079028100c0080d0014940e140c0c03481d0b88134001c41c1101e4103c0165903d07140050743c0d001d580700c2900f078400d02c600c0361403d030034400300e10580c2d05208503103551845201a140c43d0803841ca00c032446102178022920421301101505000c1d0380c4030316442d0003030200703692000981656044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684057805 1250 684056555 684056567
    0x801060602011d030d1e0c020a03030c020606090613021b0601090c02150a021810020f070f0501020a060e0312040326240f030a111e1003111603 63
    0x100d200301660805040f41c600180112425600d580b00c2d40007035081905004490010b88204900100e48a0500f52076000400150003a942c950009400801c182c18030341c60000c04840444943d18210b4010109200f415590742e509160000400c8800c05d01032000780120704003d101d4428a80c1883d101e65100c1e0181e80008590390307040b5480054100218151040c05030b80303641040650621074070581d8002030049055038003a005182c2c1382030101c1c09444038000411100203a41714183d0142e4071001601c0c030944820003401000c1d1407013440001d00c061a010010f0350310060400300400f965103800a80400e0300c41041601d82008080740120428140b50601800100881941e003001425030810300c2001f64066805500451500000b448084d0199080b003480002d800086a480401610b84a0040d40d0400c03504d540329014042d09203146a420b000c1104984903175403400c1c03501c3c602d01c00c0d0003040c0d030303c0140070980340410742030120709507001c0d5117810440c0c880e4403804e44d4402e4a4050390b40c245130b407002d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684059055 1250 684057805 684057809
    0x90e0d21060f050907020102031e130204060617010b09010507082805070b07081603090203070503030a05090315010605090616080a03050a0525051303141f0903050d051e01080106 78
    0x1e00c49440c13a4466601c120f0903407004642d090f101d008030080c1c01c03c2c0402c1ca80316282d8071440644030010964021703400101550b03080d502000000355680e182c113602000f58004d840c01454060240b500d445010000030340b4078010310394040c0c090351004c29102d0441e850040081d90782c0003c03a500c9103402501043c040c00641064070f0940d000d0241c0000544aa0300484807140a02040c100c00710f541002c4000840181100c58022601409100c80009040d142000035108144098076501d4440c140c0034107142c50103594900303c10364061030400411a85030084204d03940d0000550b24555905182042040001020500241040310000704916090b070b00da48024050000c4071014850350301c4c0e04a840ca4901144194402d8550580342d10404580c016001880e2804030048041e07030241c2c1c0d903101c60205032104014285542c1200300c60700003130760001c0e070241c0c420f85a40700100100c1206d610000c009005070b0070f5030041142e40380c0209050710844030300a0410600100800c0c550b684031661107001c1c190340c3c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684060305 1250 684059055 684059059
    0x21201020c0f060a060501020a080c1e0705030f0a0f06150b0304030c02041b0e12070e0408040602070506070b190914010f06080d05030a150b071407090e0d21060f05 72
    0x11010a03c4c01c4114014a0100d0304144d0007001050101d032501c030419403140003560054441d06400302c104001040200c00400d0b00e00300a440c40034038001c00d01d03090040b00c592840341608888520342c00110719041e0412200d42001c1d000500b41840b1028242101880e0000b2001507070200420040541c03261913807000d103200755410b0000306c1c0c103481c2e841e5200061031041400308030300203060070040c20710410090700d01c0c04c00740407910f4150741c4440b0300030301d8074095809481e16240028244805901001010010007082c1c8460f490802c8a496480d210240034200b0014501c010200e040c0d5042c007a00144180b070b0300104040c040d028143c0c0454001c1c0a4401000b8200d41400f070300094511000c0b0f00748500c4202a11740382e15507a21102d0020083c1807030003180b624403240c0382c008658440f1000182002a100c0d203000c1002c502d00c0030a0a1a044083d0702003a010743c2881000a4010001700303112140c1010360801001c0759180d20321400c3d1038403000d280101424900303040090380a00d80110710f8116081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684061555 1250 684060305 684060313
    0x1241e17090d182102010513060c021807021009062c010b0103060b180d080313060e0d1b020321040906120309120c0306090822030506070c021201020c0f 67
    0x100e0102e03a40079801c9413040c04403005440c000310902101100c11100414030500d000c901e00304603d00210418103142d00034a0020745800600d10460030300c060002010340114001d60b5003803030888402541c0d28a6031840c0340100740c07a100001c0801003160002a0f640102c01078402c0c0f2500ca84482c150241c005800c418400e6003480303043c841a5000388209003c0d0780d08440ea0a1800481b06d240d241805800381400e60040700e000094800300e0007403800f07180940744c0c180c202d0750509030761f08000301580c00403039500f00240c02c8180000001c40d005115140d03650100c61050324200d03003500002c4e040000c10800d41c070075801402042004045c0d254000c00c01c0c1e070742c1a881080b076591920240d011144040b58014007046407107005005048211b22403207061803203140e05622046c1c982e0f035500184c40202c0c0d4200c501c02801709035060340451030388110103054a913460303140ca5503142da160955110005002c0d030041c0002e0b05001021364560030356691447c004103000b99500c1d0040d40b00e1503541c150450004100b030003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684062805 1250 684061555 684061577
    0x1110a08060f042c03090907201b091f090e0d03061404110409021207081321050409020403050f07060914210a03030501241e17090d 58
    0x40c0c148241c070242c40744d854000e50782d041c90390000001c0700d108610010300c610040c0506c1d00c0c03568070b58004034881c80f205c0c2d4034074140002003034542030822413000a0741e034141c00020034060002c091078011007004a0844400320a03880d50070910b1a1080304807030607030038001e21400c0415648000d402140d21041c2910440301c07007200088040341240c69074020390066500d0481d00e42e00390b192039008407a50015406d411450590b8400010040768094928020fa00107010200b245160f000f40305640d000c0540c1d044d41007104155500c40c0d01c031401400d60401c2c1342c0c200ca40421111840ba80c2914041c00040c942156119100d00b0010766601e92900105090700c141780b00407440903c81c420510444a4900c10201c039100c000d010000315002c110740305080b0080a42082c903100030104441030b1b5640c0280c60010390755040444c800c0b6401b1341c0301c000b418442841600d1070106030f40001981d041824407566403603107041c0300e00121013600310b40c00721201210202050100022000c1002001e0500c140c0390008800b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684064055 1250 684062805 684062809
    0x5060105130b0306131b090b0307143304030c03060c02030c07060e04021c0504021f0e010c080c0601030507060f0f090306050a1b0207030b1e01051201110a08060f 71
    0x45444020580540119010903124483da041004041d03104070b44032108905001d1140400c6d4017541c0c0003030809a03c400d030f0301c0c81a007020700c1060003400940702c10303087c3c00c149000495002902d0400c420354212070046105c6000b44420200d5030310142a001c0c40743c0c0c695890802c09906481c901040c0c841c20303e00b841c00e8a881d40000200c981c0503a00f140680340840c542401521018005011990091f400b001038409104c240038400080c01e1070480002040e04090040c0050301a80d0300710003506072102d0602d82c4800742c10625440780075500b4030b405c14840e071803440c0c00030240c0030310b0404030514400c00001200b00030020030f40c9420344529584410390201044021a00b980786070084001042c000c00d401e0000c5a1190441076000480100100346a00d080a0025550700031406150050700401c07024820132580b40310b881e41011040501c64070007610348014544280040c89098843c0c040d03080911448042034009140c1c002d182050b0a81307520a041001c0d0030948101c510512a00403042d40c54614 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684065305 1250 684064055 684064061
    0x406170c0301060807050f061305031f05100302060301091d031911030a080f090f0d0207080c0612060607021503160809061902160203030309030a0905090705070f06060509040506010513 81
    0x2900024810303c1947e002c0c0c4280000c1d54041115581c1c1428485004a0a030b14200a6052007240400310410105080352196048640180440060044000d010005a175036841982d055800048001547d5800803800e08111020301910072071a00020036009800d04a05099680c00c41103500c0344001103010410b40c0d9101c2c4034600c04007021030700440c0400c0d820383c1c0300700e0041d5108544000b10742e80452078002080c640b802c01a1000d00503800902e05111054061140e00c2da026000d50b00b40c3c4c100f031496242c3c20100100188000c0c01480701107003440c195030380ca421124000e80c02440d0a956403e200000c031404d00039000640010550040c04143c54600c0028075500c154510b401c03030380c494411001c1da400a90700160b41040c4034a0940810340c0035a4061000b107004802d070300011613881180c2d80b0302038510b0f4041d40c80300d40300b05050020042140d4100003100c00320742d4408004080f88626107051030041c003c5410a6800c4a042d104101c00c00500140250507180700311046800d20126810340340035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684066555 1250 684065305 684065309
    0x8150c07060504020a1706150102120d020f040e0f04030f1d010c17130e1008150604021204031709010b0d030516060c02061b0a050301030206090406170c0301060807 72
    0x448508106040c04180503a0080f070300310f032009000100066981c66481c1c0c000302c00341c11142882e000001030018540303464601030a000c40a00144c0441800c41008001c1401000058000140c0014141e0203c21803181181c0181945d650341132030380c4c24040c0e180f002d11030f42280d003180810400001401402d0084050744281c580000044180b484840011a140450f50600700c6034110325022a034540755003180500206107018015115031031400481505c00385020b020402c1011045000703200840000c1030000d104c0700c0400c0e11551689890f4081030003849032007080c090300b00c149000d001c20194041c0e0721342d54030b414401e00520151150034055088402c003c0740d00e58003a02d0440c546000a0045016243d59a980068201e9501d116110501034841d6281da09006030440d07800c0214001046010016442c80001d0365070401300c10b11805030040c0f2060101034480d506c00300b44508141d803a5004500600865101880d2450701590101c0d07950901d2591180700e5424444007040c40d03c00002c0103c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684067805 1250 684066555 684066571
    0x406170a1413140319080105180708070509100531060f0c05060a06050901060203120112060b0a0902090f09040203070302041d0106260c0d15020715060815 68
    0x4070385840700414007902c0e2980c01203603e80702d1030000b20100b640c20720140441983c03601e41e2404029441000030031569050300014450403000c0401800101d14603102a4001c20030b0401c401161114802680d00b400365102503070340b1401042c400c05a4590180143c5400d1810303100c00b440c1c0c0d9014407052066410000c0d84000c56508105041016520500d080314400e050f0303003414a800c4003e41c56803818a40308840340b44240c6d840356010070842c2809520140104024806142850104181504000818030a00c0c40001c1804468802d105040e40b01000300030008280403251651440702da0080d400298400d48144158680070040781443e80e5010300c1694028007600c1e5050841c4c0c00c03c402041c1c0300e0051841e5803020905542840401d2081d1400740c08421610448031a007417107421898040c1e2080345015030400d070300b6030741951941030400d00c000d54002c25500ca09018410a8002070046180c0500388904e007011080211500e6808801074828540984030002da11031002c0240d0102502d43c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684069055 1250 684067805 684067841
    0x501060503061f0924020f0a0305181201020705060603010f2711090a0204470c0712020307090c020d031113090c08060f0a0521030406170a 61
    0x110304408040c407483c90425107007489002d00d03855501003162445941510450b0f041e468054420301d5030100b1582c03007090710f070000825440000d903070000c000e40a02983d69400e001400c0c2c01c80702641d182015018450003030002103486070040e050030303540c80c942510164065442c2c1a0804000b003120701072082c41c213000e08228040c000c400003240c020010100c8040d41c07600c20145c2c0543c0580e9600030980d005102d10240940c80342d04105031010441c3c0410710864400f41e000c0c0c048900c1e03070729030031440c0700108480451b1554031040844e880440e1040100822650084810100d42e040c00400303442d101c10b000780c007221304203038445043e801101c000a09075800369101d5018504864403940109400c100d4540d0001c2c24034100304030b4503946d005c03e40c20a0030580d485801003900f41c2d0b0b1101c04103602450031580f00c01c0d884420300101b9510040703400303094050ba440243c509040104403030407500b00341c1c0540449588540d07a4030000e141407140c0c3c6942010703180800105407070b07120034001c14841001c41003081c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684070305 1250 684069055 684069079
    0xc010b0a05090108120904090807030216090612260d060305100c1e0e100c140c060405120304030b0f07020f15062107030b10050a150c020117090a06050106050306 71
    0x41e20254002065003030340a83c03206105d4002401c500098000188aa0024403070a00994002d100020701d4ed08000b4881d8901a0b003003020780b5080010f8050190400749941006640440c440c000d0944a540101c0d11071000410040202048d404242180d01030410707607400c443c0c5001000c1c191042c0b0821840000c541288800e646c816418148a034038689040407105200c524010400b004880c504102c081303602d0140c03080c184089000c0c0300116828100240407850b0850300040c6141c004da02403035000310300c5202c00d2035401e51300700100c0e000755411200c600e145190009407403902d1102101c40000502604405444202c80054503401c001801c0e20700300400c4c1c2c0c4010a1000148411210050030f01c4204540740e10141d06100801c095805000c1a424a01d00882101c4401c580e6030704c0940200244041085150107031410080c850b03800c1d14041080305010300040706c002075136074007045000b00c2003400d00292143c00108040300c24131a410074800b41e07030380382d8098980c1c0c0011038407542c010310130900c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684071555 1250 684070305 684070333
    0x215041112030910180906091a1c03030b0f030114011e080d080c0708030a0608120c100e011104080d0906030c02030307081b0a231e0304170c010b0a05090108 69
    0xe80800b0741044001d485e0240d55012050594100b0381c008002c0580e03c0d400006048281e100644a0359070513034544504c984821030407070b003050710403034003404041d546c90f04140300d9600e1803040441010014020f00a05072500300240d002102132046940d07041610050504515000c81884100e0700044064040e01030192000c2c0d0301842c00804200070031904000e58800100c1c0b40703020351700070b43d06050006241400c02d80e06518080c00c0008036451804c0512507000f040400103000e0395042510b6001280b14803074020030a02500380c90142c00300016002c01d0210f0b100e2000141e0040407545a550000450340d50b0f1020341c01c03a80b50a075840b005800c100700203000380780194240c64001540d0346214800400e5441c980756241c1184012a0010b441c12100d124202c0042c5100d000800705003a1217440c0800b880543e107920340588540b1100f01c1004000541400014150842ea2425420b041c0d07a0360340d01c0062442c003e2030314440451242440c60004203890500341c03500c038140c03105100100451113080c14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684072805 1250 684071555 684071567
    0x117010e070302091e03070905160e120102070308071d100e01110f0d17060303041206110a210c0806130612030207080712050309040207030215041112030910 69
    0x310a4042c1502000100d8494a0740c1942c0c0d020900509024511031130035004042c20083c0b181c1c0010249810841440a115480007400c1c03500e1800d03007800c00c03010704404041412540c03010310b01001c65101084040c207141c4c00106151040000d503070780c10030144185a1100d900280071a41c250041c03207150030407800e103018041d080000803050400d082e02d8074a1400302407401000c412090304a03040b000070f080031644c100e400b500031344401d68018101490030b8000f080e07880c0200d2081401d1054008454414030466500203210100d040c0d103059030b0b81202040c0034000c3c3d204034020090088000710030100c2c03034103a442501c4a0114039a544801781d250102081a1110101035403e041a624500010f1003043da4420504039842600a800f009281184080c202070389a8403682c0f890040360b44501c005400407044550400d0201c074016111412401c04a14158000c441704541030607403400c0c401803112008030105003841c1142c0303600a2001c010041a1640141d120154206104025004495020705 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684074055 1250 684072805 684072811
    0x71a070c260c0d09090b030f0c0f0d0501050f04020114120a050a0e25080703050a0b0424090203010b0a1a0306030a02060a09050102010b010c12030b01050415020c09060117010e 77
    0x2103641410b01d2030300a011401d090964520602280d0307459401c202060040c0641c6000c040700b06c001d0301d5141c4108801c16215144003241e1449404004d2503102e00340d8400100c00b0080340c1140081050b842e20740f0785003d4040082e24145d010170b071280300820a42044100302c40e0b2074400c9904100840e02c4611800c005000b02130505614646c0303440d207400c41e40508006401001c00072030151400c03001001c41c000405074280c2c2101c07045030455001800840ca0008803800302c0782d40b0505414a0356120b007000850101519007030010020284950303180304845810005030180224020440c000604003000001a01e600c200402c8071500d4030400000c03071031303000916445280070b401d68014102541c000f40156014243c20301c04100c2d0b0309000d001a590910603a401d591702800d21780142d0405494a041ea00310300f503400c07402c2584031a502c8055034415000d6900402c02a02c40368044140c3c0100607480c0c0714900c004500466035100020100c4d8402d0912040c0d0030ba00284051450742070140340ba00c0d1000003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684075305 1250 684074055 684074123
    0x20c0f150f1512031608040f08010504081b01020904051e010e070c0303110f0a180504090f0b0406140a290d0311121603020d020609031801090506071a070c 68
    0x140b210010003044802c01a4805d4030460500313541d01d04080803003840000030742100645a1600d01000000783c0d1300400ca402c900358280304136060119802003d4068410014402e40090810040c1700ea0114003e4041c82d070302c54010080c40440c1c0c0c80c1c0c2440c20f402c0300102d842800085950301c0c101c011a00035801304a000c058001440e160080c0c4600c038100311761100b0383c0c507800541901091400760006807804009030a0840d030502000800d5203030151410030003440503120444000c0403504000d0f140d4022650484500500e06103441c101010030002c00400c2e100c40442c080e07003403080385542000811111882d40046c000182c0300290f881c129100c1c203104030401554410050309660003510200600b54012002c148111820440e190085c201011240050155407081c01401840f640100940301c01e841e002110050004801004a820b0a048d500840d08190001959030510074201801c03441100300280d002c5035516452811101c20284060282100c03c10913504101606846035000c0c0803801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684076555 1250 684075305 684075307
    0xc2103090503040b030709080105010b070308060d120806040b0f0306010306150e10050a080d140d09080304061b0809030301090c030902031b030c0d05060f0703020c0f150f151203 78
    0x22079910325146510076009602c00340004020480c080313600901391006009250000e11565250609624650185d0040242400f41c40000201580c480000c036a046980041404020b5202c49101510f6581c080c0e590602460a203c4956050306100c01c50207031124003e002086140c0c6107445580080c46100f0907411400da080d1000205040031104443c01820907100242e4444c1c50b090400c5141c00e2103901c03900c015000400c900384800d400400440043c4840d0401d0703940c0c0c0b9403008030380740202030740036004004400105c180418840180c1c0303d41e000b0200c00b680700c124007481050588580d80c003119950345540c010001403006600c10f80103104500c81078100800c5010a542c00030382007074600d01001085148941c0c050741075240401204950319002c1d2040307010904c0586420340c681900405c3c441c18038003140d010594640c401e0b81140e02c80303241c0906590385060024482e07919502c4903002800010001c401041c01940081034031405240606086080b9603030310407e0161103001c0501e06401804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684077805 1250 684076555 684076571
    0x60e0106031b05040f05160c0309080312090f07030b22230106150c080304020d1703011d1014030a0b1005031b0a0302240708030a0c0c2103 61
    0x8090315610307944600100241d20018140b10500c8101d400c0071075140305c458208030034030003040c084000c0101642614900747d86002c1c11420162070060081e4040d108034807000a005202520701e90a050040b8070840654412000b152030599981d813031400003170300203014000450201c40701100094031044512a1100030442c032030b1981c042101030f12000c200041e5440d40c1c1c00b01118828410600a0b0503131040020144194520041c041443c90100405403a4000040f809564074400e403085440c3d881180d0603c0400a90402d1103550001c1c0702d0302d40001d2a54003e442c02c06000b042e0103205102c0161039600007450715602c4000340ca40401c40981500404981c00082114040c51503c60b05003600d0303086140d440c160500d403400b01401030252645421040885003540e901c0540000c8903011103031556400420304218a000385082201c3c00140c0f40007648074200580e0780e004c0c1d031194103c80400c00480c0c40d8810180c40c1001515030040c45003003022189203030f0440e1075940c0455110140341c001641c003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684079055 1250 684077805 684077813
    0x6060906070f0c0b07060506040515010c1104090f0311010c140a211a011106070e1201020c0d1b020f1003090b04050a0c2921070e1516060e010603 64
    0x10056082290358244c001a04804c1c054180500e03604903a058604110501c0d00341103004100c0c041898483c1001f69041008050015903583c6030b481343d0340244100280da000317240c403860b01510407208501007180011000c1e202c2d801841854001889521440c4808103203640103d041c2e072100c2c50203028055000c02c21200401180c821521454850000040f803d030680305404141105075803540c10030001c041110946c0201003482504900359080c01c14940d40000001807180e00c010b0060380056101280608100c0f40008144103e003030103032a500501c0341400c00c050820b501c00103002e500041d58a80e030b0340c007600702502e0120103500c43d4a00000c4140310303030751022503d40060340e0030385051744150f0254003402144514000100101c40a041c417283e4401d0584d220300000c00c14a0390454004101e1841808000080312481c1c124100c054080303141404010308041c01e02030900d40501c410120a08203a24000101c2d41000008524405801a2651148090a0854040c0040d552030b040004001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684080305 1250 684079055 684079073
    0x10c08010f03034a061810020106181b11150709170a051516030c12090501020309010608030406050f090d0b010608040b060102060411240c0102041a0306060906070f 72
    0x1c1c4c500c00e90004070000207007110b111040c501c407040a1040e0002c0041300b04040f0a0a0000180c40c1d007656151104c440180045c5d0040504d584900e450507003001d16506085036983c03100c110032412030301030100b8840c45513041324141e10782c3c194020180c0c2b003c030041e502c181c076241e00300354000c10030329004503081d40b1a10361245480c0c002105442d42d130311000349501006410301a079115132001034101e007140d01c0c004080d11040b0301002010410b040d070340c1c0c2c1c808c0450b61060301515079008101c0310030b0120900381c0c50a94005d5000b240e4428403035107841b0f4003191022007c004c4a00701d803615982c045c00d0a0036161444059030000a403d80c1c003d1202075030500040d04050001d000f80740c2920b81412500c1c01c0d0605030f40f0b4a00c001c001c541190021410000010500c15a0101e113880c01e0b201100074054011862901c240449580d0000030404540030902c5603054000300141c4507440582000d0003402d0b1001c42d540d00083e0317055036008109005400c4171f8240440540701c0f0714062440c100302c071081515101c2107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684081555 1250 684080305 684080387
    0xe19141006121d0a031b02090103020d03050c0a0804170f1209040b030a06090308010609030b0f09010914070f09061419090609020a0e06031509070207031b0602010c08010f0303 77
    0x1958004200300004c1c036400c810110765214140700c3e510080c406e40d030b000402c040b00c140070080c071540c000fa01d0001414441d0080c2c8400c89010701c11a80c440d526400e080007160403521a60114441c9603283c0d4080c3c64010511040c0310004400504140c01e00c116038a01c1d03500311007405500716a46440c2d0a10740e40e0108041c64a90b80103400003c0c064585041c02480624140c010105010079103501f00001a08001c159910101010b00042c0603100c8019640c0504041c203400741982075138900c455542640858004100c03004140c603032862070750703400880701600d2143c403410407803942002c0303140c1c0141072601d000300707801a0f010041d403c0d180d1209040400c45186401541c00b859010034000c603015044802c00003205411240941541f40250300e90401c208c82a040c203024418140c04200c0c40b500030411000603580c86614000d4030020894100c00d04d00071445900c00540c20051020801c1f40680c06590580748031031602200981152429562046070082c0c189116104141010f2058511070141c0c2d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684082805 1250 684081555 684081611
    0x10e06070f210203040e0a060e040b011502010b061801050903120406030605011407060f0b060a0c05010b061207140706021602030c0906280e1914100612 67
    0x8024400e60420a0038103416001c1c542c241080b0344504140d5035000025a0104d8a4032403503400e5070707610310b6034481c0680072584c0001076466202c0203200c10480d012181074140d1311102c5140020020501c4101c0c280c98402c41000d80011080281e0740031a2120240e20f101c2c010b060500c28030b0a541c0b03801107440c0804420200c4401c10000ca0148100c4c0c0d0305000d000e0041a092038824001800701c10004510b1250340c80c000d00c01a40c441104c1c0707486980741c0104000301c00c020146500c0b200f203404041d081c0040141d04032401d500e4003080015516001d02603034000d04a12240940a5440300f0301a0340314095481b1300c910310340d000d010710000144c590004002c03401141ba6080d00c1220148103052411007000ca100d0300c9102001d0801119803a012422914a400d01a2250b24003800d14542d90030810141c006544446502d02084021010001424201c0c29039034010002c451501641410f1140300750b45601084500c5441000010310411406080641503080003d403c40c2141d406602e181c240f17181c1c0d00d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684084055 1250 684082805 684082823
    0x417032206030b090c0421080f121308070201050a030f02070f0201020d09060503190e0118020a0f0302150a180e060a06030501051c0f120507120302090d11010e0607 72
    0x1010007070340740c0101c0101103030513940201c0a0801001c3c039600c0380558014140040000324030b10a1588580c90542d40c2d04c1e421008603913841041140c4d4101d00ea1026031101d4444040001142000c0c0d00111000034082e0032018160030510f859004450580c401c203401d0040549412901040c03407c0ee10050103c03910405000a60b205184006400d00c8541c107001010701c050510100b00450b081b034200ca0b030000342900300c03003041000501d440c0c0c01071034141100d07903c43d864683c118801580350864809541d001701c62074411a80d490380c035000c00340d810b804029000b106084045440050100151420502905082c2c40d40f075034070034601003820307417590118842591070f00c04e200140c01e15a45001c041c105a00e0306100560410002c00e0300e042c2c2413084010100704d052030740400e00070444804031011b6801000314016081e5004002c2c0550803e0f242502c081280c0c2500201050081c421240341050103082c0c0c5882d82c080d40c6030513941c20030291685041c840e0015078100b8a54a0000a1641511680c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684085305 1250 684084055 684084059
    0x15120501150905040507090303030507260601090b0c3304030801050108160c11120d0801060e0105040620030d0c0c060e12030a020f090402040602011a1504170322 71
    0x3810031900c0d40c4204e015510f06401d2040b842e500040b00403c1d0794050070049000d446e02d0b50125104001c2d4807074080d288051707002c114481c09100300300c5030180f00242c0e50400519152035a8103094814180880d1456000383c9060f028103148001d5800750300d8100f4001440c22003039852050b094202200c0131000584210010301c62584c0050301d00c0d0b0400c030a199500341400d0011405810ba041d010006840d03200003144645071680d40c11404407009001105580c00c8481400c0041c10404080c041c1c10082002c05054202d030b540314405a6044800d02c2d03546941e07400400d001e1800390807207600304645900081000c0310506045000b182c0395829903079644c00c01c4041e05d0a20f07004403080403098201c15003101e10400050700d81c800035071350880b031480340060f0303194a44000e01109104462000760050b0010400041c07058040d07000c1d041e400e0000680c41c98800340c0c00c0c100011412480681890580e042c0001d01101a80b14800e0404104504c2124074003000100902d21020620501984c881c03449902 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684086555 1250 684085305 684085307
    0x20901020d030509030d021b07080d0f080c0d020c0a171206040903050a18120c050405100602030f0901020124031407032d12020709060812041512050115 67
    0x50240c0300700703203141c00c00103402c028880c0c903200d03c144082d82541940204408901034000d603244140300000300111442c0c03a1792420455100d6103610103400100d54000508002d0701c5c043e1800c1407080b140b00c0941c61515040803503440003900300e403450340e40e1441303174251f00000a819818010380103d5917881054403003410302110392300c110300201030714000ca080400070f10009030070105a440b00380150801003074180d0f0ba20351404000c000b9501041101860400c8241405400c08401042d01c10941c0c092140b60f035840e01d0481329005038490000141d10401c0b51103040c2400001038008920140b0010807030780441c2803841303071480207101c01c1598008515010010000001d03161013441690f5809020301601e56240c5c03488500403d0f6600303810190f20000a0044250407005000c0103500a0280d00701000302d00d4001c2d60349555019815403246005004a41c180f4002902c0e20801810b80c0b04030300c5d06040c80c1032485e003004040d12a0050120105004600d50305031302580d070280c0007103046d182c3c1d84214084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684087805 1250 684086555 684086563
    0xa200a06050108010c03140c0a05070611030609070c03080612100501090f0608150a0b040908120f07020c030a0609110a03030302070203010b0612040f08090d0812010803040506030f070e1302090102 86
    0x21505c07040c18034051486416a00f070604465015403400c030145d4940d081c45009882c1c520a401c4010b20952500006100ba00c01010145000e10340a5543e654140e9410700d0540d95054030140c003801040d003450005d0640e10381030000607032040803c01580c028042c007a500c1d8040d140207030071075000c154031143e15008015803071048800070900c010040c41140f42400640078510b03405030900d1401754903400ca8155986840d00401c588552042d0300554802c8615015004650140c81502d4003201c0c207000300707550b00c2c4002a071103e00d200082c094203c009059403160010610745c0411203040310514410481662204101d20085012744c502603560700c8140f042600719040c07038045602c560b80610051060b00f40078540b0a6006c1d900c6400d00e480004a030401c1c40140c0195100180e1000d0880c130701e1001c00010300040d00c0c0200903000038000e00c0e600c0d603604036181d01803070250a03004001400081ca80c00c040b02d000b290080d0040c10041641c62011010a5001e100ca42010030b4140d00002c0e106903d51f130400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684089055 1250 684087805 684087821
    0xd0201090510060f0b1e0301080c19180b031c0f0f0201150302010f0915050706050609010614220303030225020a05061c0504050a140a02060a200a0605010801 69
    0x702c000c00029042007070604010426000e21a1501804640c0ca00304012000701c4800e1841040d01558403582c0da8400a80d8030189601c40340d00602d0300c0310460194a64451220060318038a0b000b0314102c000208003a00205a2402100d0b4540309188003080c2040c50300741424032001442da1902c10307106404201401440644844404581c5840080c602c0c16882c200000203480d42464580c02c401840002180c0240884d04203202383c0001542a04402d5001801001d900d40701d00c1d01480f140d0344820400041c011300f4404d034401706c0e5214030600d05000c0b43c94000c00030107041c03141903159144040059041c298040e00103c01107640062072103150880780d40400764425204909600c100c0c6e03140d000ca0846c1c15588507150080d06c01244c0700042e00c10310b140d51000c0d011383d803501704854502030070300565a5990381f00a0391a000f505407500d17906c20b03000c640b041d14140c0203801c603403600840315401c480c0b1100742914922854982140040c2d00081840001d4180313005040204165043c80206821240d20f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684090305 1250 684089055 684089083
    0x90510090e070c03410d0e01050f0c030c040f03230a020310050a0b06031608330105071406040606050a030f080f0c030f030702010b010801082d0d02010905 68
    0x9100c2d2400107584507001802c4e900c0300700607603111110068501e61751001c24140c40d98281c56051101c81007400d03032030b01500202078038401c24040c403400082880d00b20781040d0b40d1803108550040006011140344402160440c0524804a1515544900700700480c507140d08103d440c100b51401c441e4140300880250600034800c0c00203405e2071340306a40040d41d50704580e40390003202a1900000354012866900403460400040c0450356030b4a8550861030000360241c04100113380200e02107200d04d03400303070344900c8070303000409003072942142c0c1100c100691519090700c40c1c1001003c001000c00188841920181c0c0007860380100545e0500d4500744055500c00c0d00040d01a0417520010004220a42040001d0f05e401c81c4236190fa50541c040c1261052040f002058403a00c40082c0a008010041c030085201e40310301e40c002c02070a0084801140c00d58820b11840005900c4881c002d5a4504000c40140054000000100d100b002d0842510304020000155001503591584250b041c80010f200e500407542070703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684091555 1250 684090305 684090317
    0x804080604021e06030708070e03010c0c0b0106020303010e0403140409090308090f030a02030d090c1509080c030304060f030506190b13140a03120504050924120303060d03090510090e07 81
    0x100c0310214800740402880c074030400a1047c08a40c60382d000d040d07156035490707015000703001e44244940701034480700c40325104840d00040030000113a61440030050302d060320389a406241d2907440c0c5460842e00018444092100100c00700301c001041c3e611441550740603486900c0b040c044d0b24004000c14100100c440284081e07410401c07403025600e602004450121001c01d40015605001f41403a0340115035036008803a52104018003210804d400003444002c0303850030411151070a02007003e040d201d018a00c100ca01143d040014040c445000f0707040035a20a80160106600c45c000c05d51405400400754401300e07241500080581c1c200344503000940282030154085405500c1711000b0565418061101500c03008070f0b0340320701828920541c211001404010040b00d2070f4207000b0710016207103a58a102d2084021248401d240d5810480300c4000a401180d000e18210342c2c56070280804115051011400c00c0f20424010984d40c0d83c2100e60300581c4059958903e04034100b0030100110748000d0300417024082 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684092805 1250 684091555 684091609
    0x60e0306010f120c120501050f0106090302241603030606030b03060c1207050c0a05012922060902070c0306060b131a0c2401151b0f080408060402 64
    0x102e0085400b100c11104500c0700d816480e08064082001030f400000350130016008107014420150007081c000c0d0302800c40c8600a0741c2e07944003502c00c00710030f06c4000d4001d02c2019074001c5103a10704651a204110401e6103078586903100095000881c01440210b0209a45907010700c98242c0c188034040070300c0c4080d001800c09041841801105004070b54014000402c06070004503824403910640b0140040b9404a59a01c0d13024580360703000c0c1600c0903500302c90b003401a14030000d00d90441510140c00e0310141600a80790ba10383c0340140d40c078401c440e080454684034800050942e07041c0c40140390030390183c448448582e0440c0b40c04800d884d400c0d80400700e00e01003444a050100320800b4041c00300e4a12084d0041c07108142c400700c40d203034060040c0d00d803110300410700b08248800e5083c240718510285440080d000340e07245c0c070800e40d18030400101c55001500e1250107400c035190034a0000f01d0103000b12107441e02c51000e42c0c0c4841d0180e20940000a43d41c0282c4280021401c112001800b210105141e65101d61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684094055 1250 684092805 684092819
    0x5151b090607030201061203080108010c0801050f010e01020111041d0a0902150703120926030702102307120e01060608060918030f07150506100f0225060e030601 71
    0x8040c0040351886001e00254200805000350b02c0742c00180309803101100204c0c005d0502a1409809101310003255003042d5568440300d2107000c01074180c0c1d00003098020f81c03203103600c01196500d400c08040c2d810b44d9a1000b00b100000c001601400041c0400111100d070a180b4540d0b00090010207000d00321810f0030300e00200c005030303284000d061010360014649503d800040c1000c44100303007080d400c036050384c0c9400005802c0c0f0050b488010085400000d24501c03002481c10100454482100c010b40141c2084660841030030a90b00000c0706226034000820400f410000b0b00031642d14241c500002044420700e03444900012030243c1403511818100810520749451005040013400900181c4516480000655140c00b1116152003210094040b207031580c0b81d41d00c200c0d5480d408440c0a4420460154000b40900b070300b805554030a5001920003441d03411052000d50303200011b100c0402c1580140303010380005168054030841c0083e104070005807210300d440c0c000b900c400f0034498001e0083d00004014802d507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684095305 1250 684094055 684094057
    0x1523040f0f060f0f03151e0b010e030d08010b070c08010e070614030106050a0f02100c05040513060302030c01030504050a1a1005060711011209051507090f060806010804080702090405151b 82
    0x8a81141d040c80b0118401114500240289809800c8101031f640340c10044072202c2c1d0004002801c03c0c0c96101c0300110391402c055442130115000c0780003a4100313005005e034100070005010010320400c41c10358101d440b030b41c01e1825190601007a0119500c10a000c20031590303c13140c001d100181e0b0f00d10062855042c128004e040744540091401844011607860480c2442000416103802081c5002c0145a010810040c8254014840d051041d03020568031030241c0d0303091190404030382c0d000b030003413a0340080d160040d006420010700948182c095a902040415064040040d48860616518440b40f601555444e8030600c2a042a8010402400404005082c40100d101804800d09190001c20f02003a2000d01501d406174000742180240f004480394020510611070045115032501c00c400364450601c45036046880c0b0030f0100003500500842e000c1d50143c03603500d80282c010000b091030070801c1e4020400642c0152421a80c96201038a4a011200030035040c0f03410036818200650444050792202c20a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684096555 1250 684095305 684095309
    0x904050d2610030c05010228170c070810050402030a0f050c150903070801020903120304020402070b040f03080702010b01022e150303030f1523040f0f060f0f 69
    0x107010070060001c501c0d690110500316000c140001c0d424141c41c0c0700154501115640c0300403501128040d90204544d030010486400d10f03e00ba200b16540c8440c03050f4010851605281d050301c6440650881d2022007000000911050810348010440180750040e118a0f2502a40d841510345240c2000e1000595000ca5489040380c1c020390400307000041418400e003046520082c040c2d000c401c10105c82e900c11030142c0035001e801c50171070a03207840d55602c240c40f40c240c2c49591030b403991542003140244803892100010310b41041c0050001414070607141c2c2c80303d5001c2d4099800b43c501481144046081507408410380d41c7c440d41500c000e100c218448000070b0755031b0900544000358040c040002c51440c08014204010540c08603800b0b0000e04072001c03500100c3e040b9408150300181c103011440450200034050750160410243c10f2404261805000e00d6055601d40041c50710b505219565200381c5d03407180a251015156100f00140300c007109040e10084a1140d40700466500304500700704182500c8030300c0780c81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684097805 1250 684096555 684096557
    0x2070314120711040e0d110111040501050406210915230c090f090f090d030509060f04150e0c010306092a0c05012a17150402071a0a0b0904050d 63
    0xf481201c00500030300340c01a1244460301c50401c0c801e806c954480e05180d40090540000c001e80303050703104e84c070025200b41c0c0103140c0400d404000070000a4481c2a0006001400c50f110803107000c0d04ca204801a1140c13117805894003200040984c100c0360303041c4035000b881c43c85000000403d0010481c078034003004000302580d10440d804101c210b0305840f200700e180205103005292140e20301c5c0c000b12800039600141c403103c60f64407500ba07070f01408070700901c41c460040a0a030000e00c102c1c0d4840412051b00035000f80122840590750b80a40044c6c0301501403d1a03060780340c00035000043d5075200040c00c0303c0e4140e10141c607207400c00001205c0e05692a41110750218110010724400102d64016584c001c1149001400380d8684100d041c800d00d0255100c0d1400d141100c1c5480740029040c0d403c0b2151408151f03400194400315010a081d0640030b04500300041f809800541010140d49411980c040c0c0442c3c1c090021441c4010000f00e17403118850314018240483d0407042500702511000c0d500e010340d1806c98 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684099055 1250 684097805 684097823
    0x8040b030415232e080606010c0b0402040902010507061406130207110915030f030306010806180f042f04180b070503040f020a14010905150a082203020703141207 71
    0x250540d84102d04c80c0082c604c0c40b4400000e650f0086040c0c0301544d40718800c2e98994001c1d0740106500d50700c81c4002220843e0001074440107521940c007007000402d68110100c0c107001c0108407010018469016001100da004040c602d002d182050a116000469034010082c3c14410071600000940b000e03d000e507141001c2e500c10110742e558845800d00e012400161951612400540c50402d102c004020340c410402aa0b40e80c000742c4a50090003c44421580500e00100020000031125440c0701c030b200347e10034080e0304455a1110034000241580030500d48440392007400044095403418030b802180e07201292447c000c01444003d4680d0796050703101401c0b0300c08101d0000041001d001e090a411190b617600200030810555440340c10742c20ba202252101800b140700d01a00281c1403503c113155038005000c2c0607085243c60041c041c01c54032041c0042140c602541510700f048a442c110f40f00c1444242e00c680c0040410f6411800d1141c1e121800700c915000c140d00569641600038609000d55038825031090f486 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684100305 1250 684099055 684099061
    0xb0609013204060308040330030209040b04020417190b010e04060b09150103050f0903030613020403050708030705070f0b040603020c03070203300f180a0308040b03041523 75
    0xa580510601c1d81015071043c00c00501205110903007000b40704a0344180c528014070000500300c1440e800c2c0523110540d05600e02d81d10071510070300940040080f1440144001024204200010101e070002d41000480c0b404142408140300c00401c06000604400c01488a40d00000c0e607a51a610f14140034603a00c80c44594041000c100306034002510504000b400032240e80303040c441c0031389130a806200003400130741850301003043d101c50100b4a602440c00c040256113103503032310003c1c086250709040a800c0060b5007080001302195061003664090840030000c1c542d50003180c2401e501d4a410f50b040f460781c81c092142c08000d081d042c24111001c96400e800d002da00ca24032016010704502030700d034010b034041c0103120303400909210030100100c5007414903c0d21b01e4290701160320b503103c9016203040e00f020300c0c904000e2030240c90b21040070a07480f441c0003803905180d143c60340e9640b030a9400071340c00001e40d42404418030003040708031030050300b09401d0208d0070070004407140401080c640012145400c01c000403004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 684101555 1250 684100305 684100379
    0x30a050307030e0339011b02090712050a0f0c080f190623150901090b030a0615020a0c060804020306040b07091203050912151803071e0b060901 63
    0xb61110124400b02c1d246941c06440b4004d50200030915203002da4817148040d08202d6004030603813051000e1030f41114402045a03401d2100986000d070120703003403011b2081280145205401424032031070f03040002044c04010490740d8401e030b40c900c03682001404250002c02a04c0c85d04410090350107000704c03860010000c02c040040f0010440760300090720140b01055001c02611131460b040314202402e0302c2101401c520640039900c1d170f0080c91f44050001e0070040040207450303d4000a1034126260007400190140d503849a01d0045425030451380150b0801d17000f40301485400c500700b50041c501414038041c946007a81c0003e0f203031034004000030968000070001c101118400c6a200c0054608007903042c01285042c1000f83ca19080621340d5481040c000e580c00500038004a03e000311855040760325841511031103880441e00140e46d011350914030052088001280c80b03004143c0b0000c840300320364080c1d00f0f02c5051038000c5950007408240643c035008010813050001c4a0042078200b4500d00145100094401d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 684102805 1250 684101555 684101563
    0x30613030c020d20010201050709120503120103120305100f0b0c013308011103160e04020d05160306210f0c06021507030605010207050402030a090c031103010b030a050307030e03 78
    0x70b034004050545003c01c1051541644030015807683c1c0104500314103500481c280c90040f180140001c41d802070811500f041d03803e4000243c1d1248080c1d03400c0900b03520b480c0c12680c00980c03056907501101002582031075058841c3c542c103d0140035005414900307180c20380c1c100420500c240903464000041c04810300801390302c441c44600203c0341c905400c01e000002400d4900c03852580001c45c80d00c10301c001407824014450340801150700940c90741503a840110300141601400f040e0018000d804401d03401c2603860744003c0118061914000440382404e92020880c4404115494181882c090701404611900342020015811401083c616900145080410341401c41002091400e201f2400704007150040b0b400c00c01500c010310307442101d0b86c615504030203031121481800e000d80c1124800340303c54103050b0025a4040c06000000c0f07003850305a036030741d4402c0c0c14990003615a06084049611145000c0c01030b205024000c40080c0052002a11038544a100c3c0700801001e11040441d409440c0d00c1c140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 684104055 1250 684102805 684102827
    0x606010f0e040606020f0d020123100f152006060f03030903030d0903030b01021c0c081605010b1002010924110f09090c0c1e072601050a05040203061303 67
    0x2e001449815550040a552401413003003c140a000d8905c59007d21032051040b4090844280c50854403580b644007030382c001d088054490040d55107000000300d5070943ca807008100400c0c0c070702c40c0d42d40c40b411314010080c921426860f03100840c0c407002c104148114400148140c00c464100c450086582c8804006880c51207103218080d054000070401c000360030007983c001c2d8011130180c0c40601001b80c144004907150000c80c5684040300c1d102c0414070103254400c06800700c00e1445007000b5454508140c0c1c51711342c205601340041b2002d170f448401d8503605040821240006460341e00080c84a4a8030341d4805081580106602e80041028a409000074445404c9400c029001181403a0384041e8907180120030b5010001d8103008176020808641d00c88004408c4a45003108031010741a841c0c81441642caa0b043e15644a051034032031507401007041402c500400d20140960000745245000310368095003540c44c01040d03003d6503850641000096140407c2070f90348111030108264010105d0f117010381c2e0010040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 684105305 1250 684104055 684104059
    0x2413060f0603051503010c021b010c171314060a0507050106030f0f1a040314070203010605101107080d0e0904050a080f0901021c022a06130f080705030606010f0e 71
    0x110300011520b4256000da4001c60500c80c0038200207804105050070380d203003028000010703400705110500d0305564050403140030b101450040003200c49500e07402c50491703101c400c4511400c00094540000180d08813181c00611031401e90111010580001078994013034100c4920511000289040c04c01500707600c25030145510001d0001c0c0c0c0d285d1807c1918811080a0003184c00c90054004c00311414120070307130107200319450307610414059003d18000c406504094000c9815649442c0003103155a00c045194002d6041a5a00c1c9540440c0446407803410902d988001042e0704240b0001400a50225900110032002d40d40d24500d901c9600e4114500803603558082c0005401182205030018810b0042c10005c3c4260708591101402c5c0514203d50000c411b4444c0260303200e29403e100d186441c0c1c4020801840019905051441c5903010920300d500542c118240303107280c1201889881030000040b405031040e44001c0c000d4a00700f002007983c80a01a0400c1d050140e695156800b4a109568591540d040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 684106555 1250 684105305 684105329
    0x1207080f03070c0c08030306060301051302091e03070e0408090d0323190503131205090603150333100302040c09082107020f0f090702070e241306 64
    0x41194014030f58401c2000442e402030b0500300004140d48000156401200300070121469a440c3c0001c000e0310340310208000301d0064007400150a142d85400b030320034560f43c80400d9030000206039402c160400e0425048003d41059076000d01c4081000131050321343d40c0740c0039141d900d8103410a06054613050b1013042d40828034582d4a0160b02d09001d000050030700301c03500c1d044c86102d10440000c1078590340001c54442011b0b110211040380800c80d0300408129090303250034000d02c0c0441900c045459070b882141c401d10842c1d407020800c2c0a5041c1085882880e07001103021030301401c800b401006007225a02e400c00d042258400102c1c2c2c0d08100120300e0001035034000c1c410426090842c00280001d044c510400b182c6008543c01c00824446113032406a030b456800000d04d281082d00e80c20010b030b003e0000c1000d80c2040189100d01c2c19600d424a985001d4103154000f000307002c0c6868070703290500f100105034041c1000013650030400b4048280e50481029012681c10316201101701e94400100540d40c040409420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 684107805 1250 684106555 684106561
    0x20d0503040906270c181d0915150a0e0a1b0f090303030207050703060204121101020c010504030b0640060302060901120216060f0b0307081207080f03 66
    0x2600000400072980344440a02419559245503092241804901e0f2000c40b24000500c0c0319070080e0b031003502000b050341080c4400e010410510600025141c0150142000c12150f1201e030710b10b90054258405601030082c80120400d0840c2c03512184040c0005100707103884007483c1c0a680e1000d0440029010200000c840c51070644170301c00146c00e005040c900009a00b040c2003a480313100d200c0c81c000c010001d84684446500e5035800301c000794803102042e1510b02599501000050300d03800140002d00b0404069000a0028140212002150700c616415507000c14000f8000ea41c000e0241c40489400140742601603503407502040f100d1a848280c00310b02103021900c08006c0c2c14000300141d685004009558900c0c1c403030690841111307100c0c0406075000d03900303002c07992196104611440700101d1100d80541801c0310380c1d000708101d011619017200d445440342ca0b0f41703d420005109600e60000120010403100f45018a002e89a07580d440031010300e10030010f40d90062107191000c40e18024800405036a03246 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 684109055 1250 684107805 684107813
    0x315121e020915011d010504180212040305070c1d0a0203093a080108070b25030806041404020d0308090a0b01080d022406063703050a150e060409020d 66
    0x2003404100c013400b280215611580e080308218000d03480c0c2506071103180c505800e03d070300b180d800d00003106c040ca1059020000c0e400c2c40b218012045014a03c252180b544540751860841e1142c04160409071000c401c6e01d04008500d1583c0003040c0e045681c0d060016501d84130b00744268100b4a54580701c1e0070074107104c020003d2140c000e02c0c61400074112140d5481d03411804c080c04490040e401e104400359580100d9091005054400003010a020b469013941011b01520250003412200b055003503002c5140c0e68100071031410580100300c0c054000c26a1034260780307050360000d06030551201000e01000720210000d240f0620410984000c56000004694250ba462145030b6840000f140600d00501130a07862044004600d880300030009040340918909030381c1c0106000a84c0c004c06514105030b141410300d046c0071030861304505041c2070340d1407984108980385400941540d0019041402091801040591841030b50250070309a900200c5403c0b0280c58450009011701550746010b584602e0328040e4500704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 684110305 1250 684109055 684109081
    0x302011b02041e20030c0c2e11190f090b1b010c050c0723060304060c0e0a120206030a09050f07140f090402060702011101060b07030315121e0209 64
    0x20292002d0510806244d80200c0002900c040104095150140003190000304e640010300707400c01c022403c403a031100520744c4078407284005624980003280c0c40f031000e80b40321082e0700400001c2901c608542d494518001a2070400301004180402002150724451041358030540c0c04000401610190a465410810508400c0010b20400c10000d603c0c0009400300a4001d0040d1849901540080c11410b03207800c050381c841c0c42c12030080400300e01071200040620b07555140918000d5000720000107000b2070804010346148a49408280301d04018141085288001800306040540c15a0010740740e445451122004e421040c4004019000d541ca80799982840001d1480880d00f54203005003000d01c214050120342508440750503001b034500c070000350260030400001c141052061401400b9071011205090843d01540c001d41d090b103d00140300f81c10705916004540300508003542052110785080d08000a910000c0710041400c6d05e03190b1030310088640080c043c0382440d0007400094082ca0100c0c2000c80d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 684111555 1250 684110305 684110351
    0x210601090b010909060501050f0304030c02030a0b04031d0a062312060a090203160305190923010519200f0a1b0f0b09030424080c0c070302011b0204 65
    0x43c2e101c600000715070845018110488206071140d600c1d0008207040c20384260700c000e20a8062100b41d5540c400142c80030003922a00c140214540c00b5181031a260007401d10b4080584000b48049096590500ba5940d4844000310b5080303007000071000a86c4940e14208440543c2e602035900740c0490b4090074000c0841c4c80903c540e0049600c3c12a1545903071381d40d0304030702041c2c88903030542810120707a004d07c0d070190f404250000b26100d14803184800c0d441d4410107860b1116000c891610803101d98031800b240e01c20199400c441e030300000303000c1032800a01c01940340c0e40380ca010001e62500c0da40310013202e0b07590204680a01528000312a0703074004a000009588d8842043c0d24001214159103540030900d142c1040182903020300766564a01c0943c45120b00724001500c100078a000c1003000048211105415102003070222025101998019101070070741c0c00010142841c44e103040010764202d203c04944442034980c2401d146168154802081050394200c85009402ca85800f41e0501121030880256034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 684112805 1250 684111555 684111557
    0x608070b0706051803070f02062b1d151506030718050103020705062e06030501050f030115171237020709020d0e0102040b03181209210601090b01 64
    0x710540324001305100202c0709081c205103d4109100103400510480c2c40c401c4841d000600e50743c00d050041c00d0b040c0d003910002c520002c040700c1d42000f101c01003c0ea03008031042201c440e2405070340200d00c5400151540c04940d10340c4e118154200c0014908084c407a21890072200180401d6185d2812420150040c40f0fa84a24110808501000102d40d0320900803500c03910b6006000c2c0500742c488003255003072569145440b98901412405211001855892400041007103581c003003103e51408085c44071000491280c140280d05281c3c041d11600c201200c80c0044403500412a4000c2208008680c10b10300001040300c1d680c03100146103071a600c001c0520702c002c11040018411070301400e440755802c08040c60b1110700035030400346081050a0282d4043c0407034880180700450400c51103d1460700320b80c0190401c1c1010324003c4280001004035820121402e2a81801001900c0040740300301442d0090101d40e92082c3d40e44032948042d5a1000c1502942e55290422079907196107500b090750180281c520414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 684114055 1250 684112805 684112811
    0x4030f050d020105061c080c010605060c0c150415081305240601030e1e070f0b0406080c0c10110c01050106020303160203130b0c0a080304030305010f0e040209190608070b0706 77
    0x5c40b689031640480d40c086141810040004010f035031284155000071800d10020356070b48800180940710030300186110380c0c42c500540031203480141041200402c120070141c1c0700c0300a0109005840080b0140148218107041c440c2250ba908022101098001c680081060084910100e09110190565404401c120303101180d0759551000460488144008010702c0c0d90164100b05052084141c9000300b080f2030380103581c40b80351240c82442c9050341c10f90011006010004080103115030100b0380c0d940126a10309141d02e8901507003003950b40c80c800400c004150355a9100c1e03580a000d240d00072070f2003040c160b5000380140e40c2d55000280d140e8100700d480004105020390b1126196101104403481c081c514010820428140100084250002c40e03034000319216401c582004284c0b880042d500c114425034000c030b00b641c1814401540d03000307658000704026827054140001079072210302c825071001c1c1d0300304039481342110105641e018108643c0401d1240c0115000070400d421310000800b1914020710040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 684115305 1250 684114055 684114061
    0xb061b06180303070f081902040b030f0117060606090a080d0207030215042123060a0b010f0c2d062c03040306090302031b16090506010c021504030f050d020105 70
    0x15601e83c407003100d244002441c002d220303881050081c400c8079008482d070510703c0d8000b8442c6400b0003c90780981c02079185d9841c0401080300300302000d00300b9030251041440004516685030101c80d07580380003500e603520a810105001d041038441d072181c100140020f400300c0d003444045120180d1030b9410341c08207a008100071500c44114941400854045864042030300c40c58050700407001c80c00c25184402120420407102010100c038005454003034a89010700050001820408160411a44600d0406040c07145c56005000d59540021500c03104a0b004403c01d02d8529001640400089694113080325031309101e0620418081207034800314840704410300c418100511003050385c0394965403030902d503500d40c0304000620000b0940d8111a810328840d0048904180c40c0b07038501122034400c582010045d42c4403100354128070202100440040c415030750208000c0c1031890009140300c00e6400040c1c0503091001c500c0e22410340c0d45040b2002580c0160740340d403651507180f030701780d442c0d900382082040150b00b03003408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 684116555 1250 684115305 684115351
    0x20604330c090905010f05090615071406160504091508070f03021816051c1112150105040b090d0804060e090a0b0102191a1009060b0c030d0b061b06 65
    0x4c3c14141c90348070b6500320610f840c203030030408200b1001701b2003a007101900e11302ca141c480105c0003404045100b03d040c02c10303000c03803046407602e004002030013000c00c09104a2194402e6803c0000c032401d03580d6041d00400c40600c1206c1d080218081e40d40249410300c2007280000c1c0250708201c1c52000c0d40d10841e4110000c400d510804490b514044e01d00203501d081c071081c01000140a00700030b280b8031610b0300109061545480c804002c4804010541801c010001403050001c1c100400282e8801e6240c08083e690720103490000304140102d0240c1da0491600180051540c0e40341c10501c02401c1c1c0c00036800346d030365444100080840b40d0440589018039525400b1400c82c012502501d0078042c01070f07004142130790203c240718400e6140000306840058000351300c13280703003210f20f10740714461700720b21134014500ca240130b02d500d08035010740d800080b600c03c0600c10500020b0002c000c9442c2407a05c00400728060b40070f000041e80703d20500060703444840e603500c0345034906500820034510618102e90000e5603008038002d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 684117805 1250 684116555 684116561
    0x50f0a0c2a260706031503061802010f0201090f02060d060f150908030c100f02040b0c0105070e010311030609071103070f1209120609080d0903120605010f020604330c0909 75
    0x1840700b5641d0001c0c441802072511a40c05980004101c5801c02c0c482692900d0301012220310071b812411030440c95600da029940c2000300c2a8070540548000c00c500145602d50010340c0c0c0594500a00c6050001103030559150f841e0489009008942510b0710401d650b17154001c600c0300d41080c0d10000c1001e4200000c1c0184010003529603c11110014080d20150b1000720402080c101e65000501d50b0709110102e031084514001c1c00c00d4600d400700015040c00c1c1003030701800201c62244030904250030613483e2504544004107a84e0001d905a90741e1825031521241035459400064181206110106501c81031103040c0400c4400380740606040c41c2083c00803601100e01420710700480f5404034140050400244d1103901601800c0d0050101c60b040c0030503465840203880d401c0c0419400118031315008100314400b8410000140b40901300300d40790150030f0318080d44a1400400140280c410300003c0c244940810547d01d4925450801003d580c802c1c00102500810f020032400c40020300ea0003020640d61000c1c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 684119055 1250 684117805 684117869
    0x206190606090605090301060b0c0c090a053112051207092418170c1206180a1703010303020c03010c020c06070f0c0e010e07050f0a0c2a 60
    0x56502c03120282003d0381a01e443c0d0000c50043d4041d07613034040009e2003140b100054440c3d006030201826101000c9410042c181002400c5c1000744c030300e02414441018100d14070440c0c803071100c1d60101c001e4a541000e088141c1c0e215107000d04040d100c003000e544003591003801050f403200d0103e00124551108001121110068001c54041c42821540211112030013145641a40118544041800c0f500b0f03600358406100750703024440c25100c54210b584035101c10302c001c005003070301074032030b0300001c0c13503802d6815540c03078014001030200e0300d0001f60081e1004062000c10307581c98001c0c0100c0e0aa00301c0c52a8610554800d10040d00140240b540540d0146010700cd0590985003550081070400e86032000c000d0740c0c0c1e2210800f107075840d00310302c0701c007000a18400c2202d00400c019210b61180f9803400c907210ba2001d200400200801c40100f03d03c02c0d04071707444016940000c0c0c851a10f255810542e2500c0d000148070b043c1b0348e030340e00700003210703803180d164510701a6905482d1650006d00032250328403030068600f5204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 684120305 1250 684119055 684119057
    0x1b060c020d0513030b04140709020d0605180414120a08041e0302121b16060206100f09050a0f15080d0f05030f0a1d030a020d0903080d0504060f0c0206190606 69
    0xe0b000b0004514070001803904a8080c2d5100c0300e40707c8811101d10301c1c1c80c1482c1d0051150781e4001c950b40302d2419032485440300a18080d0b0310074550300d03c1030010700c1d450a0005c1c0018990008150f42980342031040000c8200451302c95440d5981e00182c20000c1c03e400705c22a8102e54400089440b080b0741c000400c148180c03107502d42c0080201074000010442280c101c0d85201407206044422260300307150410508440300c0005000d6450710341402002410710700c004040c401c507060020340c10040e1aa40d0090541102d420510005503070f00c0c3d00740c0401c0a8801643c095030503d00349071100340c44071000c0d03006c40121078040080b9401c55001300b03800da80c100b84108945010400500000740034000108010398415240c0a001800d644100e8000d6900c42000300f440c0c0701c03a4004104426210b07010014002008154200041081e00d10b5460358118070405440400c0e254449020808000301504459a541d04c0d080e01801601030070b0f0402540c9a000312500079050300d000702c0580f41d200892041c0f0003501c42c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 684121555 1250 684120305 684120337
    0x5060417070807150b040612062313030306050603180c03010e032212030f02010c03061214011d15060609010e190306090803070315050a05101b060c020d05 68
    0x7035201ca00814400385419014507850b845e014215640741d2082c2000340a11243d0800f07801d5940c1410702c02c0303904011134032008a1f032a03508140005c1080741d10320f500c1011800079000c058480d14048000e05425406150851004400d0020000c5070070300030b4a809480d00121104a070b1346d40700701400e0382e52005414003940c008001c090000341650001e1a548048241b020603a1540c4511180801d032000806500107120303c100e00304126428007c00710740e04100d00d82880554144400910b45030700822009082440004480d80e0401080d044100810200f04101013a840d8014074640c680394040c4603c0441a02c0000007003030fa03e003203800e4403c2820b040e507070072403018100300600c04010100b003201c9880d0000e0900c00030000ba001c0c050204c41922900c82241c41e401c3c00c01d40038068690322144251014141901440a0744480000700100d64013214542d218a40b24641a1800101d8100400b00d03074140c4d41240d001d0245582207643d91103101d0342103c2c824030407040100c4450003542035040c05000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 684122805 1250 684121555 684121567
    0x19080f0a0f0e03162001080f07110601090f0c090b0f07020d0501020307020a0c0806040f060506010c17071703041110050d0920030a11060f16050604170708 68
    0x2480d03800455864611040041d8a001034160245180c000c0a034030f0031300f22080d01e640010044013030007607140b0809451407040c140c14110000b0b0840c00d00280762003c000c0780c0c403000030b91051040498250006c0ca900545650f961140b100380080e04490410100c2541400710003015a032203400c5500491b07000314100ca0522045035000011a802218140e92005c240d0840324040392080c8005c501814180e00241f548019600d00f45030000c00560120155400c41c0b0208030114900007140d40340305034000ea0004c0c4a42e02c4030b006a45204d210107000d080141c0462024180040400040440e0342c001c04c80310140c841c8416244845101c110340080030050400021030703c504085864030882c03ca6030400c03a00b445e000903040c9088a400800503034250007034001c144010350801c0d6035800044030a601500300c82960b0f85513200700c03d0390103035640c1c05001d00103000c04008003500281e80c6440b04143d0500c40110035820080d50f140d006a0702039641000d048850702c4e1381043c01c030031965030310b1384520b109042c96 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 684124055 1250 684122805 684122821
    0xc030801171b01030b061309060b03040b0403200a0803040c0b03012102030c060708030a0c03110a0c080c010501170c010c0f110f061b12070c0e09010e06010b19080f 72
    0x42c0c46020414185602c1c0c000091496032070f04094500c0750500c01d000e070303007643c41d06440c941501d6982e03002d89201102002448080707600314460700c4d803082d01820421081043c40e034000780e10181d201c01d140c0301401401400c10801c030a400045014a0040443c0c0f4616522604d9810030752100307100d110900d200c0701587c640050440820000f11038001401d80e04040385900125a003544042011500140d00208202d4a401c1d1031260884e89407041c0707020000001c0941111800d440b41441c2081407142d120614010464444110740002e861400240b0083d40c2d6120f401e80b800c8034121075000180103071401a80c0300d500c203200494a658129025501e40a02a241c2042c4010300300800d9402245200a200030b079228840140445105010700200403556500d41d6030803c1416003000403440420084880800c2008d08540180d40000040d0030786034030781030704c0640108466004210300c0e024141c00002c04102c280050007a1069920040c980520480ca08031440300080b10796548050200003c10014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 684125305 1250 684124055 684124093
    0x10506071202030c010f0b10022d0c1504031208161b050d09090b040207080d05220501061419091d03070c050a0b03070206010b071e030c03080117 64
    0x20740d805005aa291403130042819007510000142c0002854403041c0000090400200661001c001c0b0720107070083e0315811344d08a00c0c00d20404066520321a40c032400c104900c4040c04919080d905c01413840d10020303412000c401aa4000344804e0364105004001a000c0768007070b81d1014441e251100b54004034807001941640c40d90b0303603403c0040b079122078421a000003a20400880c0013051301611401d03215440c05203c081924206c00c00c083c001c0c0e0052040c540010604c4081d2510155501c038085559616004240d0008020203400b1207008038060807201400419440401030750b03a0700d44009508811b100600c006146143c60408440c10007110420049140d544004130f001345500503140800c0301700c1070b00d502d1074100c03c40943e85e41820303070801c02c403504e4145007100c02400303042062800c5150056010b134948505119007141d03000005018000c04c41c1c0214480c41500900d0043c0c20041100d00f00240205a0f13500700318041b4560078004101115403407030451041e41005e0080c554084810141541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 684126555 1250 684125305 684125333
    0xc030306102007080c01111f090821180d0806060d020d0b190e040308060a030c180b0f0d111306080a030e090f06041a0907020d031401050607 62
    0x8008980c00030302c51481010003003528400000000308009402c1c281c805081c46240d90a40d070522802078440311440f40003240044071a000e03080d09a8400c2ea422540b00302414000030300804070381e8002040d6440c0d20494031030855501910084488903564800b00c0342000041851a1810350300c00408071800ba4440c03120b10354800e13005091a410414a84d80785820b90b0054603402440070707100d0b050762480e820004078207503094a80c820790034996441c0002500114101a2002c1d0030051511b0010301591a2070210030011035200485a400c2547e41c01c0050800354a0744150031201d040c82c0c00480c0500d03080700c41c0c1280c40c03002000c580703d07400781c2e40d030f00e04034104101d64082d0401040e50a140298125200301030052030300340007400c80b040d0b2500e0000d1030308510015080c4603030355880601c00342c050030304844e076030000040d1400502411090091620041e4841c1c000da8440404020091041d9020a03034800c000b401c5c0d03c007401044000d811400c1c1d8204240607041c1c01900900101010465540c03075115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 684127805 1250 684126555 684126557
    0x1021809040c0e07200d091503060b120402030c2b1a0703050601022401060302030408071b05121b04020304020a170d080a0b01020a02011d0a0e06090108030c03030610 73
    0x4076944401c140010b100458542000c40d15002170b0310062242d0500426040b03151a014101003031040d8806403010419015011100c4182c214101c0034900a40c0548041c09180140359124881c0c0594000d440004550480c024015005280b156080c8609101c2e40046500300d180001040042c4d00c51948401e43c0713007600e140345079695212200c981e251265005002d0799a002c80d240c03509900180c0b6280d040004035100c80c40100100b1155aa0060903a05640030f41c03801582d607071114140341205020f8400081c02000010054150120a100321041200c1c000e84401c18900180320003a27840d045044030203084141403452111092038542c0c0103550003440181903108481d01d82c1c0d0b000440404176610710210740d1060800140c91a005412a68070901c9002c007849a540230100003034a49849107002418001400c030b2580c104160740460200007a8054000c000745580d071220b10001c40016240d080c0200003c3c000480c10359404070403180070502e4600110701c0c44d2185000d0100904100300880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 684129055 1250 684127805 684127823
    0xe1210021c05060603040f030c030c05010e1506030a02091f0305030a1d060301061b0302120f0d06120b0408030c07060507050d060e190905031b070303080105030102180904 75
    0x410240003480980040c0030300c40084030751400103041e820115100544202d01c40c44040c410840021565902809040e2385840c05600c018228071302607880e15a2194020f03c55420250b01c0c142c1b2070000140042b911048606002c0c0030780b54101455140c48101d100a5040b441a10001b10100e140020881200d0340c0701125045041c1d580c8c581c241103400070500171001800c05901c0d42c0c88280d074142031800c502d200300c504e00c4c82d5501d4210045d0207013000380c0700501c00a1317106110006040c000d10020380c880c4a2104040d9440e4501841c0301065400243ca40d45617610313201010a01d001d0a000880607241e00c044241e0142e05e40313490380c001ea504000d00b0f00301000020042c1c83e000410a005c0c9034007440e1945c80c1c0d070361188040d5101c0c0d070683e10030350400c0c02050048801c11000c00450a500c40c854192998002080c0d121810500e0962040c00c4a4075025903610002c0d1460000002c2c0c6030040780d0282d0344403403160341c0b90000c02d03081c0c1c81510308a0560002c0c3c2d141c180d105181180ca40341d0020700c0b8941d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 684130305 1250 684129055 684129073
    0x203160503071e212607060e3408010504050c0105031b040e0a1406012019050c130507050702130f05042f090a0b0111100c030c0f0e12 59
    0x30800c02c000b103040130780420344c4480b104001c004d20303503104188100e102414022104210981100107020700c0c031025091540342d00084034144030a01c1000c4480d0b003454400c007810303851008040c0b4180e620b6400c1c4580c0d400800000260703042d040c0714050185a1000181403901e000000458041e04040d1825401500005a03200741042c0c40c0000d000a0170b141411104038581115078100b100c0340700440780441000d500c00c20800740e0b48142416034601d1b280c003681c0d041401c00c181051500407078030040030428000d507034000e003400000120402d081004448070860040b0032854041590001d980c11804181d05000c84801840d000709040818010f14100143d0308083d03041039010b0b645c082d01e0583d00d641e0045040049032a4a01c5003424000013411025a02007034840881c40c15000100b210003401d43e0740c044485160300c00e941d841d409a140d40d0450b000010044101c00081c08007a000340c01080c5481c140381c04450003840501c03007225042d21032100c002191410b110f012003030200c0c500054000c002c81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 684131555 1250 684130305 684130319
    0xa11161406120f24010906050d0b03460b06010521070e01110a080903031e0a180e0609190e0114010909080f250b040203160503071e 58
    0x40e8030310443e1080008040d0b4140654040008000c1241a50201d90381200d40074030b60740c01000203001c403601071900f6036a51081c86105c00007400c03900141503050082c1440016500c40401c83d4003410700240c494846000f00b20101994000c08560440c10a11044c1c542c110200c0c0803407003100d9111006042643c9050600c130000403040082c180c4140d0554200c00a110003982e0022007050520020300300668020051003040d03903030b00991000105812000110b4082c0c50324180162031a844c9071842040c62030140c003028007450f40289046c07800103031001d0b03071041480c1320950303030041201c3d804a220034403925030105010f007098005114030f051051202d844140c8120074803448019010140001401d981c079100031402590040e80480d0020f4245a08d907000304054008a43c038040d81c081860b82e40f848810306940c1601c9040466030022492240711400b404940501244610720840580315102454590000e070500140191601903000040074007502c030840c4c003421442c42e511003840751200d590720381c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 684132805 1250 684131555 684131587
    0x3061c15020a0206040309050102010203091e0f12040e090d0e01030e072411030906032208030a09140105150d2a030c0e0c0708030c13030501020a11161406 68
    0xb00810059101070108414182d1001d01100601001d20080d0f1440c1041c0c11800c1d0780346800c0742030400107010000c0c184038a85081000300b114011480c00d49540400042201c49580c02a1090402c00703a035803000207140e40c1001c0741d161541c2540d5150302102600d03004c0114001d100a022201e8944146540400c0c92640740341c0400c4a4002d91010865803030040c00014034003455211451040c3c1e1040c04864110b0792038406072688055543c40c0410b14000a074440030b95001e4030000a0f200310000010f001c40800d00b60001001680580f404003403881107000e81c1801ca403011500201c84881403010f61f035613464441c0c58181c185000701c1410004040c407a0b103100392980d09104018401501c01e50130030800c041080240001c00d00b21801d40722900d0450b060b560b0b0340c030803003100400500380040002c5c4007640c00d4055810410580000c000b0701500da00c0c00070b000350b002d1010780000c58100b4005403a40c40300014480d01d01d5615800141c1020300c3c040b0351003120f80c1e01c1c0d0041c987c03101d024032084103c000700c14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 684134055 1250 684132805 684132817
    0x4030f0e040603050319031a090c040f0b040f060c11040f020409050f0612060c0d02032203091a040f0e09070506030a06052b20030102070b04020405070503061c1502 72
    0x10b13000c0c543d9041411003000051201c07910400506042c0b003400030044102c480300038800d1006840180c5180c0c1c1302007450301681b0680d00000440c0d481d0074008105602d012001e84156007020200320329068a81005807003882c0349960003004007000b0849000781307052540061440c08021100503003007645901c6d0480a42c1c0c400c403490034246500c0b03020004e503071030804460b012440c1030001030282810311100b048920b10485e21704d01d141c281c00002050814100184d0000080e401e0300311000c110705076142c0145440d4892003080036600c0304880301450720100404880495103589541e0342c0b0b0700e01e841e007110148880140003041c58040c4490028054036110010b40c40340f000e80400043d03040c21f06041000036004220100100104a0040395070720f1500c90f0302640c03076504001d07040d00c00382c00b52a0140303c00c1c07507000c0c0b5180c041d40082982c408112001c82001c3c0203510071a4244055950b00408842601003112100c3c0c0c00a4824030b614180c00c000b0409030101805201002c6d0001540e85c40e1005071303400070f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 684135305 1250 684134055 684134063
    0x30b01030204270f0b01081305191b06020c060a110109021c06050106030506010e010e03012403140d0c120219110f1504150509030708010b011b080304030f0e040603 72
    0x1540f08480f01d0740da039116001d030002c00080c0030000204220700007820749a008100304911000341c500c0303400b8400c00b0030259903074404600c0313103400f0903a04d07144c8400c541450700d40140d8466a41070011944600200c3c11295080f40600210b05148581c0c3e4110307408900d6100021141d580d0b15844c801584407482848021801841040810043c2d464070104507101680504101440e01c03050221503031f40b11500c40d140b4002403824106030360b20000000d005003650803039140380c4d10003140034040480103442c0400840340562001071305001455055900c4082034040c2e28005208204110f0004900c056460764140e6944100c0300755603c044051650804480401d4452750a83e8014101c1031800750240400c000342500c0d07100c008000081e81a5890040c1d000d50320b542042c00800c0420710307105c2e4007614861300005080384e2120303588006041c003e0807054a49400a044022250b403d42e0007030040441080c0c0c80740003e469603484d0f88003110401c10742004481041160030009510b9516809558091401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 684136555 1250 684135305 684135359
    0x1410050402150901122a03050f040f06020918060a1a03130c121b09090308061003021204260331050d020f0105010603060302130506030102071506050a1d07030b01030204 74
    0x403158010000c1c00342003a0405088c44100000c04800c000c1c0540c00a40c032945011100c90315140000103802030328800c3da0400b0b1603410000c0307101160b0414a0150b441690215100c940342d40700b145034012014050f010a000410200300ea044501905445441c0100c141d40b1001d0f4549400d85543d40000344d065400c3c1c2c1c3c01d801c0c0c01c0000034444038060010800c0a10030000b0b169240c0d8047d11143d0000c210500c1f80002c2d03c40c16400e103020703030100c2d10f41003010030b02124185058038100c01403076031030800c0b11440301e414070000707285d0301034101101c1c01000551003400d451005202da0343c8030801c103030a180e03244180b2410150001041004a2011540a80c020340180303070741c40d003a45003103d40590047c03041604203203041001da256008528901003e6504c08109655910007103030181c80b440e00d00030b055009a0007040c60307090084d40428182c900403580c624203296680d4141c001003d001070a804802c0b50200440e9185009a0102c449500181000f5013001e039910310420303441d52503450313003000240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684137805 1250 684136555 684136601
    0x20109120908070905011211120a2604080a1b03020d0b0a0b0a0f0902090612090607090509060105040501030e07031203020c0c1005191b141005040215090112 69
    0x1d003440080007400100713104003c250f00d0109104141003101c6d00140080031520150101d580381e907210190310000b680103c0b01885e20601c1d10114070103602c40419401d213880c05d0705078900011031045504441100c002041d405402c0c4c6c541907400243c52241c440e551200c1680000162500a80c09107824082e007516201c42c640b024218082d41c01280d545441b0701102c8205000c0f43e00d00550000903031740b580200584542e10b000104035039103d042d400701d2207810500c041049040002918500c01c290030b68a40720038035510814030441440948081d408102c080c00144410f512135484201441e405008589015980752105036050502d1540040000d4001810034501501080110300040c01541d000f00184030014000707055001300d5140a4102d9005000c11048910605103500070b4404c500d1718400255141c60281c0544044108a0b5102e015103441000100103034451288204d4018201c1602c016040385811034a41c0000700342410310116412414000c0010721403020051044040c4221b524 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 684139055 1250 684137805 684137819
    0x102070203012c070524040f09020403020307091401150302091002060a0605120307120c05190b130c030b0a020d0501080a020102070806240d0204050f0a051608040f030201091209 78
    0x200020203e801d40c4000d004001d03e85030b08019490b04521a580b10740b0b00c20030700da4107065034480e40e032142d000380c500d07000702080e0107041d81d00400c122403084003292003281e1344241540070748626035910607944282c10010072054a651044900c40c0a251a006242000200000b400b201da503c5403a80141d0140040004c6141d5501c51400544821940084004524201e4590300e200d06940104001d007030761a12900c0c2d6000385503400c0040d90150684440720303400500f03950710040304803042c0d91080407070f03002c10b00c2d036442030941600c42c45d0040000c0d10740c503045807103c001048000c6c00c07401545134200084034094406114450291807503001401042c6041d0000900d0181503411051007a0869000e09c01c01c48180411200d9005070140101004142c0c0b4000412100c83c42c40042c1d000b42c1001c081091300c05d402e224072485840501c00800c0261220041620406140c2c40308102141030316010070003103854030a081400504c41d100200c3c0650b0355136182c1840162141962011802d0042c042c4010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 684140305 1250 684139055 684139121
    0x6050907090302061b0f060a020c07170c040c21060302040609050906131e03050d052d06120a0b01060e0414010b0a020726100203040206070311010207020301 69
    0xc2191403800c09815419038000801c540308240090b20017520b03504035119254818028010494541001e854151400c066628007030b5120b00e1411406004e00b14011034540400c1c051455154503100003007040b42829010710004024104c00c43d024880408401d1751001024000f01c24502911300000c20003078030714418030080c1c541035086004c40500302010807112090021b012035000c240b13219107268100a90604418890840c1e80c2043d2014440c103240090640020007040d41200901d000c0003142d460300025100d140100600002074540000700004003d150800d013500700200400090106445040003460803901420841389240d0150040005c590003810401c1007117416101808151064000c00c1e1040405000e951000c80c804141003a15070b10820050000d40440000c045a400510a018425029144d920000d038803840d42c80c002814418001c0d64060b13503028101a0800a07280d8090f203941c0b0050440740c4082d9420302c031841c0035940034003840302140d10304e40c203140c0044d000100312081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 684141555 1250 684140305 684140311
    0x30f050a060e13210e1801081e1011040f030507031a0609010b030406090609050c2e0f0212031e09060709050f010c0606030507054006030213060509 65
    0x640701c4003280c550100304503c013504611075044841c0b07010480e11040a40c3c55544001002d03812940b4604040240d030180d00c0c20038140e5250400301c0f6480540404513408000150013451143d8000c541600744400b01d03504030000941880c2c5c00241000d49841e030070030f0f08121a51090b0303041d51001c0c400b0800d0144461a164031a0071071450001e4524060020420042040c85071003d0303080000005030030320215078000e61042c0d5102e1028020741d4403a003005030f69031400ca101d00e0310800301c8968080121b00e18070545601c2201c81d4107141c1e5902c0d140b980030750740b07003900c942c80d0340039030155152020036101041d0045115542141c4001000c0c001ca5200c0201a20010003a1816903c000148103109400045440440f10120303044c603041c24030900100c4042c1d140a01c01044181046004030400c040801d411040c1c0350b0503181c03581b4001150070307403d69503e000303440104016541c0f84041c49050412003038010240035130318041380c507903030b44c0d801f06074140a000e0515482c0340e0350310f8003884217140c44070076035070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 684142805 1250 684141555 684141571
    0x10f050c03090c010f05070f050105040201030b040209030c1c020607080c062212030e0709050a050717191506110d0f0e0d1403030f161b12030f050a060e 67
    0x1095142c03407100c02c0d0b9546044281c0506020034a0900c0f445584584219600e80d0341c005d4603507032468603914000b4042d0000f030714200c0c08603051030f03d45042414103109562038810000c00400907825000280a40414440511081c80f0403000d286800750b21450020303d22644615000c55417109000409420440003030002440035202c014584a0118401034868205420040560900e2140541170b0000e1400806041990081240006400c1081d512240c425007034040c080c0060365a01d082244c503007200d10420260000e020020509280d0305042c9940c0e0964614030000d80480ca034200031210000c04da001e180047c40541d0b42700440c0c1000d00c01c1c4403120f4a103080141c01c00404000203004482c003a10002e02440300a8510801d0080c880000044401c81030b050f02d07680e08200070b078000865012a2010f5070f08420540b9424414803a46603101132541c41d12510130752a100e40d0380d520112032616803032010036482e02d1800020b980305100b900d00405040a0004030f6034a4600c400c2c08030701009148031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 684144055 1250 684142805 684142807
    0xd0f14280503010824280606090503100b100c0303110d09150606050d021606140601110a02030d03110705062a04121403040b03040809090124030b040b03030c010f050c 73
    0xc01e914403c0c1641c144c0100409800303c6e48248a6451188148003611040f141c90703090000010348e50307801400d40000d50b01c083c0c040d1a4007405294820b02612805818140c001507101040c107040340c482c0907603045a07071003482d0115a240c035415800c40306410043e1900e13010369031480b48030b08210104212452030614107a087c003070303245041400b500074014a101500c1454000510f000303003006100c0400c840503404a010000940a1800b00041c9041150924080f40c04c1811103555401c0000701c0c4154954018010f00e41c10f030f00c3ca4402c030b001d40700c3e10102d0f084d0074a05000400c0020010301c10240328031103a03007043c12802d0100130f0000702d010419014180c1c0c0c000c100018000f20341802c0c0e503281c4ca143c0001002200b07450300342c845407551040da0b1041c9402c110101c240010400c80d000141a500350460300c01c4016605e030700000721803800800c51600021015000c1070041806038111161103500108006810010507011a0440d442090148000d07503541c420003045c03c00500c01c081c4c102c000c0440031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 684145305 1250 684144055 684144103
    0x50a2601150c0209010312021006090c03060b0f0301180b060d1a061204141c0804061109060d110d0c020c030106080a0c17010609110703020d0f142805030108 69
    0x4249003c130117000c05080c00c0c09050807880d80300c1c001c00c848401e000c40907404005090fa1402c00000030300c078140c0702000080c28500d0024035800188240c40d145103050741c5032440d40c1d180030500170310308503e14081d0003c143c03038560610036661403401030700000600c201c010404549050300c5c0e40c041c0141c2c0b0389051140f01c09000214000700510003003a449540104280b942216040885240002da40c501c554052104a0851849e5901000e0340f070013144101014001d840120410040b0348c000c0080082d00010b090100c003100d8840c0303400c00c400b8120782900491518841c81145400d41d48503480e44c078050f0b032140e507040380c4605091203480b006084040241203d58910303610104101c88501c01d010071210200c0707141449407000e510400081201520800c0303c40e024460b0b1241e00e81250758198058007030b004601c44443d0094610096504150340c2d01c014800e41694000190740100c0c03e8a41c2c10301400d400d400b240200c5c0f1008042010f50f607296541c4941c07403d0a500d10f42811040500354041846948e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 684146555 1250 684145305 684145309
    0x1b06060306020d270f110319120914010e121014090c0619050d0504030c0311060108061603140103062f0d050901140403110c06040f0303050a2601150c02 67
    0xc0c44040d50b00821500c0c128546090581e86c11020b0300095505029058491407800e80d24491912200d200b08070075048542903000a648000103886001904801e504400307a00f98030882480c03806800013002e2580c4402000140f9261602140319080a55998900da1460114214206502052801c0144812881400804c03568003405402d40241001d400740b01d103210f4050020745802501400c010012803402e410000c060020980c400d40204250b1102a05410800704489050b100e6040003004c054403820408808201c0f4507541004060340c0e410306036200c81c9841a1907000718020300c008564442001c1880311134107940b040130011128545070240480c800380090f40e100102880e8006525a260b0b488180544201c500b080c1c0c0300322082e0200010140c003d083ca44028611b50116a00c2d1040502403054920880c01110804034000c501040040c2c86030000707010303c0009140061000303c000034008907480080010541424102005210000c8000300c401c070b906019141203000c032415500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 684147805 1250 684146555 684146621
    0x40f1202030a020405070c150b090a02070f0b130501140601030e0a05070b1c0f05040b07020c061e090d050c0312030721110a110d020a05030a1b06060306020d 69
    0x40000c4c000c4d516480090b050a02844d16110040d4218250300412174160492070000d0207002ca03003c2c891520880800c4400c20280300351107689a001c40e10030011400798581e2914404002c000302d070700004204812000030f0080c02100041941c40091803510704200e00050f0544050030515122030f84080740c62804038030000341c40d80072507000c0c5880360b507108001900c0c01e0b03c0136203100e18410f165040403030320712030783e00039900c0301e8480c0c1d004080d0315240340c4802000704d031600c840808040d80008113009074006d140e40c81c0e04a41c2208107211000346805a40c401144442ca880c0d50b0a0304c06401c60703040c014040c00c0900068442015003801540f031807500b14005030070040b84c55070006130660040001c025040c8642d0103c0400c4a8860360706460f17060b003400007480c408407900340c454140070301c1070400c000c103000041a4550ba40d0003130286040035651a404c4a10f98000103002c1400c05070440da07000440c80606c42e040c061801044050b944034091300291083c0c480500c1e40c0c683c5146034200e10580c460000c1c0e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 684149055 1250 684147805 684147823
    0x215030c1902010b060f0a03050f060f1507050607050c062211030f07140301141e130f0b0405010c0c0804090e0304030b100f140d03270605040f120203 66
    0x1003200d00e86110381c12022401460500b011540002000941c0b403100b601700405040004019071302446140d551a03261545a40152106504203031400361075015450b090b07007841034007100c080d40181172040d152500c40c6803002c1a034900000c01c10008000c00300000600c081c0d54884441182651102e8800d4000b00400d82200400b4213000b1420000d1000303a0b900f03000e08618041c03000d04a811054890251848201503681500c0c4030f5842d01030280007014804034204e20402c107030281c48c0e83c000160a4415031006000b04000f800070442d041e0742d4005521040000d641c14001e9010044030b2410b460560700b1111303059100c41c180071510484d100007860403001c032001d882c40e9101c0800d000c030114844620750f02868100a00390100c003410084640c04964a801c01c96244c140c001084903601c1030100c006000c1c501e41241c010100c586034201080c029001c8500300ea802c030718104002800681c881818110b660407440c00100002010440507a4280c0c000015012540481c403600040b0741c00255201228 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 684150305 1250 684149055 684149077
    0x7031403090d0f21021305040e10020705100204090f05011725170109060b010801030c030b150301050403020708160e040b1506040e040c06050306030a0201080603190b040215030c 78
    0x2030588002c0d11485a8404010141c0d2404d03603100074200002104042c1d00410000f4012103181c600010780c6280034040d01d04c5400f0054007802c240c4a06a010300043c3d40280301c01d03a4a8401d0055840350101213100070001407413260300016080c04505207040550388180d100b080c00d0749004036010030205c40800d1024564615140741c00c40301d187c074455603055079007503841100c2001c40b50850a100b094103411000c61144a40c404000c41c80090f80152003c040a000c044e000041a43c428000a01d142c244580c006820074487c01c0784291240000f0300355070044400b1401a00644010410720204021552100c00341c1c0100d0790070b00e42040303000c203880b110080018029400d80c00104445551420b020017194070050301c1c5a80d90b507101c0e00540c5580d2002d840443d42034804a00014007148200d042d00c0c0500d0005003e0f108000c120f8004443c0d9010241c03e52f6458043c507104c01808040d2003207248016482180c02d00401e141c640104110b900841e6007903081003504008004112149804698010000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 684151555 1250 684150305 684150317
    0x6120106320a0e040f2406030c0f03090201020c220606140f16080309150109090f0209100506180a050907022d03030c090f0301060605030109090812040807031403090d 73
    0xa601c0001d0103001d448402c0e4280034a000c0460155461070283c001303011482880c0036951a945110840445504101000018911200312b041d4140301e41c01410034180141304031740c0780d04c00f003100154000711140c5951048a02103d14000589628040c00004046604140415031460a0780003907911420350440888000025941c080c01b1281da0b003225501d80200402c0d860f4070305810242d0760707401303070510622500c0d900d6400083c880c070b06402a60b0000f42d00159000c000030f0300354248148207070060304011026180000101c1e158540c0e00142c01c40030059040801c1d151442c006106802e1000c0e041503009003180e204000e440d5070001401000442100c06c40c0c2c000024841810b15400c8100024500a001c0001409042c0000c1005000ca1000072250742c840c00010b4410142224464899800855000d00041101e40b440c0c2e4031120045000d94809840c00440d000d581a2520b41207030119105600410800141075011500448200101d00180d00d1420103041081d542c2e4600d581c10020854 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 684152805 1250 684151555 684151577
    0xc0e030606060f04090240051011100b01030e03180922060903090509130305090102160306140c04030804090209010e18010e0a020a0909090206120106320a 68
    0x2005003241c00900c80d1700b41c11919851412181c6052001380d400c0000b56845900c41c0c01c050401468014a01c140b4440c002c40c0160300d0002030010790040362560704103000c1f800d02040c0c0300080521410030f0b0210260400502c81d0314220016085079442c2c01c1c017000030303441072207544400c280d0304010203400700e0201c4480b0303502d82d81c0020401031031243d034104500700c594031000b150030443e16400080c2030354420380300c0085054440781848000f0304100c0b031150b082c20b40e80c4d840038046802000149080302062040c0c1d8814030000070902c102e40f10650044844941d039000d401e103c3c601920304d030f541005808039240c2ca000d14584807403085010300c5c00707445040b80c0c1c0000e02d809240c2c0100801c8141000251100020b8280c024540e2480442403080e8001e140340000001c4039408503100302d60b0b01c05140d44030001c3e1039040c000a480141064482240c00c030a00300000e5030000214900b05000301001d80d10701c159800705c010316a404941d5400b0032810891051310464600340c004d4107690a2120f0b500c3e1002d1084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 684154055 1250 684152805 684152827
    0x3021c080a0f1506180b0a20010e070e10050906100e010c060f09060c11031e0408010203040c0801060b0f0301053106032001080103080d06031203090302010c0e03060606 74
    0x21070f00e6144026a82e070090001021500800b00c501e01041a00c40c210185544036881d40300c5210b4043e68100040740501c082d844100340459000040304602d000080c1880743d00503103840c09200b60409068841c2600421143c2105095100c1c0503001c00d0714200160305204010865a80e01c400e1501c1c180014580020b115910401c030240d200b0781c000b6403c0c420451024070500041003001401da41550400d90b00690030b502400308200d98142c403200841c940200c02e601010052001d4450800c4034100704000142084240041c5018601400b6403400e036038a0003421900b110f00590240e0300c80f410500c00c4501c03950406054a046540a6900c1070001c0c0004000c0e0001e0300c0052420b0741042d1b140b04025592801c581d00450940e4412039400002406404e503a843d106040142203001407401801400011030080c0031b0102d1184819020850035285e564108951592584002c006030703880c030300041031580c2402800059030583c140903d03485403290119803101401042a4098200003505400103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 684155305 1250 684154055 684154061
    0x3040e1509010303050702010f090b18060705060906060a241b020307080c03161202010c03020a050307111f090501200604050a0c0f081005060409050f06010303021c080a0f 75
    0xa00c500800055440d038580c80e001d041c0340c100d848141c0c000340a9150f11042e0f640a28014000d40700d0340c0d00602d0914030307800d04100c2c014401034441a000f6905100410001e4000c000b128050403050000d80000e1401e0002d01030018504c0e84111070410141c1d101440081900d0300600030000c840c070b85000c1000b0200344c10401c0c0e115100d0029003600c02c0440001e0800380204941ca00c62200b1000e80e409103101c1c94600c0d61255241c000c20301e14242a002e10f400645c0640c146034091803003030041c0c810286442d1100c1d4195000010182d40c1840f829200d1000c0340f901f190203120082c0c00303d4810308504000c1c80008c0c4015034502440741441059561200c3c8444540b518401c00c0c1c1104003180c19914151070010b40b0340c001100100ca400071559408540c11038001c0c022002c0e140da80c40100a5850551450301c041c04000c1d2503144c00c143e569400d140030480c203101f69451001c0c1000208403551640c94021302d401c8010b19540c451008101928482542c012800c1d0303080b1507641404508035081000142c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 684156555 1250 684155305 684155341
    0x6020f1806040605070615120c1a2a0c09040f030e01030513060c18030302070e010807081f150801020702011716080a020d0e0d020f0601061b050a02220513020303040e 73
    0x21000200c400d80411a5071035509c03080d118001c090404041c10900100c5841c0034007000034041c5244101d40303199a0050f00c5401000e110524101c2c0c0311000f070f00c1d01080d14020243c5d410b6448000c02103400b03042c940c106001c828030800a180800c82881c1070401c8038a8544070010080000d5155042c103404030303104090009540c4410030210948603603920340a50717500140c0c0b090a2032020348000020300050701003a07c01c00c88800d1005018401004e050441808205100d051441c5540d40040c81d8444803003151440503100f40800183d40e288980005072200401c0d0004140d244103003420020400c4000c41045081881030900f455262182945031000e4014001c0440781c0a19001d07040100020001c6d1040700d010494080d03a0400d2861908039468900901802d0085190402e180184203401984541d0b40390040059a00b141c06d6640050190500d11622820344074028800b410b60161901c134442d00300300c0c0b001d01d24110003002e50100307440e03000300d104140c4174801000006045c1300d00c68a055403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 684157805 1250 684156555 684156569
    0x2d03020301020c030915030717190c080103050c09041e1e3e060d09060501060f1107050a0e220302070914090a0204020f0706020f1806040605070615 65
    0x246801d200f402807662900a070b80c44c28400c064214000b0f20710b501442c1220b001304842d54807940d0101c2c01c5007440740b1000d806080c14907135600c901c0a4600c07042c900c0c4180c0d013a4003150381d121400e551550408034030f85010440c103240f0417030603e001c0c440040d100c91140081c820741c9010900329560203050200d20f45680d446400008480c10700d090080214218421b40c00c5d000100409031a0b00310030448109610701d490503040c801e070844030b90071610311b8400050a0b00d9200b0700000302c3e046c2d0b020364484065440a9000f80c2c0481d800c041a1090640c1010300d0900d41001000103041d05850701e07000900309034081c030913040c52400050118038011105042400030350305120441903003450724070b0002e5451030248254086145010b0984410030700c00e104440c09541900004c1403080788540070400294070201000c000118100511400280c0302e00203000203099a08600d41c43d6810341d84203502d548509840141b18120411007400915000400d4510482c0c000000007a0102000c290045c2c6148a0304622 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 684159055 1250 684157805 684157807
    0x1806180213020304021011030313020d02040e07090c170a0b01110316030e0901030203063715050103020304020307030312020721170105152811162d0302030102 70
    0x201c0d4000568000b10b000b18030a845400c0880304941c0106d0314400004000c030031942042012514807500c00e4036107134201c1c0c002030880d2000380003640001c0450311801800c040b1500005410004101c29221b0f038400198542805044013081c0c107131740301103040000d25030321079a552581100c0d4664440d8003011507035a18481145d82d981b0481d03043d6090f4000b80c441c01c030b000408111221944d818555041030489901800810b4943c894410740c40c0250300504a10001200c0f00c10f40781222004031603e0f008140700c0120008012046102000700f0180c1508010706050040045c400140c030300041d400c1c201c03505850f2110f0134090b2009038402034807404001800041034100d101c40300717148441441d5041d800c1520b40708680101c05202d1003420100340301d8568061609203006040042c040010041e81e400c9003038a0254001d03103000d1480d0359241440660000704001c030001d81902c0100410b104810b2070200040d615458002aa820340103400b100d4120091240944001ca055048510001c2c550050080d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 684160305 1250 684159055 684159079
    0x1203081503070f1a1c0c1110090b0a0203091c030b032d0d0f0302130905010b131d0a09050f060f090c0604050f120703120804110418061802 61
    0x10f090742905030060304000c00100001d0300304811898220390105016644031150a002e520742003009140200901050056000000c81d440c102030100c2d14181c0c01c075400000c1c1c07480c25418100e55890b40104030709501481041071000c10321001481d603400b1520513001841840c01442c040b000b4004030038101360580700303000b8048c20001c072640040c1000b1484101c0403104c0c2c8048031031b1943d40d608070b007003600100c4e01d02e03083c01106600c65002445d51a203220190002c05a481070050100c03102640a015194408584903800100d11484000108002c2100e4900004400401001c481e4003900d40306909560b0b50383c5d2400c0120a000d0110803042070010303a14180380c81d02d20f1010210049a007401c1034000c43e24000000c0c4ec043d0281d9003034900141507916100103030070601c5402d000e02c4440541500ca01c03100040082c2d0380704690040c00c88280e992000f241800e203050f0b940240c54140d0107100f5400c2c00201561035840004d60300f0b10075000030010507040400c14150060512405000c2d400c10b140a000f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 684161555 1250 684160305 684160319
    0x12090f030414100c0b010e0a02040b030112031e02070e19020c060a0e030a12200d020a0e0103050402030d20011d100204050d0b040204060504090501051e01120308150307 74
    0x401070300b41d02580d040041c101811402c50380e0b0958400c008121554131303401405102ca86e800299400282400010b00c2c00351a007a04d103869030000d84c40340400e50f907940f035140d00309541b00151100b20f140d9100e02c40701d00701c0602c00182d2113900c0c03802118840c000c54000540d9a0502c807141c03204e80410307544d00310350b030300c940750015a00d50310210b80780400c02e1f0800303082c007072031000c000211681c2c5841540c3c0c0100c4000902040d0340503002124102e0380081401917100d074411001001411002e401460040e44c0d19100300707001d490705011442c480c0c1403524140402c000768401040300d0505c1072507841c02545000c0000c5045c40d03235a00400d1006140d43c40c0c860808000c41d0710030b03c0041440c1c0b200702103400c550f00700104072050384160700500d6080f08c001c400110010b01c840e90310303980062004001044485d1030b030300440c0441d500b441007070724160b4443d0140484011842e900d04201034031034505802560610310a07030b070929209403000f010000d1800010300e511030072040b01c0c0c0c01c6003001000e50b55141e5840203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 684162805 1250 684161555 684161579
    0x61b01090201080105060a020304050d1b061709070b040b0c2503030210060f1703071a060f03010605060a050a02070f0605040806160e01080703140906090f060c12090f0304 75
    0x30201d010400c00d01c0081001d18060003524510541036006619003030904052065480100310201c0e840c036a81290320380c10304c0140d01150050b00c00e5940705442c0c58150131400311003900280c959140707500040d5003031081c1d032100c600712010340e500302c00781950b1081c61000c001d1411070f00c050000890007070b01d00b086115940110303041d42168003075401c440c07040901c00002c200b1921148034201104c404800c2c00c020030200e05c5001c00c000c10010007a6418162261034801c2c802070401f048100303c9042c8010080c07945021500625003081c04e4001b08005030a00000c13030b215101e086060014800003081e2001c005e44200050f00161806c1b403c01c15041c1c0da941c00150440d0010b00403540d440c0280c2c400035000c10b114801101c40d0a100390b0f100684c981c03000300199038003034014012008043d1140358001400200c0c29a07a402543c1580050503686854035a15043c040803050b900c942d40c108006000c143d440d10b005448129400c1c4000544940f1413200652610309440c800b24414040441c00003281c1103419 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 684164055 1250 684162805 684162821
    0x3070810230f041b021501050a030318090c030b0109060203090112050a06030f050c012a03080403030204050303031609150512070203040e0708060a0b070b07030509120f090315160e061b01 82
    0x1170210340c4039822040076051119424022960440c06c0305030100042407140380d4017298403142101c0c214145882da43c2d1142074400c04411013000c80d44420700c075001540c0c40020a001030400d84090b41c01c00301010002494400514600c0ca08540c4031404620740e10f101cbd030b007d00300540d80100d00c03c00104040c681075458141c1b003c1350750301003004802810700c000541914091100d040a402c0200101d480da0142d901000c00b51081d01090390030b010206c5c01d9101000114081c2c0328003d1840c8045044004c028040301d0309410405201d1a0240e030000ca40350004155801c1076080030720294155a4141c04a00d1406182d1100703c4504642e03091102c0203401540f201d0154105070b64512842c0c3e11218000100d2103a000b0040c00707107100b88001007200d0300c240d010a4202103500c007038072a42e04000318a032140ba0080f070000c034180c02e07002070360fa03245140401286001096940940311203192039440d06141c00141101c1c00c050100c009445185070b540c00d01290915400f03500f6600c0d074020000e488a000700600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 684165305 1250 684164055 684164057
    0x315010906081c27060509041505011b02040f14040c0603060e0c03042102030c0f0703020d0f03020102090a090225120311090a06030203070810230f041b 67
    0x12080100703031020082201e041c0c0000c41011014a43d40603101242c80490b000a15455140b1028040000800c010040c0d0020000d50b980c8640f140b101c075040008a40c05456207941d500800c1da010080350360000c48403042c1411901445401030324900106003d889903003450009249042007101140b50604506401075014a00c4000d40d81c1e00e0b98019001ca03090b80c003d40e55000942000201c8022640b0000c0d0b41c454171410355004000a5035917500d4142c1c08841d010009a0000714020245110801a104684902d180101059451078010802080000074042c041030000c88158041c54002d40488408880c0513250400090340c0d034074814000d410540a441c0c60a01d011139800c641c44500e1184115150009034030501490785c0724054000f8122404000031421090210200d1a80c82c0b2a000000344040d48001d6620f1401010080003018020070003042c8141c0b04005011304403a914080c49460700510741d50b1240e0940c0c60000d0307690888402c04c04d42c0700b400d00b401e0b19130308004600040403240315 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 684166555 1250 684165305 684165311
    0x30307050f1e0105010e040b0c130306050901181203090302030c1b10032904060b1b0d050412080d0906091a1003112403090c1302070308060d05030903150109 69
    0x1905207013640c0d030a10485e00540c4108001c5000f0508682545802613080d00340180742a0074008221041c001c0340e0320550380903035a9010080c1800080c00b4200c07400ea011002440300003440c1d5070700c032403000406180708201070f0b80e080c40c00105802002141c0d24035640034211101a600d554286001418404400f800b8180040e00104200c1c000c1c0247d0740744815066102a01d80926195000140070290401d98001d454020029503440840000d20529480c86008082d56030307e001c0f403501d0000b46071703074440400004000800c402c03102c5600b011100c0740d01030701d02070340d80d00600d06601c0a400943d4020b455945080c1c004410040c014021744450801c814070301d030099880030b52190702c2080c42d101c041d24004064800b034002d494210560202c0104158901411042103c080800783d041281c2c000029030048442584503d0b1401d0b20080e0051040400c2d86040900c0c0d078018025034001d40740340e0080318628440070401030184243d44500b203028046800c115684410003c10110030711407080e40e585 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 684167805 1250 684166555 684166603
    0x8070201052a0706110c0409020a05060f031602120a110c0604260c010f0503060315041b1e1e03080a03150519120c05030102033309011202030307050f 66
    0x40680359007170800e4091005092141c0d15202800040c0c24145012a807091011201040c0d9a680781e001e00300b403864884c42103484c1d2a008050004122003d203040d0207652081c000c451a0700030301402c0307030036070025031400d003409820180c40b191504200080256100d0000304003c51000409001c01050404903d010301c203141000c003c0e261282558418103000448203840c02100e580543c0041d40c2001c2c1c0a403c4408940b803560f44c00c001c80d04182c3d01100c3c0c088807901ea510383e00d04090614005001e003900308605a0847c1c0c2e80d4801e4405c060302c94641d22101142030b4400500c89058220000c540048180d9901c0e54800300046c01011a20001030b4040400040410203003030585003910400c0428a50b101b0035400c040e02840e007905206170440f01841d80d29000b0411780c500703001a500070366000b2515440300342006403401d001d8100103907072842c4003248900098503960341c00f43c46044442d030980601e0003140c10f0000ca41544200d80c0041c0c01c0e0302c00c00901b200000c40008200c444c0007807894401d00099 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 684169055 1250 684167805 684167807
    0x1b0607030b0f041104170c03010203040503120106050f03190e0a081b12030c090d0c03060b040c17010b0a1206120b06030607020d05130e131401020901020a08070201052a0706 76
    0x251260b00000d402d407014803051204d03684101e1840750a06d503030300803145045442c50010742681d1003110101c920350004140c14840c00c2003452001c2c050700032401c0860034950040484d1405000c001d00c0703402c101c03e60100300c00c08810a58003010345641d17190140c0e9115429410400100d50280f0249243c3d842c15000034090410b001c1000301c3c4040d800789135280b0b0368440c0c0315a071072141c2201071019801001107100c84002103d5284510040d481a82c9c0417500d210301404010032a102c041141003030106070310041440c404801895419103c6041d059511000030610483d400440c802c0820104d07450700a0226840440318409400c4510a56036410150303500001d06440305015224280581d000d0860560300501404c00b418800420340c0012210381e6880b813511280000076921a0000114594040b00b800900d2003180041c952001c001e51503c1d0701d00b40003d54070b410b1400c000d8800c0401090714421a8424002c54050450180f1450710610203241006101425a90003580da441500d10000e00ca07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 684170305 1250 684169055 684169061
    0x90c05100903020a0b040e0406050a1e0c030522061512050304090605030f031602062710090510180902040e0a18030915030621030e030f03030403051b0607030b0f04 72
    0xc0d447c051140b0400d51101e90303510f4054840a013050101540704d40c0031800340740480b00445500c18142d80089190103a00c2400b504072003028000c102a00100000c42641e00d000780c48175011590b12940000c0c4c252041c1e40240442d00940e003010142d02034501f058018008000b000d402030314806207080001640c0d40301010f80e5042400d01c010f1041c0c0041c0300b00390181110f0660350060b5070018243d0762074a0004400c911100c41d0908061004404192142445003011191070300d180b80e079410480c600a04090024400e08140c1d041c4800b0410500c8c09009a880f04100d0316000f0203054000b0341d280d07034a546051040640484405414904d0100d0041030103082840c52083c01b501030300d48109460070035841807046007001d1189820305444100010b900303100e42415142892548602050310b4019240040c07444840c90321451080c1d1011060500446010003120341060381403c01e81e5503000446021a0000d0592000e09100d000780002c1202d42900341d0024102044210f410003000c2030403100304011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 684171555 1250 684170305 684170309
    0x6150703090806010b12010e06011e030e10020301090c0e030303150f03010c030e190b0c0f090a171509030a0305091f09060f090c050907020a06150e18030706090c05100903020a0b04 79
    0x150074001010340403404000a5002a62f0a18012842c041500216460400103c0d0030820b81f9038000f004001d100741c24458951076074000e182ca6610700391a540003036941c0c00068901d00040030115602a85c40d510200e50440c0c1c1e58014009209000d0502400f40090203401d0010680c3c1c098094030000c0e0507028400c481080c1c0d44082c00c1c15880e103581c1c0c444041500700d20544040c0c0001000300c04215591f0002d0b650040c5507035801c00031554400208103003403960b0400761107200f004010512420780300c0403043d90b42d9845d8520b800519503403900c0f8070520300014032100349c518003911990480700d15029001400201d0182e04140b0032050480c0303e0004403a6245006404000680c10a118a103081d9a1840e04485180304490014000381c95102c00c4860b00d41080401350305440c401c000d4032000705065644200002c0b018501000d461108a0702c901c20403c00511213503a4030400004c10241d158101c026210103005c0c0c40c442048400060300d80b103c00d02050344940e04c031740000190b4010321011039003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 684172661 1106 684171555 684171557
    0x4030f0506091b0306240a0603052d0f04170a0c050c0301060609030b0601140c010510080c01050405041505060c10050f06150703090806010b12010e0601 67
    0x2140443d04004a29000307416244086595800700d0740540c0070b244040180c0d212001c1303c0e0f01d0b4008000240305c0300d900582800d804141541c0c9030f8840b1b841601c51441c1c2402da401c14407003807080803421014003c4001030580005050190f030003c026080741c820741c180c0c94591159504061160405040e540004403000c080e03006000080095036196501030340208812814804001e045041a01002d08580d020001190280c0d00c2a1043d01c2c0d10407000c502c1c291603203081d0a60b030340601425140c05040b1380340501c1c04103a960000c90880103d14058603014902442d00301844042c190000c0b83c403620303240b840c800045646564006104c00502d40000d0714501d5140028402103a502600a01d52025a1001c000d02500c0300c100030a10412541e40041d240d1100f0b207803c0724440f0f4582c102c000b05014150001850040c0003025140d6404d000584a00c00e80c0c031520314200041c003c460fa03034 = true := by decide +kernel

theorem cover : BRFrame.Cov 683992805 684172661 := by
  have h0 := BRFrame.cov_init 683992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683992805 ≤ n) (h2 : n < 684172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
