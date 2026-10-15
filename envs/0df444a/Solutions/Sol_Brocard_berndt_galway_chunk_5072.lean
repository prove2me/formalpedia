-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:03.160982+00:00
-- url     : https://prove2.me/submissions/4035e28e-ea37-40a5-b505-e34959f606ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912050359 ≤ n < 912230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912051609 1250 912050359 912050389
    0x601090f0c14031314030705010609180203070e10030206030915010b03101e051f08060d020f040216061104061404060c02210303010909060b0a0f05011d1806 69
    0x6442d8003a040307600b140c9484001e00c0c1c1c8191403020030158042141031008610786120b01000e680e202da600c0d1070710901030006481b9514003d800c0405030150801300d040701e25011a8003d004016280c41c0881d61980b40d00300502100c41d1040b00d1a000002d40c0314000114403c60040300030300072030790504800131014241030704010011102403042009c1c869107010f140050f20040402c0741e51720200b40c04102039034502900142d40086403a40f103040038900060124603414415100c030300c8180e441c001480140d10320848041c1d4406802500441642819801800005100d070505500c81c2e030140c82d8903040d548500c51646412800040410145510184100c81c40f544400201e10700392801000602030040607102901c50005041c034218400816407900c1a501e82290a981e242c1da502c0340c6c202d00400880d141507400d0b41c01c110b0001940c0ca413002c1c01c001a1800c0d184c8010040d400c1100446038461f000c01642500d140d81000411203a441b03414541804051501d0b000fa0b034541a000d0000c000f0441300d01d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912052859 1250 912051609 912051617
    0x60b031504151109030a1b0b0c0a080d0b030d0807021e0c04050c22060908010c080109180204050c09010908030a0503070f120504110108090c0306180c030601090f0c 72
    0x34880020b044001c01c408180020340081900d01c092201c5a40500c01c1075035041d0f040c80740484070810010350189525503030f5142042c0800c81d80d540c00c0d10300100c1c45440016a42d5400c14409400040c4041010b00600d4514510002d02c601c0041c0200703292540011451000c00c800d00100100c031581004a0002e02c48090f64040c4018101100580c0d2491001c01c818800da85810001d02c81c80710360015600c00032078505041d00c008080c50029041c03281140a41e5000400300303540820454014015401103910036503420000342c0c603100281000b03022a032954400c12400c00d007151301590302c0d40110f41c00b401114141c0c0c1d5a5100800015205001580c0320198035041400284042038204090b82e03030200550520444040c80b0030802c0703445640301865030004030318290510080c400c81110310080f030f0704280c0f0340100d16101c01200d250307506288038201d54964000c0c4000780c28030760005411654a44000101e4402c1948400081e06003030090700301c500f5190f6980c0e0110424000c90045000d00812070030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912054109 1250 912052859 912052861
    0x50f07050f04091b0f08070b030f040b0403142215050315130509100c08011a0904020d380d020f1f03140a15170705030a060b0315 57
    0x40891992010825264420355550300d400c014800381c0c440c0344040700c100300c240d8245543c6500c0d030041500b00f140500580351044038070118180c0404400c4132b0144006500d80d40e4282d0b50b560302d040704114011701c2181008968030b45180e44004200180184242c65841ca28a080031006900030000d0180e02c0b9142c0ba201d4810118401d50700300040300c0c2c0040030500b5401320070860b40e01050711421629101c0909614020800c10904030220310008074440041c4140300190481c201220251030130300072280d140044847e5082c941640d10010842a179010300302508200c903081d85141141c031000390030210420700c030091303503034001983e0720119030a19000b034942c076018050400315184013507840b0300a010b95070140140d15542c0d20601c044100c5018442c0c0c01c40c000c000454000d01610b441e8008810150402e000f14440c50003500a40502c085a4140030b00040e162080108020404201c225014042c018001c03a59481c24494131000300d0103502c0120764040c5441c28185048203102e42160301e0f82c6030070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912055359 1250 912054109 912054119
    0x303040f031502041d01030b07030b031f09080d05010602070905220503120705040612020c1207020a0f03030c0b0f091213051309050c030a120f031e0603050f07 70
    0x600d503001e403034100011880c1d040c01d400c1e84000a200c0e03030300440d4610030300039150310814a4035504141070700c0c0720385e418040b2038131807010540641714141c20045d41600061070900c0320105203200c035500c444000e1408910410345840390401540402154144161540014040d654041001c1402404084010842468501d51821080c051100d03070708002903c200920007030090800c1a100c000b110310002840070705051001901a5001c1c0c4604008502c4200401c00714024a00c2a5904800c04030f01514400902210650071317540600350490384140f8105010800701181c20001c1c01651003078031104804d01050401d90106480100000750f0700084508003c16440045990030b2420340000d84036407a031030300c0300c890550080d07103800040d0048103c180c410319079086600721a02d02c034003a900781c0e4260300d0041c0505440e030701c40e05000f070300c0c000b1410780a1229500ca20070310803505507203140002e404401c0074000d024100c3c01d003051360500c0381c075201c0170b0061140a01c03040c5c00700d01a6078000c1c6109031501d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912056609 1250 912055359 912055379
    0x20708160504050615120916050102030d150b03010e0615091c02030106081005040614060604030f081b1b0102060126010b030102210a11090f0103140a0c0e030304 71
    0x80c0c0220780c040c40d1100046181034595101003c1e4440f00032142644a540e5040b20002c02101260f1741a92885410f0380c5020417004090051309442c41a4060b614085c20702c803003000503100c034615002d15859170801c00141140170704099400f03043c41a185840320f00306a010411080600d401c072005a141c108000a49542c0f0504000302c80388041c00d039081d903136025000003401080c0f142e2004c0700d1800764241e8801c2400c413a9001c24070592145c0301c100710a141c180344e8005052011903000750000c0040105101168003500700440d0188200740462a0004002190a41c802401c00360380d29075014202c102a40101610003000b441000c1c4002c0c280d81d85400000c80f420302e4085403000807142842c11881c0041c600b90003205082d20042c00030f55944419811b02464110b03050035132000004880086a0804001c0c040d04114850806c0101e051010b03a070704111289550f0360b24a41816519032800d040100701c01340340c030b2280c8201e500014082d000104064804201d01201c3d80c840c1e0001c0206104c4103501e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912057859 1250 912056609 912056653
    0x3050c090c0403030e030f1c0813030f050d0e1b130c05090607050705120c01020d0207080604030f1727070302090a200301080718020a021b01120e0a03020708 69
    0x18900217030000000340219040840f050f4001856009a14001104000c4014281e510500c1950b03141170694402c940402030100310301d4002c00240110030130300c401c03e10440103804030103040d0400160307aa203010100c82c5801441504000c424080d45d00000c09498042d0620809104440051002d12200440200b8521549d07800d0751044a01103140e03000d01c8800c1204101510000d800035001c80742108140f81e0f0f52010f9000c06005105000302410032603c080340d0380c0c00722520a40100b010762517a54040d24180c68103142103040003a00004950f80d4020b140d0343c3c900410b818203980c0d50705140b095400469040400030210389034006801000144c84401e501c960000401d40d0001d00b807174070800343c006071004914150100c018007000109500310085090011100321103012801c014103010550240d0041c900c6180140e00204143c0c48601041c40500b14080380524041a411800041030001c80d5007102d1401c01641c04407401300d0805804100100c081c0200000401e007032082081014141c806d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912059109 1250 912057859 912057863
    0x60408030a0b0a090504140a0b070c0327080f03070506040f05011d010b0a0f1203140904150905090610031728030b09090307060203100306110403050c090c0403 70
    0x140000019004041c540c0c40481c00d21002400c040c1c11680d81c0202201600d41070b202500c1d283d40604a07184084000580344000c9948601141050f43c1c90b0401a600c100c00c0f00e0040d02400b02c0d500064500701458aa10100c46810030306400000f802c0c03130600c0303240c90079002070105154020060078001c41c0700025166800f85c0d1040403012006941e14015014000c103903010b417400014500781d00403074403040d0031142043e04155103211040c0e0391158a400200300c0c5100c0d107004201c00b0004240428428500c0000880740b00d49040c2c50800c603000030078201c4c0c80c41c07542e00104c0d021880d0148981c083c0c5000e069003010f07900b00106802d00344001e0000506065200040c51140c480501410b500442c4056070f03901c6034400e00066042c2d40714a00b0341056003040d400c0100003450181940c0b03060ae009107106009800342e000450500c0000c0d80e90030000c1d44050801c080c600c1905c0b00c00000198a4007604032803080000520b0380b10303403a500d860b13890456004544c40c03144d2005410007880d4104001a14110380d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912060359 1250 912059109 912059123
    0xf1203150b0c070b030c1c110306010503070c1e02031005060a1205070812251e0c0e0901020c071401050d0915150501090909021c030212040e0601080901020c0604 71
    0x11009991561420b40c05600400d05420003004006e038540754140a0541824540090396030450259000402c9407510001800181020b2000c00e400d544900003465102e04241049904080700361504c2c0415011440030008210708040c02004609081c4441000079050180c01d00c91818400c1c00a01c200d60300f1b0182d809140581480001848400c101820083c1080d005850115406000c0450700d82e001d000b40c031404290a1805541102c0700d81c441c581d1040d040002a02e841207095101035411209901c01c1d100041c0351f460105134800c104084c076015480340c0340016900c0c51007161050500040f548079030340707039180e0080165060f42c015044451140101400082c003445038a000343c2d040140c100d46005882c80c10400c01b491081080c42c140a0381c9090321403010a5030b0741c0c88100244c900300d0304c000790400700d0700006140103117120480c4070300244a40190f408000c1084d05000b1103401a0380088417001062061000a50300303e10020707004003001c0000c7d450510740d402d00c00d0b40d510001e00014001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912061609 1250 912060359 912060367
    0xf190f02062206050a030c020a05071806090204142d091e04030908070902070213020a20070609050a080d140903010903081b1207050d0b0d0f1203150b 66
    0x48004011500721105146003501d0b5540d495500081c04c1c0d400c8180c2c80d0000c64500076040e0003503070000442400071030b0300800a01100d400c01c004505003002900744500340750346030030300440c1403011030000d03001400c0c2000c628060500c18a04000e030412005550b403055242854400c1600c0402841d42104101c003034945040b80d031540f180c0c8a2804505040c030345070142810b820b2000305548607089401322640c0030220b03075003a0388921b034410480c8140a0029800340c64002c0b02d440030607268004e00000c0f00300d4100fa8800c42da6000040307000c908c24007504012034129a000f801482e41020880e0b014000680310355180c18140303240070b50f45002011003203042c032032042c044045000782c0c0c0085400414001d4001d01c00d064070303032030080c000030b40c169403803030321a640300701c060848000840c161b454114404024404589400d802034070303036038805041240e125880c0c2d08001c01e01e0f203a1502c192807107880384418007039144c2c103030a04403030000d81180000201800c0c5919011010341c142080300a54210300e10745551 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912062859 1250 912061609 912061627
    0x40504030f030c120c0e150a0c02120a0b0408030a06060507021513051306082505090405250806090f100c0903020409060c0f1b0605041e050f190f0206 66
    0x9107020700303013241c10b0320350421803462480ea07031025580113160416918503080310348890070a0890b0040a1052000494918000001d8600003071480d464000e582d003540ca20000f140c481d0500360200321002c0e03c81350f07400400c0c03201c0c0c2507c1d84104001081d8a1805a09002c0280c3c009001c50106895038903030f044021415442035100d1403107440040c40c0040c04203040602c0358141c0005400c40d40715000d298054401c40307002800c0b0120b0b900718000300107084c0700c00c0582418100010000b01420a4640c1d119466118545130b420242c0b0401010034660710340761041c13602c07143e5031501c40e00400c41400780e0082902c00413003c0d00041e030020381d612a2807001c0b8240c0c861450496034180b07aa44080e500505146919041c824a45e005056404450b40d40709015a00010187c5010b25148503110060200e10b01100110341e0550191740c00c548640140740d03048d400720f416800c030b04040301426105078000c510f4202c64032004000c5006100200003050090100316200d01940b8214481c005e40a04400911580 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912064109 1250 912062859 912062867
    0x6160207050319150509010f20191704060b0a06170604050a09060f1a0a06091a0d02190f030902031f090f030f02060f09030d0f0b060a080411040504030f030c 69
    0x1132409541d89042015140001b10700c0e0103880c07000e80b54000a0b140c00c01b000c1903110a4600c4125898824a11515100044180a0100d80344001980410110a41c0d2003603e1400007141c0340100d000d1040424295a0342c4100509104180d0082042c001091029900380700c406c05a280d005104031000200c42c0d445850306000b61241d40d00c0102090302d412103900214810b0340c030503466241c0d00300109240b0070041c0144140004140900000325458000802480c0d0704c10000082c0c80d140000c0c020708000903031200d10180c1c0c0107600804c071f103041c201c501c443d1031030342c444108114a140ba14007800085241d0b000300347c680c0b202c8041e004041c10130a4504500d4042a04820315081d4418038000c80c0344c0c0d26040c003c14500d910b40340680103000305000310359605031016a8500030002040954600b00f02c6905d0388004143e01c00d41d562b0070a40f030b45040c1405070ba441d00540300701201030312a09420300c2c1900e010a01d40b03012840d03d902c070300e2030035090202003031744a03105040701d07407450500240c4103000c18003d072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912065359 1250 912064109 912064133
    0xa150612061b020102070302100209030703081903050907050607060e030f070f11100e1e0306010b04090f0216030c0f061d010c0c030e27010806160207050319 69
    0x40440d040c0161a9082084541c8a010b0b41c0503010100e9040b4104840100d00342e01c2292000b40041e80164400380c000e0030540d008000460008040f00c142590f607a41d107840300d030851080c180314070003841c003440d01e03864050007801e83c401840030103440e031582410005442805200006880c442d9206402428840c0410440b40f0140c03200c0030140d221481803500d24007124030240103c0d002031500001c07421904050000308096249912400341f449644802e0004546c008080342008800c111115229074030240f00c40f0740a08040c032091035903581807216040545245444000507030f8410440100034200b112058506c856040c0b4050b0014a02402c00d00320b0914000d00c043e24492500c443c3c1940105400d8484904240000003030090742d0f51800291051b4207070800180114103c64808039140c81d01c2249400c0c18120664480b100100800c1401d840400903007180d00507a00c40c5060103451502021101594410780c8000c20040341880082138071080c400180d500d85442410b02041084405100701d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912066609 1250 912065359 912065369
    0x10c0b1902091201021902030403080f0313060e0f15040b04030f05070c0b070303140f0a0b01050c0303101a0325030603020301050a052e0509040204060f080309090c09030a1506 77
    0x8808074001043ea8004d5000c1c5101080004440860708030403030000c81924112900039000a040040c401c000c0e03100c50707000505140c0540c1c80c4c0540580044e01900c5004004030110740285510702507407861500e045440f010540411415000f0000006c2d90300200c99405503040c500003484c4030900c0f400707413030502441c10000e041143d00030b0301161031b0207000080c0521602030340e01880610f8808441d80314001044c1c85d800400305031100080e44270180c5030001c002203031043c908645001d0a1100c1d850558205403000b10313242c41104010000c0e07003603045009105d0100c80b5151807950034114030005010000e0b100c2d191140d0310000d52401c0441c080c1d40311100445c1c0140081c019454080700b0400240001c0741d500c058400045964031142d4040d680ca0702200606a0845c0d120314142400c00c048100020002c90344103858100100360203c11003464001090520001c5441d000e2020030840132420007400310640440c1070000b02071039580020b2140c01e45230042464500c05240318100001b418141c1c00c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912067859 1250 912066609 912066619
    0x30b10030612111906110c01090602030702010e03120715060b0f0a03180803010815180d05030c09030d09032904150e0601080c0307080c0f01210507050a0e010c0b190209 74
    0x80005d00d1130f00f00042c5440341220303609690981c1201801501e01f881140903040041e4024081e030401540100b03040078128030002d00711446081000c0000b1032550000b081151540118145c9004010f0540030f0300d03002c0c04e00800070750305044003480c0035642405002825804c1585820303054144049454221840c03c2e04462002e40c2c80d80c486210a40d074402c4889141005055100013801c6840004400d1040c00758003405010300032070000085410381c10141c041080034908100c41520395504004d01c0321b240089031182490103146050085a00c0a01031000d42180074840c0ca010f8261480e0150311750080d0b10041e40c150080540740c4400041040d00004c6080f44100c00000c2200c400005280807a240214201c81c0d009071100d00c800d44030800d11000c640c0140e100c20b5201107542c05602d0725201581c106809111130500646204156041a54070001264000404402041d0701c202c010301401c0302802d01e078080f0300d905ea5070024100c00c028880031101c00e80c1c1021014108154045541d003803c0200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912069109 1250 912067859 912067909
    0x20703030903110606030318030c0a0602060405060a0b0906040c030b04141801110f1b10060e090f060615210f01080d140a0e0d03030b1003061211 64
    0x94003900410540703009801060032610000918040011454440c850140113141042001050f419000f611505090b60502410075088090703101c0940d100002c0036030303900800090034181009810b0102c00303840320b00d403942080041810380e200c0a9500750081c9080d640002c0300c65400204400410709000025441414145000110410b0421850041d0021800c00660782550040e45080300c00785610b02d100988140034018443c11594003400a00c0307107610b41d0003801c01914403801e00301b074002041c1520403076440c242030203107041c507100c030310b0b4071a12442c0103001d00403800d03c01581c0c9200080025114040e800f020100080c0c249080c2c620945c032041030301544040186010008001c2211585a40018040001842540023800794014600398462001103034000d41c0104041c2e01980780c1c0d00c10f000180b0918615601d035021001400c0e8040e540004081000c84100000002d46052440815080039003d00c600d41703d0701220310202d60311402c0c01d001101c920f40400d010484481d100303920000009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912070359 1250 912069109 912069113
    0xf03061804050109140115090c05040305060702071a071a07090503070b0d0b06160f0303062102011709070b0903010f0e0d08060406060509131e1e200d0209040207 71
    0x504070035503c5100e0511480307246556900c15080307440747c0e44208980281c08030200407021b05a03002001080951034030300e16082c3c494580e549400402e407000300041c1e010200401400481c0e800801000b10001500c61400c5000e40f0345e0401031000c0c1141c0c200507031004e4003141c890740c001c6008000034a4050242c54031213a172036624100325040040c4880c0c030141031808000c2c10346052001ca424264040080b80d526085a450702c403600c146c0d8840403004c3c965545008501c103040050741c448031002d405aa85191607180c80010f00114401200c1c0103460b841c6010b00ca00c0840215000054904050007140c84810b81e41c0001e024045d00318400b0049454400700200340c070004504013078014001e80360007102e91a00e906000480700c403031040d0340000f082404000d00600d0b106034491031300e9444a1000c80e41044a22000043c20915940c1944a5075205e01042d0546100c049400d400209100104445a01038a0139040c406510004030604080000c00c0705490182d0340c107440c20402c4c0079200315100d420354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912071609 1250 912070359 912070361
    0x31c02010b0a050603010e040f0f1509120305010317070501061208040501090b04030f020f0d050d1806030e0d0e010c0b0c03040204050c1e0307030e06042d080f030618040501 76
    0x114181d50081c0040c080109150400404a074121800f091070300b0501c1c2d0322911540c0244840e0141120341d241c019240340c01044680041c40030220081c1d40000301035541c0d28245e16034400b10b1a669041c1814100104081800f8040409d218544103541665038406440c0003030061600760030015110302e001c115082030003c0303100a401030b2642071325001c0c041074a45a00f54410300481c8801401d40c81d1200d5400014104044603180d11b50b0f0282c281861084550380b518100050103c0000c0001c14020150b102c0790850000500280824201004880064810a0b4462000701802d5003480001c1d24000c1c9980d11440243c00115002590b0000c00c0c1010304d034500442d401034809910850030304011903140040303103045441028072801102d6100d0f40813481c081c9075070401018082411798801c2504207403c2c0274000944181e1103035807402c0c203000b80106044510144007916145075186010350400183d0b0980407143d06003100382101d52603985603c002180070307840380070070000310010303c0c10300c0b0400c841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912072859 1250 912071609 912071621
    0x904121202030439030f02120d020a21020601140a0b0301120c0b030c09090c0405040f0906050702070f0608041113020a111f09080f07050601030318060807030b031c0201 74
    0x8014400c43c00d4040c00d0100e054195113104501c44109410401000015048001d0f04d841a00c080c0c0302100300040180841c0c1002c500480d8280541c1100c0c1e5007004002b44400c109190201001010911080d03000c8000e583e0f28050041400e001e032100110400da91300c0c071210400402418214070f50300c6d80c480d0300075005100e10342001c843d09110120080b4074074000c7c80075a407042c400d05442c030f81400720307581c00c00840c2072015010140441041001140d161214011801c00743c03690100841c64071101d180c01e00c100c510040c050b07011500900c00c2030000440064201d000c5500c030785440240c0da01e5504240e4888a2501a4641d00510800480b483e10308207802800440c0c0c0551a49201100207034420fa455403c0d4401c54038009000c0e010240c1981038070b510112489004103e0703076040151500c61600540d00044040c3c1d82a44400010020180d114481914a016038645105442e161001c0600762200c044e0000c801d164a0343d11526803510100041603604001030061417020340100e40207402462 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912074109 1250 912072859 912072893
    0x1a030405010f090c0e0f1605162a09060b040b2808062805211b0a0b0421020126070f030515010311070b1006090509040209041212020304 60
    0x1034000c0060b6402c0c80000c006ca119001080e8901e03401c2d42c900400b201c05511000f800d5007060319051000c00843d403500d490381003034480500d000d18aa411000c2c6071027580415485580340509152050040303c44440c1078404640c4488046034942006030410350b03040382c10710000200c15000c0c0c207004035038560002280d40569401d581000810600d000300b009515040c02c0b40313060016094400b0000c0c5e04040c15050407042c41a084202803a09505000d03007417159521084501c07120007140c1242c249000303a0307110010400484018585480c2c806200001e80d962403543d050808000040d00941e401410308008903030701088000521703200b001003020b200c401607801c0f500103030681102e0208240a4070070300380641c1100c01005503038110780b1700450150841c0201d580c910721050015000081a203c600350185e510928980301150030404000c0091348298009445050100c0074000541c4404032117680058019040d80c1c14440301c45c0081d41c010600701010340c62a403000007000305205500c0c40d5294401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912075359 1250 912074109 912074129
    0x120a0b0103050a02190f090f09020403050f0601030f031409031c030b011409040917030103081e161211030f130f06090b130b0403030e090c041a030405010f090c 70
    0x601c034032802d0812400354410311710400a658002c1c00629010f80c0c400943d4035985d00e0140c0046485003500c0291040d241d003c01c000680101301441081428099407580d842d0041c010401907256488448503ca9030800107014030001c4210b8001c030400910031214100806411030700011412902a14200d5494204000181c501207941b841584110050400c1e46c040c60855424800702d2000c2100030503590b003040310245442e042501148201b8006140290300840c1036545422074240a01c55205072019403100f0050f040008916000d1005441c00ca01d0707811003010382c100d10108c001078030344c0c4c030101c0c00700c440921020901c02a080c2d41d4100400c003401000d0368011002e0b40d0354420710040a0366002e4000032458603002407140d1312803140901511a0548159410389980340030314105540150402d030005800040d8807031041c1414485290044014201507240c1403820700b20303188006c00701e024440052000004a024031500750851098201c0b480420000407680d40703003c44c030052041c800d00c41c1d19 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912076609 1250 912075359 912075361
    0xa140c15010504181712040b09060903090d15060503060c0d0b04060b12070e0a031a070f091a0919080d02010902010c0b042102010b040b06040503070608040206120a0b010305 76
    0x15040a004000c0c411550510612059186503036605d0b5a21141d469051164403e10a0785a01901d140000b4025805070312000140d00b00070306201d0400d00000c1011030700c0c0e4001c2044000b6621440c40c0ba50b022500714005800c4401592900b8020b00002e521566061240c00244a80740d284880140403240300b0607401c104007d0007506210544125204030940c080060020b001c810710440c00c6150301c4101850451102009100001d960b00407170303003094500b0300040b640c3c0804c4002e809041c980140d803604082000381110311000b450400c26001d00c1c20046442c00940c81030701508000e0302c410200080c01c0c0d0002101c404400e4031110b90342e1040d43e041b4030580c00304091060061064540c400d8040c0d540e540c1c014a140c40301c040304000034100700c82041c164641602c501d4814200c0c208501034950002c10800e820404100941c2c6001c03008501c00e910401c0300700255540069120100c842d5410107a260f80d4a900001d02c1901401d04480c000b4482f0b40100004144140c2c840858564240c03000c0201d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912077859 1250 912076609 912076619
    0x31c0b0307060e0d02010c150c1707081621180b06150702061e0714010b0102070602150a0e030f091c0519080903030d05010512120307050a140c1501 65
    0x1c0058400c0b944e8000f03640c40c2c40e03540513510840f400740d00d26004140c881c90300420b15600d0405c40307140045090000b1592840c2c02084103800721a19081350b041c0c9042c51550a00358480302419000f141001c0610008901804040f401000070090700c1010f01820064040c0303007aa903415a5150b07810484003000c4500000380140307407004400414400d84107034141018072075800c1c0f1480d0382c80224082c6001680c0070b400c40a400140f401044024030407000142c0107201c9107002070035980141c1009041d034200c0c080a01059a0005030320804c021509080c0b10306072a0b0841c0b020040040700301401c094000000c418070031a680302e00802c0e040406039000d040e03005941c2d0b0001105000f441c03006105400c0b546518402ca5501c218005000d0700890555180000b8440040e03e1036002c2c1c40b8800742c803511000100700138a00b1500060070391100c0c4000d00082d9165101d9641c207840001d01310420302c00c0209104104034483d4050071686403039911030303654074480800f8040e51483c0c0d81040303058002d9080000f0032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912079109 1250 912077859 912077867
    0xe2a04051e1b0f161a1605090d0210020d0807020610060e220e010b09040305071b030605040303060e100b03010513090c09140f070903020111031c0b030706 68
    0x1207500480c090120260300d807036004441d451503071500070140b034006006540410800360000c20403070041461444c0c1141a40c548022042910341d2004030482040e410000c8015100c030b001c085030a42850210384e61605100094001031402a02a40105003080c800548580001301d0380c010310b409488074503807643c2c1c07240100c0e0f075100200c80b1407520301804182082a5802901d80c0100c52000a100d511122008000110000c51102903451110344a17690318251543c2807180c0602c66100b90703a846464036181e00c01511a1080c080010a1104501c80700c1090001000d0b06c4000707181d02c0f8a0502c2030b420182002030180809015081c030140038240800e60410224280c0c10403034602682c1c3ca170940e860300c2c003041805040c05e84c061005503240c40b54a00008e48013074410000d04015000003c00500c80c045280c1c090400030300038000c9100c9001400440c50b00541401c00300ca07030900c1c201064803004440380e0b0850203540320000031040341000a0845914a40181c00c0403601601140e55407035640504032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912080359 1250 912079109 912079141
    0x5040b0f0112060c054005180402060d0e03030411010804020a0303050c03092d01141206061218120f2703100c12110d0e2a0405 56
    0x2100d2010380c1c1e0310b020020b10590450400c403419030420605105000d840c0c140d02ca00b00d0211340c4242140f41044c0c10080c201c0b44a1107090913143d2192408260070000416845034500350740b561031500348000075086564007411503d14082c011402d05c105180888420317541d0308280c0e0111108031092000d413089520413a84640f10726002482c03250001c0c61520183d0702e0b41e120706610b4405000801c40140141c07100500c00664424016904032001060b04c001000c58164030001e0f4100a244a1030001d2160302c8025610a49800000184103132585000a1543e205080c03000f20b04041103030802c02c084802c0352000d100c0c0303a4a203054414902d0205100d03c2c0601c514500707414600400d101070300c01c8100e20140420751502d5885c11180104804000914003080c0da403241c3c0c501c6031624101d0300c0040c0d002c0340d041c0440c042c10070103200041c0030120b11105030150000c011f49450b5500e181c0001c0030010054002060cd854010030283d00d4184500c000d00210310002e1405141420007080b620385804200d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912081609 1250 912080359 912080369
    0x1b03150601080f04050715020601090c092d03021e03120c0a11030703050a081305010306032d020909030a140406020c190b0310170a0312020d02040801020301030605040b0f01 76
    0x10b05156070f07207031452414480050130a890b0b5202d1311102003140e41c84040524040c1180350000c18096141008003000d5510b000780c1c0390104020314500700f080c1110f100d44880248054030400c12101c02940c441804407030f860344040d601c191406095030140c007980000144012060702519080381c4410320940880c417610b000403405a001c88141008a0300303600c0241000f03200102a075810503501e4942034039000311100140c1c0c180c07600003411842101700284400046c0700a0a06002075851504c07078440806503405441c520084901b4a0240c1c80c1c920b004110303920364020710341c580c2400c003500003550702c0c0c100c100c560010418001458220750a404180c0d001c5402c40d600510a00d580740d030510800d03418400044005010b10391000c958925a24080d510a961002101500318a001292402917890132050000d80e0054075042c00440d40c007010720040303203002d06000369482100e40c44000003849a58040000355202000100c104200380d04008d016901442032180c0d103449241081c110101c1c28420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912082859 1250 912081609 912081617
    0x705010509040c050d05040c080706020a0302070b1605100501180213060e010507051c12020304260409230603070b0403020108040804150207050112020f0912010603051b03150601 78
    0x20103186460f400a0404000300e02d00b00d82404640b0008000303603a8191412204468440d405200425080142e00c5c000c005910040c5201c0e405034130080e480310804e028410f4850400500c0500e00c1040c5010400215484811111100240c07070584000341028060041c0700d0294091003007000c40b0310300a40341d00502d40210101700c80c0c81d1841c00e031340c042001210507041c84014010364020903804e0009070385150821050752880b00460500038641646014000d402034414010f010104010b40c0051000d0b0420035014090031001e100403003014080c942c0440380207410030400080300c240c0c007590419035460ba000100d20030780b1454201512203405000d0300c4040c11043c0001c002544c0f11b215159001401101d40f2440c040e2186180b9001000b01c035208000b6905c00d04042007156031020452181c562141e804600384610fa03652034042c0e102d425030b66031149000c1c0b020705065000a601c403800450344141200c03180301b003107015510718080410801c1c0c800d0140c071240c030303c0300400348501e94810324050359 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912084109 1250 912082859 912082867
    0x9050109031e020a030b041a0a090b04030c0312150e0105041b1d060c0a03022802091e1006030608070501050f031b16020906190510032007030e0307050105 68
    0x5220142c0055440b4140d03800b200c013400020118800e41d011501540c09070720204d03c1d111003880d054842a1010300b94400062400782244c0100314100c0d50f00c2e80207907151800462902083c1006c9481421000030060142d1501d44102c181c20f05c1d180b181000c665009190015580c2e039041084101e4843c5c1c203245083c1078840800782c00091080c0d24040104e054481001e850065030b601090301500283e81c1001c40740d0044002c103050540420203e018071904044501d0003a0340111040c00c41e42c488803009004004800210700311704161701d520b11510403400d0b0b00760241c1c9005441400d07000751720710595011174a80800400d01c1c00740403800d030040c0c0740180c40d41894401c14440c0b400243d40001e101d503c0c051a5111174542c00200343c0000c248020001b036180c042002c135401003161442d8003034109842000364045007000c106100b48100101c3c1c0d01125a281c1211401c2e03820f501a2400280b20b04103c000108403200d0b4000f0b0707a002d0061580650380703451056024009040c1c0c0c0e901c0703502800d4003241080c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912085359 1250 912084109 912084143
    0x17070506180a0602040f0e060a140609030114040b01030b010e0403050a0804051c020601170606280e010b0a1106060d021905130509190b160905031c0905010903 70
    0x3456071041d109081100e03422016511540100c0c0c0050b000b0800c4041100c2c2c08002100030302d04180d812040464004048618140d1181c0c150181c400030f45004090200e400c03020740e41c0c290722240300c1084140c41c0c00110b01d41407804c21614102400121809120322002151469200304c8c2588600d034152210ba05e002c292140035642c0d46401070007210f60348210940c4503030b801d0b805048810312440a40040070554144601c00d40d11041101900c7c1295106100b000340c00d82d60011310034a00d5441414000074040460300b2103020030710b540c0203112141e074014000510b10440d03000401401c40c03140e5900c01c107003014000340b03a2641003d9421a9210080006010251404200c1a4a01d6103d5120758031803590f01c0c008241100309841c2113020b502c0d030300e0302084106181403269000c1c200c04450b540c010f4607003980d2210401d02c0040d08050103411007a8611404074050110f14000c1c00c0f0050481d214003903c0758041d660030030340b031b0584800641a80c1000801c2d50283d1002c4069951000440756600708403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912086609 1250 912085359 912085381
    0xc02150121050d030e01050108010e0307081b0601030f0203010b010906021f0e0d032406080109020309011d1b190303051c0e0f1b06220b0a090317070506 67
    0x80101d00c461001990740e01c400200c040207400070b00a035544021508000d850301032400c43e48160b00400c401d0f4107042081c1071042000c011511227581c4a20400e48900d1110004031030441c0c1c2e415941080d224a100110600030140520301c0154800c82c003d0140322916001120f46038914400d40d00540c0c46044210110f04001b000c000400341d00d40c03000030340c00c0403114a040c5040036402342c10010035030360b01104807132410b036400540d2001e018200c854141c2e031070881c0007414020148100e940650b40800424104002904154030010010000c04514030081c109180c0780c0c000401c160418a050500030081400c207130744143d022183c0c0d4500041d0303040c41c54030281c81950091b010600030311148802400071301414440c04840c031424000800301d50104021071072904690b07800d090010f55404000c42c8855882100301e402030004000d040980740d020246004001d0400e41100c88091000310f0f421003800e500500440480780140201449140c0030744e0540000c0c4240030001d049030b0040130004415100c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912087859 1250 912086609 912086639
    0x303090c0604030803010603090f0501051e0a05010b0306120102090919050f09072303070e10411e04060504020c0c0108100305030418060603051312050403080301030c08010c021501 79
    0x1c3c12b080d452071a041d83d50b00b421204211203110682d803618141c6030710b04012143e15030f44846405005c002070350622440b5101c902000b001d0700d201c0d4001c10b0392804085000e4054592102d4080c10b83c6c211410704040522a03100020701c003c0420703290034005420101807440c01402030b542040644062030814440141442e1101c40304900b01c4400d00b00c050150b14204075840c010013003484909014207103a00d89980014a0703a011124000c1c1421540c035481c0d42d1410021142c926103072a10070040c401c007510200f01c50100403010350003152003800d40040140890032a40040b021a4100612601d0b030707081208078000d01800b1070303990740311400016265004580303150300502800c07104006d2503607a50707a0ba455a4404c3d00103000c0c0110490404081410500582000e011241010b025a2a0140d0302c200700096030b203000f526400b150240841120700844c00c03a000b66801c00c1e5a01e0740e03580c403410302004017202803054161540c030740b044188d001c42c03002c00c11541c204403070170080b801c0780d103000400d00385122 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912089109 1250 912087859 912087863
    0x30b012d1a070213090303050c04062f0f2803020615041b020a060605040905030d0f020f0c1609020405060403081c0f0b040b122d0f0303090c060403080301060309 71
    0x20400401003da84c030301c00b207800f1424000350042144007040c5001025110054030b10311500781d0600040c086513070041007a12071002c124410415500070b016910842d600000c1100190303000e440c00107186034501040342d000c031500c3c0307040c081030352000c45c00b1405d0450303803606011b00140c1100010503608000501d4002c2440c1c070091000c02c2d042c0081c068203050a103c4820b840259001c450020304004c1c10b409258002c0c901144c0c104400700081c0c071455181e11407400f84481e140c0d41e446d4159041c1159a0503079803d01c5401c40010784842c1c4115500d81d84001039400d201c0c8c82c9103141c40008408026000715020b544001d800e00c0d0802d85186e4a03614550094071410351174240d400901c4003a08154480c24111030020030f00401c0124614042c41704643c1c2c1000c540c1d0103212180d10085035507000148407600d40804250740f10758520010f0113038141c4908140301a0b80d50082c001038209154000024600030f805150030b03501400389000c2080164866440024040e400c10300c0108582c0d4046c1d4003141005e8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912090359 1250 912089109 912089159
    0xa020706081e07080114030307080d020a1106100303021b030a030c030e0d030305160f0e010f0c1407030c09050403091401032a0306300318030b012d 65
    0x9028400b00c000c8104485000c0083c141c0401040740d25804071030010000c0003600518640ba181c1d89601c00d00d803003141c14501106400203421000b5a02c510400d40c11082d0801c140c500707a091080e07408810300b01c640f20940040c8901e10480d240030125020038881060010001c12000140c0c1d0342c2920201103181d070980a010311110340c9062512504658001d003440390382c0014051070b01000014180c16802d4480081045503400d101010707400c03020085501009082c42c00f4610f1400344104e50106000d000240b1103900d2040d0030310000f01c0001d40905981c880d401311070b02c240d00c074070f444421070758121005000a4504102080b140e00314040101001e0010315000c10420010504507040211021188100a5403568408129a1305208001c05400d61002c0324443c1801c03e50845d00d01961380b40241401c2000070340c2601054000c1d4181d4940342c41c0040f9490803030727a49007455086500c0c00d125100100311300b0390002010b0a0010b0603401c900003a41c2c043c0e00083d041c05c08414645011080701031540d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912091609 1250 912090359 912090391
    0x2104021306080109020109080a0302300414120a0f02090a291507020604090b010203070212030a0e09012303100207050105090d03050121051204031a0c0a02070608 71
    0x29000600400d03020b09003010000c107008200c1e10004006a6065214400640012204400007503010403600c2c0b00814035240d0490041140010111550400c003c40112180005000585000c1d03103103101c40460003110011034101400182d1501c030380411900070080c0c4112614500140f0b09942e1960300110040c0740001e0300c1c4000307030710401c07403c1a00e2005d90400d00989070022561070710f8443d4400e02400400043d05007801030f400314000d4011809084400c1e51610507442041e4420000d0b541e40307540003050b0030018145000f10076180c0e44a02445400640481d6105540c0c0c20006a86812a1010f2200900c9103401299a602c4c000000749902d505020f04010098048924000313032100074010350000031541045a4064546503041500030281400d2000400002e005801c0328280744d1120060071211100c2132030b08901707001c0c10900480f9503903000304002c0f05100b0207030b805440c15401c40034070300d00305c0c0c5550441190034040d0b080703c440140c2c010001400040d100d9510950001044091800c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912092859 1250 912091609 912091639
    0x408070b0f0405100b010903020d0204110a0518010e06030c0307180b0c0f010606090b0c070306021602040c031401140613080c0a090c08060d14070b030601110102210402 74
    0x10120940e0805411181c140a20080c883e00f44030700340c00c0c0041e055080201d640783e500040c29411003880060305c01c16030006064255243ea4011190341003901c100c043e0b0716646a94040d101b41c12804189070181000781044460354043c5018134450702c1d00409150071540c4449101000381c1c00205000104500b8005190f10800071030140006080c111481945031904507002d20310b00745003010244d903142e041030403c110b6a41c010540341d06441d295844203584901c03141110b03241c00d410740c2c00101a20710008000411030402c4140c0c0c01c090340300300c13018072280607500003c406503111000458a040112401040010213a55140228203400f42030513062841c0694003020a00060744480219040500004c00c20b1400c0707940d24000c0d1800c42c0c1c0801502c2d01403540100b0300c0d24024080d5002d000000e91510903c16108a01e266007034000c0112181035485410002064006444941c080f880400c9042070042c010700903200040b018590800d25070140c0c00300c00485540161099812800385000c15031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912094109 1250 912092859 912092873
    0x30901020c120c0f0c090106032c160902090a0b0309150a06090606080103170a110d11010c09030f06090807150509060618070c06020405030a0c210b0c03040807 70
    0x1212070b105124464507403c0040280e41010500010788100d030300046880140d40d610f020780e03541520418900002da03214080c00451070690341200b0408103820610317248030a4203001401c000c0f104209260000110360725000362059002c0c051200b40d00c004142d40a0000280f41001f841d4003982c46e0084034104c912003580b2110051041d11203500140d00c2e840280101c3e042c500070303003009000a14001c2c00c4d1398510744495036a40c41c1c210050170b07402000103000085611070001d580c2664000c00580d00b03039285580e0043c000440f91000040194207210003984031600501045040307a801c180303508402b49140da2100002c100c180c10880d01c62400340b1070000820704c0be010450001d4601c2000064606040c1807040c68010f00401561140c130f8140002c4020340c60108a441e001102070500300d038940f480e490100d000c5e024580185030107105070b940c800b041c8865001d0800407510240910703400b0058158541e51485403c1c00041d0084401c0030200360b4140c141c02c001c56015000d003001904010303031030340c90207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912095359 1250 912094109 912094123
    0x903010623131b0c1202060c070f06061503090c06140f030405100e0f100b0f010309020a0302150a12110a0c0611121503070807060f05040b191b02030c06030901020c 72
    0x80010380241102000c11811100c580f2001c2c5c02c1b40000c00942c030300312058000c14070421f00c000b0404003850b08030b10100003940d080b0b100940084541542d80340c589401c003d000b4440070809449a42415600103249806003070850a10401202240d142040302070403941580d00151040b41c40d4440c0c4001d02001c80117a100e510004602072000d08419082109141d1600402c4c0d40c11980c2286402c43d0b69866503030720381d640d1021040a08021501e282c1500020759280c0d015800a500b0001212900602916000081c018141d06441e50402190608103100482d41c4109240b4800e040400007441d0f0140504991341c80c091150401084d14429070680104030342181054000844151061041c102041034040c90014030540c010300c00705d8a003000540c0e031080c481c492201842815441403644900c1541160702500516441540d50041c0a03202c60078810000300040001d001d402007000e41c66440309414000540040041c040d00080d0000c0015550000d000d1a00c0c0b99401c10444111550031300000e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912096609 1250 912095359 912095411
    0x18030f070c1802030f0406050c07170307110c0d0b1909080301030209010909020312031f080615030604080910031805150a090201090905060f03060903090301062313 72
    0x45040364508040c2c03454544030501680405801401000302c00403410442c1c541c02a0011400300781c81c0c660300103905541c0b007000d0380600617401d2030f0700d135244a0402c2c800a5019228a554200440c030700000c46584519624034159800300807244604045131200d00800d401c21031515400c005400d01c00c0300ca20444500320070850311613002000410542c41c1c0100c0281c010521203d09210307400940d1b001903142c0c8031a52050109110105c00700d1198040552031082d0b030061000d44d100065110781049940e0710040360384041003800c00041c483c01d4200801d102c0c2c040d80e405000c460401c8c80c140200a0b8a1001801800070580e850040c28840240415070388007641c020406810303a1080150b459180c00c9004101c070742543c2c141264000140d0b40850448110303011080d0014441e100c0600154141c60642c400d150f0620504040c44a03d40d0040014003101c5070403002041002d5440100030844c8260310201a10400c401100310b07a5418541460762f81d80e185240c00040191401c43c0000c1488404011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912097859 1250 912096609 912096623
    0x8180a03083409060e060301080309090712020c01090b060105121305120a080f0105270c0d021b15040c030206132628140a020a0e041a0105060318030f07 67
    0x4100080317600702c05a188000429910241f86604080e039665484c0f00f21042203009450000001e009544074043c2001c202c40545000d540c2c1300309800d0b055001c3e041c969003c2e02d80342c00c800007142e01c540c09041220700f00c0103115410b0009036501c0703160000142074920283d500e07001d80d960f038001c074250b0440141104451502c0e1030750207003020f02001d590b84105802a82c05034902e070f9441d0030b00c003281c0c0503039001316450200026203c0d0340f41a000381c864000e40d940100280d002091100304140a040a01c5100103401d00711514440b407190301201760f00302914041d1004c0c8000b5000d101505000004090340c00408440314040395650030b401c03410882a8200302100c0544844c1c10011080605c80640141c10440c00e480b695144040c4096694010000060001412040e03a02d1f245000340407400f00c0d180c00405440b0642d944038009000080d040710200c0d05001140460055811040303031041c140c42d0081c1c50700381160740e0b00c2450b50701e1440e900c0300c920541c41700703010003610b0915000040c0b2500d072081070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912099109 1250 912097859 912097877
    0x10824090a050f18032703030d0b1e0603160c1a0603101a10020f0601030506011d16031104080a050a031806020c0f040605090708180a030834 62
    0x58543c44101000d055a40e40e0b072050486002c200f440001030b2129a041d0340828070001030402800f07604101061042c2d074041c0800f0500d800004d04561090b164200c0588880914401e1017031420711501c10034610582c00032091021402403020300c081c03100000c6d0223060200c140209a220500308028100c10844c40300100d03010002142428450700310708081400040c04808199000324010f4409500c0c2c0074001e01c00301044002e440d2007000112401882c0500303840347c1e96140d0906135102d1000340103401d05001a4444000c0b402c02c403030041c0d031040400420981e1000c1d8021130807005040042d0701ca8074400300502c80821079110a000d1030428501c00d400410350b0305c40d51310340540681d54845080110905400e4204941070b0003040011030b0790b800b00c1d0b20b8942021501c00140061150390482038120090344204070301950014201e40c02501c00100c0d0314440f032a054151541e07076074050001000203181401107080e21107201211420713603000782500c0c0402040310880c00d40ca090b0050020b00000d125031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912100359 1250 912099109 912099121
    0x30207081801140703051603050717090a051816050c07061205060d021e0a0308030a020309120f0d020d02072109050102060f13110907170a020405010824090a05 70
    0x50011039100851a2440c0d04040e45610054a0341c0102c0140100748100304c03480004061042c801c6540c0540c0c01038a680005a012f501a40c598000703410881c0100300108011595142441000381c130a03d43d402c400c15156129032420619440c5c1c2003850050003c00d101c8001034500070300040024141555402013800207612084003030f114042d043c503024104034121080580c64201103150384d00c0c001341e45102041c40800114421940c15400940070b01404014491121602e0b0001c500a51500e02100c00b180a5180925028400c0310406242c0f44002c00044c1d40903042c613001b5210301d02d840da40040c1408076031b03103400311031001d03400400c0724010280e031103c01c519402c08044400b44c0000c6c070051001d4600120f03464601c8070003a000001d80908801008100302d8294007641d088040a401458a401c1484002d003c0c0c0d103428038034003040c120710000114003034141c3c4242c40c1107680595070317006291150709201300c442504c1003800294020001c1c1075400c50321000708242c09002000d1000a4600d424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 912101609 1250 912100359 912100367
    0xd030903080c030112030c05190b06030f01050114040c030e010e03121005011418030a111201020903100c09080105010f050901050f0d03050a0e13020301090b09040c031101030207081801 81
    0x7002c64221250600050042143c031804844006500d810302001078100350600324903100010300c20740d0080714090380340010452241559030064170103034105c070080d03080612203509a0b4024012280c0041001101d00407924041c2c203c080105000c1c01c000811248915205003590302c2c2590040301b903400041d0301c0c8481134503801b2259003c08000c00103403200d8100300000f410f9030790943d000b481101010611404d40d4800d107004ca62030b070360005e089917045059031502d0b00780c081034600040d2242c2c010780166181020103008032880c0c4040100500350003e2121f500c0760003045c11030507410070030100c4480407403108024030441d130280c88030060046a941c5408104081d034401601f10900a28040702803d45a03116402030401d4036615041050325000182001c46011140480c41984515500011000c062003580294180c0306a20403e202041d0000c4c1030041d0705405540041110310081020000300e42c2c046800b000d080f40501d00545018066260603460383c0160612400401d1a10403c080035a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 912102859 1250 912101609 912101611
    0xc15090613061d0111180a081908040e0a0b1903050a0f06140f040203071202010e132309100501030503040605030403030f02030412093206040504140109060e01240306080d03090308 79
    0x11211076a016040820840c1c9030342d0742510207427101c000204241c08000390700003501c010741801c650740740e09480c042105030043c2001c1a00701d0300440e074030101125006c2c00365a480c001d682e00700b40200010f1000d69991108550044d41c02e503900380e0f40b0100c41d207090384051095030003080703600750460031414140101070500c55194040040d914141d100c04005076040000c8425035001210103403600c05141940e800500380c4041000301102800111801221502442a0017a036a100841c1c00c5500c401c800c04045500c01c3c0800f03451039005000400c0106e10480065038001d2003403501244409402d03d011003079030410380741250f2004081c5a05050a03034410085d0008001e600c10511622484da4811000404906001d03440050301c0210384070700742c40743c5084900405000d40100654482106260038098082c000c008101d4200100002c00c9100d000c03055060ba0341ea0300c2104071031051a150000039482060801062548441c070001302d038002030204001c0300d0340744c4c0c8010441c0b104600e001062058 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 912104109 1250 912102859 912102907
    0x3030304051c0f0815120118031d0108130804150905030609010524030a0b0a06031e050c0d11100503070e010504180513080c15090613061d0111 63
    0x1801d01800051030b42d20801054005c4a01c06005041c2084040460381400c1c602e0820b07a41c5600300b4540e000703484513242c811003085010b55130f200000d103000c540d08280d03080040303000d500061521010645c0c15642d06407480a0070300c6008200c2c41c0550328503001010301c1c3c0c0300b1120070104000c40800c1103181414070800d503000780460000c00c90340c94074100740d0702200852000d90300c5001c407440700e060407030f1000c000545003541c114035403a5081c0b91017006c00c0041c0c085404100ca00900c5040d41c03004e009028070b0034111441c2c0c80030141103400708000900810900345007065a4580c55420440001d0311190440614018181d50341981c0c1d180030032019011803150845a410010100800c1107180c4100705507011091040801081d941c5a11020040201c14901c000d08a0040010049142440000c81c0303420307944082404d0740603a403101c6900392a1001150203510020144c7c100e400000c82c0340e07100000d0020f07081c2c0031412a00d20742041900b180c81d012680184884001101c60040c01e0300c0c00038444900e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 912105359 1250 912104109 912104117
    0x4020405130320070815090705030d090302010305041505040f030f020a02060706020304080c030c0f01140c19021903030b0f0906031002030714071a010f08120c0c03030304051c 77
    0x1021981e0081121401031110f5810809040c100a04070304207214200c01050402e088814a420b030560440a0003020769001c0581c0c49062400102e508000c07580d500702180742e841c3c03809030928540042d80500720092085418240d20103150252000310f00c2000c0c000d138007038100c0001c040c0d0300703240c0980841e040711840d20942d4400c030311510051361040308440c00d680e17002001503240d85542c50a06224001c3d2103490300e644c04007103404581c0c507a000441e0160007007124000e00029052805054100200ba1500c60f4000820498113103d4010002142d80c00d0119104850a02500380c0c0745070195110381c074003100026129850b894262030850032503030f0320050856080c001c6080100000c5c3c0d0b10781c18406c0450050b1b4001c400202110300600a01000302c0c0c038200402c0e581d036401c3c42c209a0070403040705500301608560740003140c04502b80741c084e0241c5040c080289502800004001d01607000f0002c464080d229207241f4011345d85091002d140528807450040909000bc004204040600d030724580c0100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 912106609 1250 912105359 912105391
    0x30c0d020f070f1b1a0c0f250605040b07032102031005031c0519110601030609060e0c0a05130605120d02100506030c0d050c040e06060109060e090403260c0304020405 73
    0x300002d45d19594549502d118090f9441100200c964109020101c50079602e000d000480300d01ca428660910040b2a090390f00c0c8021030351140742c159000d004038010441c0c20b910521880c0b002038010740380c0308c41c1d1800200e0b504074081921140d1006076403040302e1f000500c122170401040039050030017000d9451403a40c2903903c40752101c500c0c01010350203609940b400756141c408c02580400e029949604da0100d0140031384415603103a040220103042000b03012900c980c81c1c041c1e9400d40c03100103d0f003030700c07803017802000f243c0c58030b1514003000044c1c001c2c5030607000c44943d183d60001d026541c104040c00182c400c0740c09008603001e0450064108240d0005480312281044100640f642d00895a070a04010440d0a10f0b4440c03050f041003071030400404140c58101d0710b0b081c6000310403d0002a03d600c00d0409a841343d000c2c40e110714040b50407144440c1007030341084101c0040b60009009044041004c4140041d8100703507200c0f40c1c2d0090300814203131400203140b6000810301040d030070140289907002101300880400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 912107859 1250 912106609 912106619
    0x60f1d0f06060f010509150403032a02090a02030a0f020414120703030503040237031205070302102406050705010507300f060e06101103030c0d020f070f1b 68
    0x4010f20071081c0d41041000607086002e95605400740d0414007581015645940d05c0b450301030038001c0400304001d007002c0d242c1507860042d05a08929007a980d8054003860f85500e5424910000c0c0d000a0500803e403a2104004030142030f1300c0c0301a200074814400c1c035900d0100c8440620000251412003020340c5d40141e030050000c250001e00b1aa01b1a90560320f40e0400d8080c90044103400117061a02e44c051045070055190140f0032003164810380b4005d40744010003441d00003094805107e844070080250300518010420546c69a01c00398290910030050f143d28071051100008103041500240085131006c5100c03824800f09100755030f40003a80c1d09005941d148021500200382c4202008545403e110410305248280039030405101d9110841062103050f8440980d144102811100719005284d507060301c801c401c0c400ca15401c03040e503c24019501c2c584918007100001d500030600098010b030200801642414801d0007052040d0050074091904081f510f02070785040405559650458130350802481 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 912109109 1250 912107859 912107869
    0x1505040f0806240a050405010b0d0c050c19170307080405070902070816050c120307021e1807210c021c05040b07141009031407030e010c060f1d0f0606 66
    0x208108901c052440c03050020b5001500c03941e080c2d00f1203601b10381442c00015100a014006c1c00c014074510105208107203020404540c103010345980c60015a12500e0004400c2030075100c600c0d0390f40d028910108822200720440d000d45d61003581c07000c0000340312200304000c0c020140196005800352041c10340c81c151264450f001c05001e20140e080ca40502180c050042000c01c019480014001600c06540e04256620054885c1c10102080e400b134403115028100358801600c6403200d00320010300c180c0c0d44030034191031319403840001017130710301440190104050701d0700311241c00d8400320071585004240ba24480b440242406c09001c060a0402c0c501407040782c12070b4004003503130309481420180f030f900c071005801c06503000726103c1b098100d240981070f50003a00c400725400402015000c0d80700c008110b0110207400c002842100c901030300191108080c1ea2840d031240e8070301d04450340581030100e041320741c0441d242c0484038620711491000b0301002c1b4166492600b801000910f40c420400703000702d4500640820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 912110359 1250 912109109 912109141
    0xb010f030c200705010f021609020c100e0615090702060f1f08010509011415010e040e0609011406010c030206010e0a1103010303050901120629041505040f0806 70
    0x100605864034007044a552180d80307201d20981101420b0321815910644403030703c0340c1c514000d0a00080541541d08085400007601d03401c1d1980311041441d03424909030b00d101c0250404024642c10f40103031100681000c2c0540103032502c070454240645aa42403500f0440c0d92003c246203000d000795038410412101c1070700868116884034000100315001e0b5030701c54103440f410081c0220b030b510200c80c0e01008141280158096440354088034020040184103060035266a54201c900032000e030001241d21290b03510520b80c0b041051300290012840c5c01c05c01c101d25081c02000c8581d04502d030356800703160720b41040b0030203411f410400070b00f484800c081c0d058030300944810f0140159030340c0140c030300007181604500c1da00c03035104845808441c54913540c41c2c5c03030020519400600501d000802d2410751090f46040c074800d0380111149140130310480c1d000300c0c1070360501e0642d4803d004e0200c40c0a02001925603082d002d0540b441c4030503550107682e1401d00079141c0f51144180c102c52901d034401d03402c1004160700c142030f030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 912111609 1250 912110359 912110387
    0x60e010c0209040507050a09020c16030f030f050904020301030602030609010509060a05040504050a0c1d01050303040e0609040204110409060e161434060c11030a050705030d1109130b01 81
    0x341c03140c0d443d410024584040d40c0e1080740c00514480d07000413107143c580c0c05031500e0b52490060ba001d003440036115441d55401800090000a4010300f0500024003e8000d544400d01c68108a03017040c2d01400000c00702d0f0000d07070040c0c0303003141c002027007100d68544203c016001d04030441d2075030300c28240307040440d103429400d0280c580940d6840f004503052003020091820001c0d031111060035440c2d280d080c0003c0c11f1000142101c0c6042141c000441d4030328011042c0d900b92010004444010341e40d042c10402400406481660000d0360f03181c03421031195100009101924503400041007692a101903074018410040c6100d072a0020186085580c540c00b488540b6410340320400700342c03911300741d40000c100303030302d00500174012925100702c04034000e582c1d1442c007078640c1d0041d02c0800c541075001e401036503150f010145401e016002000702070749260050019010407801041100d0401d458500004111194844c81c02a88040403403000240c0c0307090040b03c584c0040d400c2c1c05000c0042c89a0002e0302c400c03010400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 912112859 1250 912111609 912111619
    0x902070305070210090807081515010516051f0203060901090c140a2a120f02030c0105090c210312061f0e0a08011119140a080907060e010c02 62
    0x5100500d44510251070741160010b21140c10107443c4500600300e00c01a1042c40024058071000040040011031a180721550000e40e15082c0d07a1581808a041028030b002603051000c20721684100304d0340800b10740099442000240422450850002580361181c080c955401c0d00400801ca03454480355000c0d03046581991010504040c13540c0e055503803901d8606503c500742800300d01c00326030b43d50100d111144011001c803282420301890940d16005014202c02800f0200307103500c0b1003092403103292082e0103c0c41c2031068030b0a08011020a500b520f0095400490b554044072024856240241c1003402000c151840507046041c0d03070304100e440c1e0181c041066103521f19000003418685909240a50b800421030b909903000030289005041c0501071512103024000035080810146414401d070f00d801e48811640c2404c0001042c0c44029842800b02c820381001104152180b8408600000d0001048140c032045554a0030480191600c3c0311b80d440101000402e42d080b21190340c01001c080d91042c2c0582d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 912114109 1250 912112859 912112867
    0x5010515030307020f0d1403030709151707091703031005030c01080a050417212a030a060308310501092904080d0314010807050d03110d11011808040902 67
    0x100181a1351009540644400c005101fa40300429010000303510800a9840d02640140c1380c18410710300c00c4071079503410301180f000150300c40c0381c0501c002034690020582c6032200702107840d8203040700c10041c2810380002d0f950010050152113803405082c680a0b201c00d50041c1001c981c80000240248000381025034550f03900c130b0128051040d00d11910f501c1c0c500348091aa5200318080903c2242c42c0c9002140f440030304420041010005a48101c010500703101c5080c5122903050210301150790300252047c58041c0d910b540000000d021500a0030340703231014440d000d50003007200c6008000982e02254200c1c079020020b0003804203071303001406803003903c1845600383d900c0400d00c258204243c02d483ca0a1461340008140011180400904429511180da0301840800900c0d0400403035513000b809a02c00070b4000d00c0b420f02007820889079044099019207855400c0d24109022141003100c5250200002070000b01c00d104071081c240200f01d014040c80304403250a03031440e101c2d00660302990149013a1960006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 912115359 1250 912114109 912114139
    0xf0a051905041a01081b0f070c0e15360109090b01060302030c0a201209010323040210021507200303070c110a180b03070e0903180a1706040501051503030702 69
    0xc01f41c8024403204000d00b6136030841c90030450741c07240681c841c00a48081540000e030240e54011040300d00c441000d02a280c80c001a100380c020061030300401154400303412070441d02c0100b20348808900819010000213450070042c01d00d800c0c203e105070807103000e26004000344607640700b0b203404480003c141440e084112500c42003038400080110011b41c1200d220300f060013000303000310b4802040c0007042600d04120407040328006031b001042501741c3d901030103888000900941001117031000700052610513a403240e080072038400390041d001d983c01c03000141c10f2041e8140e481098803207202d040e81c00b90001c60035880e008000400ea030140400040100480422801c40754031641e0b900d4028191581c42916030b46c10002440000b0020b000e00507100c2d1113454400141c041ca0303880e1490043c0c0111014518015500d516410715030242610301c0c5d04851300d00b200140c20390f44e20340300c119000d0a42c00a090b0f603003001d08103d42503400c081c0c2806658494042d5016043c0d600008482031075a055403507800c401020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 912116609 1250 912115359 912115411
    0x2040b0a15030501050a06261e1501030510050d030e03010e101a0105070201050a03090c17060a05063003040b03040c030c140901050f0a051905041a0108 67
    0x20750048041419402192514680581026060350415550702d4203207651241c00321107010890344411340c80101500400001d681d483c8209030320034000c01011040c041c0002d0640188039040754091400e030400c0c1d44c4000b8540c0d26025140d084203c424011400b41e0910001484a01c1c48003402010700828403240b1f89130b07840a40155100d03000c4001070f83c8079148210519000380c001c1d04101200604005003150fa20340c0070f00151580d580d01a03480c5810148400004e40003042001400e589078010300c0b100080c0c0c031100890498404003080080e01090400b50b2074001500c0000d003c0e20b11a22110b510312610741d00e0300001e850100003501f905215001e40d0b11450303085110740e80005140b0b00c80041080140800348142004483c4240d6030b80d000c065990800140004203852019030040e0001c0c0100443e11348030792003408408000f40610070203642d40d4005107452600344000742c030340000b0885c20040307840c0070310600b00e6401c2d0a0342c15a826212100000b090740c00b009119101c00c4410301510b080c08900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 912117859 1250 912116609 912116629
    0x150f0a2a02070518010803030f0a06030803130312090302030d0b0105160c03020307060f0c06020702120d180506161e0b0703020d051602070e0622091a04050a02040b 72
    0x503400e268540c180900000945038621401054002c0c050b011269442000d6080143d0485072078402a41c1140c8600d04004061000079081061490b1078040c0032003c224080700442c0220300304003211200340864900500b840c0f000080c004c04031840c1081010100b034020044038030700039400c0300c00240c00d4500030040e00c1070b02856280310034280001d0702c007008000030000c0001c19240200c007200c0042c2c0d0350301030403904800d490740c100c000503180601c0d0b00700040c8981c0103042003520041c02440402a107014003884d061861500400107841c030564000c420000070381520180400f0388000b89045066070514501d1584628001c000300000007880405400096284600716400085000300b0700341071400502a4010b91100e840c658940408a44824074100b042000c065140d00036004480c54810590317101e180081c41280c07c40312071120004070041800e1884500010cc0c040016500920704110440c26200b50ba030f0740710744410000744804a60009942c40d0925411a00401d501c2d2080b0007080c00420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 912119109 1250 912117859 912117911
    0x3070c0506010b090103050c04081525082217030405030f030708061305090a1203020904151d1e0603032107031b0507030e06091908150f0a 61
    0x10500003040c020f52040051402110903a4180721640f1005e01c00c2441d80300318441c00007142d02c00d071601c1d000d95140c3c112156214101024502210300910b038400c12050707aa144980014202c0c004000c2c1030703194059464450410301d48555104036155507a04107010301303510360301d0002501000203810094200100c03132800f12240815500e030304001d000035100d110705903034a9200d00e40519280f850701c0014840c0728404d0610070700400c00030407a5103da070183e0000d400700e039080507001c110111442d192401035102c0c0e8000079110f001010300d00000e902e40e500d080751403094010000c0c000d00c0008000b0035184107100c1d010209034810360300c0c0c900000789144a004905150510540701400c2d480c444c80a50a00c21403140d00d0500c26010351040e80d5614803801e05411011a8043c8210000f1902c02c190501e421100904403d1801c00140d000039402d000321890400b19201c099070a10200400740a0f0050301c00e0400c050309454100302e25103a070f080c40010105030728103640b03140d0307980d90309481d1400c0c0d00090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 912120359 1250 912119109 912119113
    0x7140a0e09040611221a0403060f0b030f0a050f070f151106010e39070201020a140102041e0602030405040f1d010e190b011511031306030b030f070b03070c05 69
    0x30b64192030407800c818040005e90064038404100103285d03d05240d4601003003101c1e00340d00c0d1401d8116a1141c0003415000156070325140d41d48100b2000b51420019030142800070b50091504c00e0305458054640014075541b440380d134102010811180d24650758480642d01184040c10074411000400c41e005518425100840c0c07041d1400007801203203103070f03080e4040e1000300b81c0300d4092440c038102203a0b1030048036420300e000b41d410b0964280700b000b400040d0080b10f01c14815a100c0760b001d5164a100b10840105590069500040401410031031103c514160181ca440c2d5641d040c1ca41000a9103d006510685015646070042c4280030f141c40e900005421541ca01500005003100550314000c0c208114048124031444901016400c11019068081640200b0340f0b1102d80c2403180e01c0d11401031948550b4148a101c84c0690f000e00d00500241c0741000c85e0200d4115521320382030006081c0d445014840340070790010f09a61200c5c11021814205035260040201e41e0380e141e508045612031101c2e24094614 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 912121609 1250 912120359 912120367
    0x1a0a050607150212150d3804210c0308040602033c0703060e061005040e0f041b05060703030507050c030c0102040311151b1501080607140a0e09040611 66
    0x11240071403410780117100394110f222a441600341405114101e080016000d0711401c100e10a00003d100307200500e01d990443c000d610010054000c01c080242a00c040b81c5034045004d03081d0020b1020801d0740a00c9055150100030a62151009889200050005810703c2e800200140200034001514203541c02c8005120b114064001e42c3c0440001951480282e88420640031401380d44c800d0042c0829608020480c141e41d4403250200030648020342554001d1000074000013980c045001d40302c40c8a504001c00ca002280350070f00d8002e421204c0f0740e90710404401e0100041c002d64071044243d541165240c1000501ca860384c14040d2114002d043c051011484005800c110600042d006442140c0c0705020030342200000404201503043c1e84a0140301c00c060038002d49540442d010140d0508840400540d1500a454850400309003c03d8120a019602030b0050240313141d440b020900b141d007900d60510341045100b0900601c000310403a0040c2c41400002c01090030320006a00c03040260075220030040d5a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 912122859 1250 912121609 912121627
    0x10f0f0204210f2003061027090209100807080d080f0403020c0a3f0206030a110304061d0d091a040504020703090e0106020c09060d110d0507091a0a0506071502 70
    0x582403200c07183e070301901031b000201e801c91910644007020358034100760390349403900c122041499072615007201035002a01c80700c0d40b8000d601d0328400c0c00e024462111441d1001814201038030320b000d0f980e40c002062540a001804041581305a00c0341d0820b00c05003000e1515112410704074644444203100e03907400803020100240e11550113001108200801c03820303403100e9114035440c0710343d000501503601c801e1554540ca4001858001c0080d035108418200000d080300714483e00341c0d041c0d001200c0031035040380d644004070100504c500350038555200403002012a1a461840281094060700c501c000918146170031030140040401558094403010b03200719100c10490038024200c020f0b030300c100c4043c0d9130120b00100c1c80920225a801c19600c001c0c0496803140c5030102884015412a8002e1b03810410381c41d00c0048030f6859004c04030f10079001c2c90092400c3c5061000d00011108210a03141e811090728800c1480703034076020040c2d81211000c035030b02a1075010b241401040700d044d615000070034520014600c43d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 912124109 1250 912122859 912122903
    0xa14060f030c07060f0f0e0a1a1e04081c0c17100803030a051b0c120d0b100c0c09090506060906150403200d03200304080f010f0f0204210f 61
    0x12801b01d080000d2200354000c1a00c5074480d01341000c080e0035004801c0294034400300e5502101c0c0c00c01c43c426500034000b00909481a2102c030103440c01c494003080054449030311841d8821447c03118070030302410000d921054001034181c2500413002030140c02c000d80000c0c000000c41070014001c00103681601d1781c03481c0c500a0003000b05400c540b440c1d001e1080078503280315108190165140810340d80010310324034164003100c814a8004e240c291080035100e01c012200d507106c12186080142a0341c5503140001d18615001da1f4581685d086001480c0c40c0107001400309400181c641d1b080310069a0980107611040b0102e820716456140a0b005508002400010403a48901c82040781d000d01142000700ca4030941042010402041c1c05400956441c840c0751820440c0c11144081e11403c1c803c0300d01d01641e4003011428140c050001c404583d5480c405481c2c1001c50380658203809940300c800310f241c60f0500340d0305400440844400042c0131072a030350349000c01402561090015420551654a0a442d40c040d48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 912125359 1250 912124109 912124121
    0x40e01060b07140d080a020c0703140631060902180408030f0906040b0718030209010f0906050307030803011e0b07120f0c12140f0406030b0a14060f030c07060f 70
    0x9400814007440102042030200307000540050345d543c0c440f02a10b40700e180001035080304662103024041c0a8001000500340c8100704000c01220700a0700c650b284c0a0400d409032000d9030071003101038550320710a955003134086880184d070641c4000d00145150b01400843d10602e4442a40c52134501064103001c24042c0030400385d4410940e002840306030b03594254003da10b848003540c000341180411030105640c1d901500d8a500c10030b100a00070300b11107681c2d80000b00450400e9200d4040c1445a01042c01a18400e00411000e49426001405400d2855031840c80502c414802ca10140d6840021000034880c3c2d40724450003002004907280e2580118100001c401c020303040700c2c002140f01284400a154001c2d00c1c07100780144c000d0a8946040c440801c16100030030355141014013050b00300480d403081030003040540050000d41d82d0015a8603004401d01034280700c550050710950340c1c0088008a075641e8003003100d8a4150003d001601c030348035541584602d00440c0da0042409041440c2c41c3c051182c00e038840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 912126609 1250 912125359 912125363
    0xc0c0a1212020102040f03170904110c1603020d0b06150414091f0b030717160207050303030f15060903030d0b15130e090f060f011e050f010e040e01060b07 68
    0x114001e030345507101c10380c00c03840b40d413151a00d0020440000c0010948820b024044140141c00300c5217801e00d040c00042c110307420400301c1c00750305c800803500022920302000b41e4020410310610350000c2504603000109603425012008000406401c00a0030300c2e00e03040820302480c05150010f036100c0b52542c25101344821032401549c0211813003070000d18050442c000d109a05034403180d00f0b071502410030035035802560005042406028848111070214048100740d05c2c842c0390f1030720300c842030404150070090400c4190391040b48a54401d10500c80300c1d180c52081185c000c0241c100801005080c4004034495009503804150315010200c0c165510000b035401c00885180c0888054003c01c82c080242841401950541800030400c4d00c01032002d030510906140c1c10804002c00c8605010f19000c1c450b14103241100d008005010140c010419001e4402d809580c03146440000c1511604001c0400c41400e038045803c0c2c10481131003241d40c0c0d26111940203820480c50107000380001e540300e0101030704d650721228007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 912127859 1250 912126609 912126623
    0xd060e010c0509010c0209150a1e0909050d08060d02060301031b0605040609032a03080a0f050301060e01200d1809050c09130b180412080402150c0c0a12 67
    0x86018428410412640d51000c145c4600410029075028802d000600510070101d4070304806802d901076640c03243d401c000305135205040000003098555198130441943c04201c0e0a414000041c0c001800404c660000c803400c1e00e1f00c00ca0700e503640c10001d1050340351f414010350480e80000c0080113000083c0b4440044114074008120902c0c0d4403202140c1c188194411407001130914a000c0c000145008002d88034000b0b03d000d1075000451030400030801e0a03aa0307104aa01e89400105503494079048032442c00c030f4404600f0020b0466251801c05401c41503030344090340c1002018001d02040d100c1c060000290380102c0c408803030b0440109007026041c41071082c40350400449180000410300b40d03a02810b440b4010701030b10340741010711840500c80103611407161410182d071600b180d840d041c0c6450a288944680c8504943c44a0605080c890610400140510b00f00090b0408000241c0c031200c5480d4001c08000c024503550b4076140741c035541800104040c280d4081c0c000b640c000b0703030030400c200c00040c228000c1308 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 912129109 1250 912127859 912127871
    0xf0604242d1a0102071502010213060302070519020d030e06130303032721110a0b010603050f1e130c030b0f090706140f071a01230f04020c0c0d060e01 66
    0x15910305007002c034146960040c1e014000038803002c0e114501e501200c0001d80005402c000c182da05508041701c8032340100001a901141e54410b010b010400e02c150508074010340b1140b01d00c43c2c0c004c00c2d0310102c00c1d5030140600c0001c102a029030340310b0754101c420404d802c59852620b25201d24001b0041c244000200ba01312000409406051160340254803100754040008880358288449954120318010081000c1c07103d034808600100400b0310112203070070720480c602001981401d00287c112034014110b6050b00304540108081500c040340c01c3c12100e0542d05078481c541c7c0d20035481d6010200c40c030301d00030005012000000208201d00f0480c0340500a0b000b00c00c4500e559004529607581440d114000024071142014407168035540028030f800219111094039242003038039021180a01e1000d0204003904032001040100b1410310000d40c40c080d00030441d0481000000042c048158814070700c3e11481d40043c0b141040b04042002c4c1034000b1020b0030114040900c1c0c10320500038041e00444119950034aa = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 912130359 1250 912129109 912129131
    0x91605070218150f0609030a0210020c12010c0201360804120b04201c03020106152712030509030f0a0b09101103010605071a1006020f0604242d 63
    0x40e2000200087c0043c0710b0707000c60340c080101010790417107900154083c5809201c2c1540340d004450740094000400894454015036000f401c5941d0107a2211115049250b030355503450350a803103103015000d1402103420350112801d00750800e1040e80d01a44050f18001410020400345581086c819070180c241a18044c2200b1001001095140042d5500a00440009404c03103e40c88080c0364090080c400050784076107410030104001514560340000ca00f0700c0c0b050215815070b01003404c0b6a800000720070b000c0c903440c001c0c8404610740b821000606000e004904a080f640301040212400d2510804842da281030394202040628000d540c00b24040c000d03402407102c510410300a1b1400941800c03c21882c50f0310b801c0c02180d0030340051034211100c044520134070108034404010710b8091500c04003035115031460300b00068039207240145500d1b400c0c0c120101300310118200e8a0000b04001c020f805020311161001c480c20020946104c10070a0044a500010000c540142e0070b5200e480103140c041220035610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 912131609 1250 912130359 912130369
    0x39060216050411070305070602091009151812020f131e14010303050a03180305091306080604170705010606030b04060503010b0f01030f2a0905091605070218150f 71
    0x80c3c2801030721034504004840019104000408210303028180c014100591200007589852200c04107a0006a5141060041f45040c0807662100d0405e030070081a0342210070b40f82c11100c0502d00c07881c920b025243c000301c0203546131944800e050001c014001280d15207403414200c003c048a11075801d81a20454128012504920884005000e04c5200b400c0982c40c1d55411140c507808504503c00b0544c0b14100d1340a1851101a002d145901c1b9868407925a80ca03071003805010242c038698060032074209a070402121002295217078015400003a0b143e88911604039040c82486004002861986000700002d5070310340c0755000704403002d000c48e02840385a64900405099460395070400364046941e41c0003507042d41c01381e40580c81100e109640459150b2101c40303502014485003458010404102c0035000e20f15500003a1320018110031108460141051603443c1c03480c0140185c5002400b10000b041d00c19585c1e1340c02c01006401458506651b039140101c05085146d91000d8094092445100c0c520614030f81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 912132859 1250 912131609 912131621
    0x20301080c0a0b0d0902011101050f06040515010912020102160803040305071a1215031005090115030c0306020a0e040614030606010f120216022706030307390602160504 74
    0x10010b242030070b013405a58000000d14a8140407814040c0444192209440c28050a48250090b0360760b102d00e80381440034030083e6500186401103c4c0390300c4c5605052a0b0700071914400f81c445c604140c2151451510042c2d01e40782c030800300b240043e500343c4400a0454400001001941d200b034003500d002c0341d524221401403012401c0006250f80d4180000c010580840210319400f2a81d0541659591260b10106e0309141013211881c2c13081d5221400c02c4007400b000d029042076034568800320311003c0d2840d20f9000205100b8003000303128035000180c039840c0502c108070b01103a004004004000c601d0b51104c0200251810b0000d0310702038021040012100d40c01541c400c900c445940d203c2c0c00c07842182420020082d4001c0100040380c410701602a009620340744d20b08820a81c2400391609181400303550070f40c01c071070000e000511907881088070000041da406c0f1005840d0103120104546400000c09407241080119081580c032000c0c0d5000083c1e1035800a0100284503140f0484d612150701d80f0700707200c103540e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 912134109 1250 912132859 912132869
    0x1e0d15330f11100615031508070303050c101509140105090619081e061b0a080a1d0d0e01030b0d17070c1d09030c061602030d02030109020301080c0a 65
    0x1011041000490700803900d045400c03071100309843c103900701e03018080101c0c2c1d15508a0096072004562184d40a0303094415a56403890485400f9503140ca040c03111a0b50340c02c41d00008007001408138400001c0c4100300b0006817040345c0c0364418461920403503110381d2030b40250310030744d60580c1c144106007111a407004043c0c0d0594802504403002c0355183c0c002e10010064940b0710350580c0304c04000000d0718000c14802c01405001701042903200d1f4110030303038040c502107001d0075458520301e64036811060710000c01c04035110719220b401c2c4001e080c0e03282e8120300c00814882e90003640004d10900c01c4562a0700104201e200103920751140b4295684a4004604907070f940000c0d0f941005c02d542c5c400300811000e034107800703401072140402450805160303a103007075000315a03108150040f80401c101840d00d00b0b09000700d40c001c4008005504000c2e035612947c0c0e03203050140c1240094500074100046a0f0b10901c201c658204018509550302d50303540c011a0000d6209200d1348503103000702441d0315010f24003840241d003150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 912135359 1250 912134109 912134117
    0x30309150c1e11191103070e010509250c060f0b06070b0c190e0301064e050c09010f030308010b090d060609201e0d1533 53
    0x140020740c0c4560b501503540418207004660070440d4800000b00705880080459102c0d07003010fa12a86481e00500324150f00881c802d0f00907010a01c2120040c64400c1d04540045507290b5031610386009a808540c07415041e440c914507084103486115800480804050f8801c89007008281809031084d000c0710300300805194444400c006c4040810031708403a207a0001402c1c6082c1e443e008082823116001491449044c020440024041210385401e00c215402806a02441c9280100d103e44c4808540543d56601106200003031020700f000d0ba28148030901a80b00075a206108010350402c0c41e034441a1f0a17205100c1c60740b1000118440840d010040216581510317450b440da401c1503007041c0b00e41c01121045130060b00306030f40350011640c140501c1c0010700748480002002080285041505424042e05400a4400300b1a17400c011700d42064501c000411a054151140038075071148002e009a02e2840513640000c3e600450a5a06500f03d02070402801800340850510350040f40c060300403140701c0130081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 912136609 1250 912135359 912135377
    0x1806060609040e0c090f01080d05031005190b040b0d0e0307050c06030405190f03021c0519210b01260103030c080904091101020c06070b060402090d0b04030309150c 72
    0x350810360801c126884102003584d20030744400380400d204020031184000900c000c40b00400c11a141401441750900300c03032514070700d54900707620081c102030024410a80980c00d000d110000004000225130b0140c041180c103140d031a50345881604203908200503210f1030343c0c81c160807110000c10000c01c07541c080380d20501030503a9410300400c218040e00020400c0d0303018040c42403101180c3c81800314564480c0d00c941040741114040b0b0400030304d0010101210b82d00d40b4501c505200016802c00162411450b1903038040c6030560300c4c104201d8911700000360340100d182c5802c3d1720031003080030364001100003c02039840e0109071841e6918039280b0306020740d41800d8005c0c0d90005001085c880da8900e0500d501a001c00c034035042401c0081070071039280e100d0170342c2c50b0011100428595031307040c40041114841258142d0400809450b185c0c1030450180c801c2c0d119070790010f4030061540f0b603800050f4085401040c803414916103400d000d0050400c103c0c08413004100d03c1c00b1000e4000c400c0c414404030010740c0e9281218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 912137859 1250 912136609 912136627
    0xf0315021605030c0a03030b040b151c0e010614101407080403140a030809070608010e0a1805010b0f0a0305100e0c060d0e060a0204210f02090f18060606 67
    0x20740c401e901100551880e201c51a000c07501c1000180441000080144407007621414001d080b03c5900ca41e840c403842c20410744148540d100001516010901c500071655a0300300c90000c03030b4541921000c00703409404d04079120001401075110900710740103441c244a2400040c0108a00f0103d8800c0680c041010070b1240020300c08402c0c094403c20780724441e118078281c0c4030b4480c00c1e18a002071940e01c100750b12a0140e10105503002104e42c0d008200c1c44001c0400600b4020042e1405005006041080380d0b408005100c52010390400d00384500c414001c02c4c031071031080c24614040d144800019005a10420440311941449007118046a800c000685101804180c604000c1c120009e94942c081c400d0520710b100035035a070002804034405181d03001034050301d0b48440c3c2e403e003200200b1043d001031040c03104010103440d00605440c3d030003100c2d45115568441d0b01d00030315680780089000c0d4106444d01c00700810711f8103200400d4080c20784420b03201041040040c449a030360b0800c0b10078642080c424014040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 912139109 1250 912137859 912137861
    0x41d060102030a110307151d010b180604200a08010e16030b040b04110c070530031606050a05090f0d050d0b03011a01080709030b16030e060a0509070f0315 68
    0x2006004d1020360b45880a5501c1d070380140d901081c1c405801550303981000c1d04000101014094000c0b41b40020b0040c8074000e00051007161185446104810a86000404555031580b0000e0a0344200507581051a1300200070686034200d00f030180d000c01c0d052800418180c40c008070031361080585410000014108450072405041104c0c2c5142d000340c2c41c2c0d0040c0c2c1d51503590f401140700d18aa00300c000750710307055031900180c941602c640c4004e0085400740008040740410744c56120300120407204140410071a842ca0398510721610001c0c640110104800108010040c2c010340d015280a0400303110a45a0070042500c42c0300118040381c403588070340d00000380740c0e01500140c0015840342d0b90003e026010309020a0a42e658003001980c0d000d0407001e5048a9a00403a2480d00301c040c030b15001c0420760031551800f03c4003901070203201e00000d01e004e5800440e4801c0e04401e2031801a00140c3c0d1103400c0003110600600025200f0500d070b805114804541e5001e6890704c80112500480c0210b05042c64010b502c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 912140359 1250 912139109 912139127
    0xe090c0f13090f14041509020319060507030c110706031505031905060c18010c0f12020a0c290306040605031204060e0a0b09012f03041d060102030a 65
    0x1a100c400d0a00038105001004610000180196080814102c104240d100d085a8011121108840014050001260300b213411000800e81c1c0c0500010404050300000b407a241025030a60102c620a58420013000007542041d03002d1001c0e070702c051080e010242c0c010341c0d4262a51b0320072003190340842d1040102134442d410140c180c0403e406030084260301d490109040c50045099801c181c03d03200c100c1400c2082c2040210380c00310004888500300001c030401c0314500a45080110b041008400d01d940030b0099000300d01354a1a0701941c0c40917000381070030000e5100c989241090314800040240011700345500ea0b003024160301035040d818807410340f504181c040740d04080d0019400c0b642e2030340042043c1e2000c01900d2120041d05074002e4031603291410007071060403189203990043e24403910421100181d04240c0ea001042402d00c120081d415034804c101e20724034200d8910000e018140d10498409022005209841b0300788070601001d00d040c1c6890a401c04151034490040e4070401c2000d00661042681c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 912141609 1250 912140359 912140377
    0x9062a1e0d1b0f050711010e3f031903020409020417060a0209010e040e0309030a0804090e03071716020406090207140601030b01030b040f081c0b040b06030606090a0e0106031401060e090c 82
    0x450601808440403070800807482d1100b441c52000307802da00d40283d01c00309c1c443c030103c0e11b01303c6002205d8001505035500c9028a007000c0794007551420701d07035642c6406a015a070140c4010f0300c003191110350750480c00c42a4007181c041200c0b00d02910000c2483c08401e402261814001038582d103509040b1201440024404400a0001400306101f40200c0d9070f0180b103c10041c600400703c1544850524a0380801c8420902d000c3c42d6079441007041d0b80004035040c6d081d100c0003025124098680d9a62150f00c90703942641140254807074a094408141102c1650141042a00074400c110341e030f69008000c141c0c1c85500303000140c0140c040e4401000090190305c0da407a4041e2045070002541c542981c0d519889400001041e220700e04291110044810503224030b2440c440e08840038806000d02c100415541e11001c2d0105008020018000e4015200e4110081c0100070241e0b0103041580d41d040001c00030490459421000c1e2381000000030060b105040508803118010200d00d660749540e01e0f044041e0b8452190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 912142859 1250 912141609 912141617
    0x314220323042103020d0e030313030309090b01320708120f0a1b031a09010927031403181509062a1e0d1b0f05071101 52
    0x82444400465041900ca1040800c0c62601c443c10701c501d030b680604641104022119641e044500440e6000a41360989612070510052031264800401d08602c54982100c4d00d00c1c00d00e1000004150b07020413050112005840204010030344440110342105082401403509114071041410309600c00b0201c14202004c00d082c0703403400c5440d58501d00325400014120340c40e04038242c1004803480700c4898481e40007480c0801046107081e80030310301c4114001c1001d0741c410180d4601c45480d0820098000c0c2001c5000100704040380e44c0c0d1045171001900c02d40896035102203403160380c3c01d042c00d0940c10b841409645521818400100c0c40583e00503600300410307100030701600042c0c40e00e4a0f042400001007420745051402000e02d810312846d8600b25001c0d00d6941d0141d0815424800c500c0c080c2a005890702c01c02911039640c0306080034404003c90325a41e480707011180041e8480c00118580c2c002c00a403046284030191500030020f00b69403441441c111100400c0f01005440d00245003064200415441410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 912144109 1250 912142859 912142877
    0xa020304031707020f04020a0203120603032b0606140a08040f060207030c14030405010c0b04020307090606020d090b03010f0303030f0e030a021006050301110a050d0204050d03050a03142203 83
    0x880c0d08800c500891002c5101000180c08025410f200051208100040c1c1e420342c034000c1400802940d80c403511034005288504600424500c0d9401d104130342c2d40140e02151803604000c4c41300300d19001c00c004000c44408a25005001491600401c210080f683d44000080d007005295181900e07031100084c0100c0d40309403d10196030014103a8406001107500a6403030004042a07444d100a507a03417500c1c214481366000780810812603a101b5010410079034014514034140d19203101192400c070003508000b119a080c1413010402d03550008d0320130301d44152640c404050302d5440340c82e10a240320a00840300310b4450103105001083c040d80040d00444484a4009031602c030308401c25043d5004142800c0040e000200c0c42c1c41c900c4130600618002e09405c4008101c41820700a9141d4180b06020100b42407040101d040e050143c050760581c4c000b4900688401070080c0145802441c60344000000c40c04039240c403084c0c20795a9080706001e071168200006071803003900c0492498100303440080d411401c0080d904 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 912145359 1250 912144109 912144113
    0x31c02010e0a1a100e15012f10060f06050a021539030406051e090303010f0e070c15020c03161205120a0c17040f1b030203120a02030403 60
    0x461104180920b10030f0b01c103940c0c4008541008140608215808a40e9134002d00500152049150b004440052126400141000143d60204068070292001c86000600008400c803078180325500c1f00420065440001402c11848100c3c0d4050044400c40e42d16907406001640c090b400030140c401d51401210400c41e4190040450658110741402c825401c0e08007191080c0030411a0004080b6030200e8030420a005005540315400003c00c0a01741e9a215008100d2400c034644510000d040c64903c1204d041c43c0049400f80c1d6548280706049080f01307055000590040b558030624090304080c1d81b0050b1004040d00e988607003010807601354001a0342041744461800701000103240c0020395a503400e1084907a4100380b82c0c0c5813201041e45c418010100641d240780400c2298103980480d4020f40015101845c0100710b800d6134031004120b01500322242031105010001070708140320703440380d0400000c03100a0340b80d001840b000d0f440000d42562155030310b40d44101c1c245000d001c201c0e506104603410660f407a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 912146609 1250 912145359 912145363
    0x140702040c030605031c0203190917070305060a021614120408010506040b04090507030803190203090334020d060e031c0f0b0f0f010c0212030d05010f05031c02010e 72
    0xc04070700100790b4030b0400b0071003402c06222202040d0301c4421065400303882c6181c0a501ca2103028031580007040030301342240c0028041c003410405031035104c85207818030741288001541c4842c02d0006440500c02e001c009082e19600c0c1c000c035100c25010294902290b0266581c0282e4194544410541406600d041d001c110040c1c2d4042e0005294410010400d42801d0b4140022903100401d16806a4100807440000c540c2c00100c000440750301c0a08036a80383d840c41803916480802c1c81807010858000400e000e0000c0c0c0001c05840c0c964042100c8101c000d020891250014540c4401e101458071035030419009880d110303440008850003044007003032480711500500d0441d8070036003884400d40c40d400b40310300880103684600120f46caa908410002101d035000014468400200031911403249900b0b4440780c0d911a01d540c5540560180100f0181d0004803e20340c1c50707401022080100c3c900d0200001100c0f41c0085172001140d4014026000420000c0c1340509940600c59852080d503481da002e21800030f40c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 912147859 1250 912146609 912146621
    0x140a0e060f101706030a080f07030c02040903030c0e090907090f06031b06020609010b0d2301050a050114040513060903140301030c030614040507060f0201270b0906040807020114070204 81
    0x110f5039207a002e2821070310711400d40c2002a007501d0083e4090807881e00020701940440b4400101e0fa10700365151034251030120b07819010807070b009401c1420300010408058268100100480c40c0d500c805150710805020b01581c44800c448a040c0ca030310043e01000b0700d0026900401d208103214078081100b41c0c582e05c1d40005903450f0b80f941c10f054200b4010402c591036050001581084299000317000441e05400003860600c003000000e400080f911518040c580f4038004044400c0305000003d0001c1c1c42c16000c9940100001d1003072251031810711401c0b000d41c0c98030f4411503209040301c010080c5000a0381d1645001080c18001c11801d02c29100c4425810082500280d4002c41c800d503401481c05082d0714050b41560041105058050903e6080c003000900124a902c184c0e0180d20304003403074005005040740076000203200d0b941e4030341406810308142c0d46820181ca042a000d0705088003262140b003112072780c0300c80484016149040501482c00198896005648e602000ac4402c0d410210b55800050403140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 912149109 1250 912147859 912147889
    0x30304080303090d05070507143d030e2a06030412090e040b060d0606090c05040302030d020a0206030f040f1a040b01060f0f031503050f0d0306140a0e060f 68
    0x1c004003c00101d48010805070000d100d40f444d02d80c0c14541c0740d580b215900d0350039001e80f810020b42c9404240013034031850041a0001000040041c140d10900340540e20000784601243d217403480000e1200e4898024010031803501f1240c0c000b003203106404801c201c0d4003c1e840e0141903604c0c1003800c0d20602545c0700300103513011740d0080c000e4043c090030300b10010308600b42c0c943c840140c0c5481e6404100204110112846c0e0083e000d8a0710b4079002100d1034008000c0071940c015507030300f03468420b04003a82580a0040c1003924400d404a881411355000c041c3e0355100458030003540304204200282469141e544001c0c3c1007031040c28401c001590381c2d0f542201200003031a6000c5030034031410800c4140f24030541072500404032428221010a090400100000e004230340b084141921609103580d000c6607810008010742d040300582c4c02c041200046a62903a00c0c0a80c5500002d04018000c940004400c0344192205002480610b0a0b45010760b140303101d010003030409a110103085104040d41e00c452520440c119 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 912150359 1250 912149109 912149113
    0x30160c0303020303011409190b03010902040c0c02090c190c030e0a090e3009030a0b01030501020a110309060430141e030703180b040b04050432100503030408 69
    0x50305004010142502000003180b00c0c0c41c074071f024801da41d251081000030314001030300c01003104c035024000b2901400f800d0100a4010345032650740b401c21a400014a07621070310840e000741107502da1018602041c0a000413545012108001741818a40103901207802d140c031a0422031031840784540003c01c00a8a5444080e25546641c14520301c80800d00020080080c2020807a00c2d00403100c0100841901051904000c2a40050b02c06100e0381e08001e128051580310303500020542c1c613860f0441c041e40165000101003020241021110000070050780c95001c406040c090505160003004403800c11448a0b209064060041d241400d00315070340224006030242c0e07014400e0120740035040e4502184800214403405104034034403204080401158440b940500e07001c2504c21040d40d0380c10181d0102da0241c0d000c510005000a620344d0b5a01c003500881d801200c013000107071844004c1c5901150a05070160f18051410007209040c0304c0c15054039040803010485048094552010a00c5d540c40703500001195 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 912151609 1250 912150359 912150361
    0x120703060623030d0206060f0a09090609050609060c0306010807050d230717041709130609051308030a0c05041805100906050616030e180402010230160c0303020303 72
    0x361941501802c0d001400d5000380640039895500944402014159070b01c02e403000750b244c0b8010355a1140c554040d0203820b1040160805516000004140204085400d07010b81400202c60001c04111140714a410080440c907503528400119150a801072031207003800020300085460100034400c2c48280b81c8003c1003900c01c071115400005003000300a19030403c000b003100d003466440300c0d00f104164021750300401c2814400307004411444c10307025400c3d04a07000b8624240031603142ca129044001200d010741010007003074840244010410120480140411000308041504c895044d4000d40d0b9088540c0707041d0b42450b0312480b015a001803002c0c01000d50350b80340d0040c4908016060101c80c000c4c107071014200042854403001c11020f0203241c0314124071111004007207003418000c0710002d4000c0b4005060541e040c2c10f086d0b00c40d01c055800d541c01da00501c034201da003140a0304040e03889030003c0041e24044000c2e4049402d4091150b0001812500940b240f510040016070100403a9018501c25009191a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 912152859 1250 912151609 912151649
    0x31701031b140d1b0509040305030a060801060501350c120a2a0c0b040b0403020f0109050c150409060f1505040b0d020304020409170d14060a051207030606 68
    0x41c40c000d076002035149280480700070000c1e0380c035202031602c80b5a020083e824400e030701484041040e0b4003a80a5a0840c426400f08030415a0010003148070351202c100401100391071b40109400c03642103004140c081140d4a0802c5218881018560050800210400c844040846a01d00409818bc0f40219051004200e2041c0901d400c800c1d942c1c13182101d08200300d100c488001b0407000c00701c0030103640841601da4545281d40761150b5108075100d0f80240151159050514000007103d02c111020340c0180a894103030450b2200c18001c5001c02d940000080107000308030402c202540c410000315050a041c100310010b40c2c0401c5018160080181d1002d9410880c41d0115291883e030b200d034002020418100b00c00e2201c15030203019a82480d40903240140c0340c1c4d549202280003080c401c8030280243c1c524034100000c035801c1100500702007215100c02e0290443e6048601c0700c04c401580c0c1150321141c200c4050115092210400c07060130039020840751419036a8031481e0446106030440783c0ca4080d0360881c462 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 912154109 1250 912152859 912152903
    0x3020d02010e0a02030703140f010e070e1e0a02030603030412060203010f0e010806040b060a09090c091d0c061e0415180303270b0c010203270703080703170103 70
    0x42050b030803002501125402e0350000f40ca80c41640401003c540c2c0c5580b00f028014410030500035071040c036400070001d1440a03220f069441542e0322403540300b0000c601c0001c0b034601210207c0d2103802d10800c482401501c3d041e0040c0065040180500d4240c402803000003001c41220f010700220a001c0e0701d00603030b00c0d4105007643c0800c1559420024030038122000401404000240b081c1c1c0c1702d0342203c2a003040791036040c001446a0750580c00030440c42d04129148062014802840c411529050401c20000b2124119003903884085040a4015000190300b001e41c0d007000e4008018208075146812000c4024441c2002c042d045130700b083c1300340e841450140e07144c00d40040b001040040b4401e80b00c1103142c61544c00031703c41148001800303080089001c40c0880380f40100c5d4101d001d4446905e045868400e000b6107103000303402c11a411440e420b00311019403100410044d038040f01940010184c0405811900d07000502c0d4010351049040040220f0307001c0042c5440c0769500c0c040d42c4034074942004482e503501100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 912155359 1250 912154109 912154121
    0x207081305060702060d0b010c120314010e060604050420120103060b030c090103020d0212030318100b030d1b08030403080103051e0705150d0c0c0c121505090c040903020d0201 77
    0x6401410104610005a0317030300001e440700c001d0b00c4180455a290540e004031076030220808000c01c0441000f00d810140785d0150000714903d02c0070408444503a80c0c1c2c03070f90182c03886030030f075140c1e50014400c000a010a0819400c42d40b03030504801100b10451040150784003065010a4a03840424201360041c0108440b1340118075181c80100c00074082c403a0240e0000c0c102c201d06200007841041c603000540708648504c442d040b41e290024050b00e0311b1b494480b145950038a1400950141c5028540e0320700c8810789c0301c0c425144801809001480d418036846d9099501e415821401c4d91016810441e0030300040c3c603140214801c80c42642c801105524514060385400c120a500e074042c2800008454580240098490100c6504550f02c17011041a891401d10503c19944840e840034200142640e009403c414111500d900c9814001c3c41c090b900c020400e0541c400d00c000510b046a42c0218030246613035504444d40050003407040d5482c0b0840c80300018120344403190f045001da0042c410540385aa020b00c202 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 912156609 1250 912155359 912155369
    0x4091104150c03080a0908030109020901120504030509030705120307110114070302070905010b1905090d1a10080304140906061219060803040608011205030c070e0108070b2502040e0102070813 84
    0x5006c083d241d6941c030b09160005000350a11194042621200d5a109040402d01c00c49442003c2045091900340208244e0100507414040d00c24140c1c00140c6080890307001c0d8808010344091810504103543e500d00c40e40da401da0361410011211010307081e50b90003030010800e080c400c6c0c0040370554501100c0380d050300da0507031007660207031f10520183c4440e541c00c54401c4682c0e125482c002d95510728903400a03600c5400c440f8003421518051045000d2041c40c08501c0340559505192008440da4402c5156900e2046025413034000700c0100114500d400e100d0380d403980001c4010200e500b0440401c281d840042d00c212404040c5c601c82c03400004511400d84120406000c21102841c5400c7c2007440c060141c03101072065815031082c1c031a4038801c2c880d0a0041d5202441d2441c152200c0e143d41d18040003409a0a0260462601541c2c10004030713030140d101110094980145c0300039070602150b44151254004941c1680c00948032801240c0840c0c0a100411400d4800e21280351204c07510252100041050b400c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 912157859 1250 912156609 912156611
    0x30f030f060603130b06010504090204080105100b190e010e060307030b04060f050105070f020a1205030a0806030a1713030611041707270204090606030e2104091104150c03080a 77
    0x1072010400d2404205203003d60884c0005c80540c4902c00103c42d07030312035a803158902d80d20101e4041071403141900824000c40407400754034040b5444510360f00040c4141c8640003000700c110f140e5460586e004803041d10209805040504218100034007040301c0b42e1088035290002a0b540b03080b552540703800c0c8902009044040c0026180509060001c3d0142c07080700409030403e04a200321b00b08554075604100054409a0010b10320b0f0b105924207584d4a800a100a20105046000081040c140003800c1c0d801c06070403003402d202c3e0044160385200320b03910a40e4040140b5030031020100c040381d16401040c1c02c5041d083d280310750b80c0d071418042c045054001c981c00000c5400c400c804201032005100f409814895641d20720644482c42011140240701d0b983c40344003e50700300300303001602e0303038142e80007140e41201c01043d1030100c2d0050000141c498040404992034880502040c04000c0e20755000801080401050504e425200e0f08420b00101d02ca048410000f52414a55010035a0004603da0440c0e12910 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 912159109 1250 912157859 912157861
    0x1b01090b0f040b0f190f180609120509030703110607020a06210e1e03070b0a05011805090a1e020301090f1b1a0f040509040c030b1b030612070305030f030f060603 71
    0x200d02042440020500c02c000d4550308681c0c104006c5901411100e0b245a00249840d00c031842c0803400b034008a0710503546a502d42903600840f5002d00d0403546100c8005025049007401c40e51204001140d40c9601c81d00824244010710050301c840844c240900166281c0028002e0390b1301c405604007a603003089030030840c01c01c18082a89940090140d4008600910180b02c00200709241c0d4518090807802401c14040d242c20700102c803040741c2c00241a50302ca84101c2e82c1202c2c200d4034440680b007083d600c3c040340785c0c0a0f07415440810f000700000c5d0311a070000740070210a04502d400083c02d484054005076400d030b440412a00400c1001380a031400e1094003d88200f019182803410000b020300c881c90103500020024800d170792004003408036006400024a10680e41c18181042101d4a807540800c80e85041203002141d4102007071039090030880341c007100c000d140d0740d104010310100d0081035955690724810080044001a018009044000c1303500e082291070740341c40990110003940150002d4010b50f8200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 912160359 1250 912159109 912159121
    0x405090a0308043e1003090203030702040902150d0b0f010903030801151e030e0d080c0414040e07031209091e2c01020406030f02040b1b01090b0f040b0f 67
    0xd40540d82c03283d08090003024044400f0340350400e600e60584d09480d924201030001000e003d03807059000c0e4125081d20b00700404c00c4400b0f410b504039905034502945c1075009200290052515030404040c02e4400b410a40080c808841c0a0406801c003081c48843d0030f4440e940c2c2d541604100400c040122424a0800c2c0050320310307240a09400320600940103800c0000c0060400d02d80201340380e40c0210b54207803628980314212003004004000d2000141c50600503400d2401c0b109100b00155030040d00b5240f8040d241c00c0ca42030034500b0701c030310b40180650429200e208c0743d20f030340d60184060b40065000d550202d82c41e00307600200070038500c1981c010040492502041b907042912540781c401200e0103041c800600441c49c040e4040880394150000c02214020380400c1802c0c86040d00030744210781d01a1000e00800b182d400705d52099000d640210050f42106221003a00203102028041c800200400001160b00c0300b07481d20054000d003110712007917010740c4030240003c21642d561220742c0181e04140c0e01c4880d05000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 912161609 1250 912160359 912160367
    0x3020312181014070605060f040516031e060308091206010e0a05060d051e12180409171303152a18081e03040807030314120906060405090a03 62
    0x4801402e001d00030104001052601400b509400c1150060803203031901e60b1460044060142140e00728094060400082c00c02d0405020b941d009146441c400420542510421001000001c9000000300346048842ca14000c072841500041c0d405221003660b030308020303400d100d44101c072004010400d40c8403100400c003c0312003050040e00000c02010201d43da8a9110010303e0010080c00080c01d5030044005d05030b031030000c89005a007201c008034182d4103848810156130788180603003050018404410036900f0300615055000c94009486010040a2485000c0782d6003984c0d0031500750782c0c16204d4a90802c0c801c0c00311031a00c0301d45442c1c0c0e08074240719400204e03d0136050003070414121603544c0703100c451901c4454003e500002210002c1001d000c5599615403103141d8074503840c89407030358148006000502c0c1910100407503050307031601d07402001941d1441d50112001900f2510341c405114040c05070119100c2964080d60168120100401c064103002c070401c402c4820161005a03141d00070080300d8006508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 912162859 1250 912161609 912161647
    0x503090f1212130506120103030e030f1c0c15060f120809010c110301020f031006090303020703030810051309030e010828020c12180312040b161b03020312 68
    0x5040e845030f01c036082403210703400c000066044194000c0c40407a0185e10010a01000790489002c0d0360781842c40003001c002d050301c0b011000d0852865401540ca544601030383e40c050350300c2e00d0b2981e03d000701e061606522031010b0240000c0d100d041840d1112401c100c00281c40c00144054104240c42950a03480740c2da426490744510441035045c040c4810f00d0000380140e0640c1c0351034403407000d8000d5584141c0280e6001080c0c0c0104c40010b01040d6861012407054071030151002500e5154004142803800c54030169060b0000502e66408018616008107036501c0e20310013a6142070516a02042e0300c1054076000d8528117510001e1410031100b00d08201018024070007083e000c03840c1700c4904030002d141800940291240582048032840740714001004c0c80c19200c002c0ca044d81c240000c9917507200c003000c10581c86840d40c03c181e455403d020321042c00fa4050030030041000c04440d49410b40038080a03a54098802e600000b90028a0741e83e031000c0003541402e01000400c50400d03800d0342e242c0004420700c0d52929007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 912164109 1250 912162859 912162883
    0xf050406090e090106051c0615031a180a08030414010b06030a1e0c09030203161508280e0f1204030b070c060f200901080f070513030503090f12 63
    0x100002c04035880c554294040c801a1401a266001203e50605001c61018821000315441458030172a103080c41c44d50120305e0152544440719038109460032500c0003851001130410115042c100015403861002009420344a5100380c004c69224170f82420701c440d540c4100001e500a60f41043c814000c1c5595050460b07a12040210000980c1d0010420844d004051950380a801034a020542c0e24240e4100084000312803003101144c1030f2030303000d01280d0015501c0b40701b13070707184800c1e000c0041da44c1f0f50060380341d2075012a064401d040702c01c985180e0101310142c011000700d0807076503642e02d032100c1c010217106402c0e0740070f1001c005210710200034110070903600c40c501c000340c424042c100200310044e11510704111000d401000138800a061841d0310b100601150284e0200c040940c25180a04000070f010b030b070040d4005031a80f01c4580d840c228018050b2a009085000300f2208008d80c0c1a030154482d142d501450049008588581c0e4540c18800329440102d94244075030013282104200300700c0028007040707400f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 912165359 1250 912164109 912164129
    0x1b050a020f07080606040c260c092d0a0302240c03130602010b101b150c09051203030f04060225050a0308010512120318010c0c030f05040609 62
    0x2821a51080381454540204100640105980062001d00010b4580c1c0207890032602000a002c2102080ea186014500047d801003102c400341c00c5006041c214056019400c01c5410303180c600140d0000d144400c1440008404039610020001d0060900c5035900c043c0000750758030f0b008181580c00007200c0840c03c5100c0c84498100c45180256405008150380c41c0c001a0700403a602d030f08020319940d000e008203000b90b600561810500081e03510b02040e40380721040c1203455641d010a0900b1080c20140005035007503c04e104924911090240350f40300e51101480c59540300ca50b040e00f09010000c80c070780e0401540070150b00a00900012200495000790003079407040d401607941d070450703160281c50300600c450380c10000f11000420041c0580031440a41c010300c65542e4440903238803001080300b034204041c4031503c0c5510401145968504400045811030315032281c201c0122040000c150035141d40c928150001403e80038808101030700300c01c0820b14dc1b001d9090203410141405001050380089200e00c031030309 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 912166609 1250 912165359 912165367
    0xb06121003020405100312031b050c0f1902040e070303270315050f070306080d05070c0f0f03031d030312061824041505061e070609030f031b05 63
    0xd200e04588540041d50b001d007060004c1d192160100c01203190303602c410307074011103040003211980d0b1182c4214290316841e10501c03d011644c0d6642102c0e00c3d00030304296111072203107880c07080e012902004941520300c02d50311030b00a04481031040c88143e81c1c20b07220b034030000d9000e910148002500040c2281c82c00c03546440324400078024012100e944009a0310281103407245003903c2143c00c1d00358120900c01d01141c3c200c0029602c1d04641202160700b2841502003981059140075080351140009140190181046503503090f01d4059010b41880702c4d91000440c130211020400405802141114101e541d40354103108035540200807a032a0b1280780d2403070000e1071040d40011082e03520310342c0105480c400100030f500585044121005030b124140d440d810070703501540156940e8903041c0140340b41428011020041d403803528050140c2500701c110f56840342024403069800c1900f20a014010050103041c020442c2903040c14090070188441d8040b030304242c20b107a407104d400050b4580503810010203160003991 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 912167859 1250 912166609 912166621
    0xe010509040c0e010303050910080708071d09100503160303091a190306050123120702010b030f0313090b030309242805120c03090703080d02120108010b0612 69
    0x90b90410b4100d030101241103c000300606a10078044e1801d20410344400349403550110040d03503981001c8540d07600188810000424003480f0310202c80c5140c204080e40342c4107400810001c0d80341141240c2048140c021030004000782d29040005240702024954184a202c1c00c40d01c0c020318006107030050f03644d8010b00a044000000d89803007264012900f18940100114002c0300045c0940110300c101760000754045400c00d080341090740c42a1034aa42c400803a440d008046070461034841005001c1000d5540c5d031a08404580c405001c00110790850a014545d130b901d01c1000b01103500e455030055542e26250400d0141161030000c11905845022030721001d1074001700300010000707880d81500b04611100403903a2119034038041700c48415510902d5480400d0018140d003280c59000c3c020f8000c03660190140854102062031000b990480c8016050714841034490700c45001c541c2c8043d01400c541507000070b11141c402084581203001d40700c40310080c0050701503940020348038015030450344840c0c00c1c000f000c642 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 912169109 1250 912167859 912167873
    0x610090e150105190518040b030a03081b04060c060c02010203042003120d06060915021e030d150e2a1615140a0c0801210c090b03160e01050904 63
    0x4c8602044a0300c01100080200300a015400111100c821004481142085440c1c00c0c01000c0a10001074010304003c070ba2601c045800c40b82c050015208003d100300304102210301d0740020005003619484890403282241390580484c0c4502c0304038002c5910602c140300c0091030340e000c488e121481d110008038001c40110f001906000600303440a40c1003000054400c625115600484110f641c142c40d00ca040c2c2c0d594030916903108084024100040e0400744000314503481e040900780d8001c000e201124102500d10b8848001c40714107a8000041048001c8100a482084040d069014100342541c0a442c079840180c00d030000d000b1945442c4480300800c800070301d401c80c101d04407401c42d000581d0f500c1203505403c000c0001c0c00414101c018545800d00054001c031018003900080c0626030340c0d404090fa1915100002d00102820004800008070307441c9001301b45107040200c0a0082d08030006141b0016100301440e0400a4a01c00c000611300700041100800c8030805904503070080e11039190f40d42e170b00c0c13900e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 912170359 1250 912169109 912169117
    0x1e01150f021e100b0d170a111501150519050c010905070f09110c030306040515030105041b05040c05090f040b100f0e0a0e0a0c03060911030610090e150105 68
    0x665071104100304a49805400221000f1800459400300020041e071070178000012840030300580000e00c21003441900e100103500400e042d5103180380419804070115280340c00c0c0820012103100d20b0a081c801840310440081824003034940c01d0500c1d919107603103407500f4030b0903620440000042c08400308541d49220300070740006000503030003020b0f10901178030303503e081c01c54070143e01035520603d00c7c0141b44070050395940e041781c0d06541e4600045040d07585190401c00501030090141036135208808040800392002d0107680e004900c1002c00400a40c0001603200c0741482d10740c0030a02c80d03030900d030102500340d810004031001c4490030b88480340c461070004c02040251042c01c620540100c11450310360071041d0300600e00da074086056542c49420003202d000b0421081481e005018500d58142e0104a101000354030040c4103108038100403c5d0340c1d5452580c60102c1d009040045424180001005114504400c4841340759142d8101688451700340000041891001485d02ea02c030140300b10300445030380c000c0b4151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 912171609 1250 912170359 912170383
    0x60906131d01050906060307030503041e0f03231605010c08070f0507060305010501020d0801050613180e0c1906080415021602040c0c0209070c06020d020a03051e01150f02 75
    0x1c0008100004940c024002151403840601420001c143c45182c013040240840b82c000c8025814241007030403e904910b1030114100c41280c07402800140c80000159801c010b50258400c50b002c10342c0f02d0640d010717048d0091420070311380c0c1264607484050002d5014410a41d0001c0c40c0200c0c1c1c0b03040a103062901c520801a014080700018080a01007100019022083c0c1e00a0b0f034090140d039994000580c1c0e070364280e80200c0c0c00700d44400014802d60074814040c118900740c0e802c1d0b81a030f25903200402e00720621017245903a242502d1300c41041d40303510304010820380c40c00c0545086e0a0700d41118820a0110301e14010801000741c003038049414080c6100e50308104075404c0404643d10b0205d0781a107243c0404550341203000e9402c0223000079a00c0d00800c5003c94454010340203000355540e220f01202c424203a003408646065091005c5403200b0724900c0601503480581c1c60014460030030600317042040342ca80c0074a4070030f00c4000006010224460301c0107500706004c2d0a00f1407010400950030b0381444146440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 912172859 1250 912171609 912171641
    0x20411070b0402150403080712020a060615021203091e030f04150e010c2406030c0b25030f14041d100b0a1b05240406050f06090613 58
    0x4035005010100d1101805a403007140c1100d6892148141e00e4014040c0d807002404000302446900701051080366001b42d12003a03441902c10340c0700d5a568520840350381c0c0d0001903541800c0101102e5039901040480720200710180101c1c1141307001d8811980e12100b120341e116200081581c1000f03034160400c2601c620b10000340f11642c64548170210380d80802d070080c7c45400000c1d450030080020703501511254401c01c0d0050701c4d6101c0c0d2040e40303802e00364584481b140c002a19554040000200d010f5020040241206100555651011110009410442649818180b0740580d5103600094100301119281c2c1e6150505886848030000140c41d140110f030300401c0038811184240c0e80091038084664801d240b140c80004800303858070f038080c0c02c80c0100103080d4045034041404c0580350440a0513602143e00c5881102e011442583d0340703403d201a0f462a80f03655601d0300c070510040025500a1a44c400e401a9208486144c00c4000030548400a08a180a1000111450010b0355240c018003204511802c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 912174109 1250 912172859 912172867
    0xe150103060b12030720310504050c0f030c030a06050a0e030412060c0e1806040f0b031510091b090e13020906030f01020f070606050301140415021306030c110a1e020411 74
    0x807c07000d402d10400d5510206103000c40d0301020b008511845000e507800c00010691038120b442880450340740310031180d030b252203903015100b4142e03004c00898280174410074002c91141400b00c07040c400e8680d0b0015003403040e00103000c1880b00c0740711b400444082c00c0c0c00543c046000b10b442c42c0d00351054607100b0300c0700750021464003030309018000f080c45c1d0718040d000c192010092082030307081180855240b42d00017981904000d010112905240541c5600144480302e0245402e6907040071000301d03815000c040d40f40036562510f00d2121900074a442009050301e501401c407034941480d280441d402212402482081c490001c140d80e5201045400541504040215915419404ea240140d0800e00d02140d106042c841c0c081000c0c101030017008880b002c98045906a601d030390f90f0703074a03030014060280403200b94284405414240c02d260000010700b080d4600040203401480003e0021010000d0005503074410341c0c3c810001891910300038409003603d404065070701c0b0a440090b000c1c2c00d1141c849113102c60041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 912175359 1250 912174109 912174139
    0x30815041815050114010e030c0607030c0c09050106090b181201020d1a03060601030506031006060905090115020a06020c0a15060518280e150103060b12030720 70
    0x240c8040d0203180941040541000d500841009032002401780611051104a4040b581d5009211100550400600b80c403000302e42840403035040e400110080d000180140e030610148290300c1c801c40c018001278001070000d581001c0001d850404144030784210600c3c009048c0e0b090500c1c64001544015005003020651410204114040d4000c00b03010300d0080d1609803045000030020724600501c840150140c2016681c210055000b84001006150180590038414203503d0052107440b001d4517003911091070441c1064284210b40c407050304503154010320100e0750003d00740c0008049000c658403501c09691101c8081000741064200b150042004940e0b11020040ca26a904488150340c2c050310356403030715000c40b0001c0b10b003460705480803c002d0b40ca41240c030500302c0f5400c5010b0b40c600c0c425900452001402c0c41040c1c6400304002c003102080c160000140b081129074000c40c0300103001119840500480071850039202d01c61458001c1c8400c82c00d00c0000c0e00d580c41c03c60700305403d41d070091141d50b40070041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 912176609 1250 912175359 912175391
    0x10f081b07080a0306180b0319140607050d0b0625060e0f0307050f0601060f1b020612070e030c010e0d15051608090a0309050d031709010213080c0d03081504 69
    0x40c0c00f030321b8044214090b015540991510a003849054010010041e201000304840e07580340b403411081c0c2e5060080e1000700c0c24084200a0b86c0d016007940d03540c6566581d59504494201c41c00c81490602c100c1080045422114044c100c442e81e5103890140c8100e82e18141c41c1c0307880188001c2c1d0f80d90519000d0811a400d94407004000740404601590507900343c01d4080c58101d8603400c003406600c0120b444443e40705081031103629581c5c0e0103507441125100ca010190001081e940000381d0700c6c0f43c0c07c03150108000305580c0c4188528480c0005800602d684a03c24001910307030f105884815000e07007100c105d108140460000c0c840c0040b200c0b03120070002418903e10103d140d800d01041030740803610700804562030070000a0f80345051030705951071054442c285030400c4400c00c007901c8260200314000909882c0d0040000c9490301503510700e0001684c030903003000003c0000481e60300c0110280c128032040c031616181d05402b904040c0c0d140c600503c4c6641d404407070080201c014181203070802c0c0340c1004c030b00003c00c1d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 912177859 1250 912176609 912176621
    0x90b01020f062a0f120424050604140c190228020a2313090506100f0605040e0a090f08070b010f050607170f0f1801030506010f081b07080a03 62
    0x24403541e040e0052030000c1025524840c2080c100001075080145a11755110b034540d06400c00e114080241406a03c0c20b58100661100010010501d55071014407449242c40d10170010b00d0b04418800200c40d20f00303070b5080b000900500c0c88514440f6910b071110407229109024000360408000445c1b441c0d0312072200601e190005606081303028508595004c540c4074004440e1820740d9806000f101c0d504010344d0244501d04d4054446c18400036156805c80e800038005000b40361203000d0300024030246030328000568081e4815940410140300d0108418000e006403030142c40e82c410740740840429a61480e181088030300a2699000e003d641012800b1b01c100202c84145038100c9281190a1242c035882c0c404000540c031030804010080c49407c4111041961103402810340a40381c0403455050242e00200c40700994400c2807250360102404110550a68041c8039142d004407080c030340a40041008140900943d0b0080c04001d001000d000302e184112001200301d60320fa03940030601a1711015081c030040e0140c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 912179109 1250 912177859 912177901
    0x30b0406081b0102150103150908270a0308030f0c1c0c0228030f021006030302010b030609071a0d02040302150d05060102030c030d0e030409020a0819090c090b01020f06 74
    0x101090b900040c40d880050340c1c0500c070101c204a280180d1175681c98650b41281c14101c102141e40362090480070400710809883c1c0d6a130321112184140c0303089030000d8010550122440d204000b800d4040c000304000c203040d241d02c03a4040707200e602c040d21004620b012138000c15074030703080da0360710401c6141d101000c940000e250a0000c0c0c003150020200b0961151000071002142841e0072aa641c1010100c0d10a1400c20701100d000d00544403074909600301d5100340ca041da002078001d40e4603040c0341c8200d070804000d002e81c0940100c0181c40c0d4035051000420035010300907100000d0610100e140c500307030241ea40c1260f00659008240e1640200c0040350700c1259000300030713500d080c0780c03414001404a5002004135031407002404061440d1000b001e1700d002c01032074a055482d2281c4030900c0089911520791000b131105914035161034801d8640068056a100c1840e50150704040c24140500c001a0551903e0302c02d83c4c1d2081c3d00400c1448036000102c0c582500c161000e00a03108000c1445410842c2408203415a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912180359 1250 912179109 912179143
    0x612030806090601050702040911030f0f070e01050904120e0405190f0e10020a1701080a0c1a040303080402011b140d020c090a0e0f01020d020a030e0a11040507030b040608 75
    0x941d4079030801c400701008031000c6010900c1004400010b103015031003003021512550b00811070408100110346010203003400c0100716440400d024001402c02c02c07040008081d2096200032a40c1007002140122801030001009462160008501daa0203410408102080903008003c20314080164080816403a0107440103180303446940684016540220254405401c004004902408901a00030740c05611141d0801c029100d02e1380100c2000300b1038070b000b092504003d00344400c281c1403000181c2c0b12607002d0140070b1015060000d16542d400140c604980c1c1504042801e0b644034001a50071a1243c0b50000306d00c1c0304941400c0c10000c80c0000030032801001412070303404041d0f030b03002681d40d6562110506e5100c40c0000000fa40b058684c0c1129521b46010303800e40300008113034110341e42aa0071050b50324160035000300ba2044110703814890080c6c0c10040d200185076240c566165440d1011102042074003581e01c40b40000c42e030340c0c0030740c0000032401d101070410401c2c1d560fa040001e81b02c40c0302c050411954 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912181609 1250 912180359 912180361
    0x390d02160e0f070806032103090610060206040303020d02040b0a090905070509090103120c12020f010513150b240706180c0b03150907080f010b04061d0f0406120308 72
    0x46101e070302058031500d0704a1040686845800382680e85001c01401d003580741c8035107405c2c0f90038030009031a4800f680384038145c1140c480c01c3c0130480f0313400c00e4130003064004295805081003014a60014100390407507010b080c016501d1800e56003207006481241c0055420440000b00d139401e071a8048078000032a080b07a9010411612381039030480b014030400415591140d480b100500c01702c5d201142d46a18151a41054a99030405903560f10901040764004800750300210b2081e10380c01c4083c080d142e44003c100c03060412101440d0713a903000d0f0013004400382d10a80d641e003550203603603110002c00c0345041341020042d000c6d2584003400d0110310f43c452941224200c4c1010301c503e014140085060400320340c06074402c5401410100614042c5d00000c2036090700318540041d140b001d880e110446c074050002d82c1c2c0c07810354520749044102d08011042e4000039030b2800401040010320341c8140034001241080184000b124201c0f40020300300c08107400d55503449441d1a80016001251002040c0401d03c80e132a81011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912182859 1250 912181609 912181619
    0xc060804020a090506031e01060e0f090105060a030f080703031d07030c09060b0a080a091a0114010212041703091e10050405060a140d0507090911390d0216 68
    0x540304160390301d54041d4410742c01041f40b669543e008608400c5110000100195110020000c6000c1910b40c80340302d0701440c09200f501c08081c0540f0358424010380d8645505407455941000381c6546440c040c2c0000c9003c01c4101c100740c0310740c01c004c1c00c005c0700c10704140c84542701e942d10b0f6484d038036148000c0f640760a040f000051540400c1c09000300304c9003400c04450910701441c20a40c0c0d111402051b0300542903a50003d24005500000c0c202c1f40043c40b0542c0d00c009604104074180c60f41c0400e103e96056510110350740100c52441d0044074152411a038400c185c804007000e20500e03500a1030350311030b0302101039280c07001e46a200244203808200c0440780740c0489500300e0b80a482ca032050f8003505801120420505d941c0394020181c0c000800b10008807e45412040c11105007200c500362241400581e0410041200c001c00d40118800c020410310404d190075111a1151055500380800c220110441c144507400740780d25501c40322000034081c0984825401902000b03460704005541e100402030794842c0454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912184109 1250 912182859 912182861
    0xc0d0c18060e0306130c0b0d0f0b06090906100c140d0201180f061509020a03050f060a0f03020906120a050a030807090e070e030c06040602010603060e012003040309030c060804020a09 80
    0xc02e542002d030150a031601c030342c0540351601000d1303070b03090702e2100200d40000f86050300d07071000b4a45260304120005000100b0514082540ea2010303009118040c02c1c444042560b030b0380e07a50640c014000700c9541a6002d072182c4203581a102c0f0303003070142c038000c400200720149402c040307544244004540e000708102c141d107117100705d510b1041d0400501016254641c01c000121340d076000481d0a01c5403d21210400ea440c61010103030390081a045000985071001c0c0700c03034600d000503110f4001008480440006050080060401090707110203842070745204003007503040d00e50344000450000000241c5a01440f03500f4040d03901c1048a404070001004400040c1103d0300c548800003c3c1c0c2c08144e10b4a50680701c207181140c003100710504050707050041780c10b1400d42e941c070078004000910480d00041a090f146042000441e20480b12428180c0d0506820100050507180300d0031310002010602074032034540d418100c0380d525064000500c030f13019042010400b590050105071107140300f100e0702e404641c2c440354040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912185359 1250 912184109 912184127
    0x607080d0c050f070b06031e0f0d030b01020a0f08040308130f0b070c060305190c031d010c0801122627030616050f0a0801060f020a03170c0d0c1806 65
    0x4100f0b080610242c4005802c4c5c004461b044003004044810100303030020601c4814a1003840d4103503980c4017207a00d103040c1c0b10030b02459400041508081000b00749220020b5100c5801a4008000c442213401c00003c000880d800d48000c0e40e00705040c10784407201c843d694003d140d00c5004070305100040402c001560f11300c00d401c90320030070f0744000056107680c0780c104141d01070800980b8100c600c508104401c07545100c01d1207132140368121980c010428181c4100740307181003440904103482590400b020042c0903038000076041e04449007040c41a00b2243c260a10b800369440c01c02868402203c400d1006026001010140c001ca0400c90322258030030301c01058036103005d200e40300041d40541289000070b05910400148540d10345081c14603c1c0f904000b40007009265203d0035500f8013150000d8010b010721075000340a8007500320346000605160419440140003440d103024442e5040050301c00281007074104400351441c00401c454103000c801e10600300075120359043c2413980010a4003400c00225107101e10946 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912186609 1250 912185359 912185377
    0x61303050702060a0203071b060311031003080a0210060803191805040506010c020409050a0b0f04030512040606090906061a070b01090b010203040807060f17071b110607080d0c05 78
    0x10a240021907401d0003c0c03030f000a600d1605500050220301d0106004134a0038402000c01440c10072220300b005000b60444100c0803070280c1840d0280208a5034021030a03801058940069855032203020b980003c900c1e00c0044400b200c00700382810030000d0270241c0000501805940c90002c0d00703242001140484e035002d41da04086a00080303c074810082070920703038806508031038103140c18540341d0619000b20381076409800703045541e40c3c04240e940c0180a000610140c00058402d0254513a0600b61001081801800d003c2c8013640418400b007002c2242503070110005001004051001c40140d003403441c014600d5109440007891810688c0768200280030407506100d510001d072030b1081e4200076640c4024800140c409066110810010504000402a01c001800360390782d00002140c54150040a0750400c020341890118204103029103250400082e82e01d031024043c0701c4d402e030f040a081026841d074164850304d400000008680040c8001070008224400b64a142030140914603135040312144510300b59 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912187859 1250 912186609 912186617
    0xa030219050d030e031b030c06060f01050a140d05010e07090b0a05040b071b240203190c47060a0314070e0a09060506090105032d1b03061303 62
    0x400211540240e01c0038500603d00c10440341480c0c00428541d06c4207054445501131507002086901208200f0400f41d580443c080d55040c55440b4000700181480c041c814401c410701c0030308903494003001c1e954019100d0081d8418810f000030b503521004051181c201b40c95a8000642840d800b0a0380c0e04003404594074600765a55640c6030524125a00c103403600100d03021506811242018007401c059454601d000c1c11600b00100c2c802285007460300058814031601c081950070600106850110448e058000c2c0456428420b034601c0803881c002e251f0a04c44c2c280c2c20080707400e00d400c81403250142c3c02448050a400e40103031030340d0031800041c0030064104840307680c0d0041e2400403d100144e028100407440c415a00e080343c92a41d20f500199018800440341c0d2074403203030b50309a041d091010b40e01800c0e81102c019204100306504000c0400d440e04407041c4489100e40340804007110715142600f141c075901e9600410340340580c0032200c400e2454402c1c0000d0a1082c0b00341c1d00844d9841c981840e08100140c0d054032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912189109 1250 912187859 912187873
    0x5030c0907021e01090f050f0d0c020f01030c1701060e19030b0a020c0a060507080a0506060a020c04230103121707020736090507140607111207080a03021905 69
    0x4070204004040000310f40e82552211703004400180c10401c0f80c1031480c030a00c00b40c50907409803c092890200d03032001c40c1d8100100d000850001d41c60300d5842030800740c0d080c42d002c00d0a07a90752205031500904249420450607100e400059003e5200304094004c030701c11035042010100110800c0c0301ca4826000240c440c040020108541940c198020010b0a107c42c003620001051916200201c80040b10340c0b0011502e481c0c00c0118099591290550050046401d035040008000c0300a5481f1407441c003030760295645071181f82c450140340110140c0703004816114056980c403490804192285540c4007404a1100c40441101103c02c6c24041d00c9a0210350041022628202809800010601489442c0b04440004d1080e500b51504010f0400070025000300707180f0700c903142c03441c0f40110303680c04010000c0000c84a2807440d078400007202c0b400b90b040419412281c0c02d5800050f281d11b4100b2003808148600407000900c4040070680c0b40f907290094080c3c0d038072000c808290a08001c10904010450340100d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912190359 1250 912189109 912189133
    0xb0a02031602010c050d030e0705151819060e0f0f0d0305070c0e01091b09050d0f0204020c0607020604150c140a02120c03042405070f050a1b05030c090702 68
    0x2507429401450001c1c42541030f40c65941c14000c008800d040020b445401d040c4000c90b00700442001030005681d0050b42d548031054260403400f8040640f02a10f5214070b4107601642da030401803a0f91b9a030302c10f0103000c0076510305020f0045680f0313204c01e60040500e55103d42661521802c1c07034070304071005820b40401040d50347c3c00f21003960109004545418803c100800c1060a21604134040d0400a5001074100c1c020700c8103800c0d05501c0b600d003008000c24031400788a540c441c0c486032000d4603448105a113150071280300040213402001d130b0300f44141c82a103042008482d400204240298056041c0e440c6142c1d620700b490060b2902002d4001c0400c21080b00984a031414070300500240700d0a10545034000c44403101e000140d4070110005070160f0000c1001c1c0842c624032031361032000403002154040040d054100c054814080e0010140800300b40c0401c030414041c0612910072429442020403c0c00c80c0001840364007984140101c0e4004c0c800c82c40e000b90340741001c3e00c865001e403c8c55002410528905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912191609 1250 912190359 912190387
    0xe040204120206161e051011091c020405090705090f0603030306101b0c150e034c0c08040f060507030603170d05131a100b07050114010b0a0203 63
    0x1290040130000700391006404224081036088038050380c0182a80d1808036070500c1c41c40c0c5050512804100f03071911070244003421501044a84070001602d0865180d4440320041c250216400030203900a4281020040e1411002c00c80105030360b01203500ca900e43c0c95012603210300400465010344c0540c400c01c0825103620704407055414100b080c1c500022054a410380442402d0800c2d20100c0d41c441ca6140d050008a011a03066011000c5c14903044030780d00040700009035620b0711407a01042200441d403038030b462552151250b0b0802001c200b0800c461030000a85009002041c1c800f04160628000d02c1c1c18006100d10071050142e90003110350b009032241d5803114802070034007400d01000c0c10782c1c0b283c0c0000084c18000c11000090003011138503480d281c500d0000c6090302d8004201503202600c40c2ca02d080080d4001205110000f043c1c4424545035561602142481030b00e500286d820110200c3c880040080542048a024200c1454203400d070340e981111130f80c18006d05000c40e0158005100001c008800c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912192859 1250 912191609 912191617
    0x60506060904090308180102070f0f020a0f060c1502071101031e0606030b10030c05040303080c04050a180f05070e04050406180506011e0f06050a02070f150e040204120206 75
    0x4280ca071400000000140841d0340c40481140811084400c000000401c9940b441d20b04c8080c40003585050200e88e01d210414001e454024a000d40c1d580101d03056443d42c8031158082c2214100442c642030f100c2c10050300114407114211031049000d100141c4d10200c038000d40b16815404000c5c01c40255600340190040d000a02c81003a1824810001403822401406840000c10140e200000c0c107541c02d2042c0104401394007012010703d400d101c0c0c0364080d59802022075007100e825140c1b166040c1c4503a00006418411a807001d64840004a4080b82c503c9413003009010340100300c401040050291031008090f10002c13074101300418103100800c2c2507030030640c01c002e83c058801c50b0009040407440da2542c0c035104002509071041d074040401801222070f40d4214203212003e404200c0c00c054a00004055110024042d000401c100031404070403481c001c21640016145240e40014069110009004001040300d00000010280146459581024821034054030300100020700c1d116101d400f8400701e580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912194109 1250 912192859 912192871
    0x2070f0c091e1a090a0c11060c0301171c1716050a0c0201050405061b0d0305010b27030a080d0c0813020d0213020c0625080f06010c05030c01020a030e070e01030605 72
    0x643c0c41030516850b0303904c1440c2c0e8130034400040c000130700b40c0300f40c540105031458009180920b5489030040c0402c090038901982d0446d00c0524400c134426a0b14120203042000a6009170340851000c1a51254a50041c1844905c0e254075100c2040076600d0f00680030308804501c15103c0460710070400366644620510a81c401a0b0041c1001031030259135001180c150b6004541e049a000103a80c0c108240e20018080c0a00440d182e140030b009a5042512500b424480c2d407070745014070054441182104001e1000d07038400500c000741610f40d201118100202e959000f1503418000d2481c112008a08034003514440c0c2c014190010618900451542880300c0f003514048140c0c2c0c400440034010091000310300003462800b00b031101410316030034080d40d21403000b42c24036451650300d00004092080079a00030344050b0301c121b19081c10455500c0780c800590300c078a003070030014001d07000000320348620b2a0150010403003550a0b690400401410f80300c0c440e120003150060080e5440014010030102e03817181c1000750000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912195359 1250 912194109 912194141
    0x1051b13030b0a1a1008240402030f22170c07080307050f01050a0203040b0a050a020d0e0a12080403051903150608040606170c01080c09030102070f0c091e 68
    0x9500c070307107030b881054404031044030045454a840d5403503958401840a019041a10304d82c0707100748803007009403034240300404081480354a01444108070090503028101440041c1003103540e400e0104080d50f17004012500304a40d800103105101c40d07a20052280004e080e00000c580086a0b1043c280068661148000120300d108141011030400c0080c001002040e10602c0200468034024044a00356080205028140ea1060041002042c566007680ea07002060480c0092165506000d020080c0142c1d4000012549080c600c940c00c03600008811040d01d0040d8202c01c110a50424102c400100c2120b00400058007449202c400e40710030380400c1945c000f581008504480d1802c80c001144015a10440019844600380400d03c0507a10a500c040d04850034500b1003030040040c0c1d244ea941c4c511041604102c0c01c1c400081c0501032030b4054410088008000399601c041b1401c00c0342d03181414110540300004000340000e6440454440c001d035031100941142221003106401e0307002403c403120406003031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912196609 1250 912195359 912195397
    0x8060a0503070f0602010e0d080105221503110d08071e0b07050301090e0d020d0e01140301090516022b020f010e0303190605090c0f16030207051201051b 67
    0x5941d06024032400340800a622451051410100900b5902031070401d00c07082d08030040e504044d5521003507090542e202036074105900400800041403c20307100b10240040c500c5c101d40441035004009451003102d01071007401c45561a82e41c20405c800c516680e00070100d401c20802607000401e4580c041d01341c03803c000700f20f41805001d900c500c049141300f25014400a4000401800403500c948114111300103c84020810800d4038103020b03540b07010080030182030080c4007101a040d82c1c402c0e0001464442c2420f01f898403540d545500502405d810344031380c1c5200890400700d1421500c00036441d01d40005040e6140ea120790141c0c1d20710322046502c0e001c03c00f1030144110150000300309010380c0c1e03414000c41e4011981c0e49012000741c02e440d12018503080845080c1a410400c0b6614120060b030003070701c115602076445240110740b42c05403045200e10a560034001003c1404d16401007000c00498509a4032002c034003815201c2d0600f214002c48a088440020210a82c50b042e5040c02900d4880c103030801c0000c0d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912197859 1250 912196609 912196619
    0x507111b100c0f0602030712230601080c0412080a0e01080c070f1e3503041202160609030203070e09100c0509060c24041a09010209060307030c23040608060a 69
    0x140d0b030040b501040464003a62343c050404100d0300c1805800c80c45c00c5420400040e051132040d0207000301802c410704025144c0007180002805204030f80c010005603c030520f0140585c94a03099580111000c800426a02020380fa403950095040c20311070003014014074507114442d910400c0041000d9010340e02c066251400450001d070f4125110340c481e020340340c0348a85012001a040054450010b6080c8480c100040100201c800038283d0343c005a02c400040c03d17201181c01e08a10380190654505490349440b070300000d10540100d4828103030b9000360151115951540ca80c0d400a040580d0078071010390200100712403042c0d00794410642c0101ea40751007481e080c002000100590000d68869615812864201c010364483d40300d001e04e1221541c2c40482c1500d8903488140403003040400fa95245070801e000100810340a43c125054200010562922414142d4000b4010500580c0280110300c203c001c00070101861009200000d1501840a15160034144120381004001c2e004a4001445810100b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912199109 1250 912197859 912197861
    0x40501030b102301110c0a030807120305011a0702210c0310090b0f07020a06150e090f0607050906070b0906061305060102120912010507111b100c0f06 66
    0x402507001d41c1c41c48841e070500c010001910003080d4003550240c801210b800c0e0710181c1d51486070383c01003003d0034044400300351012520300b402004401c10340d000c44030302c1c008020403200c41e019002da18002c101011000c8e4100e40198121802070181d651031000c980108101428850010a1b0440c800340c0b40c80403485126014503580150a183c41080b6080444100043c3c141002820040031841605002111140e281c403004c1c1000682115100e54609000a19450007000800011a8001ca08001070041c0c0810148407004502440c3c44180e00c003804600001400500380c480b510304800070b0312451316034860170b4800340e00c4000380d240c21032028040713000400e0703204c455035200e040b40e0310280c022854000100a0401c28028854420a00e010184403044e45d000550020f01030180348083c0e0307104002800508002c003d00a0304240d50b0a040401c281e0980c480e002c00541840c2400b01da007038568402042d2174150000c800d1507040315180408124081c4200d1095a00a0042d481600312440300d4172400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912200359 1250 912199109 912199111
    0x6010801060512030720060c030f0310080a121d0a0815060607080a03090206090904050c010f020a170a030612080304020109120510050405013e04120f110405 69
    0x450036551024100024100b00081503070080b04500503626021940e607892201d01d04003a180c00c03a0a0450702216510341b106400c84094800d0310b011a42c46003850064a00c080d44112024940310001030030025200300e0000300c014525500410948400086000458810111040703102001d01388401902950f1161445d041c0a0100100980001001c0c084c03041c0c00d010001e010f207401350340700b04200800301d00c40a0a690000c040c80c500880d0114040c000135445008081b41c4690080301d10f405c2c0410454001820103160500380c8482c611110038142c00d98644d140110041e080c00c2c002c4400e0042a007c3e500100000182403d00044040e11480d46c003012150598088030501d100000b800700f50341c1c21407007007002010b00b0300000140fa0742c070f596119100d076088004461550348a0011a00300301d021340052900f400304c0c0e0301180d04000e46a408504603500982c03003246a08142002c96002c03901300d0b0031a000d0b544460f017030034144806a925410250103048080e1104c0c00040000420303503507540034003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912201609 1250 912200359 912200369
    0xd090c18021806090307090509010b040e0a0201030501050625080c03040b0c06010902091e0406080313090f0207020f010f020319050a0f0e0a061805060406020d02070f14040c050c0601 80
    0x10b86a1903154000c441c080b129140e002d20984007804042e4071035800081d01d42c00e5908000003c907003078881c400750304d0241242c1e4441d01d074490304040b15444449000503221340e056000760707014465a40c1e0fa40900460f0303c0780c07021500c0c0c0401c4009202c0002555408090b220034860b00d03801c1c1ca4069004030150440e0410b8020380302d160350020340000c10000400c4041e001d010194070440c81d00310750100051642485210310340342c0f51611980c0c2c036a190b0300d9038450700c0248186030650b9601d4074024107040010060340200f4807028a00410b80031201814070079500701030f1380600110b101c982060f0054032403a8a8101705c1085200400042e003003c81c8a0350310202801c1d0780d448103515511140405010740110014140400101d078803070703c3d20b60b602e51501c48201d40c450300b04907a00c465003204030740c015012500007a412110008001035a81c2e030000741c800c02100564240c4030040d0b114481b462888815210f0a00c07440f000e00313070640307041ca4030340d1268031107099a0401d185404001d10701c103070601c0026842 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912202859 1250 912201609 912201611
    0xc0105040203071a030721110d1d0c0105250b040c0e0f0f060a09020c03030a0608071a0a030f0c1e030c05072303070615050108010503030d090c18 64
    0x502007141010044040584021381c3d0390383c5400942842c484031804000c01c40001c04c0400074205a4002c118040403110444940341071103420701026240001d0b501841116a020380b52403464170403542d062664503905080c0c2400303080760040c43c0004460303641044903440c2d5204401228075170b07054200c20b41c90320314070320866030305000786042d0030244203e01041d07009008945280d001c101c252071100085560046141c0030070500754840c207000c04c801c5c2070035412040c980c61002803401c010b010b00101a501ca14218801480710988400c40c064541e0380310f1080e504807031020140c0e10f40150351800541144612480c00080300b0a006070328405988030110808085107902040c2010031509640c01356100406040030300200c0c00031100100148100380010300f1281180109814010b25504903600c0c4441e000c04a03078480e6440d04124000f80345090b401a014082208001070039401001414100d070001070146051800680c04d50f0040c1517408004c5030b01c0c030840d101c045803010822840302511600140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912204109 1250 912202859 912202861
    0xe06031b2829091305040516260307080423180612010c09060c15050106020607020d140405120715020a0209011a0712120603061e09020105040909170c0105 68
    0x10055144102c00c0421480508000408003030f20303a055000c18903c4020350005540d512401c0207420641006e0f903036291082000000500c8a000702d0190b00521000e0502e248120590718440c0e40d240704441000f403080c4c1c801e1004001142387e94141a0800c0d00340440a41d5941e807201c0040ca0026204485c81000500724050121605140148011050400f4000c1101c500e815030040c0ca82d405500c17649007081103c014407010040c4215902c2880d41450340280310658482c030000e900d5034011513142c401131299540c0d003500704c1d105000300c524003800e454109103024185014810503106884c0d02000d244152400012a00c139048605011210503a010302140c070320510401c610f81406034031410100c0721807a107085e51482000100d034001c0f540031104809000034141c0c180c0303482100ca07070030000303c030315111000007442201c1d0081403e04c0d440d000002542c0c06000080317800c5803031000020340002c000380418080402c2603400b83c0c076840d000d20180c1d40f8a85001044031706aa115821450380c0da510781c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912205359 1250 912204109 912204149
    0x80d0e010f1a0411090f01121b1106040b0105040c200c12010501080601060509010207080d0e0a0602011509180503070c03140a0f0f031b0308010e06031b28 68
    0x7000342e40c111074101c1d001d21288555500a0005008400303103984540c1010008101d1a80541c0d407601540c0b25100062006180740b10451801c031410550720404506040942030785003401041840c4143e03400218046580d00300300a20000700b480505140070700211801d14402e03120001006000904124002c00040c004101440013840d80c01c8180d440c20f070b051000502041101103407550555084e45002ca4a951000e40101e14098640e48494003501070343c0e0302119840e03485190b400d40b1020666100441c41c2c0c0c1c54a041b0300700d07883d900c40307070508114004060012400c0d6070010035481590800d0000c0f448860f031516800c40e0b111040440302110f60f22003c00c00c01106070010203001031710b80050408140c2036250314011400719080146580a0008130b001058010040c10070030031000003034018100382a1030b018090c80d0080c080c460030501d2200020704079150000b100c1113440780002141c4c0000c40003009001001c80041010400d40ca01c806440190001c50301d4040010500c1d4000350400542072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912206609 1250 912205359 912205391
    0x30c12020310080f010c1205070302250506060108041a0603030c0d02030405190f06081902030702060403020f160527091c02030a1407060e19020312090d080d0e010f 72
    0x504c1c01c420590341000721001000c0d800c00703d07000b00c01800d0840451699101c0701d0480c02072040f190160310180c2150041180c4140d00340c402608140310743c0403581c0984030000155040c1d0001ca900070198080d20340321006031501d00c2e1a507600007034042c04807410542480d80c10380c1000034002c09040184c4c0003080401c03051a00701c608100511080d804101840d003000c29608100103503005030424007000c0c44c0880c00504140a9403600101ca6a104549034240703004001d4440b03909640550052056088801d0903800c04201c0003c0480000c3c00032107110329040078841018801e10f0b43d29152004c03007400001c0d03c40c5542d900f03031041001030013070001d24a28100b48030b41d0ba01c50340c09590031544180a80402c41d50448a0145543c1c541d5280f1610740c8541d160aa01604d03003814500941c4c050421010200c184503c0c6111450b0b100b1400c1d540c08100c000400d61407801350400c40703a44020001045000310759100010031002d00e0310030000c61041243c54000382520013550707115010726900c184045640c81e00e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912207859 1250 912206609 912206623
    0x40e012c10060b0405010c050c03100b0118050f010c05010906050c090312130504020d0906060308041a0f16030c1a0712020307090504020309190507151b03030c1202031008 75
    0x1850410420a0700f0303e00001d0160056004560600124103103040500038200b2285084035001001c48003190705422520300908501d084640c0407035a0b00200020300d103825424001034803405010107a0036071441c2d00440e40290b82640c20b07500755507101746d40000304169006483c441c440c10445141c0e101c0181041c145007180c41150852550f40c00d0005824421103001582e040b0b031802c50b400750711000c40d549103400400390204000c0078149041400410000e0f14406001141c0c0104102031405c0b50400c118011032007000300d11000310008000c039001200b1a101d690011078013a281003011203040781c1d1120500294114000c0103102000200300c0080c1d444100052000700300201903065041045019003d05070782d004003481180c010001509411040061003d82c2008001c41440564a801c4c040d80742c0c031b22409516400c151400c56051024040c02c41c20240e009241c114502102042d10118000c010000360f0310104116021010008031150000c0c600406005101501d0245000d10b05450080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912209109 1250 912207859 912207883
    0xd09080c160e13022106061e4f0609180f03050f0d240f092304030e180c0a0e0d02030a0b011d04020f040e012c 49
    0x190400d00c40c148010800c2904210b0070f0400503200c403160310009042442924070b40180b4000301c0c2c0f0f000030b104c00024405010310303000d4640c6402070000410709401e8108010100c0c1d00030704123840314a80c032103a406041c008040b112200007100c0b050b4240c3c0c900021140c20182100d014091000703095008940f00340401012601c2c0108427031032140290303a040060540010f42481444402001498001c50490380004051000103540c0d220400005004200301400c034048030803003401c03001048405100b010155009150f100b05100e00c0d0030042005001c0c40551001c1e12001c510894140c07441b840217080c003651094584d00f80d284030351b40a000311290901c0700403081c00d041006011b03070030107250115004407070340d0315000010041d01004034125820b0303440001c1d0944107100a01050110405145050b0754000d869400c041004e07000c2c050f860a020b98000c0c1d03100040204034442d03450706038001c610740880323040041a14a5031511380b06403050014990b60b440081600e14807264001807203403500c1c0340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912210359 1250 912209109 912209143
    0x15181c0c030b09150105301e010c0c080d0b0627010806091305070b0a26060102030a080405010b0a081c050f090f0a0e04200f030606060a03020d09080c 66
    0x208007464103130140311040c41043d02a0300c40450f007081000403642001c403c405100c9020103110250000c203a541c50b40300070030400082407070903a01404503043c0694400e140a0f5a107190302606a500c414a0b1984400b8000d9603541d91500c41514030f4480d0f0020f1300c1908104440c1d0194408040304049004089802050401144c0410888035030744c0d64201035040700f8209103100032001245403e9203804c0c0c0c680c20000d14048040307502000158040c4003060800180404403a201c500394110301891982960b055015820a107d010b820034450f00c0c000f03601c0760180c0000b2450250940c0850a22071407034101d040d844e0072601482082c8028500700c85d000f01c0b000d10b080f515200c060b1203800b8650180c84105c5200382e804509041c20340d80d03070071442d6020748041c0c0c601001504151410100040c40e015207264599121440010300d407402015900c540707107024000d00340950f0313a041000015800960b00e001499402d02107100000e00511501c030311030707115459482c2d58050700701e1110300e4110000d181039041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912211609 1250 912210359 912210373
    0x6060a060e2209050a110a17070306090c1806030c060504030b01140d02060c07030204051e0a0c05040b0a11010f091703090a151a15181c0c030b09 64
    0x90349031068207607102e03088121100c0d440c0c24200c09010180080c03460151040c031801c5442d8081c04140807002482c2c8070304680d80c1d45102d80d100c9a4207841030700e01d2842100d0342c01c25801000441d1a84c0c01c041c520a01c40c0001e885410740f51450100b070007002d041c44502650b90307000309100700041c06d00402c0140c005401d2590400746140c2d00e60742101c03014002d4004951200011010703a8495103940e0001c00c5c1d008155640704c9001503041c5990768150b01c8164411420702011800c0383c69049120950700c402d681183c00155541000000500720b40d40c200e038100001000001504411800603080b0414142d50760b006450f11060ba2609680c4c0201040441170324041c0c004000441c1c0741c61004108503400c1c4181c0d120b64601c0000c1f4104955114090a500c400d8071002544440d558404114a645050b802000a1400f003e0100301d40f041150304401400403c07018001900700c2030790200801e070040420703212380c01707401d0040d0040090711000c03203645510314800d004005041c420b869106458030004d00b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912212859 1250 912211609 912211637
    0x5010f080a1205040f031b38090303030112120503040308040b3d0906080a140c04050f0f39040512070503060106020a0807112d01030f480206060a06 65
    0x101ea0181c910601a0b6024502c0810882c4c08c0c601034404400c2d0080c1629141e40c0d4a003070202070103e0108045800f0000180002c1c525402a42528040d0f134259076182425a03c0796134052101c04081c2c000008400c1404c000c41c6095000c220f866521009070402d81e191214801020805a615410500b40ca0303040000501a00c000000d54564090301302114600034040500114103101e07415002e075030020700300010807000d040c81c01d079000d02134011130665030b03200d41ea060baa500140d0090146550f54443c0380c000708a40141c2c51410b280e1424540c811035241035542c6001800900403280c0011554110100801c41898103000d910300500090000d044402e155079104402841138882c0103044041c2121603480035200c83d096060400c440342445058810801c10000c41d02c0c03039548100d800281400c0401c851030b522405a2074981003031604445602544508408a1000031410822030801500303c8152081d102c045070040e8500540143c000c508000e014012a54955080203040c03060500745101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912214109 1250 912212859 912212909
    0x2090103210e15030c13030302010c120902010806040203060402041e0f06020604121b050307050601031104111204020312070c05090a0507021903030e010c1205010f080a1205040f031b 80
    0x64907a40f5100742a90303907a588607203143c40d401280c4101c1017402c0300003004010540c0541c4500102403c0b80c0302e1400c115160000e0340c0c180c0c1c601030300003800250b50801050517405c0070780181d600044018400b50406896425004421078401e1514941b060840010000d401400c801c442c09004140b001d07000e14a00391307c2d20012866046000810030806080040105920f0700b2684102544181900e60303554041c103189549440a010955482e407000e80c041049141030720810800c00c1c0c0c00a201c034201040041e950700348020090007682c1501032661101c1c4060088001025020312900380100c1c014200000c0c400007810041450762030b03501d08018070199640000c0c031192408844a0362200c400300b545400c4001d04080d100340c0030550700381000d201038560000c010a0751050126010071561703070381d214054a41c03c1d80c5e20801e2029009081c2c00c4001c41c5a64046400d00421401c09525195031240c9020f074840e0594815200d0210803121107002d0184410040c1c001c15005041d582c91080180e2114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912215359 1250 912214109 912214129
    0x6140304080d060e09101a0a050d050c3109020609090411030303070504210b0c0711090c0409051302010806060a09090f0510060504061409030a02090103210e 69
    0x2078001c50340032400b8024188250000c0000d400445403100c3d003420143c61496445100031201c0c05200d040900090007000c0500104d2031100c2d0003401d00744424170b0304040c040380c10240103054615009071900d418080d00c5400011011a184034031648090050940f40300f42903900b040d00040b41403d203101c0302c001d603680c0000e480c45810112004003080d10b40e4506041144c07182d14681e501800080200f0072026000000340085801c00391301c0404c500c3e84001c0803409411305800c0245903c4210000c80d016401c0e01001e000301d6841104c02102c0b004101c800501601003c0361042d81070140082c0501032040c4070b00a81d41c20050b1703d4214021700e0403540c00a0500c1c0c0c40103141e00e000b01c1020031a04203844c0b0964900004001411080002000300c2c4568400b82c0821505100d014604250005c1d00306c0c45401120101c801990714050090300700091140943d2040000d070b42d00d4824a1140d074056520010200e000b1072007004100d4081c2a0004401155042c4082c4036040c0803240030a1029600d40400030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912216609 1250 912215359 912215363
    0x11070801050103020612070e030a060209010e12210d2d020903060c0d1103011e060206070906050918131b030b060d0c1d071d0627060a0302120106140304 67
    0x401b0f660398040d000c4944e0812034800d540d2601c68070302d000302800501d5008080e114400c0c0d9402010385188814080350344280b001c0d4074450380c031001c45641001e0b900b40907002540503041c965442e00300110f0145054801c0b10140500c80c0248001400c5080010800c0c1c202d02c02e500841542400b15880019807070b83c0c0b000b040c95403400300001d908000c04080f980b02c100811041000c0d0703622541c42c0e070051440713003040210881c402c0c40c80d440042011800011124032500540e43c4100a840c10007004550360b42003410700c1c13038210224645501a420154500d14032410041c40c1c1a01100580d081011a0300ea0620035040400070041c7e00340f0120310184071040d40700c0740a50744610105202e1030082e07010b10b8264091000b06c44a500310700607031040d00545501901e510380d100c5000b190088812005d40510260080e4001d0007080120000c1401c0e8941541a05628078440f0390b070072241020807041c2e4041a060b00c0025400980441a080d104640340e02400c92442c0c01e84030b003581802c036001030b88005400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912217859 1250 912216609 912216637
    0x6101d0403181206140f04260a0518040b03030706051b0304080711010e0f100201060e010618120807150603150b01030507020d0807120b0907110708010501030206 71
    0x30145801a506090910b641811209410781e89030a0042c1c82481c214003103640345e041035005803507841030885d41401005034600b426007e488917521a002c3e10201d0041a4072490070319161400301d41d409000d0400241c158990590740c10081030a10000b440d050f5484c0c2c0310f2451700450007450b13100081a564003a9004400040380d4884960b0140c0a030600e591004030b02000100f00410810a00094209140304e44024080f40d14480015950a0700b40041c1a0b081240c0340c54800c610701c0d140c029040d201450303000001c4c020b0f0300e8140802c0c0b212026000100891009442000b83e40140c504203001060103091011018240c0e80e1071105a10038a00042c0901d42c040d086025180c2040d0f000d04011503208806524410844c00644041c11904885501180c9030400240c8541c1c00417881030781444d6950380e00105591140c0c41655120031079003000710345960300e64600701c007619006100d81c0201c0c03054840c8581c02c0c2551841034500104c64000c03a40c1641086c00420060301d440c815103120b0700d00101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912219109 1250 912217859 912217861
    0x807090b040b060a052205060729010609060906030905030f03191a0906040b0f010305271c020d0804020f0402070506070305061302070201140c01180501050906101d 72
    0x40103403100342c080c107a02078070002d91092207541210003059241c2409203011401c5901d14425550840103204043e0008000c000c0040001d05900c02c12400c4292a00a1070501202080112242d182600301c00d02068060001340304160308641110300510051034144a00b2802e40e5600740c0303030b020b4a81c2d814480007001c00800c102c5a2030f03031a0103040305d6034580304016440c11114007000c1580c01d1522a07020ba0742d1007000c5003032400e20707000d20300740480080e001c101c42c495268011001000020800040d5440e89210303500c0f0b0340100850051f00c40000c50081010341800c103098982c07561051506000d56000c00ea0900880340c00202007036006404544200c0d25036100b401040c040e02c151800100300d030203800304001c222505540403601541064543e09071400502c81c48004910440038041d02151804c4280304010640700000c01540760200e00115403103001541c001140b10111000f2285179444d4000c11030682010404582e01126100d802140a03150102c641c4036a403020306180710340e4106030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912220359 1250 912219109 912219131
    0xe0c03190c0503030c031801030c021f021e0306041d070605130308030c0304150c2a0b042306061c11060a05040f090b0121091b060206070801080709 65
    0x3001c44010a4081d007500e50791a10840c60765220340c070000c5d0543c40760750300e40b64105036544680305041d64044560018043c0c0c00b120030702101e00b0b1103804090300e0402c1d000c00c40c000d0394046112221040c29040c010250b02c0342048420401031b580a0404034802c0380c0340d40c0500108000001da039030301329001824034075620082c00140e4003100a05030400f6103600400001d11480c881800001e52056015028032042442c0110685099905180000001070031003818098201400c850540010f42101d500380c0d9068240c0d81c81782c80224007201d0546842480c600100100b601c84a031034246042c1d03402c050129441c2681c0003400c00030090300c0a41c061b181c801407420070003500304500c4d180700600410450b114860940020219071242c007521102e00c8801c0b10006003002d444c06909070700ea03030503114190480d4020440940348038841a50266480c1c03038040139404580c9246800400211508600ca4100d05000e0003030f16004000e840c8000704502c0b000101710b90b20700030071120280e608180010500c540c0791 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912221609 1250 912220359 912220373
    0x31802061903021306110c1203030a0213080109050a0b0a0605030d050c010f1d010606020106050603010306110d0207380a0515220c081308130e0a0501090e0c0319 71
    0x1021091a00041c180c40101d282c540050000800c0743c182030890340714528035010712014428010441c0c15543c004c0c2b02140705070159401400e58401d6030301001d5005595403680303600f51444a403054800d070700180500d6060013601d000c0c0c10780c441170014003408440e1504020035502c110203030744181003200200708a0030040080d000341c8100c20030072405202e0303007503120f28170f640300580e00d14000340542c40c00b9800200e0a00600038202154802440542142e20750b031a07140181800310b280300070040e0104005150512984007604086005040c85020349250000031086404017898030701c201c00c903562465081940e40000264040a0024046a0754503480000550b20200d2502664081000020300408940c007040c044891440a1014081480420b1058a0740001078454010400d09844403401091004000b0310a2550440c0801000355079803d00c0300410100750355904c1000d46070401080341d0892400390415811591000d40031300c5074401d00080d80c680300c50042d4002d40b410001300400f40246 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912222859 1250 912221609 912221617
    0xa0e04090f150e010c02010902030703230d030c0306140d030c111215060d080a0c0c05040c030e0d0905060d0b0f1c200a06030f0b0a060c0303180206190302 68
    0x11240c071906800c03041d140d80c0310241082c00e48800c610341c030b0904005d4100740f05008004406802402400301c1506548807080c10301581008041d4141c01d5000700c1602c100204001d52407000c03d0b540c00207003c04070550040660304c15a12054440c6403000e01d100c00c42e520b8444c2c458051780d1600f41501c03240800c0c50b2441002c45a1807146511040308040c51046550120360141701e003c01c0007c03810696245c07000c00841000c00740c0c0c0a0311045003800b040351000d01038001d06c0142800741e404138441381d9031500080d043d10084885034000035100c00254151440800c070410507001da50801e031005c24101004501c16001e0000c0c20b82c5000c0d205c01124440340c0f203e1285c000107103000b40840111030a103040ca4000201218401c94020000c1456032401c400e07102a0b1801ca9900207111903925803a001e012009000700e02100300401da03641c005a506070b5070f45c0415a000b0320b003c1d00d40340e100094070b081c013404451901004201070740411984900698038481141c0f5201d0f010005085c0c0b410040c80101e000307000f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912224109 1250 912222859 912222863
    0x801060c060b28080a0c1e050301180201230d020f040515250210030509010b031507090f030809010c0812012718021c0602030a0f050105060a0e04090f 66
    0x60060000c0b1041c61000004410543d00c1d02c440d01080c81c1ea54140b280d4404d00c2c2e00016003206501c2e8424424103a08100c4880e4030803180281684a9446070b000900f164440120f110b40404e100d2207460455810541c94034610940d80018001c5a04200c0d49680504c51107502040c0b046e4005003044502000200350f50140002034043c101000c841d500d80d101320341c0311003055403000e40d003114000050014040051711403030340070b880b040300c203144502d05a02600e400b620450095403a102050312070f441c00c000c00b04003450300101c016000c0c00d0515018100700d8036900400140401c0303c10510204a81000f2181c040c1001e04c0c2c01c1c3c1c4404001e046c154064024a00e00d401400000c4000003103221001000c40080704400500c02403441500c4420301c11104519009107680341e80104600c091310785421403425001c0700c0c109850300506a540c441e8100d900071505199201c0c0d6410080c1c4400c4410321660340035060961325549000d58000f40607144005880001e032103943c071000d11404201801e48201d160716 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912225359 1250 912224109 912224119
    0x130510031e020307030b091506030402120f10061703070b041b0306021806120a05150402070b010e010b0903120c070b040320040524042304050606010f0801060c060b 72
    0x5119441d002a60042c0e5444001a05000c2440607501d000b0b440e02d80504180a40f44160b00d110383d00b888100d81004000382da0010b00c0e48503903038040606104090143d8ac110000e0000021504c0407201211003035003200c0b000d03100c08003103030b030f01c100d800012a6809034210210030702c50755807481c1401021144508c101241c5230007100000404c065038002d460b00c54a54182940202e202301c09200e02c50003950b0f421900341200f0804560f580c82c40d5400240c00208852107150b0307500e1004041010780c0e201c030380704440c00600c2034010407c607a018500c1c00d02501c0c0304803083d80b5140400c400241d442c80703071054130010003c0005072200300f0b4408000b940000d01001008584a40c1e681c1050f02615032401c0d10f00408454441c01501c07103140c50700c2014481c2842c080c0c07000c1c40740c1076800d00d0910550381b82c2480d5086581c3c0c2c0100d001c0e80c03400900440483d0b51749440380a1614007444d140c0d05180f8040c204c141030106c0c0440c00c03403541da08119000d042d20441d14100383c40110724100714000e46480d46e6010740107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912226609 1250 912225359 912225401
    0xc010e120304060509010b010e010f230d0e030403083709031a0624040308031006110105060d0f080d0c030f0b0d120806120609031e13051003 62
    0x110035420141d441180070b11000c01966803100c0440d401c1c3e8a140200e180011a054150380c1c8540c0039607800e01d41881b151401d0440d0703441d40355000010072140507568005242c003040c0407440b103006000c0c4031004001100614101880e59407140d40b03a0080d0340d0036003d21081a1902c50600104200403d1074407110f01c92589000f40343c44010301101c0460000380c44104d86410741080c80d16902503942d0098030090302c0c0100071007481d1031b0040300c01c0b2501c102e100c2c04801084000003041d44100910702074034090b940d04100500d00b01c00900206418294007105074100000c1184580da01c0340802d032520740101e903040649170149400000d030311a03060f441c00007501e017616000d42c3c05d905500c0911403132406c00c010800c20750f034138003080b000c20b9a641c3c000344080484602100010703c030780002074100c44040c0110120141c186c006d5030806108940901c5e040e0f1001c84e0300c100000681080070030b2041c10075001c601d46070f07030144101504000c500441d40074582c1070708081c000c14426448000501141800c0d13680c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912227859 1250 912226609 912226633
    0x1406060c0a0b1e150906220911010f0212030103080a11010911310f06080a0303020a120908160318030f110301050c1204050304380f0904020c010e 64
    0x41d0029403142d4440f5010300091600c6120706484011040d0007018020103a450408001c003000003038181038060605212040903000090140d98040c0b48580e04410520105100040005000019030b00c110745c03040c00f11140c000100c004583c1940e030000f2074282d4861010348180c40d48103840c0280c07940356280002030018010002081c1404441c102d4034290b40c6042003c02c0c07010200301594241140d403203001c020308090ba040e80043d905004014000c5032940d501c0031900d0400003000400d8001c42d4000880c03149036580440c0c819000c4e5424803041113812281e40300d035032481c0527403000c0d100c000441042d0302017458045c800c11601000e4071680c1015054072868603140300d2400b000e04840050407110309c01c01c50302d018041c9510600b40da030740e100d003001007610751407905404c06402591180030420010030f2007404450600004c2c860f50301c48512090000c811003a1880b240000c0c5c251f02481030121090700b0036030800311085103404490143c0c031200301c11100c1d030040c0300d000c16081c9988180400110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912229109 1250 912227859 912227881
    0x40b0301180c082719030f02010e01051b090103090c0b09130203042a03020307090e102706150e0601110c090610030212090708101406060c0a0b 63
    0x48481c1d1250018401440303400c40503281c002c030654080710410740d50141400c1c1c545004440d5102c442c00e070070444d039100e440014030030080d0b0300d0884280e0000b4075a008018039590240038403070078007440100030400c6282415106440340310203401c800c0380250001d81e4034102e0f8400d800240c2c403540c01503510b60402c2ea507449049929804550001c1c0110715204d040f200701d0f01030340300b500d1049810040440c0030303500801803940380c18a01c5182e00c146068042011001d030300d04104100c00341c12007400004122951001300c40c0b0702030b4510302005150703045c00c000c050f26008905103010002520980c6550f1400b01e454510050300140031403911051403082d00203440a582d5021502880080e259102c040c0482c00c1229100c50742824a40e400c012084045070b46400d0141c030222151185113001170621801041e525180340055403d41c5d295400f440c82881a041c00340030758214030140210030406c032215041d50007a0400011300e02485100302080b1400e0700c1006000b05240a0780c4500d030b000d4039182c0544848 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912230215 1106 912229109 912229139
    0x1302030708120d14060d0b0901020906211003120e0f10020a11101d01021204030b04031e020c0409032a12030c200102040b0301 56
    0x1c0c4001d010300c41c03182c0084034a084142e85851543d0070300140c51403012486903446100d001c4c86940c0e642e04621460195001d6020501a41ca02c101240203000d07a400550300a10009203494406a80c0c00c2125824040740e96980e26030b0711195140d0018503403600008048410094010300014095a6820454003004014001c03108480c4003240000c0149412180960b100300076900800030320210304009600240d4000f4105c110740340b401008c0d4a05249000c0c1e00c2401c1680c094800d03442400a100250391004000380d80360b6981c0383c001a10a41213a00313400142548800d004428900b4121110407a45030340104088080c5504100c010005030300201d05112002d80006200303074171001c078004000083c0304542131060f400d007850102000240c20b40820540b500c441200c1d900c5d002030024175115000007844002c02d1000880d603009105640040388000008400050a01a5000b4031 = true := by decide +kernel

theorem cover : BRFrame.Cov 912050359 912230215 := by
  have h0 := BRFrame.cov_init 912050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912050359 ≤ n) (h2 : n < 912230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
