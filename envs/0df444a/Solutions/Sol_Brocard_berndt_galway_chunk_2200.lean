-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:58:14.006747+00:00
-- url     : https://prove2.me/submissions/fdbf81b7-c5b4-4b8d-bb6d-19234bd6fe74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 395503597 ≤ n < 395683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 395504847 1250 395503597 395503627
    0x301060509010c0602030a0903030b030f071503140a06080d0221070203010e0a0501090302070906050901060c21020d0306050d0b011205190b0615090102150a06120b0103122102 77
    0xd0004004c3d43c400800c11501700c80c40d50103a0380e154001d1740d003080140480c4043c942e448119007604002c3c0e40c40f1715420445115842c4c1d000001c0b00ea5882c01080000364101030344542d000540b40e6040c81a222a8107215921040280842c09100c5100910b2984030280620024560b10a42442c141c04001110400e644013500a2000c80359010111948400b65007055030003022502012001401801000a46506c1c113004074010b50300000c0240703066911b041010384021341d07150030031180911130398400c031068245101b402c810781110b500900011184940c0050803605240c0045100e0000d0503174000c04206e24102e01810b41d02010207550315540241011468400d00304641003421400c2245d840800481c10406401a0010707103c102440c0c20750000700d100c0d07014a42107940182d00c5400500078441c00c8141c4079030086400980000c2441d2500304c0140b021180a0090311090328000c010420404c1c280c0508003050a64900300340255a47d041c035030480e01e1900901042c0e0358000c140c4d8000c10a40c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 395506097 1250 395504847 395504867
    0x50f0711190803151806040203070314160306060207140609030708030301060e0306180312062419020106081915090b04060b0f0f041a0409150c05040308030106050901 73
    0x40300301241015103600c2d14603100c0d44120f50960600c44103618650041c1070480c0c5010401c0748000e002c492a94030041403100030f4100038003810070140c440500e450a00c442d80c4010740914003184030020480c50124000d8240c420950100c0c08542c0300541c10040c94400b00349000d4482d40850b400d0341d5501c440710000703203000e281f60816543c90000000000b54140c0281c81c41c081d4500c15015101e0643d1001e820046186041c101e0040a4104000c01e12803244000040c3d0760010f4014161442ca022001d010002c00c01c2c0e004044401d4040042d841c0e448039071104071403000304c0b46131009000c0c84c0d0501824036101c555111144403d0500103441c8400c1010f821a004092452104104610314190038158420101034030292000762818030a4a0701e418500740d2240341d500064040e4000b42806802c1c400245000c5209070654404807644240c140da4034040e4800044c0640f044140c45c0c03210100800444030500105400e01c4010002000000c4810041e00d044502c81c1c00c0040d140c46a540c0103072403241c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 395507347 1250 395506097 395506123
    0xd02040905010b0a0212071e0f1502120907051f121a09160e060a05250506070207030b04031b0218090c0a050d021507290604050f0711 59
    0x500002240c1e10300c41002500b00f8801503800c58030041480f41588010380326404024000c0230303844011780d8100c442c03a4104c6c03a41611030a40450380010ba5103454902802c0c40350b0f24100160001154843e10701c3c03405900b40c020141c0e2024254032458280010403600140000c59050301d40114008000da02801401100c0301003c0c405000d00701400251986521114920501c140a410085032611079103031464510b0466035100d00c410707207190004021542c1c00c0348070f04608000c020000900310350090080600101e8048040c0d0306044114a8400d09214000317000c81b08551020340200701048001559982140c1c140c1030007500000003400e43e4400003801800690001c4100420403512218051014420051002030781c444901c0b030820000780b0741240c420141d010058021141c058602407003024481205c01030340f035184c40403582c0e480c0110340c041d1503900c042034903031594050200191184594040c1040318200710790b140144011306e02c0ac4000d49150100480c0480e00640040100210302034015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 395508597 1250 395507347 395507351
    0xa0c02031501030c06030f020901020a06021b01231810050703110a08040605070c0512130302122a0315040c05180115020d02070e13020604030605042a0b0d020409 71
    0x30f103c1c20141c4901c00c4500c1241c0001c0d00c1c1401c0c4d41e010791b01500c295240818140d001d07124480040c0c8420010b90031105254108024008108078100800d114000010404062041160f50b4180e8143c0031020700a1642204110f0740d5001c0c614942c02080030400d003031400d4000200c40e00d6034030f400c8004240e41a03084800c2c60000030182c02054001e841c80344194030986040c40300b503403140c0045602e248041c2e401020766111095582050301210083c04103040003001241c8290359035000182c228107240034061264016420401c841d010300751009114003881c10704030108142c10b0010071303030360040c40750003014603d010404101000100c400900003000004c108499500750b03c80008211017080c440c80c01c985210b0300e100c1521900201d00c1012040d820f0b0003918a82e031901450340a040e400420740d4612807408203008006a6517800500003035401511700149615080c544a00c091007100c0310402107411440c0411904823601084100751402c21000c5900c0b070410820301c4001e80150380081c14024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 395509847 1250 395508597 395508599
    0x501080109020f040e04140f010b0d020108181f0b1c080a0c0209070203040e180303071d06040b0d0c0c110f0f0a080d1202070c05120a0c0332030a0c02031501 69
    0x20803000c403640710503012601580d2245000b0103403d403c9800cae03111940e8204030003000035005580030b820610f603c0341c41074140c000c940d000d0700c40f214106055940003060b94039911003410715040641c03150a44c0c2c0c410030354450b41c1c06100c00128034038618042100601c00d49001584242d80d5225002802c20307e03501412180d15410152000f035181c0c3c102e405003100703141c0920001001d919465581010125200014614686a80700221040007400c00e03000d101c8050210404450b84500008000404100743c81e10b031030f601d003002d52000b03881504d0074000410400028900c00b00311018090501d9150454000c1c503541c00c140040360415020302d05281d030001e507100000880c040e0126a1080c8400039942d0050f450010322611000ca01840101824038002401c0511550602525542000c013403103045442d4be005035668500440c050350011107030091009440c00c41d0f58801182002010b00b1090510000b0075004103655981c0683d61404c000c100468004000350b4800780401c408880580141850329 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 395511097 1250 395509847 395509853
    0x1106150d0b0a0501151b060203100e0a090308060d120f170109090302010e06070f030518100b1f020606090c040302030a051f051611010f020d1a03070501080109020f040e04 75
    0x304801d204070444806110542c00506114959040040a160801040c90700250b140e0031f00a40006012241d4191055804104226180c012070710501c041500486d00c5001440d004007e000080c002900030700e200148807001400c0c0281c0a0070340346142c54644200a81c0d680115035503941032404004001d901000031401d28010380252102e680284c000344041460b0b01c1d600d50796598229007940000c0c44000360319144910a80195401406501c6d0589140d1010300320306050114500085400d10f5032400c41040504100c0303031800d04030420590b181c2d42c08050b0a0041d48400c00240030702d220b4102c00300060b0b018200b003003e86008e1038000c1c04507440d2010500c0c1044e0340d1b0300c514500e840f559a860401419805480c003d161086c440c2160010101c41c100070151010440d034001503016540b01c9030001d940103114030282505000880d000304144140c81007000b1401c0140156a000c0c0d00f240c0c2d803c0c000c503600300c0001411100904d10040c1d0380c1c00310011440032800b454004950319106003041c0014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 395512347 1250 395511097 395511101
    0x11b050c0d0f05070501090b030411010309080f070b061009090b040608030c03040e012304090201030b0613030c0e0c041208070203010c09030605103c03120f1106150d0b0a 75
    0xb64410740c200c5040e00d80752001541c0c90301403031180c400381c00f0007003001400103001024a03c03076400042c10701046400391a503607540c650f00078000b00341c128036010594206204c02c40c80300740d40110003a0f0301c9400c80c1049080007001e0403060300883ca021900c0d103000b45040d4585901c80d2000780700b6001543d48070307920104050b4403a4080d20030341301c402c331581001013000c18000a1031000007a406000d8000d80c50820140405004a40800c2e4180b5a80700040155502c4580c0104070038900c80032203442e0a811880c2c400c48103841500200303d5003141c042044800c000307840c1100d040d9516826485800ea90a2038004818441c46030000e405500707241392600915080110881500c3c030801091086a503000302c0c0000451451240504000743d840460149084600c42410740080042d40e5400d008034214103d48142e0590303100719003454500610b18080d5600071181c041607061031a0001d404100040b8441d41d42c3e002402030265613642c5560303044256500402034440c10741c400c00c8224245820205440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 395513597 1250 395512347 395512373
    0x60a1518021c0c021b03150406150e040506040215040b0a03050a0c051801050a05040306060f09051003050d1206030605090d030b01020354011706011b050c0d 69
    0x254420b42c00d000107030b9801c4140a00f4003401400d5004003c3c03800400072030091300004424094140c061481400d510300e0000314030612407405032401260018031200ba04058010950100501c40384800500000a4003c24216000354040302c00c4020320480030000d02c0184501d922182c040103000603185403a0790150800c0e0700c5200e00302c10030010164000000d03102445103503060400b44803c410344103055070040c8094909004503240150402e03880f9030b1487c04640080c2c01248480c4a146010850141a40210b603072001c109103a0700411407031951070075a0b541e840ca06036002d0003032207005100721705901d038483c0c0003c541180701817042d42030903002143c44800385000c50001a00380303451081c40f54000001c6a4081642d01845c268044c500a07040204840c440c03242d02e500300d03001c040b03030452446103440d80c00710b50350030043c96a0700380b1400005091004030a06c000c804800c00810010245c0e04502030402d0b01c00307022040c0b02e0414043c5440c50404000308490381c0c0c0965000f0b81103007031180300d00b4412 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 395514847 1250 395513597 395513617
    0x819020301061a0d05071b0b060307050a03020a03060b130513020906010203040f090905010b04050115030e010515010c020301090c120204050a05013b0408190305040203060a151802 79
    0x304007600e5150b0f66058988090b0601480c40040008032500d00031036000a901c01c1301c03450100c980d605402c0c0d6a40703d03103a1004007034404102900c1070289614040c82668010801181d01c01c88107441d580c0803d40440c40d81c84007400b0659280c10b000f40c9a03c0760300c08002d070001c410100b008989030800c05950b91800c40103043e0700640c0da0303030300040700c40d4000421102a00c0c1c1100c2000c0c206854003402d5405451801c6045600355200d0241a000341c50b2805081e010f0482e4103100746841e402d192005040300d10143e1810402e078104010700800548001e54109904800e181c200c2c102c10280c00864090480c21078010000c658004001504c0b10380701700751664a501c201c8017401640c41e41403001081c3c40c030038050140301c4248251410154000d1010341224845070508002c081c1d1148955203c221004039015140c0003800a80ca4a50040070f1010f500e510700c03181402c0007a070a0640200303944502c0180f0202c140e5607a0b600190390300441207900c100038070943c110382d0fa00401c1c690216001c0d4201d040c0070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 395516097 1250 395514847 395514851
    0x3140f19020a0b0112050f03070b0105011101020403030e090403030b0a0e0a141b0c0a0c060221030423070b030903070209061203030a02030c04050d0f03021b06070b07090819020301 79
    0x411103a803010414120007a0485a002c03816401c004003c41411900e450846131031260640034405d9a1060015204090103002c0300051585000009010b007038900f40050b2059104001c1440042c5e08401c20800c8203000b40c9500346c0c02d80c0d80386000e800403d200070809903c100840e0000840044441c3e045c0e110710032402d01445481c036280840c00d031a200c00e0b00e10083c120809121501152120b001030a01410258101c0f9415007a5072180b0144d03a00300d400c51030061300031002c64184010600346190a40e008a103120340707036103415121070505502d200b140d00d0a442901c1c0c42d44428003801c20035140505a03404a0750350343c1c100105456620f03030142c0c50803800341d101000011500d241a0740c550210f5603136007015500e185d9071408610004d501c02000c1e01d01041c0203101c086280d03210f440c50998000d2040340c00c248450450700f0080d10306050703140e0b242111040c1c0800345030b00752240c20541d03141b030303a2204190002d5100c2d04001d4840341555009180d49104451010001552208140609134000d40013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 395517347 1250 395516097 395516137
    0x1020c0105040b031308070f03170135010f02040602061e091002030a180f050618030a031109030d09301e08030a0e100b0a030f03140f 59
    0x10350760750145104044182e041800051211030010041655092061901d07928151150752080f0580140510a41c000f4484041d1280001c3c90138203034a0240000e407004060300c959000e600b202070030f1428900350b0040400c2d00c218503040403d41203460b07100070854040d52501d4a0f440d00030f40c0e03000c0848850441c10780740902040d0711444030078a28042c4894401030495000041d075407002951015026a50701659810188010300000024000c541c6c410846500b0324885410007034074107400901030800c600c03665070503c255050b00100700c41c3d0001c2c00d0706003c40c811a0201009140340070b40702c038841c0c05000c0e4852000000b940440450142c2d4031380694110717030440075160301e85440c0c172500c181c40031094840116004182800400c1c105d10a004501940e0401c2c80c3d0b40326001d5410945c2c0070170074251224005d55002c5000d21401081000901d42080000c0003240051002c200d80c0c0700140581101520402c1814496203102c601e2907081d05400e41d441c0040325260000703900440d80e54010141d2104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 395518597 1250 395517347 395517349
    0x2040e031305060a141b0a060501030b0601030b1c0c030b100314070b0a0e04020d110d18020d030507080f031501080c07020901030204111b070303030b010908060f060109032001020c 79
    0x2c2c0d90700500c00703030740d1001c3d400c0c0f10744c8400c40c10f46e001100f0702e481e02d5114908520328000801a62a0440c070400002c0340344e51661410310400080070344618107260600c00840304a481d040e80d541108408440b107900c0303114207800c05062000f40d94001902c031f62904010801c061592440b0b52080b03130f00c074111181042038182030f4681c4895490103048070b10b0104200152001d80314010b81d10724070100601c0185031015010784401102c260303000e0304a09010200c1c0d07001510540d0b02c1707140c030700f400c2c540c1c070b024079840456001681c5a120031800070180100840e2480920244101b640c00c21521060b040d076a90410b651003610480085a5860000304807800141d100c841c8081a903590603400780c8200300c03c0c3d0035070342004007400f0441c255002004042c480c201c42c88615441480c824500d07503014248483c21410000e068650800c805810b11030202410040325200003880c81c0d101c854040380d00070f140c8603000120703145103056001505540003030703900f0b10107140b4640246807141003d03000c4921101d5120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 395519847 1250 395518597 395518609
    0x91416120525050d03080106031508060a0c0c0b09060105130e0a0212100614100503160516240507110c010c0203010b0d14070816060e0d02040e031305 66
    0xe00070340280042e0225040780d98042e001e0303011038400c0d003070105885a0226025004000094002820000040144580610036214101aa54a102d086d2400d1405295466001410b5650a2aa1070030581d012522519050703500c0b607801801181039080500f00035544950a000e8107204000e9820b950186000303a101b880003801910000d004000742031303001c0203040031300d41070319801c9806103410b4210f138500d06100b03200c09020b4548024144500a00c10b11117540d0742c0e00c14010a00c0400c1050103c50301a50380c01072280080d51038140c0c0c3e120607019100310107604142c0020100303080f1b40341d980e00d4030701c2007010b00c01d00c40e100a001b0040380d52484001c40d140401c030b054840c1560442081d002080d485203010f0a0000c0c0060008602c3c101c4080c08a1450a6044000e50744012050844c42e2082c40030b000c90001042c0000050145002040805142c0801c51107064280079044100b04401d0b00c84c040c1d9451803d030024010030001c480c14841c10703102c2d8801c140380614085405000702c4c081c50a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 395521097 1250 395519847 395519879
    0x203040609050139150504030512090307060f09051c140a0302130b0703180b0904020c100f051e090709020306060d091104050106080f1603091416 64
    0x15596098001d4605401591010740c0c0388403100035002e15100381800400150901c28403c100214800f510007054100041c2c0ea03d00f802c40d580140703040c001808003284d4050b0603100d051402d05000142501d40703506103840d41c49a008010152401d1105d07241040000341e028000301405030041c2c1c0d05210310f101880398280d000c5107070000442d900b15002d580701540c0c0d10140451541a08005252180000016500100342c6c0c1c0700785100c40c8001040700070982d1040700e444081030340341c00580c40941032195412650180e024414002c0703601007110740c0c03a000100400084040c0060301003016250100c042800703054221468a511921810029101d0340041c017410300c80d2030558041d149850828030510080d6101402941e40721205110000e62510300341b180303c0c1340d18441c001030401c40000400303200c00d03180f050340141c0c24003030500c08010700c502101c0d01c000c1e404180f40005544040c0b10342c40560040000200141203114803100310003074800c0018646419102c10340c0350050316642e95403040420040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 395522347 1250 395521097 395521109
    0x103110f1c05060f010803130b030901020c0f1c0513140d080d050406231330081b1207050f0f18120a06051b03090309130614010c0204020c010207050319020304 70
    0x840c4000704041e080c1c4c94092b58020044100252410b030584d54000e00d843d03051030500d1032680054032910811940c14490360240b03c401d0410301d04000c85d90808100800103442010301f208400d0a401d1859a940e2018004480c0d20171034454136101680102c03001450200c0b01141d050340341850702d2a2040d00310085142c14070180704034140c44c5d030b507007a40d181e10a045c03182c0440d6071416002000340103688007481005440b1039031002c00c2d0411040140102070325806044140d0950140c03818104c100340460490f1050b1481341c140d107805442d04a0102d13402d1203003407540c444100020074144548072005000708145001142100341c20072004080020095807200d01c542264066580080014029040203a002c0410340304008805503449070208180d00468440405810000d04c149951070429100c0300403903459101000540e05001138a5002d01c00306034a281400080c1083c10115912501100c00309403100f0000d5494010f0307803814503980e0b04003500d04519a071b4180e4181601ca4800029982200c0d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 395523597 1250 395522347 395522377
    0x50d0c021c1805030f2803050702060714070b13091a090a09021008041b03050d050f09040204080309010801140a050607030e0306070f0e0301050103110f1c05060f010803 74
    0x41e01c1a0070355071101100d00d40d510342e2804060016242d5404d100c049540407210024000a0b03101c0059034401d150f041511010304295080100b000c01d5010301030f10022a07059850396503410640c200b960045101584080c0f4600ca081008904c0e483c03400c0c003030b150b401111186601040c1d2140725807415192000282008c2c031102c00b13606010b40ca001090241c2101f00d90b480000e134074507c0d80118003030300d00142500f004035502105002c00c002011201c4502907102d0740b074103103070307141940d49040d1034100018a000400901040e003903900d5008a04403200054010070031980c981da200042610307038205022040c003140b5481e0000032136664072b11a1141d460402011640078034101420414190041c4001703500b0007104081440306514104071150044900c0c3e03c0d01c04e400901c4080040c44451040f120f54082d07418030740108002440d14203d401d45403401c640e9806004501c0000c40c0222840d00031074800e070368880ba440020311502146480c002e2100507c1c684c0d16a803189125540c03031141c0328114642903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 395524847 1250 395523597 395523643
    0x100602160e0426040609034107180f0b09090a0f0c03140604020a09110306100c1a07020615010c2604060504081005060a030308040309090606050d0c02 66
    0x265103440e4821110748000541c0040c244203c001483d590042e030000340205820381d205200380403c02600c00040300345000c0342c1103c00c240e1205800d6000b81320f0b42c0381c202164416030315146228188000350103020701101c24240315150207070b07100243c005e01c0d403024800c904d00703055020707181484040c4511075412400180321041103a550382180700302078030007034540500c84000480081e0f0f40040448130501000300902d00c43c1014010070807402e903960310076142c4c64034002c18030444160b071a06807079002d03204450b0004603050b07820003a503c103c0030050042115808400403450704410106090080190740d00b210240e40e03504c419078017019100c0c0501c6000c520b40c0c040c41070004040da800301000b200e285901032508504259034072040c2d0410380040c070110700d0106050020341c0d0b04010380d0580700b11401c4280300703d0030006c0114001d04824000641080f25280000c0c0c103040c010090355000b412881820441541c2d40e000003007954200c4c224440f00c0c85e081101701410f040c0b0015407200141c100c446071038004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 395526097 1250 395524847 395524853
    0x120206010308070b0a11030403200309181024020706020c060f090f06130302030118020f0d05010908040611190309050d02040605040e0622031d0612100602160e04 71
    0x44e140104400c414540f100c044160285c80e910165010b41e1098480792a500c107881c0c982d8010007030900c0900520b62081c07011009a0780d4100308030b42070300344589516604d0f803100500580300858641020b0807169400d40b41440e845805024681d03000d400754240c1c1c5045459810403030701e59003075420031540003206000f1422078141c17543c010002c0c1d010040c242d010700100c800100b01c1e80e40001080901614001c5007c005509081c0203840700c5411380144000c189046a0001c0d01c80000e441c1420302801404240c281081001d5014245140d000301c00d494a680d9913890040040c60b0703000e1201d80da030081c03044d001101200001000c96581c1d064803940861400e0200b4041c1c41c820700d41d0266440341c0c44000004a5868038410f2101d02201040034259034604a20f200c4220340d01a504440d10428000498010962002003031040c00101000b01080401d85000030341f00d40100500d112190089800340103044d4550b032640c84c211003083e000c1d550398100942c4410301801e0184590088131202000003800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 395527347 1250 395526097 395526113
    0xb19020306130b011803050102031006050c0703030e190312090b0715151a09150403150f0219020d03050901021806030403020a0b09010501061209030c020d080f0c0a12020601030807 79
    0xb103603c040c50b00c06800300c0356040802e244085680190303042e03580003040c00079251081c50108058500e0341070403454075981560156950100b444060100503806120f94040d030340c0c0f4a00c1010b42c1101003691038600d91a13040040603452000302a03070100301c2094002400d030000d041a10a4503402c07105003109940121102d5000e44846013101d8a5004030400100b444d0b000f00540301c18050004006945590624003400030450309a03c0c140f04c502d800b0700c800c0001030780000c20944c40342a82c03200070490242e2110000c2c064042c0c0340503111a00c011071150b100346540021070810000c2d441c3d4050019803220300501d070803882040505042c05a00c004540b0071424680700940d007080c80b0340704407030a00c001a11000001d040030341c0e412003540d445000410101d540a0070316500350940311801c11101480d82e50240840aa070b00000b40200c034421082c005102140081e01c00d0250a201c400781c0c0c4450305165a03854942e00740302103446044550304204420310000e00c99040c2c81e07100f00c0282c0342881031780320514 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 395528597 1250 395527347 395527361
    0x20c013c18050604110a1a131203020f06010b190507050316140f01020f040e09120409290d0332040320060a1b0f0b1902030613 56
    0x31899441d0604605102048403104589600903005064142030901d84800201c448600880c814a20b42c0e00a00c0440031b151424002009013818082d075441d240000c070301101c20103601000e00034a244110806068020039034100d00d103004020f90b900d513a03c84091020a0049054491031402d2071441c0030061400f510061030121701130011207003403050103c0030180c680103014048888000300f903174050b03c1c00c00801642309640100b078000d40c2064100c6200b9000c40c0550b105000da400c0c0e282020490144080c401c0c218600700402103070f0340d00d5840d0035908010f85100030841c28060034240c4041102a00105100c8400600400091085490751821030f00440300c2010414000b42da40c0220044031080d0b0303104009039607078804030341e2650b1440c2000d0318034040500d4589003079007046503e01910b81e6042d044500304d00403030914502a580400400e181a12034150051031880118024028040c002d80f855101c0c40c40e510b10103500c00140b6014200f60300060340d05036044064540c5101c144c50707040c0c2101c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 395529847 1250 395528597 395528711
    0x6180f0207080d020408071403030d0513050d0f020c1c032102040f0302090717010b0a0908030c012a09030201050904110307030b1002010603110d0302030c060109020c01 74
    0x15007002501e885842050f400340c3da015020560018081003a010b0922600f001000350410803508110307060007003a00c0c0d03c6040400744540703075104001a07040c402c403110f0784081a000030840c0e145041c0c5c1360000d0070100314801040702601c90145884460314101c1d250440a02c1032856940340d8011a6900355294608a01c2000b600740b131841c1c0141c104ea0080c40548000c00300340314080512855030061090381080130300070f60100100000280e151421007005541100d646250701945c680c480343c07085030b2110007074010a509000008070741070b20f100150003011002820507030f80c3c19240c1101e80d42d4000300c0c0e10ba034028804507424403810409903002d4405080700c09405000801c41d140000d805581030751040b110400802e43c0c074501030850f801e1210b8441d09514050000700401030654540e03950349840c8005040c8118405d15081c001c252003031043d5041101c5580868010356141c0320040069000340f586691a9880d0002400e51540e401044520302c1e400703591140c7e40110740041c0720701c14030583c407040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 395531097 1250 395529847 395529851
    0x313051c0c0311060403020d05070e0c090306070f11150621060f0604090204050c030406150518131a0115020601050f120f03031305011407021f0e0304090603120306180f 74
    0x1c0544c54110348448d005103d14060405c842c2404c1080764402405440c40300303000e40500a554060b280090102d0b0400400d0038150b1019441d50002c50f8000401d15041025015031254402455122040316000d05c404907503d02034054450b0080e1001d003503903030a11069500503004200b030f200b1481d003110703000030025002082042c4c0c183c0100701528020741d0220b4500300000204070078400c00c0d10a460380482e0840d50406914601400a089000c080c0001c003040c51010010642100807a19001c24041d030104101c0c280031208500c29038401403d02c03508030b0480b4004201c12090344045255410390f070340144402c8070591a24144501e1006041c0407808a20440071070003601e150070030146208494100a0107280a4586061400c1d038034107191107200001d1850034441e08503004180b18050b184c8186040034020900041000944800c000f0b024040c0000200406c51004c00c1e080b11041d039005d484440e11504910408404071585445121040c03418041c8941c02c404543d007050310104050100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 395532347 1250 395531097 395531099
    0x12090109060809240109150e07050f121005090a02070209040b04020d0606090e07080106140910030b0705030403080601170711160f09052410110313051c0c03110604 72
    0x21030000e01004000c03961100040d40b00401001b6014040c00a0110f0825290507241717140503e180c40720795020700141c05108002c11101103120350401500e00300501440302c940d5509044850001784520350042038020062400020484607050007150609940a4548007542c0d0342c82e218411101c0c1e001c0c0089030f02c07a600c2c020b2107000c214140100750140c1a00500040c00c2c100500041d4500030245d40000c03c1ca03410300008101c1c001641e004a260b0381c40551300f0100c507030b030380e80c0c5031515080700342c0c200070041c005040921488550003005036110302d1107034980c007400343c072104d0040d1034a4603207009140c1640994000030b00050b21a51134612100c501e00308581030884402403040158140d0b42000c803031079400c110b0070400d112550082d07e400c00202d580c0d1030300d1400d204181442907200c007901d141c0180f6140c2440300c825480380140c01c0d0030310700500a5030340b95141e0340e8040881030a907124540c407498040080004110602a500c5025a03018100340c003c185140d0b141d14000280003603c541c49103003404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 395533597 1250 395532347 395532373
    0x121020723010b0909010e0c060a030209060301080303040618081b0c03010903080423030d0c0903060c0e040c0311070f1e0b011a091507060b060d0c0212090109060809 73
    0xc640100c0031200700010079400c95000910444e202c00038250300e070680c1004600c00c0818004108083d0508007560101d0f80c4008200c001e4029100f006402508107500100001d05a0000300c0514011403050505010040d000c603400d001d02c40c50050080c1200700100170003120400c4111506c02000000c600b69580d5a1400340080c5c210344601c00c2c2500804c034000200000c001c2e00300c0c03c200c20140d00200c501240c10000e91507955030700031403801c1041c1030b0b507416148070518001c0c02d0b820b00442d031042c0244100f51041a004152b03000300701d90240200d0030002c03042d2419009014481200310712509441c02d00146844241030312071080401e0b40c00c04a16072880e0760041201006081c02800707106800c0c5254135150060030380010101030b8048514050081c05010364800000c52103542052100d9500c41c6c00d503040050040801c140019442940043c03034a80c610b01c690442c0100c903010341c090381e041301e00c8103514502c0c0d441942d050038000350440350240003150142c888a42c110500d0005c561100c0c440407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 395534847 1250 395533597 395533643
    0x3050114060910170115021603030f0c080d06060c023309060903070905071722050f100e120421031b0308010f120323130f050103050601210207 63
    0x1c1c102001d0307800d80e180746c2030f0300680401903888100c00e0940083c40300d6103580c030000d03d4080480da004003082103010000e001d00c80b810054896103c41d10404210303107030b50f8000150030070b0890b02040f8081e00882d03004400e6400c00c46801280620b00c40c40c0d10038452002684040d007580240401035100350103011150b440d850810641c8090003c0c400001800c1c1014103014150306010b881c0722601207212410009100b14070761303401500b400b10f8070103030800d1200c61410a00b802040d15031040b69110f04031801d2101c1d8101d4114401d106c4c0114141c42481500d5656503100f441036001e83e5040c51501101d60103810600d0021403292402803800038480301914080d00c45101113800140c0018a5007401813011000f0615410010075079805401480388150364082c120080038884070400807880d20309206c0501454013219407000c2d00c04803040603141c5403070341e502407107000d03004807800a40340c50001441d43d401340918114524102400c3c090102100302c2500203940038075412100c00001e50041d00101c4948 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 395536097 1250 395534847 395534849
    0x180e03040e040209090601030c090506012c09160206130f05070306020d050606041518120609050708160306020a090f080f0d031104050906180108030a030501140609101701 75
    0x89480c59072418903004000354050080c0050103550050001003000444c1441c8140481c0e11341c9501142c00e6036440016100d40205000021701442c0140e125013400c1c0e03000811004001084814040ea03498108803c050401d0420304000941e000c4404108180b60011200120740e128142550010300282c1d41d140c00c2604a51049444d0798001c250b2688030005805010b40c042410b0320110f0415150256200a8031440001c0400703102550305001c1c032104601408001422080810541c0107040d0700e00b441c01044034040684444c05107400c0070960348000b00d81c03503108a081002c0300d0982ca0450b141e200c02940f100380c4502c14408015000140944d0740240c940040c200c1d14007800c0001000c4440d40c0c1048120607941d002c15152959101d18109101c0a4805031403040e95013240a9548102003882c101c4407410180481b190640001840c0e11300000401600740310740e0f001d002c203999841c540b00038042081181ca13408082445040494148002c200c0d600700743c103203428220749030441d0745a1104002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 395537347 1250 395536097 395536109
    0x10e1c120603230c011b0807050705060f07140a0302030a120209041e0506010207061e020304030624080a020a0303210f0c09050105040510050903151501120213180e0304 74
    0x4600301c3c02d050100288000d40300c1100070f007086a4100d100c68400748409028200c000d10305c510104601e006d001040182901030503000e04866030754140c0d0400e250403a04003040c201d60356004a250740001810110f6a4008680e00d5001103041c002c40c00350950381c69901c02000c81110354240440c404550705ca0140d60704450040000c40258010703034440f1026200300502d540d043d036222040c2044481d520442c0f048444145481072240980c0c85602207046228561000e0002414180e4050384183d982190700c03014000c800406624aa90fa4107094890001201c0690700c2480c841c0300700042401503d81d01c0101710a24131140641210145140071134881d03248030f801480d543d5481c2c1c0001500110140054003003402c00c40d05280c540760010324048900c07000c410030081301194100c2030b070305c0401c1b103c4030741005140000c60f140740001d41c03020040440030340d0301d001880e4002c80000c200854801c45540c01c20440071f00180e5424280e0f488610502591035201d0203a48030301004200100344064805410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 395538597 1250 395537347 395537393
    0x50312070816150f150501030b0a0902120f01050109080a06090c0803030a090b0c090f1c170310140315070e060a05030603010b0303091c0c05090a0e010e1c120603 71
    0x741140440455021002c4031078201c0c50b00040216103480c1740c422030115082441c000c1107004021001c030301c207404542d1200b10303003034004101c101242680c540c3c03052007607403400046d0b06180ea0780c5c00111041c81c1140704006640c0c10030b4110f000440e02d19008801e8140c0222441120280e440078001d2071940119105c0801396510350541e010001c800701010f030002a030390015400c1072030403400907440d01070108015104000503055480f5510810b0929000c0a402c079150175074034410a0410b01c0d0543c0212085801803006400c045544410744403c00c1c84620050010044500107450001701c003c80039202e10140f1112050aa41651381d8000034422841c15a0320300f45c50741001d009242c20749010641880c800d804c24402d4603030713548070360481c52040c185c003681c0503039500124102218030a819820031600070b8000402c00811502d150424030709480c0f404000c209034160017039072f50303150000015078405020316020040030301d0f84a1a420b61410703a80307050000b407130742da03d40d071756001c840714143d410304010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395539847 1250 395538597 395538623
    0x1602060c060a050703200309070806011512020406050d02071110020c04231b0c0d08060117040b27010207060c1106010305070512030c012d06050312070816 68
    0x10740380929600400c05003821b2298520681010b0510b141e19440042a02030100002d0380010081050354010000308050394281d5856000e84d400340090a401603020960307104080d41d07000d000f44221402c96105a40e80c60614044c103204178040d5118801c2075a94040c8801d80d08016a41c201131428038080c0344d0000c3c0400140030061200f51021541072805150790005119405120f9210084d03010000c01012201041448140040c0d07026450b4031220b9841854200903185400c64005801004240c07100890b0a181c9140c00108003000c4400600110600340800c2d400c2065a0340f41c2c0402c50078201110005400380341840c01ca801040060700c00303e858a500c001d031103402900200756000c100015240d41c0d0304586403075586c0c4d030031441414028a01d248403c0660141030003540d4000c05403000910030a00151003410300c213440c0101e0481c170300d41c0100d00e20920056900c5048110f40d00900a002c03207448207000c00303245400454050b00e40741000c004500c0300c00402d600d040c00b1b443c03107194200191 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395541097 1250 395539847 395539861
    0xb03120d0c020f0d030c020a050607020604060b03060403210f090b01090b06070f17040e0708090d02010b0315040606030b04050706020c06090f0d02061911010b0319081602060c06 78
    0x40d861078007018041d9040300280403070740782000c210501500414180440c4410001200724941a5801e001400c070740640c0042c08072480d40030402038011130142c00c0030701c061541101019100c440a450003400f0403442221840144426100340350001c1c100400011100303e0b0079031074804e03510040c0040310030000d06070041c0242800e52141c00700010085c0c034014100420b0f03039101c1c08085031000001c6d0411242846055070f4020160481d400340017100070307106460500303c0004d00419001d540206481c00b400318070300010380c414458030b445e8130030083c0141900348560303d40041c000c5c4003400c15a0040e0715000c010021170014205d0300d025038803a500400d402c40c5450402810402e1030609030384251b004005017642640d680103881002c1e40300b1900c0b00068006840040c0d0303a48500e4460b103007207614a0301c4004001e90007051136418182d0002c001c0c448074010908040e140d010f01c1c1d8041c00514000d069040100f100d100150008200101c003a4403a500315800003000c81e084913070b420456610200801103d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395542347 1250 395541097 395541101
    0x609020c10020901051602030106051003090b090d1d03030c01020a05030403080f060f10021c36060c08090303300106020c0d020307030b09150702030a0816030b03120d 73
    0x54203070380190071810b120b107050000b0600d200c3c0d4000100c000300c141925109655080d0b1040004000c010540c05401c1558000507015145290064071800304000000f0b00600c0046175446600e003055446045040500c120740c045150410103058041c4018049240e100509100500340003003c2d40f02c00b612840c1c2850010b04100c40104140c8510922400f131103203a441d14619100c8000341210342440048285c40b08a141040d905038405070b00e910114200c98543e0440710340041099140c516444202c41e0b070350342c0c403842c05400300ba4000540c40314104218240c841c40748607422602c40d050003882d2211000000b46550800c48018841d40c048030030b0103640094441d69600e400c508a0401000b940c900400079440e80b140411440c002c01c1028071030030456600744102c0c4051944518441d03403e00344003a503103580d10f0039042030360804c000000204030140d0000050b0360f1107000d02c1d41d849199039203190f43c60700c00400f200300140c103143c0c075600b0100c1550b070140a41d421352030740005603d40f10445003900b002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395543597 1250 395542347 395542363
    0x30503030a0e0d030b030d0e030c19062a020f061c060e0105010c0215090105040b030c0c1e0c010e01110613030e15180a0f08030705060f07051204050304090609020c 72
    0x34503241285c0071341d05440102d00c403030f200d8000d414000c112031600c1022904100d504141540d01265030b031700800305002801030f031509a81c04d9540b02040c007001940481c07510600d1200405601203861070100041c94600b60b035040610002d080b00317003050f8201d681d0017034011000101a0a1a40701c420a00140b0302000200d40101000d103418049031505802080181c3d104001c4c005c003550000400080c00c3e409101214001c05602c66032980c1c1c0c0c03501a4555405410501d0600518000d0700d08013442c05170010064501104a10301401a4010042c015642951042055814007075029240a02c850b424020944220342c85c0401e01d40455480c5001480d5008503100c0314070415041034a02909001c0d201500d1008502141d440d10700a40c49001507211000d941c411201a1040140810120000b001800c060b51060048400ca030f10307150401001100202c031107400151050103d00c0c20040480c5074950132a008030b05603842e0980790b5000c10290740c0c041d08084951030700002c1c41405181c0c00c203c0c0e10b0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395544847 1250 395543597 395543623
    0x91506010905010527120604110603010b0421020402070b040c1a09040203100e130303050112030c02040b04060e0705040e160905130605040903030f140405061f030503030a0e 76
    0xc01010300b0540007070458042d02d051500c40f0800e000004a6011913000081107018000b40420411b410081050351742c2c4008076001c888241c030303030010487d080c200700003501d046e2aa107100803400d050620f41c40444ad4019000709141200c10421100050f84840c030003804018012a030910107480c00c0c1c1480025400140d01c4100048070604908214107003030f0040d2412400100d4015a8075100c804900a0002c0240c210382440e4881c503092182c0b0618001c441547c05110343c5042c060b0341c0ea203401040091700040800380c082040c0300d19100041c501030b13000e002203000c003d0002440315194445503007542c0c4201d0b104d00115100090078808000e5a41c0c541e54080600608406c68080c40100244001400d11070a802000d41c1219030b004115250400006003c0240c0304122a196508000f405807143d0903000721030301e142442d040036844005500c40d1055070060024541038860110900c0a04c1e1038054462200460440110010f20280015400782c440800081004580c1601041c10049854150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395546097 1250 395544847 395544857
    0xb0406180e0f06070c0203031207021c02030f0a1413080601050f06070203070e070507080c010203451204030b0a0c090e0103020d081c06080f010207030c0b06030106080609150601 78
    0x1040d2090000128583c0c020040d05d480d07a4400b085201003880c6000701d460400d654845c0c4401c02c00a6079001510848143c901803088400b406050303010383c5c4900c10414000f140c25000c02c40a5089401a9180b1901c0d120206101d4982500541000006001a000400c0701c0d0010030040006217040c4d000c0c8645807504445240ca40350007a80040ea070f580c86441480c00307680200c0002465680164203541d030058204410079922540c010f05203000303510840d60400c60107842d03c00ca03090040841d03080c1034600c0321851500310b1400200d10340c1440704c00071200404c40e44500e904090442111001910040d445411240031909000000200b51869a82e8203810031902d0082001104000d49041b81141d805071501d4041c41c0d590300384034605228040861140980c7c404803607a01125030350000701114059400e44880032080d4508074283d100f0100c015001522610181c00801d0801c4006600010024000100260f6401c4441e0621004907044452900240d04a0b14405030312034107142d2000c0d0920705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395547347 1250 395546097 395546113
    0xb150a020c030c040212010909020102120c0c030601060f02100b04290a0b030f040b06010504050d23010c020717010b03010527060f15040905160305190206070b09010b0406180e 77
    0x403100c3c0402c6c1403080c0d8070001d403075280c90410340e40280811190356446901155a8074008100c541e610140c4406481c082d20a15000182841c401c4001d1680c0c906154043d0241c044d010070508047d04802c4207042c1d010703980b1000d103501410f44c82c4105601100e00c2442403407213511802040010042940444401c040800400041201ca20410b5501a40c001d84080d480d85582004a40350f000d03607000107410007400c00028091215480c1c7c48820100030803120301c04986021803117400e8411840b103140241c4e0100405100d41c2c0c4c490f4a9446480d20401c000090310900d00c00081e0179100103a4000700103000d8104804945030444051100694034140200030b84d082c180584001c41a00424410500140c480b03024026551500074082181d00141141c91102d5114804411392405200403100780c407c0401c030030a01c980d00401d034800d01e0703002040282004410340b180c00c2d204100425400c1107568400a41d8074540e102d104480160001110040f0103041039884c9604960382801c04100503406105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395548597 1250 395547347 395547367
    0xf0803090913060e06040b092526150912030903090105161a061009030b04080a11030f0a1106060901030221060a0f0b01210b150a020c030c0402 63
    0x10700242c2050010041181034603450400d030000300000c000665013401940140401c0c07002ea006021701a0040b1400d40e002130100c04c1102031310f42080f0310203488859903100c042201c4074100124a420700c50741713000c0504458640340364034100216140b0076000170400d0400e0000e000700400800200b041c40020301031131410115a450f41d207000d03030014141000ba001400d10202c00d403990340d41c40e44950241002600c0c003014903410f0310f0303981d04980280c00380d03103000015042103204000c660212034002d0744c0031070192643c3e210408107138403080c0020244203c0c100d121450788010001003101490429909850760100c20004281e42c500740101c20076a40074500340501ca6407004492411250f040b40e0500360041c80202d4000e441c0010042c541b1540175200030800c030844550480c16000304209004c00495003400015500c0443e21024070003020701603036511141c2d848950140500314002000603140751401c4117020354517401030900000507045003161b0a12410208084a10100c0495096003800c104407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395549847 1250 395548597 395548609
    0x24071509030e150301050d030507240e0703150510050a0602060403021515280608010e01050a06021b010309150e07050306060f01050d1503050703110607110409051509070f080309 78
    0x1b010f0f1038030840b502c6048030205805442103918496105404150002e015a500c05c00c1d16484210760060382d0030803c444402c620086820015654481ca641110310101001440104401005040c520700310034030114031692211100300c0100080e9004100c1e52809250090030f01c13241d02d119045000c0b072001404542c003d0750b40d2100c0284010354151041e0004440400c4850004c2c072191640c1c0d100045001c10a1a031000d01141a501e466064100c0d81e6030b50f03001c4c0200c81c0d80341d1240038016044280822000c000074280c010200c0b90516020541100f01c0d21041c0d40000b60081d41c1000b6031380e81c601c0c000d1070101417000c00010704040780648458a080808074400c8002050200d04208001030030f034020281c5c2e13901800101d100d24401548aa44900c2d0803a1703038101c07500003501c3d0300010801c02d000d90b10701035048801059200303104100c049605024000600300382001140d160003070030405e02550b0706007800720744100004002030850b58681402c0c9202d01c1c02e55000562180c00812070000652110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395551097 1250 395549847 395549849
    0x1506150314040b150d120302071a090a02091005060d0c1e050a030f0e100902090108160b0c0f0d0f0e0109080d111f020d050105010e24071509030e150301 67
    0x400c244d8030302e0502e5107000440320820280010501d40c40c0c0c111081c0d4407641030f8054400e071440350045124005140030101807940c000ca85044c1954000c80c0e0740001800c24250312034004481c03101c6c1343d0b00c031515080061607641000040f21205aa600d0079204400e512503840a12107680302c606480f084031008000b0110710842c511503003455103600c01d40c510044e1980c896142c4030130b40016207004d00c90400c0b40c8000340c42a1401a8800d0342230b08000f2400c514041030688085102040c42c9190b61702e820390303100341e03904000032007800d07400f600760343c401041c00a00407500741040c15560800c51b40a0514090300e01b0000d18070481c100308540100344900c010000b191105140103060140303540c2c4010b2400ca180810040d0000c494002c40407401b4a48000c54000d0034072030076681410b1040c1d80c3c95030011500e4400c0d01e02141d42c821481c410522034240d4500410503005804400189002c0d00b03a110601c00090f0090501125503881e100007007450740c003c039412246c4c603040340c10542104021800100314041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395552347 1250 395551097 395551111
    0x60109021b150f07080709030f06060b031f06090b070b0a0617010203100e06010e10050927090312240a03061d0c1302071506150314040b 60
    0x10001e1906400715080a084001012a00884100d80120301034552a00c10654000c880901101d0204080b640207a0710a03104290301d81c0d0b001101c510b19244c0803610600100150b492554030300c404210805141c000b9071140071401d4020701300c920540e074165851409544140100000c0300014004050740b40c0440361259001100341c44262103080098009200c03590002c5107200c031240f1001030218041d00654410031940e600c2e05000c81e034403003000721207500403103441d40010b40111451605140c00d80c03035070f1042c849130315000b410000d00d5404602415160350514650ba144800c0311a402102c07010310319413100c202c0016504003d00d102d200c0c0301c02d03c0054945142070440d512014282c031149000701d40e1049004103002041e50fa28100a03005103031881c0000c8000301104c040c02151b1100041c03030f0010075400b07450380703e000003103012400c02500030300300c101c030340c1c1110303240d0321650001c80d01070315028184030040d000d032001c1100d5014040b40d5801d00e2400c50440b4003001c12010690303d080c420b600901c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395553597 1250 395552347 395552351
    0x160914010302070219120b1510080405120a090509090304030c0e131506031a0402060d1a18061306030f120c051510051206070f1713061d060109 63
    0xc01c92000500c07000030105c07414010451640001138918880c20004c1e51280545400070164944280c0044012604c0b038540c1e8000249202202c1c280c0e1282050302c0e4842c0c00b803800c2e0380d0610b000c107401c204c1a1380006100030004094203403c1c0000d1504044c03603600000a40000d42c034040ca1a615418445014494003521118003400648945590810502030640c441e60b202207942c440c4440c007000302138034002034031608d510041c0c07200200b081d810764074020764005082500f080e07045024000070704400a412541c9045030100c4540039203a40c47d1412400c1d00d0344440c013107203291407824030489000600300901c10790304044040000c41c49000190805a410202d00c059440b4400c030180c90031040f6800c0244684500b244010440401f01c110718010b40c140791010061598a508120580207218100c0d82c0e50f0708040c010480447c015243d155070030000c0d09050b025114600c4002e81c000e1411900c46100c404402c408400b0411144507560303000b13040c5420003070303111111403855a4850050040b400801c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395554847 1250 395553597 395553607
    0x1120b030a0318080111030115020312180705030a06020c010c090f050d06060b071b09020c071e18060e01150c03120b030709060512060601020d270608160914010302 72
    0x80c0d401e0000600301c1c1038001d124401b100854421958001d225003030b050f0b145070340b4903911036201100720340350b4028440c800d242c60748661a5280101100701410780e01c03071041200005003030324141300ca400d0340c2e4010000180c9034444488100d003074562504000081010752042400b02600b98105030701560402d40e400700101c0c1141c64000000c1c4440d0300040f0840b040820f819003000800e0182c450080c01000900301d40d0b079510100082640141054140590000301d424000c0890180c1594a81c0d0950b020700150144e0b03851806101c41c1c0e0700151000256240c220a00c8083c0c0e80c0c4010390700505c0c95001038030780d02d0038150340207001d104207010040c02c00041c1c086900001c02181c07c0301e89032900040a8500e41543d613441e500060200340b0815024419082000311414008101c1c07a101c1c1606030003810002e03203a6101104c0f6a00340e0b00075100780310113402203040800d240000c807001400d5162035001041c02d150305e0541c42001d5a401110401c1303410311041c800e050711071211028000c420300b00940c0704c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395556097 1250 395554847 395554877
    0x406030f1103010b090f0913020415090c05120705091503191a040b060403050303010312050f0720040615050a020c10080601080a020a052502120c01120b030a03 70
    0x90201c0241421a5800c0480042a000350020052142e03020444000c0032607100b040520542c000300304d03103844400c401d01e04800302500780707178020b0b585403107050100010164403500c5a40c1281d41440b50b000c0019000b040407078a030b800d0f15171990b0300015907041503400d0035501d10028141542011b80c49440c5240403011a540702420401d000c84803407650024405402071451214455968a980700c0c41030b0708242010745c85003040002c032001d40340c020000c5c1d4a140c0c290b880c0c0014000e40d0101c0784041100400400b034805c1c021401500c581441002055681d0288112000290b080c200c000b07480f5924200c010407038075059148800368038400f42007a80d115109102c06030300340900d040240740c100c43d05150100016600904c3e41e4803c1c2c0003600c4041d49a2550602d00c0201e00403c0035a80124200f0001000000e0010042c808040c91000091440448540c081850503504000981c445d51010074103420668000e02c02c0c03122924000300c100200401329000a03903604824034050240807040c201e400c16 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395557347 1250 395556097 395556101
    0x150103050c12150103080a02010b09012102061c0203100b03071709030702040207060b1507030203040302042d0c030506010c0201090b030405031902070320010e01031d120c06060909030406030f 84
    0x8010031020f2203042c50b40e580d0412140580c000043e5a0040d407802d41c0903031302868030040c0307036059460081c107800020287c00e220141d001d000b81001e80c1c1c0104144000301140300d40e84160990851102030268076401c050000700030185440c4c1104411010500800c0026640110090300441c0c4010056809860300c00c407180c25803003003040203500140001006428005070fa0002611414207440800b840d900790000c400480c01801002030041e08104010005460680c005d403103034030f103030020740524424007072404441491b0b159800c0c000e4a07100c04402a5054062040691001c400c0c248a020843d40d07900080c9090624011079840800100c0400c1c1804030800c26210301c4290304204000600700c20307501940d26503e5101c04c85d0340b0142c52100004042c0703040e2002ea11584180c56441080e0719490054019104030200302c042000c400c503c0b41412002081116444900c06200581d0307903114116035410400010030060003070307007542300780300d005200001114100c030344614002a92000305040200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395558597 1250 395557347 395557363
    0x604090206092d0102060423010209040204080d021204050604210807031d0613090504050a05031c050a0b010203040b0c0c0a0e0708370212010b0c150103050c12 70
    0x1401600b5028002e80300b030b10341c22281c100007038200d2104900c10f050800490b66604120380050400064210b0343d400e24004440801d092183c9a0000d410005130801040c12a0810340c040c100d1070b0300c824142c8036826018880140b5104a00c90349134a41414072010601074407551050482810408140844982c071032704139101c40320742c44400e140d6504c0180c01c3c001c10b003504a20324000644882480d568561030103204441804204c0d541048200d8a001b0011008000050068070780c1c0c0074240300007001810500c02007060200781c1c8000d8a405903034100c0c00c41200d00080c4424600307403418912078040d0380c00000380c2d01203c9154002d03903503800c5401a41824000060442da420500c01980407501e5446985028030070042507441038001c2d605d0718a00702c40140c0969038440b0014090350403c003a088400f04100e07040014a1016140140720700740d100204800b40d012030200d280100303040c20080f00038000214079881c1c3c1c1074603540315419034840701d848101c039a00c00c500c0343c0c5914410050003001484450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395559847 1250 395558597 395558599
    0x10e100c150203010e070f0c0b040f0501050c04140a050a0308090105070503030910050c070f020f0301060e010e0403030e061b07020d06052809050303012607080d08060612060409020609 81
    0x514450080d84070000030f50028040e0070a83d03054900021440d500c00e16000520349502ea54082ea84480c0e51980c400c3e128014005403940c0020f01004000715009000781c50040712203508450b070325442c020002c0007100d65441598450740001c0010031050303030b41e080070300c00fa2600200c0e803a13910326160300183c03160b1003043c0000742070b030001004000c400b40000c01c02056452045c0d500b405541e03110002016a07106030714005200a04120550015051000300400005000b41c0009601c1380c0741c120701c0131456801d0344400f61000301d0300100001c0540c1406000700018001e0000d14280c109040042e10310a90100c41d441c2d03450011036060155558001e07031100494104100708003909055581228415051800050710080e003400c0080c1c5072150700c2a82c00f00b0340c03c031024508590800310380c0e04001c0440d120072100d010346176407200300c161340034801e00000f042c403140149440b04c41240007412020004018034403d581c14085075802c9a02d6100c401d42c0b204040710005035070a0148005039003802440441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395561097 1250 395559847 395559863
    0x506160803101505070c0b03010b07031103090301020c01050915010609090902010e061603081605070305070c150206040c0905010e010303030207151d100203160503102c07090302010e100c 82
    0x20f00446401c01c0c0102041030081d20101a82600d074210700410703102c282300e101000c0008114001c04a4843c4003411002c07100007082d60300c0c16111000107400e81c1c210546818440e5501d409100720307054100b000384841440360440d4a1035601d0b1107400f510401452050318080c2e9112040c0d501168880e90782001e004000925681c2c80303041111140b18140d402e4a01100419100004141c840e03112550900d640b040595501d460b008007940c086640d50404102100d0780d540300c40d40032540c3d18000f040f5032401e9809034001c0c40c161a040c2444610107010b03500680a8a103000018014810b60091043c10349400d03040c05650b48040c0d29204601d090300104188016140c880410542e4501940703600340502c0700c804403030744d6080a4806008030b11055511004079826a05403e0095020350040c0d503028400c14106100203544071568290480c1011910544450700e11984543e0a685a8400e420802d14540a00740030b00b90303400604040700c581c07880c900c100380d1420092455881500d0a140196024082d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395562347 1250 395561097 395561129
    0x70b0711011101141f120f0215032205100e0715030501050901260a0503030a050f04020f010302130801020c0f0715050d0507030b190609050616080310 66
    0x240c1480c585605100d80082c1411202d002010b0050103206050402d000e003030340d51501c8012100090f4410f146854800300524200021150800c0c01201c0d04c0c9402150001c130a040d2620402c03040300500e012042e06140d051040c0007403a10f0002c2c1507452510314284209001007076040481c90122180020313068141040d031741411442c008140c1d030046480300034500603406034104081e030070b90300240281504844d21030f0040200d500d20700c00041805c02050f04a2030040c007000303540f909002c50014251503d030310000030b1000803051031250941c00303010711128083e9410315600040d1003400020780c0e6410542c01040040c09941d40c41448401440000000c42d038821003040c0c0e082d16401400e407020100d0081100000356511f8110120541c030810f03541c1e0324688220440d803040204400380c101402c0541e12400c450054803041740301041c0b0040444421450780c9400e40c001e25203916500850702a000a100707000000c20059a403100700307940300700300039265640d40c18041d200580070380c841c0c0725001c0b504030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395563597 1250 395562347 395562353
    0xe060909070c03020f07061d0105040803040603021210060507020f010908011406040507080601021c0302120f0f0705090105090f0312030c0307120603150207060902130f0e0d050a0809070b07 83
    0xe203a4807051280c1c017554244c1c900c90581c580c440c3c80501c95800070500c0315040e4034801a00c2c01c001c045030311741410b1113400c250f150310020386580c2050b08690301003036001510000100d0b0000f1142e40c056999248140c11a043c002c0080031805241070080c06002c04040e40380c0181c1c0614540d001400064000b0844160400454188400b0a46040d8040c0b4a0714020881d50b522500c00c65204d0b00b01030b0020442c3d1040d444d02040240c0e40b085000c1d04169091014040c9401c0b440200c0b80140d148004d9851982032005c0400e50104003c3c0035141840001c1005007001d036040001e0740c0b075030b600840d80924006194400300782007501c005144020144000204200004060007940c010b805a07500c3d0090710041c40e81c20b41c02c40b03056000c09040084031600d01315840c1402c5d0010245584201c0e400300700ca800c04d030f002c180101d00c0c1c003090109050f1a001801461320300d0b482203000c1c0702e00c1c10006103000c000e40c40001d001c0e44102d1a000c001c0041c4a0005030703040b1404c00940000b4451085107a0796410141 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395564847 1250 395563597 395563607
    0x510030f06231806030d0c080403390311060c0c090f040302160f0b07050118030504060e0a0b0301090207052e0b0105130b09010e0406091a0a030507060e06090907 71
    0x2040062041d9104000740300800f500c00400c603c540c0c0e0250003048500300e900070940b400030440c01c1c00c842a1004000200005035104440c1802c6c180c42c0e2070525a100000c6520101200b0041036032540b040c501070204042010714840003141141507a58580c2c3d4940c6501203403d044940004942081241e82440580b554809010b0f00c614000da095440700b51481e140300402c28a24880c800f520441110180441590303040140101e9106000000d104207910802c1c615054000c90b042c1c0110301301242c20000c02e5003110184001034030448400a800307003030203070043c031500043c026070311207a030b0100385101008010441c042c00c402c3c080e07081a1a5400889e490071070801c0420303078050850304210107031400b0350080f426075440c806a00780300300400e03040502c40d05064014404a504105900304030142c43c0d202ca10902015003076003040030a800c20109a0120b00754014141603014090102007000842c0000c9001000c1d680302c0d00c0e003050320180c000002000d0740640e1190030350040d448004d028172143c1003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395566097 1250 395564847 395564909
    0x2d05160302040b09070207061d0301150302240316020a0515190e030304020d21020708010c0f0c030810180b12010e0d0c1a040305040f08070510030f06 66
    0x1ca4040c09031850403c2403101c4650f0940c4c20a002d030b40a003000b4044c80c0d000c1c48402c860080751002c6000c41050600c0002e0960303242c4a012084204100340a009600f4203041680e403d94000301d8184034841c070414081042c0c0f000030103c940c0c80c50002c01ca24104d078403c1c4050300f41d43c0d802400b150305d00042c815410500840c2038404880981c0001d080c100c0f182d48500803000901c0f6203c0185047d540d5030340074440d8407082c07017000722426403c607442a1001141e940005095101d141e0040030f040d8140001c80d421110341504810500094003407103450142c1c41000501c0c22903162a101c003c87d103a15030f160074004078642104214040718203a00c40d030321503940d00c849075200007203406106c860f92007a0b0706800c0341d01030f2100030b000b90401e12009050b035008111898540f889107070b412032528a0004684410402554100c00054001500b042810340a4110001600c000806400e0707062806001030840e45040449509142c2c450158882c03030652544248018001d64100c00c2c9a42500e0391350743c441c0c46034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395567347 1250 395566097 395566099
    0x1103040801060b1b01180809031f0207030806030c0a2904060c0210030c090b0f041809051b09071d03010c12060b0f03010e091606020c18042d05160302 66
    0x84188818000e005001d0b510001090311b0343c5c061030f01025180c400691f40445003d035014401c00c10b003c40c2100c40007840081183c0886001a1100980e00c0c0040248402414040c840c0c2d02c50601002d50f0754074030002c80111140301204121854000d000398200e0304501030001601c010100b0001900c1d904030045039040d9200b100c81582d50981b2400580844210489900c006220050144205a103a800520705240403032005400c280d5159207198003800d643c1c080500498840000004200d820828440381160507007107a8000310090001c901c410900a00c1f40c010800d41c4e8010300541d0700d201904c4460450068021701001c081080050400400d500c03071814801d1a200c4001850341f000020b81c1c0c031468190080c549181d107840c00c0e42c60705480c0902540e05a005480c910481080e00050346002400503030060300b0f051044208001c1802c0d204040d590061030f0100030040065010110100c6e01000301c40081c0c54043d40e411140c010b22481c00c001001403260009088213100d100e89003108980c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395568597 1250 395567347 395567377
    0x31e0706080f090601140301021c150503150f0414160608070c1e0c1715150d02040e120f0d05011e03060203061906050304050d08090d1103040801060b 66
    0x40e002c0601d20604001c6843d0a1030703801110040c803c050b81d100f440c60690700010005801c103000d0310450f03814079440204030060203940340c0d00c20ba041c4143e00220030040c48100d024200e8007000554043c2041c074020841c454a07240f51000404020051083c00c602c0140c0c1c1d01217807402450500c0c9000a941c4601400000c20302c0c240000324a1403050f103001c40349030b0303204194440d40c000c6841002e000040b0221b0840d410706403114080380d8824003105202e100743c1c4d094010b00d100158080d0058003c103002c0d081d6407200b010103003210610b440d01c1140000040e41500c00144070040003644034107103906081c510403000000a000000700d480303440034080c0382d102c48808218590340c0700700d00c40d5031030002041c0e284a9540d0741c9003003020070b0695000d11313032005001e40340da10825038070b0383d10841060080e00b2520100f0802700c00c3c4801d10904100e4030540f0501410702c0589418007140300743c4e89030b2010110104010340d080102d001c2c401c05000313840c000d1210100074041a070b107413a466000c9402280484901c58 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395569847 1250 395568597 395568601
    0x50105060103050a0c090b13050907020a060605011412070903210801080a020d08030c0d0908070303050a061a0d0207062d05070f0305060102031c1a040506031209031e070608 76
    0x15010340701700410003065407695a940c51520040d00701d075811010700b2961010080c0f00c000364685902040f2489200a036014040002d180c1c0f610004450307640c0c12060400042c1c03846040d440350f51504460300004000c103048820b54410501300c400e030816410040c100207150001c0d84840440180b41500b030a6240c44211440e030300d6408042d41c6064655000e0350280140c1c2032131000c5034202c8000c40c1c04c00f8202a81c20305d0031400040780d60039900540003c076020340c4001000d5040c1075041c030a0395000400c000341800014a840d07513050884042c201c1d03624071a240003807107401a0030b10b681100e0000b039100006105415035110341d207001c803e030061990b49d04030708614080250010f6120391440b450664070350f01d4507180e9004046008080081495041d888100000c6c04865407a102c0082c50301200f00010812601d0078102d11854061001d8aa010b00c0c208020b00010b0303034000c07504405070003580b40036684030782c8c1810010780f414441a8140b1194402c00044803401140440ea00060b1030540c0c80d83c1c4c6007a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395571097 1250 395569847 395569861
    0x506040b0429120a030909110c070e060d200a051f1808100e0d020a1703040c031b031106160b040804091104090c0201091a09010f0905010506010305 65
    0x103914000c410000c005154181195600119044880032582c0504186081800348840314070341040004107030003241d040c0c8010020f9800900942a9400c1225070351810803d40c10890b075510440c0c1d008040304030305100b00164254482038203404240740c02603518804551904c0c0c41481030380343e0206031030081080300b00c0490079023000c86002640140d164411040340d09400801c41d0201450050b441110030701f044001403005003044040291200e41034005107150340107000618000d48044540c0031364022400d14408030b9540d1a012005400980141c2d59a03515490900d0350b0225030781000303100c40c20341c900500b2a50004015081076900c00c0c1e001c80c103032111600c1084440c0c0a01703450448101040e103032000000f04a050703407940241c4102c100a0803e42c0380c0009d082030321921007240030010b4000c201004404600c3c040c14501c0341842c0000c0120410075241c4c2041c0203458021050300d05407039000715824040941c010901942d400e48200012032403494464081d1809941590029003084003240c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395572347 1250 395571097 395571101
    0x2031e0d0e16030f06090212011b0906200a1407030506010501140708090409120e0f0a0303020d0f0e0324090c090a0e1018031106011202041d0a03030506040b04 70
    0x5a00d2403040d51400243c40d44d82c44224040e0228011180e49859269400c0181c444541e5040c417100c0c5200041002c0f403120207800720700c0d200c1980d58401c00124a40c2082400d8001c1004550450030312a050029503650750034a10300340e840344000701010418440c00c03107000f0010403401e054a102e1000d41d03c050b40e031080111140100c92914008519040009400058100f802000c803035901800114154110f6160503840301c080c2c1c0e42e050045080c80c0580d42c00c510304220180241441103903080c3d002030440d24003e50799010301c04642c0c24040c401d8500c2c1c1015004a070309030040c0c0801000c41e40241040d0b0512426010480094610b0800c00000300d007407a50b01240b046040071000e030440c500b41c0d40350300405000e0840046c001c191809001c442e410b030704125002d5001002c072104420707146051145001071001480c0c407402e03031203034016038014066450030005100d00c182d0115008030303044080481c0b000400c0710020159802d841007610010415030990010b0784580d8040342e0800100c180b000511003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395573597 1250 395572347 395572363
    0xb0c16090504111201090606240c0f0f0c0b030c0d0f090b0610050c03040305030c15130b06011119020418021c060b0a0b07120c03020607030c02031e0d0e 67
    0x60b6884244102c950f050901d5044c42110040c00085040c0000342c0f50300007101c28941000c02c07001c1030502c07800515580c00c4000581c01c00940742550207500d60f52200700002458810080040c41a480d003a828000c0c500300103000384c402c8081150356414a40c1222100760f1128144d0300345039080c42c41f0030352100c58500c64030071040d03080780200413680d881c4010444240c00c5a0480701c18080f060203401303040d013010005080507600c01d200441c0d590003103c20035451320150845640030380d04040204040003808040075140107500440350700440d1100340051700c584610441006035442401e40c85c114190701c023041c6854140c000d0341c0070050743e0350301c20341e81d40c01440c1c124000c0d400840d1110362032001c1102485c0c10700300318050131000601a9080000413158a2240d00485100d5400f103114014840e5100680e1001310b20780c28040c0c40b400702d45c1d4001c3c1d00c85000034122803c0c9540c074800c50040790700034030032500b9410b1810f004e140c0342c08145514000f1380d0006004c000c1002d1034008088c80341000019428 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395574847 1250 395573597 395573603
    0x7050c19030804060b010306120f15020c030406030b061204050114060301052406090409030833010e031005090a03021509060105130b03060705030f150918070b0c16090504 75
    0x349541d0702e8a820000c2c5c80003151881c10541d030344200050030101010080d9143c1d1041e80c0300c000078541820450310244544903807503141c0d0f20400c00ba686e00c4070000b04890458030035050104124030400c0005006010345d40c8500d0000500004000401c0300650201c84e600030300a11105035a11104103050807a0b408840c4040504011080c0180300c1da403220390380405140c014542841c183c180008070302603840c0c1c0c2004030046000c10702446008883c01942c40004009415200140ac403001c4d0000c011680242a2505003c1c800e0355021a07a1402c0c008501c81403c0f0b40e80503c400c2c24040c3c4070a035030751644041a4018020700c190101840c10309000907006000007401818980d0811007082403086c401034034071103c00c4c0d844100c00030503141401014400c22040d181c940d103d01d095260400c103403400405241c900b84400914030051340d00d0bd00c406030401e044982c4245506981ca0b0142d1910b03040b0703041a0381400c0d000c03070284040240050540c0340b00743c4401c120a400340d5039008174410713070380103032001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395576097 1250 395574847 395574857
    0x5061902060a0506100c0c170c10030212010b09010e04110d1401081b0d1a0103021302070510180803010329070909020a05160f050c190306111207050c1903 68
    0x262020f80d1003400352900083c01440600b107c0b603901c9030303001c00b41c407410300813a2801d80103480035100f540340c200013024600e8031908040d031404600d09608200c1c0041400342849222000c41e48140c02d902c200b844501e4100007510402c141c400b89050f0240b5504100c0e072480c402070501c01001c4251030000760030781c100c4002e2401041c5024005a0002c1c00c08104461150400405088a0042145100c41c203c0d4002c0005400c8600e5045005111100c5482500469a14010814040040c60004d1103100b4030564510028001c052030301010004d988906000c0c1040074084004002d1016000030082c06c00320581c00704407042c5959441d140e03901d404460304408074440b41410420342c64183c00604000f042440c1861400c10644c0f920104101890f0017038507084c1c5c0e0b00b9020030402004000203a90381404684045070b480880800c002001c07042e020081a8a4039a40d0710b40300d50744040107440c0140440c02c0d800f65a80f800c41030081c00c0340c2020070300c00542e00c1003000318205106c950b0241364116030113a603a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395577347 1250 395576097 395576119
    0x402101704300e032b18050604030602030a0e010603170904091208041b1503091a1f060f0507080a0c14011a0411070f030905061902060a0506 62
    0x8444111030040d1080b103403900c0510740560301007040a00c10306903040ca910b070500f00c60002000d240c9018407403003201081002802d1350821849101082910400503403504100f40c442000d81a030503407650b80e000540003203010401000f04101c50b000f42d0b200c0c019004042000f040014482802d80d01c041c80090000c200c003040c03514180161a0042401c1c07240a400892004955a0f401002d030b0740c00d4041c3c0d00000d10b1182403008201c0c00100380c880c3c0180291260707024a041c801c1003001101d03040d1000081c50340c1c466a00c03003004429605044204003508401d40c480c0b030900da9080a08084014241c5c3e41843d214000c14124002d01c2020300081541da50380381840140d0b60341c480d160b80600300e03010501058030360200004e0800c0d0340405025200f50004240c0300d0404605110030640c03155203501c0344e0f08201c150307404418400180e500c95600840c43c8040f0b07484508003034403079540c6900655080f0303400003196a4410304040195040c526581d00700c4040da941e91114504840007603420310ba000e0702d0720305 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395578597 1250 395577347 395577353
    0x12160e090a02010e1c0c03060506010305090714120f030d09021008040503070206030903090405070302090f0a0311010804080f18270a0e0f1c2a030302030c210402101704 74
    0x71400e4060701d4242d00f0f8105c6244036107800700001078952085402d40d0300c0703900300600c6581c10b020f0180c000060324010300880f410035604c0c20b0388600f0f4204450259041c1881c070250076030100403000031400d00e1029207a80b040004407280207003510034002d90180c0d54440c0c2c9102c030070384110f083c04c0c411508003000d541131210507401c00800d940060074083d000e2105010300c040e2656075206150160100d41c50040e0b6624040080c0712080d00495440747c450b000c050390400100b203400341c1e0388041e05403d290050469132030b803a01000c1d134041c07091601010319010034503510601110b22070b40d450200407201e95181d140740b000c0c80303510f14022201c401c51400917034021414283c401e410402041010300305035009044a8001e1a141800300c600102c0d8909035803840c1c540303440e080706040c0c4107203907010310013040c650f522403000008002c5010000c2c20154000001400c081c440c9007a0794136090200c202510341540d00700030030000070007650b040c0e22800c000800810000d001d41c52101c5040091707044c0943c16641c41d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395579847 1250 395578597 395578609
    0x10e09040b0a0f06090f0501170d0801050f0a0e0c0406030609050c07030309020a050312130509070f0e040b09010603050403140310140a1e0806010905040309030204090212160e090a02010e 82
    0x140c0101482512060b0205d0755400c14014007454044140300021290f14107009000041844040000c1c0d03600400c91249100303034080c590340d040d40d00070703905803181024450101e4110500ca612000d5261400418005180da909004204481003582c040c00141c0d1a444090200d90081ea404685901301300509000640a600301e14002400203051880c8161f984020904019514144000340400040c00b80364140d007411880c00030b080103645000c06840c2c41c03103010b4444000810000b092018420305000d03039984a810040031002c001d40a41601d50f550440074001d01000c0c1d4049010440841c030440840540c242644d100b0030001a03a0860b13140b801b0140307038590716024000354011010010128a00c619409003d80c2c215052085040a80c030b130080d4a800c203030068001e98042804e0000b0712011070b0740121172000356a01204c1c005403007102c038800208450300341d20f44003000340103000c0844608182240560101e46440c02d04160554880c2c1c1a1a15001051002408595014100e00d1a0700f421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395581097 1250 395579847 395579861
    0x101202010c14100209030114010f0501050c030c0706032c0c060d0f0204060c21090b0a050c060c09011d03100c020f0109050307062d0e031314010e09040b0a 68
    0x24031421a912140c0c0d080c0c850070200d40c0c052103400f01c0e400290900da241400d200ba100b0540c0113440001071941450602d445054986c030540f41000808941840801300503c00c503a241408801160b030140c0d0703107101c090003400d060f85490b14000e04aa020b10030200ca848c4421007403039410f20240c8250006041000002c1d0011040546c2035039549a0551541800d4402000581050345034074541c102c1e141307003403500f450444000074240303607198844000498020383c00c00305903003041e90010b4641c61218411141e41c05100407440c0f00f442540c0c1805000c0c80c944000b8115000b080c5d035210344a24084483c10303d080540c032006c0ba019800309891002c60355855000c180b0a00251050380c17110070040303070640e0a44540200c1030382d890b00006080410800301e80308200040c40d10704800c1d07047e00b5245190702d841c0314a8410240042d9114061103802d80414011258006400803c00034026142c10f80c074040010400002030215140d5005d4260a00c1c0a845040c4240e60041103542e490742e5190065016182e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395582347 1250 395581097 395581103
    0x9090705040509030705071d071d040914010605060906091c14060f0f160c0305160605010305060c0306031e03042309150105070327150206101202010c 66
    0x90084003240d5540c89014903801004040010354031005d1500305103091a0440d84149111840c266100c1d1220040100700d0b588444141080642820303510004075900f0480107819510500d4502c0d00400c00c404040c03102e10101c98507000704503464558052050521445861607404401800250241d1030b0824542181d58484400c02000f021075a8500b13000c14000c0c4558401030300500f00700242d10142e050541d911040700c030f0303204545003482ea88031400d41c20308840300010058034045000905001e070048607442c0c48102000008030429041480c000c3c0802e020449036802840301041d0000c0351201600d0003000000c006d0700c241c0010b481c040844803404c038031011450206000004e040f402c0100280510700c24041030391186403060381000301c2c68000078a80d401110ba0344891040c103036400300c1910710f0203a040c03d00306440c0e80b07030800c1c00102d0340f215004060110101840401c10b501503102800d0310351403640803a20583c60701c2c440d16030308400601818864018811352a8050740c41074000a0303400780 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395583597 1250 395582347 395582353
    0x4060e040902060d110d0507211505130f14041e06060e04030929031b04080f0a021003020c061521011a0102030f16020102030423040e0307110909 64
    0x1504e51010242c2e00301e195420740d040c4010651071202c400303a010b450340c020701c80e103004001410702c1910810140d0030001e1261116948502e00403401c0f02c803460143c054017004120803042035580c503602e0041c0c030740d0000b444001707070030400e2040304505180610b500859216890705084101c03005900000840140d080c2c400d01c0d2076000c009020301d08061824040c601994800107a20304050125009001d0305110700a070245408031030040c0c1c0c250303000780ea40200181645403543c1000d0480c7c12800c2c020f541020105000d0000694a207850002d280c0032124401d40da2940c100306440e400b40c08038012114180d40541100700040c5070800004100d50074040024085051014004000a4103803402c0d50210303080c1e03648407401c1d440c202c280b00c040d0b01181d07401d10044d403602202014415560060410f4409d503187d13050008003c581c004d001341c9000c0d00404218194102018503040d4032200c9000569000303902d0210390201c80c10001c811a01416005120300080c10390384030074403206680042108040e80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395584847 1250 395583597 395583607
    0x21c0b010207120c0e150d030806030a0228060f02030a0c2a06031b02031204020d0f050c04050601030212040b0c0d18050d110601120f0c061d040204060e04090206 71
    0x103082441c034841407805070720000d0b1043c2c02d0045400400368080d28542e0261407900454480d603459282c7c84a0340740d45450100c1285c0c898002192900c0d0103200025401500410000010a111a98542c144010060b5265090341d0b650040c0c454003c104503100058008215015419000395207072002c1502c908a1180c40c071414407001541034401501121400b940300a0402c030301c40e807501441e21889110400e54034000c8074617402a40e00c1c840d0706080d40410080c3e0b00010159a9100365120705150409400208018107140ca01d84a40200c002140318034640804240154400d1013a527882c0d01d03407038080c00015103c17a1100407035410000c000d020803078010800c0640074045401003244010f0b0f5101043d4480d0328030300e402414107800409880030040d182c4100203000704000382c164119400051551030001960900070b885030441500078045201c4d010000034010350080c0045001e44150314040c005141c4442000b0681c40360f4404c0320001110301c0c45964282c42d00c2d07401448007a00c001c007494580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395586097 1250 395584847 395584859
    0xb1027090804050a120605010e0c040504090203012007172b0e07060302070507051e1e0307060809160605220f06052215050c01090c030b061003021c0b010207 69
    0x131102130700503140701642150090100542d9002d4140502080f41000c082441c14000b0145c10780a1440303214455500c400303004003551029842541c2c8440c40c5400e00d10700e0400c04920456079030104004890000d18010b4072450480c012040c1c852401c11100501c060030250450f18895901403120400a2a640d54501c00749a02c10003600c4001c016585026846540302e04010342400c14540c841d500440452060101015014004180f203d8044078031480320b2000901042031141484042605032140310b001203611600008014030038400c22040300c03400310b181c3c001042003084078400d68020900501c03d0307459140010042c0001d55024a1480002950b105040e00c4080c040c0d41c0001d01086000510004041e0680e1b444002d940400380c06810f068503000d617904c2c1c815203031003595080000209018200b49000e4010b803541c107421001d2590841d40300d04203602040e1040d1089841000c41e5810b200e4224064000d0303e02c0b040f031007a02101610a900000800b52455001403411030094007804261 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395587347 1250 395586097 395586109
    0x9060d0504030e09090d110303040807030c0515010308090906040e0601061409150a08090f0d031503140c1e0f120102040305070b07021003050f0712180b102709080405 73
    0x100d8061000104070502528001030f003500e151f20340103101604100208400f06155804844080d607151034540c1304881f05003007090610303100d0046002da0841b004000024880740c03401404081d00212030468a68450f40c0800085458040a49469411040041000c0381c0621000c00c1140b840c8895030f41303080000340001d410141aa0211540490041000d001e01c652000e0740e0303503004903000000c18020140144040d80c540c0801c100b041010740710350721005010300540c9044001c41e408440c0840074180200b00640340c8080101c064090f84c1613035809880034249003210740c0400c801818008600510105001c65000005416002907408000000004604000140003880310020380c5071a800c0b107104102d010300c0d111114608050403d070a0100429070352001a400010708d04016030808102000742025000380ca003101030302c083c5c801c510004d10121403603c038852501c4200413543c064403448294601803010303201c10304000001c0b407050746200c0c11b40d21500c0324070301808081d42031559a00004503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395588597 1250 395587347 395587351
    0x901020d090303090501061205060c0a1b2114070206030604110c160510080106030519020c0d18080a120c0c17102a05040b0703031e0209060d0504030e09 67
    0x100084c3d0711303500c070003d0001c02e208000151680c0c1c21605032858240e00c40307669a02d000f40072420041c0300002c0302c5e0081401076075061112070340358501000c1050f00e4240020b00c404e5107440070311000c2080c030101c0040c030301c039a200905041c01550f0386800c01c4d40680a01500e90001007034560046c0d070300c10b00e142c0c2040e4504c01414103a10900c00400c5165010040740400e00e0469124070701800f1490403103a02103411903000340c1035a060b072400082d1a80c1b8101555070b194510000940806c0c40003d54111299000c503000b0450500d070349070030645e00d1115000e4100218103216038075454104e00c2152002031103007404d21249801c1403800ea90303141450b80326402149881e41c00941c084081051034502000c040c055036103000c201440400a062420380002540503805c5102c2d8146511a1003003812980240c007550301504249122607100c1c503071351801030000c00e00301e4240d0009000218000110b607805e402120f00d40e590180106080c80d15001500c0041c14020b8012070038410500048005902c2d1084218 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395589847 1250 395588597 395588603
    0x31911062a0307020603070c0f020a0312030605010e0604050d171c18020d030f021f0203100509010303050a08060a0b0a03090615060903020613080d0908011401031a0901020d09 77
    0x440030351051050407818255480249542050029001690742c0c201581d070320910b00d042c514144089072400701c03a542024000254030400c041404814040c2c900608820043c1d6500d0030000c05072100c0c01902e651007501c02240e4801c408200522403030400c00941c40001c0c2c42013022007002100b1440b8812641c102d0140d00c0a10903400400342c043c0b2480d4041c81064110305c142414800d070454001c101a101450009000e20009180e9414907910802000417500031031590400404800b1182001039401600c070059043d4012601080e10301c1c103030400e241281d42c191111740c58041165800d0700d403031900401260780409280d2001505491031402010184429030700000c0742602ca142a0085991009008840400d80071003481069080300b50318082e00d030100d41550b10f0b80c3d4a000c1003900d00340d02c0e030041e0407a80504114440c00316007143c0c1c840160ad11490090150040104c85135880c00d00c240b20180c540e40e0000c00a42908240c00b1040c1d410031101c2d0005840c21135240070000550340425021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395591097 1250 395589847 395589877
    0xb0a08010203060a09050f1329061206010b160204021303230c03070b070203071a131a04090f06090203100503070803180111210d0b0108010503191106 66
    0x7001c40d1414030061380c003501c444441040340342809500a01d2070304000308401d0403414044d1004003806403d02c5031850021805104011815038114008a008000c0e100e89018100007501d15044480c08100340d0b041c6c2d86a14501401c1030407865900040c514207401c281c1c0c000e40d08008014429104a03100c40181d8098000c0d20710b1410740100d0001d4562241407503101c01e40010f00220b286030380200311101107461880150f03441d03c030a400001d090080c0b503403222031032045407800c005004c00044068402100c0c10242c41503020307916207503122920b005014100c0e40d11002c20040c0020101d980c80700198118628000611075107070035420f41281d1082c3d030b40003c9076003103101c100598502008a40042c0c101d580c061030900c071000e100c86600c08404a803031414031080050399250140c04101c1071200303003d0f60441c0300c5007803152154404030394484088034007008e0601201030229405048800c3c100c8201900a01c03c503000c1d00c8559181200d500000c9840e50703403034080c0d40599a07030b1030040c0100075611203030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395592347 1250 395591097 395591101
    0x11010515010e0f10121b02060402100f020601060f03230907060912021c0507090209040606030b0d1704050d11040c1701121401090302010b030c030a0b0115030b0a08010203 75
    0x50900c0b40486101d0744101009034143e041e41e182ca00032401d101220381031403a068415200c40202500d840100140503155207034003041c019a0001e50707540502d0083e100e24a28190b652011548a2502585440542e102400401201d44290600c11170a00b403071030005000e0100401d84403010441107100b5840c4d020210038402e500c003041c81980c00030551800c1c01000f29103003030006140c06402c00300182c403d100b4101d80a002458913120801d000b94404140c6008940f11901c0600a4200455060280e442d005c0302080e5180284280c6404200c02014001c030790b45140d0340c0e0350fa20101e0f201008180d6805000001d425110000a004100c0c402c0301d80081529400c000c0c4001c94641801020400c10400000071951802c0200541520000104402460680d00380642d010100c01d0700007000e580780031003034400c0c9941035101e503010540072004d644d1800c02050805542d002c0e048409000543c44c44010020b29201c10103000201149003000700d490542d4400144201040d030b4048102c0381d4001003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395593597 1250 395592347 395592349
    0x18060a060f052d01020102070203030a08072c040f180c03050d02061012021801090b090601021b04020d150e09060c0715020304020d060615080108030a0507020d0311010515 75
    0x7000c000a0142a00d0f50140780d41d10304000d00c4000310356010305058034007158180d0040e034404c0d01196034654018044a030781d4203c0d07020042001100303d611000140f0506514081d1b035141c03039030100b003000c82004541a50b4100804000003000030300b0100c1c1c10369503030b020592007400264044152040c002c401d0003048a2440c1001c504255040d0400011134012408200c01c2d03011145001003590b0742076201034a80051440403c8981d004d6a800180a0341d040000140d0301a1035000900030724425200c0e030314691101001aa541c40d507411100004050101a041c000c0c10280d01410080b01c41c0c5402007010503103994585000c0342c254105d25542840300040048402c02086902d401098180c0381504d000440d40326480c0012500c0306041e070b130a400101040030343d9100310001c080d168200b001000100d6542c41b142c3c10304103402162001054020000082650010003a2440038032640c4035213240c0709071a820441c06580f003138000c505001e140c510000002400344a49441101603040701243d01c00c03807038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395594847 1250 395593597 395593619
    0x12060d050f0f100e120d020f030c0306010201180c051201090204140601080f0618071112130801090f060e030427050903091806060f0d0609060b070b040b18060a06 71
    0x3c2012500380c1e080940c0012901030004400440c03a100040c40c40d190404001d2040181c407901c0300310000e4220100038402008010b0700158041d0304240c00801c6183c01549490848550f0540d016014400c4d40104000e5401c1c0f4160f42e4480e0b105440000411025030b41c0000c2c01c482585800504040503d0300f00821542c011a10940140300285024140d2802000040d43c1c0b103202034007120200079a10228040c90300070241e0503210405c034403c0d50002d8075090700810441c0c0101c540743c0c00e2801a1000051542d0062141603180384d0003002c0390b00c80303813406c0d154040600805c0c005014a444100000a05c19852020092a0710385140c02c840ca01d644090b1114180c071005004034205030070400c154119503a030b0746401c240c41c1a4a030310684250b5512400100180580e10a5242e02c080c0001d654a4035103990f4010b9040d030300d040720200b01150315680740280c1030042c00300082407003141c81d0104020803201d881e29a8000031220a00307408400082c0c6e03103800c040c002c0e5000b106140e20380030188070400c111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395596097 1250 395594847 395594863
    0x2030106180803042c13050d140f07080910050405040510061d01140f0c0609070303090614040306060902030901272004110a0f020a0812060d050f0f 65
    0x40c0c0035040c0c100745081e0b07200d1042d4404d031180b608545c284196405150940c10f00807500c04401c002032444d01c0040c102e541e00035030f50219103d00441c0d00300fa15440c0181da210490360065007280c0d06140d04d00300304c05015442100c0aa402003010700c5410708680c1c0d01c290308034080400da80c0390340d103541c40c24080c0001d4800240250007070381d0307822105100056001c1c03500010f6030284030142020815a40060700c0b030030480701c0ba00009080002da1855903442010041614500220480e541c80d0780d10302e111600e42c002808020005090030a08014070340c0302d50209088603810501b120b180070340d02c0c0c0e0b40504980fa194455400a82c000c020030001030001c0c8107075043c0da50000d042c03424140410102006100400c0001005051407200796000743d50300e02401c01010700083c00070400800b400848071200d80101002500092040c2a04c80f0b1441c400300b019041c282d4400441401e1051403e42c40e0060030000300308030b812540b00c03200f103000701e0f108001c417001140405e400340851501583c03a0904000d03072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395597347 1250 395596097 395596127
    0x80c01050c070c122a050a08010b120601080a03050304081314040f090201140a02030d09030801150c050d050c10060b030109110304050a020d03020a06090b1008151501030f0f02030106 80
    0x20058124085141501d540ca504005c84143c0034581810a00d0140700721700581120b900700701101380101300210b05500c04100354200b00e50030403180c103901751202d40e1940709018487c034603004040c03500c002a002d04081c68101d8400c00c84036082101c1b2204c03558070303a0500d13807205010325540050041c2900f03062042904280e910802440000200e8001800714081c64180002c403c00c00603104242520900c10760707100c00f4807100280540001410024800302080c06040f00c00603d000444009070b0040c45501501503216001d445c2e4410007501c152100e4010545019107401074011603400180700b0302c101c8000e0609048129180e5040c80080c2c01214440d800105600d4003c0003804007180c8005000c194103035049410000c21403141c9822420a0085400101014200440d29040014a400c0c545c4983d1042044010040d900c0c0b100b555105160101030101d003685502040c22080704080000c903145040c10049000350030b4a520004980420004a1841c1e5000c0014007000740c0c000700c119402c00d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395598597 1250 395597347 395597369
    0x507090606031a0609010e0307030807050601081b040c0c080c07060e0d0320030906031e07050702060703030b0f12100f11190903080408030a030c0503130b04080c01050c070c 76
    0x140c02034030884032064199000c4d12403400803401c2c545030381c8036840a2542d03103406130540f0050303990380c6491441500010b4048541c1c1c00b400d000400c00200c00aa4210750f000d0080c668500c05200d00306010050111480600400041e00c00f803202241d24035000b00b03400510340c0300a0540901d003581c0207010306080d0042d5407182d2201c443e0304020030b0f804603034000114400d0a0b8500e0846018a21030300d036100315016150420000700c10031031032105d0f003110500411003460f402c5d5195a242103049449100d1000c000750b102c1c400b40043e101192003544030583c180c6010304006103c5100c08002a5400608800000203034810307414040c10b0030907800781d40140b5031680070522403441080030101a50190202d907000740583c100d0a5600540b0540704a80195000300e14181d543c0e07214980562258000140000440e04100b0040c001d207104200f1244120140202d40c01e18142c0341c0e403010754a140140081c1c50600043c409542454020703c18107004038030a010340383e507603401407921034030004199001502c196 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395599847 1250 395598597 395598611
    0x20d051c0515040614180c0d0c180b0a120903210609150b0403031103041a221a0904020f0c0d110f030409050a0906092405010302030709050402011704050709060603 72
    0x900c030b0000c54401c00601c9408980d1b5981e40303054207001c500584030400c94480c14111403061a80d0072803030415544002c1040010002d0310703003940d01143c3c07080c2e025400c00500c1c0380ea26014841d545511042407188a80b40504e1082c43c0c4406015490b129110b400c0c21103035451008001d80341c00c0d88504e00301e1000302c0c8089003015203400407900c5140641d01c806010f101680c1da81d22201b0a0600854010706241540c9604c1c400700450400d0f000d40141002e202c111240002c029100301144011408840750014900741480c0319030548081e82c0c1094040341d030043d07024042e0b038044030f41000c0585110030054008000c40e42c540c0400600c0c80c556401d100701560040c0409044510000c005c60f015548031340c101103816252040100700503d10450043e011038902200d50703080041071404000c01c24004201c0d0344003e6103074403070340341101c40a100095051784211404c2007105559004598018014145002c00c1102805000e90454044604840300e400c1001b0510002a045c030668010386140c0c90300304011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395601097 1250 395599847 395599849
    0x70806060d02010c0b09071d1303180306180227011a070206030405070924030609030509090f190216020919020f0c01060501050901020d051c0515040614 67
    0x24540140c0058081c80340c0c14166819640101c0c00341880c2540555100c000d86081c605e0300751103441c24010301307019000030004007200c0c2c03014260742c50056a603040c4a0020703000c655406e0356580c0c0d000c4103001c18514900360000114800b8070031b140d8000e0014044100d01c82c1240304002d4003400a400b0890100e640c5500d45940103001c0d141241511001c100140c07031020300381500780e1a4042c4100003075100c0c82c00020401001000b0503d0411225220820300900030030250031650444d03802941002200c15034010404150390340c00a90080c0d0007424054504400540480c84e4600d00711004800d69003203c0a01c000343d01a01d49400c000c000352030085040c08000340810340ca9084d1030b40040d224442c254041214001c1500c101c0e0302e440c3c14640708664440300e0424070600e90b0044500240f19511f030680000791035001e102102e002680c140d000c1c00e40300340a080d00791170a40281d581c034594880c542030340d5124205a40700b000d0140c054000c2000459083d80200000d07141c080d0042c40c0040007598800c511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395602347 1250 395601097 395601103
    0x5101e03050c0714070306020a110f06010b0708090f04020403050a0308060103060b090d1a07020a0201090509070512100509010b090f0409050616020a1a06010f020106050f040c2714030708 82
    0xc1c3c180d1190144080154020400c0c0c03800c0b00e90b4102410340391001440720080790300440300c0c1d82c0300c4100100b518251854a01c829440760800d00c14446407581c200800400a14a1001400c10b44001010501c084140c580440c0c203d030001e800894841e40020356413020715400c10f6405034491806d1030309102c0182040c0303a03403c50f030150668480c0140c0c0514111001c03c1003e40529030102410304052141d46025000203684440c0c400c1c00340d011509610300400c840c280401818810003041d01c03250319212540c0c108440b0880000e082a20f0b94107540030101c0d890340c40d04084c41c02025040001d41d15125a641001102d4903000c0080f449580703004520000205c010400c2d85c0e002604086072466155225002d0341030640c0044010b0909202c030203809030031000c1d0b000d203a0040c1400e90743c003800e01425180076422908640550740d440145c0410a0740c4030320709030b0022060860705140c50a0b0b640c0014084861051222404424541c8000d40c240801300041c0c900c041a4041100188080b500c0e054810351 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395603597 1250 395602347 395602357
    0x1303020c120a0f0804050f15190207030f0503090909030a08010501051c0f0504060b01020f07050f0d150e1605010801180e0703050a03020c010c08030f070905101e03050c 74
    0x20040c403402450322100c07801031008001458000403c140c0c80b0a003413405004680c000e00466104000b822040200790509940d00b80b045541c910440345424201001400e081a511440300c0c1148205600800015214241498001e00c92070040d0303180c0038020108103943c04010410303241ca0384148441032403140d20440da64110380c020300300295551203a0314812158600655621602400e000c001c4070404c1003680312910603401140108442a0140012601c030001e00742d0f060210b40c04040c0911084c030b8200504198040c0003488900c94845c80e668250514003142e0750109002c0d51044182286141844200150001410214003850620002801c0140180201d0880e0641c2c160032541c441805c1e8403400f20101d00404640700c1c16030b41d01d0007907900d103a0620b048005015030520600154014004c00c214140d02c07982d07090440c1e44480c9508140030307004010004200105c42c002070182c030342d03c90039403080c8100d5803040d041011040030540c400311180b0310307101003601d4202049080003460050311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395604847 1250 395603597 395603599
    0x100b0306210c030d020a060c050304020a032009070f020d05041a030a0204050301090c060e0402120a0c021e0d0206360f0312060306150f04150b04030b0f1303020c 71
    0x340403840e140242c1c9046042d408242d018402e11310510910b071307000103064145ca44201d0080c4101703851008101da050006650080d0484180181400003900c0009003120241d1640c0d09540c02c00c89150020750011410b03504680460143e86d0702e23111060b4140854601c1c521103040503442c00c0d14140903282c8109810003840044000440859082c68a9070101c50041070014000d101281e41e134184060410424030a0300b01003544400701e07440c0c508003402071301c2c204000c03e89000b01030f50b56003060034050404001c21078114042c5a2340c44007102c420054102c2d6140d0900001d01c401d8a20160281c0f030041d001d0110024429060700c0945c0203500d80c0f000741a100d880410447c0300c054090051454148c000704810a980008518a9861005034064a00c145000c5048031055203583c603d0303600340c5500558440c2c204990038050350282c1410340019045540000c240f10700681e544850031290340098004541c50480b410601c030202c1e424030b01f004c0d08050704076170411549d075103560080e40c3c46007503008603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395606097 1250 395604847 395604889
    0x4031101080709170304050604060e09100b04030f02041506120c020105060306072d020d030b04090203101d010509010f060602060c0d05040305121302040608070303051e0405060f03100b0306 83
    0xa01d10355131341481524000c200103003403540ca6680701c042c054901c4840d421124003421108000846000700d60000500300c50000176858a040d0954445186187c88404140d820948415110442107115040b40c40103200310303070354004d51074148450142610340704544a41160b0410007480511343d004110b003508400d0394181440d9002c84041041c80302e1413503007152006c0c40002e514403407100d038010582c1100302c0310550f010403007000120208401c442e020030b030194142d40a1b0b02c0c1506c400c2e609620058070700101b9800c0c0000108001640c0742594000c8924000b141d440340c0c0340ca01c13524100c0c0105805805280050008c52403c035001d954075014100303141c031105840b64046428180600200c40e070814180d0840040e914000c14241400100b41a00b2800383d4500040000c0490300801c0c20000d8aa26070f4440d403400d0300e203c1e205403844110030042c2c99a190308010005643c1c5e00c0500400c544c52441526503140c1c9012000b075045c45995034004600401c04004015565440f240b0005e201c410b00602 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395607347 1250 395606097 395606129
    0x15050f0c093003030a0603020102120a020c010e310b030307020108040f080d06060c020306010f0b040302060708040f0f03060b150307050c15011706010801060b190512040804031101080709 82
    0x140400500b150807404905001c00814000d80005a401440a0324003c1e0215910012021250f03503140c45038449101c0140c000d0710109000790720036808101c40e040000c00524103031020b03d145c1d00c0694049002d22034800c0355401c4040c486031950051300c000c080c00300c01035400c003241034001a0551500500c010908090005481d0030003c0d10f00030349045d0610b4080c1004a26210709002d0700040050b07000b648039100b101c00014041655000c030b00151505400014145440c0d9828440c09400c5400e0465900105001c01304180485240110007800d14008425055156041940c06c80b0b41c3d401441c0c1c0101041011090395802035800c0f0390304100e5500d011940d90a0b441003c030b040c00001503417a02410003400001556480440118848231504d009842c060f90707903400d05901b02c5010740300301000050f062001444000e916191861284007504089140034030444070311800d164210703000c071440003010805000740303c161103000c2c0c8110030a007810700490410a2001d8a40103151040c280d0300c20403140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395608597 1250 395607347 395607409
    0xc0a0516140102161b0f06050a1403070504032009040b0414010e0309040b0901030f0f080d0606051216121104030807050f120a0c03180315050f0c09 65
    0x4150030707007240380402151280c2034480038200e14180408242d400500191802528030880c3c4003880440e00d0502e50550550314040040d20b841e00326101303000a0106850301c19506000c0d160086210308801d540d55540d583c15894034000e20490351009040801d4004c18410035612603200e102d4105400000a032071035643ca10300310782c204078880d01c250b08079400d002145001c2070001000d407407080800c5030b09001c41c0288209000342c040d42444090214604034201001292950500140090203114201d203400c1d07486072841c4c02d90f8541d9102c8400980001002520103201116403504003095030b5000c40d48a00c5003100a00410030f6035150105140c0c1ea103a42d14000c41d44d00105c40081d0f42c00b0701840c0d00c60a040c1081c945850500c01044220b000e28002c504110241c0001c5407030045540c0c40300c110303585151f28116aa1034128175400c0d000c00b40c080001c0017090048103001c070043d0740302d00c02090b00c0c81d1940682c40e09000103458078034040c909100c50b0795141e17229008004036001c07400c0e02ca6000b4501360 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395609847 1250 395608597 395608613
    0x1309060b01181d220b0420131122080601091b0e030c0a0e090118120806030c12030a030609020408030708090d02040e0a05210405040c0905091006080c0a0516 69
    0x101d0300d106044540b020100100c000344548035034014000c0a24000b0038050210201440342c010076480303001c0d91807902342d04440e9807056140711b07030500b1224145100303a070110014000c0300c0034401d0100c002074820411060304104003405070045a0f0284030080020501c03604500c0391800700d41c00d014030100f40300306980702002840c00c0880010411090540d442600c001031880584500e55617508000107044500c650207944001c044d40083d0455034960307040303412240c0c2800a0f116903803500545000c00620707039a0f413281741d910801200c040c40d501d03045610060b040781c00a500032402c190046c40100400c280c0030080d50300350b907000107071566034031440310001e5400003c0701c0d00290b0040c580081440203110000d01111710b81c0c0b04108561849400e901560104900321900f050400c0d1304000c02e00c007508003600940d0001c1d11a081203091181ca520024841400c120f40341401c034186001c0c00c1220940c8446229000403042c0c030309619103900440002c109200d40712007495071104500c60281000150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395611097 1250 395609847 395609881
    0x604150c0806060d24051203030606040b1e0f0a02060f070806010507060e0106080f0f03070c12050109050a082113030503060a0f0803030f06040203090a02040b1309060b01181d 77
    0x1c0c00e117482c61041143e00088486070140180d600403c00407043c6600c80300b00104903405460010040c906142c50220303142c415900080800341c0c0c0c8850310241107591600c01d00a0400c50017200985a03c528450500030302c4e000e0000d010f0a1440104020311103401d0f00031582c207400c50020320b003090f23958850b414944042e040710580b440d41507107005400a00315001043c01e8044140703480c181e5103d01108903c0c6981c9008001005e4943d01d00404c04101000c14410303030340a010b202d9000407a03041001d483e81c0e4280b10a000081d00c00010014200b2050010706480d40012410102044603a05022101c0010068407000040611a0000105241c0c0d900d58032800002d10003c4550100c840d1a10516510303908240e4400b000248140081441880c0500942e4440c100e84001017010030b00f03039002c120207040106202a0002b0420580c100344842034010000054099000466041313918800109400300070b001c94039140000c030320b06000c010244540a640798000311a828201e0b151403213211044141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395612347 1250 395611097 395611121
    0x50309010204120506010812040812071718040b011b02040b030a0c1707090b01020c2202070c0e070804051c02070f15090f0b04260d020604150c0806060d 67
    0xb0f60415403c0102c0090601e040c0c4200c00b09131540c180668020f100c8038002ea0003224840d810004080c0c0268210f180a0401140240b4100110318451a02041d2960101d43c554038440740102c0d00c80418101402400c000700002c1c07a0101680400c2c0c2541c1c0360804007010024401c46d100c0401302010f54017000030601c01a0440c1500004030760720200303884804451140418036000360680000c0c16181807060884820040e00982800c40001c0d04110941c044814040040b004d8203204448001e19031007c0e0988a01c200f00c0340364030606101c4041e2408a00034028810000c0001c108000524003264a411002c0c0c80c2d80240c4841481c100143e0400c85c15402c80c0c3ca01002d50b450000700005210400014003141b070700c0b8044603a4607155803144075401030080040121003044200000300c0040d02c1c0c1915688500c5219080e0000400324604040180940c1d40040c1d001c9400e000900c07010540803d2030712004242000034100403039006c1c040700d030300a10f054414a03022408940945864110050140c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395613597 1250 395612347 395612369
    0x2003090f030706050706111207050c060601180306020d0608030d0e10060311060f040509040303050a0c091a0c01020d060305030306090a06030203070e280e0f01050408090d1e12031a10050309010204 86
    0x1802e107030000d160741c00000e124642f922525001c110654014000c074412911090000c03d07405007544c841c5170180d07000c07002490328503969102c0000c00d00380030b0015000d45014443c5c0451a42c01542c0074a1910342c00e003407554046840c00c03108100007102030410407114030040c3d0300d268445444a60011380350045900090b04000340784200000c00d54580c0c0510700c6070061031802c001e0450f880b0000c80c0c0c22980c0d80103182041a00624112902488070050404a0300303440006d440c060400ca0410241c0f0219802110300c2d510120a200c80d0b4503203600016071102c00f2100801095280d500003940c0c40719248103917040c00d9000e1010503110b80840d148184010760541c110030040c002c00c5800c0740209007000ca42c89207030151400308041c01c0418048d04c1e00964202c000c41d41041a4241007161590550f40111281c3e90340250001c0c0041c4100001e684041c00340c10014100f001c021800341c01d6078480303c074170307034a690500000c0b20817a03403014040a0900841e1401d603407265152040c030760091207580c001041c0d0320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395614847 1250 395613597 395613601
    0x1602011b0f0204050106021902010522030b0a060503030a02030d09030512090f011b080f070c0b090106060219080d15090905010b0f01021c0e012003090f0307060507061112 75
    0x224544034840301d41403080d182000a43c0c0e80b85801c0341c48a02540c91034076600c0e10004031030051362060700a82b02920300c1d040041d481c0100c40c55200d000c100c06a004803121004081001400e101a01c103100c001c04c0240d020b50302e0014110f00c025124410210300500c100c0d47d800c003800c2130500c03900503901c82007094002c64110b420a01c400596071000081034600d40c2d030078000351500f2410b0070440141041ea107903c9034074131a19282e80c0c402a46070000e0a89003041316401d00400401c41903041c1a01074036620000052007030a105c402401c140d50917007800381e0004038110340400980d900c001c4441e61a01032400148040d000d1380194441c441c1540b060303a40b103007070080a8080c000c040d4088000c000d400c0341d0044808486e00300581e03c800c12000c500d203098284070301102a45009103071440d8091414503285152002e642402d60440024001d128456800406e90504034100444824248003044004225192801400814500c20000010881625096000d2400c41c2030000c0d0798549c0d004030300d07a00e100c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395616097 1250 395614847 395614853
    0x50105033a0c051b15031306020a05210402011d01110709150e13140102070b0a23010e1302011101050a02120c07150e0c1e030706030b061602011b 64
    0x384541d070340306840e10301030b5103c0910000b078007044c880f00c8100003920341c0402c4013030007103401c6042c2c2000340070b2032400c82514060b0001552620041a1004a0b91500e030b403580400d45100c1c161060404610703401308045814032001d41c0e0882030100c1541440032800303194010b03280c012502d18068002694a61064200103c0d4040b4a030304860210800d6072a45100a0303965080e03000102415201c4240e0304540402c0300000c1071f03c5980d0030301c0041042e4005803805449550340c51011004880c1c17032100f20384d51140c251061410230300c1e03903c520380e180c02c2c01ca2095040100c2c09650360b5014050030001c0d04506403110441e4098a421a2040c4080f00200a03915043e003803880a03500c0300d040d4040030381c0d2040c00200500c24140c00c0d00c1041e034000741c00108004a1009003402402400d90b105154403540700c01410a079280c00401800c20000c550078110f08900005161034900990081d000340b50500300c11802c1ca84881c000da403004215030020050f80c00c41400165000200b0048032903000000c1d0040710b0034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395617347 1250 395616097 395616107
    0x3090609010c02030d08150405130b04170c010c030b18010e130501020f030f07020a0503070809040e0a150c1b0f0f050f071505160b0907120b0907050301050105033a 72
    0x10900d21401044001180c5100700300440727204036100401481d440116401140710741d505958450700c544400305003d0100001c0c407500307030844200807c46a440b420290031b25a4140180302500109a0740075454850700b08a011800c1814040d528440710f80c20002190f8460315041c0000d02d45e0484021540c400c4d40030a507141c039500c200c1e5171045201c070110210301c0c01440081c240019a4002014500341045503840c480954060f040660344243c0b1041185541130041c0452840144250000a41040170300d0140060728100b08100040c080411400365400c040711603071214032a80404c1480c903a105618103001c00c0c201c800c40c0a0014401e0707075903c1c03e012034009620016980c13082041c404640e0144811900752150841812021038000e6603403000603100c0c00240d80280910040c3d4400588982c0040f001d080510801d6075100c0611042c020b501805010000252070164000c2c06a0b40c101404640d0300e910034407007101c0427130074a06803078203060044c250b5903e050018840d2040c406800840141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395618597 1250 395617347 395617351
    0x30f0207051509030f0406030b0d0c060f030507030b0f04020304050a08070311060a11040e06030709050c0919080601030b04050c0d240501140118030c030308161103090609010c02030d08 81
    0x2c405101c400309504001c000305803203640113580b0034146400e042a1049014204800e0300c03541146100f54000005040f140c0000050725950342e030921040d41246004040d40c5028101605040c6040b4003140b0b0f0b030310703015030f0283d004605550159407078946207061850046035a0004c1c05031100869442d08069010030311000490441c002c442a503242d8549a408840314824110000d2a00308401c2001d0011140c80c0d5521207802401d840c40181d4404417202610802c84481d009001e000541400c1413800103c403454942c0d00620300e8401608080f8010b030b8400701808060401501c4c140083e00f0080c0c2001800649c00000c1d00c23818401010f450300311500c80380c5c544110310307103002400358802c00300382842424126203002d103102d10166651401580c2e14900484502c05411540b503011022490451841d00194441d60711041c0c1d524100d010015420300751843c01d4200708107a01c100c4210500003069820a0004403001d564903814070005840b80d44c00b00c1c0c2d009415005042e2403603c0b031600440d00324 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395619847 1250 395618597 395618623
    0x12070206160c0f140d02070503100603020a05221401031101020a0308040b060109030503030112111509010e0406170105040309170316060e030f0c01140f16030f020705 73
    0x1905601c038940c030030400d04810103854000400840c55000407034040c1941000580c00340b925184420f611480ca207081003012030088016a024880030802410104254501c000e4040c204005550441d40080c14035511846898869200e503003665007100011a1190740b0140905e00030002e45602d011426080b4070b0074441620040340030000c6000f1540082540c00960781d15075100c00499450340d40d10703d410b1384090101070400c42144e1001c000038008000445c080c0441c5000795100b0001c51a0401c001c5c1c1802507518000c403000c45298010040301001e8949800d000d0070b04c102c3e0303d40303900e0114004104a501c208010080703008409007000c81980201d02440c080d50b14a02600c0c0ca0f2205009240f00c1d04801d04160341c4100490048003141c0716000d00241e100f010003142c0888030003041031542d04071340c044d126a07500003d41070b040b0140034407488070b0144032000302c00f40b175207410075603061030a43c000c2c80078158000c1e5021042c5143e110380d2000700d4400d92280e0454544c500390030700c1350759841150250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395621097 1250 395619847 395619853
    0xb0a0c0204061a0702120c0301090c03050607020d020d2303010612050604020c070603150e010e070207062a050a06050c04030203070905090616020c03240a110405061e120702 76
    0x3c290014003004810300c004251000c140703008516824010151200c1c083d05400f401040801142564280501000300d4044c0c00b48090044c1507003880c1e0b041c414050404020f40d4810346000110300e0b008201c40d9903c00c03580c180380d070400b002c5c81000d0380d5500039210169500300c0000008281603400c0418402c0c01340e1200010001781e9122014001240701c1c100c00e0103180d84c8005010041c851003034010400344282c0c020a00540d590300c003c14000c5800a0b00701500c1c5020304801c20500ca54104880e1004103210b203000030904111804044903440d0800078401d0100d4440881c03c1444001c001100c04164040c00802c49898041c1207a1280e030003501080b4880e0186001c00640042503004241c014a8800080c00d07003616003140e00c405111044001c01c095000d400c2c6103010030358050181016202404518410000000402c03d01540000b0401400645481089040740d5954025035083d604140c998640c3d401400f000814841c08003902940c40711400180b40b00110500300540b4007e051980807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395622347 1250 395621097 395621099
    0x50a140c010c080306060f07020901091b0201022a0312150102010e0102030906010e13150203040b0a0c0f11010209151321080f0d022715030c0f040b0a0c020406 70
    0x110389601c14480054000f40e801c0c000700380186841c400501c0ca89034034860b070525082d09075010a4050809900008403265164250744040c001d8809400303400700140300031450020320340324117903201c0c480d41c680900b5540000c0380760810a8040040b180307924131320b2940c10303101d1604240d6007050101800004c0c0c015400d20500c1c9024860500981c0e0080344d084000d095541c0c203100d15243c8015004103510260300f207001c00000842c038029000e240b011003c00c400742e900e20305810000c000c1680038254038401840d0100340740e8043d0707100050f0390510005241a4048141520b02d40d800785c00380e80300f0306600c25660703100c82906c00d440c1c20080007454210468801c1442d6242c00c419800307a892120107080845000c215000141100c0003090a901040c1d42241040c8400a1007422a08a0714a07095a1102c0244000c929500c04140c0c901954044483c0c0400c00d1049640803640d00015000c003c21881c0450702000d1100c1206c141c5000c0c1502009003916001d10602c0284030700364286003030313001e50300d0004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395623597 1250 395622347 395622349
    0x609130e0f0a0b1602010b0904060515060307051204230307060f0606140c03040909080d0b040e0d20031201090f060312270b18270c0403050a140c 64
    0x5a00803019070045002803042ea280e00a20115440013501d440441d561900c0300b00c43d503076655903000e004a0040c1000515850312071401e80310340000400c0f040c404c0005104012109a0103000c17100054041245400c060700c2c0c1d407a00c03408862038540d4160301c070440504050007254000003d4103946009882c10300028184042e000c3c106c0303855000e26070003d007805290801e580c075410000d0115410303500071a07140640c0c1d40010380880d1545e0300100c5038400300040d1448010240c0c083c46601c030004507000c000b203138140b84283c1d81e1040700d10050410b101c400220b41d01d9980c2da0100380249a090501600e544040c0300d2404000d00d1400d024500a05140c1051441555450310900c410343c0d0f446020802c1c8040380107000c4d80c3c0c5407621a80b000c02841c00c0040520035120040e9500010407a441104d81c8031107a01601c1c01c070301c02103050024080d52105507000c82500c072051030301400401d640c214810341d4a4890f1031007503e114540018001c0d10464507010b0401c00900404924298010269014000520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395624847 1250 395623597 395623603
    0x51003020f06161e030f14030a0b0a120303091b060c081c0f0204060f0212030c0306011407050c010e010f1d03070801060e06040b010516110609130e0f 66
    0x2000203900191000040311076400c00c14000c04840040b4021034410030040d54a282d42913a40c48140703500e419021880108141e000b08003074514074203038203100704481400c18000c00030b400300400840e1080d440e0103100c0b109407200c81c006405006c0c03c541c40815851907040140240005480880b08240310002c4070369259030040c0d050007502d005070b540d2058500d040d10780b000c064005901c40825140c00003000080c0d407070540304e444044185071340056280c502e007640c060000d1030341e001000d00350741000d940440c10300c0840086a41c4200038144491b02e0b03485c2c80e80125801d450703404941c02c10060004100c07081c80380008500b0b0342000240d8a4a1181d9818801180c406d0000d0600c103011950b07d900524007103000c01c810000603940a03086500751961207088500b983d100381c0c03029106130091002c5c00010304080c082e01c2a40402800e10710f180003c00e02c02401c2c0c41a0407440a4000c0426081665855176600100e8140c0240108030799602840910004021310001c20802041e00c2183c010060011000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395626097 1250 395624847 395624849
    0x203100b030408090112060503061018020c0304121b031a07050a0804030815060a030504060e030306030d080601032c0c030607020a170904020c0d030633030b03060901020d0510 77
    0xc901c141130030044001950050340c0707401403016107171310b07a03d000c199502c3c2040858401c2c2059903015140c2c525204c1102c0a44444510410a00d0b004000030241094008111011590400381499825415081641c2e40d49410105c15581105100340002403210407582c00541c0c81c580f0b2036600d081d440f4100d0070386071442401034a0380400c54140c00500401d029070701c11580902e251181c1c10201380d0310b8000032034541c41004d015002c20745c4c2d0000e00c01840380c03a208030b0704512a03180043d40346042c908002950b4440b03581244003000710481c00102203034401e80056000c0e11685030f0300030500340700301e400301c4001d032000c0c1c1001403a1060400c4065640340025000f8000c410700e4001e450751459503140c045015421342000ea400078810000d03088152070b181700510040c1000300181010602c170900050554080c0e038840c05003d05100e490303082100c14240750900000300e43c3c40700240f002440c00258007401d44a0404c035818020142085101e42d0190010203405001070030070065582c4001e244501030a103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395627347 1250 395626097 395626103
    0x50d05091503090c0a1d0901060501050405060c16090903023703090305030304050a0c0b040f091e0e030a0f09031101030c021029030303042004060512010203100b0304 73
    0x41e40ea003018000345900000c5801240076001d54450180b002d001c1405000c60740d220700500101c2160720202c0d184070002081c2c021000d0340080c44010700e40b4000a03c14010b038010140704072800150428654000c10884c3c0c0310b00944000340c41107a0f903514a800090501e01d00c1500980900344007a1030440400da15017890301d410b44068002d10800500e0b0590072850382004a041c00070408021003c681f08001a61045101d01c000380842c0b4a0f9103818044008682d00000c50803005100a1044804a200e044203a40c421070001414902c0c01d500c01d0110710304041c40200c2e00717140c26907480500c84088000e103510345142d2241d80894407c3e03542250341c889507201c090200c00e41c0ca0311001c1558844d4200081840941c411102c01d80c502e29110002c84105004000c40031091220300345090038034180c040d01c03408046000e5411403a181d2901c3c051040003031003800c0d042e01c000b910820780f552140e024801a14000c4c0825802c0320300c04c40603034001c2d48262101c0320041160000003600b0003268088030310480e8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395628597 1250 395627347 395627359
    0xe07080c0a1d03010b0d06020d06050a0b0901120902060c060103031e0c11031e010603200d020405100b040b0322020a030b0a020f0c01022101120305030405070806010b07050d0509 78
    0x480380c058407003003900040b1a580c0b654a034440e0b00c040c0e03075407034241d00145ca0141600685d6290f01608900441c1d066a11660154020301010010b407c000400c1d40d441c400c003801c00b842c4128400320443c00a0446030380095006001060114a00800091890503603109844040c240d031403102071180c48401c001c007074200068860404100040003484140007882c0007804403030140c0e000c401641041c0c002911504501e83d5a42c4042041c80007840741100c003030b891002506104084580410314500c174554012b8000d80e1680040f400e000b801400c0c0b50010641407103c80c3e2600d482e20340b102565442594100801c000032516803406401070980400250350041400d02690301d103503102100f110001b80000300440d0700303000c0030350b0024901e4000c048002501000583d9511841244090158201000c07200810f954005102c40d110072210380e50300a13014280307103480c1d644a10303005140800540110885001c1d03040002203d86050005d400000e1207001584c0500c0c2c00c0603003c071000d029110885501c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395629847 1250 395628597 395628617
    0xf1c0902102a05010e070605210402090112030225030c0803160318090c0e011709060705070602070c1d0903030f15040e06100911040f05060319060e07080c0a 69
    0x4603050084202ca43d206900104081100c80603190401c10980c1c0003e0209600084c0c0c1081d403c03030240c1600e01e00c10301c482000c81c0703802c0c542c010030741285050207070312039041f5491050b2081c035000300200301c0e5188262400103400f6160044c1c2c04a4402c00d4171040b1141d240d20b550200742c0c510003109540d030a00c40240440303082e8500c0c2d1800c803084000e103403240e0980980008081840903480c0251040c1d1801134540100c1c00c200f003030004140b005400e0ba0013000c0030007001801a401e6020880303d40208070761030800d84418076410030100a11401c00000c050202003000010b0320302003000103500035801140310120584c3c1c1c6c0741c115901e920048601d04204089080010300d28210102815294000a4400607a590000100701e280c150155460002111604c200300034440990043e40e0500d1800f00b00282030601e07103045c910b80b0401e540101c40c031401340030000a064034500f844030148000103207030500c4a16550041520704080c10b071200310000c2e039070ba00000d40ba4032518048a40c140210385c0c64103000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395631097 1250 395629847 395629907
    0x50a0f08030a2015013006050c1b062502030304030c0c08031b0105010812030a0b06190c02040c050909061009082d060603030f0f1c090210 61
    0x192100c00c00d188001122895032112050f040103031a41d0300402c907440ca606541481940c80c400a045140508441205072031201c043c081c5a25a03d406907100308041810b40340c0300c5040c0302501a051070304103101c0341d48911001c0340c80c0c0042c0c018003030701d00411140b0380340100046855034400e940b600035015a00400202d03000034401c8050440c01801080000b05940c0c9800c501ca00b140c1c000354100c2c80852030404c070905800800c3c41141c1c0140307020801000c900c01007144c103414070b000050104150994412040049031194411503c101410940210018000007030261021680303080680c001c074072b030a11f01c8900c1c3d4068411204072040003041c859482d80d80c0d41c03c00540c1007152011400b0420700160020f03080070308200e40103685105460383cad0f0b80307200c0800c0300d8200500054540f20050b4022803d204550f1408802c41d0300c0256104446039850500a461650030b11454003141c0060740186088030b402c2989a10440d45944200c400c052601200a01220242069144884900140c160241302 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395632347 1250 395631097 395631107
    0x304020103020412030509100206060a0b160f03020a03080c091809010905030a110f1b0913120503070e040606020d0c02030a06180c06050f0f280306050a0f08030a 71
    0x100a205150143c03606444010101000c400b4120840109002280040003031400301001c040e2005a840140801d2030718200054407000680f04151a000e000564051104442d80b81803503800c3d013020481c40c44151510f00203540c0e840c0306c00140c0000340111f002c03e9410700f422040715040c1000411610020034408440b5603440703030141903441c1d190358070403014001803414005440080e145464040a4285e10208a400c00c0110440060720b5004400c0d11002d0040303417114142d00441c240d484240359511f48442c400c004102c6840034204002481c0000015540100150b20546803999181c030700c0765007001444152000f43c0101405a0402180b85070300c1885901418641800201100e400c80e050b40c03a03c030120303109150312003000604030348540240115651800c000304030700d1070003501e0aa2141c0c00c503d02401010890814194001426200d410501c9005038110351503c200f1003040601e040b01038010403280c842c3c0c1d4060519440005000c44220300d595080700c80401c0510310300050280200c40c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395633597 1250 395632347 395632351
    0x10e150c130f061403060d120908030c03030106091203021b0a0e0f040203010e031806130905070c41010207140d021b061209011b1205101a03 62
    0x1081041480300c0c603540078400429100405420003140200c03070400400510310900042050b07030f1340d01e081007031001646a007600311140700e070480d807032202546d43c0303200c120f43c00c0360300d60301c02d0100344000302e9000f008680220055040719080e45031951441c1d503c64810103a40740c03ca0300503016070400e240390901d51410282c82440100008e100000749134649414460750102503a8180c00c1e0f8658034100801c60401340721300e8212040c164011410119020314122910100e4070016000780700100c0e81000001501510102515501000f801640741c400f0006014207001070040d58010301d0f08038010300204039816025062064058400b4074402d40c5044500d40819400c4000700a660820014000c2038404d00802c00d180840c0f0080d00c2d0100140704d0003481c0c000290300006140c0101c0d911034420f0741c0e4417001c031b60248404807034040c40c554900c07410500501c1001c02030403230700740c0044254000300e80c4525425070078030100008202c103448105c400c20a0810302c0c0150201090362202811102c021307800615 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395634847 1250 395633597 395633611
    0xe030607030f240806010e010308030a02210a0e0d0333080a051e0601060f12060806070203070309090209220b060f090f0f090a0c0e03060103080318010e15 68
    0x31802075403410040d45610410f030200d100080c6200024411540c0601400f401800d80c582c003220f1039415a01d805013540b0001d081c030603100d0360004030000070410010191002e07655103131581c8150700c3c10710b01c0701e8042e01d500e5084003c40d000712002809458028883c410b049001c010104211066a99208400e110840230f8000d6a04017090005541da030308110b07143d00c5510a5014202804026002010260300c1e600440925008070005120196001d454917180ba4214075094101c0102806808010403a9810440c02409031764201700b0450303000002042e403144250341e81108240d42e901c80e10101e02628034182da0180610284030041e07095490440000440c00000003020740740b801c0020f51644c451404844c0304180810419030620300701040eaa46c401c82034450749109000400000e403078000040922441e5980c50701e052403040d00c21912610700c0603018084071030f42e507140e0620b00348079001143d00300c00804072915102c2c0b001c3c806004c1d420154560300000c0c4250100744d440540c05a030700501d08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395636097 1250 395634847 395634851
    0x9060c080f1f030b0a1410050105161e03021b0d020306010e0403050f04081b180720010f090b1305150711010f090203010f0c08010b070819030c02010c0e030607030f 72
    0x11011840344c95450780038490712003000401901c03002c2009165a4018a001a582e094000c10420b40e43c2080c12100c400a1000b507001c0e054445d4500486d4500e0114040c1040c50a0801d1070020103400085500c017014004c0707c1c0b01c00c6c0514000400401070099070b0029015040200104a00e100203009250020700c281042814000b09010542d10740d0015072005030b441c0e2050780d1036030f100841132503490030323031002645d02110310b020b41d201c0c002c1c0d6500040c1642c0b040020051f072882d0900e0084205081c047e80005c020300106503850100406040c64444c10355504d2000d40204a100c07007441d820304451648400688420200749060021110f801854001881000c2c0e4900304103500a1003080e10800c00d0000c0000e452220f40149821100c09507400f242941ca4603a43c0342780560040040c074119540600c040ba82c406262402c6801070049205e0056941c090051701c0703450542540001d02c810503558002c121070071803440308407070b07800a036000c00d42c2603000030003c41c520074460703007220b0b0610f1503403000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395637347 1250 395636097 395636099
    0x30f0b1c06091b0509010504050c09010c08041d0105040509031201140d0c351011070813150914062b09050105061005160303090b010909060c080f1f 65
    0x105000e10340103c1c112500300e15240c0040c0f080d403402030300b41805010b09070380c01c000c14500140d000c4090320500c07181c103050018070f00200301041000c90880f03029200900e1800d000e421f0f18606620862801e010302c2d4865400c3c0300001d00030004c00808d0303071092a190454100c49902c3c0001c0054454048031001ea0401c600a00310f030b001ca6800c49240000305440c080d0144010880300010ba40111910200c558101032041d041d514000c00003212107414021030030000d40c80c0c800614003129840b4036400108000000700e00e810803008182080c00031035668908021404444020840d040503180c000c440100c001351030352412909101d80504001911500c41e42190700ca60381001c8010300c03603010200e03480c98440d024001000405e004160f000003040e41c011591484002c0c1c0541540101e90280103444c005604540030305100303802c08142550014015202e03941c482142101034010748006488082c10141c40014042c0705a9656103d009100d5108100f501c07101501c01d0342c2050020805450303a80d03000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395638597 1250 395637347 395637353
    0x40230100902010f1d0a0311040b040903091707090f0221010b03010b0702040b2d090f0406091e060b0915010c02220216020406080a0309030605100b19030f0b1c0609 72
    0x1e00166000702300e00100d8200100c2000103603120307040c2481c05076050209240010b60080c0910341558a00c07a01204c0704401d0f24805440d090700c5500c01961a8100300203400c11143c02e034010b000820308218004120403204c802034013890028841c200503030318200010054a11007030301404486100420111300d40c0c500e003000603d4141e581d1810304410b01c00c40c030095000e082c00200c03010b1070070060f9031480082c035101c4440d1b1006000200044e01180d11491404100406d5401080c58003544407403001440b001c0742028001068480c00540c01041d00c1d00100e00c1c8500f40d00d50000c20414140d50300c4405504560901001001410000c0c00c2e4266200031108550158009006095003a80c1c05100b0380b0350500420040e58810361000c80913070044038144001c65800308000058076000000480d00d0b480b11200100e24030060340c0520a00c0c035000c00c4140400360043c45c6207a14003030541c0d09104503205c200d1401c04607040c80d00220303802024030108901700a41d105149001602500002a00c0c00c0591 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395639847 1250 395638597 395638609
    0xa0f0b030709080318040e0d020703150209031203060301051510180504020d0b0a0609030506040609020f060a020114100f03110f040603051507020a110405040230100902010f1d 77
    0x504030030400d603541c0e45e500600b014415000c07032045c50310040041c2c500d1044080c0d2911928000600541030704040c00205003041d030121022004007800319140604125100b080c10780050311450f04c42d50030306011072448100c0f08003401034800000d2003d401011560415141c840d240c46a0b00d05030032a0050004240d6114401390071100010080071990f4102c0c0402c004003090180c00100c20300589100034000305000240700c9a01a921032400944040c542c0002124060080704850307200e240080e50502c002d0703040d0803124903508600c02c0c90b4440d840c2d4041102460049028a80031040d18403c20004139040e20301d071290010000d048581d030b06191801280c150707005c40e04240c2d0b95034415400544d90351395500040390301000300d1018114107480c60381c521140b8280d04c0040f91007283c80e1f001060642d0303200b500700a11000da01c01001100c072414000048888080d10000c01280190501d41d001480c2c0d03409034640349581655075001e0440c900d4001d036154001144101104400c00c1618001c5440740 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 395641097 1250 395639847 395639857
    0x90c16080f0d060b0a140c120301060e03012a0f090e042a050609060c030c0105070f140c030a030c050d0c030204050a170c091506030a09020f0a0f0b0307090803 70
    0x1d01000d55071031401030585010f90740c0310391009118540400a4110855100c109005801b000d885411782c0d83ca0108299803030490901ca8402401000100000743c8039006006440e40e4807054000788420250040c600034605055812100565601008189840e21600e82c0c407031010043d003403419001351038070544415a00708440c1107a668587c55a0700882121640035070110480308005103020b181003101140b00760003224034850040b1404030301c80181c10014015501e81c0700441000300080c0c0342580c4014580385400d21035002240841040410082d800c1c412114504130103c015850090b031240114006d0012032511406c00000340310f294a010003038042c00b26211025500940c4550a080400c40007900700da004130040c0415028141c4010400306251101e90b0044034812200e6542c540b0340c101d074404000b01e1681c0048000208a8800801d0b0b03c44002c4034000c0d181101c014074144207000d28801030740180341c0c1c8820801404c100180140303009607403182e4140307040420305540344496803840d040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 395642347 1250 395641097 395641117
    0x9060d05060c0c010e1f150509040b0f09010204142107030303380f0319060510140603240a0b0306030f01061a22060c030e0f090c1608 59
    0x4000340100e070081c024081d44c5003001117900a003013041c400400d0400c9038214080f1504440ea1590280e1110701c10b0084448010b0501410b0300300c0a1409103000c41101c0c500316070f101800170618000ca85034040510988095450161380111650440d4003080f6621440b0300c0d50b5001d1002e501d4030100b04e00c005004100c01103100392408030701c540c200c801c101e6181d444155819048448404807107045500341c043c40016040c203882c0c85608071040400703c0d0170b00c03420384001c1404880a10188041182c130b03070300662080c90601d01040815487e41c08115071042c4251560354032a505202140a5410b1005040681d011010b14850403041c0500454142c484584c0a090082004402c02681d800c0501107000900d6016000b08025806c0800c6180b640301c0d464245189840b010400880c1c0c44050901e02c00c1420780014600304840d0f0b1008001c180d060340740401ca001412020248881c0e04015440d41442c10b030050480c20155904821400c8540011002d2030718140141032810216401000074859106 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 395643597 1250 395642347 395642371
    0x412020303060d140c0a06210c08191b120b040207020a0e090307060c03061d0408041e122d0510090624061103180d03020307050313030b01080d080609060d0506 70
    0x1100406800742d070810785230800d011070404c0042d126140e4801240e650100c46007060000d179152100003980285640340c0181000c0e242d083e814041d89401881b104100e81c00c0000920521a0607414042079010310f0400030340040c00f00c1424400720345841d900b507a1110091088034207002c0a0740300d0701c0a507014070700c0c8100840e40d113082c00d120700620314100788a000801c0c40c4d02d6516041542e940b5400d13104500c6004c14031b0b0715800344980082008044080100201b062005010016090801c003201c0a9040c0c1c0714018429201025000352042203001526084000385c620b190740d2050744c90160502003000c640750f9960b040940300c400b0002013403402d010b80c040c440b60340c2142465000303004068100b5400d91294010b00c10100345c4050064040c5d540042620440d585c0d891a150903455400303188c0b0018034600020441d40c0b400401c0042c1002182d00400e03242071140da85408481d1101442c0041c0e4000427204c1001651783c0c2040111a5084100a824440c581d142c0707032200c07820a401594078038a021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 395644847 1250 395643597 395643617
    0x2070b0901110a06181101050a1d0111030304140c010c030e090709031407080c0609060702040c050f04091e02120403030c110f030c010c0f020615040912080412020303060d140c0a06 79
    0x202a400200e04003c1c20700c503280400116014002d007888101002591540c0c02d62b80000780d1081d110300d034007030a40c035045948a003010314083c41500c0103030100141c2d17445040b07040c411541c41070b140c400c10036415448122071a01e0080900528400080001c400d100200030008002a8881c007800c11504840c005002083d007021b28041c10b002485a400c1d101d640c007881035500741c2e83c079601116400c59048400244000f04018141e945004003210420701040100d40046e9214941d0031107029500404403261f5244a8104aa02240696070311a94100c008000040000b4000d50000d40007a03014104a18101c0141c00300c146403103d0007146041c00d400100702150201c1090240b18800d1a0908044044c0c07040680000d603114001000581040e0f1041190051600c403503020040c02d07508071029031103a030381c500c00244c0400000e85003240d031109000e110301074861000c0180c0c2e000c1c9200905102101e0255120601c0c0c0940c002c0d00c581d00740c0070b000c1c0780101581c0c807601840d004000e42e4850301050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 395646097 1250 395644847 395644853
    0xe120c0102180102011109040b1c230a0807200a0603020a0e041b0f0c1b0e1b030c0a09080106060c02180c0d050411040e07051002070b0901110a0618 65
    0x20b1554042d00c0b6040da070510400140620a12040ea01100070503100001c1c0325411380b00048190740c0d88a0313030b50403400c1501c002c0810700c0004c01301550106181d2002c0082480928546070356840c000b080501909818032000000608070310340c940c1c420f100000c603070b800b02c501c0e0000030706080210380c001e102080d4001042c240b500e4002d048a581010b048408020507940500f0402095265051070402c020f41005d2801c1c10900503010090440d4008407050300320402c2c170302101c1c8481e806016000364202c8030400200c11a000d50881d40000306605a200c0c1551140340f4400d1131504a000380605101554030081203004c002d1254000810440d911080b0540c80c42c014840c220010ba9036081d641c8107408100f0000c040042e00300c4161118000b07001170541d590303080c0071030300300340c140070069000b4240110b1400c8070714009005c1d001c0e00c404860303202040c9240c00082e6036880c8240326810300c1c00801d01032001a503001e0600c1802c081e2401007a1032038138003c0da45100490303aa14201d0307000803441c1e0f134958044c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 395647347 1250 395646097 395646127
    0xc2103050a0b1212091302030901021b010513060b0604051f091a030403052107210e0c060903070e0f010807060c030815120708031213030903060e120c0102 68
    0x10129094808036020090600d0b6951110f40704004d003003901c100064590003d032520150f0340040c4605040445d100c2c2801d0411a020f17511000783c24041d200d803104c13051800e03217041c81164000c5010201503108045665074040180440d210a03d6212800f40b000040c243c6541000e040d17010289090107140200d04040900800540e0304118060707801042c00c0200041140704490304680c140c1402503d9060710504d501d02842e1041102d43c2c0524220700340804da9070804550120706500861201001e09106100341c01c03140180c40303580c0198072282d07100d01e580c1803900c0209144a4081c0039188103980f1080d0030b90132044280c0c3d8402452480c500100000d040500c56030b0003038991490000100590390b20018503443c000340c580011030131401c0806032641d50b42e0001401c1b1442c0001590229640c4810b10364076034000415003d232003101d08001a6046141c2108561071950545030b4800060540e15600e0040c001d0410441207882503030301915002c2541c102074083c8041c071500160b51400d014043c061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 395648597 1250 395647347 395647361
    0x1e1101021201090c050306060403110a120b09151b21010f15030c0509220c021516020a080d200a1205060a1208040b12090607020c09070c2103050a 64
    0xf00f00f170030300034440d09940d4402124204e0741c015048103412025070f00040c0d55000943d111000d2104018401820002030300030891258044100b503482d0400c201251540b01a01110200100d080e4020a400e6060488010f000c400ca46910b06201441c080810382409000c20b80001a440d000050208000c1c9201c00c0100c5c40c49085140a01c00d403801480040d040d4020034071a00d220b185180d00380c1441030110f42445000706d030203410601034600c004030302039141c03104200c1c0200d41c1e58490001070341003031860201e0340100d0100d50081502240980f1f4682560700302d241001d45450b00e035407054848071031445e40303421500030692220340e8400f040000648041c80c41004044400d04003000c11000c0d5a4608105080b10340019041d28808001d160000f50b5100ba608001c030032101c00300360004441030340ea0b0301302d00c01d110000c100c440f903840c3c2d8801aa6142c2d805069607920004413800280c18601c5030b58078109039480b402c50b00f05c2020181d00200303118a00c46801200007643d940800c1a105101d0042e20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 395649847 1250 395648597 395648621
    0x7111507150c0905090c0705150a06060201020c0a0308130b04060212060111060103030810230307050307080c15040312030b03240c0307090b040306020c0c040c1e110102120109 77
    0x20a401c4a104040e0940f40507110b0321784500c2d100000680303110717105800c6428465200c015504a06402c440c0b1540407441a524042142d144c000d020440b58014800c075418440b0110080215420540d821203080400501c0440120224460000010144c0400500a034401d4801689548160740787d50700c00d41c1d004100b2070401401d1040c0039400b0001207030107410b5a40524112140e95280c0c02d0801080081d030380308040d05050007035100c0701d8480321740d09041c00d007908409032100c1656507403c040d6136001034010000550040b00d985009807500c000603000c40c81060300030134105503072500d5050000514110364800f00b511107101625070700c0c1c1802005913881d480102c500341410b00c5021468460350042c4002d41c3e90400001040b0854000d03c44c0074000c2c0003ca001690b0303035480b8075000000e50014500c11915206070b040094203442c0900409181050542e100080180c02c003c1d04030101e8440c40b0100c060200703801c000c014055080c00140f0511041180001c50380d45003210280807555546004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 395651097 1250 395649847 395649851
    0x30d1a27100b03060409050309060a020c0a0501020102030c161b060f03050c04061409031516320a0903321c0503151f021504020a06050711150715 64
    0x42c00506503400959411420a43d800100c44445180a61661003610ba00c0780d84101c0c00701382c030320440d82e0010b040c1c9851042920f07a0b50350159034000590a0707000039204106104000e0108884c02c17290541c4c60044140540d6140704009502c1c2400c050b054903c0d0800e00000303e0040e10588c00a825026184e04180021b0441b407805140080c000c04a8a05001034030032120006446001658208041c4848020000108145007044010480b00302600001c020102e41ca802043c0c54405e0300031101f142404621003003c8004403221b200b606030b0743c0001c1d80c490038040c1040021000c140e01e4543e00031300d01c00001044003034000d41c511001050141460032112580443c1c0c1e154140705c902100700300ca0180e103003030003510703a100c40303d044400c04a0000100c0d00042c0c198400d100f040c0720300d501c3c3c00012810343c0944582044503420410740640480b0043d4129021640402026100e103000b4180c0e01d00840c01d0007104040400000c00000810072064811280803030b48109100b8860307641407401c9010001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 395652347 1250 395651097 395651099
    0x151905060d0f051f1208040b0c0705010f080f06060a031409061b0403050c15040b0703020a02040b030109210509150901020c0913112214070c0302030d1a2710 69
    0x4c403442d1003428080c030031412820844d03001c1081044004e68028140d03844c0d5036a280d000d61000c8682d02c0484c1e204882c006000006400042d074040e8903541e006040e8a24102040e6031250305204003136008201082c1003607230324000342100210703080b074042c00385400c3c03006810181492460403403c004542000e8454050410041000882c00212803410140c181d58400800c40032000d1002540612343c800002404000f900104140d800304251103114400c581c06c00400264109041c00c0314840c1800502000344201c1c040f55102c80321094002d00074407894454500100500444c07280506410820301d40b8101040400003982c0502c9420038406003039481c2d503074034602000c104c244041103950150142040d910f01c40415103c2100c0015030000b455001911461610036803001030029400304101481c803440480c0f01036118201003d001c035050380c000d50500d24034400c0a0020040115401020200045111200e44445800107940c41818058000403105440ca10311a00c20080c0079042c28015031b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 395653597 1250 395652347 395652391
    0x7030905151c0903050702060309010902011403130201030f060906170127120512040f050d09060c030809240a051506040306021e161a151905060d0f05 66
    0x500303030b00204140102140c603540300d0038103a40e04c1c81050700194011200104101d5001c4c0705402c4201118800c1c0c2e0303244180703040110050514081038a01c02d90618440700500e0140d0b1180d0024410740f80e10140000301c1070b941300750002c2243c28071391203182d18951031042981205420710822550700c1c07410301e0703604880e05484845910002c10050084c80c4c1c03d200002496028424007e946511080355200c1c0310038103150800f4200c84400e014111518840c03080c811441d1407180d060340040b10b5250319130352075141042c0e8090352400300080c0000c4c0b02d4802c0650040007a40d5009043e40c00700c459205200d941c0c140904500113940c00148104280309206411a0080d1145411501202d402010040c0c1f2501c102018104800102c040c0c4440c4070004190040015612a10200e05030300c200e2000101e40c1900c001d0b80c02240d0201c1d0034095858001c110310310a030508001208021000c01c0d070076100c2545520004142d60015004010920b40d1107600c910340500d24843c8a8110802c1031081c0c58100c174000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 395654847 1250 395653597 395653627
    0xa030c02010f0c060c03053313111803061014041a120c010215010b0d0b0a080a03080609070c020a060e0f0a1503060608010b0405011d060703090515 65
    0x240007410800b41201c40c80072244150705150f030840e03200780709100100c1c0c02a030040140506445505000c0440650654a2204040500e0050440780e204601001804082040c0d002c1004940c0101d0b5803609600300204c2035042c0208007151002c903030040001d0100042c146000c40c020103001181003520014000a400c8a6201c00c03009070898000c0380191440d040d03400d8103040213032107a4015654010080c103c02d40414600c006403002c0c2d08550300940783c0300300c404213018207204401300c0c00002c1060205449003504101400100601028955580d500c0014030f4050219001d42c002800d8905110a91401c0506160410f0751440c20b4000012160001000c0303180c0c40c8182814003649401100702c0f17031120b070b21640800348010f228001042da645203840762804d0300c02202000a190900209055028143c028142c031444100b081c02c103800e100041d5404000d060602d0720405880e80314598540d5000001c2052911a80c0c0d034001003864101885440c00d504801da000c040300a2001c40400f01002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 395656097 1250 395654847 395654867
    0x310503060708061009050904050708280204020d0207080301060e0405010603091119051809070b040f0308160f11030f01020a02030a080408040504110a110c09041104060905010f0303030e0a03 83
    0x48542d01c0100c4c44143e41665100f540c3e6111640100d600000c000600001065900403202000161003000c0c017840e010031a441c005c2440040c01c4450703001c0d4100541003d9000e041020f6052500503c2c00055450308101500240d100314002070054080c0c002074203080c000e09004240c2410103210740b80a540d43c003003205450b488000d009008040d0f80320025042240201d00400c0003178182c2c400c0d80449046180e40b0281165800c503140725520000542040c0b01c402c40d4200c0b21001d20020080d825503403882c07410f0344001c0c20030074110000020320340421250400200d201d80314030408045602c480040c0350520240318010300060348144540d002e42034006c0101c03851407810b80760500c440d41d03840c9445422401590407071904503140c4802d951031040500020080e4180319119120300011f0014070030350700c40c054030400e904a0002c50102b0005500000d600d41101c0c4010000f00341145c8030103041d411190300b6403041c41e0340004c04004009058140c450b82c2031030180c0340c000c0c00000c0c9040d14050004c0f401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 395657347 1250 395656097 395656099
    0x1020a02060d090213020406020c040501081b131103010b040602100603170a020a081303210507060b01110f07260a0f0f06020d0c1e02150a0231050306070806 69
    0x40f04840d204565840c640d10289040d804811034442c1d49980000707564018850740c2c0c0b030049213030000209942900082900440d096008007090810310301c0c0c140060301140b6040400e46c26100e48040101850003005140070301102890716071201d01e0803000924011050007012050340c90700c4c20600c00300b103c0000b40d41e40c180302003022564030200c01600b00e00e003014074200505428000700d00031905684200b1020212402030080440c20074409051f400000351800c01c401c08602c0400100001401513001400c2c4c1b8241410703d01c074808000074040d420300344180100b0090350054601880000c1845c0020b9a041030640030700c0c00051038030001c8643d1041001c0000d0042c20312698031404000d0810400d017400f96000c003095440745110340900003d04128408800807030000380e540040c00f540b40f80e4503a007142036036005103210200714000c01c0800801605802c0d074a074007080242a038400140020041011040c20346136070301c0741d4041006030710f143d64100500c250070200c1403242207580404a6508424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 395658597 1250 395657347 395657351
    0xa1a0f01020a020402031905010506120a0f0e061305060106030c090e060303070f0c030b0a0e0604031404150215060a050a0306180f120f0206090a0f0c0323010b01020a02060d 76
    0x18500140d10b00700411000940c0503000100304203100b07441544401004119210501940e42c94204201c414000c070310585240c640c40c40000342c5900895084040703040002040001c1c400d4804055034101030084039130703500d02c0d1118032151082090801056004142a140c10400123519400081900506103d000f023078219100c003280d02643d06204071410141c0c0003405d80d80b1001c40d854210312815003484140c801034807480000c1d428a1071409040040c0003000080c02860365955030594118134241d660366040304007484041041e44211031455a038001980044c02e458000c0000400c1440008000e00e00865000008001c02e032600038400c015254000404540a181c401100340708250f090b00150506003840301007070520142c0d00040c5090744841e92000c291140c888426030340c44070150380e40b48003580425181404101140d50165059204081700e0a00541c2c0b5100c001c05002d40480d00b01c1e044080c051251210714007441186003040c1d081c0040d050212075600055420b004100001c00140c1e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 395659847 1250 395658597 395658619
    0x30a0302130902070f0c0f0b0f0a020c061b0601050607240b0402070605060126071110050f1f060210020a2d09050d0c0603021c0516080a1a 61
    0x107141441c1100140c54100070440d203a62050500d07500250400780b0a032900d0100c65808550303080c1c00e188a00030361700036400c0c0a00d0000b0003494514145d01130204c5804601505d00da151460b5100c200070b00c8030030b1074190008010f1040b484a0303810040181d10041c815502000110000749001b031a0b00d1149803001c1a444d0074100303d00d01100a440c406191580c400d10000f4920100040e960111740140ca01f13030317101c2e141e5851000e0340304031030741200d407000100764591b5002400315880303010329071022440041994509031860710084180c82c0142c0e60b401e07401c007400081104200d42031102c100c032180b80301c3c400030456141c1040030b522403d14540d0310100030380028030111401d00400054000d80c1c80300750390350b074140703034200110340210712000402c00040d081c03250000b29031034408034078584550090b00c0401820b103810400e900a600c0200c40040021040001444104580c424140700f024251a002ca90021401c002000c040c0003c1400004929024401082c583c02c0382d40300700c00c514141d807402121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 395661097 1250 395659847 395659867
    0xa0803072102070c0501050a170705041a0405090c03250c050a050606010e1e1903120206070206100303020d0c0302030408010c1d030111180d0209070f0909060503030a0302 75
    0x1076091844402541c000807034445035584030035030007018854010b441c4420304a4442d801144c4601c210200c050008640c00f2050803181040c6030300c80c0d00843d10703041c0945050741c0d4000b141e00801c80100c0038012008007240803c0941000000c4550020458010a05c1d61428100074900c010420b03a000e142c06d00002207002c0c40c2030265a4017182203801a0858001c0c45891400d0b641c7d481c001c54145001400c0825602d585080100f202c51500200b41d03403281010000006220b180c54110345101d07004888008004040f03205e80788028500c01540d03000c1c02c131901c0e010b80701034542600075010444002c1d00d90400c00110390702150482c0d0311007440c40e1800601c078450804919600031500407610365480c007190b0000c3c181d08000c92049030700c600c03502d1b494410341c990101804c8810040100c41c9603103040140302c52100311200707102500c640040070904101040d80115076610421201c48001c11405100c022156030026529001407140180600800e0b09000100ba203e00444142c07205054001c201e90f643c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 395662347 1250 395661097 395661107
    0x1b03050714030903010c050301060f030f180b0426070f0f021009030302150108150a0f11040303031404050c1e190312050c0304060c02062704060909050a080307 70
    0x5241c0118020a007034444008594803940140700452084d0710f09000414000d0090059904a881c5621503403000440e100301074014000303000340c0c103000e15503500031421000c0f8200303e60003695006640401e114070702803601451810151000010f40c000007184c0713507460480031003140d01895006088641c9840303e482c2034520540c450f90000d40c800d104004070158958407000c20000c4900981c22541d2864501c0c840020010003801140a141c21101c0c06007409403000600a400c084910310006d503080080398240d040307a0011220301c944d108005410014958513008103102c40d46a480d08012604050b07036010360720407020b8030250140400f0840d560042608808042e09079102400d11403040e00d9001809094400a010440300041d200c80d030401002e1241080c4d80305072111200a508d0706050002c1501c10001902c42242e0080b8104559100100a20701d4024942040e81204441c0c445540c02c110540e40c441e000342d011503182c5419407010074000a405039030a50000c00ca15602e4a4a06080320 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 395663597 1250 395662347 395662357
    0xf0f1e010501030c03023313120f060b0a0e010605090a0501360305071404110a020606060702040f380a051c0c0e090706030902010522090e0106051e011b0305 69
    0x3404081003221f0149840000000c0400003c3e141145030741c0c03030f02c5d0580c8104803450f02e04007800c0c21058450300c3d1700140e010b034490380c071000b001481c800900381d42e6aa03006080341c0980181c0006540411200c0d2581010840c001c0500002d08005143c0f21400051406502081d58444c0d030781c01c1844507403d074000b04a00604c0c00b454000c0290740c0c4145c0c82d01c0d03a170781d0f6038025024203500031480d02012080c240e000800b62400070302d4a5015107415240c0030308000c050341011800340d03030099803a62402d0b8000c00c0c911500440c1d40740402c2007030903612102c0302100c1040f00421080d10841c0f11a04000040e0fa07009240400e6440498403a01c503415140080040312050040013000e070799442101080c0c030032292400b02c0c40743c0c500b0401c0300c005645441c001c9040e2840701c64000d0207d0000e11100e0440d0ac6c80c0c1403148010b00d080d140000c1c4941e610480442038600c00e015094845c0d41d2500280b100d800c0c20b5600d0200144014161301c100130196000811841d0310800040549005c0703008901007601c01c800b122 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 395664847 1250 395663597 395663659
    0x41b0807090603020306010603021e0307021c0f0e0312090112060801020f13080703030c02010503070e0405010b090a0f150c03030b190816180209030f0f1e010501030c0302 75
    0x25540310303200c0c0000340c010041400306a01c40d00c140b00000403101c0c4207000700e400c0c1c80104038400b1a0b408200015280c0e5800181c02e410a5005140c0c0100e1080e00d80d04142c4800140b9940d04000b00d401c40c80054007d064001c0158043c0c3c100e0090760200110002c119044504280b074004031144008688000030521900710038480d500000700024880d00324005040201580d105120b1625a41e503800760741d41c0b540d8400140451030303048024000d5030151014540c0654241401c2034140358850000d02280d8098105044c008804240e8400c1c07410a2501c8030007400006031588043d5040000980310288460f8100c0c0c2003081654080302054480e0700b14400c42280544042090004c400404003248070a00407000a48980d9844003912091204000c007103401346601c00101d9038005980901035441800540c0e01881065196900c0401c108040640c030b0341101c2c042d01004030415190002604842c50005003a0704000050000c203802641700c90469504403125544c0440da00076221407241200000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 395666097 1250 395664847 395664853
    0x290a0b0f15040b0c010203070f0e130207060e0f1c0309021e150c0309011101140103061521121125080303090708060601030603170d09020603100e060a0e041b08 70
    0x1103070004c5054000e14041d16580e250240c40b600442000c454089440a1003648021003039910507407211140c0c0200038050207034401107030f41d80c80007407d40d1500400e42c0faa01c040703034403a040c07042c608044402c8040da42002031806020101a64000801a001b1003e0034201d02c0414009000c1d50ba030341ea0702844044444440a944030402c565040d074072074004e0880d07135022407641841920302c20418072501100900020002c249642192900c500a040035a000e0200004480e400309140180c41c0801d0f40480c01d14540d0141d0521030324049020740264100a01400310310a8800c109610201d41d88960004540c40b80c450035015000c00035998100d940464041d01000003880890800802c411040e94181c1044a1141d21550b00443c00c07078071944000750001140f40c024080785441c0b18011704c1c500c001891302180310380c0e1540000741030340d20079190600400c82400c020171607601000035040d070202080355181409890009950b0b20340350014001002b040841000112000a00c101c0c200609007100c11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 395667347 1250 395666097 395666107
    0x50402090303090a1d0a02041809050c0d050106170a020904290705070201080106110c13090c0e09120a0f27090e01051f0b16290a0b0f15040b 62
    0x40200790341c0300070a02450700000c1e42c0002c0c002d079005008680485208800000b6001d41b40309c0d1200c0182406102107541d805220310503d550717a500c0640f02d0503030380544000901c5a1811800070160401425201120b803c20000040565610756000b40d210f5040900a090612a007216002950713010104201c01c40f4000b00b488810f641c004003030648030b4400c0e2900c18a170390b2500c2d030540c0c031641c050b01c00c0052648165100c04043c18100c000e402074010807800803138040000d54565860013043d412062400065004000d07114030200000c00d8a005840500c614000e00c0303400061103820004156407d100501d14101a044508000000c4081c1c3c04045810303290b4031010544003400401c0c1c44100150b08010110703d4000d01e1210708000c0c0700c2441908450701e03250924804c032981050321060040d049010f19003000c10035000307098510b07521030308581c0320b640ba1304182c1c041d400401900021307240b850041d5542187e200d2032004001c1540840d00500e60f40003412440701c42d40304a401900c020007001c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 395668597 1250 395667347 395667359
    0x90f1704080a0c050909210c0102120708071d01083903100e060d14100f061a0703090b090616080c01050c070b010b0a141b0c19050402090303090a 64
    0x589003040d54401c8841121a4032200c88059940d6447c00d45012076a05501d4000044403600300104140000b2000140c184242650480f042d244103c440741c3c007013042c803810000c510b03502401100d0690101407071440301180c1040000e2618200030071007003045900c0c8885640320030710403140940b141080440c190b002403440546a1140c0c001755101e0a00c1000b140000c500c0080d8039050324442c1c080031b000741342c03400c1d900d4841e610340c1580c903e03150000b405560a51210040280601e9481c20300030b4801103030540c45d0510f8060300303a40012081003218030600c00c0d035000a1b44400c146d0201da10135803a45413110302c104c0c0000c00c1c500c038035441e403083e42c2d1017465214104030440c1301501c00300880c2d1008202d075507030b051482c52580c81f0310304004004511740310050010700010006051080c040f840d108148a40064003140b142e07202203000d54440600315200924140e08001e501c00c081021b45990702d4030b2000a911032900c0d0180e0150500c500d4000c07801e05480c1d01c080041c1c40501c2c0d0020025081166580 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 395669847 1250 395668597 395668613
    0x6090210031505060703120b010e10180f060807140408030406080406052206020711300c100c0f020a120b0702010c0f0f020a0b1503060a090f1704080a 66
    0x202285800b82c0b8900001e03843c070340042a40c4420350992160440d07107066641e14401080d144e03038900d06000e4202051056501c5201e81100101020f44950b020700511764101c68009d50301c0d034010081d09840b420309205090340682900c2e0003000b80d0801c501da00c080c6801012980c06a60000e0348a803202040c00504164000c2c0400d0195016100401664841c5400ea405402e03003c030803009200d607071031982000a45146d00034182d540c0130f1064031890740b0880c0c1c0005c44104140244001c003030225110700c03518110300035001c020340c44034070000d01c440907031480854407510703841404109011000003200180603840202c03e0708540d0003840c50030001d072681d990351501d070a031880540d91224840000351026005105200c0400c0d020f444002898410442c02c84c4c1e81824400128218090411700c000000e08460481c1e015100e50500e9284403d900c00030b0504d011070040101e40c80034200409000490050340050b0142900456001003500c882c0398611002d10580d8080c2c0e0703081c407420b0783c500c05008600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 395671097 1250 395669847 395669861
    0xf020a21030b1c1403120a0b04050a1b03200304050d0206071412090f01050a06080d0c020a0b09012c04050109050f0105010e011103040815011205190609021003 70
    0x1600c00b0450151070900b44a6003001018500c0384124111880e4401308a840c0c480e02c0302801690112880e081131600c0d00f0001310300940d40999541d8641c80801080e151501406e50f03c4505020b040040039495000410a10200841d4200f81691152410240060003d08802c43c080c407841503a502d080034030384190b4544070a2070100060103801d01091015114113901e01c44075150104c0c2508188020702041602040030313042d522288034000d91010309800c06e02039a03110b200d22500c005980392030821224100400d0030880c0301085003d001c02001a138503000c1c01c0050b9071861599030344401a440050ba40c0180300d20001c000c804944014005074118101c0d4404082405c0d20b051115980c0c07100003900303460050f9451099417001c01c0040c411548190341034403400105141c5580c1603440440081d0443c0d00981054030560080303005506400c203202c0b010350051240d0fa603051b501d41c071903071642c03922041204605c1806944450f070307445c14441c050f00a1109150020907801d039807284044e0180003440c01e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 395672347 1250 395671097 395671163
    0x1503020d12030509060f1605071b030c0b0a17090705061303030f08040809040905010f0911150a02031605120a0e010e060a0c0b060411030103081e190f020a 68
    0x810f0b00091130102c0106915009544529500120b6200d060380f01c3e14261900c00342404121041c40f9420100313511000c2c84039140f880580d058a2070341541412000e1840b03076000407462030001c0218010041c0c1c000141c0445903080c1c04080050f4807a10315850405c03813507500080d402100482e501c1d003580900001c09044074440c1c1c44d400300d8500780020035a12003030300729009044900300340320304402410b00381c1241e040544104000910700c400209003d01321400f21320107039250040b03801902500d0503e1841038003d1075502e4042c504000740303484025aa40b140e5140d0740228070740000c40d6000c01c20708112a840c085048461a6110600380100411030140b1035000ba00080745021142075600b441d4044440350380e081e6490281c4150607880346008800c02404041d0001d035546c81a07500000c011b80038601031071188200941c0c43e448861880e0848455004081e568503007000840303914150185050004032203800c04503070010950809a040c040031010182010900b6440340c204014184484240011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 395673597 1250 395672347 395672351
    0xc090d081306030603080301061d03030307050a021b0916030b0301050c07050c0a05030d0324060c03020706110a0b0a0e0f061e0c09010e0a150c031116091503020d1203 73
    0x2590b0325046003601c01d144000340c60388208000610245d0711841103003020341c200d540c10350965410040802d1030b41d4000c450200c0002e401099003069158103002020350980d1004418858103480d40004881c40009007500582d10b004200c8003038001d01a03003103400701000090080145260202c141c0460384c2c8103e0080b1818051003a41d030002d494060794a07000d81d50040c004100f02c1e0306012043c0e00a00307030420605402058949804841d01c50324040390040c00c40d541d0b078801c00d00105c0c500a4540301c01900800c05118850503001c00403607000a0340500282c201012251544a0300c01d060b0040146094031079144c0201c000c400c0c2e00b0035000413500e00503000c41600e0f250480c041c00403e02d01e100c00351500308072003400b004101c15540c0b0810b8102020107004000d00c0c0590b60300c00100b4004451200c8003800b10b0580b000d00400d140e00000700720441c0918101816802c801a04c0c8444000304030b0050400c5a56184003401c004030701c240c441c0c0c000c0c5901401c1041d00140c90300305209140e081282c07201c0000c4c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 395674847 1250 395673597 395673599
    0xa030804020f0d030e13181401060e13030302030705210609150f042307031a0a03080307030c050408150609070f0c0807020427020a0b13030303050c090d0813 69
    0x200380042d00503c0c182c1c042c0e4850014a46030410032880704100342e17807582071301d0326030061504140d00961402d0340c15200d100085442907a8080c2c007404d6840700d41c8044840240f89081001100000c0c0301030b45010b40c145001652503481c0001a01e9038020000078034240f264101c0244004611402c0d0140641000c0307540081640c0e03160402c0c1005040c03407813400c6d08888125904001410990009030895031080401284035049104055182200302d60240000783c40322400340e003e041c528640d480e800d9003510184601c03803c640750308c40715201c060030910070140d82e0303004400440e12407002e6a02615102054600340f16000070f50803220310003541d10903c61082400884e01007801042d40014010301c80d10313590410700f0701d6141c00403590424401a6001512441032401d0146c01c5c03003d520103506980c0760a4414801c5d40140448ac2d0b083e6048103403c0c040400842c1c00c501d2681e0401401ca0f5414a0081559503501c90765a0241c0a008030303c540101c00c2103460020804080702821005032000382018800b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 395676097 1250 395674847 395674849
    0x30e0102030106090315110703050d05150d0803070309050d050a0305010506120c072406080d11060a0b040e07062601030213020702030c03070803090a080c10050c0f0a030804020f 78
    0xd01c001e11071100410441801000040c03801190907041130f03000030000450401030300180002d43e0001200710002140041c0d502030703d80709840340c140c0101c00c605c011300211180c0300104c1c0105410f288003400005012000a80c0948207410a522184d1300406480707401d0306ca070401a2031030708881c040c2c001281c2040004100382c1444400e48000544044003c4041c4e2102010b0010a80c8080b07000d40711901e62042c0307018007006c0e4040c032401034418400d000444510700030445003040c407001460401c2002200c1055102e1900061a0760013045103200003c1007a5440300090041c12400f031215890302800c00009145608550101c11700b00400f240c003110030004005501c8010000d00000307500080c403030240c80382d04c56558041c100191000e41220900c156200009240c1109075008400c00c0d4400660403616062054845008112003c010410180c808000801040b01115003804108000c210f0000505040240b150000c20b4481900c0c00b40043d401c00402c584030031982a80524208140f038601c0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 395677347 1250 395676097 395676101
    0x18141009020d0201081317130e06010c0b090a02150306040b0111120901030b040504060e0c0604032a261605210f010e010212010806160f021516030e01 66
    0x40c1c1c0101041403601450340196580e48000d00a00c200c0e250312540c81000490102c09408490b014000458552542c644075406025440e000b51482c403801a0030f000320740c1d81183e64081c0003903104803d2602943c0e9540550300d40940ba640180d4002041c10f158030f40c0c1c510410085000310030640e03060203890201c01c01901c4500c170035444881c00398003001c040c5030340640c8500a080036400514000c10364500c518001010b0783c9044c0c400b034605035030b5810340d0400d0400c10000380c0c20500c0b040c1e540a05282c07840e196900c8a4003a01d0015494032100726401410164400e4203001500070412070540c0c80741501804071a02c0b0302c075450454503100d140384011400c5c208000704d0049401c000c2580e600c0281d420749051441812402454062107901c2c40d403d03800c10203000b240b010f0800c075800140c454062820a41c070925060b40040c400c2d40001d000d2112a20f982d0106062081e800e0801001401c21030303900302e2600448001800181c0c0c1001c00303101074140da0901e07640340d503080d903941403206a0f052416142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 395678597 1250 395677347 395677361
    0x2070b100609031101120e010f0b150a030f0b12060708060d0c050616171c02030402010905011b0b0103150518100b0103090602030106050301030b011202180406181410 73
    0x1107200003a041000130845030102410301011b00d031007015610031460388070035605650443c4c200744e5100c4110340a0070b46184030743c1d414000c0449400f03104003900840d540741403003441004d03001c05488803044c1103940d601d030700840070080015105040914550114035214001581c81d20b0005d01108086075881c5088000c0940300c6412031044881c251415041100310750203036081c41054040f400151000c03607614034010846060301c2000b15681c0b00419420400440301c5100d05044610510034803002d42d074000c0860f0140d074003e00708200d80203401c40f41500301500a00008201e0710780840044104034140c2e41041c100760b4520301c00d20650322220b4402d0100c0301c0e84c1c520340b0542c0e4020200c01c216a240c0c0e0704801003004043c1800038640d8a2500e902040e0383c003d800560109400000400421041c1c0c4c90060040070307a2034202034600e1560340010083d03c9a550001c0c10101d600b0301042c103011040c0c4c44400519214001e00d21145450300e0700d40d0f40001d0000700211180107285140d1070000090051034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 395679847 1250 395678597 395678609
    0x14010507090e102106051006020f070e0402150412050c10020309030a02100903170405150408070b070c050d0303050f06030a050309040f061211030d05090105070f03050c0a030302070b10 81
    0x1010560920400c003401d08216000c00641e2955040b0184c0400d00c1c5102d0b0600030458682020601800d0800191400c550b4038260f029640c000c080030000c01203221a02da80040e030482d1364100700c1c14040c070705d4802c80c01590420329400c01401031500800ca400903410610540990743c0800d49910000140d88034000d6501c0d2540540110004500515003901200b0038940c40303007002d40d0540d4580e05c2e01c001c4860081980103a50f0f44c001424885440c050401581541c00c2e00c184910380b6040c40940c036140c01030b500ca030450800000c1106010050800d4850001d4100a40100314071002e40c14000e024000503a00040b140c0302c00e01c003041803070030045155134000f0b400130025840c00c0a40e00a000041c405202100fa60658450002c0303960710718410f41504990158004500b41d14101d01054105520380d500002030000c204101c1c00240d8010054071820741d0002031403074040303995040965462261061541103406048910420550594042c00401c0c1c003501c42028580c1d15030742c00c5a000d240d41e010b60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 395681097 1250 395679847 395679871
    0x108090303060d030302400803121009090b0f0903090d1407030c1d07030501050108060f0d02210c0312031f0b2a0d0e120a14010507090e 60
    0x1810a003801c0c078801c03d1040c82441d0051505000459070001a450342440701a0034903a0042d5082040c107050703490b103a18071400080d10000f0318094000b42d036403040711003c00c207030440c100002c0c11005810a030000103128809090203100020310f88020081e404541c0346800040b07103000300326800300001c1910003512000e0310741002c81c02c1d5034980848080d0b48080c210728501c07542030084000741c607e1654200401000d00d00407401c4a203c1003a01408074010424400c051500004101503a40814010b40000045e1803840d0154500f00c041142400d5494010f0341141072a004e000070218108098041c1c800c443c400e4a51072101340c1c04041d100c2c25081c10440c0f074840c0a20101e101d0007a40c420072041400014800a0441c0d9580007101c0d0f181c101c580c200d03181040c1d0004c4ca10340001c0e090644444d03901d000005e0032000489031005006800310090181c01030a082844940b014402c21903100580e07082070303401d510641d1102e4503034040e05003281d0813400a003c030100050424078601c201b034040d00b4a1581c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 395682347 1250 395681097 395681101
    0x30d0306030c14040e0a0308070807180501050708130b0a0e06041203030203061f03140601080f07030c020f06010f1e3021260f071119110108090303 65
    0x2100c031020700303c20301a4840c0d512100c0d40b0500314200086c160b103511036203c0a02c146446038000c3c1220340300600032b20520007040144d207000303038007850141d0680d4004d092540c3c80e11403d05041e6640d000e0803100c030200b00039005002c208020041c0142c0820b02e4140c2e10807a03112017450034002c0c4c6000d240700c0c03030030b042c2e40068011000a00a402035548080094600c05100c04090448a44009a01030290119a960041e9248000c40841c1c45500550a0808d5151804e20343c110100c0980014604001c169580346120950b5100b8003907507e11241c414212546561180300e00302c02c4200c0d0340301d0440a500d40101c0140c542d024812890201d542440321b144034004c400f410030040b1548007605504040c40c0b24508400074811403040103d00b0040c000c941210071716140080e00310402c00303800e1507244004140017658003400000032030f4064001c0f00340c2101e80c1c0340c40d0400e82d54110080000350b218010303649034401380103100070f80105041c0910300848015020b5001940c90003000c3c0c49481c0c05800c2000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 395683453 1106 395682347 395682359
    0x32a16030c061e020a0f05010b191502070b0a030c02030403063e1c0e030c0a0c0b03060a060f090315090302070e070806090403020709060e06030d0306030c 68
    0x20350418000c0d0900c1c0003075170300d06100c0c0f8000c0c100d03804100c94100300310013904880540d46000e0b1902040d028040031081906601c3d010b010600000c0040107820396100050741021aa00524130520308151700404401900408102400b0f41c4420400000000c90354800e41010389180a1041d201018110100900c3d00341101c0d000790924000b14024800141141242c04be04070400c1112083d003004d8100801804c6103040003440f034000070440915000000c40c020110074030a207040f07076440e0340350400180c3d9800140d541d150003020040d000d10030107001b81c1150305426102c6c20080d10079a03895070742c5845220b5000003000c0842e00c4880318010150104840c00280c41c070780038000000c5c03924500c02800800010000741c0304c0e0f102900400c050500a00556014104c0e5090520003240c8420b11800f046c882901c00602900c2003204000352240f0900c1841c0030703264065400082c2500d090 = true := by decide +kernel

theorem cover : BRFrame.Cov 395503597 395683453 := by
  have h0 := BRFrame.cov_init 395503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 395503597 ≤ n) (h2 : n < 395683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
