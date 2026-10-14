-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2754
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:38.930964+00:00
-- url     : https://prove2.me/submissions/341d9f26-9f52-4d50-84fb-52640aecde08

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 495143884 ≤ n < 495323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 495145134 1250 495143884 495143903
    0x120a0b01121b0501020d18150201140f04021507060b0a08060906010e13060504151d100c0507020f12061603050901020a090b1e030c04051809030328060e04 68
    0x60b00040c0801d01c00c0b641c0513002031100c100140e02c140c40c15201461620b4648a40c00c0c00040d5068505020500c3c03042d5036030000a4a8507841ea1483d260030004e01204c80d0b40989104201c01a01e505524500c41c0300412100340d00d030141440c08001070003403d2030594002c13400e00400075500030001091405030030f0704001c1c1c6149030f03202d41c606070136040c04940418508071138060340408200f640d400700b90080c1c080c0c01000d080340c51040035442501c4003034005001b046040792200c00520340a02c150032042601e01414000d0460525000345140182e40d0082c0c801c894400c02400781da903030441d05203101d107a401c040d0b400c10315010440018100300d44c04034030013080c01d18001a03607100041c4201c42c8904842d46941c584681030291424194101c2005054010300301c6605445103071061010750f119044002015548500702014081500700d0705c4011000f180c1c14a0500c0f00c00000031007501c0d0b0050240a0000d01c50752b0000c04e83e00b801c48034107500e2548616111006c40d0f00e10301d2800f510322550007120010b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 495146384 1250 495145134 495145163
    0x9050601020d050306060c03040305030a0f0801060c050a08030c130306020309010b061e03040503070501020408061803030f06010e01180308070624120305090415050306070306050609120a0b0112 85
    0x5a86650740c402c42080080d400300f0018216140607009040a000024122030400d6180c0e034400d40345a20080031940425407a2401c01c40040e402200b00d4050195458007460710741c80d664405a403a481d40070024a2400040001f50100c840e00c4144c591303403c06450705d9503185581e0300b07000c0c0081d4002d50b0480350650900c4034444260510304110760100482c021284899686007607042c1058101400403540c5000400600307000c121f003400500090301c0b004029000600700175905404642d8460006c05413078000380100411416560b0001d80d00560070300303118642c1440040125001400c406540140300c00c001004018404441c020744003551103801d0801c004652140502007607090b076608000740d90b121a80501035500c11040d01043c2c10301ca42407403410807400400040584221a0300901ca0317001000e42006070b40b40411010360008c046003403c00c0031504207400b0491510903ca80107008401480018500410030088508105e03040000810035585405105101aa080800303642245407003010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 495147634 1250 495146384 495146387
    0x90703050406060f06090b0f0f030f091b0d03030c050c0102040f150e101d1f021204142e020604030f021203010302042a0e03011409120c07080a0c09050601 68
    0x6076000e03907545e500c0d1001800d160014500c61944258a04001c2090600c5000030042ca0b04001c0c0d40146244a1841c40170702c2e19680703252030421410745034810241c0d16011003425894100342465060342518010800511060064840c0c1c400d002ca9003020703610000c0c00007641c0c1148061903081c5e66100e84a02844540010200c13251003840301079507031001314400e0154407580564000e2802c4101070800d00c500b42d01c0701000800750b03050340480201d03d28411108510040e0b041c0200c150085034020001e00302030a25100790302140d039400c1c0c030b1405170000c400c1c021102d1080310000907400d413161150301c89808110320025203030402030300c0c1100450803140c000c0096a0000c50205510315050f0503150a613840d68003080003400411418040c20340410b507503840c080b140301d005200c801c00036480b42ea043c491000d05050840d00702505021400f1603800078098003950106044441e001c0154002e40c80381000151769080070f0b1140d20082052064044280030840020042030803141114400c001030703a41c0000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 495148884 1250 495147634 495147659
    0xb1219021e09010e0a110a0903020102160b040620010905160f1503051306090605100e1e0403091d010504050f0610110a060f0203181209060d0b09070305040606 70
    0x1001d0340c0c002c0c0000d005000c814a0a030989502c15103d100124500041000c010000c0d80440c2d040740000b04c079003006005558041100b45e0904061654104e00c80381b500515100c103000e140141c1c0d04224110350326060344604080b6020714a1004c0000300300e2010306103440c41e644d89180d91148149140d81c00e000074644a440819030840d00a021f80d6489004212002c07001072030000c0840c18146c070842903900103d8401e10801c107031743d48100c500150505280550191b074001a62112851026072402c204141d0ba4011124601103c5d0320000e20440e2240d00c1d0aa8602805400c0710540049124000210700420003d82d13040702c0b4107445c01c01481e240e01030060781c1c030201141c1d800d400124142050301172501c55040d40f24040514003e40e60012000e0759801c003900d81e40c05456072420707004420310881c03102c40d02e1108940c05080b07000384801800e44105051070300860003258818a8003098100d82141250040f4000c00c10003002c0d004c0d13a00d009880a80205001e4074180c4040c0c0c50207501003201d2141d191f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 495150134 1250 495148884 495148939
    0xc0c030106170d080402120a1a0109091a070e030d0e011b03020a020f220b04060e040308040605151003020a08010f0f031401021b0706030f1401090b121902 68
    0x82c00b40c814003003083d000b514000400303002240c04c0251542c104203000c4051200059032841000704501020034480701c0e01400d501a005140e00d9407070080488001208001548426002c0c2c0400054503a9552015a00c2c200c844034401d426020391080c502145a03c5041002800c0e000d0b203d00090316007034101b800d0038459200b0000c0242e840004141c0c0945030500f51400b100c48020000b8118035940b42070b03404074905a45203000385a4031000e2024480c5000d002e00f101420010804603054503082e01d00a1014601030400741071141c5e98801326081450a5a000c0d0102e000030f010070307000f040304c0704c802002544090481c0c00059403840c004142d4030001c15160044400c4451b40144280c15500c44880f20419691041410f40d800c01403030080300302e0148843e5080c0182400f81c081240fa01c500941076690100c503079000c035883e10300700300c00c40c9008540d4681513456206000549080e410301240c0e03900d0f002c2245180380d1049000000ca00d08450702131588a600c240c03013600740c06091411809021040e030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 495151384 1250 495150134 495150179
    0x150c10090222110d0903021908030f0a020705060f07030b090f0c0a0201090605010e061908030a1209020301111305010512060d172d130302060c01020409020c0c030106 73
    0x180700d001c0c007403401c801800b410507000d000010b2142ca440e40c416040c0c0d40114082100030703481c1c120340000e154042c40003583c502c8a401d480c06200005a13191040c0344001000501160b6100b0f01040c0d00808660540b09034540c1b1000301d508a0a00910020718003104990a10000342081c0c102e003810f0a00d441110f0050044a00707941c59610360310b201e0303400c680104414100315035035400034101040d26401303154028110002040894104035042c020b41c400285030840d05030760504002c2280301400001c0320900c10a503d0b06408554001c4000405800d80e440040e40c55800d100c03008210908840050071480d0a840040090356600c40065815014545520101c1c855100000c0d80900700f01d00f1401500348100c800e1000d0600107041b4413140d410070b40f407110700030701d05142040c202e0301c0d01c2480b991560070410300542421541305e016100401c1c1800001d01031100828004a410025016a00600700024040d510b40f913002c2c403203d41e108005003040d03100b582098800035045515290002404015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 495152634 1250 495151384 495151399
    0x1401020a050703030509120105040f1b03050a0230010606091406030103141218010801052215090c050909010501080c18030a17030702010e060106020d0e030705150c100902 75
    0xd5407030030307100e0f5000081900d810401c80307c03403c100501e0038400c0c0c6208500c2203007980d05800060601d030301c0380c80c14840403284210b10302c502070021844c00520320399055411609921040c03103142c00d80c403813044032403200d808815800031041901e12040d044401910207580d00c52008580c0c0e41c10f410713454684203907400e8001004000600209039030642c0c403035848200c54206c40c19581501d01c801e00583c4081d0b802921031180503900c1d562581d2140e9030307a00511007110380405521001691702c80580040600a480554480c240a09144000c01e08401011034220800c000554990041c0c81ca500603005544581808000840c0b00c0d03002e5000b0324003a240f44880c040c14082919002e0310040070300510b2680c14425000048001907500307000040040c4c403c1044c9449090100000e42074843c1000e100c002034010780010b1112650000c3d0310b8240300c04500c0c00d44405a009030200b800c1449942029411000c24401c00141c4250300009110001d01e020490304000d039154022000ca805000000b03511806 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 495153884 1250 495152634 495152639
    0x206120415020f040b130302100c0309080c011d0f0a08100509120301060c1a010603090506090f0d030209010e09010e040506070e03071a13090c020c0405161404080f03041401020a0507 80
    0x1741c005002222580e01c145058240c40c0d80004078508180e800300d9001440d00c1c1c804000305a842104c01b0000c0103642c004180340b2924030300107406112808d40e81e418001341094000c2096071032143c5014400000b80c455190b040d12818859216039002000280c034a040030042002e1100000d040c28100640007442421642090740032184584150810792343c080e20314100201c841c0b00c40c80d45600901c900d44000a02245d285807181c18004001c060000a400505001c02010400300f044101130502d454016550559040160340500c0e411855941002c0303400c0010600d03119201d0564020b5006508441d519505c020040781c030f510018682e03e81680019008029408031039a40620038410101c1083c00c0502c888144490f14046d0b500805034261980000128550144040b02c01d040d0107940611203031801c3d415031002c41c0e040032001810030a20012845002e0440b106940240504d00d09849055a280006a55941040c0a20303552910940134605441d13000182e01d001503039000e0060040c02c0d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 495155134 1250 495153884 495153899
    0xc0911040515130f0902180102031309020d02070c09020918010b040e100b03072a02180901090f05061005060403150c140d0516050c1b0d0206120415020f04 68
    0x402c0010350020f1011102c03004283c0c29981c48111025002c00c40c40180c40740000c0c2c1c000305c99a104412070506541080100c941d42c168036048c06016500e2150025903280c41c3c2070300a00c028400e00001600c45807000c040859010001d40062118150440f003805861196101d800703c00c4000313218203040c000d010841009a682c00c9c0120381d900c0b1884404941c60300e030365801000704c2640202c0e58400003031401d9007400080c0c100001c140b4105414810b0360151141c140d40440c18025060500141c498030340000540001401d400c00109180d2100801600e40442c0c688907a49a5040d180845034182d60743c404a4141000d8003510200ca8219003800c1d08202c2407000030000308210b07410403040003801038114002e400c00340b0040000000c5100f000580e8501841d2001c209112800600c0c200002008401b074030080004000c00d0250007003d955048007183d030005141081020700017500080041000c0840744020681203100b01e018108202c50350013074004031000c81c86510403080c41e80e2001e100902101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 495156384 1250 495155134 495155137
    0x1306030509100c0203070309090203012114070e09060a0504020d030302160b0133140a05070f06140f0403050406180323120903100b0d06090c0911040515 67
    0x3441e9802501c0c071140e10700c0c00c060250b60402c4000c0000d81d00c0090110201984208404001d1807484411402c0d541410340302200010303c400030b0116042c0a2110405201000e02652500384040040b90300350303640c401000c3c101a0301203886c0c04444c001c15001648450700c41c01900e1040d54000d200e0001000c0b00d90b801d90094000c3d6180c4500045811084030000c0d4180b003426010b010b504001e0701c0fa095001c60824601c1c0c40700c40da82c2550100c900454181e5039001260b40c4031800004088944401c04524100c5040c0a1224080c1c03a00c5906040801809038030b9000072112500c0c100040382d00d6689040340002c0c00001d40700103001940400080080c40d2050303950f9581c83e610f49909901c0c035662600e03501090b02078044d0111056058607030300b1317074000e40070000e1400341040507004600706804140000e4442d10302006070310700107807207142c060400d54a220032127102545c030820070484031aa40c109008041c0e581d002e010307034542c80c006948850f18000c1c42620125480203250300d040110600b1090f001703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 495157634 1250 495156384 495156391
    0x1205060a110904050c030a0617032b050c0d0e01050601090306050603030702030a060b040c1e050a09120b060108060a1206090204020f07110f010f120504080c03040807050a080313060305 81
    0x710310082c4a030304120341c0c450040d240942e8043c0340c95034aa00342055404125412a4000d48020b0090030210401c90404001c0d50300300082d04d0000c2c21a1060050650440d402c00030440340300516100c00c1003021607030880900410300406000300100030081400600700c510640b1a50301195806504000154840c0c0020381c2c0802c0103010381c1e0404080c0d0f80843c3c42c0c40c0c07040c4800c407910380e203490010700d05080512071202c02a840389000c1101c50080d08030f402d40f90800111980410000040da440034034058114007004113520910044c071030190f070901c0d0521132025243c15000030702b580080ba8003880d280f403225090f9109860040300d050280c0e03031200000c00c070111040b40c10680034407003d2252079544004d000c206015015111132681e0714400c100d00c0c040c00814081c1032201501c07520309001c0e40480788030721486e000c0350300080684460518003442d0103420b2141a8a10000030b01060a02000c18100100d60701942c0c01880d00b5100d410140d1a800391568202c8200f09480c4100701841c8079400c5a40c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 495158884 1250 495157634 495157661
    0x120a05030414070f03062004051f09050904080307020606041a040f11070c030c0b12060d110a141f0806061605011404031101151505040906080f071205060a 68
    0xc10ba0362131400a960740c80700c0e40280da8681d0f6540140348880384012445002c000104005450720381858001101d08021414a952071810b142030100468050703420b64020303000c0103203140210300e01b51500041550003124080d00600800c8041081420301d406508039408144102510040801040c0310040c00e07900d4500d10982c1c1c8640c2540300214080c401402c4450144610910f05c80c154144a5990000d03a840190304070005c002d40d80156040c08001604480202d45508100c0c0f03030b40c140403904000031030402c0ea0140b0340070381c002802203005071000e007007000c01c0e281c58051142d041240c4d40c158800c0348500c80403800400005030300303150402c014400703802d41225803042c400e061b4440a08641c00b009100c490b0010f203e00f40018140c11401e0001d08a401e1002882010b00d00c442c00111030741140705280c424281d0380d41e101081800381d0151030140c25119010005903994180d040c0c3d0b100d54820196800c1e008203407000c503003c010460200c900642290042c800b64443d400301c00b00a0090005584 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 495160134 1250 495158884 495158893
    0xb09040c120602090d030e0109080309090406181a07020d08091e0a06060e06010e04090f03120902060304050105151005091c081305010e03070f09020309031e03010305120a05030414 79
    0x20405e60b10016803550f064000e0703a514a00811400026041102e15003040d48698401c1c09519069514801581d5200d54403140206810030301400c2e088013800040c50003405c80305660403010071603210700c401d280b0030390075039007141c030031901181d400d88092a013656102040c2d000f03a0351011404c518081542c440201e208101c1d8001805901d60b40201c42c0e460700280349a91460003800306a6a010891500300081210204411001661441042c1820b02801424000d8451498055010640c4007895281e0040d28440d0f680c5064540b040c002c00d0104d45500105090001f540c455061219106540045039161103252072070102c01c1051846413040104008203038400003d00107402100500030310401800343c461601d0070b01c400540f00b09501c00c9194082e600c2544200904801e10410340e040310314882d00181da81d00c6800c0c04504500c290356404084500d58507400c1003106022000314122800b03001911010200074002e000684208220740002442c1800810702144001e4400044007051074203c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 495161384 1250 495160134 495160147
    0x20327120307030201050f010b070f0320030705010c03092f10030f0501081204090203060f0603010303020624090c09040e01050c0408070902090a3f02040b09040c120602 74
    0x2154006190400c0039541c0012459200b01502400740e00d07000207051b03400d0202e640c1424903403012030240ca10b010740550002080941410700610320705885524540040e440b8000340018180d40341d00076034046030290b02c0c0a24451b03c90b032187c400c401500351300412070450524605000102c140f030303102c041c0c60b8050800c658401d140e5a41950b04a08024517240440c0d042c0c00044a00d049510580c090301282c0c02140c0050020f485500455090f24980d4100584a85540001c070f010502c8805000360001030003c000710503d0380010341d892107120460451504411020306821604a0250803290840c04c2c880124100d29501009820003010107000010700c410500300741d5094035000d580e01480c51070300040c20f0000d04c0d0300780081409042ca0103c10b500c5c01001d02d0100b030381d20708a0311520440660200003094160240055a059982280a00d00080320328003260014210042001c03441949040f01c3c03810903090000800d4422900501d0443d546480d2604480500242e03d104946060782000070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 495162634 1250 495161384 495161389
    0xe21190e0301021804051810020c240108121204080702030a051c1202030103050c190e0f0106110a320a050a020312041211220b040b10020327 62
    0x50142c3c10024421251a004c008017400100c41d40545131200e0044842d4154184680004828017000e0280a0042c1c1d2090030700c40c814240310440d5041005003d080e969810b007801403201e50ba041c0e500c02026210704008410300d203209840791044807150160088000f80202c0e0080026121260014044e0303462000320760740d290304007014a031604464114a00d00604001c2c2c2c0a019102c1d03403440308804608c0e41d411030301d910390b540d1200680d0f9407244540d034990604110414444000074540390344045418180f100f00d012203a403090003510001303141c41141000010000446804264000b1100c003500902000c2c42034a43d03440b01c04940c80304a4a01d08440c900004020400f1224051001303491120b0f07403031040505003007149404080391017042c00240000b00c070400760098041c0d480201322040f000705401051541c80084a000c43c80c800801280002c17260580106040a00c00c0303408102c5205203078100070503540316044040040e031040c840c1c020003880b2041d0100041007200441000100072100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 495163884 1250 495162634 495162637
    0xb0c1306051806281d0405040f080301030507051518150f040303030608010f061d190f0b040c0311070803060609060301030f0519030f120e01050a0e21190e030102 71
    0x440580043e16a01014501401040401400840c60040b14030b90708401c1088101041c80485440b86c0d56a0b40840c00300300071680c000302c4061b400300720180c50f583c0d40c5c2065520b8510502c20b0600805204500500100c505412141d680303503a2440364410f20f00480910400c948810300c0108400f008001d114030304041880034000662080c1c0d03002c10300c0750410300b0141c00d4030b4183c1841020076051020500403a62000012407416060040715000e0355684101121000d103002c041690080c0390040c4007100c104181c010501d00c0e08184e4081c80305540501040302190245400b06203020300a100c0100001c82c80c500440c1c20440062810b805d00e1581400100c05500c00e80c01264045c0181c04084104141070101203010889000c616000c40d2490301c1c0500003a44150321142080050070561395a203e455000c80350f003903040c0000b00314514000007520010601e000803800c29109400d80c958000071600c0d54100c0042c2020680c50402281c900c0d012030000c51103c155051001018062150361001d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 495165134 1250 495163884 495163897
    0xa09020d0605040b04020909010b0f09040c081e070509010c020a030b0a02030105180606040603090602070f030f1805030d0e030319080402040b1002062403070e040b0c1306051806 78
    0x34000603075a80741504000450380803107025805a401030002d032419503158069641150094a56566192200a41c0d680d4a2185081050340185400410828550b118141c6480b0b0201c0d161403030240036240104034902c3c04200c9081d0006142041000242d500c1200c0c1c4103030307a91029212501e0907440340e94004a4280072104412242c0e80480108038625020781030440801c1c81b2607001300315007030000200703005110354003c9006241d19542d01c00c040200ca036044410580d04891448002541840d008100e070980034400800203203810030780100c2020854841c4101d420003401005c1743ea00302c0009071800c5003c440d000c1c1e40340c04180a010306a1000341040400600580d49140c024074042c81048206d0703405e0018140103401e142c5501069580004070030380c01c00a20400d43c21450424018803540e400c000c441c044c2c060003906c0e030015020b2000703c03810740a20b10130342c0c001d041640e42400070402c0b80a280c00150178542c41c04030400446004000a020600075406180c540259100200d2070907440f10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 495166384 1250 495165134 495165157
    0x2010e1c050c0118081533041512260a030203091203041a04050709020403030c260708071a040f050c090c0f0f0d110c0106140d0803060a0902 62
    0x302c9030045580c3c0855141a54410751000340c40f41d42c200503950b0765440300341000240e9030064030003049140700107032281354082c031580c10f01c144510318000d185a900170b00290068002c609000155006081c0580740b081680c2140c4c2c596a282500b0b81c03100341450101003100e0400040b44d08128118408420003400107540644002d640c1c3e01b80b40000e645003240700400000701c68400e1007400000b030426440324123420078841e500515501c07182455420a0072a038003801d42d45200090010030550001c202702242401103485040b0507a00307092440e14a6480010350029420412100002800003c0a020760324007400350b0140c00e0204100721105c03072505580035140481010400c00404c10108146000c40c103059804000900f00555000d202c1d02446200c005850008203500c00030160300c4060700d4664042010502407090f540c209006241c1c045041d030a20b40d400c1c020007040d51503081000d03041c4440083c220001c244929161000160005058030f588402c40900008422603136001802c45001d21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 495167634 1250 495166384 495166393
    0x2063007080702010525030b0603070306030b091b1c061806151802070318031b1d0411011704080a200c010305130b040b010501091e0302010e1c05 64
    0x803001e881100024116003c5a040104012030401c0c03084800680e40c46280c1e48408042003900300307901401c1900200d641201740801007101059141d080041128003650a5890940f98140071548802c0c4450b0300306001c2e5207103a0a00c0040c1001c00840800300d1403924443c1511201d0f81d0b0340d80035107200143d81f5203080010703940341041c001c0f18840c240e400d0b10524422109245800f0001c0c045081c82c4054103c3d00b0350100c0c0e5501031501a410514558050107000740042d03803240380501100c0c06c943c21403545880500c0c004a20702004a13040c101d45102d9803400380703d581d642d94034403000182c3e5041c05810403001f95044030180010589031401b8903c03402600e6241d07404120010110f900b070004500750203185418520460b1004118110031032400e180114040d40d03601e448190141c10030100418070302c150400c00c810b107d40303901a141a120309031384070740d04d807036560311004201041d84280e03907031b0440b054100700015802003901403180790010b00001480040b04248050b8081004015503882d0803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 495168884 1250 495167634 495167641
    0x4060807050d0c0503040b0c16021203040b030901050412020706020a0602130803160302010c02070f0504090809031006090b060405060306040e01110f0c010b01050f04030618150b0901051507020630 86
    0x80940048d4010104e130b01d10303414001060050b01c00c0b8009441d0107400356880c43d04881c5040302c144200d070080c05243c203215a980c03c1590400c2d0003020f00301c80680e24194242c5005500920108642080711505d070f000b8030000b18551680c200075480200c15030803c2d0102c82c00007032054000d101916944007421410a071442c0b190030040d0950b220079400c90210340041c9000e020060305110094280d403800d540c00221b9003554504604248110304e803050703041c410071464000f90001d68002c3d50603141002c40034404514407005002460060b801200d0348108140002105e9081c50341c0a4810508105d00208510004c20240c002c1540f240c1c0080d0b004803400500c87c582c411090145c1600c41e0000e02c0e110746041611b44e2000c4050060b404000c020680311540400500c800c0c1c1382d8464019003001c0141c45440241032050020452544002c0c01903080380d00004452500f12040d124580c03540d0a424a00b43c810b03405c000c200c0d84045e04050200b20f4190281003840121031004840c00c900b064001d6440c02e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 495170134 1250 495168884 495168893
    0x50c0912010f0b040e0d050904020d05180709060f1202030a1b0305010b060304030c1b0807151706030c0f01120501030501090c0b09030a351305060f04060807050d0c050304 75
    0x2411203c80c18050f0b4103054510303413505000a864290325030b492501e103480d500c2c441c0025020303101d600c02c00b120307003030424042c4100441c1246240200f40320820807a400c413503079416000161001403091020340b824241e41004140ca24800d006895071005040d41c800316000d9881c4e2032000707072407140c030b00313010701100d5090003004400d00c242c030358510040b203800d4118a0640c1c0c0081012800510003010f4581d131540c40356000c114568160f024280d040c1c1521900c40e1a60074403200e01280148400004d050b80c441000301c0680707402504d00034074010b0050005400810300b441030301103040442c1810070105108412000080d0b108a90180d0700c07420011609490a080041c1500c0702900840e81500c010000108191b07030000305030352500e9000d80b111441044229200d9000060380000207041090901d1000b01742221030002c0400e5070441000c800d07450f484409100340c60184880d01c0c11401410003091007110300489500d5401921031401a18044080c0500010703a003442d14a40003103813001c0300744802c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 495171384 1250 495170134 495170141
    0x51c09140405043c0b072a02060c03040504090503040608070203030106090e07050c0613051c051c4a03070f02033f030c0d050c0912010f 60
    0x1080115070078405410b0648519414190644000b04e0100840340040c83c00412500340c0005450814941c00700039640342400301801400701c410f031000415454009014100d12416070f170300100d03031000005041c1c001e030b0309000035071340481c00c0b03206644024840007070f042e9502d000b211286440781000e103450340d1400320094050080540706100390740060005002c01c0758086114022600f001c60714940d6900c6011007030750f440c800c1c5100c80e043c40c000e0394100701600104034813894081c4d20843c03c13210280e40a82c1680201200000c3ca04002002002403041181f0402d03820400065049000184107840501003590004040040b04514049074020214031825803c0c440c846011019120b40d5140322222841d20303445510b10007840800401c500c1019514100a40122040e140d40303c07032214604185403014889610100210150140364001d04901c10802524054040402d859083c45001e00c041000380000501c4480d4240060100014564a400881880c84682000090484600c10002058 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 495172634 1250 495171384 495171419
    0x201030219210b01050a030f06030206031302030c03010204050607031115010e01030b1005060a030c03060e090106080f0f1c020309090c090f0f090a0c0c0b04030e030f011413051c09 79
    0x83c0c54100031140a0f40c204013280c20399002468001411503032681101c0050445803c045d42001d004410002000010b041c100e503054001c8007120400d09001d01054240d201d0ad00645401c601c007130086c000001d000d001c40400c0c523040202030342c1c1c210307181045000035800241d000b0035a0616404c0100180550801696000003041c0d0030300882600741030110309207109220407030301010341d07a199a000180c842c5e44000c0280450640f007001c035007080707101c1c23501030417880c003c0d8003c40c0a1841944041d00c000602c140803107070140064041010701c601c20103141c1c0050000c12080d80010002d0f03205568840801506c1500340514551321240f001e801e10800c41c4003003640318040c1c040312510015540d030303900460390312261041c004203000094a500301d40400c02054024024483d9800f440100740e004400e00e0001001901101c4144c4d02d00040c241c240c44414a42c03510704210f074404036440d65038403071482c440075010b801100c2c2140400c20055110050840c50b0f80c00080082c4c2c000c0c001c02c0203040d8400760 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 495173884 1250 495172634 495172697
    0x1a0d09210f0203122503020c0c0a030b06041d0105040606170a020a0915080a0f0501200403060209180f07020609030c120a020f0f0309010e0603220201030219 69
    0x303040980c458040e5607445600c00c08801140c070742e00041c0c00f05042c03071903140581e580d099401940c1780f2001c1d8007501135007100e41c03036140602400c2c40e546d0841c10f121548400721b90304194480c0342038070344000f803000828407800f80c10b407208020000c2c1c420300c020901840340621b118000014400707141c00300e140180ea080f0a2181d250360407054203000543e483e144601f09490324440005030440e11030882d0741450300349921050403801a00886010301c0719006007219500c0c0035400902030302560b2500c25194280e003011059803500144001d201096196003e000c140c00c01030224001c500d52804101c200d00422500403407156003550130041508e90600540740c01c004144001d608000401d60160b4440850300b282c407200c40004154000c08500c200481c0d000710032501c09a61b00d20380194041c0b0748a500003140c0c503010070181e000c3d480003410200202c034440c040305510b00c0300d04444c000e04043c1c84141004282e04042c1c003481000d0344088800080c4001103d9501c62020320b60211407192001000d4001444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 495175134 1250 495173884 495173897
    0x30b07090806150103150e0412051603050702010504030c090504020414060f0d150c08090c06040e01030609030c061532100201060315020a0e09040c1a0d0921 69
    0x881d100011026042694001c00010420007440128014002c0d14075840320750b01401800604105601a85405140240d4101c284501146010b0750544aa440c0d141094540d600c2800003086c03041c6d0103000184d00c149411490a990b9448015a620441d0003400724039584105100c11450103124040c000004403010b1240d41c84d2202c000344031502d070b03404180c7c0201034120f000e204000c00600d4000c070f1126243c10030001c1c5540f4100c01410b241d002c9a926155120f00d000400a61420005580481301400340301f5a1513821a44d071007001c1c0101e01000c40c02d110780c004030840003808074003d20314102014060300da4400d103481d015000c500c10f101200c03200b03d064006641100014022080d00b071050a85241c800c1c40040c000490041200e0760000c0c0803000b42c60f0b076a08421203a500101082c0070280d541d046c00f060010100080c009007aa0020040d00d425903042140031964005c82c80340d41e800160b01d50601c1c11500e4003d0984160010072203088101501c20603c00076503040181820b80d1074600b04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 495176384 1250 495175134 495175139
    0x11103012c01050a050d080c060f100b09060d0c0309051e12192303100608060925050f04080d031b0206040b060f12060603010507030e0c100302070b10030b0709 70
    0x51000913031401303400e020384004d446800a1004140c104ca0403c0159412203507680741440801eaa001c100380c410400c10325812000084c2c404640f800c4c1da84000c1c0041102d464441e16803403420045c14000744d035009054680c0304240205000340714072051201b04407240c00d000c900001040c6c0c248480070a051900000500503103a0a00480d040c0081c4a41d0b1030401040310403100340f24460041c0c2110b8269030940b0004200320b62103484840c000215002c648504004d510740c002040307030803c8100d6144a200c1005403040400882510003042d8444003410090328201e046410400603502c250044c4409074022010b1044c2c00fa0305100700520a040301507680b595840c6004025140d89015001800c00020000800d00c0c070741e900010300b1380100c00149130515120f9a060945d480f141c04440e400d00c039518140000e00001e0007406441442c94000019041900d1640c00b048200002d420015040503402c0c44107400085a1070142c0340108000070103c00c55a24610b40b00d0002d59004005404001101d0002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 495177634 1250 495176384 495176389
    0x501030311010618020a1b11030d0e010e091f0801020309060c040f0303181d190b01021e0102041a03040c0909030909020304020f060f09010809010902010903030809011103012c0105 79
    0x484d41c031400f100300050b99a107007a038404c07501030482d5a0090404942c049000c070812418088028422030150280c4100d540300e207005035201c40d610019075001c54002240c903402e518001c4460f650200990418a41c00320040e101650858116001300003aa07600000b030110044080044940c03084490788064501401c141c00c2c0301c07035010584001424444045e1411504012100e00400070f170403c83c1081030302055910120307500b43c0050303419244a07011070700349078850700d0f4500440002040c1a0014568402c100707590b64807010b410382c0c8111681d50b0a103c0440d0705080700a2180d225641400d81350f840e030419080640140c036031503220030740407490124030000080d009002c40d4111100d510300103803070780d07141d00109918100d803681e0a98000000149411030280141c064580755400b03980d40107581e9a001c0341d06088604c040f801074042030340d00e802000001d218200a0358801590f000100700d0307840c5103128440c0c070342081e0083ca010188840c00d030344191130400d00e2203c0d10751040300c10080130b500d484c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 495178884 1250 495177634 495177659
    0x6070315080c10050a0908010f020a030b04110f07051203130c1203140c01090b0f01090b090907030f1b0b0915030f041101020102120a1401050303190c0309080a050105010303110106 79
    0x21400130b101c4003041907103c17540180030300030040c41c008000344107500d8840c45000080d4030405225010910b81403d42941d401c140c0706414150400c1c0c2e012528201c0d6070000e070240c80c0c000e40300c11201441000c11a00c101070100000c0d40c0120249020301d0901c0580786042c51008200c2c1c0c000501d81044903134900c002c04d52081d500c1c02c04400300507000390744000401e640790141c001a00d0240c2a043d039070040c0028010a030104a04884840008000100d03214040140c118010341d1465007039484410280003103040e089860f002c6500c100395195800d0382512140240703540550040e1400000030031800180e081c511840b601d00c402c0d03005110310350725000440c1c545100000d4005881200803903e41d1855074000d43c1200e081e80a6650504030501c7d00c1c616407130241c000e10001e0503400c43e10340000603a6040c00004d440400100049114496484040480e00307113540740340603000c1080e4814005403011040c08054009070092002007003641c158100136000d1110213602c035015a1400c0d404105a105900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495180134 1250 495178884 495178909
    0x415091205031207090b0c06090d020a08040e07090e0a0f0c2d02100e070807080a08160f0204050103082a07031b0b0408101506050715090506070315080c 67
    0x622000f0a03143d203502100c10300c0c06a0007680c0c100e000060742583c5200300050b4548542c00b0601142e2445419110480e101d4002e007100814204080c0301c14050034248480c10760340f107851880c01400e031642d60b950200c2d140703070260741200d0407568030344c50a07480720858040d101140310b4a00301900b442d80c50140700c100721103680d82c0e0750410306055401700340c1d468030074000c0000d034016042090010042841603030340c940b6694400c102e15446800030026007a00040350300402e841c0c12500441c01c0000e03c20901c144808406801c5491611540c0364000590303440c40b0b0b80e8080c5000724401c5459424042d1162002044c3e00131004811100c52280d08040c0c070005502c401352540519038480045600400d11803440345a04032002c524000f241c082400312000034000b03003947e02030380d080c403100c420000c141000d24620b018100000b01c040040e040441ca050380d10444000041e203000400d19400d4075400c0c142403050320721030000383e01ca400344d17072000d0590041c0e00083d101150151489495000000c1e82481082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495181384 1250 495180134 495180157
    0xf0606081b0f0d050604090203030c01060e100b041e050a23030705130e03040905010b0703090b1303080f0c1b0a0e13020108040f08070303200702010903030806030c06041509120503 79
    0x10000101551031b0f0307030403104100c0e50203404c80b5110a401d0401601030b0038180211204084c103032002802420300e00091070120703007203804000d06e49070402c10b16080250320f8115421403008403e030700040c1c40d215201c2c0d203c01082445034480e4880075940001c0c000c2c503410000ca0b0b110703a002d10421301081c5d030b4218121400c3d8000c1400003a000e03002ca044c42c1d0640c0113a034816421240303008000240b02c10305100074041e01e4801d655180c1007603121060320000d03005241c00c000300710035041014800680141c5c000c0c04d2410140c010175007010b00d10f900240c9445200c0c41c82d21032a01424035080050b00700044010007a00340030b100045185001c1580200c44840d000700a41000b4101b001300d018050b224034010703451500812680d940307035a1030801070054404040820003041c072401c04d11b64401204400d4841041e07050f95051702c2c0c40d1464404588208015040300d9140c01b4031800c4917a0790342e4210041c0000c010b400400d00b4080c0c031249003d03120380b00ca40e000d2074131034219446200014101200b03c0340c290910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495182634 1250 495181384 495181391
    0x2105041403160e06040e01091208250c0305070803090a060614010c110d05030a08060109090e0c1003020d181a011a07030e101205060a0510030e010f0606081b0f0d 71
    0xc0d100014007030041051086c01d44d51034800e080c0180440440030441c21841c540b50890756440d4281d0f4005103110b14200c2c64144d581d01d02c0030000d01c512804d207401402d40a40307006401c10000b0388035240035902c01d0320340341050751224034a013040018074019100101400c4d009002c40c049200000703841d003008458000d0014040207000b9415944213000a15001e4100c030840e40c40b241c20440140200b402070710200d0128081e0840041c00660b2400ba50001e49401405800005148000d000b040110500c084c1c0c24144c082c400000009401e00c142e9102156042922071020300506106824401a040203111b421500b00184041101000300d0703046500d06000046e0794107598103046036400749440d042ca52240303520485003621a807100c00d0342d64804201c0e400704056201e480800c40482d9081c8149a000301001100383c104074069840402400e151000100e10406c1800201046420b6034005c03201040020081c04980c042c0700c540c1040300c0342c000b41d41624050b4250784c10b0303d61b80070300a84402e400f030303c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495183884 1250 495182634 495182641
    0xd031a060904110a1709010c1b0f021e0a1e0b070804080307030e030f0105071e1e020715020a03050706020d020904091211150109092105041403160e 65
    0xc03641c0c4425580660094196101e5180c0c0307130024807401841102c42003100d402c1010a660b0782041c03007100311600d415250150031410016012850f064440002e0302c4071030b030051500e07005d44c8030342d00e1046200c030613181440ca00d8440001004140700329030f08403031004126001400180d81d402d10884041e602000310268450780140742c0700d0210710aa410402c1d03140004100d110800d0380000d1a00c544403421030a030f0340c1c001103441a00f8222007040b20404c000580c0c444d011004c0b004072031120300c001744040c5002c6081c1000d5580c0000d100e460902d5050060b4481d0200300300d04191212018560780582c07000d04814000c60324020b07c40e01550a001e008513900141c4140070040650488001240c0500240981c5599040c821115802d1600d07810200d4601a0100c0c92017002151000801c4418556241e00342d0800304100001c2541d05000c0701c0c900d40301000c00b4030070388503c00d00501260359a0b44e1241e503035003850384081100190181c2203002c0d52141c56100c0101c00042c620005886000e250f040141c1c1e03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495185134 1250 495183884 495183889
    0x507030b090f030c030301050109050f1014091c0606050a35010510030201020c151605030912010204060207050f0d1212090c03021009050d06090303140f0402030d031a0609 75
    0x60b400c001d0640074440001c0700303103d02c84040007540c120b582c2603d500440aa0301c0c018803829043c0310341c4155200204510700d20009015103241d1050508200d015418500c031b450100300c041c081040d4556010303c20b8400303402008014002d0b400580030590704000094603124158000e601108148502c0003e0707102e1703503030260100c400c0c981020700600b4020301c101c3c1050130158030002041d01041c0d00601660380c50341c1035400d00c40000d0881c0701c503580090385048041510f0b07400314450450304841c60b00080010480d55540e1036007507104410140001a5200c1c0b81c9040685000707580c0c3e2102d80607500750014407a50b6950600380d120003035080850560090381042e02141c540070081d0040341542d14107211041400707420050341c02924030a0365640b103020b0710303401c0540e003211403031142d0380e03118083d48081000640d007500041a5140700e8200420010203842110301c800b0000c940b080c00f01186502044190b160411100107d00c0c003a040410140b59403c860340d0703500308428401070141800040c07904154 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495186384 1250 495185134 495185143
    0x30807062307080f010501051b01020702270f2806030203030f070303050c0301050a0b0703052a060a05070207060f0e030d050301060207060e0a0504090201120e0c1207030507030b09 79
    0x42403205100c41d2100d010680042080903a00700d0001400700001030b0000c480040c40354161401619210b00f4056102240306110901c00340b0b00355195001e000100068031b6400307000607400343d984078a01c3c4c003028502e90345580301401000078a80e5001c10081c000340d031500250b10424800307190001c5a048201004d901c001c0c00c8581e00094252000150703003081004410054000c5078420364084c001600c0d8101d24078194002030003810342c0030b1001c101c00c010840480005000140c400e0400e14140700c5651185103e1410818080c1c0c0e20840c92541502200014460541c0c00b0f481d81c6800c110504007204000e55803485400303214184044118540b028500071b21400d60401c0e8000c2c11251500d00180e00201560428402c001c00351095900c003080c29409030344605100d01f0054084030302d1516003c1000b0182c400d8440a9040c4041c000400c030340c092841c02855100012180102034440d40402480100e00ca51401078140d500220b00910000310302046442c01c403900200c0c81002916a4069035060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495187634 1250 495186384 495186401
    0x10050c0714011b02061005150a050309070807030503130603090335042105160b060a0308070506041704180f110301080f0c01170a0e21070b0109021303080706 69
    0x35840c01004480300a50020304a440f940200c8030758942c0d187d84006100310a00d0602c208030f01501d060005080301441400919803005a11045950203580d6105442c200012600305480a4100140c06c00c1114408040100101010b190412442140d5180200200a10400e0100b03510040d0701003081030010025480002442c0e101c2c86009051601e020311648030003010420003203403074000c81e2442a015406541c1e0328040035018815240c19955401031040d40144840d500c482842000302c04155244080d002d01c41c4294020403240c1000e040600c25290f604c103840410304020403052042809800d1102880c440b59180460100d0001007208041c0a00d0002c64422110201c00051403140014011810a400b0001e40310000403541c01103074030305c44e0038600c41c808491100102d0b4507082580e01004500c0300e07030f20541d8914088200c2005049a8600c01c60b1054400801c00c80e00b03018840c036055004004070b40d021460966103407a242c048075007a100c00341020718041100400c0c444c03181c015203207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495188884 1250 495187634 495187661
    0x402090a061706011e03022a030a020c040515040209060405060c100e0a0b13020121060611030405010c0318050d0b1906081216080f040810050c071401 66
    0xc1864407814018065819444402142e1148601085465020f000c0c05200460f10f000440101402c1c0a420340207944100c590200c02c60303100702c00c40d0807000084002861104900f01031a0350b154a0701000f4601200028098851460708080c8050011840078858003003a0554015848820030700c002085400b0b26400703290440c82c000354550740c2080c0410b6510f005d4941400800480103d084016524141814001c2c014098280410751105004038420201e510500d41142d000903c0c0300360320041003480c0f1003200c80d84e480b2402030055031303000b014603808044418011401c007403504000034202c807002d42c1c0140c1441200c0c2c1c0038007600d0700c041422801030b00001d4043c0c00c41590a00d4011040c80b0111101c09080501210200f45500b580c0100700848811000900c8201e0340c40849400c0790b40046c0030141d81980190302440065945005442d1007074850700c805441301d140c2040b440c14640c0362901c0071525440d2608018070380d03c10300c0540e0315840d00701581d0110950106043c41c010801c0500b81003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495190134 1250 495188884 495188899
    0x81b0d0221070504051c0807023f060412120c0c020913150e15090d090602030a0203120a02071b03060e010207030c080d02071a010303021615030902040209 68
    0x2601071503400c010a021030030207124010559910300c000c0b240e6004078029650721003850000c0c0c0c503140101e80d10410226004540c50b61130050690f0000b44078180c503410700c1c0f40320600d101c0b4500c000100c0d080d081485441c2011214010106445090f03114003000b40010040242c900c002d80b103040c0707d291400c0084c0103041041015451078071001d8000c5401c0e4200b01e21030a8140e0000c1d925000d50748101007669440489030991094031880b60020741100d010060041c82010b05c00103640354800d844501034692480a41a4800c4240c03000386030780302c160404c009644c000c000e2141c1d038071b5000080b138180d00b00002e140311054030761464907000b0f440340c0107026003210000b848000620190fa0600002c40780b00d800d0401010801d41405400d0380200391002d400f045400c2000000301d1b0440d00100f02901910400603d07111702175664444480b500071941c21826243d10060081503010001408807a05040c805103030701d46844c001824400741c0070b10302020503403a0564401191201e405413094404002c1c00725 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495191384 1250 495190134 495190147
    0xb030c0d061a0315040b01051c022b05060d0c03110a05120625050406081008010e0a15020313080d14071211040807290a050705010f0c081b0d02 63
    0x51210340094030444d4900c0c058080c52a031916207440703071148041e0185c5409051208a02a11044048100e00e9810b016000c0100c0c0c941b03424115000140841c00c8203c0124424001c07045004499004000f24018414940300d0301c00f00d24408200340c100c80d488003d4449000d01c000c0031500d6842207a10076500001e2450401c1d0010b034002c12541d120307840401581d440c00310110100d071610f900c501407180201c0c0d42003100348080740c882c0d0451540440c4804042117455901d100c0c807421510007140d862240d40141a690b02000000002c2ea084071180110035810350400b0384500c8004403907204000e05c42c800005141c003240909030003d440c003250240c46400c0d9441e04802c098841141e6082c50301a05241249071484490f01c103042c0c42c00d0392619002007014504201e102e0340040c3c02142001307100703140d000d000c03c002c5070118014254814690390f8503444205900c3c02c20300f502ca09040ba88079003400e2001d01010f465201d28503035072180461004540a03500040a011144070ba4541ca81042d400000d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495192634 1250 495191384 495191429
    0xd240203070e0307030c14030708030f0703022b120e0d08060a0503030316050c120c03120609040f1101051b030712020601081207150c180501090b030c0d06 68
    0xa18410031090b124081400c0a400c10140c95500c203010051158241d6031060200308000c03044062451005011900e103213071290401031858014004000002c50000341c031104065052001050044c994000d1543c2d07d89080040541c14640301d0120040000c040c0548020400503040144000704000a440b440810b4140060101e102110700030b00403444404009003078240042100e210f0031400c5a50309280c094035004662540c0120b070120301c54400c11a050355403c050000030008154210003e5581b15101042a0803505000b802c080c070400c800420400400d22140c4005041070703008181825801c0c00300010780d024014046201c0c100c050b41001d8190100c400402032100c5130003445101c11b0f03041943d1040f41c1d900c100f4010f049150304491a20518014042c001c1c0c40c0440c403e40300301070207113030301840c0704222403400b4a12800540b02d9014030304031710068000c1c840500000c0c0380c01c3c0101c90802d5554003891002405845c080200012280046c98043d8804405440103034090f0750012600c0d007c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495193884 1250 495192634 495192637
    0xf061e080105090a0503030f0601050c100609231b0c0f100b101707030f05070201020a0f08100509040c0506070f05241303030b0307090c02010516050301050d2402 71
    0x24030346190701c2c190114800390000201d000445070701c400150300c1c6a039400b0b46a060040c014080d0b9050200601c0043e103009010b201c0c1d03407254400d507100000d045142c403d1034015102589401552032049201c40461018109100c1d03a105400301101010320050683e420464403855103030480381d0160700070210781c8840218034584e1a81c0c00c60018400541d0441c1000046c9a208600402050240144001c00501c41340110b0f4410118100000e18030420982c44040e5007041702c6600050351700040c0c5408603900a00c2c000d00c0510365103440130340352800d1044221403480c180a00c501c515074040001d41000001d20700d4202405010f040d03a6251905450a2000c00b10b40040840341d9000e074510903031400c020032081200c00c2c5101c4c01091516264414902903410744d5100036410151600781c42c0e04551030070041d0400070406030800080403005100700908407a0081d003d101403540c410f540e03040c81ea5204056030305403001200c1002c1822640d2600b0800807045da5001c00c0b03844c8406c80c5071072000b0202d50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495195134 1250 495193884 495193889
    0x804060c030815090708070c0804030b0f07080417090409060c0203090a0b09030303010501030b0409140d0f030b03030a0e12070323010917130807030b090c010513090f061e 75
    0x102d4148841d12540c075110f0000d040c1001041e0000038130000a4800740c80f600c200b42e0829454141a1281e014903121b6200c50340c807641050380c041c02d160702406011506107840c00c0e4880d03607500d807800f02400e0036610350280c3e58074801840304007100400d1045181c3c1d80c550054200a44c4804100602c542c00c60019403a5000459203e2052200c4940003a000c05480c0480d101600018013640c55a8240300055005000c0e501c4110780056584007004001f50004016020f940c00c0000188000e112002c00100100178000720b0700b082509100300c954446d2400010384540341680d0600504107481c80000c1004034401800250072445030450000c00d0001412016840b03a6404080414001c0440303485400d84000c00401840c60141d1410703421840d1088024207001c0c00c03091300e0800300d682d544a03100c1c40d2030340741d800c01d84045603c1c50601c0790b5800c0030002101c03454020700b011810580d4508803541800d003207220321001203031030710f040c10381c0c540301a40721001800d00c00c170704038541205012403035140ca1041d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495196384 1250 495195134 495195137
    0xb0408070503010608030f0702010309140a0f020f060711130212010b0403061415010804021302040b09040609050601080a0903090b0a0c050601090203010b250203012f04030804061b0804060c03 84
    0x81340c045800c0001004440303103028000061480c204450340118000d021606040c2c071888049565040c2d035050601440744014060440c4a0004545004001c00e00401c0c0c601d661064000300051000641842c1e403607001400c04680c04108440c0042001019204036207403404a581070038004101e04102c44080c01c1034034000c0c2401c100700100c045000314200c00c01d0300c45d80700c0c0c0101c10b02d8420240d2700c0b50652551042c809013000c2c090b010340351640c03c240e82040d04015255080810503ca46003040d2080c3c00083c04810400e21442c03c0c030300000707014400702420f0b0f8a809510b507125101454001d000c1900102241c0d5030007640d410000740002e00d003104811088885005180000540c26841c0c001c0ea4103880100c100d59142248601d541459000644110b0201400e18000c40e80565400e109200280040e803030f8803c484205007070b40a40c5000c1c000300030001014280010300204500c00180c1c0d00f5268030381032200001111300300f0400f160503c030f1001400d110740010045030141e882150200101d209 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495197634 1250 495196384 495196391
    0x61e0603050f101103130c0e090a17070f0b0403030b03060423060114040b040905060a02040807092304020f030d0f3519110901090504052a040b040807050301 69
    0xfa41c0a5400d03507102c4280e074036031030301c05002041005481c894000081445140c0308450a6960f940c100c0035443c0807941d48030143c2180c0f006000b40081a0031a0740c01108100201e4a04081d966448201100090014040c0750100d40000c0415019070b10004c82c0e224001d040350920729140c0b40042d001200219044203c0c5002c0000f614001d0b00040c2c184e05031180d0050440840c440d10342440300416140e2181980581c4a0f040c2030080350042c00b2190140b20140f0700540c0e951b040008841c81c090752a40000101403410010403c10b0011080e400c1400d40c1d4003211005a4446000141400280a40803681401450a195101a040310415554902940b1614004c02c0ba015034050200b28540b4803409908100c042000c04006111400d64001d18002c001c0400c000000880c504481c0e48030006160f0f04000180515950f800005c02002000e00b01c90070f000b00e1800e030a40701c007518000c2c0c8100301d071300b101c07946030f49220003c900c02d4030301405d1014105074179030343e0700c8811640d21100307071080710b00075442c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495198884 1250 495197634 495197653
    0x103060c0f050a080c03060d06060f050a1d0705130306020c010b0a05010f0c080a090b03100905061509090a1d010605041404050604030f02210c01050a0209030703061e0603050f 77
    0x10000c3d40c50018441c1c48000040d5104000d41c01d0a500c020f0900d0350103c0c120100c180010302c1340c8a080d000d40311810240030031a040070180301e08001c0307a1700a040040580c07603080d940140290380c695801845441c041c0c1e02c44031180484196207489410040619001080c0c461000c0c405502464009008482c100e25080d951001500c49201c040001c90004c0c2543d940c0502051006009109440303180c980040c4141c2d9544100b04035400540d103209040120307201c10800c140050050a070480d8017154203100128080d442041c0da84036000301140101c40000c005032032081e207a8000040f060341c03140700342108001e0841c0a4003d02c10b50140510803490a94100d4541801200191185910400904094582c0d0300d0130f4507620301040300e10046104074410456414031900d042d44400880d070b05c84071f1700d03030740791890850a462009040d52030851060044000c1da40e000507045086a0300200300044220400904101c1c050144030044015170805034004100440014945401519041501c03500341 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495200134 1250 495198884 495198887
    0x4080d03180c180f1b110c0306040506070207091a10020f06010b220302010e090411060a0c060e0a110d0201020c18011a0304020105090f120708070501120e03040306051e0103060c0f 79
    0x1d100c0385c84850340607102440032241c07500800c4c800f540000210b04648503801d140002034a0b000040358200d440c3d4101c4401e010b141034041100d04085d0403e40320074056405a40d150030805241400340364440d10209045a0519009012a882494615050342e59640c2c40d140102d40710340c001c542194404101c0d0300003520341c00901d0441c80580f68165540720100c2d203400c041000c0c0003000307001074074061408000205950349030401841c012a140d01c0d0104000c842303003094800c54a1603c0824150b4001c1070109001600c00c0c0680c0c003140404888800c80882c1d1800100c0c500f440d003242041e0082801507030b14206a480710a154121080700507440780070a500908004140020317500280410002d100b000e0840c98490360500002c000906103c1c120800c1b150f60b01d107460900d034022406038000850a000c5035034405140c5502800302034060014409403521644d5900c180e1001520380c035603c4010640006030394800b40c032540c4d003000c2c00d00b55550312404e1070b00060002d405d4200200307101600d00c0c130009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495201384 1250 495200134 495200141
    0x30e04152709020609040510121209080c0a0b0a02070f12020405070c03051602040e011a040506010203040506031f1503060e011a031311060d0b090a0204080d03180c180f 74
    0xc0d58040c0486013450905ca00380005060081c0001182194864021885c1c0c10000380000800d4000d0b4110300703001d803905402414800940d0441484c0340c00804150350789440711180001114444040075580e075040007000c80c2011007982120000e41360300940040e080030036030500300c0b00e14001c850400054481000a941e403400c0400e000f804a2424460516010350100d100611180050404035064101c480802d01b1200c0c6080100e009420040050100b4100351240c80c2c0d0081084c0029444d2908080004600f4080103101c40c4003400440740d1010307103429a0b0200f100070481450307004400582118054040e00282c0501201841c04d080000b0f00500b12045440d038101c040c5071118599203601c84440c1060440f008150740d02452031410010340d8807050018501a541c0354000503118207040d0410007006000f030084c01005005002c180301c010340114080c1e151820a00f400580f1607040c034109021040510130241024800b0140019105102c5918131144090548108070f0703107507001001000c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495202634 1250 495201384 495201401
    0x20a12211e03090c0315021206010302040503030706050a1b020a1502040501050702101808070f050d020102070e040c0305060103062a02030d1805030a0f1d030a030e041527 75
    0x554500c07840e80600c42c0280c0c000c00038540220190000ca039169110f0010550f186034103054915400510070080c0c0001c00f4581d90804803d00e015490030385840d001a17542e00070140e01600c402d586801042e210100d0740d000c40001c00342c041c003500102425040194a5a207040340a8603000f024002200312107000b84211401d82d5416151542080703140e0b028011800d440d40421f50a100609803c2703100c01c0c402003034103c02030240c0e000600740142070001218040000345c1c04540900c504100140041c0c2c2c0103e1003006450b210700080c40713035a07500d04280140c0c680c41c2d48058258000d4000101c00c1c420f050700324401711648400c0d20380940b81e00507500c0003030740030f0101548016001400700c03d103204805d401c0001307003c840c00004403242d502511541c0c00c59201c07010305404034070741c841d40c1d45c03881e600074848a07902c100c8440341160b015a410046500c070114035400034100070b0880000019503441d640890700b0507000003500d10f40b40f0348901c40200b50f0a0044d40300c030701c86030700380301d14846e081145c2c082c0100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495203884 1250 495202634 495202667
    0x90c1b15010e0405010e01060807090b0925210911101d01020106090614030c0904080a200f060601020c10170604110a120510050913020a1221 62
    0x506a00c0e280b500e1111420161080b14a55220701000310340309024020b0001034002030010704491440c200001040342ca50070080790040034800c1c104404214054805c40841004c01c0035860442c1085500700c91900004100c04800481000d0501c0c010545600a640c403030b1044040e065107401244c1084401c1c03c0d0102e600b8000790450542c0d80e100d508600c03a903c1607940c18000401c00d981c444103004181d07025074100300408418a41c070840f65180800a0581610b410b507003c000908194484403202d11842031401d003440441c0c50107011840101d01d9103103042214105a074124580c201a140d15200c05580c03142c018803c00c0b040e95000d00d006c00d4881080100b43c0c4407101202004021000b05510040a09501a0b0303500c026000b0307070b0f011100910b000100750751102608101e40407954202e0314058188000307943c60900500c05c64550706101c58006140b0700d406113042d40b0900c00601c084145403c8500240008080c0c41c1c10000e0707070806055441d6202443c901102c1000400700c0d15401a00c51004c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495205134 1250 495203884 495203923
    0xe150a06030504020616020f131a01030b060d050709050409060902040e160512120a0f0f0203040506030406020706090204020f04090f141801020d060e01181104061d090c1b 75
    0x400000c2c00c84402140a803010700004101080030780090046a0ba05400c030344035580710181040400c0b12b030780d01e0101204d03090038100510a50038010804a006d1040034400a43c0e64a001c5002d82e4091000500142001082409518001d01e003a10141c40a4a803c03801981081e00d041c00240e00804d04105050741c1e4100e0726282d92902e0100403030341c41c0742c5c8a07030100e6004401c11071a01e0541e41d4000c0210030440e46070004100d5030b202000700484590b803041e5007190411302052080c0d0f6141422207170000c2e0441005a1543c2035801c2100080c404104025401840090140001c04884000c3e008440324804100844042c4511074410b80d82160b4917190060700c807000207a8141d40c000c01d0603100341000d200050916081c01c03420012201e2a030484c0740d080c14010010480307600c0300070070350103410000c0b40288100040c05111a08a00039805400144034182410b424400403966031782c142c06400170120815410819152a0154488204841e03901682001540100800201c0d0b240125030898050f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495206384 1250 495205134 495205147
    0x90c0905060d021e04061508070206010f03080315130903031b0305040209010501050f0f070f0c15171801060f2c0105040f020409140f0a140417040e150a060305040206 73
    0x1144608104548036500c0b603503806c0e01003034446910f601548518907503110340d8000c4c282030002a1415005a04c001902c10350040240000303248074003035035040780d030b440d0f07451168641050001d450001c0c14441e14a1403880c001402c001d140d4150070811301d8001d40b4500840c2440d20301412826140100d40294000c0c40c28030040060394400c10007404034031a0385070030f1802c048550030104204c0e840420140c42d16004014000d003481107060944005080c2245803140b254040c02025208641c82001c0e8544d0120810010314000c840b2000760200c0b21410000304205501c80602c2d1555800350302640d0380000d1840c04895601a46048505000781031006c030718080da00c0c05e41008040c00781c5101200801e074003440f000840d413a07140030300030200315046080344c810310f86614001c3c4030034001800201802d050002e0b01600d411280034450b0841d0700825080c40070182d841d6107907520f20a42e03025008205204d070804c220007101b9180c02c0101d803421a8111071159486104805841089c0c9000e0751002d820040c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495207634 1250 495206384 495206419
    0x30b010e0f030106050904060609050601031a210307030302180103060b040b09010e06031e060301201308250501020a03090b2a1b0306090c010c15090c0905060d02 71
    0x24810341c14014000304203ea241c0000ca00003510954046030802c3d25940c00380304100e481d0107051f40c0300b8000c0c0307010098000d14201180300600344101c22070281c0c102c92154444421a2017082c5140b2041d03800312030b510036851500078000c1d400700c1490142051604600ca0856100e8006c40c030866010005150034641800c200c0c4400da40603002480c140000e103450b06241d903c80d100594450a140803004044100c041c000303051820008102c24444e0745004526000e0180015401c0c04032400d1040d00e544540e00852480c840b5011500045a03901c0f82e80803448481d600c2d882c80300085001008100c0103a0380d2040103a81c0d4917401400100800c08400c03041c8000517848014202a1804913402c3c5820120138010320302c60040a0340114840d000641701200c9014203d0b10314a441030154020302c41c500d000f00c01d803034aa041400c0c400b8100320307403c800e0300280b2081d030800fa180c1c5140448d0400c0340164a14280e01148071a02c02d850545040c003002928902d4100b01210080d41c001d0300c00c010100c1c41006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495208884 1250 495207634 495207649
    0x5010b0f0a1209150222050907120b0306090a14010501030506150f09090c011803110411130b07032a0201030e0f03120103060501080601120206160b13060507030b010e 73
    0x415010742950b43c00160049881c0036044216507114043c01650350010481c00b02c000d1540c05402c40207060b41c0b06082046446201a01e0f5101480303140080c40c0002404020002d00303031020a280e4544111020702034425004194803a0491203440c010441d0744e0070540242c2a51424031020713050b604001d0004030040c0c210708000c8103c0304018000080b030360446000440504054807008020b51080803003030840d5030051381c81100b107000c11905122051071903950509040f8080f04550045840e5408a4800c1420303c0650b407040c840303d288040d8640e2508150300c410f801814090f000588003140044001000c0705050030900d041d26100820750b40c582e00150f001e800500124581417094401420607104140701a1044d054140b2201c0d00e03e51550801c1800c1d10701c1a048400c0303030b401c0721004000c806120405096625419902c490f00e8010780d4140758074000c921040607124010300c1041200030b06141d07001003415441100c0401c01078440182c124203c8880c610004c3c04500030184a40c202d00d014003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495210134 1250 495208884 495208907
    0xf08190302071a0c0109050d0206013804120305030a0b1807181508011a09010801060c02061201090b0306070201150306111b0d0f020111030f0604060b0c1005010b0f0a 73
    0x7190f451601c0702e0b0124450856815590a0704d00d6000407032102d000300c0d414004c0c5070050400007a50402c908620602d014031890a51800500400b034403503520b112103221094400803d40040030054011440c2000341103680100c4a90b40c01d90315004c1c00015924040c001c1ea244005518001900f40c2da03049800d41300201c0741031000d800c0841d10b030800559901543c5800c2c91061455035032242c194074000c42c8160705201000c0b5003a100750140810b10a40c0d13400750303a071411102c182c900384880401600114034580702e4110310403068903c54001041e0f1304030541201100340300c1034040710000e5407240c00480c203e40c0601c803039021a915204082001c2501d640142c00810b44102040746000702402b0204a082c502000301042074010a010700c14550700242070310b60007061030001f40044054050039449921005002c1000074040802250389900c60b94014800b400203c914240e80d420103850b1269141580c440000007507040800100b030044e107140503265110703406000942000c2103414240c0303010ba180c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495211384 1250 495210134 495210179
    0x160c02120609070e10060f230706060302010e03010e03090411090a080a1a06030703060c020c101d030f0a060506010c0807061b0503071707021002040f0819030207 71
    0x30004203260340500c1501d001c0d499100040510915100011682d800001e1684010140c0d01a040009540082005103502c0d058900920080b030010841041c210050b002c1c2c22544e007000c12050204410361788003c042c0c5e8001d0f2291005902d0103000c045c0ad8034121881241c09804c10300c20f414050030590010f4102c44140101c042c2001560340101d00c5104840d40001250340c000c2d968401404141c081c400c4020312500001506807a0507008603640301c01c540f00040160340e444140c0c900d000d100348004000100010511036803200c4005004204049031015841803a540000c140349525001071134180c004080f8000e400c03422602e0300c03441d005050040466050165801541d8001800c3c400140f0480b84203003030010f50038502000301e401d0b0b2008241c0b44070600900300140704005400034044203d1011000c20070809542d42d0303030300302e0902280560421499002050200d41d040e540784031482681e0406044858841440d909807120b90141040075003d03801c03100d000c2c0040440100e4240111490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495212634 1250 495211384 495211399
    0x1101030f0e0a050a1b030b040b0a111803120a0c0b0603280b0106030b0102150c09030703030e180c220b03071707090b0d0b0d08070b04031403160c02 65
    0x7150300c402c0c205414040308075800e0b00010306030020041205041e440502039040a00c90160542d03503036200c501c1000c2c00103480301c044c01d4002504052150418861240d402458644a0213071180460402e107000701698428019418240e031807500c01d0017514903e44540d81d4140d0001e01686070940d1b8014083d00858050155a01040d6522800302c01c44030104504420041441c040b41420110500c068200504040c1402c3c0c140003540e030300091a0649010012151107581c5502802c282d00b071007078a6026405008652000081c1070300101400d80001051380e886503010510145280060f600311768170350080506200c688460b414440507a084000c95841090400d512040c0350042c0b40c2040303c1e8040005d40c030340505241c9458030400c01d60042d00074100341407401c0c28410342e01380502030f155040d40300b59942c013001c82ca0b030303529900610590368101100741d503540342c00d0510700c840c80c000b128158081340005c01c5929121160074100c0703102d8080b40440d4891802c040700704035001581c012090341e01292 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495213884 1250 495212634 495212651
    0xc021b13090305040303080907050d030305060f0a080309040f0516051804090c090b0904050c0f011b060603140f0703080c0a020927012c1006080c0a050d1101030f 71
    0x414410041c000c0e000352182c5840700d10310b260040c10842e00074003600054114000801090b00c1e041c80810905601d414041400c1c1e4446011481c1c81c2c401c5203100b544020310318000200030138044010300d20500d09580512004803a03d0500e03090343d00603600c42c00c5044c3d801d4902044079200c0c0001d420102145c0e40c91020b03c14040e00003a00303030b403e80b0406558543c4582c1040050b80c48070301c18188000d01c00c1d80c0c542c40c1d038a03007030311350342d8071071660014080c001c20f45641015103030b0384100b2221803041056600003021380c0d114140f034001001c95020855004615204880080f107000407040303699080d600c014941c050556581c03114907041f40d40400c0b050321805142d600103950305403009108600d02070180314003106200d2201f0700c200340d010481030b481e407405507801c9440c0d8081c0b1150348503924070500400384a4006010318a443c0c2844c0f03844040c035161800114a1324804190121030310000c442e88a64640c1b0b820030484080c43c07916006054a240654540d01540280c0124042c00401c03003001a0100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495215134 1250 495213884 495213919
    0x6040305120a18080d0f020105100302010e0d210813050709111b010903091e090218090910060b0a0203031503010e30070f110f180610030c021b 63
    0x10704640025005420101281740a00e500c044400c0009240b44000d02803400c0c641100d00655001c1d0002034104002491000580d4646400201c1c400fa0f1184503074600f00e0452286003091105088288001115200403a580e90b000c0340e03090b050650454050b0012514200c81180106a9005000790b42c0b60b0500002c00d94201a400100008100304004282c029040c5001400c51707107107030002c83d82180000c507907840302c00b00030b040e20341900d01c01c030f0b40185d9980b848000b005060031307000004c591100080c002c10032034260104004003a00b460140500402c2d840d001680018040c1d40944001a40b091000401c1440203049016100c0d8000d4000a00842442109814094110f100306016502c0d2480000d21602c40b60351100c001400c100503c0c1890304a80c4c0e40d080405180502504241c0c6007a4000030f280c3c0e41001c1501174060050000c0600740764003005102294045410794441c403141040c490865003c0d0040021800c2c0d554040c1036244445000c107101c1d4604001c03d90303004010794954a07000e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495216384 1250 495215134 495215177
    0x63106090507020a020102070603050c3717010515090607060b090a020a080108190213060e0112020306060312220504062601021908040305120c03011406040305120a 72
    0x901d0b480c3c0c05020b484080b8000603140c08041c0d800f2400b00b40c0340100300302a6102d00c4c0281d0300300c4a0000c4003403007043c0241068101103008901000c0c7e20700701d4410101451a000302441c504442a102500d030560390329010011182e0741104500700c800c4003001109002e1401000420525208480006004d41002e02088102404a68500c00e0a5000918080050300b1252980c0106507000090480113100c0c040d08050502c000f0f4005e0144603400c0e8500500045900607801918404442244960351006203401040c65120140d009004460225280342404110007070900d402050705072918a83c1241620103804294034421030b84003079403010505a50b54000d031002000884005040c0400e0020254650381b6541801c00f000c1e032041100c48040d0b441c9400583d28811603040c002d0041d41c070b030304081d01d00f4403400d6000c0020b403025400f00b15001b1041c5014506035084d9001c8051600081420b00000e8421400050900e600c940354003141c98900c0d400a040b9440d840ca01803035131144481801504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495217634 1250 495216384 495216391
    0x170c1b19060c0207050406050d020d030203040806090102040510020c1509010e060f0a02070e070c06020a03020f07140c040207081206010c0c120b061e0d08040512060f0631060905 78
    0x40c42d4503080701044695040207290050710013100e04104a030b19050000d80707003032031500e8020300440341c4004141c1414001d10560300200800c1058074900e06e019403925000358024010280300340c5100d039030340c00c02d1880050f06814000e00949038883c4000b003c102d00c2d4490b000500050f0400c0031103181c15007152200800740c05d190001d5014030352107401030603000e814108182c2041442c1e8054904002c8919440a1048141d9800520042c2d8075141650124068480c03048004242c1740005520f0f0300b0030038128180b0388580817410a80d104021448200f02c1644907504000e81103072800e105940c01d48121000b0660004414140001c041d10b0640c0c1c1c055400d142076124041e03540c2105800e0090040d500646c650048080317412860b0305030328500c107d440b440301c00a80b40c00741441115080130000d00c00c0c01c031806044000c2405038400c42c084542a035900040b01d106d000500b411010404500700401140d51460124414405e01100003501e41309110b0040b00080320b064450500180144481c4900c600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495218884 1250 495217634 495217643
    0x110904090b0a0501050603060d030e0d0b0c03070e10272607060507030813030c0b09030a021006080703080d06122108160c05150a090201170c1b19 64
    0xc262a1a09200b421224142d004501030708040040200550b1810124194180d1500b0706105017541b903008610800400c68000b400b40c03c808062152141c840380165120324001d649010040e5152030a203c0c4000c59031980c07001141c4002c0b20030240c06951080600c1c40601c0c1c0840399901c0d41e50f54503501c01609040d014103032407100c80f1134075080181d080c8801c10281c50320341000b40c644481c030f9400a01c8900020062048050281c2c2c0103410548210102c000b0140c0081c00c0301c1030303400d10302881a01c0754484030300e4078058400c9001e645401d40d198040c03203080350204400b03041c40d14655226200b055000c00400c1031b66590b1080c01007200c0001d0f48850a00d107008104e2400c448000d03941c0c0c07190707504203ca200341c1032010b00b4003003120340500c00340c5e2610030b40281d20301780f0b0111509180180c07600100c08410000f1002d40010854154a19071244845038000d07611644840f0b40f5103540b0700500000c4c0c500071000b0204212244050601c0701120301c00c00b00400032550f102e2001d07090300d5007940c44d500040300e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495220134 1250 495218884 495218903
    0x3030109240603150b0412060c02030c16080c180114061b03031501030b1014070b01090b01020d1716140a02060a0b0a0f1809050f1f0501050306070311090409 69
    0xa01421072131304c0207009043da05401d1490300307003400c10740a40098100b000801c0c00b83c5070030f00c0d00e4001d8402c0c0300b076401140010085505504942007101103402c0c1c98000c00d2028411500d40244030301c0c21448054102040110b5500700c1e07402e00100360b80444400002075000b0400b0040450110041440350707056240007806940c890030314000919116180c084000c1c101810007000b02c2617139583c1d4112041e41b10490901054104400781c8a041500462101401d007810b00000040c2d80c0803203402c80c0c51052000da0980350b80c440c4100701503c0a012a861340d111503540d04000603e4908030711104511200d85041ca2488802080c1e217052a035480f04600c800181c00c80c00c24007200c0400d42c013440300102000c4488082680c2000703090404c0384507611803402c264030070f440504400ea2169208084007500642950540d500b555481d80d83c4026072180d15600c103070300c0900128124041d10450781a02c1006000d0201c030341f90707200c0440c05400d00b102c403681d82417410802c0d02030710b5550f48030f040e50040c400d08484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495221384 1250 495220134 495220151
    0xb0303130801060e04120309170d05040213050903040e0709091a030105010602030903101d07060503071d01091202210a14030f03060105030c0403060c03020d0c030902010203030109240603 82
    0x1603095825650080d21300302988424400090562416104a462207140014011409041081019842440e00c02c0300000c00030300c5104012080e00720f14842e6000b40d4a110320040c401d111007044440455800982d904140014404c0a03a800c180d107400c09101c1c40d2140145842c0c0002408403415071051811008079a002010705040c280965030040075540091804c20700408040f80d00c8038450b018074134803181d44008401010032007904100e020016403048404990300c0d80700242486d40151180004207848041c880e805501c0c1a07074032012504c06030740300015645410320040441da00d0786822680903004031350360031410852540007141024008000d21454040d41041c0040c44422650049550803c001c4403007580e5003070003241c1e0480790a10740149c0c0c07503491301ca81c0060f5025035040140420b090402c980c11290f450b801a0140c51074981003001030740b141c030000350102c0b01c0c0e2071002030143c0c00c188010488055564400c1004d406c8041030aa6490300c9d2024841ca0b004203078000b880400d41e2030410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495222634 1250 495221384 495221399
    0x40f0f120905100816050c010f02181302031513020d09050c0a1a090d03020a0c09051b0903060f0a180c0e1008060a1e15050301051005010c150b030313 66
    0x300045941c1d20300b460702030f03810701d110481da81100060381703202805000070b40c135000094258801030413081d0310842103480d081140410300d100740000310300f640718210b55504c89001c80d00030310849029003402e00d000042c5c0100d040501003050720b01c03500c0100b031940c02d0144032117a0680c1d00513001103901c1100948902c0d8582020026102ca054105d000b904401e00000f544220b4070703404858919008441e48070094482d071404a2400f0709040c0c00502030704100c0310008499905810a030f000e0f60070b01130105203110302c03143c1e080b409010b07005801e0b034180e0110b000b16104035604901d01e5040b406001780440c0003414520004841c01080750b080f1001c0200540c00c10070b481ca10710580341c2040d424901c040c1740d81e181052007651f0b20307405082e6481c51507070740070066489900b1203451805000d03ca2030030b11200181901c06401c411941c452240294240300c0003d04006011019605886050f16038501e00d00c903685403143d00c4c1d40da44500f00c050b2961040050482d41e010009020f4400c8032a01e81b0034081e0030042d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495223884 1250 495222634 495222649
    0xa29071401052d0f0c04030206040b04050310090f02040b1c080910020106030c0b031e01170d050301050a060e030102090d150c030b0108010302120c0a0b0c0c030a0b040f0f120905 78
    0x301002d84002e1400b00c2907611003000c040f141c1003030480441c00c0160700ca201c0000c2c910311807948005c2d442100050005208080240a003003150340480641d540301c0a202003c1090314541c3c3c2c402000018500603100051030142d10202c00084058020f01040320a00b00311034048507074560964246201044060251034001e94101d072a05c0c85100030300130a8610741e562403401d846030040e07001c1c00c0d40200c0092400003408103c244104007001030f240d02561745403000c042080c4103152143c801e0191030b24950255004004a80c101c0f17801402c610442894800225500d040c1c0e9407032a0b5055400700040d0100c0d0f550440c88611003801511560130080b024891401210b4120404100703044c03c000038282c091382c11401d0641125019244403402052036004181404a0b102009610210070f07003001c1040c14081019113401110703001180d0142c1880c20425544520740980184250748180c00540085c0c0da0350101c11515100d9034400003413a50036a1004030700b85141030103c00045108004014600c0c001a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495225134 1250 495223884 495223921
    0x708070e011d0117150a140a0903050d020724022218050a020904060308031f0e0a090206191d0d0b060907020a08040e150a2907140105 59
    0xb00620181c034031499003144800510030410710444c041306060307904005000c076842c1405032190150492034100c580200a084446611801010031000940b200019125680290f5015250f650404520005c00c102940c17144030708039107210203992080a00c01b15543c071404c0c4017001080c05a220b1003078001c84411000001450b410180b42c0030000c000508421980700c0c0600710b00722022516980310841903001e4458464000d03041442e0003800401d10940314040d50150050080d249041c8201e00c500101c840064010020301c901c144003c2000254540e2102c2062403014140c24100b501003c0081b030080c1da100c00c0c0c00e0200d68070100f0031400310b4519003100d070070b09030444245070010180d444000e908000102140c0c05000480701141c080e40c020002c50402035800001156140d03202c90b010310b2984015034055083d60380d034010304101c03403400030451001e0380c0c611101006100600b50306c1c0e0b01e9185c010b840c2091540d0041143e18081148456030380c00310310b214400031989003490b42c070746000c3d0231480 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495226384 1250 495225134 495225149
    0xf03060103050717041b0b07030f030c030b0109120303060f08060703110c0c0405100504020708180a05030d0c0305041503020c25090902040e06040f0b01050616031803050708070e01 79
    0x29824032144544d50703078150b400a03000030010348206c0384481c00c0f4002c41060b80203c2c065103030224203d020580c0c490401d6606299550301404440040c10b000d40039280c005084501240c502c0f0401d2103007503106003010800b0f602131b2501040700ca0b03a40c040d099a08140380c010404980100081002c0399416008030010601e2043e81c8524002d5a40d10b100c1d101c142400341c5500c100e403140081030034a01d400c070084002c1c10b8014000c42d1364480524210300c0b554040e10140d922449038000611042c41c24543c8042210b001601400f800c514001c4111124280100c044051010520000c2194898480f40b1852030840b070701d005036070b4a4140c0026180c03240400d03403855400400b005410100d001000000200c4105140108401b843d520001d0041c00421102c4861441440100814812200c0e4608091405001c94a215988407400c2c00920300c074504181c16298002680c90000170310502c0346403449410000c0454280f600c0e507513400e007400d80036440b010090f0300c80c510501c001800c4858086c010401d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495227634 1250 495226384 495226397
    0x40b3001081908121519091125080706060e04021e061b12070623090a03200708010e0114060a06030b01020307080c010c030e030c062404020f030601030507 68
    0x583d52420110b1090b01440388045500c0d80100b040301d01c103e0307035202c2c0074000140300d401c004031008800c03001d0740078600c241000c890400c00c8ca065140310030340468007401198903542d07103c07904070b11181510320842c0b2002c907001a010801900852010300c9108060b1040c1c40c030001e03076030400c2d004004100d80c0b41135568080e00d48520a500c89a62401d0031964150071060b201c402010040c6141d5041c8440000803007800d00002884004020299208107000007044242070100000d0b04490101610101c5a01c0566880b0344510400701f070148013060000c0036071030184e80340d400c20701c09064240284d66106000c2070b0344624441e00588000c3c003d440140c1e081c902d50b1000e43c81d00e14001010240316100c0c1e04240355603000161102d91092007190345030364200c14070f240d95281c07014540380240254141c5000080c41c0c02420f04000360b01000b21546444070074001c0000b41c4407907105080850644490003001980c0182001454039280090031f44021102c043e00d840c5e10300302d0009420760381d0042285040240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495228884 1250 495227634 495227683
    0x9150705090a0611010239030f0f030406021c0c02060702010c05030c071403130302131107060b060c010e060406140f0130080903070e010b040b300108 66
    0x4441c6018411503560389040140c0c0e610b0031004c0303802032003415a002c8005900d00c3c500848003a140342a28003000101641e10070f0340c0020030f8419124022440e0021a0b15030401a0541c0d00355010081d580003400b420f0014508404010031a1441e051905003140c0c2c3e0381c4840d00380e0016a010301030a13602000e180020320820b0b0a41c01c2c01011888000c0590384800c001260ba01d0a2182c2450418629120b04048a40d90030075000c80a40b0540e180c0b004074481c003102018224240ca41b4002c0c1064030454104040c00c0603100e0380d500c0094200000e065401100521900031941024043c24406085607002381c0202d040c2401c00c1c0e010384111014403106503081da000c1c803403072802c41c010382030441c1c00089201c8080301062240d10001881c020036924851800441d070410f1104400040140340403c070200e03629250768081d071100b1890709115680e8a010f081c4410000c110851008201e001062020030403828282102840c051f20041010303000d80791000e0060101201c100200c0d91340d004441e0f0014228203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495230134 1250 495228884 495228889
    0x604060e130f0f02040c05220e040618020306280603021c0f020d0c06120507050a0309060b06130302010807020313051e0a15090f030b040b040f08030915070509 70
    0x501c500c004004000c6084100c040c0004202c0b1800c100e540144103000107031410030014281c0d08165190403a10341d150500302040b222001c081c5086403042d030f0311010950fa131500c0d54030003495886428510302e1801422440180d60901c11103100e003070000d043d080d844600425840d404148505a1b0207007614000040c00903a0365103c060000854448028030511405c0c0b420492100703403800003e411404e0203524404109054200405980c1195a00c00c10701000c0f05070b420984030107a400380c001c41d20401a03866018800e411608840d40110408180c0c50007c102060160b4060b403000710400100c201e003407007150b038003001044d000642440110b040200c4500b0154006100b4840c1c244146400329580420440400b901c8002200003403556499996415421807465010740c0c0002c001060582c010592000800a590540741c00040c00b82807a81c40d50b031090340d0314a0291054603003c14202c00c0c800024403040c021449420321101600400c4001c125146100030080c1c02e03813040c04414801c101d41034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495231384 1250 495230134 495230161
    0x12060b040302090c07120804020f09190e16030c14010f1209020f040c0201050906130b0414030c070f1508010e07120f0903090311062b1508060604060e 66
    0x70707038040b80d0030035184d00c846800901c144551a001007020002500b941071040d00710852611403402511400521101e4600700b101d681412140140c2c0188602e880b40c0c0d4002140c0d200040704082c040482d1030200f5440003000001c21940d0045440108021062046c1c0344002c0100151701000e0070803c0b4181580c42c800f520a455150000002941d2040000c0c00d56031194110404030401400c2003100c00150100240a04801c0307800b22094454480402c400329032800480c600c060308004481e050f5141e550b10080300741400c1111032110f100500690128030000d10412005054a05540c45c0c0d00b460b12100410708200081d401c001d009213003004200b4043d9440000364801307030519141000e0070700c00300540000c04540025054080ca80340c414020507800001802c00e4074000d0007003a900011101c1000351620030009040b540e125640c0451902c008180c24101014054050103d038070203000008200c040065880012564040001e1002c2030800e803240c0000b90480000c034010a20b456103003007606 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495232634 1250 495231384 495231389
    0x2901030f020a0b0a0309021e060a051b0607050d0609020f04090507200a0308060303091813050307200102070317090105040509010b030402010f0e010806120a0c1512060b04 75
    0x14601004141045640300e040c0b03800942100d4103482d440742d01e8102c00030010290005d04a0082d072803612100220301c241110503030b004100500340ca10b0181c28007000c581c5900700e100c400401c2c401086203d40d072006d0074049030b07100307094940e186a15040d442d0703015001da425076400740d040d1520412407294201240c40498003031381d460b61b4000c0703200d4950300c0d002c4440c1c0707882c40700c18200003041710100c08510001040e5049000c1c06990b50508503100c550070162a403003400c0001d50310a00d0140c60b88101c4000d90800d075800340407801c0000c0714006603103031182998048001240c0c6440e0700042000082914007150107072200a01c014802d05003150b48181ca816020f000140700c502004ca159020390f03104400721006888040e008240d0365030341e052200c0d099002030302c003240030860b088806100b2034429018260340c0c841c142c0d91400305031250300500002c81030551800845010316035006000c02e00329800000100000380041c0e08100d2440001044003068003401e641c0329042440070000c3c800c048003510705 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495233884 1250 495232634 495232643
    0x15061f020a060911092505030105090f040c0905090c0a0e040302070317210103020102010b1806090c07060e06010501020d11100c0509031f060b0a0203030a0b0a21290103 74
    0x90f00c00f46130820701180c0c0100403030640d0004d4248100503040c9007290030617120f030344008288100c11050080a66003070109004098000e482030b0b00145c0e98003003107440990804d0285000ca5000c0d91142c002d4000c3e241704072004007981d8043c01408005d4140b80784108004c0c40303100b5070018a0304181e54001d44039100c920024001c3c42c004005248200c1c05071044038000b04140809034940c2074100c01007004400248401d81c00742d40b13041c0100070f90742020003009607082964042c1603815a82c04080041042000d40840d29a600902116001900910850840c40700c0500145440d40c5010002442e0541d002c0d2090f04100315000c3c8041c0050002522090301d003000300340840e01c41c1d6104801c031064050001d410f03601d80f160307104c4d480016880c2e0841c1c00350000350325024001d031519000c0c003030b61500c1303130300d1840700180c3c170400000358007508075440081e040900509048400380d95922070100c00101101500100c55038113046e0081101d43c0e00280d07210104140580350303e556501d10944000301c1488043c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495235134 1250 495233884 495233891
    0x1505031509061908100b030a0f080a050d0e0a050c030d020c010e0609221a0d0303180206031603051f2705180c04090512090a0815061f020a06 62
    0x64141c0d45405448000c000d8040c510410305994004903691100f001d600013001c06c2c81c00590200c942804a1180103050f040388007003001d000240d940009551040064808100041c00b064140d80e80c280100058800034000900c21504d0320306103c0c0c00d1021028040d4402c0d40080034940030b00f40c020404040c80c4009003804040103090001144071445100b880c150b100a207801d49005001c00c0c8403a6182c51000030310300b003098940090000080551949405611181c46810800040d1081d046119000e0a041c1640c00f0100e40368049106508250341c455070a21260100b147c0f19585441100e502c10f0308e481000103104010941c20075a0b0360240110600c407403500e0490b14000380f050309480603000441008104c2c074984204001c4c401018026810300d0384c041c0003400e813118035050181880540e040809400940240c1411f18541d9012481c404d8000340b0342a03000236688030a21210704c4068a001e0140700c5440c0402c208240500d84084501c0440c2c05040c00041c940d81c00541040c0041c0c1c81003001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495236384 1250 495235134 495235141
    0x120f09180905010e15010e010320010c0510061d16260702010b0f010302031b030a1103010806041e03020a0f0309121401051b0910030b0303040f1505031509 68
    0x280054121040003400075070a103544802c4c440f2001440001200d40e070b4600c1e0800340d8840c507074541c10000c2840040e202e107580910301440d20400300440b0143c18014108048800c0c555520740c0d0500c0710f803081c4c0c1d9031300703c0d501d0104000c001d00107203546d404509007000f00c00c0f50713140503842001500d0a01d14202c2c100700c3d00d130b80c5034040c0700c00079084500880341c40160031846251200c0001e01030030a0309500d60080c0d016102d100e02c55401381c025a40205107100f111040071380e060460800903000104900c08040c0c079604aa038003102c00100450103486010013900207172829040048150f10028402d9002c5441d000301080032a501003401261650b0240289010944a080840f03816038250042d0a00200004e0003004104030240c0c0030080c800c0340c00083c459580d60010380c1c001d00c1e43e003041000d49a181005090107a150a01b2080304418031410001202959100031926540042e0400610301c103888600744001c0e0b043d41800c00604510380307002e030318625000c03a10115040309040998000c01041010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495237634 1250 495236384 495236429
    0x603050d090803161106040305010b150906030411031903020c031b0603070c03030b0913060c0e0f0d0204020c0f0304080c0a060909051003060c1d1008190b1309120f09 73
    0x10305d100d043e0014402038907a1b403207040c040d00906016104a200e21609240300303da10500e8800e603000c0540c018075050450f0b455803100c813402c21195903240d0381401b0b08078010a00c45071800c21701c00c0c02d0f40658005e0613490198002d0504c2e01c200160101070700344141c1e01014880c1d6411003246c0c3e0243c0207150000c220481490300340c1c050f18410043c5607001c4110001c000d034102400340320700b20803809424144101011020251488680c5e440e0080c1c00030b003c15034404c0315060140e0008021440030700014684040c81c054030b0300301254041c14500f250070009081000b954100903110391542d003112925015031401c0e202618132100c0d485a120202d0301c590024543c008440d42e207100540c2c000c801803101c819942c1d80240000c0d0103c541910f901d001d143d11a900f1b0031705100c840c01540c0c040d21000c0080d242ea411a5061104000c2d1114039151540e00e010000e48601f201405200d104020108046805141400d0113061000038042001000c0009025503903110140000300d0f18804074200c0340c0503a6104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495238884 1250 495237634 495237653
    0x80d060e1f0b0c01020408011b0f09080d26010e010f08030f0a030504031e03021e07080403020f03071203020d17100504020c07030c0b0c0f07240915030603050d09080316 74
    0x1c811f000394a401d096070111050010300000724900359858064065011000307884060703041c003e601195011040e61940e0340d024141c600c40900f203c0300e0701c605031070ba4401c080e404658260041002c6072032440042140c0d000321608540601010343c00346041490704410f1520078040c104047c810103803594045001d041c0900303000008080c11130070040300c0ca2078400e00078019620010121072103061000c204a8021005800e0f12070260b4030609081c40c1515640802616201080c0346541c50700420500044000c08136610130310f01480781d00601880c01941d2000391130183d01c1d00c00030a243d4815000c125200d201208058103940c5c003142c0041e00e80384402003580ca031000e19003004000118900d80400c0381120321010300561606e50048840c1c00341c20084841c0c6400b045c0c07040b001d04401640415000c0b084041d01194200c1c0e541c03030070030b10140d5a501c400c00ba09880044900110303035131b81c1d03051081c8102406511500b00c030b1030610001d02450441441c0d5284030f01e800001540f030000c01c8020800c41282c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495240134 1250 495238884 495238889
    0x31e0903010203040c060e03030703021f060f0e01330c05121206030106050109030503030f0406020d090f0506100803121e070207090b0102010902151303080d060e1f0b0c010204 77
    0x38001c546034030b81840c1080215560340200004034488040d15107152034000100c50710310380d260b409029041c60b072f4101a4002c7d5207d1000701441034a41c140801e241d1099203424006000b0036000c84010352400c1c242c0381c004100d601544040640060050070780c03840d20300b00c402007500c1030700e00a10000c02d01c1c2401c03401d2900d44030304610142400655030912100059115001da1400c50080040c159120010342d5054203600c00103002c0d40040c40007a91010207408810303402805184054944903510181804070b60065504650700804030700d0007014081c040004c42c1d17000e100e854841800d28106091640c1d240900d8510300c0c0b40004044c001f507008440d800064450b82441034040100d41020500a5114080c82c001d81403440d25001c2e11242d60f41c03050080a0110350054402c416502c1200c0b0b141c1055800000145800c0391850000400103618400520014804030070020381c641c140850710390310482c040e020f03e5480c1c00040c40507555a14081850741142c800884181c0c2d20718000c2c0c10140039008a9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495241384 1250 495240134 495240139
    0x115020f031b0c091b0307030f141f050a090c1205040b1902040f0b07060b150c07060e060d02160804090c090e0907051201061a09040c020f031e09 64
    0x8102d5112012100004524884a1078103032030290740b012051240c1000c0846000221541c060519228460114000e641150881c50042042d5070b055910509a0b207032141030700440080305041141d61100460303803071114100c40e808205414a01000280100c0082c00340b064260fa032800c94565480c001d80c10f2064403802104140540e00d0b00781048110803900719031120303c048040a00b20504989482100e06944440d07150011043c1410f0441c41160031585045984583c1c41030303003004d503980d030781c10302000081d1100d81c0380d82c0c1720b10480030281040c41f00d0740210f0921480d801000d5041d52060203032444103115100041e210340348940100005886c0d1800606205800103010440c00321076001003880c0e40054554244150b5901210203107800201c0b0075151582207480241328a142100c842a400c500b0710001040803502d034402c0b00c08144144660400081c40019520154207141c000c0714550541800034212107600103110030b8481c8940610b08034842e44030010004107000150a444406202 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495242634 1250 495241384 495241387
    0x5090d06050403022b0e010306270c0c0b0a090812010803120f010509130c080d17010b040608010905042d05010e4b060703050105180115020f03 63
    0x298140000144001d8500b60010301035a003000500705042c80c240f0a034040c0c0c660054446442c01102103c1c440201012141010340340c0c2d0001420820a450001481603200c201c401007855041c014401ca41d060261182440500c0711802c0c04103c031454503d501195811020404042910781661184215045940040200300c000b00f41c940001024200750b2004c500c2a01264495542c1441c42c3c5100340321b1168810900c0001421150350001c004280718800d80d00002d202d5203801d226030030030070807c240c0fa0005041610f07943d4002c11a001d12070043c1000c00f1450302d0070b4249a0000c0024405015000d042519103011030100085641c24102050185040202c516003401009100c44044042076402d5801d121860f1002c080c01b0074131980303480280c0c0110384603046641c0c0f2094803050340e0755102d004107029402440b036030341c188840844441d041c038003800241c07a280c0009002c603441070b04802c1c0035240c14444050083c4c108014507040d0f80c40a007100ca070003c045201240380814600d6503004a000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495243884 1250 495242634 495242659
    0x60304030909060807030209040602070c2301031b02030f07050705090f1e07020d0e0d0b0a0926040b25050c1003140411010207152a030906050a0509 65
    0x240900700381c0c00d45292140038414590703242c5050740e0300e00481c00043d41c400a0880400c000416941c01405800e10071481421510f50ba51200301a1010724a941d4001030b503540303403145c01c640c0d00d0301c81c48030184884002d40d1100c40f4074400096a9014911440018000001f45002880350800c078400040100402e420802d1030900d0035039082480c01c0d1510360000c4410400c481001c0407882e0051321a4500e64011301036100c071554215620000a650b80d900083c07010b55000114804490a6210b541e05087c045041120b40c40e03c049614607034010600c034115042c001d411451948801c40d4100d400d1403501d95103408402d54500005805602c00d2981003185a9906003002000b04203c07001d4003040b03078030140e90380010101790142c44500a000c1c00c48115100010005014901041c81844041c41102c201645840c5007100c00c60300c8891107408644001308850420078442c42c0e0b103900410300802180d0b00c41140d500030380300c00024080c40c41849008035403191118072400541d846120014040f030404035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495245134 1250 495243884 495243887
    0x501080304030c0602030c060402061e04091b110601050402070804090c02151e010b03151e0a06050a0c0b091c030905010506190306093f02070b09010c0f0206030403 72
    0x140700784011a0801c5840070001031300c900120650741015080ba0103051190748a078200911584045001010720091310f0702c4e00c8034502d641001d0006400c0c1c8000000d01c54901042c1c10100d8000034406000300b025100111140d00000f091940c112a01a580580c03110224030380810117000704e0300256121880c01e0b0840320b0656000800049441c4540402c3e0398075212155100c25003818a070800d1940130204004015021403140119840500c4c1d009011400448000280140400401c00301802c0c0710005c0d5020645000c075034041c014030382401c1c0300d40703012038001002d400950700381405014130f41040002589508140710300402800d88466181150008940245c028600090240d038107611b0940001c0007402c2424514440d0400041d8540d4910310359500c0b94080e1100f0403049400300b01d401c188040301302035400210303104500c03041c0041c500342c0c50038529031007405007031f284c4002c541c0818000c201d007115440480314000c2081c42c204803040d005017007010825410a40007500b1070000401c200030f05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495246384 1250 495245134 495245137
    0x11360a090c0e101e050c0a030c0212060103031d04050402150703023f07020f060d1404080a0e030105040c1205070305070602060718030804050d030e0409030e151e1c05010803 76
    0x1140d03803d0101880b01c2000800329294061b010b50051107034802000e4602007805011000706040c8000e00f0808080341034854241403d0303080c0c0c400c90101f801c0d203c2161a0344110300b041d6010780c20a8408100340d01e05900001c0e5148030304044180311150000d1800c1c1490b00c01d02c02e001030010700301d00601200700302c0e102180140280c0c19140c1502038403180c020009030800400c45200035001060820203510602c204040d0f40c0c800009601300310340d03403040c1c1409600c141d07084610940c0690310310307901d5602c4890041c00d2601c90001c40b6100b64900000c0100080c5038240300401e45810b046070711442511440c042d481c6c041c4542002d4034603c0380c4e030f00010341c3c0d40c0c0c0064144d12607070b55a5a40700029524400c08071810799240002000340d0400c0c0018055402c3c02700e03015501c40d0081c03814080c0702d40c8040c042404c076259203006600141c0360703101502c0039003004010140611940000c55107482c49a42010071601f40d040000d0040003070004a80024115400c4801800b41461000300100d507074515407190759 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495247634 1250 495246384 495246407
    0x40f1a03010b090423210703030c03090f110d200a050a031709040902040f062d0504050603030f0a0201090c0506070b0a05070311360a090c0e10 63
    0xe507007402040002c6080503e9010300030303540207410940f040400500303a040204541c0c00385205118001c2d5801c0c3c1c80880c034034202c1081110510465407442e01d42030003803d0319425070f012424035040124070800a02019110108960095880c590303c000f18000140c0024015074054a10902c0203050200008500c1580111000454007041c54507650070600c004c42a0754400500907602c0000e481003411a00c0c4001d2800e0f100003000004c604410b903001408a5004650003d82e17103030b984e8401d01c0303201c410344035020102c0840014000654482b030300900301c0c103505000d02c50260ba1503201140c51600c0400039901103601c4602044e86a0085290003402040b0703229061300d050341105c90005040c20f202045030344494025001c0e01c000c1c0d50792500080a0080074001504040c0d941840b8080071201c000034106074204d0007007806108840001e46202e0690404c80e10b81d07000c40d210b841040c3ca030742d4500c400085802140c0d01081d5411020780548040c50701159185c1c110035440d075520b60060f03002280c002e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495248884 1250 495247634 495247639
    0x80106031103160303021f1e0212010b091011030409020c0d0206130305030703051003080406030f0605060f0a0c060b0402070c0e070306152007080102031603140411040f1a 75
    0x30316500480003c080c09903100c060050380115214290303a64094401070381c1000d100d10045480218544680343c072a82e25001c01903116070108400381076100645c0003e0040c4030100c00a42882d02040c00100c0300b50803000030805000c0d0416050075405010f009035001419944001c40d00c8041c104407550b101d9010000780401401001c2c00290b8960f0414a403c4445c3d13055034a190941d030340c83c1d00075401040050a41c00071b04070246000000a0207910051000c2d20f00e50782c0100b04085030007905400e03141c0c07680001d0310501e4180900c90b4004d41c0d2500341c0d0b01d1000e1038507200d01c1901042c1014001806450120ba03002800001c502d41800821440c0c0003c965590000e001c242e0354400c011800c403182c0b4003442203150682c02d001e062842c45200d0400d035903011070b890600e00100f04a4014500000303980140c50a03500130040207600003c080601d02c044000e41004e100440c289034a1605000c0000d00080200780711102e00c05103030f20707a82d00c440200701d89003e0030000a16004a030840d0305030076462651 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495250134 1250 495248884 495248893
    0x6020703140d1b0807200406050102060603150606040b0a0302030709050904050703060e0c0a0807080f0a03091203122915070204020a03020702100c060f050919020109080106031103 79
    0xe19a0000244101650b03450341e10400c0c074412041c60f5031450200780c0000d54206400b40061400700d9094800403020744850010580140d540c2070520041d100380e94015415504032800300030198801240311004c00d003191401158036590200040c8040c003543e00704011080000c240d00341011703010b9004601542c0c440d01c2c0c00551564450401003040d03400c1f1001400ca030850542000000c0340d503002403038030184210a0320049000c54011800c484105e45c0280305560101b4408c00590005110034050640b060000d0314140318a510007400c103800790703c224421b480c916100903060612a0b0710390030720b9021207d414018484580495201e502c202025041c0c02181608040c03010302e031126031008a1401c603005541841c0280c0c0801000707402ca10420310030300d5001c102070001660340c840100340415075922811751420040c00d02101b214a400d9941c41008c0c03820301805520790340090041100406054240d0015040703200484561803da880307c1401e42c01d021012040120300a92900f04280980494 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495251384 1250 495250134 495250163
    0x70b041701060e150d06021c020306130e2a180603010f1e0b0607081914030601270807060306180209090103140a1e030201050a05010b0d0c0207090606020703 69
    0xa40380600a4480141034400d04c10100303814106a0b01d4105610300030840141004a210740500000051050241403642d0000c00c0020924040b01c20a2040741410300c200b20f400540c1b8187d6035900c04400d520240f010007284140300c0c111540100010042c009402c6909982c24002c0789a071110007030b12082e219500f0940150016209480740402c480c01c42e0309042d02c0340e02c0d540f240790300030400961500e802030380030030840010034080402040c903120002d00410341c032283c90300003c180c420790400c0b1802d840b0080090094bd603a108500c01c00c02001d8030000301241c00c2d00c04000346160295444000c40d805a8403000480075095813104048070b81407103a8401500070300300903200328400d40111540c05152400148040f601c4000301071010031014007100d031904403075260303800800c0b4850740c00604003845050f0602050f41c2070044e0740e040b4001c0441840194102480c10301e00707000c0c0c45158054155150b4000e14058030030440340d401024120707030400041d510780e01c000391070305e409010a036076039254035084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495252634 1250 495251384 495251399
    0x30c01020a0c09020a09050d110114030f04150902130605360603030d0203040606170c01080103030f020c280e090601050f010909140f18060408030603070b04170106 72
    0x90015680d8802d1240940c182042d40e0f850003904054a52030400501c51000701c0c20762902a10390400501030403648100954860005214254040020103d03108c240140403007140034105541e08540d10100c8003207528180d403085001031045850280d48400c0d2001d90004c900d505910840c15510140c43d9440a50748102c2080681c00e4816861104a44040b010a003401310801a03c2c3d00004010166444d21444000c0c0c402a03800a48080e10b0f250750358074082100303006c9201d04509c484880c6000d0281074085800180c989141440b018080c0211203c444207030510a00942084101c000d10b01d00c04a4400208083c2d0246030b09095440e201041c44041010061920028403d803500c4004114607800c00042c0070a2504407000941130116070321020034443c007540a800300c484522a01441c00740b03082143e012510301c015200901910040c404014000e8012030100c0d80180c200b07001503613a803915030100389402042e0340220110301c00440c1c003003003016044001814044024000f4802c040e00c4511 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495253884 1250 495252634 495252643
    0x902043209010b0a14030316030306090b120a062004030501060801182102150a15050906060703030203150405180d180e0403210207150207030e060f090d11030c0102 72
    0x2040340e400580c40c0803c1140c0850f0403c805d2406030003405590800c10f460000c1d50780d080070b610701100442d48482c41840204103a00c5803114007001112124548031403030401c20748401c05006c018043c1920b88141e0103441101c81c201d003044210300d6580b1a602c603a40d081c0300c2d00800150140841d0340d42421f034007040b01b0080c1448408040e130000426410800c140314080c1440040f4a250700540c000c00380d0240c400045c0b5541c0c02c0c40b649041c0c3c40405c0b4100c107141c0d0340b119001d80340c020700d1140d26101c007444125100c4c0d800342c0d103c060381401d00503920740707441744074400d060840340056134400c2c1803008215006001450310110b85c801d200441c0c11652201c18143c840c0b02041e15003502c0320400b44001c12548400300a020b8005003e801c0600b480c140341004101780e0f51003146046050fa0f00010301c2802c1122010400805500410045003010729581c1c0013000e0032101c40105108000110700146a01c65010031900442d81c000c000b041c1c11900d504d041c81180c0d07489016140b180c003510842c40507039400403c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495255134 1250 495253884 495253901
    0x714180105031c0309020d0f02010806100203090f150a2a0206030a1a030f03030601020d050408060403051b06040b040c0506030f06040f0e030c03040e130c0306090204320901 76
    0xb005060389900481d4103518203540501000100341e00c5109400141c1c45030500000f03001e000e040802c01505440c00050510000034140703a0180c0c485412540741d15030b000c01940d0381842c040b62010110b401110004560101c2c541401d10a90000518000726136002104004404100c0d62890311101105096482903004542f01a400c15000c10020f040040c1035408001c1c1c140390400140e03601011040402d10300405400000c1e0a41d00000500c4119a010062402d43c0d20840c03030514a03082c103100669440e1040076000900780030002c00c4545e00d500c00b44404040d101100012520b0341e24240c02c16105024043e101910300154a20010030581080002c40388102111013080304992030b810b05000082c407545e49490f1540e60f441107a03180d0404140010103510b600a80195203440c108a80b003600440082e00380035152441da5035880004510030750203003c40760450000601c4a6030707400810f0141ca030300300910058540052410303842c03644c0046089a0095016201c034803960741c0300529402c85200c2c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495256384 1250 495255134 495255139
    0x1a04060801090209120a060606020f0a030e0f031c083115150b091c0b0703020f0f0d0914010c0509040e03090402160b0f0f0c0d0b030714180105 63
    0xc100501c40e5050b0354008101c2200041e0456000201100785107042002e40c21049901c5501c4041c104000c0394104050079451414001620401020781e6014146c023005501d154001e02c02d5440b02102a40c01340700714840c00044d140040121044504001c156143c110b0340c1e60405060000c0e07114028041c12200c28a0fa4a8001d41c44075802294413a40c0301035655641128245072140041800503091400c0e1030001c2444190f102d0311044440308101c001070000b2030485065414170029030208005240440e0064210f0034016580d0200490303030700e074034400c8078000c034140c80c8009400b11190384140c0c050220240584640b101180340f020001303090760310750640e480000f00107005e20000c626169201504210855007100c2c54101420045401d9800500b11210f510448140386414425034a089941c401c0a150207190780d440c0c81010a400c01001806801e000c00010621700482a881d038008803003060004c048403812a520700c0340100c610308140d0170341e0041d00c0c003070b65003041041c080780018140c1d07000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495257634 1250 495256384 495256397
    0x6010608010303051b0c040c0507110607050703021314010b070201030c020c090c0a0309120e120118030c030c0c090501090c0c02152b0f060501021f0b03030714071a0406 74
    0x801d40e5170880000070004a08160241407000c80b0a607865200d05440d1f111540ca0f09519882d0500741000050f004852540c0070f03500c1000b45000003a40854440c0c10783e98100c0e404459441c1440755140100640d0803090307030000507540003189070329804000c0e004d27241c400d81c1c0034044015000c0c000c07a204d9152654443d00b01514402003202c0101c0700d006022601e0b01841c0000340c00788203490b150307512020383d224480843c50b5080f030001c0500f00101c1076000c4513a41d0340240484540d01290343c20f80342c61a1000703001c00404503416010035110302c03c0803100c150040d001c8120f45d601c90855400510003072046020b03240c0741240015025024136011145a60000d00e6581d041000c1c11141c440c1d584160412025401601c01400c07400c6000c0d4000002c1e011480800107a01c3c0c02100410304403003054000c0c906552040d200c1c02c01b2000f079203a1160f218200b4072000f054902c40c41c00840d245021343d41004200035010620b8120503c0002500801c4800410445000410036200c40c549031145000c3d5600160b41c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495258884 1250 495257634 495257647
    0xe0a05010f0c051c0306120c030201080a0f0507030f06090c120c0e060f090312122a0c1b0109030f11010509152a0709110c07060f020601060801030305 66
    0x60000082151264241100b104800d581da003401c1045550f600801e103104034a4421606501d40305042c041c0c620240209a221442d4171035909164140c40000d04100740c102c0040d0401440750040641224880400d219504080c0b1014000e031980c1f104c41c281803490550001400c050500946112044c81d84030340d0060040610098050600c00c182807007030200d0721140702000d40702e8000408991094008068a440c44d00c01003508000b50390041c0c01c6c401e101408001036101412074995044a020102c1c05504048200817406080c840d02e400e00036858041240b080500740402c1c802e040ca400900041c080342d41c01001907426441c1404080e1a5020041d2024005410340030702c00741d12072050401030300301101500094041c50b0b00d00d481c90710440011a409415904a0315589100840f103000070300b40040700d120040d03403040c240c03241040741e503120744d4030620f0903010390308890320304640105840c42107403a0a001360a01141d01290001442a680002441441100b40c00e0590b51b00d6074506103082d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495260134 1250 495258884 495258887
    0x11010e0a15080903090909070e090304050604180608030a0306030c330905030706030c0305090a030203090d02040603080d0207170733151403210f070b090109060c0e0a0501 75
    0x4030300803ca0722003480f04014003030711135a40301e1419105a001c0c400400d042800e2544010f400500a0040d00f011351060001303124a60381c1c00d080e40c0c103542000c494552440070070120000038141a80c05841d2900001a0100c801903041d081001603a002d41e40c8510036070756545000401185510614035140f020500010200485d004480c0040c100c9281980c0c500d070300c4200080c140342882c0e10a4010035074901861600c00d4043c001c2c5030b030024126020300007900c141d1b20003a40b42c0c80b0308280c20b4401c80500031040e003150f403a60b105501450700b1048040d180c95100c200b030402540312010a880f0000722100c1000010341843c112091554080b0140607000b600c2c5684409100c150f01c00c0000320307484440c0c21003140c0f07014810052803654a40c0c01c54005480c0c050305d002c143e8110488180240c10002c1d1052000c00140c9510170b24144481d002079880c0e08440e50011103001c0c94070010701211845051010040054020b20845800340c04104414030414000759074a403401c4017843c0e017110122000b00080e6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495261384 1250 495260134 495260147
    0x1030b0603090604081b01020301080102070309090504031e030f0e0c0103181119090e072904180902100e010e041a2206030c0e0702010e191e11010e0a15 67
    0x42c0d00046400d054510710b12186d6080ea04241c100e109141e5010601d0400d05a0200314800100f01584c3d003000700c0e04080d00c000707104103042c840e1409a0501c103004201c02c5842030b40f080142c24000c000030007040c10402211510b818222100d140000c1c1002400c07802c4210740c4210000255102d00e044c03000382030b40000d12812182c1c0c581c60002c07100f605400003c3c10140c9010f01c24141423420050000c032410551001a46925582d00c0c040b243c120165441c8000c50000443e41034400c2546503030040d1803814644000380548c000d00a40161110105411158005a81c00c182182c01d03210007442403582c1040c0030889080100c200b05451000c8040c40c4a4180032a49007800c01202900204002d081c02030101500c02d2a03000b00c44400000904020070043e44003407580003095440284184007065003220303a603408040282c2c0182050780d10403000c0280801ca503030840d03544221045000320307190a101d001e40c03501242c00c90202e4200c4210780c00910f0507407181c0080d2119002464810208200119541c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495262634 1250 495261384 495261397
    0x121a250201020f0f1e04180e0a1202070603051308040510030f0e030c0106050306040c030b1f030b01090c030608060a09060e062503020a08070806180f0601030b060309060408 76
    0xc0d554200104107441d07002070300400100146202c000e03500d07184420b07000810014944200d0300050144014040089140c075000000140d001d00483c4034800c0c0d4000d2800d0200d1024000c1c1031503400c407040c0d540260040b80f100119005514100415034501d00342000007050b444c0d0003001210200400d00c01c500e0800403509024000c0d207000114408541481e03011240c14450440082c0c1c00071a450300150424040c038800382c00240d010341400d00303140d82d41511060030b0340002000140000006603c106010710010511200360989200079541c82c108042e10120030300a010340d250405001d203600381c1c001e005070400c503514240200300640d0b03151000401421a01e004032480d51b11104990340301502080150701480740843d00704100c80405008035102036035400c9010615005215856200e50005071140c1d01c6940d030f04010081d0b964480000c0d0101c414101c55520144400303080c0103400c10a1006544104000e0300e0801140b00040200503d9000485034101950311600001c3c1c00900004050301e01c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495263884 1250 495262634 495262637
    0xa050304090e010b09180c010203070215090d060f0f0b030a020d030302130b12010e010518010e0403110f0a02100c05100216020d030e01030b0406061d120106121a25 72
    0x900c495988001401c4032030986d9030040008090103c8441c80c08180135590b92501c00340011072500001d540450320311140014000394403003010a0003202c80c1c851214020a41380c0c01031080051303d01181c0d00f00010014190390414240c600500c08010741000104003071035503001003080382610340741d607400c50103540320209188030401c104100060303a841d92400760840c0d03e004200d4800640c1030888094070704005a00c82445a0140001c0800e00d0315402c1c8941e05407800c0e5240c3c12460383d500d00b4242d46060880c1007101c1d09214a064a0383c0c4c070b02000c5101c500152085814450a1409110440b1035406160000d030190308070003907080c1050051f0f4010060605c030203070f4a030510f01180c1c0004108054010003a0045a80082000d219691611885c00285c0c0111010030259007003501c0100b101b200604030036103658902591170451783d01c1110100320f880120009001130b98132500e0039248901510001c83e610b903500c0302c9028400f4240c4408500c02c0904421a400340101c4004088a204090348100b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495265134 1250 495263884 495263891
    0x609020f0a080304090c0f0f27080a060605030c03071202031903120e0102070b06090417130509060603011203081305060106033305040b060c060a050601110a050304090e01 75
    0xc203545401945800500100d4051a1910302e822070701c00c1942d40c5000c003071040040c4007100d03a0f14640c00121035500100d6610300040000c04003403d110300840305000c000c5075402c21510004841c08009141e8241a10840041c4641a076850074541d9502010480c80d50541003601c1c14007140380b01c40c41006246000400b100c07160814144c410200c0d40815600381e00190250244a003543d00e1800b404520700103450007146440055203c241c04160081d101d98400d010300004102441200420800c1d50010508040d0780e5405541c204000080e05104082c010007900c1d00051403807520005990481c0d00a5000784910380329980d0440d0680320040c5240c1e11b0030005812880407503010803c1c8d40c00f824598800003110506001c0c0c00181841e600c3d503a506540d03080300c841d80c058441c980f00070116602540e0116482285000241040c0101c403413054a91042d0420805808581e030040345c020b030401c0c0c85910b204001c24481d01e031208a00400a850350340200300801c4402c0b1140d003c032000d50050000007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495266384 1250 495265134 495265159
    0xf05040f110a0305010e010f0501140c0f010608100c0305060906090405031b0c0117090d0e030705060f0a08010e04050303010b0a260406110a0210090c05090f1005010f0c060902 77
    0x10610764201402c0c2d800042c0ea1040107225030058128814098411761038076121051030b210000f880e902201840c44100b600207e04488004400c01c0100380302d00900f00240840d41e160411640d90b05c42a042081e1200d00f0501c00c038000c03500a2284900070a005070180010355548800e128007454080c00403200c51108100661034030090708402001c101c403a1028050103540da034001440c1039a800c2c008600040a042071005913000092040800a5141044101e02c0340880000f82050400d80c001d03034228100040d40303161030782d24800915a0240c9603c41030b040e86d0302c0b00700d0440d8055080780c0081c00350b0301c2040140803082c4041c001d0001c3c0c3c2c00134603149008005400503018500100009940105502c0c41880204507a0b0b006040043c00f200d461182025203081b0000c1d507401d000700c0c5d14442d841d614010300c0284200c82c41c180b030107444082d103005440e0800100304c10802508850f090107107090340390042001e40c0700c1c1c80c01c00030902e43c075a00c654075000300d912008014900d503601241e03c0300310318480307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495267634 1250 495266384 495266411
    0x1202030712050309090a060504050609090c0409020a090c03020409060807080607120902062b0203060d02090604062103020f030708070803090a05060c211315021201030f030210060f05040f 82
    0x20b01c520011b1034041681d5141c90305120a641c1c016103a87d10421504003080b5501c100054040c0552400311404950200c46e800890089030003900300c481c8107400c2c0350040344419090f4008008845202c20100225030740c58040c1c40c3c4400c458000c5100b030b5000640800da02510901920f1150707001c9100000d2494903607400142903901081c0c036100c02410f0313200070b1211221110b08886400503602425440d6107001e00001c1c4000d40e0815001b4454801c0d880803030859200e1381c0c03185029103220701501c84c011802044841c5d0b0614000e00450040c4510583e908418401105030340343d60380d01c20040303070a101680ea101849a0001450905180f2445040c2d4000c1003080000501403020b20b40e403d580c540c1ca6480349525040c0d006140c1e1100f420807001d006511300c0c030a40312035034550854804984100504102000ba10500012800c407102a40010003480201d01c00e0800081c0f0039001c59050006850068046d20090710402844d01c2c0c0d0840c0400040c1401c3d040007030300030344098000605442a450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495268884 1250 495267634 495267649
    0x30106050a09050618090604060506091c060509161e0611030d0507032c0c010804051504081c0506030601031e0512040e09070e0a021605030d0e01061202030712050309 73
    0x2050030003403034071503040b0302c5d80c10402c0702290084e1007a18188401800c04010032440c6c03040040302401107070701200804081d0640d114001c215a44101c06000c01e06042400c141c1d00c400c0020340400d000300d690000a0220745603041510080028100901d4007407070b001c0103030f652210514a980060104001c0d002d06814980b04007441a00507840000322400100c041d04044030503c101c0b007501007150311741244101e20000e0051444442441e180c280c41d40e6910f412414000700e06c6207000e00c800840184020864410050040d1454070b01c0324204980740b4a40c03940c142c0d18240ca050750144c22030701c0103101140c2c5004c1d4032900010404404080c1a626030b41d46440d050031002c1e03000d0520004101440703a442e60204064100801c40028a80241000304e8620300d414050705e0701c2d03c0c0960005614042c1040c51514510560300314064a803900180c03054003000c2c0c9503800c4841895468890702003840140d6111801540d40c02900400c0346c80e05240c0b10b0421021080c030103964034032082c0911800c2d03554070319 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495270134 1250 495268884 495268897
    0x16050f0c0a030c03060b120f0105150405060108150a0b0f04050a0905010b030a021612030b131a01050705010b03060c07030219020f1c020603090d11070506030106050a090506 76
    0x500481144240480c00c05148000051007480900300410210740712880d6681565009400020b40724806000503400d401900110303006030042504050710003034191701c02441a403408103041c0312060503200300421904203c400390301007184a00441c440d61640440180c00803800b400450b1240e0711186a01204e4001c2c0c03505900d01d0314001014010b90900d905610014200c40b0720902041d410402951310500000300311814290340450111000c84452041c04801a00b200b010034240c0c0f26018000d0103404549a128041d1083e036a0140400920344200401050546030000c0840805001154507501c85c460076201c9648640c44154140d4050001038001da4410440d1540c3d0002c510b40030341000300088400380c0200c0c1d88202240943c03240c01c080054031074115056282c00700c00080540c40c3d01d0b0030300b0029400c03100c0401040040d120000740084070b1041500e0303d8071480c1c00200f8495039004e072801550b41100003480100841401140030704041002c030b00b00258060f4807140401d00542159 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495271384 1250 495270134 495270143
    0x1b06032208042606041e03090308161a090309060d0b1e2106010b07030215180c0d080a0e1c030203070c090c021203100e09010203090105071107030b060616 68
    0x2c0c1c10f02045281900e080c0d02d0050954024122070324254a814041000500c1c0c10746c400c0305820098003c042c0700e2030201025541c0b0440d0a030315291241e8024001c081c80440031a174070210412084181e100b000c242501c0390420800840c6404c008009010454000300e450551898403000040150b984030094080010b4007900455640030982d0304020040300500325009039200001e04284c05a140440d0b01d44c1900ca5154801e95150280d01c1c0807450117044810300310045602c2018409890f17074103013141c002072020724100c0302e0061000c0c0c00c2140c0995005001042007204009101116000300600c3c120110001c190a9400c9020107411100320b03103403142100113810000c0d1080801218013200d4000d025450310800800d078600030041e54030701003e814072141071008000120800e102d01009030140c28030b070342001d0480c02c0060b80c15000c2d4109554001003035080400250340d03684203020407085600b80400070038034545151100f00f15101c000c0c001c2034102e80e080184a1a401c9007010140c40035104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495272634 1250 495271384 495271409
    0x218100c020d0f1217060913080c0606030f03121b04080a050c040f0b01080601120e1009060b030604031b0305040b0703080423070b03130618051b0603220804 69
    0x204d00e4803c4080c2c00a40781032050188125000d9182c0c1c05c0012050b90008050b00c0c9189903494800402d160200183e02c0140100d000003201c00c910750021400030f010b041c0607000c03150034000c0d2113426600d3303005005a08a058145000007000b4410700400303030011100e00405103103000e4440340c41030305082105d5002d40701a808500c9071a09400c20344500e002c0081039040c1005217803071840c0000d14100020740074504210003d0b83d00c003100d6425034130401060b410f940c2150444a11144000c025008400f001c0d11030900c5c4c40038004e00c500b808545035200355415644c0d0090141a0781010303503880c0c002e00d000d404101c0c050001269220150004000084c06504d4010f1a03203030500c1c103901c200304040071413030b0103941124049520707030f42c002000c400340e03500174284540302e0340c0d201c10184402c0202c0300b000d043c41e428624142c0c0400f1b40068001d081a00031401c1d00d000f172691500ea02c1182c4210b56203180c000030b0030400100030312001c007246690216005042c1c10031000940b01c000d01900144c11030381c0500312 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495273884 1250 495272634 495272663
    0x6060801170604110d060f0501140112110a1404080d1d03010c1b030212030c0c0d0807050a03050c0d06080d02070812120709080109080a030b03010218100c020d 70
    0x1481d005030a10314200002c0600d880c2980e03c1d29440201c0380002c502440c1c10410640c00c10900750002002c50442460800c0a5a0359140c519203441520390502c0c0803a01c029581103050a09005107075a1005841c07484c1d02d0110241d1080b20342100c034000c9025181424080400e0760171090000780e6010403144d840d940b0f0014141d10b085c84d00d2519003485c070306c641e2501540c0c101d825040ba1800128440c42000c6480a090718242a0f09001c108401a40046d50000800c454400781e9005460a68a044101c5080c041c0200054400c254150381c1800412000d2100c40b409900ca50000c1394416100039a0504080100901200307172031041c0c215400a40202007461041035041011800514004000b0591280203560807030a521800c14241070502c00100061003880c0a404400700802401c0c000f001103020381c0c241003169800c101c0b68a00001d041c100720a0b00d91905000743c03040c5440c0e034100507512141e41c1003003154100c40200d41c0d806120f034051001c0c0141c0d075a0082c9945042c09038006808251 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495275134 1250 495273884 495273899
    0x7120509040c1b080c12040e15221d0a21090501090302190e040f0318051e010212070602070c1a070611070f030c0c0b040b090405060a080106060801 65
    0x40b0a6100c1c0e0003082030340b00b074002c880e00085100344040d581105032540d95000001400b82841d980030310345150142c1c009030000340540c51030b4809200e5810681428150750f181c40800072001c06075060a1550035400c1400d08282090f80d01000c21401c2402c00c84403140a110a21803e01c0511001a580c14000740e031a0110b2010741d100c44403e40d10b9502e009800ca41c148400a0304204080c00040e0090100f417000034148090508540c0280104016004e0f242c0750a1400c90080c100790b0401f2030000c1c0c45898160003c0f5085001c0d941981c0c4000d0402c070f04882242082c0311690318035220300d41188240b41c40c404c54600142d008068180c040c40c000341c1d880d43c1e1401d00025007420365100442820b4030001001400480b0015144415031081e00440c1141000c80c8000c201e00031450080d0580707801d8000c0d84200b50300716842e00c9000d4803400f0520304290395282d07850742501652091145092041000c0c517a540f0340342c1d001c1903100c200140414a441d489540e130b00d08484140d080f2401141e403140040c003009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495276384 1250 495275134 495275141
    0x9030218180c01090b0d0e160314010203060906040f1518050603030f070b070c0206120103061a0307051c0b0106020304081b0d06181203050a0c0302040e060d05030712050904 76
    0x4000002c04042e04800002004240701d80704903808102c0105080451682a403c0b200c140352040301101c140c4802003414100302170720351104aa40d44110350420060302ca041c000d0703910445c0010300b0a102a5103050611000d0100c09420a0855546805114003003002c0908a400780215455030842c84440c10b0400f012950301501c1103220307610078001c104050380608105c415495100c00d5501607a180c48100340c030b841c2d0450070000d520240110707100b1001c1e072400203070300d04a034003d6505120105095480101610507540c40d1a05a00507210500c07080c05c0c801a12103000d1440300074284134030307800e0b00c480d1039001080e0018401030304001020000c8c1c00040154903140015601c5170711740252440c0c0000d007030510042c0d00500181e1139001c80c0151006914115205681094050703005458051008006140440301ca5451920b4080022980c0340f092003a42c00351081e074811840300ba11f8040822100b00000c1c0d80440d00c41c1700c20000c0200160030340d455100c00d00354580360b0b036031120445803c10064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495277634 1250 495276384 495276421
    0xa03060e0906040303020a020f10091e0c03290f010801060501050c0307030f03181101080a2706022a0606040905150a060801060803030f1609140109030218 68
    0x10442030000e01004507804107200e0342081e80b5081c01039990228180a07800d110750fa0184160601803400c0c0201c00c2d40664101400342d0340300d880c0b1102c1100060300d1070740f0055040e12000d03050800c40182400003070096108025460703883c103404200388042c41e40300c1c40348400407502114030100e82001001100d409010707a0700908002d085c20350030015400107140ea44e006940c80603081210000c4183d41c1c56000c2d500030100ca1015010214507070b00c050501200724154014901e0001e00390304d0000f800200e440c070a440a0001c00d260a02c8881c20410100300c4424070440f095441a40c20000341480007194000c1656002d0050540c40c4821046843d00782480c1000b42220700582c20000c1c1440040c0c808541080c078034170b000d40d402040e03031034030741d1541c001f00041e402c401c40b107629202012800c400000044e5200d049010001340c420758902c601004035210540c01d11012950310b01c0188000c007e078401c0242081c00600d440300502d0380e1b0383c0004900300301e19030258251085400038802c0041001e55144070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495278884 1250 495277634 495277649
    0x91014070f150b100513030209090d0e0303030601091205070b0301030b100501020606090403110a050615130b0d03141201030804060e030a0b270f07080f061006051615020a0306 77
    0x65581e014010900c0360340e100584e5000c0200004508041c242114450000b56070080c100d05550703d0508903d90ba12454024080007007010100e05074681d140004c201c134801c070410780d10140624a04044c8245035011402d0403903043c081c049001c949425140c029600070b5008200110160401c0b0520810982c159080a811501b22808000640d1030f00713800b464110b41e0514203440803420250300b80381000411500100140100801d101d41010401041a0688022181c507550f9110303100006003181e4130009025000300300c01e031b130400c0400e01902955002084a44406241c14800c510307661400000741c00c00c40d0700c03003400f05051149950100d092171903100b00f507005060780505603e646006071801005401c565441034020102c00300302c09402c5d031140d03a980301115400c0281352004d548031a00c0c1e014610113840f400002880199000130800e00408131600e91418941c101301049503145e0010325651042302640e46d440001030b142004001c5002c105600050325a0014000101076030341030f5001c01c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495280134 1250 495278884 495278891
    0x10807060503060d02120f0105160206060a1a1303080d0c030203092d030c0a120c03081302010c0803041a0c1e09010e0307081c050f091014070f15 64
    0x819540c004080b250445411030728002000010b10010301c420504c80102c250303130301903401c0002083c40c05400240c05840000269445a401e85008a0b0745a0045900c258044c4045200308030101025000c5000000d2544003c9d1804440d6035260207480743c4d5600403600c29070000b8651000e4601c0e88074a80071245145019840c50500405156544001100300c20f24444803500e05c5100c102900320551164a02d141901d0325204100c0303a0580340c0510070003d50302a0f10000c109a40c1900c19540701080f50f0341515524019101c610050302c544000010417418071083c0c10502001c24403001c0918400d40c0300da0341d11886e0a0b5203045000f60507001034000030305017a0a00919a015480404200c1d1034044065500d131030307007841c00c0100d4001ca04000400d4041c09141c40c0815101408113044000b2040d01c90492107090b1051000c0b19148202c009010005800740000c080d00d01d040e000143d442800351400141c0c024100794031501c41d40c4603a00840380d0039014420801040340304c0c102040305004001c0c041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 495281384 1250 495280134 495280139
    0x7031202040b0714030d0f050108011107032a0b01090507021c0e0409080417150618060603060307031e260403031215030311100e030d23040c0509010807 67
    0x10118021044020710560301d282c030380304e103075002001500c1c90b1408808090120440c4078061030002c060030301604020b5401c2c40e0714013910b03891b030b44203c3e10f40c00d0307040e80e90303103200741090400d2400c1300c40c081d01c0c0303841d00c600f51800240803d5034008041c0c0600000c1d48002400e084c0701c64064941001c0c82000500300c449406403402054000e111301c586100281d4021452180501e4860554031564018900c10400752842150618000070401a40740d59400b01e484ea40d12500c04204640e4003550101d800b11a60400003196420701001846d00818003504035070441342c40b07030b50b100654a0166400801c912600c0004010f018070304079101829540316943e88940000f0a61840e01c5105900001e414001c110807044030340186a80400002d8010042a43c0703601d49a240c0101041a06074041c41c01348030361103da149120a80c8500810310007040021860940444502000341c40700004244201a90701244080410703400501c0744180d00c43c0001c4100c150034481040031601040e0007a55007984050400d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 495282634 1250 495281384 495281399
    0x10506030a0c1103070503090307060302041a0702010219030e03070f0b03010b0c071502070501080108060601082202190603060b0309071a090409030c020307060203120a0504030215010b0703120204 86
    0x44a4000206250204040c100321105983c00c000d61a10542d0b240b00010f803140070711001002511085104074151100c06039100c40071420ba0060303024040c00100005460b9000c40203880007041040e1060050ba2268545c0400004501c1301e2680d058020404600390026503150500891014000c440e41c4000c8290518a80768118081402428a81300000404040a2004105203801808480c41d4001c11824210009495440d9031240c3c601188101001280001003c60f065220310f4042c0c1d242d20642d5980030803001144001c030701d01d0020202d050461005038980141140c201c80d02404441751640c505480182180c12aa1085000940078020b0205174075022030135000300c4064440d800ba01408603c41286284200d50b001d0b0340c0203123440d01c65010103400002d54040700b4021001e50310f0556491070107a0316407040d0780cc41480c3c0c112050015151842ea1381c052a0001c1c0244111413100c0b407000f061441440081e08030001e040703808110002007640c030405110f071880002c01c040d41014501f200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 495283884 1250 495282634 495282637
    0x402090c12060d0c030b09030c1608250510030e0606040e120904060f15021c0203040b0313050346030515300a08031b04080105070323010506 62
    0x205903c01c201006030f500500c466680d6980245030481403281260911400140d6030740d0100750440c0441c0034590700c2e01c03000400c0b8290b8104495080020700130350192101012400000c0a00d0300107036080465011810b07844a584060204006840014913121031821441c5000e0b0014000c40c45682024107031406620302151403024107507031102c01d0751140c10142c0050081c20300c64111106c41651020000764074502d4811040d0f48445c241c027920f502c2c1a8230241680510b1f0004075040141e403042000708509154000110360000d0a45441103003401181e6641d4110307409000040d03160201d24038044404981942008005204003140444945000580b140e003180601090010303d541c0b40300240e6440b41054420f2100c600c01002850340a003092030721444281c040380040d41e40c9440c003601e00066040040c1c030f584410b420403240c90540e42c60f03014510520002c884010803004081c000014003201c01d000311802000c458034041007040501111104d40c824445248d001c00a840004101d00c0e00c9000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 495285134 1250 495283884 495283891
    0x121206091302090a0905100903080a0614010f110319120c021b060d0e030307021204050f15040306050109090b0a0207020f010e0a0b07051b01080103050c1003230402090c12 75
    0x20380362100366840c2c40400d0002c021724107000c0c00e5070140e0005032000302000e83c4042004e0f4441e441c3c2040765180c02c07859000700c90703003401a00b404188406040d140340d070150452309005000b518014060440c1314149504642003446e42081d0030003060b00c1e500300140c002a00409504141d0703420003c0f0440b0041c0256640b030707030210801e00c1007030703203e00c02000340c8940e8101d0b0007420030035070306006442d0031801d081d559034000c9482c03000500031100f202c02c0c400202400c81e811104010b0100c4003d4188034108440320901e04000d0000c645c003000000001354013401010b00914110000240c01c0c112404e01d40720f04c4200900c2c84427114410000b40340160344442c0c0c1112403400c28170300030010306650404500c0b8140342c2e40101c40340d410041031020400c0070000e941e454400b541c0800710f0310075081d000191802c000a000c01002500021a0b0f01030904010020b0600c158003842d01060540690040500d282c000e503c010341001e03043c804100075418a440c051303801c0041c1d540714501c0d200c154148000003402c0036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 495286384 1250 495285134 495285139
    0xc0f152c01030b1002060403030c0906090311040912050a090617150f030f010f0b040b011b11090711062a030612030a08010602010b240c010e121206091302 68
    0x800e6450030300e9200340e00070049800003a055058003010b003840a980d40204940850010b41008018590f051062503084200e803420b03201c02d82d0745401e594403812225560078019030800c0e611000a0042442010000c0301007245468060f9070350451400104403070100d800500031b1001c80c0b5552011111132074542507100700032400780a4030340e0b40c0900207804040064100c0303038544611815940041d00c1076024a4010040c01070800c07900b01b02406210030750710741040d0980802e03c44c0000310030401d85810545000745c420025074400034145c10000700c43c901d0580300750000403901c0c004580408030810501e500a8074012580300b5400e0385610b00400841440781e521941c0c2c0c2c02102140113900c0d42c03107151040c01500d0742920f441c0c0d80a490018900c101c00d1080100541c00c080021b155070800c07451850f07042120000b85c407681501d1070140010340e40034001e0091990b5854243c4142800140161000310344003000d420354031283c1c12002c802001c000381c140c500c40d80d092402e010602284582e0b400074103505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 495287634 1250 495286384 495286457
    0xc1d0708040302010912020c0a140603070c0609061a03150f0c0702190303050909010e1b0a0c051f1406060a0c150504050604031e0c0b0c070c0f15 64
    0xc0e0b00d0104c0c0500f032640401083c3d0f14412420386d000640204100c0b0840c20305440d400389880d075030180000c45c02041c034645500400b08101094800340314100c00503c9a0241c1408140385200e40c1e114012112144080840514421b90281a030328051250a1403004040200e000c0e5080040002d80c0008014061240b000c00011b00c0c07008540b0b4182405c2a5401e03200c060f02c07040e035a60306000d0060380c003171845c00e40304203000000400c100c00200d1815008034400140c3c6080f014910080e40f03216448000c0341e0080c0400c0c00c032040e001400030000c120000501081298600b1104951103050782c0b448001c03014060401410410603494500a40d000c0e8002d43c904000d00d00028201480340140c84400c542d2507a040104002c1071000025416004a20943d0b4001b00c0c1c8520101417a041075895103c0c80c006064402c112010484e03095040e60001c101041c00c6103405419590001414150f900008a0f400b40c4002000708031030b00e030300d010a5403255051041e05e03c070b1100c3c0a00383e8010720300e804900c005070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 495288884 1250 495287634 495287641
    0x6031b052712030c01050109061203210906050a0e0613030c200d0c1508071b020a090903020a05010b031623130b040f18020405220308040c1d0708 64
    0x714410b40c00550381508080d6a5a0320b001040940038050034011802141d09111000440f84050708074410165007513500d240741d00c88019102d44024070308048400344152100c0ca00408070f0040d20605000307202800c00011011181c2903401d0901c64004c1c1b10007040301c0c101e000d02002c290051800004070f0f602c80c0181c80d412400a800c0caa810180c0c0c4c0125800406e084480b20030441e1404080e01690040c21140ba103483c10007104440625003200c3d05000076412040010148041502442195100600d0301e45456110080a400c0f01e2088005600580c0501004402e00c0401e1280004980058004c0c0c0410340b0f01da400a074000140348508120041d00c00900902c540d200b070407441659000818070b15421000341c4848000d4910911b405214900d41603110420308050b2103003683c80d80c40c18a0210030241c0b240c0070400280b00041c03540141e121840b1134110768144103500340f900207100b0745819403181080d0409000c1044541c01041080410811f40e00c540014900032540c440200d20b819900c07550b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 495290134 1250 495288884 495288889
    0x604060e060f04030c03080a080a050105010c020f03071e090605120a0b07020a0503120412020703170901050702040e0a03120c0507061109031b1c12030203040c080706031b0527 77
    0xf18943c0080c02c00301c1c43e420044100030001c0c000340760100c103a599680d26625054116001c5502c28400d080c0403500c4600400e00609002130034940c41d65005003034520196072280c124a9100c2c089000c40c036200740d520824483e048161089602503e000d5941c032642c8040303113000e142d56003407680d0040c107440788100010728294800c002c40301c0c1199010301520b0f12803580d0080041c80d0a0700f91001c0301c00706480403003003905503c0000c00d1011282c110001012040d040801d41c9690f900c01030000d810800100722034070142e01e550084a1028004100a0040ba402410014001e1201c0d81540341a07e042400042c44594440c054a145941001e0005002c62444080300d61b43d1180e00c4030790b46c041c06016240443d0784482d030851003201d00180c80100040c200d60180c3e0308081c026500c01440141e00b0302c94044c18522950103954041e1003803c1c07804036680c84403a02860910280d12000009480c0c00d050740224664000d501c0391a0b8090404500341000b1142e20315000740b05611203051600f4103030000d010b55 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 495291384 1250 495290134 495290137
    0xe07051903050d080c070c0306140a140103170c010603050c0f2e0306080d030c030e0c0108011707080a050a0c0b0906032814010510080c0a051321020f0604060e060f 72
    0x100c1c7c1c807040e005180fa90b217241040180500400c480c4415141c8800518004a5409044409000203044090076821581c4201c949412968001c480741d90610143c410303c0300900c204000356001e40000c0074590310001c100300c07016640200060048d010071080c55004980c01407842229010b10b052541c1c0305420100840007000c031035010b100203104914107204c0e4250550301c66403d18400307603400d1011002c00c0f6441c1da9208005a03509002400030001003148108000b0f61900994044040d2a01031b680e5110f21854144980000e850a40088280404108482c0100f5004002d159059410843c5143c00554103000047c1040e804d8041c960a504480401d102584059208440c04000716500e000d52602003040902803d400f40148902a42555018103201c40c0f040110701d403c246045440c034021145a000080c1120722040001c0021075100c04070464110100d640c1301c08480c17a00d00b64010884050140c4901e030f070040904000c1403007410703880340710b00d040000180c80c82582d5400d0340e41009040e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 495292634 1250 495291384 495291397
    0xf0a030b040906090c08010b150915211003030c03031a190e060922033b01030e0601150507021e01020607031a090405100e07051903050d080c 62
    0x8079140c08200810081c01e54071541c0e150b401945183c1030745071220150307030882304201c440750b0380f10400c030b04d101110701c541c42e0007070070940009042000c01580340b814060140d00b084d019891146034903801c2003850103100000e240d00140d50982c4c01d003035524588005d4070300c0000e803001808042c0c503420042948180c952868040c800003030500e40302240034030082c0158500f40d010344070062403a100461a035141c1004040d00424214800c0c5003404103c0c4c01140b0341408410b42101808140b46120120f9411074030303001d035001c0c2003403a40c5001340d18604030344e003210046008040c1894981000440740f4040081c44605591042c1006101e00e0030005081e0707010b00402000030f50040105840c209524500d0b0001402a0400e8003180d5140e29888d07000da042c0e9040e65013803076118451204c025910703c0d18111030358106005000742c65070a000480020241e50724902d070141d0940c84107404001904005c440150b640c1c0120389144007090841d59010f0302c9400d4410804c080140c0c0c400843c0d00c0f43d1844007114007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 495293884 1250 495292634 495292639
    0x1110a0c052b05030a0e0108040209060f030a0b040809040533030a081c060e040803161403100303090602030705100903050f0304030306050915030a060e0102220806070e01050f0a030b 80
    0x2c1c444491500680e01c2e80320592001c00030301344411200e602c0d40199441b03400b840d40180880200c1e524103003030100705440c1100041d031601c03400c40b1000210b50104004e0b8002c50250541680c0c071007402c8103210a0380c4001c0c1c01101d2000002010402c40a5046144003403e0201114500c10480c03d50029140100c8007a014060310400214410880000700000c0503e00e0849000c2c01070b240e4604030001c2c18041210013501c06202000058400c4a10f400714182883c0203081501042910b81c0b0781201542048a034100308142001e0f05005254010281e40020489031000310718058086d81c0d465107804a07a488880d1103929054150704041c06003068602945000002d1912450681802005040940301c1d560141a00c0008076014030100d403603018132250054000e01840540b80d49050041092041d103084656007440200032050044140031184660b0500700c074802c508101c81d850030030401070040014048440c0ca40401a600075055443d8030040b038494035100c001c0b041c02500034240c100038041c3d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 495295134 1250 495293884 495293959
    0x1a0916060903050610080d030b0d0818090a0c0516050a0212150105190b1c0e0106080f0d1704050109050102030f0717060303032d010b030601110a0c05 66
    0x9000d640c848190320031079000380c0480e581526030a0001c40518090300aa80103900060b000582c2c09000750080b260400004c0c01c400d4001c1a139440e150550b4014487c1c201c07480100a589512a282006e070140e00022149000c216500700e80102414034401c040d60100f01c481001100c0b4107121060181a05a075000362440c0b0030680510b240302e4580079080c0c01da42110400e20000304440c00c0080d0568403100c40d9003003000341c070380c10201844d0154010744101000e2811078507045100e525680038020701201600b00114070703241072000321070814500684140301d550254410811b1551310102030b5a10745003150340b0401540b11401c2050143c8103000c0b01070100d40c000400e101410490064480c412041c2d03650712511411b442e200c010340b4203804e640301540342d80301384041800c01c01e600d100c40000700f02601c47c00144019045c2c14203020f010907400744402ca1804000c20448e0f50f08022003110810b00007006e0078864500d84c1e01d003040b615240c0240340c011541c11156405195007070381580d01c00c05e040b44a09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 495296384 1250 495295134 495295139
    0x1504050901141b04180903081501080a0e1c120c030510090b12010c0f0e030f0606130216050303010f08060c03070f030e011803020106061b0212030909070c1703041a0916 74
    0x17107000e80010380c0e0407000500e403000080c0704180c6041c407842c24030700b0581d600d0549858030100c0703001504085102e8000b03405180e0380091101c8212450300905e50049e00d6211119905050726012502c80d420480281818181007141040040300081c040d500c45d40b0000441e030003611701003150f480250603504003641c41c100340c40802c0c0350090a00f0016a516941d41c1a10425100a0544801c2c0303100d4044200c0d030103000031410030f2130010168011101d90a030018107003071440b40141710705c0d000190107641d207810001c0140404880c0301448000341c00004001c00490400c00802c0b10640b200500480400c030441040e045100d21a4020014040300c8500034400b0804050000b5250030080504601542c648207000421074001c408030b2205800300c0041843d18070043d02480240056065986d003640010070112032240e40780071541c1d004162540c2d070301c10707200300342e15000404100d80701e155016080309204000024400c0c0c244d0145a07c045ca149030941e890b0381d980d071440e00120811540c0d02c2c40258001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 495297634 1250 495296384 495296429
    0x5070209151c03021c020c060f0d1503080d0b0f090108010c0305240114130f03030f020c0a031e060f0209012616020f01051504050901141b04 62
    0x101d0400c0000c9580d1071106203001944005080041001005608003007104211007080000e19804605c160050340d2151481c40002883e40d40080c10742c2103100307408140c00103800d1080c440c80600c091013196955646007181c94501c0140140f4031800406911011030b8030b01603c4140c08515032007806047c090055845180082c083c040030b081c0d5a002915200000d07003160f607000343c0c44510348220308070140c00103020f200454403401088501001081c081190041040e03520344940010010cc585560149080d403800408840a1000000440d407001795036001680d0b5508044003140e500449202e20030117914140140d0042603000540018a04401040e0b222050b400901d4402026a110706454803110021000010000216045042600006415447c0c400d4811090101c580101c6110300005030596080d58800ca5440c01d115130081d03450081401c2a004054100035010003d2103190481d6005035000880180341b20440c0704d141105080c0e9443c401c040354080c04c1c50000340440c01851040d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 495298884 1250 495297634 495297661
    0x72123040f030f0201030c09030809120309100201050702061b0901111c05030601111605091003292a0a05040803070b0919030503190b281509050405040305070209 71
    0x8044c1c1c046400c04103c1030780140f0910780c00302642d40c0600c486042c002c04030705101ea07040710882544414801081071080c1e139030355101440320061042c1d00110b144d1500640080c2004070107841d603a101005034103100c084028041c01e1b180051000c1c83e048884011400d8154030789400419103840c2d19150709170b01001c0e50b40c000300070b61080c0800c0e03c0b901c44070082e598959a81d01c8100c0020609604009405d012501d032086049400c44523070586d80c100240c480c0c8602c000401c1c404000d480000158420b004400101d21020b80c0c40700c1440b020b40c40ca0041c08441c002c4580341031424200340500080c001090720700502c02d440242110104030303612210246011010f0070000c2e14140214442c003d0019542e0403600103e00d034551703140e0380b001d0039502c84411a00c11030009490342e070781580c1c54588049850700c610304a40701c0713102104140303005000c03591030f010b802c50001c0c3c04c04000301d244800c0c00d82d02c00c2c4d000007114013100e10948001503a07076600c0c20219a28010104000d601070311250600803084020305 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 495300134 1250 495298884 495298913
    0x509040c08070b041d0403051201060c060b060306301203150d05030a08060303120a0506090907050f01051c060b070b10030c0e060d0512072123040f03 66
    0x7030031540900d8480b40414070f54042c510031154080c25800e41e51200450941455800c40e2290501909110381c08041303c01c910750907000b44000031107010340304040c4402c40c00b40c148046030039903206155003041e50220300d413500c0031a0340e800c0c1c1d002000391965400c1809002c00c4a104442020740c0d002d444a825034590607070007039840303102c1c40b400214003d031140b9000500c44800ca6014008506e003c4030701c4026110580000c04c8980e06000500081440c00d1900000360300c1085d107a54009114074140041104004d0060300e170b11480e0784249418000c1d903d80348034600c000082401e000d5210b4110208080b80054003070b24102142e420700340d0000e503580310503026000d0648201000c541c0d540c2c400400000c05191444060902c4103060f104101d9072524881060f00b004014002103a0082103407100e6203030035030f0707080e04030900d40c0001203d006000c161444006c401c070214a0280c44600320200040c1880c0380b0351070340080407010b981210544030108044800901c000c0c10b410108a5030303070400b4181c041c041c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 495301384 1250 495300134 495300149
    0xa110f0304060e210114041a07050a140405180403020708150c090f04090b0105040c03062d08120d110307091a1c0902030f0a050d180509040c 62
    0x15142001009008015101552016550481c0101c0380404014900607a00b20342c044440c4400300703203540e581080c080d403030781070528491031812805c09107450241c8004003129003e04090b50400d10212641c4070781147d148005c00d02c0d2000c00e1022040c28904984165840194040020500100c402d171600d0040c5201303074003a4083d180032940da404c900e0744031a80c060003080780554070b80004000340300c0d0001030b10b12000301800030501c510b90700e0041001c035a0841420750314007003d10010041441c0c0307801007080c1c1090b280b805000442c544859a005d8bd40c147c0c640808840940038083d801d1020000d40000411401c411900039a0401480a00e6030b0320040c4000e001c2c41c00c006104c0503264a01c4200c0b40100b44076616404050310745800c81c0d080c1030999101d05070440c030400c80101010005100450b403120320b40400610803800d0300c100740c5002d544100082568104100c00004508080340710b004143c0c1505010b656680c45031990100c4010309d802c00ca90001401c2c041c0000e000c520301c1c03440e007500c491 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 495302634 1250 495301384 495301393
    0xa09030b18160e1f0302270925050a030204020306031f090507050103110a0818030c030909010608100e040510020c01020c010621031b0206121603090209040b04170a11 73
    0x140c41013508481e0f42c1ca408605094003013002000142419030181d8100794100b012152020b104040c80c000c02d0000b40e85000c01644050702c9000c4040d000412486604606809180d46514020108420000c2448081d02c225408000204d00351001c1c040b048510124040900980040c4c410080c010000789000303844510030301c00c01040b01d502910400c0c2d148d503014000b40c0d0911a924008484d441002421000da12640e0f144c0825101c4080016084040503400519103030007542e420300c00d4a40050340014200302101040c8244030781e0030501c0c8800d03900e40249100b125a11401c0c1075180c8086424001400f51000403540e00c400d0041d4003a01c1940845002030011030307590844c0460310035044c0508101c4c2d5a2040340f000003e80101c040b000f020400c1590a801c151181e00000c07a15040b030b16044401c81001006c100b52100e100807045074000007810208081c128940100b03074440c600800040410040303001040c2031214502c600035180242815907541c98955034002400c10726001d01a4100d84503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 495303884 1250 495302634 495302641
    0x110c090906070e03030405090c0714060c120c03101502010b0a060801030b0f0f06040b04182103090503120402010201020904050c13080307051c050c0d03050114060a09030b18160e 78
    0x40100403034080703402c0105000c040d901c951001100503802008125007a40814003114bc4c43c0d0b105101d0360b481f51441c00d0313010341c4420201080d42d101030b6000381451f011403c10010030004d0f0280b05010000e4841c0d18646001e4071040315000c1c0e0040000784003c40c0d00065020000400701e078450052030690784100c0e01c102076911a050100788004050f144102c0034030a080005680d0708081d8008401002c0042c40440c02c0d0503041451000c0c40c041440070340b80c0180001030310074020000303150b440c5032500380d190410440ea050f03281c19480340030f070f501c04071400c1402e0801703d003e580c401d4040e5401000300400070425410f10003842006a07100045001c0c4951000703400051522011050b40e0010b60040c1c041c00d516440d000c9040714111038000c41c030051000034456000350400070801d60300c84008a0b10000381c1035061502048a2803035244a0303c2c840c16040101c5007405074440d1000c01107942c0030040c1c0b01c8640300e0f11103200c0c481000002d960700520a03101b06841100c2c06141c440f0449286090a4180c1d86 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 495305134 1250 495303884 495303889
    0x20d0501090f020c06041b090f0c0201180c0302090a020c0f100b040c0909020f2107030605060304200301110f0405090f060a060c02041409010c080a0e0c01110c090906070e 75
    0x80c9666410303a17078106a0004000c00c4128802c03198201c6090280c0713141545076601e08044594140c003014845542d03084516a0540921400c0116428124854002d2003c0e40c1c0d000103120f03490100a010781c103a000800ca4444030750f0161414a40c000050320004658065a17541e80c4003900c0502182604200d00a00141860300ca82400980159240d034402c50401c1800f00196100d40031200880c1e1040052030f508600342c03000c60202c00c8402d1342d58161402d090400506560464002c244148010030601c0000741c0140c03507003080b01e000800ca900b40100311100203801860520603407201540002212118000340704008d00959408407008034070360310f034140c80c089100b004850036904016040783c03d21016000308402e00c252032002b071001c11224010354111507024802c6d64041c80d20fa440300850b502c800e17088914151311421400040207100c1401c0000d6030359000604c085818010000c0042d403040d041403016021888000e00301c014036081041c01e2550704d840c04c03a100d0002a5000100aa092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 495306384 1250 495305134 495305137
    0x61509061213062007203105010e06100908120406080f1b16061a01120b0901050f030a050307120f031e02180406030305041d040f0809060409020d0501090f02 69
    0x8019101380a4141280c9503242451103081d40740c4114442140781c01712150359100c030034180151104078922806204d071542000f03c500c407082c0010000c1c07414140140000a0155080340d8481011110100202400c0f80256401851a003040501d0700504e0714071681c610f61030000b03100301e4a1035030311203030281d982c23603080d0000950941d40c0c1354071481e0480c040303d1410710080190000448402200c20751048070340d204400c5034111850360a0407209890019000c2da0000c20341d459849926509021080451002a110b0501405183e105256190050460703480c10400c1c1464981e204080320343d550754030b0920190007034009190310300140541c01075540380e5110b03002d42107400440c0c004101e41030118149007000707900528940205204c40780c2d05a0101e40d40c0313000e070710300440c020380300c0598580c02d003280d61905441030103515050f02400f07024000001c00803808001c80a4129110301c0c0c9501d006c0e00003550354481e0354440e141c883d00116100310f54a42941c4694122175149104014440c0051004000e9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 495307634 1250 495306384 495306431
    0x503100905010b0909190519180f02090c070b1e070f09030816150e010b062109010b10030606080f09030901180902070501021308030306150906121306 66
    0x20800c01c4c03156509074182072080942000b05c0080d02402c0385810400d0804950b0115062240071000703000703510405c0014454805c02c500031418003018802503890310130720b03040b010030700078010700705600003070b540f0102c48054560096015400b41114103084024100390300644410000104003a800301d0b03440f0f0301a010440d154010350326030030280d500e0b54650071060780001c1100c5602401440012000461043c0c054010110316280010100d1429004508407000e03e1019402130000304a244a064400c4a40040c0500d0210755117174581e6038a402c0c28054545004003540010142d0103d440d81a00b40d00f1032026100c080c1d035051000d5840031851054508181c903a400c49400c1005480410f51180c1c40c1d0804c1c070f400c1a403c1a030040d41d2858082c00320383c80850280d1300369502007034000141c910110110010a08540214118240800018030041203c0d00100198100148844081d00c449080e40c15803440d008468085103480010140c40c00c8c0e180404891841c6000010038421000c0786d40c1400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 495308884 1250 495307634 495307649
    0x60d1119080f0c070c030209010e1009230a150b07140d0801030609030905120304060207050a030206031306060504180506090d020d120e06130c0f0b0d09080910050310090501 76
    0x140e03d81501d81001640300500c05d480008900300c01001588400010038007c013030600e501d2156140605005001c106285c0001c50b020303003401c2a524a40c42d5103541141025081e80700405c040e241c2030142c10081925820000304401500710018180c3c0364040a061540e0003100011080c03440503104a4840c180c0030341e08030100307203903000500126485600c941da142d4440d0602d122410348420001d10320040889698801d60310015043c0101c1e54144151002010309580500103117080d640040c030b0074013000b13080d401c1c89000c0000000c14022560414401090003400c01c10407003005c0f5104000081c070005040e00d452080c08041100008001000c014541956002c0c1100181c0c41000300c0702c2c221140c16454005880d0b02849400301c0061200c00e010b003403154007030000b05141c3e281101075960310303920079074076212283c00800400c4c409004403080e05020400026038000c8500c1c1c00d490780e0040b502c0c2160004140c180351490301d5000700045018520401e0301d0800c141e510b141c40001e036402401a0023 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 495310134 1250 495308884 495308911
    0xa1709152a070203030c120408011103100902030c070f03050d05130c05040b01020c090a05070f080f010b090a1809060b0607031d0301021b030403032a0f02060d111908 73
    0x444801c004003030115284001d080e0380c44c0c150403102c120320307100e90210605441e5000240c01c1001c903d0074071416000e011100ca541d030030351070300c0c0146031074000a030710138050074940000002d242142004c040310801540401c1045d96800d150030005e10540080e61046075a40c070740008683ca032101c4840002c01b180e0301107518172190341080c0030b1001405241c80a00e065126000158000d43d8130115001e2140001180c002000c2c030340070000400c03001300d400c1400e00f1b100119040c40341e0b120300c8816550645510400c0c2a5035445203802246203042260310840e21000110420185040c86403c521a0640220402c0c41500703201400c104a0b0300ca0581e009000c20800002b40d900002800c401301d118032002000142010400c1c11600056071800200c1c500a41000500b8010981c001d5290f800d40d802d901640c5410305446003505407000403030f017005481a00f41c0b0124804659407003084a2001c035130000140550081d0001940054002081e949908140d86040003800c0740b003180c01a20400f21501c105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 495311384 1250 495310134 495310201
    0x7080a0605030c0d0201020727060603020c07061416061a01030216110f0a0f03050d020d0c081e0d060f0510020606011206080601060804210905060a170915 68
    0x5850482d02000305d0550040705000100702e1945560b4209d5400c294182c000040b0007000e041e0125409904041c092510601c40d0460002c000509441520300c103041c120b01800715440744200c140680301d140c2d0f980b09400410003041260310307080038007048241ca6090640440c0d810055082e809010070228440340e8824107000820600c01c3c070947c5450011707044011580740440440c503041c40580001488900c0c0a000b0810482c0c00c010201e28074516201500c400354036800000d00100304848090900203010400303000c03010803002d43c4003d080060109030b50711020304099002904481c80f85003c2503040060008040c184450f120a400b01158081e020650705e440c01540c40044407642640b6070b598540c0d010414007402c024090281002d6107808000303241900d4000141c03c3c040251600580d0b10440102c1c0706034010142c1007ea0320308407000d41c1c442810700401c540c403060712101d000202000f641030103080200450b8011000d000c424101c161590391118052245076116180807240c8202d0248 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 495312634 1250 495311384 495311389
    0x39220e070f0c020d050c190b040501080403051605160b0723120c0a0b0112050606040f0905011406100212030105010c1403130806011719020d081207080a0605030c 71
    0x9103241c403220700b8070007001c0d03289402042480c11042d400726441da01041e48007107285054160491601e902400a90340076051804500c000d004920030607051002c4440030600300340c01441a51203d00405032900e07072600c0700d42000c0d540d58080021180700e400c0341d80000b0039000380000031220300c03c4c1c001483d40340c014020280c0541c2001d1502c0e102d107650041d480d1000c1410120001400e00301d40b003800516084605080000f80c004069005a41070302250903001c1c000781d00411400c0e07021108507800625110009901c002400f03e403000100254070342000c42108112500381d840c014207041d11910011540310005a83c0c0d4010740c400104440c00900041040d0f41c8240d0ba0002d9003403140781c61003040140c01c0328403451600410240c200b00301603080244282041006101d0041001281c0b03a1202000b151043c1e4a5808030b04035100e003401202803000954a90040b454000d55003c0301403076581042412103180c102c410b48440c0c001541c0b203008621000110302401d8140c0f9002400341000c3d90040e402c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 495313884 1250 495312634 495312647
    0x50a17060a0b0408150106090806040b150301060b071a01031a0603071505090102151005060f090a06080a0506030123100e0a0b04060f0b0339220e07 65
    0xc19507008880c0c140110b204035030140034200a0040741c0040014030140c4481c2d8490b14416009001040088038040102070800070301aa0040e40203685076501c0d0715091180f4100f000f860180b642c2545c20444005403142d040f0004001e0310740102c848840c015140404051614403c2c40f001d4408060041032080b564040095a508040300070221075425545841d4401401000e140002c0410030100d8000007658040c40200000c500c06000500c1900c2c08204c0540c012485000320380c02020081540d504a26103603045907840318004140e00c4115541d80001458981c04a680300e65a42c10240461070a06050040303042084103c3e07007403002c110444206044800000304040a80344042500055600140d40320034020300c407007800032031031341a1b8000344030650700c080c0d11100d050f0360049410080e803014001070f00e800490408290510014800c0301c24500c103a09405280070301c180c450056070309001d80d0020060f00640c1c21030800c0d10321001c07000350403120303541c40340d010301504000026a00c036100c0c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 495315134 1250 495313884 495313891
    0x607050a150e1009021201150b09010203040302061204150203070203040509091e0303100819110109030501020a0e100806011e14070515010b16031202121015050a17 72
    0x1c002a84404800c19507152034010400ea46060f0f80c0d5402c401c0941c1030400e8480c602d0703610b110003401018074114402010740c07200e00c9800d00008000c18011280ea1091040307400464004140d00d44909403840e0aa2601105803411141030701280345150b400c903a940296071045001d038019505080c6403005002c0c41180c000c194080e140103d5000d00d004170381041d030740e102e03c440e020021600d034600260800b043e110107400181a0b5800610201040003a0710440c41d012507010883c89916900000140c5103c141078100924550000c541408a9503000961101c0c8010460b0104400c403442881990400380980c0c4050008007110080740c60340c1ca042c8400e40504510345800d130449070400e07298140b2908505021102600810340ba91303561801c0c48920f0740503022850f201481d00f1100105011723640c03280c3c4001420701000d1007500b0740103081035040c0c0302c40c2340101540078410314042d01402404c40850080101e1404141d6050307842c02e2040064500c600c620380c5807030781c0d00385880d00a1004000b004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 495316384 1250 495315134 495315173
    0x2070609090b12060f0103030206070201090506061c0503030108160b030106080f1914060406061716020c0604030f0501050a02030c04030b100302060a0206040c06020d080a0e0c060f09030c0607050a 86
    0x1403807285603003c04000702403260f504800030002a5065207802820244050300c4c42e821a8146040718000c2003000c01c0e071030340002c07080ba11645c1c807a0f0400d01c206860f061030038014206000120000600c9500480e191844855165a00c2c0c111070300d1701010a41e501007801104000786006000070105640865402d80120840710200c18100901c0900026260000c69031a01a480303074080c02800c2c02d0a0003110b020384010b0510340c00c2c1100090b82440c007910010b10000401204104d0341c02c0e140c0c0240109101c0505c00307000659604d40324100503210008220088030150310b048005a600400c40c402d0307030700449045140600e0a442e44e00c0d00c000e1128060300c00801342c0d840b07000005c0140d03601c0c00104100315480c0c001d4440d900e02030a02219030222a4005000e541106a0320041d0710f0b130050385c09501200346107000400d6840034100d00c0ca082c0b0541d40c000d4100d400081d50100007003211000e015401800c4040f585080c1094061102602070603a00403e154800c032100c00014640c0e0710103080a40c02c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 495317634 1250 495316384 495316399
    0x24080c0402190f141309060b03010501050f030c040e0414060f1b090105160c05031207020d020603040f020a090e010609110d0e16031a071106060f030a06050a020a03050702070609090b 80
    0x1a00c20704610f40c44170750489944400b0600410095065014100042400420780d50441d89080000f070051301c02d655044250a1000002442906c03132182a039010f4080403205092900d010702e000342c0c0c5403411503c01c480b6031140c500000c80d26507105440c2032144980d4007034070700b00303010000344001c26400c1004290305014050140c500f51814500603290600d0180c41d81c1c1610701c0c0b4003000e26050403081383c062221248100840000b5171200d100e0f01c1c0c0d40a41c15208240e60b581d550400c4a1981c540c150000e6000704625070004140300030380c1214012003c840000c101305a6a4000401118a128240130407450103220040200015921142d8201460300a0303407640060780c4084104150380b5001114060302003a003202c200c26805181c954403036400d0804008607030840d060183d0b20000200341e244207005100c0c2201c3c00b5201803159202141c0e009800348514200b0514003000380d04400b0b100d03400207143c0000914a03600c00503940c8110b8819480d0a5111030500300403230042c0081c40307034081d000b03000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 495318884 1250 495317634 495317657
    0x3020c011503060b030304031205130503010e0d030c0e09060d110a1e050f0d020d1e060f0b0d02090403050a02071203110105060111100f24080c0402190f 67
    0x2001c0c09515114045068500780903419890074408031640301e0142070086e4024442840018140c901191076001c09081c8a501c80e0114021038505000b290082a010750800d514030017803000c0000d450283da10141c40910040035110800ca80b07140d20307101ca055100102c0004aa82402e1164400c811039010b1011b0b141c5940100c000f080b00c40910f6400803201004140705403048032058290a80541400c079004106c01c10010300040c0380440b03014010340700d2410070450404000d0b00284180040c200f150759103c05a025091003002048544c42002d10a4101010105240b901040f4000e060f94024072269143e1165201110241c0003003001206510030440c0105420125454411001c2c4c403907a0741d20002841042150700b9100b001c4c0004d0306004900c0890f040311800031501c414801b801c200000307014180c05496401030141045500c030301c03010201f06c1080d014a00c4040c3c4050b02c100a0446181842a80a02c0100d204501003081d8448140c0410980e040c40386001d400c07060002c0c54180881da2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 495320134 1250 495318884 495318907
    0x4030204050403050c060c121503010906060b120603060405030a0c1703180d03110a0309030306031704050a3011040c020c010224010323010515040e010c0905060a0302 73
    0x70420384068010480100c0c001c10328000400400d40e003c0e410b5003e090420b21a501c1100d07605501800c0403840f003210490900c815103096000b0b56080d50441c0d001d000e06a502c110075012540205440030742810760000180c4207060025800e402194813000135480c0141c11070f0100c031806001d07201206c0300c160340e10845040c3c4805d000914003501a50605020a011588100385040300104240c0d041c903042011900b008446401542c0604445042c046034040305442c0490003071a1350f800042803406e00b031000007184541d04000c0c1003a110140e0300c04000c7c1c0c1d2188040c0a140b0602503100881001071160025a840340445044603544035650200c1c00500150010b0700341c405000c2a0b00050b4400c02004540d5a07040051118407500702c024000c00d03640707440c14644020307014000944980d6100303991065500040101409200352100204035a040c4403e400c0186001d02c68228844d44c2003031002400e028062151030750101c0c03171b0b8440890661800050040d140c202c5100c24080c598203120898019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 495321384 1250 495320134 495320141
    0xd05070f0f0303051e0402130c0302120c0901140f09220906050609010f0e16111207021e180405030d0905010905070806041205091f020d170603070512010204030204 72
    0x6030321a44021413075243c8a8032801c5a1501700e90415180c0031102d0a00025880e4282d00019201c0700000106c0e1030044d4901c02d07006407143c3c1900d03502030007543e820481c403112510080d20341d05c40243e035100400e407554004620385002d90402c60440c1c1100304807003403561403c0329501031090301c00210010b0154403240038000b2520756003400c1d00e203d030700c5004202d054907003003401d0707405000d8580d414034480d821b1490400b02c12800900010300501c1040d58900d21070300a5504041d540c200c40d049498017400c0102d00388060708286800c81c0180f954803001c00103502d159480e00f50140004d0800568010142e4142c2070140c0050301c01e0390365020803c0640103000d124003d403100d00b0702600c000f15092080703140c510314041c40756010380c542e40c12003018403000030301400d0300c1c09108223186401d5071a44442c0c00000d1105403d1441c4030305810040e00c80c0004d10b0b0300481c85504050b030940f0f0b000e0008024203134240d44041d00f03c8038194150030800090101e498182c0340c0541c1110050001070516072694082400c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 495322634 1250 495321384 495321413
    0x7272009040603080d02030a0b06040b370207080c2418122404030806211606020606010e061903020f070803090d030902030a020906121b010f030e0d05070f 68
    0x246c00104020f00401ca80c00740028080003658580c1c6003601d0070120000f1402041446400c104810007100517402e0100c00e41c10103e0407030711041600307025405001c1c0d503410780c621404490707000d4152031070740a1801c40740850000d00740b0200c1c621080e00c1ca144185072036000d0150110304420300400c00c0e1540d20b074980040021b43c401c2d0300500800514054080701c05d41008401100d80308a0010080081c0d0300c005400d030020f5050380c04400450b402c50700c2103c000142c1d000070040307128030713100c00082d4004505408200c0d034003031b001d0750605e4403101c0044581c022801c51060300403400b0418220144140504201540d203145001070920702401c540c2e030000c3d408240b055503402d50100a000c100c50051049014612180c10208540d4140358080b03511030400d0f08004e442540d000000603810b40346c01c42000a0f00e0702d0001030303034203592081c2d840d5a01d184110780d0b51400288103c4503081054042d20450029010120003046c10801c40d1004686641c007400c0304a942c000100001c0d0001080c03082055107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 495323741 1107 495322634 495322657
    0x1703070c090908160303020403020906060c0a1e0804120b0f09060703020a1407030207030b0606250309030c0e06041401060c150e0727200904060308 65
    0x91034004d01441191130041143c0403410140e1560080003034a1084856605a0b19408140980d41c01204070000303040c0e1100c68440c02245500074108103e0390380030840001035000c0e41d03030800241c000740d101004c0c2900508201e020094103a078602c0d8401d102e42030050640ca0a00f91480e501c0401418800034150300103900e40c0d81034130842da1088a002c00000a070b555141924009640303003198882130b039007000340f440440d000b40391a50417554524022203c808400c440a02908841c02810700114240070407000004000345140d8911001030450510b4022145022014401691500b0358000041c0055a0052242c140c014030014487c42c0c02c580b2103001d00205091043c000d11451000c503100748511200086c8980101c9500c9071070b000d2002060205000c0340001c14181ca44222010b88201c90508903801c2c2d01070800702626802600402c0440c50782e03540d40b00c403007550707010304501700707 = true := by decide +kernel

theorem cover : BRFrame.Cov 495143884 495323741 := by
  have h0 := BRFrame.cov_init 495143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 495143884 ≤ n) (h2 : n < 495323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
