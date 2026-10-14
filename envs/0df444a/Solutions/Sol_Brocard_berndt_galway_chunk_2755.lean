-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2755
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:39.654991+00:00
-- url     : https://prove2.me/submissions/73b4820d-942d-453b-b56c-5d61f02da259

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 495323741 ≤ n < 495503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 495324991 1250 495323741 495323753
    0x30709140a0b0c0604030f1b0b0c04030b040c08070f0f060518120309121c050715020f040501111c03151a0714011109010c0521041703070c0909 63
    0x14020b07200b51441d06a45640c84034007260b944404550880000b02c2c84003094000314490b0310825904204006400d070040307a9903480e00000f000081010121f41c8081c00000007003028904031b240281c3c00b5100c21800c03030b4102007080d03040024640190429004001d0200411091381c49820304079240c0e890401d407101003080314207010b5030844150b503078440300a02e24031074401d001100030004207208480b8000b40440c04c11204e6100d4003010740c46890000c203451010101d90162005000b4a44541f10882400100141003812a003000c0b414001080300441d0a02565070000b43e00c6c0c01404098000300201402c1003500480100308003200c1c0d003010b44811160307500d28180d00400b0061f00e4601c1051520300c1403580d040b651500f0041c0151408035030000807010583c0184036040910a0070b40d0070a00d0091030301d005580c4484190403c5805200e04501e0640010605c20200400028108402c2c3d0750352400b44044c0e207842010002400b0754104110207070015070961075030011a03681000119052017030341060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 495326241 1250 495324991 495325009
    0xe100905071101151412070905090f25050102010504150b01050904020f0d0501170616050c0115060207060905010c121110020304060f020301030b0a0f0e0f15090303070914 75
    0x100c200740d03003841c010721501d551360100c1c2c60075907000c04010011202e040382040403004c4c2c51440844150415002484400303203a070085a40070080d0400c450038111070751480d034545548c0303a80d4140c030031354018014a0b0503440ca072011030003424248024006414591500300d880942c40c0411800e541d902c0540507003990048d0103640411034010011510b4021030003041007141d0040c913000b55980c5c600000401d80103051a82c2008408045000300525610ba124440c1d06d801102c8003003051003802d224550000f4824060080306207c1102031602c3c461034400c000c5d207050500c0c4c0014051014810b4184003e0741c3c06041c1944054000c165000000b0364070b03206440350303e008860f1301c0b0940141a005015001942c009500030f41c4030340c0c01007200e40a01c9101c0c20490100b030100400c0b6041d204041020b45519802c60160290300c0d000028180c1030303d80340030307160001da0f07500300c0920341022400081082c1245885603020301c41002840c83c6240649008111a0342401403880c4002e03140c0000304540c44010807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 495327491 1250 495326241 495326267
    0xd0c080315010e10080603010b0d05191a070c12050a140310080105090307050706080705090f040b211c08040206030c1909080d2c040e120c070e10090507 67
    0x1c00301c020b0711311030000c140140440c0c100b07000e51b0801c0c403410300a05003400e08290264114018198403a0b0640c40c500108c05042c4080e100c0c410501c6a0401005964006502894103a200c2c00c04100c0c07249050361420003550a404188034090240340b890702d8022003401b01c40c05c80102000da84c3d540d03000c0c1841c2071a24542210005610708010414800d10000082070300381d014808403034507150398100495a40000b214100000f070814011100b09007021045500c10302001000840c04109400204032134030004510480c2c284010580594170440602440d00e450191058100b0f60001d424009407003c2c0024000a0240c3d90000000d48034241c1501551040d0b140781400c822014419070b80200018030754010003405010f94501c5040d0140550400741050a0010030246000e0072015000408445a041c00e6005a121940c17184c0c080c500b4018403131600900d010340303030303c0d04015503050b4540300c0c181e00982d035101d243c4001e020100503110642022241c558001040d40d0351000011990f4001c0400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 495328741 1250 495327491 495327499
    0x1406061c0e06040c060809070b300a05100504110a200114010302010906020105060f040218150c2a0d0201030b0d030206040b060d0807060e01111303050d0c080315010e 73
    0xc3c4020407819421110484031741d651540c0c2c0d02d4640210054961213148201c40250f80300300f000d580c0d5480b007004010020014070f00c031030003284070b9280c1c082809003084501d510420f54960070412000c500e900400003400301034408000e942c0401440c40c84901c6010800e80912800384601707c030092180e010350984e000c140000f40f04596481c034010001917801c0c013040707020800315800420390a00c14070496102d00170080030009840084010f2200a6101d81842c90321115000d0858110307880c0d07041040030045c0980310a0741d4039648421042c0c01c2161a05da4003841c00c82804400c2c01c105851002d103101100201c2d601003c8040341c0c07005800070100d0382c41194001020519500c103160f0040b03a03040c8030728060842e020b0103580e400d040110721803030300303100074450f54003803120b8000b050140e4040d05040c1401c100000300080c80103890304464110364070148a0010030f041c14010400c2c2440416060303030160900c46880413042d0b648400740d010040030b050b41d034022008001e42c941e21a82c6c00786043c03680a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 495329991 1250 495328741 495328753
    0xc1b03071109060108150d03050c0d120b030102121803040e010e0702010b0307050102150907080f071d06150d0f110c01180c030b1513020405041406061c0e 68
    0x100c0c1040034003240c1c0070300901c140b01420002e8410350103130450307600c1040601444034041400340c080104056540c0d07400d400b00f04090043e4040e095041020a07070700c01c1c0a850311003d81c1d1400100e034050b180c042104078080d0f401440351141080040108503044502c8052650340000000c030414503500a5512611120700c42d5000000c15506404145000e041e480e4001d00c0504a11303000e1581e01c004500c03505005a101c078400d10a10700711081100d8100903030b00103a400f41660f81e1246850b2603904040c510325a0010703001007100d01c4480c0d0918a40100c141c00346161803400000144031012100200c080002001a00d8002300656a01c40351150301d0041040010781802c00840029070800070600b070180d0318004a010b03000f410840100025036004050318010fa08540d1103a11050b0080e02d030000c5034058902e40c4405540c0d0401240b80300700c0c060740058507240b80000700010383d50a90004603c881424041c0452511010211041c954001c0b012000048100c8240402480001c0800c0d90a010750b03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 495331241 1250 495329991 495329993
    0x50a0f060501091b0912030e031506100207050105040303031a090a27050309010f0c14060411010806030a0605070903020a090504060c210b0a0503030a11070911030c1b0307 75
    0x7548064140d50162000f046081580b4202c900304011803811503001c1746603610200030308408280c035034011900c68503092007118500004079181105428401a65451800c00c0010360306040c01c0402d4146d0b018801460914a40741c0064218816404042c0816441e00c5040d031501c030429a188580c00e001602c0303d419880c02a00c2407001b0314400351340c03000e19621070341c04c004240c41c44410b0403180c5802601640c50400e1420040d070f19000c03580080700070700c083d00ca10400402d40412400012140708405001720789001d28000620001541105042c0003e601c2070080a840004403145600e9103c0000612038a41e564162806400c5500080d40482110b401199400c0c49400041c0210f110b8139050000d04c403200c0f410b803803205130f030700c0303100ca4801e0082d002014029540e0012405548080c203c000340076111000b0070f055a0000d1529004100c07030a44c0e00718000c90801105004001d89502003001c2e00da80d02024117140f1000d010342d23455a070049001c610a0300c1103503000c00d28280b0341044a90ba9211 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 495332491 1250 495331241 495331253
    0xb0117060d06060312031b0e090f041a040813060801060503040f05010b1020301204110906060316030509070f0303120507090e0402090703090b09011410060516050a0f 73
    0xc07000c1440c600c7c2c46012850315030f01406100e101c02ca8001c007403851941d120502c840c1c1900d001801681e50f903501030821000110a80c02c4d02c0d014034040c40260760b40d0751241e102d01a4100c11a03018504028050f0010010075a0000980340c0003980480110700c0d00c04035041950140031040300e0b03c3d80c404039034043c00c2c0c0481d8103d104001c866866040c032201d480804012a44c5428a400030486916010040c000080f003103c00425240720400c620b071414613511400328100038108a40894020460340b6240300c8503d4405289a44503070300301c80c11490b514114008904d4034010700805010f0544482c040755100c00180b01d000050282074095500d0642e41e810003c02d030044040340403040e1494003002c510820305c21054003041d210007141541071500c0b50307401c3c130030288002002c035820582d17500048000502224941da00411b450000401ca11344003580e01d880c619005440543c0948840c80100039158000041d60303500710b6211a0413114828505100d420900b000400802030100612002c042260f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 495333741 1250 495332491 495332501
    0x406150f0306080c030a0305071b030305070b0a0e031602120607020303101208090607030201020d2c0606030c0118121203050108030a021b121504060b0117060d0606031203 75
    0x103099601440450ba5078140b003521a040d4026003505600306100f40d00100e8081c1d0000d09415205840500402121054107050700403da002103001a8000580030240301c2c0c0000080e402400442081000c00c1c0c004034002d42d60f206403001c42610320b01b100b03100410355036142501c58061410904ae50b070309250000d002912075008540c2d4494000c1140004a200c03600c0c0076020607055401412585070104440410049400c081407c408641d02004203e07665a001d002c0c1050100841c50010a09100003ca000680d4032181070783c4a55400300c3d013044100e030b50000b19614244070a007064421a4800f410f60b054040198200d4840000900c04480410000e0b0465504100d06950b0401603a40c0310704240d41c80b80b0541d00780d0340040c0e00041021023000100ea080c4d40107560300401d10355408034110340f81400c0070086800b90706803000071805c00041c045e00b0300840c1c0c0d820303009185c6075a0141101d00741c400c44e00c50151080340510341e142e4100040080aa001001641c1c11070341c140c005142054005024103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 495334991 1250 495333741 495333767
    0x190b06120f060612061902030c2b1107110613030210080f07140a11010f060602010f0b0a080d0302031905090c0f0a08190f0c320618040615 61
    0x1000e100304c020010750115500d170160024151003a0002e000110010180d040030346840120102003201d010348122a40582401c03082881d203a104000422001d541111548001d040c40440d04120040002e564000c0c1d00c040d0f820304446090f04e85000040c1c0c1c200c90300b041e400c002c0d0420000c036140000c264000b03500600c202511034034078559503508001207680760380c49801002042010b020003404540a81c1d001001c50706176000002361540b5500b41d1300c003036078110f03480080582d42d02e98641040342d20f6405251481d5500342c0340248000d14050580d50b82d50b099180f08800c06a0100225180c000a00602c0703035081007051080c0001e0a102c458661210a954061440390300f01483d58003090070524501011140e440c1c010f01000e44100c0b440c100300400c2040700b00c81c1c400c20a12100000740d0200d03101009006003d030014000d01d603080851444980940c1421007420301440c0003800d6a49500407104094844081c038000d0003111004240a0485a000381410342500720000d4055907001c0c400b0a041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 495336241 1250 495334991 495334999
    0x210f090c010c020d020409050f100204030b09060103020a060f020a0b1e070e1f050c060103030e0918030304060c03091a1f080d0e0612070201061502190b06120f0606 72
    0x10010310041d980c41e088030701c00a4000101c882c100f0050310f09507011b003007964081c1c01620844164401403a013011042c0403458907855002c14140140070701c590802717a1001d21320340240303020350458000409005d1148650000c004496144560780d9100b80030001180742d012400c112a424880700310821602c15959040d210804071f000140039a01c10703100042e03a504042d0003041c1140541d5401e100300610001c2c2a014060208004045c4a0007000718600a42c0a035841d007800a1a24040109504000e811400074030501d0410101c001c0000c0102c2c2c0e001540706000045500c600340e404e03000360200100280c00740c45a144015070071031400c4041c4e48500940350001510740d0115401c070703844c45086e0103121290380c0000c5000044038000c004052440c000141640e00f01001c541014001030021141c40d40181d440c4c100c2080203100a01c502100c03895540040d066100402211190010300c801020f004c4601030008616191103001d001a0f007800340005407548025404200c90340d0f80701c207807229401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 495337491 1250 495336241 495336253
    0x3030b0906060306010c0b070c02060c030a08010b0406141308030c011b0c05061611030310150c2103020d1505092505030c0d0501150f09060e0105210f09 67
    0x41450084126131280138140c44168020a180e00e0b000c0d12034000030101c84c10f2000c035072098405640d400c00607040613800a00155030350400c100d0002c0c48114103900c500c0d140c250511080c403665802801440c0d40320b0b145901c4580b100f00c04200800160345540c0104024000042c50cc90704c0481900090b551704000d00c181036244084800440f48411603540240482d0807007004280c4000c141e40303001c1c3c0000060f2a04007100040002c94906590080ea0550781c035207030010040000d10103441e28828103005508040035050303025182c040140d019019020b82c1d001c07074420700300840d6001c0d40c1501c0040d441400200100901d101805945820741d0160345e200307500031000a020103e89001982034410706548400e0004014101601e0607003000d03004102c4650280f00d0030040400c40c0c401c103802000e1021007501028040c42c000b40c0417081d11030f00b00c0c040040c182e00c103010a9402807a0750302d20001c01c0c0381150351581952014110124102e4100e152640b110081c41648280d4013040d9005548180c10303640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 495338741 1250 495337491 495337501
    0x50a15080a0515071209020d240b0f0609040b0310060b090a050415060516060f050402040513030206060d0819020307020a12020904150207120f02070501020106030f02090414030703030b09 82
    0x3c1c50714085803400c001550045400c25001e80541003243c80c1c0c5c0c4083e161040c030860b1075462000a240031044030b82034000304461006a00d003540a1b40258410549801107140d00300340204040e0300c94480c01c140110f0f1034134248012510200580d0281071074000d002c0240c0d41c0c0b00e0710482c2655000040140c400c406015012903540382c81c3c811004109204140080c0c000d15002050740c164201a420040e0440f200c0325840100d603150083c00f002d1840e0800c00225850300c0e00c100411284090701148104041c03018100001e03400250003a000308049030207841c440203c1c5402803480c46040680c0ca9000f034944508030455800102800c0994801c842c40340d610341e100e64042c004c81c450500c0c00b0754407946520100300030440301126400029012003002d86410f1a07519013502d2080440b051600103031648207403040c00c46e41848400007a0030244000d2020b14070315251404803141c9110f001e4482c01280d00458208007000c1500c0074400d4980044d20348910f11030038060700401010124900501e400070000f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 495339991 1250 495338741 495338773
    0x31b010f1103010f27020c0105070f0305060d02211005070207060206040803150f1c0b28020c0c1c050105072c0102030f040909050c04020c0d03050a15080a05 69
    0x390580b010000e18100f4070b45001d03010064009241d061488004c41c017004020040b00320300080c0103013002c810022580d814041c800800700c0118031b0100301018903103001e12241d030340c6047c1d08219441c0c0480380b070410140d202203092003d800902d5036a00d1441140304031608500250002e80c89070402d42c09907590a5500e00041e601c2e1041210001d04083c4100700140c0b440f07480030181c40c0040750150054400c03500303003c081011440c504010617040a540c800d0301c0704029040805542c071032104000840100b103511002c0c140c03a6055040302c585180c002c9020303450310030304002d1105032210040107049403034071900000d8641d1104013025207542d4200400030705640e0080f040c603000d00c00c0000c1400b07030100502c1603001c14590100c82e0340741103000070071800300225140400780c00a04160000020300c1046803030140e24201d8a01c2202c0d000d117005204070203960700d0200316050fa0032020704010480d42e4030485541c006114082d261103000543d10700118840e90000f0702c5102551181c0c04841c51440403034620 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 495341241 1250 495339991 495339997
    0x101503021e1c1106040b030a111603050d020903030304080408060f150f04110315010912050601210b0106030509010c0306030b0601050f0c0105090d02060c040501080402040e031b010f11 81
    0x20030b800c00c0491070001810740301202c0c40c100c0c10740146900c0c0124050b040004940e60711503400444203200c04424040501160302c81c1100941d01882054507208007884084600440500b0142c1840404a000b0210301201d4045030640580141500c2c2d507490145041c00d065001801480d40c1c41c8103140c000340e0742201043c00d039800b444828400004440080301000010b6882c950040e42080c3c0f114203402d51022080041d6000d0080c1480111b03030403401c14001098202e039680105182c600d0002420701003503000c565079054840c3c5020343c0d101080c00700f035070181c00314031101d000b00940503c0c000011070725410340c0045e00500703110000f030203c42c06c1c2c41c104070141c0b0380c6400058604019030010590547c060b40007020040800480e490405004200c91406c5400854010f20240c110301324a294056040c05101e03170100b40609440e046c2410000024221140284000d000b2951510782d03400e101001c00a490301c02d801c103035280c1c003203080752950315001c1c00304450664585420021140301450104060b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 495342491 1250 495341241 495341299
    0x80412052803090c0b0f040311031c020c1005040e2d04061a042a02210703090e01080316030519030e2e0207020a0b04060309050d0e0d03080910150302 66
    0x110b41414123546608825480c002e0319654148107504004170400c0100442e81880c00590b00588421032050040c40801e120440071407007000b0040100b4001c070000610f4442c1c0103800181c2c007964520040b08110702134410403035284070307200600302004100000c40c1c00200c01018002c039484000c0c4174000c14441510b5460042c3c5140841117030800c80000040c010000841013030f4411110207401c60405424120000480c07008804400a0725905154001900b0001841c04100d80030096142115440d121700440e51603500d030300890f15040d001c4c907115000341d0310032b9120715401000701e040e1301b08050003c00e440040400ca5004207800d0001d400040d0200e0a120600035600714041041c1e04c088800a500c00c1b0720803179002c00250400701c0c4610440c23024002921042e01c00103000203642c00c016240100303801c060000c110081e0913135104c8e6140e158020400f00e0f07040c02c220f911604c2d1240b043c1e04003068010780c440b42d240781500701703541e0b2070300d100b604400c880c0255550514503050354206d4a090100700d403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 495343741 1250 495342491 495342517
    0xc0a09060506030406050703180b04060e0c15090303040e0109020c0c040606020a1106120403081906031208070207090e0a060608240a060e0f010e0601080412052803090c0b 75
    0x9004145d17290070640c1e100101e480c00042c15140421000c0d0b0740c044440303007030f10107640700340800c801c1120610484241407c464000c00c1e105400d000042d8003400301d00c0e100d45100c1ea0108001ea1140ca007001610040c0c420000c091030150b85071021070000b500121202142e40c403e12104001a0420380b08603001d42d1855409044800426201d515000503070040d0281c0181003004004600e4003110007031405107201b40e855000c0d909100b404110044040d50980d0080f5240030f00c10000940d109000341c03520f82072802c00ca140d0b552501026070520b0308540c440e0038903506120a403681d40d900820f0490240c0e00c034100801500e51070f0130326180e6400c1c503070070b82000d444100702c4400c20030741204401d2948000c00304000b0039030540310030881001c0f11059460006244040340103110348a140300e80c15a00050a1034103d10b507251035120102a41444611035052100005a1440794001403d415a1240181d031059003402c05072003000b0028110800155810015544003140c0440340104559411140c28 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 495344991 1250 495343741 495343747
    0x1b0d0c0309051c051203040c170615030f010908092103090409080c1f0c1d0108130506130b0907080c090606160501090201020d05210c16050c0a09060506 67
    0x84248550414003c058504440000521000041c0100808a40f0308100ca101c26180e0800349414540e00b0704540001a4070307141103015000046000030419030042d050031003591400b10a60101c1c0c2001d509410b644015400c3c80600f006001d4440d00404205100790b403510424a21074800c501e51090400003a001a0400c0022120524258201c45501801484018030f016424070a00380f40500081119040b00750701d00b80d0f003904034094805c1144841035410b114003854075543d09500c107221150f014030706110421010862048514501d401e10950040444205040c82c240c51900c50b442880116604070034034001400300c850108a000450380340e90020a29401d00c4010041110001082140c01050074030821002a0020403042e2055014100014120b941c0c0c2c000203041490240403681030003000c12000c1d01c001e0714290040c1c0210446242d410700b5840e180d038403021601c1010018a050300a051200c000d12101042006000404881465169545602032401e880a0384141c40c0d1088041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 495346241 1250 495344991 495344999
    0xb07021b011706150a03051603020703020a02090a0204090c0e09060d0215030702100615080a06060e09060a2c090a0c030602131e030317150111010b061b0d0c0309 71
    0xb0035410382c2c01c108000d203140300f118a030000401e0145c2084030044002030311a0f00703000031000c1e40790300d18803441c106243c15858032010b51006913545605a030005d008540450005100b10600e6064074003400e0341c030209104e900100300c0020704007101e0a02c014400c51083c030204000b0300e801c04118407590b0b4040c0010a036035042d03207000c0445810040211085d0300400c899500054405c2c450180508020f031041403030364100a00090183d80001d00440c403d600e824014007040d90014854031401d901161224655542c410120b044501305500c852540c954401080908204c10507883c2c6803109100c450b40c44990b1241840e0341c1d1404e2844018222120780c0e103090021542c075030010464070125400d01900240c0d24440c0d480f440340445035443c84911011814010150301407000d150821050341d007444241130042080b184d4480d2a090741307041c40920004180604801c0d003007051085002004161147d02022210070741044403840301503d4080c014041608601548028030456051b41c3d84030181d42c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 495347491 1250 495346241 495346277
    0x10e0d080403030209041803110f030313020604050a0311091e190b100801090c030b0a06111009050106060e04050f07030c210624080a0209040e03070b07021b01 70
    0x4041c10030703010142c00308600300f001d0b2200e025281d9182d6994016130000000781c02c0042a01c1d100c002008920742240c020754140160000c1a03075041002c034190740d40703042d02c18400030300280b081d6841030390042100c0e6400014005100503003018690262788100007550f50000c1c011210410042e8001d0780384405002c00c000b0080340309140b4013921899400501244018001100d10030076000150001e0781000052095001d14010740c10f0f03d510700c0c20288225444100021000b1015008010402145407131480756940d0402011084400360380040140000d1401e00c903001e042d15008a001140071284030f51900d040a2041500c2400f10522060340303601d888800300e028026401582c0100300d815618450b0b005108007580703a40304503611000400d00d103000000c60f2003031400859041c030484045690400950404c0015901100300700300165a9450000003500802c1c482500858074440030800c982007041d52180303180280c03c950211080071070070007903800418120000c000d0014040030300c281164a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 495348741 1250 495347491 495347507
    0x601080709180206071b05010929040e0a09020a0f03081801020f010e070f060c0b0a0b061c240b04050d06090807120e090f0606030414030307020d11010e0d 68
    0x201512400c02c0380403150300040d5040d00500030640d500a40d001300312a90700c4042c0581c00c010300081c02e0a41456141106072240f202c0b440002c0c1005461034060035074000c920408a401070002002c00c1c04081c1002d01c443c400401e03904800f2030260300d810704086564503140f5241e108584c0d01202140c0350186814401079142100c1404506510030311000a041031001e0045500d541d10304802445100e1800030100c801a220364080d00c14448180c400c640813548028442c0c0d44811113100101d50b8000c1c4c1000300d4560b11449142c00501e2480340e413605041203540d04060a00081c038907450301003840b1001240d02d904854030410f40140400c1000b0846400c02e01160303464103000b5080012514660740310401580d10242c1d049500c6400d41043c4041e16401ca494003080100c26501d40303d051620644c00e00941c200504028816003001c40042c042260120b0b074222620881c0045c0ca1701c0c1e003828480a035039884018200c4c000320300e01c0c4070000c20b0040c0500c81c282200c0340d882c0040011800031340b81554484 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 495349991 1250 495348741 495348761
    0xe0c04090e2d1203040201080c03041b15030f060819050c04050a0204050111060402030613021c2612070302070c1215051f030803100f0803030115020601080709 70
    0x4040d01c2c081805500035441c0c0c00c544070785800001e5010340c1031001c038241480c0c90300101544680d010b00034000940d912210b2564442c010008565880d210340c01e06a4032504200d040c0d0308030007510700010818958907418a0607100b000c1e242031100c0440c8480d0300d02540c100b03000d011980d0380306041204210f42945050b8200c1e070300860980e0040c80b90307680801c1c06e0b500104c1e43c1846581c2c0010f410484c95a1045a8a05880c42030000d040d01342080c1d07000986804000d05140618004d03100b51340c4c195920700c4121460950300001c01c03890060707689050b0403a50751551000d0312101d88115030044ca440d181c8125410300c0d02035003803072501d03981e030b4481074009411540040c3c986039842100801e2403003001a001040728010705403010100442d9050b54244d400007000200d1428118030609440740d10310b4007070400d890340400c1280d100d681d2070151200100751948030b00c0041c4003802c800100072102000440c1a901c0311010862940d155010503a41d0720400e101340a91030b0301002d010000c092259100b00303004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 495351241 1250 495349991 495349993
    0x90203210909090102091c081c0b0607030c0209090706050d0f0b0303042d050d03030c02010f0c0801150206160309080405060c0c01030605030f190f061d01060e0c04090e 74
    0x404528041222114220b070200c00a80d40003959180900d0301c0d1400d0069001c611f8a1061031002568802c0d01038024441035403521600d0385244155003115130440000704c10b01400d4151200c14a04008199a49480707003680600c2c10b032404101e40510229112064640c140c90351071a124403109040001c0c000d000002d10883e5039088800c06550702800208010a51801c81c4954244c01024030790350510008407008064182500400c0350380c5a041101401a400d4200010010700085c003d078058600d0344112080d480c542a4816466070700036060506072603a501c1d400c0e00d550f502407030580e980c14081d510310842d034512a4810038400d10a4000c61216485040c481d4245907881c1e0214585400401071490300350003083e114045941e01d48280c9004103400c6005100348090300d05d0440c0c850b074070201c0e140c8142d04401c1c269810f01110103007a070f440583c480340401c9900390704901004510300d5101c0c25401c55084c0b0400184458a42034041d00a03000060224036142c035040e030410091140f03059240c06 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 495352491 1250 495351241 495351247
    0x21e040602151512100b0603060d020405060f090a0e100c021e0a06020414090601021f0b0420041d01051c050a0506010803040602210f0918090a02040c020109020321 72
    0xb5440d44120020b54402240c001c050044114a01c03170192014a000940100780a00402299a503524a0142c0081d010f43d070024083c0c5428001c548000f4210001940004001d82440b40390203103603000d000c5903140001901d280030011801401030f5203001480000580c44000f44031a16220005685084a500d004a6220007007a0391200140d070401c0d409010b035941c01c5010040a030520541c103962049003480600401000840001d2100301480040c1c1c01c4c0c1681e880c0c40001d540c0b0383e03034010011109055403190326444601100d04c450350142c0941500c10800118120700e00001d0000c041c1650350040c01d2840c090042c1e500d4110240000d2410b0325540301c1c2c040020701164003030100780c1c00b03405103001540d46c540c00c1030070107454848410012844c01c2c84011019609002d0b14064402c0448481c4030f05640d50788030000179160b806002a1402c00000410a2104a8400013031955203948207071070a10401c5600c10003a4225450040302039016008800020520f184100841200e07038151204542 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 495353741 1250 495352491 495352531
    0x306051312051206100903080a030e030d0507020c15030a020708090d06051b0f0d090c0f120c05121518071728080a02010605040f021e04060215 63
    0x201c10a44000018041580002c4900c01c204141c08266409142030b64100f000c600380e00c1e4006c3c541711192001410968000c01c0c42400641b00382c100d1803080381c001c006c480e1a00f0740d0070040b41c0106400d940345800761081407031256513810024500c0300708101c182c0c915401e5a4800383c500c4060f60000c002111203004c00c00c82c2081990303e40030581d0f129801958000389500d0410401031070090050000030107a101845004800411442141d0704940c025401240500303140c81c10b00700c5403115070801034002109402c0030900740030803035820385840e008504e030304540c82d550030070b0160040004040907920380200d140f800580d41036000c0203030000d0420001c0200340360b81c0c1c1d80050911903103070056254814002c41c02090f0030810088c5132107168101d0042101d500401009806880031360900801c0088086a404000c500030743c44440141005041400902440c06455000b544403030280d40c1128203084101e0030091485055030180c0e130241e0002d0000b460f603010321624102000b40030707a48803003035000480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 495354991 1250 495353741 495353753
    0x308031005150c06010608062d04020a020f010f02040303090b0a0c080c030a0e030c1c05010608120405010f02211b030f190f050909072705030c06040f03060513 70
    0x2c1004080a026540c4030603010301d10724100403043e40034404003c13068081c001070307940c0d88102c81c2a18000388201c42c110302c80148000540d080d12030300d8907800703880402c2d5030a006070085821258942040000c0014401e890401c10483c0120300010300041c240150920110803072500504800311182030005c503d2a00d80e0381c030758083c1e10010041221341c00200c2e0825015820580ea1110010100c000d01015014003002c10650b405d00ca038604103603030644000e18207100e000e62141002e802c145090b1034140d4420020345100360b01501c140da00158016050004040c03010a01500030b00b1074041d4515020140c010400d401d401141c0030012003410b0340d8841c00b100c038003000140340d00010381c0ea4140d1030745510603854080d40300d200302d1001406400580700784040d901c00e045510303541c01140d40c8844c0e500d81c11030850304109a040c07100c01c201014020184100203018880c0204c075401c50440301e25400d80300c00e10900d03009920682011280c030040510002c0e8090708196803001000c1034480c200e030056180c031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 495356241 1250 495354991 495355009
    0x1d01021e13060e010c0c0b0a02280227010801060e0a020310060e0609090a050403081b040923040b0609101a0c010e060a05010305011a0d060c09050a030501051e09070308031005 77
    0x1950780c044001941042a601445216200e07142000b4424004e50712b50300902c020843c8040081c801c4c0e001803039511a5080c000d081603004040720b4014a250748c3c4a4815900074a118040c01c02e50b60b903048001a110546402140e00c14911250740305402d83c074011068a5082101c03085591040b07092000d4000c0e901d0b0503000920450300200702080d6800e2504000c2d1100401402011642c000529076400c102d17012011502210b548000019510650390007040310124030552044042502d80180001d22422142036401030740f003100c2c00501d91703c234402240f0007401c19200b120798250074010032444075130044000d060700701a204004103480d0301e40343d2301c0360522004440e442d00c0c03a9652401172003402024403581c84490400008040c2891510001034500c40c1034610042046860304245070751070344203110b04402004040c04000f012622464024042c003800c80b5040000210880d200303040c3c11260510900518041c00a0f000c85130850315a031259600082240c01c0c40c681047d400502c5458510b05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 495357491 1250 495356241 495356249
    0xc110604180605120c03060103110a0b07060e010506030601050d0314130620030708032a0315030f07050a030206031e0a020712090303080a0f1d01021e13060e010c0c 72
    0x40066818140f00070003840601010694185500003088400d4076100042c100e03040d0781d005001140070003038100008480581e1504210480900451070314100706a603041140c00d1041c0d10001c0c8116500c0a080c196030380000d11441c0c5d44a81e0071151900828003e013001065162829280b03490180c01c0c8610b5101ca140f50780c040c200164030390440c0c03050b00007806520340c2c030719160101440c0340400c42c0d01c0d451024000035040743c0c1e08c240c2031003500b011014242c0d021031030a05085102a00c078034054900b4100060071440c0d90740203010b24500d500440802152482c26100000e220f084514250340030b108075500000c2000d140c0c01c03841f202d09081c8015142c6801c5c42511018000b598561003840c1040a90405c0440a41031090340041400040d4010000e41e0b070200c80b62400148415120b4808006800282c49581c42c007113135a0302041c94000103400815400349680e2101c0311f05020305101441034480c12524541c040c1034600c0504c8103511035903120021040526017040814015100c0b081103028a80c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 495358741 1250 495357491 495357539
    0x9030601031109070503161209060623060301030b0a050c040f03080a031a030601090f061a030a150305120d090b091515060409320919030c110604 64
    0x8405410303d03140e02d406074400c0e003034a050307425820f100c088004800c0c0c00b10706480511909541106c9550555403103c000303107401444c00d11220341e45144079400c0c4c00108035555440806d010034415103080640499040b42d50080100001c1cad540c07200140020032000e840704030341c00030411000550044c0720180102447c001c42d02c00e9a034a11042014040f41c640300c070710305c181c08502241c0c92a83d99001c646141110b58172600444c000401d0340c1d0701c1c4000c10554110740890369441807100b2080c001c80c40a1442000300c50710810005100700c2140303184285510001b800c0da4050b80c4000e0705041c0100c064494441d140e130340410603510903529030340b21203012141503826a209044000a940c403584500783c00108610400e4032890307809021a03894411402400c8403185c84d0007000c848521001800d50b08101a20042c203600c403694128580400d1064403116200c1c403a024000540c910041c0365200c0751030b0b2589658052203070941d030f521503103032030700302c41551015040c040020410341c082c415401d00d0304228 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495359991 1250 495358741 495358763
    0x4060e01030f14060d061d010203060f09010b0d15051203071101090b070201031104050901080703120e090f09011407050714161e051908100b0a14010201020903060103 73
    0x40001000c65220180c00a115810a01011800e90f41a52000d80199082e21800d005580b1030038014080c1204c1c40c4402038400901100208203081075014500a440848903045140c0700786e03003000900c075428000c0f1185003074208951082c90003075501c440a02000d42d0092103c8581e50030000701110031009400710240c1000030600b040250159074504103c2003403d00510850400348000f1060150705c00003418103030384900d6484284080400d5070010300000340400242d607110b09100b900c50b0400e1104880d1111200a01031484e40290401c0d80220000f80ca0710802c0c3e0349405004000140103454100903550b2501ea0300d80601c9091241442034480351503a0f0b90b0394420b40362034840c01440302030906594000c6000c2e801c28032030a018100072104007484a0b4520302044032007400b586182d501c440d9002030080b40c50140284c580c01c01b5000c1310441019144c640b110501c11b903003656111900280c0c020300c1003801340458140540301c01346000061000506140180021030718201702070304140d452400340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495361241 1250 495359991 495360017
    0x100801090e0604030e0f010e040c020a0506071103070807080d1505100302040b161b08010f060602011a01030e010f0614090615182205010f080a020f240406 68
    0x2a004912035400c040700200003a20302500c0003060b042c40880101c0c480e40e114400012268403a001d690f0351004000c2c4200211140040c020359500c6600c10704030f682d4059000020241d0340188190805400d00401035071409405a44890883c0d0006c0e00c1140c01d500240305025140304544206203983d045032804800840c100010404141d2a0300800020980100014040d520400c1e0641d62039447c05100304900c55228174220140c1c1801a030034240108144400040f26601504084011807601070100300c96600d64004a003a0764405000e0003000000c0121021254440c0e4010026035202030000650b0100c000454400c2d546a607208090000052024a6840c076041c3c1c20b1340e800c0001200d0071a155a0590320000442c0a51084000009036015401e0059140d240b5094424501d9480c880c2c416020240d480700200f40c03c2c091600760300d02c0c2c10004156800001341c074028131b540013000300c01e461106900b048502202c0e464084a80300c3c15039210502d141821000c0c001400076521420139007803503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495362491 1250 495361241 495361259
    0x6020409050a0509120408030d0b030c150a030c030b030c0909101d01050105010f1713240e2e060515031b03040f060203090c1f1103040303050406051602100801 70
    0x5070400d09011700c14104010800044000704a132248025100040f40b18103400d4000707030400d01e4541410350445c550300d050f140b8840b1300500900c0b81003110340382080004440e220460880d0500301d019605980f040150030320320300d08103c02da03a00c4402c2404495a0242134143c04059865881c0c407488103483e8100460480c070020302880d400b5190a02c0c2c101c4034005003000040c8031510b01d41c410f849901c40c1a020070807400c0c240d0310003c816504038520041c00c606400210801d89404d008074044d41d4508107103c155100b0104150109412a8481b21a2060480c0342e424129020107c0354030807681d5510300180f01d0b159034031101007007403818907065180d1514030100184014541c0c2c420310f5000b41002048005042010300705032154100c000161250358910a03070746000000d21049510858148442c03e000300003031461003000e80340d6a0350960100c10941125030302d028500000f00031503c06d12050000c0c51140703000d0240c0030513950305514000c180c1d0b0041740d9001c003014050030010310410014010524 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495363741 1250 495362491 495362503
    0xa0b100c03080114011b0314070b04020909070b0307110106081e06090703050307080f0702040e072d05010e0315010e0609010605070c0b03061203041202030c01020a0b1306020409050a0509 82
    0x1500c1803e0040c04c1000000090100c40002110030724956140c4000c0240340c030590038515103100100005594404c0360401124100b000c590803842002810002072140002040003412140001d03001421510b03880416140c8044562810007250345e1081c00142a010400c03580701d802911034190001600380c010910b040c40b000800c00545030340104001c1000680c004116010300380c006202c5501c2e510703003c0981407684035120020394007604245880d010000302003281003c442013518200001c070500c00d00c0c1044034800100f4100011040c0c203003006154000d800721001c010008068a80440c440080f00548020a0b0850441c500196040064500701041031902424140c00e00c0c9040502c90740d290240c0c4803942c00b500c0c406801c0440880e0a5072207000c03e500810300010300342e03030f01c942d140c080742410854180c41c26407281c03003030f000e0a012950011844003145a00001501c009942d0300003001c540030010103080303030480d60800000031071803924480c03e8011107961002103032070705104805903d408 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495364991 1250 495363741 495363749
    0x210d0207060504021807080a02130b0a0f030e010b0d0f020a0806090304030201021b10030c0e0411070b071701090c020a0206040602061801050c090904061103011206050c03040c05090a0b100c030801 86
    0xe021300c5d042c00812500041074540c004421100076a481500d614254044481035000c00182ea0002c11a80740f100c0d04101e21b40396107901503030108840f03c2030b070340d8850036038840e03800c00e54000d55102d40e110003003030340302074414651800505441d400940c2d07010590320b000021901c655440e000800d09004540e414030443d80003c065003124402005004001404001109500c80c2410ba40e441c5085015003e0504c114a0350784c000c00800000c2e01504a81074927900603075040340e800300d207a0001450036000344440d0b00880380e03000120701303103a09201c2d042d001000312407055002d6214000d420300040c1d458100600c0070b042d04c3d9000d0000c0d030410210300c026408440c168407140342d0410f41004504400310041d0740c1943c40494845045444c0c030f080c040001c0003560180022100000008501c2080d420800303845c2604c6244200480ea070b03001c00081d100c0c00151401402d50003508d00822191500c0f001c0315411801020001032074007401c4001403260750803084440c02144801781104281f58011240ca8010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495366241 1250 495364991 495365029
    0x171305040501180e0f060c040e0f010f1232060f070225080304091409010902010806040b0414010324090c0b031306060602030d0b06070203210d020706050402 69
    0x26505001543c0402d0026200714143e50399900f18600d90900d04000030144103200500f510030302d04082c0094a059441030088814480c1c554012030341e505942102c0504031840030034544000b5050480c0c1a00003101c1160554911222101d00081900c04822070324120880741c101d01d07103a80b400120b041c00c2c0f00d8000c081c0c0d000c01d0070510401042031b4001c20207682da110400c42121941d0000d0182800c1c04ca031681001c255848082000b04000007107070b1112841d0440a1006441642d03055407031800e8441c15500240001c150502261090509030040c10602d10002d1020075544c1601550b400c181100b648195181c120a519100511b0340784902d89015220050050012900684038140c400c1128880c101c8801ca0000010b02c55407424603c030b1049640c0f1034418059155100d400a55135045442c48020032854002004820f15003102212512540500548080b80c190812040010315a1038445480081009200001c90140c4000d1990701c4c49154005900e08140c0113003c1145403282da0200c0d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495367491 1250 495366241 495366251
    0x3060512010504170310090f09020a0e0403170726060406050a2103020a0f0311070b0c0c010305150a0320060a050304060f0b1017070e060d0e030717130504 68
    0x2107454131501d4400102c0181c501c5a17aa2582241c078240c2141075400300c0f03449450202d01003100007507500111045402162001c5240d601d0b0380c0c110240d94401e4a0090204420115249843c509442a99403100090911302041192100c241d049003040c00558a1003c00070360800c20701e840c04d440b442c005880d0554004a0b4281088407407420000209210300c62441e5842000041500c200004407610354040580d00c5c0d03048281c640608030860000500520380a90b16011a101020000380c07455a20703407100501e519076480005500402e0083c24103584445410350f08451a118099080003e5114014000c0e183c2c2c244004444a440400092441840104429102c0da0352050070303250801d40042c4000303800000c202c81080181816419590049041001ca6580035001810f50343d84003070f07403400c58013690b6404004403032510318070b20a00d074050828800d0340300016150f0b1104041d103200008503860800c007038031900011100c0e141ca246506800190741c46c000740395940007000501e020b90342804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495368741 1250 495367491 495367493
    0x6040501050f0c12040204060b2701021203130201170702100509010c05040e0c070213090b060414070e060c0f0705150a02100b0607020904031e0c0c0303030c020f0d03060512010504 79
    0x851441613100c1490b500404601017010341d542d55000200808a10000315a03c003014056400c8503640d4400d21100c0d2207000306645080e5001041680c8a04031081d42c480c0b03580e9030341402c2c654017505005c040c0c0c1081040c050b1050302a92802286001e603c264006041100165210209a0b20b0042241c003031641484000740b5101c0e00541600d0594050443c0d031360290396400c007122510702950790003035440942411242d052007166071100b42d107039000e821700c0304403a40e91005000994081e0490700780880042c0f00002c0300d0314403d182e41040c61000510306071801c0702d40c04449180c0f13440a9001803e54022900170402e038644444d00c030706101038804800d800c00182100c0a9260702c0c100c03a000c4040d64903140c08039503d503640402c588120f0b42c020444007641c105410014900e16a0016085110200c1c101c5895103074003824800080c65409100300a20b02d08503a000c4000e00f410205200551060248500f24000140480400003415a500084040c03600c0200841e0a031103540e03040c5e441c0d16081c2800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495369991 1250 495368741 495368761
    0x20c0c010c05031207050708120106090603050609180a050a060e06010e010602060114040204150917010605031b0d0212030c060a0b030303150a05190305120a02061306060302060c06040501050f 84
    0x300c2c0131418518011060b0b66032030381a03519200b4208020440080000c1c2c00764190742c1c008525050701d000d87d0b00c1309052503c0d140154100e410980d4400d42c8408a440050904140d450351040b641206006a43c84000b00c0c0d926036240c92200c40045507000e48841550040c603104008490040156614110b1154500072001c0d40b20314042c02032030358184819041c0c2041d074807070f6011140101050180d0004401c0b030010700a00504050054070f40c0540d101e84242c0080005008030410b83d01e00801428002140d0155102c10f0b016055031981c210018803113880141e60340e50801c2c0200d00501c4055503850032042c1c48582808401002604c1c0d0502d0200100d106480000c20380e0791111540d0011100148008002290603a9075407055a2051013080398004000e51404140304803480307030044805000c500007176070146016081c1c5801c0181d0003100007d440d82198a40e4a444034003034000018403c0e02c80d00401c104d6444210700041e0342d401700c000e000401c4001d128403a409940030380c095110342030010b005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495371241 1250 495369991 495369997
    0x120b060d02090f130b070809010606031a010c1505071e0801060915200703051c0e150c190b1e0c1b0d090812091309050a15020c0c010c0503 61
    0x107241e243c946640003c4100b40405500501180c120880c0ea50700d26107903d000b842094121400311483d420100000743c1903000b40103660040e00e5150103c01a00000e000444894010540542d2240711a00c50814840d038030744901c0e4014001035030740494003030b480002c119114140c4001d0004001d00240100300e80b55006d1784907801d485407098801d4080001c103004480321240c81202400352035014040e03016405000400724210b0784503409a45810514020a24201e42843e18441c0404c440d00c210201d41d20b007841007010300003421400c82e070500800341019441c2104c46a00000d0043c42e0b009d4400c00d00c05000d1002c0c0c1c1c840c2d2017981008100c80080314040c0806005400400d50460204102c014817110b05100c0300469a0b10003259800e81c021440100700803150300c44c050150040c04514504070350440119202444050400c944c00122620316000511500341d05654500814107032384009041d10b05400e841160841001d030700ca101c80c1c0e0910382440ca2903803040d8140b0001e156000001400441a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495372491 1250 495371241 495371251
    0x220b181c0b2805012301080f1b041d10080c0a06180302030f0d0f02030c071503020708070c030b06040b030616020a05070801091a13060f15120b060d0209 67
    0x5880c5000d00b2844a101510300d1070400810b2420a4004142a0f01d8418101c0180385403504840001d0346510054400382d50540300a01d20b4050600020000303083e80624180380c114400101c0c1ca0141e4442500700040b403000c5101d04080903800c140080624580e0b0107202034030b03600c0060030300007145c1000980e00020610030079081c00640c1c841c0502c00c040c0c004008000f190082c055450040e02002050340701d452040045010134010b4951080180c0700205954007120014018024142483d15602e185289444d40c0c4080580030030200c000118000050001c89111700d07149120325081d45019170780d8100082005015920f01451001540e4001415540007c0303944500b01600c60015001ca043c82c8030b80c44040c0c01442840c1001582c403070305500041040f4003841c602c480c01103901404491f224000c1d0790b000321004021080c10b01041c1140c1c89203222070102c84000810403840080c04400403140d600c504100d00204402c41c083c001d015540682c0050110b40d4070b100e048882d40040e840e0200540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495373741 1250 495372491 495372511
    0xb0a14040f0612060e100209010c080d020d020d0504020f03010b011b0510020301270506090c0a02070510120608060f04150930090b220b181c0b 63
    0x600790038911140e44450007030410030050071690321650418001800c640791174940340744915aa00da0629045100b0303511602c00c143d50310740c2944036946509000303030020490442003541c00c100184854100d03100400d9480302c4004046410300d41801005181c8107854009802a4101103044195030307401001c1c00d8030640c0c90380d01c00b000404942040c038900410300e0381139901c507440040082074602480020a0045154014601042404182031301c00c1d03030300954002d0381010b081004a100c25000c0c0000d406080400d10480d50180d0340c0340300051003802c0d01d4a04401050481c050001e055450f40240380240080301d006000c541080c481020a10000030000341c1900f00d10100c2060710142a00950000b50b0088151025400750111150f44036a501b40285010303800c0c00c1e034066206010b10203000407504038955060401c40600c20090b8101120300c034401c40929854004a4401d0f5014003400c00c2c04001c3e00b10a4240055109100d82605036141000b181c1011241c8040002d0642da0a00c3e88500d00503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495374991 1250 495373741 495373751
    0x301060c03020a140705120a0c030b06131409122515020f130510080a020a0e0307030503181507110d02041a130c0804060905030c0a03050d0b0a1404 65
    0x105049042c0310712444003d01d00041c00c01c134010040c0000541d4003e40300d0454041c0c10308a9121001c0d50343d40320b00c07072004040a003031000c2003010403098580c05510400161608034040c68081152084842103240040400051024018000c100b00090046540100c0501e4a080126a03000d0400c800c201d1401e1603400704c4400360810410340d002501c1c0040c1612006640b40c1d00b041441072101d030071a404c0c8020701c100300400040c0c1c0e0318105d0000c00259034580c441c02d0f0280c803078800c020040e600680742c03076050202c0d0700210140c40d28200900070096005070051629004d01700ca2a9050590201d0a50b120b081e0320f00c640d8410604800403150103503804441842400c0300c02000c0390181d8280c800c060340c02450000001120b224a500021035590101c80300c11100007000c0590f0100e0300c018818000041c025400240080d46942c810728a0790300a004890500d5100d10025141020382c1c0d070300b10000303000425480b82c4c4018a00900d5602c1000303c901844c0281461005000445c800c241076205070344403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495376241 1250 495374991 495374993
    0x1017040602041a0304050d0503070e04090602090a080c0a05010c0b2a07061b0f0504180b10020d0f0203040302092403030c01020a02150f06010f210c02060711030301060c 74
    0x2641214010403d0507010094901030030310301c1c0c4990704102c8040e00d0302e00502c1006011288a181200d00c122483d40b100d0400340d06800c207200051030455400c0320358950030840041c4540e40d01030868020a9610000c11240c0400028030007072400740d6102c2414010308400320070001d070100200c035900c80340039142407401419a00070300d034640f40c521940c4413040000203001001d1044a0b004105c1d40185401080d07000041000202d42815000c510007001172414042842a12058140f40320b1203082c1c4d01000c5415440d0400041441e6056409900540d1100780e20802058000a581c801c07003c83e80040c6040c9492b60300411525035006100720440b04482c0d032845070090031400405055903019003202c1c3c0351400065014000d40c040c03180b0300c1c054440c42006464004594841d0f40c0b20310700c0c5244002c2c480e20f48000555008100200c100e0034010048404950600c018405412104111101041410f4000740c081d080c1328026004200308003d0034000c0a0301f2038004201e0f03046548030314110301c00b481070b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495377491 1250 495376241 495376253
    0x1403190803090a0b0117010c02060702030a14090405010e27031902150a0218040e0d05031b0711090a0203060d031409030f010203090118030f1803052a101704 69
    0x3e03034002e02d064004000800e0050b0710407001d000f09040c0800070044100028800e80e03482c0402c031400e40050b4020804812501d10500703d0552207000816017500b05401d120005040d01d000341c006903500d003040001c01621201503015400401c600d0504012110045036035540c491058203901409401100e2001010741e10800030300002c0c41002889841d00d04103480341101a42c0891605a5510081041100d607450648142d81c01d10801100615001070810001d0311a40c0006115803610350707410b0b40c40500e02450600422034203101c0c0b00341940fa400601d0400c030b154070010300100000c610600804c00c5c1512110300c4542c0e01070b051b0600c070013444e900d0410600e251062445c0146c160003070181c03204112070150003841c003036070b40c40c00240304141c2d07210b044001c10040540b016001402d209081e9240502814800c20f03071040394642079103d15207070b4603014503040104103d0740c05403404118901c441c44c4030400c2c0708030306082164516100d041e0443e00604e030081d40186540461852000b02d410407031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495378741 1250 495377491 495377503
    0xc030906180d0302010903110706090306050c13060908060f0621010e0d030f060b03090714011407111e101b050601030f112b050f030d0204140319080309 67
    0xa00070400782c0070701071030b1900901902610400f10b0100e96905004001480007203032010a0301c0c125070b91062264074548a4902400c8090b244d550407040402c03035441910304024005015241686800c107803903103400405441c4c80401401050804990350501c04582d40e448540004007440114050545800d4540c1c50b00508021120b80480e12036158800121a01a00803619248039107001b04201540c8120941d218032085642901e40e401029083c0102e001012144040c8001854110508100c40700c5482e115030044c1c605603070003940d51201e10f1044c80c00e0110301c0e102941c070754600d4a0041d00354000c5482f040c2864282014042c480500400c810b0001d0112100c03980c00808403a2956502c0c1400105a8000c8809680040d0a54440c80980c00c0519909145039642001d02c8045426414180c030b08000c007000442c0d40e070060036500e120142003000602004c04400c000140e4961030050104054161104a10b00030342040c0410828248002d011506003034000e50040e0752070781da014200b42021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495379991 1250 495378741 495378787
    0x100b070f0c0b04180614090f13120305010312020a030e01050706090b151003270312050c0904180503070224040e0411011e1b0b0c130b0c030906 63
    0x182d008940040c0c203040e00c50b4003100030090181c040003010f859500240b1108035260025400c071f60320b140400c40050200c03c00d1a0300c400f16420b4001c000d0580d5a401c00c0c0103044203e0000000c0e00d450042c000e100c070305005251841850f000514403040310f590041c00c03054103040c03080c0c103100c1e0204800d018060150031180009a01c6800c0c5400c520b4200c000b694203100d007280c41405020f0580c0031101c0240248240c11003069407804c0089000d084605064180d04002400c40402007000c001070020109401414003840950540b03e44880c4c2c100b0600044590700010420441801c411b04008a0b42c0070085a084580541e9145c901541280c481c0c00c4c1815140401d204107507001500003540500030b40070342e005130b200e05007020701a00301000450308060300c461060103d40e4144420400c0c0d90060401e00f544000000281c0d80446043d2907444800108a8405c146d4880010360303d1050410700307a841380505215041182854041900c0380d070303240106602e41d03000d13042c00504900361820303040702e1700c0d821 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495381241 1250 495379991 495380009
    0x9010b0c16030501090b010f1a0715150e060312040b030c091206060102100b060d0c02160816060f02070902210a0b040f020f091c050105010f0e100b070f0c 68
    0x155030b01e10b4542d0007000d0340d50064412881120010600555a03c0c0070400c40b04988007030505105406915051640001341c1103540b464680714031112840a0b0240d1028017143e2000082d41c42d10301800740c0e1800d00c0041605100303420100c0c80e80d084060b1981624107403000c82095a45030799071003800c0e40300c5d8420b0300c00465005081d103010300901440041c10900c250070070b030700742c03607086040244000030b41c0d00540d60103500180031300220540f41d0455021928440781c900c119985058040340a41249a45070003044003034020031404401102d0070a040001452a40360041e09052072a9009490b00100c1c043e800025400144015a84000c42c00396265010103980c401824281140000018078500c1c1e03030f4a000720300b403102400241c2c0c151b100f5550b00c03030720138041c440c90b1000075420440444400e10615841070b800a50701307408030b182441603c0c00307040460f604061a5003070001341c80006100900c80503200380348040034418004640142c44d29154071a10b0000c01007894a410824020240c002500c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495382491 1250 495381241 495381283
    0x50a08220b0106030c08011203080912030109020703020106150f1b0b070e28060e04020d112208070b070303380904020901140d0507030b0609010e0609010b0c 69
    0x500500740405030480710580c0b400c00c03203403100c110251411032091140f0040c5158202c0448042801502003c3d4403240400a80d0710030810a02d1680d4550800e802001f1a541d010480c032003015024817488002d0718021a002c01c0200c070042000f00b0101e000c0401008001c0c1c1c000c00c6026040b0b040701680510b0313901c070908024620782540c00801d12030444c40520300c50000b80452100150030044506a80d0726000a0441b40302d06100c02591340d60782e0381040541140c1e00f0003c25010340e49500c100068003100c86402c95441a42d0003207141220303da800c041c4180300f0b0704001004028000280700003242d141c89280c5482c3c5605040960040c240c0b00d405402c8403031400f403c0c2e45403000400c1a010800703041c15002144000c80d0050024215040310000d40081400c40140054600b50b410b00040180081803076130340744502d13551682030910f10f03442116500181c00a001091800d4414980544140d1980803203038a032070700025180c5041131080e03000c8414009401c0e110440c1c00e0190351086810b001c811f40c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495383741 1250 495382491 495382493
    0xe03070506090c10051e0c070f08012f09100c02060c010504120311031f0f03080d0f0c0e090709080a24020405010507080c0c0405280b01050a0822 64
    0xf4990181e10040d43c807410f03100394004282400740d4180c6a0a40c0d112040803c0740ca41842c102e9083e43c0102d058070a00c1c46602070005801031701e01108000b4080d42000860515511000c1080c20114100a21000084c4c0414034a01415141c1070b41c50b5820100d8450001c9000b9601c103a0314032050f0200650072080000d2804000b2038150041800759104034aa02140601c10303604030100c48117142940340b000c208001203490b00180400504603418418400028a83d41c0c0d498028812402e500031500c5080125006481d800a8030407526180f80c924000c3c0305510720488001c0444101c8107000c0d100304403c902107207082e031080302004054443d18080b291110140d08000001e40e100451b800f2543d49440c0c101d040c0700c98240262012a401a103426040c0100d9694551840c0c0010405030110300c5000300780c0246e640c441c02200d00400c0f107415002084149941c004c000144d5121075280e40500304130000c01c03941d07400021150383c404c20303241c45a00380d20355440000c0032200f440303404445801c20340c0945c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495384991 1250 495383741 495383743
    0x904020c030901020631080f0403050d030e0a030504061b1506090509010209310501060806010e010207060e150f0a0f081b0901030e150907050406060804080306040e0307050609 77
    0x30b603140076001c8601036a58011042400400c02d00c403100f0085602e1b40e48a40d0402d0135001540003449051450300304480c00300100d48580050744103607a0765103d02006680d4a8051207090070320707840c00000d400c1d241501e45001e006842140b00c3c8904001071500162580009900d24000690340690140311140b09542e0140107410f8501480c01e6041c94a400f24072941c6051007140d0080c10041d0403006032200106c5440d421042080f00814912500e0040403d0450148101c601801440d110f5040e1420034000040a40038201c0b8030783d041d584050824040d940d00046100360079034007190325103030400c0d02950030003080c051411803850007480490011501e5800202508844991303540d200141e80e59082c0c004160803c182c4080d00b4218200303c0c003c4694401d40100341e40700400d4088035800c2000c13000300c940503001107542803440d17040000c0030b200c145010302407032004192901e0071110f141066201c00d289840f015185070320550341c0b040f0700c81c90b030340e002e005544102e90000150307a0342c0e2030482085 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495386241 1250 495384991 495384997
    0x15050f0d111305040203010e22120305070905010503150402090112054011040612050c12030a2007030b0103060605030d09030f140f0708030c06010506030105011b03050904020c03 78
    0x82c0360308410a804140ca007410301c01ea904139000401d4550300c5403242108414020408009450034060031a0007101040201c0861009551075030b03000125451302400080c49460b21b034120ba03040140c20401d01c40d1481240c61302d020302e914216001a904c0300c2050050b120a0303424001c44182d1414502003204403030798000d20340003d8030080e40f4510911510383e5840c020908000074881c026003100d24481c04518032003040b802418028000048003a16125680c5044a0081c000c88069110840c178403094103001c0020800340300c1c560001c40c2000503600011b0001903000b8a81456000030400c1603c640a003008000e00840d0003001d490304958480c100a00a0815802120b00030b2082e4414082c4580c8298814011240c00a0300940d40120b2076440402d044000414104240305958950417100c83c00c0c00007400901541005580c2c0d000800115810010140d108500c1200c061004010507600109801e0700c1003582c08140c80d003a00316181c00d880300c0c017550010300e400c0340c804581102494400001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495387491 1250 495386241 495386257
    0x807080c040b010507170706060308040905071106060d031112120a1401030804030206130510031e0c14220f18050118150905040501050103031815050f0d11 68
    0xa02c0168001e0006550768811a4802042c03e40340b000e0f4070f01103d0500d000750400a12900c0c002c10840d40d03d884c1e8002c5d540003a003020340002d6842c802d008080d130b0000903440c403044440e4084c040c240f902a001407105c1007a801c000c0e040c800090361140b07441030140050202280707641d00b280d403698841d01c15152481c0c0c0440f44807500901e0300a955482c503072410300d00d60403070750300004603440d150a5900f40540c1e80c1040c3c00d040c0f100c0c1d180503800700b01681d800c03241e60703c20002580c002900249520404107000c6a4000300b0203428034082ca4407034110340c030580149941200d00c41c61a50360824500500c0c141022002c4c030240080c4000010948400010303806045448001c0c2c41e0749022840707180c00b401c8601c20301c6a0101105004010885401c2136008808034070703008075103a0b841d190313510900b0b016100308981c100c40700e0355200014401c040e003264010510920303c407002400c403410001104000003120f520340d030134001c01044d542d2100032200c04450b8850036441050296040171060440960007400c0c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495388741 1250 495387491 495387499
    0x51324021209010c140403120e010314010e0712060b030c0a050c01060308071202151503030c01060e01080d170402040b0a03150920060405090702150408070c05010309050a020411040807080c 83
    0x1074102217411080e03500f07a0f900841c080d94648071002081c0d44403621954821305140e03c40755042d618404213084030b40203140d404015240351920741c8008141c07008200d40302040a103403003c18080710b0200300550b60703c8860502c4040d550072042c98140c0b41d030300801c90400c0540d8207200021040181c0c242c054907540b44281c10750107143c411074400342c1c1c0b01c1d03500c8546044000780c4a00090714450700310060240d400005030682e03240c00c0d4915501030139140719412091800600718010001003008000410010079145852214000038241d85201c0a42c007801c003034821615500c081c0103690f82e001a85c2c0046901c65a8074251303101c1c1c011150084c0404010035a000c204c514140000030000210450320810010025031404d810481001034070140074191104500c80c109824003041d11954855003d503028010140d110307540341c035180e1401000d0750040e5041500b803c14140000310001620708500e40d0448010800582d00d8407207108034003880d40085124803c0003400034030000040390000c1c1c14107080e9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495389991 1250 495388741 495388757
    0xa06020406120b100c14030a02060114030105091b06042301080a1a04020705010b030618010b040c122316080609070906050a0212040303080604051324021209010c 71
    0x82e0340008840031090b4560f00410f0307540350700f44114820907071407040c40c0c810f40c44840d0880701211030528580144100c8005a4450b00c01030001c40d114444919020408400034003580c900090401d85800030307a1009405600d84030f00303090a0b60b8600e004d40c1e0261181803099000c1d40703031054058000d0740282c4c3c4160701080d103100c04154040b0450084080c00c940c03500c03034541c100f210803007844000d40c03107e6011354840d542d60380503069664040c072040c1d00525100700c0e0202c1100c000c425040c211821415024840c501e8480c08c410743d03e8110200344070900c01c4c590b0004092030a0140e65645400b84900c490700c00c001c04081009549510070208091001561000b105540b2102400000c3c0b000b5204440402c0b4006020046c8502c5000101500400c42c4103455080a129032920f6250300540c00c200d000ca01d00904001d07071820300d44556980081c40103807031440395189445140b2081300c000380141040840142042130b02910f501240c03196108014410094500b26550600070644800c103807000400714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495391241 1250 495389991 495390017
    0xa0203071107050f1203070c12050d030c0f0e04022116080112020f0a080601090c11010218092701091101020d0f1d090709080f0f120313050a06020406 66
    0x2804000340c407000707131000740072689031030401c0700300c1000368503030003862104108400010384882418001000007100d4040b40c00c136980b5084d82428101c05080040500c0c02001103400c0b0391043c159201d01c0c080703041400c0700300c1a0360080381c0070740303c1e0b44001480ca0418400141c00c0c5e0741010301a40c800c0044005c10304000d183e413071046980400c280b01382111284146551400f40c942090190000c04c0010b004841c4107542e1002141484400d0307000c00101e0f176485409038110354221070b401083c003000c9802103141c110b1071103100005283c1d00d00b036036018080c036200182d11402044039054140200e0403e46842001aa034424003a20f14400200e481030031400303d00245500026401440248035200c4c640b04148401040b2050310304152244201003102084500d562519040d46000d40c40a82c1d03803040540c01d114823185061143c1002200c0c5500940f200c02e2120008209188080807080c15155a5202d03100100480b44d2a800041d21901888003da001c000c51a030081c01110000d0312400200c00c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495392491 1250 495391241 495391243
    0x10c02010b01020709021b0f0a0605010f12060905011104031b0f0f0308090a09020c0109212c030f07140105040b03010b031b03010f06090504020c030906030a02070b0a02030711 77
    0xc200301c8140940d000b49400c1c000b80300180c015102c0d507000000b03c19040780c0c070702c0e4200d440d02100d00c41103601500540d1002c0140b0405000b181d0140c401400d644101a1800ca61511401c0c1e180b10003404643c0e4900c0300d6820401c0a42192901c06012808e080d2607585908117111200004007414200060641c030000d0b5204d1103544080884d1403443c1c1e40b0340ca1920f1030700c1d12502640900070f06503004400130710100700d00d000c0e403000d8142c1d00d660000000d4240b5540c5402005207a100c0039200d0408010200b0031545a03115010641070138060300210034461b9010042d5031b0001c0402402a814040c4e03a0306401142d40014651302110071001e2030790303040c0001e0801500c07117101d20700402c0b035003980410051090015107001560804c00450382541084600d01c12200304c0d401c217800c59151040a00410001a5408000c40f006000229400c510b8000e02c0c800082da24441c001120340904400f00009000110740d906940085411441002c0307240b502d03012a100035441194440c000c00e001d48008460114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495393741 1250 495392491 495392501
    0x3090f26010b010e060f04030f110405070903050c12010603020303031816060507031110050405010b0301110c031803070801050108100f0209010f1407231c080402010c020406091d010c0201 82
    0x182c4079104c8001d111010300030958000c2c8036242e030707541c800c00001000030020400d203440d0500800c1100c1080c41c0480c2040107407000a401101000356a0b0b509002180c3c001c9041c80c001c00085850501540c90382111030301412013503001035454040882000000000c4100103201c440041003522120a00c5207d0441203203124012000010000c1c03000344000b030b000c0c4040900b01d4400000b02c61140381445107400035a48211800c8070b0780e035150340c110000ba0509000d0340e10701229030342200c4d08207814030349441d50f28080d22110f0503010105250303100b081c2c2c8040c802c0340007800d0741c0d400a01942d82c440c0561a901d0300d02404118244d40b03498288030384200107200307650300c008050b550f07241c91442c4184122034240348c1d850b0340c030100d503810031050000510030604c9020152042c07401e0440c6010b0001c48034107081c1c145020481f4000d00091030900c455100104561266090900607021500760001c41c0c010700d4a80c0000c1c5070700d40703400600c00c04501418200d107120081840280600740d100b08089080e80e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495394991 1250 495393741 495393761
    0x7020c0d080a050d0612140613150c1418031608061f080a0506010e011d0712090f030806030d211d12040f0b070201050a0c03090f2601 59
    0x1074081c40800c02c2e29203d10300400082d0144440412100e40b00c02085100035000502141d0501c00c00484c440c031800c06205c181c0c2c3c0400d01951240e050880303900c1e0700400c1c0702042e000d00032080e0b498a501003854000e00044950300750414009480318000c5600070030b241103c2c01d1480c4a44a0019210344440034945044142c030201d0b0045c10f0b0585a6550074241e14018083c6200300354200c881c00b141110741000b0140040e0701440041a9035407620000059008042e0001030240c50b110a00100c48521050f0080e00b0051034a000030507003070104044401007141d4400200350300321568040b02419801025030740502c070101c040d076410844440d002e0b5502107000000c0340781c5107038005208000082395484081404800c103800403403000707001002c90900d258038500d0082150003150500c00308080342c0e8401c002c3d041303858000c2d1a241050300060a1401400303810000c11030007194a80815200b000d481c4010040100f0030075003261a8203801e5848041d1400e20710251401941220055105018119140d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495396241 1250 495394991 495395003
    0x606090f01050309070b0a17061c080f0913060e060d05190809040509011d1b09041103100606121415010203040e070302030601032315040609021207020c0d 68
    0x901100010744454200500301300710ba000720039002881c4145040100402d40d020368500c0030b44440019a40d80c13148001d0a030398069003c0701c19011a5002600305241240d402241054803140c604400700030354881d01070155007003111000201051400c0d030b0040400c0d141c080c11806120b6030391506110404003d00030290141e8826441400c0641c3c0340886012464004c03071425191540300387c00300e4103944080c1e5111806a40d100344022060442504058103410090301070407820514000300d41d0b4010700444058850f00d83c0c54042010045824002584440d002d010b5a8000c5c2914510000a085134480e9501003a4154034140003105503200301410300c41706144402550729107082540003014181220360540c0b00030080802c00d4124542c0452141c203544d500566217203403003c00181a640500000c046100b01d5003020b0100d68052070140c0d5000c4d10603c4081080c8004a00150142c0503039070104449620020b160952190301518107071203000c44e5003c03545100032080501c40303458420380c005010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495397491 1250 495396241 495396259
    0x60908070e0c040906272f07080310030b1e0412050c01090f06051305031c140f072d140d020f070c080f0303040f05010f0e0c0108100f0603020f131d060609 68
    0xc1c1e50384028070322040c4c000c11fa41399007007800d02d50302d5000c1c40e4415036443d049850069410003c1184c403082c45a03201410030400b840c24210081c00c8801d81c0c81c00790000741f0400c1c1000002c0345192052065a0700038189500034440c04140d0308040d000e5600900099132041c0c1804005507200100500c1484010383c420015490464400c0070501c042c0610014803840f07944400394184800d0780c00042601402c0c181c40780301602c1c1460350000d8040c0340414190980c62598403071450f80c1006442b400b94a840650400e410b0300c49501200e00080e20500c0a070304400c503c086000422a10f064000d0446503100b401815007880d104e1000755900c40500507180520303402040024001a660008905024032070740c004144100040300c85000e95110204c10b40459011503503544141da80a40c0c0036420088040349001d581c5d051041000b1410031501800c0c05241d000220700a001c2c0c1890211803040c60464110100d150711500003204801d8429904a008404130f80410400d2a04404842070307202d0040881c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495398741 1250 495397491 495397541
    0x12051c0b0f0d1410090305071b0b0a020d021b03030406140702090403030b0f0a0515070212010203090c0a0e2403010f09030810060908070e0c04090627 66
    0x1804240940c80e401040050100500b51a202d0405031100d100c2e5451020860542c44018945407100381c80986003070400d034a040110780c00c13508071105203400444030745030ba940405528003410792a9000804000c0d0010701d0800403680403400e4491490b0039400d60b001000c10011b41421601c440500310741c180c004000c10098503000e464040070130700d44491204c3c100012500000c290840840b802d4000c40c0d292401e000d041c2c90821040080e600044032126101030500c00450401c051031141c40d120b01c040000c4072401d5580c6d00d4041070351546010000c1d5940e207061041982c442078854600e5020b6a13078100007140c0d808000085070b1040e15100c256500c405010350701c00c8000c1c0300040055401d03540e00c0ca42c40091425602a018641c0d00a844d81d40650810030030605404015520800411140a0091080820100e410750846000d9040070301035495661000041d4400c5074004400c031490008001800803a00c510f03107140503c142078202e00481800505c1069440c0c014180300c4256a18802c08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495399991 1250 495398741 495398797
    0x1b01330902130f03050c010f0c050a020906010e030715140f0d0903030615020105012c0408090303090a27060e060d03030f1505030f0304030807080a020a120c1205 71
    0x80700c0341107503440c0350072956602c42900020031a9600160303170130f03080045031405a50304003030f501e11401030b01d16142c050079405032503051700e48455a400078403850080303002c180ea6070310603606c040f400d0390001c064400702e0750b49600c0004213140c1c020b109004180e080f0954115278a000054400c94890310002a24142007554120001e200c03191044003410f54600020450040d002642480010690000642541812101c4825400c002140382500035880c1050755600d034540d00c81c45c2c005a02a45894071120502c0000b400e5004001c041904802000b5000502d80d0881060000c00c5040e4189030b29010030011481013950194080c13180c4a980080100700c6505243c441060b40501a15000401d00c0d410010f0809903400d580500d080101c5405040c04540741c180280400300d45481e00071441e2900e144d0700c100301c50280070030203801d202000c200f905003030b8001e11100400540c04248106880313039041c0007420f020350100c0300760380801c40c14520f070b50b485002d00200d500308802c6484454060205805030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495401241 1250 495399991 495399997
    0xc1302030f0604050415270b1f05010210231e090a03170a060e090c1203070308180304080102030a0c020606032e02040909141005010b09060309031b01330902 69
    0x8444034100110041000d0740054503030307086e043e11a030800e25550400109d13094180c044000b013140c2d081083c49042040d60780004516a18950390034002c918044131810311003000c400c070800d240015003228204045070031010301e402034440b60b1900d41030751904c42100782962155586402008a420800d4028444101c0410103030b000d884190081002c644851a032a00c1e04001d03949000b541c0c0c016903034000755240c28070ba440005480c80b8000d504294054400070706c41c00e40507180c0c00105180f4811074020030304c00c2c800c403009440000025592401e0a00d0518004c10291850748010300625000c200540b0b00030840ca264800c0080070703a00d10054143c8a040d80940d0f05081311100e903420840010011130901036409054003c40c0d4825020f0b104058941c1440034018a00c0f4800f45010010f0140c0e401c1d8030207403442d0030000c1d07a515032203a40e520001d41c55882010002450354200c0301030107150150540003200c100e805c42061141d840429001c01e0340c4500c0b81000e18000300f040c803d060140107010350103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495402491 1250 495401241 495401261
    0x21c050c10111c1d0f0c04050c07080c07090b1804020103051012051c1713171803010b010c05120307090506040303020d02010c0c03021b030c1302030f0604050415 71
    0x18561601540200c00242c0b00c2c03034850900802c031344642a0904040401e00b034002c0101d00e20010305204004802039a40f940045000288516030302d202007192100104143d40b20350380d0001c9880d039242001b40e9815a208010720030899a1801c02c035000e40c01303051100c9051102000c01902e09999141c40d401074001e001d000b804c4040c015129200026074801640030400428000c002516190903903261503428241c1c0b620f901c00522000201480c1401c03181540701c1e900400c01c5550214240d0b4516001c18254211010f0305800180842e60600c141884103a0b281a000c0c200d00811400c04103100559080d0400407000e041c0f5040810000d42024100d070095074002d03c00d150440e0ba40b5125000221b540d041504103800591110220390192030f024410386560f003500c3c2c1441c0c000c042c41c0340c0e002959680c10340b1480e03010322560a10004262010030211540c24001894000e51001140c0100300a400407151141c44250100100748641800d2080c9402240c0181c803070801800d4040740c0c44058120920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495403741 1250 495402491 495402521
    0x403050f070c091103160c08120106020123060d06020c2103040303050702120d090c05063114060304080c10090615052b0f03021c050c10 60
    0x410111540103400505420388a450010030b800d091031507071802c80740301c03a0040d1a035034000c00501000d0090082401810029480c101074081902d160000031030148604803916002844004901c10b601034009000000c0341100c2c882042d81183c0503090130000aa8283c3e03048a928081c1c0350105015800a02d04201014219055040000243c01c19171005e0010040110000b000f030004060f403502500f900a40d180c4000d044103261400c91200620482400d144250396030140b01d420480080d1544000380001440035841d0400341d4102d01042080003c0100010701e0b10140101856460014405840620f4210300d642004001400701503170020300b0036140e60200b444400711000003080690651800d5a0340480c0440041c64214155511002e110000200030f10061000d9202e0f10100e0380850720f074501c2102c01380c03040c8502042900c19000b001e000240382058920030705400040803068500c82c0d5903c0d6202d0703081c13580200d40d05c3c00f07030407102c030b800f500004000300840c182a00624100c2403140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495404991 1250 495403741 495403747
    0x41403010e03070515130812061309050c030d0206010f05010507152d0c021203060103061706150a03110d08121f0605071124030403180605070503070209040305 70
    0x81c0e006451a08000000c40d0349078070140c0120361075100300300b074240c00a45041d160b0340a0b40303065a4101303040c01509004868805020b002888a1381daa51004504071000c4600708900d0801e4185a506c8548a0311814024070540d60100d45451000480078102d48120b000080340c1030030038004607001d47c010b00b8152940c8a04009142d120202071058802c504074018060005840c01c2a640900380204c2802e8018185046910507546030046214444504121801a5a0740e00d080c010703001002140c1044050507109800ca0b441c10100085076400340701c0418000302083c4200e4100048807010f400020054043c2204440c01c0c0d0030009005603d0741d101d01c21890908000c0b80c05812744000803101c90035084c0c2c18044081c2480110080003000d01003520b48540350040a889414007000c100c04024080c100000c410303065800c8507501c00c1038185408150598900b040d0600405d40381c2a00c6843d0320403d90440c0001e000c5015200300c0e8065940300020318200030858003041000d2070300070420743c2440010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495406241 1250 495404991 495405011
    0x705011d0d2001090e09030a08060a08010c020a0b101d0406020d022715040302090604060b0a050a0908070f06050903010b03100905150c07140c060307030b1f0504140301 74
    0x4004031801000310b003402008040e50400010041c0800d0380c0310f03910340711010044c41902c0d0b0000c1304440c0404107070705140c403040d11068081201844103034002d9800d946007901e61411035502040c1c4606a81c01566004c0701c645940301030348101c02562107040ca040016141008182807600442e5500a005200041c10068404604416a8002c80c3c2c8810108004650100c3c0101c2c003901c82000c0c41800e540720f40c420805946048a188268080030344034804e641d00140c102d40d00c64200c100a400313040d8401d51910201c980241807600b0014151010582c0038402182c07026000410208441c0c9800e10b141d9a180344c40303016a5641c0c42a8103ca40554030741c881c03a0000e0f00c5c1004054a1039100c19400510300314113060507410a202480d2080403840036900f484001d002c0c81c1d060782d1403035401040d0f10088848203505c040c41e12140118003a08031101108114005800d548210000c0c0d0043d5205007495071600f805109030020081c4c0507001c2803043c0700030301ca01441c10780103401201303026000007119602 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495407491 1250 495406241 495406253
    0x2131403190c050306070801090f0e060a0f110a0c0209010905070c031b0c06090609080f03070813030b1005040605040915050c0d0f0c020f190b04030e1801170705011d0d 74
    0xc455000114650100409c500d92942c03049500e0700d101048108501070010a00c0c546442c1d010388411020358995155543d1503d5540c000040402650140d941c2c4540000b4050440c0d802182c0603445581801d0000031140c0d507600520744154000d45c1e03201d01040d010b9500342c440541010070200324904107103031040081d080c2c051034406001e2a0700d83c2e4000030715140d401820b00c5026084120b05401580c01214081c0001042c0d070303013050340303e594513031108600c5819000d0b640c034075400a41004100e03814061a444107000780301c2601c10036141440566215020301040d00c51500700186240f281091950349203e85501c02504124060019840d250701280400143c0c0c8010301c44068a503a60b81c1d001c40035503010030000c41c0e2030310110094000415230080c900c800c4201d906000e007118103020001000c02d48100c0700400300000c020000c03105244082c0b55084001000d0141407030124450100101c04200000c0c2c150460381b050750f400034480404c01e514410307007041051070340d00800d25403048000501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495408741 1250 495407491 495407503
    0x6060402160614090105160206060d060b0901031101182d080a0302060907080703080f0a0c30050f0912030c010e0a0308130c090e0a05060a02131403190c0503 69
    0x14007200007160512484e0b0a0840b180506844606603c1c045854442600415003070780c0020100c60381901c8510b20306008000d82020806907900c1901c1c2400401001003400345201000300c01c3c2d8030201c01300103806200d06c14007035a00440300d401100000d01c0019080c1e000c00300d0010300e041e8940c860b00542e20b18003180303492940103003100560421010071482c440c0800c02c00300140908002451031620710740b120640b921513401d644610840010300c1c03030980b5000da000031149543c080101e0b400c1c401c0307000b070102400310324401d40c02e81400520803010703009200300c0035222560240806e0518010640c8204010644550765072250341c002400149400c6002b84a80b403054420000070b40150851450010035807180141034414007821081002e0101d503014901400fa41c1140b100014440c8042c0400341c581003032502c0007840d5204c0c001c10041c000c2c5c0c00f50080c200580030b000104151070703285c8803c00410710302008800d405500980326030820020280b001d003072290180e84560b143c40e441d000400d042c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495409991 1250 495408741 495408761
    0xa0b07051f0b13020f121012030804050f0f1e071205060609070203271915030b030c060a0806010c08070303090b0f06090402220f05010503010b0111060604021606 71
    0x550303a028500350b03a042120800c44501e4600004602e04009400d4010843c02081003107181c090080380041c00061030124800064803641409003e4100c251500500caa4011a8111510700030108000740039000081d05061807403000020f0300d443c15000c03203540c00742503502c4851b00f0a84580c0c01e0019291070340b6950190014012400f5085901c1d181080c01480c81019000c407086510800000305503015441c0030a010f02d40c0351a1000c0c03284082d034005115411341c0386003d403000725501c5c400515a8552000000c03075034956101031002c8a025410952241d00c081003d0350422020080d200c441881031030313800d42c00704050401c40006001500c0d40c0c04036401c030035001c4020981c1d0b03500302c0d020722400c0720b1115442034800280301824506000410104c91015000900855281e803402084803c1510313032121424507044104030007c0045011405450284a454043e500c1d00c0011000ba521400d0243c510501c2c3c40024003081d10741e8810b110081d4000d4440445c4540200070b14800100c841c019000b0003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495411241 1250 495409991 495410053
    0x1a040605190e1218090108030c010c08010b0d18061b0e032b110708030403020310051603050a18050114060d0c06080705040e1608150d021210140106090807050a0b0705 73
    0x5000109e285421100d548211500b4060304400421140078101c0c01c4034035100f410800482c454500300c0503030034154400180102254107001040501c40c11081804212010380da0714108040e00c41001e154031515407030000b03104101a90b4034003600707000d1000d1480c581000342c0b825180e42c10003046141d003420a0758000e0100c54000007000c0065140400c110345043c0c1c000c2f074041049042c6101564440a45c90b203064091644580018070100d000d070340100101201c52400101510940c1303405c5000340000a0b1000b00103807000c0c0461100e0500d5420715111940c8401d5203a04942030035020707203080000402901c100641080080f4540f85003942d409e0040704908100c050300c4211600141482c03000500881d09a40c0340382204035540d448540b220521034040c2c0724005040121211030303003000075680d04002410709040644120b08403102c090340c12125140d9403c900f6a807204c18440d04c90341540700d26039115451900c280413803419100145032103841882150034001071099915a84420322103400d0f80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495412491 1250 495411241 495411247
    0x5090414070504021305040c03060f091e05070c1416061106060411030a0b040b15071209030b0115200313050a08060a02071a040605190e121809010803 66
    0x312403080180a001d40340442d82541829605052a00c4201403441744034816600c80c95030f081554000e50101002e400880c0c131003150b190b115000c02000e89031aa60002c410b041022003072504034002c1c8903290240740300e43c2d00c0d45c5076030303035140c5600a101a0a07250844507000b03003103400451902d4440003100800c52619609041c10f0b130103c51a007003c00c02040d050146e41001d452001400a00d800ca9500072000c800004461b82e0b01e8001c0340041ca91b102055401c804680305030780241d01c00f04050100213120304002c1d4080141040101c0700b03696031b4030000300541c5129005119280d94034036000311024041c81c02c3e100400010355851002142c0d400000b115800002c0c004030074006000c030304805040d041e5654a5250303e4000721603550742005103400c822540c0803801608003da02a480400d8040480201226007000e052540003000141d4035000c0041c59102c1c02d0507050350134015480380103800f501070120300401400d9401c10b03610034440c000b01c102d03100400c020640d44043c14940030b88526801151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495413741 1250 495412491 495412523
    0x120c020c01110c09160c0501150f0b04120314091801050f010507080d02070807050601030507140a0302010c060f02130b0d0c020c091f030b0f0402101d0118050904 71
    0x2002e1511203803020950032603071188140743c582c02c1c9810b40000d2080745020000c1c41c80001241c0a8032801801010b950808400c1d032000d600441c0b401d010f42e800108540c0f441c55030f5108a50391403003144501c8a50951001d0054086801240c103440040d0782c01d81c0701407a04002c100040c02c400c54131200c1d601001100340043c081c0342821800008041c1c02030070201d140800341c0d242d00f02c1a010f940c3c1350580f4036800007010010010310b04103844116032701c0f01c00ca80140d616450519182d40d824002c0b003403244044007141c00c491405515100490740c040e1036101c20003078035499040103410300720310103050503808000904400c69802d5894001307100300604d40392100c603950321040598003d402060119842034024a000c0d076944240190000500b810030a94400e0105841341582a10f07400505040301940c20040d800800761140c0744568400c550600c0070b02403070f1b04161012160b2007100c40180010540d0f24a0030b5000d007684110000130111008612a030301c00004000c0607080380c0880d40404454030102c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495414991 1250 495413741 495413747
    0xc030708060301020307020712020d0503030910050c18100306050603070e01110a2406081204091d031b01090807031814030d05030a330902031504050601120c020c01 72
    0x360440707402c800070f510b50b003131001000b543d030303d01c50060704000ca50301c074490780031596540010306286900106881e268a0840f4680b5150b56000d20565102c500300320018403001385c0c0a0032100c0032482d080540d0403403040c090602005400c84240c51040c5940c0e29404181c0740d40700009903100d40700d81d17030310100c1c00c0200724001000d111300e0380680c95041c0d10889420000a84c84820031445d107408a41140388141007141c904090b010643c1329990074007440b0100c1c04d031095543e0040064501c0d90030140810800361440442d02d02400d64402c0c200d40040c009502e0825000300c03824080c1c103580d0b001003154111900c03410388560245030101d010800800d00d600704409403403042c100810503040741201000395180401d0711045880a8202003110000c0000c45042c0c02c1d07404044241c042c001007200c0c000c04c0802c10305203000b449000b507141ca640d242000901000798001c40e0f106803441100103d90300746a60500c0040c1001401d0141030180118100300070981c03d2141c50080709156000305840c0e22104005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495416241 1250 495414991 495415007
    0x22b111c1205041707030c06020c0604022d0f030c1e180103210309050d0f030f18080d0605031f0c0509030309010f030e031c1a15070c05090c0307 64
    0x20581e050b0070300c800c101c00b054501213800d201003d40d1544070381d540d4180c030741200d0b203030a00c003c0100500d10100b0600000c6500113201c07441907100340c44040000b210400e50210314003000408040b480d000c040684c0c4141040e4810901d028401f90407581c10782980340000725007100301a03100880b01200c0c01000140c0c075060081c40e1404070004281a40e03541580c40c1d52054050f4a00c0402144d000300e0b4601810a00ca40c3c0080310854218050350b0042c0c0040000408410410310f00000003410076820401803503a0307200e400d0712044401c0803510701031915a00d0a483d034000031002c061440e070306c0000207040e440512540c094009a001e90030888807081e001c0303d04464081c0160000c12105014002c0300342ca000003100c501203000d0070074500d11940e5035030403400341090b16190705440c000881e42843c0c00d0303101a0000c044000b0950280910104140740c4180880203e845a034090000c410340b140c4545113600421016005200c2103001503180d00101740b1072102500c4c4c40300060070000c1040308056102102d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495417491 1250 495416241 495416267
    0x90503100b0f100207030b04020a0504050112060e240c0c030408071e03171305041d0106050409031b0c081e060a090c090f02071505060907022b111c 65
    0x4a08401c43c2c2490084da02c0d24a0b010040214168a000c24255691044018020007005206100a40c0c40d8074044080d1600302008880c424200f0aa401075550041200300048075440c80e940c2480c034502280321001074000d4400403044000b00811075a854080c4010001703003440000403c2220319044c68001c3c401c0c180406c0d5152001d181d0001e0000450b12284002001002421140c4a0045096000400040340c1c003580d0700a290100f00705844e04498400071045c1003402c001c0100707030740d0f582c140029aa02144020b0000740b602090320415100d10034060403c034041c24071801c6981d244c5220515000d040c05034071071a032600c91182031100c101082042c0d806132220800740150b6507140d44583c6414498092454140e0301c1e0030541d0000c51a66041c0c4010760342014103103841e04000800c1800601c415184140a01e01c404000f5591034000101101480119080340108028040c0c1420442d64071684100400185100c00c0c032044204016003290581c01e0418079907010000c2e40003070104800440c4e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495418741 1250 495417491 495417499
    0xc020d2405070e040e1e011e05060901050d1401180c15080601120e03030a0b0301151203050904091407090b01030b011d0d0c0312020120070210090503100b0f 69
    0x300021980d01c0400c924903c407098402140500486003510f0400402e10329a030620300000c1e601940103601504031304080f00d068000351504402852284064410407124681c100380100010001030501040380b022490045050382c51844c10680740c0b07425140488207004064602c0342d8400c1c140b200d015203401c010b040030003a00031403040d604070140549a0080c0300c20f051205041d49030400c120700f44c000f6070700740304800c060f203a42c1c4c230700084054014050b099510703019600e0402528101c03528000d07181d041e912140c0b001e00070158241d83c1146c095000300c400030742080d210752040c000079043e141058450451000500101414492084101d031030718405541058240000003a0070f0341c001019052242002217216084410340c00858805400b20400502240b00d0000002c01d12042e03890a407080c0343d059000b4014203000c00058141d0001d440074184041c041041910014500b01c500250004400d0819045036555007000a0400c13030b0390041160030f50b80798001140d5902c1c10404020314201c04903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495419991 1250 495418741 495418751
    0x11060c06070809030c070602070f060c0305270a08010207021318060518030f0a02010c140f07020d02040f0c02010b03060c031603020403060f060602010b04090b160c020d24 75
    0x800456520200a081071091040c05800b00d45001028802c139a00714103408110f8840c03543d6140d00030b40d45c500038401c00300180408400402d00900c11884800c0103601039550038140100c4500d11041c0b8919100c020084101d40301105149458640364000200100400140c44180500500c40c4052103020104e2545282c00820100c104070f8100c003010302900081d0008007590380003201013521800c084020341500c00821081109034401d4014501c0c00a264000d0120021841c1e0a860100821400080707102c1c05000b0040c8110107135002d4204140028280440401c964010408446d524072102c0304990b1914030660516409028405401606074020b003001d00c1c4c9901500f900e03000142600b00084010ba1810410900c2601038030043e580041040100c0043c542c2004000c0004c0c1c41120095400e1000e40c0f1401e242a1003810002c54000c08a00c00c2c40c0e0300c1003c2440a000c09509405c20b001e040c0317a2000150303c070380c001000402c0c0700d0001c12b000c2c41c030300601145010002c120146e0741d40b8282 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495421241 1250 495419991 495420007
    0x905040b12121c050c04050a0801020c1b040216060510140d0209060d1a041403030403140307020106030c0e10080f0d0804240c08060402090d020d08040f06020303041106 74
    0xa940d040c204020303a542516a5109442004045140f50303203aa500c604002c280b1070b849080c44000d1081b681c0484a0155041d500c006480c00d034000c1c650000300c81c0c2c000300b0445c510403680100c1d000d04140c1c0200010710703000714500d149240f110500c1c0182c0d0641d5803803041025a802114401001d841c51003900d540004145001609045411707074001c0c025410700f000f242c03080e16510498241c60b6400b006c0040016110710107121140303403c99003030b180d01d030220714840304c410808000c9902454142d40d03034801c10001403101c8845580007624170030031596103010000100b40e4054400c400341c049945854021f080c40c648411040c03400f0340004800340c0003801541d02c2c3c503800144000040391035080000141d1703294140310320130b5031403c0070700320360280d02d040c00c0140080c0a80c800c900c500c0003a15909c0b1252504410302080380141041c19810440c001d01c8280540380a06e804100325204403129464181c0f07a100782040c20b40b059000002503480402400100650403c4c41e0340c004206413480c900300b00036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495422491 1250 495421241 495421243
    0x30b0411032208030708090705180f0414030403050a120912140111030703140f010f03030810120507150c020f0402070516170709140f07020102070b070905040b12 71
    0x2510060641c1c0412003203005a4010001281c2c074140c00ca0300603510380c0741c800e80181001804803502d0840d4051500d0109092512121040c2d60141d44030301289280d0342d00900540c2c010028200f40ea64540481c01050150810001000a103106101401044030345103000c040300380d0300805100501004840900036024100c204038a0250000c5101e1805081100303418014000a00c1200080c1070000c20481c0c107a415401028614950000015141d5902c9111000d203460a000b10340b00008180e904101103842207100c20340254403d0340301c80396541e6840109065070b403020022034560f0010700c010010807603d80008a407031030b19410203840c2c12170305500051101c101568464400c0e540400c40001303001d010070401095440c14107100028a0b11054169810741c480c11041c050ba20071801c011808501602860000e04011417005106407a0140110036a0034000e00300d001b199402e10508010443c440d031810302030106a190303064420304010a00c41503600110000e402900c440e590300c0c0304204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495423741 1250 495422491 495422497
    0x61f1b0219170615013b13090302030d0c1e020d120b030a020d0f060501080c0f0d1505040503070b040c050108091902061803070306020d050f0907030b1306021207030b0411 75
    0x22007446c2205002600d2500c12a00031000084182582d0303400b1440800c5500d40580100802d104030b1300c100494501001e04000c0c1d0300a0940180107070414444040d6402040d041f603e0f000e40c50b814080a140151400c5441c0816500400e03c01039021103104e00425400c00740800c16400468809c6c091060b005010a503102103108009000c1c0b0380b00b485010070721061100d0660308a41c37180041c411135a50f03011881c0d6403d1148822485400b51261000d82c5140400356541d1440e4071065903403c1d400804990402844001c200303036020b0004005050001d100080305c14440d5100303c0a069185042400052104c2c0d4002e00e101415404400b05c0996a00704103404002240d048a9895480c1180e01c42200c460300303440920740d01813154103c04010049190060b11600b0340008040003107503510110490bd00c54159900740d40e50b08041010700210740640711242e4000000101500c103240e01e990351070105d034014901c106d0301521420078814041c1e403500a505035580112020322855009510500d5584 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495424991 1250 495423741 495423781
    0x1a09090f120a050408030304051b010507030e04090303330e010b0d1505130203060411070b0106081f1e0801051905090c060a0512061f1b02191706 64
    0x1d440410700b4602c2e280300d58110380103030100d070701601d4890620345000c0e40d0310410b074400c45210390070511109541c1d505c540700b0364501c2a05030783c4600707280000b0020b010003090421b60980416840e001c1032010b04190040710040d0480e081e24001c00c244d9582e40203c103444554009140c402e201c0c000420000840781c055071407509260200259000e80c0d04604c81801d012544860b81017501310340c55005814155020314410102940c05003c0c0c8440000380c280c00f442400707401002c03140b03400014012103100c0d840403603010015000c00a01550a804124260606d560090b00050066050a8009000100d5440003071109400078001c0d410820000211040f015a001025555410000b030120000300b283d4004804040c10003586d410154000030011750000452000400601c4c000c60484e040554828001d1920b41840c1c944081c1001d504a0303040c6440c0841c224000d0420f088800036036281165032982205009500c0343c207600c0c000540340c01590074001c8483c2904007400b0001481d4030501d2100c419 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495426241 1250 495424991 495425023
    0x607051905090f19080601060f02070f1508041a040b041a09100c0c0609080912030903060c090d0203160603110c070e1905102d030605090f011a09090f 66
    0x707081880c01300710414103075100e03882c01d206080002550b00d03004140101900325030303801d079003000c1d0b142d005590040300140300e580c000b58a200c09500d840761141c5100c6030403c0c410048a441148003070a1032510b81c6c4190380a039411004501800f08212204522400030700c0c00b00800c004a14000c01803c0d00c0d04140d440e035070707012030700d03188010007d900c42d02682c503034030b82e00074000c0000c032071142046000c0c2d030004008140a01c07540003286110290000a40d4404032004000340f01c903a403003804004141d000280d20720b0300000244136940050f902400100c08010449101c0c0b16102e1030818010207503980300c0d20000e500d5408002c854082c14002ca801800d4500d51100b2024984819404903031461044025600441c605030900c11140100001e403c1128001100015078142ca0700840d810840e2003100d40d006c01103901410400142d0303540003503034403001e0002946d000080607100142982c2e500c00e40506d440c44203089519842c0b602c1da0001360411003203001006541e00009200340c1c0c49010300c140601d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495427491 1250 495426241 495426259
    0x1314010807022113030f080a020f0303040c09021309020d0f051014060f21010807091103060904170c0c15030c0708090a03060c020609010c081012060902030607051905090f 75
    0x3141650080134000c542c058002e00100c4410b0620445039041020303040014020f4a040703894421001050768003c81c0c00643c0742503024079004801c0c0082d440480c40400814480c200021465224400342c02421100740020a541d00c4092030342d012183d000b0300340c1003d440d129100740860400300710103880e0030100352640c82d41e0300300e41c00540ca032500800d002081c00a89410a000c21400080c22032412507081e0f030211340c0083d4486050b0402e4030b003a00e4103200300301014800140e46181158040d90084c0c0126411070100d81d00004840c03040c0e00070251110700340c0c001ea80ca040700d4202100e0b8141c803128400101400e60a00429114451180041c064014030001c104414580d9070078080b80021644a80c08100000204c2030103500c40703804a8404800307500c0c110380c201170240038030281c0b481070f00750324040c1000608100300341da0b44014031001610721654502e00e1100580b0200040b60042000707071690380c3c881c1c030100c0104401c2d02c405640c03e000c10005005c1008180c80d00591545526000c80364011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495428741 1250 495427491 495427507
    0x916090e0a03050d02162306190b15180f06090609010c06020904051503060702070f0b0a05040b03090604140a110909010b0409060b2704140313140108070221 69
    0x406401b4850f45401c00c215440200c40400a019011000e42c006159800d2400443c0401c40c0352128421a01050360341400010844d80f507500340c0c000d0076901001021303034844005201080000350805150016211212251000700d40740c01048581307554021200715242410020110701ca41c01440549030610001c030000008002503501910310441002d0001c014902d042040300815401c00c1259038080e0141e2004288114400304040084e034a01d000072018051403d58040704c6540800c1001e003c01900740000310340e00c00c00c000154080c40300813000b016681410700b020030f0684020000e049081c0c1c003d819202c0040c4012201200c0c404007220304081c01d0365100400e50240c90b0b0050320580c014a840d500404103c441c0d80140301c16001502c401903044107200c0b004401030101841c442e40d110f140800038000a5a286440203415a00310036242456100c045406000c40300d600142007442c1c90000781095564000701030b81d8406010b10042c040c9210b141e4001402c03145da900400f031704840009101c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495429991 1250 495428741 495428767
    0x9042708130803161208150f04020c07080610060206041a131b0f1d0f1509040c06080c0a050304060b03210711040c021020030916090e0a0305 62
    0xc0e0042c042c400989585400202e48a2486094120704031130805104070a034481070302c0740840303510402400b40c41c401c18a40d1001048650394a40b1006644640c080101011910341402400f0040c040c0714000e0555080504801000c05515001803003107500100820000c2249407802602d05504001c12244588a246003d02e000500c4070014003007610805080a0420f10b405001040300d41030b510765610a6200d2180b40c04845413080c02010118080001c100c240042c4041c80c2c1c1c1101c6100c0340038201060000c08a00e1401d02102c051340c41c040c11020400000e41c1080201e5448401c49007520315213510400c0151403400302030005486660b4410a040c83c1d51070410580742141c142d0780725203c0c600d4810b2240c0c02d00f80c1c07004204840c01800ca207018815410140529030610109401801c41c12005066150040010000c03001d0102d107a800980103000408004501501c102030281c207404041c1c3e40105200007080d482036405501e0810300e8a400c00c030100d00780020650620f00340b559054844140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495431241 1250 495429991 495430027
    0x140103030f02161401020c0301290a0306050f04050c04091a27010e07080705151c061d070e03071203020c03060c1e0703050702090702010f0f0209042708 67
    0x103c25041c0500b800710301184000440b802182099080740c00f030b0941c0c0400d1600743c1d080c8040c40480d6145504080c0e00000721003030f01c4403c08501030902004140d070381d2112802c0d107a056403030b10850b00414040c042400001d1202c0442007000fa40d042c4041008d5595803486642e100c03c80790a88006100825001c20320144c680c1100c10110ba0078510401800450034028542490480f1141c41007500000e40c203c4041284000c0b181c005005402e034011003485603ca590010b05500003581030b444100180c0e400c107201d43c60107084105140301d410400c0214131105454064580424031590403003441c1940e4000845200b560400a605840d1003c01d140c1a46040d01e50300940d94140154000c21642170448000381070350114003800108011071010181c11584038070880907000031000c104000150806a90040e00082c0da440006034154401445c181100d4440760f1031540d0f181c001840c43d10503e0540030364649601c2184102c030301c4000d030008650181c040d600009044031404240b00948080104003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495432491 1250 495431241 495431263
    0x90914160507051b0a0602070b090105090303070606180b031c050f09121623010302090a0e040c0f0906081009051203010303020601031a0108100e01020913091401140103030f02 77
    0x4a5103130004070102041da607681c40d16694051035074000005100307071001501e0700031034071280d10740b41c80c0c0380040e001182c02c0e0303020780345164051100304240d000007000c40c45050020800c004414112200507a5440c007600c113001038582c400d178090f201d1007500102c21600b910200100b070500c00c0da9500e50902c40722090141c04503095020141040d4000c600e10007142c44000b01030300300c0c03466140302e4403480c114444038091080d09100c07014441c00d0100365402070b0300030100003000501031b05030070342d55100204d8a070000b11021146658000343c10010640340400d0400542400002802820700b030200c4260788940302654030303400c992140c081109208003408100b000c18683c5a0700e90341c80d84c480c00e000e940c9040a04c01141e011038002c0c0982c2c1040703852200d06040e140560050b0251001183c101000b4003403816851038655420403072310030140e41d400c45414208000640100380c100702801d1400803801c002028440d40d9041030443c680010032410000c2c19a589410b00c800103208103182280b40a107013400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495433741 1250 495432491 495432493
    0xc150601030f110d050c040f0b09042c0d030c1b080c0307030503162307051612060609270302150a0207020405070f0f20030d060609091416050705 64
    0x2030640542c074984001010300c4d0181c40da050002d6180c2c48086500c40c8143d10a604010303007803000c24071183e85100d0050071400401400402c0005508054821132000c140c1e90920581c482c02c400c0103a950103210b111010704080c00c04004038001030f00c5c007078641c48156002c400c1a0805038030794000c01c18443d05a88450920408480e19600f5038a405401d03070b032090f50041c0d10000086001419240708080301808a101d030350002048501100444145400c03240301183ca83c0140340665094801c0700011500802400d801541e9503074060504104441058011210403420700c58450400b2440e60f080c4180202c000030320700c00070092410300320300341203142164180411270b01003400500401a0007030200b4230b00807941008a41c840800aa40c20098540484049540c410140c200346000e0b0041e4180210384440b810004800c0e000801c0c1590312100310090010380e611420f000c07081d03101105d00040e01111a04101e000c1d0b4459132907420140003000c11400e4400c10300c078400d415100308159118503030304c40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495434991 1250 495433741 495433751
    0x13090c0303030507170403090e040f0501150f08010203090309060a0507150603060b0418020f030109020901090e0f0304030305040b09010c0f05010615140306040c1403070201020414060c150601030f 86
    0x40750040c040c0c041920070300e0000300020070080c1c040740f8143c0d241d80140e80c1900da0b1220355281052400d22104003d109803428070f5020481030104500f030040c00180c940610b175520203d4284081c002040ba99500140c400b07070b10510400c43c01520000c110780800c0070072034800ba19520405411159886900002022108400c44a02d00382c0c03817603000316058902c0b660044c01060b04103c240401c5805003c1e0051003c030048048030090b05183e200e4042040b40a0004980703002c460f0040340300013000382c1c045e4146503601c401381ea021540910400d000c0300c1070072001e50315061564038010800d006600580402080000d840c2059a00540303030070801e1076008006a0b20f20341f860402600900c041e100e000050211100541c0c00544500c9000d0401004804450b0031070b103a40090000601d84a91035105002004022600d103041a80155110707011b44d07800582d40e42d040054880441d05082d4025014141c207003c00700742071074045004107441e19070100503581c698814004901500103042480e4490b8580 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495436241 1250 495434991 495434993
    0x1b1312021f0810060c080901080a0b030307030c0203190804060513050d080d060902040612050903091c12050a0804140115350706050d151410091413090c03 68
    0x108910a40742c20550315020f0ba03507100141e038825203204000381104804c005040c11980900340c0703650407900c001313400500f4810040110780b844c1c1c4141429030216106040e19002c52404008141140075560940455100305503120700140c0a907003d02c4090000c0401c54402841c03002d0402001090002c045010041c404c3c103152940354401085044428140580458540c505008590480741c1587d6a011141e82c0e614900008081c040c00e9001180410058407085580b4070301c4042802514982c8400030301d0192070000c9041c04810390f14814400140840e0024682104803558001d402015541310b1601071004a80100201e0424440c000e00130240426146044012102940c3c00c840c205101d042076840e401075014100804c0c03442c035070b0190009212851240b0701401f0312996030300d80414070709650007000f500484136410460164008482e1050581b522015850800072035080c400321513810009c510710745000721041039001d0540000d030780204105503403140d115583c0000c0c0b252141781d12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495437491 1250 495436241 495436247
    0x90c070f030519090501020c1201060906091b080c0703110a02032505030c0d0f02150d0b01090504050601090e0c1204051507020d0c0b10080102030405061b1312021f 72
    0x84880080b070b07003c0e204500c01d181d402030303c01034150b84058008006202c2e10344c0c100308809104078001142035481d2080012071200724080c08000d070618507008038030100000451034050103049042c10801c004241400b064140c44000c03115641c0e05407600341c080301c03110f045251800d1040301d0300a40612605001c804502c41d4070020100d41101d80c0b0070752409550b60400c1503650420001d50a601070741800b20480016802039030f0452403131000e040040110b0305c0d5a0351020f41e4006000a2001c01e1702c0d585041503e690029100c000341004032010007080c141000028003014242c06829a0501c440021442001800e400e0300c103148240074a0198030325091500b5626a0404804551f10101100100d0406400802d004040b4100c6075200c2c007008159071241451140007409400740155038910102d12400700f80011407046000c3d030000c200c0341c288609070303580200d200110751032034400610000103d20b00b0420050210f90000c1a0501c01d41000e00000c3c20001503564030407030300b0000c0e078810814550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495438741 1250 495437491 495437497
    0x9060c0a02090105010e181b0304050709050f0c03060f03122205010503010305060a05060a12080304021005030c07020609031212070e0a18021b0304060e2706090c070f0305 75
    0x1c426510080203999030310055580494013014594045840c030302c1582d0000542ca54558040701420f100d503110301c0d81036900c90380d681c82604e0a032001d0b0480342086c4102c04640c020640c100340c0949500c02140381c824034000b90307400080c0c401031143c0c0064104001954042000c018807010140b00145d4641466400b0302e040d05040e07003602c0c64190b03074080003d490360040c1d007a41d042300e070044d02803d0b03e0f503a400741207802403c00a1501d41e0000c0c106c000411421040300030900e01c1d03842500025541d04103401040260400c500012003045410030800c03109034088029140c080b50305070740558840841100090600540d03601040482001080e11191841d0309a440741c050072880e1200380f0b071401580140400d850301030080016084d050014a091b9619541c010451900e81c0c5000c03844c0740400b40115801d503401580580d002480c1c1c40c04066141c542821002881031140d1100d000e03142c82c1074502800c05400074440741c41180e040c0c0019400d90700b0b003822107404540c00060704150540c14940580960 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495439991 1250 495438741 495438743
    0x309050f10090b06040b1c05010e030a0c0318060912030333061106040308040305070506010902040510170a0528050f0601020d0c02091003060f0605030c090714090609060c0a 76
    0x10383d8000800c1c3c180c1024420351110300009400080c1800078018440c50001884004071069035a40c00c148900c00300500240400b2050b03941e82c0141461b503070800070021410000c1c1d00b44023002c0030108002817a0808643c000f200c000c02035240c0f40c00c2c0a8102030700103080c240d007026480e42589402c4900c100034260ba94250000c82c415591805456174002c981c21654032400c821168070210104010a00441c4c2c1c0c1c60b0f002c0d21034070b8010719210942d610142881e80c03c0e03100c507090703d401140600007440d005548010f11003c900e815a4440c0c0222446400d103840601940078256807807010401c180b000300000e9044444c01d46401114080650f0031300c0052030120703051803203014100c01080541d88041440c1402940964940c1600d1105408000d11548040d02141b11982c41c1c1d1000000a40f40d4003a400351814904d81c00104146400141070a062041414a00c20110201080011500b2910384c030121200b80341d101751103140b0940843c0662041084030750b48004040303440300704000c00140c1c4030200b03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495441241 1250 495439991 495440003
    0x140a02040303090812070609020f10080109050105181618060809010c030902030a20040f0b03160b0f0906090612040309080106050a210f0812070203030c09010309050f1009 75
    0x35581d81c0a031316102c031005c0207580030850382041001c000c117034240c0001e80c006000a081c0d02c051502800080c0c01a56100d10741408034800744010010f520702c40c402c590041c00d060307454821035507098518440542d0002c0a05542000b040e03803d0448920441320038050440c80720101c240e003520303100c01130f01ca408102c450b080c2d90740c28042c40000040c072034019440c40d5540034000300b000f003490341e03070f0101e8005201c5401c5600c260703008a8000340741d589001d024520b4803602800100d02c40c4000070f250514005008405d40c9a4406d4010408800000115032699030b61000060700c500c5444000740c2c00c1d206500142c1ea0200d030200700702d11220141110340d40a50311170f4403218000d0b50344800349400e960b424401d0075849003042504014010304035419540c4075008901800340407980c2d66800158901500003a40c450748003081c0740b040d1140c03940e245900b003201c40c0000c41c1145008140d41c0342c170388100282c3e02c3c1010b0301d814800f810480d08201201c0c40c91444002c0e504400885420710004004424041c6d0301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495442491 1250 495441241 495441257
    0x123120906062e2d02010509030310050d110d03030507030e0d050a0c020a0b0c010b03060a0203010806010b09061e090102160305060606070807080c01023f0a140a02040303 75
    0x1d510700840041c180c0a0000401014403582c5045014469904944001400381d0703000413041003262140d0705209482d4080390301c2d02000f01154001d003143c0d030041480480398010010b0080705100768030351401f140c20032550741690350301c40c2c07810351310782c01400c0e0311541c1254014004404068150300314038420007895800300203030418560b01c5039542100d010b0400102e001003148091462081e8600c0301881c0c0054280c0306440d690702c0e490310060340f219482c030091ba55100b40428061406000854004003501425400c0d9410300d01c2c60380e220714061003038001c2c1e50300001e0f00845a03100c01054a03124210f01c403c1081200d003c020300c4074640c4c008405503006008041c4034480030074401040da400e89411400400c4581d49120904c119607102810075105180300f480007400048030741d07004110700601d640016031200783c54401041c294003a00280c0341c1d5042c80304000c221420000c44291011100b050141103a0340f0740000a100409500002c080c01c0449001004404135840d0020400c0324807964035009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495443741 1250 495442491 495442501
    0x30c0b03090a060926121501031808071703090c040c14030f0f01050402180f03150a020904050a090222020d0903090f061e1404050603011805070807020c0123120906 72
    0x85c04e807080d019596075002c0c44a021601101c000105801c00520605001810345020074a2040082c40b030f042c21510b00100140d4201041040c00360064096a07000f4010300b5400c0009002ea207070022241540c1c0035583c0e42040403500341c4104a50301003005c0c0c0d0309419580341414040424400c50454203440c4002110000141c1e5091074400c8414200c00121098045000c03007081240c030364120950345070315200300d0940042c550f5903480f44078081e010800e00160703101c00d810180070030307644010420b840c00d6103082c40041c096107409061184000c00c80c0c003100080740130320744004028012074010800781868581c0760000c242d0050f04990542e032040070110303642070b51403c048034400c2c07000342c140005848911304c00000900620f0b4882d4103c0302c0702c90f42070a19032110085020703134000340d2041e031040d000304079074035203000b4140f10300340e0045d00c546000d010500d00800b01030741d100d102161450401004082014090b92100b80e1101340141541031a59036841044007201e5001e0284c59185c854014180459 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495444991 1250 495443741 495443813
    0x51e01021e07060e0307091d06060409080a030203070c0b0702030909100f0605130b0f04090e07030c12050708010e0a020307120b010504111e040816030c0b03090a0609 73
    0x1d66801414010201181070a10446030507081c28095034152241c0d01d40440d9144060140000310000750795074080c100a2100030a2a004001d020381c1e02503460030010f5000f0407140e02c2141c0388042d080c200560391f500d50100c200e820048140f0045c201003440d4042c8034035603901100034001807104851940fa40d4841c200141d11102c0d051240c1070881041071000c00103540582c01401e1092405043e0070348180ea106100712840c0c2c8410040c4e29000400181844490300602ca80312220562100070081c0e0b40c15070381caa211481a5009058144011800c40010088200202009445810028062224402e503019070302e44101c00124480c0c0624000807446102d0480c590156070b400039001c5c009a40f070b00e01444003c12090a80040340e0703108220a20034000d02c042c90580610000303d50903942d514181c505070528944030448040e1020906c0100046100081c2e54410b5582c0803200c0c6660b0744405100b18a080c6202a0041005050401c0c800034000c0f0360a0901d03100d2000e0000080e42003c5203030325 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495446241 1250 495444991 495445033
    0x61d1f02010c05090307030609080c1605121c08061201090503070c2108161202070305010614090103110102071509091503031e02071a21070c030509030304051e0102 72
    0x40340d0540c6c4000c00800c0132071510f4010141700e50040e6011440c210f504040c080c2480b4401c00b0b01e03400d11500d450100541e080000840308019101005030a0250311403040a600300b1580000c00d0411a641c808162540d940a2503250740c1512075008120050740e91038203035140e8004a00a45044226110014101c072403004050311440300c448032011612042d58540b1282d8200d0006488012100d0b170f503000015070b4100c40081e01180b81d80080007040c2c41c500e001d03800d441c4076410070300703040742701400500c0c2d140c803055507190550394080b080000700080709004030300e481040e6201c0071007901102402040250802405002e44105010078003810007541500c42c6d5040345484010001000303020464071140e880c1712a05407200c0c003441036917a02956412015013409440c00c0c1303010f583e400000d500314242c58881e40d1414000031003900044a10b01000301030a6040b803080081c007801800540f19945640a00486010304402004040002d207181000c0c84103081c1d60403454094410b01840d209080110054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495447491 1250 495446241 495446257
    0x3031a01021501090513020d15050a06080a0b06060f030f190506060a0309062d1805071a0d0906060302040b19261b01021c0504061d1f02010c05 63
    0x2c541043c0d103000e000400900f00203214101c496914100070300147e0700c40015107003c80c0100450040e0210564421040b944041c02e0b444469291110400240201068003102c19420a581ca42d480d5100c0d070103d8080c8c4201c04001004503000402c000c98034400d140d8482c091008900700316000086c0ca0385001c221a0240c601541c855420701041d01d00602c00d4210000142c82000041100000d001010300c2104070209144000305401c0c03590b000c042c03007a120b4410090108a44d1360302000490310b503503231600901d000d41007026400c01c000301d0950200004407007a07050304000410071160b040c10070300010315041c00b0480c460b0b41044410365461600040c90000d004004481140711072526044a070380c0702958000c804901c070030004040300706806203d0000c051310f0b5030700d0801012815034002801d01d480b5461805000311440b0081854603403243c240c5003514901c2c03c09644241c00e004043c050315003485003131a481003204c0710100c410030030420b4804020300c00e03030028840340c0001c860070780340b500805070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495448741 1250 495447491 495447523
    0x3131d070c0b01050d08091320070c050108090f070f15020c01020c060a1809050a152709080d0e0609070b07020d060b09090c010e01260408130303031a0102 68
    0x14400b1703251000c808008140302d58074240c50700c642840454128802410282c08480d40c580c00e5101c80040c4900c46c501c05841d4100c81d81c03400c4800c0d0b640c0b8130800011701900d41040706000001e04c001404002d29214540c0c040101c0b48490390703030301d00200c0c40c5040e070040c070300405a2140040542c5000190315400000c1c141c0283c002d5880314024000640c0042c0412020440040401211980d503a03900c40c01034541c50f400866a0f1900b0808070054445040104c1a01064242c0401480c401101d800401402c03130501c0314480d011807050040035140c0d01d20054100c000010700c1e00c0c001d880d03d0740b12280910941050b55140e45d5400c18960b201c00e0b00c2d21034a0507d480030040c160040c5000860140428071400c400141700000a021030348619044601c82c0540e031016800104660b04010f006203031140929216400003100c03c480c0300c2036a10700ca140d003c10601c0034041410402580140c446a200c003400da105c0302980ca090080282c9007400700405007002c0d2209100465202241402c601c80800f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495449991 1250 495448741 495448763
    0x309210a0b060102071d040614060102100917160b07030b03120d0f020a020d0306080304031a06030a0203190b15011e0c02040f02040e060a032303131d070c 68
    0xa201c80411801c000c12480c1103019100e0081030220181034050916000e44030501c25a1626141441c1255400ca039182a1902d140b400c000f0b05a0f40020b03400000078102c40302180180182c502503051055100f4124000d00d00440d56050f0b203030346a456261003030f00030243d90049440384038007a0200da240c2c80040b5016008101c00f00e0241210000511013403140900010302e0305900100340c4202d070031140b964801a000f00d0310002c0310b40c3c0e1600400001d007402002441c40d280c42c46e079130b0b48500d504c0039000c000d03d07801d442d000030920765042c8000034806401070181c41c0c01c2c00301e243c0e4080503031088120854207080f42d40d000c10701c480d441541d500110001038540080898107080a9800030f049900010b041144420744d183c01600c650203120044a1f501401580701c0b8180040e818400d4402012540030700c5200c2410408107a0102004402c3c0c016903043e40240c092000c1028118400d1036103100000c8144c140c00103031031101d94001c030610001510b5140807929144021100f4905c0c01c0f1010b44034058907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495451241 1250 495449991 495449993
    0x2123061c030c0204050c0304051501051c060f0504080c070602060906070503180a1a01080303041104020904060e01080715110d0e010c1a070905060c0703120e0306090309210a 76
    0x9480910386550107410110308008040d4000707000e9820803070b504e001903c004000e210400c5801c000d0f80f0f100784100150f02e040ea40c18040890302c02e1400006044070a942d901d010000d000d0309910801c00d0562201e01404039181a080c00c440645c04101026030920480400040c1544045100c9010781001005030503191204401254241c0000e428490800e010700700072404100100144901244200315103a00356014400c0c081e58280141d1100115400c10001c000001e007040442c7c8031800d0301241c00584500300c00012a00030101500283e82600c0124000f0941000007d080000c4030032041d51614409028032003105c0d9a884e17514200c609a216800c19150140100102440c6403010f01d801c0303400d41420740760002030742d65141d0040100005402071150150340040e400016100684e6a90b103424020202d456441d461840060b003400011203a04035440c2c442c05424044e54001021111207003401c0000c9502d0741d1214001502c207407884910b1289030901c801c0420411421500075100314152 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495452491 1250 495451241 495451279
    0xe011215030b04051f0504020f01090b2215030b091303080114061216021b01020a030305060a050a06020f010b010318020f120105150901080303010b19212306 69
    0x8090710132191809801c0b80a41000c0100d83c00118180607184041124101030040c41640349548000d0350400404000c140142c880c03940481d042000f0b0710a007114104a54181c009802d0b010386c00840c1d41380c0c0c03403040112443d60305030009400a10103c5031000d80d40c4807981020301c001e042c4500180405c1c0700b0703001085009411000035203100009400301b850320410504a004001c002c55008602002c000d50a44041d541003240f80a02d13008201e035000084c0400300040d642d900d0081e8000c08040d151800508103842e06a00500244000b42c032a100c0030380c4540d40a9100c14414a0003078447d8030307001e40300c141580703c1d001c2d0f102112a4100c81040310b00b141d40901ca4891040b20710150092400110490228401d105030b910a0326410034010400c11110700700a200719042c0d0040200e40d00920040c00001d1a1070203c54007218000d00f00080c0c0300c91040305079455000d00d0b028070035190201c98115803c541540189400301003a41e0007404069a400706007143c40be00750b8020341c00c06401c41c2c442d080b5802c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495453741 1250 495452491 495452513
    0xa0b12071101090c0b0d0c08010503060c070c08070e010612091e030c0c09020903070b0712030e070801110a0905030a050a03030209040b060f0a030b0d030f05280e01121503 75
    0x100700d0001107040481511a0300720b1008a500840e081c600008001c103e00e6171500c14600035040324501040a54903020000c1e643da030018041c52880d004c0000c283c001c100051400000501d007041c180e83c1000e698a030301c404840c000744100800301d01a103420a8203a00d9611030740030059803050703003a564102c00c0e070720001500103546c01c11424032401c44e03a83c0000c40d0042d490580240000c010160ba40d498400c241802d04c00c1652015601e050140a40c50004504e030030103038030401f03c40c03034005804078589801d1481c0504550040c61315520b400c80340c0c0041c0365180002c03c4081c40b00c0d200c0000c410303a03500501d6551820f040024115410840107480060322a400030104200000c00c0443c0d400340d400005281c6911801050401c450001408130b85c041c0c040c0621012510222030011580030300d078602410742c4038956161800c200d030010707480502000c50f6120b030440300d0351480e0042602c0c6e00c1c07140190105100503100707404284c00740b040c00d1007480e0381c1c01071010369501c84a50401062559581044000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495454991 1250 495453741 495453767
    0x723121c0f091206090203070b040303052215030902030d09080d140d060608150f0d15090c030f030e091b0d091e110301060608061c0b150a0b1207 64
    0x10348040000f4400a030464903801040c02641c0014013083c607441050701e031001d25841000740940074002000800d40107415219075203442112030034540100b401c40740700440c07990084010101c1c00e9140c18200b55150380402c481c0761094086404c02003d400d02600c0c851413600c5034150b254051440d56484600c01c54100c003100d8030500d012818050070000f51403d80b0a145c10040000b040d007800c0003d0409c3c20222901909001d440035a15200100d010800f01c05400201408021034079115040841040e400303510a140c01500e8400206d031a464003c0290240c0e0384160001100706072084118035214034003034000d68000c00401c004141c22032116246070010319032210040e95844c2e036540401d000950416409580310401c1c0941d65180ca0150b0202c11080c070464002d81c5451014418244c10101d40d40c0c00ca6812554813207640c48450001c5c80240360348900500c0301154406111240100c00000025084110b850078245c82e252409108031780942e010903003002482201003074000d40a50f4000401d9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495456241 1250 495454991 495454997
    0x80a02090601121b020a1707110910031a06030c12070501031802191a040305070501140c070e0610080f06120f121e0306090402120723121c0f 62
    0x444c00640030b42e01c903050360711034005078200c0c040250030441f4152013640102565007655040100c1a2150404068000a943c0c007504441012661110f03d18030f40710000c640c010415100e403c4003030f005203041542078400030700a1007444603910203450103071103003590110814001c02c44145010011005403001c10441d201c0030218074052000350701c60182c1c0799544d4803085c40c989141450690031495160711010302c1d041c044000d010a0000a6000c10808210348003442c106005040c2125040710600c07519140840d244038140000415040500c40c951049004803011000840140700540b030600d4121000b100c2c54203203000040300c9140208804400c1d07294001124030384180301c9441440c4c090388a00c42c0c00c2c1d220001c00d0341c2440c036400e01140381240c0b42c4c80348101d0960034010042009946c1c0604000c0c41580071401003d0009402c001c418002c0801c03c1c0d0040e040e011170030032800c0800380c071a0304e14010100843c000ca1007040008920aa001201b0388202c0c0b06040044101d5001039100075007410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495457491 1250 495456241 495456251
    0xf081902040c050f0d1a0a080d030c05160c181503080f09061621020d0e011107060503010e01090e0304030b10090903020f012a05070f05060f04050106080a0209060112 73
    0x958000c400540402e603c40e44001814260841c141c44460610900162203080087d00c240302c00d0348003091038031364400a420041810306e10314900f0b03102802010700f140d240c0152020307000140a004411201140da500d0024100040700d03010210640359401020f0445140000b0b0410001d10300d20300508441240c4080107040207504d07000594203a200100d0000f45006c400d0b0010148015203001e0340d0141311303d00304405034941d01d09001c1c4d150307508010000280507048000944590050740c00030140d200c7c40d000d0742d480545400018125810030300451356600c602000101b0b540040f0b2140c42c000c501c1d008000c1d41401d10310303070741d8080100c0300074800402c03074040640c000b40e203c500d03000b001e4101c0c2c42034004c0d00d035001500003a40c0c02c41301407440c0c200410b042e501c4210491034940d01c00c9688013a86280c825a541e0407424044091030200000a00398815542001f41d00c071200c48000b03004034491030080c42195a5000c82e41d0b56030030001c90107980800c4110104030a07602444000714004080340300400c2e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495458741 1250 495457491 495457507
    0x901080c070f05070807090c0c0b25020d0e060f09150405030105040b0a0b0109050108060112200c1002090f120c0d11010e04050c07030507050708070b040f081902040c05 74
    0x400b003041d86108603043d034454203045c019100140250b170013518480d642000040d0200000403d07d000d800409080c2c0951403001c00c500f1411151800068a01c2c070741078001803440c0307001c020340d1031f11a450030000080700594907000c1440c00d00215042d0300c402070101d60500f001101040484003c801c1c1a0044802c104000201600c080c040c0901c2140100c1c0d25081d00d1820842070070584400d03e084c981002252001071185a800144264000d5020310300180c0e60b0148130520002416a804411a06080102c05420008005000b00340343d41d2214191500c1e40c010030400310a900a103018030f5445180400c4d1112241020081001140880f00840d03170f00c0780c20a0086551f4095074070060b651242a15501e003050b50f00401c40711510f000a6074104002d00d03196500d081140540c5c035004040100006031502400010008980603002000a541141d95140c400a20031b80c4a0301c0780c40c2508010010000d1000000300d404410300b011105103400f00ca11503800c2100416400f07001509103d018041b6903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495459991 1250 495458741 495458753
    0x10e1c050906070611120f13060e0f0102070f0507050603090601061b021002150903040302030703060515150909010b040e0403201b090f090a0b0703060302090705030a060504050c0901080c07 83
    0x80d81c140c0701c401703202d9550303040840300c2e80018100900e45034050070200184014803548040208025402c10300000302031400c1807005051001e5103005800c1036002183c1041030115080c01c211100d44241e00300c41029a45e070043c0000b5000813500e181c050341181004000043c01040040c9590694410300421030099500040070000406d0a480c016400002e8225801f40b00714a0540c0201c00d0100540c141440c50f800207130b4508043c080200b54640b02c0d0049041611101c010380480318004110010103101c540c0100040d40110344030038230445280300000b42500e14001144c064480d4208184c03010307502c5403400d0302c2c890003a107c40101c03580c14a107000800041840320040060101c024040c1d07201e29a01001280280a0300c0c102d181c0210030103000a0010001d001c3c4001ea0744140b00c5c060b6507580b43c006034000c04407a400030790000c149404020030070b913004004510030415403000f0040152182c003444100c0744103e5801004010802c024900340d17004a07080c0ea40f14240411a80c503050613503031030f1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 495461241 1250 495459991 495460001
    0x2010c150509100b0a1e05040e030307021002071707030210060801060501170c1c0e03040311040c0e030705061309090804030c0605180607020612070809010e1c0509060706 75
    0x44544295284180461900b05003c00540c186050506000c59645000003a034807900c140300764001800d10002c02c0c41050504801c0c41c0060100500c1041190700824403181c90780d008590780001802510700e2a1501000b500c2500c0c003454214466580020120740105480c1e840080c0a40c20340c401d2031a0b040343c0103e00c2c0a1807000e000114004900c181c034080014010319003104040314071000f000300700000c1345001c0050f60308090b802140c0c1a11100442c40290007480e40944021550000003000300c01e00c41104e501c00e017410400d45040006206588044801c2c1c441c02d0700c280c0d4550040e040401c100c0c5450409020109924030041e28016502c0d0903440896414110445d5201d078040390410a2007007059070f8400600103402d246180680324141011843c00030310b805032140c1c4012a001c003c8d91550001d41d5001214184d89082c103040c0844007610584048031116525800e02e28104800c0380c0208030001e40c1010112001403510400e942625260484007001c0d0b0045028495207010543c64096 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 495462491 1250 495461241 495461273
    0x80c16050715030905030d0b0105040b04030308011a0a140d2310061404030204180609241109060c010e030403030518010c0201051602030c0409050606040e061303030902010c 76
    0x30001d0300d2030220750514050810030703540c00341480c081001d40820750100c12200161f01c0c00c0000540242c060b070040c0c0d22070007107420842c8141c50115001c020103802080003816202142d125005550905e0080605407080049685c0024280c06491011914035809490f080800e0302000c81c80300c4040f41d0110740011a05440d010701030b868414002c1c09801d84203c4c0c0b000c0d040d00d1070a9158000b260514041d140b00b540f1000f8080c954031603100303c02d002086103400c40284d00c0b80062000c0d8040d0b04100e400080c1c1c011074810035403005801d03205203c0180c403400b500844221519030a01303584004019003074100084080d5155200c00384034241050074001880a14420388031540ca43c400c030400400301480a01240c0e050040745116080942e0308182682c005c1d00c04000300303124242503880403c1c1001a09a02c0341c4d04542003040301402c01c40f001c87d00c0d621a900945040104120b03011009030b03601400d036003494611000c00740160200b407090704100122801810414240811030f40ea8400c1a0b1800e01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 495463741 1250 495462491 495462493
    0x100e0c0405061c0317060a06170a0f02030a02030a0f020a0e061605070e150a030f0605070e09091b0906090c0313020907050d18050601170a06060306060f060915080c1605 74
    0x50500d520f05c85000703404e0b4119005407000340940f4100500035000d83c000c8001010040d5120b000580104055000b4210060050f0425902c0742044400c0601940090b1480d51005080c42c256100b48034161080d15080421503545038111040081172040540c0071105040c140300500d10700d2404191708001c8040104882090303400186048c400082502d104019250301c1001c4120041000c5601880d00a5105410240000b040d486400d400c0d1000043c4807141e640045815041010420020034002c10101c4540742c0034031044003850030450f40c40c0d012244180d2092402d004902c4102800e00903650088008074504040c0c40c036a00017444130030301203c2400015500240c8411500d030760b40a180080e10340c054080003125425a1401d071603500c14012803800401e011040004114200080c0704183d422102c02c01c81b51340c903400e2643c058003d50007041c10402d180d40b000074089100310b85640c106e030b1041451703485450414004030303440e00c0d018001c1c3c4403540d01849031084a000034001b54800d144124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 495464991 1250 495463741 495463757
    0xa0512040302120601150f02030c0d020709060b190f0c1703010f1d0a020c0a080d06080c0102031c051017060a0e01140a0b0102120d05010602100e0c0405061c03 70
    0x4810403c10740b00010002ca8a508a03200400c040d528a88000e01040000d050458800e0040c0b4000c078a54050041288440e02c03400c00355080458011a401d000d5a030160000d01400391034002a059500c5500c5c0c0314403280407122100001c052050b40d0064030102c2510703110550245940720700035003a031030144040002c88004010000354030501500c1e40144400040c5090340c030101c019074100b511009200d2210143c00003503000a28200b0f1201050441d030000c0310544845002d51508001c01050180281d680306206450543d0f40c0000150b85070840260700841c001c0d41405a04405440c0190641580d820080c0001c1400f243d0707503042d5140e019101004001d98604602c001c1e0a5424030341d540455640f6001e504070034441603450581d80044010008140d040c034000040f4a000c107512080800d010000c244c0d004041c2040d0041412140e250303003107031002c51800d103820742201d90000c09900181e1041c0814001c50415401c100d9214400800003019440340f00000030700c8105624003140081e5001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 495466241 1250 495464991 495464993
    0x6080c120f0a0e10051e040803040308040507090f0504020a14130e011b0f030c1409120a230c0f1813080c0120070209070804110415150f020303070f020a05120403 71
    0x608080c9002d21211134a402d25401c182e16100d4441c03000ad403014081100b520b0006061210800a08005000d1036100700480341d09112002e00404081d5003c900c1081004000107083c0e003e003007481c130219402000c1d5003c1007036001d21a4020a00444040c04954031100403074016144051401385a004503101e204140403880c0004040350f400d802120705000c0000455105042000140c41000d04140d030050740107600320510500d803100b004001060000030091074003e040d0b580d0302084400d103d100c1140c45824041c030401012948041c48550403c0341c4062608020000c54043d139001040c600d40b0b041420084c1e00c0b008466800360004003079aa440f400100b1029410415a8503412400151030b82808460303800181c1340280505188100002d1002103020300851481081c40514018030030400f1800c07a80c90880401c03000d20501200980d9218010506401420030b110280002da02951070340c0d68422003540c0610816845d1000c507c1004403440c00913804010102108039102c804584891075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 495467491 1250 495466241 495466261
    0x203060c0901120509071203090506031305060c0316030216020306010b031e040f02040506012a03030606181707051305010e100f05061608070c06080c120f0a0e1005 72
    0x71080b210003a546084e04000c0c1807400400c038141500c8403400c2000c401606820f04031400e13503441c3c00c100ea02801c000280050a14586e20303c40f101c1c0d200b9416940241e49540c1825a80d020403220420070111000100140c8e034401c0e4020090700c1c521440c4030101c562550082071078500240c1000f050f08400000703000a40540c01d14814a1050160100c40d00c0c0c5841d0381d59180304500140024021600c440203c2c20983c0178144069034040e81882d41ca0100c00100fa4940f845040040c050300420700d4040c010580c2c81c4204070050030360031505400e0704498545102c2010303a6180c890304000390f025540010425507600c011180c0e216580c2c00e0b01040fa94103101c1ca02440140281501c800c0c0249000c0400a40e0b00f00c0f102c0e1002c440e07048a1294a03070340201c014080f03643e041980142071150000e043d0307042114241d4514240c41d5039546048450340c601441400d607124983e020140300041e1000908c0c09890350340910392040d44040003092084118031307000c0c0781086500d80310314420381340d801700544404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 495468741 1250 495467491 495467507
    0x801180203011a1507080919030308070f081501050d0231060914030307060c050a080609130602160804030302070623040b090f0307091a1503180a0203060c0901 70
    0x4507580607032072288050f400141408880148282c1800011030104280000f01065501001c00074084000d101c000f081940c1181c00903000403404198440d010070041d91040c40d2a140740c40c501e86507480552a2150400c148540c0b07001d100341001010001b680d03081d0b07114009000d21045095842203c9900044408d002c6600c0c04910032080150800c100201076102c280c100c103d80a40d0303134204003c1c1042c800b282c154469450064805814100004038003544a001014146800d0ba0703002c030702d0344945003000881c1c0307000d40e09104040300f0810600003041c8541d00408503481c5100000e600500280e445005039040390303105601580100b44100841500080c07a00544150700192072400e950b4a20310010500590003603200742c0c64045034040d60340e102e6145080000754002c040b030300500d40d40e0001c440909400c0c1c0c8a03d051074901418041c56080500c1031251144002d4000c9040d5587c0034200c04603000000d000004901c00e60000340c0240c0c805005003800b61510101d0255190000b1002501901c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 495469991 1250 495468741 495468761
    0x403020a0902090102030901200d0801031a0103080906090112090c03020a0e070c120507021201060602010f02160222020f0702041a0904120504080708060105010e090118090606080118020301 83
    0x1e8010003012505a90100c2103c202100c00d08081d0300d8070031200d006200b1154803501c2003425101d924803082c0c0d900c3d00035000c00d0403248981c1310b004c4501603c884200c81c28100b8400140182c0d01402140140d01d064006401c0701401890984400e0050b0007400c010380c0c20080d4251040c07415150140294208038410a014054810411419040495004010a03078420020300050300b204074403d1124451001c82e06080e07002401c80d801b4050b00c044160091502d8800c21000d50301e02000082030700301e140259020b5400501a41088a109800340060900039445200c0180034800c405009488184060060b003030081030304c9502c0d1065881400119420f2042d01c0060100140f0f0010702c958a40c5286e81c1e10aa00c134452500c58500ca020569084c0207a402c41511070282d404081540341e400a40301741215026030300c54408407045c4081c040100000e001e24880168800402c0059051640020340450321070000080c420b0742c1c0708016821580d0b28681c0c1000c0c0c0e4240341515003940742c00d0080c40030328 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 495471241 1250 495469991 495470009
    0xf111f0605031501090c03060e150109080d121104120b0106020c010503010e070c020f04020703030515041b0f0207030807050604110618010c02061b03030702010c02070e0c0913060603020403020a 85
    0x203585a003d10000f5440148611904103407244403001c04d01e48207030090340040180c5075910340141400301c117030050141c0042c000d90010304280070005028400244020210140d40c0b1101851950707202d018002e054003504001110b081004002002c1c0c0781d1648000415006a011000550400600038140032542d006941000300920040c0002d4007914100c1d908104030b4180340b0780b00031641c8042105580d060021503441880440c400b800d15406401580c0304284500d00944e00c503aa59013000b0071070306000300c080703030010b40f408100d2403150007101e554001006e0b41c012120016941e660324180c5503c00304040314283c00c0799041c041000100c0c0082d1a040300c0480c0c2c0300d8107128040c80c81c01c1c1c404280402c45170401c04246000c0303040d51205011100c00c8030001550350701264000b05000e580f42c0c010341d1603100540ca881c045041c020700c0450f265080d01c0c4468600e40c800d0f1111004400d80740c221a0009600051071707424020910640d104141c0201550380b000768503586140100000031003a94004100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 495472491 1250 495471241 495471253
    0x3060b0405010905010804060609060b1201050402210c04050927120d0216140a03020d02030703082d09010b03010b091323190c1d070f111f060503 64
    0x21982c0c22001034804e0380c3d070a00c0c00d1201e590300d904018015081c658440000145040000315607204188001d11485003101301c2d501d0643d82c0c9009209c200c1c819504da654265a42c0084041d29810340c0e5052038100c408080403504068030b6200041e14864241c42e0012041c426480e41c008140035842440440c4070000e01401d101580f1700c01406140c0b040c00c407416a2a540041c0eaa07081c05654114540d201c0c0d044142c000c0c82242e01641c05030f0390031594405801512a414140c0c403400d10000803a001c60b941a40e410f030740d170340302d50041641c402441541c0704c4282860a0010011020644420384540c20b500c1c00805c49031200001c1c9030845a0207428035000301a9101000180200000903089156002e11015194508058140c106008500d100b4502c1e0046c0414400c06015402440301c03a580180400f10340156035010b4030007209803502d101c5a4900c41c51000681c41c6004a100320046649824000c07815000080d00c10301b01a9007c0c14800c1902c00d901c1c0a01c00c0c003c0900c56080600016002040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 495473741 1250 495472491 495472499
    0x2090f040b07031104030804030809031e0a1707120f0801060201090b0f0402030312040f0b0f04120c1b0608090f06090717010b041109040b090601050f07020f030610030303060b04 78
    0x141c00d04014079070028140c441d801c075080e1007440340403500110341141080703482e25200d20b41110302e54002032005200340308015000102d0442424611007000c210f00040072070b5181d40d52a400c880d02c83c0e00307402d90404000d115250100e007041200414010041c0e803a804440031103000a061400c1c1038200c60308583c0352604001c0021aa201d00c2904042100050303501917656200007840c5210300000c0c441041014800d02041010b4010b2003800e65126659001543d03950703a240030424075007250701070a10800c1044841001d40031b40c2c040d2101c1401041c4040d200e00c0305100244890300298000400149400c0411025840a01003103900941c040042c003024202008075507514209405101e40754200801004144902503010806030348004e07005101c24543c18440f64056041100f03278500035030800c102410a41341c00c2107041d2042c00161202400c0001c1d010707004481da088050102d801008114010480340e030704000152203003a40c01c10800c41d11382107250050030b03a003169002a041c00b000f840140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 495474991 1250 495473741 495473753
    0x11401050a031a060c0d080703020a08061306030c060507061103040c030834111f031d1e190201090902030703020d1e061d0604181502040302090f04 65
    0x1c0c5040c5103a14010403160a0b000c0520420340c000c018083d0300400c001901d550840002c121940707511041d0b100e502d99a95840380070b400ba48140c0c002e900024510b80700242c0d1620304014800c004600c8034000142c515100d82d1040460681074004101081e0302154200801215004000c0d1020b030111000e410340c201503495811000081c00010407103280401c4211040e001e66948214400e0994400324a10702c50f40014188070396448000c0d50510303800b01c074682050a01480c14001d10400c5201c1d1020b40714000801c50003051050b0400509039101840700160300e404002d440b50b6544261001d0640d0100303002d101d0318200342c01016160500581c403018000d40c0e0403da602d01180e054000142c0d403035403001400c50082c4150142101028544092815a140c48480a8055556a981c20001941c640c0342401d0480c0a10428030501216000003030300390700b070039084035902ca860141c8032a030b58595680c1d44042e480034461000740450380410204107501d410305040390400b04000308405581002d403030300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 495476241 1250 495474991 495474997
    0xf0e06040c050c06070c15021e030c161101090806010b0d0f0207060e0a02040e0102090d021c0803130b42060c010204090b0a0b0a031127010801140105 66
    0x11620a5a4400e00c0001e810b00800840d180c400c008016140c0c6450625405880020002401d03510162200c017018981701441c8215080500c980504000444651030064250b50004200514840062000d1004071500c0001824001e10450072102c401e020740b4001804001c051b80507040700d0b404034004110fa80103400843d080c0c403d84c0200403444448404050000e440f030103000034030061504011010ba00300100d152001c0b03600c01c880c00c1c4400c4403021802820f074040c00140580c4001e0803041c04005103843c008134a00c84148400c51840c420300c4d510384074925081181e990101c81742d05100c44040000340300100342d0110612191212209000020345c00c0480b5441245214900081c030580406050300d040104501000704070301e50b00c0040060050207500144590050303035040440800c02850300500c060252000101c40d075040c10700801085000e85260307a4081022041041400c0d015040fa86514400303607100c3d00e4840741c1203000400101440416130021802c280c08510582081ea030020031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 495477491 1250 495476241 495476251
    0x90b0109020304031e020619051509060312030c030411030703030507330b01080a0c02060c0708040b0a360902071109070908060106140f0a120f0b04060f0e 68
    0x30058803079441c0d00e400c0d901650210b0740520700040504c00c0100301c0d5400280301d4402c0c0c000800d410301056119400304182d03002503898000c0c800e000050b500b0709041c00800d45034800d000908682000e00075001188880c2e10541f400c1d485081c0000402c01488138100c40700505110940041c00c1b40f902d143ca0046c95030140f9440244002c21070000c003465102c0c540d80c03d000b500f41040c0c100741c040d40303690356500091903111121800b2404050004881c4d050130b00c5a640c05e99040d0b00904050baa94000c1c2d40200c5d80509022192180140401724400c04002c1c0500b101f03002d1621028092200700340108908429414130403090101c0d080f02c130714042d24100c007d030b04660b000c8401580f144c1180ca00020403144840c90a50880050020400b030070344c1c031640707080071250b807031003a40e5450362628001c4940c43c4003041a04048802003003207507980800720006010f034034141d140c081040e4080e550740200f5100c41101e0f40109546034038203912a441c01e8400c00c00100010321400b070000c0e28290402008000c002c6c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 495478741 1250 495477491 495477509
    0x70617060d1401060803041703030603030703180e01030321020a0905060c0304050301050a1a1014030604110705070311011b0f0302011805030c060105090c1912020403030503010503010e01090b01 85
    0x401c881000090000c2910700c0450000038403055450b4103916959801c944500c5044107401008452860000710440e40140c43c050059803800700903403000e0b81c0e103030070700c5401075465664424001121810311fa000c50185205c0c0e0794490050028800e07480c00c2c150a0b050a0304001d01c1000001d5401e0b03000b041710790458809507100b0351110100c810450860046030311064055082c0030130004007000c1640306131300b1444000300d0382c01000d43c51801d0050600002d406440451b07400103900c041c9807840000703150f012000410228100c41c0c20b41e058501900200d5040b00c06a00c884c40038001c000280c031200740b0b858020700e04003a626494a065111845032848060b00c002070801124050510030740011035000310b030403441c84600605260240c0d5a5114100883c1680910740c00070442d490302c5150030b80901e05440403541482211000c1c010104c4140c0100018004441c900300c03080006400a0b1000b10b0103502d4241d00c80d0b240c10213140c25141014842c0300c05074503100b481000142100e07034803419100811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 495479991 1250 495478741 495478759
    0x3020a170603120c0109020307170a0b0c0d020f2107020705040f0e0708071404050c030a020a020a02190f080f060403050d0609140405011a1e0d0218060307061706 71
    0xd020a0600e5110780c400d00d01c41d03500043e0420420f03415041b40f5031702031080d400c0f41c4240740e03508040d000d11004110140b082d5003204d80b1800126400c0718407241c0002103684114074180b17400b0050803c9a010708030320842d210303001ca007480101144002030902d96202061030055440c0882000b529540359008051069541e800440e08642c0c03070b40d00c540c03030b40280c003002c0f10f03003542e1036546569461050b0701c986803c03201e040d281101e0700d060a014050146013003001c01c0b8116201c07912680003942020000340210321410611344c01680e1402c0100301c1040015080507107460410798007948407030003608030301c1e40785d4003110b8060310341c5c240011202d038015054503240d5124480b100d200300c0a01513036403002c90800d0500520180e130490288002c1d000d9442070707000b0010a001c0300ca4100040030300007441c3d940600c20240f414800040d1224150b02403e0051404440e0b0f5000c1e40054082002c00110001e401100d80802485013002c104e030078094105428a0420905548064100c1080c014031300d902a102030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 495481241 1250 495479991 495480001
    0x11401090f0b1c0c0f080304090b130507031a0411030c07021c030801090c0c030f0302090604030c09020307020f060925090518010f06060801050913020904051c03020a17 74
    0x5520116804030028048000c4020111106400c600051001c1d5a0b0b001404e030005961401c813078900c4116030700a4083d50400d46440c801c01c0042c5581c190440d0030081064040008409500c0f545100701c9450b140022880c25120103080c0c007038503400c1c03c00c1c099807800d40c3c0648488a0102525440141c2150303003036884220f403000c0345c1040401c2c4c2d0604c02c1c01c0d4141205400301038010007440d040e142c01c03c0041040151000c0c08442c080490003014001c00c42800005460501c0f0b03400030020103c001e07110501c5e040c2d882d83c0381030180807580c0c0f003a0450f5501105000c04554103119150050b61818000d000314241410362a0312450008141d9070301c0e000c940d003442105041c100c4881b008007600181040280341440386210750030805640300d05107501e088420041c54025220390015540780d95511103a60b0b007040f080c00031400c400303030207100803030010183ca1006030ba81c0307411140b00c1e920030380140030b08400040581440340e03404000b01082c1801407069541040d840020031a2590b990800e440c225114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 495482491 1250 495481241 495481271
    0xa02090c04030f03030b100309021804050106120303140f071e09150c0201020f0d020703060e0709150303080a061802030619141f0918020d09060c030e01140109 70
    0x941c2c1e00041680240c1c00d5203006054041e481019060001d645040c400d81d10070400300d048461104000f03520011499135610380c51500c10342e9552003403081c40002900c3da1110785000b0541c43c0c0410440009880b40608101e144225038181d0300322002071500345050600c401d024100030422110038032400400c00e030201c180d074412043d213802058408070180c04020000310007444151054404e0b405440f43e12410000c3c5600026609400c2e845d41c0d02401400d421070707903600050280750480f0350052040c48404901c070b0301c16204202e04490b482001c8440300d0310350300d0301801e858001000c11012a00d030650030014040c02e0443c0c0010400703810340040e0341e43e5800001420070190b00c0c16010720403240400104001d000301c0004003a0318411600065400c0c000c0300d08009400b107074484400000c002160401038540200175410a1f4a52641302508142d0524003120498a0142d025140c5589803200000819010322489201e00202d4000780315000c0d81030900c0f07108403018410000481d80c2e421003802c00d000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 495483741 1250 495482491 495482497
    0xf0b07110d14160506031306110d0203070801080a021f0314040506011805190504050f06070e040615080609070c06050c071e0c050d0c0b03100819050a02090c 69
    0x2801403002158103194102020580301c00185030b591849900315a4000104240d002022140c0081003103185607103900d00ca001c40785100e1806c554003500d840854800d10420b501038179000e030b030022006840e803800340001848414181c0c000600781d0061180c560140e01e425240d2201114210340d031001c4403400c82c0b0704500a25031442403119049038482070004004020501c14121407001500014140e070a5458900300e031419500407140549088903440c801440d90050b540c0310b800f4000f90f038444510001443c0c2001e20032144040010381402100b80070f45010b00c90040900003008840c1c82c21111820050551203000e44281e1046100a0000f46810301c1605030720301141c0e00c52018021800c2020200c51142c103c920100c680e00d0210740c1d580ba8240c8000800302c8085d07004080d56881300d2030300b000c2c00703104008a0001e4a060032000c80201e40f03009188001c5025403401069060114501552181400001d0401e460035451148844d008187c001450010071501100d100030103490300c0d070f01c4801a00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 495484991 1250 495483741 495483773
    0x60106031d010207050a11040b090103380402093306040f030606210b0a02030417220f06050906090607170a08090a02010c0b090a140718060f0b07 64
    0xb600000d420000c202001c2181510340b80300d803403001605540101000b003912000c0c0c040d95081b10704500100086101c0c607400e07010722845640c410002d203451403400d9003444a52a150000c0c40401d000740021414254a0b050b404207640324241c8a911080c1c07600b01c0c44c0014610082d50503244100401440e58545046800825840080c6401c803070307607071030500041c1246100c0d18421800152440b0700708070a40410f0812240d002c1c1c1c3c0c0c14815134840c01d00000035000a4025910001901018402d01903614020700390074207a1a20f1034031300000780000e92044a41d9401061441c100200204040798102c0d003600c078420411107100d52118000e0001c01d41e14040e040010348407016200c001c0e0400e54040001704860542950b8100345039454220706503640040d078000900140180601c0b6000c0365002c8030454000700c603403094440510f00d50325036200c040d442d6254240c445d00419020003003001403841034155910701e00c40a010a6203400040140e03500307513119003c03a0f2440042c401042040311040d0365046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 495486241 1250 495484991 495484993
    0x2011d010e0f0303010303171315020403050c1822120f021b090708060607120f0e0405040c120203120d20070c05060f0409050a140f09060106031d 64
    0x40481188064003810038800a81158098403a100b4545032020003200c0c1603a405450700040445090021801c65200405c0c41c2c01130304000351590001100168070001800801c0030250312070b41181442c03410300c410a00c4403031252002c104400c501100613080130b68040741d281c44900144400941e02c501000440100405401104da0088034840d0812580464403500798201e07081c680441c110803100e43c00c911942644000c07618009400244170302480c90740000040d20050418101d59219521011200005000310702c8180d000b01c0c005c2e6218100350b8510804403024402428a81c48480c45160140a0500e81c840380748032400543d182000f004504da051170a00b280e403401c1c14070141000384000d00d101580c120710b45034000e40c450030210a80b04a00d4000d502660918a000100f000951004403202e49407007040c00001038038800383c850035108401d452000318540d0044211005a5a801405030b4480031024087c03106d094170014001e03043d20341604000501d0416036035a41d404804281c00c040031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 495487491 1250 495486241 495486281
    0x9150c030906240518010b0d0b0d0302010f0c030b090609090a020306090c010f0305220309050409050303041511030c0c0a0c180c05030727030605040f1709090a0b010201 74
    0x4203484a41c0c8100d400e400b1003e200a10135200e00800c128148203068010303d0002c824010710180142d20002d0040610540f000a10541c0d10b802040d0034a80204c410340150755030b41114283e1a0047c029101e6450492030200b220120035400654994009407240f405441d00310000750098100300704d01d0000b04c1d0010125505490701824844c0d03120800d4500c60b00250011019082081c0240a46401850901aa000281c002041080410031208020340c10094007000003c1c0035201e0307108807400c49005e070303001c0c654a1501d0b04080032405100320004154900d40440c1280007044281030b00d80109411060355030b0303030b942c500d1403510300075041c0300180c045a00b148000070080c5504070280368528032241c042c0b1015050030b80644090204a46810210710400c2040e5144000c0c80b2a11074404503c01c01d04100700d031603880305000c4840489003264026405c45e0b0f000284810390713000481811704070340e01d2442c1206030000320b100408060b04c0055201e403107540300c10030f9078000c2d0030000c51400c82c40d003800d0f9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 495488741 1250 495487491 495487511
    0x3050d0f1107110904020108010303081905090d110a030e010f030209150d0c110721060501090203041506052101091202030a09080f07032402070303061401020109150c030906 76
    0x1407594001881102d15062441c0405258103002400c0c5200d03a80503119001c2d942c0ca035803425600038030010040b8030003066003454a103200c7c0c114842c45004491100042024080100014100c1d140b20300b401013117903204100c0100040e52111404403610030078646403041014292040d0042d0040000055016205076241d40c000b415a1014050241c2e044405000701700d0201d10644a48100001498031030300284410b12049040881c03424036541e000c445d40070f03000022f0f03d40c00c048940070b0704140b09454001080c03205000e61000784684444c4500010848640f44c04001213074009480550315a00c0d400c1c4602d500c4400b130030360006e20f105401060500b40c603441d02d00029202d900c6440c0300b2002c150644070110f41c3d00700000b215204043c942c0000d0111034110703110740e142764a050820550316507020310a40c0d074803400760001c6d0003000e1090303c001c644642008145081c03040550742c00c2d070442e807505204c0c40115510525102d12840309540001b50b061018a080f00549800e41c0080c4c4200c0c1401c0203d0703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 495489991 1250 495488741 495488771
    0xa050a11100b0f06030610030b13050901060303080c0f0409090c030b04050718230c040302030f03040510170a0b01030b27060f1018050901030f03020f0609030703050d0f 74
    0x84482c0d102107410012044420080001c6070000380c40c2c0940040d07400801c081481d001c0d500c0000320943c0181419407000085070b4034825207a00b00e0305086265120801007040640003d15241c018400b281103909001e00c03a40300380601e0140d40325510701140c8441c0600d0502503001d103460059600302030608224541400c180e03a507001030b44180519000045054542000e1501c9101d440d0f4082114840c50a03240e00760410304110080d01082aa00c0d04110002c010380c6d0030029a44a6000500559241c2e0b15020810208800210f05001888182d4901c061f00d160b503a030545512450001c0006000c1e07000c0401280180b00403010326800030001d403040e40c500410510b0420051040140c3c2d04810360300c80f000e1000140e40722144540000b1410f0a13980f015000c1c03803a0140400b4056420032200341c1e500c00007000040203900c151001003408070760f031090550501151415420030303802402c41d41040713000940d880c4a900b00c00340c204400811300c441005540e40045a1048500a091000d115030705090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 495491241 1250 495489991 495490001
    0x7120339080604060b16020a080d0c1203061214100204080c041512020904060e15060f0307030507051e060310050111012007060f09030f0f0908030a050a1110 69
    0x2a03020864100028580b4074180c065001560f040d080c0642c2442484100720100704840c000403a842820700c0c1000c9038021040040445103402c82d5101103203104941420645182c098015204050800c6d0046c4611120400165802076200c030310403185151601d685400d2118601001c0c4140d8000100010400390004141d00045030031a010031500055160082070043c03548590b80174410140060400b61500c0e40642ea4040e002e00b001141c01810500c00b80d05150340c0311454a207010903d41402010f0402d0701d2100300e0070700b09500400c035450941e120607030f40e28585d2054612540f0b2a80f0640c4080c0140700702c0361115003015000c50340381d080910066000c0c401c83c0c084d580c001110081e0814100300c1c14000c1d40c0c0b640342c000040005403e5142e40781c500503170007000c0035960940c40f019010342022440c40ce2000301c80c080d680d0080700c0d07000d0250041005907514044400c11260700c5081c0711036440817040f960368410b50701340981d891094620503155403032315521482d000d028906900c15806200e400c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 495492491 1250 495491241 495491351
    0xe0402070204061e06030e0c01111005010f1403030c1b180c070b0c1606020a36090e03030f06030a0c0603020414090106050a0c0510060b070c0803071203 67
    0x601d040d139940303c040071000c0320744062132001c00303070b00070300081e801e55020b64001e0680340306102c00e075082030000d00940300a6820aa0041c00c18140ca900c0400c046080305a41f18020003045010b9494541840040e5a8804d480d20352600e8203007441001281c03c0d0740705528180d141100362002c00203458401007419140d001076070103442031444400003449901c10041103c2800d900030545c161440c0e0716846a00081d00406004018806902c02c40704255100d0007800301041c0505001c104080d10320760301c88001401685c4118006030600e040c2c8080030601009883c0d12004414800e03240e030381c807900000d1903c1071661019010100415000c2091985a0018401d59000b2040400d417009042d00340200064248900350024105110000b041803048002d01c00c03035801501110a4501c0b01c0848604560a5611141d0318210000c1c41f41d00300860a17480500038503090000c3c5003040341640315140050400c280640405580d550345020140c26008400c0d07102d00107500c2c00004a5038503440360503084181e14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 495493741 1250 495492491 495492539
    0x8061e1207050316051e030102040f0e0a0e01060b0708070c0f0e0f0108150f090c03120c0709020909010b070305070506070f1d031b040e03070b01030c061107060e040207020406 77
    0x20321306807002d45a9a0100884002a01040c01001d250541c3c2404100c40240c007981075408100004494100c0710a48026015280719080142084803900085402c0503c40b003a20f80d04200080100c00340100540788041d801020041d620105450300801142c00b9802c2808103c0300c2542c081403c084003400d2500c10108003102c601c00c0e0343c940d082280d484141c0c040e803076107070850800007401003100c0954407604201000d08540c1810230950000c6d04120071080016511003012606a03144001041074030020160604c046107481c01c000d02041c0e0410050043e00b0204400103071001c1014410400c0b00e00043d0402c05648550800c6035000704020000c692180014008890900d0038134450310b00c4d00c1500310b0080081c040c0000103a0b101d04400c2580c0320242d8025900c0f10060a0014144010903204d48500e100c0d02c96076056240140d044507098201d0f004000b440c04000800c120001040c10940e070703290a000d8419001c0b0300001e8041d115201009401600780400018460038103000c014021010031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 495494991 1250 495493741 495493753
    0x411040303090f0806070f1803210801080a0f021302030a0b04062103030c09030506011502010c02030c070509102d05060903030909061c051c0302090108061e12070503 73
    0x40c10f5160305034038070301410a01c0e030841c2e0702103440c45025400a44140d1a5810424061803480d030741103038500041d600a403007001e09918080d00051a03100d5810460565007042a095410310344169610050100c00900340290810a501903640315540c850001007100000d650f41d20b800005a00600003940080b801913061002c0031511044041c00000d143d00f5a600351000704007141c808030043c001c20390082052050060001c00898801d02426001c1c1080d4071154485250500c00242120b640c45810411504207024030458004013180440031190b0840700c070080703526225403d004803c400d52140c01400e600594014020652550b11101c80c075169400d8141155134006101403842200d81844c0d041d001040076084500c1c10204190b04041b024048061166030b40382d8000340c0780c10200f0244c0e800d51150f030b0201c00d0103d0798000a405042e07180740079070406100200180c4072140c09060716209000b02070b95041001a04000740c0c0e100c6c60010201d040ca682940503032601d906003030040350302a01940c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 495496241 1250 495494991 495494999
    0x151302010306051203030f0402060c1e0d1806140405090103440c031603020708060903120403031a130c120504170c240108100504050c01140405041104030309 69
    0x4c0042c0d0032203000443d01940c910b40d52141c04c40c08944000703100f2a40030f401404141c0d0701b864101308454050442100d001030625800e2081850048a5116541000701401c031a0804c070740301c00441c600b00d4051b403c0854904900c049591043d0295070003460f001038003100004148482c80e06000c5e031010340268020014081c8040c41e01415a10b001981d021480b818500420495100000d281303040c2e2180960b401d2103401380c2c8184a002a010303041c1d0050340108401d20001505000080e003140c0900029450601c1d04d00000d442c0482c0284041c05043d0303110700d00390a504505425240c420710040a415a10381c402045900601071081715800040307400c003005181181902c2524003590b00f1055100d9141c1c130842440c9031541c8001154402c500403001c044000701130811002ea420f06060720010110340c1460706440c40c010344602c1d0050b00302d05100600000c203901141c03501d034a52003032031720405404846640400310310030360b402a500285020790041c11002c00a010b00103882c401e90310244c2c06950b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 495497491 1250 495496241 495496249
    0x2d2a0610061805220e07032307050306070807030b0312030703060519120c0b040e0411090f0402040b011103070614130c0b13090c030608010c181715130201030605 71
    0x80742c000e0b15042044500e00030961810303440c2c4004520708004c4089881c08142c1c0b60681000d540d6072003200c581442200e00004800c803000c850b11070180803001023401514280000e03a0301e642c050004018444d042c0d001c22103103407180e0010400c40c0b00240844024401140c1e14a482e580120307a4040013910f04640401c003490640c0c40a01000300551a0342c8006042c158980122078082c101213441a440c0000054907282490290000303014440b8440458901410301034010304041034140e00c107105840411030001a5881c0003604103030140c03000180d107000c2d4070068a0043c20503102c1c1d82e00380700124400d010046a030304500c01e485450490b5404988030882d1926922400c008000c10040312801c0520038010310101500c20180d035048424079180e84c4244450890b50035101181c0000c1c0c60740d4060110328003d0203a259500820301d410101e000c07001a6940243c103142c080c0c8010200c440360300d206c842e142040001c48144081c00503001d2404c04440c038409c1041c1d2503800300c0c04641840000070740c601d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 495498741 1250 495497491 495497537
    0x40e1608090f2104051504030c0609032120061f180203070207030606081b0f0310020d09060501170d05180d02010c06020c032d2a061006 60
    0x24a410040c083c400c500c96496542c00b003944600301c2d641c3c00900001482e680d030320552402090f0790100045d5101e0843c2070004081e0200e0300182c4c00d111414000b00300140600f044901184cc40c6101d0080022001c04121f407011010a0381440382d0300119030300d051601010074603070300a2207107008a454800c80b05000400c010a0351044040707944e00040c401c0407030040c0e50000c1d54084603a20544603003580702d80c0c0c0c400460300c29030401140b540c08000100c0382034044500400c908107048910701ca072100d40400181e07440080f02d06403507005030082114401104c540d00545007403903018400b48810b41c0c40380c86c01c442c01e0104038031a0394a032041c0240b00040350702844c100d030400069044c0ca121841c004805110303100380414800c034100700480b0714580c041032640c400b5000c00e06890010b103545102c585842c0c60030a45402c2c0b000317440705420341d00302403006800040f522113113540c0010858901c155051280c440c9040c01701a0001e00801041180f43c1d02c40200c0c031815550355888050424003009a0544511 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 495499991 1250 495498741 495498763
    0x2d0b0307140108040f060b180f0a0b03071712030a020c070e070e0f030c0306010605340303091a0a050109050a02031b09030a0602040e0403200307020411040e160809 72
    0x80c40140480d0110725603042a0070700701d0180300702090070310030b4030007040540a0300c801c08d0955050100038040303150000d00210340c118001b070405010130700c61039000903240d803841d01c80c07404030034040c03020307480e6161080c0903529010701001d4405842c0e19255241a001e588040102c5100d402003460100320b0351b04d01031000e8045c2040359200701e2104e05440034015141c0400020315454480c0704042a110340c1c0820a00740038013220b0713039096100c0c40318603c80a020741d0203140c86030420558001c080309050f503103003104840d650145404116101103060940741d0070b0003402c0301400329100e80b08111250519800c524104e4241044c2000659036282c0403008a0100341c804050103a42e00c50b8145109894901914003139100800b0b44400205903070b91001203a21a0f0b01031440d180c4120b0400050607000300380482090840340e28000030414080c0c66589900c00e66000900c6183d860440d07000141e04207081e280500500659080300341040d080e0500e407414803e03411b1000401c03140002d52400e6009c00d02c0c0f9050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 495501241 1250 495499991 495499997
    0x1e05090d0903020f01120f0e010617030d05100b0703050702090f06030a06110906070b06090105040c0912150203090105040c09020405010504090b120a0b0a0507051c2d0b03071401 78
    0x1034210b41c04c02c4110130300c030114a81045030504003580d0a85991040203402103100900003009506015035500303441e9182d005446d8185084007140e5404004402c80b6801108a1000212652040ea46652000e20380e044142d54800c0402c02008254001e4028031400d8000c5626101a9464504d03507100074008580c042d8141c0c10071441c4100040564000034030968025041c58100040329001c503580381c10261040da0030320315020501c0f030942404030701035024010030340c2c003401140b8120f000031740588039512404e0b0600000704e05003400c2c4600c1802507180305205000030355881c03c00800f200d01810b0141c50541c0c54281c0300c81c00144100c60b0344200c4003100c1043e1a1141050f1420081d01c00030300b044075000d508140501d8050b5507861040c0309009c05188130302c44001c0075040508100b812281c005003c00d0900400f0007a1105400035103030f405060f105044001f1909a400f01c100781150480300d4000300245840315640d005420240d040203550160680448103c903559120103002003500786000c03408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 495502491 1250 495501241 495501257
    0x50d050a0218010815190e130803061c0c0f2d051903050d05030103200109030f061407081501050306091b162d020a271e05090d 56
    0x1155020301000741e0300000d640980c0c1c001005d8030010a10030a0740280d80f180706440c81d4800d0041501c01e88041d5000740c6030000ca5a1008030580e103180b0f06102c0900147e2241c0d018a240071070303882c8004078000c14a540108100c603242d68a01134110341c0c0303419001e06107250341d0403070b02d8549400e942c1384030110b80e84c11440024902482d080612030003c01000c0c004419600f46040800807034020843c0921103c180d9941c03655941c594102000d039118002a4190302c103c48000000a036a8091484c00903260442451502e43d581890880020000b0b0750b1401000a403000401007560740010b02107209a20368460400f500c501c00d40115603e05c0f08980c0c081e40041c04402003621402d01a8800d9961400360460fa49801c4084010300483c0c0c400d404100c03034420107290500c2d110000b861202000507040b241e1003502e82c40690004a00790102c5c010903211021109940c0070048143e959007a8401a138841001703070303410b085420134200340200280321070705041c100840c00003400012031000842207580c500d41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 495503597 1106 495502491 495502537
    0x30a1b0e100e040b06040b1801050a060c15090501060810091104020711220e06040506010f060c03030c12060b030f0a0612021201060f06050d050a02 65
    0x141c070301e0340d54040194401d4600d81542281c1d104080410301d41d01c1c0720105000700359050ba016400358032903841454110a129805041c3c60003560415195500da0400761200e10103800e004000303020710808a2050a02c96000843d080e1042c4000314815580d500500e2401031186d4546d90f5072907507180c07803030704010b4040f6080040c00b00a48081d418007200c4e0f119000b40041e15030b9214080c84500000090f045070110031980c1070484001c041140c0c2d50340780302032681e42c0800c4408a03458410000040790780d62817413060300200d8215550750360500740e80781c0d0210090102c0821000c10301504121121900b11039004410140c121645820780fa07103000c510301c0c2c98200000c0c01c290601c52610300140459400c0d807800c10f0400d501039640e001160300c4e0040352401800035074014042c8540154010682c00d030303c100282124411500240030302e4a034400444100e01ca800300f15201181d10000140c = true := by decide +kernel

theorem cover : BRFrame.Cov 495323741 495503597 := by
  have h0 := BRFrame.cov_init 495323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 495323741 ≤ n) (h2 : n < 495503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
