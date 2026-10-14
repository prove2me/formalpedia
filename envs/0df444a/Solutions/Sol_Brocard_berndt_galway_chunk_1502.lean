-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:17:18.418673+00:00
-- url     : https://prove2.me/submissions/39015fd5-7eb5-453a-abfc-0ab7c7aef35b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269964028 ≤ n < 270143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269965278 1250 269964028 269964043
    0x60309030f0201050f0a020a02010b0306010f0303110d17040807060c0306140303031e0702120d020d1103060a170c090906011706011d10050301291005030c0703051b0f 73
    0x802c40e0b141c4000c204107800f1401280b80c00020b00341c4016541c100040e400c078003408403402c54503010b100d110000149059000490004c490195450381a0411112807458031420495201c1d000503403649d001d00041107038101003d41151080f80c0d10381c034182c40c0c0d68450307060b40c0350f40c1500004207903103a004001d44d41c0040c042c2d00c0064000c4010754a140380c003c0c49410150071a0400600c5100c090f0000385030703039008010715248050010302064131861280480c0d0041e501c03030303001101164189410442c50010310310940c1d000b403100501c82041c082c01c3c912829070300702e41c4208071003003441074007000e0403e511a850154090910314000d01040d6041003c241c4280c00644d1008083d64044801040030100108139011000c0f101c0141181584801d10651100403054008a925510700300303601481c00e1001d0b045910031140412085a00b110060810040701e080103803202c04107200b0000100154030080051602904c05c0c10040c2c01c01804a004412012101c0c51003003245d440f04481050a081c02c000c8507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269966528 1250 269965278 269965307
    0xf07020106210303140c0301030303060b03040203030a0f050405040e060f09030306010c03031a12010203070809030a02032508120a0e0601060f0c020d060e0a0c05060403020604050616050706030903 86
    0x24004075190104a81e030005074541d514403200180e50207001054800d401104084902500b4071101d404c0040300311035650710a1008402291038518000340804005065901c80e540050240d4180862880c0a82e040c810703844010042200401010555942d00d01c101d02d042040c0360010080ca00d004d0041e110348140103007401945601c20700402c075941ea07201ca0a1020142d1519004c05c41810b450030320954580100e039000c1c2d12450448604d03910b860154061441001c00d80c0d170721002500c9840d816074403441059680720041e0402c1041c00d030190506c0c04c0303240c000c410a0017181400343c007a803034a11494200840c41046e00900e0300c240403c0c0308003405542c00c00002170000d41019450000e0150500c1c26049905043c4181c0c8151001950342c2e0450702c08940da00705609005109003856103030317110040840202c854442c001d40101b1903003007490585050b42c1d8003401c598503040c103003006c0004d540c204503440c0d245490300b28000c20000c0c1081c02241d0007080142c0700400c20b03614a00c1c02070001d00f28803145 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269967778 1250 269966528 269966531
    0x2040302030609070f15020304080a1203051503060a110f07050102121e040624030606080708150a0b030f031321020a0504050702160b0a0801060207061e110a0b0f070201 74
    0x180020350171400b01c402200c145080e400141e1031100c0f41a4110b00840c0d000d01c00340d01500f6100c00901c103240c1c000511541466404010540d01d0881289130200035152580d0164000d200003010307030015a204150f075019403041c8505050503103000c0320007688050300445469402168844010b09000201600216001501e454003161a191000f00010080010300101d440d48a00d02e10b4440c800c0c000700d120a1030b0b113801c0320f030b56440e81050000380c13180e8411001e061017511400691800041100f00c0500703400103c03250f0b10f45944125102500311200303011750500510200002002d41040101110301c090745207242802e140c010100d41405580f6520b000400d50517103504010f03510001520b05075503007101c000a05403141d0030b0803440e10101c561a48584104c5060104055461700d001d0710581a1603a2038030102d80e210700d0200e0b202c42c00362090002080d4003404004030690140307020b15281d100f52511000b848980d074022454808001000d40d80e42c2000000d200c5070400c45203040e640201d0380e000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269969028 1250 269967778 269967793
    0x7060905120a020d0602040b1306020f0d020a06050405030f07060501060909180b070302090303040e01090c23030a110a200c0f1302120103050f013b010f06080102040302030609 77
    0x4241e44990000400031300c284009020360f42044940d606603005000c1031001c0d00c0c0c030b44054400d07a82c00c5840900074100540300708000d03020004000142c400d42e11504e0ba0144c050451295106c5014040c003900494044c0414410310200b08a08005001d616000d194041880d515164018040e80f1280d080080e01c541008082920a0b11200110644a5105c9075556a80d900c0c02d508030000e028140c001c551601000400203001c801d2042c1c0141a0b0b407014004001c582c08088082d40c0c1d6104140342e14000d1001040c501c4801c00644010b540d102c100001e01140324400d41003c407446500401c4a08085039030750014103c0d1310103212501c00702507803403c001c02c0e05102c2100046c480c290381451240c0704030301c0d103402150006410340580c4c081d46148200f034019940c40b0310f406c98a07200010894803207903190656050a03030381c128440303504280c0603c00c0e84440c403562242c4842c0000c031038042c0324655902e80d01c040840c3c2640c0d1160030000d11000c400181c0f29815413041504000e00a0043c029a074090038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269970278 1250 269969028 269969059
    0x3010b0304031b060e030904050f01030b01030f060b030a060504050d17161202040303200102190503040503071a0118020c070605071a01180c03140a151707060905 71
    0x141103907000307a01400c00c5805520006510652155036000080c101810b00710400c102c0e060000113004c003000b0847c0c044c0f00719541d800441c14003100c2480080c1418031914010070200b81a00400000380d4041d4402040120810303022902c0c040e030907042292041c1e40e84007040305109091000d80c2101d100e070718200c40c4400981e0641800502c01424a140400b4050044c0700100d010340111003611544d500c0c1551030baa81e070f0901401c46600c1c04c41300c40901e80304030654410300c403040c400c540f41c6020410800b9801003081008507039030303000100111994070041220f500480c00d00903040200740101100d8001d5581043c0042240311a161180b004150060000305201070000c5240026513030b09140a985580490a1024100d80710300040501d42c1030403400481c0d0b2450070011808032881070842400740e4000c1100860485851903030405240120202003603680e40650040001c0c408022403680c060b94540b41248800008118005015441400c04120303042c0c110402000030102120700d02071004444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269971528 1250 269970278 269970299
    0x140313110402161101020a1403041502070f030305031519061e02070513060e07030605031c080f33090906060d08070305160305090f04180602030a0b0405160807050301 73
    0x1c000400075441d1070820b07000350740701f001040c90306500301111420070020511243e44990250050712140e2031001484032a0600000b911412141404409184189161421546904050100cac030400380841c5600c070041d500d00c01d01d07011100b09019940740701032409001500f03d551a0014110b60000324a8542009130041003260031a00c6c291805580507100c1000a0010319140d0400314079140c4500500c01141da155105200360b40c1c058040f5410481c009843d40c0d540541e1b1018400020f64100c0092040190151101d4000751242c00c60b4928400c4400300c1480c8443c490184141c1041001980540d072030100034803a0080c1c440030240800d0b04100020401c00c514030880a00450400035002c03041600c04c00403119a0701410b0742c0c0c1d8465800c20718008016a002203030701c0380304d001003071031540c000d14140c0b00d1655000f0031852030440c840c2c0103980d194042d401c001c04c0251000e684040700000c5807964059540f140014074cc105100e212603110140c068035000d05000c04101c4140700600c60320711034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269972778 1250 269971528 269971567
    0x40c11062503180501090b070f03091203020d1b0314010e060a0e1324050a14070c05010f05011e0e0103121d15040819050d050a140313110402 62
    0x149000f14032104a00e2a100181c501c43d400200130350303c1c001801c018000c00c2c00d041405400c0c240d9900c103071a00200c03022800e0700c030f42c2036015100010300d50300b04124501035801000c0c030307a44500001c5041c103601c441117940c1c1c2250344440c501003501e4007500c0a260114040c02400340120200000d0760f41400300118200e01e485009107c15210307240049140f1402c03e15803201c4003030780b09251110360601b868140710404a0381c450700101e01c8c00c00020980c1c81c1c0c4540654a04049041c040302040c0c0d13101142219882e4541e0340640c0d595583e0a81c240901c0340900410b07001e000c000c011001854808026540b4944407035100300d00320041e02d001440010010010201d82460700c2c500070720a1942d5911116004210b00c843c558007000441c02000c5000514000c0c1048400010aa88500700b00400c3c2c20b01c48142181e000f04240c006400c80f16241e4017480140c540c01100d40343c0900d4005818080c544598801e840740103400502c0340c080010409441151584454107071802d505081944040c2c51310303440c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269974028 1250 269972778 269972851
    0x1a0d0809040c11030403050309090903030402030a150608070b030402151303230109061a030a03050301180615020a02030106050a0e130501020c0a08040e07080f04060b03030405040c1106 81
    0x85a8900c11500b520a040c040708011401c02a40e541e15601d143c80c1b55254054a0150b010790054000074092481c0031090703d02c01c5402801900500f4959600c000c1044603400c2c48000d0b5540d0348070081903000d003c00c80395010305803c032a01c50f564285401000100000c034020070240e03102c100800b0511440450b40c60f011aa480140c0f442185000010440c0091881c421008258a054400001e210035a045014000e88040001940c880c0400c01d1588aa1032210003501040c42000108500d400f00c07240001c803601c08130400104103072108007105a02c0b640503201c20050b0b022020b054213610b820710554005190480302c817440180381004c02210721000914108101840030240c6040c00301c29011034442c081c1d000e064400c00340d07142c40c10301e0f142c0c0c00c540a000c035006841d1001500940c003c0b0066070080c0c24504040205a03a9607948001030030850304100e4250000740000142500d80f8021305030748185c15120900c4004a486001d403a10314005e14190700318484060042c6103002501c24a141e0782c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269975278 1250 269974028 269974031
    0x31b0f09050702190807141605010e1f050301090f05100b0702030f01111b0a03020a021c0f0309060e0a0320190b07050607030c02030a08040f020909011a0d080904 71
    0x81d03481600f81d08240c1213000b14070b25880fa03002d00b4010044184e00500c54a4480d0fa0415101800c441c1ca0300d644101c8080700207229482c01d00117220a43c003400c90542c1f50400100b4040340c04031284a1480d2041d12020710b0804500b002c00103222500007401407040345013803510b04100034070b040481450021020b22032142c0340c200c00940101591801d000480414660070024080c082c12118841c9265000c906ea4240b410340c0c0b07003004c103c15800481c0c030742c11241d0181d00402e02c507412a0200070307502180c4070368644844038180031031002610600465a12501a4556078203080c50024040d25061301d070719900d1711600c81c01100740001048040d0f04036079038514031410000f410b801008200a080c01400085007182c0b60080001c0140d0420010007080340b0034800e48401d07440f11070040c4e040d65005d800c0307000560024095200307c1d62054502680c801d0080344083d510400796004184000c5041c0d0310b11f200780e51640c445607140020190070880507034058980b03000b0001d45480c3d07030f840f0740a0607080c0c5100300d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269976528 1250 269975278 269975281
    0x130903020a022806091a210c1b0114010503010506030a0305031509090703020a0503060f0f2d060a050d02011e110304120302100e0a03200a0c031b0f0905 67
    0x100140140d0400d0320320006080e0a015881e40b0000d000d00b40c49124413683c0c4030000d00000440c0e10101d06461f800c0301c131101501e50424141d04007190300b10009100c2e0020103824410324154001c041054180c210b144000010384540682000340d0200c0d058001a0190b0705040a02c410754400045100301036405150060312a140d030150302c2450a5020920781e840080310f014450054404118031084034422200c14900704e41d40c0d02495181c0c0c2e0f08541c0d260748582c484000820801d03540c0d0202e0f50041001c0c1c84450180b190800486510025012028200300d80204208003801c14403914405003d007180c2404440050b42e000820103105841c11a54068005c0603003190703140155145d110005035002503d4807261201c880c0a800600032401381d00511512112100380b501074420602c004e41480302606560a0340d88040c0d0f800c5002d40a03210b0194040d448020714000140308103038180b8464803007aa0000d1075410103400303900721140054005800000c0030000c07541c450b00058110341c0303581000b1488d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269977778 1250 269976528 269976559
    0x105090f0f071101060b21070c140a0b2e151d09010803032509031e021c030e0f01050412140307031215030503090103200d0b130903020a02 61
    0x10f101411452a110b982000360200d9805010409440c00c140e07210101c0580c9588015084080c50303003540d0400220b00600450700200c0c40302c0144440280c00c060844040c44060780c0c981707031b00030303000c96603124649600350103180c0891040003181c04069148005042032070920b078070205a00c5000b0584402d0040c1d496841c003001c000c4222a0b00c2042008040040079070351043c1c459100d17842200d48941d1410380284900c0c0c403803442c60f5107929410150350742a24180c259070b50000c1c03000045403130002d80425998013100680d2801c0100140300300041001a040181e0303e0003030803400741c200c4c895104001d01c04240c2c046903841002c1d1800c03100d105c40003943e48002c50400303138408820080250100d020000300300090541245040d01c103602c410b003003000b0148440d101110104140e00004103960410440e0211561003600070010580c0c01c130350b20340b055542c26400c2002070b912410440e1461074171260445030900e815a0190944070000c042401440b00300d07900252140030000000f40715000c1800c0300d40300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269979028 1250 269977778 269977787
    0x12270203010f0203040303053709050f010518070f051503100b070602041d040317090309030a060b100c05070e130b090f0705030706050d0b04020c030d0902090105090f0f07 75
    0x4410b01028021591303801d15040040141a00311f5241555002c0302c1c030072404000c0c60421220035030104900c1d05442030905210103015016030078064449120785001b003640c3c130f0070a10841d4042d2581e10208450080000b0403241015074545c410840b410041c84100324588880d1310300311140c01d00265803035a81d6142c60b052444060946c114007180f00b008513002c42042210f82c014420b039289640003540e00c0205c5420b035041c080c070491700180000c1000c0d0028001a400e6072249400c00d800e603080d02c5c00c2c00d9020340841e251403280c0d4429038410f503d5558600c403a0078103244210501c486031610481c50000c07a102c90b59034400d41d20600d101c00075420005032104119071940160750382c0c00b03072304c0302868104500095902c403404944202c0c20b005022000881d4580055103004540d900d44560342480710901c841d40003018599207254104c2c2d008c00070b132071a1240030310041c100d40d0040312001030309030781c54014000c1e503900503004a8040d54810050241d026040200e0035408092400c0803c080e940d07400d41100d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269980278 1250 269979028 269979041
    0xd0201020124030606091820150304060507111c030906050c2703070e060607061506030c090506070b100305030a11010b0607030e0d0302010e060f0105011227020301 72
    0x768000d1000032440e00705504282c000300312405407605001d07494031411100100c40c68010307031b200310701289802ca500088004504403840300811158050321040b510105040002120100c220885d0010811040045a00c140b80c0c102005107480302440d4205c00c15039a80301801c205010301c000980d0b00b0f04407114441d802203600a0742c055014001800d040343c3d402c1d40350300004809680da1a9000204207000300520b20b252030303540f00034024140710b49041034011500c000904000d8100000f041120041003880c041c80482d03408000028440d94544100107040705d1211011400300201c0282c00c01050381d601d02521000340c0c21040b4081c1980b80c620714000400b03041d0b80010414000400c020720180d80100044030030005440091084810310340c100000307403140c1d61004004c510802c10201c0c0605010315083e50f00da11900001622010442c119880c000d4215408410400d1f14001840742d540d000094840c801600c1340d0500c849600b0082130014440c406c6a000041b2a886c40042d06540e000d41110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269981528 1250 269980278 269980301
    0xf0f040807030807020907021203060d0c080d0503040b1509010e0a18060507020d0804170702031603121e02060a05060120100b0303040303020d0309060902031902150c06060d02010201 80
    0x350360450b0780c1d140c40e19680c1c014000c240c0c0311314403040006942c6400400d4080c00711041d02d007110328550342c8004202c2003610619040d114444440070200301200104038150300501e02d0384070075841c0e203014507000040004c018143d4514030103841e05d01040d80c4a00c841a81034805001030f00b0015980c0c100f40d84001d00b0350840c1c0d50306107402c00605506201480e4040c0d40150790643c00c0d2070680d000c0700016940c80c0f0060382c00030700c40fa0a003000c04113030150301c2024102141c0700506031001e0041e11ba15030011814ac40d0025980e40b51049910a180751300441c0c00d4405001214100300800e282e1503000e52200300040280000d241c1b203000141d6540c0c890540414040c00010a21801d0205403450075601c0f08000d00d0401804d05c0e10350540700718a0000161007c69038994014003a13090007040c00c50180400c0002200d085d82c840340c904006a800307024510002544032424010b040c206c0c010405840600f2003151030b1180c04021602d158440407400076071000d016030f03120040d40b80e1031004070300400038224007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269982778 1250 269981528 269981533
    0x206060402250f200604030b0406020f0705010b100813030e032d01111309020f160b0402090a0c020a021203040f0b0315010e011220030c0703021608030f0f0408 70
    0xb103104103e011032001c1042c0e405815070b003048444400e00c03105850514018941c1c01082807200f04001152440c0072640103100d42c50160801c24541c07841d1b581c50300828030480340b60b51211151500381c14603010b00780c109262840e12651908150b114a00c000c20700a10250410000c92050000c6071001c205411030035101a40320308840c440c41d04070703401500f102d00d40c4d450154280b0b4150a00f50311000251000d8001c1589480e883c186800b0500b00254030004144000c12030600444054904c10150358100c14010482c064052800e403040105100c001806004468030300708912070816070004210b03298a038140d615440303041c1d2008410b4074501a56006542d00e02c680c0c1d0b40800d441c48a2006140501c80f422400e0990f8514a0010355144c651160018009800c0503c82c0d208503106401c200c51242d0700d10b41001c0d00c410521050402c680c01101c140c500c8080c0069910300309070b4100b0500d0a40c024003800444028100038007140c40f44a10340e54a140070f000410031072540d0f0000d00031100200700711003c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269984028 1250 269982778 269982847
    0x907080a150e0c09030f070308030f0702070506160b0703061412010b040c031d060103050615060d0507090f08030310060c0c08071202010914030d05250b01050f100206060402 76
    0x244000f41d600a28216001c0c0c0501c010340211858000759041c250b0351300c040c100342142d0368848a0858030b04010303c09000c5110700c5500085584600e0b00800f2403a1450300c409040742c80504003440c01e50303805130800c400c1601d409000c1001c100e4440410001d9001111035502906003400c04134050a00f10320705c075500500c0e001829050580581c08200d131000020045404101e080040c80e40b80e200920001e4000d40206000442980441c860b0b40c00140000701818100103c82840500300c030710464081e004500385540a028038011350344220010800075006628510340784c0d064600d8110940b1a0b00c0a201110b080c200800590440010261204008483d036072980c481c0c1d40c0200402038402a4080f41141a0100d41074a5030501d02100031406001051201f00079071040381d2a0307111400c036266034041640c8512013003501035a500d1416000d00950303900795040c00d08000c00f41d600c0761407003403099103000808100360742c002c07440710b0b0310107000ca8006894814106400076111005095803a64000740d91 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269985278 1250 269984028 269984041
    0x1080606030d020a0b040320010911120703020105040909020a030212032a0604021003020c070f091a010804030c05010603022808010515090a0b0301020a0f0e0907080a150e 75
    0x500a031003904210225140c2c40100700060380c5643c3c10603006065441c030100060007003401a410031010110030201904004840c112103801c441b1640c80468091004c0400d5511516003403500da2203944e040b602521003a4034560000e000c034480d51007541c3c25546c803003900105564500f40445d00860300076041c2a0841c819031880c0d0b803a54800030804642c5844140e915003205210380d45161040203d100400c280c2d00e568003040011000ea554082c1016001c000b0001428001d21003180184419048a0304e601e05244862080d6aa0700c08240715941e103e40700070307a4983e400f850305c98100c3d806082440702c031829400c21a000d8420780d0406904040c019505490b031340b8010310741000500c00c80c40014441c1da04c030803030075003640c006403000c0d04100c8101c0385c580e8540c98081521904003582e00c90020308455084046806e80c0c1080b40c000c0081b901c0d0004441d04a5000150381d411000200d480b034200c0d182243c070190120724050002040150750b010408030880d400540341c409401c0c4003202c101c4500d803d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269986528 1250 269985278 269985283
    0x1707021002060907060302180603042a03050606030607091a09100f1b0b06060a0302160f1a190f02070f0606090f09050d32030a1b0210050a0902090108 66
    0x81d81c039843c06215944000941e00c3c46442655054602158282104948074081046582024006681029500310340c0b00b000e14050700810101031410305001b01c050300c2d40c104a401c004005180300e029810010400c200c1d258801c000805480d00d15110003c69050140300000038040d110a41d900700e020070301c950038200d0304005204101c40d150b954600c5481552172038600580d8160400a20481307500b40407414600d08071024201440d5145001030a1286000920b0090200200151281c080303031300b03074202480a4a0a0f41d0142c0071190800d010509000d01d03000c4c8014401034000c1d8071156a1030340c28005502c140c049442c0d45801003103445070204c690901c00014182032040400f2146004e080340103044183c094500000c1e0008080d0507206082030003520046610703200d04561403030420414a0308819009060001c00032402a9901c91800403007440071074026458003105030007101c10b00400280c1c0000c407400a440707005408a200e440f80304002e07000c1d080d00c0d00020350000d840c1c000411680d000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269987778 1250 269986528 269986531
    0x12050325050a05030d0b03210a170f010905060303040305060c0702060c100c0f0207050f0d1407170d0905103e060106141209031e0711010906020a170702100206 70
    0x10042001b44071510400d13039a583c2e004502400d03001c040b0740944d4030141e81400b17422280c5003420000001d052996080102000844e03515014005081c014008141c1500ca800d500441c290000d519203401d5840305031741c80078001d20010821400280030021074484405840480b0009002c48014001100b0781c080944581800440015141100c4880344e0388000f907802e0460740c0181207240000361910500443c00101d01d010b80d007018060040080003582080150020003400700c500f46d642840d2504c0718141181142e250042101040c3c0902c020b0344c0e11600c1c0b1b0340c640c42904140071684840d01c01d04a10046601c3c0b82d12845000c104200004111450341c07840c900c8294090350085e80e01d07500140c1d10322111503000c469134082807000c140300403c10621542c0003201481101c2c01c0c03440d003402c82c6a164071200d4002462043c0072a0220030030030050918882030909080954540c1d0501c82e00030350344c080014020b0010748981105080c50000e800031079032200c0e00139000c4030706c000c440f03c80a907640a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269989028 1250 269987778 269987797
    0xb0a050909091e03180103020c030708030c040f1d06300705090109060b07120302130b040e1503030901030c03090203030a0f021009020d1212050a0e010612050325050a0503 75
    0x1c20020f030300d10040701104450401d03031714040d03211281e0b81440044009412182803c1e803103103c108122070214080c1001f4611490000415964a60800c0700d9440905196400748031448082045c91260501d61203059500c581c0a42c0d10000c0c005080788003e05204081009104602d480c03400240303401c1011800c01e00b502d07010f40d016070b9141d070f071419110101e4001c2e108210707110704c06102550024440541c603411481c5c0d140350244c14042d0703600e064000c0e420f080c1d1000710309200019040001e80800c20143e507020048800c0020840350190100381c581c820050b842d41015510f1040c580c1090103644101b0310290082d0850303445010051010300202e400045440140c428046845002103040c000c4100c2141d0103404244554019905c1680c000710030840c0505202c01808071420241c86c61007828481c10740084045501c17964034034802d0860301180c0110800401e281041401b2920001c11203511100020541488403144100410318410400d0020000d0003410f441c9002c1c002e0001c00f50000c040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269990278 1250 269989028 269989063
    0x10050405030f061b0702030304080d020106180203070206010b0f0c06011508180307060908220312050403020a0b0703020a020306040533160905100302070b060402030c03010b0a05090909 81
    0x1d0038202d08a80c0c810040b92110303c501185891004041880009015a02e02c0501128140350f01d030f1910745c0c1841821450180180e548080c100420801d00d07500f6080e900c0022021407960405290094541d44c0500400503030090002d40d061040860718101d031030001c3c91000351131007542c507590807407030301c0d55032006400004d48180007055502100000c940302144628008519040361540ca12002d0304441c8003c0d02c9004041c8a1030f000c50024031144030348003a0320758020700d816044d0300d001103c0345200c0d8122010008240010b10050322000e98110680e001d480145403107007194a003c80c0b50550020009415001e0b1106020810030001500b0180d403560380c40d03142080c4143e01d900c110020102121000302030740d074070202c1c43ca00010810300001a2a0f441d00025141d19000420f162259000c1c81800103940082d0000038801c4c01000e0a03086001110103528600b0000c40c9000b00380018001c80402190000d5500c0035903000b40d0071501a1840a8007114252800c00240d0b07881c1c1c07005d21144d05296 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269991528 1250 269990278 269990293
    0x17071809140609010617040c090e060702010c080601051e041d0103050d1d01030507141603090e01240302040e0f0103051b03100b060f0708030105130225020f1005040503 74
    0x40c0360070303c1c40e54142c400d96a1000f4070704d8880340b0840705004003d001564a0720000102080c0e40c440b81c010f40c01b9240c0008001d15030b40c241440002d08541c031f191041070410a501040c050182c1c0d00508695181c0c20301c14035441c06c01c242090500c80c078880c7e540101c00d80000d00c1110700440c0020003040d0704032401441900c000211280302910807800907148002c00c0041ca402504440d8000e40c4041e0700000940b5107002940c41e6800c85540585c000186014400f00110030801015844041c2d48080c0043c100c00040c15450114000c5403c2060309042d60612030481c00300848900c81d81c15a0001c00c0008400301031400c01d000d802000060a00094035580100c0003c00c0160700c04c1d85000c42c00d01d5001e0700400811140c20712001c003c068031200c0c640e12840c10010034242c4100d140c043c00c0d41c02d0040c91402d54a51520302003100741014a0a440b07413190041c024410301021040c02031f6050104084102c10200c102d10000da00b1843c2410041d40c005020b0741c061507030b141d100c1d001d042070301c00550480e50031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269992778 1250 269991528 269991541
    0x4060c02010f050a0207062a0506150102070506030105060f13182d0e0304090e0d020601151403070c080a020a05010609020f0702060702030a0503030f100e01061707180914 75
    0xb80c813a0700803860159100d4001007248910035a074541c08031200034005043c1804140c403000d12a0302015003540c1541c040b90078083c0350101d40c9000088580e09000600e0f0051800c40032502c01e0005120b024460600454520744a603408c40868450707d0b0b280d140318101e0b03512018032004000b820a902010b0760316028400c02d8100c901342c600d0342114051800b80151204400c0d4440140041d4420f1400e0382c0000e10002034030000c50700440385079034a0f040c050700540707480d15030092802d07005900405078254541305080405400c106040385280e105011144d580d40d5400e819911203020340070003082610002206041c541d40404c0040d902446803009020b21641d810303841c030a9014545103200301200410442005180587c02080358503c041c0507101c0d04461078903407604541044403200f007480c0c280c20810035019003903514038000c3e04614030007c29550400c2002086000e200450400c070a034040c0c04141c51074003607280380c52101408030800c82543d072a2050400030b8080007040034808000d40000c00c1c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269994028 1250 269992778 269992787
    0x7050319060647040b0c060c03130b04020d080d050702060702010c140705012703030609021c15080d050d11160308040303090c0e0609060a151101060b04060c02010f 72
    0xd52000003000c0c041240104144458022540c1d1264840c01d40b07403800c080c0c07003e440900130300001c1c515408041d481c0c0207203050301824240000c0001c2c9140c4020010001003001e59003400d51006c0d001021009a9075403407000c203010b2107104501404075000800c80784d9407040c46030042c0e842407981e0f9007519a69100c10310280c0c00d0701c0c080c42818011507003410321072182c8a08a00542101d5000d0800410222440c2031a08600104c4004180d0f48072019001c1909042d010300410b0003c02c1030007070851030f140e0807107858207081440143d4000125180d681190703181012140c2c060240c0500d40659128520403e00500301d94070600410300041d0030079200000d4400d154040d1341900d44c4022080c4e04202c83c550b021240c01c0c000400440505035180c80c001d000c5010060844040c20150800303002c5400c100c010429407000003840c443c810a52094148030182513421000b590307510909001560156161600d805044590070200d0984004240011000c1c0d02041c100b080a00030b0300c1e06040c408040701d080783c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269995278 1250 269994028 269994059
    0xf1309020d1d03160312020301080f07140108010509060d05010e030408070506030103020604090e030c03040f030201121a1c08070b0105100801080601180e030a080106030b06040e1602070503190606 86
    0x602d00d030400c0c000d0496500494010740000b510034901040340c0510039103982c0803604281c015112690143c541100d64480c1000710901602e80d49551882070b4008000082c04500140101c80c02042204007280554503180c001e512075a40c000028064031840c2c0449036980d07085403290035281d1140380741c00101c070706182084034142c0340c01800391072510f4200041035028100c1001c8120040c0b00400840000c140140060000b034102c2541554185295000041124100406401c0210724040741c2750b1070198615500034141800b035561700000100340d00d01d12070005980002800d50321001440004011545000078140d41c4200c60301a0351000c0004216280d04090040b1007450703012100502c59070130042514004c03102c0c2c0c4580480c21010680000f030964000d0b45011001c80c0d903000041c040b05405026400c08c0500c1034900e141458908541d020352101c014107141c48000c0249213246143d0f109000110140c07401a0454002e01c143e4114400441040002a80d615140040c08600002c02c1038005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269996528 1250 269995278 269995331
    0x1909030c0204022d07051608030d090c050a18180302060414120f03060406060f0e27072001090c0302062a010905010b04090203070b0f1309020d 63
    0x180c0031410350a00000f5481a070f2541c5015103c8001d900701c2e50140c0116240000d10384081da0f8554042d40f4015280c111200001d0382210002e400900c0320321800000c0c0e88800c400810040350300c0e006800d05038000c58160304440e0f007100c5150300100d814840c00700111340c518030020007005060803c403a020300c804000000100140c12007000304001c0341c66805486020080c0a00ba140c5005003010940d0055001c440d400c5200b24001c0b00700704040ca0644910001400d0f50708001200702c2c41e8007002841881e0822030f903440b40e90410352103861070280c09110441201024000e112034100000041c19400904224400c005d00302074001d505c100045c0208416903520200300e4400a003961f00300b040680003440149540d8401d450301160b030b080326042c2c00300d80f41407010002403560002d09015013507650146996000341c2c10400c0160050310001903903401c4506181002e6160724a041c0f8100c014440c200c00d28041c25419a008a90700c3c910340e00810514007614801c200c4200c6a903007032807a640481b140c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269997778 1250 269996528 269996537
    0x60904020a15090803070303090201020d09150f030e01060b1c0204050303041406070f0b06010207050301090b070302091302071101120e0d05030637060810270f05190903 74
    0x2c11460514001442103000e85041000c1076036101c0d0722403403940c5c00c003503010742c000780e02d50004506550301130144240104003880c1840b01d00d400d00c1401401d0a10f08900581089034541206185501c2a80424061007241000703000203a501c242c122015000081d55040401904403a000c642c5454401c9504030b4a000d07020710300b050315000c1c005040010b42a9401e4000008001e903500240001c80c000303810521845042440e03040c210002840e0031000d804c1903011340e00d060314002c0814005041e090b40414035160140e0f03242d007207002007500281c84140c1c260040b80003042c0d80e004c215414403110a14042030761406103550507640d04106450340b440405d07002d034118203555101c20384204002d581c8610050704c5c3d00001c082aa02019881d40400e00404406486174002c4c03451400300a0f00e00b00819051802074864205007500e0b0101c1002031254406242900700660101c1790000100351303001150900400c00180c4a03a8254042c0c40704545280c540000c402e44081034000c10f10414020300e4041e039a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269999028 1250 269997778 269997799
    0x61b01060e0123010905090f0a05160504050d0203160308250201120c1b060515061e0c1002040e0403021c0c060222030f0c05090411061c0507020d0806090402 69
    0x8440355a900d4083c8403504000c0b0f11100441d140d110f40522901410a002d04650340340b40014100c8115507015003088074961480440401055100b030949003950400c80d03000882400038030009150003a080c5490051086514000091000d1840603080080b1b03450341c4d03822080340e42840144c2c03950902c81d00a0200c0c90b0100c820034991340d00d070f02000603100e45041084100081e0200180c0c00310b80203000702c0d90280c403032040001c10810344a010090300c1003618203e0400120144c008806921580100000c01000c516000c9070401002103074002c0c80c00c22021075a458940c0440c2c0d01003241210306901500c100d1582d07036110000d01d840c28031008415901c40b030002c810340e030b22040694020500001101c2c840800001c00c010310f0b03403140c030045104410f80b170368003d400d203083c2000d80d9240d404a4854890b40c0100170114000020304600c0c0d8030204e07045680e0300c25440d4183c4110410b0b00094007042c0c517007070401452a4001590101349a11134443d42d501e40d4545003000307942041150002c0d0400120007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270000278 1250 269999028 269999069
    0xc0c060e01030902040e010e010f0603170c0102070f060504030f08040302070b0c0c180f0a020a0c080d15030b0613060f0510110303040303050132120a02061b01060e01 73
    0x1104181200c014036001c240c2c01896000036095403421a00b6032440c0c3d40d02c20b0107441c211310034450b0750038440680f031007032100c1f0789141c40b2540070b1360811041807235220001030390101c1214298115000654003400380506074070f0a0a0901c001c0c04122801c6000c6510340c0c030b4608402e4003c01090344201d07410340c000c080850400140b00304c035411014028482d48102404e18080b5640e66000b45004000c1d0b06141c902c80c40d00c400504055400684000c05031881040452000c660100b40c5e56482d0340c100c000a40d0780e5400140b948020041e0b1844040d4000c90030742d011041240102c0c00b140696001c41d440009242000340140803220781c2d1140140500742c0c02d00802c441c0c10619510120003829007440280410760000c401d0840e0303c1200c040300041e03550030062196079503400c2c2f0001e40c3d0078250b0944844104c80030b000501c102c1030b1060144038101c00a0514618442080a4000305a010f450aa03c805100c8085c11042030049801003031542481c40210300c012769411098102c3d4005c8110300e800d0b10300d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270001528 1250 270000278 270000287
    0x702010f05090f0f0105040801110c0631020f1e090c090906100c14070315270204060f1d01060206090304060c05120a0f120203060a0302042a020d08070c0c06 69
    0x20413400d81400320034000056802001c3c40b40e42d4500d9400511070380d40b040e10301c3c407590420f40000c18144010000c50103100140e943d01c2c400081032030700c04800303800c040722a00006a05150b072a1101c0e601154030300c00b160314090601045000c3d00c0b01502c06403031544480035000118001d01102607000307080b100000d821481c040c1000f050104081c1003080c810440c91b03c60344981194110348142592003030b081041003002042d102c0781c2e000741103002000a83c0c070f0076001180410556840d4102a0040751000003590745a9001c1c000804211041854903940c036040c000c4075400c015415400036060100004990740007003030440c421128180510300e0907081040699815040c00400e0700c07144680c441900309810741c0e10061040311801e8030b41c003040c4070764950010200900500c140040300d005005004584d01c2d400303290403e907503044070040756000c004078154001c056048a00c0588460580b02d0421454000c01ea10341c803607100d40e8514110703584942c000d07560355414240003480308a5540040008501c02c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270002778 1250 270001528 270001549
    0xa050a1401051e04060c050709050708010509040c08102702010c0201080907030606060c02120d050f0a0c0c0b0714010902011e030e06010b0d0b040e0d0302070206040e0103080702010f05090f 83
    0xf0810311609129400d00c003402d42d046900514041000d801c003500903c981080018020421500c0030710480c07a040e040101524818800d090051400c000410100595250761201500d400d90448000780b090b0460314015120161000e08010b501810402c4207031400503e82c0301594060f1a030420070040c0c0d600450b01e01c10300901c2122240600c80020000401d00d020340c0e401089260303209510380469004015000700d80200c84556903211402c20703000d182e00f040c151a480301c44455441e032959074041003036403130f401c074850010721140c81980c0104600c80c0400140807014001c02c038081880c1d03442a840b6007214820b07074020340410900d00d1103212030403d8498503017801c255031801045030021490182c0c5828400e800540c0c45840126201c508800248101c00a8500448081c4410b1350711038a4140c50f1a448100c0c0010181c0004060080d500c8140843e0000d111044c1300100da580d403428001481d4000041c00c0b4001104101c01404561049040e20b080281c001d000a903201248800c200c48250f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270004028 1250 270002778 270002797
    0x7090f1a1602150307020303010603051e0103030f03020c03030a0603110303030c0702060904060504020712020606010c2f090406020a02060601090e06041e02120414070b191e0c020a050a140105 84
    0x10044140001180081d010714002c0c81075400468030380d4140100030f002c7da4800dc007142c00a43c0304407000d412445070009035604690301803d0020408007800001c502a11854030031315218817000040c840307018070f95071000c002ca0380550700080f000d554600404d0340702c1c8070503603590030a00d00610038840980750210080511080061002448658400c08241a600b02001c280c40b181d908600d51005590140501136000c07009183c2101181e265644154412411159451080c500c40701d004004540c20300d07594100d05070042849500b845d1915111f400386d4480a1050f006001e444003141c8035502031900380050303401c801c544102c141d40360024440181003039180c00d2284001d200610056034014030003030004500d03c44500b0194a803d0900c0c0460744009000e00205501c071002c01c1203002912030945580140884c544480c180420004a540304413400c0420001808028554a03480c0c1241e000009a0720a640d10802c00350303a41d00300800b120085c40350054408603502e041d40c55600c9800240710100d0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270005278 1250 270004028 270004039
    0x50d050c070c0b0306040f0b010918021b06040c09050601120b180705070605100803032205030a031b230c120706050601020f0616030c0c020907090f1a1602 68
    0x201262038410050a10740d102d07003103c11000050100e6070038107004180a060340c0075424420f06009800081c20344a1510400c0410401214034680d40c005c650110b4440044407580d0744825000d0f51480c50701e52801751822100c45e00001000500090f0034020740d8450305050b1110810560307500c4032007002d0265980020b51001d4500500000302c90003445040c040c50180d600d031900e480d02440d0180460b03101504004030110800c1017002040000030850340d01c81100d40148042200002c1200c010040021004009000208480d0009507069015100c12a0b64468545142200040c143d035090b40c1e610b104012540100184181007000c8802400300700002c004880e10000350f6103450859402103002141d0b15074549003403080310360f410403801c0c1c49084118090141410036920140d40d0303c008542d044141519200e250051a01901002d10003540127480d124485c41c1c81d10340107112a900d4050513402c14a0304e000401c05901d8002c001007072003054000c240c681400c10707401e1004010307000b03012a4043e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270006528 1250 270005278 270005287
    0x61806040b19140627040201030209061903090b070c0c030b18060103061d12090d15020a080f0112051b04110403060507030c030212070c0512070f050607020a03050d050c 74
    0x358980b140071041d004140030340c20f180c1888002c0113030a048000b982802813107003003e40c08102002180558000d682402e00694540314034000ca1001e001d140c1d01802c0740d4030f001403000c0081d50075030808103001c0e01c103011040340c4e5a01c0782c1e400c1c0c481c0b40d030b009809040035490307400a100055081141c1a000391021041140381100415440c1c03402009800031076601d80c88444030402c09914012410860840b50007404900340720140318070480c082c10380618440e2060052020038448007851449044926003415551030900d2980a0a64070041d10709086a01210000041092045400101166111020300f410701c40604041d40200c154100481d4840d549458504007564810001c000440c483d540100b030303620784088042c04994004012400780340c010031144030701000140840e1350164207403c043c8910f120740d0800c1c52070861018042c1d50300f8100054a401803000030800b04061611030021218161766181c012038581100c80c50007170106809001c1d08048c040c20340c0150303500c8030000119030f081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270007778 1250 270006528 270006571
    0x9040f0b0c0c07030305070b010f0602100f020412030c1a33090f07080903030c07020405090c12101d0a020d030e18010501020c0f09130804030602030405030a02061806040b 75
    0x3040b603e544100c020420006110007000115410fa50041a000190182c41898020081d480c1c07581d0b00041040155603100d108034040d0140e050381e015112504800c2c09544181c5009441c104121005a40b001803405e61155072000300300c907691181459000076040c2407420441203100dc0e20040c403490199106241d40400e40e181c020415100f4200506401c186003041d40000d8030503003001e403c0c4030321600100108a4101d48440072148074a50654000600b84c2c0c0c1c000404d4200211144415400800c1d8044c8150780e44001400c03c01c1c1040c041020040d694100c10201e40102070b0800121142d001502c1400c05450a5060211458001d06000503d0a60640041e1050b5a85060042401c40000040c070580d6810002d01c050403a040c0c88045121120500282e10340742c0080c2403140400400d03011208200c10311040da00110380c4010150b4880c2800d11b0125242c1e00074014101c010301c6803000040461800c400e4040d103100702800504001d86640c0c540d07400c01000101540c45c03108021003d03518 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270009028 1250 270007778 270007783
    0x9020f062d07031209030e01050f0c07241701030222020d05010e0112050a0b0a110d02030405150c0f031b1305010f0f080f06220609050609040f0b0c0c 66
    0x407408010050707503041503180c0900346400c00380c604801c60b40f801c2c85c041c0000c5e4210384d461a50345400d0a0841e103c0801002008030361048500c80421030240700720004071131010030004150020300c070420203044140e1000840d2003924410801d1283c6140d40d00400260414080f8105c102e0408440d0040944442d2202c4042e40c1c040420040392581d24001040350031100c0c2ca50718050140d10950328082d02c480c1d240c003031380c94151000240c10f100130300700462481c0780715600c0708481c240726815081d00d40a4a4410340000d400440b0291454010304890309001c82c03550b10340e80e2041c0e40030100c2a05011041d0604038003600010070021881c242020400c0d0320b1011040546490300f0106000480641020001002c030050054a1002c2c068060328010310a80c0081e41294460700c0f43c0e1205207241c1d24600090010300500481c200b00d007411300441c013001c4121383c22450070340d0311804080c403a0381c076940c082c031200302e400716009480e0201c80d41c074280c009400d43d51003540111504400a003048c140a84890 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270010278 1250 270009028 270009097
    0x7030b010e0108010b062a210403050c0d0305040b0d0f05010803030a0c0302090d060b0f040203040b01061107030c0608041b090e06090102070c3602031909020f06 71
    0x40c10810030700042200200901411300e180c28103803519070400741460204840fa1003000041034065158140c0026010410002601d5040c0d0302c040c026208850860801c14a500501095400740564001c0c2003550800b141d10200305517041d0f0320245032070f18101080010741c112400c40311005880d0b04250b02c0d6011940640c5018010243c0503555030b0804072040350440c0c015034240c009150041c4400ca40903070f40d02c44e10444080d0844000b151030341100b800281c20202c00c24110758058808030601080c888050503240c140c80181d29080340c04003001420603035034007039840010714111003427005121951161401c42c0d000f5108200c03000c4910000742200c00350100d542c01844456607607031781c845400302041040582201d0450300840c50603406490707484848000c0c0c004c4c000c001030010b1441840c00e000b603c02600c1301c030408c070340941e4050790462010065442907500d0300e4003001e21004c401049600d4414419882c3d4018000e00e4401004c10030311005800030b216160000c401a200c000b0803100c42d03110003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270011528 1250 270010278 270010289
    0xa05010c141c0f02010b030109020109051005040b03071e0206010323160b1801050301050906012105070e0135090304030c0f09060b03220c030f120f050c060a0e07030b01 74
    0x303d2140403d403000900712000f4000c1d99119030306014420f800350340c02048140c103640b81070341c07410306508050405413910300c00c0382e000503031030400041000340180c2d20040100149010081855448100b00d00c101d036909800c1c0009400303900b105e07904003203017211000580c1400050034191242080245e403500c05092090b480100340d8040040c090060340d94402400d40e0350942400c0960440d414140800c022240040503241804000d848910745095900c2c4e4408081081d00300034000351030900703002003c03c028001078a000c680b80780c4002515102c10f07842000200d8405020b455078814600d0700d43c40d00c000c094140041804204400b00c0881e00c0c0700e460307402030700030504a1204649007100b03407011648541d00200c80d0207414402d00034004009030503c50404142000036101c1e4101c0c0c01c1841f035200341e0ba44002c142440c1d00406508100c419507510031842c02549560007103c841c0c42064a03d480b40018940454008000090045101e80e20808801410800711510942c6a0303446400c02ca43c02e8216 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270012778 1250 270011528 270011537
    0x316020d080307110d050403050c0904030c080f130b0903060f1503070b12010609180902041d0d0e030c2b0b0f150a1a070f0b010902070605060a05010c141c 68
    0x1c0c0820b15004205d11a0f0420b942e00e0035078a41440e44c1c03038040d2901811101c10744903040b03490115090520400400c141d1302d03008051740d56118050880c0c180e55500181082d20b4185021500140000741c03041903400180e80540584401c1d41c408000d142c01150040c02510741d00d140081c03130542d0340c50170400032020703025080d0140d907103a000b002e6040040038140e2004042050744881484444c001c00444030f41503041d5030011495948910008003c0c0403e0902640c981400001d031305003c46000802c000d00402c0c0752110700ba01ca140d03100381516008503205054000d9849806070310b0300d5403c3d0304580d0089624030110000c16010385d5841e405010251039501403e807000c0c0074040005040300c0850380e00081140d0b0104403030b251076500081e007048008031000c0383d84003180c11030030b120600c1d007801c0c000e030f601181ca0300c4113603103802545000350003900e0309590403864000010024203003000c808007036071016100e40441c3c24065545114083c00002001000d00644207080d0700e5804aa145e602c0b6190079484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270014028 1250 270012778 270012797
    0xd05160620070b0c030405130c08130c1406070b1005010801091b05070201020109020a0e01180e060109050613090b0601120209010e1011100e070b03090316020d080307 73
    0x4024480c00c4654503285540441c100600020300c400180d40048070216070403603844424007400d0600750f000f507a0049411101000024640302d0b210361049030600119241c20086443ea60160482c03810500001040302900007014411054440489001480d0050090b494800d0300d51304c506000d030b01910304072800340c000c03202884590f030040040c1e4050030415501b0002c0007200303c03d048040080c0701840042c0100026007100b0369100390004040381c1d401034181419250b561803407240800017446841c4e41201000070385451700b40a0700030403000400c41002800680d0804103900010103014044942c0b0070b82076142e40c09200100d01079844028002c6802c0040d501e0101c0025241c4200c680c83d03440407502c10000d800c560f0303802c18001241690151071182c0600140c901c140e64001700074200c840309220307000072031040405d00d400041071006040151803140b507443c05005900d001c00e4865000940080c8a546151960301da01007211a0000b410000306202680368058103074825203440380000c56402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270015278 1250 270014028 270014039
    0x305061c1202060f10030609020a0806070801060e0301140606130320040b040603050a1115180a05010807090e1302180a060e1003030c060b03030f040f12030504030b060d0516 76
    0xc0181d500920000541104e443d041c2d141d00c003900c0280c000100541d40c0e582498096444645544002d4460324040f25170350f08050300080c01500092140b640003d900c0410481e02d03040c180035001031a44451320404481e00c81000f0001c51750025440f51a06140c0c1180c0000841e02e03116012103149400c2c64180241c480c074005002c10b03070749d4030f9400314082d40c103000003000083c00010385c0142c59500032905902c2880100c0c002000c00c6024114030121080100e504450485103021003019a1407c0343c900c0d0416913550010368110004035061000706000740404c000c2e0781c184203260b03640b060020900b070045004c05d41c00200078002500d040d0540c85507031002c1042c05402d82c41110003521604668044a00d4030520440c3d41e5059800300604010700c0c44000d07003c005841d000b02800c44801010707a82c451a449050318115082840b605a024154450009852403008603400a540c3c05564291070981180c4400c1142c0d00090700c03031b6402070002012200442d50034885550034500144000c80100d02d001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270016528 1250 270015278 270015283
    0x1e080f0a0e0405100e040f0b28110301060c060209090c0318010b0f1003060906030803040b0703051308070f15020301140603060303072907020616030b0a060305061c1202 74
    0x505215020360b181a007070116003210904c0c3c40c012134071798440c0a806540d540c075001600c0708920340700404800c094001c0c8013920f10040300414980204002d0300c40301d13044501c42c84c81030f24140040c4640b84e6000300010b01c40d40e03100d0725550080c140035040152420b03003081c0104030950000c40304d000c0c81d00b00100a20445640b10120404040c40c408000d1140501d83c00000e00f0f08800f200e00720303104140d01e400c0001c40701d02030f40041d0010481d10070200041d40c0d0381e05045038994000c0320700f152407103009800985254003d110f400d00441035944141d100402690f05e040c4654003031442602c049a10703164100001d14041c01400f15a03804002c0583c81e545048000c81c0701081d01c0d0055440b4070018810400c680c0c90004c10760318981e03081854488145c1419292180a510203030b140c0c004100400100303c405600000c405001e1807440b040407404645804d011411151045030165200502410400666101f50080c64120a00400c4404040d080b48104182e16507211422130b071900329202c030a08100d806 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270017778 1250 270016528 270016547
    0x6030209100519030216050a050309090c13060c080d0f06060e010f050f090402040e010803091305010608070804050c060d0605100f050f1305270c0906071e080f0a 71
    0x42e00b01581049100c40b0f00807400c05001e5222004c00d0340c00b064104002c14002112144150010145d6001035090700300251641e21184010f40218a5000450114174110f402c4407000000214802222410801c0844d49100400c00a4030448020300100c100301489202d01d164800808034006951864150060011118070040360b0500c07100380c502a45903138120040f078819010440009683d41c4449000030000e010702d0700803803106007031a0b0002c2980d01c0008020700700e086003210305000645c0185203d00a40b034007406210006059840030840850241d07048980061180081c0d406980100f00860a903800070720440c4515515020200601d04051805059940d11450300c0c00d500040000301601a00c02d01c0c800030101d401c006140c903d008400d100d1080030704002850300050401c05e82084a00c0e86284200380600c2e004800455408690740c400c0312a84003029020608240158030b40300010044034141c1c0d81c082d4a14402400050540e200800f5180c490000341c54031041e200d01c0040c40781a0b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270019028 1250 270017778 270017809
    0x912180503030414010507051e0a06050105040204050604150201060e10320d1b0905090d020f33130c06080910020906070b011502010e03160212120406030209 69
    0x810040c040300700071307480d0041e000c403080c01c0c0942c0e2288103150562500300c8403a05003010b80300c41c00a0845000c40842c2810b00c0074000c110500499803140100000c9200e144101640154100810004140d0040b641c2030598098000041c540d40d9035544400520021680740e03095042d110f00038012030b4040d1511078440284075026840680b558034008203005038903481e1522461103440c9030020094105c402c8549401d4140081c6021940c8922200c05130009541d1004a40240c25449541520000301044095146030003054020503016501c0b00e07010407010131445651800c4031042d064a4240d03c418010540c00c851019068140d0a010303500c01e400d034001c041041172640602000007400100400c100c0c01d6003c0069403030380c03c000088e05900c0b0b460401021584200e00000d40b8000c10b030b5001d02c01c034009400a020042e603034031029449100301400c507028691641071000142c1000230b80100a0a41d0300c0c1180e00031b60010a502da00c40e00541d000000081d0000341540c00c900300203501040c900d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270020278 1250 270019028 270019033
    0xe1f0318020d030509033901030902010c06050a02130b0304020f030d0206060105030703020d05090c0406050d0f080c030f072114030714040510030204090c05130303030f0912180503 79
    0x112039000030282c040c0c0c1c031405420050049070030701d0a03503000e01c210240700304860003612011440660402d440540d842c03409250080711119902254002e0160f0f584c0c02c1d074169240c0c02080740a13519480145005082c850745180c0c02c2c820481c00403c9203920002400c9903442c0035441e441c0620400025058074690b1364001d4100e400348540061f00040c0e10344c0c0020003400d0080e202d6640e490203e00078041c207400315402ca420034052001074500414201812042a40c051110a4a0b03070140032050203503c00091001140308071707540203d400400a09119417100094034503114016840300c00707030380080c00103489090503103481c1042c03048001699022200301307007824107001250780c03c1030415000043c116024400d80042c155903804406045030040c050003031a2200c2103807007402c000d00030b4109028ac60030442c84c040081100500400c10380394201c140d4011091090304507074049000d4000850303840d082545606070780000030380340b03010100c80c04556540c40300380005903460400e41d400107901c858000d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270021528 1250 270020278 270020321
    0xe0105090c09010f0e241201081c03110c060f0906060a03030804030c05070b0a27030203070302011115130b060108090c040c020a0b0c220f03020409030e1f03 69
    0x2a41c0202c02d414201c4c2e40c50900160350800140483c4200d03102c1c60055a1503c10440d6412480035044054030b20200c203c1d00011481c1e0700d4103401690780f9080b0004a500c8141c9002e004112480381d007007a0488070314000c119052100c8000302900d4020261403000083d40c3e40420408561400c00105502c4075045903003d038004d02d075441c003402e1a00d0288c00a0304010030070a100c000d212040040c000101829500c1507911641460010103603100d1210659100c881c5043e00003580108500320001d480d00140078000c99803541e401521044807001c0ca101a0340a04584c0009481581a90358440d0150242858030544149030044c5205c01c0100040c2c1884206014004030580004000e44182c0b8180c41c005081103503401d09a1030014015002000d4001c076004010b0005440c00141801c03c00d50748250034142c401801c032458517040ca01440c061010a200b0400152406401040c0301e0340c001c0c10105a54043c41c0041013109894208040750496540f01a1040540c0352180e00001c0702100d5426103007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270022778 1250 270021528 270021547
    0x20304030f18050d1a04030e1309110904050f010e0c1503070917250f0e09060f060d0812060109050a050d0210050c03040609060801050108070e09041502040e0105090c 73
    0x407116405000c3c00b51160411000030040512811740603400d844003055204e00d81b52a00500352070320040b8413401030b0411403020000500c1c5004210401d40d001400703007c4810080240100e4490040098440c0e200702002044148002c3c415041040780344006002c40c0400c9000303106542840706c6045004102c10410082240e50151f800010340d0521411241001020342c4040e141c1500415802d90319802ca0b4000e0380ba004031048150202c524400d03641d00c01503600d000c0c130011004202c4076040310b90840d6002848083c15403411540c8100010400120803170103484010312600007038001100c2c100060140400c0e9a00000410000c10040300c40e0701203c0e0500000c84c0400004400003030040c031050315110740842c000c4c0d0075250840c1c01141107030345460350b44000411040c0680b140c0ca0110b0020400401c95502c22140e25224120380d45800d41c05d041c1c41004d01c00307180001042540c2c0807400061440c192099030008100030100300c03102204550600c4200b011550019002103960202045500138 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270024028 1250 270022778 270022817
    0xc1403060d150204090b030d0f020604080901031103010e040516080c130b0607050a1401050c03070c0c050306011509050d050607080a02040f030c06110106080601151103030901020304030f 82
    0x1844002a62180056000c0380740c98002d198140010292480c0081030100340b00788107600030b460418040b01110309001c1c5401e4169403103c03003901c1440044c1c0294000038003243c00d400081c1101e00303041c50005980c1e881e0100f600c140703400a03042110031040f4082840280641001004400d845099002030341c103160668042d40c6130070021000d4000ccd0300f5845010505080c642c042c10100e04042d0015586261030303c5c045894503c140400c48481c000303092000d0301d424052040c144100003100f00345155803a07520003582e010300c585404941204002c00c0109550f242404441e00a108082e00b072071941c0110000601010001c1c0c00c040d0243c200d400000340451070001d5415081032842c1443da0b45510703a01c0515010348980d421130700c03106520034000400c010240c400c11044030003550311030300301c1c50344481c5460a0b00d905200310b82c0f090703120740c0040c0001560020710f0040710b1007605010415090b0320801c40e041d0f8000b03d64500d810703580032040000349608080782c640307001d0040ca000003900100c00003020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270025278 1250 270024028 270024031
    0x12080d0f05060415051c05030d09060903140304020d0f020303071203020315180a021b0a0507032d0618020405011508130512130305100519090c0b070201020c150301090c1403 76
    0xb41b100300c0d442415001e00109004850050300a01802e00065400b030034a4009062600c0c0100c0001e81c203820040001000c540590380a59801030007c0b16185040e2144c40c450b6000c02c1c000c2e030380b5020400c048000225401285013810005031800740e181c2c034000c2c00e000b540c00828400300b40100d002c00300000c480d4902c410040e6002145000050310392030320b0008444200380e410503d5170a4400e00c41d804003808000190401100c0c811604034031980180c100120100b06481d40082d41120001000070001c0c445c4e030407e04d51241c44190040b00c21703040c0e0f00020241c179000c0e40490501010301b640d01d042582c2c46043d09070300c40d10f2510180c00b40e04d11551083c1e50780120311058286904049074a989501c0350804007070085422904a9004000e9201c040303000707090641d101e6100710400c1c400070609001c2405a0601590004231a008191500c40503001903440540c0c124110300500c0340c01c8a1641e40c41191800000070002c41c01e44a604107103101040764580349135a400c0c04200a103403241440c03500102d0303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270026528 1250 270025278 270025309
    0x90b030f0f060102030a1407031e050c010c030c021522061a04020708190207032001090504180807080c1504050f03090d0f0c080d110709110412080d0f0506041505 71
    0x11f99554a15040407542c0c40b540300e01c05907040000b04100847c0c15031103030140c00700e0702065008011408020b0404d504031284548100c004d40c000000a0040d0b544180810b0b5100e50400c14072890100d504c01e07000c014452204084400720b90f241d4110300307400c03c207140c180254481511300318034000d07850b1a03d0000e800303900304145100d0750801c0c2c0f0070182e85c4244010402540d00c680e5440c00010507503c0480c406141402d400d000a440328030004492a2034002c0d16030604698000c0004402640c80d2450540d11060b015600c800d8204810801074a04214501c90801c10810004440c101490114141241d801000303046138014040c4c181c0f541c0d200072b9511815640040e0368030524400f0b10f40300c80b040c600780d0f110210354025030024200345a049001959040780b10002d498002c0c2e2910544800c980342c1c2014079054034001e100a01000005403c0e2003c500e00914489041550014110050300c0c082c0d0700c511821900c0b030091012505250040f5030985216050007200c403401c19020494031411028607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270027778 1250 270026528 270026567
    0x30504050d060e011a0f0a060518040605120601060f050906090609040b03060109150b0c061f09060603020406030617281704031b0e0c070201090b030f0f060102030a 72
    0x148041010541c44200d280f541c0304000d0114064902e561444801c0195a042c01102c6001819901c0c2c40d01c3c2d000760080d50000c0e1206800e00071099491524600c040c80c0c803e811a5442c0c42c081003503512030450701401e81900006040e190f04200e402823490808012150500c03900303206280d05507076910255011070f0401e64607940c80305410400600540901c800140c0c141c001e07403001068a03074041c0c00c01d580c0307003180c0008104099076410314003e440c400c02e040070a05801c038001207000103800c082d14070346e01c013400c107084480940c550803418125060b55101e440403d500060422140c0c1e054007400700184249910031440c900c404840300c2d1507414a2042c0610b1102e11586050110900c140342d038202900140c0c1c4042c1203043c0c0c003040c02d46900c140003c2d140461500b484100e440d0303811800c042550410903005002c0d0721100b0f6505000d4000010480c140421082302254217051000598882d5240703540c00a00d0741002c0d4951082150050300060464008000840340070341c000d9065490006403115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270029028 1250 270027778 270027799
    0x10b0412030e041d070501021f09020d150b0307121a06150a12140702071502281104020c0307020f040204050603010b03090c0109030b07030203090111040f0e06090403050405 76
    0x5003103400089000703025070b01038545030b41d55030907900113824500264104821038218a4403540160303503c000703001c6681503901ca446040e0610707400b1904445c000700d1001c0c1c241021301555940700801192041c403e9038890b56161800075207803504104a200524100c102403011803281d46801c0c0d5150000400055414114000b0400720345a908680780c412003010001e03038640d070003808001c014091007a00850118107110806150303802012005004016540003880f03030502d0500b44041e1450200f00000a6001e440903c0d0a05420030154500084408400308400328840c80c1441a203200000c11a000e94418411015030403000000c1b03a000301c0c3c040390305140304588400090080e100d16042503030888400301c00010000c000d4405903001d40e11030019200d03d2880640110f9a6250920010f840c84602c04042209035010741c0c015030300250024004181031803031680800700c4d603115601c0425141d102c0c20f42009a01d05420700d0319003245007265102c0b00c608050324004c0c80c40c000c502416124000c240c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270030278 1250 270029028 270029033
    0x7090e04080a1413030c090e0a0f050f030417060906010602031614010c0f11010b06040303030f0f0c021c02010501080d050a180306061a12190b031911030303010b0412 73
    0x4000c00f00e450480c040050b40d502e883d02c0c40d45041c2200f488220340400c0c0882000c05d0300c0313101d4040c0c1c03251400500010150800305454000c10170b0807a0005451501801094184041050004001034a403c10054154500c501c49844c07912030000c0003650355800800061002e1507001c4100c4040303003820741d8848208509800d105a41042500c40040c3c25840d20003120034054100e41261802e41c1315860b5500110604005e00b42610b1800303101c941e120b4810042480003901a41c014410403c01b5130303000426950f0145d0f110f00300d03481d6102480140e401348514210a0f41c110110008045651009000f10752401600e6543c07090510003a00c00d01c800845c940010510580c40901000d20031762411221554070700f01a0000c00081c019420415440342c404444800010f080b551583d031170400e54903050f071b900d078050702080101402d502c02141d03e40072424a16501040361417041007000911140c580c4440c50520803544220455a010350000c0c4010060320988009660440300c070a0b04100311445e8a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270031528 1250 270030278 270030287
    0x1308010b030706030506061c050612070e0a050a06080a0f0b100501080103020f0312030711010c030605060a110f0124050907081b2a0706031109060f0403121707090e04080a 75
    0x11035860502201440ba07401e230b00e42c00307800090003104140c402030f1081400f1a005622440d05003e1440003031040d07804194070351044d40c800c59000e00030f8803000509940300d900c0c2d103081680f1801c0541d0003280d0114030710b00b40076802c1440364204242c4c801800e4014648400038109140500c80644204118007840302c454505002000804440b160019502e152142d0040c2240c582154010b1296113001c5444405501a10480701541d0005081500b4004001821260b02c0040a0f0300c8200d40109902c81c400c8031f10900501040c0c0c0c099800e4201030404040c2d41400602d0b81e03900c12881160079038180583c6940201007507400c05c01d4403804807800705440c180c0e2203851040f806101da4103810104e03560010910b08400915500380300c02640d200c00d9071410300710156080b140c00c4406d1410b04120a08041c5820001050540d11a03103025041a5598480d911544501d203000e202040211001c007800c980c400c81d406501c035115003003801441d030811440000d4240000d00080c400440002c50100d450b016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270032778 1250 270031528 270031537
    0x1110a050a03090f060302180d050c030f0a1a010609030807030c0c030c080f0c0907030e07050307090504020310060e070e18090d030e07031703060604030b0c1308010b03070603050606 80
    0x10111001401d032490010b1071500c1c030f0311a041c0c0303440200303c010651030311900072100e000d955610454404c650319030400c00c09110713100c0111028031825600602d6a2001c1c450503400c00301c198041d000700109402d14050b01c1607110441c181c0302c90b00800611010750044030b01340940b6005906591924101d10703003551160701079031004d0041848e240001003000001c1c0030384001d031554442070b2503c1200d031110740c655a0319815460b561007030030840001c80517840fa501400003240c01d0380171503c40540c0e49012038240f000e01e81001018940390801c11056040c2000b000b186203117003180800c00c00f860b015a468940102510000030406900d02d000d920b50364022421200d02c0c14a110701815080c6110388a540c2c14030002032002090500c000081604008110300003200d42100c1c14040d12828010540304c01d0b0b1000f8807030b5521010512000c004281040c84140c413655290081540d03545a132aa000c0030341e00254012103040c0e0504266074450740f40400c00008a44940c18041600d49401000a0f01e6004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270034028 1250 270032778 270032783
    0x30c0804030c03060b0904030e1017011211091006030b150316020d140403020d080408100c0e060f090d030509030d03140603031611032b020c061801110a 67
    0x8041408010311060380482812288110b04c204070200d860f0090000002c0120341c098082107c0207090300e0740d4104140041105195803820300d0b03c0c1301e4164415000700c20b081c0c00003c2c01280c68440c1c1020030251081c5030640380d00442c1c224215140007412511201007600481c020961210580e203400e8551511144511140c048896100d1501100052507011030207940c2c4018480c1146508205000d005800840b1070000f641c0d61815045400313000360160140011101d1000070071000681100030f0060210b034565502c1e01181803030401000400b00c0500c10344031032003003508114804100500d0307002c803140f00006440e021004051030805550b04d02452000a8040c0150700c4039000280d0306a00c00c4c89040344a20000c19241c0340c19090503500d000d0b1650a11052030391011010201d800800c0c1c1040a650090484d124490003110041d41c00d40c00006c002c01c048000549000e426405111421a0b40310a0720241c3c00e05050200036200011200c03490783c14850181266030b0480400e20101d940180c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270035278 1250 270034028 270034043
    0x170a060903030c0306050f15030c120f010f08150114010306050418150203060102060601050d0608030f0418090215070510020c1e0f0c09060607021005030907080106030816030c 77
    0x2200c0c0c1c100903002e000100c60810020f4500280400c4a10380362a644680000142c5481008480c403112052950320190105001800621040742071200c0c2d14002441219010f624110a500d0069100c0388640150002e41d001c0e00400e240a1584240015450448050043c4207040c1162440140c00401240e044107400a0902c41410b014410160040e0740d0280306603000034a03642c4031509002240001c1c0d5070303140160000400316161758070400240c1689404c003600016201e9a51490600d1a40111114603036018081030400c404048044500e0030032101b110f0a01c840d0705203034001100460b107818621000030010842d8414040c0c1045407161645440c40211340e60f8041508082d66010300d4440100c2c00300c04040c0400d0a0500440c0c0d01e10103150150041510b140100c0c100940b9010080481d90041d1041c070800016a840c1d6030300c0e0f00e100440c1c1d20380365581c2c1480d51085060100c00e41111790160b0400b1001c00010741004200c850300050011116507280161070200d500d05038140c000361000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270036528 1250 270035278 270035291
    0x80f071709010501140301140703050c0c071202010306090b150307050d0612050607020d0e040c031107030e2407260705030903010605090c0702011124150613170a06 72
    0xd105502c02030580d031041c1c2580328940485e81c201403c2c3c8881034151004001000d01007100640250003064205d4140c00c40e003810030b480340e40304d41e00d442c58030740c802004d4115241d040019540c0600c0b450f00a4480c02d10280150f1b91803401040701d200301c4d03021003442c40350000001005603129005035060348000c10340c02d203d2030f0369a075003000d0703e0303c0d0303001080e141d078007030100880c0195000042408604145444181c0e1035010841004001d14140454030300345525400d02000d0031407050000d0220b2446130b1108080e4910b00c80510002c584100040556191419040b5071201c43d040261500039900c4a2840a0792040e413069100c1c403030081e014104807800104929080100200203010500c0c0144d000704070036a6104204075240030f00b41c40c0110401006c010007005540709c1c021466004d4460000c40d80d240000c01981d0303202001020304081642c680100303110004409801c89104407500700d41a40c1408aa440102102d00840c030401c00c99021031141002d269030140840403000d908071030b00300880b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270037778 1250 270036528 270036541
    0x60b1002030408070b1213110405040305030a06060e03030904050a060b12010e100308040b0702010207051221190f020a0501090812060a080d030209060c0d1e020d080f0717 75
    0x701d411a010703005080c041c03001e0114013080c100c001da0749003080440000e54581c859200304c407540b410000c810f85002c4184002581e03180c43d280101c900035071281e6101640e918000749864100e81c0d13160000002c01c420340f40c1c802c90035500042902e2495030100c80004060b25880c042c6401840e1b1544080ca030740768040f40130320341e114988203043c1c120707040c0f4010715007640d40e40600724400000c940802407010200b1302c028880c10b0764000180000c02d20600480702000c0c0c80d030300010b15a603c1c00207401038550180c4400d024500c0330502083d25000c42e540001e0500840c0181c900d04510a149480100081c00185520182c4208050640d4980240c0204034140e014100240b640d48030451041071414030b02e01168840c00c00401610448018201401d001919000c0c01c4019501459150f40d0000c800d00510a40002c180286e0300401d166441d0b01900032a907012807402101c3c511041c40640d00008409a4000c3d08942c00f2540809080c82c02c0410703560306801914840c500400b1640c07896507041c03c1000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270039028 1250 270037778 270037783
    0x8030901270909021e090c07050114191104180b010c080c060402120f0a1101050c07090e07060c0b0606030601030f140f0a0207050334060903031d19060b1002 69
    0x60f0090307175101c81d1405c401c080c0100710340c012016983c100000318001002400c9090190118030301c100004a102c5596a4140d0310110090b9030394051244440075088100446105444149505108660801e40b03005070b01144002e16045844000340c82c3d40c00c2921a80c402e01c031102625500054030b076142c1d110f40034000d680b43e00c101c400b24001c0744480042c0709045000201001030111203402040c010701140d0b40d4550038a03d6070f6456050200038452555806010303c0a0400350114200003e84500312034030941c41c010301036000b0b0082c0113a1001240101304c1e02104180e006900380d03107081d07503030300c8840040f0300a0025941034008c032440c0003175285a001042800d40c0c09100042007a94040c0c55500051080784500200100554803c105480507200c4004409007041c0703030495072018042550744401c03102025403004442c103a43d5070a8440404d43c140c0300740740014a004c01741711070b441005902966162030344140709820a8030030340401308014240d08680c9240f0005004c85035202c0105401a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270040278 1250 270039028 270039041
    0x20708030c070501050a0b30031210060e011e1b080a081b04030b0402150714060c04050a23130c020f0c09181011030106020d09080309012709 62
    0x70f40725424000400c41c0e00606020b40011144002d01e10510301c100d20000e000c8a400c0441e50318007000030341c004160045414070150180364014051b01040346003280c4015482d00c900d0b08104240600f46a009095903441035051615500101da400102090400c080d680703181041c0c00600a0840c4001c0f0300200507070030000d041490310a490f0b80001c1c0c0c90b00503032034a98030001d3b00038030380c02101888100b012a02046000c0c1e0403a0002d803070601c0c130301941d0655100f80d42c400003060320b444103644101c131280f0f60208070301a4403888030100c1c3e504003801c1a0008151041a109103c003864110b420107405e8455840e0540d10410018481200c10040c811020083c2c1503010000f005401000804040c240d4045403820741050300034078001e00c580c0d80140f200804200c180c51800d8520030800025004c07900340c0724044605550071599a160b40c542000285041f0401c611003042003032a01d0100035603080001034650f0203100742403110b64110440c500c100d4a400319a55401803035040100012280155400352 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270041528 1250 270040278 270040283
    0x314070c081806030a0f0c0905060d021602090406151403060f2211100815010507080c1b1309030806061c180b0105060708070611160302070f06020106050f1201020708030c07 76
    0x30710040c040e040d0b003650202c603588145030702b08038204400c48648903d41c3c014105841043e5500c2014a52500410160306040b207040317481544d111040d1a03030f0080900510010f0604808ca075401d643e030030002c02c0c0c586202514401803d214400800c4118418240e503004004d410341e5441c3d040300c81800e00e100c800e000d02544a004e15017084081d03062501c1039400920a400c1d4420112140241000441f1546d004002c19100d0b1002846040a039290a006601103610200420700680310b01c0f00402100c01c04080d01c588041d03142918400021380c012152582c040d20440e42e481d1600e10210040070070f0400d2901000342c281c82c00e1950081c0c008110031031044107007d00900050707a83c0ba0014030180384160000680007140c140f000e00001036150300004900d0f040e800105040046c6402c45103040144040b0840141c3c001000034030a41108078114002044184001d0042c20b00c0c00c8003280e03a140c0c00658450142e010300b0840c454154094040380c00040d849510182d03a0b18003002c01c0007654000c09804c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270042778 1250 270041528 270041531
    0x3070b0403080c070503070b09150f0103050c040903270515180402040e010315020f0a030c023304050708030f03040501110418020d0e06070f0314070c081806030a0f 72
    0x45043d00d0001d40c207480402e80d00c040207501e008115240d0f481001801400061030f40305031081042c40d401801e001c180502c240c114030202070f505500d0041e0402c44841540e4cc0500e14000304100865072240104454103c5200708251013000b0090074800140d040d0003160b04104d1840062481c070582c0c1000f014145502681da003a055241c03400c020580c400e501c42c54441e15040e41c018008100001207203c0c801044640043c980800401c5440c8950802d140e20340100341d6900149001c41e03014040c51820200380c500100040b01403c008030504080c2204582c1c82030b240d0b000080420408000340e80141c1080d1046917118000c403c02900d282c0d00490f0102d88a5003000c44484541846900303540544444032076035861120340c2e02c82c400007908500300b900105500d604c2c110b0a04107007409001c2c01010913584e40a9850940703c006010b4400744403099003040a14410440c40542c00104160b0181d444a5220ba40740780e54042c0e103403100300d025101d0394008400010710981c459950303c03200e008002c3c160f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270044028 1250 270042778 270042781
    0x402120d02030d061703120901020910090510090f060507020103140906100602061605092d0f030f0705010509010917061602060f0c1b01060b04050a1a0a08070c0503070b040308 77
    0xe4180d204911704a01c00b9178000c0c4408044120b00109441d440986400014201069480082e000b140f040c015207000c91038194050189043c1006c40e41038004441c2440079040d440e2100a004040300c52264204100000ca010300440e0310030741081c0b900010f200c0c03c076401820143c0d452503c0340000d54003485100c030445000502d590011500f03500c901d001c10011481c5101007941030302d642d480382d508540d011110022610382200d40300c2d00c2e60f144a03446202a0441d10f1600240211a4940d400301131181d072044509080c8110001703031520960303a080c40e003240c030707195a000140c400e0041c580001004d140700c10065010030303000146141c440e5030310104090140700340c2036090780c5414064136080b910041140008003e558640d008048540320036010032101c600c3d169406003100e200303410100140c480040c08000a00d44449442e0107401141400c407504010384021003840d200e44d07040c00c8248125a000603640b42d002e049081c4095030803409a0382c1e600f0700361a200c8050b0104407421400f0829000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270045278 1250 270044028 270044039
    0x50c011e02092806210c030516140d021b120c1006030308060d080d06060507150e030711130501030614011401020d0c1b060c20090f0402120d02030d06 66
    0x3c80e07660001c644100d90000d604103102240c140d10190b640d841c00fa40c91408008220b281c0340304044180d00555000074007400c6c00d8001800124500306840308000c5008515444240840115003841031104070042c2d036031000700c2003c804011004c852000074054040201035000301d41c001001c40d030020a0070f07604003144482d02c00088070894003006d80083c59010004565007040c1c82c0c183c0005004200503403d0030f00c40f45103d8141c9a02d0b400502c0000c0300810751200704650f801d50172682c544100028400c201c50001000e07038902940102130094a0400071109941d164002d504074a44d1806074180000d42c1c5904058016004e01141e464032101e03a04000510503803040d00719581460305034081c01350805941f03030490328200031b01030560300c818050171610900c0f0b8403d0001001000551141c0f29550402d01b08410110790406051380070a24244609415641d44003010f0390109032681d08100540311400800e490000401322199a0311800d06c2c4000203940007c068500c1c2810340b40c0502c4a147c449 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270046528 1250 270045278 270045319
    0x91e0a0f05151b0f0a020c040c030c110708061f030b040b04020f0a0602061519030c030201120c081b0d110405120a0503032e09060f0605130501050c011e0209 69
    0x4000c1c04188401c2404013042d41049800203081002d018030480d00400c80c100c000500f1031348001c0212000c01c0d42d4010a90100c1e0300010070f44000c82110f0041d140540c43d202c0c1c92a1184001010b002d0a4450b4a8107020400030ba124404091600100c2d003800340d182c00e00c2c1444440b0800c0e82c040c1e210b5542c0084148080c03a10406c240280c441c1d13540541120b071241118200b11038075420640b0347c4844070701d80c00da01310019104258025402140384201c540c0c55400003511044403041c40c001e070b03039080120380c081032500501e1040e0021f003e550340903030600f042d1120411354090001443e60a070b060003c0c0d0300115002c0d2025100380c0300100c40301440002801c1180e99108004c1000400d141c00510004501c4410174882c421480c1151941121918403800c100101501c0c40d04030410403555108140070340b014481042001e840541403c0e440c15403403618030f0b08007810501c12241009400599040f5880007074020040040c0498492411048002c5500029400800717145010f802844040541e03201311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270047778 1250 270046528 270046561
    0x30d050915010503240a020c0a08092e0503060d050d030605040c0302040e0c030612030301060c0317060102060a0f020906040b1801090f0b0702010318050a0b010e091e0a0f0515 77
    0x102130790030580703c0c40300e000c85e180380040901110036401d0040b100019400c2c440313410890b2144038007550700c0e1080d00400c14105401a88042c0b002d0044042c06403030b001030082020b40590387c0c100f940d00c0b80c0d655000180d80d1500e8140040071070040340c8061400a4064000400707890b400c85041c0701265100d1003c6007240200d10800200e400703ea0b0218015195020080d50492000791030b210032000191003252035036200307078403040018068503c01d1090640c001510700b1050f98403400031800b404c2c0500003d50b0b0340b0024003543d1030350366100c10080c21070302d495044038100c0d0800380a0170740720380c0d5420b403a0515810941240326072000300c0c0026a01584641102000d465203c403022001070b040900d00c4015400c0120102e042c140d41e802c400c5200b540002c0c000701403511502c01408460281c0c40d08102200041c5d01c89444403c081e400d0068044012400c2c0b001861140c41d21030036001c609119518110207a400681084800c004500a011010070110100c01b10001443d8054994140510320304c0e04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270049028 1250 270047778 270047803
    0x402031c0e090a0e06010b220b03010612060302030105090a06150501020601260a150c0f050d0905011409030408120309030f03040f15050118090f02010e03030d050915010503 76
    0x144a40310a1640c80d02c00d04558010301200c070001008644040a545401350a8012a6241d400454400c00b02604811046a04601100160503051410312140e540c0d0006000341424842201c455030981c070903e9100d00c2c001c54004000b40810b0801e40b29507500c82c00001d00075a202420003010300f042d0003c3c80c2c1c1c2a0201c07070701079000704020303842c1184040d9010070743c000306207101d4031451810301c00340420807207080b110f80070b12080e208045195203004211512740420409100000c100444001c2d0000c0688800100044012410b44030030b241043c010070a0464000340c81004400b0310802ca64000082c1c8107841c8681c5c01c0310300e4540e090080d0751082c081140c40b40c805510804c680702c1103070f5603031002c1e5802600c140c12401d4113030100d40d600441c525038115400100c41e51f42c00100312510405804080010b40300a081150071010f407030f6880182900310000e030500505594000064400304212410a283e014003007203281082941c1c1520b50701500c0c0c0d824034001003c0008038440c03a002c60217496501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270050278 1250 270049028 270049037
    0x14040b010c0506010e0601050708130f080a12050c0f030708030a060f08071203050408010507030e1002072f09040605010302010306060509030a0311010216050c030613120c0f14060402031c 82
    0xe107040341180608030000e0046e81080170a00c800d100169a80b4041e00d062440c404040600700d050042c000d0300d611280c3e202034072551004108801207190902234103411170507407030250ba55990f0550803503d0420740c040c40100398800051020b06201c44440918054454040107011017650303000c02c044182c0550080c100d0795040400f0800c401804a0004001127121781403242c00c00c2d540d96000c508482040f18240d020984414140c2e00c1444103010a02d441e8441030411420442541c07a11010f03e040c10070399400074100710004225202e00113818921034440140031008916113890044003600e000c0c401240440c0c01e0050204001d03019400383d03908110050000c010034062520301b1658070039040907400d0070355400c12201012041040665080c07d000350001c1c42d80324800814186400d100406031034400084441a900145a0140b950702c00c484520b00000b04144a08041007441130100d80148000803401c01c00031001408280103204500031420750f0f2032011901d1064030304c07107801551880001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270051528 1250 270050278 270050281
    0x4060b040b0a050a0905120607030f060b0406110a0209040f0b061807030507170109061e060504121a0a0506040b010e0319080f0406050c0607020a080702090a02090a14040b010c0506 79
    0x1984503c020b0100d60a191401e6152199140042440b4200100c400301e440d4201000304440c290301740c0161805503041e602c080220515010071850385001d01d001d001d0812501000070103c0701d0080201d620441d4009008920b54105880c040b010915002d00458080c600d030000295280343c582d04c001000e80124402c1c074950750383d2403c101c00901e001051182881600c1d02280d00308010700c1500c6028140c00b00c0c2c0011450308282642400240e0000c0c1ca254500c0d00c0352080c400e1980c84802e45d0b0454440000301c28640010345001d030b070710700c9a0a1480b44140801401c000b20011907030001400340e9000da034100300400100004440000000d03001d0f54150b0b0040c0c111003880007001f810041d8080c06280024100308558821120340c0c1c2c13140d40100c000602c0404c00e00d4541500b444030b56000801d50008040e0809503650709001400703074400203845691502c000038a01d44d140d404a0300d20441c01000c8808840e00d6480c56120f0042400307255020707502d09003060301254000d902003800560450000c1943d0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270052778 1250 270051528 270051547
    0x250c0209070c021c03020f01180c050103110d1e0f330e0405030d0509030c2805010f0510091a12160f0503160621060f08030904060b040b 60
    0x3200a5001c103d0300964048000201c0107591300300c00c800366119501a010b00c410b1380b4055429180d8152041c01c0740310b06454803c001425040084088440a0030086551380c0c01c429072641d035000f0700114510207070902c01103d202e0002c052840ea09640100c204104030105c014408084401c8c0fa40460560011141c00ba502c541c0083c5642c0251020809601c1c0410740313554000004c0c2109a5023214258000320300291a0f82003805241e500801e548002d506200035800380554415907007891400c0d040300b24001048010300c3c0c1e101819001c0c3c00500901103d18030307a8042008280403a68501c99040d80d402c0403c12507014040d101402106500c0940800241c40c1009444c03098100344011900c10400b213007205100c001c008000410300e811b510f080307592400f002c0c1402c040c144103007080c1c152f60240040c01855044080c0403e0300500e54400c49002e49080c034184000c0c000d03a00900691142032400244a010000080928480a8030103000e840c0e628121a03405004900609541d0402445134030f10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270054028 1250 270052778 270052787
    0x1e062d0915020406030212010e071d011707121b0f03180f12020d050703170723040611010c0206010506220b12071706190905250c020907 60
    0x100340524284001c40c461454540c0403a80030307900080c003003078001c10040c40d042c010819a0780100b040000c1c01d090b40c900104000d000c031600b43c218650220100640da14964455440c0c4c1f010000c100d40e6290301420010301c040c1030512000046040141040c0c140c1c55a0030a00c940050a03501c152611500c444403182d041d030242865141015180100c2030340c03400070a5072220780d54420b84c01410b040040100b00e1100078200b800b000d20034800d010041180d04002a4481015030040b11803051846950716410803c4681002d0581034816101e2000091303088803200c00010811030380582c0307541c15445002141903098031107800598025070000401040030703007044d030f000b040e00750b1040b2540e0a0359000d4030103d642010694200b031100001c040745840900b4000307aa61a08176803641001010480c0003a40080501401080700e4041c55403880702003801000c1d40400009400090300034001468034440040070301c0c0e03140605448a90f086241d90114038092000c0150082e0043c005e039003c2d40d00c000d0b0035213 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270055278 1250 270054028 270054041
    0x1119030e060c0a080c0f04050d0302010b12011b2609120f030f070c0506061216030f1703090316080c030a020705010908030c1c0c1e062d 60
    0x405058440c10160026203051001512840b00c0303070442625a049a44014000c44c0300401d00103892500300710506215144405840481d401201c9141c0c05150502d001c070301400e80c3c541d1039900300035200107140e10900c064110210780306200c01e100c41c007802689400c844020f10001c0c103901c200944a200c0030340e88074501c0420303444105801202d10032040d126504070158440c14210030800c41c0402400228151100302c507411029030b143c2002c8100864990540303c1c0405090103224002c0907200e0307542ca142c280b0143c682c04880740054100d01e039580c10481c58204068408a800e16040390650441d030901c6400d803806a1058001141400300071541030900c000c1400301951011024000034030304100801c010320401d2010f80c00f42450398a000700151045106401100d0540c00511115002110002e00d43c17603d041391344d0b000c030741e4240c000718142c440120801d0701401c1122070900f4841002829006d204209104000800c00303009901480c46055000e01000144c0c1c489002c14a10707074512641000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270056528 1250 270055278 270055327
    0x809040e15010803030103031706010f082d0103060b0d08030a05060118240905030c0d11101d06070b010b07022206030507050a060e060c1203041406060411 68
    0x3035a402101240207032800909902500442d840000103004250380103981015040001c501c8141a003403400001e0104c50502551604002c030210000f184005090420403647c04410b211041e15160148120140e03d02400203a03040c50900c80b0350241410004150030240ba0000041c1d400c0d80c0344d01c42c908002d010040c00940c104543d4088212100a41c06161001051107900520507042c1c403801841c00c114103410003c0600c074130024200100e490200b0b50b800d41c1001242c00b0041d05540e480c010701a40307070304031240d904140141c10640c45103811810014141100700c6201035500c0d000750070070150784140080100206043c5004000074000c08000c3c00881d0701c010018502900300081509403601040c12403c3c2940e01c2d16410403d02005000500c0a80401d40324084803134182103020382070b100301d2003420b40030f0440020384025594041c81400381c0c5c0c0c00e003080c0080d03481c201030501c04081350581c0c1d015902c9001c0c03100822280c4c601071091600783c00a01c00314904020040211652414000a90 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270057778 1250 270056528 270056533
    0x90a17010f02120405150402031b040213030c0e1320040f1401050a1a03010501110a141f150b09010203040509010f08390f0d03090302030f010204030809040e 69
    0x8280540c1c40c0350002d03100c44044a00d446590703142a040c400c0c5011450b0f031205203241d00e101c05000c05071310003040403400340028070407044900c4100000309009214000916010b403120071004010030000344444411502a40c1307055a03245c5070000e50304400b0400400041c81c80c401000030803000802e4000c440322034030000700001002074440030440705580308004002c908004440043c0501d2801018540103860042c0b0044460213005441e184a880103000d12814001081c070340b199040c60030042412101c0d0310000410600d03948140083c1d80300b41351aa01403001040e08083e020700b01c190320940d0303840001c3d000d80072244d5151a11404103640107031002e5046010803c404603007510f42e410b07003600070031200144042880c6808982400c1013414904140f05555001100c40900540991390b00c60303101d01541c1403400740011000418100c01400303030300d8104250f41d05090038141c004e007806081b00d000744c058a91840340161000e0803403085001c01801d80c0000c0c8501c49050509602612018024408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270059028 1250 270057778 270057791
    0x406020c04181a06150a0806091b070501050a0b0f0d1203021e0c010b060304030815030106031208090c060c0a0b060a08071710110703030222120b0903090a1701 70
    0x3d41d140c00a01c42a180000c129010042c05540d062422402422440360380395a81405081c1340014422200034000f1486100c2e0800070400700c200e03141b05080350140880e00b15681c0c0510b490040d000c0d00c0211040407480f46072544041c0d06040001581250120042c000202c10b203460b0707285440d9541c42a145c000301a0f0030f00c86d5510103480c01504141c10f00d80d0a01305030b190303100d6051260945001004403030045806005010000c0d4010110756004051001810142382d540808240180103035030029000656020107082c0c80d541180b40799001d9020142565010940101802a640314110440516500000c2010081014001010b81100703001707048210003940c0b403072440d142074810341004103100080e580e80c541000342002104140031440c40c0c24021020703003120749030301400340a40280074940c001406400340500c0020000d048256400103100303d42c2c403240f018900c290780c0d890480b2910340710808a401440d0010944010100042000366114104414026154503c1208200075900c918 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270060278 1250 270059028 270059033
    0xe060a032a0908060a09111c080301090506090a0c050a0e010201090209010e010513090c05090a090b010f080d0201050c2d391c09050d050f01060503030406020c0418 72
    0x30a55054951556402c00550400c4843d500700300004d001e00c224140f81450080000e0500e0000c4401144200c0380da071181c42041055148420f40100020040c081c000700105040507940e000074000d15064030070380010740e512030400e81100c0c10115000d010400034001103412902c0313003000c155074030418800494410100ea010909030042a0400215000000014085410507403a9580d055020b00c0062243e0b9056403502c0c40d20103041d0140d2401100755500040314514582c206544503a8041d100800035079465404802c810042d000c4c0c2120780c01441c0785807001c075105000307960240d454204e4007450200d503c40c0c011341807500003070b0104454603040c02207035040e48040081d181082c1814105c02c83c0c002c509040c22903400c2a880c0280341c04850070260f0802e0000000c035142c1c000c00040011212250b445000e8a00064a034002903101ca42d195410381048000b203610021040060000e2100a0701d9400305601ea00071070080000503445080d5000080ca00354001e0f2500400202035036280b01c1094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270061528 1250 270060278 270060341
    0x30c0d1b05180f220b04080f03040b0603010f2d06080d050c01060609060c02090603331303050304260a030c09080102031005040b06191706010e060a03 66
    0x34004110098040b0801002194145505a1120290b0007503043c03100c0c140744c4400050020030f0090181c580c07100000f0704105141c3c04440344010300041280e142c1c6020325200ca007a100486450f0300a50900182002c00002c0c1c0c001c01c00310020034141d045103104107800c0d106082c0901480040c0c026200c5200240d40403050045c00ca0002882d944c9a56034220365a0b15402d4442c50740c0560100802d0b50000c014546d8401940c690483c2e04a840c41078640700d107800240380071002400d90703098280f019003200752146030760305100c00f0368174840099416a84240f403010b0f0024118201402040e020000180010040c064502210444a450038030703014030912041115009030703180b42e011070703914000c40022641000b8200d0003808144000d40c518900703401d010000745090300c2060f02490325614444030540d00d90b81034440c41224000198006601d0f9200280b0607140c899110030124a100c1c0800c2242d44544a0700081c540d024100034588050401e080b001004c1440722001905158200d413503c09205 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270062778 1250 270061528 270061549
    0x81e0304050a1b030317040f12020304060e06090102030f0f07050a2a05031c030f02030f0f0109020720030c0904032624010207120507090b030c0d1b05 66
    0x74000914018001d89800380d03016050440d1241e0301807881c00200002070b848a4038103640c18414403008505e8940d8900644d082807064001801e9201900fa5811419800805002207032030a5135440e04250400c2e06002407031103820741d2140141c000f0401c2c0e80c14401c4400c000d003081138180e98150701d0590700381c0311203003044980311085540341840641c00865480d080140e41c441c0c0849010a040d00d450300001903980c110303642030b14400f08145006040203a00039845003102c01d1000005640c0d901d031601c0f0024002504a60341c4c2d441c07401e1140007080b400c0c2c152080c2d4800d154800c1f0005c921003d071664000302041c40008066051041d00c9014550751120703071406008074820f44a42d00c110b000c841c1040e00c5c614030780f00c0d000f2500f048241041014000e44804905056017582c44420b071806400c0100c0c1032946d9900b0001a80503010701010070014005680c1d403c454402d6010807010101004158840340400e4030705501444003110100030500c070110264601c0030300311185213000e5403180071881c070088 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270064028 1250 270062778 270062783
    0x203060a1a1902062404061a040303020d0212070b0a0618050f0115090b130509010f0305010c05040302090f220c0905010602120f090a091a010306060e0a03081e0304 72
    0x320340a9140d200140c07204950b4030080c00640107a182848809880300e0201c404000d0b8443c070300648915544442c7c0c00140903240803200c400300207000c16410f546542c090300c0101c0042c0708501081c03074081d101007031038104c0b140503290503490301c6a5920707011003108025100300b1485c4c0d40c41c000050300702003138010400c000c1c0141c0c8000c00c1a14081c0c801070134050059002d01d1980c00d441c8035451040d0350007030b1500c05450305007412603100d4490720a910380e1407074a90402508a40c136440041148400c48074568102e0344510000e001092801408440358082e61000130340103400000400d24803031800b8000356002d401d83c01c0504170340400c1d1740c0031500000022170617a00c5503092001403200d150280980b501400300790000307103030214404014500724403d141041315002004502c000f0f40ea80c50007103080c0101103645003400342d240611219a10f4484010300940864604003001a0300ba0284024850304240104030004071851901c84441540c4800801002095030056400071141e102c005940a01e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270065278 1250 270064028 270064079
    0x212006040e0114091f06180305061e07030209060412020301090b0711070b030112080d0e0a140c0307030201021b0d140102090112021305040c0c0212010e0c010c0f060203060a 76
    0xa0b041c0300307120402c00040e00c680300d009800444900380010b004d003403c007220600e180842e03680c47c3d08109410f40003895000109980503200501440743d440320304049102c0044901c06c0201d46407480190100d108000440780c00c25001d100803c00d19001d44e4040750b40c0c0e0300107000410a02e085a4070140320310001c030380140203c1c06103403100900180800000c0c000c0c0c031080e641145594102076803c1003580c40341d03030024640c51000441c84030003075142c0c101d19466040c06084614041c56890145000b00c00d00001120600c10020944614527001601e50116501030700a40b080d40c40050003003540803081d141058002c4484003803540054000071941031301240301000181c480f0900000180009046ca0300d00090074010700c90143e068041c0c4110303e0032550704850001d2410f96101c000e452052404d080a5807001035a33004045220040d08803090b0502030030244d61040b0001030054030b446559030409071503160300c04400d00005035150300170764000e00d0007130090b6500b41d5205090f081442200705490b41e00d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270066528 1250 270065278 270065309
    0x10e0d021006050f06040302040506061605060a0b04090c05101b0f02360402121f1b140c0c03030a090305010b0108220213090309212006040e01 63
    0x8802510a0002402c422a10b04d1800580301c40098154066404003030704c075543d0380f0041102070755035070308840858046403103d00c0c14280381d09010341c9460302160059030b440c1c207064800c000d034601441414036059008080c92049401cac01d0510821800c0c14407e0070502451a40c0b103882c07800620024401340d40305800e41c0c40014424414441000d41901c1071222031009540c070b45081d09850b80c00859055240e41e2000d04a039202c0c00050304294010358220098000c0e41d50300c0065040b440c4802030003001d8400e003402900d5030481c5000c0c0c04510018440b00041b0506030302e0b500c040c01c0c0030081429400c0d010480300315417110000642194401803030400403601c005010400c102d02809042040d14090a0164603894021300740f082c1100ca06100302d41a022041c0b000c001c40d40d03405c2402054042d402c10030810140c151034080c01c07030300d00740c0034100881c400308403602a24800b4151500c0d06035070020300a1a40408120104907080b2003a01c5c199010a043c000030a2004040c4003650003403102042d41c1810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270067778 1250 270066528 270066553
    0xd0603050715090f150c02040501030308060306061507200910090e030a05091210110c1c1718010203251e0c031704080c1203061e03010e0d02 62
    0x38000b41400c240512500b8041009984105034141080710b40f0226903001e02d483c040000c0350800d0541c0002503001e49030000100905a112404074421101036080794519204d03042044a1078162145040b210002001200300140303441031165a64409201228417403030001c40050001351044480369028000700300100701c0c605081c0104404162508080c502d0030800940c014010b1080f0084940950b60301c1c860b02c51621010851428415810301040040c4800c0e0410103255a20500d40c00c5041d00c40c1d02c0b00354041c100940b008080101480d100d000988088003418016000c1c020030144401c02096880c130320344c95080c00118402c0c084c21034171070400c0e810b12042e4030020140c0a036150401650003d2032801029103018441d00a440341000c602145843c90115031554148040b03016006c0d030181844100706c0c0c5000641042c100e00c0c5d0540c1e01c0800111043c8646020448800f90310142c3c59400302d11018200c8101e994030b0340080e00100b0400b90b008071080c40d125035041c45000503800101078505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270069028 1250 270067778 270067799
    0x3120a020d08010e06040e030d0905010c1205060d320a0b070e030a15150e101a0403080703260f1e0a0c030b030d030504020a0e0106050d0f020d06030507 67
    0xc0c49485007480107080d418804402c3c12644000c00f05c500480e607542150400c01c8041083c1c0b0b6018408460600c61107071107180450213081c145c40c0080c0811150300802103500b405000b40c500c09c00c005000d480307415400c0d032114102c00742030f0105414000103007400d0a00724901e208641c60007560140081125055034a01b40c07150740c200a000004120b03058854000664001c1050131582d5008000c180c18603820b2132140004007403005461940f00d080300c000041e02640c114000344580c82c0030092010a030303507030171103131f126034004244544110104120500020f880307500500301c014024644000d40d59080d4143d50b11765040300c070039003500c0181e0404100a551000d40e030300d40d200387e0002040315200341c0d6141c83e9401c0b91024104010241c1c54071054401203110f80d11090b402403008084a050284080700074006044c1134030164040d040c260004180c800603903158130304a0380260f03501c03403402d00c01400ca00000c00c0005154050713141c0030003614043c1c61180c016903024500070030290109900e031409100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270070278 1250 270069028 270069043
    0x30f030e180f060904051906150e0613090c09020c030306030708030a0f03110c070609060905031b09100503121209062e0308040b0304260306010e06040503120a02 71
    0x5660800002c101c2c0e100d10038899140c100c0c0040d40c43c40b0070354680f450f1050600300b0840740c003030f00c07403041032034610038084543c10429844100c440c0100d400303521051040b1148800300c0d98250011a600c4403280c66182caa80240d4091b070042c1c140800b4140c0311000e003c142d0707200c907a010166901c0481400981d02d810300c078000041840c06c2c019880c28201c0c0c2405002003880e52400024199904081c8540241d00c104442000032a0000d8900440d00c5001c06081e03142207004000001d100c080c40428103080004010844040c00b1480c1a1308034002c030700300501da1000501410405034608000502c0c0e450401c10040390a142c20006070710742e96003804171401100014010a0140d01542c00e0081c0006075034400e0004e05c0c07064018103a02c055205090b440c11580d640010310240c400180010141d4580c2c000d58010784c807804101074045c0c14140c00c1580760b03d030556001d80300b80040012030101d60050f4620076020501a00e294180340d900c0340040d0038074a4048541d240003800145020b82a42c0c14800783c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270071528 1250 270070278 270070309
    0x31314030c2d0a0305030c0106060f02071a0903030702030708030315011e0324060903031e080115090e0a150e01030803060108061305070c1b0e150406030f030e 70
    0x22000904155100c92100c40031403504440d100d0754100685542c890f0f4a020010b15040821240c1e070b600340d000300354000c010f0780c4140f000085c005818035185500c040783c00411650146c60141091352110000da4569100d080c2142e450301c0104001c078016101805000000c06100c40035540b02c0c900101c40d034440b4900001001c0c10030040401c030918180c8840450b000018451800143c41d000e566142c0104262007009602d204090100000e40d01d903121080b08107603880ba903540703001c10090b04d409090403500e000708000841c10541c010301c12085240e103440d0038045546010708080c3e43c2e4241e6030315062000d65074920300c10b0b19016485803040e803544152000346060201d00701103601d1030f01e4400040c0000303007003075040003107900100c2d0080d039404454024002d00098104400e0501400181c40d054045100703c40d001c26941c0d0140c02e182c200603044013114013611303070040c0c2903485509000c0c0c071001080f0a507900980d9440c01101007403054a102d46000d109803600c2d09000700860130402c40340a43d1411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270072778 1250 270071528 270071539
    0x60a0501061e09030b100e04060f0c2d05160501060e100f0e1b030106030515040e0a0807021504120318031a04061409011401080f06060909031314030c 66
    0x2d82e6880e80c0b018028003160b422488068403a120812900f1034071b81994002d490038a42035040c442800f4296010304901520b041e400c100490038030b1003c1e1100c1814000480c0051501407540383c0d41354105031510351400c600d2401c00d01d0665100b12701e00960341041015582a90355050038440924041c0c0c8181d007001915011034030181c5032400401c000c1ba114050050a42103102c0441c80100030303150b08101b50122010700e10b40303030f42e101c800040c0142011036484905000d07120600d101810148a40c0b695160b1800c003401410b001030301c0d244000c0c1d1040000700d030040d005005012000e103080c0c02a02c060043c82003040700000480c207001b03040c595030410100c00600c0d0050200b0000315032042c20240024502043d03000ca41c1d0702c0c20480300500102c05d8050b6122042000c0205100042d449012417080140d1a010307242d1300c42c04981d40d40c0003c0d104050702640204c010980c0b52420042c0e1070351201029085030701e0703c1403d008899102c160f5600611081e401800c10752100c0c81e045c8a258078038030083c0c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270074028 1250 270072778 270072827
    0x409150e1b100f020a0f030e04050f0c0405010c02180109090311010e03030a05040602070c0303021612050303010501030504140a0f1205180f0409051b09010501020303070e01030b12060a050106 84
    0xd502c0c0e580510100041c407414245038601c80c0e0090000c400c1607900500ca5030014980da0070042c01e51030b007200c12144070741e1601000034a9203039400c852500915800405034107007800d080054498101d03100c0240c0e4001154060350b142c000650080038080c10343c0240100308800b15290141054491098964036a4180300102c9001ca10001c25694441c0401c48041180e8070f0710305096000f84240c00c0c0180ca2000c1c102c07404014035400155a6692940404905040b59076451075040614505a4010100d801c104010406507200b0b8000907081400b506100700e07095641d19109103480e080d00b00803115042081600000d10101e0701c410584201d0604209207450081d01c4520742c1951a900114400c2c4d8100680d14010349480d40000003080e440000c0302c050700081032809460300003802849118490b00b00000c03400d540f000c01924010022074840008042840b401940580001d40d0030340c1c0c203c1c50788502c48806a40801040340280070606c0d000850354140f0750020b046040d4584070ba0b68583d0040c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270075278 1250 270074028 270074083
    0x2130806060618040b0d0803090105010602070506040f030f11060c0c0f060316200d080603010b01050c070603020702061215040609061d0a0e0a050304060216050d020d020409150e 78
    0xf442c08003044800c40d00081d03045510000034104180c07422014280c914084104074508030705501203030684890f034080324404c51b6140204076881c401d5000740c41c2e080c1480d900410004101044a0b0861403107541c0d0300f07584c0414400070991030b41180ca0385161660100390b02075100c1c1400024510714880c207943c8540b540c030f4601440700c0d032140402110020400c03e0020481c03d040c50000001902c81c030b4000b580c82c021050000140744c01420741e0114840c2d441c01a8000b0f1660203603003200c042e26817010203805c1252901009500940280700c0c10b9170058801c004051034000e0a2141a02c0780710407155680c0710300700003c00e0000701e5030650000d404052412034103003c030300441205007000c030155818502d800d9555005450283c01729564442d62442a0003000081090200262007595219802c48010020b20554030324141d03242d10400c0d4000880001100140c02c241002610190010f0300204010405030b17603a4000754a211000501550740703068903a2003440030311503190003900d40024100401e07500c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270076528 1250 270075278 270075307
    0x3030c1805130b04020a021501050405010303170a060305100204030b0f010b0d0b0f042c0d0c030e010302090d0308150d1a040203070e01091406061606020c010609021308060606 77
    0x20700070303184580c1840342040d022500541102d141c04602030425900c2d100c0316038010350b94441c84d514840200b81c009001083c68100783c4503403030480b0b406554100ca07010681d060307200758840180c900016a80c6a0401102141c010001003401c8904040c0060b91585076003841d1080c03210241c100a081180c0000400030002464250303140c1525803800017400c02e001c0700000d0f400d44081c081040d00141804100c030303928002c801982420003030854101030115024003805840da82c030601c0c040c001c1541d0300004804288035411503903000d1018140185080c40610020309a001d44500840003d0050010080389031000311030210070f49410b64104403d25055a038013078401c0000303106807401c100b5800c0082c00390741d410480308005104080900405503160031261000d042c10440e405030004202c400300d45242420320072500340c44c07070f0074083c03411140d0b0603074580f40030b0f600400c0351840c0c40d0f4070344101003121607242c8000c2c0300380b1290913080f00495140c98032403410700b20000d2010740b06110901244041c801e90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270077778 1250 270076528 270076577
    0x2070e0112030207140a1a040305120a0801031b0306050f0601030e07081e12220609050609130b030106120c14061c06090c0203031f061d040b040e0a03030c 68
    0x145105c072107103a4a41011500d0314189600080070003504940325007004034007800074000d50740500141c0e01c0070030511100ca407032803083c4080040003a450f6801007000ca4001941c1c00103a41e0030880e000001c2e43d40e85c0713550090350300589a115501c01180c003488865a054401c4030217206002c0301816242d8074080701d041d2142400e500350749500010006e680d01e0b00d0000e20080789015030f8518200c0d01c0c2c2d980c4041c4c68100f6030703404050b4840102c0c00b12011032124090a001c03011201e0050003276140020030001d20002213203842c1c698060540750a00a98155000c3c041d0902801280d00d4520f2942c200d82001201c0041c03039401440c0b01540c6070118130706600d841d0119540150403407075583c01c29020240500080038103500049082d450009004a4158048021406075035190b810b008022000000941424140c2c8119000309170388013070b2203120400701412131806000041002410306032a50114054800c11020300000d6042050300c50b0030181c151040901d0101e40e86005480845102c2c021f941c03202c070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270079028 1250 270077778 270077789
    0xf08030d0209060903011e06050f0d15091221110307110a0c0f050906010305070210091e06020a02150610030509032106040e03130e220302070e0112030207 68
    0x80010382c0000c0c54554074215484648003800070402c08001d03d142c0308032100705034000021541021030009240c644000c501e070012000070700c1e48168003541c0d610241142e141d800c540f54807036140d040800c0400d541c0702c0100b540702c4c40c0d6110a82120002c448080450300a800038581c00e5140c01107041114621000b50395100006081c950715080e090080b0500c0e207030312010002c0694070030000120ba11802c20103d00c04440060301e1481d001d88070000103406542c0211040b000681c846107001c4000c003e66005004c03490301035410b091096507940c100400500303401005450711a0001040004181e040000c422685c0c42e00d5074030a5982000c80c006544a1407440d09030040540303400c08644040003e000f03c4203403030000448464405075813030540d40c0c00d2170700b100c81e1803241d40b5044c0030071102c2101004a80d17039040b480c03c88140840c205241040044c401400c102146060203980f03101045940782d250100502a8004204061900c2d1002c507503141c05801040c0580c89941c41c0e200001c6d00001d844c0103484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270080278 1250 270079028 270079031
    0x1b05010f172a031303030608010212040312020d0204091a011103190302040506130e0903070b19200405030106051f0e1215090d0c02060f0c0a2108010f08030d 69
    0x40702030b01c08032030720004070040c2c0c98840004280210f544461052a0341c807403281d00c0a03c6038075910410b0500300c1c002c2d4010180100b0700d03580000c0c0028429402070792140c20103c0c0050030069006881d60480e0015000310030700958881030350403048100108030b5880102441c02e64040301c12440712548074018402201900d0b202e41170130014544c02501664003030080501000d81b03c80500b41c0c46200c2c09014407480302d032001e400c00403401c0c1c2e8201204443d00f0030381000c400011526000500b0000580e082281e840e031640c0d030a0300c001d1001c03100501c000c6036490080501e4441e41060201800c4401c21382c0308510070030b0810b0300340d0360b04001c6071041e8035110340c113013011a070480b810004682c0310b0b24102c46001c4240501580d0003038074408202e8460041c2c424104540c0da5a548180c00d0758152085800658000020310000c1600d890354002046e401c0904001da456510b0203646a81c1d407415148010303c1701c0d45091801443c0c00340d001090900500000d0441241d2500d04134110783c603449014145807005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270081528 1250 270080278 270080311
    0x30b060a1d0402120d0e06090402070203241014010e180a0f240e0a090209010e0405060a0539030702070501023304030c1b05010f17 58
    0x1580c400000000418046801c810300e8182100056059401110101d100d601d102502c0c040d07024000540030801209500c03810f414960010800880f50028030503603078065002c20054005032428408602900d080c88542e0301d080d00c294100c1016040000e200c05056500e011040100e00515916110030b241c00382407010342c82d8484408a1100c20042000004402c000d0b030501403441400c1d4404040a41c5500003046a0882c90169080d41c9084200440c0203500000d03090221006240700f071a00602d900d440000d232040e040d8003090303484409034420510054840100001d0060500c4490b80c0409001d00030411490b02200e10074218002c0c210030100420f420b2062000607001ca440f8128100701403030016141e01e420000203656000c580581030060150b02c0c100c14401c50b010f4840308014109148414000a59090f400c1240c140100181c0400002502400c04113403a00624201500ba00902500c490301741400544410b00d80f4020000308428107800c4140d2101d5603070040e8200b0844503184042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270082778 1250 270081528 270081541
    0x12020d021c17130f080307030f09020f0907090e0408072901030816060906021308150c0f2a01050606130306020901021c0e0108060915130f060815061504030b 69
    0x14203c030100010040b2580002032010700c0039a0700074602c1004182d8061169104c0002c0d2001681d1808500942003070b4014481000c138940521002e82c8417050340740641050741e95000030f070340c101030981c0c041c1c07800440000d02c0e409000c01403c03d02000b840c1c4100b89640003001d04100214290140310103000d805000ca5250129105d2410803800306820400074440d80340c103820180c00950204000c0803502401d85d0300042c1c1c0742c2022600100504504441101603521440d03030101543c03080071b01c0001c00004003c1141d60701c24021498182604c15405910801c0c0e400c04845d00b1a04081c08841c480c0200b8090002005a465031031000d4940c420340c0540c440401d400180e180c0f41d01c203030200c0309011100d0400c03a56582d001d03038000350400702647e403548a600c500080c0021460140d4005850340c042410b52516410810b5010300541007548000500f00ca07142c41280844400d41c100541507008941d90301107490b80030700e115821010444034250869084d618444191050741f01c02003500c100c4034002902c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270084028 1250 270082778 270082801
    0xa06271401120609150503010c0809190201020c0a080d0f02060c09011b2405011e1e0e07020f010b0f0d0318030b01060309032006011a0712020d021c17 66
    0xc144c0c607582800704c1084542d500c0e40110751401114081d48ca03214414400314415800240180201009413503a9083d20300351668030050340c10168158402d03521000344c41d803500e48660340104005009402e542c00381e5200144816900d011407011988030106001d410010081155175581007402d121151041c490b4844568040002000e03011102092461a1811f01c002c03030818180340e0800c041046a8070340c1c506034092010803400c040300c0c0036002003c2c86a820307405283da850b81c100700e0090054a660308102c1c80070107400c50302c4c400160003080c91503150040c00d0058000c02401100d124540e0702c0b0720008105918041d50700a81000121000541c18251036250800591b41041c0141c56641e110a8040d024003000c2a08a0002c1c4113a071400c0c46002110004042d000404006000540d1030041345220001c4101d10000c04484100520400940008800400021590050300440302505406401c08410070341e8180c0d03c08030340216179405580420b03402d0100a104c1c00c405c907540c60340300c007440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270085278 1250 270084028 270084041
    0x30f060b130303020706170f13050109082101180513060f06141f141204050706020d020a050309090a1112060915090402040207110a0627140112 63
    0xa44010001510307103888a40c03801410103407400398080340c20030740d40c0b01341c102d488400c00d5100713140024800000c07030b40703403080014040d42004c46801c032080000130580b543c07400c43d024003070111400700d00082d000a0502420041903a2000744609503c055807400701088151908034041d1541e4a507030b0400111b2070f00303080411344642c64110004100c580e1070005664020a150b000342190009050811501844c110100210f02c502c200e050000b41900b07510203495154400c1d100c400403604c144240304040f098016000e2295014100501029203031032006420407c2443c52401150000d6515002181c400012600c13040402d4410007402d940d1000110001d01409440300500d9800003240c0329243d084545450240c801161001c0143e11801a410180c488411509412010150000340903242c030f50301412089000d040c009846241040000e005d00400d9008017011418221051441c004140290300c0b030301e200300d196030290394202407034014070b0091040b0b078a04106040e007907142403401c241c0144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270086528 1250 270085278 270085289
    0xb0604201e070311060a0c053c03010f050d030f0804080f0406030518190b060d0b01030807060e0105040c03080a120f0605040f140615070b01030305070b0703060b0901030f06 76
    0x1a92588460f00d00104000d50441c0449440e104e02000306440700814846c100301c1c2a1f194603024500121503080e500d00440020140e0030004005962085610f0035030040d080e029090303c81113549604081c140840c080d00754102500802e80703101e00d42c00007500888400015100c50411200c981d480749040c4c1294440c84404c9940340801003400502d841d0076400040c015100c155050300000b1048075120359508182c5032507003660b00b11401400c00f184d0822040c9070000800380444180100300c0d01d560f018410203134802c40d80a100001d9a8091005c5031103503089000f1200c00902041c201030311500110036103808003402d1004000ba88951480c054400080001c0c000c00050000620100707100c001400c030345c45940d001d0742c14126200001c40607840307000c0c0c0c42000200046541e0700c4d05000c1c800400e081c1c08041d8000f44040020b640411110710a40e4000e601c00d6a401e0ba0302e1b03000785010501d10b04064100802d25090810a110440c89032080e40ea00c460207203000940344807603400c50405001c3c0395024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270087778 1250 270086528 270086587
    0x8040f060f0c030501030204241502010204080a030915260a020903061005240a0c0f050f030d06151d061b030903070617010302010e0409020613030b060420 68
    0x8003000303e415401c41030403680212420071600001d103085030100c011030309034000d10715182e5030b061001c0c014036007101c40a80c14600c0014140307a15140300c2032401c890850705030003043c01500308006001c05c2004418010410b45040c05400042c640241c00d503245c00e0307045000e895161000030390180d034035a064a482080c01012244c0c6401c06210703108000040340912070040c45100400071920343c1518458089514101c803043c0341071881707501104c580c000400d0481d00111f403000013a01160042142c107402441c220051503540300c4241d140c0080700d8803a48080b03420b2845c1c42c05c400c111a00925014551440828018141c1e030154002552900c00e0200351103411280401101050400101600c40c9900a07402c80f080551145025260ba5080840c0320307010b009210f00510040d40700d00914544410f01800101e02041e8030350000c0d032103804c4039090250512000c3d10801c14403a400d03100710741221050b00c041201c4005880d10300040001ca81c00e80300404400a00660300180c990900380084240e01da2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270089028 1250 270087778 270087791
    0xe0601121203020a0e1309140c091b13060513090b0904020130140609010f17010207060218150405010c260307050316090b03010302010c1401020408010f0608010c08040f060f 76
    0x10003008100c3c00c82d09660340201105102d4201c02300162a1a02402c024442d01c0380f81c0c0d80021100c0341011000945000c00800d22400740c8080c4411326060281c01c43e92141510b4421101039000f01d00c1c1a5444901124203084903000107403100044c05e40c02a8080c070745680c9001e180d0710f107641407500038045481c0b011072081d212204800c066101c4a03404020440030140c4d80c0b0740004004449000303008010b0043c0404c5e10400c01c0030070890550380034910802c000350516500d030b1242003c0346c1000540e4030200100344001c10742854000d04020000c980500c9185c1050304100008101c00c3d0800b000800200790402080c0007211030180200f0340f4688428226600d14201c24018840c1e04107442c3e01580c9010756949410082c0a840950262003070300d0390352030448c2c1c0b95030011a1059003500090703a12180341901000081802e00091020307003206c10000c038040b0407501d030800c100c0d40d15a00944d2680d143c52091090190b01024030382d00113400c082e449a26550600386074006010800c100e1110503d0b044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270090278 1250 270089028 270089059
    0x1f08010f2412060b0a060305060306090a030203030c090a030b04030c021206060d03050721020309100206090a02040207081201062a1703280e0601121203020a0e 70
    0x40216034810581202801819442541400e00c030041101c202100e40032000188110704140c0c4100600c0c90040710045032000031440814681041c9402600001e81c541081006030304040100c29041b1000c640280f444d501d140c1c038002d440b4003000c1d00c241c540c0742d40080d1280707a42e40d484070810040e58000c0d291a190b41090319014010000781c200490195850348491000d061010406030302c20781d0041c00011108009030340403580783d40142c9040350010000c45800182e200e405054405c4c10f05a50015580c0702100d8042050b11600080c2807011907101030b04101103c5000700341046034603816200036844101c030b441c19042d140607248803149888080800040d050350700058070000c01d113005008811041c00317a64004c07402d0035406c10113000180d0381e08c8440f920011840003154428881c40071404c41e011a1981c0104031503010000c0089503407a1025054503c1003403000c1030043c00200000c1603010401e80c0d840340c140d0b01c415030f0f0320305040d404100c2e614034501805c4400300a04d002490507042c1c0c2c00c8c05d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270091528 1250 270090278 270090281
    0x140a08010e0102090405070f1202030703020705100c020115050a0b07080408030f0a090b0301030f23120702120601060c12021203070f030c05090604030f0c03050a0308041a0615031f0801 81
    0x50500314032582c00e190201f12400c2c000c1c0a8081450b9480c1c1d9403185c6015003201281c044d44c4060000c01c1090f074200003410100703100f8440c0300c1c849114881c01146000b82d80d40024207554000c1032903002c59582d06803c1116944050201045540010752280c82d08010b080885071800340e60301c416610300000441e0911000b040d40141154030183e01c070781c040c0540b11542c1180c0e40c00240801007007450400c3c400004510303020b00c03c0300350250350030444001c0b00c0c42916090501030000c18410016401017100421403038042c01051f0301a0898005081940c03400d14000d011003855070000d0301d50078408041d80407030751007400015424107411000542d20b041480d401881d04070301d108000e0000b40780c89076803403115218104071130300b640380280702a080038110b403101942002000350403a011150141c00100150b400e0220f40030700750203a10351000074a4141041780150040101c07120f1403100302001c00165a5801c84100080700300c4e5100d441d240e5030303441d03549512540c0001002510b0010100c00240c8207205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270092778 1250 270091528 270091537
    0x705060403090e040b0112020d02040e0304050f030105220503090d0b16090b0405061605060403030b030d0306030203060c160b012408010311090714120a060806090601140a08010e0102 80
    0x41c0d81c42c80070386a594030342140300c003009030750013403007405040010401c0d04841581071101c1400100050403590a5500280484500616204003500081410030151130074843c41c4034050000e400074060f41c41c00705111a100080a0101d041121304581d43c8070600900308241c40d42414098a1324443c1d170f100d401d00700c400113000c8440f070524891050441c07040300d100d2500700c1c086076000d0341c403941003d0411080003402d820102151214090400b600000300c0c0702001020300560013601c000911050750011f140c280302007440d00000f0306080140c20001070301c0019445501c0500c007118541c070389150034160030241aa0003800303447d1810410001c203035945411700b0001c1d540c0b6105580c2054100b10b000a840c4614244000b0380054584140000281000100d07954056107070b00d0040c90854014524000c0c0d0b8100041c1405582c101004001d40b64007107114a5005d401000010821880d000905079503a8030b050183e0221501c1c402900c0300b280c0c40d80352060018089a200a221000c03100710018001d401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270094028 1250 270092778 270092783
    0x605090c120103030e150f09031c050313060204050618040e0d090306050a020c10020450030a0602190e1e030a060612050709180b0a0e010207050604 65
    0x14418042031200d0100c0301210140d044444010903140e1a5840c1074400c90800c1007010f422000101e00c0c0040003160350001d0101c0f1403080c4006880c0c00a1200b4107140c600704080a04805408111411b80140c005d020b90380d1044002407010285900d5250180c0039029942c451a00100081004810380e021500e447e8000c2c8810350b000c01c0f10400925545d0350b40c01801380309a010880410051020410300d070444d581c4a80b00c4180540351175548a2403601e0410b01342c140903007090307000c20140610500c031050100454511403a07200324a118440b80781040c8600300592461081094141715041c2000e5004480c011005041e51070301c58090505101035400300c0d00f40c00e9040403002107c261107003d60a42c8003501406014900f4143c101800c0e41c0c2417658100c40140c0c10302c00c29101000162301402402c014010071581c44820519510301180351403156005000002e040c0400c48044042a44e5210b4090350000b81044060315000a954010594149203415550000515000b480000a0034500a52 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270095278 1250 270094028 270094039
    0xb0604090c112d07120f03030c0e0609060a111e010608060c094507030903050a0f17040b011d040803041403280f0201021206010822060605 61
    0x410361681e140d01c0403491030155070340151804081e030404a000d190300b2520348000c495039117440360761020311079101e6001110100b55000500c020194940141030140c14182409580d40c4051800a00f090180040003400b8100202e0780c0c05c1c0c140d1040d41002d420140340b9041d03600c1000f000701c5582406010003000b8446600b01040050050000030b80c561003500100c071242d062403c4e1008004c0004500c510707001400c0d04811250002d0742e40152a440c00740000d10102107161940701007003229800080814080c1481c060701d1001184d0030404032103840c02c0524169103070510000041d030320001c0710540480c05040e40c3c810041003201c8105924180c0e13001c0780b0514800510320051980311482260000c1012000707002040008803c007481003000c803440c2090740d00b01213441211a200070400b02e40d0401c0050300074084914150086075110000c02523200a62415145001d00b20410002034132107030400c62010001820b5201c00144501c600a40801c0458000c403d400d05802600f4140a01440b84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270096528 1250 270095278 270095297
    0x207060c0f1701030209060d0203210d0b030105040b0f2212080c0403170313021201090204061401020604110402040f0303020d1218020904140a0c081603051b040b0604090c 75
    0x44031582c0c081d90480f58020036a413401c1c1e072080b0038000c554048000881e050301c2441031501d101c41d0790045014403055001c0ca0325480d2501002d507501924036141c443c0307000b6490102400301041c400c6407040ea00464810800c0f44d50303250001c1c41000c01c0d60f0100030b4064010055a11000c1009404a15900505594444401382c0310541c2007080b5118911004001d410522801401145d60038040e60f40321604000000c050203607038010408028843c0c015803d583d54400740b0f0011032800d4030981c0c3c09004060303110030420510318000303541d80401800c05844c0901220001c4215551034045070302070035541208100c00f59903468040c0d40d0340035984085003c2400410f00c41e50706076903803182c5000002d942c04920404586c035000d100a580d000b0f03005079048030305034281ca0704010301000040e01d031078483d941c814a81031822104505000385500300321585044002c0401c04205c001501070381c0e2a000c00082d11242c26031500203002800480c4425411417400700c3e0005224650380e001101742151502d441010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270097778 1250 270096528 270096557
    0x50417060f0907080a03260411041a0609091015020304080706020d1d0a030803100602061b09100504030b0103140f0133050301020c07060f11070302060306040207060c0f 74
    0x551500e0300800100f82d00003100340f00400d1040d40011030709060280c2002055022814010841f0812603080e6100c0780c0c810f03402c450505092084403d0224400c100d221801d108a0010301180b280b1440ba0f8031a40204012641c1000c6035130b002c00040804d0130200e0007204204074041d4a0f40c01c503102d080b6050044440c00520340e0f00104180754207044680e10710400c8034445c150000035040e88414076030030400104001c400a070004008600800c00c1110fa200b0552801034024070705040200b40071207011013105448160110030701034560402048030211007420707540404503420302440d80054540b0603860000070a00c814a20320510900c90882620304a4001c11030280c03c2e40d201d54030001001f881c003a0035505406403020317100240c1c14000d80704206550f8070340009003642c101c03a0a40101e508401003c12445801c401601c010a2040c207004d52020b0b5036000d000d40750100c0713202c040d0040784000b00043c0596240c2d41103520299108004010031074080c8801800c2e048020541d1000c074110441e1002c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270099028 1250 270097778 270097783
    0x5042901030f120e15091201060b030408030702100f0203061005070201021b04020c010e0601052701050618190807050303040305061618180506090105060d0903050417060f09 76
    0x50740d4010400c00c0000046990b084241c00b858280d0408111080d0752a1320a55540348012003240c1c01c40a140703403140469410400a804003040301e402d16031400c0010424800c4910a5035803250304815901d84030794500c40280d080041a18090305c140e4604031a03480d40f4130030755000d940603d070b095030043c000300c0c007c4000313030394510440d140680980d000402c040745080b0180445c41c41004080c00c050b041010300015142904e2080c800340e841c81d08404014822401c0552041608400c1d1441e00444010012031031507030088107004442c000c20b030001d00030401a8030341d081c0e480c0d920b41c0075010046c8410480d0144048417410301507501c03035001c0d6800000341460700009a90a0740e03044006404523031a0598011004d0003903c040c6018041c010401c0308403a100402d807136005001000ea0030f0a402e811004c06002c40707130300910003849540c42d080140142e4503440166943c1080764080020400355034142519a4025644107007171340c05072210000540d10010800d02c1c01810010f444801c5a255404101d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270100278 1250 270099028 270099031
    0xa050114180411030a060f0f0b061c0603080c0f1e0c01110a060504050f0f011103010519030b09031c06081c0c0c0f03110301060f12020303090301050429 67
    0x1d40c005800107850350052048060560070034414a0441041e0a94502080c1420a0458151600c540e034004040a165030750142e0f94402c2d9804800700302c1d0403519000901c80b0b00403008030324400030040c414610702071134070b130711410146820a00840d154001e408c0b40ca56030b07d6190b1307409005402801045444c4400003c0c40b03d403480107071030290842440d54401120b020700c40c42400ca2041c0300302680f450101e982d920816004034040d0029141e0071180304a02c40c54034004240e0391500c1d0380b6000d65642110043c0090380e05480d0116481c815900312542c800c040200d650f0400f4203103401da03900388851120001700420780071044020704d00b01d0030006041601159500c2c800ca98840e04040c800e18005c000e545a130302454002030504801c40d00a98580482046594000800b0207404920a01c01d0140742e45c4105400c1313000b2402407090901b0101600c1c07003205288200030b1800c13101042e030300441d6810b0023501c0c12003002a000f0002c6103407900341304180a1a10603007002e03000302101aa024140a2000309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 270101528 1250 270100278 270100319
    0x10908090f1909020706020403021c1403030403170a0902040e060601140c1002160f050a0b28110408030c010510080d0e0f040b190303030e190f0203030c06010e0a0501 73
    0x8203070541c50401007070f010750721480c000c486032075013080701000607920343c1c0043e8001441c090110303440390b85510701882c8510100d040d039203184e0700900410002a90018030b0b100700031000707440940140c4078800000b001e410883d40003540030342000146a442d45001a520744515026a03030003070701007041a054007841c071030100d1000c01e54002180848560050f41c0003847e04c03c0000c000210741404a480c1d0b03a070f070740505030001c544d90780081844c074051100d1540c00d184c10002c0080100315034030000141c8441042c0300d14000c0c10058685503a4046d101101003520002c0005509032582d500b81800c60f24000d00044504109942980c440420012000620400d4515660f254000980c000804000e18685003240e5075502c9905c85000284681b0780640b50b031549151180c0b201f05142c110300c0c000e4181c03015602c400984d54440d0004051000e2148100065960003440c205c40c0307140f007400400c0c214031611501400d0340c440c1c18000101e40b003498000911070503c00c070303040040d66201d00355181001000c080a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 270102778 1250 270101528 270101569
    0x1602102615041a09130803040609060b09060f01141b0c09090c1e0a0f0e070809010203150603041403030c03040303060501031b110f01051602010e010c080c0705010b03010908090f 78
    0x14241410481c0384030307070480c04c9089166680980c95a034140b61361f008680c1203c80d07030749481900c001c1001078069031003980411101941149401c0010801075008052458104100952214007045551040f50400b0b0f1100d00e060500d5407072540d0a0799195140194036019140c0c1c1d00002c1c0d401140814043c0341937000605c200603907080b0030981c0f501e80b000104025030040d00164005442c2c400d00812100070080c0d40d810b00510324000380050031496000b005130800d0b034010420405a2000508181c2000204039405509c98440c0e08159809000703540000c01d00380f01c0081441035882c10700c400ba6104512030b40c4c09100c075548039401182034406594a011851210b8105260180c0c000e009640600070407108441c10310418015041c2901d400b070340d55490261642c005141e00603420301500c601c4060100003802410380142000744000c2005215046038803004c42e90f141017100a4000300c00c0b090b0000c00901803000f02d402d01304155480054080e1194410701e00b00c21890070481501c3d80c1c4590107945 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 270104028 1250 270102778 270102821
    0x30304031a0a110d050106031a150d09060204121e20030f010903050405131a091e01150f02152a070f060e03160210261504 54
    0x1840400010b4414000551210007120091403048041c0a040500b944045160751404c5009002c40300d01900000081c081140d46101700d032200c1d4030322002c0420000031983d50345011404200280440070004101d2800014001030341c9480b455003081180c01617001984000d1003480030380781844c07004001000b80c45165102110f21060b00c0c900b100100300601680d007900606c00f00c103800c5800d00201100400d40114007400319040c000043c820840c1f18010410914081c0c00b001c030380c40200d84122921030920600010068000419095844514901c440c8030310b50315a842c4d4290f00011412820020b40710b00324045400e4800904013003a101d107541110841e40b1028045105120b4a0340d03980c0a8041441f244100d03c031114000f407210600400d0860141d907140d1602c40b0640340a040075003666802030164a0311060181045141140d046640941c03803441700704c090780c40002480c3c642c0c03540e01d420010000400110b4125902c120741c0d14149107040440c600420040b0b85003460f076204405132419 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 270105278 1250 270104028 270104063
    0xb0117100b06161208130302030904020706090c060309030305060d020108070f140a0e0a05010e06040902030907090c02100b03120a080c1b30030c0307030b06130f0503030403 76
    0x601c68031011030007824681c6007052080507a166120340d00e00440e840c070004414003940a0340110540d1b000001c1000d41000c000d45901c000b587c03401307031a503984e01c1540e000542c4420080140d07c10003640e075212800200ca01d035507400140007044c0e04041540802c0c101000241e82e45082410f2000b1107505071102d28981c2c032545405c40c1e401d0094008081403100c03442e0700e50380d452a4500505a004c105503610846030711103d0a020f003d880552045040c010003500c1c0310000d5039a01c0545050b910741c0b0500507103a079151241a444c2c070700d80341c0c03052407541c4c41c0044840d215603000c103052403d0003101c407062151340412418180d450480710f5160500790024402c0620080c8100c900680002641a10500700700d0200700c40a5903038111190031009a02118641c00300518901e40740246d22808082504840b081d048640110b2000401e41100700c80000f0003c2c030200d0007603000800039103003d0041c90b214a11540130109c2c000040c025000c902d5401c000c0022540340000456081c3c03584214640802036800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 270106528 1250 270105278 270105281
    0x60a06030b0114150c070303090812160516090f1515030213150503011e06020a030509121b0307050901080c0d0215030c0711030307020102070b0d02160804030b011710 73
    0x1900c6613500c2002d4510070300001800307801070322100000d60054a04c0c249103103006403501140b41d005101e0b41d0003200b4054451701440e0140d410040d0340b00704c5034441108a180850400f09803402c012541c10824002040c034051a80c005202c0c03540e9036404005e1452524017a1445001d00c0c0f04444409161580800040703220342c000d88041b0100c540704c03060558070780c1e0724214081e240c05c503035000084000c0f004001c0440f5249008014161807141d01100e203085c550025192204010064140030f4001400c0d40c454480e0b070744038280103500b0019203044a1501811345030098116800350301c08d10a103040072600349007041d0780d10304903800302000300504c03d1100d00780070003174005100036a440060004140c1d080340541c07009600c20580d0f000582d03907030764081c507289041101c40c2c070081c6e0107a80240940c40050745c000803640e059170320001c21709445e69010fa081c080607100e803000558049450100f10020003180c80c3c00341090b01e103d405140a66a04c3d83c00c031900110709081031040c243d0151941d80b02c8981c0f00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 270107778 1250 270106528 270106559
    0x50c0402090604050a0e0601082a0306130510090e0d020a02210303090a0510090f06090c09020406050408060c07030c06090819080402011404060906122c060a06030b01 73
    0x540b2040c1069920f00c000740c00c034241c992105901c0c040c49010407080390ba0090380341d907000a030025004410382e80c0402d0700049504142c1025403600000010550b6643d5124210500103100742041c400c9d8541a00100705240d5103200c0e035440241815060710711190042601c0d850310b8001e40c02410b8880e0f1980800410010301d0034040203034000f41100803902c00302400218801c621080051410900520700140b4040128035407416107490440c8000014114001e00a01c07039420640106840c40d0505003c1c1c101c1602d83e000ca20098070000d80062026004030103030040390750800a1711601c0c1d07500148a0035911030a44d0042c0041c130806c10110000b001e5600019a540c02844080e041100400c0150010030041034407001041e501410003086692101107441d14000d8801c01d141018503222010700340a280d80901024005c2101050306600c407180d00201c40c4078003400400000102c0445da61002d6850f0b04c0c810b240341c1c0203610024416445901402e000c41c0d5000c44810b181e40e18144440000004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 270109028 1250 270107778 270107797
    0x14091e013804060e070806150f0309100516120b012703020307091b0e01050a1209080f03071202040312050a03150f0f090b100c080c03180406050d050c0402 68
    0x28070034081203071510707244241030180403148103030b509a0a0519006c1c1c9100802401c003442a80826110740d666000da1042e80c0910740340b8140c2e25109d4175104600750828a802c884900030b00c1c80e000410040030204d00f0844981038454544020380480d000e50182078403500c0c401280850f0641922030304024060010084001041c150305014540342d0f40003e05154160303100542d400d45074400b040d644854161500b143c40c040307090400d07180300f081001030250300911040005120249882280c03112050300110301031079014000c035648188111003c5a950000d881d13042c002200034040304107501d000e208590540f40c02061176550308900d4a81260203a0001c22030404042d19081001c1b01d520300c0c11019800340c00d128040b0303002c25040c86a051b04213070195120031165400c080002d021038944080b4241ca07003159280c41e001d00e030402e051481c440c0c4030350b000d003002c248000900d02103006282d80b00d400c3d100c83c04890500c00c90750707604100300d190702c1c0030800a04140c000801d91405854140e008149412 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 270110278 1250 270109028 270109121
    0x4080703081303170913140103020402130e0f070207060206010609090c09090e15061806040f060e160801060e0907080601090510030902190f150314091e01 68
    0x7500c0b551344801501035a01c20007032200000c20705914a18000900d41c1c0001344080b410016041100c590ba040c0310f20610010f8003540e0300244415000100c0d45000c00034007041c4d02c038400c590038280c10700070311404112000401405501804145240b003c2030b254100d034080d130740b8200c41500303050402c1c1c01841002e41c1c4a06124114100081320b44e99401282c044c4003070180540003a01c01c41440c13419007500140114807441401311a0310008121884190f0001c00648001403140c0102c02c5110081005030040100c042c1c01c241003100c410044c10086982200b141c1d070740400760742d8409040e1070384140e807128140d00c14101000100501d114504a44d40f2142c140340c000211546c1d40d010030019100e01000a001075200d0502405505040010241002000380c002c10490300d06410001c1c003003414020003107240d42808500740134a105e508000f00d10300486480d40001d0400da62026a6402c00300e4070302c1c0c82580880145001d40c3d00603c0f9004031700100c8207400369620410000c1096240300c800c614002c91 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 270111528 1250 270110278 270110317
    0x903010207120c020901060305070c0318030f141b010f120605100903050f0706020d080a020715020d0b180a1d030d1e1802040207031e09061101020408070308 69
    0x3114825885405541a03c941083d0402401030001668050b085070382490b0500c002d21400702e61294032104607981524040f022a40740104c00380c845541907001500750489205400140a200f9000381c0c11008031074111a012500d0031000d0314664014100d20740440c1145554100c201e0041515505c20720300d440000668a0711100050714030b01651443c003002511081c01801000410006c007400010341800503e041440d00300029910040340441d881003001ca180425920039041d0107452441e076108114894820340c0600d000c009400c01c0804040d0203042180f100d10a0a04c03c0c614200d030304041c45000266070319001002c0c00b9168150551031440f698068146602d002400541451510303c0b801082004411300034a0035100c1c07120b00d0030450307858a94a098501640000c020b8601d6060300c0c056201e010b58107003650703940c1c2e089401502d403c0d41c100014040d9035211400070141c0d0582c0c0c40d5640c9031a03018007564200c0c0158019803c0035800b01100340082a015000f40c40340305880008940c45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 270112778 1250 270111528 270111533
    0x411030708030901090e0405030306040e071203050d05010b0901120b0d0f120305010605030f0106030f0608030a020d030501120f1403070203030a18050103140a0b0609060c10050a18080903010207 85
    0x2054a940d001c14159040400c010b5074940c1d1205042006040000c4204601d0030203031115a240d10014140c0da11a035612420036030b038903009222820090055000c01002d0ba44582409420755100d5849101050302c0c2400115121140c0b0741540c0070050181d6402008080c1c08a421004261105086601c5512a55080b0000740300d41418200b191280040058a201214000c0c040e10010382000c014040188204000105050002c0e41100d50900e00820a15841841a002030400350840c0c00980000a02c10180a800141e4807080400650702040107a90b5500c08840030041710000900d180b83c00e5004030042500500d10413104411001501c1c50800183d002a25641c0654000000310b107008000c0c002070000c1800c070794001c000a007070034802104444510400b910f0b004002c0d9990643d01c0b00c0401013a1900416030351030020140c00c0c07070f44e225850980213036240785040c410b941c141d003020f0020306a140c160040c0c08540341c000c261a0000c0c0300030780d00c8020035040808010340542d8203004030800f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 270114028 1250 270112778 270112783
    0x21b010e100507140105070219020a0b030405061017030d020f0d050906070215070905041805031c050a020901020a08070303110d05010510110c131b1806140301090203041103 76
    0x950070385940b038030b55681c1081d1502c481c0c0b0070070000a0a4041c0d00d004104004160086051a004100b0301c9404220700c92510010b0480c0c10305801c880804000801048104400000c81c54010602c210648103103668912000d0423482065044e000c0903002841138120f51030300b5070082c0c56500004007140b81007c40000d00002180c1c4129031015140d0f0015041c0144280c0500c240e00f06102182c880c0c58582c903242002410b18241c61281e680030325529107071520141104111454819440030541c1c2d039a40f0440c800400101d06100e03164403451410b0046071901d50b051003110089201a0003600c0000c400d5110414a40c01a1030240e003416214800035005101c0781c0c0080c801046815000138065042c4000c0c00702c02318020044405101c43d410101621701000104808001422146007a42c25003244d5088042c001e034800004650009001300307509182c010301c015860800400341e2482450303496400700c0303c00040031071159000c002000180046450b607002942c0c854000c204c0c55100002402c0400d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 270115278 1250 270114028 270114049
    0x20d020d02030a090b09060c18180403030e0f0c1302090307090609050709060e1e01030b0d060501140910051311070b10090b0a12020409020a08060f01060807021b010e 73
    0x2140e844d6919000c9013003101c0c1a00117074003c0062030013415140ba003041140620300c0380784020701480300c1500411006640e4048041540401580f076050070b42024a0084d001e8502d0b141c110740c80340520405640c00007400540c29411540061030020b0744406607040c1002940212030298050080c510003080781422405401c000b0021103100203554908160001c040d031a05400403000c22a81851010b000d507074098146034002d070302ea05c075442c80066000042e0014420a005030784c01030041c01d0715105001c0030380d00c994121203003c3c1c03113400d03001c415038100180d070701080702c0801a414200c0c0c0e040c0300c0c031305200a01080c41c80d4140000030760420605460041a0880001100c10a80340c1d42041103814900030f0220040103031001c04d0007a41ca60078001108072040c0d00070301c03d1109524882c0c0e0f0a56440f83c208503d004e401400300182e41c0c0d15140803640701d45080361356100e004540400020010300c1000c14031311510440d4060719950103420300c40b0120481c1d4400445c108002040304248a548400106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 270116528 1250 270115278 270115291
    0x31302151909060c020609090705090406030f230303070f1403161805030c1504030b090604060b0f010e010507020a0b0d0914070e040b2d180c13020d020d0203 69
    0x29602401c528030007040034034250030050030001804c80302401a2030300d00c2500e030b44050483d07004070159949501144c040c0144d64601c6d41c814105000041400100c0e40380506941c0540e0420488e40b14140b1242016040401d40c940c0307640c02003001603840c070711030301d00c000b140106840c1902c181a0020b0019150b60000d8034000011020070700d1804415070400301c02c8030f01c48000512041128600000281c40f00425070140703000c1c84113118954044007901381198091a840525144a810154441c40e0b03102400c503412035080d807520b1980000341c5444100d106150805958245007040c2400044400380c115080407a00070b44450300c086044a03003100644800010400002043c1d0410b00704181b1040800c510b00185400c500c03414001d2200c00301d00c1e5680f05810420600041e1a40004402c114900760742820b22011308112000082144035422401150400c6e40201d94030740140c42c03d520340c00e06040040c1e10000d0815035100c444c07501d030043c0c02482d00e006801810201e4125040003a03900c1110729 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 270117778 1250 270116528 270116557
    0xc030d050702060f010f09021c181e08040303032307020c03191101030203221209080c01120f02120906060301050f1504090804030f0606050a080a03020303130215 71
    0x400648542c1048040d50020041d02000455403500324143c4401c0c1c1d45015003d2940d80008000303800b1507403901d059018a803101400c00103010024102512a0071100085500e2048407812007250001440c21225071754014411618080c42e60b0350507001040050702200003102d0802d81ea000082e0b40c0242c8921a140b0382e00501000808402014180700e0319a030041803200c058103040c070126000c00c1701100c04220a08005a0342d40b240401014092000070905c02440d510498500c100102d80452040081c80b90315261030040d1140740d11621a4000c4e0b0a2a000480c00700e4642804034603500300000607841ca20006181c10602c0150007140e0318100c4081501e640310701c06102d030302e0800344a0507602c03074020044e450b0242040b00390421288800c0300700a2240d61141c0e8207105115640c13084500440d80000300e40001099031800501a200d144500b600c107540034207000543d4440404e11400c6980c1c594080c45c91541c481c03010803011445220241c0c3c0040c03840f2b01d0303200081c11a070700802203007140458 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 270119028 1250 270117778 270117781
    0x908071e031e1115040302040b060708040305100615020d08060f100e280b030403020129040e06010605040b1b03040828150207050f0d05121b160302030c030d05 70
    0x425070f4075001840c41003030281d150100c4e04c0e030500c02c0d0801078405480c4c3c1280e000c10302081000001d0781030b019894000c2c00d00d03200060300004201001a001105e09044d03001804002c1d910011001d20808014100c07000d0b03040114422100c1c2c2c4104480c96101000420042c050007009001c40c00518180800030041220221540c7c56451b01d21906d5140c5101e99503106030f501d0000b40104801d00c0a449058404000413001c1820103000f07400018407104102d104000400c0042d21466004a50400c86400b03541750106603a4100004100d00c0c0c141c811b1501c44034549882e1071039810003540000214034045480110130403400038140300800040100700000c0c40400e10501d20000380042d29864240940c40095100300029400d4200c5115407407510360058450404d4204641407504038110340c1001d004020081e11501d4005003c0c04c107d034481401c000040e41c4240303002c0d40b5006007003092050320000344000a188071300c0400c05800d46119105403800d00c4107030305c50503103150080f03074601212589900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 270120278 1250 270119028 270119033
    0x90612110d02040620030f0706110d09030e041a06070f08030106020307031206060e01120209040c08070207060311091002030c10060302040506010e0d0206161e030f0908071e031e 78
    0x30a08017025030030030a012462800c600110f07a0320b02c03603c01c021400040c0444d0000c24044190f20600b50800b50320320141c2d56540f94544013008100001085001c144060446080340c181441914500300500074250f91141e800d00400c545500088803c4415100d60609400000c04e4000a14001c24482e0015900c44116140c003034820b202c9100002c14552a04000700540d035841b414900c5182c0c0c0030308100180c40e21003400000a403003480802074109007016403030203000342d01c0510184a0216a803e0710081c82e01c5400440a940741460300e03000030002485611690328200091810010050048a11b08a018018581080a0a01c000d1030803a80c680040055080c03601446a20003824030301650303080d0703030500006e20150126030064021715000c214401c00c0c0c0402d4501111150700300e88220629103003c1c0e8941c10b0100048012070000d1844006402c000f40212142411780d0324000c0540a41400c080440c401741e400c01c02043c5101d501d5403400400305115001050380501000038442c411006070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 270121528 1250 270120278 270120287
    0x9090b03030f0712030e0a0b010504050403090312020a17040602060619031b0503010b0609220f0608010506040b0a030209070809010216050102070b010e060a050405090a05030a050c0c060301030201090612110d020406 94
    0x801b01180350b00120310b0000041c00100c11181511403c81d40090140c0761410100e821600302d80005000403400e181010f4540d07000030704540750b02d20848511910007a000f200040328002d51094030096400301c00031071041c0c03400084c80300100045c2205226941c0d503a0b100c920102104100700b000c038913038800c018000c0b41000c0c000c00c1d00148007511480d1030720110740085011030b8a42c00c0c019213600f04505c8501880d6100c0c0d0425480c1d04c030b18000c00d000e0135840c0c080e2180208010380703070144950b20700003144d405420700c00c82e40c5084a400808440d06030b941c4004c02e0710740795002080b182d0301d551708001c4000c1c0c40c0c401e894501e07042c6000300d00040c0c903a2550315010081c904180c1100e051190098100300c250350304c012421082e100b080e9804076650700c0c0c01c0c0702285070040d00c80d0010042c0c000490990b0b100b0b54010040c003081066401203511401e12a401d2180612081c0806030001d0031018040c0030b824081e00515401a400041c0007450526401c503000b40303501b00606241c1d40b241c00050401006a00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 270122778 1250 270121528 270121541
    0xa020619020727090c0302090a0b0117010b03070807051611043c0207150506130c12020901020a0c06050c01060902130e0c130e01030b130309090b03030f071203 70
    0x90000740343c3e01a05615a590804000285166015200c51040c4c040080d11024040255400703003455242d800d1030351803000508500f09023207000658841504c0490310000802a0482d0b28411219145407210781c0110703010f40004006800b0b000e001c010340583c080c9501c26031481c05008603906107100b000c0c0700810050300e4018444a2881c00705401802221a1440881c10300c0d09421000d04152002c80103940068002d02e4400741020b10145101a111400c0350451841510100c0341f14891035092401c510480d0f00103120607000504449815080c40804d500418600d80305004440c038150003030740d134043d003100c00b900b0a4000460104000c00d282d00240141000392008000940c18200143c07805104128540700d0149100c3e0310314049814503003440100c50703022400358a280d1126440d5005d281e40780d5002c0c8001c9615680c4000041c0714126420945880140c0c1035482a60452502c0901030180206101196040c00700704075400300e4410b8000103000e0544a10301c03420a6070b903000b0b001ba048551 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 270124028 1250 270122778 270122789
    0x6030603020411030f070f0207080f0304150207060503060108040609060911090604090b06100504050306130c09020715050c09040c12200a03110403060608160501090807170a0206190207 81
    0xc09006110312110048001a0f000c901840e02040c4400030b07c500700d1500100b644840414000e071072000e44000000f000800c1525202010140001600f6508a945401314800d800000c4c1081c804074505611a090607900103000310008100e401950316040100c0d500f40034100c3e422500580c080005041c8481002d90010b003c58081244200b29114200043c000501803840303071141c421a260389a000d070058801601000d02100c04a15246000f8000009000401c0d06c01100348180068142018022200c1042d0b1021684919681004045c0c005c2e1201030146c0c49222001d1081070001e4496120b540c0683d8940d03035407061101c1d0300030800802ca4100c2d90035140d041d15000342d400030b4140100100c980001103480c4c0001e00b141c044201c0c044500031504003e2400303060280c00921080001200201801928031042486a8580c01900c0d008d1003031081c0c0c0010740100900700240d00f258001a0b030b070388812809035107501e01c16900183c03040d4045088514105101000c50074504d504016042c00b628 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 270125278 1250 270124028 270124061
    0xb030f0c03070e0103050405010f05010807060908010b1c050a02041a0901080a0803040b1f09021b01060f1701020403020a0f06080c0c03250f0507050f0d080307050307090b04060306030204 82
    0x50142c0024004038612121074103250b01c89004c01d0412000350710100000680d0034003044296111200141c031a2040d02c20100014000c10340440e0951040c8260340b41c4845c001c140080306aa011030071507000082c98002e640324000c4156900160302c55026030810540c030720306028081e0000b0b2040001c406010f80010300c1c00d43c0582a8079000601750310031642c005421602191040d83d5007400d10101005844426000381070101c0c0001d504035098001c1c10385d110050300200007440740340c1450340c201d400a109400d0b102000803c10000307000000c0c1c0c400360501c0448005440c1c1a12900403c01c41f0103075038801000080080030030412242c0c0b1544444d086140782c0a024580010140415a64003400c2d41c148140c103e4010240300c14090000c00f100059408000764807203144606089450307040c28800c46000b12040111076000f4641250601d10700c1b07074020000c50454032802003c0700e154000802d1082032100c0c46402150008040019000030145a500400d80e5130462040c841503800c46200a003201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 270126528 1250 270125278 270125281
    0xf050a0c030203011505090303040801020a020a1a070e1002010e01110a080106051204060f0b19030c060e01231b01060602120304020d030f0302210603071a0f0a05090402040b030f0c03 80
    0x180c48440c030b04000c00451b24005446586420010381944a02d80c010740c0e496100040f2810901d401180d0150b0850241ca85040000c0c5031180311001030313808507a4540000e004140b490740e2450050740304489004c051000090b0741202d403289a003181e41c07141013508014004102d403003207035a101e0440c5016150501d4070a04000b15107019032000b0030003500080116840e03809041ca001040d900c1100914030061040c0e02e41e51b807480801c040c00500740002c0d14480c0b003150010030514001d01d1307940d4503050180c0d1141d50708100e0201446400141000000b05144104401c0c02c0c0b01c200b00125000c0c034554040000382c1d19241c50006840c000e01151310240580040c820400580d4451030140c850350307010706112282041141c1d00b207000340326800781000c0404a4144903008504030314412031284a00740d00f04e41e10302e80c5074600985035600d04c20010480f240304001141180804101409100d0103c2c203200e814400300100045c145e0b009030704800000d503008030800100e010002010350f0820b002c0310540c1e00c3c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 270127778 1250 270126528 270126539
    0xa0510150207290d110f030c12010510020a080309070f030c08100c30050a0905060a0b0a120f050307060203070225060f0507021008041716020909100f050a0c03020301 73
    0x203600a080482c0c100c507595400c10004640505c04590101d0401681281d491610310004109600706c8060848060318000c000711b0103051403c014842d0042076001071a44500640d03417409240d00040c42c40c2c8060003803540004202c0303c40000c0c4805140f042061031580d50401c02494640a0b044901e002c40744d0400240041080d000f0300c4540d42011f1200d000d0000581107032040380c3c071020410810001a00e84008c00204071b5a0b64441038850f0b125400787c6a0395107914040c001518a030401c0c455100b407200008000301075611040b03062551140d1100105040940c84050841d0081a400c3e0341c0381360000100500158140125140170002484c4940011503031410510780002500035401803006072064000b00e14050026100090342c001e01c0780e0750030003413880002c04806054400301c5145410341e0b20782441c0d11000099544c00815410a00040e031415020407010040103041c3c500790b4080c19440b040f28040134082d05164204004002c145810000e400340c04480320140d50504151043c00140300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 270129028 1250 270127778 270127859
    0x907021606050a0e090c090411031b090102150403080f160804200a080a020f0109030b0412050d0e1b1504052803030e0108060d05060a0510150207 64
    0x3070703a04929007a03480b01052642500c0058440c003a89030300c50958010010480343c0c1070b000300342424080e0b4052116004170b500c0d24009000c190350b00d4101c2103500107100c1030202144041d1848400c14812180303503042102c4c1d80000144255001c4d000943c00100704410b41c07020040941c0c1000344d190b07088102c4150031030002c0450030050801040c00d010960340c4040034031030031222080d010703000341160a040d60340d80c0750955132060360720704a000e080b440c0c20b015510340c0a1503903002202c1d000070003110306548650700c03070701640e007035201a40034800140501450007545103d18103501c3c1010000384201c0a00140c00034487c58441d00c8a84548518815900bc44221030299800c890055902401c1c0d03040b2104221941c0c2c00c04a1285180010707410300005050b44401481001e0400b80c0b0f98011a072103540c248a0300303007a178440c054856801f44001c075404480c42d03801280e010840e00140300280b5215800300300420320f001c0e04c04005034071400c1c0910512943e032801060b250032020f0300f0700c030b440480c004520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 270130278 1250 270129028 270129073
    0x311090601090b09040c020f12120601050301150c03230a021510090506030a06020c1509011401120c05030607050901020f061e070908191a06090a110d020403060b090702 74
    0x6000b80e46411600c07000b1b90003005800845d031098401c2d6480c0140f1900115140c2e0400314681007881d6203c00494955400303001102d05840034a905d2100b0f6200d02202500c80c4403a00740201e00b08409080100c1c548000c5603504074120b02c0440a007035840b00c910000a12300b4440924142c601c84040702486000040c02900000b220150b00010440d60303507040010341001030b0b11401030f000030300028420941c0400498041c200c80c01071500c40440e601e5810100f402c031602c0e10071440d00101002e0041c003002c00083c1c62208518864045036480c20b84650200b41044400e60320710001c0340d030100b8403007117668051010809002d02c10005081c1c41c034155100d03030000700130b049480c801669040c010661142c03040c482d00b809820b1010849140403241041c0094040400106880344410716011000011100c00602d008000041801700309481c1d01d4820002090351003205009040100702c14030f1100e40d6030015100540c0610000104000c5010a21580a5004100c801150000501d8844142d09184080e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 270131528 1250 270130278 270130297
    0x4090f111801050c0a030203030f010602060c0714010e070321080402090f040812040b010f06050a0818010b040905010f060f0e0a0b121c180b03010902130308040311090601090b 77
    0x410007a240c4030060341c9500c01c2c2e60440829024880a0360b040c1900000114083c918085003191583c4c1c0c0d9400032a100c0794140c0300d0552411007004507801254040780f050581d0b9602c1c600001c0e40740d0204a007076241c01260750088a14240b40110124022514240c10003582d900781000400e610f0541c1c0000d2a134440103105a81f02031145000c102403000c42d109440010310341c1e41d030702291810141094072820000344190380ca01c1d15235a501040702031003841030b1040005640c03101000e07501e81240342090808a040703000c049650303920140e0700c642c1c0d1745d000d07282e1301078055000010302c0c000f042aa00c3c01d6840c642c00c0920403a044001c1003250120b88265650303c5a8031100004010140b10b00060030030901c14041c0c08584035072040b03c040c030070310080c208618043d191141118a00c0b05290307002070780e000d0300c039440d1140703405c0c030040103e444560010180400d01403508210310340c03aa56501c82c90342068000340c54003030211141c411582443ca210903005038090030b05010b50781ca040d0501413248a40c6200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 270132778 1250 270131528 270131557
    0x1091a120102070c090e1903020c121f0b09060607050706030c03020d0c02011d06060a050105030c040f0807030c09090b0103020103150806240a060206040201110705040603060204090f11 81
    0x88142032142903050750b400c580e018400c02a029901c00c0940007500a82c208001e0034000d496604c2140507103010072034405a45030f00a03150b10f040750000c010034401203e200960b00d018424400c40640802c04942c118219040000201039502405001400500500d05d90180d80c080040d24081a00002c1310011103207a0300d00031404400044045000e4080c0d2102145003d040180c04d040950301034025024000c0004402c1c00501040d001c03d0b581c40805543c0503822900142042c441540708030001e41d800400220082e26090362012100320302041940444030342e4200d01ea043c410800f03803404076001001c22010501007450707140c4a291016406220003414155201c40600c0d05031520507264005002600c00da070101d18101401a0450380c081c0101c00307100c40100050f44552902144207001e03903030349074014051569903034010340b9518031918a0204c42e216403180050286d440c3d000306005144201c801603211843d114800d07044d1080260204400c5007042845e1206078800380582d401401d21402c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 270134028 1250 270132778 270132799
    0x50c010b0a050a18060f031103010f0506060a03020f070807060c180f0510170c0a1416020f0d0506040807060c030e0c060a05040509010914090d02030a4401091a 70
    0x2544c2d8001c20465101c00302140c1014000003e02102402215000c2400d5009100b100414800702d4200c40c8100c41079640040240030f0b044040b80300e980030305043c0c428060034a14010540e1591082034000c03000440b452911481013440565014181d4a40031000c01181550300d824609034000340c0805004203400340c195401d04020f5144582c509540030484c0303c10307180352408c0140509045034802d03504400480c03200304040c1c40386a01c05088400c165105943d60000d0b0380542c0c00c1003403a050390400d41e98861481045500415000c1c480316005500c59801e040d61140c5602d8450252201085004185031611194810501c000b04554001d10412100150344100b841015036850113140c01c1950401e000500100ba11328142d0700c142c00504031050b003040c180d92581405d0307a440d0b1a00803080c0c010b0b04140310400c6040d000710201114012800344400c1440120700c4200da00f030352445002c040280d82150724030701012810305810f0140140b0740080c4aa03803911140c02e600b00c41c85e510303070358002c140809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 270135278 1250 270134028 270134069
    0x6180f030e0d0f03080603060603070506040b0310030519050d091d06040e0114040c0b1e07020a0509040b0708011e05190f03080c0c010302030415090606080d050c010b0a050a 76
    0x704691500b9500201044030b1103998140100901c0045410070300a1041801040c01481c00141c044201c2d4030060925141904283c4041800d80014210300301550f0703081c0c00400041c00030700800d4500074902480c02c11003419810140e20b0030a0380d04d82102400728a01c0180040a004030640c2c54000340921032100944942e404a0014402003a0900b1030b9440c000400c9000d1451446a500445c05200440722184c1c50345015078051003119401c0f00c5042094002c82c0d400c13004030002e00b100c1c81c00280f03810b16040c0c1d2003011500c0c0180481d000c0300e48134203500411045541000f071031805080248007221800c1140f0340812070144650158601c00c7c02e5207050016102082c082c80005445070364071419401d5603929240b44103401032a0243c1090144620403546540300b4801c0d640f00301c0d0001c0610320099240c100c03400090803a428207503103c0e134a86d0b0001c290300c50100f102e190040900c0da181503172059148200d03421105080340302c4c2d11502c65150300300b04555130311210350141c8001100c005408881178 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 270136528 1250 270135278 270135289
    0x11d0a18050601140306010b1201050904050c0411070b0a090c060c0c050a0609150815040b010e031e07052d01230403060e0a0528020d050105010306180f030e 69
    0x11001080e80c0b165900108074201401c00030210040c041d0212402c990f25034810802600542c01580810b0700040700400c040d10341a07820725045401102600c04c01040c80b0003107001e484c05810100c21864001031440100b10038104d0003135126200040c02c010001c0580c0e0b0300408485103209a0082150200e035100900261155160003080300402c8400071640c1d80344054000806407082c10002d005142c0503402907800b80045c5481800e040c0000281c1e503480008000040c40d410034201c1c10020701b0306880640b0b813000c014a0005105c40a40c0001b152450740400c1d1070700440d9008907008184400c0389408602c4405804810b01c40d1141e5110356040d5503200480e903492141c0616402c024803c1c0d4100c3c21903000c1c05c02001600d001b00028004582c181c1c010660b902001c0320010516402500410302d01100e00c05400503001c198107601c104010b0b0f5400003941e0311030002040d80c481e550740c8010010064248604100d001191034048081107080c0c641181c1141e01040c06010b000e02d204640106943c0c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 270137778 1250 270136528 270136571
    0x20306060d05181603170f19020604120201111806091e0a060903080702300f010e070303050d0902060d050a02030708010501140d150b0403050a0506011d0a 68
    0xd504000610b0041200c01c1c0680c148003855240b4042c10500102c07654000002100b601d800c031b24402d0500509100007883d5034802a0106800c44040c024950005d40b0220740702d00404e55070740101064101030030100100c000c20750145055a240142c0440412600f45c02c0da80400b1411105064038061070300461100e124681c810f41d0303c050401c1c080070201d8101c882c4003410940c10390320140c100d0348a040540d9182c1241c00f001e80418020702060300180390a02031882004010343c114480c1e49058050034107600790340c0d040c042094020521482c54510f0920420b0117220740080102112441c544014010b449001071042c0c044c2c0c3c44228440554440c80f04032450003076000d108005c01d00e04181d492001350401d40d4250001400c0c0000001c05602c1204803404443c00d2001c038901e080c40010545000b0015a025082c680500c11400a01c1035000d4010340002e60084000e00071415092404c00d0600c90145c008025203101d11401c01040c01203041c0159019402c15000100500000041c0405096 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 270139028 1250 270137778 270137797
    0x20702040f1a09150103093e0d080304060b0409140d03230c130305100b0906010c03051903060f080703051c020a020409050c150406122913020f03070905010e0a030602030606 76
    0x100302034200384408d02c40700c07100038050000e4803e03001c450000302080002e090394440502191001d1000c0f50120703203207170310800018100920010300441540d9a441c0026080303030180940380c020204481c0200d03054014880030580380c40e946c985054041c14201e00180d405000390b801602d0108002e14000e0400c0d41032005903400c8401c56100354401e000c0000500211041140a01007503804682154010302c403400340ca031ba15880c0c2909103031400c0076500c0801308058054041680301d0074009010745210007d07001824200b40a041e03094154113206280c000800603896510f11351545003028030b5030204903a41d015904070780100340d580840c108a07190081d241400eaa1003072400c0c944280303540ae540028011105191202410400748001c488110f4140e048141400348100b42c10026074029a004031072911070040006030780840c0820707030074201e81002181d9454083c002041c0700d40d25401c551907030300424003460035040e85004030740031485150342071000900017500840450219039864080e12240e10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 270140278 1250 270139028 270139073
    0x151503010b0703110c1813020a091a12060103080a1101021903050106020703020117060105190207030203010b0a06021b030118080702041a0a03110301020702040f1a0915010309 77
    0x58541c256034145a0001400b2004140040c8070440251008181c800d0041c1004017003d1005a082400c44414030006000e1088203180c1c60f8075000582d241c03170002d00a02940b2500103010f4880000c0002c205d4a5190110710940c2300c07044d042503090000030094156903000412a4440a00e94001d40d0001c160840c0019654004690014086180302014104800f156001d01241c1d90f41d590583e112049400040c0c001424461690035500804a402da003140b01891b02c280341400100000c216400c07221409001030300285000c1056240034000c0c01c048074130854905141c0e0340b512001941d00e1000910031400341c4c40c00a04908143e4017940801c0500c42644441c01c2e40c6021490122407503130000740d04902c40c80c5402009108010740940304407450340d01600b00200ca908503158003d01e0b2a0350550590302d5902080000e0050b21103029881c4c0304441c010010480000c2c1d520400b080441347e05580c0d0007420550108039005100c10b800c0300d000d910170b00b0002009865428940b81c4c1a960510080365403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 270141528 1250 270140278 270140281
    0x2030a030c3201380a08030304080c1b010e01030903020a0203030c0f0708071406031f03060b040c0201050609060d030c0b0106170703060e0601030f0e2a0303070506151503 75
    0x82c0100100b002c03a1107500008004030300c080f9104003050900104e01c6104000f002078200e801e4002c1411070091000001c0401c80e05681d05d0310340e245107502c01ca40440c1c41c5880464a407501c10700400561210b40940d52150a400301c0c410300003002020007a075954109038440051071b050500900c00300d82016006425281e540050000c01640e409101c084810380340f144010020f4260808641c40095558441925407201561b004000c404d03000174080000c40400d0403108844c6082c00c0040b080214030400d408034070424088200000c40c0c020004c2003043d0390600c4104000390361a054003d070710034070480b4a501c907209942401c5a46141c42c000040c0720403140000442c2c0e240d00042d2101c400c843c54111200c06503a1a4411400e40d000d9106490082c104100860f41e0381d0300980200154002c11030000800c40d081c0d6003401c1c50030070070700a1001c402d44407411002c40c81e0038490001206e0402039004524080041ea07456903116402040110490341e082007122266a50044200051b40400f043d130f0340b00e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 270142778 1250 270141528 270141593
    0x1205090607140606010909110910090e0405010c0806010c0222060915090507020a050a06051915050108070c2613270903080a0e0708010c03050f09010902030a030c 71
    0x503603006441315030218260540c00280401c050080c84080c13106000e1050034003e04105200c940310000d610700c8140000a000480c0f41c0d4084958a441140900c0001c107105190441c0a030500001604890412507003035000000340c0c4809134100301c0b20358200c907011207500900748040b00402c4150030006c2030605001240e071828580254900984500e09800c01458a600005913600c41001c0002001d54004198100118909a1200c0d03808503620b8490380c01e99110b00c0040088810610314042c042c1c51000080c42a542e204008950002060a20031000088c5440396124280c00c803150a91000c40100c0d042c0341c88900009446101281181c0900e0341e070f440e0480f1001110000500c031b048a45036219100d86000d40e2b0041043e0550180c584042d0350b111014000702400d401100f98035640b00d0094009100c071024818140e011510703642c001514100010f00c1811003401a10b142a00d07130500155034056034000ca4944102941030800d80038612180c60403000503812000060710070358010002800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 270143884 1106 270142778 270142783
    0x15020403020907050d062138040206160b04120f050304020d1103030a030b15130501050a030b03010f090308180d0c030512010801020417030304120509060714 69
    0x2185034481e00401090064001c40501c40400c8040440a1107240881440b0b107a84204550a20b592101440b0145098103d80d000b230282d081e20110701150f658808a88940c0c8030200c2544020b0304508000c190584110f80545070702c0848258018500d214410a0410030704541f502c40c2561070300d80a000410300c0714101143e07815100b035620203942e035040003d8180b80706250b4002c1480704005050101c0710350740c001882c0f0001401d0001124201410b82c40105441e402c0c0f070070940b00d2400310310441c0503000000c9a03642652a242402c4500005504091001c50080e01d990b1241e0310b4004030f040502c291291240c0307440d000300d41c0c0003102900c00d01045d84418020320b09241801090f46003100f0031075083e408048661340c0000d042145001d810032001c501a0440c1c007850861515803508032800120200100c204200041c180c100b40d580c05095401440c0c0100c18150342003c5030228a5 = true := by decide +kernel

theorem cover : BRFrame.Cov 269964028 270143884 := by
  have h0 := BRFrame.cov_init 269964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269964028 ≤ n) (h2 : n < 270143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
