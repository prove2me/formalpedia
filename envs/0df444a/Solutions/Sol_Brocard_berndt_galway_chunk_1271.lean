-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:05:46.638824+00:00
-- url     : https://prove2.me/submissions/def08501-79ae-4fd1-90f9-d5389843221d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228417266 ≤ n < 228597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228418516 1250 228417266 228417289
    0x91110230c0f0a0f03080717090607030e0d020309010c0c0902120108010f020f04150c02060c01060501080903030907060f0c0c0b090118060f050714060108010509190f020618 76
    0x500502280c5030202071800c02032406600108402040a0b10b01d55444444441414030014100695000400d00c1035005240d01c841c06602c0072660400c0f860031580c0207031f0364801141d054000034245180911114404103c5e0811030f582d55014516261440d4010341e010200c6803011070b4504e030482000074040b802031020381030060280c0e00c03201055145c1400542940c41030305020301404d1040002d4030044824600b12400c907043c580f0445540307490101c00761449044808007941100c00020404400d900c10761200c0300381c0f2002d03200d1140646881d1105c03036aa000850b00d5402035130020400740409401001440301c80101d40c82c00a5900300340d60359170110300a0aa0100924400100707003428030b9030300034a0010304e5440c1e1642c4605042e14066006108403140c90728082400340c001816414008214074030700c020240c070001c46000f5651800614000c05080b240749a8a00958403019203003c07540c448034903101c0e001a01170510000980030003103142d000d08840070114450364440ca4064a1300e0301040e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228419766 1250 228418516 228418577
    0x2d0e0403021c0203270303071a1e0115050705031303061505042901020c0301050c2503080c1308060f070305011401050d020901050403170c010b04091110 67
    0x1d00180302e10040d9249414050152040d07401c24043e84100c400d000c510782c200b803904a400754035a86200c034042402c510034504050a840a000c61504100854000e0740d03004131000141c020410300a500f91a4204000780a403c2549030345460740201d0310b06c01d5020b4840c2c540200103603442c10890261901c0d40301d80741d52003140c0c016210f00004100d5103880409000801d000d44040c0081d440b01e9589215014801018511007c00c212104005034401c1110154481d0064000c000f503040603090205030380c009130807840002e60f08a1a00703a0301224805840356182d45900c45444503254503401407500e8201645504030204400f1000503405010020a40114a600c8002a040c10981c41c01000d440e0140c00c00003510051800c6405640d03400412590f4400140c900141c0740c1c1d1198004868911460f03101130b000c4403501d10301c100703100c066500400080c900c0c40000c025110003241800300380d900c2e005000e403582d18021a2440031b410822400c600358403d07450100e00c052030321a5852a414005090b50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228421016 1250 228419766 228419773
    0x40b070605060a0f230402030f070f050c03070b100501030b010909020d27063e1209031809040f060504020310020c100e070b0702120c040c05090907092d0e040302 71
    0x145c6050b000303c12040541c001c1e5429861840c0c04088000340000252a0b1030420000c060300f01c900d02c2c03241c015550035949240c01d403a07451103181441441614161290241c04010b00030000c0c0d00d600910031000142c034180c440d6042c80f0320f80340020009400000d104400d06845c1c90104140c60128202c003410594040c260b140404903c3c00c02d103040714002d0b0030500092808810f07511079010a030488081818a480c1d000d0303407000390321006e00c105019180300420403002540a100b03540b20040064601d004c000440010140d88100410909020035540a00095941c01c00311001c14030542007031b80c0c801c3c000343c00c664401d0f4101000808aa1110f441081ca50b0040d00c1781078044205030190000f0913144200034500942040c01d0340f400c40c850410024400e4074903c2c159020381c00d040c809644030f40c000500c10001c00c140c0200107082c2c0d50102074403034404c0700c21100168100c2d001e4040c2e00c00f59010800c0300100c05001a07503010b44000c1d4a4942000e03444000c40014445100c0303014540700714466400b0303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228422266 1250 228421016 228421049
    0x8010602010f050108030301050409030201020c0a050616050f1801030b0d050102040611031c0209030709050903030103171c0f02090409060207110a0b0a03020d090b130302070b040b070605060a0f 85
    0x2821188080020b0341c800d410000100300702680082504c2c10360b40200e4000690803198030f01a4020710890300300c02d50341e0240414003028090041400ca11804055800c01c440402486088440340b00305e00c02c4000240381403040070800f081c035a50088141c4010f040c0000c8513803140c03001600680384000100c81d20303900041c060199551204c02c50702d84180c0d91000f1801d040b08251540358420342c0350000303030301c290340444c80c10116901000020002c0018960420039420441c1805440354003d020545002040c1c4061401540c80002290001030201c91070405400352680c1d0a00a4a5540201b400c03141c0c09102c0d800d11507503203214101000b8440d00740103035a01d01c01c1c60400688018034501c284a40c0b00c202040020303a4862044030a01c0c07419240050f031399111500741000400412030041d02ca11907030b2080290f002281c18001c86040d000c0d808580b0201e588040b1140303103116a008a103103690050100400041031030308019080200180b0424509880b40e080720b03100c14190744000100b4410010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228423516 1250 228422266 228422279
    0xb0f19090b070e06120c1303080301060c051221060102011d010603050c010305070807030506032d06150f0d0c0504020c030406090801060501080c070311102903250305030a0801 77
    0xa0403442003c0588100b401c0c030294441d05000e9040080406c1000d080014644403010141c40200d40910761141c5482d4030703540c5031039000303002220708141150913210f81170841a21030f0040f819a148800b0301800d2032800410607030f4010303402c0300282445041d0364071441c022046034881428411340390300e000c0001402c0e0380b540c14891328250301134101c181414502814024107680c048400e560000c80c50030040342c0d603240d100100f4a06000044649030800585d004207403c80f000303420081a10548600310b41158031410b40708400703001686803050b07210311880e03518030310383c00c0c940003a0f00c0b034602a0902090b90b80e528400300b002d07a4042000e0b0203ca800000d024402d20381c004c1c0e62a005056030200800c0b4160800d00003130444807014103004d0401c000070500104040c86447c4070802812000d042e10101048105407101a14404c141c164500c2d203458240041510300f000d4105c25950b00400418003804442c031000d255011800041100110706240840441c50400041132454516500e40503590301d00007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228424766 1250 228423516 228423527
    0x115140f0405010e070c03020708030a03061d16110321060316080a08090f10030b0a051e01110a0c030b01030b061f110703060e0c1c0b0f19090b07 64
    0x8038244a00d2622005018003100203019992001050802102a10107030505920f07280f8207912850003880009540c105450740f58008004481c150080605e40c07400c2c1c0000e16441640c01c60300200003084542032141203501c01c00000074424003d1042e2890501c818050301002241048013803074001590050000c542820085002d0360030110014400340c90500c0012511381195402c090301741840883c1000c1c007a42c4803c4c1d5004000c00007840076082407195000600506082d42e0b401c0d2040c81c0300c0200150a003001100d80c18540601182003c00c103465070015a034800e88403080740b04a00c1101c000900140000d1807440c090360050440e809a5031440ca001c0518140041046001c3e600d142c030f0708207403510320091a0b0603070300aa04007000031407042c000c0d1901d010a02c3d40003a006504001010070880c0002ca0501152002603c50304551030342c00000200c401450000248521401e1000591400c40301403903581005008000050700142d8800c01000e03154042010b40341d800e100c1041c441110f4100707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228426016 1250 228424766 228424789
    0x70609140d021507031e05010906060507111c020a0803030907050f09070c06020d0618060603060302010504120206040e160e0316060e0f0d03020f151003030c05011514 73
    0x340001c000210305010000c1d201c0030110742141d09110010302140c2c045000350007145c0c6456201c0c072601100d081141c1450068034007071080c02d16052400b40049030a43c45203048503201034000c0c004810040d424000d1100043e8400c1c01e00c9410300c01c2c1c14032200160b80e43c89200d001041513200450b1203007480070000703081c80f45d654130851040350109c00d1001103889000c1310b581d00c41c3d034a08090182d09410b04043d40a4890588201c4980b4900400881c0948110031000284803203000100541074541c40300341e08846d00d6001c06800b14005000420072007070300340e150b100000e202030483e904140c0e0381c4060b940080c44c203860900c003118182039400320301580800c28030100c071800c130000c0940d00800d55155070b80c070b81c850060b081080346003480e400d00c07174a4001e10041c0c950409030049401e03446a0500940300d04280c05900c0040c0909840f410440c030301401c1c1e140c0600c00e101110161b01d4990766056900c40d100900841c2c0345d540310400e90703c0c2e50300561303100001030401c00c90307617000c040307940381007000030758a0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228427266 1250 228426016 228426053
    0x1b03180901180203100e13170f0702150412080702090703090201080a0209240307020706020c010e0405070314010308190302190309020607050106060306180209030c01200102070609 79
    0x528010080d8640d514a03940b00c01124a0340143c1d02c1c0c40d11a00450604503070b03088881e00c0301030380d801e22081c0c0080c1080048840d01552249500e6003825594110328807690032041030101041c416100986040003500c0427600030754000610f0550f03540c4607400300c0c5251000640b00b40d8000300341c00c000e41c01c00b840000c0d4402054a400c1005031810390020300b4190b0068040a038841d40800c1400058482c41c070351050740d01480c0c007030a51001160101106a5004450120050081d29000aa268000540c4210f4810b0584502040185150900c0014900240001e00301a29607000348070482620048a010358050f611065585c032100641404007405007010008052040003500003d5082c0b01c1410b00303900543c5400310f48000c0d1400080d28500031510003421651900500140c5283c0503444642101d0909981600d81544054448200c3c047d02e52140c0d0150403483c41d0015a621414046842c1c00000c00c05010301d010003501c440c2207801c58001211070b285d0b03c06040381800201030801c10079400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228428516 1250 228427266 228427279
    0x20303190b0312090301020f0301080c0f150a120b060c0a020312070b0103021009081005061008131127041a060a062a030f0809060c0f03060301021b0318 67
    0x12070780c021070f82d204101d82c443c3c101100b0110384d00d40f10395001c1d011903402e403852402094403561a040300355214448040403d12072119454902020304000c1c0f40a010b518052101f2400e0034110141035507030841201c005851582c2d038014100203030751500040d124a000300b000030a60140c03548185441d000c5162005c0c0c3d2000c0040c0580c4002031900c0703903243c0c150703581615400407a03e08114155944083c41c0c0007400d440c069404c3e40d07001e0b03180c1980954407980045a2070f0b0324000d2414800c0c0d50f1001c080e505035103600c06507040b400200d001c00030600d20603980a007101290f59218800a9050003130b1059010307442038003006100038071852024881404083c031005500038242880082d035602a07034031450013400040740314610050319012540b10503043c0322105c83c7d5281990700d402018405c5078100c03a800700f00d604d000f01d5081140040c01520a00d0945205480e0140303000030392030075070801045161f140d9000c008510b00c0590f45107038090162150401540c03107030180351400c078031100d616204900404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228429766 1250 228428516 228428531
    0x101104080309060903010e010501030807060f1e0203060f030d03021c05072a0602130e15010e04110c300a020703030e120d0f0e03070e07110a050d02030319 68
    0x8400300c1210b0015008030f80e407640d1450100d01007805810310003e00d0441c0e5280c40700010900c1207240040010f180701d400c040042c400403400f0402190100307003606081084ca080e40c11018071803940155042403004000903e1541d4000003c2c0c900321081c81c43d800001e401040d07076003da0f4500302c40d40c4c50070b02941005004a180c14100200f1251a9a440e101221100103260300003600e1400c902e03240f203401c400155a248122042100044494810a205d030341007000003900140c0c5801900d440d01030305030354850f4074010f05c1c000c101c084c00c10fa9a0708131180b81c081140315482c0c80d041040c0803501030148040c0e80000c040c1c44442687c00190700d025001c018003040b108c0c0056602007140000c1d40da05040c06004860b84001141040c810f00313284c21854807070800180c03071003508810300415000503075441107600b1105806050f11021309100b0341d0703444654100403406540c01407600c660380225540846860085945404d450b0034442500000540c20010038451000d1a900101c280350888040c10b01011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228431016 1250 228429766 228429779
    0xa141005010e0a05270309010806190b0309070533070b0c0d06051809010b01091a092209050c041b03150b0c0309090f0702060a0b060d0c02101104 64
    0x200424005030103648100217004c150034070490512016905540c038004000f40c205031035513a401030640c0c9001c220310400007029807030800111084a1500d8410454007480c010403502150000307400340c031540c059031101080c0ea0b21030140320001d0710f0146a5002c04481d104078100900c14010701c1d4803821501c04c2200201295041301c17015000300a140c203182c1e41d00410681c1c07a0060405070442c0341d0200d01c5034101c840c80b80c0c0304106980200504402080238510420054034505090311821811004c044500c10040d40c0440c0a85903a040180166000160182c10f09260806500c452017040ea1703a1980302040c40800c1000401201081e101041283c04124030308000b50000052101099119800c3e4500442e020000e000103004107804103440e150390107031035516500104e8801b801941c0860010303075003c640300c0700c1030700840d00d5402808150f00c81c2010300d800b8200003283c10342c0103003081002820516507403040c04115603040e40039000810b1003034200b1081d10440050088984405d01082c88031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228432266 1250 228431016 228431039
    0xc0503010b030303040b0709031403030a050601050c0d0c15051e060910090b0307030804090605040e0a1106070305250b06190b0c07170105100803030121060b030a14100501 75
    0x406e82004d1501d645a662600403504291a90001425215540150080402c00101442c003842d5070790400d1103039944a800444290089506115455000769045606140104c1c18040060700030400406501185951101039490a0782c840c1000b040008010308c1c50155441415004402121000c09030b00b40304103560b43c1d40119004600120fa0703106001c2949680802175140219072080b0302d1900d8980d40c1c80352000400151044d24041c0b0304100c07182c202e07000045151402c00c0d501408032071003100d404d000e10000750408030089052007402c01154580a0035118a04100d11b00300c10380d01c00443c050301c0c18094040020740944c5c082d80c1d60310328101e64a43c04100d40002c0c3d0380e443d0f0b94161514807016441d4544000c07544140d401a43c0c05d07441c552404010b4000d280b08016900b0340303a40711540c0d441c80381e03520702c024402c90082c0781c801c00768242c00002d1101900c02090041e600450100082c0001906109200004440b50741d00b113041045650000c2c00300c41e400f25003d0070200142e600d400e1003d80c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228433516 1250 228432266 228432271
    0x5120703080105060a2006060103060617070f2604020a05040b090103110d021e150f030601030504081b07090501091e05040305040807030b07080f0132100c0c0503010b030303 76
    0x2c14013001c142e101180c1c0c0f09504010030295103070b440c0410900c9040405440d04015200540040e00f0000045803e40c00340c4407604500c014034030341910071354943c0c00c00c8450815550000f410000c2c01101244042c4d01d01010346200e06008500e07502a04080c410030001880c1039022a000d2828200c29140558954107441c1c1103030b42100b4a101c0c4e90b031103000081ca4040950708000d500c201e09080702d18101c28081d01d440380c8040107441642c000003003004046114021003101e03e2084a0400010700203522940000b9001071007110354a08091440070b60503c50018041c41c0c00d201d078894042006a501c66008960051500c620104080b04c442c0032041c1c0c1e2010f0788030043c084152507101260800d4810750486009102650603101c5451303c0340740a40842c001980c1180000e10000e01150804560503030300340c1250460f10b998a0341c1190f20703615000d03040d816204030861001b981c81b00d04140d03c40221a03290302c84c803540c6400c3c03151118503100080c00242e0308076601070f1b0f1400080550580b00001200d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228434766 1250 228433516 228433519
    0xe0f0322060c060c051b0309120a15090f080706020d0c11030d15030f0c06021018020f0a0b0406050403031409030703021908070303080702061b03070c03020c0405010305030705120703080105 83
    0xc3c48013841d041519035200d202e40c1c2a003006256041c6541e040c0c0040045c2036001c1c4101c41485c81b40c42d81341c00d402c5e601c404004014107500c009840e0040c4032040c03a400a030b00d1030b201e001c00e50b90403905626600010f400040b426501281c000900e04800d0b00227102c1d030001d1030418108455012206640316a07030340110700c1d030f245c43e00c0da44e00d01d0203c8618801007100c00039a4060346001800e00e240c034010036800040d11800c000352061040805002c10b240c01031050801000c071130007103202865002c0143c884c45078002c1f0b07034114501e2038020031444d1180d40104080c15076901c500f40c3c0c0b14918500100b503074081c001200503d0400b8040c40149a030080fa5213800c41f0b8040b030b01554108140b110100312a001a808640c1a21590070008201500111007500c50002d075002d8850350b0350f812000c25603881000c20302c4121150204001a10b680c01000c89000c1c2038005d20440f5400840180400d04446081c1c006451030f92003c6403981c10800200b048031022414180010308000c840c0d03070050542d0106000e9103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228436016 1250 228434766 228434771
    0xb04060f03020906220b16020103050a0914010506031501180e070b03040312050c030f04060203100e1302240702040f0b040507080405010507030e10050702010e0f0322060c06 76
    0x540036200e038064424808000b0041955040380c80090072007440ca40001d81045c11070741c0c800003004514031099840240b189541001e00f481d0b40c1c1d00460041c28000c0c515810307190f0306d00c20280800ca82d0108009850a20400002c00382400f90425182c540c07440403a180d100700240040c01380c40c254901444c01c58004080102ea000b82c41010503040004c1c940040360441c078040108424154003881d5032620a4120400300f0094845010840c0f00e4030041340c20040d40c2c0000c40108002034032950081d0f40c81426038000b001d0480e140c00054000034000c1d00d003e0b050020207000345082d8680000074080c1e001c070001c0c01c03440c0343c2080c41700b00740a4020000042d00c915071b20380842c2c208030a260004602103500030010001403414490103008a0010345080c0c0d650740c43d21000411141c000d00c91039484411420081c10070003000308041c0060400107045400715525084c00c115001c40070014035a02c041c002c0c01642e1501c40d130207144081904420340c1881248001c0408010594012042c0c040607074012501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228437266 1250 228436016 228436037
    0x150918020d080f0a030225241107030504090f050103031e030f0507030213051c1713030308221133040303032012070e090c040e100b0406 60
    0x1101c443c1c0610035907001c0d00900000c011014644c594003c00c030484d000a0441045000559181900c0c07403210740c002c215160035075241001030428040c082007901c2d0b203200415000c1040e1080510b64001d13120880c04100c01003000d01422206000303070b03000c50072042c0040003158996200148088001c002c0c018a17851001c4001e4001446500610075600780301209110b00c0c140040020000e5001440c0d8614a1b801202d01040b0b0b031601c0d424200c031200641d0891403a081c0385898200040d4107098007807001030410420790750210b040c0c21004c0b00441c007a4860002c0ea10b07141005210000080f518110741485490441002a032100411042d501003a01c01e01e40400301840d1106074008201c81c1c0c031305424251540b10141120910051042d6446603906210340c1d5200300c1201c190544800d000290101e05104440c0a03452f05082c1c0c5901c015146803000311120810f000c24952441030f40c0c150403440340041c00340701010400c46815000960500140e10041ca0a12401d402d800340d40100300401030354024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228438516 1250 228437266 228437273
    0xb01080f130b0712021209060f091b0d02090901060608011a0313050f0f0609010606080f0103020d0c0f06052104120503091f0903080603070602100b0103090f06150918020d 75
    0x209201c64010500b0466440090008011086c50116111040c5201c0e880010781c2c0000c5045542c4d0040c800c0c040282160100201001f201281c1c203041190001244201300c8056618252074038060b400d04400001c02904290000f000c0b400141c100c42d0840041c2942031a1003900313801260740c400654a0b815040c101c8500d055400c1034140d1010244a1140004c41d5410107008125140106140e0b0000c1048581d140010f6401200032192035006e5000340f0010000f60608401e0300200c0c620814134684450380324000e034006803d1030707041500007075400308407c00300c02d01d0f42440240c040d80e1080c071590301d841c0c01d80d00c2c90041c00100000d00d00304100803020030404207040000503120034061703d20124907180b0001d50001040034074020740c001594a000701d84a814041082015030b905070380502038100502448001503c01d80441c40d0405554811110100e03d0000003a16090f21500001c20b120302442220288007640b0340124180b03500e44106280c40c40502c12040710403507410f40300100a189030b070a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228439766 1250 228438516 228438527
    0x1110c010e0a09090b070e01030e0a020f0303120a0218010816032f030405070f15030e070b0a2304050d11030307050a050a03110303040b01090506030106090c030b01080f130b07 77
    0x1e004402c50f60a01641d0420000f190300c1c818454049541c6240400d03d4690044003511554484405290028000030016041c540b100315502c0c00301504486c540301c0800a540d030b0382c0d0300444003000c4440d0b000c2808a54101040a203c06400c003d117841591420454680202c91002c0d00880050503620411903075141d200e0300b030715207159821068080c481102240c0c851601d52044608031001e00440c0008134503007401c0300b100c2d416241c0030789090408210310030040d4000c0480d1080000341c4d1080c007000242850740c10300107200742110307070b55042c43ea1500c10340d02d4900c0b11115a00600d0301a4140300c10302540c0c660018011209030056200c03c10306241202003815880b480c0400f503d180141c201d510207010f000a00307038601c14405c0e80c50303501140c1c0f0b07019140e0301e90000380c030020f140c08005001001028940d40000f5007214004000040d0150380301c004004441e981e01545000c030351104001c00071580c02c0900164003099507a560310041c941141800c5035074140c00030090807851501d01207004240b00e807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228441016 1250 228439766 228439769
    0xc090b22090606080a06080303011203020115060e1003060806220f081b030301081f0e0d0f020706020109021f090b030114040f02070b06210a1401050601110c010e0a 72
    0x100c1154002516100340c00e0242040d80a00c40209106002150405005200c0c0c1c0084a0002d409542164240044101c0b4a940c0741c400354219921030154852015900034110020941915030100300d855407414040a03c6914641ca8103061402d6000c22507180b0100e035081d44142441c4000192825021030803450389007410740640600000c42d064010031501200420900c1195810450b510780c502941c030fa80c0f44802d005420490700181e0300000c40e100940d003600c1c0b00c030400d52000f041047c00c1c1e04c401807906590401c5140003461500e0311000c0e0a4042c410b0502074290317071009100c1d01c022034020a0b410640e080c44412151410500001a944222100406002c00c1d10115644e560358454030314440511003080c03172249181008200e45107185100b02c40c02580d0120300001c4507035680080144210749000034405c07c64102c00c0c9502c21080520041c403c885c41946458800880810000c0c2110303001400541480f2a01c0c2c5214812000001d5040e40c20800b4686544002c00c2c120102e400c40310744d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228442266 1250 228441016 228441067
    0xd03081906090209010306080604050c040b0a0b030f04060e0d0806130b060406020c0910050915030f100f05090d050409020a0c0c140405100513050c070c030b040311010c090b 76
    0x1400404079842c8680e4000b400107060903030b03003800141d4841400c4e589501c001c3c0d80051059024000c000c9060425411080c030700305008040b503009595076403070700b012a442100c0d0f20304052a007904220400c0054410301440b00c01100050040b2100540003a20203280584090f20684500c41c0d154000622a080300f404140c0190035151030b0742d0340e060060b40d1680380e01040e51040398200000342c0301500c502d4030807040f46c80090001c051034865034203100e650740c980c0810a40600400d002507821140c204409550401a00c6002880d00c0c03454041c1405c41e14082d0880105804c40d40091028642c0b20094800351848100c0069840e07061007801d031a600d86020000b00705840083c0c0c001403e1b00e103c019002e581505540a2016681d03e48017008003080500480da4886880e1851034942091903020741e40c4004c2e0384400c50701c1d0030349a465580c08103806901c200c0354215607104120030594002181c24426140c80c0c001d002e85c4682c90405804400d0300c0c0103001030200c01042210840704190080d101154a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228443516 1250 228442266 228442271
    0x1908010606020601030b01060509010c02040f0b060f0d06050609030616170708070206070c1e0507030812042906100513030606050102280305070317070903060c0c020d030819 76
    0x981c0c45010351907040074803003590707540c0b000d4000064040c00ba2048990303140e4140c0d1a4000c02c060341d42004010070000030075141040d03031410070743d200f621482d008200401c074000750552695082d202220a8580a401c4103016400a101520700e54500182541d001000306099460508501d0001c981c5402c4036600100041801381c02e01134640e400c0021640240c00d035500b43c80107a912f107a0305844035850044014440242902c441c10382500c030a41034102144242c00762440c542e507940781e6008580004050790740807a80001444100950121844a130b1006c02d803070311351083c0512040c10a250401004140641440040c501c0361621440403038031416078240720154800c0c2c8904000e0f000389441d001d141d01600c1540b000b1880c29490716001000e208206400320301d00c40066408803000c4c4c1141070203d0500c49400103000d680e0b182c1a5034a4440d024958600c40e43c00e14501300320f0705807628a40d81c00b0501010b130100d040981c03100180108001d0305400d004495899091120144080c8403041140791071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228444766 1250 228443516 228443519
    0x608190f0203071b0c03060509250e060a0f030f030909020a02010504061505090411030a150e070f120b071214040203060109020a1d010c0b040302010b13020a020c19080106 75
    0x3419640618080c2c0e1456503a0894510316004041c0341100005018200d07180d10396040000418542199a00c00b43c80d0007030b00c1c05010032042201c081080d0038102d07004022140313000d00ca1680503801855021108440e1041d80354640304a02c15040c5140c04081c0c50103501400c11028580200c0301d0a0040106410856881d40c07004d100038001c1000751803c5a0041c00c20b6206840b160b410701d03200d0243c4400511124990310b60365961500101003120300d0703030180148145100400c0403558000c03610030410101240d170035245d2035210b01380003a0307400651840d41072140c140722548689100382001980091042072980b221101070320160103080190303a41a0901d208444c0d15100100d0390750145100742c00310390960b600c50362850240c3c061800c869000801d1940b21903485111401800c04031030042c180108d900700c031030301e9143c500c0e5800c072420780c09030307446030340c20802401c10561110541c503c0c40c0007103060950b007181c0251100e5201c070a0500c035203010f65205d5880040b08007040001c1004c04020801c09 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228446016 1250 228444766 228444791
    0x50c0909130206160b1b0309030d1524020f030f070308060102071a070303051312080c090a030803070e150d09080408070306090312021201051c05011e15080304060819 73
    0x181700813240f0703c1c900e01002c449004849048010b4a000d208a1800395062032000b00c1e03610000c000c0650243c80403c681400003942c1841000c8088000150503110740308034584030f201030700c2e121410149500b01ea0040180701c1c0117030440c90903144c803181c0c14035110b0142d803140c00040b8504222500403581c041ca05442c94501e40310f0150081c00724074401d44007400241e80c1d5200c402c099401c01d24010b0710103940d01c0342c044540741c41031914982c48508000301c141071030117410102d51741400c40d400c01c44141e81d000040c046400e82060003150340f60310071034080302c0b10f11007020780040fa40500e2100c4000070707441701c0d51841004452010f0303c1c041c0901c03c2c02c5402e01c680c1e9091040140c40345102c00d0b404214074250804854250380225010b2440351516442141d292500348640035000040d000d071240c0103800040c2c0050028050031320801d02050290800c1c000d204000812920150035402c00840d81d281c003008600c0c1d000c02683e0484900381400e158503a540300e4000e041c44018a07849030f0303051a220040100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228447266 1250 228446016 228446033
    0xd0501080f01150506090d051207030503010302010318031d04061d01210f0f082a0606010f0905090405030f0706051509040b0a09030e0a030f0204050c090913020616 72
    0xe10503000080c08944240c1800c0703005003c183c00744a4020004200c20301e9103090180b20308060910440407a0150050382402c81d44682065800728000b4500000400542d03a06016207442c032501d1524110b407010b019a0050b0284041c6034070303900d04c0c002d281280402a038132548100001c246140c10955250706154100c0c03842c0c1000d00451441d14038015010614100409842600780d5201400450303082d1a03480329107040c040c0d10310845100300c0400040700c0d0401d40d024a4280713018103004e0148480001c0c0700c0c07103090040083c81d880c104070700314280e6840154480f032000b0440e88243c66220042c2c0720360804c0b900714416202842e000d103900144220030010160301c6144581000460b542e4101c07031030000c1002d00031007543c001e4480c041c0c960204444190710341c080c000552181c1400c1944480c680007007070b03c0c00c42c6580282c40031000002400103505080c00b84035071000e00300c19401c0c0790040c0c0301c00050003500e000c2c11510301c400f0514260740440d00c0340411102c2d580d03941c3c040402034448520300380300d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228448516 1250 228447266 228447283
    0x92b050a060f060b0a031107020402040b0702040c020f100509070b0403050d02070609060e010806040e060705071a06010c080f070b1501020d020606010503130501090f0503030f10060504030609080d050108 89
    0x48441c035020b4600c68407607851003000140c0b00042d006a1038146031800480180040d080310600c0c5110412881b401a540c520062004103030020420752918058010002102c8180d50700d2025900a241480d00000006c070342c41c01c11315000380c80041c01c0d8584000151410086c0d8002407008200081c0200c00d020002030000c1c0c82010030b40c00c94100d591101130403141d40b0203610410000c11503081c8040c440758046c0144070360140001d4000500040f805107507514012040c0c400c900442c4001810340144036a00c003609d030b1410301c5e06050003110b08094000914101c81c20f80068844480402d07442c003079052940031618002e03044000c51110b810010040d0450507015100140948240415071410a00100b9124400d1105864403070031680d6070b29411110050800703040340c06560320105000002c20140c44844280d008000958682ca00541440c0101034040c01c1c00d00c209940d80800c02c80c8a5204003260140c96101501103510320540c549414540141107120301c0781c608000020a41d02c0000034400c0c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228449766 1250 228448516 228448523
    0x403050607050909151c0c050a050402120a2d051905100b0c010f05010311090108030c0601092a020d091d160203091008010e0a0e03092b050a 62
    0x10200c1e00c0c0c011003620a0b00c50034880c50313000104200001e415074000740008818103c0500140c00c1c14010f108050100b8000f220110748031007030550103110794280891680083c0c802550110f00d0002c000c440c00c540120010001e410030380e01c440e807042c200507014a4040320b1858034943c405030440902402005007504452544240118000c40e84019159003e61030013000440b88081000782032038a00c4009500141c013040311992128881d07000c6138118800c00b4001d500485000c2d00c0c81520b40104621004182c0c0701a981741d1080c07100900c900300106a65045880a140c00030348120384008044142c03802c002107007500303c400e580201241e5004500402d18240540d1070086441c4c03528031405007200c1800300c2580912000c000100c3d99456180d8441b000b00c1140100c070304060801e40061858030440c0340040c002418140100081c2203410304090300800c0005083c84120300320b16081359a4003850340840d10410b100103048030002c00000300119178007151031130400c0c000d1250a0180e5030300f0841c907040303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228451016 1250 228449766 228449773
    0xe1b0a050f1c2d02011704020a0b1c0e010e101a060414030c030303090a080c01090501060b070c08070302090406150504050c1206040903080105130e030310050108061e04020703030f11040305 83
    0x107858038603c014140010036816165900701c04621048400c42c008001c00403070b0419240758012500b5403034000a800c2a5070842c140903007411020315001c040e84d00c0c1c6c042c100c0c0240e04240c00031000304804103010740580740e034040c0065500f0302c21164851131040c203d00c66802580018011500540c0302d44070641c511019000c0b181144d680006160b501c3c032045030418140d400110524000401380401040d824507114008242e6500f60340b6400e00f1179845074070a68100000280031000c222680140c2401171104c200070b403d52514507000304500c8031001b44003d00007a99040d000218007400d403900b80140c01c002e001000b0510f428802607030307558842c5034480e000c0354101b00000c500749002d0041e194030a82c5030342d401403140d107400c0900060485280710402060749800d1640300301c5504102441c4100043e01184503c24541000901415005480c4900904214001c01718021164000c92071407401a5001651a089810210010008070a4602145084c03ea51140006c1241c2c0500150ba00450a8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228452266 1250 228451016 228451073
    0xa03050901231503030d050112020127060e060d0e060a06050a03120f1b05150702060610050d0e03040b0d0b06030f0703090215030702010e1b0a050f1c 66
    0x80300641440c035807040b655160340400609a44100d04209440100c05402c4a0908014496203c15640d00741c101011205000e074840c3e080d903a00c1f40d0000003081100c0359802107a42d5000c40070410b801b05009050511100c00440c0c00551503143c1245e102405050b4108100310410400d152101c10a40c0c401c2c2e0300c2c50400f600442c65140c010141c000310396004102d600541030481040e140c0200032a5036100f4403460590000c880b0544a0409280b41d104001500c09a000444200c05861000d000c860441d8007000822500d92640240011018802e0070000d48034a10031003020050041a84803000034000498001740800300007018040b81600c4860910100640509000141c04206e510480e00f40c2c1800208041e20300039408a01c540c0c6c0081d000c041c80310080c90400c00f80c1d5209a50600050b07644000f4040081000d0020414001541c00178600000100c1c0001c1e82004060050520481c01500035082a40c2c0780550f80c0c1090101c408101c81d080000d003480441a60080c0c2c1480055031807015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228453516 1250 228452266 228452291
    0x31a0601030b0307050f040b0406030213140c091c05160806010f121205030c1323030f0705041e05090a120903020a090f2d06050d0b0c0a0e04020a03050901 68
    0x11300000780c4101400580754001c0040c01c200161a000343c00f9a041030395610044050303150402c0c000c400f04500b0300041014070207010900d6400d01c0007000d81050301d506010751980c0b40e4503602e2590383c08541c082c03804099185805d0075801d10034010f11580c00601500340019822001289040c12103103038a6103082c200c0d58420341200c506030940c1009141c4d50000c103007082d20034050f001035600020700c1112941408072500145100c1c20640c3c00580390700e410b807604651180c0c21401c5203044d80d18160f000d881c40385c4c072a022080e6210100e009031071203130b030b142c0c1440c94135951000c1040c0303131200480d032050015040c81c14400f07484525000e020f44104102c2054898402d0050f1a080122a80640310034411031410890b5001841c645010304112502c1e21561110019105284030000080d101284020004101e4000455171103070f20080c000c00d080f880d10300c00318001403644c44c1d00c0380b805110655200350308103085503246e01d625030310781e4010f2001c500c46a101d0750543c03203180300e51102c60003004285043c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228454766 1250 228453516 228453523
    0x206191103030711060a020711091312120509070f0504020708090306010b03011805010509070f0e04060b0c16030203120a1103070b0403030b1e060a05040b0412030306150504050405060604031a0601030b03 89
    0x301902004279100e00400c1c5d03040050141d940006a4154241ca044c07903543c5071000300f501800b410f40000d03c0780003000340014840c8907040d0003804d00c000820b071051611041d00d82c130300c0551060764440c650100d1814240301e40d0b0821918140402029102070307684440710380bc03254200307009603800e8143c1e03060a030240810502c80c031b030305a0f6030080c07840c0055900c003801250029841c00c1130b034041117140007106249072038500a502c06010710070519501d62250100c03107841e002600000301c076413a4510200f00003603140843c4c07022005901c010b55585d5404890f405440100100c0841c99181c80000346c80c41c103000480d00071601580c0f180d542403119005250070080b8250540070031084000c0d0000c03880a807881c06500909800c120380c20f110741443d9403840e00700e80b02e07002540f104503900d00b003180b468201030f0316206040c003401d80d0140340e498841013200010001c0c005c500555003d41d0340c80021800940d500001e440040d0b622051120305251191003451a101e403e031039080c0880d0401011440510300407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228456016 1250 228454766 228454777
    0xf030a24060804020d02041d01092a03140c03070305100b010311120a0605060403030c17070b01030b0c071401150e010b0a0e120307080c070b03040206191103030711060a02 75
    0x10b81c0c1e01d10440d00c0c0c940030460081c1211030700b26400b50b41e03011600b10030f4411920b600c007020030307240000442a445087c15501e5031401010183d00d15516404150001c04120802080d139812000442c0b95040c0039603000c1c5020441001e0a52502c201c0000104000e00003c140c110360002500a01c0540213550055041da100031100e00c08015060094001110074200401e41c0080403080c0461401d5a4901088142e8001e400580003c8c030310080c04014030a900c0585030009000180507442c003a45038481c1404a1018007004240101c414040356551031400d0135145502d410007620701400c200c0c2c0a9650007040f002166111f81c2042c070394000740c01c100d440305942c100c88440c000c00d03203400000701040b5135070614511100e501000000803030046500400103031074050f100e40182607486c0e0b00e0207605807414615600c100e00030b030010410400180c41310010b070383c03001d40c00030380445461016100603075196072031100d41070710303031201104203c0d0743c0e648550740036000c0080b0410b481041c2c44291900041c4d1140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228457266 1250 228456016 228456029
    0x60c020409172106130506040f1d0f16050d0602190903110307060203030a0b0312040603060e010e0c07020d0f150b010f0c050307020d08190306051f080f0a020f030a24 73
    0x185c40070f1429200c0c280c00c07095000390000c2001074a403c2e0000e49108480c40450031740804c101d2100e10101c200c0d4100300c1c82e07400c0d410340001400045084450300ca0719203041c3c01007034000c00c401ba1320042000300940648240c4011100000c203405100d6400420401213071005841c01900d80c60b0705002030501048490685603164055461540e4440500c405881d00040164161007201c444008003ca07c0d000342000e0100340d94089915403504c3c403580c0c409da42c10307048800b004685034180b2444d100110120703040d181e0305445610f010740140c11300300c0040504a10152a01c521a02c10201c004480d900503100d41400742c03030b081400c0c2421082100e2410403e1401130203a0310130440c1201500d4508015811a48a40e009510382148021400070340c0d00c0d20b02d030400110b516a94140428030701600b044540820340441b0340c110041c03640006102c3c2d01c0141980010345119408249600c0c056012250790051440c0c503503690703041110240c0300820201c28803d4140b000e02c00d580da4441603894104045452 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228458516 1250 228457266 228457279
    0x80d080a0b091302010302090303073206070903121103180102070f0b030c07020a1505030406140603061906080703050709140c07110f090f071e0504060c020409172106 73
    0x10fa940190029404030110725070611091011000040c802c0c0c0d940b20304000b9070b010210106220f0590414048181c3e00f0200950b0400010841c202d580b1100355022a60800c0c84d03400900c1030610150350017003540034091114080010030b828000300481e07020301d0914003039085a602c030380c0e950603240c1c0f030041c18010802c81480c1000030818181c108800750104d03500080c00d00c034100740d440400d40c447d1044180d221000c10804010481400f034507100e05000450510209022803800900080d1034100040c1000d41d0380e800c034020381501401c254405005003c43c50100c0302c000d41c690400036a83d5142d4410366203030302d00780079040d01d200c1211991140a64410360300a41003110550303401100e0b03003000450f0394001c0c0c644040c1c104075559100c2d00b58020051210701c0d04181c204080d00820301c16030200d040c14024000b030501603c031a4400c1c2218129500d91400a00c601c040348001800342840345000b07480301d402800c6c482050302e100390003024590a400d500681e61189203004400c5c00d00111002940101d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228459766 1250 228458516 228458551
    0x606110d080601091a0c0601030b04060b03030301060f11070519031416030f030c0204050a020a030e010e1b03070b031e0714030106052503050415030522020109080d080a0b09 76
    0x40c0180c281002c00d14103c0c040604006d17100800c940381107001d0f40b007540ca00b0f0ba05010700040c044a44245075190409070041c1d0710b1581004000b0b0800000d80e260301040202c441c0c100711486005200c4140540760041140d40155030b034040180c542041408262850b800780d507880c2d4043c0500150498108000c50175003417545142d6141c07504031880d841c20690a01201d098070100603940d42c426644a0f1340d482100507241d0b400c42500804a031401142d00060768984004c100d240303000021024111010041038080810400c00464188a0780c2d522601c0e6049002c400d100a207404120018403000d41750320317002c1596172051411500000000b014a9900d03604000501c40d0038812802880709c032580301c0a2103d12100e0842101c52074146190070740008038042400e21441a41d5031142c1e1080200386000e000741d0402040c019440000c005034207580c90500150b0b2011a405103039000c00508143c01903030034500a071340b03014001d401c0031260b80c3d600620b40321180d541842c2c22120140954030360b00c2c03180c2c0c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 228461016 1250 228459766 228459779
    0x50c091e15070510020c01060315090b04150f0f020406032004031b050324070908030301090c020a0c06020f0c220e030409020a09180606022e0606110d08060109 70
    0x154402c51003a96540100c2045040354145400200000c00e6100000503295145041c04103441030301722041d8070070710704100c50310b0045100e401241d6042600440404018405801c4003001008020b410894040c01c0c03240071501c8016503409041110322a072014810f24410300300d8070038061100301e1440a001414041030001c25410a50b040325244061246090540c42d400000d160a00e0106800d481801207201150000c84448020f034004010307040100341d40d424082800c0d100d000500600c070701190788511010000f4420402410082e42200c4c020000d5a22010020b40ba49461401c000c0c0c00c2c030035440001c0035800d08141d1000c1c1501c0800703030440114502c07480a40034100b142007825552000b0711000c6280490b03440200b488120b00d1f100c007411140f914403c032600000c00300f500903480d45400000c124464001c241000140f040da454078607800a042d40304500340b01d2040b248100e80e45480d04c0415100e4014021240c0241c0790011510704144040d021078041e00111015400170391540c6040101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 228462266 1250 228461016 228461059
    0x50303071d0909013306030209031603081b0604080403110d12050c1c08010302060f040902070602091906020d0c03112b08070503040308040501020904050c091e 70
    0x145074070044528100301c446000107881034016a072008442e550354500f05044500400e11500b91040c4c01c0c1d641580d51114044240c00395038622640d4181a00002c042803555400e100c01114108010000b0300296200c2c04c1c81016504403503407003c3e441a0b2a172020080210002d0301600c40d82e4800d803406c3c0740a0441c0e9492407e007400c00c1c3c060780c20884650b03007440040c0c200c1c104010480c0c1280c1c0e03040d80f6a115030310020b240010f4407900b10308910740f42d4900110103030300c1120313181501d4040d00d240342c2d074034502120f00201d84501c3d88203c4041d44080342201c00c02a59030000c0840890849136007260340903a078004640154180b00702c03009a40b00d100c0080d40240140c0044221070f00a0400001204049001d03500304001a210042070701095060408001c8021250001c0398406183c2041c9a2400d13000143c001d102c080c0c006024810090002001c02030250120741c910300000c1c109100d01d007040f52036450703550012615a445180030448070b0240c10b044d1202010f11400040c451030145200c3d0803500300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 228463516 1250 228462266 228462287
    0xa0603140f01120609081207030203091204050a0b03070c0c03050109171303060c02011e0504020306010f0803040b160f050c01120b01050331030906030c090806041b0906030c0e010504060305030307 86
    0x4c0724a8140042c0247d40300350006e60784582c0c45910056524079000a0b02414012207a48070b414554040c4004d11036519032030903140546440c490410307505d4441c078109a9909030681c2c002014255400408010424190042c2481c43c0c410b14810860a6182107a040503000715100d9180560030510b0400c00710700150051412800039000008030041c0d145614800c84c46806800300303c0c991100c2c1803001b107050030001c450050003080c10040800f82803004164482c4986d1092038162100400c801348003412200143c4622548440b11112011240c5040e940b5958501a6a40400c0026141500e040c0007030040303c00d5030301d0595525185a4800401d00d11000c8200c100c002e685403090201c246802d20f15100204050203500c800441515100300102a41d00000442082124070f0070100800d650001d06150042d51080709500c00d40d0026441e0300000c607003940020001402c112000050000c51405841174504800218005030303250000c0c0010340c2c03034a1000401a500800000703c001e4441c4200c0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 228464766 1250 228463516 228463523
    0x5101a0114090604080a0210030b01050a0f140a0f0f0302090315040807081b0132090a0b01060c050c03070803120c090d030809010c0f050f0d06050a0603140f01120609 73
    0x50a040b140008101650401c1c1c01070b0105d0703445031402c0350542c40c0110030708015200c145010301641042000017015401681601018402c800c0c48070b21225025442c4d05090703110300f044130b9880e804950001441c020f90351505030003040f14000740340341ca01d12078004c807682501c000e0000c0207503a01c8580701e2034103040028800c1d61081028001c40002520503001404200d81d6500303003485040c20841114210f4801d00c1c0d1072094061210a1101c1c03080000c02c44c6001110024110b08142d83d0398a074850a0203808040240000320b00400030562907006610200400e000c0d90460303d8814085041c1030303480046014050142c2d0090010120008522840d40c0e8000300d2410820308000c84840410000103107030000f180403c01c40410060b20907003d2040d104404002e2900308bc108c0007406020b0643e21520030704541907000040c40c0c0704128090f0b0007a200504010b0304204076107940c1c410013002020105242c0304070140650126106919880b58a03050f44c03515089151203580c1950b030100100800403045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228466016 1250 228464766 228464807
    0x303050a0e0a0812040e070804020d08070f050105071e03110301051903080c2a0f06030a061208130816050409170304260c060f0411030f070305101a01 66
    0x42501801401045004c2690008035078035170341810f9080c403d030303840180900c04001c809010440940d8640010381d00342d070f030400100c40da0740b6020700b840307040030810000c05008d640c24007080c0288240d005507107554120002c20446000c1150030800c82c103407220b00d00030700c1c00c41400b071006100350300c1c06801d91401040b462010419036a500d03950f6a8440d0001d000340e0955400900c0300704200c61503042006400d130a050b1341c845180c403000300003031100000302c0401400b0310700200010f43d4054084d0f0005026091810f100ca40c20720451410030125800740100001e1403d814100140400000134580081202c2c20110306005003000d00b884002c01da13043d000d4a081811501000042c20707190021030040b0f00402d410740200000c1d0442c50001c9540c02003140e2210400c0010b242c0140c4042591500020404414800c0f5100c03400c008040c1c0040c4000c441c0e02d801130400ca01070b69400015600300701c81c0700e0740030b4503d100c16290121040342d8454031900c0c8030604d00042080d0542c4a190502200c0000c2c01c5076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 228467266 1250 228466016 228466019
    0x40306180f060203010501020d030606301401050f101707050d0e10150f0e0405010e0102041d06041b051b0706110606030d05070b04080706150512070303050a0e0a 71
    0x1c89880300346252003034031001d0340000144036a590600100e10003036468101840a6441c1c103400901075402118030364055805840d4121000e464080d00e034240d07101040e428480381c07105034121001e20100384109807054411540643c0306085c584c54202019040f62152180d005860111207a0a90000d1071701d0304109040080038003d006a1241c03c10648402e0002c1000b0300000d4141c02c2140d001c00c40115803944198030402448004c1c0e00400c0a40e80c1000d0010641e841d58a0b21a01401c0c0307080c01ca800a500210b4003149030310303002d20185968107603c0c029210325111070060008070380d66001100b5100c910400764400160141c0002d225485800901640518a402d105401e1810301d070011000606031110415214204200030b44c0c0001c0214060052202e1a850140041c0b04241c0001c040c11755400c0003601303100d01c51080c0c03040e55030460014042c55881c01007900c0c5804481c061f1f98031851055100010460000030070750152941500c8142c0341c207150040036a448007550350080d6104008960 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 228468516 1250 228467266 228467273
    0x72312120304112d010311030606070204020d06080d090e010302010e01050a180b040f0602011404030f0909090c0504050109091a0619080a05120a120207030311031f05030c0604030618 80
    0x1402e80e150184010344404c1800307001c035008801c046050890405060021000150074404101d0b90004421200c8030341c1c401c00323803001c140a03000c0c00040d55080c52800100203110200450b140c09040c1c0303581ea50071441600d40e50a01038001c020b000290000305400300c00c105031350044008000702002410400e490b042194200f04622030706820102c2c1900300840c0800c41c0129020403040903101c5800280840345040d20304000c1d022006001800b08032660742e00720002e0780120144000380081c0201480030360708038101040900300d1485414083e51420000280308901840341c1e0a40c164480c0c083d5280c00d090f01484000e180c0003030011944030321450785892000001c448e0501c000c20f0300c1d5010300300f05100790822501b0101c1c04a0050704441080000b010710560103610b03160010805c540058a038000390604a00805440b46100e07207141000040c042429a181240c080c0c02c000418420a600c1c3c4603000d064a5500f040304951300f20350144028000141140c00110304c0005102091024651689 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 228469766 1250 228468516 228468529
    0x711010e0f13060503100e1c030e10090203100603020f0f031e0606041808040306020c030f0a030b0a062c0d06090807120905090f1807231212030411 65
    0x140c05000d83c0c0780c0b420030140c00d05118032105201c00b1360702080a0300b409241542c4070015800218504108040c00141d014041d43c0854a1115917000310b030150420040908000c00c102c0d0802d03846031184030010f41101406004007001e50b0380c0580b241207207002080a01c03070300003da540081c0d4180124600c001100c84c40d00128401c15031044010300280c00d2510910085402d1001341d0580c001d0081803c10110b5441800c90702202c0d030103100160f584241301441c6086000d64074040301811400143c440303015503d0741000d440210211101480996604070a840e80d0408107a001d903489203810a4480c0201c24103000c0603c900c000e811020305608554800044038110b03d0100c5410001155603402c0c48201600c00b059240e06082c03004103e800c04001a003084401008018461003450010381180144a005480441c044044071003403a10b5082d03290001c801c900c0055840c1400c01c140f150a45002008510110789140141c0003000083c054050664401401541d040011001030764090b101e88 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 228471016 1250 228469766 228469789
    0x302030a061e14090417030a02041208070302010507080615071103071e08060405100504050a0b040b0106020114040f1b0b1908010e15010e0109080f0c010809030711010e0f 75
    0x80300811a40c1c20118090350304034109103c1402a04003204100000d03024120f0040300d9102490441c1c0c681d0390b030305108406886240c000140e42c001d2074600c0380c1088461001360a506103c0d400070710090351810300c1151340110880d0b41640c018044030505001009000003089502d0140105281078111403020070f04e41581a072140301c0c044104520302e41500c0490720010080d00c0c1070800f4100034142502c41070340e10007590100b9003031306030380b0b101240c00c000b000c006201c0b0059015661907142e16150070102200b4100740f00d40c6026500b08840c00032080c400d0520070f44a15803201d0750401240d0706464103030301c110300780090802001843c80b020600c0200d0340301614410341c00340307401034500b150044010500300d01a0702109a107602203040c0140180301200b092107546085c07800760354080300400101d45010040c0e000082da8080e240880c2d00c1042d000c01c40c1056000c082c1c96181071915080040b0340c0d280f0070380d20088c6c5032096011031040158401c1d050301200160080008500035442c600081c00746021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 228472266 1250 228471016 228471059
    0x150a0306051006020c0d1703130b0403080601080106171602030f0403050106140402090d14070518040b060102030f120709090c080f010501090f030308040203010e0303090a1401060609060302030a06 86
    0x1940c0d0400905604100c01c005e080401d86801d52403582c16510301d1205a4030842031081403802000050342c114100b4045141e068219543c2c00c500c8c1401d00380900015415240360f4005414500042201801141081900e403000400106c0d65503070750f007040000c00d41c074049400c114041085113401c1d15501c40090406140280000035045103080030443c800c030099015a40614014080c5856030f030b44091647c01c009400185050300506145406030800c02c1c140c0103103902c4646d2a114030150420100140c2c0300d5032150490707503055242c070030059135240a0300c00b0151004004010500c22400c0345001a6000512400d000803801e880d00501000e6901c41c480000c0060701031000c10054001152085004040030308201c40d2f2281011030850381d06005000c0070b018403a2100c041421518250311a40414210b0810b8944906144000a84403100800b0a80c0c20343e50030410601011818441c80040300c000c0d446a00702c0c6441c085c01030700650401401d514031160b46e100b00048410b03241d004034562061 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 228473516 1250 228472266 228472291
    0xc0906180c02070501050315030a0b0a290d12090305071220010f05070f0b0103060219030e0c0d03020f06010905011a09060301030b100b0f0307030b040b09150a030605 73
    0x10300890300d10848003660010030465100d2002080941d070410304587d08010011511001b103801200480d15105030281d00030a6140a0340c20043c2a1400d50302080451040c034845d1404121451680303110001607605c504c1d880010302c081000040c02d0340801a16541d4141890140c2d10b64a032242414042c040e400300e05c0b0300c00e40c00255800c00046402c0441c10714140b07200360401e0081080004c00c5007440740954006c1c0030340011001c080c401582c801c0c94a55070310080b500f400d9a1a0710380314000c1c2d000350164000c0c0742034020b480b280c800d001c0d01070038210042250043c029038689008205004c02da1070001c2d404d500407146030710480c00060114074007802c0c0d0300c80042815450a00051101c644004152140c800148030500c0d450360340008407411660003018916203070300c4e04404415180305540c0203400c020340c00074842c1c1d0b020310b0700c074003079481241d5030f482c10005c4103008001d21082d42c4042000f41c0d4041d04580002d080810620600c2054070780103406044940e84036950841203c5095404810801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 228474766 1250 228473516 228473549
    0x2030405100b031914070b0c0705040b0108041104021c2306060406021b0609061809180a020103240f03021201020708040e06011806030c0306090c0203070605040c0906 73
    0x201c003400b07010340c0004150300801d83e1034028103c884651101d0760000b80b044007040a42c40c221141002100041e010640c43c00746d0b240c0090a10f580d0320760a603c9076a010b10f0401c16503604030b42c040d90a042c80340c0c0c1c1000500e41000d1143c1c04000003580b16030078611a0308240340c0b4100844416200742889038494841890310400010641c601c0c218008202c0c900c154001c002c280300702c40d400b203885411201103503103a81c0705640000c002511406034040b0b01d41c10500c049060010344088140030b00d58800d0a03500040e2036150380000d40c4129465003003000355584014150790040d40320780d01500c504001c1012610340f00c41401102040481c0c15401028444061141402503103882c1d08010140d03c1c05d032000b14a0003080369688601d42c02148100003045150b03100044069004514104e10700c510031112005154403690081c004008036400503001030314042020070b01d11914880c01c0300d0305100d80c00442c20001c05030780d000040d100082048400480c0c0200c0050380360424094040680381103a0000c0001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 228476016 1250 228474766 228474793
    0x80d09020909030a1b0c050d0b0a0e0105061f0e091302010e030102181c020301150e160e240f0c1002090a060e0d12020d02070b03040512090d050102030405 68
    0x80180221920750402c00400241c0381d04400d01109044080c1714208400c0c50604004010303071450740c405508803140c0c02c1c0d034204204c445500103101e441003900c00c11a1100320389040742201c100725210354008003041444901e05c0344e035584440d00c40c40c00b841c0c03980412020002044070760005079141d01a013410640072500b10741e04401c0c01c0713100284c2035001314142481108409096190407100c2e5010b640c80c1910031110800c5c010f40460066005402400611488030b11a4030141d62480f60300072030b603000c001291505041c40d20034801508203645041410704070000708600140b0380c4000c9a181080800301c081c0706034117a409040c501008490140d2a41020302046040034211104800c0d49481000740c1c40042d5240b43c01c00064a4407482c0894a0b22a15408074218081c4520050000c200c590190000543d00068000500c3d04550030345600ba0380d200c2c25004240000d90340140316410283c52265110802000307405410300060000c0440c0c5441e480b29803ca07441503d0984103500555480001d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 228477266 1250 228476016 228476029
    0xc100c030b03030f070b040503160305120f0402030709110d06080106030201020106061103031b0c01051017070608010905090106030c0b0d1401030f020d0620270105031909080d0902 79
    0x4070030041c0c0c059450f1131088061406544144a4010f003505e41c034001040501208005680c0b60083c0050800180001030038040c02c5504041151400240f561000601c411400d0303030703070b00e000b164050018940a400c0c44240c01c054880600040049a018030100f0341c101c103280200d40050140c040002200d90440c0002401d4030300a40101051103a14250000f14207800001c480e484241c8800b03505590801541c520501d105900381c1085279070800c07060003006200d44c020902245c80034a4002c00c0c20b4800e580330741d1102e5040c4100c0010510600040251418035084107a01108071000000d0307807a1603550795001071505421170b8284031030100303511655621601c242d0300030218804a110b1903604d16074442a102030340c0c81000b07000710b540c91403200030010150009a100600d00c600080346a0440180e0b45254110811020703511140e1031390f00484035182c0c0070214082e041a9611481c0d0303a83c8102a80180100c1990a105160f8402d145008107492034040c00d0801d055100200b44500d460041021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 228478516 1250 228477266 228477281
    0xf010603090507060f0504050409120905120a230a0308070305060d0807080a170106050a032a050304030915080402400f06080c1207050616080c100c03 66
    0x24589042103040101c0d03400a0810111340c0d035450403000100d8208000c461901503640840d801a04100c4094200003584081800c00b45585e651800d001380d0381c10400c21805c19411500510b81c1000d1841c00208110742e0310740d00443c010581c442c100204e007100440c5003861400c029000a8803d006000315940d00d4002c0030b410200403151303c520b1811a07110100d4a1091340e40040003003070005a0004110700440c98041c00351440c03e824205503946010280540d0b001c203161800207440c024608441d200c400f1140ba264016140c1d180c1115540104151220750001d4015800e0040c020000030355040c00c2410040d504101f0750341d1501071305062051203a40000101c01c00d0a40c000b08141d01c000001c0664480103007100c1100305014000d10001d804014a03174586020f500724140180840d010314009000e540c4e4450980302d0001e80741a56600c1500c42900707020312580090300300300c0d40c200a6509d498902801d030044100e5403038003501040c03da01e080d815210039480f0a4403540c040a905406125044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 228479766 1250 228478516 228478529
    0x70f0f0302031b120f01050a1d0601050628020706110f0c041503021f090503030c0c01050304021804050706080c0c100f1103010f1503020a0507021002010e0a03080f01 73
    0x1405030850380040e44862910106200104180c042a034207999103401001c0c500c1035000a442c50250300c00c0d6a2400703001c0403102074142a040c0318084145294040101c0c820349040000342040f64202410800c4580c071810030b080c80c5551082c840b18820b410081414031803001070b001403c8003440e19030094640206078182100540200d00c200340c0c2c050010403078068048044400060440c000b040da201d0341c031007580002c1d4000d47c101e41c10031480fa10340801741b000003920b502c40c3c05000740e0b118105940c0b0b10894000c081d294001c1e40e4941c09070350240c005190460710003820b47e0529100440041a80101105d0a40e102ea001d2501004400d401c130102d103410440c10303440d030703840d10360980c11141e903441d10500c000480560305c2c040380140344d01c0b41d403018a071000d900740d980d40e507035a441c000c1e0754181d40035005440790414050000ca007070340d0080c03080b58203e040b40e0300c0c0c190409001e5001c0040040441101000359520340d0b070070f180d2000d014414462142d03c603071035402d000e04214882284001c8160440c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 228481016 1250 228479766 228479789
    0x5070b0901050702010309022808060105120d0f05070b15040b01030219230418060506040302090403110f0f0307030207120203060615040e0726071b0c0b0705070f 71
    0x15200e640e2003070440c2d010325028240820301980c1880865031600111072440c0b0030359800185616110302c002c200d07204882c26181241d5690b43c83e0340c200b00c500249032404031210703031010402c0341c1054010a080ba0801d1010304002d42000225221b8026500045078904c034203050600a00146103044e105e0b07107080302028038046062030340d0a1072a0940d5441c01c40c0041c14040b0004000003034401d88001c1c2d148413101a201d0584a5a40e800c9070288403440c05c1160320071900b0100c0125640c02c100c0142d074200c90b0001d000c620244c80b1510103503040d0900e00610540f9015030301c03119140600410070104000070141c002c50b600c4507541002800c00c3c3d1f07250040d0380d00d0300c0305201d20700169800040c2d564220f0411124807919660004100c8040e1144c0c3d840011500b08040c00c02c008260401001c06090460b820010280c5150014a0b980c5480445a8501045c3d02507010869002400c243c0340302244510020303103403141c881180c0b88550700225021110341e4405c400034460190448500402800a040c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 228482266 1250 228481016 228481027
    0x60a0503090d080f01270e150a14060d020f090106020309011412010311060408060916240f0504030605010f0819150b2101150807180203040201020a170705070b 70
    0x31880c0405040c45400b8801c01d640b66800f9071b003002e4041400f0b0f08802d500d420804000084c030b006881d0412401c03a0500c540c550300004404050302d0180800000400110010a95802d000c102d061561200d05036004152800400059219514554042c20294004544500005000518560070320980c0032010b901408110090070b1b9085001d415a03a12901424508640307602103801409590b0085176144201414403a041c140840c408225841013958540080d413200038205903407d040401121a10080701000c11052091409107c292000d1801c5440c103030380d036210b84080c0c890030303040104003500000040100000400010031900074100354404c0e015115204c5004020800600180e0130b52202c5203031800d5602e22122000e04a02c12400707010300e10080304020300801e44016008a505099080030685480c0000c400d012204140c0b10000341004200f2803a02035040a00200d042d88142049a0300040380d0300c4250b42002e424006081c2c80701c13042d0900c1ca140030007a51100412050030443e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 228483516 1250 228482266 228482281
    0x2304051602070e0a140106091a03040b060904021f020303061f17220f0201020c0916121503031107050103020a080c160203340e1b09060a0503090d08 65
    0x40e40401c4441c1000050100e61301c0340a04000352455803031840320452070500225060350044041026901c030584d2003400c550350400340704074501c01564003034802174040c1c001841d035141007061940c0c4a0301c045c0c2074414500000548105100081c409803025030408001c106041c10a1590324111141e140d00e203107008001510003502c0008070301000c4c807848040d00b000907400e050880c601030400c000c07860007680460f00ca040c56040308000d00d0080b801805000d1884180d440e29224044c010000e4101e9800d2180d85200d00f0f449500c041d10318040c07045d841e041840c0c5006d0101200500850181d00d422560750304134402d00d030924140703400840c180352041c0302d4450000d038400043d9500040401c483d0760740346074100c40d24505100c043d40c000d50500c20940c0c0b444140074114004159900381e00e40310240d045141071a480265070b50b0141e440e0721301d031400000710025611798860a0042c00f11131910300c0e12110782d021401d65437081c1c1e10b200220754000244040c4c204c080004510f51056842c1078000c13418040c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 228484766 1250 228483516 228483523
    0xe0f01030b0f0702150f0708160806042c06010501080915060d03051201180b0306061503060d1b2d03080c01020d02070501090212160501080705042304051602 69
    0xc0034040d0b8942000e00040c01c0c5402001000d4500c0a0001000d030300f880c20f081054070040080301d240300028a01c03400700f000645040582d0505d00840c1d02c0d40255551900144001400054041184040c01a8407111b03140c80760084e1a000081d150041c105542c141800074204c118054801da4540c0d000c000000316136101504099005001160f81a20f507000d0b0707045c01c0300d0300d020354200c2250185e0140000524039035a00004908000d03141b509010402d103d030101619010221401d07600060301c480c2074406a05460010760b441207001300f00007029140e0b62220b951f80c880c2c2c8001044068501c0200340300c141c020134105c4200641c0c150030026042410003c459408003d031000a04201c1c0100e4581c82d142d10a405980d020950028115240e0031142006800303812071020580c05050496046580c2c4c900c0440d1290110000045008a41d480c003c0112061a001005e0108005041c480416180c1218600030107440d80c41e207a00600754601001c20080b80c802034400c10303d42d551b501c0390101d540d0300803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 228486016 1250 228484766 228484771
    0x14090105130e180615210f011a0301091e170f0c01060906080a12020316060902100905180403031407020f0c01050a0c080f131217030615030a110c070e0f01030b 70
    0x16200c20320058811b51400c00304100c140500845400b680002c00c52105055003d8401d00c0390150040c461421a881410b007201d000780700141ca00c00c4805a01601c0241c02082c024200d031244461681c4000e00d007200340900d4100a480c8080c200340003c007400c0f20203090042001904002c82d0801c4002c0c513141c455951810010001000c0003210101034400500a1040c2c1c1c0c141140040c410300520320526148005000c90301c0228440c075032401c00d60700620700c0b982900c01603c0c0058450150484103103d01069440010801c42c2090b4891045200362204006454043e8074290010038000903031800490a003410403800504201007801062481940315040c2c9040540080c10903948600303c45412045114100702901911420300c00010b1801c80c205131b84c0b805c64004c0880300c0350360000c40d0740b5020511081c4c0754281c0c482656070036880420880801107030016101031000810400d0401000c079160441d6200c0303031851300490402c0040c00e060b854000e600c88102503207100b2541c1150380d4094240d101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 228487266 1250 228486016 228486019
    0x1b0a111e04090204201c05010b07031b1a0f0f070e1011070605070b010b040b1206061e0409060504021c110d0213050a120314090105130e180615 63
    0x203500c4200c2c01d42d00ca5038000e804d404104060702910300780000e0026440d5002111802000305482604185041244182416604030900c210300d82402501c0031290002e2400004038003004009004c0b0008120307040481c8041ea084c0d862040500e0900c401410800c0011310b5a882101c0c3c0d60100603285d68400c0784803840e480c084038032201441d0f0701202201c1c5002032440c400d85a201c1c403032006c100550040041c184180c8102140ca005a8940c0d0146015005030b10074801340c100240440e00040b00225186503201902810503401d09030008660510800c0c0d400c1410f00c0c00100040130b00006c809401150007800007a1802d501e0a000141c400182217074030b410102d01c580d502e0140f5910348610004890103084903080541d107884510340e215208040600c101807103103442c03000001d40604150031942c1310b942c040e07c810541107a201507622a542c054403825042100170131125840d5100900c40001405804c00c9044540c40e000c4038a07a0b40e162608810102c40d070001c01084004003140e008110740000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 228488516 1250 228487266 228487271
    0x307140310080a050a060501050d0b040201080c0c0616080a110304020603091207030509030120180102030c010e060105090a0501030c060509030a0602041205060a1e111b0a111e04 78
    0x8070350808600c4401d80e600108118001d24003803d051000c00035012400b2806580200a41d0366900e08000341520306e044010580c01c150400200598001c0900d294008104908145017510489145003040812240c04514a050520355141c240c0c0c0004070303075032186418034200402a007442c003284650000500083c4500c500000140082100f4480c0054010036040820b4880da09403070041c180790071484015000c0d61030241491461041c1c00b41185d05548099001454108039000380b08030104002c3c1994158481003040800c01d200900c00c20004801e4403020380ba403941000c0403c40d07003180141c440e0407000e08101c0180049810f070282c075400c035034083c18155a24040d0402007428491010009005140f010400203039a010040300490318611480541e400c42d526005042c04965100c040240a001a40c9a50002e00c0559021207860318044002d030382403156000012030411011006001180c0066084c40200308111030741d02c844d6101202d070a00005807070581c0d9541c4900c6e4054051080e45c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 228489766 1250 228488516 228488521
    0x307020a021c0209010b071b060804060e16080109060b06210a090b0a270b07030e0a0209010305151612090204090b040c05010e060c0c0108040311011505130203071403 73
    0x100d030540b801800b03901416030ba00940e900e0200350a01d0300441c40640e194900d400c3e5101c0003540300c22107102904c02c5c94131903402e151620380303c002c010b1030400c3c031014191040c03030244003c0380124440007000b000380000126400d0001d20704201a12114804203009590502009a500c00400104001c008504500810558801940c0d1000e0b10b842c0d5409044001c280781442000400b5800c0305001a004039141c480c0708004610116560707224a5001c0c1c10085c2c50004160310303034401c1e0082c40c17140c19084200c5059505507000a400c0c40c001f0303803044071152312105000680c62900b010003544007110042841c041c0700800030240a00c4803c1d212142c4160ba100c0f011000c541d00e550096000340e411640d0030855240c289055000e441c2180122400325401078042d041d503181c15000c80c0c2051301f07a40d02074410b00c080c034001540d80707a100be0f008400b40211918504a0000240726115160140043c12038550b85880e0034000007840c252130501d6040e00410411403d55080a03040c00040341c03042c1c0072962036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 228491016 1250 228489766 228489799
    0x3030c1b030c0b010e0402010804140307061a03060c1c050709081c1209020a151b0b0601090501030c08150112020c01020403060f0b09010b0c0106090e0d12020307020a02 74
    0x10203942101045920408a1509141d448103001210b10311890030070320740766240d820561030684100c80080c00102880d00040006802c0072401c0200048003040b2820a80341e6a5098150340345410030703030200204c50341020518601084001d4000039600c070000d01e028417042201c540166a0031a020710592508041101103204820300300c02420035400f580c064043c20a8210a0310019440b50400200b8050101e0442c1c0d00d50702c00d05018035070041031001c83e00e00d001c1242c07019210030f103080c06c04d200c1408ac1050f5100396030100d40d45c0c001e100c0c0300212801c3c03601d00000b47c02030702c1640106041601c0d100c604031000f40c2025500b5044210141d0075241d1034078480048070607000f0400c0c032030800c5002041c1106000415006031084c0c9115030030a00c10102d03050504012510306115095200c101d92004003c5504804000e0244255a00012070708a40350304030441074550b41b80c943c140702c2e4441782007001c0c1e1a910881c45140507c1c04a400d524604140c140250344400619029108514820b85c00002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 228492266 1250 228491016 228491027
    0x1103030403181a0a020601091a01080619030b100e0f0f1803040f08011113030b070e0d1217040b060f03030c1501080d09030f080c010f050a021b071203030c 68
    0x20f02c51101080c03440400001c4155140e004541084054404c0d0400030a00c080d01d40950240303134a41c20508440010500c0045075582805014150002000803180d804035180c100c0c5400031354050390503807203207041100b810041c440040d40300e000304000150501900e1440903038201d03004075100d401d00321140c8895a259000050040301c0003010303c0005400181a2803007a540811030709540000c000e14604807514050600c02c852000c0d5034500d801030240300103000900101c2d003040b02440d0100c0034100f83e00104030500b6130f104064a400c01c070a0030202c1e00c6540000b1148400da42e50140720703424100741d540c1c92101c810142400c1d21072101c4450a5034162020801d03109041c8120044030702d00842607042e000440001e00403070685000340c46003064500d0148024000300c90b4411304032a59107455840b031b00710743e4110700c648071501d5483c0c00220741860080e000e11070040d542c1920041e62401801c0c020f460b81c0fa000c40c01044660003000c001c20201500707000344c01d10903030181130110351a030414108450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 228493516 1250 228492266 228492269
    0x140d060e0604050f0c030c03061612060e190228120204091406030703030806090402120d0215010801090803010e07110706021f0509030a0c05010e240106110303040318 73
    0x2451241d14104410b0280006403e40c103880c2e60015034030b00300303011403e040c1c5480c3c2ea5581d60340c06900200100c0c5020034290803d205a410505e821690442c0e14500c0c202601da681e480b0b12205a86801404030020028403545821940d03030608625040005881c40034441c44003c50810024160703401511050040c4a0407800302a504021552503403101d501c1b00040c00700b5604402080b880304000341140c1800a44041907a42640700c0b80480e0780c9100c100712354050000d008036044140c91031441c180ea18108040000c01403203030040c0549080d211009000c10005901c09251603040290744d0000c100e00c03a0449064a803000301100c5140e549010a942050b121200e0010910030f52a00080041c0c0c040b0741b101e41b17401c518100490022009040e074080c2c483c155150b00700c0346c0040001d1042c450040c00100c0c1d25504c107200129908103a1010507041c903014402014a020789020b85010801d03040641d607014101504003200203c504180c0156280801031000b001e028200c0f02c211f40d0000380d100d9000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 228494766 1250 228493516 228493541
    0x204020d060b0d0605060a02070e100b04090c1e0c150207020604030c08011b17060a08010f0e0114010e07180b0708180103050411041e06080307140106140d06 69
    0x80e007999141520900c1e803003030f10b145a1451900e0000b24841c0307070440803110304000941c01064002c1c01c0c03030020040400c01801c1c0e0340003000340800001d0280c482e05e010340010817980500140c0505010005051419602d0006401500a04220351241c2c3c120380b00c1c00394a0780001900e0350749001c1c03405040091040e040040d5020300017103000000c0208045944045c3c5400600a01240c0310b4000701e45a030a80c54040d05004c2140421000c0070039000d030300b40c40e90106c001028100056071302c40945003100e200001e410075007a1240311000b0010401d02942c04000c0380c004400c41158903040381c1458070074000d00803800b000b030150012a0607084107d1403a000e440301065150743c5850700d141801c100e62207105503003182503400281d41c882d50b0091081c0d17442203402a1791142c0104600e401c1100821303d000080080c1c1c072020400311044002031261034080c040c41c0b00219545c40260800c00035416007013a100d03405a0400e0018000c210304d00e9140b103104802516403602e0320200780703820006400500280d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 228496016 1250 228494766 228494771
    0x3110c01050712090f0b1f060305010f05091611070b041206050c0901020604030e030f060c0c16060f12020d021303230303041b03050f1b010903050c0d0204020d 70
    0x5484044040d40803901400341912505194408084660103035103a030400505000e180c0c80400c4045240007007066801001c07029210605121115440340c0c94911703400400000343e9a0700103002c840244042c0300041c050846101206183c03480d16030590a41d503a50002c02c201c0d6022200709800c60030042030340548141400940c6542d03d40c0d03a800035030481c3d0308098800504000210b20885603141c201c1e001d00d001031b400781120740c0d2662000e0303c0800069600981500c540c0494200030101806142e015000c02601c0a580340e81415a01341740158603000210f03040e1000204100d00350f0004290401038040d0300b040112181045111402406101d182e0701c0894000200301c00b003881e0b03e411440540b40b081c082c040ca070f2006504c640304250f1520740a0403003940100081004103400e820b40d03840b07049841306094002c0b5143d07aa1b050900001d05460059540410b5401c448880b22420000f00d00e00300f0710740145000d2458a5060380c680745102024000e00701089408295201ca4048071001040000709 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 228497266 1250 228496016 228496027
    0x901030302010b03071a2a03040602070e0709080a1b0e0a02091002010c0e040905030c010c0507060b090c07061a1e01020c0f0f060a02010204080d0903050f070e07050a0311 75
    0x107400b0380030422100344a800384030340c0401c51b070f4003a52000a048201e807440034244481d2043c03a44440200e00b2265551600550140c20840c0b0104001c2024004560191800d2803401c8503143c138003807003d000340003071100c40791042c00003d80c0010741c0f1401507080400071203080c0b140c0c0c03140c00e0004500d030003a22414252008011818800d50000c1483c050160b502c0404080b03400f50483c01c8989194038800054042c0078100101e140c2900300024543c01403090700c1c50524104942403c595107041c400c40861070106184040c4512072103070303402c0c0d200259001e021a2500c2140c1c5882c41c454014014000350f901e00074a90568840c00c1c0e00c1007081c40c00380994100b001c0303003d41386074001c6c0c48411440c01403046020340500e07404d00c2c007940e00ca1445c1c050500c0d82003440041c10011107802c142020b1045660920000512900403c01c10100b9811612401c6030785007141001410315a004451000d60340c03002408005004544181c60303072007800da14100e51180741c1004101d02a20403600c8071006808081a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 228498516 1250 228497266 228497273
    0x4090f0f111e030d0906270e04060507090b04050303070b070516030513090608032a0d030f050703091502030601090503060c041d04120c0204180605040b0109110405150702090103 78
    0x420003603003004030f044492445910f4000c8410002901844001074142d110204041000e030201c90700620002c001c2d00c3d0b002e80c079040c0b015024601140c080e255507845209005d280fa4100d800c0740082c1141810561802c2d08040c0466501d100d100001480160440f002540f400c1c40348080c1c403204249141e0781a00f80c0040c1c00c0c02000ca801c001280d0280c56290038000450421a00ca40c0c405c5880050145d0b0901450b000c0780a50b51041c40b0400500450b01c007074140310030005004920b0352049948001407408031401c00d03401203d8004141c101403520701013074000401c80b804085000808490800f5a07280d035001c0040310500065480a90503205040c14010b054030510f014105891040b03046007440d041950011880da07109442c041c0c40c00000300554141c8510800c0300e4440f940c006080030404000c030802c0c0310290641d0041c16684541e07600c050200708680c5003c0c0600409005d0001d1146100c01344414080e03116031302c1024496014036031801c2039021018107071074480e80c006103006155031b500d0a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 228499766 1250 228498516 228498559
    0x11070b0f13081615230a1403101809021804060605030304090f05070c03050406121e020c012d05090a080c062d070f020a050316050c04090f0f11 63
    0x41d118588900003101004c0392066544141c00301804c0030221042e000c2c155148450b5101c03046201c10031008100400c40048968005c60040660341500c00002d4034041c610586c14401140d000c02141c01c046a5078050b945440311201070b50b518200000e125265860007000070255644600e40501011800141084440d80001c4062022040a00481da00c0710400c0300d640074180c00c02404030300705200c01c0c400c0c5481034100140b1000c600c400081c179100c0000c02c4000384c0340000400d400007500010301c4403003075900707000311611103400c0c0c1caa800200c040405038960a40358018009501661500014111941003200e10b01484e04688920360350a01411051349444044070846000203c60b00e451219044500c1c43e482413035601c1319051001c0e2220b0380120b502d40c0d0f502280b081180700d02d84492003c00e4017400241488001d14510655103034052503c40d0030040014032880c03290f4a48070013000420f90340414160702c150b0003154000840e01502d4042c035069210451076070440c0c81280799514201941c2e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 228501016 1250 228499766 228499769
    0x20a1202031b03030402150310030b0c0a0f030615140d060f030c0b160210031d070f05031b10170906040303050105100e0f0105070602180111070b0f130816 68
    0x1480d031100702014021010340c3c81c4000d58000f508400050030901c17180c002040510340005054029000190740c03a01c0d095000c0a080d998424100400150141c02c503420412103550810315040600c060340c540440d502e07400c1034000c808805d00111086103a91042c00004488031034400110401800740c640701c409071510300310f0204840038609884081048145d030360a417903540240704444141780c8050f909000f0b12440b4031004c182415207907030600000b0303042120680f0709401810010808a450400d203403a601c890f03548000c2c020f401c42094000340c104411901c4c075050009035440c1000c101400f03c201c81e058242802004001642c0782803107410807002c51102c0c041c0d40280d03400c0c803043e600c8004011100d0000b015620200d044500003450505005071000e1400c041410700c0c600b00400364903840c060340e0020881c0041030100e5071205080350f0b0000820140710203140d0040070400c0c10018400d0751803042d07515440ca10074000c01c0d4203244000001100c005481c0c00300940309110700b800c0703104c001e052aa = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 228502266 1250 228501016 228501037
    0x2071e03050f070f030303022b0c0221040306020c0c090907083f0c1605180103030203030414011d0a02040605240c0114090f0708121801020a120203 65
    0x10b14894080c4004009126410303501030314200c960311859903034164002d501202d003414460400d00c1c24a00340c050824195000503600700400700b510800b84d44000d081544035002098031030340ca82142002e01d01e000003030b9426240d02200043c0d4074000080c405280c50b00044030380e94040381036000c004030918003095240c12a51a50101c030300354214000c10400003001c0e41410450b24405c94680c0982e5200d0f007002a001141e001e4220349803052403e81c450906011494001161007005020011802d00342540742c541e2004041d186840d5040d80e4009442e0310001e800504403800450140c40d00c06070a600049031804120000c58405035060310554484408800580c4218541000010700381030950240a070106051070b92841002102c2e400d005a401016090034650740c0c1c0c0c503d81031209600c071281401102c0c48002083c0f091451965649400d1031900000c0c407a0b000002d003a070034121184203031120b042c104a070b40525080240d0040b85400003005002d4918540312102e4001d003a0044020b00b900c010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 228503516 1250 228502266 228502273
    0x609071503020306060a1209020405010609080f03040b071b0503070f08100b010e01030f110304210e010e090c0c06010312090b0418110d060f1d04111002071e0305 71
    0x406000c0c1c1c2240070403900c041e04160100b0041402d0342c4a900100c203d000d610000190071401900451b041b80d00980248020406450b020300c02c450b800c22015a0b05d00007030f002189403c1c2801d00c180080e0051800040c10402900008821300342648050000f5100203811645079982d90030584c260203449200f68105400340c60403803400700c1c0080c06841c10205060f101e10f120860388000440090000540304064283e40e07800000040f4130003001140207030300804150900590391020040c0300320403142d08805006a030384070001d030b03a60810340340c1a00442c12110a00c640e91010b105c03404030b01c2140030303110107400340304000f0042141c1c4640688941e101035840b4800c2c540c82d00016500703403159020f500030301e9912118089203044560484061101c50300c0400381000291540442580e255400c0410149101c52041c490210104588642e0440720084030520341403540f03138101504003c003c498018207520840c100118001c0100500919000caa411300410039171100403d10315107030004507160701 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 228504766 1250 228503516 228503549
    0xd0305090c010215181207020f01080f06040f020c061003050d020a0b011503060f0609031109160c0206090a0801141b03010b0d06030b07030213090c020a021e03060907 73
    0x303030004a1845050040e00100040490000c1d0704000d0300c03000301814000320040c84000c1c503806060000c3c2001e11000c1e200e054481c4100d10410005116150300349040048c04020001a610760a62090300b010040e10300295034002d001d060340191140e000014018411502400403258032400c0b000201e80c011000c1d0b6200c032a4078003040348c9800750030501420003100c0074014454035075000442607101c02c850400290196a03100c01510490302a8414408101040020003d1240750030096a0701c4600300c40b80c03002c0d854030b00e076507400039114405d0960170080d500007808119202c03882103400048000341072420b6555601082400381c03460b410325050707000c451008600b040040780404240402242c5030325046130708000c4850010380003072030401718298541e079000001c14203514a0f01d004500d146d902694422030303981204000403040d032200c3c90091501303103100c4109501254442c0c00b10b5045075450807004c0d4041743c8210b1106100a4107506000391301c280b00e0010400100c010489204040e03545101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 228506016 1250 228504766 228504781
    0xc050304020909072706170d08090105040305271306060215040209040f0809040603080909100503070504020d090b25320c0706020105100e01030f03030509120c0d0305 73
    0x20510342c41918050101e0900d42d0000171403d005104080c54a00c20009090365120340e483d507092504510380c0265042244440700865100811942c00b03400c800c0213101c2418035a030001c1c564403401342c2d1000c002e900515182c0c01c6e100180700a500401d8001c005554015802076140c004010611417035026204420360901d604c42207100d0244600e400400c82030559031151206d0b07590102400341115450010410300302c81c2e544605c660340107180141d40c46034452203400d00740300c0c00010107041d5140e5140403403010080c980e0002004030540e881a10050380b180c00c101c080d000548400c035001001e8021501c204060390822a4982d0640d000200000d515103020820513251810812041440400c2401d43c0110058201e5055803220b04075901d00740ca464a1010100e09125a03a0841c40051f5112400c3c401c05c06080111a8003800f050349460780954910b44c0c0d4401c142c40aa000242451784400c00184d0442c002c3c0400c0c1c0300034000003d01d59403041205c034440c0c1c48040f0955041d000c20b28041c00300342175 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 228507266 1250 228506016 228506023
    0x1061d0c04050f0604030803040f0215090a030602090f0d051b090903040608060607080c06041104020a0512090f07030303020a0813020d0b06060c010603030e03012417100c050304020909 81
    0x14a00312450034505401c20341440003114002d09000d412030800c010000014100c00000e605c298017820042c942d0070700c94410840d420380c0195898001da9410b000c940c0c440d0761200b01c45001c8a91000005a8030041c80002c106915502c4a101d0340c418003408190050100c0400d95a06141021030705c650005862001c010300d0030000d03031f4609841e500074002484980d0007102c440743c1150380140803504044590303507240016403009001c1401c580001c0103110410604511038911194110f401f981003254920005000c7e000d15501e8a600c01001c0c0007140e4041000d202e01078050781e4407410750724410340f0b03410f01401030743c0f01118981c00a41420001010b541c055894036107510303401046003080c220342d80c5030040f0300c00e40a405154045400c000044904400b40300340c1000b0b510945400c4558000181050300711000e2034106c0a216442d001e55900348510b105070307141942c1a29403048820071800031203d1410301c402c1e10080f0090b00d010701049c000c0d60031030007641c130440c070071078aa01d15955030741845900e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 228508516 1250 228507266 228507271
    0x71203020406050f0c070b0705150a020c0c01180b1b2e02030423070503010f0c08061002010905030f071202010902062d070f0209150306070518040e01061d 68
    0x1a00604c0040ba52098580c000c19071a1240c0d0101c9085949449040f55140d00a44045500d0b9221032040540c00ca818a60140d20050f0f01c0c10450030715a204012a031908071101080c0e04200c024401d10201c031300360005040240000d200c03810707214004e04920003442c0c0d03d141200811840340e0000b034082e0007403100500e01c1940c101c40300341040c07601c444000380c040c0d01f02030000c030750406c18100c1d21224082080c4011803903240343c00052450f1440c00081c142107d058072a80d61006040038504c400454000d0340c41c1d43c00640a48401030725041100c0100e00510b20344000a00c02d001c0040c09105d000b0300c1a0142407094082e08206082512203241a03088a074001c43c02504104d0610244031440812402901280d800394507249942030002c44204485e4041501250205000f64800007076040016295900c0910082c041500b03070240c10000342d03107690090240c4100803000484000160742091000340b140c10151081c02a02d1081c03070741078080c00140c00b564030984200300c101d41d40315040710312890 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 228509766 1250 228508516 228508529
    0xb01020f0c0d060c0e1008190501050604030f02031623030102072102070503060103080304030e030d0c0b060a030f1101110102161e0b0c190807200c0a03080712030204 73
    0x9000d22060303074541019010440945045c0211140c10038040d440303044031103c004050360303100c050134508200c01240d00480c806540c04100c0c075140040c80103486110841d01a01d804c2100c0d69540411480028541000ba007100001c0030002c4070f0010b41100e800038100c80c103142501c1c040f0800c0140d481418200d00400b00301505400d43c4000c150703216241d0b1a85605101c40c540306079615980c854001c01c2c6002001c2e030048410800000c100b100745a8070a0700c030030341808118013034060006440d0005161136080d0b1005040b02c1000ca0201d9030b2959511204801540d1203c8940406203c80c1080982d5104c0d014180380411190405080300c0b44041c8220f50130a070968001d6651801076444e080f03200d13055481ca10045074504115900420001c0301182c0c401c1007500c00761556007221140602c05041e2820748070301800411001c3c00440c58101e10886c0f225584020010391001d134001415291a0303c0d00206900495442d802105202d140e07401052094017908060603110701d020000c9040b4440c0d803103107a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 228511016 1250 228509766 228509779
    0x10504060504050c090d03200f0111040506030a05060d230d0504050d0816140f010e03040e0f063c030c010c0803040309150504060809010504020a26100b01020f0c 71
    0x10825180c041400e81503e030103031030212002380300c1000c802c1050308140c1c400c10050340a0144005505801d0007400b5050304280c035001d003060302d0103000ca050341c003000d45900c100f107459100003100745d11460b100005c1141c00c00e403400302a00001b00c1074410b241c0c1d030001e904554000e00c11595015405403044400300e840141600050803100e403510b0b40690410000950703110081c00c98540031854025490b00c207032114801070598142600021030840b40030006680030b9800500c0200700a07042583c11a5110040c004041d62a540b0800004c003400342c00f404654506000403542c5218015640c8058480c10f80716071040310712425403081568039091560818009000c00c000400041c060b1405190014400d00702482c002e42c48603600044011845003d0303000600c0131030304100da25440f440c2103821440001c02040310f81059004140020214012945103842081d04070140000c0f0410300242c02c4402425100075002400b80c1c80050064903210034010701c40c1c0443c03038001c45004207403c88c0070340c0005c046 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 228512266 1250 228511016 228511027
    0x70206150906010e010c06060602070e130b0604050924060406080a0c05060703020709050408072307050424090515011125050d1b08030403080d0905030f0c0303010504060504050c 78
    0x11503c1c602600c0502d0704110280c41d0040007d0700300d0094902401807030b00500030050802080d1401b01c13400410b2074110004610700c150209016403050380e0021412342c1c0125050340d5101403a440c0caa5a1701d146000710003598801205280c0c42c50420b80168000c450a008130382e40c0790b000603a40c58500d0303400f404044c1e044c00100300d1450404010310f9410311a005980400b41d03034054001c12102c04035415210081c00294980c104038440e049420307440c018044402d5403e40031a1002c0d50760b440390107140e0140e6a02c0c0b0a001d080012015510b4070111031140c071090b0184c5504c0c485028010036111078900c2ca5004050300451b41c016190750559240c80401080a01c1c964581c40070701d01000c1c24040a0a0114000443c10740c603502c205881c428010030b041c1c00c00280da80c03481c61071a555544403a215402c140300600004104004070341220007040c0c00881c411029050460444c4100f0300041014480043c2c1c4018014021000c0d50403524111403c0101b070b5640c1d41440140c032806c41d04822080001c100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 228513516 1250 228512266 228512269
    0x12061519030206040e2a04060806060703081513060b0d06140d0b040f0f11031606020d0503191d060717040b0a110307020309040510030b040b0705071208070206150906 73
    0x8640d44490400d141300744200c2d4172240306c481842e042d00225035031203001070180601c9422101c00c40c0c210b203082d26410714049460320000e00b61500500615041c4070204da01b0b072120764a00d24282607000344e5040c104061a9601c02c683c11a9009005590080d403e20800241220000f010804800e0001d40340302503054480e07941d01440300005100711007511001c0c29140204000c0300c10403560b1031280320b4551a000c501020140b0340101c2c20341186c02c81141203020b21146501107120407140f6080d0400c26100d03100d90301c4000c405907403040400040d070301c5d01c02071a039601713a1070082490034441c02c41586c0003601d030b50340101e850080c0314912103500301d940c00c0490300040480c1030340381d0700514003000080d048500f01d150701499402900e150f0010303030011848200905d494490641c11619100800980c54030f5603480301e00300b10008002901c00c00d04100050100ca01420481b25039503440980c540108814050203415603c0c160b540300014494800080c0d001c90f07080c40c1d1400010b00c020300302c84150f40e42c0c0d030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 228514766 1250 228513516 228513539
    0x80a06080c24070f0219290d150608010e060307060c020607060c09090e06011a07030c050703050d0e040b0a0b090102030f0c01060501030b2205061206151903020604 72
    0x40c010400c00c41e05510ba100a04040019203001d9125007404080300c0702078010444400749858200e4010b00700a4400c100c8a19000c0d00181184044080ca121611032032900c2004d038042c19041c4104c1d01c0c144161140c1d5050741b400c01c281903441c0c2c0c2d150194141d0725070b0031003490f000045403501d8141d4040380c41406258004c00680382c1e6548020422440d1903419600d41041c0d54040c2d00034030208004410a0000340064010b0329606c0000c0c00040400d9132402d444a44108024442c8902c000b200040b4402490710494004c00c42540244c2201c42c500e54030b103415640d0780c1c00c0c3e03030040c400501455003007074861415010b00402588001d242c1010281850b2041000380d01c0390000301d05512040003868042105c1c800501940385c8207400018440d0b00e080005003c2c2d41c8001000d620540c3c0d14800b01c0034001d12808084105410008002a140da0300ca01040d414907000c10fa400e640d00c2640e0410120034649040004124419254410b0600800550f65200182c1c0d02009500200600c014000480c076003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 228516016 1250 228514766 228514789
    0x4090516020c1306090c0309050d0201330f060c05010c0905030a0210020309040606030608011103040f0b040c1d040309140114090d06020703050a09060513170c030105100501080a06080c 81
    0x43c40c0c001445551140181d08a854807440480426191010401442000d0140702402034440c0003d0040d43d8943d01c41c03000c80c20f00c03a090483c8900004039000341c1c81082c00c1c01200a45008103040381e200b0340380d1801411703a80824504480960030709901c4c415691003105030310111600a00103000e0741c0002c1d800c01840c0d46a5500807800c6200600845e08a07582e1800340c0f00017400c0d19200000d4072801c01140509552030095010f00000080041c0310024604e0505103600b56007201035003509407514130307183d00d10f0b00c03595000606a140410302c0c507003608000350f0601d01452280e01c0b01011665500c940010b050302d403880d198081000d00544091500072040213000c854001800d0096400301543c99a0403600a400180c002680110750801d0351a0400b0f9418042d2809007006401d20700707410003040c0c401d4400d004100c00800391481d0303048070003c100700e8000a084014000d10003890240000419007510784241800110342c040031400d044c0351485801c0985500201600e03203040024180718500010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 228517266 1250 228516016 228516049
    0x130b0705010f1a0405011a07021201020c121b061b0702040b030a140f01051009240e160516030807090f0602030d0e0c13050c130b04090516020c 63
    0xb121038041038510644142c101c04202c188001a400d501a41440102c0b0416000f514641c1098030504400c03000d550305075602d00c1d60459000700c40c010b00040071400781c001c40c1d040c4402071141e140101851085200602840e8003100360041c500907130440750a59406084d10032104080c00c914243d106440344a0042003c6030000c0d1010820000c0000424a8101c8800b02910f01c107107000c6010541070743c14400d09070f4500c50140248031909111031b154504680364450461003036030f1034203550080c0e03886503a0542201040c61480200e160340d21001400044225190401c0080550500303100740d00900942d40c10814034640c9203800d04e070658003510300d403002074412418420314110004110710003d034148080d1007107a0266856200410301d13101507801c91007141100f508030b0b5442d00d9031911505044400c0b660414004503050311200240c0c070903403080c503410f55401c2e0441000401d04030040c0009000312070f80f442c0100031940d260740b481011950400f0b010f100680047c0b19101d0300b480c0110002800084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 228518516 1250 228517266 228517271
    0x150901170a0e4809100503061003030e04060b04030602090102030705120a03050c030f07030b01091a040e060607080d200705011d010e1f0908070b041403130b070501 72
    0x2058500c0c01c5105824070240a1000410203c058159a41c0c506040450300c940200d031030b16148151001a0300c0040b113030060424400181140b2880940d1070300038a00034080d603015081c0480c9002c1100b0a6000070b07404103280c00006c0490382442c2c80341a049450040c4000e0516046984442c080d501c11000300d4114030040c00101c01041060004c0f4404458000c2c0c40c96036030500c94406015100020b10303a83d1072072028410010110590403205900044514001900322002c03c0107940000a94000381c01c400703c1c100039129441c1e0140010010342e480031901ca0002e45d220b20030040300c0c1c4a1004000c0c2006414049070f413166000742c00c01c03225400c1b403202c011560040c001c81403440780c1101400790b4042c1e4480b056504031110b09100c02d11010b0780c200007031044270f656041050b80c0b441505040900d0366600c04042600c454107910800304c40341d010801554509242c1406540710303c0c151401c0c1c42c864030000380c014102200000f2900b034480000b0011688038a4034010303c500c1d4010305030907a150f54 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 228519766 1250 228518516 228518531
    0x7060e0414010e010807140609010503060301150f030311060405030a050a03091704150c02030712030207030615050a0603020901080f0403030b04090302010c030b0a050d0b10080d050702150901170a 86
    0x200c8101c0c0d420701803d455240018150b14003030660346440d00c140d00096403090904034250311070311184100c4184250a08101d581c176122035001c03d004143c40002101030309103865000c240c840c200c07500780044038066640d1381c6054201003901d035140d01003524004e229a000700141440240140d0240c0022015070800082110142d12020100f1868420f18520250300103014083c6807a9129803102c500007a00d045001a08030380c0c0429034a0000f8000c18540100388400c08003010301c02c2050300050756000c4000e000103c0c641a40314040e406c18000c00d80709110000c00030451a20a100390b45843c0300503074404403103445184041d01c6500340a4016030805440c0c403074074216922240210022a4401c0d40000b400c40e155040042c11a00000b1002e80300702c0e4101030420940e915807442001194100c5100c03984c0f0b4450382420302c00d02d48990311002c2e0030701070741e414070034010380010103842c555009641c030702d8000945604d094610721840c002103022540c80060b402c03c0d007910110302036104416590010720701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 228521016 1250 228519766 228519791
    0xf0f26030a0c02010801060309031d06091e03010501061404090b01032415050c0703021302120906060108280903032004051206070503040803060a05120a12090807060e04 74
    0x141d214003040808a1070141d0040115680071807154010034180c42c0411400089560080c4069542c081ca0041100344800107001760380c1c0c410444041c100001d020161000d10f0141012424141a4035580309500e48400028002e000b4280714099880c14042c81f842c080c2440032034001040c07407002e900c2c10141c1d5101c2020440300300e052001c00c0c0c018183ca0000010b482c20070500720444910a001d02000001c0c03154580c0040001a507000303880d4101e800b001d0042e1030300100e2000780903002962019010040a01945000208001d4020b240c03c1ea10340c1101e54891641da081c20205c48030505184d440b030500340c21125404e07030144000303500c6440c001c01c076001e4520b000107007081c1780c03541e400e5140da001404200501d02070745044c1908a107000a00300a142c4000080c046000c01003010307041f4000040015420f503100c16454004e000000c02c0704031008000c503903c9d0394912900788102c46102203003500050040c0528032150884641c0c0c0300804405041c440200c614809c0407280300c0d0080d0f110488030400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 228522266 1250 228521016 228521023
    0x6140a0311030711011a10110c0402070c030302070504050c0313020f060c070f140a0303050d06031a0702010f060807150c150516030603020a0509060310110a02070f0f26 74
    0xb0300d200d607540040c00c0c1c04d103250190842e40c0100c403191960035490441d01084d2604105d10300c1d4207401e4200003075403880e01c0e00290b00308007070b000324154030602c005001e01c200050b00401c981520301030390840e803c0c170343c4610a100850f58241d4456501c1c580520019140400a00d0090005031020788a1894070203030b1404100141c1248071180981d4000540c10300c121a40113511400500b0980c0c1810724005801012444c00142c5010141c104500090f5030300c00c100b40c0b41c01c040015944050805104071102051a120900c1a18110015400d0000c09940140c160050314141c403d4440600300c59440c0004090400034038070800014403e2599400005c112400701501e1803034901440404c0524000d074140f20300401108041080c103140c0305081c805610384401c2d41d01900e0040c0c03103082070f41d00c40c6c400107860035140d01010602c00c3d0500850390b0009145501420301c4e980d550702143e40c01515070480301c03100011030103030786c2030003182d104100070800c43d01d0104203035254048501c034102090710304807504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 228523516 1250 228522266 228522271
    0xa020a020d03020601080c030c060417030f0c1c0c1a06010309050304080703120206070813020f030604150b0a06050316050c0601140a1d04020f0a0801020a080907090606140a031103 79
    0x1d1380011004104510003840040d036840070880c0a82083e00001001441500840c0148450101440c841d160041400c000700e50000b210020400d481d00c05001000c0e41d18001840d910f6034035a000030300300d1612402503001845c1503500c1150304a4540d501c0d51100b4000100801650415031a026410080740342400188080c005200103002e400d4210308114807509443d00c40b903401c5501c00010490f1090380f04a0050300b1040c024042c80c18038006000040401803000c007042d505020380d0050000b0071059001d036030f07050070302c0c50001d10000c41103c0400c4201d00f518460400810801c0001035a94000d8428118500285d81005401d0118207600c1c14a0501c09800143c484407600401e90750718507100884d034005000c0800c8585510000c0d900005921002600090298105daa040b0905645511041014280b240c1c001c41d00d503141c41d1001440e050040c0e446e00143c1c000c400c40441c4a05042c004c3d0015107001e500c603d0008030350118501c1c0b42d584034140358020107685410b012001c1071001d00850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 228524766 1250 228523516 228523523
    0x110f070501020d06050922050a020901080606090603030a09050904081e0c06100f12020a0b030a2703020607050d020d02070b1905100b18060a031d030403030903080a020a020d 76
    0x41c1c4407501c907503c00088580e6600800e02c0740c080207003003184c60710b41803401d00b01c051801c8070020041030700b61070854900200300d00000d600510710000451416000102c05124020445080546860703c900f41a01c070f108400b40d05002a2041c4d50501403820a494102c1d041441b40036454a480e8032415103644101c00084040c084078800983c19a0384441006199000015100c4611490f46045868030345280350348161700c04403c015540c1010b40da0b0b007910071001803004510042e130361f2401100242c01020002e07200c07107070030751080d07006800010620356161130540d040e0010b02554555060075541a0002e5607000034094007007080d96505850744c000f41200604c46e03403c41e0f11a0410399000b08031080d4405001c044203140000b0444400b038131600c103104955603520714a98490103080c8411003602514403181c1c205200180c095034a0741d02d680101c01e00c4225440c0d0150341d074118034206450b44564400034001841a039818804105d10300010502c030720490040f20000702495000c1456940c82080a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 228526016 1250 228524766 228524771
    0x30d0e031f021c1104182913050906010e040c0b04030b04030915021209030102070c030b07030608070e06100509032b03020a0c0f060b031606021204030203030d110f070501 75
    0x20800d40c80541c04003c100d22506414462020448120001e60050340b065890300003490351102c107085020f900000fa0a01d40c2030061180300080c042c145041c03141a420300c1c1c01160070001440010000d032044074090300301400501816443d041d184864403078087c1003038076106800340340016201480380080c002907100b44603214140c5000d080c00ba01b25242640510829134400e00959095640851405c2c0d203200e400784120384034000c0d0004a40240500140180a40d1038040044103000d91088994402d6000740d600744002ca45a094054658105200c0d008840d5086004942c2e140b618108c600e28081c410301d04035041c1516680001d203821103c1040d10350740e20043c0304000c1300220000f00c2001888081c1000c0d032901c8112800201128101034000e031074002c02650707000800200c0c0c0c000c610a24401002c442c0f0b00a0813540058011042c2c0c0b19000c00741c821108004a4080c104040d60212070f002005107003800582c0c1108405494202c000040d0000100301c000320030211138015040c1540140b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 228527266 1250 228526016 228526027
    0x5090f011e110601050a0e06010f1e120f0b030d080915070c0201030b060901021e030408010207032607090b0706110c030405040b040926040801050c03160e030d0e031f02 74
    0x25082031410b8220034000d002c2c83c202800703003003520821f00b5040071083c0380040800158100890700208000e065204502103020740b002e0095000015142c0c400004508009090101c0803040883e222a4641901074104d409400110380c080c1c0b400e15480741c1000c00703545c0701501d925202c80314910121280c00100d80b4260886080d964180b00da0902c1c0340064a45d17a00e07080316100003039900e0f103103071440300215060141a150452018401e980050000d00025501c9038030500d005010002034201c0c3c0400424010000740001d6064201c69000320800c2d2205c0c000541405000d000c2a400a6010b40b02c154441d954482c403040c403030300200003208404000e940c0303036030a10040000b0f5808071081644330b581024041c0b008a01201c00c0b64080120b001c40f1003d11058004080c10240250392201c05103518040030410413078516001584a168402d00c44001c01411003001d0b00d10150600345103406602444060b800305001d10321002e44054002c00300c0d15101c0c40c1c80d040401943c0d130800032140d4a50081030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 228528516 1250 228527266 228527297
    0x1181103040b1f03050709020703030b09090c1e0d0f14060f07120516030207020a0306050406060312030e0d081005090405160602071406030a090f1a0c0a05090f011e 72
    0xb42c3c50200e000c2081552080d42c07440d21080e5a40c81c140c012048403550003e0794500301400b0f58460340a528014080341080d00e05400801c0d2500c0307110071164001c15000400c03459074121000c0c20104084020410400385903240c41390101c0c800015821145074640d06840c141c03000c820411203106921000000103c0d140244000f42400d901d46118400c05003000c09115145548502c0c0700f00b0703450745140058841100f4000904491082d51024102c1d03850304080c04144520b40d04001c040d01d019542c850700c0c884101000710200d4940200d48078403070300b22049034100c0c44d01c43c4001c190000c00c01e0340751b80c5100751103800280c070381c810075101211140d120600c54000c0f81440c1c0c0140f80101401d00242c01014944010f07070903840c94440c12544901000030006180f85441c1c0c0c0003070001c170b0b080300751303003800d0083c0d4507280d207241c01c144c0c403000c8044540070b0001e225517500f2021500354190079520a400d21a020041c00301038080303c00c490f4103002003020114140c02d9849298040503203265560b06801c0c80030312 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 228529766 1250 228528516 228528541
    0x90b0702190f0803041b080a02030706090501051206041d0307110a150309081b0d020708061522051003110108070f0e0406150c030201050a05090601181103040b 70
    0x809001c11140c1c414251000700c0c0d4031101ca0510035401c55003081d07882d0f481e03260180d0100300e403001507a1820781c040c802180741400080e100070303010b01c264102d882e45a240d0509441e00c820500c82d040c00240104154585850b080e0001a0009005403020444030090519400032201007440e08940d54800f05d80d050a0000e54000e00c400d810317003525103442c000d0034086580541315502c56154141916940c2c000c08125070602110181c0c610a00965807005802c020310ba200ca0f40710505100510944001145004001c90403a01402030381084c007405040309010301150328900740c00035405480301c0d030301140880880d0054603c50b800710428400c6450840c40c003080c00512b030300589410070618408000620b60419108a0111802d0601e0300000c0320f020b000034040c200c69040456464040c1141c01ca10a80242e27100e1001703807081c3c000380202d5948201c8070007200ca0480b484100343d84508010002c44245501d554812f4444c00741c04648105942010040f65100b65400c0720b0030340c0c8140c10012902c034900c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 228531016 1250 228529766 228529783
    0x114040c0c14100609060e0c0c0705040c09180e0c01030903020a050d08010512030306030c1c0c060216141f0507060908041d0f01031101020f0a0c05042003011a0d090b0702 75
    0x2800400c82e190400c2c0182c3c007d13000040424402840015200281c441d0400880c801450700a01c28060002c240c1401400e40c421445400642c004060040103491503c3c014006810b010000902c0c190011a0045025041c04070003503082d40034060b20100482c005101102004689458000c503651400c01803003010001000111101e402c20320038440c003594085200d10f5444c4046400e03202000032021310b081543c1d15a00000c1484200200010f036040e000b08200000c3c1c0d001c214160343c0b450b656428040c070300e119801d02580c441e50411500c0c03408150b422079140c81e00d07254034000e424417003140d44280884103841c2d4180c981000102d020850b0f0085172070000c0304542d161707007000c00300d090045e00911080b8042c0402000c0880000183e240c59208020105181c0f01440c01c4508019403401e0181410482e40141402281007580c02592030300404000000c10207070100c45460343c0e103040c141c41039184e002801154100b00030416900c040e85240a800e0845004004140c0c0d1420a0400a441c0c240c51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 228532266 1250 228531016 228531029
    0x30b0108030307090e04150f0b120604020a060201060b0304081806030108150714031302061c0f0509030307050403080a03110d0b0103321902030115090e0114040c0c141006 75
    0x14030400000540a408107c45c0d41000c40f400f00d0481c0e40216050301402c0c1c2115860307002241c000c0500000100061141d0081c0e000f0780c0d48200c1035407905012820380b01640079040300e15004002160008510000030014a94584e42080c0944182c80c005a1554070a078000b0045502c210f502c00d09020f400c43c1d1180d0810310504044502209120191442e0700000340451580103c0c00811400d5448420894006e452007001b480070703e9145106c414001e0031413000e507040c0d884c40c080c0024241040002120b016140f140c8580741424038507030f54003060f035210040d90803c054480050078440400f0710082c011101900c0800f0a0b4040500700040499070305d50200810b00700020b04042001d00984d0b40714401954010400d40503a5411141c2c02c45000340001c1e00d4141032000000040640d0214001414007a055442d0007038285d40c0c0d00e840500c0301081c0208045665814004070f21071401c0e50002840314040d00341403461440726100e40d1070402d0300020006141d00100301c481e000713030840e12420024001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 228533516 1250 228532266 228532289
    0x40c051026130609060618020c061e06090403020f150a0c0305010303120c170c0c0708030a0509042403080a020106051219080f0f181c0813030b010803030709 69
    0x18440000001c0000400e000380c000f594800e010f909200e100e0b00b101014001c50215400004011103c00000350301c0304e40208400d0240002040a1101e03100454a590301d003045440c0094031108200400d0180c013501c103c5c00d500c2003040d02c12a5101c20710481c90071502ca240c240c0300c285007101628040c1c45244003030784101071501c80184000703608030003032044c0541013540004a44080841c1503540900450320584078180c18000c0100400440e0f000f00001c00d1034606694450350707503401050385ea0059036109404580c1c148911625400c0c20b03400400188103480007400d480c1039600b0540d81d41c0a40d0f4000740c0380aa000a190904180c09002ea9001002c0980e40320061400c080c03a115100c480d1245404548800341c1000750902000c1c10035200030780c80c200c612907910006000011115445800d00f0018144c146140c510140b90260320800d929250b250880c84400240c1d5031142594401140207009009071280840854002c01c055400f8041c00401540c0c0c3e4100900c028004050a5206000004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 228534766 1250 228533516 228533521
    0xb060a090908030708250f031103040c061103120c09010e040c0905010206100806011e150f020d080103080a030e19030c0b0115022112090303040b0615040e040c051026 73
    0x1c4000c501e6600e09185440c0003007d404030414100c02424000c13814810015002c0700340000d12071006000c0e4200c5501c3c1e10f039900d0541444162645900034010b00e200e00c40c0c180e500140340c03c445400204580c020501d0f2884140040d60001000c0f0342d66140c6002c0044c1840d08203100c1d6580409c95550003d001400349800170380b03099a0255182d41c14000c040480e2080a030740308074000001810070241040015080120039840002003028080c8000c0078010703ca1256600f15940c0100303540c5050303e0300580001d19055140e034081c0d006e001d02410b903690920a4861010803145031202d100442d607c6651070f01c640ca241800c0410b1180c40c117800002800000d2012050129000100e1514207803050915202004a0018206140c060f902c03201e01c810340080b007040203d40012001f148298400d500030322064480c48140010092800030014000504020510550200c1c1c00d07140d80c010f12404604c21403948440104141c145210003910108034080e84400484110001044801015841d0340b28240b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 228536016 1250 228534766 228534811
    0x50a0b04150b070609061b02031e070809010e010e090c0705060108060606120c090604030c1707060f030b0a0305070f030506180c09090f01050114041505030a0b060a090908030708 78
    0x41c403a05100902081c0d44100c5e850401c070399504610104502c2803484d1a0900182902940b03a5000c0c24120482180e1560004110351004040e100300399000b110407810400481c0054442280c2041200e040c08a42491001c00d540c40d008901d1203040003812040c1c45034981d2501910b0324006812103451900030004025164a9480a46000c0701800c5100121901c400c0c0079003815100309280c554001c0c000003800700034000c0050440c000c68031444061603621080601507900e41c080b078080c00d80041c40c034000e41c4840f24031980000901200040c83c81d10010b5407a5210351511413240e2104c9202d404810040041c08424404950f00407188140c0c1c6000080b06445280c40b00b440041945c42424440081009045e0400094840356150f00c0200020b5031106946505000c0c4000307031602c51410070030415050143c8a00403030460f58040d008011516583c1c3c3c520405840040040c0c0d002220300200040ca0000c601410310718900a075449030782c1c0d040881c802080b41030014901d4942c81758411305100c0d80d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 228537266 1250 228536016 228536039
    0xd020d260709080604050610050118090e010f020d4506090501050a0902031905060f1509010b0418020403030f0309031115060310050c03070e13050a0b0415 68
    0x41050300da05a800d0368a110040d1401d1901d6040040e2074800c41e81044100400041c0d038500500d0010982c000c0e2954440c01144d1055400d58034443d90340c04010100310101141e084601241e880308008602e040944c0c0c0e890040360030052842480c00c1e25203900c9644001e002c2c0c0032a64000450308800c496008503a803032015414001928444004007035225014090745600480f0410341c040c000b8003007410b1203299030001d4a0701c0102a8428000c20044c00d00c07420b001c0035464501d5a000d4003500b0a9640e82544004c0100c005003141030100700001588925524682e00700c0c06405902d07001ca80311410322882c9c261448600304000b4103a44104001e1000c42d0704010000301440e030626020400014900e400c50b07421841c80e40400d070500c81c0a540500c64610815114800c06084d82261461075404441c001a60030a81e0910841780307080000c40d004034030414600200e01c034054002e0102d0301707001304400201c9804841c0d102040d50b640c5c0c800840741c0340c1801107000030603420031780031001400c0410310500f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 228538516 1250 228537266 228537317
    0xa05030a0f05010b040603050d0e010f020a02240a050a081501050d020313060c030b040e150705210c0406021b0307050105130506030f070f0f09060305091504050d020d 73
    0x41a000a800104020b001d4010035000d4001500610480743d5078070303040340e030380340c0c03c10360f800200701e04032210101d130b501c54203000c22102c050354002c208012280d028000c07902405550f9032201054611800c00390f14401e002881070703940503a19244d0310803122800420b010005841000f1409880c0400b843d1a0ba2000c2614100900b44c0401a500c2d00d41414640c1c516809800041c101c1c0c0c24a1781e6015107a405910902040c00c0030348082c0041d101c4c0303807181e58440381c0c0650030310f0401400b40040f65940c4e1084019104944400d01c0351400195000d00b0b110f410141103611580354030340003a06100043c4d0601c040314040d00810600c80ca606000000240c8920b05801010b0402001007a203031080300120601c0700040001074012956820100400e6010490464040010a6140310820001c91190165001001190396449125410140200d000e42000340c41100c1900c5487d850845510200790482c1c040c610400090034015002d0704081c6c28020121303440018880508128181102d041d444540e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228539766 1250 228538516 228538523
    0xa03080c030f0f27100f090f1e0602191215060f0201061701020706050f011505090d050613020a09020406080c0d111201051e060d0c110a0308150a05030a 67
    0x2c629035500540980c0c01000102010b408940001d013a0034119002c5400c4200e01c2e1124818040034408000400907280c03c010700074007001d18410745402003200b85100d0a003820001c124290f0480b21502d40e402640c01c10344c526a180460010030078202500140301a4245034a04410b101c000e00c00a030301ca040c85058458201030110300d24004205500c01c0d070006d0080d04000803603100050845625038002e401800c0110f801524107004100300743c2821048034120741e04440889900883c0305421125500020011504070810485182c0080e4040c020f162103040602c01900403e007950041001c01c162981c01406041d10401050003072070343c041c0f40a90720002c0d044282c1e81c1c850044500304018480380c030600c01c481a000ca02c02c07010140701e0941c0d40c121a4215480c3d00000c003455510051100c0c00c212003680514100300411a402807508034260100d0300e403c1c00080307010f0141c42c80d030400840748406c4001a84503020040d185c44085002d0682850540d40704401500384004203549a00808025 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228541016 1250 228539766 228539791
    0x6060d020916051903021305010207030c12150c120f020406092105070f1e210c05090a0c030e07050d0f11030106091a090402061902031204050a03080c030f 68
    0x1103880b14000c00450303c549403542401d185489810900030300030741061400c640604004400060b03107610001790041a030383c1010040124070300e031090a021b00c05444a00716485000c5195845500c0b985220b20001d0140c04c2e00c51000555006128104550161820000882c03041c0420701c442d96101040100396075034041901d0348031040900400c10040181e81c01060b500c1011008140c0d01580c0300b00e10300711541c000103a48194110b602c0e0020481043c003132410301e0744d2814024140080c109a60340c00c618041e145440c2056210004601c442038200c0d0740c2101d50781c070361500c44030b0700380c2c148510862040100080c190701c5044c100001d41d10b920104000d05004ca041e04220140300302d00c1c2c0d200201000080c001c1108554a41c01c0c540502100b1034015460309400c2c08421403814020348a078461070b0300420030b0385030001c080300c082d200c802100780c400c0462200788184011442292034050003240500001d01044080746401012002d004014014803001070040c017206101c402d030600c2c0c06c41c0504090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228542266 1250 228541016 228541051
    0x1707050901050f03040f1b060f08040305091801050f0906100c0201021501030302070f1508010b0d090807080301030b22060c170a060806060d030e0d1a04060209010206060d0209 77
    0x1242e05000c3c41141c0e5401e0080081880200318020840b015039038441c80300c6030003065000900f41000d52540c03140d0300c04100746510064450b07100d83c000c1503000348a0b0618078105a08107001c141c044070701100f8108403c5007a801482549000c1c03030141400c880441c1c030140b1070320b41480802c0f00e143d24500746006100c5030140860031a07000380030b60308007141e40b030201c50840d680d60304000307583e50b0b2903105540d40c3c03101d203000114000e940f1000c038502108003900c2e0030b80030b6443c2600074082580180134203140c0340c0e555204080000e15003001040c8032030190001c01c1d183c2d411b41c1405072004c040038200f250407110189210f100301e550500c0070130109801800c002100b0341c1190b41542c40114014044400d103a5040c20000f00100076446141944c4003801241c1603aaa00b4082c0035184003101c0016022809810b00026140307003c40e1a90030702c80c410300c5c01410080400d50400a03101e02582c00700c404c1380d008500b524240d41d0401469501200c1123850b1015800c041d00440c42d65400541421000a41c2e40c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228543516 1250 228542266 228542269
    0x6071505071e090e07030b100e0103110d020d060609230f10030207030f020c06070204050a0e03031e1f0909020d1209030b0906072001090c030c080d17070509 69
    0x34412900d49806102d807818560403040100088414028441e41800030000314a50324424800c1c0b00281c64050f0001c500b640f03030700b441a160408007801c0a4100340d1566480d1003598a083d01415800000c4503015884000584801c41541c190b500030314204130406d6000c011410020082201c411901038040c82e805000d40301103013421008036aa240c20200c094201d0346e00d194164007c0034054040d9030380540c8411444012030321514407041403079001000303100d100e001d403501c0d9000070341100c201e6900047c0d11040305140303800c54104a07080000640e02c6c0410407c00c4500708411580034090701a2180c00d546031202d02d0ba4210840d00854880d00d41d1510b1141c03c5440c2c0340799a810a81d0070031038228501c4900d100080840030703a400212000603000c8049410058009821400b48049403510500c01c041c2c807048038802401c8005620b020b6480b50041030102e801b00e4a003602a501034608042014140105030b4541a2000c1003001005000760050303802c0c00d000644250004103615001340d40300ca0400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228544766 1250 228543516 228543527
    0x906080a0b040204060f1209150e0a050106140a06020f03030c250c1a0705030d0504020d290f07140904060b120603061308071704090903020f0106050607150507 70
    0x581c0940080c80080c0c045043c0c1d80050080c07107401026030301c0d00904008004400140c811a0347e0003800c5220742011400414401d400160003020706c41c045030070080315910341d282542c2c0d03a07500858174074140340f081030700c0381c1440a01c41d00a4592030005150503002400341c696244070003051b403030403a0000308005180000303503005c60001d018442e22485680d0b040c2e0920340c1056145204a5140c0005000041d802d945800180c801440e0400095800c024440c5045001303000d00910881c4d0010a110346080040c1c8401510002030003002c4003128000b01d468804001000040c10803c080c804000c00c0104440d4080042c15001c00a100c0454032990400086000751000f50440040101c020030080d41c180c0c41445124403c02c8110200d131035903200d9040c200d00d0100081c82c06010000c04200f03030300114120a402c03003031040010b54130928141e6240014021200c49000c110300507048079035019165002409501e014000c00c4441c41c3c90009103689284007243d1549072103004c80d807100c00041b042800b84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228546016 1250 228544766 228544781
    0x702060c070f140c011211091302160b0403020c0d052a040603060207200d08091c051006080c06041703090d0b072a06021b011503051c0906080a 63
    0xf241c5991186500ca0080d00c55420140440c005900109000303d1030141d40148120b50042d0050140340203243c02c2405144d01d95100d502402540030007680741d100524407043e6a60300e008540400e0142418135000f0f00b001150314180d40b003540410309010100700e022440c1203000041d40d41c42142c00385440541c840c05160454841d038000d1a16100200380f101e281c0082440320710410802d1401010000140004401880100c1e04901420001000140d100c00213284ac080d00400c80000300301035040004211411480894039600102c9003a505101d41c0d00030b440107400110090b02d2520031410200e10103020303901c10004d070900b070b032002108035000600490f00450005040c9081024076414100075001007130300c4030f0b4002005006100d00440b107801ca10800340302c0c5104050a240101d4407004040d400c20707040940005444518100e080e0424803841110b603c003d1901c00e0f91615608000d4102004d030001f1180958000c030305142c10039031104154040d0b41c2d00f801c0c41070302901e0f90800c020060149 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228547266 1250 228546016 228546023
    0xa02031b07061b180b0c0304060c05010b030601030c09140c0a0f0309080c0607080a0e0a0f1a180d080609010510020709090302030d0605030c09070807030e0307290702060c070f 77
    0x1400030080c0c219413046604e2501041d100f4034000e81c42d40c50510680e41d01c45d4004920541e0010b01082c45042e101e00c8140442d14020000454008048c40002e42080c000780d1003102c0450846204000750201c0340264031240080c0380e0504060f2174442e1580120380301d509050810881c2400690749024082d600800025811560658407410003000e41e40d0b80c0d0109079052000714001e1b00c00214030710254010159840b0802d005001c000100380e07a468041002c1800480d01503841d0010a090700b103003021054031981c80c0c251100c1c0070941c40000e072424000c00a60480030480b54100b08100d40e03d0f010101d50448400344c030041808188090100d00b41441900040c0b201d5080650030000d040d8004090441c002c01010b0400c04280c0d0b841c10181d4500b1a125465003050148000403061030103103003440d0780101282030214840004d280d5141c2143d2000b682240e4126240311520850009061104210806410320030414204100b000c2c2d5125001000d007440103000241c0300741003002019810400c2a070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228548516 1250 228547266 228547301
    0x150302011b1a0a0e06010303021002070c0b0c07181406060c07080f010506180601120b03010f020c010203010815091203060102100507030e100606051b0a08030702060f0a02031b0706 79
    0x150459082d24890700ba80e001c40000d0030302c0b612040c90350020034424101c0e641a0018641c00c006100301d040650005034054400c4d00004600282d884110b0004020520307401c3c001d00007860800040e158404050000c1d040e04030301d001140341c00040c068200d140c01c107070100d440a0701c580c0c40183c510b26141561300541224000c500b01140c02d0031054120314000e07007040300e02d2241e00c4480c2d100c540d021942125100e00003040c5076070750a03080065030301c010ba404001400104409981d0401e030030580c1e01c0011000826940040100a881009d201180311008072140345503460400d40040c0359109200e01240c5038040c40000410b480381e00801c0044070780700c6c09450612591030004005002080c0e8054001740500500740400240c0440e2700c140b1007920501d8aa0604001120702c0e540c0c2c440408640044c01d81c4600920b60003c150f440000c1c1d403046020b039004086070324080803d207013540030181c6008a124010300c144045001240c144450740c2062210300c41d224400c0d402c0c40c201601021340a00e0000a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228549766 1250 228548516 228548543
    0x30903120c03091903120f0f080a0b122a030a03050c030405090a0903021e07060e0303040906091b09030f060209060d06060203180a140d020d08040f0501090801150302011b 75
    0x4404c811000850340141000f0542220394202510300301ca000d21a000002e2a100603111420b00804509130000c19900000400c000740c900800d07900c0344100240d0b00603520196108030b452a20400b06090420341007107c4102c0040c007004250341d207100620040500c600130071610001c40c0100161001804001c01e580c40a05024145000030000c030002540103004039941609594071060905104e44403650080103018030b4410115215040354600642c580801c0200280752030443c040d55014015050001072090660000e031030101c4003025001050180702ca42c10000714940c05a1038684a402900159485480800043e064401c12481c904840d103862404170b0465400000b500082420714a28031900c48440e0400c440d5404902c2800920448000e250b400d80c02d00c01c1c5511055031000d000b50b55102900e0f0785d03051445e0400c1c2c01507054914506c00030000b075070340101028010020703a4020003034400e0002d241a0752604900010341880100d4480d10403130224010a80403190f0031900703640500303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228551016 1250 228549766 228549799
    0x270a0f03120c050a0915080c0a09051509100c05210403080a0903020a05041404060b0301020c030c06150625140d080117120d05070912031808030903120c0309 69
    0x250480746844c00000c1c07941601191001d98881c404040e41d40303a4441f4207072030355108003841c640c6e400081440c1c104203000c6400500e036103030904400c0c00c3c5a603040096468000581c10301500740d05492440d02005456008000441d401196024003401240301ca2191107110040c54441846281d00c01030a01500003080ba5202e0341c003c280d4070a0724402c81d080d0503500e0365601084107540d000103d040109400078013080004000d5804003543d800090009030030016242035690540c0c2184002c5400d58107c141080242010500d41e0508114115121030800002c84482c0640c0e601c00d0618a4840038484850404c2c401c680c1da00d085c1890b01e010840707802e034580350310040060030300b0b109800031000c0710281809088030101d8200d00c15a055008103007043c8072b0b46425400b03410050100c40a1286003600032901e10111440c5c1254940a03803100150388002003807203180e00840c1da000007801d40082c0880c8030b0581d4080707200c1b511080e150b00e58944a5000980f501c0c01c521420100a034031070b90424540d09034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228552266 1250 228551016 228551027
    0x603081903060519050108090a06050c0319090b1f03080c010b0310090809060f0706020a0c02120a050d0e0a0b0a020c0310050c0306120307050a030503270a0f03120c 72
    0x8031180c55509000d915a40e0301803128030740103000d0761210284070444c02e01503035100d6945140e010480c034084035840d24543c0c03900011104180c500c1c200880b400000c000d1010303884442ca038010180c0381e1080283e00c0c46a21161141e84014046107400703042013401034071081130a09603001841c2c0091010b95a0a02083c1181c000d18000c070519000340103041540414080c9841000c580c42c3d0803201103454403800b03000308034140d4008041d0440a100c1800705d040403914510140c01402c101380c54101c00c80d44980100036801070390b01c20342c0d40790341d010003030640009901054a4000007841d003811005285170900195818a580e081903500c00000700d81e02900d15070014241888010a4040d101a501c02d04010390940b581103807544100b00040010078501e09004a4000004500320240ea0611040e603413142d0905014100580001e1400b04c00c0c040001040144542d150581c443c0081c40d42c84813542a5444012801014003810b2140e440039081c18090802002c0c6042c140d032040040b1081000040c02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228553516 1250 228552266 228552307
    0x1d060903060c0a0306170706050313050304081b0f10081e0a0c08070c0c0e0a090501020307030c08060402040f090b040e07080708070e0919060227040e01060605071203060308 76
    0x342403120001e8441b03080030b030861b480200400602035080c1400d81c143d4080e1300203040035125002031800031000c22014006803024120b02c030f02800c400e0b4ac030081d11070900c80c007104413644200308005042c04d403903070b88222440b01b4050608000a41e507845107441400784c2612011100340102d22400c0200118444d44071803141b0002d9110712101d0f488460301115042200c903401019207103004010b0015000c1c1d81690340d4011405100860002c40ea03558207800d9800544801001c603803074503205000c0c990001e50480e030000064400714142850301d90500d001100314400c3e0307581c0c2d40d9201507c0700507440341d4025003080d40c07140007240c0846503520241d0341c0e9500301d441809514000e0440120b819803800042c40d00607010a0010005070007914407030402e40e512580c00701c0f00540c0c00c201400c40035014030000041c511340080901d595411074001e01043d600f00084020403030340351540a005454004003a511256000102000e80c024850302c154020310054001400c0340b00c01240307007901c045e00b0580004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228554766 1250 228553516 228553537
    0xe0705030d050910081320030601080c0d0f0c050d0c14010f080c0a02010e012c010605090420030105040609020f10050f0d060902041d01080d1d060903060c 68
    0x1109240350440455150007407000c031541c04201c054440d442541700d0b000703568004903503c441014003c1c0943d06c01079806c00001c2d81d195110039144100081d85000c0c80300a00400340c40c0e010340005291140040c10400f0881002040700401090301014031041d1541c0d1800b5003800341181c02e0b1000e0504000c06800b0b0180b1810011140c100c40042c039075440344107540340c80c1c182030712004943c0d2100329014040f504512805030840d980c031601030302c107038509004200704400f071741d0070070b11040400c1511031030460800c424868031a0b040150411550325040a15035105070403405088a05520140612520380440f1440d0f61540c208410b210034410544c1c080d4100314421500400b1107244001400483d10320100400f000c68424045804c1058141340104040d4042e090001090786d100c50000040b60001e0304050942195450082e01202e24a401c090140003058010224880303c1d8400501b285103412910304800105402c45829445000036958101401029220756180a080101054100c0210b81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228556016 1250 228554766 228554773
    0x30c080610031e1a130908091026090705010302030f010521010c020309210703030302090301020405120a0506090712060b0112051e13020609040b010e0604080102040f0b0301061b11040e070503 84
    0x5840724440d03c940e20702c2986c0720642c5801c0235900350401000420300758000f001d100441030389101548003900e1207101d20314181c01550741070178a40e03142840d103c0c40f60065818540304005109006410300070043c1150001c61340e826043c11410f000d01d91980010032130041a6080c0302d070500c003140e008070241c003104505860f12040c81c26003503131300061039808800d0f40b00540c00c84c00052003c64032940043c41c00758000740001d442d10380d0343c1d000715070b0480e28411000c5454001901c203400300101070001ca40c000d00988001c00c078440c1498048042d0703d5105a000b00010354801d00e144869000715403d111640398104100482d1510b41c00380a4008004200090507070b1310b00c3c0c00607082004a40d1a4101c44d42c01501c614103040080e824800140304e0ba2800c0790500c48403a2480c0c00c950394900c006c001030701c01c0d0800541c03940e2904000040c001c0058003c0c0108401c03d0005214041e40a0a100c1d881281803e210b4210081d03400d0a41d601c9100e031110a4201c0d040a807050000c040c0092120200d030801d600b00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228557266 1250 228556016 228556039
    0x120702010b0f06390a02042f030a09080307030c0e01021606050d0209090403110606030606010f0c14030f07110306010f0302090a02121006030c080610031e1a 69
    0x304006581c0b206202a0301010600201d80c400d05040000c208500c1005035490802d082c1604180451180b4160030046900c016002011810305028200c0400d2200d003a001489800d0304034800c4c0780f46520301c0700164013004400104c003010284c1102d40c075035070440c09030f0750303a414502030082c0901512040c0c0d40200c1e42d50036103c000d95100084444511448400102c802401c012007251030340d0104ca240708203542c083c044046243e940100c07040c0071f24400e4542c41005d00b8950711560070315500030700c040d00c25048182049881e903044240020748480e10303d4020300925043c0751400016544107000c0c03681d0320020940d480190782110060290701c0c040c50002c0c104104440030107603185001d0080850340780c480841040141000000e13250010104a00581000c000c6140001c00c11801c9421038001c440b010000c1000075010311031191950f02c94680048103180c060003080e414051030068004055603402c6549009980380356400103101008000e03c00a4020740000d00c4803441c1c80d407c58807451b1044d09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228558516 1250 228557266 228557269
    0xb0103050c1203090402181e21070b070203010f111e030105030a06090c0305031813200c1207050307030807021b090c04030803040501060905070302070506220503120702010b 76
    0x20b100c00c0055084000303610b442c01000500c0065008501e4010401801800ba1555907031050040254161803001510100c2280000c00c45460315580554042c14080c01025418034004078000099801b00e140c0e9a40d40c7e000c910100f4010103040a904100130720340071410304d02101c0c810082002201c0307001c0c041c0044082504042d030380e2100b84105540355000c820120005000d0b900611411801083c3c81100150f489c5c851074110340c00b401c21801d88a602c00a070ba2500c1ca412807201301e0b084203400040280e80c106a10040c4403508101e0309904501c070204001ca030407101008440803000f00c030401c4540b40c4815203480d0303582c1d410000341140807070031020028800174030001d5401124001030b104002c10360010f0060000c0c01030041c250200b1079008000120106800c00001c2d40942d20400000034124500400d0104039403001d0004010980104080b0001c154002800d5801042800c40d11400c0101200b007000031074007110001301075000110b00401c6080000f18035621035441500240f0440c3c10100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228559766 1250 228558516 228558529
    0x70302030f030a0c02091b0f0d0f09030c02041a0307060e03010c0c0b04030309051005071205100b04030204050606040e040506040302010615080f131b0501090f050307050603041505040b0103050c 85
    0x601c1c400140304d00a48a002d4600043c000d03804c01240c80306141d00c130040c54842c0c001d940c400b10b03000b000c84200181c040000010303071003403a5030440c1c20784040154842d0355600600e41d194105010b845075885001e4048010400030404520034001001c0741c03101561000c019095004003070340d075442035107807504694655010380e201000d0320b5403084242d800350380d440c1d5064004003c04001a10b1502c6a800c044800000e02c3c424180914180e850300780c0340b0340302c10b050072007a920f00608030052548900005c0290741a00002c0c0c6054950480c0c0102d4565142c101240c4c0174020341d484903402c81941c00070b0000b4440041003103400740d030003a0300900119481344c102000310313164110000001030241001902001008070490703048028116403a0440302e00e5241c24000380c0b0b546001c250920400388c820040c0b0341e0000342480040034841c0900b44941d25000019440d040c540c480c6074002c0a000001804112200c0750400d2804811031003000fa40c24141803500c50001c09000031a050300c02c426440441d4503014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228561016 1250 228559766 228559777
    0x1009240e1312050706050c0714010606050301090e100218090109020304120c030324090606080c1605070b0c0d03060501020604230c0310020a031503081603050417070302030f03 77
    0x12480008980203603502d0040035409428800308224041c004000010040e000c0d079805901c0d007a8100d031b112314441c100300751a4080f000080d00c0761381c500401081860717040000d580c11900744038800250700c00c4c07202500f41000006048030030300034400035203e404030309a4000d4007461441611641016a00c07480d422040307100503180500013031843d2000e4026140300705c070220a6148207260101d8015100d46007600032040c4950a900c0003105014140f21807941841410020011460320340e42a040c42e03941c10b00c0520400386c0360300b01204841003003028428104901c400429090743e0761650742d02d0204030075440f40e2601244000090038030100041940c8000303035041c052500314400d03840901d071150500c841d100e4090319542c6540a00640035403590717010700c142e0070320030503c0743c001d80d80d0648000001c0071110401c1e00d4208652100d80d0034000728040a0984a40d11042d1905030b400407480c1c103041c0c0d60740c09668040c08502d070002c41c82c0708104002050341030460f8400d40071117101001c5034a1268581c0541b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228562266 1250 228561016 228561031
    0x141e090613020406030203100e0c0d020d320c18220302190b0405071205030304080a05070206040603090303061403030904110c0a051c090b0d051009240e 67
    0x119022620203074400c07004000d014401040025050384d01c0c0d020a0409440c241d6918059540e070107518151801403004c003e0400b0200c070891000724440d40002c03a210950b8001070240c03007240140104542e490101c000205c1c4da03d04842a11110702840d0540c2c030090b0800e01c03401521812030300b42e00c4440e08a140e502420740710102c500c0f696220300b00710500b00d581080580c114400c0010b18440580d0003004071240c503005a44013540d910303041c1082450504140e208006012120007920007094001c0282d0741c1040c0c0c444c400740da5a00708403e0840b268018072401030b5004000140002d00396806622004e00380c3d00ca620188840345e910a803540017a81e41c1210280c043e0401c01030000300c0e10b0554462068000b01450743d500301100c2100d891716040a9007800c8030603074080014800039980000d0704000d905003034509007040c10b040102d929075a000308400558030b103031988040743c025904540410090024030b45e00300000c445625800416425160403024850503841011030885800001a44640304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228563516 1250 228562266 228562273
    0xb0103050d0504120204020c10020a030b0f12190302011e14060f010504060e0103090c030c03030215090a0b0402010e031203150f0604060e0a2304050a020c0601031410141e09 76
    0x44e80c003804040d50000b070f10f10300207001d00603440d4101c000901c05071450a80d1680c00080141120b418090354450001c10346100d48818085c44d000090000780c0325002980c0d480448900d240c1520701a4054880c007904140380f10156003c850400354190301140150f0340c8280520010740b1040c040c0050a1040300303105001a004001c1401201d001c0c139540d41045006140002d0442d186894041c0654541d4004540017840241c0801c203040c2d0402540000c00104441f00744903080100d000c40d6102220900102129115400181560300648038441070f640081d09441344004184010f0b111030380101c400f002e5240030281c5510701c604141c024080e400401a001e60f01e1701e0308007030b007c1d01d64410051a85038080e41340c0102003105006206841c040d0142242c8803184640420100001d0340d000500c580c0000e0b2042c0484421101c000400604417500040f0b01c8100843c84820f160500090750150301c155420040d0f0248160007080081b403041ca200d0784080000f01d00884918500c3d441074034101e0f01da07031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228564766 1250 228563516 228563549
    0x8040b040b1801021909081605040b12010c09032303041809150209030c0d020603060103050411100216060207060807031107020a0305010506040f0e03040e0406180b0103050d0504 78
    0x20300c440c00042c0c01411500c1405074940c4003403020381c266448510146650080310304602c0076030350001481c3c0c0260224002500213a8160380344211800710318800c0d288120340716004c0143d0354986000143d250b03e03070780b0024031850a00d01c10140100007c1e10040728805203955401010100c0189a4000040040c0c081c40ca02031a010005400701c40c880c9917010030a81d680d0b03d04000a07507100d100000c41d00032100150300d825401c8205810078500251f4980520b0984c0c144100603035880f0200e940c001b100b4240040c1d10f440300d080075410034a5074104103400904203d02d101807241c000501c0300c0e4002c40010442e2401e5124841246c80e400c21b4414840407500c8200403800b20780c0a82c0045484141c0c05404604141c044d03000a00f2140c00f0342d00980d02a59540184926030500c0e0040b08000c43c80c440081c031085402000c256078a100354490100d101300307542c004c41d0400070690401500c4d10100c2c284802191184d003000160f4071030a2000721120300c5400c02e100d100034010f00075902100c220100850710030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228566016 1250 228564766 228564773
    0x7020406181406032a0a1203020609070509100501052209020d0b0409050616050d09030e1e03030a0c0309080609010522020a151709030903010b0303070c06110f0a03080601080708040b04 81
    0x11281d25021701c0d84100031000210740b0040b20504041058000d5004200c14107068070000e0038010355800c11802031a40c0343c1046418100d12404c4c034101c44007880c280f60380c2c15580c204c0390b8040980310400c09c8081105640015100059005082201c0040804000241200c0100401c840030090000c1c940d402810024080740304801851801c61041d0a2179440d02001c8803020013201e0003810700b100405c5401e52404407070f0501d01c86c1d00381440441c454100c11010700b100003070b54034020896a88208020142620100342c480c0780c8200041540d01e0450700e1a040146085001e0315048034104003410881d00c41c5074a5800700c85c2008002c50300982107075041818070703040c503240c0c40e81d030609041070044804d006120000c1c50141140714602a402071601d60401a00309800d452090308410f22070b138014080c610114200e003112000712003190a01070300a402c9840114101814106944030354000c0103844400d244c0c000e40114482c6000340c0c0d82030482d40e2421000d44002d40c059130040c1c1041042c50000c0e001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228567266 1250 228566016 228566083
    0xf010516060902011b0602120106023409020c061617130201031404050607090b040f0e09071a030f0c0304030203091012090c08010c051207050702040618140603 70
    0xb52030040c5032012031040062031656104031143c8044560315400294204542d0441e0569405080c1610160200000c800721400c40524107454071028100c2e80c64000c502030740e41081e0709004148081040d52220041c2e00d0954841a0498160341210707190ba000c0e01c02c05100d02d00c60340c4007101389400c151560301c60100704107550b081120100c2c141039031071004c0201000c0c1c00c480184a58401c07802488103190050006002203a1796100c00b400c244140400e10820b103181e04044191145182044055a10b98142d1403510202d5403207824000785145506200454440c000c601c41c4807101c040c5000c1d91a0424060014441180c0160044e08140300d90301482c90007144281e1403010740e1805a0090349000650000c072422120300301e4000034000020444210280a02020544241030040c14a0f2441e400d000c403600000300710100b00400054110115504c5500c5507010745054085142c4503001486050020080c0d840380d00a00d901500c00900c0a28000811a00c540c400010458002c0440b02807031a1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228568516 1250 228567266 228567281
    0x103030f030f111923120c07020d0510050105011403040813050901080102041d220f0b07080403030b0910060516080c1f05010803040b0a1707030b0f01051606 69
    0x10160b25203040c0004682c0c3c05019000c00d4420011202006880b030201901070702a45105100201d0403840d40c900501414017030baa402200076802030102d583c1c18004154030310906100075800b07001914404107001001030000c07039048401c042048140d0b212001562007800303aa1189010348400c0000500203101400a00414454903801521701c036103803000901103901c26004201e017a94045003c12440025185014060102d810b12441e00c0c2440d6841110f410b481640c1c242c2030360301d031211200402c00c11250ba84d1a5603006501e0803060305000c3c0300105890300548058000034100300b40d401041c41c0038620180505d202c85c031340100302d078503041c0240c5803600104044c1000108503440d10000c84d207104000c040d44100074000e00305071410301e00b030740c0ea1140440007a04e840350319000040c004540000201c40072b0301c02160026454141e002c1c4210f98480c40e469205107500d01800c14050026055007200458510407120b00d0308202802d40112854011807420400c4180800c1c444004610680d01642 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228569766 1250 228568516 228568541
    0x7081c0b0d0b07030b041e050c0706090b010303090e0f0f06030703080304060605041b0e060d0b030d020d123308030a0c050c010e060306041517070f050402030103030f03 74
    0x41614551000500c200d00e841e80c107403400300741c1c00108420340e641407140191a0b0003c41c0c080102c90302d101e1104071044900313402203a809549001180e50040d00302d0641d130450b0f900c0b280900038080c5529180c040f10781d0030703c800c8010600940d00403c4201d1441703222071059114551140b02950b40008100354104058200c0c1c0c2c042c0950900440440c1f03500300154481c60059201240507850201400300300c0b5418503080130000950450042030580c0004182c1e101c2c241110f4a0352205022150701008203100e2508941c14401c141c107242d401034000c145210140c42079241d131b044482a400c0710600352403480011801402580b11070160f02c000701d0388240d50b07001800010700105074450000b5448e42d441849104080b41d601c4140b1010040f041003407060f0480c2c00c0ca02400140b1080010801718040030740424440c60710783c01d08810035200c1d560140e004000c41d459035000c1002c000510b586448181c003c4242d481006280070071076003464000c40e030490340e240d42c49150f000740b050000c0b4010040c074407051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228571016 1250 228569766 228569771
    0x120c060806060c0a11190602010b030f0f07060815040207030804030f05130315110a11011802010e06032a0d0506030a21180609080105090d09120312110702031207081c 73
    0x5054540c8000700d201412454000181e80c0c040203041601c0d110030707033090014652200c480000c0c1690040f40f60000c50711281403510560311418400080c201c610342e140e80d00b041c40410583c050560204a040c0280e000e51103603604a100510b003101c0e41d01c92095100c40200604400708000740a03918400007108141d040052424540c110320040d07640305100703010004020b10494600110300f8401d4800045005450040f00141c41d8006400f0b910325000e0903200702804000508e604d00e00c8840e1180c480d8100d1690b800703c3e11061000202900b101e41c803a00918a0200001c80030b050020b06888203c0c0c1104d100d140040d045030a00d6005294800540c04104006925980f040d10240300ca602078200d90704c5800117182401c02d06800c41e10014080c12240e8400b000000c2c8298101043c0d2003560309013407100d1030314100ca00781034485000a50084045500d070019000c1004400405803000900c01c800352000c004a414810000380640100030300078078000c0140a80e4002d542000c3c2201d03c10640b4003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228572266 1250 228571016 228571039
    0x1e01050d0311060406091a0405060a0c0e102007030807020d020109030b1905071d100315090608060903041d180a0f05010c021209040c09120c060806060c0a11 69
    0x201824010b0035130341125980e85500c4d1200801030550000c00308100b811581c00040e20b01500c0e1640c0d0351201621110040c2e9031081000300e16803144010854a02c405041c1a400180c1844000e040e40f01140c9114086030640000000254020940c3d40482c0c1d040440ca5091441c15001c0121345039031010b0890600888502c000001900301035882e101b4601500c824580008051504082d518000e0901e801c200c0c42039540e1108a10030920b01c80c4005040c1d42040c200d0000603420f40040500c0d40d104520103810745400200004c680d0491000d80302c9100580700f003501c584515550783d0295000f2242084011144000ca40181941003035004410803e5a1622511007680780c0c2864003031171054600713600c00840714007400350274001c100c502d00452004181a10079144201001c1c0034104940c0d210315100c05140086521030b00b05000034003580c0000d94041c0742c880c038080e000b41c2546e114600106a8503400141c0c985440c600743c0307a1109010000c3c081c030280c1c80c2d03601c0e495030341c51008096215030502c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228573516 1250 228572266 228572297
    0x61a0717040320041103062101200403050705010f0203040e0901020d06030308060a05010e0a05120f060903041806031a04020a090c020304050108092b020a0204021602091e01050d03 79
    0xc0c02c0c03c604204005a01e0f01000e00030501050722503079980c5243ca1201042802070306e0300c1e010b101c0000c900020700201104446000118090041d8100e01c4550030a00c420719560b00c84404028001c6a03c00c104407804295140010b403528005c5152078005a0002d2204014095241020a601260000005150040d00310810040761569041079002031820742c01c0040c18100000110040c00b000d0a00300c5460714801d00190a401041c01018000c030b51107035080b4681d034410400303c88401c190b002a0303030052600d00300c242d6481e0000c0c0f1a250242c03e5152191076400094414003040e250410441203001310048941e08030b80c10081d00498100300c410400103403441d442d104608003040756601943d0f0b640e10700000140002c2c000380001c49183c002d040f2506004403040040940311050b03c1031500380f01c0700414141c0c2007500c1d9000181d009400054043c071021010f003017014003a41708480741701840e1a04252900c8554880220140d0a541800180b0561904221000b8803600c00e10300807089026110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228574766 1250 228573516 228573533
    0x70f261c0c0b0a0506030303150301021204140d0503060906040b0105070c061d030606030d0c0201110303070504091b020a0314130305030408070e040f0f020a0b1b01061a07170403 78
    0x80440004144004910400c140c9640c0b140d084a80040300340114200100001e8603480068510011b0340d4040c44035035601d0318203405403031005ca00102a90082c3c5070509282901d0492010080c20354040e0300c0092800600074025240a100060010710040ea551010312006140400c5854103020082c060700d400101901d500102402d41562a032116010350155090742d14140c80d0000d02c0781d00240204012514000b47c0c82010703400a14000c10500924001601d880d40e80c00300682c4540800401c0088e01504640108211400d203141040a00c001d8000341c18a544840c01e408010703008040400040b80c07107003410010140841003182c1c5098000b0340200c03601c180c07907442110703035810100381080a54000c0c09480002d0020045024240c602030381d03500c2088400080c0240000002242d15065440d240304a80287c160341c040155074452248422264162402c04082d517903080c580003294001c0ea001c2021060079169000900b44555036841c5403c8a10241031000c103000705010010100e003500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228576016 1250 228574766 228574813
    0x40e0d0216050102010905100207110a060315051002031b07081f050a020715050a2304060b0f0310241d070801032301090203030d0e070f26 61
    0x150001e149514115082141800440d807285055925011401c0042480030a5100b40100340500051303580b801303450400400909100c1d01c41e0403800d4010301013400c13501a0b10501100f814040b01080e180d40e50010001c12545a8540307400603001804591112418482008045540d62090307c0c84292122441d0b481d01c805042884002c41d81c0004c0c00032040c1c1c244c03203801d4000002110561401400da00d880383d151990181c02015107940b034000400600c0c030381d4059404218030545258102400b401d96169940003948d081c0c4100d45410b450031668540040a0901801d010f00a005c200c1c04a404580c0180a0104d01c0b01041d071401c0c0844104100840c5100b003d4001d2103071403600d4556200b070007403401c0001416002481300740c20050002c642204160030b54000c4400040003034025050314107024041c6454025014032004c500310a9000c02d64100e00d40020381e010460741c4a9541c1c4001d03000300c035120701c1407258506040b45000e070300c2c4001c8000c0141e10b10580c07085600c11109800403001c0390300781 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228577266 1250 228576016 228576043
    0x4060905010e0d32130f0b031801050103030f0c0c0302090a0504050f21030c070b0108010615021515010c0b010b031014100503130203070305010b040e030c1902040e 72
    0x5803d00a8295084000070001000a14005410f4104042900820180d41e1074403001028040b443c421800178521400b006022440c0c5400070a503507071480c0081940003900d03d441080e20041c494801d0400520980303049a8140e80c8041d882045517105481111a440c0107484480c2803410201c050784544850600406031007100082d075190606185041c07084034144000345400203030707207201c0180a8000c1c13008684164120565681c50740415400c56100b00e038001403201c0000000060440010740c8014200d0304017070741c1410040200c0108070707180c07c8130b8401000748040c1b10000c240c2c450401c1c81580701e40341042c1406c0c0c15041c1c0549800c0c0000400741e01001c401e560000801004020001000700100002507102d688410494001041c0e9030722200b05808000001c0300040000b0119087c80f00ca01c0e4020b4142c84070700c0e4603401e100780601600c80b0610301850410743d13000c6c0000d00000c00c481c48414607801401c20140c03540b1200d444040000b4050342d01545840714000040c20a11507580054031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228578516 1250 228577266 228577273
    0x315020d0e0d0305060a121b0801150503010501150909050a0e0615030c0d0b1b0405180a050c031009090501110a02010c0801080f0705040b06190f08010e1603020304060905010e 77
    0x10080c0003804d4841c0200040d01a4610304400c0000a2100c9291440c983c3c0c040301c0e03001c000d41021902a00710a00d544403804660030f149441d42610801480e070029620b050f0000e01c11a0f80710741e0918a10000c01855000180d0304040070006810b5035445140c00900e51071000c00c850185440e10382c60100181c6800f408100720406119091a0410103031081d17000c15180c0d00c7d1800c059488034414200000c002100003001e0001e103c0641c51440f080f5006004010300c0d80140e41e029540c800107080b030499041d88101d18000c0030400750660407007528402c503c0b581010701c2c0c00e4184401c07034001e810b10080484e1290b4881c1503141d081c10b50038028041c0c00e0081d9000092410b00c0890080c9115010713401140103801070040010101c0010511605440b0151008241c41540e034003c079095102e88980b803d41c20194100c500f550030b9010a0308058200345235107900c416600c6181d00404101c2c151600640d82e0309840000d44201d000b60045d40d4014025103001464400c1620741c2800e464172140c10015580 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228579766 1250 228578516 228578533
    0x111040f090509060106050f0d110a03022a030f0a0e06030a09030e0d1e080403051c0f0f05180d02040e01051806090a081e0a0504150305040203070315020d0e 69
    0x150301d8414198442e0300c41e8028011035260800261091050048180000c400019940c070b0b84038098024614203c008005150340e650410b000a0094024000d507007a0380049600790652481b180118003210700108000c0d500c1e0088070411608280d00001c00103051003480062b04d1080d954840203984580d45800f0082003014161800810b07515050051304c1c451a140c00c205004214117000f24500f080200e4070560848240342030840060041b50702c010510300c01d1070641c000c4103512000b00c1d41d07400102d07142c41004003180101a61600200007600c2d0000c0c0080c4160000960b201c1c0400086440103821044851200c3c0c02240942e8940d0540f442c030341e91500d083c022800d24169040e030185000c4000b0f40410300f08200d800f515a84103170005007194030041046c03900c070031075103100840c0011103144a580c1d8005920000d01160094441c40c44058168a96004100d019028540c811b075401006850038904540d15250350100320003496180903428407102c842040c240c8165007074000303078100610341c84 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228581016 1250 228579766 228579779
    0x150c031e26040b04110d170a090509011a1b0f07050f060702060405040b0612040c050f010c050d0f210501050f04140705070305090907080a150503030904020c0111040f 73
    0x54100c040e1003003980714000e08110201c0e030006109600702d83c0c80103040c0300c40105000080d00195006d20003802c1108040f09a0346610703d07210051410014980710251000c0d5103e0401245074824400c64100c4002c06070100f10040454000384000340700a000c01e4181e401c00c00b03d075440c01da030000240752aa0301c0036030240035034541164142c7c208070084948502d0301c14a9800304010740a50312480380501d458401818036076a500b4103440f0051000c031240340c0340c3d18103404c0c11620044140f00d15805044918034000d02c0e548103608a00700c0542000040110b02480582100c0c41c0201d06012800c02444a45c0e810f002c10008400c0c07000022607010104095043c401000310880d2a4540345200c1d034648410102980c0c40c01d03200300c0d400000c6d0304002c1e440d8030003030905039110300c103201d00b041e80462500c0c05c0100341604810954051104150100f0110f900d01c100c003c0010341602401c0d60540c424009001540741036001811070705000307000460303100c56034108400c0f6a00141c100c2020072280e11400d0046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228582266 1250 228581016 228581057
    0x20a1a0906060303130e06040f110a08060f061209070801050a0c030608010c080c0f09030313030302010c0e090c070303090501020307110f0303070c030c080c07090506011107150c031e 80
    0x20520071030143d441c0c5007a01c03c464240c03520f54403946c07464122690016004d40e5403503020060041035540300344201c800e4280d404031103501c01503924010481c06004a40a81080d41c1c081002c0c050180000b032078440084000e039010480100034441d94486c070440072890366400e002d6240174140c03643c004917042e581c0d0000542036605603080b07500703680e00d00700d190369106500c50240e9400102c410252581d07980c059503404a20311171100c141d509440f00240c0c07151180802c00401c004c59002c2d9008100c01d282c518004c813100ca515492090b4840c26020110700100c10f0000100b14a40c17090400098040043d40d4150030f9030821501c4401003a680c1040c250012414401103407190410070180d031a40c41c002c1c0d8042c01e1003d1114018040010a04021b801c000700301d41110020311a00046600703056a5040b400301410048400c5400075044040030400113900049150548071203d094840d080d004800c1102c01c1c150300300080c3c0402800003544c43c40003115003100c406a212969a040006201d081e44104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228583516 1250 228582266 228582271
    0xd02041103010807060806060a0f121a011d0a140409020306090f0d1112031902070b100504020a1b060b0909160e01080606150d1401140108060607060c020a1a0906 71
    0x40c840150200011643d441c401c8582000a42c1099025010ad94104803030b40741c518582510110315003828040602c894090200340103c00343e8072104440d0126406d10301031078001c005550800701078517003400501c1946003c5500b5003406003000640760b580c0c0d00060f10304441640e003452550044e036074003141a4000e1003412002a4142440c410800240051b1030b0b5034000400791451561010000c12841c00031401484d1891400200a5448407810304045484040c00c0e640c00c900d09100d80710004103800c1c140240c0312030841715180d01501406260050060880c0c44c0e41c02c90742c141e5101900314003030f0344030901c0c14001c65040c0300900d8020458a2152071110a582190160000d24001000680030028086511440c141c41da00d500450417401d0000c01d01803400e00510080c245090050250400e00c0514125060400000c010481c614015603000c00142c4001e41c004408100360004100c0c10382010000c40c02c584101ca41c401100d807143c8020f85581038052005c6265001444031200c0200103664 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228584766 1250 228583516 228583529
    0xc0204090629090702030702010c0b0c090a081005090106050117060f04020c06041a04110d1b090b150310030f05030d0f0504020f120c1002010f0603030c03080907030b150d02041103010807 82
    0x11f24203030250300040c00000e07200d000180141000e40004410303440c5901a520f40602c060f000b440865282c0021640710102240d0380e014140c80c0000040d080c4505010f07801c1200d906850b04402c0e41c0041401e0503191070000d0031a6040304ea20300c43c900c4991110320041a44d0100c15014002c40d00b4a4681180100016100030303d0700400002880080341c22948820102501250a50040321051406007401c060f440b909100715019940300264600c0550040c80c104c4404881d41c09091707020500001090109844520104c0510101030000400d8000d900180d540650100c1c2c0c1004680f83c250001e980c4203032046060151950140811030501c49000d940254007280e038140040010b0500e11b6840c950f2045007841110031504e4100e644e4002c4d407001c0c02480b00f000060203031549030308015000042d6050100d0000e64140001003100308049082c0040e2940014542c0b400d84403008808245204551340c00d40c0304c0111f100a00041c0d6903842221000440e115200e6181d6141906144c00d0039000d90010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228586016 1250 228584766 228584773
    0x80313030218040203030f071506060815090118150b0a03151d0a110408070b0910080118091a0a140901020a17040309050904150f0c0c0204090629090702 67
    0xc4010317070307000c01a0b4003402c0c806100d0546429a07400c000b002d0a0885011854032840e100003c215164000030403441101500d00f141400c3c030310718042c403405041c248030f0031043d42c80804036440e5407000d41e045412515080d540414003183c440c425004603030300031501ca001199403240d61030303458405102440020901e0301c03001d1030110800145950010001008040c1c010340c1d43c44403002c4000350a060758003611070354040f00d04543c2c4a1a4806645c0d02c2000220702c00d40c50245c0721061103118640c054142c58540c001c1409a00d441e00e101c0001e01320380d803822620345507110194001c01c01071281c000e00c100c01e103100100380000420703100c95405901801580c856401001303641c2c1d800c1d07001060440720f4020302c0728000c00ba41d120704085034003400541050754440901d505201c18000b242daa140c0c0e280b01c02134400c01440300610003203012500c1c0e1180102c00320710104601000f501e090791001c40d800340128008100c4035079400150040d403400440c1d00c4c005d044e0200110840c5d04051640d55800081c60008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228587266 1250 228586016 228586021
    0x9010615140d0c051303060203010905060906011b0302150c0a1103040b1210120321090c09092105040305121e0c0111070c06080603151807080313030218 67
    0x42100c030b01c20820300d68109501d402e41480708500c00d8044504010390000070280c01500c0313152141c0a90300a01c100c982240c01c0c0743c0450180d2602e80f481600500b8161210700081d05c90f0011b41440c00944901170b41035000d0740c0c00b4103510740c1d43c4e401c0b428441c1c20b01c0c5104503684c02c0341201c007034044400c9103040c1643d6802800f05000691002040300d000101b0381d51b00c819241d4581003034248001d195000ba1580b018460010020150030070b0240d150072680040c1c45008881a4180c00200e4002c4880a232030034124030340c100b0014000f580100d45503801011503a018129840d44280d0f00403196120100191000808000b442001e1005a0500581c0031284e032501003400890044c0d12030740c0040840340000020500c01c1d5210951100b6285070000c0019070b12801d060511a0030304a03644101d10125800d43c00107032140c580403a0749000709500220202d8980c81d02104a451144814a950b81c1072250700b0b00840e001200300064100341e4210155280301505520600c0000d400b025a40b10204080c0000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228588516 1250 228587266 228587297
    0xb0405101d010b0406110316050d1119030809010212070806151314010c05070e0a06050103140c0310051507120809030708030606041d16020f03220e09010615 69
    0xc1381c04503a168a0501c003c002c04424a6003148101d030320f0340041c100079020b0b1004002020480342e95100c401d4403065014407400141c01e880308420754280e084114a5502400068024502141c00060b03110006080640c01c00d002c0380c07001402c3d074040000c01c4101c4100602c40c5001d4021320903c42103205900d091865030343c141c516003c07581c040d00c1030080003c20b031240140d10032128440d5103500041251103103030303880b0110f850200702540c00103a01820300c00c01041550003800f45041440360030311013500a80d40e80e0740340459500090f0120b580f121030b0080001d427a55660854a1181c0e00d800320f03003079949099240420f40000c4d8050b42c80240041c020400075804c80100946002c103030001c41c003c0e900d94911001811601c102d4202c3e05044072288006411181c9100d5824400e031143c0f0b015040c8000014000d0307a40d0482c204030a14154010446030007206200800c0d615410034602840c9001c0e88c9805038131003001006c442c0302d085030390341e201d0800000c061544502d039401c2550520011101c0c1b08072 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228589766 1250 228588516 228588539
    0x50f151008120c1609091101030b01020606130209040c020114014109090d030b0301021c090501060e071e0503190c0207030c0909020306011707180b0405101d01 70
    0x30510010480b0228401028560510400b2504920444003d04d12621101000002e0400c40b0040d50328142d010f48185481d4028402d11034a200140c00404607a82d90b9010480350780301002c06000340c00d40034010803100e600c96000740101c0308156000031510003400405403000780300590141402881d154005088242203c0c940030340300d0110781d03a00010054007502c0c41202071582800582200da0340c82000002070020441403a981400d07075003031201c28101030405080c1d000d6080801101314800460601e201526130007920017511031030000c60004d503030b100b500000700000c882e81404251000f02c561805403005a030301e0b82c02143c0d070030424118284500b80851901107019110718240d42c42280025141c000c001180065a00204018100da11180548040e040c040b41c128001c0c850303000045100d001500c811084850000c0050a1081c1340c006100074418110804500c110742d20800b90310030741c40354058140b00d0038504180410b800e250140c2c0e00349845050b40c501e10401c0580005010102145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228591016 1250 228589766 228589783
    0x60e10050d02060a030e0a0b0414011a0609040f0c05120a05010b030a0b0103240906061d060a18091b0f0e090712060e070908030c070e040807050f151008 67
    0x142e500035144c2c00d45070016401409020b0280320148218222042086804a80c2500c628820304400403000f03a0b0741040c0d820386043e10041a0b200300b0300d200010031414203038041c0801030001040452920f100254ac1c01c04c46400301c10840c0054000180d0183e840510704205420059154007089550715001c60803040380400b030202c182464542c10702110580c400e800800c4422554040c040801c5100780b5030306500c0d6403c0c032561003a142441000107081e4000ea504040810021220061810320700c41000107130380c000745a9406002040e5012150101044102d2010b0424010700044218441080760100c15030500c0c50303410005010380c141042f550121540044000c2911020001d440ea004141c0d104070440d081d42d01107515084e07000600c1000d401045008211030b0316041c1c0c5164071505116101e200f00340d0b08801640c01000e04100007841d0044141d0720a00980e90607041940564905050555a0107140c04950005074960030b03803403803c80c1c80ca070415916400e03044428503001d140d43d150440d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228592266 1250 228591016 228591019
    0x1b010c081305040c0f080703150302060313021c0203030d020a050c030d020a030b0a05010c0b060312070c090513030c08030601030b060a08311e0501050403020d0e010f0e090a0b060d060e10050d02 85
    0x3d5500403827502e140503050101450303004140300d07128541000812200c0480c01070692007840002440c200390040e08400d01c584540241c05035180a00543d540c50280d40303c4081c42040203810010a500175038248064050050402800741ea1244900001030940354072a00da0792088402c41c5041003d80e0304100c1c0440500d5011030340c1c0f5401d503203e000080c1005007000d00c5c0c0d0344021001034018100020144000c0c16100d0000d0100110340710f0112200c0c41c420002030003804101c045560a02083e460f901031070748690145008a403c411000108006410100c0d402011641e20b000388685600480e125524047c81c4090340e199100d254011043d881c048240084c00b0011840080c00301c06249442c243d03241904440240124101303464001d607a8007052010328001100414640d03050f600c0b68151051052590b41c1d103003405941c10007000380188001d0800c02c0280d40c0ca03480082d090f01c40c2c41c0a050b1005504800003034103844c0680149100000405101d1145141d00d02801203560311000e200d80a0340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228593516 1250 228592266 228592271
    0xf05070e1309020a06091806080a0209040f05070e0f071107090905070e09031c020304020105030601030b0f041505030d03060803180a03050703050c041d1b010c081305040c0f080703 79
    0x1e40c05500750003004841c8000e074202d030080c103020070103982080c0c0702d00480d05c2d100201c4242c3d00c0ca031038980d03041b80c3d41030203003401680201c2c0f00c0c80003500d0210940c64000740980056038001e0190b81c0c2e81481c0c07070721136030004021486150030802c42400d148070b9030703030300920600348025000541d00040d0340f038805502900319000d81c1c401c0140c0c103110040080d84040c100c44158055103040c5020031507941d422050300c0c040e5414251100528880301030003030307038000d50303044c1c40707880c11078031200019805411502c0d151500660440c094661340da07100c1c09208016680208808041070500061500304604001403000307243c00c00c801004031050020031640b400c82c80703001550401c501240040c8110340c817540b001d0140e20400c00e011060050200d031700d05104000b19070402800304405100d00400c40d680808500ca500110f0700c14000c5400d0410590180405160a1603140415941c50207107400511428040c9800342c0740c1444541042c0c410310321204c0f07036400d207441044a070b10340082c070690b40284100100b54 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228594766 1250 228593516 228593539
    0x11d0c09060618040f0204080c22020d0e03180108070c0f120509030703030305060307170a030e03030d0f0b12060124020a020d03030504020f060c2104080106030b07030f05070e 77
    0x103618140303d1419000082c0140003d51102485101039009402400040e000d1034046816501c0e000001c40b001444503840448003040d001720990080d000946030f800181c0d1200c280749402401407006000e003842c0c1185420403140020001031159200414000a0040240c488400f00f980b01000e00b10301039006844600401d401c40c81191a0f0207060100c0b50903200306000402055015082584182019000c130b94545549140300248042d0b040d0641071543c0194840d100072038070581207c01c2c1010003070101d9203480c1d6500307243c104503040105003402460762680c0880c100e11f8084035424001401d0f42c000c08555050048401500c20b04c0c000d20100c9206440d001001035000341700e1401116001013544c03820309001d080c05400b0b00001c4404a104a000c00306208040c60100f09503486003d401e0014100039040182050721026030208100030603006000000e09010240a640080d6118449100550404020280a4920200c0c0000e042802d1800b04219650f0102181c40013040440c3c01107942c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228596016 1250 228594766 228594787
    0x106050f03101d0319020c01021c03090203011e0f0e0102030405070620030304080d0e2b0c150e06090601031709010507050f030406020c0102060903030c1c050108011d0c090606 77
    0x21003000c03041076600011603d00c583d184c0c1701298801c22011502074480f0710720b01000482c0c40300000343e05960300f20048102900c503140b00380d00c80f0103014400b4000044802040b01140c18448c1c03000e004002d003a03114404110501403034010380d1740915500c4000d6055042c00e6544c50307100e0056014104c100003165481d10880c0c0d0340d003003070320580210b00e0080d031399a802c0c141040d0210381c0c40209264010f5080c00c4071600c00080c00198010080003401d012049070103420ba04480c1c6511100360b5004118404020346c000c00d480582410b01e40719450000a00c02a50110355030030208001c01407107040c1c00100042022a120801ca0694424200001942c90719a40c0044c0c50a0080c8800641180716018403d07080040020051003a20a19002c4550110b48080120b0743e9510440d840440c507041440821b449402c0b50002d040241c0d15220716481440790741c4803120480b00240e0000c240fa0f03442c3d005104100004105140c0c07102e40c086c0c0540040550302e030206d0340b40c540c0035103600e008038000507014190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228597122 1106 228596016 228596051
    0x606020313061809060e09010c0504030b04020402031b07110f0607051009060605030607050d1404020f01082205030301090f20181c050106050f0310 65
    0x100d04005040312000369094040710348105403c030103d0721140034003441015003140c0310070303042d203240c03031030415080d00c01c1003001ca4203100c0c0030801800442d000d15521a170060b0151400342e03072621003104c141c00090600d0441500800046406410840580c105030740201c01147c100441e036011071300300102c41c0300e1001c0081c51980130340c540700180101508031005883c0110400504d007995000801d04040781100d0b03060004500050b450882c0e401446144110b102d0a0300d000650301e040d03404594a00c65860700c0d507040c86140400225594100c0e108001ea218280b03181c13001040d403925201c0d54903003081c000c60b040c0b01e08103100740204011a1050a24410741441c03001d1411459000419850f4000004c0080d000038106800c2001d40b5a40c503150f960031b1040c81800000030031420001e084618903084248150080218200d10b99400103594480860701c2800117148040405c82428 = true := by decide +kernel

theorem cover : BRFrame.Cov 228417266 228597122 := by
  have h0 := BRFrame.cov_init 228417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228417266 ≤ n) (h2 : n < 228597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
