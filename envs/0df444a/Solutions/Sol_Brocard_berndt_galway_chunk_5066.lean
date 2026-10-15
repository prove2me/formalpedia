-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:52.105687+00:00
-- url     : https://prove2.me/submissions/75b3412f-b28a-4194-925a-989731f102a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910971223 ≤ n < 911151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910972473 1250 910971223 910971227
    0x50a06030b010e040c1214160c1406010608040c05061611150f1222030c0302100603060c08090c1c050309040c020607020f0f060106030e1905010507171911120403 71
    0x1207114a10005801c21030125985030500910b80c04032148d1010b1410041d03203e40c41841100c445071307042c4c080d492200000003c0411103041850030f034840380c0007800c1801400244a40450b020740106030440e062440c040381c1a90341e0382040c5511401401d0070402404004681c0c9519008034294102c22030201e49d0760303020002c0301e040d03504003104407502191084002415030b00d40221ba1100780c520000604602c44540c0d4044506441101d0206d003117006134401e081d0781c0b0700c00c0d0007502c000d18030600e4081500d0302c109500411424004000c00166884481060111348403d1051003209000c15241c0030070444c83c0c20882d28510032002c4a80e00981b602043c5824aa80460400c5c09a1010340c26512144442c1c8021950340d980c10002c8c5400e41c101d00700400846000382e200d0a01c0240c28401c0e105a44101d081041d142c0e101482c00b41c0d501d944803030402c081a58040313100305000c01072440b6404d9505181c01004070b0032584518061040340c1c0c644506640c810707801c0c207031094098400e5418156240620300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910973723 1250 910972473 910972487
    0x50415050f0711060402060d0903050d0c09031a0f16090815010e070504030512030601030b1c03030e030c1f11040f0905010b03040b0708070e03010603060509070f050a06030b010e040c 80
    0xd181c001a9001c0d807070f010380540100b203160169400a051a040026100102004001226048052200421513518541c909020303003036591800740c0391300460300e180d82408503d03004410140c10040b0b0030541088451070b50714a00340d811040070b8404403103024081d4001d4a6018003500074244511602c10080b151901c0e0911403416a2084080d05d8010385691605842c0e9004501009119403c540c1d8554203429404d000f669000005240100d40c07426401c1c00b1a00640281c07000a0042c10540f40c1c0c081810b426011b0803585540c400005d5140114075482c09413102c2ca4007881d095201c54091128002d0b0b013180e0016102003055600d072942e0780703a5070380c0141a41c0400340300b2800480c1c20040001081c0c5544000ea0f4031a41e002003007424079640e04e55040703a000c44020410710034881e408010000076107003442140c026601c0380700005000d041c903100c0c2600d0710f84d55a014180c40e100c010814081da032103d404450441310f071030801041c1107a4401c0162881c0000c00241781d040ba2510011340c0090740d207c0d003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910974973 1250 910973723 910973731
    0x2100f060311120d030504060b1e03010b0907050a080903120907170c060909132306010512070e0c0d090602190e3f061f031203050415050f 61
    0x91035002c00849014000c1c10280810f41021581042048401d0725000ba0480d07a40503100700c1d4001a0200b803500068042d460900d2501e48080021a800c0484d040c24803640392901c0c02150020401c0c54401001065803054290003403c01c1191800300300744040c1001940c2078503070480c00104841c039050422641e03505051085196048041c400c0303000641c0d010881c000d07130141c090801380c58a160f1206108421802414601c0d14841c840135035004980c2c0d0400b04488141c80820f640b07001403c04941c1c6d0310344071042c9c101034420102480c0c060890340000548204880348120f000b4074580c0da0424400550051400d401206030805101d20200503c43e0300504807816101c6840505039a083d40c2103e04180301e4841c29004184d82003059041001600da40da4220180d00c000304000e0b51840c4480c6200010b0a8401650b07030162080c40140c106124500c075002c141710407910307106071441e00d130394a034841d0710100b90040c19034800100b01072001e00242110f90102c1ca45042c00542410f4040743d01c000e900711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910976223 1250 910974973 910974983
    0x50c0a110310050c0d090201110703080903010b01051606050711060717010b34080403080301030c0b030906060f121c12090302030306131503030801031b150f02100f0603 74
    0x602d4a80c1046190311800d80121802d5074624208001c40b17001000801c001030b4183d05004458000150006080110030043c6110b50849621410003505060079902d10403081ca040c010248a800c2800300c204d440002c032a5000030002c900c64540c000c0c242d860f1389515000111a020344c3d4100808543c01401a038a404a28400082940c1c2d84105020050003903081c40d03440114240403c18a40145020502c3d46c4c040d00d998038401a42b180d50780200b168000e600032614078202000400c244805000c00200501c00e030401989185010503150703840300c200419440c030410700e0080c00201c549940d000e052350821014111903a200d5943d00460054030800d1300240010a80e25010a25400c54001da40c0340c2c9502d81c00944c110f03100c070420000a0003502e840682c4042d540c9074240400180044407000070340c000d880f504c1d040e504504008003610000d40014001548000c41007040c08151504445448010b107481440035a1448080742400800c0601c003112a0134082c941c2289003099000e0b200300c81c400d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910977473 1250 910976223 910976233
    0x607081620010c050312041704090b040c051e0a030902130f0c020c060714010b03031c050708150d020f03010c02070612050106050f0c0f06190f0506030706030c050c0a1103 75
    0x71500444021009203801003480d0800e100d00000040c4070804c103a04644108104585080d5a06821915070401c2d40b1031a64540c503500034011a0400d80300d42c0c40c8280d403d181203454076446038002c2c40071111040100410a60024401c481c10303109601c100701d49070703009148000b9000c03003400c03078800b600d10040c14000103031a00c15110700c1d4900025080b07210200151207541031841585440001c446449904103043d52075048085840d90b045c0014010509180c00715403400c40310a1051003101c80c010148170034002071100748848c080358861880908503045500c0040403115201060301132040196003078042d0b00308059103804640200300d10040d5242c0390340b070b84882c034200030f5007c0950f202031246502085040100807140450a0700801c0301703d520307008585010107000425031901a0440d204102c0703940814600884927010701444880b03402c030396024003080c00e20100083e04d60380c0714030a03002410355601c00c01d034589010b01c0035144c0c04800741060750050310041c2003ca19914142641610901032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910978723 1250 910977473 910977533
    0x21e100609241503020901090305030706060602070e13020f06070b04062f070f02011707081815061e030a050607030518071503090506160306050307030b0606070816 72
    0x340300d003080203e0704040c0301c004424a0103501a8025400202d0f03280c100003104d04080081401000281050391003424009540c51406000038100411900315194522071641448001c01004410948840d01141c80381d140000250008004d8814000000d025807504810030013445501d50040c8161170440074004400c00012004511903440d40241450051041c8094004034091040301c520080c4107041c0070341c0480c0038005010040104940850005048008100c21180c06c17440d41c6406406210040041c0101560131901c01d4031300801143c024100c01400350503004620200c44d6900348068180e4540c00d03402c4c03d00704d0721503104842c6000441d003804045a41041e090800e05a1443c0380d030042d2a0450400024880000f0764800301004c141d140c404010201c0d50600145000701c4541c40208403d030b01c3e8440180176100d02e0f40c4968071a81003401d00f00301050b020124550b020350121982603a038900780c904130541e4000c0d00103828858986015400c1003100c1410b000392080030041d002041210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910979973 1250 910978723 910978781
    0x1308031012260702181302090f07170601050d0e0c2206050d0210030218120a02010e0324100902190809061b1305041505130b01021e100609 61
    0x420008005d400950070040740000041800603c0d4100c3c0301007110010600075a00003e54440e016900c021503038106800b40700b030598102d040b84604842c44680103010b45810000600300d0302034103240304002c94840c42141c02204050001445039000113000400c0309000b0f9580c2060a40d00102104000789010300108941c036040020f1b1071006c0d401400024901c002420417030103034010b06149440005c000b03a200011399501d41c420100c0030441c00050030050864000100349601354001c103400b07034216502c1414a01045500b40841d189191150100340c0c13581d00c400100c0c1e10060f0b0040101c0351001c14110090624404504008001903580c500b030303911003090f040d03180c80c1e003503d05001002c0c0d0140840e903002e01070009080350140120001000c00c5da580081b41c283c542ca01692000c0c01e011a1050101d4a0b100703400c1d850032103e02c04208078041d10600040c0d56500001c0f002110b291169055401618042000c01c041202182080c007240795070701c5881d800f40c0383d844060b06841040c002c860701c0c640 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910981223 1250 910979973 910979977
    0xb0f04140a050a3b0f1e0a090305070b010b3006041812020601150314070c050a120504051003021905030613060308070515130803101226 60
    0x20390001c210010070352410135071043e034002c80c44851100340c6031504804d2800104a00708070785050b0044c0c0e03890301490a80565003e01c4002804a1103410301c01b20080000c0342820000d40d4840322440d000202418141030540790350084403401840c1003004400460105014400760014109100200100780300144400c01e02089c500001c0303101700c6031480000c0041c0b4140e004464680d00041c00c544a413040380d15440495280d400305d0030090303403184004210350141e4150407290a0540c4c84c042050740b20002d54140240c00190507402002030003e0070405004083c800c0203d0301c0c0d800030003c2680c1b003500700040e203560400c0c49000d1040c1d02c100f10492100d80613000b195a0b0011100c51110721075842042a00c0c50340020740803076003104194211414107025840b030b01d03024600680403680c8412041c40d000e4a01084081103029001806060017860444880441c60003680302013202c1e100c0d5550009142c4000300c9a107c9007007103c62002d84002d2008072403c240c0f003000d24035118001141520b055403218 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910982473 1250 910981223 910981229
    0x206070804050a060b060919050906060405031c0201110406030501030201170405061b0c0f070302090c07021503040f06050f330f043207020105010608060f01090b0f04140a 75
    0x2d074000c0f83c2c0110002d00303154080980040d00030001400e000300303c00460030500e04c40a03200c41d840407000b810b101d20700c5c04124980d4030020480d01c0c60300e081d00b0500801d44410441d00c201260000c003800000d24107000390480072102e005440086d44541e41c40b003004014150a200c1039010882607150307903001442c1003004070701c201c3e08a002800c1c140c581d07001c00104e10118004000720f80c00140501498039105004560301c03110040000c1420380c0c02c2d4010400d03400c070003806091110304c040100c00d0058840c0c0103007a5401512080060701ca0f40c03142842d04c000c1c46003440c001e0200c0c1ca0300c0104060200c2070741c0c189008041440d42c085240c5450401d11009404840d500140100d14a8940074030380340c000d41c1c4030000074000d80007082c1c0c0c4041210051019643c81c01c142001012604142c03443c0c140c915030564008501d00c002c1c8407a5150580c05810000060700c0b4900071080740031002d02c0759000381c4030180101012400690794012a1a04149541180c0100c504e242d00c103020028081c900040303a2026 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910983723 1250 910982473 910982483
    0x709230a18031b02030303070207050a08030702010c080f090306130501050f04112206062c0904030507051e0c03070f050a091d01060312031107111e1c030206070804 72
    0x6006407600d080d00c03080314407143c44a8090759001e2081c0140c500b40b000e54010212600100a400c0c00d0000300105005582c0000c4e005510074482d000260307034403c07407001c0c64581080303081e5a11304003076000039824400c080c0ca6079014070800c020301502c1401d108400e0001800390f8001c010a480d000070300f1844100c290b4002d4a08901d21418100d00d282840e096400004440d07191403a05034584d45030010340d81130343e010401185920800c400c5113180074a109000d07542060b000281905080c0000b40f00300da0180010701044030200e022801c10000308600020219060300d503a640c59040c1914640d1203450503000e80c068091050001203024a910924041d45e03402818501c20302d041c40b8000b40144828405140c5a22440982c098615001c0c49928061401428a4100d03030038180ca015003500c07107108202070700170070400c840404039044800e40104404111010b07800010f002032801030800001c040603078089005a424211038040000c0c0c0d0364201d1294080d00c034148c5d903c02d020360b0444c4080f02d010f00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910984973 1250 910983723 910983761
    0xb04062405040c030905010f09030e030a0503040b0a1b050d090512030f030402011b0b010504200316110d05040905010e27071d070e041b030207050709230a 68
    0x4034625003508900308541c424031300016410442c2e15030350f0035500030725040180507503212410070525600c00d02c460320701c0200742c0040100d89000d07520f450380d85c400c0d07100344a01d61307101242c002c40940c2b080d04c0c032840b440240d10301074034400424104181c40711960004200403985140d0000741c14181180e05800134a10280654140301251310310a61903440100100d040041001e041c90031150090a005404c5014204640b050360614040c0002c8030320808044030b022143c1101d03621080f840380c1c2140e5000c0c42a95640b0b50342a4400402d41d950a07281c10200c9a50041d01050701021317900801070021950440414407650360303500d0b2207041413030080c0d0b4102060100103001c0b409500c82c00480812205070401140d61180d901e5800c4810a0342d0b628101906032480c0c428441c5860744605030740c13031a107021a820002c068014450510b0711035105581010f16801180040038050240b204000505462030140b0881d007003948880c0d0030112000003a101e100c3e110700824010422882003520022110b24560 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910986223 1250 910984973 910984979
    0x1121030a0305180f03180901053d0e01030f020c0d0503100312030507170105060904110904020304050a020a09180b151207050a0b07052808070b040624 66
    0x1005407100030321000188401c0b40012003c00701c10001d4071469140c03079014507240d920006507a022070b8103100d0b075a8401c40d107a100502840e0354124400b50f0107892880f03843e40581c09050144840406000d2041b0b06006207a07400c03900f550019203000503035100b642d00300949003030402c000049008581200303285034017899070500c095004400a40d04440c8190785d580600d44c1c0d903031f641c940c0710714420004400a508c400c180481c294214000181d22951000840050740c10440890014060450b90501c6280c0380d001c40c031048080d40d406c44016207404ae0040d90703280340c9401c100303543d1040080b00b00c8c010700008100003011400d510881035180740d40c0d00d90070162011500d03102000079001d0240c411082d10600c04441c02c0d902c442e0100f4840e034100024015040c6060100000c2c40b15a034801000c4000410521001845c08200c0c8a030360240d0303907406403450000294200070300d00a94002080a20001805003d206900e880d89200754410340041c0110900028411007190106940303070034054091100b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910987473 1250 910986223 910986227
    0x1005090103170702120a050c0a05090915070e120a050d021204030201050d0b0303070c080606010309110d1a010e040b0606180f0102030906071a06090c0a14161121030a 73
    0x24010f09000a009070241c1d8400082d43c0d0808051070000c44144d0301624a00d4494207100f0a00320041400701c1310f0040c00d14140c090306441e11030009450010f005902c0c00a1020717800f88410018802000d0038a56203030329500c4005550391000030090702c00d8494102c20724281403000401d5015100034149044c10185150b00550b41c9822482040034a1611990921320743d803801c0001d00003550007020079100e1a0305d0850300c0c1e4200000504190304040c00c00d0075400106144407841081030409030b90000714402181408200208401c5440c10b5041016000003441308081d0400f60040e030080d88100403d0319083e081042c580300780c0b002680121410500804070b03181180d1803182c0303400180160703403420748407000090507503200000031109040d04c280422a0501118403a41e40300000f60703840c0c08142080ca00040d903034000d1091580404c14241501e01000f125070046d1210544580c003000d41d489482d1400301c0a00711f000c40d0303844c001d40c1c103101c20340481a580110111781c0c85000020318a8510b0070401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910988723 1250 910987473 910987477
    0x20a2f0706170c070515060a1809060608010c02070e0a110f1c09150203040314040609090b0405070c021e060d05061002070f090b1512070909020f0a0c0302190605100509010317 77
    0x1c0d82c1c8c0140841d000082c540d80c0360180265501e0076030300000d90304000380f6004d0300301c2e440358004501e07680c075151036041c40d81d03000503062081d0385203010112520ba0740d00c00301001400b00e1341c915880c4050003003450a1102042409017001030444001140c070815000c0302d0404840c001e00707002c1c00185002038801d5502c2c00f594010b5030424004d2915540350318003a10380309100e0f4450b43c4410b00103107401104000e0000984124500d500044070140801c1c14800e20040c1614003081d4042c0c81019400c0c3e06000e00c0c002d24885070501e1402602d03a039220700716150614020403044403400d002d04d56440110314014400701c0c030702d011784203c01501c0f00c1c0641806581c200602d603813204990014604401c4049524000000d0481d203018148601100d02d050640100a40b0b0b09601c041c0d9002d0040c4010034010106c00b059030030072045031425081f0341d116810202d01e446042c0c881c030385070000c0d84013540b410b104da140c000d1481040f5201850030050390b41e9092001c00380091102412070400504e04500b4100341d080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910989973 1250 910988723 910988731
    0x90922020d110a0b042d03140a05070609050f0405090604290c1305010c031d01170907030506010501020d092105030c0105090c04020a2f0706170c070515 67
    0x11061000480400f10b084182a81c100b001c3c0d031000403504002d51040580e4907806c0500e00b4a407440076001d0f0242000c0024200c0c00001c003140400380c400d201300c100410010030140d81007400c40380788542e20030011302407240714020103000d80c0705804910500d060502a1501648110009007100d80c0d46440701c0303021140b888400c142c900031810007040c5070340e104980240a03804a000301d07076441c0700a105001301c10b1036551113a8188103002d010940813036008900b4494a00c910400c5000039651040101d44131500420034070030041008090008103034001840c0020b6074403c004840d4266244c00c01a659884149510b0000901c80c0800f4001c0800744101c6410901000303d0b40e19111415646035411034008040780d4110b41c2d903d00400c0300c40c400405c80d02c0e0250009a50441c41c0c646a2400107104007850804d68030548500010001e50400081e283d40c0448500030544500d42c0d103d240051000010780014070381c110f0b002001c507001558030002c541121340d0000c002e00035000c07100756401e0460b030014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910991223 1250 910989973 910989983
    0x2c1804060b120f070f0e010b130b040305010207050c01092d080f060a0c0e090430090303020c0a141512010312080f01082e060308090922020d 62
    0x50011015160400318a6100541002510398519143d0981d890700c11550b0045144080740402004840055803c02d1705407030f00c81078090796481c07003189031f408500f84590003e20040ca00103000014402c1c10f50162604600c21010703038800a0340d03100110752061840c0500000801c0c0b8040d00c100c0524031004220700241070104000da2329944002450414801008801054200c40c01f00142c100e0144a40320045403141000c0d0b01e156203201c0481c080c188001c0c0000c055507145c401388200c0000340c2e00c60005180440050404e0708903d03042c0100b05402a101c200c015101b00c040042e81860000c004100703841e1800c2502d00169510010000c2c0f07020030750f142c41103014040101c40c003982d03852162280a5409001d103036180500101004103841c1d03008065174012520034006000358000030404880c55944980c0b110b0700b02000100080001c1110000180f074189031800010800103c1c00181010b100211070744001a51141d600c1854401240409a5110203039044540107140c64001882454010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910992473 1250 910991223 910991231
    0xb04090210180f03033c2303010b120721020a0e01020a1104150b070c0501020c030703050a08030709090513060b0609030619020f0a2c180406 62
    0x640200e9801d0000d040c0c080d0008400c0008941c0b4001c090350140002c004806484800300d2541d00d0041ca40c403551a00d15403049902000e52100c001e0101e04000035403141c100c0040d030000502c201401405410030350b00700000c031550800304035482110a40c1d0496000c400e20515100c210407007038031002d1000f04200e0900c459903096010098105903d8980d00044a0300140d1725800000058041c6480c0d4400504550011a0903400501c0c1800001454a002c1e039002c541000d1070703044a044114940c10030303901301d0b0740815140f083c07141c06011039048603400c0c1c0903506401d0301c0c00300781902d4407201d0101170701c203070700c29038000e800a40302d04000c5a000409243c000c50140d102d0165a040d075030182d500030544225035501c4024812184529040c1c1401151454500903984010039110000241000031011141d903000c0c65188443d012603848406800c00d00e940e03803040c2c2c032020b480e041200800e4070b55500c020100c1c41e058502c0c100001800c4000400580304e03680b8005002118150090003100c0341521 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910993723 1250 910992473 910992491
    0x30c090c0c070f05040f0605181009020705010f0506010203030c033105010f0b1c020105090312030709150903110609010c1502042409030213090b070e03010f1b030b04 73
    0x100b40401009841d11070f220390b0429280400700015582c0c81c04160140c189020020880347d40c403101c2c0c0340003420144504220340d6480a1043c0c0e00d160885c0d10242c005c500004e5842d04000044d07016051049040342d0404c0561549401281c1c0c0340401c03281380e4000754040000c40d2240000003440d10340710110305604d41c3c02c0304900d003440b0102c0a10a50450300b0341e46680b4444e80c2c03511382d4001c060300040c05881c80401004040302d0986234028180010b814000300107075610f01ca8406004048030540c0300a409980ca084c0804003c0400c02c0314412804001c00503101e9034480c038400c20105c011a9001051491803400900030011b241d403007600080c2c14090210ba0a8000841c03c0e824243c00355040c080c010303150b03451710489800098121488025696800e44d1050f603454114140380c0c00c4d030ba0180c41c101c01c02c2646003c08401403a01c02809030a400245081182c46903101c2241105808150024030142000c0303681c44d8242e03052074641000401c0703001c6100c00014802e51102207104801440070500300c2c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910994973 1250 910993723 910993747
    0xc060c0705072403050a09050d2105040b100e0c090f010e0a030302010c0e030f030f070f1b06030b0603161209080d0203060f030a08040306110c03120601020d020c030c090c 75
    0x40483d008292180c90000c480015038041c4076840e48901c01c50030900000a40b0341d0b4442e19607483c0c3d068201480340342d0381c010280740b04000050301c00300c888410420041c241400c0503002241d04903903803107540250349000b10f8240030840583d809035001c103a10608250040e02044101106800454100100034007a48078030358840b12628011402900005500c00b940c0c000105002c01c003140d418041d80c018030340b2441200002044404105c40d5948080d01c425561920070000f02c01c800010b8528441c4001d00349260000c042c0e28012282c5540f400c1080c95004001e00c04e490004844140d08441c0e6518040007040c0100c450200484040380c0004101006945070450f41d00b003605550705a036404070070400b07541001d5582160a0000f200144502d24050380c50701000e2080b800020002030712051221210030f8000256070b0082e40e8241660b840303507005a9040307016981200c4840c014840c50803403884030ba001050703c16070100054050041300c0400f10070b00000001c003500303c1000010800107804c10301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910996223 1250 910994973 910994999
    0x40206160b010821041401140d06080d091d15330f0d110403080304200a0803042714070801060f0806100908070b1209030c060c070507 59
    0x180c8115420740703195041036055481c0c05500c44031244112210051054403642c02030680d402c442040803600c420f421030000495000310064030321820741c0404200e0410081641e002201a07a003178a08940000d40030b4035048400d41000d100c0c40b600c085070b680440c144202050f40b9280c0c4100083d44120722503004c000071a8003902414640b20000841c080841003400340c0100b40403880000d4107540e4100440025000401d02c034140b81429100c0c0e413500c0601750503442d0010303203008641050049480b8903160628644100610001c1640301d00c0d1555024020b01e403495000080d01c00c0321000350704060508102940350f0317000d6142c0d075124a01c07261f945140c01031a80a00c40400000f100b16004500340301c50041c0c080300040e0468428003000c00115100144d001c0c240da40c0c420001c507505259401c0b560b100317403003007003544c0c000d40d840340070740b00010401180d03000003020035800041c1d40005603518a400319440703016040d141034060f0840c3e008a042c0398800005441424041d005480b201503a465843e0610 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910997473 1250 910996223 910996267
    0xc0f050a0311041514070c12420606121d0a11130606020606090c0c06010b0309120304080f070c0f15030c0f021e0106090e0102091014070605040206 65
    0x2000c0302c82241015900c40c0e03801401c26030845c511810600d044ea22615869154058122010015400f4800380b01540d619a03044690b42040c800b1900103040d00030302403903948420401c160b06106c181c460000b2262003030001301c81c180d41c0c992281044c1c0c010308401814841c3c040840411000380c04102124003806006092880b4005204c101d0001758280300c4030040d80445841d1003440e10004001164011809544c004c504655500480c9c4d00d00e40e120000780034002c1800c0845c840c450012524100b40307030080d07006910b88001c6a01e01c80342f080c5010301d40d1000f02e40040c2058418406d8940c4494030300d001d0315402784280c911100700c5441e01041c0303400401c1503028031450001003002e1400c1540502c28490026003520382908285801c8001950359000c070800c208906915082c0150b01c00003e51104005d812894001c0c001c2c60350703c0040e14080e4206001e15441646248440d000060044035152440c0001140440c03c10489407147d0006080c020003d0740c200d2020440c256540c81d640c042c007040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910998723 1250 910997473 910997489
    0xc0218151e10050304080f090105070b0916050a0807090b0d0506130606052e02010b0a18051612150b07030c0c05030318130b061b100c0f050a031104 65
    0x5141030400202d000c0101e0700c101070200400621010600c4038040301c200c12128040c0036510b44001004079400d2090340005001144110203000341100c3c0030448a038100c0065118060141c0c640003000602d80c1c1c2d600c00d40b203031a4800881081421000c0c0c02c0186582001001000b4140e0151034170703810150100c41e40030b86a20700c104106d0400141e8854040580b00668007095080d9045010414070201d81c81d00c12502c8011280816815100350084150754001500e8800703110fa44030442c5040b1000301001820060811000a03a081140203241d130449619a6078803401466444ea418010302c1200c80307112211612910124000700000028520f01c0d102c1d6031410f1161141d8106140150040c2d040729200e9007040200078113200700c104080d14030445c201ca0440c5980320a401050081c608085a20307000171001c0348248034840d00382c0105201045034400e0f030b803200c1040c0200804948600007407601085451900e0f0650754440d03005080e004c8000d040008d007516401e50904003a41150f804241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910999973 1250 910998723 910998769
    0x90b03070f171009171b1e060c070f0f080403080a2a03021e0c03060103050109030f0e01020307060504080d050108030903150c030c1c05090a02010f0c021815 69
    0xb198010840c1c5803001c5040c0c3c004201ca940340c2d41d180740a02071116000c04a001c00400c02e5511421041141600030052100700c681c04170041071480c80711411106102002c7c011940019032241c107140c00c50f40b0740d56100c484200710f0700c041d1f503ca205030000c451050f030305800140310100009208000900d01c4200907180d0340c5c0842d5680c0031054082180000403140c620b0540d1008000940005801c04040c070300140a120402d610741b4258138028154208036418881c5200004c00d001042d4080c0c04003d009684201c40380c1c02a10068480002201680b40181d004000e03e00100d02947e0081d0303013082c03240d409680b40c000c00d89a42c0091721801c3e00032140d10b820001e231400580c40e0800401e03a424060950585007840c000340040014040100844940500000c43d840c05d07121008030034802c0c84403280b0800046c10102c4143d60741e070310000422804a007150f0b0944251074042c550341c01c41c1581c014a03d000421503004540480900a0000203a111240d02500c601d81c0d81c00300004080c480a5003142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911001223 1250 910999973 911000009
    0x1a060c0313091b030213090f0b0303121b190e01030b0904030207081b01120c0203040302130203061305010e04060c092601050f01030201020a14030d0905060412020d09090b03070f 78
    0x70f00038120030008007007818410054222119592100301c4c0460301d514100042405c007940040e00981003440c6019494000040e01c400300804031040e05014000c002c5000700b043d07a6003025200c5c130f40302d088c505200e00c80030714045a482504c40c50044074a1603061601103840e90403200443e00866090b1002c40c0540c02c2580c2c1071103051130401c0f089842d0a03580c80300c103500c001d4000003e0410307054540780c1d1080d07607122800900c44034000c20864004690141c180b00d055450040071800075002034400c02e1041d1014082c1056210103401900d0682c2c07070030b40b801d512a4031195100c2004001301c002d04000e000403244002480c02680d070303640c0300100c3d91070441100b100c114000b41d421954002c09a00705003e500005202603680041c0031503807164071601e100340c141242440707d4514003130b805507000d00c6800e010300701e0f04000c004138450b030082e44618404001c50b03404031b50990f02e442035468a840010704940080045180a4000c22a990070243c141c40c4c04980b54601030604104c250406044600701314032034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911002473 1250 911001223 911001251
    0xc021507150e03031b0316080406020c1c14030103110d050c0a090207060e01060303020a0b2509030209060d11041a030d090f0e0105130507020c10020c10031a060c031309 74
    0x78170144030050707014510300e4241000f2048000d001080810000394030001410000c159045622070400343c0708031100d1700f000b000314500b014140f440c04400101d00c43c2a00c400400760106985c10b8980c00034001c58054140000e020f1900d0025a080d41c09201d0a0065841500c0740c00d80340000d000d0100b400350b620110f80c1441e405413108440304640c560f1500c2d804001082e4045030300c601c00f079401883c2c20142c0d11040c600100074074180565108030f06014441a415640003400f400c2102d10076a40f4000595401d01009101051901c000d04000c450300b80d14a40c525041e0312411001d503c0145030a0b0200d00f10021901e820401014076002c41d02000301030207070b03484060140c00140841d521005940d0304200110744800130301c000d80c6565940382d070040f90302d44c0d00a100100d40001c0c0030b800040c000d003412000075692a4644140f9000da14401d4801b840b0512901034a024401e45d801c125041d40c019400380801d41d4001d0041d419207001c140441c040e121190306040e4006c100101d4042080c0d81c106503d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911003723 1250 911002473 911002501
    0x6050604060807151404150206040b090f0d030e070e0109140105060a0522050919050c04080316111c060b04020a170c0418050a0b010c021507150e0303 66
    0x440c00ca99400f81030200500c10340203040d5900201c05141c82d044190f0021800d000310b020713582010740018103040160300400ea0008041d0701c0303180251100d010030f440c0e08681c42c0d2681c0c0c8140b0b4104e260341110780800c81c428040d42106100140030b01c00c0f6206299079070720400f03090703c0a070002c0740c1075925800343c1c148010200700c20f80d0142c042240c07424a0010742c103134050410710400d842288012041c41e50200c52600d80c182c07004c02010050561055803425425040469280540017a40c0034981404a8104021001681c06070f6004e00700941c60042140f04003008a0f541101c2221008464225540c458580703840912013010000341d402c24914017840c007081035981e05020140201e206010120416600172130203001c0f52403110401d81103449280c40900d442c411504036050002d400494201906c0ca01d510140c818042048100300900c808401100c141d4a0b141000e5800041d1108800b404107541c0010070314071344170704200200c220442c0581c5080c0c0e440b20440451030742000c420000700c0a84012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911004973 1250 911003723 911003729
    0xc052118151905070203180303090d030507030207060e010215090106081606030c02060f0609060d0b09070603051302060a12022812060810020c0c0d05010c020d0f0e04090f0204090605060406 83
    0x40074456450b1131480290340340a052000d600714401c030504000140c506000702c4800311b0000d480b055240b441d60902078056800158210700603ca1800c00240d2544102490018500141d0140c00303005520045803207085405450108295611680090b100d9020454003180001110b100c0140700c0c82d000d400b80841e6101070703c01040d50414000c228480c00d440480607803160040b41c1c001c00f0b50f101c0b80c0104480000341c10000384050046014810b032260006050340c1107880c079070360600950396000340100b4640327550b030340083d0032402c2833241224060184840c0040d0084a010050801c0178613841c21000f20081084902e13040070001041c0103181c2c4c070241d4500c1c05c0248640501445191064160b0740d0548200b0784852694080b0304202c054405228444914a0090100a07880c070182030144c001d008088069015105040d5501001c2c0e015110ba102c00c8030903600e440803482501790a0001800c2080000c440503a400c140d01d20040c1e8480c41281d0400f030250748001110b1421106000450700c4c290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911006223 1250 911004973 911005021
    0x9060901260f1c03151703210105100c0206070209041b03231f0e0a0c0b1b060705030402010c030c060c0e0306220f080c0706030e010c05211815 63
    0x10300b805c0306a0842952100445111911701251003c1060186045009241d5100078005030031503841d509641008405045c0c400c1140c40f07418800000900341d80d0460305170350080d08041c042c003851015240030903141d94081e02800e1000030841445503100700c0174085030011100b40c440a041001881d69150101083e103000074001c0c410101d18440b800d13100100021096112a00c0e0070003d0707141d400a005a1005076423280400c5440c80d100c81c00e15180ea000f032601800c00d0140809415518480090114000c2c96280c407614030319140c035001140c4d4254121016424005d0070342d080c0002034098440d01071948119a07030048004605010981051800780500e40003c0c2c50045110742c81207400c80071002c2e036600019040030300c1ca151504c880280510148440c0e68011904c0c00a442034058200c4102044960000c200c0d405401d141a00c041c0100810780c00300c04204090103803c0d4040303006043d00b03c036400f2000c0f2600b40305401d45900e0307c0302d00d071203030030b44010040705000b001c08444140c101384810807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911007473 1250 911006223 911006231
    0x2010c0305181f0204050a030302010204080c0607241d0606180601020718150b04150519110a351206060d0605060409020702090609060901260f1c03 65
    0x42d5070b62940e00c0000303910380c0c800d00f0b000e00b1104200fa03039180c0c122001860050403540901d562410082e000b90404e2061030303040c2c011800085520326243c81100c46e0740b6804040c8090300030480400d41c2c108020452160f185603a1740200c1205050344030300410286540b0801070440d850000d0900518681c03850317940a170041d01009025141c0e80101e0702c1c00540d90401c01402080c6010b01c0754001803ca004201d441d03020703c10802107200c0c0d100e00020015940100715942c040102440110341520454441c0011525803881c2c01d000140b00e4403c0c402d03684003040440d440c14009032510fa000c07403560b0007210304070b40482c84202c1c490a122039480041e00042200389080c0508000484010500181050b100380d0700020550042c4085074014405010040c10058503680c81e044044000e61003084283d2083d8401000188603143c078040341449900094207042c0640d10308a041800c1c3c2c16192a1241034506e6a10300601e2000d00300302e02d1001078889401400e00303610024208041d1116407032440101414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911008723 1250 911007473 911007511
    0xa0c080f072102060f13020a0f0303030914061306050703090b0c030601200c12071208250c090b0103020906071109060307030f0308060a150903020f040c1202070f05070602010c0305 79
    0x1030005d5580c010000c13001e5024214080c80020011211034100b00703944428148080b09040e415485048a40d20891612604005000f8041d0342c0c0c2004461620354021845820710002d002c9810040d0042e4850801242c10f1516aa640c0e21000c401c4640d03a00c400404820803200d5079020320801402c900e40c0306c101030f0078201010302989680300328002d0342c01115041c403091018801040085c0080600030394520220003a403070051000c0e844003851201302d40c2120000032804450403601411140d000304440c50722450181440081e1903000d1341c86040c10f41c24400b40c4810b8484070001c4c500c25202f00018601e00300ea400803c45003207806820540a175001010a100113441195500c15407500740c2440c0007180c1d00d003000914040e020760000000802c0f6401041020340d004160001920300c00c440c2d82c2e12000c050f105000454829811510010b404104c810301c24800035401010300d00c1c0600340d0404080c010343c4a40c3d1801145900a00050791740b0002100e025616201e21a04180250f00304000849 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911009973 1250 911008723 911008741
    0xd1404030c0e13080318011a18090705060f03010e011202060a03050c07021e10050a2102040902040e0a0b06091e03070e07170f010503030a0c080f07210206 68
    0x1da001e61000e0038035110104501000c00800e0056450f840400c407540c03840c0142c20f1084944540203400515820603403007156295981c0700104001c00c0190104402500e0351042c114460380181669449001c1c840b4042556154100100071070b09184041c1e640d41e5140c00450400c4a5050b80880c601c80c003901102d00040c0d80b0701c001c54900501524002c20b0719214082412858424041e00940c015501000500c031206441850581d112045460340202c2c200100169401d10031501100b00148200c0c0c3d00c100c5181c030640022201140000d4010f0425072558182412030b03205800090003028403000300001d0140d03030300440010141c281e9615061035030200200704080301e061000441171100c40072211181d1000c008400041103c0300e4007078814144080090400150041050104116000044c9502c8402c4c240d180c104c403c050000c615116408500b00c0d100c040c1424203e03041d0001700520503618420102500c0150301510306000044400d4007440c501c014240e0002065400001c10002002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911011223 1250 911009973 911009993
    0x3110f2107081c0f270e0a050a0506030c15070b0405010b13060b0d0209040f0501300f0803070c06050108011a1801060302090a12120201060602060c0423030d020d140403 74
    0xe04e905081440c0003180d0a07010200c0d000c4a0b075410b40c0c0000940009007129981001c81c014100000108069100c41c140f900c00da9034105d81c6150150321604008860f410000c0141c546803110072151810403640380e03202011910705407400c0d5001d80d15000001110303d80003903680f6061041d0441040b0715031070030074074003030034007501c030b00c0315407059000c25294030644540e08110084105403e08000a60b124900d084060b24008100c08040c1401c0300030520b110704042140000a0f000000004480415991074201d03600040904040256520625000030154010307180a0300d802400400c80066007411a81c4445030031103590b22404280c1010664025203101403415500700389005641c0b8603400700402e0390880c0c1540482c0701d03007101000f038800740001c521403d03140c01d04030340c003c2c03183c696514400ca0307a41005607206a00710300304220410241e90861460008942c4c2034480042c1c9000d5031000906180c1000c00078805a08040170329070031a907210542444850720340c4035850925056444080f00c034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911012473 1250 911011223 911011247
    0x50310060305070903020d03030c020c040204120f021203040e06100525050708030f090a0506070201020d05030405070f121704120f1703070c0605010f03110f2107081c 73
    0x70650392004100d905105124440107103801501e0300c64a0003461400500a01c0b80c8150300d8014080e50240c0030301441c00c3d0084400300c50445100c038010084070344545414101d0014200d03800b04200111001c020000e00c068002030002229580d050314020080c4170050008a08020802c001040075113442603000c01c80c104a40c24083c4890700300309030341c5485490000d03075030452111407001080038005130000d04000e18500c002500c1c9081b11990f00d0061001038095014000d001d07030030040c0701c0d50300c6c0c1d07214401560b4040d0045046a0160795544032072001c56110790862480401c0e68402c90084c40303a4001880942000400c00c00d1130315242c4825054506020b41000f0605103002d0300f0042070045071605851200e02148019540f403c1c240006045200000c01c125101410700d40001086065401d904085903009175110810b200b65104000403440e0020b41241e120003201c02d09000c0b03c4028041c00c0460303070000010a07419081c0f0001519181e481c28070035000f02190b0300e40d100c0c0300f98820800044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911013723 1250 911012473 911012477
    0x12280b0616031224091107020607030921060b010914060a0c080f1e0705030708031f0305010f0f06050a05190803030709061b0b16020f011b0306050105031006 69
    0x10041071a080b034048907055400d85026052000b00c45003c4010821400384e0301420040508031960703001044107603003c04a032214000c07000d200c00000b40c104036008048291003864040e0101c0d0325610000280c2107007408a40300c4041001011040145078842d1174502c031001d0800c00d2906240c1902511520b0401180310b000d00d10204080d40060300a098644d08142d00015460f10341c1e00c44580d104054000e1900d0406540c9000d038a001984020f004590306640c0040c09186022002d40383e80e6507035480504911081e0122080813a07011089083c0a03015620607800442d00c007100400400070344000b0800507140501d00b070b1082059580d01c070b05d508125507082d2601002081e00180c0602c1c0c41d0015070102c0d855000000401001c40d9000300500183c2d00e2070b80700c6000124070120800710454800c3d40040100f1141004540c0c103005010750500c401344a841203c02c0440d020070041d00b91181c040c003c40e404040009180e6015405003c3c0e24054002032a0660451400c4805121a59464414801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911014973 1250 911013723 911013757
    0x3140412030b0d0218040c060507200a1d071d010504050d02030304050d0b16050405030a02040f06210c080a030203030a090302240a0c030203010f05120312280b06 71
    0x1929444600c0800d01e01d6030002d01500002c134943c5c0304859940c2c4103c40445c3c90095a00f4007107091406641a2020b00e6040705a4181240080800441d0b181a900b0003e81c4542c1950000924842c40f0080040034050380b40c201e00c241c03c04e1100a010100302c0d2403601100c10a8a10800d079690740301090344c00703c0b40b04844541e810580740c00482d0551050b9040560400f1600c0c000c4003d11402c504814000d44071642400202c80110780103e410f80101d005281d810f030880b502c0000549013a820032803415000031000101a96140141d0144920710038210007418070509007842404038014402c03004000318809458140d6041e43c00035240c1c44000c1c0001102e554480c02c02060600c200b2008020208440c041c2424402d16601120004000c0350500e16542c100038140854611900a490407a10010f840d400c0b458280801c101c085070a50f00e030354110b4841480003840c0b80042c011124042c050140740d070b03c40c1072085070300301c4c07501d2400d812072030180c50a20f0070b4a5074035116482240e28081d000c0031001c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911016223 1250 911014973 911014991
    0x30c1416060912210614060904110417100c09030b0a0221040506061f030e12070f0213090f08070206120c090a080c030703060b0111010c0305070314041203 68
    0x1400510302d4120142c8900200100380e0031207900718150114988441078100b11004c8601000301c15101d05c0e02a61081243c3c00042880a0130020f02510711400020700100b0b0150b290030052800390170903480344010124400074a00c1c500030502050750011046032040c42840c03c12600a092440e05110091a101b111000a031111005606139000404040114403201da07240d0712524071a901900c060303406d40a441c0124409140601c0000540001c0c000c0025481400010641c0186101040c84c2407038055251131007112481c202c006d00c00325119408401249005005001800c4012101090b91614020900001c10440c0e125500071940c030480c195600c03401440070411a008145c03507071200185c500203010301a400c0c140940714440d801da5849281558800c0440e40d66a016072240360175030002581400850920741028900b10b006052482c107004009008900b102e07554802000008c1e03690090090243c0c1c10301584501008800800c1c1d004d090603129450800003400c1d0003400e0513a00d640c80303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911017473 1250 911016223 911016233
    0x11040e07151d010e13020711040e03030403021b041517070f0807090209040b03011a030111040e13060b030f0307030e0108160806040f060b040f150f031e1b030c1416 72
    0x1580f66170a40c010954540d0ba9901d440d658071032022100520070760600200000403200007041d02e110310381590044c0070000d050500c1014001001c503400743c0090311649003d1060440248141c02443d080819800c0c85400102c00341c148031154209115904180004005507a80010340070140e07109100016910644d04002400801101c41e060340c05500740f80c011403403601080c0300c0009001d0706400030f0045041c050440c036154030403800303480c45000d4144040340f900c00440840d1030419114140015030b4400002c002450104203200a0482d58000203a8604040e0b00ca161125200400e0900c03001506002c1030361081040102103000030800c0003800500300380d449810203a05485650390412145498a2282c0b0040c2d01500606000c0c0c000712070006484140101c00821202c0c507641c2c0c080c0201c0f00c42a0407009441850001d07007a0718640114a0721a16540c0b18084040c1603d80c08454001454400038064038201c0e5a50f0303041c008210030041050651000321501010911105080c0712818500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911018723 1250 911017473 911017489
    0xe10050d1e0b0307050a3017130f0609061d04050c0d0510050a030f11060d020301091d0303070f140a0206071b0f06020711040e07151d010e 61
    0x404804901d99280c18030748500281d1100520340e900b030302a42c1302103480d41c05205030401203100d0300701c031110141007400c0c00103800031a01080d4036121150a800c0d00b034076101c400421031500c000304401240001e2055215100368820001001000c81040e02035180c09400381c08400c1034403510703050115040c3c090740d0802480e01034012981c0010010440c1c2d04080303240d00b040b900724040c0c000300381c5c0c41c2401180c051140048000700300c88005090500c51401c641d0f03514545900c091040700c04e07007100c0c1c1c1c0c082010380e210805011003541040c8016200d43c5001e03640e10540d0703103e046042841d80c110100c1044240d001c0100c9034020610b003401017203a0301040040b02e00301c5201c4e00212207254080740400340d07140e000c02d00383d0040c41c00b0341d41e04500e035049040418540c2c004010046c407480000170013400040d9160041d01940c1e01030542a00e10b040454007142c2540d0004100004c3c40d04603100034401d241c1462410701c1008407501d44490398210340c04155903100004c1241906222106880c00b0640e942c030b4403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911019973 1250 911018723 911018741
    0x308040f020f10020d170f01120201020a050a0809090601051e0c0a020a03050706110609071a040e09070609060c0c0306050c040f091b0c030c03030b0402130e06100e10050d 75
    0xf1181d039071075203600094030344200c210705a00040c4200c0c50307200a0001d9101541c00b442d502c02c00c0300e10507460a60001903085035900102d055000b6021050080307041031022212690155262a0f6180184003c002981038000c0240307040c81010310540b4204103000321041c81c1054145650382d41c07011f03001401d07868500c0c070f81c4000b036000e8044480403040100201d002c104071151512424a400d0030b08aa86494540407241d801d0554800c1204014010310944160b40035407601c04802d151544442160300e2007a401c481621035a03110800c100441c6074003500c003000920f003e24103114514035030344d15061402d005100140c03003192200c000c10030038243c00017158000c08074070b40134011080c3c0c0c03a0b82c00030280080c91141d4078090780030f0410296403400fa0840082c61540344c0c4d280c0840349900d98007600100341e0511101d8005509100345040d407500946641c000c3c010444a40d00da86c9003030000c001c000000c240c1c040c0200100e411201429840d00034103203c42c0d0500382081b0703442b2914130344900028210b43c0c1e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911021223 1250 911019973 911019979
    0xa081506120d030b10080402280906062006070c02060c011d0d03050702070b120a0908040f03060b040e0705010c050c2e0804051e0a050604230105040308040f020f 71
    0x1038400c4920f8059201800c501810789400c4051228080c0c01e4401035401ca40207500f100130984c0003040700b40c60785248603c1c1c540105112213410344803007454017290710175003140c004140c40e20704455682e1305140304101c101342000003c4c011413030403440092408403d0b0000901950b004500420109400e402510291041110062006104000441e52949003450303c4012a240c20701043c030140c07003c00c003002a100d48150891401074204900510a0702c0149442c031400c0d602e02000c000a500328006000900340da240e10764801d070444c14040300b1503050889680c8100e10b403003a01e0705030b0540860301d030f02191000d0801c000c003a04207003441410410100c2125034080c0d00000d8401400d0b800180d83c0040e00744045100701c440e00051000d07200315200307a4000d4800c3d403141450744040000f4030840d0086022400035a840c580099940c00e2a14500350350807a041d0900c001081c1d440300074070380c0d1450080c000d41c000f88070604080c0c130054001c0c42c3c06071014051301b40e80c0e1180700c01d41d1503150000c07800c89006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911022473 1250 911021223 911021233
    0x1c0f0c06061802280806120a050d120f02190f12090516050105130e0c16111014040302190312020f0c0a1a0a020109120309030207050a08150612 63
    0x60450070001d40c084c1c0584d40118100342c0d4003003d03921850302c91a1002c45152517418403511484104400f0350b600b480302c45050b00c81d607032a044c0024014404036103101003030345034048c0c1c6040100c442025104608071f5001400d206200e1040440011110026620f0803402c20030100c2040e4201100d041c091450461410b0b414454524104507002507444c5400100506a901107a11800111480e114048440c089540440420721030500003580103a003050035a0903883c41c25960982840404c42001c1d0140c03040c0040c00002c07501400c00514900d490f54042c90203412001f040340e101402d5000c1c1e4000070b40106841084500d8800c0f030856210f0141d40c101c16660103220350518001c0da521299101c100e40360058111240340c0d403c204c1c0d20380080c0c4026030135001d50040d955000c8000fa401041d41d060031036488030b0304800401c060315a0800e80040b2980c012501d29511309003c3e25007061607129600403146c0344020000c042c00131610110b84000e022020502c0e85403c000901c0c00d54043d40030160038011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911023723 1250 911022473 911022509
    0xa0e090a180204090501061208130e060607240f0e01060f0303020616120e0105090c01050906070f08160c06080c0a12180c090f061d07080a060801090b0403021c0f0c0606 74
    0x1c20f402600c0100303500180c0ad907049855040d07001120324191495a0000e0043c010303007000800700400300300c2c00800010359542e1f035100406400d05a4484800c20182a95144849030025600380030f40c0001d02290b01a070803002d455a40c00944e40c031002001d200c1942c501c9100d07031039807521960a03000c0d109808181400745c51307480c0401a000304020396020b9000e20a86607034610950080301503585282c1c00074150b6052440f10340780c01c5656100720310308440c005c1040200c03071031071401c0440d8444118014420040b903a403c259000c0c02c505005400d09000d03080912106a40c15409008074008281140d00811640848000340920310300da80300c003c5c00e41c48292030204000e0015071000d10003104030303042030104a81d60047c02c4400e90750441c500b8003a810000005102502401d40c25400100190000400c140c1d10b00c01503003103a02140d01203a01c07a250200313100c141070f81048030000c1e00448244203c0500c003c0c10340508200c0b00003400406101c460312010041c071865a0200e4000d10501401c5192000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911024973 1250 911023723 911023733
    0x18030a080910050405030a0309030e040e01090b010b090604061d030a110102161a1b0a0b331003140f04050115080606060319020a0e090a1802040905010612 68
    0x80d04441d003064074030a80381c801003680741d14002c80c0c1c00ba9402c440510301e01100e0900440250000500542c107110034103070f405000d502c80c0c0c0b0a00b002c40e60f126000041940d52464050390340c2e003042c0e000c000c09440500011686950fa00101d900b107409505120146800080035098600907c00086515000c0d000400c0e00788051140c0707509920009900707460341c01615003410800c241c1c5030300900002c0030001c4044480502e0120040c10300c00285009100d0110042940515010060104444108080040c0810000d1401c6075841072202c2d1501080414608118004038500122900d4451a8041c10681019000358015500504010185041c51a04049081d48004150b808036259841c00040c2c0c409410070516000598040308050071590301c4042c1008000c0d04060250300c2d4440c5500c0c0c02c00500191840201000c1406403501d400700c5856008024110100805a00c07245041860842c0060500a05124400d2b4100c8000503100301906041340140096000050915448806201800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911026223 1250 911024973 911024987
    0x50913031b240b090601300b19030c0509040519140706091712030a0c1218020109080601080a06052203020f101b050c12161104020c1518030a 62
    0x118043e2418891030f01c50071700440d003c16480d0701960b4826051a42c0036041d10014003180381502c0d0100700070410f84030071b8000a03491b807030b00c510b04292144200010402c01400e101000c004060031945d138611488c181e10380ca07449032410b52247c1d5911686072a03207000c015644030641c252183b0a030032220503903160b08021b00202d103903008500c894509619250044200001c0d000c11552102600c1425500e81084401c060f01c9180300c400d052240f64070b0382030072a5001d0310032130402800381e895426011405000140c0f0814480d0060b80480d01b1010041c0009100050304242455201c0c01c001600e03070302d0680c0b2101100900e40b504001c400d9000d1608240755000560040c3c010080b01529240c61000580304126662076224214500c011520720b40701500400190000c05d010405a074000001082840c9980c0d100c80f461810b0003d030462001d09001e0080b00801e5500c10681c1c00314902494907c040e40d032001c0c44655030055a900d070b40045c03848050301d1411005201d80300100c0b500c500d40d15502800b08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911027473 1250 911026223 911026241
    0x2802100203190b030f0a02010c05030903160512011401060e061c1b02150115110114100f050f04050408070f050114061906120e0a0c050913031b24 64
    0x2c1e400c0215018041c50007240c0d5200c040d04d004010010b0500d590b0064940051400e010b4030719000a00c442500c40e04c040c0107804003094800681036500c0e0801c020012002d2440403180407907898612003070390691090600506440803070030407014040300c8500240652141c841110044008072011141580641d00b00d80c01c40e4680052450950380303100001c90741c0c3c0045207280050b0005110040210003000c10010a89606614001050108070001c16003922140c030000d00c003100c0c3e12820000101c40f0b0384424000b4220300182085298a80030024017415407001d90780f84580c2c1d030b800110f010440430104640d81d80e40d0001010b42c0600060601c40e00a106044049062401072000921149803140d00784001c5441034042401803828500c0448401c6cac40c405c84030245a80d02d0707480c5440b0903030800c410400c0601c588600d00e84181420b06000c40b0000290066442e040d50740004c0c00000e800001340300030024444d104040b4007516042502c14a268464034520b10103003005120518011078100c4948 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911028723 1250 911027473 911027521
    0xa030803010906171002030a0e1b030717030919080609070f0f050d03030504020402211009050108030f07020301090609030806040c05041208160b0c0c010f022802100203 74
    0x1d565030b209400013001800a4140316400103c01040d6044090303004c6c541001515400040448409500380e20b000450340c0e24181c0e0747c0c000900d1400c540390030800c580c00307040050041400d03801c1030514680d980c09203801c0030f44a5007003610360028005150014a00a11002084078120700700911055100e02181c041c0c030400106240c4089100c581d004c11b01d008580020707040c11507100958604a000f408042c00c205d9019030204041d4031602900f1001d0381e019000d5540c040031030704040401440c2d1074042d070b0100311460308203801000000f00100643e00c0c1c00c044041090355507003480c400240101000000104864a8106c2c10360605a04c1010b10b40b00c0c1405640c20480021518001c3c0c50a024038421303070f5400d0b08194150800259060080c0c09170202082e440025075082da40c0e00a15030004131881c1064070700c0455403483d540400d018000302c0320a40c3c80c00714036280f0240341c1400d030144405e0413104c40f135070400d07a01d1003281c0c0300700004815040e03106411134403030508081004480d2090f542c0415 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911029973 1250 911028723 911028731
    0x30e03240a050615040501030f2c01050f04020d0321020a030b1c1104020702060d020a0c0323091e0d050304050a0902130e070207171533040207020a0308030109 70
    0x1449044c4544044040480301d00000d042c50724000044002e4101d210491061303d4803070412148080520080349190302030a49996421060712030000e0031124014140e9032582040002d0001584900c4003d1882139018540307412204904100b03c001e80300700c1580034004074400108407903c10303490342c029500b031740d0101d0717110b504491320b1004c8900f98035a200f00907140c0c092080e104030080c5026402482150301c060501410062940104802ca03045404540c0105142c90703004000c265001c1b51a518180714103048500c40b240002056641e400b444800c940640125504c90102c1803500f040c41d20302d600001c108020a50f02450034603100e070424031840380980e05550b800b00c1d00f48014020744010541e1021440700e8603152038402103a10030042e1031201580a203c4001c602c80c405403c04507030211804004100d813246d0b00c2c02103041e02e88024440c441c269080d0200c0f903481011010300303051042442c0c282509035a40140002c00920a4880007584141d5807c0d00000b04103264016604807140304100704 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911031223 1250 911029973 911029981
    0xa11030a0309150e030703050709150e040f0602090d11150c031801030209181f0501120903030b030a06050f0108060c040306050c040905130b07020f0307030e03240a05 73
    0x59403a034103200c0040110780c0c0e280301032064141c85041c501c074000d01c610300820622130708400700b424943c241c5c009403140d401c01d0805108456943c0940322807559a1001035407010b10f440140740c4244000340006150581880c00d00d01070002c03a405403440c9120041018901a0052030701031130412010180c1c902071290048640320440141040d00c482d44043c0014514100070455522000941e8450482c185030f400d20201e099900c0c0c1c22030006070b03210b48107001c00d40f40c280781d06021a00703c29a1304083c4030310042e0f030023030116036800145255107958004012414681c14541034001d406004c10311a014425100d00c2401e0140d00d803c01030048000b0705c441c1710b4592b2600002501c5020403038100d25a01c0041100708005800c1d50300c6658400c401c50421030500d034075029100292407080c1c68191001e5142a030390001d00012880141e00003c1c2070008081003021079641680304c0c01160409002d00c0b404515031161500e06000681c0b502d80e0403000300000718070301308003200400c2090320110072803441d02c4005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911032473 1250 911031223 911031229
    0xe0a03020d0207050f0105031e070804030e1c0308090109060c0518031b1306050307030309410a05030303070512010824151203030a140f0103060b01051303050a11 71
    0x160f01600c002030180c40300d9102e0400151080d82c80500302e60714004640410074800740581407920b02079440383d51440007034181818010100800400752520480d01e54100c84051081800350600282d07040c01c00070000d40e0343d038806e2030040490000181a035414808100d510329448001482100c43c2c00b80e04000c0b034046141850780d0380464514409203c0e001c001600d07601c0ca000030b07241150009060010a400c0c1d11074000c20700b001c003241e00840204001c40b0b003e2151400c010080c22003800062822884008169500c18036845130380c4405a4000300c0510a114a440300005000904000b8045a540e402c1c00d443c000e049900c400080c52081d0300340000821070240c081002d250107442c1141c20f03080100c904c00c5031007201d1005008410450031024400c609504e82d034041811a001d054003541c1c1f40c1c9449004801981c80000b07111144036505d50070403400d42500c18410b03043d690030400002d00f8046500c0143e401e4821448665071090083c3c0703000080200008412500d00d100d144d42410241c001c0080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911033723 1250 911032473 911032483
    0xe041112010303081329071d04021804090c050907090b0a39050c01020c0a030803130f0b01090b06030f0f041b0314011803021b0604090e0a03020d02 65
    0x903803185808650041021a10902d040d68210b29a00c20080c0c0301105540d8620401d9801205850000c42c1210480c0800c29128800c5902480d00e00b0708002940400b11030205e10071212010500c284c0d03010030001c00702030700c1c0000e4507a02d00b0041d00070010f400ca6824070001000641c402c6c0ca00c46c0c900c04001541302d6101d00c0b5030b0000c07141c440040c2d50030f00c510010182d5030000c00400040000403090050503c07013103205a584180d60746007000c0c18596100d0b05041c2d0808034110001810b41d845806058566150309904204580d004401192170f40c6507a00c114911003440c00740a4241903074042e290341400180302c1440d04813401002c0c00c02c0700500c8141445024041119a09045060107000030520616900520b51146c4201c1c4202c03802040c410941004040070340054483c824000714000c8400800d100f08503012074104e80d00621076505583c02540c03070030a101501c8c001100c1e05140c02083d19a402907801600e85c05c0801c1c094036148804665a85802c82e0042c0c0c010310501d40c50460140c00452 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911034973 1250 911033723 911033737
    0xc060f240603020a1b08090a140112150603110c06070f020607030504020d140c03030c0d170405030f0f0403020303161b03050606270f010501231c0e0d0e0411 69
    0x5034418885c4020a0000301141e6002c000d4540745801c003c0001d03e80c0c0c0324110b400c040c1c0b803036000420303001c80200d00041200d22000030501031a890440d4400c00c070002000c800701243c94924001c5440303900c56094a02d1030144840d160b040c1e10583d0244200182c00140c0e044021420780d08485a80d503401c43c00300c0c2612415507000c0c0d0020f07001d09140d00402c4d03007824600300c0e580b9440101c0303100d80034040c040303881c0da8407803807110801d6007007aa51101c001e5400350b10030340c0791a040107000d42142082e03240c90740c40784200c1c0c11a80c000d141c006209540501c40b032041c0c4000f1500101980c0d1145403494420b4003150080380200c0320540a82c4518100410103c005400d80b50800700401c3d990b0340e10b04c2400407a18500c407245152143c1407291841c400c42000280348944210034058001c1d52600001421b100020481983c0a04802e8818103109500340d080d260107103410b54030202d058194021990090106441500c001d00642021405440e080403504249002c141d804008400c200030400803140a094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911036223 1250 911034973 911034977
    0x30903150f0106030207140a0309290d02070f0c0315060b0711010f050f1303140a08030420030102030907051c02030304050f010311030114091608070c060f240603020a 73
    0x1801401d201754003512160340f280040728525001560020710b0708081030b2088001542100083c0140d030f0700c404c00098003000111111501c4844200b0340251401100d8040700c803250301240c0b044c01c0c001035400001141e6003003080f04403101c0c0c1f2400c00c14094889148818240d6080c810300146144001381143c1309242c20954044841c20104011a015001c15841408202041c0600034006020f20024078541c403074410741c05402442c5180141340c4a003c00d0110707945030000c4030345a020509240859510981c45002000780e40c3c004c04c201d00700011680504c81e0190720100c200410a84001401401d4400480b000c0c800840352003450612901d01c0c290094042e0070900042002d800c2c070a032100d1000105050221307600c0e5400b001142e0706d0708240d120301c400e55007003225118681811955180c01010781c50b4140c06200030140090942c1c54050b0040c4200007518441c0f2040c800c05501007003407280003810501203900408140140c0340c0f00c0c004410351a040103080024a00d00910840301e64003455 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911037473 1250 911036223 911036251
    0x60f08100507020304050a060201020403110402160b0a114306021312150b0636040c0306030c0e010f05100210060e0a1a010e04020a030f0e03090315 65
    0xd40c032010140402514070320540c0b105010105a03907070303180802006043c9681c00181c89a00e581080040f040c42d50030003902480c0b040007030fa244044100030702004e007900200100c800d03803a940d41003401012181ca901c82c03081800700c2d0b8955142826195215003504d500b6135804c07456881d4220342032544c03844c0d041d181d09201c041018000184160050310a0062080c9040710080e61803149c03141d8201c0d0f0440c1101c84444a6215440e071817113910921b642c0301c2d415150b0b80d04001604030481e110030381500440306440c4408020b607003004e070403120035288000050401c0c00034020400014018001c180070484c0c0c00740706000041610b03003000391114120343c1d45400480e02c176031400c0d06020071000c6039075828045000300703841084e505031980500e0005021484c0010a03510785a07000340200c58201c1c00781007075000c1c00503043e00b103030781e200006000032503044070010b0303035103012000c190010040c45c003200594500b4032030011503816000c00600031203841a0180c4008605c1c1c15056035410348110384e203103030f10b8401e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911038723 1250 911037473 911037493
    0x1230a0b0c1624020a0b0103031707080705090f04151511030304050d03110f0406020c0406081b01030b0f0901080d200a120302040b1b01060506090d020d17030c070303060f08 76
    0x21500f404280d42c00140184d07107442c1c03102d4444a82d0090300b41c00aa0208501a524110403a9400c00300ca0740030b10b00d89000030131030404050080c29403080c00d480d41e00c11119030018140d25032361075100c0c02e6543d850300341940045549448080d42c010402c1041004500d000d103811410940c04402c43e0703c035a40c441d002d130a401440c0c5030150001c00344609160150003080c00f220304500c00c808014805003515800070f1801d5082c0c1420042514807503001807081e50001d8460b2401e4a20040c905200301c03030309082c049400142100800d091402e17801031a5407090039100001003507840880da41071013800f2641c0d0310414101740903c441280c00f00c0c0d03900e50001d40c0413010080101340041c3c0c021050010518001d07150941d03400b50001d03c1c0d0040e82c0c0d45116520050100410710308244100001894262849030408854900003060203809a10290168141c00307046010015100400150501500c503003548a0a0002c040e240580140780b0440100340341050204060711142c0e6640d0480d00d004e4018003450303076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911039973 1250 911038723 911038769
    0x90106140616080f030a3242040b030a1e020607030305060108091f02091512041401140103060213030507080c0a140901230a0b0c16 58
    0x4806420300b911603069400c080000b80341403000300259001e85a4454aa0a12808001c00c44030f0016040b4000450182e0128510300d02c94607149000d1506643c1d509141d588850340100c20241d1502c800c4100b4a159240350012002c110340390324103481c10a000000850700702880704540110784000d034150f118272040c030000350414a61140e1404d00d001d455015070300c0d80d0b000c543c0c1c0350422041100840e031240d040254550340141015804001c0d04000e11401102520b84a10104510014810f142e00015024020f03281e001e00340b0402c024030003590756204d410360300400d040c940a8400311046040c6500c2d1482c03071720050080f40003140170110117800036482d540c1c0302030095010791105510041118000804240e090020200a11106c13010301034100400c4200b0004414541104d0555141c3d000104c50b0398544070041415a07100c5690310380c80300900303480300411010f1008101d034010083d100104c3c8640845002e41174805030241200c0011f1890054900100054000da40c80c240c22203c441c0341c0382c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911041223 1250 911039973 911039977
    0x90d0c1d060a0f150302210f1302060d18020a0f0806090f0303010605030a15060809120c0613051f0204150206060d0b0604060503010e0a050c0925050f070f0201080901061406 76
    0x20b884c0d040051800550050740841c0c50754032000c0c58415540303681045044100c600c0415400740005a4403a600380b06c3e139000a4250203420448255a43d690003503812848000079a0030003030350018540303180c0c1540c035540108190310368060300c8224003442021030744079a00011800c540c6030120707010354150780c20940c2c1159160401010680015103400c2d6010025800c00c6644019250b00d17514814035251119165260410021400101030001c100310401020081140d03a00000340c4c2c1020100480c017400c00703914200500c2c20402e00300041c0c0c044902e03044850744c0104225010701f03024031035000c20020103a8a401c0100d03901174120b442c551505000401000d1155407040d40104001921a260340210742100d940c00000801c5902c00b50400d401c0c44010844000c20301401c071a80b500e14270b4100b191910310b0003840300d04080050259800009170f4041c500751111025159070032601eaa6480c1460003c1c4080d03000260f000c210003001040050206018140640c4c1140c0c400040201e14030081c4000c2d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911042473 1250 911041223 911041259
    0xc0608042f04020a1e140301180905100b010f09350d0c020f0607080d020f040302120c0910080a140102040f1d010501091406090d0c1d060a0f 62
    0x1d98140340d0a000e640e8891014040f03c0240b07641d41e50303844406002001141074841c03c0c6a060058400f000720f00030782c00304200c9040d1804010389042003101402460041c02015800806600556a004d199150980d01c0b00c904c180090365651002800c00c0419103142d0114051100c41b681031204d02c1e007440d14400b140d002411340f8010700c40701c1305110285044c2050300342024a030005d0300216409007545480c5440918441080f28040d161600d55507602e00e080c420b60303144046064021400001c1d0040c00c0c000c2d40c2c000c58018050b0598034182d4801c0c141c80740b0001030309520800445010802c0c0310300340070610080e20624401401030880365156403980103850b030300f030090543d02004080398040300440001d000b020301442017100381d243c80a98440411051300b10342d041140188013041250b42e020f0010f103a8400690341e1a90300c00c400d0022905c0c0d6600101e0151149505000005038025901440c80f80f4200a1030b00550507161a42041005151841906d0f01518001001e0080105003040304e050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911043723 1250 911042473 911042543
    0xf010807020a080a0f0305060a050922080a090303120e060c0c1c030b0310050402011403370e070302090406110d0908070308011e0b0c1906090c060804 66
    0xc18030b5940c041440c2d11084071180042c115061071517080390540112600070408a420702c180c507040801041090400503e0107040711902215850f481d6a00042400c102d0f4014060b035076540c01500c4041e001d00704501c021800174070f40161400441e61a407081c1e01100310b408010f040281c40d41c01c50100319400c00c100d000c4990264285004800c00c0d201681d150081a98801141c060608001c26050558000d50040064101400c000060381d011145404030341d826020f8035180d46440910101e004225040e00f002c00300c0450900c41c0106c0445030a11180c020302c0001c0c030a841000d0940f6803902c000e48070007500045c5d000702082c00584241c02000895114640031414003e000c01618280c2d02d81e1a0156840c010000d07481d018158803c02943c050442c0c21b0035407000ea200600440d10040c42842201c01d14017000c103907680b05400c10b010303414000c80c0c52031072101703a144075003000c20040030b840313008803501810000300055a6001d0070132540300d030b5004820207525142c001c8250703d01d40b0a40403a800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911044973 1250 911043723 911043733
    0x1303030c2601080c010203031e040f05100906150305060a0504050109020a14153118060e0a110f03072f0c0f0303070204090c050d050318010804020f01080702 69
    0x4040c0c09080c11812100c50301c401d00c0c02640d40360031101420302c00040781040c11508100f04003d004c000c124141e8048115582d8a05450751703a1b41441c2021340c0d14558002c0550151698032140b803100c0c2c1e00b080c03440e6401341c01d00b044a42c440d40c0c00c100c4003c456210041564001000003003a11111342e2109900c40d00480c00414200c2096000034410b250303d401c13503c2003d6038030b903003004142020540c3ca901c2d443c00070700c514600f050403400f5584ad480c504180081c40c104a84851a00d00c2d801c0001c1300c010711105d100444e082c01c2c3d0492000191089000c0c0b440078040f9680003600088c00c0740078030302080c04550240307450300c01c0d08003170b0321043d500c000c0c0280140b210100071000c07000400c0000c01400140c1169865160b00c07680946810081c000d889148224118100601c0a950210031180c0f9964111400030300c06030f40c3e1070403044102d0660700032640003441c502c4607414403030040010006004400e241901810740ba400640b0b41030b6007541d019410400d4500400c0070755014104c0590000b00500440d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911046223 1250 911044973 911044997
    0x516020402031e0a06050d0b040f0803010b040512070608241f0f0e06040b0714120c07090603030509040c050909180f06013507090504020f06031303030c 67
    0x16060340d02c2a190302d080c4805a14803028440ca0400c4155007103102c01500340903075413030980040c0e00135181e0007015066076150340106080000e50700c2c64150140d0300440a039101e680d5082100895082480fa880c09038400d5215070b41c2005000c2070a07001d651060310b030800d42c2e03114081d4005580d10704c0307142c8020341c886521400c04595110044030b00c0c8102e4401c051000c50708481401420a840319491500380600c1c020005901c0d0350300404d03101580d0a00ea009a1a00760608044110000340514003496016242c7e020010203c400b0060a8a240080c1100d2440f0356681100c0c0440302d0320310002d40024014408445680360a82005035400600d03d042c40c2441d02c12400615420303001e550104400110703209080c4164428000600c43d12b18040140c0030641c5004d29603110309030003840d9101c000ea140ca03009080000f410b0112640103140b0021119aa611000c244000b403a055400342d1151103a203441070b407d46460f00849219590746044110440d00f03c3d0b03030903000352001c1e005100a20509040c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911047473 1250 911046223 911046229
    0x102040b1608130821030f190b1e010201060b0f03040609080910030f0e0f0604060c020703050604050d08150f011121180d2013020301030605060109051c03051602 71
    0x10001d40313061009401a020902d407115071194107080d464084e42c3d4140204040c1000c0881c1ca03d5000b10207081c540100101d0350a02d00c0203004502c020707030b8002d500322036080c402e11b05c00d1080301807034600380c000300710340c90300e5800f115014012144005081c040c00c00c005000034066411503010584241a0a400c0c05424000980b142c0411014100041d42e42c140c032185540c44e600604400030004005400e40c542101c04084d16060014009881c064468145401c407a10270000080255003140070b8842070304040c540941c88503e4400751200280c0081d01148a1702c07101003ca0881000003040007038210b64660054030114441c40c928a00d41c080c1c81c4007080300d003010006045018050305d071016500d000d42c1c1200b01100f00540c05460158454100c003000040c000d4031102c03d002c68041d601040c907080c00000807403080c010030b0195002800400000100410b07a0482d0707010700826200d503d04280c4030000d00408450b00c00480da101302d60b030800780001ca805840103241d090a202070f2441444015004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911048723 1250 911047473 911047507
    0x2120c09040618022205030717030d0612050705180718090213080105150603180a080711100806010915050c0a050c090c030907050906060d050709060e030102040b1608 73
    0x1a201c0320b13070001408041846040004007505030b504401c41000380c10140400d5640500e40242c3c0c000031444d22111065134005c0007901c0038030103075480c00d000c15500c840d40507204da018080102c84510030410045580e192034611410800d010902c91030f06550f9403502100d6620650015412460005902233900413490004201c46544000300d024404d1034002da2500712400144234665500146100940c00d03580c05041b41d402044100b80c8070307994590280c507103090021404008154a0001a0540c01c014541046039851142114208000c680d4841c05072107110003140c4031030014500210601505410b00c444402001440c44d101e408e01c00200007003450060031020658180e80300c1446120145004c6081a40c4103000c03006441c194181f2001c0c1c10341c1d81e4481d004862041c00a1400241c860704c3c0c00081e40c030400f0005030103001c6818503807006801e03c0400e0107400300051400300140c5680c1014000c031070444503500e0900d1724290b91591038840c109040d01040310540010400701da0000351620f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911049973 1250 911048723 911048759
    0x11060103050303072c060a170403080f221203140903040906061d060a030b04050f2505120402010e100206060a0501090b0a120e070f030b070302120c090406 68
    0x11a52130608040140c00c0010f1303841000340001502d48101c603211003008992105100c10303911035441e02403d5100781c1e4002207100078842000e041c28104414941c0c00f4840c1d0740503e190f00d0b64446103807581048000d480c9107480c01d541c0c02d4004100401c0018000030321240c0810142e140000340702044509200400b04150388041a43c0e0000c079060007801158401d940c000d15860030800c12491403004858080040040c107148200300c0812200456802a0441c420400d0001e000304028586641c070140d42e07650070344001d0003200004040c094081c004001d00d4081308545d807940c0d401c02801d01d0004581080040c0300320304012061050300080d40b15682c841d02000b8458029101500c3c04d1428001039036105e0340018108121349500308219031150b030458049103102e1400c541c51b400742c000000040d0070740b10700001803403140340300000b19503071404208802d80344180003c0031184c4032048110b09030f0040c003da46580e40c0d42c42012600b00c800900c01005580405880444d10940e40d5409417007485600c0c3d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911051223 1250 911049973 911049983
    0x6030203100e090d0c170301060c0b0708010501121a0409080a020f0c1302090d0510020a091d0609090c0d0c1707030308060f030102040b030c0a11030f091011060103 72
    0x20050181180240305070310007400c0c246504019901d0090545595007040d20141014055032406060a02a20010026080726a075072101e980b5607546000600708010302c40b056545da0703d00c41c04211003a2207045054100c4005a40c1e04101044074103100c0c00900b182c0842142008030081d0071100c07502c07140134824645009001d50307030716131400050282c02c14000800401a58102c42130060076a52031440030100003148400051315020490041130b10b010290001424038402c140a000c01c0600503002001c8110003030b56880b021b103540c0c06a00c03480c9000607070079850b01d00312040000c2d07090815522481e4031402c424121000980d402000c60a00d08801409403000c0c1313036681041c4a420303440c11403c0111110040200361062035a10300910081000d42064442d0780742c1c0500c000546d40940540d009485800c06142d13036030411034510707801ca80c0003002400c0800c00e02c031000414440c000c010342d100c1003e0340404500d0641440100401004003d9250f8180140e54151401c800c0c420860740d4040d51182c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911052473 1250 911051223 911051227
    0x80601030f12020f0a080a0c0f0b010618050d03030207050709110a092309090703211b0b06010c150203040327060c0b100315290105092206060302 64
    0xc0c18804060650a4204000c3d9400420005240080012a0440b40c1d810502031078942107045d0f0203c0d0803642c6454040c10a012400c44c10040c0080704000303e0480390301d51103201d0414a80160820008494410035030b00c00403c0d010040400c3c002d0b0001c0c20024401d40aa41c440c5886100c6501100c43c03207940c400e1460320101c4c1d089403664204009801400102902c0c8960100c000445c0c503403118a8000e260041440780d0204041c21400c011010213158008001a249228110180070a00b0350303041103000610341d80e0345c005172414600792940b0745d203822070343e01d240990340c0100640300710701e00da02c04031403440c1c0e004a02914124580f0165006034403c0eaa0801e1001d01c01600d8602890b90800d013120302000284100541078201902c4110250300911103807242d955031100e80f0390b05075107520203410051640140c114007840f81d4810003c4a60400104950100c030003035030a048c43c1450304039808914100a046510b280101e800c40c21440710700d190076582020b001a6105903182940040042a00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911053723 1250 911052473 911052503
    0xc0313170610140f010201021b01020702100c020102031e090a1202040f050c250206041d0a0c270b041409150f090703020c060f090d14040603020a020708060103 70
    0x10310220b6000080c0c10b400b030300014102442000008942d4441c1c52080070200d014403c1c40c4d000f03405541c04045841c8503088005680c100081c082e50241000300d114101070615900201e008d9503030303a02c01b548c06034020744c02c00310f085815038038110300c05404815010b004e1107590703501c0c1d5403088408003510301d0103007100c0072103c50300c10700c4151210f28406004060500301040f4840300c41400341c50800d00e202d80c200c01005417a03038500e05a075840c0388000e9000340c80045c02151900c401d4911500f06081241c0d800c0c003035900c00303c1500c12684529103640001d844d401c2c240b000d04010030440100409220802c020140d0745070a516215070203a03202a800400205050480e03182c40349869a029000384010b18107031031540009007140c20022015486044600042900c1c20702c00d505648502d64580204c0341941404d00500100c6101207a07807001d14030440340e41d011310314410400320414948600d803160915040c0f0308190043e42200c8003c1c42103128064001428850801c02c65000f18054012580c200328 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911054973 1250 911053723 911053769
    0x140a0c080609060412050702040209090a0507020f120a0e03100606120b0f0a0e1b0703080103110f0108071b0804090e0706020607050915270f0a0b0f0c0313 68
    0x40204042e849812000401000c20f0540c1038540c03c2c90444c0c90415940c100c3ea01c0090700034000d001c1c1031a0014491010041d00d00d400b60b01c1709000c0d0305580c080710000b90802c4845596440c00e1048070030b0f0294140110703c01140141003111500c035000b02500e04294000c18100100c1d045684100001a000b80300d901455044c0c0c424002251002d54120b4030f21801d00740030a00c000428803071000b982c0500000070f0030072180000c1c08005c0c605925101669080d15042c000d040d03c80a02040d0307005001d0078180e64071841c2131681140c0048068464480998408006070f0700c011080010781312110903901d1410000319410018000b1300f050120000380c00080e80c000d98900402a0010410344d40a00107101407960080e0075100c0f620403c440d500c0f0765030340184a003a0a80201c005030748103444100d10740c0c1c80712101e02403001c554080a80b5880d222400b88420018100901c0c445e00c81c08030001c10412091204610040070b26144d100110f92074402c1402c0c40010b078072404e43c840b03d401e07601c40c000503840c3e403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911056223 1250 911054973 911054983
    0x1031b0e0f0607020a0b0a1412040b060904050a1104020f220603060e0a020708040b400e060a050d0305030109061a1c140a0b0a0801051e04140a0c08 65
    0x80040d501c0c0b605107201e5074046040e209041c042c055141c8004203144010b140b04102c0c8500d142034075101c8a4440d040c0403805804940103440c02c4401c004260000345a60905550300c0d0f120b40e030804000c0190703500b140c40e00c141c40c11510300c040d50000d0302040079001042e0100020100410000c407500c8407030621008240d40c41446130894010141481230030880d801591b442241c200c42e80000043c0d030f56519141408091069611049120030003042e407086000c50042200030502140105030140c04802c0540600b0741e6200860486000c4404000d0080e20086250036034800c2025201c0000c4035264400203a0150300c03c44220000382c0c002006007c1c5036064003840c070007090002143d020202c2040c030309001a0159404403110f00d00c503403940700300310b0005821000c0d0082004140800034100700092401801107003d0003405101c0807100081d102c03605103d110300c207640101e0080c18181c0403483d28280420b018005aa60a00b85032441406c15000e008600d0050f10481030b2017076461601060174200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911057473 1250 911056223 911056249
    0x3030b030a083c0c0d0f080c0a05120907151b0b190e010515010801030803070e0a081c08070206100e1f26031806070201031b0e 56
    0x180d00a4440c881c0056420030030740d642e9000d40081c40e008000d54580110121081860182400c4458001d1001c0c1d5502203000f482c65000f040d0a41d03032030710030040e0250341003500036104000140d008400038200610401c007410803041c9524181d03140000c4100d82409902c01910009800c1c1c1001100708075a080e00c04282c0c0c07003080d086c20901c13804004882c9824400000b00c6014003a803601000181c1036800e03640c201021541040d004100102a12141034001c086c22560415014628002c00d201d40d8003500409040f250f006441510b50b03680d08104840b034109400007075410080001d808076040500b4048400d04c08090941e80300c001c00c58500c01812041c0141c200c1040d034214205201d80b0312100e850000540c0c01000c0900d415480303d42182282820706602003180008213540480d12807410b04000d40f179840209890020341c0b020140050701c034811030741035100c04605595000542d04141700508a994014100018980c08001466601c041c41030364400c00203103549516074980c509a0010440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911058723 1250 911057473 911057479
    0x60f130b0a0518010b030406021209060907050301111617030103080a080c0f09191e03060c021f1a1005090406090219081005031f0c030207080702091009150303030b 72
    0x11189500000c8070681030242c2410800000000380508c030454045521701c00302c07020092681d241c1010700ea0b440310340544141009011b03207900010649014001e03641d5041141c001c03685080204074403018400402c400884041084559017000f0080f5100610f0082d800380710741c65a0740142c44002007a46900400c0d0000c00d003004d2210400c691030003429111030384003c0d80d01a40411892099100050036548101880c007241c02c440200c560a20082d541100c2c4286418064400c00040598640c0514072800b071580070343c012610315507c034540082c2001014440d040c00b12094142c0403901100c0604003040c080384e8006514130a074185481810010071102c203045040c1012580b509040468140b084020440f44002041103018140001d00003410001d08458070b02c440e0401c1d2000807084007005200c90340c81c0031503010a4600038001c45041c59440b0702034071306d01412942040305081d4090403442c01042c680102141c25207492081d100081c80040b544415140765203001415904218123140c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911059973 1250 911058723 911058739
    0x12050c032a191a22140402031008100e190302150705070501022b05040b0c0702060904061d010f1206091a0c1c020933031006031a090103030503060f130b0a05 69
    0x40024080c801c4035082d1728080340d025a403030701c43c03a051588504160b0071404117805210110f1902810a500c80628029041c060791028401420b55182c0184004000380141c2c0100b0b40b854114500d1079000b540c44203150902e10b0828043e602c1da642260051004040e406400720b08982e00105202e0008600c0c0c00d10300c0062080d85482e03514501240400361881c000060046034060440d40e0701c00c1580e04001001d4020814160350b07a000407941c40400c0f500c1c44201010900100e040100404101c1c15244103400c002604980c03a0354190080c0300c0e41a06a4043e5240c0030076200c85603540010601401035240815143d030b00f840109a034400342010100342842c8100b141d92a5503c4000701d941040c00c0030070142c08403012050010a07030328580d000c0d002080c030000003000001c0441c4101141650314940d01081203100f07c0c84450400d07084002596444441d0f03000400000340301c1c0005540c00000600701400424800001c28545406410b40c1030350300341c64034904040e505005903844000c00303049030010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911061223 1250 911059973 911059979
    0x3031902010605090a0e070501110a0b0906042625020405091005070203040e04020f030114330102030d0504060e0703060501030530030702010612050c032a191a22 71
    0x6646807c984545070512103805a8502015018092034650036000b85008209140c0886101d80b101c2d03007202d04490b06541100c0c040700603c41305a1406610035003003100c9140c5030200e40b5402005038101c0a00a045582640440068940d405110701441100d4000c02d403282c3c50410b10700989100504510440d071040c0070811025607044030727054100790141c0702600c1e603180c0c0c00086409040748103200b414039980e02d814404036013940e0300c50080d040c20b000b840c0c803410344c40344205640d900c0e0005a01801030b80705102c0c40c0d240c0382c0310b41d100c0741e04a84200c6002070070031810394515050408039803003555010b44d10310042040c00740c00d2102254481c0c45013050074607040300d10001c26522100e1070a0551840300403000030801c074001d6000401030b0a091540300401001807401c41c1ea20010703440000d009004aa03469280c41c40c20700c0702c10f4040b068060303203070702400086014806454150301207480038203c09100024103413000c0104004401c125620156030321196240d110742050120039400181049007020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911062473 1250 911061223 911061251
    0x1c060b0f0f060c0307050d050403050f010b0a030809031e0a051005071b06111306030c0f0e101704060c0908030c060406110c0d0201020c19020f04090203031902010605090a 75
    0x903000c0070000c42d0150303110700c18851854918010301d03500070001c0c407410b080c0a00050304940a1700849100c0c0d0221000c4001c4031141900381e409492000b50460110881800054103400c050488030f14050100e0722040c4001c455008065110340071001c46400c003020503014014144422100441002001e00c050b080100000b032807466808464500c0307031140b02c0c12500300501034001269003140c102c80c5030f4031050a019900d900ced04052040300d000c00c0c0740c52004480103010308142021000c0e19112983e4605602007480206035010728480200070b102140080a110a104e90b9070146006500000751502c1d90305010b030142515802c01c9841e5402408501035040002800c15445940300c0c2c40030603502000082602c160007035641d000114020901c0440c0e105a055001d0003c1d000d10000711060b0303d0400c0c643c10410103900c94041c0d00100741c10fa03100c089081540045500c00e201a0450313182441800c0c48507804036080c0800382c01030751a5102000580380824180703402c19294001044251907500384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911063723 1250 911062473 911062489
    0x403020a061119110108071803081b030409050114060322060b030604030c06050601050c0c04090c0b07060b130507080a0c0e19260d0c020a051c060b0f 66
    0x1520042214058482c02c1e0348500b4060b40102405000780003107600300903d00a09641c00d082892030005840c2000103115510410400303c00b2440210085034542c1076403a0a000c2ea4000200f0000150300018800c502c184100000c1005281d014000540c950501b544407a5040140321018030601007031050084d42d102110900980d64200b1440700c00d81c007803d00c0c2c1680a000c003100401da050154038100014160818468071843e8810f5504006594507980103440501802012521507445201107800c142401c0d803040c10050b0092941c056107d03954481007600d944070381406c030740c56901c80e001c1602504042218000c00e07440170809001a103084c180003418614003c00c11044541c130b0703903500c02000e4001d0306100c0d4415005840000c04016003840c0c00c4a8100c5845408a11001000941c840e007013200301c3c4507802510301d00907128480441e041101c4020344048180d074031030f02e424000a80c030f60b6075038110411044000d440c07108413102c0d400c1010444152981050040203a624060904d640e0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911064973 1250 911063723 911063729
    0xc0a0c1101450b0421080a031b0809100e0c030d1205090c28051c170903030301031212020a1d0a0315091b1d0117121c0f020306040e030403020a 63
    0x503018101c0d02018071144c0794517035070300e01c068640d482c002540b81e960795054010784203009412141c402112500e02c021078500c403007104c10380d1058000b9010304501c400c00390030040c41c7c98650f00c21160030710040400242030003480c1e400040420b810300c0c40c000e8040030600a113907101340203601404da0300c4107042c0805c0f8402c1c01e1000210070514018034001e0034240303145600d40039140181002c0400303141c078003407100d121000445c140c2d0041a401c1030021003206581c221440b500e0b02501131130541e480d40da10354050028001d07100060080d26445074044000505c080d0010102e80c0da40c0d990070f80460425580304845001e4100d0054901500500101d000381d00b04030901100c007140040c50ba0140e007400b5250b11801c0c1845051f0b40e00d030900005241d4070104409444002e032164107030069989901d1003640c03d40041c00e00176107410081044040c5c4e511400900202c888601c0c50702840e0000071601421205c4401d0b02010195001c004d2148038101031040601c0426200d00540c901420760300082c2824040344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911066223 1250 911064973 911064989
    0x507170d090b2a1e010e0f030d05070c12030f050a05160809010b0604080c0102010e0a0b2403100c020c01020d0c020409081c020d050c0a0c1101450b04 66
    0x1603200c0c20a030f20002000400d80030341006031842d40c0900804840e0031503540602c80100e40c00c140d0050f070114000310381c4007500a19807008502e8202106844030103400300410300d00030301c0010f0700e84502080800d41e045d84040703040d58000401441c440d80714401ca0714003401010700076140a0400480c08050030740043c4081d580e0629510302c2d0765030070009025040e4000419000140400d0016910a00084418200800340c00070711045842184080d550180c840003d00802c043c0b40205a1618034240420b001640041c600c200c1b1b003100c0004603140081d40080e50061a90350405440c0060f410721840301c041c0d00c244040d140507541d40d140100508502d81c0082d2041d681e8140d14401c1200901c12100a400207030b25020454003182c120303400035040500300740102c07414040014882c03988002150326524075512240105d01c075a40745d817106d004007191b405040c0000f03041c2c0984d51030710352425828000594103c0c0324480d90342001d94441103c01d1003003191600f9401c0743c103209080e91301d015582681c4600c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911067473 1250 911066223 911066257
    0x60f09120810080a0809030105130807120201110307080f0f10090203060607020d080c010c030605101d030f0c01110d021e0c041103060405130209010902070606030507170d090b 77
    0x1e0703000e03146008036a5101551078404c50410100300000c00014140e00f0b030301203000300659521240240c01503c000700008018807803c00c10040016034100d51388040d02c1c460702c0001490311a201c55011140d0003070350000c001c10009420001503980c0780d8219580811001d80c40480d030706005100350804107a07401803408454002c00011000c0c0c803008140c944c0c90303400421628844690b0306201c1e03466401101480055400c14146241e850b02a003e0b88048900103420300c8040030365100202d5480502011102081c0820102c80501c1e0398108528505100e0340300c081d080215604002510505204043c82d4040c1c000284205c8020780100758413507074140d1245a40810405c9883c1e25040040060030305902c6031400303121400804004000c0c5100300c205036020045074480360803540e03420000b103100039408180707000140820f0a4036005020014481d00c808075070340da204e80d00c042c100845600305084020741d006811140d00d40402040f8081703611400c00340b8583d8144415a0454421066442141122 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911068723 1250 911067473 911067481
    0x6120b040b03120a0809070303120f0f0e24090d0e03070909030f121401050103020f1201150f051602150c010e0d0e01021f05060a030503030a09060f091208 68
    0x854004848401e00201075a11200300c10b4107019440c0c0100e0045400200d6520004000d0f0b0f400042d05015aa00b640b03a07100309210206600e00680009844890642c1c7c0307600c21205030040034040d40c400700b08400d008d440d01c01510700c0780d10041912004000c050701070713020074030501440114503102c2c0d2441c0c1e4030386050200c1001c1c0104c0e1800f49503a0111b00e580f0324044146d8180b42c0c0c80807040903102c4484da20302c264040b0481d400c20540e841940703c03c504464600c0104032942c0203034000c003041400c3c03480c40c07410408101c02200c0c44010907800b081c2da81c485203076880b04646d030041d10740f03203c081203007440d0307041c03c11500e1610800044181c0080c003980e60b51110002c503e01501c1507410003403c100090240000030101036031130310000040703500451880004055698000b0504e10036000101c040840140201303400300700645000380c90036800803018400407010440c00e20046200d07201d448004152101686401d004a07810480000300703a80c0b40262107000611140c001e131018880c2898141c6803511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911069973 1250 911068723 911068729
    0xe0c09070e0109050f1f0201060f0501090501050324060a050414060c151e0703090b06040e031602040603020a0e1503030a1704060605190e09010b01140a020f1b041506120b 75
    0x860700c0c46c4158850301e105443c0b080d40c150048400e86a42e82c40b0308070610396a8005507100f0301d2900410b4081901840002c031618094070040c40c0402c08501a00c1310b0300c01c10408504258024041d410000d58005010301c28128a5441c8207000002650000d1800c2154020036455042c101c9070179007a42e00c1e207004100b8505952510b0440d103d5503001d03c42d0309045c0710340041c00516031060b08a0301c6401401c00101030b031505101780301402c03c5040c040d41c84e041742c44c4040c1d0003507450f003902261302543d141c1d404405a01d4215070000504101d40480509003040784045808507080d103503003440380e881040b61280666101150140d41154100101403584480c0307001006407043c0d070059504000e200b0112201f40007100d62100480348800e50050b02030b00c40e25001800d840c00c040c81540425401c8211130361713908000006006240040c4150741202c0d441201480c00c0280c414282a00c200d1800c8405160303161511409114840c00d60904407070781d00d404805405036600005000c281985c84165141e261 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911071223 1250 911069973 911069989
    0x91e0b040b070318091413120309020a08060c04210314030403031d0615031b10210f0e0102070218090c1206040b060d030503060918010e0c09070e0109050f 68
    0x100401c49140d0324584500c5050000e206c06030b907003452103c1401c0420307484c0c0d0304011005843d42c0c0060b810400303800350090590107800c0d9098100c0e044420340c0c1c4005115282070003403d000c0c140214003c0d030f0352850138001d10094160900740c4503c549051046000290700300000c0c40031511007108d51500d80e034981c2002c1d0002e24032021a1000c0085040d4407044a140201f0511300c21080894501068800e4505055803000c90802100b010300142d48085801c1c5010aa18230030031501c0e19052654075011850500b14000c1d05440c0400d1544660300c0c0e510341c051500941c5144400103000310b090003819000144002924058050b000840030041a03004000f44054904910040d018419843d9014440c0341d413480304580946113a640e02000c98080c0c9842d110810509405548484c150744601c01004800580941000007282041082c804c2022003805550402c100050150005c00000030a010103e4030040469040003502110345404d6a00103907500b05031901030300c904109080b0500403880d90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911072473 1250 911071223 911071247
    0x90606030d0207060e040b191505090d0204021e07050609060a090b070c03051b06011a03040b0417070210050d0f15061107051c11032a1807091e0b040b0703 68
    0x41c1c00f03900c1008c002d0320507006c0350308440302c5c400c40c040408080d08048a10340112507006a0050128240c00301500e0b16801074a0344400040c1760b00d940c41508035640505901a0a00300e4041d00301404001d803d030f600b4803015070b11403101c0b0000d0200000a5442503130f10314000784860148440010a0800e042c414002c2c0c0e000d01070003100414200025520141c4d81d00b00901ca10040d075403160b9400c406501c241400e0300c1c01603030f000c028111180c83e81c0d548e0461444015541080011091103e480560b4841010202c0d40f40c407515102c1d510031103800300070251002000310380c5030300e420042294141c01000d01c041c0700b00d0781a86407109000d88082000c0303052036070320b9000691100c640c8d10702400502c0c810101d80115480391800e2521000307180241515980c0800a209000c1040f03401c90310064003012036062140c0d001015092002d012074488070942c10281c40b041c0005140780c00c1445a44022030b42c140049014180302100e80389040100195407181e4000d0340c907034001c041810f0b02058001c1c0f00100b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911073723 1250 911072473 911072479
    0x60509011b1d030f16080109020d0f080f160317060328080c03030711061b0306030a06050903210c07120908100c1d0d060c05070807060203090606030d0207060e040b 72
    0x80740405036819a0311600c0d0030b541c0045e490180000665032074148590080305501828161120b0740f5074172410082d000340788060364524070030000c40e01084c1140b030041010620302d451440d0720a069050042c24007143d400d44185145605045c80240c0e5400104280f000e11600d0341850801c00000c04020505400708000b80b0003000896804031002c1c01001861258849580d400c81c81144411025034429050b258440c0f02c9100078585001d000910300210f0740500c01a044803546919659014110f440840740a00700360030214907840307061034903980110811511a03c1064a051110703640085101f00c01000304403092142c00050744a004052107802004100156200102c0440750603001e0a4051000340025900c0c003444401302c2e144001d503a401600290002d00303200d940350388081c01000100c014006201c418013011001030398960042801c1c1e44540c2003da12820034819075860f00001800091080e040301c0306e001c1003254001a0703142210014601085138181c1075010400500c1403418041d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911074973 1250 911073723 911073733
    0x152a0d0e030d050103030f0f0e09060f03060906060418030206060d03020f06070210060608070c030f030b0406090902030705010302040317070f0b0405032205101409040216060509011b1d03 82
    0x200040760b542c00241201d00a40b10320480c0e03c1c03028400c03124000000b038070401040c0d0f05030051041e07041906003240d0203c000f03452600c0025401c1c00092821001700ca031140c81d58060003c222050902c0d0045101c075540c0400123503a07070b9104d6038020b91181e0005044600445c050400d0905051003084440300079444101030751094144802e00a4071014a0b00c5012042401d05000050103032190020354481d032140d1703880856580c500c1d5011516040096800703410140c4641e00c1e110341750b445d4800c160040407a16000034050700580b040c1030600304143d01041c10b040c81030104202103204110b100c4204495010b03071310b03590039003881c0c10891840715020103000c48030140c0410040100c00001016000350002c490400c0b103020040001d114002c5016190700801129404020180212115000d0b07600c1c440c61582048400300202d0101e80001e04a1598250f0000f903440920a0754400d1640050410000b03009109500d0086000e6160501b9580100494068441d6500440c0307500702d612000c0040c1992 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911076223 1250 911074973 911074987
    0x309012a0f0512090a1418090d03060e040308010e0903130605030f06030601060e0d1e08070201232a0a0305030109110702150c1e152a0d0e03 62
    0x10805881e0308108450921496000e00419100d00c0140c0d005070a0090040091504100000b030010024090003a08407041606d601240a5440c00f490702c111211001040b4500c010440101a00c503181e00500c2a0f110b41000e22010075805064581901c0d1030354014509601d50856803403461080d004400007001c20602c000c2003c646c060019400b4180c2c400d4011029101c2104240d1100d40a1189001181c2500f00d05104c500305110314500c000d000c2d1807210755111070b00104100b4084080c104861800c0d00150300030466030002802c444a000702c081584c8a0080031075034808901c80e050240c403d48400b501006200e11a501e8084002250300c0700b81c8030007020914019040790003c2c02800d10250805071000171a41d010010b6407201a0010319400c10004141c80c00001a44034034010703c92401408003007902c5a0900d49280e1036a040079004045598881c86c0c11105128080d01221048000805412551940101c40100803c04c42807540d50751080e100418018159482c04004601002c100c2e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911077473 1250 911076223 911076233
    0x2070b0f0f1b0f03090f0907020a17040509041a010e010e1b040b160c05030c01050d0c0201090803090f15010302180601050919091a03030d0903091d090d020f0309012a 73
    0xe090460806da035a0b5501c04545020402e00f804121900c00040e88404407070000b044c03500003204030b64400f143c4500c1c50f25848102245141400321801d41c1e0480001c02d86100480c003800207a401000d036401c20780e426505140c240202d000300a070104400100e42d44801c035801a04008840043c102c492030300c1d60310f80e141000003240145405c42a5486103c2c400006038900b4082101c5000d988140d403841e1030010080f0b1408000c0c290041003504640d40c540407103001070443c0000b075000c1c40e0403200030100e600c90003905500e0808000100340d9118400c400400046c0c4468403100070f101495140c1c428103651740d00040b01d450151580c5180c2c85803003441490038020032440800c06940a8402c1401a40d2022044100c0121040250f40c0c140d4410003140400d1000c42c0c0c000600d882c46484d0800700d0300c1d0b4440001c1c00407614100d4440c401ca808005105a401c9c0400c8401d4141c0c6180c000743c8170350314840804039144c2c0217420b14207040c00500445040e40c01443e50900d42400400c001e406c0c0c3c4011301e4100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911078723 1250 911077473 911077477
    0x2151914071e02032203050712140706120905010f0501060c0c0b0708040e0901090209071205070212030711010f0903031407030e0a080a0509030601060e0102070b0f0f1b0f03 76
    0x4000030481003014402a5080c4260042c0c100c0a00d800a42c64400344460700041410345140c541d2140c0c0c81400301000250302805114000c1030148a80c246072030290905a0100d0406d0f9030103911036008030010030002d90861070079441080c0300240020080e0340340c01d01c0c50141002a54824082c0d18080000c604e058005000303441a40c01648101420f588552442500e44103170000a00481402d200801030243e820040a5001042500216211115074040784243c50240d4080c00442c0000002c10705140300c40c460b00d07030300c40864030080c0b600c04111300e22040281f10280030790b010410500c00710071901c0400d4008500d64201d94604010741d180c2818018020b00124404420004090380402e0525101e400b4462090380320502400c40100035994551080e800b83d42d0355414424140244070450742c0a00c8154000d003216140c1c17a045030307a0382c0c00080c1060340a80203c161100144590444502450300703565003080554041943e8162049401c01d22015a44008100d845030703941d0000e0b05000400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911079973 1250 911078723 911078731
    0x9030507050a0b090709020f040b0f160308011701020a0c0210141306030506030304030c0e06010c08161707081b0322080d05120402040c2007051305060102151914 71
    0x2510343d17240d1181c00784e10607072090400c0f41c1c24456080c0024032030903000200410400070300c810140e10345110312070604000d070002c40d4182d004c555001c1c010003a000d903280b04501c40d0400d5000844c94130100d0000075001642c61640079001da0b005680f1040258001c1c0040083c00c0030081549032a4a005006151000f00c140189400281814007095140c02d00205031410b0300d40c48841c1140302802d01c8c17005500340c1c200410312410087e0000c0300001003560340c0000c0c10840040d011032a07000c801814130940001440c0d0003054640c10801082e004201d0040030307543c040030313001e84003440b0b0ba2054a0b41d514501030004409170141c005964459442d04001c44002114400c000f5504142450708054499010381d48440e601d24030540001001480c00c0e41c412002c0100c0c1d401c00281c0e29404c13550f103064000141032041c1003603000503011320862510550f0409072440c070344010300c001d14000d80001e403190f610903486c0083c041d24402189011b0320905100451403071082c010044c01d85031590080c2070f004256 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911081223 1250 911079973 911079991
    0x903010606020f0618010b150931021602040212010e060604030c14191e05121f090f0b070f0305010e240312040e0f1909030507050a0b 59
    0x3031001800900208100c52400f90308006040c0b20369810140d542c1c0010700d0140c28905558131216140b00f0f0b0f4500b40d460798201a00383c43c2c01c1d22541000140401c00c03002d588030b0a0920402031110206502070050409052064040542c481010040340070340031603c0000258002d00208007036405070341c400a0f031070407260481e00002c0303d80c4405c020700540b8070980c0000307042e4203c9180d00f8418031201020210800d0342c082d20f50017526003c0d603c24050a20b0740d4114100003480c00162047e43d41c48550460f0240070111581c1c070300c4140710a107590741e030f01c2c07084048020360f407201c10026014813036984a01e6200350440f182428113212890a0102928211050300104e150790f98003491403031191042c02c2c180c0b00c4a00580d0810303203c07482d99588050070800d69030000f90b0030b0312814003d510b00303210030309415015201c040e880764240109403085d03805c003c0101c3c0c0d446001000b0485400e421507040303404441d01c40e10014000c81c050030300702c52031f114881c009031440c0710b140d5400c020070103c901024440c2c0061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911082473 1250 911081223 911081231
    0x501060302120c0906030a090f0c080615010e0f240f040303120b0109061407020d06051531021909151b140f0f031c060302032113030503090301 63
    0x52003192250007100443c58005c401400010704144065103c050120f00a0030840b0303132404980c0e204005e210050300508002d030041414460791a4481420603180030702424080340f410320080c0410000007100c44002d00c10002d00290401c080d078100010800c000d0082c24043e5030b022454602c0b00e00f503200d840308900241c925204a003006480340315902e03d001c4140d490031101464280219900c00308803203008401d400401c40140165030360240307209074502c034400100d614580416030120307000e805c5604c0e0f802409a00746040c942e0b01c001d0b040550726a403009002e4844091142240004d000700b401c40701242600b000061900364200c0500001c9401c10b130507803034191b41c1d00c0740d007103811582401034105003d05c03040600000900c2c02c0b9a00c000c40720310a0880c1c0f002940848507a00e4443d81c030f5003000c000c5c0c100103621001d2020041c040d96a988414000f0b002d00b0789151301096403214502001d010f601e003d44003902d01000483c0c01c42c0c40e40c1c00c414580e8002e4a480e410f185880e60300c00b80a542c030942c81c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911083723 1250 911082473 911082481
    0x30b01020c04052202060405190e0f06090403033803010621060e120703092d0e0406110a0e0a080705060304020d05010b04151e0f091509050106030212 66
    0x480c0c0249813290011001e5041c0ca8400d00c0c01d0b820301e140880c282240d1001c0240300c00b2800e0748444190b0402c1c0c1c91400c8001c4061464440d880c41401e0004c3c2c20340c840c0c0041c078170802185490340d0b010148c01640c103180005415240c203101e03103510280000840c2102d003103032100350040d180c0074916000c0c0b800202c00801409603101926504a86080e01075038491446c00018000f1541c6030788a21b0166181d50151035071801b81014482282e03210643c1140400c00c09103041c4a8042c845108003030102021081d1241e51440008401038098244aa4a2078994400000d0304000082d00201e00e441581ea081c2500c81d0000d42000d0652801c60103180e00881070640b00180c50200016282d045940260034645142c490303070244500100e183d44255050b6490380404d1101e0313142c0d403240b03900380c0120440c0c002c0201c0c00e200c280200d003241c08648440d8a09a80810703c42c14070646010340c1100d2600c00001001061030f000c2820850f555440005140d140000000d00160103400038100c0c40341122814400e940c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911084973 1250 911083723 911083729
    0x14040305030a2d020a050d0608010c020f01020f040e130605010605030723160206040b041814250309061803091a070201030908070f03020c0301061a09210706030b01020c 74
    0x9100101003c5881801003003084080140e40100650b002510f001490410001c0d138000903600390b0f5000c0c809682d9030f9800d1080c00b950500210601000301e200079440c09886e0010542113021b20300884c0f00c00e000c084003142000b500054131020080c1e0001040c09290381d95500503080d80c104407001400300e07400803182013480c0c1a00842032840d40380780c00d90908101015401c3d6054000c80c03601260881002c01010519024400c0588000c112404403003d40c2c014a621780026241d01d150071080d1401d101c414022812103480030100704003445400c100c4001401c00d400c5000e8030600c440030784440e1525100385006030f02c03820703c2448180a078485200380c0341d880b03070400503040c0d2204403107205203800d0060100540c0310303800080c5094000d42c15103081c00a2038613205e1550411980807030240c0e211409007103203800e080c002d0400420030120225170042e17100d03034440360718499600d007140728105882c03400c1150141d410340003000707803805000c480c03916450740c6010b0f00405883c103005001d442146240701440c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911086223 1250 911084973 911085011
    0x120601030c0b1c1d070909030f050702060a030b030c13050609010501090308030712091509020f120a0b0907090c0206251209060b040f1d0706020a140114040305030a 72
    0x105510a520350100e22048040300180381c0b4403032051500c100c01c010618480410841030016021240c00002c107c4050700d070140405d80301c2d020003014803100348110000351b81d4003020340e000c1c0ba0042c1400f29043c0c542100081c1400710741c201742980502403c07007040064041e50700162107200b0594001d83c0756621040152460000da01c0010003030f201c1000040c01244c4106010700814075642d001084440c0244e403641040f50f0410703c81d440740c43e6100b40d0300d01940742000b41c1c001c800b44261400603102700d400d020251103241044000d05840c0e01ca20118100d1103080201100428510408201c1010396840003501c8250658008099003611701b142120610401e020146410b516107070446c02c2100007031268040d01c407509040d26202e03902d24145060f40c5880c050106114a00000018400214218030502c00d010981c03041066000110500030250001150032080f900907844111240d140f8895501420b03007030046c0c89541c142d08041c00704154000004d1401031040c20814048412050080c40c144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911087473 1250 911086223 911086237
    0xa15020d0f0b06190216060f0e0a0f060c02010512010306140a0b180c0d062405030910110c0a060f1a0f0121091b0b0406081f05120601030c0b 62
    0x8008200280c480a0900075404c414004150050750503001d2440e251083c6080941d1194000c1440c0100000a141c1d203c2246040c154088030000b0006050820300d5012610728000c0c20244003401c2c10078402d45e8003030000e0f0781c1140003141c80200c8a60310303407034501c002d0a00401c15035070000c86c41c400700c2c0c442c444900031982405805040402490700a2014040f0000d001d40301c1d040508040020301790b129228000c0f0005040c2012404e41040003c5404200900c00440030300100b000034002d1000c294004038044005028a407404103036030046011540707641c8180c6150100903c22003001e0300070443d55401200c404c031407480d0108074901c455106040d00c3c40c5074000d00da6003c5001900a5aa036014032000d2a01440c00783d0208a801d1000e201c407402c86514110654003000441c03c081a10801c1102070303009030003045651030409203450f80c00b82004102a0000c5005032101c0000640d14821010020007040024904220003141d8030010b170310f85400313000c2039401210110001c6400c0502104464203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911088723 1250 911087473 911087479
    0x3130305090418061b140f070f05010c030c020601050a0b09040b0a12050a110f010e01030504110d08070210110d0507020d0b0408120f060102190c03120906020d0815040b01020a15020d0f0b 82
    0x40c07d401c14000740c001e81c5c8420f01c116507522400009170003042091085101100f800c1e200040c2d0601d6094000c0c1c644807059104a104e18000c40003800500b000070141d030006402903a020a5203808403000520020440d0012840ea2600f45441c1050010010301e441d02c09000e030501028103a041b80620a00c10051203420b030106003840d07e02d207603a5209500c542c0c1e2040c02902016101000103002807035512018600b076400d00d030007141020644c50185406800352010381822202c140013136540315141c42141d0307100d00c140076022401c4003d540b41d2414038503005503c012005924a082d07d00f50b0120b41080b011155040031082c00079000c400800c5840e802000140c00515403488540c41021580034595022610103c403420b00000107580032114803c291007030b40b9051507940c01d20790000d00e130141d507500c580100300200c1c00703019500196511700090443c068130080ba200c121880143d00d8128041c9008112000300d258401d4000e8442e800303001c00c844814018001240252000c609580c580d018490b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911089973 1250 911088723 911088727
    0x503190f0201030b03010e21030114310606030b040e0601180b040e1e0a080901050307031e1b08010e181504031205060603130305090418061b14 63
    0x1150006000e8850240705150204076042982e01003400d4490003183c03090f03181c1c03041068286000d1594000ca42a92441c1c0c01c0504640c034107200d0207050301a5203100b03401095405100301820b11610040405050350004c42c0c9411071590320107030300034441481510b0002e80790442c103000518041c001c2c5e40c1c40b5040d000080c4070b66400c040d01c001a4401c0301518021140c0e0352583e980403a22035003c0d5460b9651048058501030341948111300c1c0d1300603854100c0899402000070000094860020f41c2e421000a10705140c8035998410154010500040c03402c40f6184c1040c808281e52001b50840682e0340c1d020503400003681010641540c0300c15081c01070741442e44c280b400181d0103010101205064890410440f860004009402e0304600c00980e001d0b0006510588100c8251095002d00fa40000d410784d80140b951800308400300d103061781c0050040030440006691601c0c1d6a131508040100d00c065140480042c0a51414100500c070b407155014803041d24600c050910b030f0203011680031841070300303050314 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911091223 1250 911089973 911090023
    0x62814191d04050405030a080f09060c0702010504120c0305010c030b150c0109021908010b010c05101505150c01140103030c1401110f07021f0e0108090c090c130503 72
    0x5651100400c00300c5441c210164840c0c00541d5583c080c03940a14091006142d982800345001400740c1f40081954505450200601c0f508080000710540d11406207500d65131070300200d20040b02c080c4140c3c0e005120010182d04d9050910000703240754001c8a1081000304481c18440f1810f80568914240380c47c3d01400000c100b8200201102c010511924110700001d41c408281c0e000400c100f103403407640e100c800880d8000b4401440248600400034200742030210b042c0d41182c0c0c2c0d039070341c40e000c81c101480b510b038603000c0c4181400c14221008002e024014032a190529986031501042d80100c450780d2030340d41c20401000e002c2c001d054801c50503603801d55650440100551100207032048521103001c0d6665954526288041c100005000001c0b00c50100c0c5564604500400c40540110403130035110580d00c8502c03001c00e41d04800388045160083c240059180e0329031440d2410203001d502100d800c56a48005c0000c6014103034010b0504120b4108680c5046449406040d5121010991a0880c0c9030782d0310a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911092473 1250 911091223 911091227
    0x913020d0507080f0f011a0901120501061a07060b04180b0c0c072c01062111130f080601080d111f06150305040f080906281419 56
    0x42039928000c10469085035a0b4400041ca019400c2d01a50f0407900201c41900d2043c0e0203010341c0c10f00302d030540c00464099008200092043c48103205026007440c1c1d03c02c42200f00202900020020000d0622030182000806600c960603440400101c4230310303260012000346840c10b4458051003220b00110031071850165076a907600c5401c0a0592039000c2000e1004221407441000508013030f007902e456054440b944d0b5030703003100107002616051151112617001403002542c4035541c41c0c41c00e40c1c42011040c06070a0710550320014008842c08008242c000181c55400010402c0c075801201e034441d4004600660b244011511a6401e02540c2c80302c1c0c00c10341d48003e040303100d200440000c4042d0404c1d204041003400e4103e242c03a800b1414030300c409454240c20411046046940846a178060030144440d117840d9660705499103031900c1c01000707241c0108601741591250b2080d00c009030000d541d2140c0d13070b0404092011104880011050004a03010f100f9008001d1043c203445a04980f4403651384040004001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911093723 1250 911092473 911092489
    0x1080d1103190507151e0f02040f1202030c0a18091a0403090608090115050d050c091503010b10021b03120409051603110304080a05090d20091302 64
    0x4a80c0c5103200a00c111070018541101d0000da42150391030700c66071480c0c02c1c50196461041280d4038404e56181408074080e0000d11012905c240c00544400500d42d100880860001c0c040d9810508401c3d1550601268a02c0618240150315000711304646558000380100020500c55002e0801c1e00070200c806a0001c041503085044840e01c1042c0d08012110046a003001c0324004a03420740001c1d40400d8208680e40c0c00501c6e140c2c019683d00d009012561507950001c01c50301c02c074440c0901550007012507505000082c81505207045000380482c202c1e0070812100305190415071025803103035281011010359841c01d0f00c10b0345081c01241e0060301082000b80407075030000d10001842c940501135036601480e8240224018001340901c183d0000b02d50034845d4654090f91900010a414103140a514007209046001501e0348254003a0841e90303900203440c2d04031003a01a4070045908000d00c60101c0080019140442161045c00440100b84061000401c071382007009031585050781c100b040c0520050f040c1900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911094973 1250 911093723 911093747
    0x309010912020a0b0a0f081b0a08090309030105101502070f090902040e10020a1d09160e1801032907030902120319020d030203190507030e01090302010c09080601080d 73
    0x100aa40f55501c4804a943d03910050702900011810741002c0b81c82ca4010040580002101e9520703100c0c06502007003aa228803a0480700010f2000c004000380e0006401c1085a0346d03410b002d402480702c0e050184c403002c038004a900401e00c040c04482004144284001140011030f403001d2215102c8a207403c003c80014a40c00900344c2c0c000d5124003444002034070811910400c458140001030303440406481c020700398241d42051000e0f428001310820402d5523110f100d1034110315400244005410a080140e54020521002a030070002d4069a1000c800b04d01e00c415040700d000700d01c900d090105420101040d4295006901658080b4030b000c81c000e14803a034081280984094003c0490743c600d980c1503490b40e00510414900482042100900c1645c14000016544200d040a604600744007190301032120501030f00038503140e985d40002c5c45162182c0c00001c240322400c40208001c580c503040080c041c20509002101043c0e58180000345903500041e000d04031401e1300003800448400030401c80385100b03501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911096223 1250 911094973 911094979
    0xd0513080c011b020d02030615100c02060f0a0c0b010b19020109021e0f0604030803060a08030c100c0e1305060a140102100515090c030726060f01120f0617030901091202 74
    0x717a1070b900181c5040004900840002d01301d030b21808070007010030604e00b0301e110810040100035281880141c07a01c038161013800300030514850701e400c250304003203600c1043c1d8000075001070b5140f000000e0380d40c07542c4020000e4103c0c0940c0c603084410514001e9082c1c80c6511002908040400c08403045083c0065400b008820002c1c04248921080d100068036900583c00603110440c0010078041980350040c00300004200a0380a9801e010300e030501a610f401e61510307882800742d200c1120706001403140c1d641280c503c600900c2e103800031b001c0e005460028541265100d0050074a0a8003141e011219004511881d105078001d298008484a1540141c03101420115000c0f04a00e01004281d40f21049588203181610040c0c0d202c3c0341c4803800800200182c2c0c1010918810780e18070748000094000410790001e403d46501642c14042001243d0280005d0701d24002c55180684101441c905a04400c0445540309107064034000b0701e464013501ca200350000e0341c0c003040940e80100301c4000000030368045a4001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911097473 1250 911096223 911096239
    0x1605070503030c1c320d020a030b010207050303030c070830090606061c24090905150f060d0804031704033e060c0d0513080c011b02 58
    0x203140800e203141c016110845454220740403441007540c0400400c001c200e80b030315104d08801c21580c00317442c6507510741c1c0040c04403c608030080e144c000c5d01c10044951011000100315514107252000400810090b440d4a00500079080b001840d2320380001a2809030100703082e024508051340c0d0b9920100c0d445001203499603088400c0070b0071419805200c07150301c040039008410302460315023103085c24000024034003071180f50f062181d180b103040e040250718840303c1080000a00607020194400049140c2201d015a070250101c001c110026240c021076070f0780b48142c080f1581c82e150a0203003506200101c0340c04040e1100400000c000d0b150104101908a0080c0d12442c60603490f0389400c002d4031380b42c44c40d000b0305400008040040040c030030343c90a02403a1942c00f803441050603100c0a982755220a0305556040e01c50301c0c110840342e03070716400c0710050803001044a68282c0d0a480241064000d900450703034518980c1c1000500000101d0030300b0802005940303524400c908550b0040500c9044a0305a80005503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911098723 1250 911097473 911097479
    0xa0c0c02090a0b03010b31090c1a0706061e090218012001050903032403070e061908070305010b09012405072021071205010e030301240c08160507 64
    0xc00000811030541c0203c202182107c01442c0000d071800d40c00700e03000349460505003101007048000b042c000c0d1403056071201c510b29148d12255956001d040405000c40e8902840056030040d0046204401500d42c8907080e1140c2e92540750100300c1c0200700d01d94070311889a6850050540c0f00d440c01218a0301d0307103010300800302d8940c0a490308541080314140030319400001840f0004251001c0c0e064800028000540000d8860b0003180d111400f5124102900c0385c0d11004c510a0350b00c83c440c603201c0206440040c54269aa840720a42e80e4501d8403003601d041d441d04620792028280241c0c05416100c0030410100c00d0089500d000c0043c2c016400080c0030824244003500c0000ca80070300403d1000010303a04103c245a00d40100184814210880d09180c00202000c0a0204010441004070707910a02036034500c0b8a1800c03ea4050850180c05040030b0100200210f880d40540521000d454113428030b004600c9804070342680c840c1d00980c4007824005007441100c40007040c5080c210360f1244036030213076203547e55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911099973 1250 911098723 911098729
    0xe030703050903061503030d050709051e18060d08030403021c03151e2105060403020a140105060108010b181f140a0801060f0e0a030b0a0c0c02090a0b03010b 69
    0x8101200000d0002507500d10741e1404101081e0018155070b0440250078151002030b81e2445020752040307840340c81e840040c602e2400380550000910303002e4100c1128800c441e80b411480c0d41c902c003000384240f00d43c2c64005ca45000c000300c00c1d4880d85000d421400343d9102a1a20003103600300038230441c11842207440403510342c00841d100c62184562514040380f006098071200c0d6819103103801c184a40111950341d2080c03d00b007941000115100c2c2ca80780c1c00c40604052020300301409036200506140f162405010800d9800904410210300840d840701a2840f2000c050b800d8441c20fa0b407550004031800d005200c0c080c00c0e4801010b025030407496040b030211462000c607142d00c2d041d6032100c0c41240300c204401c840c0343d000590200350164010310a480d0032a81d24014010303407410300500f0104005101c00344808c900403c1c051038000001810300760000d981e403600c1201607800310fa00b24403c1d401d0a41f00c5d48107038021040c00903030560050100321140d88042c0c034080240701400341c0a0b410364075021501d01c4d0751 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 911101223 1250 911099973 911099977
    0x5070c080d24170148050c0601060c1110030f0903030c0e090103020a030b0c0f160309060c0506070503102303010c0801060f03050415180b060a03030507080901030e03 73
    0x921501200d10801e490009203600c5907038a1800c103881030341001980300d2501d49044401c00b0b0103602800941900091051600106a0402c4600c1d10041e680503035a8040c0d41000c00307081c40200d42d20803600c8681c3c0b298410bc50f0030360740417002085441c1d10220180146086c2500e812030f00000c0c540021554401c0c803000003540c0362400c055002c6590f484004072855031040301d41c011a0403d503044c41103545581c3c041181d44d8a01c0c40040c0c800d05407680815440081078048035048890b8841540d1248141903035030b59040c081d040c00303d01080d1501c00019a20b80102418032600d50460081d10a5644080c0d06848562000349200b503c125043d2020078541c0070010302c01414800d00564140c5840d10109042c00c50740341c0d00320b0005004948004000048d40f00d0f0001c031404074180380c045400e40707542c40e100c00101240315030f00030890300342002d0340c005558007440c516400d070094044802a0300c1e46801d11000da503190002800181b401c0000c040403449035070060034901d10600d000540e18141c090510304613 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 911102473 1250 911101223 911101271
    0xa0203011532100e030705041a0609030c0909010b0a0501110d0e060c010c03020d05060306041e03032703180f0b0c12030414120313030e010e030303070306030c0905070c080d 76
    0x110b8138521025003181820000351000d44000e40c4c0420101c035a4486d442c0c00b284440d4a500c1c443ca034000b4035242075403010300c451100c0c04800380c1000b003142030070b0b0800c0340030780b02a00440707020340c04100c7d00050541c4a81242079a00c074800010302290210150200c550307110100d0301c80e070009000c1100c45100c600034030451100303000c1e0741da0050701ca84a0380500001c2d6440900300c10300c00c0e840f180501c004a40720125000b20184040140070050020307160980c0035005910b440d02c444110b102440c0e40d50001204506000b600c80c4e40c9a01500e0b90303809581001c0910743c021000030702d840900905c10502800001c003860708070401181c1c0c1c0361090301401c3c45250300455040300c52044000351200b0600040040400007410a800d040c29403070810f40c8414038000014000d400c000300d01e1580c8283c3c0e40150b6001640c1000641903a80e603240089000d000b40055110440740742c0d0705050001240c9120b480b8490103000c050360384501e040304607210f4140c240c021041c2c410041d0b0741c070f824121586c1034852b4000c0da6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 911103723 1250 911102473 911102477
    0x216020d0c030c0b0a091d071809050f1f1a0c1006080f190503030403142a0d0305042a0f0303030c0815240705010e0a020301153210 58
    0x41e40722170040c0105110140c0d0b0000e2418070281c5408000b42e03840381340b034941c8140130b4940008000031820078040e0101140e40481400c52401c0240040c0c0801c494001384100055038982107500f210078598000e41102e44628502140408a10b41d0303060140340081c414035161504403545404c800d03e00d9030840301158003041d49540140028010304006102c1d03451120110f030301c89140c0c40001e85400740c503480000c100508000c0c102c8000c5900301d031200b050f00c1e04910b04800680c000da1500e0300380d030200c103c0510101554414500c0b0740d55024481d0048bc0e12480e0302050030541700c010710110020306024035004054404241c40f011404042d104d803c00e0066009075408513000300c00340c10281c013a50001d4440124580440b10416290316190700486001019414035141401e1303400c0b80060034000c0c2c2a00818a5091800c64031504000281d4032070a00e0085008100280740075000080000e130512812500c100da24220340001440e05550704002c0219515815100c03001100090307070f0004001140b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 911104973 1250 911103723 911103727
    0x6050c03093d0e10030e01020d0504021507030e040207061410150f08071409130e010b04020a0f030c030603080c011506050c03090d08070b011502010b040216020d0c030c0b 75
    0x51114814280480760201d82c011119000281100400002c00c10218500442082c440b031200c0c01c0c4a035000130440d81d5520021501c074071b440301043c40904010b0f6020781c41121943d8644561004e5035007200d1070540c0c56203c0d211b08000780002d010180d000179000380ca0460b526500c141248001030345442c4203404680c0c1200c5002d09018400c003200b64268021010400000c07604c0f100c058001303010f00d4001c29103052000244070301105000c0d840c40f80300800e94000101d100103089401090700082c6031104180000e01403540d150042c4400c80c068540184009441c1c0846040b038240a54000d11074490b040c503022581d681c40c0c4d01d581d003103540700d12464004ca070354884c1c0c0b01010b21496000e1201170206450700c64030300250a408255280590800310384140704c540514801c000c580030407541140d6115032030196540e941d05080c40340c00503905d4044095400e02c802e2440302c0c646803007140e25401121112000e005495000d000c12070885400c1240e003101c1945010010032101300001303000f85020840c0503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 911106223 1250 911104973 911105029
    0x4030804060f08060a0b1c110408101131030819140417031b15010e0c0304140102071a01051908100203060303040308040303170601051306050c0309 65
    0x2c08080c690440001004100340034840c4c155244035840701215924403c268603100b003015000e0205c070140c6151029180740900c061446080340000e401181c050310155009240d81460540640e280c9400701020410704110024a01b030b6100505201d4030802c00c2c021209070040201e03945000d215800039540c015002c90035142d8012020f80002040d003441c60424000e4840740d0200856000b0340c080d61070038440c00000c4000640080007642c03030712a408101d6152281c014222a030300c030201124200041c041a40010400c2c180c2107800d203015180c088205480c50355141c4078160751a2170042c9843c0340d5502009400049200d680c14403e08101030005043d0170752401c400c00c8555502102a05030f0344091400801c171560001c40e00f481d071194001c2d005a500c1e0303107001c002420340c031580e080141034400218010082c942d02c40c2c459002007408070f56071040358854000549960003003003410300360341c0754080c030502841d0310950103044400090340442e401c001540001501c5205000342040e10260501810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 911107473 1250 911106223 911106227
    0x504110607051203060303070b151207060801051005040e070e030601061b080a09030c0801061a030105030309040c14040b0c011a1f12090b10061d0d170403080406 71
    0x4210249021202145010115035650340c4078400c06a00720251000440010201e8800707008503010f050344446002c4582c944100c080300050b4203090003501680c0d6800150101050000350201034600380c0e01c2c1c0000aa1070401045180c903003007038a070000c00c44240f1000805d07440c481c611034020900c82d100c80021a080c7d00505180500591040c0104440581c820201006100603a402950801082640c9944291050700d41000b6079100030321a40f8641d41c00070b104541036205000355a00ba1010411030214102c2000440c0000e0281c940d040d0010050091240f500b03510042c014203080c10040240ea00c0c00c504011a50420b5000c3e10039050005003614542c0001e100744081c450b885030010703101e86051408200900c4c1500c4178103e10100c101125200540610b03038060410f07402c4074091000000616002504020550b0400c506205001011418074081c8803403c0c4c0c05000c90140c0b80c041d00c541000c00c03980340910074007038031144406518100c01c40400c900500c0514096403405954501e08040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 911108723 1250 911107473 911107493
    0x5071d030106120303090203030702060309062e0e1e011707050406120b1e0a020a1701050102101107200114070f08030421021c02070f090914060a0504 66
    0x90348281d1500200f40b00000070280360452694240c98009039280d82880840e1640c407600d00c0c041d5000350048100058001c1c009010342c4100e050140449441d106a4100c00c0401d812a420340b5801d120300600744452000304250707650010303112203d51250820101d04c100801c03802c0e0001c240d03420303211107451807804013003003078000a081c1940c04102c40d905d0080110b01003400c1d40c43c01085443c220011800c1404108040001d80710450303010101810b00720b680170000d41c8080d600202064820801c1c01109003501c5030907040f1141a005000d904110960140003000c01c2c07425813449100a020040100790859424072144581c007411600f112201c0740050320b2a0181c2d06c0c50810300108000040008401c00c951070704460b0f1100f4003a403685c680385400c0000040050b5158004610401e503240f446c1da0002d0301c580c40000503e10141c80741c000c1c0e4000ca03152840340c06003204000506408011100c001d03440641c005001e80c285110505d110f1920b1814008182c881c14041ca48402c14030050000c0340031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 911109973 1250 911108723 911108777
    0x5041b060e0319080d0c0e100c02010f180b1b012f0a140c0109060f330506040603060f060f0c02130b060f0301080f0a260d0507 56
    0x80a401c08003614001030380c1d4402c6102440c445074840080f110801118070145c0c1e0109222034018060000c0441d0014440d4a1403007001d4400e001c0c007903804c0700207401010a10181c80e0103a40d441941a07990741d040c1c6601c0030103a070451180c9061880001d8403000c100c0504042541e0a20866441e8264800d050135202d01030603666401c103e05001072095002000280e021604402408c0d40781c1c0c05040d805e560041012020f004408400100503c00c40c0b8107600888140e4401e0004001e150950302c03901c0c003251625200000303500c284242c0a00024089000002110902802c05440c6a220b1011441c281c005900900210352110070500016512503850409000303380741c501c8a00c20403d01c01810710200e1400030303010384078604c0301200000190300302400106003d061181c0d40e1080a94411569200b445403220364018500310446006000c9440d46010b508402039205a0b07034080038000050a0a40c50b4500390381741000384030301c0507415001b03ca100d031a654482640c81c04504016192001d4940 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 911111223 1250 911109973 911109977
    0x24060405090d0503070c0c0e0c0901080a0c0c17040302150703020f0a031d01090807080703022403061002030705010f052a0a030209010c02040204030c0f0815150f0405041b06 76
    0x107010382114541c00004e40303521440c549400b41d400030356810541020b2289400c00c0d003080e00207004000b0000509801084181420383c0c030340e05d840d62804003d1080302d0032925500002047d4949a40214169514001d1201022102540f07025070705d50002e000420b1a0007401c2944402083e508189501032011107440c05c46200034101100c0c80e0354000300b1210907206000000c000c3c10030b4401e11a4800c5141d680030b0001e44003200c004540b00c0001c0c1361b543e105403108901c2a2081c6244a40740b0601083d00704414000403409811615143c0030001008800031881c02184801d02890380460400d0013000b040348013488000071242844100164110007003060030001100d1a0700400a100c40d050888450019600e0016102e000c0200101c0d4480c2501101070741c49400800e0201c14002c2c142c207888102c03041c020144e668203603500d00c1180c50350a00d41d00c00c2d00d03204150b40050f140080ba143e4040240c14003c02070b20020400c0d00008045440a40f8203a54a0038884a400ca03442400d401d260003504640c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 911112473 1250 911111223 911111233
    0x60e041d01230f0103020f1e19170c06040326030f0402040507050a1d011101021305010f230d0e1e0c0f0f060a0302071a060a0b0a1205092406040509 65
    0x754021403500b010950306103006500c101210300c0001c0c411030846488c03690090603102d0760011440390605954a034040c2c0603e039244030401001c2e80b42d00003061050303203502503c2c203401e0070f145403658240c010100d51000d0708418510300c08254a03010600451062031000000b89060500e0300500080703400080074201401020030500040036085041000c401007044020f040482040c00122029034260070301c04061741c000b1410080360079021880c00c2c141c074000c2c0c1e11002c1d04820cc1008503008071003107d58840c00d4040f000000902d150400c01050b0000e18140c020a5490340315452902d00062020280310700d1030103860305040380109014050700c50300304544600c00503501c00c001504a01102e60103a125100008070748080b40d000b41c06a400c2980c0001041440c4c1111007000c070003640d411141503210351b4440c0404102d5621a600340c81490b9801d035a1890a032011111180c01410007030001010380c41840c130703031b01103a0265500c803007094403403144c1d0a402420030009010948601401c02109a006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 911113723 1250 911112473 911112479
    0x90b0307050331030c141621150905163804060c110105070b0c0a03090503130f15270819050f07060e041d01230f01 51
    0x22240a882c0c0048007000b43d44404101264205884003503032844011810f0070034680803e2503000481c00341030f1805140c01890303100101c1a142e480c0c130f40c25408103001240b00d2200307000b03072641080031b5241d90310b109a40200000c85500d4074200105800b42903128547c40b424803104019050091150a07944000b0165460741401c0c0c0381501c03400e00c05811806d58040642d40442c0003a0005012505010340b070300d0503a9a41c503198000c10055912400761110520010309000552040c001c807114980c20850510b52a100c06018440b25071002400074209030315030076180080b5105100510140c2003100c02d07428418504100741e042d014059204000190001111854954100c0c01221b032401541740014600c0c0742d10381c20700c0c452060582000340d0a02c035910610454024114054150b0b41c060011583c042d40c034140d01980d43c484501030000000c5a0040c40101414250444881884965a5000300c501e001a2403421103a0701103001000c8111140e000c05110404031845802580390710340c5068542c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 911114973 1250 911113723 911113727
    0x3300203091b0a06050a03110f19051206010305071110020903010c031a0409021309110f06070c030215040810020315090f04080d0603020904050114061c170c0a030f090b0307 76
    0x2511130b034000e00c4800140b40c42450303c00d60291002c61414114603450788841221a4815000800c600f100c80005d052585c1d4254000d03800d54040d0030346981906000c0e9a001e0045000d844047d0030402802600c0d038810f08544030610114440781d080002c0141c651203002c00301070969010b2038003501410702e03014102c1000c00781d090031480412020b60700031802c906c82d0307c08030310121850029044541d28280300302003005941075200d10400700c00c96050040c82c80e080104011031042c00c07402004d00d86030080400040c2410180000440c0101c14460300781680e502c50303241800c0e81c0f02c56003c5003640c000100643c1c8056803a45891011099826411602e010100902080c4002d84043c00c01400850860311904070307500103102955014202085600340fa180c103038040c28120480d0b0111100000004006084c480ba0980d0700205031840c4005449150312540040d60440b150410701d00400c2040c9001c002080241c0c58003070344079076903603042e06d1080d0100400e80d0078941c0065010110400901038995 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 911116223 1250 911114973 911114989
    0x9020f09180916120b101e06091a07030e04020d0903020f060106030c081308300a0b030d050d24090621081b010c260601020a03300203091b 61
    0x55019160030801d4075800c1b140403504c120796000ca84800c841e92010504041c1c9000c140c0c0c2180e20316210030b43d055450710190300c0d840181d248410101c03201800760f540400d200f03080d00060802e0213040146410100b07107102c41500c0070400260b0150b84000074101a18000b081818010700c2d40f89804c000801e9280c600038031200d000750503001c44010348440801405004401c9030b2144c2542950f4200e4001c860300f14000841641584281d80140312000034070100a901604100101c010068200c4075150384003551141c1140d000c0018030b40d40c4003440c80201c8003035072508505c1c500c1480c001c054503241048400039148190231031700703410300380365408049403c01141d210303080f030762001d000368a40034180005210165a440c1c254450343c20801c0103050320f600949551100c20641d000c5448280422203441440e070000c0e58102c1c0140e00c0b61441c800403a03c201101626141480c05007024108005d859102444580000c800e03ea6400005c0c400502ea08100c101d080c08003d442e0b0040340c05010000038800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 911117473 1250 911116223 911116259
    0x5181302120f0304091b020a0b161404270c08061021020c0106080105060f0402030c0f45040c05090909011a01050301030c09020f09180916 61
    0x915034809034011151024802c410309207030041d044944440e551560900548611500d4200070381100c11600011840800c0c000c41c01a0001e000a0351a00d812030b01d506c80300b00c500c03604020000700c252201720030007501c00100000c0c612150781500040150305c210800c0140d1005801c111440c04180c2d04480d500400710551050b02200c0c107041611503684169100364585904612915240400d903c0703d048590181c82c50101c8040200300301502d40308118201c80b02620800d0f44190840340903011840d00760011980040480003d5051007102107500c1c0d0b0031307001010301c0c0c4020345044242e00c1030301000e041e40041142c0d400342122504250b86204419515955070180d00854a80907144010b6018404607010804041c114103070525000301118000c050a207050008100d1551801c0c00c80d611500959050301d400c03c0400036413078a0700c2d010200950261280c22041c400034005907825135958a804043d0b522446602255032a2247ea49410f06500e01c00700e4164006004061004c801c51441442e16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 911118723 1250 911117473 911117479
    0x3191704080f0f0c07170304030b0f040804050a0905060f0411030604050601090f06080f0c040f0b071e06142226040b070c050301051509041b09020405181302 69
    0x154500c0c0100c400801e21846121090001000138007444030314001811300220790554100720701c00d805c6a22056201d01c2240b04c068000c40d06040403d42e2070b64440e0350260080c4c41910a1407510380e44801042c00c6200d030394801ca0a0179036900c104102410002d03032131300c4c03010381c01c0740c00308254520ba020034a41408041c250900031b5664000103010380e400380d4078000151011880a05030555100d000610200c03086505084c1e01c0c440801146902c1e20361003e580c15035a00d015003c84090400080030550b4010755003e4590000c5e400f03050600200590054458502030b01e004078904808884011600001802e0070303840400140200d12028a0b401071003000d550b21640030781c41000c1d501400b001760714042d19800181d69000800088008103540284003180c030915454000f140d450040500303d40e030803942031000070640e0045809614040038044d42c403500c81c00c1c0440d440c2ca01e10a1451200c03d180e0400c0c520140e00080c2070040307190008040304c8280c04444402100d103499009008030052504000b40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 911119973 1250 911118723 911118727
    0x1506060a0804110411040810110406020a0f150c0905030c01090e070e0d02040516080702010c05030103141501080706020f0105060a15121506030506030604021027080319170408 77
    0x25840c4d0b0740fa0010100032031201805611652241401d90b00e83c110050b000c0102032400d9200505056035070240d40072218140c010704490a01074894824060741914200e540340c142d007a85001c180c04512504001c902660740b105802410072060510300034547c1c3c10076040c4150f405080090814290f5516800041c9117090b516019034440851000f042210000394041c1c100350400100c84090103070300400348180d5441d02e1070360715800b10590896250350741c40c03c0007a0341000140042460011000b01003100d401c2191000201d40c50942c540c00b00c01c0c0c00c6510250400c040c200480e0707504000c443c0792541305000810040c1441d00010325954524400e08002d95065007100b40310a0094180745281c800c41d881c01c2c07140010300c200d02201c0d0310040c002c10001c20710f010085a141e050000300305111715070190240b03501c4000d20f04151041c00458504090400d0503034005151813880715925001410250000d54541001007110402848a400c80404101140824480003010141c100790400c3e00034054903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 911121223 1250 911119973 911120003
    0x1080a2103060b0d050604150602070b18090f010509011e1503060503060a0b0913080d0b12030403060912050a090e0406020403170d060602030a0c110a05121506060a0804 74
    0xa030251000e60f02802c103408000c200070381940007a8000c00d20880c07007110100302005203203078421545001c81c0103071001079000c104140035010742c08001300b824810000594444d2203a00340010b841160071250035190700a1003004202500300011924094a0034222404843d40c404040c0045034031036114141307100b0b000407407004009020303500c05006058050207480841c81c3c040c3c842400b800086010b81d00590700d07200010142c9003244a90020341d0f03809812503150520b041402000760440d8aa001d600c42d140d040213045100e03081004100840c03213841c001c0f801360180e08240015032200300c02441032060811814424a620a81c808141c4090b100c102c3c4039501d803828100000d0103a60001088400c250031a144002600d00152000070310001062005a403600c0040740c60340200210300c0007050240854100252110000b8030203007c02502d01c4140640d64400a02d80c2c4c0d880004513003c84e00403c3d4070384800c00c1032480b0180e10090655090b840c100c0b624000900b0000700070b2001c3c0219020218075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 911122473 1250 911121223 911121227
    0xc0d0b01020d230c19050d050406140c0c060301060f0e030a0305040e090c0a060504172a0102030c010f1407020f070b0c011b0206091902090609191802010801080a21 72
    0x6680207074040740486a07400703003105201211502c1c3d1042034920f0300c240387e0310340c0d2801c0c0305404640680310030341d8403011180311449404143da000110982064003030300c00d44880ea03803501400355008151036901c03022006d840d41005466010307501081c80c026009210b882000c01e8202049604454041a10028642c1c1d050403450416203031000c140e034061107444000075401c1d80300300a8401d5880700300d0350041840303d02c042540d0b2011042191722140d804a000b41501c6003108a00c80b00301e00c03060054a190000a0341c0f214212072008403010700c1c0903507070f103500420b081607200d11a0b0f0180050000b4944040100740340780d83c461051040300400c01c400180036554034001e4000803251030303501034400d0040104020103900c480040301e09280034841c00780c0140303104220540c0070301035640150005a1a482d600140a00b4240003400d61409050075804440f40003694818091100a405042126841584001007144506900009080d4865003045002c504120640c0846002c11850007410102943e07003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 911123723 1250 911122473 911122477
    0x30c0702190312030614031b030a0b0c0415020a0503180a0302210615060f070305040f030813050f1008181b09220b040303060306050c0d0b01020d23 65
    0x7030440d00d28400d10000200550700c8140c0700110a00e89041c4445510b8200d61a80c45a04a0f001c17507160780318070315040000725181140c420001010341540c41c0c0a0f0191200e68940e541a0b84080d4000c0c030000c3c0c100300e007403800780003180d00c5412407016124011068480a65a010756941d01c0424005006105110303903981c99264021070f40504140e02c003040309042e103424003d170080711080c58014080002c220110302c0c14004d80600008044034104840201c0c0004d03590050041101404010070010a034600352030031030780040d482040c2c00c5035118001d0481441c0000640d105500400000d55031a00581d111413501c12012400e01e80422965100342410320203850b1404a02c00034011400781425000f0740380c8041320310306010794048450ba107a0081c0c65291507070b100d40310300c02803800409902c0015080c07410981c1040c043d04d000f20700d50351070346c4450080320020350701106903034000030381c0d0740d69119a400307030000540c800d001030244122404406003ca040e404440c4d13010400316042c0e0400e110fa2201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 911124973 1250 911123723 911123749
    0x22031a0903070c080a05061b1b0c121b0103060501050909090c06211501090b0c0a050111072a152006190608100203130506070203090a08070506030c0702 67
    0x40c0f4080709a9460b070001d81c94070249801581c0501135100054a030041c0080590700300d000e084542c83c5001c42d640c051024951051807003d15500440560080f5640c3d0313403201c02482c20f40480904000008051005081035444417028180341c1080002c2140d6a00202913464181c4107543c000d01540c0c50510b6542040351580c4200d0f880310000c00c80e5000c1c01041d5031041c0020100a11012150319400320b503000c954104040540002e03150a8144854401c590150050074000c03001c076400d05625a440721309527900140c8410581002190349028854a03900d426090007844101e01c00c084004070041e2803000481c0101d2407089030400d200c450303d07031190b80001464081e40c600d0307050141071480c1442d10350a003580c00300c4d50b2000b00000300792500d41910540c0700329007800000740103050400607000080d4100803c0800c03905c9080051001041061101c984104015400385030b0b221030580801a40c0d9080350070662055000d40000d0100740c44041c100c0350010170000d142c40d142e90303d80c0b0004001a034640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 911126223 1250 911124973 911124983
    0x10f0305160f03150906050a08030313030e1207030818010f0c060507050702090f06010e0603130609112205070311042d06030506130905062e06020322031a090307 71
    0x581c0012040c445d40d11403010b55804445a0342c10317964070b42c0350310760b00e02099840c8504c1241c406404030019004040706540300350090808041401590441820003006902c151035100b07000403104075110000c2c400306c001c807000b424425040e81000c40000c00c2c1039220342c2c2c010314240c0c0c1c40000c43c80700b50065003070f82c103510790040001c1e1046c6440d22401e07600103c00d0b2455070101da5154080d9401c2e141213030a481c410340308030b075480044502c540c4400014041400341600c09035401008107103d600e5200c1301000e0201c4000d480707101c28079141a0a0200d40b0300030001c100309403814a540b04c441c3e240600301c80c1101c0c0701c007080c1d00c0d9221080c20f98804001c0c10000041d6659451a0000f0308250141c04c00b510540c800c4036a0040100200d0146d13050741e098540041080d0440380c0000d04200f03080c4a038401424004d00500900c00038044000b05014641c0c00240250340003080420682c046071402000060034181c02141e49071840d03480921400030003515510800303900d0009568980c041041c0c6500035048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 911127473 1250 911126223 911126261
    0xb0d02191110093206060604060507060b01090b0c030703080105031c1d03010c11010506040911130e010507030e12040f05010f030e0703060204030b060f0a170304030b0f06010f0305160f03 82
    0x90703070031a110310204d4031841541d00815002030860b203410400c5c0c400300c4210713464580c648a1a503541c00010107402d01c2e01814001001d00104550381d21310701402c402502c030f0300103642c2c600345410098040302c0143e121074403e6224907581a00015588280f48024a95040c1150f00c001c9918421310441e001a0b24260950701e0301c800401c0c01c951081074201d1299000000300580d8a404080c042071f00c0c6001005081d294400c0c01805490a000244402c02e40300310400084c0c403850445800d00751032059a690001903142e42c404410600240070544085001d80d180601e4545803441c0050f0900356441094103210b5101e40841059000c1d40040c820f2034081e00544070640d80f645080340094105d800181c4001030518005042c609000c020b44844d003000400c140b00d400d2402c01c1500c1d08000e040c90010290000303100000014101e00c407105d000d582c035070b02c03c00d450745006000141103070319900c0100201820f0005015950040ca5030f13200c11104613140405003502540810790141500489a080b00010303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 911128723 1250 911127473 911127533
    0x6070606031e020d080c01090f120f0e03060f0c120403031a10020a0213090501110c060c070f0206030a110c2d030d150b0d0219111009 59
    0x15030180d819a481222000c03100d025005140d603960200440081d041080e0100b0307003000c10200c0c3c0141514126280001c90307400c43c05d03500c22101c0340326260100c8401c5c60001c074143c0102e409c07004401085241d13180c120102010480042c1e030315a4043c0400c241c0101d1000402c0020b4420340071039891001b02401000241003500e00240100820150b0440c14028080901c040385401e508032190140c45070b00502c10a4001d400f0807104000b0910f5050000d507888900c080000c0b000e0040050759008203036003644510f03034050f0590420000910512144c04200034200c0000c0448144802c1a03406a03080c540f41d076205070000008240702d510fa1413500c100410740c45032103600060041d020000d4110005408500722058580c030315048880280c140d0018014501e00c60b9840c1c1c08800810404280e6140459a0f02d0122486a0190140c80d554640000b20707200f0100400b1014036440b041c0d86080c58060f40790423181c507102c0b59103140c000748060b1240c00d9001441421000050501111300d00803402c128 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 911129973 1250 911128723 911128733
    0x9082509020d0204120309030606140d140c130f0b09040807061109120a02031e0d0e04020f0c060406050609040201051912150501090807080d0f170f010519030305090105090307050607 80
    0x7100d00c400c45644ac2040c50120350700480392400c182240c405400402144990b83d83c00081040728440c5820f20b00c210b8a244400d5070b200400c1c0c0400e80c414140000351b1080000035041a01e480849107170081c2114803c3c0720025440400300c2d800035030860340000e0501645441c2803403e01ca01c003281d540c001008603050743c0c54100895044c9000703208030f0442e207590030034100303603445228206200d10590700220240e041ca5401a0100783c542440180010301c2e16101c600789400d286c0014080214580c0310300304000c2009028450141c009200320782c4901b41e0324056000900a1003140d0016100f404803000c1c0030380c5207004081100c2866a07081040c09401324072500382d0010a0680f003450700244800000203511480072402200b900e0000000c5c140741112043c5c00c1ea01c420086007403004210b60a60b0ac0d2402c071650200d82805220004400c00555241c40104030b00031409030300403020781d0170300325040000a1700f090464085400a092041d00c4080240009003080034030351049400041c00516502040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 911131223 1250 911129973 911129987
    0x4090213170a050c0d05070e0702030a09081b0103020a0c0609240501030b010b16050304090501090b0301140a18060509010f05071404030b04111009082509020d02041203 74
    0x1900c04600d207100541900251642d81c44440406070a030381224014410381d090040f8038142d803074050070403603d5144d03840c41101e003600707000c0b112000142c202144400207103a00c00b040600800c01c03000101502a4901d10405a842410103070740c1c18564002904504170740207141102c01c4a40111040000070f285040084031049406c80b804003a00c02c00c0482c2c01e01e460a449007e05076074004c4402c00c102e80c04e00d40d429940b58001100c0341c00c40400c000d00c1a000440030801880030344840d050105403549440d4840301640c40550250f44240d042410502c0503034039500c04c003a030110f00c0d5100800d1481460402c942c0190005501405140c103001c100865203105400110100301d400740708116039074801008030303a00e904a924070711640b05c0800c0704101217400101c3c40783d0002c0c05401d54140e115191000107820204066014010072650107040094800501440c154401c0c0c01c01c10700142040340c0b000c0070050880b07006098806901243d48035040d501396050724007400e03559140602e00c803d6030030701034000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 911132473 1250 911131223 911131229
    0x71d180a030c05331b04080a021906050d0b1302070c14090403050a11010f0507020c100f1407050c04062603190c1a0718050607050304120804090213 65
    0x64482c0780c00d243c07070007201c44c0380a001d149552015880705030000d40e0360f11040d1801828580300000045480002c0b2503190780104020021100146501c40c0d0754814030440307074510b81d08421821090401005250740107000c8401845001d000068469402000540c50b100c0b08050000b501c0d1022801c00b0411100d807036503005481131518041c4000307400800304800c00e030b4203c90090000b01c06000314050140100f81101005080500204280300042d9208080b900b0490b10040140d2001c4000b84940c1015441d07165034080e0362400c00c2104070340d10b0b0082c04000b42c040310501030450001e0200c0a10105100510010f8801071051043d50b0361103c1c42240251381c8400120030410140303420a0101000086402c51010f54100d03641c000d02e129030554006240250680d1800e0001c961420309681e043c903400c1c4601c200e500c49000d90b483d9103a483c5945641c2d900000c0c0074260400410000ca40c001003520100d4040001000012446150454150065600004c4030600114000c1c5001c032840d0807850039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 911133723 1250 911132473 911132483
    0xf12030a0905040501150522080a060615031415030703060c2c150c100c0203180909060f09100204090617010c0c020f0301020c100f0e071d180a030c 65
    0x14590b21a0030040c0c0c0c0100d42152400803500070083e0390144002356040748140307094184c4180c203065541c1c01c0582022030149c0304960090307171141c00340310300000e4500003413640c101c0d46001c00c050041c0c42c5a0000c040c00c0036002c0d0200d40340303400254025650400498016550040b401d22038031035035000143c40c01e01080083c0c402420089800c04c12120920030201d184030f4011300d44911041403911502d41e99100c070b03001c03810a001e031440d00d4080d15542d000c2c4c183c0b92070741d96004550f1144c2c0c444501c1c1c0741c00181000948155908414841100360008000360042c0c1d0328200e10b946030303c0382d516807131800e6084001040c041d030010400007140380c242d60204048403104000c00d2030a80130704600c40e08a840f4003a040001c075000a40500c0942407210480040d81c5d00980010715108951030540e29150f51580740311100c80d11141907000ca00c0071805851015a003c0004103421420140003400c0c2103242c440d5419060302e2000004d100010200e42442c011201c4415100c41403407030306004200c00c00802c0240c83c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 911134973 1250 911133723 911133731
    0x5070311040b121b01140d0504110306040b0403030f020c0601150201150f0e0c09060a0f120f020304140c09040312090b0c0a080f060a090b04020d0e0d080108030906090f12030a090504 80
    0xf00303550141d640000c4880b5840e541b01d00d0105c0e0036400c50002d01c3c000d0019503180290950000154504008080c0100c0c040c007501000c525091070020b0641d580d00d030200b64228014090800408030004050b81035a0f955400d03c221801207004c12401841010034032035811501c80300014078030742c6000d001e201b03485206840c031440342d4800e60480d041e80300322400035410003820400340c1070003482120300207410307401803418000440d150003484090700c00f604601c800881d0300206200c100240d0410007810b00d5240340c0030b090f0110b004000921007480091001d8103201c4020840300140d03a040d48103000082d40301100524900303002d0503d100d10f800200318680440c1501001c00c0300f50022401c0144a960300910b0603401500303108103d40980003102e04160025000c1c00300010003010303406007484601302e40001b0b1901807a00c1300001d04982040c0e10916440d00200050002c907204c1034101c8180c3c61042c0c41801e11111500042070100d0148030801c1203e020100e900b0721400d901800e0981160707403c603800c0c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 911136223 1250 911134973 911135023
    0x70b071418010c02032518050c12100b0a050904050709290c010c02012304031d03150f09240106031d0d0203030604061205070311040b12 60
    0x200d5188242451114241000c4480440070b600c50201d07003820610283c00d0f551002007000c8552204012120310501000048000340071803100f94000d0720b01c6002284050109081c14039500103d8451040340c2182030030000005840307034100c00c02000007031866015860703440c4140c481c010b0583c0c0148601c24840c03410321380814501441070412005640c485103001945500d400c2840100e02c850000e1403602090500044006200030322610382600740580001c59001c150404524180b5403600c1000341c0e105011041c40080b0f0307400748102042003440082c504100c820000081c0c81c8c01014015601080e940c8004c1003580c520301c04c0722902030482c40c021078440000c030508103060f00c0801e1149000c8448080d00401c0113502c29080f0100030001e0058402c032600c184011941440030b5042e000380982d20010074016542854030408001b0000d9540c24000b207001680c903240c4900452101500b80c501981511a0703558840d07001040b050300060100c440e204a04508940307840400c0c1c0500004032400042c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 911137473 1250 911136223 911136257
    0x30527040e0c0a05011d04060b0c16180b04060e04060e010c020307050a0206090f1503150a05060a0807020c0406030b0402030d020309091b1902030c010501051e0f060708070b07 77
    0x2e2010100024015010f042c10500112103400038041034070817192040b5001106a1550700c20000170b00a041c06007a0b844001e0018149002c5400e01c2d04060071205140820410060844d400102c400d90b000100300009801e0000c1c0107446030360020500c0003444000d10003045900c3c5c2c8027409510390300000b8800410602ca0980c1c0b00e00914001500581065200d81d00528006004020031000182442c0c601407104002c180c250003800085c44c401c4900000303000c01c618420305504130340395003101c111b440c0302d0a000108440340103640c42881403007024804144401c2c002c0c0448040e894014004000c0d003952170810b4412520144d8081e40a030203070026003194180b01000b182c4900c003014049000790f40f110f0700300300c40308103d8540e0200021001d1002460700a0391282e031500705a000e500440d01d5041103c901c41c2180c0041e03112901c101741c44401000d000f44269101601d1040413102c20810240785030100324284280c9e000100b5021000031000200249020024004c0907503507600c1d00001e50768680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 911138723 1250 911137473 911137483
    0x7140f0d0503070903020f0d06050c0c0c030c220608060702030904060e060a0b0d0603080703050a080934090f060303120e06010306090203010b03070f060e010203071e030527040e 78
    0x1c0d0000b50740304c942440541010211803218003c0a00913200c03c0085403113010484206460225480e90005000d5000c500100184800b194044018028101d202000111103c014034071414062843c0c040b81004110f51358044402800c1c100d042d60711516101d08000d4680e8000407070b6900c2030307140880218400074040c4566100d0903024141609031030034a12040c0442d0400c0c440401010784800001c800110250040c081c0f4031300c29203c45884030000403015001500081000c0c4056200d82d1550b0801d040701e00c403180d4010384074200e119100d4080c1c010108200555005811442d041c68200c854131161584500200d80c0280e591044c0300c00b101c01c50b402a502001d00c64a402d90060b00117001250080c2d00039034401c1d2004000003124121200070904000c0164850000c00301c84100811645d034012078948511340c424405149802c2d02a6600d0740d207615408260107040741902842000c040c06801261003103e42200b509150340d500c09844120650441c02143c0180e091005000001c007000175 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 911139973 1250 911138723 911138731
    0x151503100b03131410090b0103060b01081504020c160807060215091213030b190e0309030307110d0510060f150e040c0e0616020f0d0c0e04060207140f0d0503 69
    0x1c0d401403001c051351110314a0b0209940100c9040c010218100000640c6108210425200b509001c00661450404808a80c0003018550601501c50100211000034901c00042e452044a0058855005400c540d141244c6040c44142c0d10200030380c0841c0007100003919600f1900168200d03400d0081442c2c11116484080e1030070840d80d402443e118074a1281c0700c020b090005034580c0035000035a602c1d120704040f000141c4400d40c0101495070401000c602501540066007130807001545046030a0000c640d0b20b00c15807501601c08a01a440ba11266950511808400c0c0c0c11600700d46807407032080c005400826045c0f10300744400c4441c2c3c00004144410174070000703d840b5103444140f0113281010510015110180180d001c11030b40120400c0300303a4860f80581824508890001c0c03d0991500c14040301c0c11007002401c0c072440c2d00300ca07c80d0020301c03500c1c0c010080c1c80c041607450010b5108e51034050040e004d20382c4018080e000c0c402000c504000e001616040d41b2091004484280d20b0300403040e604c510080d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 911141223 1250 911139973 911139991
    0x90a090f0510051c050312150103060b0f12090703020909160602071d0a0e070f03061d03160303091a04050d0f050d0e0c0604090b1207060e09151503100b03 68
    0x450f0708141540641c03c4891142c003c0717003a02e140c010406d001c494502c02c1103c0c941d00c00c51228800da201c5513031500c91100500380e0b40a801c0d15001020410090500425508425914002c00094400042400791b040250f50242403503000f070030080440d0f5111f030000420101c6694441e140000c0081c40010a00c0032139180d001008502406800280700c7c50000402c2c10340f509444032856040c900c0100f0680740282203d0344210305841c2945800390540740c01d0743e038101c0303c288484288002d803040402110810107103001140000495490141d0191154140141000d00e00c1e5004030b8482c1c03191894940b280d4420001d58441c5400400d06841c2104440c070b40c2c90015134280410307160003c46500485407010540c044a80310340b02da10000c0e40340d50254100d00f606580f684203054050034560803020703019995102030038800d410040700920141074824104e1051005001141010300d00706200d4006010144c90294800b848808803002d5500a07128603404203451000002c005c03041c1000d880c0201000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 911142473 1250 911141223 911141239
    0x30d091404021b0a0501020a1d060a0804020a0306020c011b0206040f1115030103061a150d051305010212061905150a0201021209010501060906031b0311090a090f051005 74
    0x80601c0000e410092104030f01100009005550140c00c01410080c2071140c1c0c001359072804100401440e03034a1025161000c5032200780304204907070307440c0c00f40c405039100c038607210806544500008450142c10352008c0c001500c0054100301400d011341000d1040d40890100043c80b6199020403651880e0440340070345940405486a40050038150302c0140c84800101507442c00783c40300355107410b05d60080e442212910303683d0022212165200c1c0940c1e1207590b08480f140604140c5048440c0d00c0d115880e06070414581e10000151000506101c00c007130150004001c54580100e42c070980c0756090181ea54a20a940c6074102c548031068a0800d8029110301800b000848e501310b104011a5030440d03e00001955000e0104426403052128507610400b07040002142c5545003d00c00f5101841035040a81050304145803140b071000c5032002d117200e03802c9526001500c1d511002c00003045000d4560bc640e80003050290004504c14950400c1c240402094810002c0b07071952510003101000074840c0380d82041038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 911143723 1250 911142473 911142509
    0x15210b0130050c060d1410030c0605031b1b01060b04080709050c0c0a1a0606121f0e0705120606070203060105011b0605010312020d11100e0a0b040c05030d09 69
    0x107088400a05a40b1a004840300b2400c5800010f026801c400800c00300e180d65010180b00d91112002080d4100c04510f001e09000d0703045845004450340c50340900814070500201181d010800b903084840d40c40790b841c0034107480f46452130380121280350f10404401c4235070030302201103004200401100d044508980050285910385070f410307409400024036104a0300f1080c0b103800144a001d01803004014812010340c4000c0c0d244041100081b50050f14482c040d4505000c0e0304000700b54010070740c1d004a03c600050f0011080341c2c2ca004100c0a450300a40284d59804060181f100e4100740a03028009040340c0b08d41865542105002c458028240c01952542c072a07001003081b0750245042c12003c03150b504000c54596074548036001503407020381c42220003120904007030703041d181d050001c0e00305070f00c80b0301d8801c001e6882440500e60311204402802080d5641d0300410350240020461601c000d43c0c0404a4041440c09080c180f0075103400b0f21440b0301900034815001034480c4540c2c00c08003920100d00f001c00741401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 911144973 1250 911143723 911143799
    0x4050c0a1101090204060f0312030903020304050f03101401060e0102010e07050105070c170a03031a030a03080a150f052103040902030a09060911190501050d15210b01 73
    0x101410900c41c1555a40e10715a0260700c031800f07070304084c10404041020385803961808600c0c04154404d80c00415285c00340e400300103a8003100722801c407002142c050109041c20700000c2d040050000d000034445180c485480c4030a8010368a840c125916030b220215960029401a421394020340d01031030b01034212807014043c81d802031020301040c3d4000c07040800401d446443c044070402c1201300031815540100342d40c100301a4580181d0500860011a4081d03126440020a6599810b008001d0900c0b03511400209410320580c04003c54005241c0c8118466940e8600350800040718010075000742e041618034800800010010040742d49013000035032a091810b5460360094001400d6054030a44490041c80842c1e5503024805280d4000d20088000c403181c401001002c81240c650741501c4100c01008014030ba0b00001074413218000050086640b4011200000d00b51403da0031440d02d43d1030b0542c07141c61030400c40c6249200c55205d8034402ca480d907240c081e1701d0124008006400b600f1040c03c50b00d1900c00d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 911146223 1250 911144973 911144987
    0x60105190e190315020f4e040b0c0d022a0d0219050a0f050c0a05090108070306050a090210020303160203030c0a261f052437030b04050c0a 61
    0x42c0301ea115800c211a2051000850a181e200901000200c0c1505469580b60300303803404043e00000c8451f49124500745100c6004030b00104050146807290001684840c2e00e0702c1110a60b51400b00d08560700e18002d1034030081c01501070b4440e58500c030309401c4031481920000c4c03080c2100010340c00410f01c2181c1c955511003c001a204200c0e8180500d20300080080d0003040d42c2c031080c0307120b40e0290002601d00ea0900c00046030b1540001d11581c1941c004100d003c034003150300c2043d01c1c0c20000201d00c5d6038030003503c04084d04036030100039027281040d0892103c040d40070000d10b0107032010850311205210000000c0765030780800e44465500c03c808125044000e4082c4119142c4620780800354606e01c107410000d50200e000846a8840790081c0081c1c4050301c0040c58000341c0a03040031100440c0c000300440c2c85d04910a042148203071503800000740c502e0f0503407070845035403146010030103000c41100104c00c91000c0300710789110400c007080c1808500601845c0c036000d0030744904a182412802c1c031138040e2040b20380b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 911147473 1250 911146223 911146237
    0x3050d0501140f1f0309030c0c0b0a0815010813150c020d0f02060c030402040510090c02010b01030e0d080a021e0c1b0d08030f060105190e19031502 65
    0x44501002486821241409000d00810301c4550900441c041034040c40a094021941d0520502003050091981261080300b111001e00c1454001807044a83c03600307444003200408050304001d5130010010b201c888582c000e2103c00104e81d13400e2020303141d0410100f404144141d109012418003000603030840e200304102560a0b010714440fa210b40d1101004000702c40e8407180503001a00300803a903100b143e80101052603400303424401400103140c442270403801400040d00c001e10031a1100d02040350810740c00380c10405050350030400c2290048290019000304541e0400320301207410843c01d0440c405001c601d1281d014583d40300c420003541c403601500000e50106c001d0341c5042251401d0b40701e4500841e405842d11002c607600405062607000d07000c2d0a0682c01d0364149206902072540303500020002800d0f6038008504040d1050183c80c0c900060340c49010341001c0300850348140c54501c040c80c1d8010804908140180c40161401500e100c821000a0007408080c1c00300100c800b0104080840754018041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 911148723 1250 911147473 911147477
    0x2060417120c0c040b010c0b0a0603020906060f030c0901050906031006030b060306010518030f1207062a0f0309120507020f04050610110114010f031a07090b03190609060e1f030f03 79
    0x7112507607910b000b423414090790040c4030103a6848043c811400c0000001d5004481122014104115030301011020312000704012070118001c40d00001e164050b10644500b1000200309548915080314240d108425a200d0a000282407418507081c2c0d0420104030390280c40185d54552611040300e07001c1c140d0004041955400d4420001903030051441482a09030032040c100741c2035600c5041d400e066040c0e40446021442c81900c940c522000e841500c4c400f148a1100d80c00c14409180303550704168000c1c494440c000d400d0310610310200e44015402001080c540f4070884104c0303c032402c00c405002c201c0303078101d0300c0c15006480c40710454800c40c05803042c008020701050000c22001c149050810101600713a020b4404030445202c01c8c401c000713038028442c9003c8443d10784141c081c502510001c1c8280e07518440d5145900380000070441010000c1500e6203019002082070186590b500503002c02010360f442008080c2440c1c0c004581908642c007251032402c06100c0010703c0c140d04548410b12009070803001101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 911149973 1250 911148723 911148737
    0x213030c060e010206060a08060609090307150203010510080108030901120e0a050312010e15100e09150f03070b09190306090605060a3503040302060417120c0c040b01 73
    0x140a03440d128016010a589601003029980000b9141c80f1016040d40d10444c201401407004150000300543d0201048803640b425480d1a0344441c00c40c800c5074070103000520901581c51041001c1c0d00110704a0b1030541c0c485004140111040340e0092003801440308641042085005544c8070341e80c04c40d20040d50f4000001c0d0090481d5560386000f0708030744121210f4101090300c1501c1100010384070300421202d80051101e1400c406007140c010380d0803000320300c18032501012961170f920039440020900405403042ca091b080c03580c0c421825803003511955108080402d00810541008101c160464000116903030030f254240d0100203905001c240b1288945407a01c0001010412601400c100d040c002c180000e07640c100b940920900c500150840c40d4204c1a608600383d145c0c20b1201c003400e1040d0004421b00c800b041400728503056108640c0081d52042000c10046025540f2121201c2010b04a0045441e07408a003030b4560355502030004203070070303d401c510614511401d02750400b41d101801403600c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 911151079 1106 911149973 911149979
    0xb031008030d05040c0e100510030b0918060c0c070306110c120408060a14040323040305073f03050409090b090105060f0a05010318171305060a0c03030213 68
    0x2070080a41c20040f80e00d482c440d500c0840c92f03501c0140f000c28641040708400c10f4210520252480f01d000700703004904000441022108440c3e071880181005034651784071030004002d19120800303070b4602049100e001c030005212108050641c10700c2c441c1c680e400c2005c01c03461310f00011b10b03d0603050328080703c84003030f5041515107030b500541c0761401e181c0585810010b030081640c2030a00840080010a0110421901080c40000d6661079403440750388450b0072000055248801d8009042c2e10f5038451400c51190035141c80c20a818042d0411034601030b62417080e102150303050031050760740307030f0b0504e050101c10300080c05160b800401c00c5030018000080e6600080c1d2880140c40b4071818196904482c1c00381c2804800c01010345508405480d4900c45a10300742c0740e441e4040251503002003900d80c000b0075a8500b03e01a00c401003c9c0d51f8411a100c1c1441d5410b400a6200f03400301d80c80808514000 = true := by decide +kernel

theorem cover : BRFrame.Cov 910971223 911151079 := by
  have h0 := BRFrame.cov_init 910971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910971223 ≤ n) (h2 : n < 911151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
