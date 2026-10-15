-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4971
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:31.992458+00:00
-- url     : https://prove2.me/submissions/1aac6f54-bfa2-461c-95fc-d91e0447e834

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 893884892 ≤ n < 894064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 893886142 1250 893884892 893884897
    0x3a0b040807020a051021090c030212150a0c0e04020a1b2612010902040f06050307050d0606021b03010b03120306030f120d0b0402030c090409060e2d12 66
    0x240d011039a55141c03066880843ca4004254100c0b40c0e1003480b02c040a52260f07030120313280482000c0c401c280340d045240d00c080c440032039403080c40203003501700404010300c090701302042d03182c1071400f48000b1030b15145044080380c0000c200a4031003428103502c414000340ba9513480040421165000c0360300b140741c60940100903000c40c0c440001d80c01c644151841410901101224900078030b0b5102c410020f40c03080c180e84241c00d65116005001021001c0700010503010101c0c420389081c3ca101c0705e07131031403008e0808009582c00d410041582c010130904008030100b0101c40d01403080141015001040034003c0c0c100c41d1603621611620036402685005002c000c3c5940c0010725170320709288080d0865403034540201003801c00c0460380784031a10303100e5403803682c1c112048140145080a040442040381031451020407059200603100342c03205120a200c01c03401c41c40d00b94400d8104520410002070102c800c820030505009040003195090449c07604005c90750040400c1c000e00031b9884030082c04580b55400c01c90303612070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 893887392 1250 893886142 893886151
    0x301050f0405060d020402030c07020901120c06081801090c083c190506011502010e10050903070606142803030f0207080610051f140d02093a0b 63
    0x4a0300d41d0b000c51450385442c890082800c3e0098029075580c41e2541c2c80c0d5605901015003240035150060001400d001c4580ca0040e42d82d9005540800340e907e00402200ea500c00540f1302800c4075590707140054401c0c0244034450000303104400303441034a0b00d8201d030603041c03041e55040a48440c40d0b9505811040c40c200c44454134a03009030340901d0350104c9044010780360070f81032140416a803000320007a00c140076000865034100d41801c03032030701001da82d1910101d09903421506003194030392050010b155428080d03002643d03c010401c048a00700700494407500180c4005905c0001900c095881000b00ea082180d20402c6014400c4000559450300e4102c2c0c0440700480c2c44041c00300007181811925003403083c4081d1004102901c1203822600b000700000e070301440e9611800c1d21804590302481c0449010703035141d0402a06588901e47d240c1c103000c14000040e03000045010150b03a00300050704e0540d0369402100300a9428140e29280c0d00100a41c60070f1103c6040074084070b41e00b0b030341a800001401541e000c1d41c003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 893888642 1250 893887392 893887399
    0x6030c0509161101060302090f01051f05031513020304140616020a08030a090803193e1b0f0c0a03050d031104030804080105040605010609050607081b01060f030c09020301050f 77
    0xb10f0990412150042c4156000290f20038118010301450010700102181a0390f0100e8a01c022400f0340e1648283c518000d154400116a040c00059083c80921400c02c2e050713040039258040d8000d01004c840700b06c0c0e1040703c0c120380e0a0f900007000d1140210802140364044148039001001038640314000e0354407240720b00000c0c20904000b0004007520101d40104034007d42c42020142c590502032007100a020f0b25000e01d042c0035107041e0f00c40c1c0f040805889409034082102407480001c0705140410030161010300485d00101604010301100b00c03528240545561024101030311460305218480b17800d202c0402542c912400301e4020902c0400d00104032500c2d19001800d00103001e8083c594010820f0046500c0507014160204000543d0301c410f40119102d03500c6900100126a2605025124032540303000382d5030080340a10040000441983c000c1c000c408069004081ca00c5507091840d0030b45600c1c1e00b0403580580f1541c400c00030000300322045c0024002075802542150304141c0031540010304203101911 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 893889892 1250 893888642 893888657
    0x9010207031d21160b030108100b060904090501091202010c02160f0e090c100c021c150f0f06120b09010b010c020f0607050a0605060a08120a030914030403030306030c050916 76
    0xf1940b001c108800d449030342e0f0b0f1041d0301d07501e1381c440400200380c00900c0307009024083c41d00b00d004030100c40c2c03084a41e060f00013031105080c05004000e10000300301c020805c03103080d945c810354203000c07c18850a41c821603841c2d07070022684c034004100083c104507060030344480b00d402525080c403170744030103c80e9202940c0e0701c101c0040c03180e43d80354401d51622109841e03003a0070110340e07041000c4690384641e08042c180d0003a03609182c81e4188000301c1141d5408481d001e442c400308420b0200b061075041d000f200180d00c4036030022803070f2442000c3c1d8004440c07050740502d441d0658044144200221701c42c4040d402010300c0000c0061105100010300003525580000b03111780040503140f89aa591001910411600306045481d03031070640c42c0c400024102030328840c7c820b042a4000044c0b41800080b10416000c0380b80702d460410000c11000d034042d009002c001c0752032400c905001d03889a9800c10240004600a40d800301c2d05e02c1c514200803d9160954000328092411001000100091050b01c5049069030707107018207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 893891142 1250 893889892 893889949
    0x51509060f2205070519020309010e150903010e1b09012d150f030609061a0f04050d200904020d030f12020a0e09010504150b13050909010207031d 64
    0x30b000b04024111030b00307640f42106108545500502500b100c014038199501d0001e50740b58182c1c1e0b41c0c00351205032800038114490184407420031070f01d0f24000c062000109400e01e490f603000a800c0da0070f00c43c1003074440e51200d072034020f00c1e03514600e100441d08004c0d2403140444d41005180c006400078001d60503503034184600407960651400160000410f0507120141440b40a0900204000e400d292101c0020b0b040c8000440c2d40703046441002d00b25014000c0c2101021100c0141c2419034200d602c440c845188103010024407901d480c9005200180f0440780700010b1600009180442083c1c84a614000d0007070700d04000041e1070b440b90003590687c16080140c0d158600c582c00b00c1ea01c02e0304002c041d26882c004102402c0460b005441c00c0400b0504079030304c001e60384e00c2d0424041210650080d8241d40c0c032100c44104100400c00d8018110000c01580410741243c079140415144241510310f00300681d40010942d050591110b0400920030014042c0c001441c2041c0c00a447c40700c135135200400481c2d4880c2c110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 893892392 1250 893891142 893891179
    0xf1d0610050d12211a040e19050a1a01094a010606120f15030213020702041401091b0509040f0605091f08030906070f1104050a051509060f 61
    0x191040300e000c2407001513501c10411054003500385000d0f1004021072010180310b4924150090844207000380c1c0c01840d09805200845141411810095610b0701a2444a5011038401582c8003a4031014014846c655458000043c0440e86c4c0ca00b04040c0103041d46000400306076151940000302c0c02e82a4050a0001d007004000200c1a5041000c02c855840c0550004126402c010152074444482c030003000440210840d8900b65100391030072804480d403036102440140741145840790f24a841d8140141403500325400324045a140b40c01e40d9100b0303185a001003007284200d004155010440101e03105400f040c1d4071018095000e840c0f06503101e5034035841e01c0c18070802103502000c02000300402c01e00e06420580c82c91160114080000414020800300105101e000001203401071040039280303614141d1280c0751142482d191440c100c801e00041e40c10f0350f545942e10b010791400b81c42c41000009503810701da824000c40c5d01240000380c0c0141d02440401440759980c001001e41c0040c140c41d00b041d19110704100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 893893642 1250 893892392 893892407
    0xc1002040b190e1f0f0c020f15120a061a07020109180902040615110d0e040c110604200102150a02070f020d0503040509060a050303030a0e010f1d0610050d12 69
    0x1160b00003251a001c04c41195003000c201042c03ca041d122501419020141160760721803c0d02d01940181601d60300d1815410300101004a0103c07c08000b400c1090f40c600c100c0d0015001c0c2c60309020144c49610602001d0b040d020a810000e202e00c1100b0314109840d8006000d00001d4419101e0348604240056080f04042d0005004160300400400059441d840c4040003004000300403400161415042c24280000080f4510003506549510100c803040030b0820002e0708800500000b0440c032407034500060f030002c112480c025840f410f40440c0d0030490820202060640161301411580718886050041110951040d001212108007595500342e50418100e980c110340300c000c1d001103200314007506220010018200780c4004a4007808d03a611a00100304c18000f030350251a034190410004918804075550190380c2c080e4900001007410700d204404841103420800b50388040c0800e52004818012040c070900f54064213030201c811030301e4289008140c806900910052842d40d60214200c840d81c0120f10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 893894892 1250 893893642 893893667
    0x30c01020f031b0c06010b0903070321020607140706090804030813080106051e0409260c10020c0d050f130f03060e01050f06011803170c1002040b19 65
    0x2555501c842070032031012548225282d990015401c160600503201d41d408551000c40c0c014020451a42080e0b036402c0107500200c0c4150307040c410f40100200045050039040004c1c0030b0918a00e44204070040e0290038040010185e0003000640068401a10040d0080d81c008a4005000203020806843e000300b0500c9a600042c0c603018010036540641d8048011810517900085d0003882095600d80500c020f0744410700c01403404801001401c1c14a091562001c401c4038020580b1510400032041c450b00030000742d49c0c4a03581c07540001802031584808000741100d50700000401c620b491221182c80f61241803c256481c10000f0000b61501000703103130000c0e00c00c5400c090135405100781d60740340b0410031203c05100c103ca840d07082101407079810506114442c4603201a900b0070009513180d50044541c0d400075040e44e138a84100329400320110700c3d40003020800e00c4072031185a80d510791904042d0b1410225240700440070740100700a12040389000261400c9004000c006c14503031a0884095521190601 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 893896142 1250 893894892 893894917
    0x1180611010f0e03210702070501030b0d061d0c0d11040509120406032013170717100e0613080a030e010c020c1314010513090506090a02010801090204030b0f040503 72
    0x70820f00060040014614007a908650000032a00000d05440b12a011214400560058030081000d94001e40002c5802000103103400001c12540e030703840007111b5112014246c4010301c0c81c041e010302c1c01c04008245401600321600c4603c01030990b15283e022080900c054080d0f03490b0004104030020411a8240d4006d031884070545403502c0d49801001407407405407641011072540d0f80841741d02252000c444003280900e142d107004605010407400721040050079460740c0e100712600001c1440c882e039400316840d15041c0241003202c031000c545000f6a907a40501c40002d800507030501400a8400000c40e144540c0101c1035074413034125000590060048900d810308a50920051134503840c0d020032171380442101100c1a211440c0c83d01104400c0310300d8402e8202070050b144006001c107240c180c9005002d1641004040703140b00c0c1e84d90b12682080c000340c070410440c0d03001010000866800c2001e0a000d01a14141142014a1a02c89201401c0701420aa0582020b880844c040c0b00040c01200c6040180c0da = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 893897392 1250 893896142 893896151
    0x90e010e0d1e031b03090c151e020f060a180b0406050a0510050109060809070302060f03040501050603060f06091f06020705011107050f0913060603080c010b01180611010f 75
    0x300c0c0548900150011545003001000d829070030a4003074070400030f060307092280014000c51305038010303070041001c3e0101391000020740314005101900b007818115655600c0c0d0301e07a4220506034602d5203c0c003d5545100e03040d50000421000a01d000141f11030b03018030005000324080301ca10a016100b8a104c050192940446004010510000741c11440c091350161504001c2c41d41ca920820b1020b0a007030081034000b9080c2c1c13100b085214410741c035070350b00412100141c0342d1791f90381ca600180003a400f490b40d0b824411404000c00090010a10030541c1c45207064014103002d20303041e400e04440c00030003002d0300d12500d10800452410052824030306030301c84005c42035180c02c40d20703210040d507a039015100c5c141c0012608a208420b1190110b048412140041c00525400e4484410000300c6000182201c0810910baa28070700491702c24001c0c20001c50203070310b4035a0b40c1c48801c0e4480307095594020200781403042080b250148084d010207000300300c841521b042c495420340c410f40e190143c101610130703209003401c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 893898642 1250 893897392 893897413
    0x11d0d1208060a0e0a0e030f03040c030b13080403140c0405190c02241819061a030a081b06010f050901050a08070e0c16050a0c0915090e010e 62
    0x305810510348150540780c240c002d581d44001c00c401d400141c015059000450b20109888610642082011a400106403820103601000c801480e400c211015140075000420800c10f000034007010760340100d10708100c0740882a039030305c0e04d443c01c4c4107603c0020704c1524200c6941c441320070280036403506c01000070710600440c1007041e22518003a0040034655541880c10000035801c07800002c9a20003118143d03150003917003010342d204842e0b441004045200408070050300b00c03444001400400e088503008402071034000203a043c4a0200c0e8000c41c0d50315040380c0a42c0710711085607000a544501141e1160744c8940e500e4162000380d00590f03443c4850401031080c0f00c0042000180380101c0f40c143c0d1b80a440a05441c4c0e42c44042001d8524644a01c28680e0000f44080c8001c05211030171961010100c0460b501c1c140d444036140e00032900a030b505803502c0d0006c1000808010000c0741aa0003400c01e0b80f001d022901d0b441c0c4d4016400103141c4038822100755110003001010400b1740100d900710403c441541c040a01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893899892 1250 893898642 893898653
    0xb091225120c02030d091a03060a0e0103060c0801061b02090402040f090b16030209060a030b0120010b010807052704061a030702150114100909151e06020c011d0d 71
    0x40c0b584128428040d501131100c1040c800e80800f4100d807170107240c00001821905000060303034005050581c2000b00301c4004180c04661130300350341c0250b00c20200001c400084c41d8004000c168181c0142d01048523005130310006500c0b031680e03694040c3c0c04484000d1142c480f880050000c0c401540a164890700f0074454a05000c03204000c0f62292403030014a08031290f201c0011401c038460141c1e1182c0c401d200384802c054052096214146500041c1440d81d500a0b264080c0c9a9030361780d0040c4080282e44400301d40d229035900003030341c54000c0c0d2242000c5042c402013a0b602006844056861140c0b0350050601d408540d0391608002c0080030313240e070301d180400842d510000d41e030707401102c0b60710151003264080840c40c80d1a00981c0e04131034008042e051340198190422543d4154041118200100304102259640c2d96100b481c0302054002c003404a1a8a04004041c00840a500d40c4494841c04002003084c80d070081400c555030202480c10700811265140400c0d6640b403d151255004154460450100007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893901142 1250 893899892 893899907
    0xc03061302120a0c180b06030f06010318080a030c090f03030206010e0f060d170d0510050307240c03090902070c090b040c1d2106040b09122512 63
    0x14001e8680c0020000e00074031142da80c0b2640300004004541c1c4d550200300d00b04100441102500d0329203070108840b0a00d01c00141c45030410f603420078101c81801c1c01d11400c0e40e0144038070412800040c01041844e11561640c0341540103c0e90f0301014980c4070402042510300c01d00c40030010382440d02e100c210b4551a400d000359202c0d000d01a60014a07d41e5020900440c142d00c1c11074410301c0300a240303503901619551030b00c01251a44000e03c84000c02031216941407400307400b0b080e00c100d07001b80ba5100e0051810741014030b003840070352142c81036040009408030782c0c0700b60031042e62184000d4104116102d100745022521031400d039102c140d5a900c049442010845440418011100e100c002444101e240c0720422041310382c1c000020012880c50205101d400c01685400e4810702d000030f0070503d00c903482450748081b04002102440302c603007003c3c0400041003030000c440e0740c2118096004140000000c1c02010383c0b403041d0480d821001c01764244007511032844211a85006d5840004c500b00c2581401d805407002d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893902392 1250 893901142 893901181
    0xd0c080303090705030a1106210f0901050601050f0306040c0e031002040f06030605030a020f121207060c030608060708040620091525020a08030a021c020d0c060e0c0306 74
    0x2802503c0000415280c00541c200340315410195820f0440c103044100b003840c1d80030f11003100300020300c0d1a00680d2424280825441000d0850b8103102500c1e01d0414103084034401810326041c0041407294404a4521030141c0344e1000081c0c0e00090310a0f0903d4007a1401095000340035810f00c10b00f982c0c1c0c0c44410554024004035100f000180c1d0241d505d4500c25016144107005131609079001c0311000c405880c060f00405a101005030401c124044120141400c0c40e00b00752100284000c00561071041250621a64100b0411480c0800c401410304000c15218400500035904016002000c10f0907c001c0d5803103c0c08504100c00c0b0450483c0c41c0050b41c0381e0603082003d10904c0340c19248548104106d248080310168490740000b00d0711181d0300344500004a040e020142c5c0c0291001340c0100c3d603201c0400c0100355850b550703001000107002c0f0740003001e03034401c114008108540264082000300740c0c002607417046440d4008004181c50041c0055240307090002d0b000650b0500c508070520414000007200301192 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893903642 1250 893902392 893902411
    0x7150c051b030f03070e0406050a0b1c0b0612190513230d050f07050102040f0f0b07021518100503061203040806041209080703060b130902090408090d0c080303 70
    0x5102003020741e079220b019030303249081011002c20000e400503200f941c0065801030018400207106845038040781e02c03140c1d01d800a580d80703880000c0c1004a070000d50300340841400912410b01c040302c0310f01d01240c4680107980502c3c0308050303410b012541101100c203545c10108003416040286150000d8441b20f842c071040710a4540302001032056205d2480300c10081082e003034190050402070300304002100e85910000c100084a50305109840c0060003e00080c00141001d04062000c641409000a80c1041c0c40d4410041090700300084030040c0c407000d0f02d40d200520010012511144052425140b54122609403035014103080c084001079600940075501521050310300d80081c2e0791008c0104d035039115a0007a0780c407036071045c400180040c1250b005200c00c842c3d1460050304165843c541145000100c2d0803c44070b0613140c1141289600346103620400050750000180b15210441e00800c2d1084070180003d4100d00c8000307050102500c9031511604055802914115019650700b0f00b19243c1d00140d502c00c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893904892 1250 893903642 893903677
    0x30a02040b01121e0e150403180803272403040f0b07171819170a0c050c0a120f061e0b090a09170c07121103010b0114090607150c05 58
    0x1805400155510302403102890f0b11b11261a251000e6469181e0614541c0489115400c042002c50062024003081105054608880c45103c3c1c1ca40043e040d40403d484d0040400c04040240f5160ba0b80e111420b0901d45549030383d03261203900b0400d0240b8291000501011381c0e91042c0000c03aa03200c900b6004902e0786101e0f1020686400d0107100c0150520b500054040e0b12414170300c0281c0780500c3c400c8030040e120f40600d40384040096403660b01d1340c01008002c0301041e10035881c0c1c01442410b22031260021421940d1710304190074082e04035400110704002a01c071400081c2c4040405c840c940c0101980c508a081444400a00e0310342c070f4003c1c00e01da44401740903007064070207e0f141032502d005403043c5c40d610040b460a658004c480760702c00e44e004241d0329040c40c41503407000619010611540f8480d940240d60141c621008401850300396400006020b04100341c100b0040d04045002c0d080d110340707003001c03114075564200605122421614091441c501c9924000c0c2c44062603800030020303c5802070102400f207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893906142 1250 893904892 893904911
    0x7050a0b030a0606260c0904050117070e0106080703020309010b061603030b030c06091201092123030a09060209090f0f070302042303011b05041d06030a02040b01121e 73
    0x903400c1c0740052901d08a50505d00070b481e8004aa5064198400a0b0f244400d00f0640b05100203000d030380b0283d2045d9204564000b801508003001e00c403143c00b0f0400c0d40290221075240401c021302c602001031800c810182e0102c04188000741c01c0d000079403442c80c020082c03901c03107a99000d020340c840382d114002c0b00420f18049442c12682400f003801900b00e007004007400d090020031014002c40d8030000c3e0000c525950303280c0207400007034246440d5136014a140e030340c2c1151125030201b0251040b00c940d807254403840003040356080d000d24000f040342e6010f2101000442c0000e4a85808400390003841c0e00305500018880070400340000311040c062140c03120310a81d9036541c41d2400154220312481c040c4100c816120384210341844035100c0300c00c600400c0900006468030144079058104401c40b04c6000004100141c100072003110270030000304500001d40d1080c91b03400d205000070740d01d56400e90020701941e220b082d0400d550303001d94100c030341017200c480302030201140c481460f0211410304007441c0c43c4149007600d040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893907392 1250 893906142 893906147
    0x801060f080a06020a09030b0703020d14090601060e04020f0301080309242b09120f021612030219060207050106150c11121f05180604120207050a0b030a0606 69
    0x41190781000260110b000d15072034840180d0300200070b00c0c0a0103e985c40010020703120400d114803c0460b40e40058403240241003d000b698190707101c1d81c121810103800c1c0000158007003900390460f40942001c41c01a400900460064020481043c1e02c01c070f0080000244242c0220003810020000c88404943c02500c003681010b10012250f6641420814020002000b45440500c901e5100c000343e80000011003003d03201c2544c2c104c240c2242c4204a08a95505298000c080d0418102503800600460450040c20400240180c42004203038192410380505041c001e210074908210f44100c0c9031807101260500300c0295001d001d00300d0741d0391710313140c00000c2d10b146e1801c01c3c01071070078507680e40705030b0301d800e17480b038406040c04100d142d030307004803031264101e112982004000d91010341602346080064140c00c41d4800c49400401c01c81c00030010344402301c184507021a0103940250711044010503000b0038a8124a4485103802541c1c01c034400c0312001c200820000c01461184138032103003c1c0003860b2181c104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893908642 1250 893907392 893907419
    0x10e15040c0504060803220b0f0a030e0c060a030f060f030506010e0901200702030c1c020301140702370303061e060f0c0305090603161e1211070606030c080106 70
    0x18640141c000384001d40305064101c801030750601c0c0550b201f0601603100c03054100f40d80e01220009810090000d021004230341c05010b001c2402c000307031016084901d206404916507104400e0003c082564802800300c11048a600c11310240907c0d4003040581c03502c80c500a680d4500c02c0c0600d11448a12800141c8246c00c14014140c114000c44801030381480d8603050b002803900081000c980c1401240c0041d461511017845018403145a1622a07e5101c160b005050840e80c2480c8a020307036049010401c044650000754000c3d0070400ca100d0f0f0703114808007558140c00ca40640e400030406003d40e021000602d68160043c00650300e0000f075849030700c01e903010041480320b100e100d200b02280980014070b8515003d00380b00ba0000c1d000e07090481c5400c019100158a65008840d44050b111988500160b256440740c13800c0c0035140b91031507212880b148100003500580c10f01d48031811403030f00c44044000317031100b00056450300c41d0700030414007010f91030386451080c110941c06903903070941c6403c03000a0710740c4e801040f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893909892 1250 893908642 893908649
    0x509070501020f0a1208070c240b0f03072d091a09040b07081509180d08070509040209060d091128031401151e06050f030f0405010e15040c050406 64
    0x1d170100355100e941d600360b84c00000180488140041300e0a0034010401000c580302c20302c925201090000352440710b00b54120341222803410700500324048103101039200002c0240660b4491400d05516120451450250b60300b60b2100044d808001d003000507403443e00c2c2c2c1000036044800d0070040080d110703030414003080e0041210007414810307103c07011510647c01082820307044141045604d84400b04c3c45c021920b00c260135501001d8100c0da14080c20304180051248519a410700d14015155040501d001070141c05000381e954032459000401e031000e9a03a0ba01120380c002707898001071084000b1801c04c0100c0e01c54200c01140554000c070b00d40d1180201d85e012610488204e4113104480305c5c01d688441000341307032459648140b503503100c080524006034004144010000c1e030101c1114003112805084c8490403660001007488070512800d00d1138420034040d2a4044d0782c2c0c0e01040300d142d641c3e09115000d0040b02e031200780300b4010b008100c2d100200072541d4034030407030051400b9058940c1e41d0042c402100e04610 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893911142 1250 893909892 893909903
    0x902030610030504031803050307050f01021c0e0a0c242307060b0a0b0415020a030f0806031f0e1b0105040512030c010c0306140409030813150509070501020f0a 70
    0xe070460741e0360b80203600041c1c0060083c9040c03199080d0310700c0c80100d4400c2940080d10994004103035142041000c00c8031042002012000754101001d907041c0d8040115095014000d15448000300e13130f040501003040000a40d081141907810740d03a100808028003a040c9180142103030088400035020b8000c200840d1052110005810010240090403130f25270461402108e0441e12581908225503e01c00103070042c001c411803042e0b03980d00e803105110851151203400030664119928072008203810480040702d40c4118181040c0d40d80e0b41c540044d09200744006886a07040c1c1c242c81441e4203019540c060710481ca4030008444260000c5803c42e1040603184080c50700044003000300740300c5801c216a0449000300000100c82c03c1c06100c08000d402e581c644103540c400a80d84040400c4500d40000b54a00600c0301a2010460640b940e1030050031036800902c1d0200d038508118082c010003070303840002c501140c0c81c01400c1106041c00c1c0f583c603480f210244511401072040410b420044400400e41007031856101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893912392 1250 893911142 893911159
    0x2803050f22120302031905090a150e0105010b09040605010201110706020f0c0a0f060b090906040308130807060c0e0105031303080601030e0a0b0103021f080a0902150c150109020306 79
    0xc541105040700120300440311140420700031000600301640e0103a05600760302c0240c1c80740307807524140c09070405c2020300c0400c06003081d082c410301c0d00f004600c080310150481210000c0070201c02c2d86030003401e40034158084a620b82400002c40c10703054400b078644c13040c0440301031080d03a0340c0d00012400c1c0c400c020701106004d0010054240001d03000c2c0c1c01000d00c03180020b81281482d900514480c05d02117581e5003600c07220401d0340c40400300000f600c01d030143d4440440d0034001c2402c05e41d0a866030303800300910003400d012a060105a4900044a00c1c0c031300e50360b101a81c16074400c0649003203800b9025140e10500410502c80300484507600640a0364825076a44190368002076494038100c65040d0081c05040c14135070782d9201c2c980f4440041c0281030b9054041c2c0c4503062194914414000c8656140c690031065002848140e40740320390145c0019040100b01001203029111800011031041810044070501000040c4800041201207101c09800d440c0c040c90421680c7d95001d040c09034442180c0041d80540c90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893913642 1250 893912392 893912401
    0xc0a050601290d1a030d120c0c030e01080a110d150e01080307060b1306030f11030c10031131080309060d090c080303090705130b030715050f2803050f 66
    0x1c0e032124407522907242c2c940c4021300350180441c1c1400011044c1000044806902c1070700241f00c0d015250b20ba407010302d001c0015501c1031320001d02e400091a8142c0c100401c100109901000d140c0041c08010b810254143e03540c503040d007140009000c0c910340c0b4001c400e0704640000707050720700b0305c8200d04840004000e1441c040483e40d4005c024410340036455070003951a20705602551701c0f84100e4010790301c00d01c0b40c01c200c400c0c1428002c0545007060b0310140310390b1280b04149980e46541030030b0f125203141414042001110311090005270702410044400b0042e145000340c0c16000340160720200d03202030042154209441741710b00d903140d00c10074540d83e03040300c410890241c5401141d030066001c9401444c00408241e2210302050035035005440f0180d240c2c0c008941807000d46820000314182c06919182005040051008641c48030039900c00d09001c07400c6002d8820005000300100c44803100d800e103d040d543c0761441f0a4101d00004007080b10f54440862404443d0706000b480340a001d000c48050502c0e4035500c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893914892 1250 893913642 893913667
    0xf06060316030b091204030303020909090106180207020409020301020f07120507080708030606090a18140112030e19060c0b0115090905071106010323150f04080c0a05060129 76
    0x280011251740b0400c51819907400a6a02420240d48070b40d90140c0d403680300300100b00d17000001601c03a031040d9141502c10000400658036440280c241c941d0302589908450000600800003207202a4040d4000100c540d0308841040042c45003038440c090312610304007101e6085601c1c1c02078060040c041502040340c60b0100d24844c003d9039020000070910342c0780c001c090b070208000c0d9605511848091140701c0d050000c02981d402005034502d01d0405404066250180201c0f034519140c0000e800d00c81c1281806005454407026840114040802c4440455665800030700c200355104081e00c030205018008901c46909a095038440c280c0b540d162640107085c000d03440d0081030060140028014200c8891080e40028007110303000b0360180301104400904600e40300d0bc503042004c2c1d41d100c150420324000c0c0b003070111a000703681c1045480c606180c4607683ea00d0420309501c40d81103241450320403c004034080000000340941611000d202c11031184460000041440c0040b0281c40b0041d072042c08515005175 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893916142 1250 893914892 893914913
    0x6020a03050d27150c0c1115181305160e0307050a0303030e06011403060a0b012d020f01050601020705010e0a26070e160c0515090f0606031603 63
    0x482d90900041c50024207800100040c5180300c0e07003800c0d124103146040a010680481c45000018a2401e000459030f404009241d403c0c8503030002c003492510b486001c910703204c3c2062000404403103221180c0e941002d07200d81c05010004005135103e046d03214a04422008940200d40c0030303500e2080c0c4401e0a400500341a01c00c980c1108020340c00d0b115410002506503aaa40c0308402075009440c0050802d0a4440712801c0034016008140d00405907010400c1c262400168107500400c00c4c480004e10207402001242c440114000c0e0142c001001807525103012400da55045071070300980c003151520404540c840c2d0980744102c0342c0c10f0141e00f00364000c100ca94000c1080000c4044010315010340e50361103075003940c0c3c0a488040e4503c01c0004454008103104410003d80019010340c1444100b140740249080580701004140c48040005407000c010400c0410008030820618221600d4501c1c6000f82540313913683c41a20503880e19214641c04a8000c0c1408104031304030301040c1070020103803030a40d280c6080c0e22 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893917392 1250 893916142 893916157
    0xa05040b0f04051e010b0306150d090c060f030f0e0c13090803090d0906090b09060714060123150a030203090708061302040501060206071d01170c0409051006020a0305 73
    0x4840d4440c1d526440c1c0c1c41c0c0c411507101c1c484c04400d84100c603030712003038541486a050300200c581d10010018481036681c0e1000e82100380f081c0c5100181d2350081c010040700901f80040005221143d0340002003184c7e504021550803400c040d43d404c02120b010030702d80c203054800450074050035400008801080d0300b0501c1e02011210402d00003c500c40110b80e5518209030b10031107850348aa000415810441036124000fa0000c00d0030b841e00c03e0005d41040c4d82041d440c4900c8950324482e0000141c004e007000542c40c418000012041e060b510190781d940c0401d00a008402a42c0540c4034024898103010701e4041c960703402280011125900384803003200c4c280c000b90310290540c880391064000014174410100b00d00c6108913a1400000840b50f694810702080d60300680120b010f54001504010011740e1082c82c0d00c03800300030f28074002d0702045583c0040c3c03800d51010700d400511440400401007207002c010014000c0311300d0340b8000c210315590400e28005000b0350740100e030010f800a10780040428480c00250081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893918642 1250 893917392 893917399
    0xa03030e0103181a06012a030e030109150f022803060f030807050c120c090402060c01060602010e12040501050301121e050f07050a060905151e070c140a05040b 70
    0x401c2618100a83ca003110b007501143d542849a084c10184140c0c126a5908070b00c0070700b0209084003041000507005030320314649107a40a68101d411007858415980304a030000c0c0540200103800c258103001c1000c012895104000d241004941200400c0600c00c83d422946035520941d0407040c0341c281d00240b210b003c0c1c102c0041648070140070a50414200704a4000e40c41122115503030402c9142c41400c01036000e035107034070511070144540d48035107011850f50b4850000719068038040e503c51002500f0b034002c40345988880d40c6000e4020035280d0301580f20110560a140445440c282c0907910ba8040384118069030380050420b000402c41400c0502c614418148a20b80198030049081c0511480365000c06040e9040e5111280f103107890103051004070082e00e001d88004980908021001e0100421845020b02581d031040798801154492015130342c0d074100305041080078020600c00072159820050090310580440c510004400c40c44140c00d980c03140001d001404054070740401c100041a02041c134580 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893919892 1250 893918642 893918651
    0x312020d060e040b1302060d090201030e07080f1603050d110a02031501032603011403010b040903350a020708070506011e090b0916020703050a060204090c02010b0a03030e0103 77
    0x5050010700400015001640000c01e00e4a810304020014200c0640031140c00b14603040c85c0400350321a0000c0382c046080d26031011440c14250310049000340120752440c803a03402034003404203404d8030214440c0b140341c6a403403c503074007014046c6100c81f40c001d5610000706503900040c66030000c00d000c1c094101e407050300744040e02d484a102d6008241011028258a481c2954200047c070401100c81c0305880340e40c80a0b103001d003501c4030300b0b00d441001e880180a45a2007104c407144900e400d66094201050081c401f6006100401c0729140c007803c40070b4402510b8450610508030803e009620601e00c1e01350440301030010a654850058200082d40000001c2e15041d10400c691804144204200da00811a500900041000385220161004190340111210710704084412419030364480d8440d400c40f10790350309a1072444981d1800d03850b003c2c040d44010800d014007a200e20600c400c40e4041e00071242c0129041c0010b10710503030100c1c200c41303001c1d10942c0d00c05030a04041c00800d05c03802e800021040181030005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893921142 1250 893919892 893919907
    0x12090121020307030b0915090f0a0e0109080301031208040c0e0403030207050619110f030c09031c0f081806040b0408310e0403051c0204030b04030203090a080d020a031202 75
    0x81ea4412580b0001003a00c0795180000740c01c10090480d0b1110340c00d0602c0f40c450803000c0005039081e00141c411041011020b011440000b91070344160324400110b0001c0005000903d440c0d20950004d22095520300c4020f1000088980034038111882160b00491440b440c40c24102c00054030080500283c040503800e1010a00080b010089503008680d021005102e90b4002105102520078a0343c44003c030000070301c00d030650341405c2c5054030b4100c1480c040302915540d80102191410300342c6d810480144800b46441441d0b150884180d801c0062141d503403602d142d4486084800015000340721055a5125000044c041395540c62043d81061248001d5460201c62030481a10007400d40c0c10a040c00350a4407450382014210302c05000100300324503240c0c0c42403900e81c0300074146007d0300540c0c072112000040c03c40e40d403581c1c41d81164050b60b40076082041906140c01c001f95686c1005004600662070341102048001c0006282812501250700602c00000141d0302150a0060720003124041d0b40c0a12040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893922392 1250 893921142 893921207
    0x30c0706180215040f090207020f0901030f03090b070201080609040f0212030909160503070f030e07170c0406030b13420501212406050a08120901 64
    0x10310004101c0c50004200c01814010445012680007042154902c1044200603c0c08100803480031030700c1801005803925800e00208095520881c0c140b607100c6104000407041005010283e0703501402941c407842419107584080342d40340b00b070502c0680030034684030004001c1d10b0a050f049502903c41d280440e003100780c50340455030044a6400100e900c0c0c101140854803400d02140c01071b48031245a000301201144064090000c3c032000c0c0c0f03402c08203c58a428074091900941012003590100d40444079071035540e80f01601c508182c60304141103802a0309188070326203007a0082205036a0010100d041e513407108506126440340c0014221084d8208008080c1c116210b45580000504807400b4035107000c60414807103079021080040d091005113490014007000c0ea0002440302102010002c2a01c24185030921040d801000c685100ca030490511008042404a0b080780c0200d13202a14140c017010780b108d030416202e804400c1d159801e0401071106262562058a048050726850f083c0900c9030000c50110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893923642 1250 893922392 893922401
    0x518150904050706030c0512041202030c070b03060109140f01050d0e010e01020d06050a2123150606090d110a0803220501090e070e04020c0d030b040b04090f08030c0706 74
    0x1da625400110f41041403640501809159502da40f4026150a40c180800403244074090b10240104690940717120303009008108460b5500c001d042211006665100e80102940c01111005e0000d10b00d610002400b50050404002c5500b005000e92480207240004581c076401c410b15041e1841e84441d00145000b000380700b0403c24181140025a0741c1002d1040c0c9002c0c0c0d2001e500c80c0b40106210441044110105034019031405ca03c0042c1c54205406420301113503c003068510440407800a1000003003201c2c00090001149003038885810065440d04100308040c0030f299030380340d04441c07044405000268401100a906800106003045907501d172404581303917800a4018400406070032503050507446079004000001c06003440c028042074148164010080b40151044091140c51602d0051540e03540d016190244a0442150b040d040c032001d00078094810010780501807840d14a4541c114201030080c0742e0a150481921103006040c0da0b200e041d540e10007071400c5a212014426800025464041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893924892 1250 893923642 893923651
    0xa0e030f0403060203061c050703080d060e071e080112020f040f0203100905161e020703021504090e0303041101081302090c0d050609060307153c0905181509 69
    0x500586902c0d000307003031022485c40512041c010387c0041b00c103007001810005d5540c040c1c03030303010502c10b403180c08444030600600140e030004440051203504000072980c4c00b60f90126080034450445040c0103820001755a846070a0044c11001c0ca01910f80303001504098040c0304000e04084d00000d0500e8010a0103000c0360802d60b1705007500c04009108101e5502c10340211508410111403407407051341080d0307015103400000c0c40051040480a413607804424001d0024000864000d01640e100440900241580b90300a010701500f540c9803124100007030030300000340ca12603075102c84603800301200200159181400104a80e00f4500c808440000584910342124040c19080010a884084808514003035070001440d85004002e20000c0201036074002408804955800c00918001d140414040ba102c00d00c900c2c114910b0000c4128101880b20519100c0480008040646040502c0c2c0c14049540c6c0866102d5664007183d03600e512030349217071002e56007500300100d05400404540c50002040c0817401c01c80307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893926142 1250 893924892 893924903
    0x120c02122b05041416210b0a1b03060b070803100b0c0c0a080d0801090506060705190605011d07050d090615180603150b060c0a050c03240a0e030f0403 66
    0x905100421483c515000e907850500c101414603280a0305c184942034804e032041e00d1403544400f4400c220b000d89071840007440d03a00700c804450b6502d4003003d10070280200380b180c030a1500c2c0754604603885072b05c89d01c00c5074241c40240e8401441c103801500c903250503420190000511000e0141d00150b070030441c07001848031010100142c1940c40358401004030b5008240c0c002e0106070050440c00c61074543c40400c050540743e0801001805d516044003041e85801b81900c020001c0c843c0304a514403030070303902ca003018415100705802e0016a8a945130078040c8000100305404040c3e00034080b50115000300d01a0031404c1c0801000100306600b1788801d0f094540d140c06182c4c4100325041c0c140b103080d200303411220080440180074401d4514642d61021110081021504003a640f218040b03c2560f4038021142200280303000c60f64518403a0a18580780c89450702c1c0c80c1e01c244501425036606000d01000c0d40d91200e0001002c0d0090b03981c40188001420f500003100c002070008120364a41400d14034080c00c041c2d4040c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893927392 1250 893926142 893926151
    0xe0306010e042f011206150e090705191b0b0c0d0b01050a05040b070807081b01050601021612020109081c08100b04121a0a0c120c02122b 60
    0xf810b1040450b00e80c072555800c541c51a107050700d980100d0428501103540286408089600b511480400070900c0d0b07002040e06044c484009503400c3c0d40f01100103041c040c201d80c4403001e911214025100c0c0d1003820807000400c11040c050800450040302d80c50f41c421075482c28800144943c1c0c9c0e480c2e0035128112801d69a9820200da076042000c124481d89601c4003080c2005480c004180170064401d0003188182c8600404c001410300c1000443c1d01580c1c0c40c29400388989490300d65a25050301c0d00155052080495072801e40050f100b5880001c1c40c0e442c00211145c200400d40c208000700303040b0b081c0c640059040c40f00300040010301c1032082100c003400c81e001c01c405080904249034002c00b00c030340c0902855041d41031401c047c0444000e40703044808a0b00c82c4000305a1240c05e07840d104028207101c2e0110540c02c140c40e020080b40000a40020942d8031280d0f45030104105a504064210350880c04070754016403066a000740c228184100030212002d034800741c018000c0b0701403c2c03c250502c004525070201c0380c94 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893928642 1250 893927392 893927401
    0x1609510902031509060901090905030f0a02010605100207050105030406020a1e090602070e0103052e11031012050d120f0f1b05041430160f030201020c0d030e0306010e 73
    0x424200600c10900f1619807513141003201c0060b290300e0040c040c0d441c007540c3e0381d01217000300481007080340c1545117440740f01c03912449007020182c007e2180d8480c05e8041c02c1000d2501000510205950701a940f058551905544032511610000d41194503c041805031100d01d40d4000c0022050044442c41255103407040c81d070505d00c3c02030070001c16600000e02454002d00600006902181d044540140c0e00320026030300328000c1d200c041542c4100f07500c01d40b851907d020300d414408514011131003214000c1160340c1c15552a07501c1c070311000400a000e81207030032020708060010300ca00d40103a1303041d494060108481030410304c5601101c0c46803240001a41e03981541003541c0c12111000b40b14191641400c0d400d09280c40380f81048a4001c04c0c10714422440c0c03031140200444011103c00000441c9141c418182d840002c1c01a41e07076251440c1000004002200010103c10140e6442d054990680c080c2803c00c650400b4841c8040c0004002c50078020f44801d03149040d01c0c100640b600030f081f408401c0e0030030f090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893929892 1250 893928642 893928661
    0x50c19020a06030b0d0615030c1203020714030d0f0201021309090b09030a091406160302010510140a09020706180510180f03110a05160951090203 64
    0x34540d1041c02458280004079004e595030907540c00e40c16402178004030700c1d040c0700390300d10740f84e401d03150401001100d4100000c1000b040e019401d000c2c1d17034400c2d001c0f10800d540340c01d60066900045104a070340f561126243c030386910b20800345991098818000503040011411004190504540001e8000c50b51a0046010b10810780320a54008900001031031070100304040017002d28550340103802806451070a028090703210381080b2248505203105c5004d281c0c0303240c90024041d00080d140c0c40d021040004012411000c10001c2e500c100000900f03e60419182c94103410194001d20030568800d559a9074030a1309503081400222002e2003480607080c800340d0350300318800726004814000191010856441c0008002084800d0007031707010300b03001da141034140444511f0845002c10041050103041c60b241442225645013106442d45c403581400303194030b9a007040303150120070b005030200e00029064143c6080c0c040420f804a80070402307000c0910692140c0003c400d1a915130150320700550000c01c001d210351 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893931142 1250 893929892 893929909
    0x7050c04050708040222050411030d0f2709020406080f15090a09050a06090605100e0c032d0f180a20030309090408070501111c0c050c1902 61
    0x182110100241d050116004140c000c008100030302072440a4801c1200c3c2c00c0b0b8001c07240c260f400c420400e001c64038091829128500481000c0c50091103101030009009010303d5903400410461303524203200380303130a80c8844000c4029001d40e04800190350b0300403030300300c00a0005102400603600c4102032130404024604803800010f11414800b8041344604805a44480c0403070780114a050f4003041034525410050701380801080c001f4207a51400a141040120301c0c3c03c558400e01d5882c00c0c84401030345d91106820426001c99a1803000f4200308005000a086e510900c5e5060115054400110365002080404060281c402e22040d640345810404d020485414414142c0d00c945e000d80590b1105980d808030240c0c03840688209150002d4401030310361010401e84610710f00040c149071890429061180f4a5407081d00c041c1c40d15400d101d005151300603280102c400081c0f90301417069910306030f40303a210000c0001190b480d0400c2800c22481c10461001c0005680035001000c4403403032109a8810000b480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893932392 1250 893931142 893931163
    0x28020307080f040302030706111b1005090f0601031716050715030204060f0f11010c0815030a02010801060503060402191e0906050d050907120b0a0f06050a0501180b0c030705 76
    0x201da01010840003c0c4c5c00700c29900c1d01688500d02041d00c20803507052190502410501035a00e4262440c400200c5000091420b0034888408041049444400c81940c40301c01a142511050348048010030010b800c0d44142a0f0b282001049141066040002d480302403000110540eaa6030142400f480040d918828400078080700d41804c6103010710705407015080ba901741c1c10140030f01c2003081c044407406000c0da0031084601301180081240c0b01020718090704c02030060310741a4201640e804d800a003418005001c5400e650161078840c50b0f6840c20b113007210f0990000740050707042a001d03c1607407060304403456003200c4201c860710341c400c1d85940c80180e030383d01c0d0003640f03022010001018010010781d50004119054665008000324995031008441403404d0840d074400440301c05441e640c1418000c9000405019120349181403000c0028100c1c01c2087e200e8030700a09a03c4100300703070200102e6002d5002003480d40c2c01a0f0781030304c4440e5120340b03004844c2c03c04a800c060f0340d0000140a4200801403080e10040c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893933642 1250 893932392 893932411
    0xa200f1b0102041e090c05122e060309030806040204120803091501031a0a090b0a090c050d030e120102032701150b0306210d03020a0c08030705040f0b0306090606032802030708 77
    0x10800c108030311011012014020640d243d404681803100602c1070800306032060400309c0ca640f01c80e0b42c1c90354000c00422281d2400e60000f0790660105c1c05520341030080310b00f00c0c0c401c10b946c00030b90b007083c0c2ca6042107944003500d040780c64070030700c031900162810b9001402e00942c000c00c00003015074101100c0d9151180000d01c460107851402c444040003070020380e8400d40102c54210000783c039100301d12300380c1001940b40e00101d83c0b00400e80411010554000788071020581c043d6814501221008803d5084c0c0c001074605840c07011200c64424088240c24070708120781050840080780c0d041c1081914446125103400c010b20052001080000506001440b02044c2007506500402c80a2281015459143c2200b522701050340008000e003070f052144043c0310a29822024956881c00d0004000d40650f00501c070303013907060035917010028075103c107141964410301029225150319940e1004000d0564801460a55064506490000b260079003003661a124041d0913001030b03072810080c0000d00811001801030a2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893934892 1250 893933642 893933647
    0x3040f060507050a0b07020c130c020c010c0b0a0b1503150f030a020901170f060112030e0603010303020d12150e0604200f0d140a200f1b0102041e090c05 67
    0x10f40010b2000081038102c035900d091500c50010490605c411900c81c0740d44542c154000c6880103030654045072181607282c00310350001040300e0054034412a102c2c8050212018840000c0c15200c0c1a0000e001b0385900030055000c8403190b070135602441d0810703100600048862068140c86080c01c020800c009903040f0003e0007035403140e0740050b90030700c0b05000c2d000c1d50303c0c019200405e641008012144a041017070f02035440d10b686900c080b04161100d1071080e4006810224450b5080c14842c081342d068903096400f40c80b080500802c10b0b15501c5440c1080060141d596000d60703140c0c002c045d08040a05115004500380d070605108000540398820300310381085a589601440b44030a25084a03114071002c0c060300d89034080c4e6204100140000a1444041480141080600740003940211426140f00028111031030042011000310b020302d9085c40c020313001c100041c05440c15151000c843c00c08142d000585465203401c41a50b81703e0ba00400b40c0703007402e2110b03030500401ca07441c018201018543e01c1d00d1070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893936142 1250 893934892 893934907
    0xa030b040b1c0314070606080f160b250c090929011e090908030420012a0606030606080f0c030604080a26010f0b03010b0406030c02031b03040f0605 65
    0x241d58540b02074010705020603a602554040840025260042d801980807c6a940d5411a46850300c1030101c50030a14040c1070144802c40c01c0055401042e5400785860500744180c80c050100d5034044070301c0e05d449280702e003807003140022807095803c40035108119000c600c00d0f440e46008144140400081d2002c481096203100c20018801c1c41c1e02e04445001c0759141c10031a424a83e03000c04112900500481424204140180804040110300413032142031682114030012018140e9a00022011800550088071380c0d048824031050700700c00203840714900e01401c040e40d81c0303a43c1100d1655004540300703030310740801f00640101845000c0e9803010b0b140c00341c0f00d0402080c0010342c4568004000400105e000300326002031602c6032948040da42207107508400006a09460082039840034841c0404254280c2c20100c0c0e11101d034800d0701d04984001c04094200303400c256017540904200ca421070114403003030001004012081800d00c80240c14500510781d1a4203041c154407088001d504a031090090800c00c1c407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893937392 1250 893936142 893936179
    0x50624010c021e0604030501050405010b010806090609010b1c15061710092730050d05040303020913090c050108040f0b060619030b0405070f02100b01140a030b040b 72
    0x2c0c00d03941103000291030b50f10078000540704e00481d007026016620b407208010030002c05500020140303500342c0b1a030705283c2c0c0c0d140400441800403500c054000803540f00412402c4440c10190070140030300717101d158031f0811035030260040f07800e20003901504880e41c000401800d0b40200c0854408403903403040c044189040035003000a4599403040142c40c0d030341c0d88150380b01c801c001d50074216081c000c0d0111424180b0300d0304042030904400029030707204c059a8500702c80c503003407103001401c1c06402c00c1d2100d9041c01041c456034002050024420703801d042e02041800503503600c240000141c4e4802b844000340c0b0708240e081904040c0322a40205060042107014040843c08141c981441a948110042c071180e907200c002c03460034080c200301800750b010340b00c00f03001c803181d01900601c0d1524401d0314100140d5071070403400c8410300070302c00b0b5000c05600840d68030041001260420304a81d10181081d010303080d40b4581e20392442e070107082d2201c006550740c0d01078991403500b406480c80c031070411958000c254811100c0b8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893938642 1250 893937392 893937409
    0x30a240603171c0f0b04060b030912032203050d110f03060f040b060a09090b0f012a0c0e22030509130902060d0902090112050606011b050624010c02 65
    0x4400110030701142440031004030b02c0600c16042c6851800f40300f0111550502c002411a1441c05441b135800c0030f0b00490f07083d40202c142c0340b00e101402e004042d204542140d00301d1981c4090041840b410062003100055540201a800001d12958445644030310081c000307011224a40104d03201d044e07040001c1c0d0b0486843c003040c1ca80140381100d0200410700700f00e00080003454100303501c2c0e421150108603a240706030080703c0441120409141844800c52074010400d950000e1080c1502180d401500052040003450b80e04001940307030000c50301116480d40394480490281e038809041e0311015020800e020300142c0405000c1c24060445c80982070041d034000d0810300880703550714003808520b9020000c85c0d0036034101892064014242d10354030a591212500074060480d13044e405503800380000509001c600c02006030f4290801c0150440742c50381401103035290403048072a80c08881207120740340440e00c28050340303001e4000304030b06030300707110040c03140241072107031172881506124110b62480050b0321107014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893939892 1250 893938642 893938673
    0x804050306073f0e010e10063503041e05010807090e0702031e0c0c01180e13021207090b0f0109150306080304030b07120b0d0f030e030a240603 63
    0x4440044000703e0032400a803c00806183d0141428040b001c0801001940314030040a03003601555040300324111a10140c420a12030219207a040e14014070b081c01c040c58070194a00e07806008100c2915401d40e20619641080d004411110b03501c01c0c240514010541e981c0c4020300c000c0c2041c8240385441d500140c072481c410300c1000c41705924030001030400751003401141d0242002c8400c035240000903226594143c1c00080581c1c25510403040348001c00e41c061423040e0309941c00b086c0301a01140c01c081000040c5c500240641e004c0701c408410b150016030301c50491050242911000302112494040b031340c0d06171041990680e001c0c0da0380c54000e5030b0700e0360700240c0031007a038404114503d0030301c0000204400800c45c80c2d00822840c000468044200840001254000d035203550742d0519501007600d42504407a80f000c41e84c0c1c1e0100f10b91b42c550303000605111211840c0b60081c241100c1200508000c2406c1c05580001250000d00d450408802040c3d02c0c0d6040f0880c2c03402070420031905045940c0c5840c103604040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893941142 1250 893939892 893939957
    0xc0801270b030c03012a020f0307030c061e0506040c030e0c061b030a0207151e08070c0c090905100506061608041e0e06040e1b0a050904080405030607 66
    0x2403003811603460801c801c034500400600200000389006c281c03840c81078030a020072501408641c1d048000707903100040000c2c81e0740301c0c003024500d096583e0380d00350f070082c0070b40200311039050f12942803c4104003018010442102d0091010425150400c00c000c2102c82e0610b55005143c41c00d0038000200200040c1c2d80c0d40428140c8105036901ea81900118032050180221500741c07000150608107143d010500c4d03811680500c0040c0b0f005a1068000d41d2035002c805c1000080c010500d10440d0002c1c031a401c40b40d0171250500b40908041c08540b100309446a6540118200710b03200c20300e180804c4401c021079940440c00704030800140c2000b0000030300b98030502c040704a40d1141c003140001409901022640140100240110601c400e9600940d5070f501c640300b441c00e00c10050b400107581e42454018910b24201407400740004500d50400b2080c00300401d60701a4004040d5440400c890322080a843d002c0c60090054645562605040600d405e40042404081250409800621715500140d010310300b03501c82e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893942392 1250 893941142 893941151
    0x30f010c1409030304050d06140a06050303190314090d110118020607020a120b0403090602030a09180b030a06091e080f03130f030c0c0914060609010c020604090c080127 74
    0x20382c0020310751701441d0002c0d03501101030b00e24a41041100e62145418000010100905543c3c0039001700417605070b442040c1e010b4008205010720304180c042000702c800d050341000100300b40107114409070b000382200d410440382c5c0302c01c0a981000d60401f90804103121a90001d0081101001d0106482044028028050079000c120030046644003058000070305105580074840130081d08106018078000c0e0307002e034003059480c40082452440071080340c001c044e083c0c481542d07880c0b03400c0b0094090200e00085103081d076070b649100c0d00b040d0303410f001d01d140641c00380714041204503040c14490110195084200d14241d80c0c01c0c0c000300007031000c00968605512401d2003036200c1da00c10b03001142d095072800300140703544d03103488201041640144c005006940941e01900b60980c032464803000b180d000076401002d4621904c00100585008002014400410f2421048014685d070100e002c942040e0001c8200d151155440402d2550100f003142c01884040000c625507016940c00769a0030550440c0800c40c9a141c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893943642 1250 893942392 893942407
    0xb0307120218070320030f07080403180e090f030313030c0f21020601050105161403070b010e0901050709030c09021e040f1a070302060720100209030f010c14 69
    0x4000d030b8503010020400c1a80903a10384400c00400902902c5124003084a00b81000804c00c500d80d002e0702d100b03500d03c10202401ba22a114241ca9188004108800f0456a10302505244c908618110700403d12070440a00c60b04064141e11f0034540c440c140c0001a500038401c21407000e06040c0501c0c2450380608021803482030a0503c0d03c0014484140907001030a45101c048650340406003030b002260036542500e91030b0b40c03610011102441a602c1011440d1041030183e000301e0b414040405042a000381268540710007a902c684200d4404d0384060340540c09442080140315081c090554049071a142c00d42741e4500710707510f910003c075a41c09032010450740880c03c2d040d5007494035542241e480e50541c000c0d0310b45036604410b07050300519004610020742c10316024607800c0b420b9000d803604d165060b005800b195440701e80803511103260b0b40d6400180d02c0518521007038079005001c0009907054241c009640ea4100c4001d0501e080300411040940341e00d420406010740c1c0d445400b030040342100d07203d03a40d40d4010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893944892 1250 893943642 893943649
    0xf0a0507090c050a0f05090402181c031e0e18180a05100e030c160527070c081216140a020d0f02150906060405090a0f1b08060423010b03071202 63
    0x6030301ea51f02d40103407000500041105541c5e41e030310403c410843ea80c50f80010301c40a20700180d134a211008000ca000703045101c3d0b203100719003007500130507415140c4543e285080000152507959403d45d07c5907000641703014000008100118500044203030001404204010740d41c596a43c06600001c5101e81c2d0780e81070043d104c0000384102c4010800d450100c503d10307440d05100c85030300c3c60540304161085e1290341540c2056011491752800480c00c8888010096990910a039484100507504851044003040512071010100c030446000380e130f4070f03805180c410808620207450f64449641d45040680d0034484510103550004841340d800400385880400d0103031007001649070001103c5080c098605000802800c54400607142c0c3c402d8208a80900554803090b07000ca448001107640034140404d415481030200d240d07074540c40c40c4540106c40c411111542c503030105003804400d44084403070307100540e20100040ba5800703030788142c6d0103217a0081040c60390b02c2c40060742e21600b52007070040d1081941e208005541c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893946142 1250 893944892 893944897
    0x2030f0133032a11100c0207092c030d11160611090402070501051902130e220302030c06070305012114030a0801060f08040b011809050f0a0507090c050a0f05 69
    0x10615149200d0010300b00d005444c01000382407444192150404200071104c03140140351380c4c1241900a07201290070300301d4030350250007024003028000000500c0510141912010f084552010102540d150001c5041080a07182c2d003074089400791038284441910003000c954034074509d680c02000041c2c01030f49103d40c14410f010765640642d1191000c50510203108040d04030381d00c10400d0f800c8034011120244606000c0340a01e14a140e80391101c0c00040c4000940382c142507422445004200421078414004401c0024849074200d0050304081441141030204104054100030a803d090000c7d6044c5241150345d01a58421240f661041c2c0d54a0401d00c0a80c070003070b405520300075044d00e03079540e00807802406c20301081c8900030018540000001403d8400c087c2e0f207000e81e40c407140000869107000d04081065218003015410b45035500e900f0310001c0c01c208503400d660701650b000f80032810080d080c00c90a00381d50354006030038241030818107480c046d4000d045a40c10740e21402c114080c1070b2104000c80f401d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893947392 1250 893946142 893946191
    0xf0a020d0b0910060e030d021e0c0d030507021903050607050a05250b0a1406060903030d06030c050a050904110613081209090c0c06011a070602030f013303 68
    0x4409803d0080008603440380380f0a84650391280c0f1040c0d2002c005050b621100000d00383e006030404940c05240c0d00d080e070288648895034404641070010132a000403520700300280708902181c8001081811800c1c040a105032020010042501c843c2c903680b6115142c1c1c000074440740401000244100440b4050000e603900303281e104040322503031403030407800504000d44100241e848107500000564690402e001e84143c1030f0234501c80d825103072604424411903811580ba1181e2500060100780c040300703014450103004501508081520b240360400388120035000c2d030000d80c05503016004100200e2549141700e4010f036002e550003903865404d0000b0304880451a01300810303074020860b00c400000c01e00c40280540200440c1e100780c0300d490700c01020603541f0a030030310103403107030040d0004010080c42801d02e42c0440980c850203900e40400d0340e60303a8003241c5c811560000c0507c481d0005102000ca080610903010081396014012800352041c1550b2274841c1612810806444140440c4c00020301c00700e80010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893948642 1250 893947392 893947399
    0x20c13140408070302120309100507050405031605010f09121e0b07020102040612090b06311d030c0a081c2904050601230c0d0f030c0203030f0a020d0b 66
    0x604052600c0c07200b03640301d44000c0d0010310540d1b5100504040401c2128013030410103008083c1c10300000180d8010b0704000303020b481030140c180f00000d15920f0034000071a202404022405080303042034000340c0b14040d5400b40304d08000b0300d440e05011865801007085603554101039070800000d0082560150320b8925000203180c060034005200802ea015000307401943c0d520b0700c0340d00340c102c5046a89812200701c8900980002000380110f42c21381401d00c01c10301c185500c4100e001800d0389401d03558071014103040d4030600480e52500b001c1d00e04860410109000b16200002c1e501d441d9603461980c3e55250305035809400e407840011000784840010211180c803000d00902030002c0a584400340314880c0302c2840440280b4040c0c10850f0492401d4800d081c405c110584038034041d241c000d494090400e15110200210341c80c1040100084442000002514000d982d900481039294950040594031428000c0040d54014814002000701d5654403d9002044000c01030700e40c100c01403000c2c050904e2240c0281c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893949892 1250 893948642 893948681
    0x15220e0109050114130e2505030601120323040302030d05030a0b04050402010912020402040302150301051e0a1205010b0d080d060f03111c05030a020601060f0f020c13 73
    0x8004010004080c1214040c200410160b0ba0340e5140840020f10004419401286210203ea01e0442c80d80201582c000300700c1100e04103101a40181070344048510380c0000318a205408010502e4100b203018094002008101c1c90303c2595540030b0b000f22117050340010900c1e00610b0642c0410f020300b064a004540080c2100d01d03a106117000078055034800e46915400c1c5050080142480c1080c0c01040d002d5541030b034a07540744514001a021201560040c12684181c0130440000540c0e640c001c102c42010042d0122580d9501d01002c00456075841410480e0201c260901c00c0788607070f5818254411035445669220346000e66152160050200f00d090f80d078014000384400b4103001c1000f01620820406500c1041441e44441e100342020800c0d00c03000f0200785552400158500307080010201403100308980310b030032000d90f43d982411500200340760001a4006801003000350b9100764100340c1d0380b61504050085000d0400025145c0103150020360260f00030500744079049005610032540020b45c19030510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893951142 1250 893949892 893949899
    0xc0d0c050f1b0a0501170a0507050705030f09040c021b0f011e0306090606110c040b0d05060c030601082206090503130b0c010b03121b03091f02060f061522 68
    0x410702c0d00240d03000e000707103800400450b02d540561503101403103881610200d0990b0f9003081650107013200421075800c119051200078001901080a84070540310003900c0c645568050083c801140d450390031003001c43d032000f9545141401000151103103400151507140d0141c0c15080142d60070b100a00810b403518074035502d86032109a140d400078043e01c4c40d82c0c00900881d03075160800c031030750031f00e5900c010441e4204040300c1d0001e16180c0d0107600c04e260068010140090180c5405040c031000300d520300c0104000000b000030f2981d01c5000f1035030161120f0091100e107a00c5244801301081c220400500150703440801c10148042002034800d0342c802d05086824894448101b1a81030304081048000d039801c00c0c001010900d40411441d0f080e01e0940d44540c10440e410445050f825400c42e0b0040880c0404c2041c2c02d002c6e200c140e803041081d004c02e5086030043c0070000b002031509500510f1000030701140c000744807240c0c0d141e110902c2910341084801d5102c0b0502070200341e000210081030403681c1c52085000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893952392 1250 893951142 893951173
    0xa200d08070203011103013803090f0705030105011a030a140103120e04140705090a030b1512011a1302090406090615030903081306180308040b01120c06080406090f050102090f060c0d0c050f 83
    0x183e26510bc600140c403245907640052501344c90b420f010380307291486c98006001e1000346100296503c43d04e1500c005c0b500c049c500840034018442030b041594128091201c90300c2d401c0d080682103940d80e0040e01c040040c050200c0759078508141c003402c0b117002c20000203102151039407410241805190012a0001c040c00c200d4014603460800e0744070740c4e00034028000741e211180010b20410010a40d6421480e981d0300d526020012002c401c00c80e0300702c03440c1d400c0c4220b04080d265441803502406050304001012824410a841d60030303400b161305002c0500700b009070000a9444003007da00403080f49541d10b40ba2409291610107400c0e0300303a050301490f286992500900d58064400c50141e03001d024014200d90f01c03180040740030902e030140506011540781e000c0020398402e543c541e50003805803000180d143c040e955490701e105072440e0140c415030b4000c03400010070300c1c00504901e90b0340c0c81100c00b645000190450592510f103650704e803405004e20040d541003488410b0210759107624a40e000d817419021100801c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893953642 1250 893952392 893952403
    0x302060924181212130905070804140d0e15040b0d020702090108160b030a1407030b04061508180a08071b0e090a200d0807020301110301380309 63
    0xe1500c0a0b10014030078046090461600c5504030741c0c800640383c1d841c1d040c8030715211341d8465003144104008021001840b44120703c1468050001551402103509240c06c0c0a50303424024580e07401d2603000028254141e07600301c18401401481500e801075500702d03e9404242600503a4400000700100184101394510a0b60082494610890300c80c8280c0c1d80701d0b111546d40c2c0880c285021031313100b0284814480790ba5403401556000d54040004201260910001e01d46c962099031400040790320703808181c100b450300340606400703083c0210490740101140003008001c104098010410841620482411600e040c000d10078195081200d1503036a40d0949050311580d80120402c2038001c05035080404c0a4002e43d0f5845d01800c100b030000c00f141c07141070700c550220304514040c541d400c0840501c400750759101c182c01c8403a17581c010703418030b522a1840c0c01418250f034000c82110030319000420041c07245802d8004038181b0349010092461042000030000c0c02d400700c0b80c0c445e110700483c01004010001d100090b5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893954892 1250 893953642 893953657
    0x100512160203041502070f0e0105060d0b030304030f050c15090d030302130306021b0705030303070c03110f0607020a05060c071e080d02030406050a1b1d0109090f0b010f020a05070302060924 83
    0x5102400d0ba10621078230558020700510b58490f408000101400c0559046181d003044018183d030f113055501d03651005030041b5200115215001854522070710f00c6c0603518034115500c1450450b16080081000402c44140160300901745980440c00700c0c82c8080c14000c00010b59440703001156a2400c00c801d6200031070700074190300968412604042036500300401500d0288883e07403203001c0700b0303d00c80d07a0690304807020407002a030600c10000c2e0034501388000c0003664080e06003034001e40401191401c005007000300c0101105401e60303042107a1000242c0c020183e4045404848114204628a240c00034491003900e909640650010060005111055001a0041c100d44008004003801003090349134000102810402140c0c0b100c130400c2d02c1000502c40c101c10341005241c4010b001c0d0b2694001c6085428031642d010080c1d5841000a0b840d5030824160304205e0440d000910059105985581e966000b82c00024000d50b000710381d482607600c0b52580302c4a00e620303c10005e607281c8508480140150400c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893956142 1250 893954892 893954909
    0x19090507110f16030209060d0b010b0d0e060c2209051014040b130b0111030304051506090c071e0203030a110c19030204052502060610051216020304150207 68
    0xd03000074001e00c0007070100c2c0981c501c3c40807400400c1ca541c0810903030080003012a42c00559000320080000c0c19040401d0182c6070b903000c11520340304c04070f0074502111548000c0740282c0c2e10004c1408410715412091701c007079400c6190750610300f0a059500706244121035010550040c00c00e014055540c460020900c1601c00e280d803000d558410381000c2106882c0703080d4001d5040030704404043e91084054102d40c010400606040c0c400c2c400c0789099074910390007194248c03001e401c00c1c1121004030104a0754241c0011089a442600c1d041405d401d403664030074914011322040104c202480a509000300489401360000c00742c030b403035101400000c1c014403450180e0003400d004000100060f40f0f0f100d10b2900c402e0101041d584d40e914119400d200050002801c0074202c04201384580c20030760551640b140e4090240d40c081c00942c1000028812001c00200e8080d0030700c401403000d804070000345298158000d40f045110010000031905c140d0840c072454000019000c5540c3c0100c00c05034002030a40300311030105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893957392 1250 893956142 893956153
    0xf02010f0527030c0d0f140c15070512040312030501090608340b0a23090405100f0801020c06060604080601060507060609021b061003030e1909050711 66
    0x14400c503094491481d442e0a2903000d000a61042101e84001014040e8050304071a480355507070000560343c82403a0b03401c462034148410820204210315600c00300500d088401042c00060110015915020302c02d52103030300c000d000c2515801d0103001c00604044038243c0000c1a50b69441c3d0601d03500b641601510300f008a41031400002d8803464a00c00c42045401d1040501010710140c5d0b66801c2d10084100c0c0480352107020303581f95001002c001000b40c001c2071076a42e41c558034050303000064241d00d03031650002d11810504010307141400348c3c01d08450521034115000905a81c80f19070b01842c0800a41007107132242800c0401088003003055009080300402e030000c0752100e40c0c5a0301040014861401070110301d420000040049074040c1c0050104184034484c0810110b4071100303a40100d030400300c51701501041000c00300050140038044503401101c0c0b920500c2039942961005043c00b031100c08441c1c0a0040f24501048540300b81c1c54120290451205c184814205014000c2052980180c0303d0316a0160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893958642 1250 893957392 893957417
    0x90f060e010507113409020408060a020406052a39030a030e0310090309261f0e03071109070809060622020d050a0509032a0f07030f0201 60
    0x500d0100c800040140000c2105c1019009402481080c1c15100b060743c0d81d4802011500c0030300d00316220b020b0480c4d100010703191441e000c401c84c900440078140c020f040380f041005002465000045900a51079411000c182403110110101a4000820401301c05e0080c804903800400800500d505664010140048440285003440b5001004a0912581070f40306900c0240040d000d8103003083c2c91940201540d80404080c948681070f50f0703241000301c001030310968088c03041c2040c071040e28003c0c44059000f0b484d0003410748401603544048081c0e08a000d5000001e0050403003d642085900344440360689844060700c0c0b40426a89528030030700303485082008000340515100304075440c86031310320500401003034845000707020804d038804c2c0c14814100184a0700c40ca011000b80000c01c1160040d5034005401d18005195000306c8501805140da6038000b0441e030b11203110b03141c0010001c44040480034502c4100748030b900e49012180c4c1c0c041247c41c040c0007000802e02c18580344400b001400ae0300c1e00d034120401e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893959892 1250 893958642 893958647
    0x20a03050108060c0c0a200a09140c0906072006040b0d06050108040206030a09050a140c040b01020d0f031508060f160302070b01030f0614010b040f0503060408120406090f060e010507 80
    0x17072821298969032100d43d1407070100d1100702c41614510811641e00d0000e0041002280c41c1c4007640d00544001500ca0300e8606800c66688000c580c49040c6503171040c1800608400a1010f00c202030003c3c103080078000f0007141c0780e181b4010401222000906140d41c0340c5c0d0b02d0b070340819150000f080e40401c0501e002400180741d40260310f4144141d60007094545543e803500c0400300140401a010b9646105504404000940f0803c00345900b00c1054003c0200c1102d45d0100300a841190600c2811034215070303442c40556401864203100000a82004211018031180d540003000c070903442a24144550000d001100006c2c2ea4120302504840042ca4a1055609419001e910030b99600030114920203004001181244410707030319440c400e04012540105840e80001f03104000c1e001041c01042c00039040100f110664810402040b081d4040d0203589456101c0700120f01442600314182c2c0c0d005400101001019484040354613400b42c51802110030a09100d0014418400c120207198030b0140412411070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893961142 1250 893959892 893959897
    0x40213051c0b04020909030f28020708071401120c0f300f02120a06060210090b010e090f070605070308060301050f04060f091709090f090c061309020a03050108060c 72
    0x40d00102d07960215202c42e1309001c4c01610042840c3c1c014002440000300042044c0020039030070340f22101c0c5c407602d842c80480401102c0d4241030318200f55031142e8810030004401258090880d003403508071244003d28000180e40030b000d48500380e440945001e003100384464010070705d20001e2080d80d03210000c442c8641e05902042c011300101800e0f18486142424900e211500500d400f1005414050706080950008800e811400c3c3d68100c4507580382c3d0810f11081c2d50412110340c15082c034440610030203642d40c4602c018504103000b01d5494641100c0024030f000010002c0c2403d008107942210303182992500000c00c10381001d4006c4001900c1d9070081a618501401075600030340a42c0d03041c0e08151030b15580d1100030402c10300c5c03541180e901c90011001040c00c1c03400d410340c01d90b004200720755a4604882002a00000146110318010303805050120802c40003400207035030381060300c5007076980d07030300a0f4076058000155001400389400016201c00d0194035800a504039101c0c0c900312005516102c03442072190 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893962392 1250 893961142 893961199
    0x30b0105040303021018240b1801090e070b040f090501060f1d0a0506071a1608070c0507030b0a0b0307083009040c0f08010806191a04021305 62
    0x113070b0144448960103c2c050744031541d060201c00c0300c5c0310b216840d541d980d200c071a55803400c12581c0252061141881e1030724040d100323094100f1100040d10894080e1910034a070700c10700400e2000c3e95641183c01c02400c1c2004460060068110319946880d0358000004900781c09004000b4031a06102c00040c0b05409140702c07201450b81e0342c44049000d025540303030700181044c545d04503500c0500c85900190310b4488500920300c044c0a0010007410504016222544c114003030281012805e00a4078041c6040e0301580094101c0b5540c50100c01c500d0550401e0b5191a06680024000310709040c00d002c5c6162441d071201c84e0204c000e034242d07020749130359035545900c610181842e02c401c88140b601c130780d181c3c130412100301c0010176040c0841030500402c030000c542240c80c004503200200712a1400c0b110140d820048203070040c018240144041d02d4102c9812007004012940c20700855140c034564030000c00c001d69500300743c003005042107407a800c142650b000c0c1c1c01501d00c0380502628071164005501d0789242e0701400705c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893963642 1250 893962392 893962397
    0xb0a14040f0b1015020f070f080c01050703030e03030a0506211c0903171c020405030c010f021c0e100503090c060705100f020405090105090f0403030e1f0903030b0105040303 76
    0x80c0c0c407141c5011038000d015000761010340304081a0b1140c00c2d0304401d0645882d40c024801d44c1b11741d02c032036458018190010000c0042000d400c01049500040d240b24408007840d0582d1102034070b245c02c0d805000803104070b40440c000801041520501640850b1081308202c6a401013242064600c642e80e01c102003d2078602c0c1c01c50005808004000040840c800c056450684182542c0b500c0e184840500700402d010390f84000900085004800c01c0750100f05c500c109421880d040c5480300080c4d51300700039140d16040c401000542082c86000703122094941011428028400c1c0d50044024040050050824820020510300c244410300c40d10a0342e20031100c40c0000c14060340c4020822016401c0544101c40700e01c0f41c9c42481100360040e0052200d246008000961124100000c110864005030045805400e4410070000d600c1c0031a0122a0095010305000403c00320030201a42440d641070703500e0142d1005d034042038030303c030025a2122203110700a660070404400701100441c0d0a200c1da2002070300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893964892 1250 893963642 893963663
    0x3160f030f050720270a063011060a12050901020705121b0d0f020120030f060418050303060a06020a0302150901060f081b0114070b0a0204030209040b0a1404 69
    0x249481803406542d1021130050601208502d43c50400b84c0800c403240020310f004a8034414000c85002d2801080041d106800e4503040448035107264450340301d4220f55030050303101d50410380c0003404802d0030401991500a04040d0780c0740c1e070b1413401800c000c180c2c5410512041c5400700081032580180f00b5100b2860340304025040000d01c3c034040c180250011807010f41c3c0c0c40d01c00f80c14182242d0003000750302c070022403645403012060300140001c1d0851702ca01911085020540920480100301c010480e688410719003103d607071a8583d8400b0800505105001c007040c0300401e004003042c031000101031407242c1800c4450004d0147c9035501281c40ea00e11400080140c0c1c84450003d034030000f05200181d01c450328030000500b00340e80b2415804244003903409000700d6000041e0b0040300840c0c111184020707560038206090001c1c104000c240240c401c5110160062500b8004112090543c0d0111001140c0041000e8650300342410701c4141c1600550300340306014a4650301880e046c4116981501c103a0b0081003c24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893966142 1250 893964892 893964923
    0x50a080c0a1a18030c0603010609030b0903030709090c2c090c1303020d061515031a03031c0209091e0f070f0503070c020a0f080706020a02060a1103160f030f0507 71
    0x4411844265555500d40104074000880d51501c0d4042e5002703001076521550380d946941010303503400c2d9016100c0100c0d60410020000c0c201d4000708940b040390040c02001480203504482200c414103194100b08001008048511038002010038454403403038200c41500031929035180e405083d01c2803041502c03c46d2010001080546014541d0141c420f0113140003242060f0202c01944120003a074018412003441c03618500340d041e5043c0300d4070b68003412a0340042d104d2060003000a503a4020003200b621080314248029802d1806501620391185015000362582e007010401e4600a90003100e560b203030400e181e00040c040490004115000354a80d031542c0e44011491603086540d5400100035800b0300400c1d0101c2401a11a0342c00c040040c946041e04800283c00c04091600b80041d075400901194086031350300d00940d9030802100c4544c9240d00700b007561201c0c074003485400d5000302d6040840340c6900403009420700c00c1d01804116001e109a54040c8550b00d807002c1038699014080019000d1031a9a01c0341 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893967392 1250 893966142 893966167
    0x1012050c210105010e0114010f09031202121b24010608221209150503060409140f0708100c0806090c04080d09210201050d020310050a080c0a1a 63
    0x100c2490155075000303098441c0325102503003515020f130310560200b402c1000400928522014031040e01800340380950031908107100c024071082d210300002d0a1b903001002410300d01c034020051100c03d46514840c3c03546802c0c08203088903058102009400180c01074070030703524000705100c02261401503200084070309070342080c3c422188040300a10824030b070300b0200500210068240e11404d03400740300340e28010030500745400003890318045034020351144e4107145400305081d8001007540d902180560340090402554200300701035103010608114070303001d00c042141c2441c0010840030b0646003140c0031204800c003a21507882c1160200e10158000035404c20208405180604950360003101b920708c1542003644031610f1a0034031909072118804550090020020680070503400607a9a8100c0f208025074203460300040c0c5944501200e1039180b503400070014150708001040300d409450040c0400003c240c030741d461a6554503500c88558801c18000500150b000c440c8002100e5003c20303003040908091318002c42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893968642 1250 893967392 893967409
    0x6090b071a09010f0e0601050d0303180b090303180705010e1c02100c11030106060512130b01060c11100f1101020d02130e09010c0903141606081012050c 67
    0x200c031075144400d50704000c00d03407100c0041c1c040d212240c00003d80d0740502500b0001c941003010450416048900108410f40c1c2e0066605080c1e034041c03c02040501501410103220307108204003d20030540c1d9410300c10360400000c0036520403c1c400b00c0784508038038002a202e65800c4503100f40360000d103050005c62000d0403e0100300e246a43c0c05080c0490f62903003540002c2080f030214101c5400151048059000d11003030148007944804290004c000c03242c20000020451710565903a5548020030300080344540055020b00d60030b0a8200030342d0550340d612450020700010b60601700380c40d41c0584141400c424a0a108400e07008980313034948422036010f0304c6050300c801040416801c0195400d00405242c42c40c14001410140150186002c0301313401c1a0382aa06054080e00e0700380f2a0785404000156150440000d80c281ca4100060008100c600140ca520300054156102e102d981e002c40c0018403c1c0e0440c42141c00380000e845c00c05c0d0200d031629440b00314569180405000d9620110b051b1210342050502c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893969892 1250 893968642 893968657
    0x904030c030c151b030b0a2912160314011a042301110307150207060929061012050916060c110103050c03150619080f0901050106090b 59
    0xa02c0c1e1610302207900c46201e8080c00300318501040341c42d807540f440000c94400b00100401403605041260050341070104a01380090f001c1c880c00d01c400b241e4403a026034008044884081442c41c210369031031000303034008107410b00705881a100c124026070901c0d03125030090103001c45406c00c114503034143d6844c2a00c004412917004003c0030003414100b002041150361015908007c1c04189501c2c844803140200040c12944004008140c82e08144000030004c0c54000030174090701140c440260300c0d0f2010342403102c002c12280d07000420124101c484074101c04840480300c0303101c8203400e203003ca00d99200c409101c0d24803984264540061034280000b0480c0e5203590200b500700000c0401c88114500036002044013440c560005404034481290280c01c00a054118002411003031901703010078202840258a9030201070038080c028004582001d420b0344411b030585034048a419446054061841c0d00680404000d8036040705240046001444007201401414101e603d1a5640c148041ca0002c1b2007500e50090079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893971142 1250 893969892 893969897
    0x40b0609091612090c0e07090602030313032a020301140106050d02071103070b12090705010c0b04060b04020f2107020601150c020918190506160513060e09090c0904030c03 75
    0x2441c43c0c1c0c145241c800c1c901228460103050040506004001c0324551000f0240410411040b50902c402d40d03000c429030b90442e041000c004010211454180da056082d8402c94a281101000e80c0b0000e08031f140c00610307120300940081000c8425481d0321703040500c0c00d000c0d01d408940c040108808407100ba60084c40741e20b0041048015852880300020f041080c1030f0300540300c090001c213600301c00e1990b00f00c5d03454020120700000c19142d4030b40750001c1e254184103031000d0500e509000011303007407020b950030612119500400455480c24130f902101c0250b04007030b5050790803080c00800002d4900341e0324841c5000c0c40c003d80080c89260301c0d2261420740860020841c004106104084c140180c0311012070714000c02e44441100e000442c180203461038200d440d8240c00070000c14140c400003142002c030350aa009003619004074000301c00d044003030b00c0920500d641078a4645089000113172159102ca00c071340c18080121002c0703055031160910550f4900c14042c001c0c1d0301100078404107001a026080d02031070140b090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893972392 1250 893971142 893971157
    0x31e140105010509150f031006020c0d02130f090c080706090f17030c03120a0e0613031112040f0503060c040e360601030b160210020f071b0302040b06090916 69
    0x1094101c6038200780003000c82e6110100501c03510300c50595403080030f408030307100808e41c032f408850003d5541c070240440039000e8114050480042d6405420070b10950000b0340b001e120804c9a840c1800003807802d4402c50544d03004103180400c85a200d60000003c03540c500281c00810381c181103480300e4071035046000c2c44840c807003081400310714602440030f40ba00c940036030f041500602d0081004029550841c051440f2a04000c0400158005416600c440d070790301803906801002c800b0000501c1c0c0241e80712200a11040400c001031028014031952055038800e0303060b20155155803502d07900703a000c0d50003088011402003000640300c407000c12143c2c450300390700a03001e000a09584c2203480d060280500d260301c179412010051044c0294000c0d5070ba0082c3c032a4082c4400e410f4440802912400140d6034080740f0740e0006800c8058100b000705541070306030003600c014800400500038040607005844124006d6040450129140c40c01005643d41c0c180d001d0001c0910f03545030444411481440c420090500881 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893973642 1250 893972392 893972419
    0x90a170a170706050c07021807030605362403030715020310140102030720030d09060e0f060d0518030a030209011e1b030519031e140105010509 63
    0x1000c40e100c1040640e0a51580d58802c00e0601c003060b508020300e80c0d550580c0c02c2103404010303254034800803100c1500c41d08800183e00c3d00e07101100509940c0c1e00456120701101c5030740d44d44001d18a100141d41c4800842c0380100c80c840d045080c0020300c1114850024100201c2c40041816141e0f14840381200040540707192030070666070076000800412a062a00e54013004202042901558500c0a4440d24180d40c80c4000d207040000d40c0c0384500c00c070040a401c0301c50007a502d5000f08282c0c601080318020706454009200e0400204400c009200c0d460001d510400d0000003400c08900c1c94100590240c50246400e52606840000c1c000181c05000d21a955058407030381c810003031025001040c0d44d5a800750303560600b90001043c2c5142c413484641100e011010540c02503130010702d09600c41400440c9a08103c40340c3c00d00340e4490003507000300c2010154540400000c65810b40c003c1e4405022458040d035a40003004441046407036510548240c1501040107010b10340c000d03009064131100c000c02c994280c101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893974892 1250 893973642 893973653
    0x2150402010c022e120c1d210f25030201120b01020c1801090c0806032d0a0303060e0c0a092d0b0304021206070203040905060d020d0521090a170a 64
    0x89040480b80003607613004c1000c0a4045c28024482c00910780e00e041080c5041000509201001030588503100d58110070746019050091856030700200d00c05019606841001a40b2a8036282510412403442611141074840c0b5038500c0e0041e01030303a4041e51454401403071041c01c00010403900c130a20703056100f01840c1341819680e194140c40000300b038415008072940341040a400351000c401c08030083c48860010003200d918001440c4801c0c481080c0e80c1c03200c04441400c02d11050900b00840e103d24001c540450301855016040f050454031410000240c550356844402d8540c003422440c0400901100c2003003026001c1c000100c2c1c4075034082d285104600034140031a140c4044640d1080d0303903081000c01080151700e4000b400c10690a40a0050801442c04401c0251644554014954040d40d92404250a80c40e031030f0f000f51101b83c1c0642a00b40c400081d040580d640c80d403040c01060461584a8088050140e42c400d0710b502050180000c000b180c01c24441100200c461203420410784519041c0c0c038040ba9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893976142 1250 893974892 893974969
    0x50601090b190e060711060919090b030601050108130b2508010e0c090112020a1803050604141903110a05030f0d0e011b08040f15020a02150402010c02 66
    0x451400075a541c81c240400050103c003681000c9522801091080b40085001e40400030701e03c0c00c0480d121550303807201c1000910f4900901010b00c4901c11140d402241c41d00e03856114000e40b8900700c046900703903a61000119081c1200700d41024044680f524000009020b6007041508400602921100d58000005480c00c0319211070034080001c440b03200400000300d001343c001c3c0d00300d01f081c88458640001440040d20442d0400c2500d500e0550000b8003460300c51007000103c940e10403a02c41e03003807080c2c1d80e4100143c0d030b40301c00e88041d5030075400e1258207124000001a2a1030240508502a640a6544d24251004000c003a00241c080c010000d8100020380f0a000801f0910340400f0415159854000034104030790f400b6458041d10303854011140a40002c1144850007240b035843c041001d50750f14500407440f801400700c014204240c0380130602801525401800c00e0032080e03070849020307824029030200400401d8802902207030303855042c2d50143c01c0c04401e0089004616507020a07602c0c0304590b107008003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893977392 1250 893976142 893976157
    0x3050d0903110f1e0705060a140c0102131e0311060c1905071d07120b04020c0d0f030b040b09010e04141b0a17060621060c0c010c02120d050601090b 65
    0x80d00310958284c00c11254120080b03000074241c00900b186820711001ca0360612401580c007003442410200301d682c2c49040001c882034281c1d140029501e4200c004010100710000c0d020f15501e4040034034400c401030341105002d00880b0f4005501d81c1006000406010140d409140e4100d464040d50110900300d08110040080c6e0f18811002829001d1800802c4080c0300c0b26040d045100700214018044a1503019002104200380c1036000900304c006003002900901c502100500107008440311501d2150300702e0202900900e16071400e1042050840401c0100c42c0c8c180310050b4010b06420050100009900800d58098071030703d140300c640124020381d54a445208446981c1000305440301440c00d04202074000020120f440ca00f10702d100f41c5216903901c606d8002c0c9050302801407a082c03120041e55101c610140e08501c4000c0c1d030f1990a151207281e81d2139210107003c02c81c0e5070030b244680031041c0c40042c0a231440342403070380114100030131100d0031000782401910782410403a0612020a0140134403000f002e81 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893978642 1250 893977392 893977423
    0x14060709030624080d020609060f06041a1905120f032a030301030606050316060819111c1d030412020a1a090a0f0515030901060f03050f071203050d090311 68
    0x1e030445c1c4028601080185a0f040540040c814084034901c42240f0f903400900841d00451402d4440c101224494503075101950302200403042c5d600703a04003903140842a0790003525000c610341580d150f61981c4135007036007920480368420805480d160b42000d040748407441c610700b01001c2c2c00800c070400a1840d002130f04141c5a4964404003000203140400c035103090600301e46441d0000b030b490900e01620802e00288410041c241000d04a2170003140c81e445640030400941d1800c2d02d44040c64002e021201042043d004124079200040920010700785486005040c01c0006514144c141000c000c0d4100c584d0008a8104008030707008220781d81151401e00d0b12400c540c103006e4a03142e50f030040020302e83c0ca5601c070b03044480e0a40d1050180f5150021440007284428400590301d031554000d5500400c1e1507800360003065031050000c030811070045080d070440f5454100700c5008544400802d0505140702c1c2006000c90000c01155140301403541002c6001c5010342030068030401c1b20b481103030600ca01450342d41007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893979892 1250 893978642 893978653
    0x30715140c070f0801050f0c2a07060c02090604050907170c1f18140103020702120f0a050d0e0108040201110a050d0801050a090203160516050f03071406070903062408 73
    0x1101c03a00741b003066440045080c100c6424281a105203070207200b4000407949880a5981800d02c009088107506610815a821152034a50342c060003081441e00107803c0784141d0030100460b00c10316060207440e00407007100e0040d0078400e1034054900c5284c0103c0741c00220500800048a40175518603c440020404901803055140d1414400501d020000c014080c0302191600040c42000d0302039841100b0300e102801d0040c0e54090500001d030b8413884d41a40a0041c1c031a0901d180c120600115000d801548540200d03980d0384500f08040d18141360402c910f0340006e11140001d000b543c071aa82c150201210b08060b904480b1035903c603982007258401c02d1601050070b4000400190920203481d60041880103021403c41c200b030000d80400a0b42011440c040000204051840202d4104030940d8182e00c00201c0755260f8102030000c3e180e4200c200182c400041c0e0100c859489540807940e1441400309a40305800c1350f080da500c1d0390050145202030403030361030f003a440c1e5541d90300c00550b00d00260a00707800a01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893981142 1250 893979892 893979899
    0x1060e010905010201020c06190204090f02070623070c03050c030307020c0f0330090d1101080105010801050609190f0803072108220807030518030715140c070f 70
    0x10700c00d151551100741161710420180c0c105081c0441c1c0035420141980203010140f050f640200043c0c02180c0281010780c2c0b80000c0c031615140306038000c1001c1440760005000c1107050410480c100340205680700e1104840c0000160700300c0c420600a00005e1003400d0503800d064100030150b2031508121100005a44a45a080c01c14501009442c0801030124002d007440010384015900410603020380b052000c0754014441c8019041c40103864034800301500304e03040e00169003801440e511541c941c0c2400305540b8400452594441c090080c16514090075182c50315020000340001e034809040a064060031101d00400e0301004003908000501d4000015a1208444c0c01d1584164078507000c61540001107140c084140d941040b001a4030919090b81c0d00046008441c0380546100705000050090000080e582d0801d500000940031a8009a001050361180e24040c596201114004d468031625198450303c8140d00c103881002e400140c0c880180d0426070503c180c503141590a8001d80091000300c82e050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893982392 1250 893981142 893981147
    0x915090f17040f0e060609092a03040c03020105090a090e0a02131503150204080105012c0402030615180a090506070e0604090203060303130e060109060c0c05121501060e01 75
    0x40c815101c014603080c90011140908a40d511620213240c00381000241c40e5540c6605840c3d48110103400f201d10f070310b003d00154001071200c5055417661021182d0307007807502d030400050b00c0c13140764095503403400079066800668190308103012095200c145d072a404a1040c040b80110100c1141d4080103120503900c1e441040001072400054503a0f481c0307814561030340044040d401b60220f981040b070801c820b01a001040c00a4844c541100b085507080c18000126004802004209800a0070360207095002e6001641d807142d41c140e401942c90f6000102003410300781d00182006000038014900d444550f0040e0032240355540441d40d600e842603550480400f408000e0104541c05506440c0000c1c002e100480018018010b5006040ca1b0f01c0c0e02000182c1151800c0040f60740350724400d404c1c03c1c290b03691410030114040b0700b01c880da4002542182c001403e54041c031004240580d015071300c2c45943d4101701c240504264508800011441960745064541c111418060b02824a560340c8224507a90617001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893983642 1250 893982392 893982413
    0x50a060605040e031603080403120e0703030f0203031902090607021e46090f060303030f02210601170f0703140402031b01050d0c05030a0b040203060d03030915090f 72
    0x541c030184c20401480008042a0852032140d944c1410a0f81c0d0540b41d50600300c2d00d11309900d61540b4264600311144464090001e0400e08480c46507480d009030900b0740000300e0302c0b40800d9600d1515407200403480c0700790701090b03005803904590141100b03041941980010303021000076424425140d40500c0400c03202d040000000c08100480c0c40e00f1840142c151074000d003805030008400d019402c0b034044468160b00031488036170003080d8807081400449079000302040103040d544006c40c082860858010310300a85e030700a840d102d0001000541d26006840301c1140b0b690b42c0106283c2c10440100b180740d45c0140c101c4040d5005024258260b4018030708070601808071503944440801074041030003000010f980029055041d0304ca5040e00e40c000c48004001601d140c013074100c10420860400e400b082e1500e80c420040c51045007194030900195444000707002c201c0c032041d1205034000c0216010600803d01035084000380c14450300d030a42038019001143c0003160551441200da005611850f18148400c0050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893984892 1250 893983642 893983661
    0xf020a170c03090d2f15010609270e03160507080307231c02100614010e06070f0f121214060f030a06110318030c0c0913050a06060504 59
    0x180746051070204680d4400001079041c1c10440c1c07404000c0c5c08094100744011615482d452180c00035844801010b07101c0d103081c0705030010040b40c41c00001d101441004500c080b201c41d0800104680c42e1145031815110003032030044030590316100c102105507001c0005010880040c150300c2a001024505182400c05540c07011885078024000d0601103401d02c04610030500c1c803103d00ba5070f400c000340720290600c0c814108800d401c50745072681c0c0b40080d801040301005080c000e80100302040e03c0c1da01c2480702c04458a0050300040c009601e40d800380c20500d008182c034902480d040840b80c00039035595134416004003001c54401c1482c0c90301108594202e0308201c043c2e07000c0305041c09600c042e55001c000c00308000703041510803d040c014000701502c0621840303100d01d4000006000300034052400c1e4406500984e60807280d03c5804103c0501090040140e034034120106010300314200568042101052005d4802c4000c6200c1040b10070020710200074141c1c0003403160101144440c0b51804000494002c490b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893986142 1250 893984892 893984911
    0xb1f170a050d0f02210a0c061b0503060310091511040e09030d05090309010e0f0a0504090b040c05060c06010e0a0f0c03270f200306041a010f0b0d09060f020a17 70
    0x362417051144010141c501c48480c914060511940720300300000644041510842d21008015001c0203865010004501c68841035086800d001900c8245000716146100c0182541206180074203002d6042e800080c2100240c4000c035040039214501701405010070b0b106075480764400518815119031600803a1380c440903803009107047c030013034070300291040c5010071080d40725015051805115648048600d0082c18001d001048515600e00d0101803190b81607e00340c80d030400c00d040001d050302c1c0400840e8a540c044001514003a403038111205420900039008140d82603c540614080c00c041d0f02c6508983c1001e9540441c200640c81a070305600520303203510900c0626203412181c04a105045501c468660002180b4201d000080195000300901c1400d954180101c10a02041c0308212180c040d550000719038201c2d2a0340c0e1508100c0d8481e07000d200340340304c4078018051007000d9101a84090841805088041181014038582600302d030320000700c141c0800d2207403150580101910f040c45a0011204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893987392 1250 893986142 893986183
    0x100608010b0c0a0303090309090c180503010b031902221505040c090608040c0b19082202221104080106080c0f090721090b1f170a050d0f02 61
    0x70441a403a0400f007403001c3c0a05407118280003c0500c54519440108001402000007500c500c03002443c4284400c5815403003d8500710100d410f00c2c0601c6020012039008000300f84a011301ea207081e1009a461606a910065007920303441c0e41c5008082c0c030384034a0031070580040c101c0305100600c0324121071608494016880c09943c65a800d4020300c40d03009580c6181060300d9290742d5450600ca10302c14036000720350a81404a000010741c0c2910700003002c040b1503a200d14525503221282d140d4003000095007181d0b040f80034001c020150134950a003084415800c10a0070320f5030a0003904600782d451110b904540c80b02d0000c0c04100404007803080310040c0900e0b0025000d8101a4070010300315608500c072091040e500c2c900405c040380d0240c00030940c02c46403502c411018580d404881002801f0f03035501034504030307001000209003108440f00e0644096084808400c0b031420900b429900101040d02040749109041e90800855030400a00301c2503403160343c5007030364440c2c035403070081c00d02107103004105401c0c002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893988642 1250 893987392 893987407
    0x71205070e060301060c140f010b030706020a0b130203010f1a010318050604350406090e27030708030f060f01110d080c07020d151b020c0402070c0509100608010b 71
    0x2148110390441d00c0750b2030100d81003603440c180105e20381d580c01d010490700d1040c1e0084c50340c008c0f0190051a50020704605035aa01581c542040e604e40605c0c4000801b030258180004210500303c12840e0f04460000d0700014000e501e00380715900312030880341c00d80446c0e0004918a1150340c2c0c540101a900100d00649203070103241959555540c0001400003480c59000350510049a0922105811602000c42000034805031081c5c040700641d1050160000003910080045090306c03010340420b000e07140c803e1054821541c0c50100410012803a0500400c5000030000304000c0791000c0b0145000769030901c00c800050800d0420400d03003c401d90304440c18490b41e600d4890201c030300414200d8610050b401c10380219506c04007203500d103101e035610007940425450110018400b07180041005104600300c08c114800c00e0003600400d40c00d07103005100050340242440070381801d240c2c02910605100b0742258008607128400140a204101c4190100010100c010403240d40e2000341b513401020b0122400d81790100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893989892 1250 893988642 893988649
    0xa110f0315040b0414071701111603140417030405040b121005090a170d150b160606050a06050a0807050711010e0a030b070c020102150903161a071205070e 68
    0x81c0100050b020f940e0440000e424420440303208011000b002080e1500d2980300d425a4880d19403a0030444001d610302041c0e02746070341d400802c4440819619a0580805440d82d0341158070048500e041d055520052200040d8030124051301361216140d10044c58490342082d081c4000c650601d0182d0f07108100c0300c1c0c7c5e9080d80210200b04090b001000b1a8080f079290f848000480c13070100e03c540d0003004a0302121110020010540160140407441e9109000c140300c03800300c1e040038030400e0241c2c0902c0501004403017010741d241c0b1100040584038103404a1000d0360b400000725000d5841e4084004140002124099198024a2a070b07100a5a04007076080c103c084c2c6a4030b0b441a0b02c41c8140e1b0501c501c0c0c0c2c0031010319550b1a03c1c404011640480c00300d0701c80c50940c1000f0008280104124054455450f00c14540d81e00032031681d2240c81c0000080d4103103565031002d80e041c203400034802ea075026801c01049c0c01d44026201414860074081c0c640300036a0f62120080d2084800041c9403c041100f0508800080e07503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893991142 1250 893989892 893989933
    0x50d2301180f0501121e0210030507030c09260f0a0305120a050f0411040b0307090b131b0c080f0a08010608092a1c1505220f060e0a110f03 61
    0x64005103686c100340c140d07005c00003120b003507204060340c0251010000c5100a0f490780200c2e100d061107540500442041c181c055943c10042c0c0540c210608a01b8184d00081d40181024859204e00c170040b110300c540c00220807800c1c030009107003e40009100098004800d00c9000d2040d801c150310150801c00c07490310881c08100010094001001452182400c1c051680c4541219172182d200505403500d1903a900455401031429060150068081c40c050014106091050040c6404141c9a07000c0c129802c0c0700444060b12141001c6810f1142400104a040c400c0c0d009003003c2140b980340c01e8800e505104d4080d103680401000c00c80183c1c44041c0410388182d40102c2240f1180348801e854500310041400612030300e01d5220215520325a031114001032000b080d080900035035407400204001e40318a45000c1040014480c010001c1044030070a1000940785076401030b0440c05201c0000c0c139030501484d0a401c1c2042001d003500c0c2048024543d46041c5400e401a41c41d161080703004080192000c01c050b40e950 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893992392 1250 893991142 893991179
    0xa03050c04020f040b0c0109120e03061501020304030c060206010f1a1603030e01090501020d0c0801061707051215010f050a0f03090507050d030206040302070e0601050d2301180f0501 80
    0x101d40120f0200b000c06070f25030564002d010034800b4980c0b10700598610900078100c03250b05903044012060b0102100e401030407260300301200600601042d665131030000305080d00c0011101d0452100704000008030752007020003405844654090400b551600040100351032954100d070016481210041401c00c2c0c80b08121102e20006c112507100e5041241000d60040c040316200400303a5003050320390300070404190300510714009082020030034840d40100071540c03c4001d010321000b03d01c0a0710414403c1c450a28038a501240500e842403400740e0040074505603107410b030b40b00315501c44036070820f001660304400d245055104e540741243c01e00041010081c410030205400405040e580c40544080c8a000c1c00030101403e40908030215101017458002d644203000c440c103034014041c003180070410b116541075003402040140c6d07030039042c0b004680b19040201320b41c04143c001e110001490080c00c1e81020950341c0208090810703403020301111403411050700c044d01c03a81c0a04a00d0080103010200f80c8003241c0284 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893993642 1250 893992392 893992399
    0xf091c05040e0907050a290c070509090c03011d0c03010c12020703030204030f030206010e0a020a02030304240c121409211312060614210a080c030a0e0a03050c 70
    0x65120f00c980c90381008660740060740c10101c2080b001c9032078008201003c4060b4203613a541428010b5410307810405000700000f12216400564080140d0710304080441d401c11601000c0d22140180300f0000b900f1100500b0112440b0f44910000b0704200307205110300c013000c0300d040e0004c0c083d00d06c01000040039070f0140c940d0940040d0740070a1540078140710340e05a80156a10008591100440d424041d68403c400d10408851181075000649511224020f841101c1d190340c0085085460f01d580d54000c03000745084c52244540d1115103d464180325000f100c801e001c1e81d480700c0800341a4a2806e80a0f00d4440c40a090005144010b00c86201d80c0002c0302d450a4580b41485007241604070501d0a1034401c0710322442d400c80e0002d5000c209190503d40207500c2c248580130400c04155205020702c03c41500e41903966104c96002c04010007103400e1900c452030380848105403110042c960f40e4201640d000614589602c7d0310202c0e44d2190150025841c03e0b1081c011035540040501d140d8681d55101e0140c19074602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893994892 1250 893993642 893993669
    0x402010c06050702031b0c0f01210903050712091e030f23060f101403030703080c1603050c0c030c0d12180618140109091109090f091c0504 61
    0x610304c20300988000c203881c00400d24614401801c40740d65070700408a158451035010401603403541c020001100d0300034649000261098120000d1b0f801400074050650604c0410008600003400c4000c0310b40c1d0424035038490365070aa003001046910392005e00e40c8032070b0310740c2c102d00e050012030350980520b02c210780e000d18514032000c00c0d800c254400aa0060740d403243e5200307a5003400456201800224412114109035078440e0359521200000c08580b144c2290301a0010001800840d01c0343c82c002c0c0c2d1048848003841e150544e2400181c04440920300f0a8000403c046039155002c1001d2100104d9000210014040c9100c8480007400d60109c0740c0f40202201100a1006900d1f8040c12a0803013442c01030313103188600d540c1d0700406020311200c003003000c0001d40000404103200c00344503940c00c10080103950b0301541d1820446c10310300801e900300184140301703420310025659640300e0302464840d0300f02201320500b5040a42e01189020380e0441740031110a000000b44400d00c0d406002e48045440c1d0040c6040b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893996142 1250 893994892 893994901
    0x117120d090804030f03080603071409090c06040603020702040b040903021c020a02040516260106050d1407031401080a03050304060f0b10020d020d020303060a0501050a17090a17030402010c0605 85
    0x8020701c220540181600300125001042c0401c5c5604c5c6210580a600c2e03200a80d5201c204040d1242c0150140c540c00710301d024803021050800b42c81c0e940c1c2c8000c04004036443d004c058070000300b5581140c0c4c0100c000a800040c50000c505250103070481790703c01a1414000000d03544d0b00652214402c010000580e101592101140c40c42001072074420340e0068010812424100d83c0e42e5442ca80000c010030100300441d64008004c0000340c0300d04125005940c07138030b003540d0030300f03400715090f03072050002c603003030985906410540e0381c06064041e014403a540c40c0040e9070b41c80c606841c1d49441c4160b00c4a1185d40080d950300020030b40000403280d0260744000c00041e1850714000810050040114958000c900e00c02000d000a40000783c03130040007082c0d02151010000081c040703a491004407089500205070f003100b00920350040303000d05180061801e00c02c040a124156120016000711050b451603809074001c41c051100042815000210800c0343c14990715282d00007070320414403a000144069074610026 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893997392 1250 893996142 893996167
    0x70b18040b060403150b100528051c09050f070e04152702030609010b180405120d0b010807091409090f0f0105090f0a05060106030f060b0c01050f011712 67
    0x1900a1917005440d0080c003441900188014000644040e002d081d5441e0000300460244094a03421302c0301d088449007000b480c8860461251000042c003050040900c0030480b0360441480c442750f24400e0300c0001030000c00c00d0809500d41801c0c2c03941c0ca00141c00401040c8240d140c03840100c4da12507040011400440c400075002c20050201104040009c02183d560b505155101ca14548070780c0d00880441c0c45544410004508849420311510303800340f90045582c000405503403050350f010340298141c0e182764101d440703205040d910494003014601c2e070701d01d5503524640c0c011500302d400c041c0c249040702d0320b01d0510b612186102c48629415104418070400540303240010012071035000c4000058840351241c0c80f1065000e858199010030320343c018a4903100c0301c0701d0001040c940f0190030200801e00c51346001d2041e40108070a90400e0910f5444801c04110b503001030700240300c1300740710100001c3c2c0c07031908142c0090a50340c1030304a8505200100d8408106650004406128190040c80540c4ea0310040310f59 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893998642 1250 893997392 893997397
    0x11190912050606010e06030106021506030102220e0f06010503280c050403140114060d0c05031e0c010c11040c171f09020c0703030e121e070b18040b06 66
    0x80d00004880180d0000c01101040c218003406003a200c0a0500d1840010891180824040e1400603805210001c880c09404495203410075030103400189081201c1c1c01801d00c0e50040c6030f508500d1072054004000030003440306100d500280c020014496801e04100003001880043c1038000c0400d400c00b54101c010060400790400741d90031410410100c51031610240c1142c00601c41920012518080144003c46c10300840400304d60f02d0100b098287d4031201000802c0910300416a901d1891506c0401c071070300c0800250008845128030301c000d5001b0f00f04402e1801d02c081d8030302d9040041440d00240064000844040c0b000c000304d901042c40500c071081100e03d02009005484403803900814009403510020314500c1003030039898500e000d1a201c410000c1039200c0c101e5150300587c080302080010078418400c03400c1c120310080281181c500480065440c00c043e0b020301502003003c800c2c43d0000188204920b0000300803251460f0f04160500c011030416429880c080c900540e120480f40c0030035a180d204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893999892 1250 893998642 893998649
    0x60c010f0c030e07060908330a1a0d05120c030c030d090b010b0a0912020d12020d03060f050a0b0903011829010b07020f01030f0207050a050d03111909 66
    0x1c00032910300501c028050324000040c078520f40078000c800308242c1d00c45d0707403084140d0342d1581c020138030248640d4050742080c0741d10b0003d41800c0d0710390102c4043d0b08109040180140e2840e1004250880c640450888110b00f58501600c21a00064000c00040700800c20841d14017140f800c4540312101031310200c3c114440c01c11140c1c4507000005000482010365402080800d00a1504580720b85c1c94035a83d0300f040c81454200004070340c00600802641c3d5801c3c40300014180b0103045050380720183d80e910000721b1b2402d000c1d000942c11040d030000c0700d540e0610440b00104941c9110307404c900e2400010030000c0e50075000d018481d0800241c0c00f03903561401d400084094120030b003410841030392410008404110b031600301c21a801104084143c51928180640c145c803407581341c45182149603070800c61008050031030303d414181c81c0c0802418107412440600715450041e005441b08401d2880c0050400c20300d58040c0043c54034203240700c0380410a401c00e4450042140b5000b1104100340e90043d2041d80c2280d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894001142 1250 893999892 893999921
    0x60427020f0a1d090d0801210b040809120c0d02010804050f0a03081609060e04050403200c030c031216030509060a17180d050f04090501030506040311010204080a02060c01 75
    0x40068218012002c41400140c001004006074032213807000c50b1a5000054600001044000103011548180b481d09141c1c810344ca55a178004401503a94501c001402c9030b09980030107000c01d0210b0a420030311142e90b2880340c0b541c0034001d04034429002811540310f411010303042042d414001400c212040002c002d400f1030810407103054854501e00100482e000b115400180012a0b181e0000d41d800b0391030380360a40c0c80980301d021402904005000040c00024420390410255204054100341d01601d98051107a40c2c1010381582e440e500700340b604e440e0f22006c6e0140039a0100401cbc100040c0c4080949a0b51105801d400080e66000d00b8129070601500c6a1181d104400192003910140c2140200184010040b444149580c420f140c0d244d946102d5940492180c21034840040618841da004040d11a030642c6003a0500f500c0d0b034050011281c00341c00c101c40903404101800300381078125001182c4e0816510080d46040c0c2044080c0e515551072000003401100041030310748021000f034124500045c01c52 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894002392 1250 894001142 894001159
    0xc0306020d09050709110d020a0e090103142119050f030f06090108060f01210c0803030915090d030b0f09041a070203040b031609050a060512060427020f 67
    0x309010010840100304403050321a013500090301c076200703006509110111400141c20040b248840764046d42c807040c004400c110f480f100b00d918036614922042d02a5005072a8030f25164008200c0a02d05040e804029007025000c2d150201206c5c000341c02c50759440c038070b440040780e410100507041d03e1074020031021248180000c81048492040c50303050344c0c400c400494144881d40d9850450310f4491405486010840c0d424400601038031408024080c151010190180b41510b10350b19580410080b40e04040f120341c00000500100c0b003010040040400c03a611400b90700760a0030342c3d81d00d40d10812000e81006140d00d800300c1c980f0542e40c0b80c4413544003420151403540d9074909031400042c0d031100c10111224061007440841d4280e403000080d10705548113111024515102d100e40403a40000010445040010700070010230300342c94901c00340e0002c1102c0e4845544501c40c07101c000310303c0c24006080b01e004926152078140e00190207406004060a6001c183c503089180e4000704542294030f12116401c581207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894003642 1250 894002392 894002407
    0x21140304050d150506010305040302030d0b030c060d1a010905010f180b03151206072a02190e01150c150e0f1e01060e27120a02010b0f03060a02070c030602 68
    0x3e0740711080866001c0802c00c850b58452006408841040c0c2d406401a4002c1c01490f460889660007035080c0c110080c111008a042c40d40000d8007a400302d0014451207890300922015a40c4803403910049100900342034814a00b0320000034400d4083c580c289003006141c0a40d1a580801314108038068850100490341e03e01d002c03030080c901d0700c000042c118010100028140701e0020080f501c03600600c0c01c0e03682c104280e0400c0001c80300515504c01c0608088040700d0000c401651650000d000e030450b54580702965500d8403030043c40c5400141e06c082c820200c4460160300e007a5101c11804c0d085a8002e0840c09a0742c50860118014108401040c1c02441840d4081004582c00070344140000594007500312000ca0140c0080d0a03030f0385178811032000b1550300001c200b480a4001300e5144500c0b01014010809042030f645500e0b10180c1505010452400903803004155420b0184141c020b005840000c043e0701c6400100390740e01d10080503144510303400300e0303413030100440b907102d080007140c0020007076444150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894004892 1250 894003642 894003653
    0x30c070b06090601080109091118040c060503040c0905180d0915030e07090c12020301120308011215020d090605040b1f060e1306080d0903020a21140304050d 69
    0x20884090350485244000501145490070850780700e114181c0d11302d10940d103444511406815810340841d12840d100300003282a84483e50301c800b041c000b002c005416400d01d810306040c81002170308070b441004801c01c1040081500c1004480443d050040000390030761320f031f5170002000007642c41105514086c14140e50a5194049021815500660064948004e05000590031661201d18090b895000a03134100205580ba900c50700308000d4505100300e01000c202ca01c0750881c1e000360000105054045015428194880d146601500b0742c2006903a40450b01d03218030890a0082d41c8280c5034540008840320550047e4201c3c460240d807001007070082d0f0629280018000e8001c03030f6001040c43c8070a4404007681100030008040b560740e0384a15254055080a006051f0310541d91a1201511110001800e03201048200460840c0d83d58541c500380c15441001481f407040d07400101d41c050820040b001384200000081801680708840a01d100c403080d0005041d4001c0f42d02644e400040d40040d40103000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894006142 1250 894004892 894004897
    0x72d1d0702060a02070c030204020d060b04080d020106120506060910150509040c0309031d0a0308040320010908120705010f051801140f04020f03010b151c180b041502030c 75
    0x40380d001c1d54102c0c0e5480040c0030403030007101409411101035940c01c0001d403c0542c020714180f40000070101e43c113603c1c0c07030034000079910580c814241a030110302c43c00132040d8288125070151440c2c003c0000d41c8245500c4041c2c1d184805400244244000400700b0f21f41c0c0b110702418001082e03465000c89071281451405030064000300c00a500540c2001e07900311059209100d4601001c0d0306031140c1c40c8600562542d03080d0041c0d80c034119500148a010080045200d540150004512451103680e00007422280ca4250584020404d4144443c0c0c13001030019900c04545210840544c084440d11481c45080150240c0015a0082241c6107010240580c01c41b841401d5a00c10340641c0080c0322088048564240107039048800c8404132111601080051034000c85900d8241d800900104d2036024030780c000703000481d0381040501007050002c1c04800900ba1404861405860880c04001040c1c1110700f00885c00300d400340090050410000007020010003403062f0f170008040c02d030115101d1500900ba007201e907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894007392 1250 894006142 894006151
    0x7060f12060b180a090e10182a1a030108100e06072a03030605030601060f170601050d0c020d1803020a031220070f09200d180c090e072d1d 61
    0xa0409180c41d04040c0d800480001b1a0751040c070840c4881c03d26170b027034000c480d0b25000480952000450001d103180c50180d0114800040a58107640d0354035000020f8a011801c900302400141070445030b149210b070114a07a58055554240140d01c0c202d0000140c0c44110800801e50002e0740d0702e0000014103030701d548600c040d66070507000c460982e40c80d61021b884d44400011442c0009000051111200b45031215964100c801030400d5824000c80302802404d0303804001040c40141d000740391446031140e1103445c1d00e030082c580b40c120700812030842e00810400e812602020700100301c110151441580b180e02101c02000c010315448071450030f0007800c6030b1100301611813080400801400820070240c030f442108841c40740c8560004020310341d0640c241d055040441d11a00c1c260f80e9103a607040540c0d085422034102c1e48200c10000d4a03a0802c41c0d00300403201c0700c2d981d040c202d5100e40402c0c000c0c00081221080343c00e2806602c1112041c049070000700181c955001302e200381c03102c850740b0300108980701e231b1b243e008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894008642 1250 894007392 894007423
    0x12030415020f0c1e1f140903030403110a0f080607020c012a05120f030a0c050301030812091e0f010c0f2f07060f12060b180a090e 57
    0xe940001412a03651092150600b8280c209104111140c0f9010705428254244482e49145034200c0c0800183c20461100c8964000103801d40c0002525900c005c0404600c50500d6506040840c8100800d075280103d000c000e02c941c0401840c0300e410ba440d10180c4004050442c651404d10f521489a07030b844400c01d4072120054443c2a00707000d050340c042c00034906c060410550165802801c0058551703070300709900701030f1654010061070003c0e44103001d0083c1200160300090b99602d041c080c144004840001c041d034001c003c000d0005100280507841121000400ca01c1401c0d00e544549042d02d0a01409020080301180f0f200c9001c400d03442d01161140d0201c0c01c10f002085091805c03101694090500740340030780000d800d5034034604410031a4085d6030795842c2c01d1182c081091192106240b90201c13940010b40860001144070780d5041d0300807059009206416010b214840c601900481036006034088148460348403040400e098a503440740c580105100d0740284a00358482c08016250759505016010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894009892 1250 894008642 894008669
    0x60807080607030516080a09060608010e0609030307050415091e091d030a050a02010b030a03020a0c0801060608061002010b04050109021e07200d08040914010806070e01030b0609120304 81
    0x5946000307101c4c951144140c800c21019401c4201d0080b20009001445511301035640e00c60b640100790140728000103450b0f0400001108003c02800620340b000040161006034000c00412031403551213026201102d044591b80c0140102101065079055039540142d80460701c40700d0368100840d01d0415100807120b51503006c00030140395420120706c80d00140c080c0c4602c2e17842001680c01061061005000c2c6400303030310000642e81588000170b42080d05c0c0300015001640318040240c140001c88101c44001c01c1000020070007140307000c1000d0414040103208612513541c04010b000c5481c000c4d000307680640f5000708200000d6071a00020f030001c0d001003041c103030840d2200c12108120340c0b044089482c1c480c2c0009119140c100c00503241807400380f0020390180c002d1a981201000a000040600080c0145507008113648201c15031b0107000010581c04036140d0f500c0f1000b4042c0c090740008400b8810307807080c80d02060805a01c800b03c5c0c0e0911802c401e01e50490741c500c61000300e059000c4040c1003600c607494101d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894011142 1250 894009892 894009901
    0x5030304150b0f010e011d030a050102070614010617131e030f021b040f11040303081603063804090231170c06070303050406050f01080d030e0c03010608070806 70
    0x3c010401c0196540491950283d007516580a04081e900020f104283d810700d104554001c00d04008020204076500da401098000420026000d40360b031000c1080c1c101650b940c5000d500901a04034419101da40c4400040801c1c00642c401e0554440b1580100f03000c5903014080001c0c00030740b000200281d00040a1a020703140403480407c03900f4684a40e00e0080c610100e14004110080c406d24086554584d61150b00c0c002e40781d00c8401810045000b9220301119180c40b03015004842240c401c1c2d0b400b003500c0d001c02402210418070b0210512011040040c03007054a03084044c2003502e4104118000309c0c004903000403190001d40003010000911140d8071040300c00c40822410fa080000d80801c00c0b280044000d11400c568070315205501000b0104403170301c01c406900410301d0b80d407104c8003d0300080c1e21a0100414040b4130701a030741d00300840000c0d88043e580b50510a47d11808a00c100500f00740e19407001c1e0301200750404c8000060f402c0140200403403a0384504417541e609652140c03800900034080001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894012392 1250 894011142 894011149
    0x6033c040512130501080a0e0609151509040b04050a021c03020f070e0103081305130626030a0f0e10080115081e07050d0f0501090b093105030304150b 66
    0x183c1c014490302d0030481c034103401c0c03d005468403540104201c001c1551071a01c00c89000040080300d005400080142c218200c0c0e1000403803020000038240100051003140801c6140c94407501c0507405900032041c40d4103625917240150410360240b0020b036001009030b2021015207072440c000f510385807003a0201d4140715a02035500c0d48510030391003846a0044a4001000841c198000925190500700445d2400c1a2a5000101c02040d110618850706596400c01e000303224010302e050405d88482500042c0000262404656900c2101225001c01005460020900d070003200c00c560340f0900104005042c80c2c103940002c0007840244150300c0340c400e0144070484e815010b03c03c041e000311005c5c2e0403204907280d100000240114090280e808003d0100800c8000303075842e100e07100c84038000510103d280d5140c0750b902029a10034045181c41007001070144460300c8000d140680d00c2c0d10002900500e4010114494081c001507000017815900002041000b0407083c21030b1b505040b200384004004881000061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894013642 1250 894012392 894012397
    0x1526010b0703030b120721261c1d03131e050301050903090a1d0f0c040909030e0a0504111204050c0d050f070e060d060b0301020c01090510050f0606033c040512 70
    0x5072012101d16600030700000e400d23052484d095107100c00149403152a4104110380070204400848960361181c074020035042c0c2c0c031810385031218488011803c140c0c50100c0c0b10741c0803007540300d07250740d2500b00c2081075205007844802c0c0e00280b4004000b002640782c01c484980d1a0b074406022288545090030b0007080980081c40303004a0050490f8000c06d06503105064407090580240a025941809000000b4071101d140281a1002c1c420727a211500001c0380018400c42d0f5019810540c40350741007862000f00f480b0048251200040c5442c410155601d403401c00750300340b00c1c2e00061180c100c0450718010050181c0043c1c0075820441100c1294105640d507200b035890a4010f80303800354000306000c02c4c9000314417203412201203a0002800145040c0180c50040c2c00c585440341f04940b07641000503071000c080d40c24400c091340801c04032842d0800345042c000160340351100804882000d10f003049011440804560700e00c101d410505030b0b19881c03811402d0703154600c1c0780c116030864a6100304240c2c0310203044e0300c105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894014892 1250 894013642 894013709
    0x12010e0103050a06110d0e0a05100b1302091504031419031b2103060e1617130c03060509010509010c090501271526010b0703030b1207 59
    0x5001144003503a540c030003924008101050000080c000351504280a00c5004800341f1030400800c030461aa103000c904056040c940351910310b14007681c05031191140500d096500409400040c1da0702c8200000611002000d41c180e10362002c0490003104112031003140070741d413041c0503080b1001c6441055880d40b140c030b8142401000a222002d1140a03143d0407090040740c02e10900c03065241014546480e1140c00d4120921400a51504810040b2240f1141d0303154004140070100d54541c03c26400250208480c1008400076481c1400080c0b000e0b02e0440542c12903551101101422581e41e0030000c0107044241d520031590b51a2001080e6080c605104080c80d00c084c3d901d50010040c986030055034102110f901540141005e800c0da4681d0008104200f405450201403500f114488004010021508280030b220001811607000313407040c51903083e0504407099440c005a40745aa89011000380841164440d000082c402c0b45140038000420b4a4040c2c0c0c1468072205032045c20310700c810455542607003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894016142 1250 894014892 894014903
    0x50f071d030a030c060b12060709050a0b030f04140d02100c03020921010209030613060b060a08040b070e060a0306230603130f050d030e0705010305010b0d0509071a12010e0103 77
    0x200b03500024000c1e546150018018000003030102c0341480070860800b0009418003040e006071080085041c1c10007101809401d040c1e440d000d07054241b001400140c480502087d203020a01c000080820100c20031410840b0607080c00c2e194001035402e0042d580b1074805081e903004a0400c0000704484c1e11a1003600c1d05003000400ca2404040346003045200020301d22051080d554080001c00f036240c40801050b400b555041e400d4000710226400c01d0400c96106d080c95500c144400c102c142c1c0c10b07581c08820305d070300190800040245070715410002d48039080140102e5400120103d121b00030150158802001c50b42a0f03200c009141040140d1074108101c00382c4100c1e400701060000c11381d003512001c8201c418500c14140345031044c20507121503103000741c0400302c03100080d211010744030420801e0003000e00401003801c0c2404103504010302c0e01c1140c0030313544c00ea504103a900c0c0e000035040c603010450324006080440341020b05000950011800d079019000f054860204000001010303204044500d0407a60002c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894017392 1250 894016142 894016153
    0x715080106030c051b1006060509030c0402072301090221060f130b040c0f080d030b01050a0903020f130609061419060503040305040b0a0c023a0303090501050f071d03 73
    0x1403080c6400b405003075603110681d103e403c85c21b500200191140303030b0142c07004d034a60030b8942039882c0c10180707000704414505000314010300910700011420245071400c2c012058498a000c242c17601c08600400305481c002e9401441c0b0404804421112510102108900c0045d548156101e000d4501c1d034503400d585075044610403910f100301090300b4682241c4c002c0d124208480c402640c440c1c4d0032800308415000204642c010603200501716400d8071034508450070070b080c1907080035407810340a0440b00c66480082d010b9908003d03042810307a621740f4100f04507000c11204005c86170301d030300c0210000c19850042070304801c813804d002d100a280441c1d1070504074000c00059201c05082a00490796600040c01c200c080c00744c1440045000c11101018129131042a40d440c4203c42d09801040010060720952848000d00c448000c0c1d00800320a642c196092080d001e003650080035840c046000304021600504603518006c00d020411420904039405006c8903500d04041d07500991301070003806205c03441240d145d800b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894018642 1250 894017392 894017407
    0x314010f0c210624020706021501180212040303060602010e06040b04060b01110a0803040606090e0c010e01050d05180c01080f0a0b0a1e091b080a050a0207050715080106030c05 77
    0xb209142014616020020076010764480c103866032181c450410315454201003119542c07440e030401624006010601c020450400c24921070903404d0010f000710061080d41c0703100c8044100c01e94045138029080c00800f1082840d190500030000c1c00c049c0140c1005508012a04001c4d0800082c800e004941090030002161100d075541d800030080b501c05241803003100807181c01c0502c4140a140c1c20b16006600d0342e40d13a4078041c60b284040b204980c111802c80c41c40c000106240c030781c00140310000000c00f82800352440040c4001a04c080c0140611540080d040c0010044044034440c0c03c0a00031202600311080c10b0384500c015070b05003d00b218804010488100042d0600c600c039040000105400341c40e840700907803103a5040c21003861041100c00101d0160f8000c1000d4400d51045182c03113006608148a640700504008202c040c1c003901442e0203030780b240046068078580e6411180a0703035200c0f04075084256140401d06440243c0d41c210801b04c1d11f00700c000035406010740035850613842c1c0740d640c0ca03142208 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894019892 1250 894018642 894018677
    0x2f040b0414061221040e010b04080a11040213090905100903021005071b030809070821090a24140a08070503090106081006032901031e0c0314010f0c 65
    0x12640416201441200e0600f40340a9134036100291078201040c40a65507400c10802070003403181030b40706130381801007041b08020b80707540443e203c407505901c622500401001d400000f0041c0c090300e10b40480b00e0095890000d11460154020b00c0050700c1035007650b103820303a80203941c0101d844000002e03004d03810900360300165070900d41c44140e0281c21030030702801031042c151000003c0ca9043e10110049a01801071044008080180d08001c10602c001881214505071120340d0720300f09011491424580410415025a101000c54001e0300019280030080400c0e03181c415148801303000b517203000c00d000140070490302030110212400700d0040e4894003082d1311052002c6900350b20050859900b0f560b82d02010039800303001d0001d43c04142050310041703040d40c20750038041c21440010f81101803a80c0e0451181640940c2c4e0041300307044135002502000c140071b207000040000881c0e9000108511603452003c020000412580c000c9180080001c2001c0c04860210000b11507032003c40c0d1000c14410a030301d80800c0c1c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894021142 1250 894019892 894019909
    0xe0c03011401290f0309150601052a160302090709050a2303010e0105100e040b400606081f020307051e031e070806010c2f040b041406 59
    0xba01505034181070f01d003a182c44010741058240c02c0d001030000052021505081010180318000351003a10840d050440018186120301801d13041d00c02a03030502400002d801461130004611072106a540146d1944460070b03402e481400200d1182603458045180140715408d004140c40c8041c14010a260500310345841707880c0000000800d0300b0400b240c0e1000d80c0c07002c0c041e902c8080d50400c00840d2504207031030306440c5650300f03070446024603030040c3c108408107065010680c0c1040403146401c0400503000050764240c060303920314103988000b080c4a41e140203041050101040c1c0942010480a51100c80b01078407039100d071180c41c0305043c044040d030440d210160300841d08401c06050040c075040c900c0050300c002240c1d04840d0304081c0c1c4080200710021082501340705403e04a40385400252800f0b01d0003070306115020301094100280e078030030802049980c4c0308600c1c1441600700400d6030310800d010500d0701c0c48000020940194140412219541032500030100e002c54414400082e940da91018444000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894022392 1250 894021142 894021179
    0x70206040f020f0d02180901050a02070203072c150306060a06210e07030f0b0f060907080714040803030a061703070813050901030b0702010b0f0a060c0606050909010e0c03011401 78
    0x10001c915044c0140d0b00c07100343c1d18000414116110b440c0ca80300380341c3d80c2122001006500501d004101c6000141d401056a506580c1d60861840c0c1030744a20024107407007001c0c0003404c030a4a141106000e20204019401303402c42d08101c04a03643c6965480501031008c1e40c42c0b00741c0020440f40030b103104041d0192190300d034950549490004c2d0200f00c106070245819116070080c2c4401c03040c110300da01402512180c0359404000341003070980c2420520003041c0401c50050000f0100301c19200424a468442c6010407401c01d40700840076195520b42415035244d60081e10449015444c1c0400010003001948c004091601144090f60416105807607440032944003001c8020b01c00003002003c680303990340c1c03400e840c06503000d5200308070580f4002501034210380980b04100d1040044881760080ba5460f54416401e650452030031502c680c1d40707407030024083c00c00c0750402503000424008019084005520103050383d010a030480700162008000e050882d052200703240f00c0307001003000502000c0381001088111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894023642 1250 894022392 894022399
    0x203030a080109150302011224151706061605030906191e121508011803110c03060106030e1908090103200702060903030705030a0504180b2b140114070206040f020f 72
    0x80503ea402ca00950840d10382281385540c2c0620417482e1801d50bc040801071015000340300985500307002d40014524000d1311064a003170b071004903810b0b08105040c41541c00561018200c01e860301d00d400300441011018404810009940305103480d55003501c601c8500d81540c0c6503c0313550032030b120b12100034054910100c0780041c4d0f80160300700123071645091082603200107141c0d450344810a001d01d0010507603801035009031130a80c803604140c4410fa90209425044070f031a41000642c0070f003940c0302c0a0508210281c40f90b4030784070205480007440031680040184074400d036010032156418004070a409060004614610380781070201e400103003810002400040d5001301141e040c030b1420f13070f07416165501c00920a00002c5010a0400c4281075024800d2001c0700604000d0010112000100b4418503410241c00e950740d443d085044000b6690411165034990801c465038610340403190a0341c041d20841e07034054081e00503e00012001880441c1e4207010b55400f038011081d1070819000c1140005094111990 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894024892 1250 894023642 894023681
    0xa03080403060615020a05280b0f060f1c02100513180f0504050604030c1523100302030303074401090c0c02090c070203030a0801091503020112 63
    0x860418406000154810b21021440d40d0130502c503242100154291a0203550184188100240d0007144990042c6210071007030f038000c00c211440e03030070a6040440103000c174500703082803100660160300c01e240300b8a0709603185610680c0000c02d200800d04041c5040917030080451104005180840c80c2083c613029510b0503038108111a504204a025203a0200b05400c2608865450a5940307000b0004810f0a00c42d04114920389500c3d1070b5201d040040c4014200b049800c100410082511500c4101d468802d900700700301ca108411100624041018011080481c0c00010700c04190140009094a42c05005142192603e100c10303282683c1042038000c80c1c185207a44412010040c5c2e84846459611007507113254484c1303096140c412444180c204020060038a0040003d0340d4201741c41e0011168107071800d04041c1c0e0758084038000380c00b5004000303500d130200003541241194000c4580b07040c0c82ca2460704102e9170960071031a1201042c20b12000f4080b426001413400c950318a40e0064141da00340780364101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894026142 1250 894024892 894024899
    0x12250206131d0a05071b03030e121b0c0a15030b092715010b0a050904020d0501030b010b1c0f180b0a0c050f1b070e0c03071b030903020f0a 61
    0x212040300782c100c404546105500e9016100a500042d90000c056403c10040c81c1400341d0018401d488008040110100e0318901e181018800d5005407a858520426281250b044400c404415480071844c41c92a206803030381095085d10218001c40800ca00034100c01034035140001c41c41c05119080d40d81024542d48000d520301c10340b160215140304001440407030a820050b4480c3c610b01441c00110818181d0240c04003e580415048203141500c0401c480e040c2c5540311124100d03000e01c44c0c00b80e0a45c1150021078000c20200191700300505992107405241e05036070326800e1000d90b074022003c11244040e4554a40e4501c12001c0d4040140d8403401c400c00315801010300741500521603440c0c0c040300d00e6080b20007003210191052055201c840c88030715000d4a000000b1040d074038103010f0082005440f24680c030260b020103104106490040c8040d940d03683c0c0500d04601c008070f0640085501c40b01051241503444020648002100e20417a415207c00b0423450840c0c0a01c030700c200c0082c95031034010300310a01c0070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894027392 1250 894026142 894026167
    0x1404230304092003161407171315050f090f120d030b0d03050f13080f07090c0507030c150b0d0b0a0c0203031009020903030f07110312250206 62
    0x1031002d822070b05400f06424940d00e81c074800c10703e03094100c03521085040c424881d203103c0708820b00c03034100c109150503001c40003000d4808405100c1c142c00108066426200302112204a201a190751071080d46480301c126640d4000020407402c480c0010006603040003039a45581c541da020f09400350020b02154400020080441ca04a0106800e000a5030010100c000c07550703410302404c203507180c0c10f4500f105129082c2d030340640680508070841d9032010000c142c80403610013001c1e410008042c00340031603103643e040791541610ba100c1d40c01201c3c6101d081500449056020b10201c0300c1056059a6580304940251a00391491402d103c800040c9620ba1845070340e0341d500e0325112019103024003004440c81c245400414101e40400000f101907404c00d008000c000280c62a40c00d089510301380b000b5a4030012400001d04612400581600400c0040f802c801800b6141411800303a14090303089601d03015410400003030500a60015003442c60056a4060003070040710001045a0700c0600794508000c1c003502d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894028642 1250 894027392 894027397
    0xb0c250807060e1f0c0504090e03071205040801051f0510020109060c11070e22030c0c0f031211120a0e12010b03060a05040f1e02120607021014042303 66
    0x1400c01c0c0d101075540f40141503a034030944d5a40340c1c8140200851199080d011b0054000c0d4403c855246075030340441512040148201c45480354001d0307445010030074000000e88140c000b0700546566600e00400035421000b030203048081d07000c0e0016330203800b92500040000d5441d1041c00c007011135480c0c122520003d600350203071244945540d02c404034000000018140741046e1540304140801188041c001c810800e9410503040b080003600620310f074411402c0075101810f0600c4002d2010b80d040b103000800b00b080d5807000d81500c0c454200f04041130032460040780c45900c66008200945c00026004038410541c2000345520711503410008405901c0c0d000082100c000905201b095944451800d14145014072246510000008082065080c00d0321006980c030803040d80244542480f0744040744a61000c5140081c681d8024505c04a00b00f03e0b48446440b60800da88040151081514400b43c10f02c3c03074018600d91250f52204030103580d0341c076151118036028403e88890480c1c5e42c0020803074454002c3c0700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894029892 1250 894028642 894028661
    0x3050c070f06030c05030606071b0b0301061e08100501030e070506040f0812040b0d051503010c1106090c130c1b06140a02120703090816030c0b0c25080706 68
    0x2040c444440c903001020f01aa840c900519040180420400c4201d54550007510121904424480e001d00300303102c12401c1e80d14450700507056030000400002203c40d03003c4480360750490108900c4004915110059a450300306450051007210242028481d80d440395111603d0900284101d0b201c0554503008141a90b00942180343e07501c0d9000c00c14008541e04101034848098418811840d05207801400040c50045006440d040341d2180b011818444030110f031900745820040080104481060014120a24070950314203a40200d40028188500100328115441d802a00240c40b07034400a02007002020441048824030600103607c05600b49951190400d1510506000604e021840f901e55840103005090385000340c010016100389401a04109800004600700428442c0d50381c50090401d02a50300c0b40c4611245940e10030082c1a0302c109620301150103012840810344460310501c2c85071003008400701000c680000c260700007140c01004480c0c458002c0510780c0c00c1c0b00707050350f8130b1040e58554075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894031142 1250 894029892 894029909
    0x50a0f1b050f071403030706090204060e0721020f0f0310030b040305180411070b09010902040e030d06051905242802010c080114010e04050702030c0f030306031903050c07 75
    0x2544404640400519019200801c0003803072504d00000086d40e24410f60100805658072120f111045481c1c0e904000050030004104e50010300c0c0030b0400412042410000042d1241600098900c0d5082482103421015050080c0c0d49400503003d81c0b103900390700181c022400c4031781d052400008250728410f0309001c4c070322990300d00c0d07a90403c403845854814048258644201d18021005003d001440c003107900303860303001840c2001655924400c500400c100580079400905103840b12030703a540c000c4000e1a91103941f0408003d0700f84c591060000c0117610300030580400a07050024841c501d0450111340c0c01d480e00d40316006d4510004c2c0d010003000d41002d0f000c108c0c0607001c01d648048200394100b5007841c84100d480200206403007a403004040040600c9040108040041400f5103030b441107452480006014005000c0b50800c500c00941d80d6000c0980c260440c05108244044444040116030140f10014001c005c9005a1031141059440381c0008805004041088099041040c0042401030030b000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894032392 1250 894031142 894031153
    0x7030807060212100b04090e0309040f0209031009080f07050316110f030a05070311061605060103110a15080a1d010603110a03030801150e1f1b03050a0f1b05 69
    0x40031000a240f40c00780c40303c1d942d40500c44051198010700300503541100c04002c00883c8004005000034110b01c0f80366050754001b410803801daa000e000c10340041c0150315080d0111f03180101300c1c000c040b0440b105988001c00d10142040341280b120f440300040c00080703008106a078a4912000c46502c41250480b00487c1d00f003500340c80d10b0440d0700d000b490070300c0946011342c0545000300d60780d594191070b540c06000c02080c8014245a0600175160041030f2055580380700c00d80c407105c080c40c1c200345940d4282480708503a40800820003901070700345581a40116802d00d0080361740c0d6941c00701c081d503d81d40002c080560300c2d90349050f44c41040050b52400012402076000024502d8103500700941c180541201d01c80c052600309008000082c0d010107564112800074410000071007100c0002ca80e40c407003190403264022a40c5101042ca0b0781181400c1040d800243c03521803980c21494040c04584c80080e1003d07001c20740c2480300c40c03a07a5006120b8400450b0281c071700166818102e070300807401e034103800105480c0d40d03108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894033642 1250 894032392 894032407
    0x60d0c05120f190506130911120304080706020d1d04090c0905090d031e0e0c030a03080708011a0a0e040605040e0f1902030717120a0c020f09060108010512070308070602 74
    0x1c5000f071107840c0341030701010b00c01c900e0310301c1c00b060703c4504101803c2c1c00fa668800b459024854800c8401c3c01c40140149880304808004e681980e40c0e41150081c80e20398003405600041450000941c52001d42c015143c16445000d034a10225805040b107400300e40040c1c58501d0040020700d10620400a00a01d50740005d580c2420352030107140041003140034040c50f11340100710001c260008050301001c1101040030031020000125103040018000380e1a416104844180b02010341241c40c051040340550707982c4030142c0c3c2e54850200031a2171141d8100304c4000800084455a2061955081016010b48041021030b03594010400b110b00034bc4540000350025460700942ca10144000c2ca43c080b040c03240030000c00c0c801d80000e42c441500340f0440d4100c1010b003c08502001c3c00f031158400411a22108a49a44180802400c00202c03201d0803071142404200c544d40c1031800140d402c0c0a108185d54022403603003030500b4480d0403019440400e010b485107107400400108084000c10b0030a22030f07000035845451 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894034892 1250 894033642 894033661
    0x1050714010213060f0801030804140112180302121201090b04090c0e0601091215090515010e1506070312050c28030b030a050d0e0117070207150509060d0c05120f 71
    0x10518541d40c10806d8900040012500b040c0a450580e10b030a10101a4030300c0010050fa00c28801001440040342024446284018081e64075491980603409030b481031407200c0c90440072413051590301040d070020b402c014003900c00c11750f20610319190050000a801541c540b6020400c01c19640b080041c0d0551004100465900100170700080c2505003118483c01c032156225214014007501400f08955140141c809001d010046150581c40748401007080e0b5845101e4003110500c11584a03800c0228030200030764908008003254141031300b650380d0942180701c02e0b00100203088090f240c0c0c20585014029802c0000080c600d16440a241101d48003540f2840800501922600982d003446034001024460208201164040b1000b94524002070503011040059034000c9810102c80a524451010484d00503000109031040c2c80102400d00a00c0b41082c0703040310a8800c40f04943c2d04030700c0500c100c0325134007055003207520b10f1205820864146403260806414005007121310032002418103060010092 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894036142 1250 894034892 894034907
    0x30302010b030c060d020711130e01110705250f0e0a05070509031002130909060902030c03032d040e070c03090608070905240d09020f100e0105071401021306 69
    0x1d078180c001c2d00c103400b007120001e0481d00903104900c8003290001441c20400c42c184146221119006100c0513406140351160401400c3d42c041e4440b156280031150140004041c0644029650000013403403a0b46441c0c22402500030016035450b200740304904041803005280421601409201060301254588415030314103648c0c000c0c000f101801010003101c80180c801146610f940d90ad200000360b0f40d440c01c40c9103070004180c40e038000340000d0b24001000c0100501f907006070550741d00072811110010580e07010145c0301c0c89181c401c045206845040101107050616201210310b0031800550b05140e40d59400c4080110200c480348005455038809a00701078100c048031014240500d09948640380000000c0c041c040701c1e002c2c161051204566001d848a4100c0c00c00c000750340740002c10742c0c0b1103000b404404064212190f04a1040709141c540d207800d41000c008004400407241e44900c00e0120f001e005440c198400c00d8180c1307602031036452a07814800240014004090340a070203c80551410100401c0c12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894037392 1250 894036142 894036161
    0x23609010e011a0315180d0c060b09010b0d0c03020c010203011d1008150c1902010b01030f090506010501080c07050a1b090e1f0e0a0b0609070c0b0f070c050f0703030201 74
    0x4140180000a070782c400040740341d001c010316140c03903801d526142c580074020151b41c103022500b449807582c0c08110650101c80d040c4864414a800c0c01280c1c811810410046000d02071503800400c01c0c07040d031201d604290802d135160350050034010b203040c150031012070a9904c00d0300550020001441e082062403d003800d05503001282c0410314a14504290340a51200003c07982c04d58103201410200700b060b280841243e000d10f841070400b0400c00d501c003501074081d20310603d006020914140c61032013940418003800c1c2c031086e40301c0058800e81c0e09080040d102240046c1240d00080d00030b02501300055000c00800900c140190090030b10582509845008244540c04c0521140d0425134280c512810008114261000c070f49099888031203003680203c004c5c0001004200144540e004aa0501001c14200da00441d000e85e002d050b550b9503000c0990f4030200260000b820720511000143c103114503290400c0c1c029219281a122341d100940343d2034600610f44200c21443c0d00070341001c00400d50248110b8516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894038642 1250 894037392 894037421
    0x31112011d040305030f10091406131a1e221a0102061501050c1b03011a103b0901060206070f1d062d030103023609010e01 54
    0x1031910f035030014101d00000c4d011058258089001c03c0003c400e610f45800586141794041080a4010303000e200e2143c010b03210355001c2c50340c41380c0c550415400d90103990b030089504100340a00d0701203003060000183c4600560042e101c10811040c50315502d46404c91164210700b090302e160700701d6112401e0101d40200341e51b54a44a00c0031b50000c0e8070b0342c011079540d83c0008400c4040d991501144016540b51148500d610800d0254600d170110130a80d410310021103071801d034001c0052041418031452480480c240b11940203900c1c0c011740c0c0350341f445120b014030080100942200041c07a8420103880e0750b008141030b241c0003408150200000c2c140081d03018010b00c014401400c0904018502510240705024a501004071482c040d107107808040b040c220016101805055a48640009415045040b149460210190ba500700e24080d0001ca054030306030394000709860b1a111101413070b010020103694109100b8550f95418110708280c4000041c4900242400404c3c20300c0b80c811090700311003000060802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894039892 1250 894038642 894038699
    0x60e010e04080a020f160f0b0403110915030d0f11150a020702030c090c04231e040f050106050910050c0606010f0c080c01090c05121002090103111201 66
    0x8a0404108039034009400c60481d5581d0000058101d0030101890a130303070351610034400d4200000c6419100501150307100c0246081c0240ca03002e04154a100314440030b010800d400e1580d0140749080d545a6800c41c00d06040340c101503d015020070704142c0e1401d400408906000001c988454201307030b2002e41070030149c000c1e0000c0d8210b9111000c00000280000f645250301103a10b50440d02c00700000f9003402c2009250a015250454802340f803507000d4040d403c0c40e08021001c40304000420003203040707070003001084045180000c00c1c10003200c02c0907000081c2d000d80c582041fa40c0d08000313889218060b00c0c1c50b5490a41d07070740342c0109014441d982401c580c0104a410080d060305580046136203504914240f1702414030250708103084502c0b10345800003400030103002036031800c501c00c1540200c1c0b525108030007540c1003940c0c6504008004212060011032500310440c000a0f60036158024035404c0414100020566071f070064602c8640c1080c00280b040203068030051000c00b21740d0102040d0601040b44640 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894041142 1250 894039892 894039899
    0x11b120e0102210d02041e061b031b0c0915080705031b040b03010b10020c0414010e0a050901021312020a0915030f0507030b07080f09120f0309070504061503060e01 72
    0x880c0c0c0101c000404001e0f0304041039888032528581c0498004000308010018010307680c11002035200e025200b007a000c14080500c100c4107c0e01c03200e8000c1000d40646030401c0500002290403c003003e5464110382d010420700002c11021650f01c102d002040b07192840100d0203040200c514501081500407a01c01e5000c40014614602404000b64066000762804680600070b640400d000d41180741001d0b0f44039800d03580c0c1850350755000400c203c0c0b0f01401c403800d00411100d650f4045013810207009224000ba80c078000105100482c0d045183c004401c20b000501d042c68803640741452840c07641041e49040741c149104801d42c50020144e1000e852404001c000c1c0042001c4810501c000c0391000030300300403c140403101800400e01c983c0d401150840c401100d44c0c50b0000c2d004042000450721017121240800101d2002c50b800240703441c0222100100c0ca29200c03889203005060740000b401480e02d8450300c0340c0403130315480b0b0303006207401005107444440540b0000e65020782911501e03048061150b14940042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894042392 1250 894041142 894041173
    0x807120608120c01020403050a0305180402040e010306020c0c03120912070605040513060e0f0406053315120103050f011109060a0e0a0f0609060e0f040506011b120e0102 74
    0x403511001d500071243d50b50038010450501902481e8000741150082d00046424180c0210017060011200543c8904100a082c2040101d0185004a24181c90f0100050000984d40d60042802005003001c840c008404c400c0082d00e0114509201c80c500d0401044140c45428100801c0d40f0001011000d003541740e0034982c00402c0c50046100d40d41c440e4240c0072030031411040680c404000340c059042c48904c03503d020304c402503103030360250740840b02c141c07403c03000891180106c0f16070702e4004250b40300c20300c440510701e81d0303d24103445021400c0c1d4010021580000e131036800300000c0c0f240300484c0700320707150b10742c0f441c1001b5041c0404c3c00400f082c04d90501a104054041813001c49030040d104480c0b0f181c0700c103034031001110030360f142c2c1c0b0010390000c00260000c510131412983d01ca0032030300315546144080f5100c1008030b9500c60b100c00625000031215599280600c3d107a081580d000b0010314281001c41240078511651900000c01904e001c82e41042c042d02180e400300e440d07942c401c001e00042c840b110416000c3d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894043642 1250 894042392 894042403
    0x6180c030a0f030e0a090204300f15020d1e290103150801090302101b050906070f0209070309110a0308030a1e02040f09050604060f03080306010c0609030807120608 72
    0x40c00c01480d0700c10f51132541e98144013a4080c2c215a10115215602d421120440700d64480901d03244c0c03429869903503010003554881982841c0e1020021003401104d6440c01c000c0c24510400b03046540d005d00038800301d10885e00c00d41043e542804039100070b142d82c040c15002100c0348120380380034000310f801c0c600001d000c580700b09034412070f400c3c607000601600700750340075202c4091600460aa0750030200d820042c580e0001c5c2d1803642131160344080098a20700002411003019500420001c580300348004040d516000b8040c000c1c0d18010703880f10751400c141d680040c0d41018121024008255505040001d0011584604140031030035500803980c0740c10f43d01c03002c610307000c020030700c442709038440410004800c001495581c4010a080065490b80d48502c10710241e520b1a00900100701d00c0d000c0050814500f50298404880e5000c0c401c5c1112070568895000d1a44010111410310942c1502840082c48030710501c2c101d41d0103580c1d445154100310320000c01e240c107030003480340000741002070a101c800340100c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894044892 1250 894043642 894043673
    0x318090c0a053a271e060222050103050408030a0504050f0f01091a04020a0b0c121612080c0a0c0c0e01081e010e120a1106180c030a 58
    0x41c40d03070312a030440c0402803844489004107803062000107040d02102045442d106140b01d070121007880203891078403a0424105000b10408003c0c5810000c1c0404181030b420600742c448030080c1c20f1005c404854440304d00303036405441d03041003c04071061f440c00794090107600ca9014013000d20b01031000d802c058030382030b400317001c05440841c0b0943d452000c1000c00c07408110103038100c400d001c180e4500040007a0554028803218a00352100708803016010002a460100b480c8240d43c01800702d00b040f402d004100c03541c1d0300164880c242c1440392075810046081c0d205d014021f01c01d22681544004001480c0855285005002560070b00c00e150b0b052107144009507094952500301441c03d20b0360054541400c50344081d035039100042c040c60401c008034a9407000700301000a0700035054012822180940d005003200d4407145d1040054000910075a540e030411001003003425030a00c0c08401045420111508101090342c1e0303901034007a02c1213098442c1c4014042d41d00c091100b00c001c0d11a244d00340e26000c000064070074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894046142 1250 894044892 894044897
    0xf04030906030e06071407051b0315010b0703051c09050a1e02010905130f020d15060c030507080307090302060d0b0301050703140a0228080601020c270a0209060c0318090c0a 76
    0x1142c0c4000c8a1b5042985c11040d0070504564400100005d0b4444d400004034001d4040d00400d898400702003210a1030078101c5c1d4119000702d180c00b40944017164581c0000c156041d1140d8042e00110350940c0c0342c090261010f020b600501420107151802182e1a644140703007241040c1d64071114005070b82c0020840d01152819110300c0629420034024500a0004e109203845080c13011610620740d9040b94440500d46a15840c81c540e59602c503101036411442003e002000500b0400a0b2750000e8540300145411814500b0003141c160b40340d0303001070f12300d81000b2503126001e591613681e201245006d0040c81d4100310b86090400890000301e1603020010002445c10700c82a0b000a003002d401c40000f480e141964113050350007070f501c00902d58010719001c425507009005102d0702485214900d40002416002c0000c00802001c0b46074400d20031480c1103004122240b115030903c0005150340303032400244009903805028594490340c40c0c0000d00c410074075030b201d80e000d2031040d07080140b000002e0741150074100550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894047392 1250 894046142 894046157
    0xe0306190c080606030601030b0a1e091103010506220e070f0201060b0301082e050c031b0a05030a18051e0f010903080105061c0606090e0a0b1011070e0f04030906030e0607 75
    0x107802040c07501500345d00c031014000f101840d025140c90390380bd060f0186d03900001c0c240100c11102800704000c3c0000e0040b0340c4c4c070900820007582c1d41e0034900c0c10801d00c50340d080c00d1454090ba544424a10100c812501180801c24407988809015030a204d039101a1081d200c0882c15541048446075a84100d480103000203541c1068260300310408141108298004a2091000c0c0c9051070040e00e80350070982d003a140c40c5030032900748407881ca1051b050b00c080b0603050780c4443c01c65541c0345021000d010024201d00308200c951000d040890018005001c0000e418502d40343c52aa1204d9410710344a030401c20790201d41d140c074400c200001e5212403014111203080703d484ea218008181c047c0104840d8019115040c0e18280d400514075402c004120219420200d000c50301340c7e01e40c800320041d22400e6240720781c801e100c00d80f15610709001d00303010041c0c89a00740840342c900e500c1d69207101c2100003d4441c61172181007541084209a44404c45d0f0f0040d0401d0300e018070580401e101c01c0e40c0d0303a540240050b02482941c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894048642 1250 894047392 894047411
    0xb07120209040203130201180303080a0207060902031006050f37090f090b07030902210a0f05011d0312130303020712030609240e070e0306190c08060603060103 70
    0x255015a80c0701c040c02002103550f410054500e1a0009480d03c080307010411408070a07640c1c0c0c0c0d16596500c00c0780d4040e01c3d00d01055441d541024029440000b04440b1155982819409601c04015003028440c032103a00040f55421300b010840c4130742c0b0b800402c5101d46510501d0f000389105000d040700c0070000e020032700303105014405c42a848001c8140c0054814038600408515241c1b241d400584003103016000c1c031442911400f030214150341e40083c0180d0002c8001d500c1c000b641001c22101c03020007a014040e01d140b00600e54410042d028a4030707090312141c1d11800c218400c80e1403401890001035543c0015842e050003e881d40400c400000c040f2f0840c0400313807a601003894025011070381d1443d4003440d850030312548a08058014151805850606464980c2c50002c01c4a04541c4419800c080810100d070030707207010144092080700800140c200480c2c0c56810320365032070800005028105510300181c00003126003455049a1a0150b800d0800c2039120502a603501e40008480c1c2000c02813a020811a80303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894049892 1250 894048642 894048677
    0x6040609140a15091a0406050103060f1b080604020d1104080d0206040201021c02120c160f05150d021201080f06090606010e0906041d0a14010204030503160c08010614031501030b07 79
    0x6a2040c00c4030020005c04c0104010300c5070700070360599104070820003003503200b1b6007008221401c0b003c201c0e814504043c1c0c0b01244a0144e000035500c40c0004101600d040c5040340c0c641c050310b1b160664030020b000c0105040c06081c0c001d00040070040d0380ea1009010300e103080e40000f591003550142d080300d5240f099100c0a4018400c1c403100d0301141007a251540e4482541840983d0307180802c0c0310488400342c01002143c1c100e10410340ea01101e0000388065140f10705054619090b81c8074005803961a0b07802c008030807601c1c8074140094020100c40018041180500c0241824100024403d50301e40d04500304001c010f07170304040014106130054540114550759140441d00812a04d0301980b000c0541016904e0031000c0002d20140841c130540e00040c00926080800b030a0b0301450000074001e030000c0c85110201d003031890541411038003c08640c46815942c642c0c6908581035a0482105800f8582c1c401e9041c3c10b0030020b240089100d0841c0e04010340c516251010f4400c1c02800103002c2000b40c02d10381301b0920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894051142 1250 894049892 894049913
    0x40b030403110a0c14090c040918060c030e0706051309110c161505031506070503130e060a0b12190b041107050114070804110d0506040609140a1509 65
    0x100e007040324145803032410300c06404812072142001c2c41c00084542170503814100c038068000c41285003110b003414107040741280034045105911a4008400c20403030081040c07030107961903a80d001d880011740410320760b0007182003d51980006007480b008200501740e11140b211840200c800e469400146801d2516401e85a4402e250024031107101d503c03881328442d12100a400101c40b265159008007000f185429100340c001207a07070480c90180300207004c1c0c0500b84007000340649440780c42641e15052018180045d00031058128580443e0410100201420914801405059000012810030342c16a910131041030000f808810000301c02c9021114101e081d400101074104001d10600c0350b100d0f8007100c80344030f80201c0d00c26125503003016007591409985180340d034021041c560320a2081e646507110160707012000c180c0c25800003484101c0d03402044e428442c03240102d200c0d9001265035101c0d4103218207090341088401086800680d00900042e075090301e00390004102c0d54003c03648892a003004071002c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894052392 1250 894051142 894051167
    0xf020603090610230909070e0108060609060d11010e1302042403050112030c08040e25021204170106050319030807090b03040201052b02040603051b040b030403 70
    0x1000c03040c01070369100490228452404100040e508550b0744450114110b4030344100640340c0a6000b01800f01d043c10b021080c0d000b02d04104540307035159140c5030f20042c580c1c26400b60000b034200c04148221403078440c500702c0d00703c0710841b690000940303140c681c00720b4039450403599410b020004103400042c0c0c4412080402c011180c000840d1155505c40561030b12070745105005880d4520300d60396040c11402417140c281a10040103100b03400480c01d54050b14904511b1a056614100900c00014540e89060300ca0b0f1007169070051000c1c00c0b07000032031000d8640403284054001d6400001c0103000513060300003031718216220700c86031381c01c415030350601c140c01080b0b160403030303a0180a180d2105c0d42c4090341c64040c01d00c1c01e02c0381c1d4400c030b4070f561980300448140086000380b801c084000c0020901540c0314201030241c490440c41106c0c2e0b052450300852911040003140d010b202a00410b0410501d80c0520503564410400042030b441d8200d1503214056512460040e501490404004601450b02c21400c0840c070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894053642 1250 894052392 894052399
    0xd05040b03100503120703032313080708030124020f330a0207021f050f0702010e0d0308090d0315050d080f0301090204050a06030b010215130b19060b040602070b070f02 74
    0x51284009041d81140d01503801540070901303109d42088460102102003400c0201d60068503500e49405500701c49400004a050300c1182c02800441c0c04504c012008600815840448446007429103201c40c1c1e00404840c071800641d00504030f41c091501d00820340b42420502c1d42442d0b6165101d105654034009912080307129480d0a00b0104941e0106690003072a20034001c0f2491b419620660415588040ca41180507001510921901c03204212100142c004140705061034050840d0b00c2c000724600042110081e00000c80010520001c507000b03001c2e440850405103814411102424809100030f10548500c5000d140c5106081081c05100001d071541c00c040b18408503601d5070348400c000d020790058000c42d0b107c1e503005403000070902d0282c410200b2031001a0040d003804510018008021440240347c2082070104068001c0083c3e01d0461880c49209951072041000c1c0c00140e4080480700381e0740086403900b0042000b03100e05500014600116040c1041480d5101003505e0000580b03980604000d41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894054892 1250 894053642 894053653
    0xb030f012105100f050610020a060906091a07080703020c0a081b0d03021c05070e09090f0a0f120804020a030807031701090902011806120b0609030d02031b0d05040b03100503 76
    0x606442940101340100501d910034010350b01e8540405c0540c10f02c3c101c034580540c1c440070f03d010000f00340d5001400043d0041c840000d040850f929030340e90344804001c0302a00e10080400700f001c1d141e00035400304e03009455460114101101103000c25030303840c0500000381144c0b10100e80d01ca01e500c800e07101c940d081820321050394240000c010f0054081e400c1a0382a140f14104000e8a05e82001c2d68412240709124a5480c0d06100d180c4000f8028032803005007003130402e40549030142c05042c000304003140055100d006c60011900070f41c01d0042e8051417030400c02007041599024000566146040801600e4201585550b144a0740c5400d444002c10441b41d195942c07200d000000300310003182d10000c035244c001e03200c45c10b66056a01d014412101140148c41c0821404a9500300364840d6078015002c0c1b00010744110b14101e0380c540080e2800c1702c0c0111041c010391000904040c0c402c16092490021941400108003075250701c0000342690065004200b039503407000c00082c0582c90b040111100030f180280580c1e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894056142 1250 894054892 894054913
    0x20108151206071112090f0406090509070303140403031e02030d1e050f0603120906040b2b0605030606011b022d060301120210120e01050403090b030f012105 69
    0x180c4070b4104441d020301080d019001c40403000004074400d202c10041150341303803804001900700000210880c00840d0003541c0e80c5004a19064580710303072401001c664005000e824914640100060300342c1c50790940c040340c00c0c00304000103600020180c562248103401e45100c49503d00b0124910f000301c03460300e40c0311404c0c80e01e0036401002e02e501c4000640700901d000c2c0075a507525520f138620b100e0706885a58256210145020804a280000e8880b4030303001410744c0c0c949541e440b00542250800502e8005000d50281d400d03211520a0310b401c4502d0100c24814000b030391a05002a40b24a00100b000341171002000982241d40c29401c582c040d919402810890250403801d155400d01d05691807078032401408030341c41c0c100c81c0741041c140e82c103c89a282c121550214641d09200b818040c0a01c402d0500030340074449001020540a034441441d440c0700000744a180c1401d00038004041c0d070b070180545010400511160503818603840d41543c005c0f0410241c020b0088501203111070742c00b034024105005410044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894057392 1250 894056142 894056179
    0x15021303031101021821070b0c0c011403010329070309050601080c030604020415231903110d030509040e15010605040f0303080a09020d030f140c0a02010815 69
    0x1015603000c2d80d2001211150300e0301c0d4900300d10403004038035140d20000050503400e20709507000b00701000c142d2845004011070149132900c0c20645801c201d41d82c01c00840d4018079800100100c80100000746002582c00e1500c2e442005244018080909003801d10140444545407403902c0c2c00601d000000c6407212803078402e5000b0024806040200c80c2030041ca4000910050009000a010301c1c008014000329125a400c02c002089c20b810382c094190782d00c04000a0900b64421136100d41c1c11810200c00d00c84100e0b5003001aa01c0c580b03803401c42020486441070000c100c1c0c40c18101020070066800b4000901e07a03040c15581c900401d41d4280d889414002115051603001c540c0440000718403c0541303160340c8594040d20b881c007072406010701c03007404c80e03008001103032003494060b40080c0341c020000345605154022036075150000c0d009801041c4200068003070507030701c1a039440300c03c0c40202c203442c101007020541a0712600300f0390000e4100120b010204103054034120301c0d09003002005084400700750610074403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894058642 1250 894057392 894057427
    0x201050f070b1b03010819150606020d03150e07030b010926060f07020d2a062703090504090203190f0201020613030f0804081303230106031205071502 66
    0x31414a0380c9800c481c1401222030b01500c5c181d40020000c3c140d050091021804031000b030040c1500d07000c2c00201d5801851800e807140c036014000740c3d8003500c03014210f0407001c0c00f0380b16424039980110b40302c401e0030000c0c0c514205540307030402142e140100b01d4801d40801240c40030040d40107580301842c031480c1c45801b03540c5001e0311001c5031403420554441d0368a041c01850340d103504035890405608520a0340104034881c200000c0707001030014aa60b140d102100d1266203e01150b042118601d54031b9010400e007035810803510300a10f82c004900030340047d00740c3e00109441d01a106450040b500c0f2070030582156418000c0502111010003654824986420050a40151400164090301501c2e010448918940308801c4940390142c84004000414203011031344108010416900d5090510200351968443c10b1841d0046008510488401648040c4926101480d03041250903a00d050020000500f164120050040480c00e0998580c0d5060900c1d6040c2c51412600000c42440010450820005c0300c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894059892 1250 894058642 894058651
    0x10060902041503060f1202120a08031905130803180a110f01020607090b070816051e0a0201021f02090604150905040b061614010c030915270201050f070b 67
    0x4122002c10007400705400f180c007140596240050080b4052000d10301c14081c2c03c0d0f24501c0030f00b03880030b6100900303169402d001004900311074203403000007480000b4801e0326501ca03403011800d804200c9800d00750034501c1c1c2c44820a2004183c01d0f0b0210006108001c0032000240c1640c482d403c0d00c1a50340d0350700c4c0c45048402c2001c03829118001c60100c0c40303025440001d03180c0c4111031319158640102d00700210134003031f50884901120402010840c4964085190b58800d1000e84a0343c02014420440c00d1640d0300009000210006640280703020400f42c0e900140c1c02c0220301b07042224030307400c2484a4048010b4469035454a8120a000400150a002503004240624920b03507a84080ea621401088180c0d202d01120641c885024005c01103100044520304a005128104031030b9606001c1c4201070a40b01c02c01c0b400c5021a030341c0e0a480b0300744007803440e100c1c402c0c20b100c09007003020a8100d070703503415801415400711201c4a003000300794045900070803c451300d546c4192001515800589041c038010301c81100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894061142 1250 894059892 894059909
    0x41e05030309010e0c060a032d020315010503190207140717010b0f0d0303471503011716030b061e03071202040f050901052d070f021006090204 63
    0x9441492200046285105c40000600e02c525180c2006000c401a107140c4d00600d00b0341900440e08070710010a1060b01546044a1a025032207251500c1d0782c41080310b0707005055040c07010130401c010303062001102d24071100c5210200141c803045141042900e2181d0704e60010602d204060021418000061003040c0c65500100203000340d00c03400e000d00c405440380c100b0040e04094401d244000180c0241c106540d15800c1c200541c8030140e602110351440704509004100f06070013110501011a01030741e601c58001410303580504080c00f01a4160000d102c1440740405d1103e0382d080603c4005024050501d9403200072100040c400d4683c20426000941907076541d00c51a800c1141e1241c0e00c1010392540c07581c100003005080700c1c038a4001003a8403070114030b00481c3c0c042d80d50b08034145120b083e0301c262405010501d000042c54030304051100151440d401500c0c109008079000a02d10340315400131036611562a10300703086180b8581e90141e141c42000c0758004da031581032200210b222159507018000311500704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894062392 1250 894061142 894061151
    0x130f0b030d0519020715080a020d090311070803030f010e0711010c030c030e15010303050c0f07080607170f07050d021612021009030e0f0621040201030501050621041e0503030901 78
    0xc241642e41d40000d06ca081015406010250030b194028119694050401d407009031500291202e91011104200d400f10003040e003052007803e0f411410885c0001400d6080001c1d451401c01e02c1c500084903105210780c0e44d0301c52110b80050300c02440317062100402c07041c15000b4007031010800c0028015141d0001c90300c000078a0034442c003a41140001d005448212401b12026007a421501c0460307065001c40142481c03481401b1030034007405010000c01e0010b000e200050104d0f0b041c180340040030f03e9800200c120000541e0014000030044001d1100d8015410342081543c80c040c2c027000e6400380c0100d20700c260403184440d8002083c40135003513401c41540200d41c00e590b0180030007903801b8102e444450011b030000710030b04505078043c10800c52540541328000c10306420118840c000310103040785807801c003032000700030024002196090300900b03024000c1280c0c514100303410350605242d0058410b041c2700b450304050001c20107100d800c0a4510304010803040c0180c03503207680c0c280290350b03034820389401d031880d0b00e030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894063642 1250 894062392 894062437
    0x301030605010305281202120406031409030a0f05090a051804030e031f1d07030503130b1c021e0a02070305300d0f1515020c130f0b030d05 61
    0x3114070001d18210303c5c00d85540441030761100c3c2c066241c0d01c4402020340c407542104100300340984c0080c000800307103503501007200720b20303100f044a040b2009480d540c01c5510038800d10084580260100c403001d4564940741761100c100c580000d41031240340c1d1105400008526002c00344000c400c4e82c0510450098403801c500d01604414507541ea020880000c03a4000850220540c01805800031401e0f030f000e58070198005030358940c140b42004c0e96a48110303541d900000f25070381240d001c0b44a030802068141e140d00c5c00d01492107502c04944003010280e03a1510350014030100d555489080070a803444100c2d003559103507a03861030080c0da0707070300d01e4081941d1900c614201e2000c0101c296440000d0b14070f4008440605164030050b280c202c1c0c00160800110300d4980703040c00003401151150b01000601d21140d141e0440c9491041d2030f5401d9000404402c6400204110b00c06444280000030a0310f1045800250114902180f000801000040c00d91501514421040b4203900102030825401512204a04c0c1c005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894064748 1106 894063642 894063673
    0x702090c0c12070201050d052a04090b120a02040221040528170c0304090e03070c331205090d0228120309080301030605010305 56
    0x404140018890001c0240c0c1818810342c046840c0b400c0a2600000d04921a00340306420658440d070105926009000101001c100388210203c04200b10288891240c1e01a2142c505081c0c105081c2c43d80524100c01138559949401c3c0040c5554a4030350709000103900500300503c02480b040c6c402d050341c2400003008070710441c4141701400f103046107040b00002564480400160080543e00b860307001851041290a400c01d0341c020385912403134103901d0710f0301c3c1d84504d80060446505100c01540c3c402c10000c05407259a1081c42c20300c00858884070f5050010400c3e1001d51030a0100101c0700752075103400b850940c144140c07868900c0c100948141c80d241a11803d0b03c3c1114654070107101d841c080390f810b118040521604100480d41020b103110184107803400e15078040d00d9070482c81003d03202c0c41c2c06544040e204580c820b0540d52a0b41c2e680c00c16400418003480240d03403a014091a8441444 = true := by decide +kernel

theorem cover : BRFrame.Cov 893884892 894064748 := by
  have h0 := BRFrame.cov_init 893884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 893884892 ≤ n) (h2 : n < 894064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
