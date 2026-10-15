-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:31.713312+00:00
-- url     : https://prove2.me/submissions/8c9c9650-cabd-4205-a1ce-83cd48b7fcfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 952877697 ≤ n < 953057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 952878947 1250 952877697 952877707
    0xd081b0f060a0f02070f0b0a0b0a0605030c070317090a0510090f110604181506112a0907030f1d0a060b040902090423010207170a0c050105070c020102070902 69
    0xc46940c98070042c0254210660701c41401007030f2102501100e1030036801014140d011401e40c6480e01092a084030318802040c41e282d2024180d18080c141e480485130766139185c42c15515031141e2829658809102141404002c025401d540785503038000902c48d07a906405400700030010f042460800486210310381086141140000000344400f6002a119802c1424840940742e200c1c04103100d440389400400d0a070703d101c0900f0031540c0058101603d03222a5014058015681d40c3c021780b0728003003540031600c587c2c01100c18250007007046c080c0c800100d040e40c10764040c410007500c00309858a9061310a0300c00039031200810000340f990350240c02d6006a8420805c1c0d48081000083c070307210344050f43d00030705098941d400740b540c0755165007080c0000c40d0020042c0c0c909044c6464404c44140c15802d02c03006080f00c803404010340c05810b100b5a2607654200300088070864003600840b03129481300085c2014480a244000080750092040c00c1c854034041e1602c0c00036171481c0c000603141490b90f60213498010300400c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 952880197 1250 952878947 952878973
    0x150519082a1c03112503110d030918200a08070f02030f0a0507080a020705011805060702040c030f0e01240b0a0305130f1203050a0212010308030a06050d081b 69
    0x102011980f50145440e220410030386028a013058000c0000d0402105d001c0c1c518010303101e0300400802101c0c480e8600c3c2024108044c14004618002c0700007401203000007404000c05205048802c08094270358030001040d1658510000004280c018420300000000c11420001030308490141c0d0400b0366400d080b4007090500304c000350b50b0f00c01c105a10f240000042000c0c11210301030340c107843d04207a10400454a800d9800d0009584800701e116403400101035403058445401c001507581d046c1c0300c016140d0342c5042c01c580c00b40409082a1040e8000301a920200754104580b03034415541e03480395003000407a102000d0b0000138600c820708528002c07018610b6030100a194090022510020070b18103002c1005d035a415000780c0080c007005030140c4920384113000b40303041100b5000b400715454880c1c0c8040100d82c55603e0308c4000c0740180c1d0303844214024400300600103d070300300000d164040202d05e408607065031660b000c6850384c031411030b080781c0255001c2071800c8101444406000191410401000c005038050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 952881447 1250 952880197 952880239
    0x907030203062803080409090b4803040f02010f030b010507020d0f050303100905010906030f0201120e01020a0305090c01020c01021506060706240801150519082a 71
    0x505428100d400e42c14001c1000c4402903c0310055800c140e0250302d441d5201a05030180032507440c2101c1c090030b03403000140f010940300d4001480d44240340803201000f00d1610881f443c1c440005901004c001c01c640c3c00032080005c00000c0d88218419841359500c20700907c00544602030703070314816040c182041481c2c007a43c1d82c032030143c030348040d012540d040500105007498a103001c900740018145005c000100010b184c840788400c03080700c103a034108010b2070380d0700c280340001c544181c000103005c2d00c2c48401c060050362046e2003072007440c0c00466000419403100c2c0c01150072030340a881c9070310100303460b00304010808005100f111425902800a07007174110000c40000d4680b800c45000b40c08010351800440e059031125815240201d501810412100503008452040e034000c00544010090300004080b400710418090701c44500d10040704000114200b2040121240c4003054000325192400400510407000f0065640240c2d4515400c521a80c4040641030000da081e0b030ba101d000701040c3c019040c60038509 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 952882697 1250 952881447 952881469
    0x30c020712120807093f0f03020c090402090a0209010909020c0c03010b090c041208070812040537020411040b0306090a020703080a0902042c100b06030a0c020a150605090703020306 79
    0x200440d5040600e18000103803150100d003114040200f5201c00110800422001c4018407234002d03000c86001841c004100031103c20100d5000703400103009008107124580c00d402410240720141071000e071858031458050100d8204600600042d4007522004145040a100c2c00d1003040c420b07601200d0b249803040700d038040c038400c0344601d504a01c10074034050240456841030307854480e44010282da07605000042440c503031005542c296601c0c02824080305e541c01404142640402c4003c09003080010f200180220038000b0300f0050342c005844172290601a100240280003070030900b01520344904003c400d01c8549100200444e407034034070401c0180d001c20b40160601e41d000d81c02410200700d80c071072840402c01521041e0569403840318401004510710031b81107244289034107601d08584410101d000c0c15130503550480081e03900500c040020405010303003030308080d860b13400174012101108030031b6440142190b900180a04990f5a40b44203000c1c62402003030b43c83e0031210518003582107060090026051441d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 952883947 1250 952882697 952882739
    0x1c02010c080d0204120311060f06100219080a031b08060d020a0b0c07090c05090f120106080708070303120902030316060b0d0501020309071d0403030c02071212080709 73
    0x14054294108080c0034120394440b6100078041d0740b60703503036201461004030085600720701150b0b03000e61502a100001800520400440300c420056441b06001e000045108a413040e086008403010307220807920300da41e0b00945510454940fa554804078000508035901a41c018210303808900030714500c4ea500003030031030b040a011103051907041201d1000035088400ca900009901201107020300040d04c01166130421120800002d0040301616081150184101c40c1c842d0780c801283c2c4d480048500708880790303e42100b00c0c10000141103489124840c50700c040d0703034000300700c07544415018020164840420a41d18400d118203105490706c945c00203440f406201d4080c0842ca24850300c000c14044140c05c030700000807016082200f400154200070f8082d50003151402c01e41e124070300001582101880c000d9800480003080d50520740c50300d035001c502414075500104218031a1800c046040f0a283e803c682c0e0162281c100300c1108100350401420740d280013840d500a001149400b0414140c00c1d40501b810159 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 952885197 1250 952883947 952883957
    0xa0803010608130210080a0606180e04050a050a140d0528020a021002070501080115141810050d054b01060305010302150304051e0c030616030b1c0201 66
    0x1c3d40b0082a6910402d00320003960000c03880c1c5e201c851705900000250300814040328148442da460313100940b8000040c20700c1860100a03a00d081040e00415085d031504039202d54107440c280400c64480341e10301641880700780c0344131802c026118103040f4100810000850719041c658186984000703201c1c41055101022403810607089455101641f09021080390194024100070414680d81402541c4642c1401124041a00040080394040c507000d205420742c0a6641e9400d01314000c1c440039016600031200c2108040e4910040140c00e80c0e80183e0600c040032035a40e05a21004e20b04070702c2d0144d61003c1c108454540554074012100d424102c4174002c0b5a407058440562542c440070076030a40310700784c243c0300b20705508000082003990785904814120380c021117010080250924446860b40703c256401002e40e4480802c002d0074688210a81c0c6a10881c00d040ea4040c4280b0b0300401d08043d021109208001c040181c040f82c03898062240c28112071003030381c1407852032107201e40c480065105048081c0c1804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 952886447 1250 952885197 952885201
    0x3030a030b031f020406110f07060513090603242f0706021201050a0b040b2502030d110609010b0d02040207140f03130518131419140a0803010608 64
    0x502d00b00550340442c00c04211600d414100c0c1c041040094202d4041d00c0c1c00541d600c09030640c0f4440004084a4102c00280548180340c0350070415901030340200c040342042a2128000590900356205010042d801000d21104414000e5402401c003500840c5520b070051800185001000c2c074090308029022880c58003200c5000780b0700c0c9a002034000d0200c014941d41c000a103424a10b1142e1045504859040d608461401d4440032500724501880c050401060f10621008516500030100381074103410508a91850103240e401207424044040a40b070003080d10b60041d000c0000003046000c0d8030027906d40c0200803e410744800031319040b0b600c1da00648560b402040c84010301c00c10a010003030b00500d010480f41210714846405480b0b4119103c174429181c10b0580001d02c1c4d040c005d0803403951121548199642d40e46a00300c4e000110990401030782c0f5005403080d5030341807402c10030681c1c070f0800c0c0801858048010300d1a24101c0c010203d107846210760086007010000450100075241554603506100c4c0481d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 952887697 1250 952886447 952886449
    0x91d090a0209190c0207050a1505390102070b010e090304060c021215160806090117070504060f08193804210c05030a0e010516060b1e03030a030b 64
    0x144200311903020f035880c000c25407491580004071034044174019109500c4066a441c00480d91030351481c41040801d40802600141401d0000082202071421500242031308188203182040c09805141c00c1d8940e60004040c0c0c244542c0c5070700c1900414040201000d58079080c00e52036200d00a034460f407002d21409094120440d511081c2c01c201502030501100e502000b80c00201c0840071056134007980310300e001107d08214521540380d19114030350140c68070f5016480c0403401c0b00c0e489114850212140910200812159105c0c018200180030080344582103d0030490341c00d00700000b40c01c400719100d281e404804002000c0d103601b110305c2d071440740d0740d1b081031090384222a400034040c43d00c50b5047c4601c103041000300007800004090380301c901c0501c02d1000d0414502655843c4005030060401c0c0d20070701c102400c407803060080c070840340818544207050007010012551040b14500c02240e4031a180c2a460304207007420500000030b0100d9803070601da042e01480c0803d869206060780701c400c05459020703841c91 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 952888947 1250 952887697 952887721
    0x10f0f050f0a050403170408060612151009060e04050d08060a03060c020307030e091b0c070f080c04180c0308091804120810181d0a03091d090a0209 65
    0x1441c1403818040e80d0350a200c1034014503550050000700c0f045208070400a180c44000004d89064403403080c0100880d448080802600b051607800074030541c4149202c210161110141c0180181101d440010405043c0707071301601a6480341d0080401d90000b102044041200081c40705a072841341d091001668a42e0300100e4004981034001070903103404d140070702030180d90000080075814001c0e80c41c45d0f010740c084802c202c1040415100f140400000404c52450985210f0090160390a40c0302140c1106a80d00c001c0e02807440540d1141c0c400b5040914071600c541014010300c0e91021a08011480c01300d600c3c2d9a560000000b8000035010282c040b03030074000d54031713002000307525083d06c1c1140c1c0406103402d1401c21044040d548603000061922004101144907415155054400c3c0b030b544c81220860510350300005042344124408401d101164185004005102600660b40680e503000d100301c0c10030b440f03900c451280d01c00812805201c081044a03003000428840d0580d030f811103994606032211421050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 952890197 1250 952888947 952888957
    0xc040f02040302060a080a2706110408070b0309061501050301061b0f06020c07050a120609020a030f03080106090b03011d1902040f0306050a0203071b140a08040905060f010f0f05 78
    0x9081071300003601c407008942004a9a00c5480944000e0104013104028911205880050545082c0d024000240010b401d904880380b1101d000c620f49003460368841002345495402d901034440302000106010075001c050043ca0351040900034440401102c9000007800c91105210f030400304002290000c0e41005182c03413840c20030760401c24105c41d5441ca41012030095100c0840d03800741d84268140000d5a0510b60400ba042321100c1d15240486030030780c1c66520141409404c105d074449400500400020015070802c00034a01903070799800150b0400c17001500401d1f040d0132150602e4014001041a682402d040e80c442401c800340c0040c107521825000b1051000c0542c03004003d034000b041c00305d01001c40720540c0048034015001801140c0700c20074035008912043c6c61000000e015914100d400ca15000070321900c0351701ca024580c0050f24800950b07824860113030001c40e00752000080402c00c00c455030040350b41245045841d6202c50210f4800079054400349003040040c0103840e41c0000d400c0d402001552 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 952891447 1250 952890197 952890199
    0x5060318060a0f0b090601080c0702181810050c0405040c030b2d010305040b06060f0c150a050603030933070614010f0b1e0c03070f0201200c040f02040302 68
    0x18125040054a00010b40500c85054001e6132501c1d400700d0042c50400c0f04070f03004501c10384940c2070f903444500003140c0641c4100d00aa030407402c100c012408900703040c1086803040c141c8002c9240d41c0b8041c06406410034510341000d044c0b090814044c4810303102040b0843d0100c403c201d600090072068030509138081d04404808a500460040403001c2c5150100c40d925000314070b083c8091810410580107408680e8107a8001e045100a000002c41c2405d140c401050149540140281400c03c1d2807006413400d840348281107094024003003440590f40d903502983c0e42102d411000340d0300b40140e030030119041c07550512084801c594200d1400300d401e41c02200706200304c528840002d03515030190038441c000d80700c0c1002c0d447c0164002c900008215800801034400c0d2541c00024515141c401d042841c000c031134504000080790703000c000022004004200409a0354400e10340320448505500016114948a0505440701d5180a05070705000c800407481c0c2c180c1c8001260002081405880042d00a0045400003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 952892697 1250 952891447 952891453
    0xf0409021215310507050a0b0706051803070f0204061701050f130c0b09060f19120c2015010315180308070e12010c0c031206050a05060318 61
    0xc64508070000c240b5039001c41c100c10701202d042d200d4246504801c25040c0f44000c5070b40f1030400000c0c503d018000640c01c0b107405002190400f5440d070000880b000380740e40c41103903510740008074901000110300429500000f207003039010001424076207550700d0b88030710382c0d00504821042c0c3d20352045590320362120f0050030442e80c40d07000640942c0d044600030042601c0b103040c00c17004031002035124001c1101c04620f5592080d101a080c80c44c003461100c0e82c0e0410b10006034040b005000710920401420068918042e4010400c5c49141c0409030181042003040c1c0184801800d22100300d07919600304a014031a0f03000005100481c4001d4442c56043c60089103908002c480564000428000c419101c9114041400010068011694a01c0c2004051483c004010851042c00200814000c440410b62202e0140042c04080b810210203400c680c1103030940804500740102c050180b550051454210546446041002c181050f0015600d41014418dc501c1001d00000098144204400c0c13603d980444100b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 952893947 1250 952892697 952892719
    0x80a200d03030b0307240206090a020f0907230702101d0f040b030102070c0e150108150d021003150603150909140601081c03140708181501030b06030a0503090f040902 73
    0x1501d691b1207a40094440103214801c00710709144004180e42105030786c000c029840107140c450601c825080014002010305c0030f040751181e110803460003004108003d40102075540c100300d104001141c3d540010840820001c007664010b00d00340c80c0e0801c1c0f02c1d007e0407074034204000350707070700001d005801d5042d295901540081440020080c8983c00001951007240400c1e42d80d0356011100d0b0464030b824003d482c00140000d02081407107410f00703145182c81002800d41214204240c001c00e115441d040402d80000c1c2e80c0303200c03c10709081701c203030300c42c002e0300c003d103020f11401003249440501410755004902503207540740c005d5010843d0120044146070301c0a42561404d61359510020780700c80b20000c0384640c1640c0180c492508500c01d1041c2041c1031400f0100c3c840030740b40c010085680c0c1e1030051000e046241040b50b0201d10420802000800002400303018070698150310b0441e0f078622010384103c2c080d51003000d00d4000140080180e92020340b0940d03110490102c103000042c0904082ea0000c0e40045a10784 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 952895197 1250 952893947 952893989
    0xa14030d1d010b0d2406080d090e06450103110109090b100807090902070503030a062103030b060d0501030605091b180a090c080a200d03030b0307 64
    0xd28058a2500d2100810403031040314144030380305184c240c004203410341c80c01c0c00c03404a00d01c070f0b140000550001e03400020f5064841c806035241c0b0b02c9a440c45008203040080410040901001070f076440541503648884290f003581004684003031203469181403003808018508101c6120800c4404146050403081c110b581d241012600659240c000034000f0b074003248003041d41000c81c01080d05036840075003070102001b10f450b0110f0350001c01603d031000f08030780380c000003e00c980240040c16565014070050740d0b403030070000c4c01e02d421280c00d90b2025000085070b1241031527400d0b1200c074102e642c0f609403c01060b1400014001603403032003480c8a000b02d03940340100100030702580c2e40c0800e10800c840c0d8200d401d01b05806854007800001c00c1903c541c480c5c82e0030074a060400180c1007960f040005581c001c621205c00b90f8408502c4902c03600119031540c0014400414403001d510000c446120300c20000e00c0c82401a0041500d41902d01406001d06032204c0862000d40c60030800e010044c01007010a18907180420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 952896447 1250 952895197 952895231
    0xf03070503032b0516090b120606031b0c0318030d021e070918120c0206030601030c0c05010c030c02150c031501121a010e030115122a05010f08090a14030d 68
    0x41800002501c411804240c4107d840201c440e1a0003180c0078008503034803074040000d1540001d11a4020710b03070801c60301031074054180150940c08982c5014586030740d4580103004a141c58000d210b4071951140d04040c4610780c0100325541c1c104807842c0c41407d01c1c110800860300d403100e075a000351010b82c500700354004000a42045115070501c0b031a085112144c903860100c070310b40941034000c0d601140030808501558025401030807480814140303680c140e900b9844643c00c59000f40c001c8008217448840c007150641d41803018070061412070700815a00e05003038840c8116400018111401c50400c1002035003560f003c0c21949901c4840307001c041c0400b401e081c03006182000300030300c07080c041400c1e01081032030361070706000d070000c8a04480b8007144003a1074510030080031240b00800707441c001155081402c1e01c110306a1114081d42e090b9940036041071501c400103003510b01070a42a0100840780041c0685c1d2940464440032140e08102c0c07403094602070b1040a819407080c1c0d14600d0340d542c600701103154903181603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 952897697 1250 952896447 952896481
    0x1050c16091a0d150c0306032f030d050d0b060403060c02100f18060f1803020102041e05011707021f051609080a260d09020f03070503032b05 62
    0x20070740e4288940a070000d200304030b030f0725110042caa604408003a0401c4d801950104840c1d002c54078000c101725640e0303100c400040352142c0100b04912612082000c0204500141c600080c10540082c02101c10019000f0310901840c91000c45540d15060b80740203a9440340d043d180510340100d0f00700865032000300080d68600710407401032041420142e103402d00464512a0355154100100400d8100d1400da0b84c04005150140c1c8100d0101d9945d0107641041512203141c09001c0d1282d000107a07181c1c01c0541d60040644c3c00780b104040c00700d070110f0901090740d106041c0c485100c4aa0240b2640e5202d00c00c040e4141981071660b01c043c400c01541600552442d13030001c0f03000c1c6501202c0c1701c0d01e01e040d030501156021030b24015906140d21154482c400200e140b010507039103880c003e040303149045421800c2e52950380110800c1c0c8500ea10b03004042c00350700e0100200b2540c0c8004400a02181e40f80101194490042c40c140d030203251641801c10340f50510350310f0b041d120030468550400035882d04c481c3d1850044c6413 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 952898947 1250 952897697 952897721
    0x3260c0c01020606031c030f11040e0702070e040c09021b0303070306060801080f06010510120501032306071d01030219050301030b1b18060706050103080903121801050c1609 76
    0x24070b00218086017070108005480070000c036540100914141c41c15005403510340c0100720022341d01c100c1e0740000e0303841c01d01910151103001c050074000c0c10400e000901c0c10038503420415610036541c0030f010000707407140c00f000200e600c48680540c4a07242020304500007032817900c42d001503010001c100444a6416401501a00c03880e89580700242d0b2509400d655500c03e0100341c01603540814014800b0749000c0c08122503011907440e041041b800030200309001e541e07007039000f180d0020f1200128100d00031b0040b4401180119030b40205614640701d00c000307080c03004142841001e04081e90720745034603034465011134940625401c8082420300e80141c009105034424401910f01414040200c2e20758102075000b0700020f814411201e0030190900b100000070164030b1059a4405806c000c5280000c8443c01014002c1d4010121140c992191005041c1494032103a00b50075008000c100709040100703800302ca84046a403e1810540310900a1501460000c400fa1412920440300c1c5002130070781001c1d000043c006007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952900197 1250 952898947 952898953
    0x4050c09040606030e10052509090516120216080415030c05041203050d0e01050708150307050307030b060411180102100b0906010c17040b09270103260c0c0102 70
    0xc1d540d43d045080b200c1c507100704042e03500300c440e00700780d5211150402500070308043d2019050828060b100c046582c0c035003021102140040340304100004c01c0b0305c5095803000c08180348002101640600400004507074060340c0d1f00039408201c0c4840c1070028543e10004561012280e41c2c0c4a0315841406c0c01802040345a20020303040c2424000441e104600760740480f03200305120b0306003040555007541e0340d8200e00c0b04a03c50541e00e501440b640c0d042401818090f01e15a100c800c81400e0054490703554400c0c496070740d40a68080101002141c8001540900300c4c0d8200c00301061988a04000034050031950b8520302e030a0202050b0080d6002c17041d09100b034a007800f40c08031841016852244401d507403542440c11f602c81000000150507501130a0038035002441032400070300304200e0000c401110b4101e034103c2803c0c4000072502d9442402e0082031008020005942102c034401c90350302681c28103405010040414500a1401c030010506c408034a42070540e0f0075020b41c40792880d0f0807080c0c0e582d455441a500500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952901447 1250 952900197 952900199
    0x18181410050303070311030d020a0c03021c0203090108090115150e0a03080702040e0703120216231e03070b03270d2601060c12080106021c0c0204050c090406 69
    0x40d0010251004031440600a0360805126880980b0440d814210701e40b036900041000c884842034500c000d00c82c0c0d4070b4a0b12501c12000990400a1400c8840104201100b41c1c4880c04280c0303c1d000070640e45c5403034013441c05181d16900d1301041c038094031030340c03410444102d8101004140d41072403684100000c241c950307400050341d50780e4003003090b5405103110180003050200024805814180c10040017a41060121009542d990341c42c100310202040b00c00e00141c008290f60b60700002070114000040c59a0003018000c0c4107881e2049605030a05807500d032281ca4154a00041080c2102908400300c40040503103003042d954100005080d401100c0c908000b4581c8806c401c01120110341e03c030351000090004241000d030b905026500c03001c8814400000004c0151203a0f0003504544070139001c2d00440d40d92100d41d81c090300d0305002509802d81c8132418060200018004964002410316101c80d02d080f40e0f210b076546080c4140c0d604800c107440690080e00306001c00c41407184940040c118102e0940d000c01c182 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952902697 1250 952901447 952901461
    0x90f0b01020f03090a120317090d02100b0a0506091302040608061201020a27050603090a0b07080403020a0204020a050f070f02091e0606280f1806050307181814 70
    0x1070301c030f15201142e128200e00300c107029080b9854803e49100344242091140e84401c0c23102e143c1e00d4079048071240ea2951042e400c940c45c1d15414001721071001ca40640610141d045800010b6400016001d402d000d003002081e2400c00c0d9032280341d450400d0003002c0c1d045560700e40316000100081c2c800c071f0701e580c05002040d86003105050144215140f0500c0790313903882d244080001c10702c904091241500028a20450741c04582e694a4a00460040d8901c5000701801d10592a201320f0b00c0340001c2c101000d02140000304008a900490180141c99045400580c0da0b07a160000352200d001d0700041d0310101801060110400102c0c98002e9080c80c022940d41c42540e80f656001045a0304103059015a4420b080201d5914103002c0040c1006500c10007140d940110380c841ca0394040d0500c00900d40006200b503010b808010303001a0505102507078101e4010069050403800781a52101070170010070012040300c0801e8103800d411014000e1b1810a030038000c002311450b40500030b03045c440c0c2c0c2a140b611480010460f1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952903947 1250 952902697 952902703
    0xc09061002030d0506040605040e16140112111204080a14030c0a0c050f0619051506160201020a080c0d0314090a0f05010605220509060907051009090f0b01020f 70
    0x3094103158015403030601e041d0342000c06400080c02070750b086901d850000c142ca43d01d500031312084940c050000d1118aa2012410982c140164000c11504100280a008690b0301001400d1110080e03a00070401c8801a6042c1d5078034420b2510454807040041e090104100c40070f001030603104039680c1c6e011702951519040f0340ca64071003941c0782c02402d00100044540d841c01843c1e45481e40c2d0145c019038501311000c6520038240241101c41c4028000d00c01c40c460b07403c80e81481403039000a029a40700c0b081d06001c10100382c551045080e03c00c1d1040080c1c003103408680c806c00c0401602e552180c3c0d5140c848503081c2009a58607004500c19020a090043c40364107500d0070340380140320315241401825103000e10384034100c0c0881c11100540d0155200e01003c1100d03202c040680651a00fa608545400f03102629a00c0441e0005066010740b5044242071014100c8002002d00507140102d0b07143c0c6c00001252402d852500081d4031503c0300600f0091001c120742242d50168030399200070307026240e0200103884182c0d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952905197 1250 952903947 952903969
    0x1507060e07060f0c050f010f06030212071802030c090a170706020a02060301060807090f0b130e041a0601030603060906091208010b0304080a030f1d1e070b03060f060c0c0906 76
    0x400198104010303c000da11420640b0307003003400b070410380e00b100101c62201c50035625100c0c089401e06450f03000801c110b0800d20107200442003043c001d0500079044c01020345a498035810307502d085540210104e07409400034030454131120030091800024650b1501c283c83d21910030341c03e04e6494000c0510001da41030000c12019001c5500030001032951303082c148144c50b80d0304040c000300208102c4c600082002011101c01c00c001e08200c0b241e450700c5916001500002e00c103242c1204501d010a0003d000000d8500d074600c000000b04201d04542503030354000102c0041c08142d1029000781d0910314030105200140c1e210540b20b074040c06944042d0b0f0403080056811402c00e101e0191501420000100440d0402001d001240801d103404603180f03280c54046005c0d100c2941040c0300002034000c5406007200c0c204070351455601000304007078107204d104402d207072502d00510402140f8000040001c03440c5d6500f810064030114001e10040e103880482a0140d074581c961a402c1b80620b6042c03001ca0010301e04205602 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952906447 1250 952905197 952905209
    0xb010909060e041712010303021501090209030a03030f0b061c0509030703021c0c0807080c0c03120d0e07050405091e0a020907110a0c08010e07050f0a0e0c07021507060e07 75
    0xe0b0f441e1942c50140c200543c00380c1002521081c81582440300042c481c60b40214002ea00500d0301c10300b402d01c404030303104e4180c1c03001b054940f0401c22110107890200d9000350720b907011704000840c86c02109101002d8185101c16a030b020700005100e249480507a0600440040e159104200715500c10b903819689124540d400790160703001030700380340300600310f80c1500b202c81d05a41703030804400e2115541e81181e070b04510021526840d0110f40d02420340000c12045030003101c220010241c49a044e041c002840c030a204903860ba883c0c41e01541e0101010801840b40100b82c003600c20002031404041c61511401000c0c55910b00c03240c0041c00d101d000000084a083c0c583d0018005102c9481d044400e582d0011049004121070042c8911200411000781110004107105000402d003d8034030300210307007080b402c1d4001c248034514590b644505034452440c2d070300503581c503100984002d80b40c01410038118000c3c4000207520210080c1d50841010032000a810348500c5204188122400400d4658464450740255 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952907697 1250 952906447 952906469
    0xc030e0f1203040c03060f0516030606090b071e03020102043209270c12070803030f1b0f090103050106030911061b0616020613200a08030304060b01090906 68
    0x7501100000c0e00554015109a144903065541c1e41e554000356003410713214510503035865040103c2c458025034039106002c650302e006c00100c4d0034940003074520641030207a01c00310346020882e401004907840c2d0141c886856000e00c00f5014000e0b1800a0103076006009041c3c80c030720103170781c520042d031040f5940030940c80c0341c0c0140450b500502001d1201600e0010808a062080140c11458541d0091401e14407280740390098609000340400384120a001c50089002652169208010401021040d6034100d44044200c0c0d040da111100e00c00720300341803e880c1040d0900300007514190780014034014010010300380c81c1400345aa07107a6055088515041c0041c0481419421115042c907100005150b040303454043d2180d4107030300040040c50000308483c11130411401882c081003144d01000259840250040001c2c0c403840c4a030745100c0a101080000e1124030342c465141d28180d80e03010482c4010302101c0c1e04907601da20b0142001d1024086d401b40060100d004a0f03000b0400640c90b002322025103c1010f08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952908947 1250 952907697 952907713
    0x60f19090b0106091d04030c032c09060a08060c0c0703050d1205060409030c11061303050307110d0c060e0d12020309100306050a06050f090a0e090d05161e050f010c030e0f 75
    0x420b8031201c0706ea50045040141d01c00b06096544864500040a2b800c803034001e1401b016500f0034040d00003005032880344254003000c0100801000001e082d41d2200c4101c0c0c0c25610b600d10030540f00d15240342d9410050050140d0200200215801901c441064032000d800b40700544820062008039040030388081c0010b4030783c0700181c0204401c1125405c001c000070309414a0300000b8244c50b00600400d4008482a420008000050000403ca0b840e0200400c035181c21a190096442240e403151603c91001030202c0144140c0307855584904010003660000c0b212500415000002512940203c87c8644108800201803000611902c100c400b92030f000b8181b60300050070500195414ac10000000030b00d40e00400c9000300c291900800b100003011480c40040140c24181213403414070540500c0102000010302000c1007540944407044400c0d0341154018035201e51610500e07503040b40703122024200c0c2c030403098425242c540541c041c43c04040c13039540400c006409040410703280c04403051603c03400d82c42003031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952910197 1250 952908947 952908953
    0x30a0809060f33061602041a1f1205130203010c321902010e28081b161401051306030b240403060605030f060f19090b0106091d04 57
    0x4501400722540d6201003103007204140c00900c09074005c1c00640781114028443e9011805c09000b41c140441900d0040d501e14214040422400c4a0641c004074681c07124884a5103002e0290744c00d01c400145c2090b0501c41450035141034000100c1d2054101e01031340c070b030810050b40d80303200c1c1d65161000758444055410540d1507510802423480002c0030259084010000006030a083c40405400c0e10b840750000715500311a400240e04040b134400030b200308801d01010350f0240c0629400311000d400e621081c0c007921240b0700399200c81454003442c0182480d100d10360305400010300c0640c00008590304001d4007640c0c00044c1d00111558040d0480d02c80c0d450440c000300340700850085c6c100400c16480038201e080c981c0c01d409501001d0802c40d005580c4003034000602131050000c43c0c003840c80603040540c0180315034003410781031a5403588020907a40c9040f1102000c03d40a07243e0003075400ca40700c6508000e001e1140c86081c84100d41d0000c0c0710300004100c8400001590f40310319261400c5211480040c904950f441d44c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952911447 1250 952910197 952910251
    0x30b010c0b071b0b010f0b07031407031214160c02180705070804060e030115051c0606050301140f07080106020d0c0201090b0c0c13060b040504020f040503030a0809060f 74
    0x585a002800070b058151002903e10b001c222520500a8021031100d502d441c82c4039400c01001d8004915039001000200c02080c1c2102c1e603558007107140c107a0b4982e640c9090804480c141056200045c82900f800900fa0782c59640350485406450346840200c8041c2c6206d40a441003202030400035082203002105104110201c5803140d0712800908103d85408803580d50341d44581d01641000001c1040a0b45446460800348220042039032949405802c550507e03002030080040a01411b4007030b0b9012003003000b00206500010000d0502030028801d0300c4403642c1400b00c0300402c4414020304e006440000d01e080f03200302c45190485203250090102c1680d2110100d842ca806204140e050102c014000901c6030042401011103d141c540074041118841c4100113606840200f19002d10381030038024400a04044112411103804075401641d4101d000301e0f0802e5070280c2da20040d850f000101d2114561070304603c0080c80b5001c80e0060f01d406940d60084a02504030668910a0280320810b0005e1048451 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952912697 1250 952911447 952911451
    0x10f021b0d080d020309060103030305010f051e0102070f06020a0b100b0906030c0937030c091a090f07110106030302030306060f071b080d1e0e1206010f15030b010c0b 73
    0x1680b105440c01c06681000b00076a81305030352404e0141d029200410030b06074184a424050041101c03a0440d00340313081300180c00c0000784079990901040c040c641d04880c2e8020010b00008207031400309040c2007540c80c1c001944420036448141c0f80000190000b4188111020080c415140c21212041c2094089000e101454000410610185004000e50710142d41c42c04003001120081c100c4012419591b84c08203100c440440c1030790200c50070090800e00014480c45100380c1650b90020000510311401000701d200c0c0103011188c1900080306a06001c03941c00c1d4500c200388654101c0d02d600080c0c01620044600302d41d124032010b07005030024008582540740c540010203914a0b07020000c5e0074a0b501e920b4080e09100e200964802c0e0010070748041001c0c4006010300300111502d410a00c110380c1007072465914141511a0300010044c0141d2000741c1a90381d00141c030300360000700003112117a6841b10b6440d00356040318080c03040324a0a10800420551090090f00c100d4401030b90f60418118190ba42c01c9001040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952913947 1250 952912697 952912703
    0x20307090f03150902181f0603020c1027140c010518010305070314090109120207080a150213090911040509031b12070303050f090a0c1806050901060e010f021b0d 71
    0x2401c2c06c214020040000c403034001c0303108a4814102e0040342d4a03681503810180e0155080c54010b0106004108010628502009400c10042001c98410405103602c10154000700c1e5040d500501381c034184494501c03481c00c000150003c8900b00c0f440301c40191102e029060391803240d60400c0b24540d0880d4883e4001e66000b00013401c01162100703c810b0174214130b0b4001c40c0c44001da80e54400320402400b0340620030369440c0616001518505003400c0c881c503200ca558001c09481215903c210010620080d0f04035180c052400420090241c0c40314102805007034800c00540768100d00c52400c00041c501442407070301450300c050007540b03043c0ba226951402007110b404d0035580344c000c1d03225461000b1900e0000b4854179220355400215440d207602058071014015150395102da00011500c0c1c0003034402d0703403140e0540300302c606d24283c0d184090004038054032458029603008400c2c1e000002d101604500940c1405100740c0321404081400c3d20200e94882840d90380445500400384211002c1c02c11090341d48640340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952915197 1250 952913947 952913959
    0x61104090c0806030d08101413090302421e0717010b0a080f0c07122c0a1206111303020a06020309030a290a020307090f03150902 57
    0x6a5411110200d44011240601240e00c00040080381c3c60300b80300c5c440c40c0402a061450340ba04119030096a6800c560240703501014100203080d03800d030340315030b1080442c0100110921a0300f0b070318900291100b403040c10701d10240543c4003c42240640ca01e541240441c01e040d000c040348030481c0041142c2250203050307102001400984014070842071a64140b04004544400070001a5028030001c0510140e000601070300051000f1030319139900040c40d03074200040303580c3c612058030741407034484540c820180d000700344d46001801006201d400c280341a840044401602441c42e00803440e0b510b20300d0803031100a40c01b40b0f540d2402e03c5a4807011800c421024054400040d103461008a461410b9200c400955410341d1510300c2041140b43c511313280005401248060b504102d104404650358070540d84008001101518030046810801d01c3d01ca6544010014080c0c041e040c4001a00001d5009952980014000340004101078800e840c110301180d6102e180026241c41c4103110308000e10314404100da100f2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952916447 1250 952915197 952915199
    0x6140702090c280f0903050a02090402150a03063b101d0a11040b2a0607030507020c0d021311090a030507080c0103060b1b011805010e0705011103030103061104 70
    0x4031100c0480e0203c400c560850300c0312503c0550141c880240c4514910030403224aa0600c00107a0100342070340b91a6040c4c424050700d480d0303480012401140b002c03084141940c0880c000c2d44075035042c0c1203e003c075a0182e803590100b500d48250b0320440301004000c0310b070032070342ca07075080041c00d11040c0c0070b55000b030282880070381094031900000c14542075003616803200c2a0300390600c66942058480c410a03101c500c41b986280c1840c2009005031401602a003001201d1144001c1003001d800030441d0786200d004100350382e0780d4038160700c3c090020802600c10100611481d090801d90303050240d0021040e580080c1040010482406000b0151202c4890601c01c02c00c18800c03248103403241800d04c8090351280d03014001d207904000301240f51212038482c090400d806d1010810410500342c1c2200d030030401844d88503070a1310003e0301079400f400d207000f1800e4000084005100c140041907000c0d524003180c080540392480d9942004482180804881c00440e41041004000041c0703683e020303030f80c2d91262030401030a113 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952917697 1250 952916447 952916467
    0x1a1c0602090a030f110a15030b03010f02040923060109120501021e0c15010f060c050f1b090c0306151e21060922022202070b0106140702090c 62
    0xb41a0f004446814400c144d901c10000c5035142061240e0040e17900c01e1040b4a0192122800e421040b40d00f01859038401c06040c440d1400c1d000700d210303500400b0781076541390b40c2c3d24904001050b01c6c840d440040310441040103204104c81c00c400f405200143e40b1041c1103800c02e46241c16410480e13034200d6180d0f50070480241c2584041400c0c00b5039124040489484039403400c5514200802c10320302c1c14042c6400320051011814048041040c2c4e02d0500c0d00d580724a480b481c0031440c10120209001e010f206840401640e40c03e496072018528100b40c4a802c49900c4038401c2400f80d0200390b030440d034040781c1e80e07411000391401d01000d0240c4094944101d80c3c0c460300e94000c05d03d50b90010151059180781c4515059840d00800d00c00c84c0c21072400e41f1018081d10303140c0104c5404150a0003840701030400018000306640c3d94025031024036030f0543d10100b08024002040c8020352009a08071000f1240311f000150044c091010618030702c1641d001c95140c4080c40d400c00039442d000074071400141030180131079509 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952918947 1250 952917697 952917709
    0x80a0e0a020f06090103320708061e01020a05161d040506070c0f06091203060e1015030b0604090c020c010c0b06040f0e030c0f19150515030a080304061a1c060209 71
    0x455040003018500141f078904544181c0f040c0105400240b11016003442000e80b60b041c0290240c0080713007242c85d040005400100d0901e0340c1050003401d98400c4148907071849041100074022111300c0c0750114003807a5117490101c1c8003c02164050003903042903000900c8503016aa103180151f01c64051025500090740d04c8a003100e1607000c0c20384d542e0f805040300c120001e42500c2000003170b0419815070741c0f041c601103001d405c1700c1d078207801294000402040b001358114001d400c0300140c0c01004100f40d850381c0c0c503041002300a000640b020f0380184503682c91556154080c0461a0203035802448101240d601c0e60148400742010803040307181141e98034119107480c0380600241c2280d14004001d0702a01003011707080c40c500161080c4081070007509440410024030704214009950500d0711010469549010718500c0b0b49100414154160050b1101d0600300092480254845d034031031001000a82d0030300d818011080b144002c941c0d0080c40054030310300e04034214140d1600f0b15104400151810400070b011400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952920197 1250 952918947 952918991
    0x206160c0b07050d0b040209030a061e090f2d0f0510060939110c06040305030d0e19110d021f0e04020306010c030c05150403080a0e0a020f06090103 65
    0x20004070701280c68103c40c2a50b005098030703108101e4066080841040009072544010440202f0103544e0340210512030b02c4500010b0444100f8040c208000c0855040c0221401400e03c1d0488110410b07410102142c0c4111120f41440d480510540c0c02c031b07007001c7c0d8951112800059041c0c600b0710842d10302840e00360150050b80c01400c14400041062495144003514001c02089907421042c41c90104050b9030090482c0c00170700d030119282c51080b0205016680f030a00d9620313069640c00c58400140071050200c000300a02c2520140001003006840500c0c8082d1140760b0020016010f5a01c2040040031a5034482e40c1122864020044060068154000b410006661040950442e9030f04800070b803050b0070a104049804058030158a03520342040001d20481c0010002000d0014560b149028007100f00450060380705440e40b01c900c0c5083c2410007034020074088611000c040d04002d50310548003400700300015015400340c180f1120002d82c0c0b04204041d00b00c1c0f0940c40c101a51040c254418540c1c00a19007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952921447 1250 952920197 952920211
    0xc0307110d0f110d02061315020304050a03080a0501120f03050d0c0306180b06031807151805012303062e0306050a0b0d020f120411030f0d0206160c0b 66
    0x20203201031a0b0703000741c0101c8140e158808a40c12500d0608101c58011035100e5000d9802d00e42c07855981000c0c074203c03081e04684420b007404d0a1010081008218000032f09000040c040c0e2502c074888e0b85c4503442032065500900419044800407000d41c00055508445000024400d0504a0a1a05103445042107609114071040043c0d140c0c0c0d400c002004500f5003280d8601101c200a00c034100420001c110baa100260120441440300545594907210902200e40504020b501c07581c210034410000500180d0001c42c4045103410b10203000910391b0185070491f03d0300c021409104840c045520340c101c0c00f500000c1820360084040110810048120724043e0345c3d40d415400c0402918034030f0000101214400d4200c0c03409038052910a0040d508518180c031046820780d600541e0318502d22602c2c40d518064122105600050305051104018840c80c011400c54000d80440c0c41680d1400038285d9120b03104660000580c10490103d0f403030007c54440e0582100307071401c04000b510b00075901c51600c1c14084541d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952922697 1250 952921447 952921457
    0x5130605040c1e020111031f0f06080f10060e010e1c06060e010504052406090904080912030901050702091b210108030915160501050a0b1c03080c0307110d 68
    0x1600c101510b14944076281c2c00d43c070080010110001448206e8400984042c0709050b07000c2c032000c80c4201d0f4100c0d86000d00b203000d84200b803599403418080c15191040c0c4040c1c030520309180000e01021740a0901000304d440998070001da404c145001515115014000c040e0400890307112041e2084a038074258611038032454001030528134000000200c5401178005034400c90620041c403441d0001c1c5101c0d410680061a0700c001421201d80004156105225125811442c200c04120600c416140030707103907a5805a1300c404c180610140190789a01c26240c820b804034001748496030141c204071f400c140d0b0080324003031241a245101041c8006c0c0342c004045081129506101300354030b030381040071034a004040440085080100f82000100c00ea0100c80d94a18407240200d010b8043e030013600798042582c3d070094001c000f5402e0154140d00904031040300f41c0d001c0d00c0c84101c166440501c0b00c085c0c05115425a83e40d080e242c49a400310b0100342c0c030140a401c108003001d02c244d0700b102001c1c0b001940c0780c101600d80c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952923947 1250 952922697 952922717
    0x1110f03060a231815220c05040806070c02062d030f0603161206020901120f0507020712170c120a080103290c090a03050a05101b0905130605040c 64
    0x20403920324405080c1c490910265800e000e03001e1501050f01c08080f404540e84441035244400e0580005494122401b6950520140101c2640c000008009854803001074401a41d51083c0996540345503002c0250009020005258548100c0c1c0030a180e4a50b9004040514030480008500c2900150b40007407041d4203660621a03e0f2408100c002c110b000006510340d8a5032600940701a03172510100050111a00060707101d034035038800c6a2010201840c3c83c0201301000c148403004004040842d45071000d0302c5581c201045030003022060302540c6501c030400c0422004c030446650500c2d000a911206184548078454042000074000b074100042181e40e213055561440c1001490340c0006002041e102c40c3d5000c042036404092038000d54462104094a5078403011000403034035030462948058002c1c02115948410032030700aca8a0a104c0000c2c100600295540054412006902c80e84e001d01080f43c1d90010481d50508094071003042c0c1e100400020f81700e5907240881c09542c2d030502900000740301040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952925197 1250 952923947 952923949
    0x5010308040f06020a1a04030314091b0102030f0706020a200105150d0b070f091e080c1f0e010509060d090b0a0203090705010516080f04140301110f03060a23 69
    0x2d0301c000140158030090001003000d07103402549000301c0201c20a18a4100001030505000f070700b01142600c0c0c20342c0000700b00d2610303800083d1140743c450b014920000c40041c00340320644c4000251505200ca2840503441c1c1034403545c43c4c0001758809982c580038045144204521076080da01440e40c4c030781401d03001140900d003d000c440f070a000d01c06405440b9000720303030406000c1051107600315840003240c14020445c0141c20801d940486441c0d2010519146441c50b1340081c4986c5049039049420060072101c642010300100300036120743d109603a0750408035802007070001c0d10070042d61204e41410b040c410319048501010803a030758040b1045000306a100e585d45400c10881d07295551740510306210440c11400d042c0f643c00d894101505c03606d03041220105500b60a520022030306d90b0b0307995010780800e0f80d03580300043d0001c003a00144240c0d403401807007159001a600701801090843c3c02601e41e080e10300703003110840d1043da80024040e56088504090041166200860032543d1005405c900e1540751501c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952926447 1250 952925197 952925219
    0xe04050a14070f0b181c030806100816050c0304060521060a1a0d062d15050d020d1410141c0f0f0812090303130816060501030804 57
    0x20401d16558490041006006a604240002e40300020440c594031400c3c10a60781628854032500d5500c1607290302d502c4414091004a0031400b072103078840c2c0c1c1156645208200540030484a101c0c080317000c50700042d100306210b40b5240a1039145080071803d00c0c801011141c51500103400520107d03400044208600800c0c034000a41040c5403c1c01d00c0841c07600300d0100c1c4900c0355501c1050085411002008840105001a64884202098200b011a0343d0780e89040e417400c4c1404e01c54603030b0512207403c58403540d41f00c6c41000650f0b03440808195800d1200404540f140c1c020348281541990034052290310000c580103072808640b100d0030060b0b040c2080740c4d80c0c207416201948540d07403101950304d16220300c2d102e038039010403180c1007090303105105007903070a101c2c0c503051000c0e03401003012000800640030020002d0281050781c82c900d94280720b5965400c52140d0300e110940e4003072010202e54140e00c0008010800805100520990dd441c14944c5a40ca803800d680080c0c00c2242c00035030125080c02030392404c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952927697 1250 952926447 952926473
    0x40501060603140603070e1005060d0603020406060f08130c030b0709090506010c030207052407140c0a080a02090403020f070605182202030c190c050d090803220e04050a 74
    0x31030300b2100c3c1d00740100040e0b55000340b40310f45c14850b134000d000620042d10b11460b001c02024007800f02640c425403121000c00400d0a4042248100d00d400d0b808210903100c0d01002007a1589515086150346481c051451151041030088888140001d00400022000c200f406c3c06500b46440d00520103080c980400c0a556005044e1810001c00c2a040340c04641d0000b900011140242d80341d100905072a0850740054442d0349241e101c0e00c20005901081041d00300041c0124440f01041d100f0854a000402415841a00c240c0816510280301d640152030840e804c42d410a200e401110420030307050b0215410710209920100100e0340c04603108400d004501000d40a0490840310840002c08059940490301e10049100030481d0340880002c11076454401110022100240001010801648001c1111300940000c807503078064904c0700c021281c02100c40000b0307102c40303a0141d824900514801501545000c0800d214104516000600c0102c0851a240280e00441c06085404a2070a11004143d05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952928947 1250 952927697 952927721
    0xd171b0721080c220f0b03090c0619030203090c0a080d0813030206180a020910090b0301060e06010f05190206092109041a032e05011508060d0b040501060603 69
    0x4504012100d0728010840d040c84000c6084c54029020608807001583c0c3e81e40c104281804444201050900403070000d50b00c919050022108510385080500941b4050641141600c0c0070409551803054029005550701240700030446205102445c00a00e0600c890b0303102c400c9682000e0002ca001030390201c0a1079200200c02e40740010168290380c001d5039001c00401c0c500c04258101c110b901024418021805407640042003000039042031501000c610855202c0c4d68a91840c004030302da03081c14103005800445171040305801141e9204001928400009440d5900300a010003680c1c101001d8401c1d0f503050314050358006e040e1403404208051400701c1001c07030201412a4129224266030105003110aa42c805030b60226050708816801c100ca0050920a280d0500941d940c0014007602507210846441c201c0c501003811040036511002114001e01511140c1052210f80c0c441040c000c00c12180c1040c4080c020f110560680c0d168003044000c190740840300b40c0d44440c01000318030743c180110062000c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952930197 1250 952928947 952928957
    0x510050d0807060506010c06050a02090909151504060e0a06030210050712050a0309050118020a0909080726030406020c0706080f0708092104050a080d171b0721 70
    0x840c0d4640e0035403801141c0005007582d44601c0002d50a074410807440243d10b0388050240107a003443c00320000690000c8164030302409524000801101000900d0040715840d8020454580c6422880c0e03114000c103001110741050302c0e01000103c20304802265480f4403502d800009049056104000062200c1040031082101c01d201c40700100d2041b40d001c0b03040c400300c0e0800542c0c6981c3e03108194042e20700ca080140040d442c114040c01135240240040101d01e10844170300c20080c3d1650503800840700a640082d2400d00c040c802c1000080c0c02500703c0601e1182411034094000740c544100a07150700483d401c4880170b80126074420004410480e40f00900b0303640c00d14856911b4585101651410014122000c101d9440d0104102c0d230428028a45550411503140741d4006038000c100800d03034071501c211402980d4913000001c901d5400304600006c05400c1d031b654024424422030440419034040d12681c4c585900c207212030050102c21005000192181c69940300344e43d048000340c01c08021700f44201d82402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952931447 1250 952930197 952930219
    0x606080108070e040f0f0f05160f0605090301021329071104021c0c0f08090d1e020102040503030301030b010305150906310807050f073c0306051005 65
    0x1900c0401c146080d56002d000000640c0ea40e818408402100d4a8010b0014480160741078140306010b5140003446024804039040c0c0100403440140d41c81c27072441600709459101c03d0034449d080c032800c024000240000e0016043c03441800c070904000d82c10b90700580005081d400310400e410160300d0303045100716203681d4181c140700143e181c0150784140680c81d2071045500040c40c0c444840e40d071800c1c50800c10004401c00042949072405030a5402d015181004982000d000420480340000c00c1103070800641d5403208510b000103a4504425020304142c030555409010201d81500e040018500a500500410b140c80d451410030a0a0040051480707680c0e049120402415104c001105a0810000c058400b611030f020680340116007030081540cac0400d0744103201c120034020164043c04846000b03800f9100030078091403d0b6030f0303203071071500c10f03004e82012108810080030011001c211048039500f03c902441103480c4d00c07180c0d04543e00c1d0000c846065807036091010070040066041c0280500303a03a411a20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952932697 1250 952931447 952931459
    0x5071d070c05030702130906110d1406030c06030402130c0801060e010512010513020714101413060f0f0e070e06010c0c0306020a03060503030c060a150506030f0a06081f06060801 78
    0x38070074400086c0c000c031044640075031144a00e502a965081d0080700801614180c5016070045500a104083c2401c1c100f90012015615011015000d108014001c040c0c0b46079010074040a504010000d0b6405064040a03041c40c1c0594000e4405080499540225035810040081d01444203011a03170704016003840700d1760301d00151101c8141541c034200c0745801c1c503840012420003c1d03c61440e00500b11000d0f01d0044100c01400a0740c0202d01d8103244c1e050081500c002d00d4400ca0a1040750400d200e00041c4120101059455020b948604001030303021480080139501c2d8001d982d5020800c7c0003a41c0002d03c10016020451207841c0c00c2802440c200c4401c1d00d0f2078540442c2d544480c08080d204a42c0040d02102d0035001e5440b0200800b00602600e494020581c0460386401c000c45414906d141001040305111070010201e0703040e1840207000c2402c42d100c90340c2104442d04028a444400d41e074a1030080341c0240300f004801150442003480180c0b4480c07a4024000f500d6540c1d1011040c40101c0d4014446 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952933947 1250 952932697 952932703
    0x7030804021306150c05010f020f091c08041e1a0a11030f09011404030f030c0c05040b060319091407080f0106030809011158030c020a05071d070c05 65
    0x1520310740c070344100d410f0f171142850b90052003441c0340039580a10010ba00010511010043c0c06600011070f841c15600708c81d07988800d00c1e0581c04400030b040050400041c0914038110b5420049004001c0100551980f10201c08449800f2002d0f10840d5100103e141014282d12180000802003140d000d18200116805144c2240c01141c48450610011084c01010684841c0c1541c006640000e00a05448c50500300070f051440c0505041e180c070020100c0215250900c2c2c054072039076810107800c07146550780da1080c810b28154035007600da46aa848a600c5c201140c0ca00e00019013007030741000035114440c601042946031890100400b840c0f40d0402d001000403d004102303aa44030718082c241030350400b0061391110300304011500054900701101c03251148002d152a03280c01414072211240510a41908240038200140110402a501110a0075450610940007542031a1403401206c21412840c0ea445081514540001944088846906042c0000101c0054105100c1d00349110549419100c03151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952935197 1250 952933947 952933979
    0x1c050a0c1e1202031f06020610030602090f030706030f0b09010e1602030c030d09030905041820031b1504030c061d120601060e060903060103200607030804021306 71
    0x846103040300355009820740203510b408015074041c1c00c00c40d928035056480700c40c03413060381d10b203051800d8000780041000c5000188803401030b400a00882c1a852640e500e075070203036004083c1180c005641940150440d18100300b800c0c09410140c401082c4450348040721022598002e84992041c43d552004000e826034402d491030300102491400507802030720b030740306901d14803605411584034840066104401c40086d80b0502e040c1d40319035250f02415540708204802c0c0e4004c2d89401040000140140b030004240200f40781400a181030002030307001031a00000e0410040d010a100900324829216200d464804c4805030001c411188507802c3c00c0c00d540f581c14001032a40034107424041c105d41200c4102084889060140d14001e115050741541000c1807922107100b8422200410741c4114201041e1401c82c00369402d841000d0003c040582c0795464ac020b01c04000c80342040d80403d0b486001800f074584200070304078030780241c880c420182018818400a540c0c0e10582000381880c0900520648402c401802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952936447 1250 952935197 952935227
    0xa150228210207031a0105040609050702030a110f01020403060902030c0307060c110a0b0a20060115031505040203040506012412090201020f0303010f0513181b0b1c050a0c 75
    0x140703564580344140d142075195040544401e000b080d8400c0c40096604a0794161902a501802426550f61030341c0c003520415110035000d60403c1c4144840d1912519801d83d02c03042d0401129240302044010394226805074009a490340d4070350202c0015820204081242c60030305500401d031442c5448402440b1410001008100c46c003000b03000c01140d40e0345a0008003400c5460000c42e61511b03c54030241404018010100d00000e000014400501e03000c5141070480b100e8140309022042c0030582140145000025401c1100b049113002c26140c507684059031040d8407030001006d0b01c1d41011409119600b02d40301011030f8400c6040c0c581d80030780c1e00140361611a1100075000c00c880d1458070060307052111507002c402107031101000000328600c00e01001000c440c003d540340120841e80303460781000ea030466162001e8402602d504400003d08922040d040060000346002401d5203c2c515154681d006400540c0d081d00007503c9203030003011031b12900750072900d00300c0704101e0308a000c000a0328141440d4400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952937697 1250 952936447 952936493
    0x80118020c06010b0904051b03130507080102040305010b01080901020703140304020d120306140904020303032208070308070e061e0a020a0f05060115080c090f0a150228 74
    0x2048911290192041540c00d0010b40d6080d6854401502c142e8021440781c0c0d120b01e08000204500d814110005d0244200107036000b0f03d1581c4201a08106010b49441282c1d288900000000c3c2c0c1c50707003072000e003000e144110004a5118062000105011030251140240781d104201510000360080c490400c1950282046500c941da1800026010043c0d0030020700b84181c0300074140d810701d926078000d00a82d00300000691030041c4090501c0312048003110000d40603801040410070840310368140e001c046c60b110000780e40044840e901c540e0703035400c0054100c010821140500a8483e00200600700a9a06640c840c0c141809821142c0d01c030b044503003406e000e8a40000d86140941d1090107403e4820303800c60503c6881401c5880c0c22030b615034092064031124401c200c40710072854400c0400501030000c5d00d0b0441c0c106a0090208225440d007890900d9002891580008100400c0308640c1403a00950300900961a5030035124980a200040c2404441b1941000c1034001400d403042e40741070807051200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952938947 1250 952937697 952937729
    0x210050309030d110418051006050c0a0f050106081c0e090c070f15021b011b0206041403042301031109101b17040602150402150d1d07030201030b100801 67
    0x40485031045401c200400346418501000300340c0c0c40e4100501405c001c1004d00c5230720b0394030f031411902ca028031282104140c07c6294924040303000048043c070f04c0c2d4022800002c1c42039807403150b240343c80c5000a030745100e00340058003800100d0b00400000d40c011002e071400103152911403002d110740c4c490620000c000041c0301e207981060003402d203d110100380c5542c1c1c0842d070740c440704901002094038400500d03c00d0343c20041c103c1d507100300030b55102e030010300641c006144544481c0c0e40c41c04820b04c008403402040c40f0034000000c44600d0f6804031210580380c003e8603410307401444001015241d4451100e07011071010007100e800e41c0c680c2ea940500c1010030380740201050b0080f165201c5400d2104901510200740c4480130003400100400034404c855840e000c40b5404102042940d104810842d4043d44c8400c0640070410f04c950400020684500001000a40e5541451307140d850f000034005100c02540c072000c418000c5582511400784020400c550312003032403c2c10070340145180c00c14040d04503007040c1080c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952940197 1250 952938947 952938971
    0x3603051207030609020318070b0a1e1718010c140f132d0f05060d0f1515110303010f06050c10090b0601090e04020906091008011401030210050309030d 66
    0x100c84405004d25090642d62401c1446026458a82000403042140216040018181d981504503044001540c8a150315200c0c00010103031a10300d107102900c02c1c0071242203603409002100c41202d214801c0b41c0050400152100c001d20308680900d40c00005200062030700004002c034107815141d00c1c090031202c495071004404400520000103612006101c00b5080d5907500c20705845041c0c100c103070501002d80c03e1966480e08450318040141c401d907034114004120029012001ba00b042c0c1074503c0741c00b8040f40c050781100b80d07407200e9009503010b031b120905012403903200e9580c00b00400303100c40b094400450465040802c2502d60744203920680051007030014801035011414890740000c04030501c005c200001c49800d1075107201c030080310b10a0000d03190482c00300e890b1000104081c0915000f9114400d540e85440a000307905001800850358005c14910014004609024091103066001c00300500d6500d1403043c880001641d0207450188074007401086a240c00c0003094901c00d401c1c24002003034900c1042c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952941447 1250 952940197 952940201
    0x21206040c2c031608282d05010b0a05030c181f030812010906030803040b181e0607090e0c030a1514010906020c0312090a09360305120703 61
    0x180006803d40200b000c41180c00d1044070149041701d05074401d03100807401c2d00c0118540b40f030034055030042e4903d0b50083c4a0100704544d0848130900e01320445510100e801055101c4a102000303000c03200781c0e46902e28003803141082056100100010b5004210551150000030001100c0e007211030781c90844140003403500340d50269038000d1030401840501d180d0342c42c0d0905c1ca080303a01000003d503941d4603200001641c1c049a100d07110440350415800ea0654407641e8865040700c1014141d840311240713140102901d6102800601001604501d8075446138a10085242c1032420040503081406507020341040002503101c4843e50103014a424590b0740d5803002403034002819210050404075448080116a05101c08050f00e21600c0c2600c6540034a030f92480120381d030301c000350708242e0150007c1c1c646104410403100034003c11789008103031403001a05c1c2d0050400f140d0640c207618902e01e500454900f41034600800340c01c1803800c00e4100380e009420b262000361440c0729800c1c00c6051f090814000030180c03442a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952942697 1250 952941447 952941527
    0xe0618100b03100905060306010501050403080a110106060315050405271216110d080a0c030306080d05040e0109110301030b1815012d0611160603021206040c 69
    0x1c051401e88078100f40107100e030aa011405a01c48a0340b030400806d045240002d004d6040781c4059554610302401c695800015401c10180003050228181540d0810b12080c0136604c0030745101e0307400040005d1813100c00ca00560040d401213008074909424014440002440725004140b140c0500300418481841036185c5002100c040088410200c0c1c001c1405c4001100751200c2d0340100141e01600070710400b000321000d080c140c0200100c1080181d051003502075490101c08a019080000e81c0d2656164614204900340d408a000107100050501140140811381405845600c104015400c0036840f103141911040c0400351102c4080400115500c01e410078035514a168042600c0b12181010740c0c03103004020078041e82c0c0d1281d21154480e40e41e1a150251000e40e81c03080700703000780d0191a001d000e84140508003c41c0d41170b8014184003a48044a00c03c00c68000c104035a0016039410421100c1d198920f006021184250704000c0c0c6242160b0b03000f00403424003420344650418a45021107209004264 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952943947 1250 952942697 952942709
    0x615090204030f030f021b0103050705130308040f0f080709092a1a0909270609030c0d03050708061504171015050108160201150b0c070e061810 63
    0x180071080000b495140203c0d180300b610ba22021a0344c00009980759001b1040590513041c020001c0000c83d0300c41d801558010340d603400c1591625095a2407140361244c290026110880e00107400c004011145030b00310001d007003001201e201641003108182d1112590f1140c2c2c1c003019160148641440400207041039248210340c06a58a8040c0d4652500c0059a5200c1c04200ca2098009075108020010840301400d40040281d00f41d0340c0c3c3c1030010a1800204000d42c410102d05000c4100300c3c903c00c012280c000c5031814000e50302e07540340c00c41b0b0b145045049401c1c5020142400180004260403184164000c076085914901e0124285c4001c0d10f00d0145034098030f441e100405140b41d00000108900c5800410020140901c5002d040c405000c020140b00d40303400100b41000040c2070b500040e00341e00c040c110078400454107007a00310202036805500d8000420310000004e01c014030140803c0070000900003042c0034402498500c0020300e021a51400c1c012241040500146e000000c02d83e000307001d420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952945197 1250 952943947 952943951
    0x303030f0a06180e010c05090d0609140d081602070312030903110d0302040509130b010b0307020a020a150305100e060d0305130f180e0c010c051905030309010b010306030f061509 78
    0x794046442c0c0203000f02c6030b90340640c1d521b0049101c500c5803051080740d0031404090310455101c41c4c29a10140204629501613078000100b64040b0034644041c0300c0c030000b05820f50350b01c1180d414071355011251844400402c03000d40d40444010000600d440201841660144c100010030000340d04040c2ca10300c81c80014035070140103480c941c5400a8044d8041d105a44080c3c0e800701b40c507694030781101d1440c1798860001d4003400c0020010801c620f01e1100465002c2090310507580b0340c502a5020407040b200d250003540d40e0030360041c2c098009960510419900a4031451204420782c5000280345004034003030305e068082d2840c100100241070196040714446c081003104032401c150b4540342d883c5500017900842c01d1040b803000000c0300c4c4240501455080c0109080546140c500950066981e211004d6084503d03003e2008100511204070003490700040c01a00a180e40746086110203086480f9052454180b600e444014804200c0000101e00c2c1070360721180c00240d1107020000700d40030300c440360305c080c103168 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952946447 1250 952945197 952945229
    0x1e071a07060c1808030403110f060d0203090607120c081506040e0c1b0307110f040b0904050d260c0a17040302210f031f0b0c0601150c020303030f0a06 66
    0x39880400107501e0240c2a031848420b03a114a041c45d2030340301d070b807001501441400f100b10401c3e18200d211034801d6040108005c1c6400140c0341d1003020390f0401ca4084115820581c00c001005412042c0441c22600808040040707c11140c1d01608140740a80600884002d4060203605a1074140485000e07000e40407404000c1d05c0c0c4002520525030020a4083d0b080540350f0300402d40078400000e4a90a55000182140d46810401484410090103d81d00c0c1d0041d241d0907444410380f121400b1380d01950050002e410305000d122000303405035102040c01b101c008100740820030000034a2000d1034001c5550520265914295202144d2480d40c201d10078144046500600c0209a000aa000c900c2c861284d480703190b6010081150409010b250f400f0440120b0801c00190301001c40180601d00c040c0c030700803d00c41651503080c3c040b21504055011540b44c2e01500040c0103110032040c0d40790503140c8915241a01c1d42079540800e8590002410082d14100c041c004100580001c5d0003500147c02c04481082c591 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952947697 1250 952946447 952946471
    0x11040b060c0a110102030c060109020a090902070516051c0326090303040614070503190905010507121104030503220503100f0b0108040c2306040308040302031e071a0706 74
    0x501c0504002c580200c5050f0b50a0752550000c019502d00a1120b0050200b076803070840042c02a52100c0355040c1000703038410340407601000d1403001d0a4110302400040c0011458a0141400c0c00c00e42d40009114201c5220407000b0348403089200707204954146840105180309946c422184104821480600c41c07121040040c8060004040d41c400e9016000a224008881101c0b0040030740554250000900c1040000d000c8900c10810380580c8002981c0041c100700141c403040d00f102c0064401c000020805041c030b024800c09400f90481140070b2150961503c0e145580b8155213100307400c01100811a03603a40d80c10703040c00212102008060140a849400c2d0354550705030020001003040e850014609001c3d00015480b582c9500d10071544250441051400c1a42010720341412141d104188602d444007810300b503c030f100c0540001c62213001c1c0e2a8840e41144100350a00c2044100d502d00300b041c64a1000d074078200041c0040483d00d103540044000510601ca1a1851048050140c00e0300d052198026031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952948947 1250 952947697 952947703
    0x41104060e2e0e2e1106060d0807151a0901080d032301090c031b080604020c0309040603050d03060b0304030903201206160207061202030622090314090d11040b060c 72
    0x548030002c0c4c2a81c3c044030b03902000742ca1307050070403414808660100c40000d210f0304110450a0303915008007810b609000319a0b41b044002c0c6140401041100d032141744500003043d4102c506102000119508100d540c103010b0625a03541d10714140c1c000b00740d02c4141c0b444481c1e5407441c0000c00e14038030381448100c540e1160010000340c4162400800068641f15640700c03040c1d582c41d118114500c1c507a6680e02c16889007030412019421807501c818441c0810804d0740425961842800c00031442080500003103980302401a08030b0391aa8099030340d68004004000010354800304100903070f43e10001d5900303001d84c00810034495540d0320300025040141241040c20010b40080c0380340c410004035441c04000c0d41c001034200c0e190180c40c46944045805201b05404601070354002e10f82c000b201a045001d9183e5110072560400d50800f50441d005940d26812024140d0007100d903d004455800e008e8506105400410442d441d0340e00d010b403044901c01c101584646e155040340142e18402403815072034142202d80e03503131 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952950197 1250 952948947 952948999
    0x40b070c03031706130c050c0106030c08010509060c0a030f02070b040f060e010b1003021b1e0d180e0604090b0c040609090e0d1805041104060e2e0e 65
    0x1140383c80c1c0c8407502e10040346040324483c060140000c9144d104407001d00e0068401004c0311414443c040c042001803070001d1081e6001140103200c03403024185840181c5085500113403c042690300928204400c1c500110b04441000d02c00c0d00d0f0000d00142110b000e14000e02038403034020301081c0302909120600807918444034981e405110100050078400e0503050807907a40c41092a001000e40c451010024065805880720082c40781660f8040300021000720f0400071405d103406843c16200321411900401003000d106d0161090a00350507214009405042e6200103108502d0341488803030000e40280c4882d0020401150321141b07440c0315040400360200716420600031400000e0802d18001034a01c00c80c0501280082400c001d00020020100112180c4406010882802c491240d00046603180d910407500310003480610640c8490600f40028120410881a1031091058100101c00003030f400300030343d6111405410000750741d810800181c0741c1440410b001d613800100b5400790034000341000640a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952951447 1250 952950197 952950203
    0x3121a01021b1c1e08130f0303050f0c010e01050423011e02070201090317030f0c07020306010b030709091505030d1b0803071b03230a0e040b06040b070c03 68
    0x30700901001d045502200c0c0e1090b44403544003903099200031440f10041600c00d0030318021070f05540c4604600d8201c5200d4290b00c5000c5407400c00000f041c3d5010140b01d40c41303001416203107104180d2103146031801030103801a40c01043c107490b4001000c8900590941c403807205020748000a11541c5018109407001703010310b078080c1d482c40d13041c840e855485130750611070141242c2c220035203410315070b0300e10003000c0c000d40009008a040c00006140400468941da00c00d82c44550300d03001083d602d01d4403030100300042c04050072410303072200f0038080d1030300603940414100d055038414400b0a4513940c503641c00311070072040340c0e22420410b4038040d003a001080134104030b0302c159207064003216000c00c2d49200031070341810700404500610901181c503c000608607401103030408000c3c80c0082d8802c08404000d0401e0101000480200340070341c1c000281c00b1598030108040400e0328580c5402c002c4020350280504d20700d803891a00c42e941e2600001503965524003070b50007404851218075101d02c3c4a10f071407401842d543c0001e03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952952697 1250 952951447 952951453
    0x5040522050d0305070921020105040807090603020f0409020607020f011b0807140304080d0807021e030309060f10090b1c050d1209031e030b130606030509070e060d03121a0102 77
    0x3c0c0e00d141c0100c00c0d140480d4040901c1c0911450710780c1c00c7d545081d0844800300d040150801000075240da00300300540c040e100496001070468a9881000001c65070070308814025400d103030701c080c05070b5500740c16154491340640700300c10b001620b04c004803019541071043c103c1c004088002082800007101c041d003803d034072076061459043d92000f00a65603000d48d03c03410704c903a404402c205d112940324880c2c60342c01c407965004a901c500221141003200030014480285c003940003000700202c00408001c0c1c03580209103643c0030200c1d41400e504d01d8111400a0040c5940d098030b889031b403451a01c07802801e400592070240c48440071540f610702140c40300c4808a2100001343c0141e8400d0143c1d50b5071142d05010350740f64460f080a410070402c02e5080d0348218202d07505156035048650500c1d01d031121000d29045071850005030392420240041c089070006007000207150302c801410f200071035032a0601a0441000c682c6100c1445c02032404581300c03e40101448107150402008800b000700c03403007801220010076026 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952953947 1250 952952697 952952701
    0x90f04061202040e2e02040503011a0f01030c0905060f04080d0804030207150c0b06030f0a0c2c0a090f05030d1406010203070b07080a0f0e070306050c0c0705040522050d0305 76
    0x41a44c582c4031500600045c0310301283d400505a001140440c0480204400341c1083d41e108000382c00c46140c540e16400390400f0300d4260a803450400c1424101200908007044040c54941c00140081080c0c018240615000124242d10000760b5007500d0042009604844100115010041c801e08059804502610550001290044c440000c1920030240c07581c40d00090142d035154101c4a860207070190f50140141c01d00c0d40c0f803a50302407020f00d543d140502da1a00c032041c82d0500c940640c200c0111006900c444c3c00c11000e0389030071a000f24a400000016000c90b80183c54240309103521010b4000030454480007800c3d44810b502030700f05084d10001881c4585aa030b1b034401c0160380720300c03942800500303071a461000103c081e8010701c4050b4118182c24400a0170340c0340b4412543c2140e40c00a05103203603510414040003003041a000722039002844d221003030704114003001c070595102147d0141c1e030310a40c0c60381300003141840550100c0006019002d000c14440c0b03028240182c03a8106042d407c00000c1c10480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952955197 1250 952953947 952953971
    0x40609243e0115030f060b0d050d0906020616050d020c070518090712051c27080601090b06030406051504020301230613030201200105090f0f0604080906090f0406120204 74
    0x80c11400ca83d0007040d5185e00c6402555614018900c40a4841d4000501c00e298404500100704400c6004002d80301c02c201141050006850721400810540880c007525480c41c030003550200980c0d8200117844005600c2e141c82c0e41c400c0d41001c0c40b80d004a50425600400b1038019005103c2c10b07030080000b002601d460300e48900380041145000c440242c02d0360701221444541c60200401d0511100300c902d095650001142001e00d007079401100d803d074140f040c50030180714811051100c0c50040c881075070104980040d44021801a000040c40a00107580c0c0e60005040c2441080103162443e1005100719a2903854010780742064401064140303003010b010380580320780d061031011031302e852004c568035194080c9994011101400174203540b44005c0c51402c0304201c0e0b20424001c86009042c2d40002c6c145962102c1000c81c0791411181149865a00080a210110b00c402c001c440360000140e44d110381d00c000d00d00104407012400310355640c100345041030018003581480c01104009108460a10825582c22 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952956447 1250 952955197 952955231
    0x40b03100f1a070206070510050c07020411280509030703140d08240d0507090506010809070f060302071b060503070e09061005071a0408040609243e01 66
    0x1003800c105800c2c00c00c882d20241c07038aa000751405501c110221048002000c88d40b90035141d0030703504200c221303102051400c21854203000321a90346400d5a02607040c24a44204560620030400440b00e45000e0090301140d40d51080c401c03101c0c075010240444841c40e603680b515001e441c3c4880c10101041c003a000e04007281c64807803003006018610200c1201e4100402942c8800c4200582ea005a4040f00881c2808005002070040000501c0002c2c800109460090005803550000030a41d40c61504074400a100300c40c44071440c4420358070705180058807071000e4030300351402d8201201041403c0308000000260164400000e40c410341803580d400c0011441a81408a450b40a41c3c4c210750154401c154100346610950140403000d0051403010b880410440034075020f070710291015260b190000809010311500b24185400804020f54a068078040180841e1500000f1810040401000c9014510080301c0881006c40c0c03039592a482443e04001010b00064524809001c60000c0d420014070f49441800d803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952957697 1250 952956447 952956479
    0x609160902091011010906090f0605090a0f17120a05010f060215130f20011d0f01361404020406020709090807080313050c1203070209040602040b03100f 67
    0x2d0f0526000c0418160169061891041c0c203211a640e01c08000000c90894021600e4940c050548101441e80034140310b0240c0364001e001545561000002d54005034107070300b0410145400004d460b820b5241c100010700503100d4500440c2602c40001b042c092802007660020341280c580021441c1166030741c09083c1d0310381210300c6a00080d4501d030b8002401c00030071000d03071441c0c0238458100303081c1202c40c0380d545800f0844c4040c402c54a440f40c0c001101302950308030300390b8094100d0806804401c074200c4000280f0515050654070b04006002010030100e41e14064000c2c1a44402e0300b000403000c2c050510b028219070b81e44500c0d144024503030340202030ba042500c01c480940c1e800b0f07400340601038203144802018142100b0f00b2201803c04001c0c030808504881e0265000703d244c140710600b501030758181545094240c055042c1720f41e50410700521000c00010403540c1c020f9040c2c610016940d601c1c1040c100038001c51b03000303520000001003044040c0c44002000e40607140e550015891142d115102449030f2940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952958947 1250 952957697 952957699
    0xd2405010f050d0b0901090206041707050d0b04570308040e1e010b180f06030109151214061803040303051c0f0e19020907110a05060916090209 63
    0x4150f1006001c9610403150301d50005020300081004c0f025540407402540c406d034060b00c80c0301103100103a042c801062003104010a822070300c055154240380c0f0b8140b5680c4000e80010701080304c1c1e02e151245000843d44285c1b04222040c00c2c03420400d8140d0a85140401c1c0095286284140750f00d08181c4090584840701565003051085003405d090845210607280e020b411040042901d003000110000c655400b540600485070203652941249008030103810360400c1018858810703000d21a040b80c40f02c8043c1c904441ea24000420700802e4054190702c0c00740c1d150003c0c044503440001c0076050101c440240a407010354841103841a544052000200480a4042c5085c58008103c01c201007407141000e0700311081100001a40b81005105c662308950b1008640170340315440d4180310041502c00c1c0901c81540081d005600451a036941c00103003500401000e01d8240004c1d20780400003801c3c100000311209a2000c2107407203c0c2411a0040da45e522041017441c442c080303d540101d1303000414001d803101c0f100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952960197 1250 952958947 952958959
    0x90708070605251a1509071e1d0a0801090506061206011206020f0c0a11010f02100e190609020a061409010c1115070209100f0e04020d2405010f05 64
    0x940c40807801903c98080b401a244540360b41c10400388580513900781c1e4050411208000e00302e511500c1808150b18006010303400b40301c461080070079100020400009016800d180410000303007594089680e040042e640f180d0003800090300130802b054154000c0c500c80c0d001b001141c0040c0d640381d0402c8504403080302d5000d1545c01c03210041249084003079031201d19501c1110007505101030305850141981000c10600c0841d4002100c071820300000100e0010003042c01e00e440d14000c030404201035664090302c41d419000b00e07503c5503164150074040c03100b0042940e07101c012101034445810207102800352990181d00c240100e503000503001c0d000b2001c0f070440071b05034881241400d89110054562921100043d1801018007601c0301e05a901e00319800e20201002a8140c0c9030030086c014032070240c0f002018a07000d84e41112082c040510700c1501141182c0c0400c04001031940d42d44045945400521001803c000703451307228840c0d18183e9a0181c1854819100400080c0c0c1da40003048690300c0f20703208441d0092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952961447 1250 952960197 952960237
    0x9081206040b1c02010e06031609300c0306180c0f050109050f2116090204062111070f06050604060308160303060506040e0f070306060e1e09090708070605 68
    0x180551014095005060040405004001107001f80e031044134902014864100d00364000c0f9004208000980410040142c0f180c1400c00105118103490b03030341c003100c460500218020404a21203038000356034884014003041101d800f4280c12040351400844102001e040c021920100320001c3e001200c0050703644080c21850042480044945000143d820804414403601e0004100500c5004211140000c01ca0a54028040d0a24086540009084c00d004010030005568028000b402d01d046880b4514003440f90f40b50220010710026401e50741c18940800c16405000e01c1c001d68400850144409000e1340d034440e0b00304400c4400c0e80c040181980000c1c0024038005480887c0c000d101c134071a00b400140d150700c901c0004d09942140d40070204280c001c0c1c0c1044440178410102c40e03001485030406001003414440e0140203805011035160042c03071003959551010b83c0211000007050b00290002d03607141007980343c864032520039011f100712a02c160400001c101e40b04408980750101c084043c00c400c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952962697 1250 952961447 952961479
    0x20a0c0513021608030603010b180103140a151a040203070c140328030c020a0b061504050d0302010603030305011a0904051003050610060e0a240203040909081206040b 73
    0x30007030503032081c069030b9400c0c0102c401030420030006040b050b00a0380300c41e07164079210081501396907607140c00500402074002960340b00302039010400e054903403000403648000d0328040800d01c1c100c0768001c0075101d81080c52451440c40025440318000901d105030b001d0106466009110503484244c81e03200014847c0380b483e20104580c0e41c41c110300e038000306c070a072864544003100700d07492441511440c10712521001842c1c06031903018883c00c00c14450314005003514038083d40321032040710001003007680035a0601c5104041d05080300100c401a0a000b41540e150320141c0c20001d0003070281d4001200441c0c9014008211024a94030010480400700c1c0564030340b501340c8043c00060600645002602d01003480007100003031060200511404041421031405854044010700c000c1101201a0140d40e801c803003440003113000840c284455541e260f40604415601e01d040b03103940304940c405003a2602d03200380031040001100041c4182e4141e2003a03404140c80f201e04000865860020305940601402001460 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952963947 1250 952962697 952962709
    0x60406200a0e151c0f140601090608090307021f03060602030408070603020c010b090c19050f03070e01020a05061f050f180903120f0919050c0d02030f0d08010501020d020a0c05 77
    0x5031401410301c42d400c20900d00e010b08450004101c0780301449885d0f000945080300a849030500c00b40154541c0c40550900c00e001a1030500d59002d8041040310314000501040410001c5425040d4042e184a0143c81855a041300c84130000022800190400310300041040c0300000390780507034000001618880742b400310250001e61182004c03c006540710030410b8001d035244c44a4901c52014050351580d903240030107070400703003c1000301303568280201402211110082441680d038001502d040880e0048007080050349021f00384200209144100000c0160080700c602d8000e40c0b80c1c420610000c00981c40c0d0b42004080301c0305002c0b860304900e0403440200044c903101c550319041075040081d6850005100e140d5408040111440c60701e0b0001c4006001c00c90104116111904242d903204801034810384e543c07162904a000c26451140180201d40c20075580d081c8130559108544c0c0d030840310012a925405480f01e1001d12580c0e002d80034101d25208010300104d4500c1c0741c1503000e480e10301024207007406c0000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952965197 1250 952963947 952963969
    0x5010305150423070f0902310e06040e12090a060c170a17070e0901050303120412120e0105040201031419050703090204090c05040b15090918060406200a0e 68
    0x7501d440b0319580001d1201c17624240f440903040708440542c1c1c0d540c0000c4404050192903814507822510304480046401d50180003074161000752243c01501d45488c4c1c0050068080c8100c00c0109004403000c0c043d02e0109440100540345e400e5492904c04d580d00d01c41030700c0f01c03000000301400c510280161008014075540082005801600b001c46c03480031050380d10700c41072000300e4070200864101e4078050104e251050120b8010300d0100d000358540804d40c021800d0401002e00000c3c224004141003d02c4075014000d0a41c01d0362260b1303400c103d0b124010030454007800094805901117440c01819052254980204a110310104400c180401981c3c061034001800010000c0f800c240c1d56050000059889025138101c49004812000c036882c20082000300b101c05c0400c0706440f80020550214440c0680c40564400341d40460342101e0795611310302c06502c100002c09080040340100c1041100300b01c0590700020341000d030401201e038140c0801ca01c0c00c0343c030f200d14150400420700c1141d242c03449187c80c090b001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952966447 1250 952965197 952965263
    0xb04090b0a1509240c02010c0206300108120703080714160515010f030f0f1a2508062808031e090a15050f030406050103051504 56
    0x1018180d0780b82c001541500b02c0301524030001e6207200041100c1e10780c80001141ca085140303944020480c19441c0582083c42018009051015020000e0103555808041e1000c2400141c01070303007024880300c2c4025020b508683c02c081c00d10740e040004510418001000c3c0130009103000d1261070044180c81c2511400e000030301310020040d40d060078146203183d8030040c002001c2c0307540d20650100d8403481e0840c05c0242003081d00700c4600781d0b0401082003040f0310340792908881e0050200e200000060500304000030040d80090180c08024030134600b520400c50005100d111054000d21011120300450a211100011070100191500b0049441860000711108a01e080c3d10001e511030b54886002041e042481d40c400c16140c0c1020549e09080c82c14291820b0115240ba0001890402c048000640c03000d00360062603110841034611440300c90142c411119042c03038070b010654980c40d0038905440900f800f4002146c55000da08210b1095105554a031802294801c0d00f074480704041620640d0500420040701c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952967697 1250 952966447 952966459
    0xe01080a0b0d06050f090609120705010e0115030c0902030708012102181b130303051312050703110405090a140c060409050708130b0c030402011103130504150b04090b 73
    0x70402c1c0da991050304191445a5004282c83c0340c0b003084d1803160b040040001d000ca420070010040103540c0800c80c0040031039426a0316440e00312609080e801480e00a100101c19881c1c103052001c000d0390703141c004049034070030809000810b89800b0782c9002e03400300b42c420070042000307030300180308040114110b07440a129080c40614a5592500003e40001d100d81328042d102401300180060b005c0100104107442030040101441e002a62100203002519480040c1c10094003003079484503000442440b4006001415889007202880e007440e9485000c588001c071444960050000c0250400e401100e2060b28004040d03c48092140c07a12208021140d16000c000e0003003550000f92582c600014202900d8070500012b114900300401909007907000c0c06410100c040c6910302000034a02400c00e5901c840c064140c1d50312034681d440165141c1402a0a540c0070703001c003140465226500d001e6082c102c68044600303120350800c0e03000400c9241300d98040c0414005003003000b442039103000e4022240a50b000b61203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952968947 1250 952967697 952967711
    0x5010e0d15141308030408130e040c0f06031a10121121060d141002181306120b0c090307030f120e0a0519231801060e01080a 55
    0x40c840880d041d820307070201d120303642d2920204803842d18101203038030036040c40c8981c0c08101c80380c0700c40c130242c0001400103140520029444500b90b1134440031600074002d015403c0001e007007600c4c04c442020124020100041e14094001620310312030b029241014070106050111001100b0034004801c1d0050b0004041c800c041d4031411000109216000264409810864503003c041c20b404103e07440340711180c03044040000a0007616910321450751b01643e40302400340b151040e40da41c4141040040000800110310206010440940400f003100d141c0804558590310340b140c100d1200110390250141c1e06c0005600d105002c00144c03000d604507000320794114160b080403207000001b80307012000d800496800e41150514000c000e9a11a000c0030200382d410041c42458105020900c000541d100d400c0c800c01182c0010030400f0034070891040600030071005540420f41e0314100020200c800d000b101e008140303602c8199624115070004038183d41841d0b8881075248465401100d1686024044403c0140e4a0301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952970197 1250 952968947 952968953
    0x2010f0c0c02010f111605030c10091e0b12010e1f27020c01150f03121b020a0312020d0c0c061404080604050d1b02030c0405090705090c0c120c0705010e0d 68
    0x4501c00d0030083e034031315444050f41404141420254140300c402d000c0c400b82b02c2016406900001c05005550b40350740100d00029440c804480034500d15804803801c00300008000c0700903046c040001d81070f2002000e50411607110070010008a03003690841c82d1036001907a03001d10001c80034601a1548c02500300c0503c0c9081c002d286c0503002c0740d1084005008980d1b41d6031030700203280c1d00510360400404c01154062861403540e02e40b0780e0400e1074101c4020401032644130b00e580c3e090403101d16104050300030b03203040103d03500c9103050381a55520a03d202c000d8866109401120b911a94100004a61120a000006103405416203040500354406245020700303000103d1150801c00141d031060b130051000388001717010000041e01c0c00030061048039040036450001405600c000070b25454090b400e80b000200b9554001109050070350300c0e00f22a502c2100c100620000039910009030803050303000025a07124044043c1030250078464400246600d0300004400c1080750300031030440c050900050020404420555 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952971447 1250 952970197 952970203
    0x140615030702011103240108090c0d060609020d060509010b070f0215070828090e040b0c04080d2109020d0f030302040b160302010605030102040f2903010602060702010f0c0c02010f11 80
    0x180d4a840e90011b854030a00b6411a800c0d40741001482820a4a003a0405d100b00135102c442c8480040d0061500184130410000594080e000030200c42400310b440740c1c1d21481c03034005080c0c0c511039a071203500414008508a04010308440490b948081803403042e40b41a8241b290407a040c2840d00b0360028180302030000b1442d802d00074900c0102c000e818145810740d258140d81d03038103403030301640301000039081042c480044071010b155080b0760003076111300d0702d84e50310a400e0080d07208940100c02180191400c0000d981d400c240c1a0311803200e00d041481038024684039400c00ca071080c00010703501400101d080000310300c51290210b41340d03000346001340c50203489403101c0788641d003d1500044003010f0b2040d00d605069081c03180d080680411002503150910301401c0c0200d000a90041c0c2c4400c0074884440c1183c8003541461820308000300c060141c03a50394444c030107500c4070000c46000b4055400c10307503240d492450911929140b4140758403450ba003801c503600111001c040b01d0404609000c03141d2001e1840c16810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952972697 1250 952971447 952971451
    0xc0305070201180b09031e0c0706090b03070e04060801020406021b150a080c0904090b0910060609050f01030b03071e09020708120612012c03030603030315240d140615030702011103 79
    0x103891a0341d07408c01051058505031040d4806010840d101d81e081c041028100202c9400c8911890441b1000e0f5030a400200204010f40c020316482d8400500040c140d0b40209080c10307052000c6505068140041051080000aaa00343c48210200b000070304c0000e800394201a821406680300242041d40880c0450301701c1d0078066060340c8a80c0f0b0b000800120907801c01c07000d00403004089051007000d10f0070710090b00c400c1c0907020300381c89145014124001c40c0d203c0d51000c800c801d4014101c0e110640e035010703020b240c00085011401030f0058088003091401580c000c444800d0f9200600c40c3c0761460101218500340009401254886503030310b0105001d003000d01860580391a12240d2380260422009980e9640c2034000c0c0e40c4103250001e000b00141e0350360210640382d20424101c40426100004000074046080c818410840501444400c0c541d40c011240940401405c0d00801c02c51400301091030a220141110071942c0003811442031540f1a40003000b4580003200c034000802c105440540e107103800c1d081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952973947 1250 952972697 952972747
    0xf07230105040b0a090506010522150501090b070804061805031e0c030a030c02121501060804510c0201140105010305070503072708010c0305070201180b0903 69
    0x4907820300060241940040744c020520182c20010304549540701511108140302e52032051a049404181c01348140154030104180014101304110500c41e100e80f41c05954011203000405502000c517103100503000320307503a50b60044086401c151901500320b4070340428441250700d03c89a80b60015541d1010082c120389454810b0700004800d0481105502c1d1a101105040c403075840801c202000c41c0d0400c480711440c0750180c0d99070341c854640d00303030300303842c040d4030440d603802004250000086056010407000d016034407600e91491840f50717445c3c02c081e01441510001c2c1040e00310f000d4010307100d5420000c1d400115482c03031401d0001c64075111008100c0302c031140805d025035160003201c00000b000300d01c05030140c0000d0804124909112000a156000091082040c00030b8201a034513040c40c05d0b0980c000312049083c0040610380c0300c0181601819000303000e04082130a10003ca621103006010310b9142c8031914a1328901501c2c0c40d15080302022003e04280902e00041200c0d80342d00e804100d0704400302c20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952975197 1250 952973947 952973951
    0xb0d060905060a20040b03252001110d05100b040807050f062508040911071209060f0c0c0306090b0121080702040902010e090106021617030f072301 65
    0x290101c65031041c1c601a00100351804c19008008100f00380710b0080e18107031000070600c1a22562812000e4140707540030030307003028214076041020001550040856075840286040c6000c442407500303125080c0d510348140c1c114256000d101d546650100c646c80307250b014904c0356201c4000c60b51542040020340c4143c010300700c580c100403428081e0341050b200d20b503100d00d01541c001d8a04039038074a100034200c0584136a032403e00c942035482818001480142c0d0f0152244840400615480b681e0307103202c91340080d000b2141590034015851540d401289017404a500741c0d147d1020404d80041c045600500100f021034039070742900408000304507940b0902001c103104e5802601da139418000010800d44011072907582d00419070703591000043c05001680e005130790607100424035901910042c2c0b45e01c04101700c8103401c01d601c2e100000340c4680c0050100742c100b011005111503540c89000130030190701c043c4550403084c0d104014180802c0584001013008a00429000c910038010741e8948c0c1040842003480d10580e9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952976447 1250 952975197 952975201
    0x204050a0204151d010c081209030415050c0a141006091a030f15060d140a020907030e03040b0307020102120106030c02010c0e0d02130e01020a110c030c0307090b0d06090506 76
    0x4001002c03c0e0704074610304140c50300d444034003481e9150250150710107040100202c0359008016000c010f482c0c0c8081d14005803600791920181c000c0d643d0708584207980340b4036080020f28126074001c07000c56142011034405048240002d480c3e620026100d0180b20020f84034010071000340310001c0c0700701d00c0500710300240441c0d1003286120007121104800071b1207100b074020f208a10b1002d0790004240d4481c400c91982400555a40c4001454580e001280a0550180c411011070030000100782c1c120f01901c02c861701c4445450700c0f20b003281103e291200008403503004000a2003040c111001450b40284544005442e0030361902802d034980c0c0c1c080c0c0c485c8000c42e4070703090201c00054080c0507803100c5801c103103000105482880700180e00654040406030003540315030a00c081035860307500001d24a48800c002503540d046a444014590b00510114003280d01071100076410318540031030000d0301500e00500a022032400c05034054000c000090913960311190b46016a800502180510406580600b02806a40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952977697 1250 952976447 952976459
    0xb190321020f0709050907050a0e041401021602040213030204110a080f10170f060c040311061932073309060b120703020a120c060f05070204050a0204 66
    0x108115403480c0070354205244035052014002503050840700d601c8001305842c0c4648448a040040a4000c030f5003140006c00003140161400030700ca80254401c107103040400241c004254201e000d40d11201620700c1110ba40381c0054502a000340c445d16002c240810361031603482c0d000904a51503031a90b8801c0f59000f040a00d101a00503d9860b07100c0900c90044105c3d203800c503841099201c0600a840096140030410801041c0810000c0b00c60b44510045401c81c0c1000200c024030ba402520086514000d045415480c0e801c1000c2544c01d5800001d0713100800320185403080d6000030780a25036034645900d910212103080e101c000c98041034040d0140c01940c03404541407408500c035059003e01404580c1c09084038411a035954403d10403001a400050304288610380040030384000941a0f900c0018900600703002d1801180e008101c91089480242045c0d440c205d42c0142400604081c09806820004200303a5000f41046060080140307441c07482c101090707001504680c4150746c11011340b54041f50078400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952978947 1250 952977697 952977743
    0x1b01020a110f01180209070302070c0609080c010504050f1c060513110d230c0618010329060a0908010e06100602030f0720120102130902030f07030b1903 67
    0x10211015009104013000c41580c05903490090b00c00038024602d0303000140c006842981591401c03948041d003600d200741c0e5008001c00e450228054040240950041d4aa09601440c101d508861001d0840c04080a0f44c00400289040044000b1802001211306a00040ba60706c5850311810070514855040b8005080613000d0907030340c08030b07103014681101012020030312140c40c5600c01502c1030300074020b00b03030802861814180c1a0300c509802880204806801a0401682680c0c0140a0340c2c204840c02e217043c01c5000b10402c01000d0f05000d054040b41e010281020b200030300c480729660421141e43d07070b41c035040c1c1800c50b4064100d4088980194048c00359910f56000030000402143c4010740c10012070b9a09500c0612400300b004201e801042e114420540300d00003004c4484070001c04404028010041d214082c0d444032415010388a403140000c01d0400152003aa4094980c40200c1c40c41542c131010240d0007030142d000d40c15409100814484a00402c41041c100958400c000101000032100b5200380303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952980197 1250 952978947 952978963
    0x70f03081e042f040608060f0a0507140c0118030c060c2f0f06010b0301030b060319020603040303090b010f1805161803050105070f02060714030105061b01020a11 71
    0x4110044a024400030806110001651101c00c04480f0645101c4070540725007a101800c025800c103007482c10009181402140452082048450340c0c62a035503204c1c403030b0f012030b0003ca17030500124000200c07810100000c00007800040c1958800016103e01407a80381ea0314011501088000504807110f40003002070754055500c0c0d204150401040f0880305100b40d800c0008032401e0000d4003800e500144e0308003001040b59542c4401420103680203561a81c041c0f52140e402408107480600c0158040b0307409050000b0b6005521080190703801c542e08165081040d81e80c0080c00a400309070303c030040100482c40c1108a60f000f06440b540c20780f5500c1c5408a0114940005c14094540500d080c040006581c5402402203500c6c0103848c210070000e9188100f0f07804600d03140c1020709958680000c1015550300702014882d614416003c440d00b0340e0380c40c44107e6030380000c01080740c0c9450003800100a6800c0420141c5020482d803114000722108000110f42244c11004041e0005014440e08019102007400154 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952981447 1250 952980197 952980241
    0x150f0c050616032d1a1509180105010512180d0f030e010b0a090504030c05030304030504050a170a0311032503181d04210f020606030a170a05070f0308 66
    0x2c60744580703282c41002c4007100100c2d074042d20b51900d034043c0001700484079102404c5401010410071610b040740024654000016803409030b00942062507a01c1440c0c00b50074101c9505030348103807410285050328a407510000d0202c07060404c0600d010007409105201d688064110b40d500e2170098100110300400b55190a4400c080503403504001b1807241c0c5030318480c801a1000c030312012803903071111304e01142c450040b003e000d80b41c2d00012003031104165201c002001158070440c2c5007803070b09495400c42c3c0d0203404021400d240c0d5900c000010400070307020b40d0400324456585429130b4106048001100c440052041c2a801c0000b80c44c04200b08050f00304403030203032950424800400c1541041080300d181140d0345e0401b00d4030090500090100701c040946449010144c00903c09000c68001c0040c0101c0944500c91002d4001c101c0080c03190b003000650705440c1c0d9000758541c24045c9a0480a503000c1c0d010203054020040d003040987e001c241101c12418010348255202134251818000e030b5a03032112441c1d908 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952982697 1250 952981447 952981481
    0x60a021204080702010e0604060305060906010504062c100201090c0e010315020f0d090b040302010605042708040906080706090801110d022101080f010e07150f0c05061603 75
    0x11080890240d81544540e00c01c607001d81d41e40705800144c41200241129940c0410001408200240d1581201e400b5000030b84039070180d40c442c44c0040d20580218010350300000d01402600919500c402c429040700514070410304040d40300940401c1c2c0c80c8036442004c0c80580c0d100d046041c100007091128500502c1000c1c09003500c2d5040da03071280c0c0d800c030f0320b4101450303442c0e00440c03484088c0368108100d0702d0324103000f6802c20686c03071146004a40c40c5c5040302c081e0055440c02c900081e050409008245c0d9100000344059140c103044440d601c1106070923002a20303410006e00020030300507864403c241c0038080d814014119286020402400c1e24003580110006904065004c85507900d00000c0c1c030f4101204150150300c0b01040c40d1218019004040e40c0485c00b01d00342c00000d0020000305155040344000c070000c0c0008082904444d0751522944201080281f24155684000d40300303c0052110420500d001001d140b52174880f54580751069481c3c086459a024101d001250103201d0755454040c81260 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952983947 1250 952982697 952982707
    0xe090901090c03030f0210020a120c14030c0a090e0a05040b09030a0206190207021302041a0c0a030f1101020d0621030e0105030a020403050114040c0b03010803180402210702060a02 79
    0x2402d00300040503c0010f040c802e44416a0202d280207120780a00007074000811500c83c101c6040080080303010950401c21203240c11b03821030005100702d6144080b008501c0b1250310315198419040b0362540300c498103104002c0c1210001c2125103180c101c0f98010050550081201c0c00d00d41880c5000f9000500840c41a6208101c54003025402155550340034030b480185660385d00c00100c0c1c0401070300c10030308000d41c842d003860743c3d03200054074a40c0903105480305440303c80280d000c03001180d052842800840c81c02c3d41d01202c4030f030780024858604040e41581a140040000050030080d500faa04901084c84583e616028240000748520b4241e054140c8241c204d01c140c9501514084c0c03032040c00c00c100764104400000020308281c01601128001c50307014008000080600c01f100ca000c0f01d0640d801c45031801c0004001409000c40001c1c8c9040c2d4006002035031600d00103103030f07410301d1100340c002c141c3d0000d03001d003e04401605001c9014082040540b0b851070280380c030440082c100000280307032654007441400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952985197 1250 952983947 952983953
    0x41103070305060403180b13080d02010e1011091201020a030f1107120e1008190908030a0b15030a0c030c0914060702281a041208160203010c0e09090109 67
    0x2101c9400076013504080001c44181c0b191003201406c0307504038000c0e01c400024401210601d61640d031045800d80c905589010f41004001c03400d840f80d505860023245d00000110040c0c1417590711868003200707502d038041d1400d440d10001c40c180d0b000700a0981e501d42d40c08603503031840d15014020544543c5442404100c4c1070311070b504c0780d01180500c40b00509407480e004600100e1038004d01a01c0d80d00da400410540210140280040421608450750002402c92042204610101c1c0c000ca03851580e2024100c2c0c195580c080b0f000c00100400d01025500c00441074020148242450065010b1080d229010034260328003100581501c14801001e41000030b028410046400e145040c0320350003078111020341d03444070f0a000040e4201030948000c0003180d0704a090010040442c0711001c100e03586006000c00c02840517140e0a1180100c5c41104500034440c286407002032644001082c1c05042d642807800340c1142c0383c011030708503562428000042104440000c41c0c6103854035040350701580450090100a100399 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952986447 1250 952985197 952985203
    0x807060b0a0e041e0b0901150b090109061d04060303054512061810090803220b0108030a090b0c0c0d0f1e20090c0f041d041103070305 59
    0x40016103854806107014140115184c56141155003241005100d820081034990081c0082c001d01d00c0300c502d5912001810a50300030079500c0c2520140c65421a680c90141c040d1061403400441181040c00c0100d042e1311556944180d030013540c00380c2c0d14652191512603031800c014030304896054142c4405100c200c0b00c02c0b402a0104c9a0b00d04940b00c070320500358000b0109051104040d00d4001c5030156004200041c0140d0040e020010038200880c0c3c0007100451051089908546003e04134100c20000295002c81014217112540c02c014a12030340d40c80f09840308410f00c8001c0c4c1201c0040d40000a012514560048060020f4007490030014030b4010f8100c43d403980d9600a0705a6405511140351150911015030441c1d00140d4003c03a08a20000c401c802d0307050491107500b0111504000700b210340101070309264940385000806400100541c690000c070540c1900000c4160485400c1000082803030304110758a5403c0241c0d28130000001d09051810150054801c21020700a87c807480702040030071400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952987697 1250 952986447 952986451
    0x160b03010801151a03180303070f172401230d0b0621060a08031207030b1009090b011b12021009020319020a09020a02070302120d1413030f03170a05060d0201081009090807060b0a0e 79
    0x4034805007014cc2c0c0040162072080280e4a00190b0021aa8090120b8800d14000b03050a411103003040182d5189070003000700e14000e44101c50110100c5400802992910b04161904440b00401801903030f41c1d13030024103107540e104c1d041c4014201c001d041400500c603054098440710074011140c083c0d41c0f03a08410000c0c481280c501c50b54038016116a10540f00b64000e0401800542030070594840a000c6070400b144a0851503140200500c24416406d011a00a12450211982c024040d1000c00d154040c9208404c44409050340c1c401005030340085c258109100500c40820f094000e04080c2d85980104955a1040b0301e15491030b401510346840700692000f443d10040401d8100c0c0c41d00c1c0d1900a2600e02d840815410040559441c080f400d024503400001014281f200508942c20a540b0000c0d100c00356002070300d81a8100b003c803090100150f000d042011340c0300810840119001d0380e40c7d422401900c44042c015900078900080350405c0c04042d008948803c0c0c410350b0b40f242c0d03003072038911404008140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952988947 1250 952987697 952987741
    0xf080106050717091c11041e0504030e0306070f0206520302070212010c051b0c1809060a0c0507110102160b03010801151a03180303070f17 61
    0x540303241c83c50094100042e11203028024040b8908005060081008101c40401c2510100c0480390740c20494a8a40585600d540355507440da407003001040d039000080e00000c0d00c02c800f0304c4014004c620b42ca0b1020000503108600680d030b0007100b22100c800203400c00d0310203480161520051850080207000442c80388445035010701c0c2d5585242c080c1000300040d040e0000214401a11244691404036415009028218021984014286400113005088031001c0b12000081041400a24070300303a11803600078442001c2c40c080d034040c034186000140c002c18040150860b0084200e0a000721481d040150344d5100011400c1005819171854000e8545e0040480003006002c68003110101a40309000b2240107034145404aa20176845010021a58000b40a00f20803503203003111074466070900481c601c04840400b4103621202d00102c1020640f5440105152140308100c9008a1401010170085100e4142551641890311318500c000300380251100d02c40c002e42d407814090280c4004813180b481c111503c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952990197 1250 952988947 952988963
    0x31e0a090e06063a020405040506060c060c030a0902090108010f1107050c06031306021c0c020a0b06280b09031009030e0915030f0f0607092d03020d0f02010f0801060507 74
    0x2003100080e0010f4a00003000c140d502003c140d24503921a4020304187da400f203e050215070385917000c1c0311207401090311840407039000b640401c1441c220344004507041004841c002c1800c022a0f00460008802070f48140e03600da6482d046045154000c0c813602072100d0b1a03220280c9040d619031100351703503050403820075131040c0800000f103040c0040c034140103510682e02c514159110f0340c4401c5002d40010803880004500b9040002d222849403001c00c0c0c1e0105140d206864188503210740c014013075100072294000c4450800042851070310066508100020015004901e5850440000341810b186000d204c1310741c05402d0100103000290002b001d540e144070190f908810075620807815012015031072150316014043c0302d602d40000e4401203100002d0f01d809608441d0140c480c100100d842e00d03164840c07204800c594003859441400321007000c2c1800114001d00000f980e031070b0b0300081c49a06d48030104880704a0388045180465801031409112440142440100e642c0341810280080c4039007403008000340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952991447 1250 952990197 952990237
    0x3030a0509031507020115170706111002030f011802070f02090a150602070603060e01061b0f022e020601030213020903121219020a02070611031e0a090e0606 69
    0x600c0801c070400c01403008000d480f803141000e03003010380203100000013900b00040c8a04045680c0c40c0311511113481c041d07410000c01c0400e02c2c0c011f04403511012565808024011141203da00e6045400a0343c090494414a407045503d0001c501503154408100d06c0100350040c00400003003039100c01e14690343d54042d1001d203201d80c3d900011038000c2410700d40d110348c00038884030003003505c60b40015000161401c45e1010040d85454041c041610042445068001a00e0316081d40c064260700340d0041c403091280407091662200c1d036001925101c03041421019400c0d03014403010710003204000300000d4140c640050545541586c01140074900c50700d180d4803c1c141c000a01e151503440411071000201e41d20345019884035881385c449105200203451008110b03020703a007800112401031088071102d16030341d001040003501c0c2940c20b07242104841c02c2c2046901043c4022400500102000c19400f40f030140b80340d40e034000ca0030000c2c04c4181250031611058100008101d05a110001102d8904100c0c0070042010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952992697 1250 952991447 952991449
    0x20c1c0201020d0c03051c0516081b0a1403090d030f0e0a0b09070302040e01020a0206100b09010f11030d0f05090d2708030c060406050f070819060f0605030108010506010504030203030a0509 83
    0x30380b0800005440c141c540d507004c52111202e56120318044c40227403820440d40d030b00e503c4003110550010303030703100d45005401c0a007650706407501c0c80141820320660808802c00a490b2050340400c5e001200c140d021174000589500c3d5140d0b040c0708004104000c02002c1228500c502041030b9200d260900050020151002280c1c401c2c030200240402154010410720001000d000c4c02c9002c2d403c0103988030054841c0c0e0000c05c0586100c05441d0080e83c21f80401c0303074240301400f801161813540d040504e00520044c50009040e025080c0014200001c0e080d501060a10520280d03108484c4024661405500f150041000443e0b10542c00d0940440b180b10415103a99082d0300c00341c824007142c0c4600f60742e01c000240b41f00d00780e4000c5242c51107140103180c100865941c050300c031040054100d038501c0000e0708500c0001d00000d6401c01442c04280740c5880050f00070348501e11090203006d16040007012500100c010441c054090055642c011020700e0420306203841d580c046903480c010300d5a86003c0c0080840e6007080d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952993947 1250 952992697 952992707
    0xe060a0c0302130f0f080105060102030a030207060906051e07030b21070f0617010f030f0210021f0e060115050f0d180c080d020f0304050d170703020c1c0201020d0c03 73
    0x1014440c1e0700079042c103540c0d10402072500c18511400c511031140712400906d511040c850f1038440e11068024600d0b10a01d46c600324025070101c1c1c412180542c0e20021007001c10b8207403044a12a2480c41502000000c00711240703a024007005041004040c180301e104140398845142c28440c3e00e0840c4a00d40c3c00964029401d8280300c5541c21441c1548400070001a0316603015901540d50030180c5414402641c0351892400080c85500020f44540e5001c10b1000040c104011004000c0c14035105031013041000c00103801aa49006012022064882c2014410108180480c0740102801d480b103165000003a14054981d000b0301601c902144d5010075000a0440786410080c5109210303e00e212010049240c611021a403600078591b040c883d082190041e6400018900380d5040e078840214281383c6490f042042c80710481000320349592a171568088040c1020001d40415807107600644284030f800c03010f100d080c3d01e445004500c200450800900580d0300030450541482252600188100b05801c090311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952995197 1250 952993947 952993957
    0x2d0c01141b100c0f050711010c0602120c0310170a0f1b15030b030312150f040f0c0e090c0a200d1d040e03030c07050118030c03080a0e060a0c0302 64
    0x800d50240c40d041d075040c09090f42c405010400591204103000180308002c80b142e001c0c954006100110314107405240350300910b00c03400c003c0d10506002d450311190307104400c1d0041c801e4841d41d4101c0742c04018040e0119140c4034902c003900c55511100c02a854051409503642100103000d0403c1103407070040c00a01082d041c004501d9844141c96015540d81e43c805030600440005500000900e4000110f07894640882111290508203441d50920b46a00000c001003d000d2400c05500400c070fa9207009254585001c0d6841041c0841e00c00100f1400e100e02c00f80805500003440e905c00c0c0c0b17445082160030002c0c8411750b802c080091070164090340203042d007a41424001d10b04104c003031081e414500da010340c0c8403200304d03041062122002082d00b844800c0c0000e982c200d0760503050301c0d0810300006140641c0c2070068040d06000e00008038075146a40351101c00e0303e02c0104142c0001759800d400809040d00440240e401500f65031041040343e0b000882c03123455007030142c8040707030180d280c46507240f05602c43d1701554 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952996447 1250 952995197 952995247
    0x708090307060203030604050a140a0b0a0909060204030b070c120c06090804080f070503030c0705091308030906010905091203040f0f0b0106030f0605060c03070b07112d0c0114 77
    0x110303240d466102c00b03590b0307400444010744102d0a0034001442c81156008a4449843c0e110300b0100b0340c0c85281e940c0015005840084c2d4004400d600f000410000c4e80c0502510503002d0721006076114114140304e00350f070380000d22440034030614640802c0052180d00000c036001c029898840340c0110b0a00d8404003030418580081c0401c3c2010801154030f10001c101801e00d41d0304001182d145070740e6801415201e0042c1070820320301d038104641c100041c3c10450350b403030743c840309104000c45900035641d40c2c01c407103410544200785150b01c18001805681d48600c500d541202609000b0a100000c0d02251006844014801859100851040c00c104181d1052003e8256440000c6060350340c1c40ea24002c00401c48020b00000890804500289504150084800028844002e5890034143e9202e101101e20080c1501c0200440b4106e541c0b41140c007881811000601200b907102c5035aa07042c8d200e404010080780c0c1d010a504926000f1410741e8100d003000c0360401d5a42c01d49a1110b091100b034141d030781d80307061800e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952997697 1250 952996447 952996453
    0x3140f070204021b01150605030610030f0507030212150904200414090c090103050d08091207050706200a0308060d0804090c08010b030705030105041a190302310207080903 75
    0x11219280c2014504d031200b2202002040081c2594401c0c007502c2d00300d80b0031200841c401300081000d034245028010409001e0f4280460016150020302c012580111255800643d000c100d050000500c920550303040015901c1e0000703806040701c0040c00000010300010485030a000c071104810418000900f140400200100f00c0502884004001c018003251112901d000750a150301151030441c007094180c9800500400030010000700a54240d90058103140c102e1040e401400c03c140081001800076074030890207400d4881c50400d001d840f101031400c164150240c038005070b01d00e600380015000700b207503014580706070281c03201c4010400000c05c941002c0d00d004000100440d40c13003d0ba03080040c00c6100e559400c00b650b0f0b40c800080a0038001030300c02500081c410401044180b515801032510a401c4003400c2800c0980741c6d000a420301041d20000100e4038201b1010025850b01c601c2011441c07201141e94180032008900030710110405000c82d00e80c0e0b40c1d0200310702050040309030640323a10400c09411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952998947 1250 952997697 952997707
    0x11070c03110d11090402010c02030706050c0c0d050a02010e1c11090601050c06040b1509090c0910050604060c0602130303090305011118060a0c1b03021206010303140f07020402 77
    0x188440101404203641c0441d89a45031115400d000c00040b452640154a0320218894070f000c1210044003d00140e0410603040c0751040580e4050103120000c0a59449040d5a4000d04a03e642001085a0940d114800c48a96540411000b01e42608443c4d4240f0788244607514071000a261184e54162603080704500c0b268140400200c0003080c3e20038001103c09204660391600112624441c81018071055042000813038009008107840325005584805036000343c110003404601c154104840d0021145c0c0039040f41d501c00e04204040b190441c001c0070700d0960302402d20010607424441d5225100c02c006485015034144000d95040d1210102030001c5084510707600d003401000f10710f007800295015460000788900341c031200d904403151407061600300c0c60130880180c200102c035088485000140114040384100103481240a0b0898100b416a4140201d046005002e800111144160200c0e0b025000500c0480e03000100350074215241031240b5901c1e1402d0180a000d170085610003508a8000300b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953000197 1250 952998947 952998953
    0xb03070c020f03010204272007021c020325180c0f0c050d140d1b090b070506010e0907030f0c2c04020f0111060c04050109060503010b0307121107 64
    0x81800c06090084440440c441c040008040c201d00c10b5104840031a146090340305411006a529800544001c11000995282c50002a00040e500c858403000b581c0700000c4500461a04500300e0080c00075200005110074410360121f60380e94800300d1000010407218108d50ae0300750402c3d40a070042c0c01040c80000350604100400c0e0081d01240000301c5c041140181403484540c07040c601080d890350801c00030700412038504da003078441c1080e03c0400c00c5200340c2000158000105805a0315216100c1c0d460300c000c0e90740c1142c0c01000410203421807900b5207001c01595000c1600041c64506503a090710042d4842e444007818245003000c1544001c040442c04846503050142ca40d01090859482c8180c000108010400104503481030340c5210603c480300801080c05801c1004d046070710300c00103050200d004e0814440b8149448011680c800c0364030310004003071109507480742060008001d5410218219410564080414000201000104240d00486944422054105410030f1b010180f015a440416003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953001447 1250 953000197 953000207
    0xd1b0c080a030311130e040602070b0f01150c030c23120a180308072006040b09271306110f0c15060319020f060309060907080703080910090b0307 64
    0x220035000b03c1d2401d4002c1094042240c1190500e061062a82c0c14460400c440c8010844000c1c1094a10580c244180070000f48a46505400707065441058000d5615000101102c098001241800c000b89000c90710000390700103180c184450750210740e001828400481d1518000e005100c400c00510a641d110220323050240002e08444616540392040c0002800c01c000f001e508070310006020394001c10012020030381200c17480140141c00102854503003204000500aa002600100744080300007845c0112490510403008941040d40c8200800040718020889030250041000a581007008414410031143d0b03800b47c09145100d64280f034440c80905c100200a4103c0c50a031034081c41407140480902004070100c921031400280141401e01c0303d010840340c0c2c84581c1d03000301d1700000803100c1016544e03901000340d40300340b18044c018680c510380404024905581540035aa02d60415a010300100c6c25880850307205120940380204c0162544004a03000f0010b9444904c5414000c000d01004640c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953002697 1250 953001447 953001463
    0xa0209030a2105090a0612060506130e0105090402061605030702030a030c0b0916050103150b0a030c1b0c0302040908090405040c18060e01150c05010f020318010e0d1b0c08 75
    0x10080c0005918921030055a9034411391503c1c84c2d2246130000708100d858801c3c031048110009075071002c54645c2c1e90b400030450680140304426004c00e01e401050004002c840c90300e500602045502200364180380e004240944540000c0002c82007000b41c4000030701c40200101c5d0b1a450780035086500d400c4550400034803175100c40034100c404e6041d00c000f1a002000015044503550a0300c003c1c90041481c00c40158001d0020705020f0a6000e4556400603034184c0b04000f40c403508842e030f240450980c0300520010810200317403810799480d103188c80b41800814024401581030726416540054140100e0601c0412400340c481030541c4207041c00100400c100801410404681424190384280e51103070401c0d00079202c4600074041054586001084101c80c0c1c1c0d04106d51b84c0e05c00d8108501c0f210160340f81c460030748940103000c1d80c8503500007042c0668102c0c5014200da04100c03400003002894003d04040342c4030030701103900c00104521540c000c2005200d4680b0840100d90007802e240055941ea10629250009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953003947 1250 953002697 953002733
    0x503221a1e060105090f0f18010e07020c060c100513060903110d050c210c06150a090209031f0e030c010f0b0109080607030e070e041406220206030a0209030a 69
    0x41002041c2d842d40104291107100b48000d00c1c2085507807444050040001c8804d00701540506151801116401c154074158041e0458001c0620030785004540039103030521400804d40078000410900c0c00031403003c9034842042646a20228035500d0b001503c0120f003002c440e02901640c5014a003104254010040354200112803060360f81d140700d1100e06039000d000300340d2803202540103540105404a2108070800311900791300c01c1c1c5070a203c10744402d145000803c440000030300c001d95030b000e041441d00303030030300402010040d07130035450040c009011030b4440d0502038480902d8030b0940210f0640c000280c0000942e506c13110200ca40300c00130b080089000e07000c41800512001c0c54006a07212079403040181000751018680201201d450f0740404500070000307004242114040d840000ca50b041261504500807401429520040c0a10120050500700040c03c8940b07103461000110303500303c242001418120b5011560f1580342d03034641c0582d0001e4803480e5040c5525020b40c2003803e04003d010140c29001d901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953005197 1250 953003947 953004001
    0x21f0c0206070305090a080c250806090a1104050604091707021905180705132403050115032409060f062c0f09010303120c0503221a 58
    0x142e0329025821507100f500d015010340c111141500206901400030229150080211410784644042002c82c04d03151480d4031000d15109101080094001c00036203800c0051400640304001480d030320341036080c0c5092241da005907210000124159655800804c240b80c1008000421861410a40709540c3c007001e0101c1c0b240b8031412107a2400400221001c0a50310050010502440c00c01c030100c81c10080108103c0c1008401c002e000c07107041c1c9005e51000100350401c1212a0041460314106101801004000400d0b01d08ad00400c00705000704000c2c0d41480d0303581000102d580008000003403600c1c07107a40d1042c42d4442600f00040c485401d902603021030b10401c0503813440f652a4170003190315083d0b00e41818582d19411080304500f5560305c07150361003400c00420452025100c0004070700350040c00d80c0140d01142c5400c50040c451402c42c052040350380d4041c5046461843c203203980850140070b48041180c8900300c2140402080256405407614510b842114081c030b150041800080b0600d440c040c4407494 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953006447 1250 953005197 953005201
    0x10c021c121505040f06081b060f0a0e0906040203060a03030f03020f040e04020307080d0507060203060406030501090303090210090812030c040b040305010219091d0c1608072006030c0307021f0c0206 87
    0x14a52090700c01f40c0340101c01425101c11008680810240f800c9641075100b60100600101442c0c41402011814155281c40c030700c6403032070810401c19020041c00702d0300880c0100100301a642e00c0109401c2a01c0e407504040d100c600b40c591040b0020300500d03907020181c00e00083d0124107040f515410030b208900c204d080307030f0000341c0340c0403c07603281c454902d540008100d00340400c00c00a03a9540146a000d0340c040d000082d19071303580e00d4403820340b03174000340907004203541d00114015401c0000111038100f10394240712800c03900d007190342ca5407161540030a01410700c0120203d0704040d0341204850081181151a645030794980c10428000e510a940e0007103103000809845040d24040c0c40c0710f004895420201c1c58182c500c00c8121840c002c801400764004201c10803520682d02c0703c4030b00c070380e0015008060554442c5010314103e03041751100c400700500c0440900c600c00040c0e58100403241c1c0300594412503501c07074940e41c005920b08810718910340e864008030f0501e809060450340c06020030003402d500301c070229 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953007697 1250 953006447 953006471
    0x30c022d100c0f11150112060e070f0905040c09060b040f060905060d020a091a0c1002090607030f0201060812180a051f050f1911010c021c12150504 65
    0x8810440c2d01001081e400c0c00c444900e1401400c400c1c00541514050314284036040c0c145024100302608000c144141038000356041c0708440c031480b00820300d0301000b064070505000c451940ba40d03240c412883c0640c1c4600001d4104003a20b51107000600c0d510900740f0015031110700400b819040303400f422040f81602100000c07803a01c00d030f00760340458038083c0000c0c0c0f801403001d05540c0654010000b107028030002010005841078511012271150108604042d162031028120700d041646041c2c956103810b0050003072330715a55488048502707035035050411110000c030b1664144d0140c60f00e5070204035580a0b940c0d0004100e0507000051007882101044003902400394001c020003003006025407504800a106010ba43d80c4003c55401021501d40c1402c030304005c56111010b410344d1102c45075405140c10194405c0c00e40c2d80010601c1c3c00301c8016402800b90700855840203589150006c54043ca043c640301030310007103a010750b450038580000d450003400070240c51210b180010741c0070321841e4005c0e407400540c0064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953008947 1250 953007697 953007701
    0x5090102091801060807110f0f0d0f17070503280906050f04050606040509100e01090c050d0b0a020a09120303090201090503070e040b060f0604082103011203030c022d10 74
    0x1030b130760980c840c081c1585400341d00b124144007140700504144101e41c000d42c00c0050421280700b03d01c03541d20040c80014810b40004090b00c50021504c010321240b03090800045c02c04000c095444907842c03070059100c1c0c1da2003100c258046e00c000a68401e03441e41801c1040400d03002d8020400c001e020b04024400b17900d40c000381044007207044501800c143c2000d0f01181031480d064005542080041d4219406c41030000c41c00e0080b01c00080e40c0491507035503603a40c1030030400c6950801009200441e10b61200340c095884116410030014100d0340f000358000340c489e082c54040c040301d0002d8070103040f02c200801c0b058a0054000c004101043e4007040480c1c1c8001030a150001d51075003600d4000b5001c4156071115a52100c0b8002e025050708c1e880b00c010406510715072586c0d806000100100c070028810921800008004055440c441c000e941d1020030041c00184018030240311403981c5032500080300b1803600c1d0101d04019803164002c000c0e01e030116000c04c1d0700948900303404101c01100705403900019408a1081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953010197 1250 953008947 953008949
    0x4170703020a061d1c030c0206211b19140d05150312030112030518031f05010b1305090717130c1212110c030106090e0606030d0e2205090102091801 65
    0x543c000d00005d0a0000380c403030680b88400f5480540524104075011510041c4802d6031a0000747c3c1d0b440b084100301c20000d58010250180760302101303051a10302000246140b10140581000502444844c40503082d8207100440e0021044a0b40421803400d1208500c80c0c82c030b246a4426101b8030801d00c0703501c4140780740d00460b8101e408403001e20700c405d1a245d400b9905504000b80300c502ca41000107560000c2d4170705100c20940d000e0f2a10030710b1501300c010038009003115410f070405030500c40d0900ca445030f141660b10f001c20543c7c00c100e50342ca64035550310707104459650001c111400c84810190611240500f0f551402440d28411220040090f44a100c0d0302c410003120417015055810885800996900030840d001c030011204040d84e0500b08800046400d4070016448000c010703568420f0032105c200140300760390f0484030881c0a82111140f041c2c000381102c280001141c450308070b1101110007011171101c1c0c8102c41e6503101c82401649004100780b8003e40011881e036018101148042d0070011142c54202c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953011447 1250 953010197 953010229
    0x815010503030301120c030606030821010806041518060f18080403060b011202072009040b0a050a09170d050c070f0605040f0204050f060a05031204170703020a061d 72
    0xb5007160b28003800390301070403988030050b50340d10111017000c80408c031035010b004055401420030756071399030b2884001540e800d0f212000c00701c407400180060001d090081151500700d41c02c450304c00d952111100c1200010100d910030382c0001003410390b800c1c00f00030300e5403c0816032021240c0100f081c80000500e05030284120301c03000f80f07112001c0005200060550740000707500401858a40030390b41c105001c00040f0f03449503006903100e500c81070350490111030040ca2182d80070000c0e52110100d041680c2c0307150340c008001c0c2c80107400c01d4840002400c486c56541c001c030781d42900a0348801041e00454a2244603034003910700c4d81070a604140c00100c0031200481105d21859002141555420041e1901030041001801c1220803400448050b805a40c65006260042c09103001c03050460601c10100300d041c5126502440c082d402000040020040d00f1054408440d4004000c481c00e00040c00f1007414a400d50300000d40c864400c1b000403c4060307004a081380da40b00d0151303607140680d10410422950001c44500c01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953012697 1250 953011447 953011453
    0x70915061e02150f04170f09011d0a0b070510180807050a060f05070215092503080705031309181e15240e01050d0c03060c0305010815010503 62
    0x19040714040004207100c00a0244142e445000d01600641c0c2024002c0c0c43c1c40c00751000700001c0c84240401d001c0d1260007450a0b0303107218074114600310901d0700c6002d40340c0280d0620400888007800b0310240c3d40041c3c1c0b401d10007000190310300d4a440040950b0780080c0c1d82070312180700d103508802082080b4420340114201440c80c00001d2401980c824081e58800034013190300340030380908140001c07014010914140d02a0301d02103001d10704414000d250020b07003140720000304400400c0c40750101000c1041c82480491003000da082c1101480d0104160400340d01c01050201d0005004040c010040003400b9541c080544d40042e4a50700e5082c2002d40301c90740458a0805500d6400b0800100b1055012000316000303030f07c02440d82c40c142c80d241e2140c40c00c4502d01d582c490300c50700c60102e0700c03800007020540c484200340c19501840c20107074841040c1505009090040780c241c036000d018009a200110001c40d445013040c4404414144000c000d0f1000307102d2a00b45100b80c0544140d6264000382c0c46060355000380003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953013947 1250 953012697 953012717
    0x150503060c0f0f0c0d0c0317010501081305031c39030c03090c030302210f030f060616030e010e03060f0c0d060812090a0b0703022a0d030207091506 65
    0xaa0300345540041103e0700611070400104030046414448244000c41e55100c0711030b41e010505000d0000907000110030150118000140026a08500b20a0704105c4e0741500a49000c040e02d04581f0307600c20a104540c0e16940b00c1425501c500080e001002c84206030024856000d00c0d035854101240c04200700c90b9034101d910a50101160304c01d0f0b00034803c505842c9000300340124a42c40746941852244c0050300160441e060619005006804111443d10308082c0c861034442d480c81c000305180401341050160120744008100d5a5407818280c1d080741c0c0c011030b1040c071445502c2c41c2c003030081c1584c8085d081c0072440785140c007405c5140106503a80f16040e12031034143c8582d0707900c1100807184d0000400e4100240c0c0d4201c0450b42804c2086a41c14141c0c0c180262075031409010100701c42c0812640c400c001c90041000600f0000b40c0c0401e940e001e000741800404001c0652092a585c41070044100300d800c04005400001855400030b00c081c115000c4000401003040b102c0b904008052a5002e00e001044c2c4100c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953015197 1250 953013947 953013967
    0x60108030313031e18060903170a09030c080c09070e0d0209071202070605190b0d0b040f1505041104050603070b1c020c070618030308070c05070503060a150503060c 72
    0x1c4124400d103e071030200140c04c01c14409002c05441188024001848032222084113031241100d00e018044500745000d00741d00e5035590030070101e181021042590303c04103003143c0b1075005000707150180d40d0058001c100c554503054526950240010394a11401605e40070906260081c0601b80544038007800703c85010780b44c0e4090000c1c100c00a0482c0d4200049c0002c1c189084450384080c1c40824411030020400c1d04014070002c4003403440f810000340c501d2411200f00002d65503451017681843d4000910f04099840781052200d852118101a00d10f0031168001205c2200c0c5601c8903201f03520510000e8600f84090f400d03c4200c0304c6c01c40e045134040e03000394800e108480c2c1640c0a01607007003075200c145140e00703400d20500302607070040c00004c20581d005040901085401014040d2250720402803080c0b15895074600800c000e0b405001c010034440c04903420418002c0c01d001800c00f41501400721200c43c1484c4804000a1180c4030002c0c100400c04c00c40800c1074940440d00038040d06001059a0821185007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953016447 1250 953015197 953015221
    0xb01050906090d170a031401080607020d2319080f011505090415030302060402090112051c18080d110102040509010b09030a0f030903030305162708060c03180601080303 74
    0x10f9400e5400a4850f00440c1d0b6442e480c02c0240301a00c0c00c5c0e94003086882100302050400641a000320010303801900c200841154001294041a4039601d00a585802d003d40f5900f05503034a1015001c640740c0008901900b07000344030203640641510354488480e6580e0345030010700d100c401e016292009444100120390188a04050310b01c0d180b00a2001032302c41301400c0104034140f05984101c025030011800c100943c0340000c2014014030049130849460541da65400d80c031205117040034030501070b00124201c000d0703110783e00c15aa082034049404140c5d907210088075a48441d01103c1c10700003041221000c014007811300940301214000b42c030b80780069003484904400354204850054052003007160302d0020a1000400518050094440300002c1381141802800d40b0401498040080c2c03079440c0c16400c4030b91040310207400c0d006403146180d80e41d48403081031224214039400b28209214050901000328207280c003d6008101c02c0d41c000301c04800c900002500c52000740715110041d04144001100d014400b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953017697 1250 953016447 953016469
    0x30d0305090721060501060228080c0d030f050108010209090115050f0a05040501080709031a060406080708160e0609010e06040b0d0f11120a030309080f07080c010b0105090609 77
    0x1000950381c1403034032082d0b1031043c11254120310399800769154200c014400c0e90310a01c1d003d01101d1019000401c0540700204590740c040704c0c001c402000d00c0303074203005001d114429541880010800e8414030844400c000b405400240310b10f0f0100380c0b8120000525030814401c40340c402030003911101c2181c2c6040048460341d0840103154091080402844e0300c0617810034003d00030060b06803681a121802e0a0005010090041900c01449040c910901c0440c4502c00c098142c1d403810540d0f80117035610341c00800c0141401e9400b03419540b28a010116805501040741c4c0150014041d05003c5550344006005031003c09880d01904417203880014000075054a00080d07100d2006040410880c5840d00810300d02d041c45001500d80038039185240c0c007002015401014650f03c102c86151410060780079850305c80c296080f0040038559519403410070002c0761400c4d00ca900e000402001d480300e980781444400c0c0e50110454088035460006040741c2e66000d8000d5408100c8003034802420700350007000740000e20540f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953018947 1250 953017697 953017711
    0x6050904021902030304051b0604050f030f0d021b060a0e092503022104080f0c1c0203070308010b03131113110903010b0f1c030c08040e01150201050402030d0305 71
    0x1c01504000e401081d00782c440d511a02d500840c2d0700e140904005042c080803904070301c801d00046107080740c0d03907071680255020707036104984410b6000d4a00340001d1500170714801e000600d00030b076150b00201c2c680100c1d002000c2010201840e88a201c403c00304460ba100c0ca400d9440030402901d18100d050804620b5540d0264a204044040400a00800c441c810703540e40c4500000b9000075a483d03091149454001031444c1c28991240c07070f420a65902c00c018041c11090307443c203050128070746041071001c2141c0d0086841003813603d989101d003050002d407a90b00580c41a804200c82800006406010301308480c4501403207800000304140541e900103c00016142280d0300840c81d01c142d1404004a21071601d00f1481a401c09907900703110f200341829a400000070300c3c0304084002c580000c0703031034284840402e4141508004c46407411031605888000d00d04c1006059050081000700c2c68004050380c2505076810404a80d500c0b901c0e407c000c03801d80b0f004560007501078110360702d9084010700170f400030307504121 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953020197 1250 953018947 953018951
    0x1212060a0902030c0d0e1b09190212010503060c070302070302100c14071a0f03040b060a031a150904050a2003100b1203031e060a0e160201061e06050904 67
    0x541e03920020183c1c0c100395180c9510700c0d8009040d4190411342d100d0071550540d51380280c0320140081d42081c050400f142001405613040740c00117111041a40141404104246000c649408880c83c00c406070406c00d005150080c411032002c034540d07031444800d03034410a6042d07008000850940e800d00c0015049044107500344243d000d12840001e500c2c000b43c80c07403035224000802040e850301000c06492078000c0c8080d903240104029480c00021002c044039071003034204000c4280c17900c1d01c0020071419420755101030322811150404202c0840364540310360190340c44242400e6080b1a5404000300518203403001801c0764014846000010390103d10651310808003c0e0a031080f89003040400d0401115000589911740d03604400c41031860151040c0104640e150001e40c15441c02282c50345148c9580559034000791140f01c0054001c0d038961800c0e801404010000b031103941040138a201046a44ca0b40c1c500240d4200500804c20300840c100c024040407505400c400c0c074618061080c2e130305030301030880c8940241d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953021447 1250 953020197 953020199
    0x20f0d061e081f1503050a03020606010504060e01110f0609031c05060609120705150703021c0206011211060f0306130915020a11030a0903050d020c06182707111212060a 74
    0x11070884c1c002e9009600950117031280301c0b0340f450002e04000d0002d0916050200c2400140010743c1e218034038490090007801d2004003040004030b001e1030202d0010f60f1921a00c510070410a0000011001d45811100c0d40c5110020744c241c407280710180d880032279004e43c0113041400072000ea46400c0e03c00a00314420343c401d4a04050300c86010540304401d400d15031900e01d03c0054000d0415604120280c03503110703c48001c444409d841207000b52501e0040c4550000c07141d400003408140041ca080c0c0c9000c0344002131000355241062414409030b508121809840355444550803c401141e41c001e0300c91103507225200c4254900c0380b011080007904120100820003c03100a03540350010100028001101151203520400c1d10350300c0c0417071030082d6295259045401c41e81184903581c46220950780c1088a0300c0280c03000714840004a00720301030b280625150b602c0e1100701c05000284060a05028180581c0c0740d1510001c1028000e580d0040c0d002c0240e07144800304154150004901c00039500418000d010408003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953022697 1250 953021447 953021471
    0x1a0a020312041104110915040f050909070b030a1d01090209040611070609050102180d031202071106070311120a08011404090b0901020c0d080c1c020f0d061e081f 71
    0x803100c070a40050344100c0046c00841c01c0c54903440015820203445005407815085c0b13078413099807011620500e40909103400100f0b1007000d0038011303040a0701c8181001504e902e04148000090104500b4564403284000c1008514000601a4119040c1c0143c0300e081d00b501c2d5903942c040180803400a065580d05c09200035400201c00e03014100816000f82c00241e01c860f46d404a21308400300d82c03020386200e04800ca8010002a0f084400203a20242d61176005031180c40a04246403080c2c2c564843d15800343c0002009400c241d041700c04850292100c50444000100f45016054180f04d110072a10218a540004201c200024800140303481d0001c0e1000c15003206940e1001814802034800c540643d4001c280701d426040c1c10402000200807178584100303a4140300c510408140729110f8540510f004c0c1e904180358007441c40d0100d031317050304402c0002503403105000b50b030100500441c01200c00440000b0003c10350310101700a0081030714214030150000d215540a41909020408090190191509858005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953023947 1250 953022697 953022701
    0x111603020f0a060636110405090f04030210050c0409020d02160305040e06010e0d03030f0e16090e01020310051c17030411010f05090111030c0a0302071a0a020312041104 74
    0x85079104a5010131454244400a4801c5000c00d80400b40745a815030901a20703101958241000510380c900010001c3c46045091054410358205c90b41054030b81c024070444a402c0450148514001d40c2619200c807880c0695809444060b03072400484a800c0c8030600c516903096005044003071025900628101c02e502110500015001e01a0003003040410108481d000220005034818424070300a00c5500c0807130005006e911690a0140806030b640d0701e0b40000304175a0340a900c180e5a030b0012031700c0034100b0708124400d1050703602030398155a080c07141d14025150140252409401032a100c29602810101402460309038090958407042e1364a00010104200350302522586101680070703030340d0f80b42070300b070280d040540c0c0e00c1440d04203c00c0030303402d480c0580d0201c10f03202403207000d10700b85a941141d103d541340341d4090a40c02060a01410201d6010542c000a4000445d4046000d024170303081d071610352a6140c010b031044d24015800c1000900d84451708408081d51051040c0d400440b001290000720b01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953025197 1250 953023947 953023963
    0x15050418061d061008090a050a050d0f0201140a0908120411040b01021519092901060903080703140d1b0912051b210c01080109111603020f 61
    0x40c145940c0c11050100c00d0011402101502402c212a03103142020008030310340203000c0c10325104004106011074111007080c400740c60703560f8021080380e2464030349003425a19003143d040c0c0c0030040394446030140d08850040c010341d894001c030300171814000d554940d1064050b1400704003c49038518100020348043d04400d4a5902950042004c0606002124244001c4032400b0f94298195405000e203c1d8289140001c02903202c0807d98143c56546400e505030009447e542e81c1c01481c2a44034007900c601d00014040c094800c81030720310901c00590784e421040d1050b21090002911402080201c4000b180c050943c4041d00702a13103024502d00688061454120780383c0c0740b60107074042c62561440d1081c42c0c4c004a03c8021709003c20910a90070490381d120f43e907031080e03032049101041408503d105550744180d140d0b0054110a1801040c1c000f40c9101141c40d6652840a40d002c906a14004144141d00d40700c0d0105070176080c1412840d12a00100d101c25590300080d040f4118480c0d8001d803081c2305414400f0344 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953026447 1250 953025197 953025239
    0x30c050d050d050c093d0e030c1507030315180c080f10091a0402070c03061109011b050c1f030f021809100f1401020c09040b01150504 59
    0x380c0b180308001490060b0741e00a803d0003581441442114440d179144000b00b4a40841c0b483e00507141d00012041042d046070b400009040300030802c05003103800b504038403003070b002090481c29510409103034020440c108040d00250f8940740001d004a20000303009910440c1c0540c0709131060704507942c0d0340c4091a001c20b81c01903c04d040710b45034540c0034021a00f04100d9908228004118a558034002c2c0c443c040840452007100d4403540c4540001c599041250130322420302c1c2020340190368406990602c0d41020302d2920089500074580b1114500c980b034481305403130640205954141201014202c2440c0000c001c840039200350080091081403a0b940c82404038555880d183c134801243c1c4154400307800c5030030001c2d04d007049074010080b041000204051611445100f2904001c481e11003140c800d055214907084107004250010000c908d04041e0700d110b44024000b41d08682d90b9400d8030f070521101643c103503030040100364818010705c90f40182c480d101d2018401d510b00a8102543c1d040d1940c515142036102c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953027697 1250 953026447 953026457
    0x411130b0a030f060b1002120a0e06221a03150310090b090d02191209081002042621280e090403050d1104271b0c0807030c050d 56
    0xd00401c0264001c03c4d00344d6070229158503520b091520061741700e2300d04558420543c000042c0103410140038002d00501020054600c50716102d00c2003400c150000c3c45102c0f0350444110080c00101e821400c40d9500341001d860351000e0450710340d000000038801d080856280e06010b507200703d100d03424003441042e0f5000d000f00110010350420110f420f040c107158100040454020300010141244968604002c05030f104000e01883c2003861002c44840700c05401050345401100b00e003800e035800c0c0b900a0415202641c44038041c111012120f01d50303e00076500b500c0c00c0c641081c1100703c0f1840745500d0100551450507040c51910300f41d00f0183c08864404c059942401c1019000001341503440311000305139000664070030b800e505040c0c6000d4180c3c000c0b2042c01c060b1944802c07401141c40004803c0d280207180750172241d1021710283d1158052a40c2c40c000a22200b440c000a8180c10890040c400c03e200c021601c0c1d01c0c0f00541d1544815004d9803140c0c209905100318040183c0c0068010000744005011035030b28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953028947 1250 953027697 953027723
    0x10911120d0c080937050a211403030a09122607050f0f0c1519090807020402030f070e030723041b0906180e160908061f0506030411130b0a03 62
    0x1001c481e05c00d507046240a40440c500c01d0190030a134000f2230865181c01000406180f24a29002d4034501c0020b418400c01c0c000803060080c0340da02074115102d00c0e842962070f02d541d405660011500900e424030412030100c8503406140c4e0714504100f8803900701d1094134001d0702e440d19000240d0340e107134040d030044c0b00f00000004e0140320141040c003200b002000c0055130754200e401e149560b08140000c01148034003460f984d2050404006409080b5410246e010b001592030780390000400300e1003c0c00b02c440101085204000300b00d00c3ca80400e424041d40e411810007507104100b08006a0b01c041409007480d041651505100e202e03007034000458900300c030941d440040043c10010024000c0d0031900c0380e0300b03180d400c2010900000010f0307000c2aa01000302c0004503180044a8401c44910b403c0e603001141d0b90040000f440902d603401e59007040300800c12082411a0ba95680a0003071910003124084c29004040c40c890030f81e0300c1d0241180004c15251103020030440e51140c0010302c101032a900440da00310605c12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953030197 1250 953028947 953029039
    0x15070506091605060a020304090f0c030507020a020102030a05090f04090b0103031404030c0b2a06010521060f06060c07090f0f1e021308010911120d0c0809 68
    0x241680040703000d000d804801414880900c62800700c1c041c0030701c12100481e55030001c80c400c005490042240420603c0210552160b2400a1108030001030001c0d081c0070005d0040d41c0006001002141e040e4001e500e010940f10b811292508411280c1741d00004d81031a40055596602441d490140141d80c01e0003035506d1490041e003055940c0c20810307148407041c84104080743c2c00485110868035511030840c0e880300d0401c642d284401040301c8903048501b0400300c0c100c0c12500028035505941c0c050b01c4d6a8001120006d00c91908000c2d00100520fa502c55800168030000c590009500250040d15860810130840101401c0c0304c851f400031020266184403443c2c82444c54041c01c0c07986000340408002c640010042440c81d800b0744070b1441c2c20650002030701000d2400407408040140400300c020480c3d04418a450040d42c0110403409100b228625208801e142d004a001700c1c0314241d6481e10300452036613075201800d6400a4030800d51100012005000c0700c00301c3c1101030108180e03158000601e0a4040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953031447 1250 953030197 953030203
    0x210e0d050d02010b031606030906021c0606030606030e06130309150206090d0314041b080a110301050f0709031704170d032901110118081b010b011418150705 69
    0x29030713007070702c40d5100c0c078100c0c091411450060415545513140201d0004160b0070a20082d00c00c841c40c3c1528480413440516070740885034084400d41e012580c0c00d120465841c4000c4054036400c00c82c640d1980c00400c0410307403207880800030360640340c400c0c10444803503941c03401c980340d4006040d6600405030300404204101580103002c901d0011404d81004c00c00386c16420310140250300300038030051240c40c041f0203142124400b40580001820715404a50061009251070300700d9056100305a8001d40c00d0102054088a1640e90b0a100701c0c0107542d036520252071611031010b402a00c0364105c0308102c0400c404a6880700a59030039000071140001860b1307000300c0d21310050855541610002c040001c0215201e005001000100100380d002d03e002919080c00c8011140148503400e0781c80a40c0b0b2071942e08104101c40100580001c86002c02c981e000b001004107264241c2d4600c48140d800540034a4400c020142c210019042115103070f6151145403020101146003000035a041e450203c0020503c0000c000c410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953032697 1250 953031447 953031461
    0xe060d17130e0f07121d010b09011d04020d031103180310090803130501150e010f0f0b0307050309010902150405100318030e03150106080a0f09210e0d050d0201 70
    0x2101911030b43c5440036080f83c0c181c10241c046410058517411019100c142c2c1c2d00078034481141e003100e035a04040001d4809008281c0d0440b003602032120710300002000110100045060450151162655565582000403000c0148002c07402c0c0081240500c081000400c05043c05c00c50a1720749140d450014420549080c050f0640c1c070001505002d140c80000c1c05140649820081030740800c10100c516280c000d014001c2515180001c0c040e2400008021541401a50407201c640e04407141c141d0b2100a5910041c0f03090090b03c160071001c1011802141c4142e00840d4046615030001070010507036800a912680003080c41105400c011078240314038a0021a034000d00190340c2405c0199603a40c440d0b6240c59a0b440c80090148200540d10b0041074505005a001520440041c8451980c40d010040d04182d01a600c42c10000d1501140142900341071040034000c0780c000d15150311804402452207034542030110510b040015489041c0c03c192a0a100e800515101b140074002450074504000c2c03c440c40c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953033947 1250 953032697 953032709
    0x9020a1101051009050c0918010f060203180904021c05010506030d020c01080f0903130605132705100902070501090218011208130e0921090105040e060d1713 69
    0x9844140b10b0388660800f03415040350340a040210f0103696402c804240c50240808882d00803d0f800541250f6000411856059400f410704c0010400d03100c0c9012a9070740241c202d00401494613040404107840c0c803111540d402031006000003481600094543c0c8a0288400e0895a680d100c506002042c039052104011001152000f41074a483e00c00008022039000b07400b840700c0d64120808101150001d00848800d0030545135070b51421030b55010018130310380c010748107002002ca280c100410010307210000c0d1055240d028803045a0441c00f20581c0700200006083d025410142030000585041540003410a20b400340340001303002070480c01441855154001d100440010300c000600060806801100116401c02c01e81c60300c96100b0340b40303c044400b6941100e0341a0030750004000c1042c80000e00001000407055200948503d08100c100c000d004000703145000c5001400140700701181c10f0030043d0700000040c0248425a4140c40307141040c81c0030544000c5c090000280026411080e843d07031402448 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953035197 1250 953033947 953033951
    0x1c0f0c0f1407060b0d0b0702160506130513090b0106020a0309050a0e0f0403020309030a0b0105010f080910111614060c0406141b07181107050a11011809020a1101 71
    0x603038200d4000500c0b540e24002c002c01d940b0211800117444124003954003035400100d10445080c0103802030358845044a82400c60290340c02d002c641c0b81000c40596200401c0c0304400e0030504d09200402510b002d022012a00b01641c03500030070089031b80044801c3c02001d050b00070785461a070600700104043d010360232046c0030703c2000800300000b0130070b141101c0d80300b900030100750741d151242d20b8124258031841c08800d601d40318200d4420f0911031507081c0e9038100c8100b41c854106c000e40820b01030351100340c200d4004074585c1001c1c1000c80c1c0580940c10070300030503c10030242860950241111081c141c00c1040c01d50740d200005da07195280c18001c00c1440e800516080000342400c1c40c0510080c1542040701800004905c04580301291682c000d80e440c842c01c04000c1071b201c0c003d803901642c0344200404000d0242d191300345001d4040c18580c10701151943e54200b03015008507031560711510050315480450604008144400081601d40741c12600098841010050fa03603900c03100d03005044121720301038401a03074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953036447 1250 953035197 953035217
    0x6081b070c030204090c150e04051503060c090310021902010b0a03050705060f07050d03050a1506051e0f041d241002010b13050f09031e1c0f0c0f 64
    0x741454101d4007180d6040714081440f450514141d4110f00003540140da46c0e120b00b000c000301450b081110260a03a8060320204041d9030383d0345000c082d41c101900f40d181c1540026000c03841c0b08055000412100c036001d002c64070051404032125080b0b038031034000c80354445001e20b0145902582801071307a83c0810200c818861403400e545a0b103448081502c100b5200f140000340300320740302c1e102505641541c0d4105050345d600d41101030018000d00012101c19099514003844203180b4070301c0b48490800c2d56034a540e542e080c010010085205441010448813207030300c0c02d00012040c030b204075008001904000344d01e0300d032405c8088040c03604980c5c007405442070400c028480d000c09222943c022100c903002100e42641d01150b485041c2d004010205540790015048100344030902c05070b80080c0d0040061504084c01a0780c1d09070040c0d200e000c0c41d114881c4440c4a044001202111840036044600c10782000304500039240c00301c80c084640704144200020740711034185012682082c081c00c103001c2c16082c1f1032418 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953037697 1250 953036447 953036453
    0xb0a14151327020f1206031f0b04020c0708160608010608060f0d05100b031c140c16030609150e070623030a05010e090a0b1b120106081b07 61
    0x100c03070040c821441100c2c100d44012240c500040104912141c808660f19880c0700c0e41865164440040506042d48000200743c076420000b629444401c144510041007400161100c005080b140454a601a40a010083c5414001e2001d10014508140107056142902c1c1c0740391034102c003e41c0301c0020320255000401805800c10449944064100d80910140312410001496032450040c0540380c4c0c807440da0000b05d0b00d0071561010030203505c1102242c1070100d030642c944d00720301c0c084036042e00001e50207803c100041d002e034405400c1c1c1148800c01d9400d01c00500d944a43c83c18510340c81524206e4031500d20078184071480f6440d6607450480141808a080d200750500e5aa070700e03600c5850100508801800c40d410009803211000150362409240c0d02d040c42d00b81c180150500303001c4c514405001c1c0000c21844400082c00c010301c290f110810f000ca1781c1d103960b2002e4600d009140081d5042c3c42c01c005665110143c0a0003074041c0000362581025414894a2040240c0001c0360541203a20204000c0c404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953038947 1250 953037697 953037727
    0xf04061205090a020105070204020712080106020f0303040f0f0c12150501060c1101051305040213030606060f0804110126070318051e0102160303140f130201030504060b0a1415 77
    0x20360302801e00317587d80c42851001c14020310800380d000d050070100c10303140c0100d154000708030b90481d8104c0d07080760b00042d215045691248410384006001032401c603c0b400018040c05201500300d0300131150b5440095036120340301041140384008551044648000c001c00032118447c00740506154034280e000d5203003d80c5d0b40c15015102c1c0e0145410b020f400301d5100022181c40d842c0f9001303410081c01c29074840364460350f2105609035030b000032200e481c20028080360161007810203003028800e564580c00541c0380c6480e08401d8110103014030381001940d140e2036000000e034a04106440b00003100d200c480d40341000008003221800500741c01100341034803a035404a00009070075050b410200c0e55810705003050340e107010b00a10541e044032140ca04600184003d040d00341d4401340740b00c000300c0005001aa0360b01209044200e00702c40c00030040002440c03c20255109070f00403913106205090015a4442000010310042c580e035124814200340c8041101d1301382081c8000d9042d54170981041400d0080b103880303c282d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953040197 1250 953038947 953038963
    0x20106031e02190b030609042111100513080d090b071101060803090609120c10020f0105100f0e0403030915061a090f09150402031527150a0503030f0406120509 70
    0x100c10014000488d05000400c268040440072440c1990022981c50801411110a100708612203000318082c040802000b4000d643c41500d40c1e9101d554070940d2a9901183c0ba008112800ca0050742c500d040c0e000244100030f0310b4002c3d14941c8a807022690540c403007038252641d41c0c0000f02c89030018400847c00d6100c400c2540c5143c05c0481d1a5460424500001c0345072000e184001c40d4010000e07803448410b070350040750900905010f82d0090200d81e551400446240b0f50790300c201401030005110400c01e00c0c03042283e550b0018071038600031030124a9920380c090000d001c0c0501d2407010b66a1201046240c4015103100000c04125241ca810906d6060005406c9143c50f0116401340301c2d01e4000614242604920701c0b0302550087c021900d03030401b2710000c0002000c0308421805107492290780c06850b524201907410100c148822801c04c2d0340c80307103090520000712120f842d80168141e00d0114440e42c00b8005003a40e100c03824505602ca0b0314021300108107280c41880e012085182030140b100907400841d02038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953041447 1250 953040197 953040199
    0x3020f10051e1623060609010b070303140709061b080f0906042111060309061b130806041e1106072109050906041416020106031e02190b0306 62
    0x100d508400240400041c1c4a00c1111040d10080728914000b0881c030010890101c0070103c20b9400360090703404e115941e0304000e407407481c0d10082480040003858807140051040501c80c1c035001c11511145610b013080b0500a44814010406c03001c400d000242e4842d806a1300703606040020021039526031039604481c8550715895002d1140080d00c0f14070740c5c8031072048070014170007580300580e040c55000c501c020040381880d0440703600e40d105550541c2440d109007500d020308614000703801c00d0384802200b50304100854990b504203010910010111188044080c4010a01a4040c14042c5000e240002c94000909111440410000e0440340070074145074481501e141e00f901c2880d03482c3c41c182810b00c1d01c612010603403a04820844020b841e100d82c08060f0b041260020380d0a110242c0310380f01044142e80c418070502d080e03660114000740c0c610000c0c1d491480b8030586d6000010300507840b80c0380c3e5030704030180aa40006a0398612608000c605180304040c481c200213407906208242401502151071102800d41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953042697 1250 953041447 953041477
    0x108010c090b0714010b15031f0303020c01030c03230a060b0a050403031416050c01140f0d09142d0d140307090b13030203060a02090d0201050304081c050103020f1005 73
    0x2d460301340401d6000a00c2400c00810141c0c00761440c500d810219802161031008699204110606180c01305e6a00360a0340d9060300600448a664801140200040108001050f4841d0740702000300c4440190310005417141c2404c50b03807a241101120b401d4950560210303003d01c0c4100003904000b548001514180c80e4503107498407072080c500d20964021300501080392801081001420100b0100080543e88480c0c02e0b2a410b10030161421802101e000b500702c17402c41e040301000042c810142c0d91b4800840c0921510f1510320380048010102e00d803544010148221030301400d468040f05101d00b040480c4550046d008041604c98401d0050041f140c5a61079020002c0c084007082a01b401104032001418008503101c0c1c0f981141d8071000c0c8481080d1006034080e008102c0810403441d243c0c02204c200b6200500784001c410701580c011501c660000b401543e00942c01d000890102824042034081e8450381c00300824254114010858640071840f40c0c1c3e8030030060352800d0700c40c6030340050a40301c94010790004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953043947 1250 953042697 953042723
    0x506010b030c0d051021021315030b0405070503151603020c0a0f15060e060f01050a110307031e02060907090203060d0812100b0307170a020d050403080108010c090b07 73
    0x40410f004043c0c1c8008100c0c2000108446440115150011148040b049601307824070395401e009a03c480741070182d04400702124100c50300c510380e0420b041588208181040b203681e41c1d00c804081a400350340c101d0745604000713030070000d9260810600822141350a01c3c810103050104200a02130310030001d0a05140d00400c4041d191782e070500030031041c1398100219105811091034807215192484100303a6015160039400714490040395100c51003808080c3c04507400010f180c005407102c4d000300c50880200030201c1c81101c180841480030300f11151198a03082c4a00c800d080d0001803070b003034940444c01198068400c00009090015407401103841e2000d005070f4039100c0c00c0104d042c03440114009000c424000903080404400d55184502c01d5007080c003c500c80544584010010f844241c030b00000058100482c001400c4c0c0400755643c20582e400c01c01460500c00b626901c00782d6208a5055000c1200540100b10b000000c0c05800f90014403803034a40d5503203040840400460107640c40241083e81c070201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953045197 1250 953043947 953043961
    0x80607051804111201061e0507080f0417010608061510081f081b1f03020d02070c0602010207060507020303090a03180e13030e040513020d02030a0b0a020702040e0a0506010b03 77
    0xf0100b8482c1c1d001e504a84da03200c00e40d18414074418004e10800740003404228501e0340054030003004001010565450919040e516180c0e88201d40248445004168080000041e441844440a00030000420011440915040c46141040402000e1020200d28900740004035a60000380003001d0640d07050101d11038071948152070300500c03130f440203207144c405483d0040740d400000103501c41081d0b032000c00702030403442e00c5040c40808042c030500c06500324083c00c112038440b80290060541e00010038030050512450340c607601c202401940c00b000242c0d5000401e90140001c074003a1a07401710990000b9860360403e4483d4a503038040784a0043c04100720760440f01d032617100c1030011800406141030040c0321410400780c034072032120340c102003100403602100907100d20303040a0003201e100302c4075841c107225011150b40901100091001c02241c1c140a400d08260010b4180da2145020b4182c0d50001619003031644148000c9641040d42824160b020008050009400185a03415103070f00c42e68550716521054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953046447 1250 953045197 953045201
    0x403080c0a09091503050c0f210c0d20040e0d030e010b040219021504241404030302041a03010506030402010c0f0f0f0b1501090605090f1c020307080607051804 70
    0x180002c4102403c0000c0c00440e202800c60135410303240030324155000442c44400300400007a40190060b000000301005140c20062900306041a04550041d20450b086050010364410350700c080031118034070014081c045101000c00340014500041d2000c00c050f40140500e9941c8420004400e406c141c2c564000469420080d04180c0004202400035510780d0001201440010010032f1000f00500c00c1444282c0b80403401100d66004c1e1342c1200c612281884c41c000c900012101800c01c080b48651282c40900c400c40059116510540c06603500580303072402d10050303170b031400c1551a0308211182d003480103100984c1c80000b101c0e04203609003000c4040815618000078a10005071018225504071030201090040300c10381c41500901c02c1022980b144e0752107112440b40100c41c21158001070140006000c494094001071025281c028030032114030302d9020010f204940408040251030307029240040071400c080080d140940b050030043c00061810060041081c0600e0300c104603451035200800015850715 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953047697 1250 953046447 953046449
    0x50906030111040f051f0903060b0a031406010e090706090e060f06030109231e09210c16150c020d1208040b0109050606040302041a060c1006050103050403080c0a09 72
    0x15800440d15551354031405414000e041c8110760207078900b07032942d131030400b01c0043d824002d1481d078885100f240d04644442e802042400d01c221381007040d40304044045500d00001d880c030b501d0b121000b070200f5818101750601c02c0d50302900d40b40c030300d612181d801c0c0700b41a0000d003048180c400380d00717016056945000c0040c1d940d94402e210345030401e800000100d041c0c00950495020110004c03854107111210b0340d81100b0903181103c411001c1100303c013118000824502c02240c11001d0003080b11001d040e03c03010405243d071044a5414000307000140f08101d4074080c400040045000910300361a5850141340844480308160000100300c0c0c041104003c65035001030142c036050700300000003421102e840016241c0d500030b503425a105403840000081c600da1500850b80706040203010726042c680380d9824000603003e82c1840d010103500705c442e95075143c0c0325440500b0f0b00780a000010440748403588580c0f411035203550030860400d0304210030000400d401040c0c1c15000b140358100940d8800804108440c00105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953048947 1250 953047697 953047721
    0x3010912090e1302090f04110301060f14060304050712140304090f05150a090902031e0c13061a0a02160e06030705012604020109030f0302010603060b12070509060301 73
    0x18400d105410990700010000c290b0b600030407114541c2d1a0081d030301003c00e118901c001d502219142c002884400100d440a40152240785000440000c0000290035623805400900310440d80100030811720710111015240010140c07055407640c01cbc55100d8035201c001700d000d0700f98076030890001c2404001600c00c501c03034600d0742c3c80c0a403170f262501c0d40120f5000d01400b06c580f0011508080215a0080f1604400c0d0b0002000500c0f00761014544640c4901401c040754091764176008080303014001842e058003804560726118050f01e800740c4601c042141182c0e598800081051030070038180101c014100d0003d039800c910842e255151030b800c8408900c2c2500c81c060280519400d60b00018103a08006a5103014040c110203550200d52500011941c8030241c1094101d041c8000c0c0c850344045110007640d5401c140103250030b81c8420b8a98581c842100380d0010201e005030b40d0345204209010f40c601c103608000b841101e5090490716504452640ca0219004241c4108651004210140e40941c4002c081c511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953050197 1250 953048947 953048963
    0x60d0513050115061e300504140f240627101d0a09050a05070815010504140a0e07080a0f0203010b0102060103170702030703021e031b01020d0e030109 66
    0x4030005880641c0341c2d14400e04010070001c004107692980040500c6070820260f0791440034404030800c0104022604440514154455803400c0c20030407000c1c000d540c415409520384c1080401d810100e80e10b0502505034480c2b0542100010f0602c2c80202c014070b02c0103005002040c003458030707034100040c08100811900c083e801c0489000300d504d0400030001c01e1150341c090f150030b24a555219150711401088600060303041c04c1d0b00340050305a88083e4441c1117294003078800c465800781c29a684600d0203005401011895000307030b07514094003081c108020b014003400d0f9420310096030040302000d0125005403101209940761109501004010008607000300303506022600f070500c1c0c900f0081451250300000ba0701135402c3c00c640c10417550002420314126540401401d006190000c014280fa42220008a0b0f00d4099004004003507580e4a02c0300c41c04a0940d408020b54901107410140b400e0030099403046080e0702d03031219080507038000c40c1000740000340d400c1100010310801d000900422001d40c00600700c603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953051447 1250 953050197 953050211
    0xc030103030815040e0607140301061b15020a08100503010612120c1b03050625050a14030f0f070807080a0e0106030c1d0f01030c05100e1503070f080402060d05130501 73
    0x117580060100c0c050911a261058a81d400100c0c9030043e01c400d000d00c00c0802c14005044410052680035401c4250003030700d10030444142418060141e070301c6060340740c1c0015101001e01803244a1030810344003c0a08900801c055490016405241050b4007409005400c0c04045490060b0240008040c2d960b44400a412a0f200381c07025451000000e0000381d4031842603a000a1310060342d07030348011300c03285100280c0c8200c41c9010022106a44200f0040b4100324091886840303110203200654003a0114211000c0285000401c0742d0300440f00402400030031407800d0038046456000a00183c104d0303014100070460041240019015244076880280703803102e0309400203441c400512520a00b0102d01c0041025610749092101000e074007800b0240002e600744000b00014500030400c60b601400c0f5040c031266490854001828264041d40406841800001003000c5164400d003a03c0d0000e005092040c03c0341803980200710980994032030000b00ca5922004544180118004049103070391060082c4559 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953052697 1250 953051447 953051471
    0x320070305010c170f18070305030a021b061903020c031c091406040305090907120207030f090807121e0803071106010e01050d06200c0f0c04050c03010303081504 71
    0x81c500c00280f0000a40305001e1018007a000009507801007001d090102540d03181c802a04402883c44c50f4569660f109410000000403c18805050300d100203802411110b65040e01012482c0c0180c86410321520040002c0400c1d010721717901d0801e407030319035181c01a112620b628000e481c0d40300b015022020900220901c0540c1c0c0c4031a0480c81c2d400e41700d00c2182004140e110f0705a9501e900c1a00c1c0140400d005006c000102d0074903001c881c0d0f1011591a00450848580d00b000080740d00c610010380001305113030040c45400381c008070700c0c400074000900106401d0345019800f06900004c41c8000b09126080650f03007542c15402403003070402079084400c8950301d00b070801c0040e1179440c103000c801030340340500744c00000d00c419101c0155040700c0e00580b09030300e080c100d955010010041c1107c3c0c120386482425415401c07291001c003801c0400207520080c000e8421802180786804120920544183d0410302009055108001928116585400c203403148cc0c540d00b4030030b51610140c080031600b180c5041003200c22 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953053947 1250 953052697 953052701
    0xa0609021219060203040606030b0114040c02030a05040603110d111b0a03080f0a060f12060b0604050d020111030d0f02030106110d1d0d062c0c0d032007030501 70
    0x11948200c418420040800e150075848000103030000644079076481051021642d190021030703001e84101070004031640c49507a8091103400070380000a45402c03078034541c5180e040c544101d8440000704d0000b18104103030880c006080b40300c1e501070001010307203c546865000c640c41050300d16560703100c3d90500006191003202c2030250040400d841c140755505440d040c5074440450551007864040d0b0321030416944508146c03010007009083e03401c038680e98040006002c03000c50005400ba2101d814414804100e50034038030240d4a0303a2100e140710783c03802c000800240d40c0343d02c0205500e1f03034203085c4500382c021409500e07030950080c846a44034050401c084426810440d600450683c1c0711f40d101d0991070800000e901c0c0d83c0d10214104100400e860700041e0300c4042c40801031174042c0000070842050207079076540d2071003929040d92004010b0514080392030b41c4d50041040600ea0704240740000c15011030000005500540c80f0f00d006005c0c03140000017080c400d80d0717007045d504c03c0c18111400c0340c441a940b03191240c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953055197 1250 953053947 953053961
    0x1204020102070b0406080105091e072622080d0204060c0c060201141503031e09030c18011406040918110d08180f090f0f010f082d0a06 59
    0x100500030504003084000d15202074a090b40c049640c6d15005070b00386400e0221801d0701606450a08005940c00c60f4000940311009101d2442a661095008120398000b031150515901d103049001d0b2001c1003214507000c0d60f0001901e050891401c0300307030960a0070000a103200301948800c065000140c00700300c8070341144003004050f201d0529040b101e9036032030f0f049088900400a121031480020041211304030303100b484454425004007604d01e03060641890180300120b044c2151003204000c02c1025161406101030800e86005544e1201c0700c1402c1e9841440f998014040c86207a884407059071170540e100e1509541c040c084024040181d00484041040740070301904040b50082100710104008d41480310f03c0c84010b41e03200d4142070a0031400b00d070010307042424862940d0002c2c2c1c9503600d62190756400400c50301421440c000d8010900340b0440a500c550016003101850180701c0c101001107107000182c3e040d121b00c0c014035144003d07024103061400c1c49095004542140300340203903081030141a0740720786 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953056447 1250 953055197 953055199
    0x703050d0905030a140f0706111005010503120a0318150c02120f07020d0b0f04200105070308100504020406091410020601180f0507050408190c060c1403120402 70
    0x6089111046012142030703119001d800d4154019000d040000740c59a000e6160380f4626034203445400c01110750b52413400d20980d01020010f500750171143e506a0090040c4180010f400005100d00c0d81400c001c06e5540a044284882c5c1304000200441983d01c00e42c000c0240150401c40d0307a45c0d1560604240c3e0540b03022511712040c1501c0c2c04100900907000143c40564802c0e2200910b0800b031080e00350314100e0b001070328245d800c040d03d00c022070300180c1c520880c18812485d00100c10368509150415600030710299821b10b41d003240b00032540036a070703810400ba01c00865242c540012a90fa8490107610340c0340d030701e41c407440e045030001c00c000ca136880d0407100044c107480311102030a030f0f54409802001001c0c1e0408107840056081100144442036411940450a0a981501090341810b050100d41100c0c07084a8010010b400410184404d80382844140c1c1d010342d1003800c501d19150a80c0302c20364800101c4c480c00d02400b140908260401ca0070880b150141e02903081566200d00141b00310002c0c5600c125012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953057553 1106 953056447 953056453
    0x705010605040632010519031803050901021912030213171c1d0103020d0e060108070303080f04080a0309030c1b1a0a0e130e0f070305 59
    0x8110b0100c0c01e841044045041c0000110f000c60030715004070b942002d504540c1e9004054400742c088131010710307c8805030301600380c000340f42600303406042a00751000386082c50780003405030035844c1d02a02520b0044901200300d10840505d041c2c000c5c003400d080109084600d210b035001c0e11031f140c0400c40000c6031940319542d8111140f10b0a091100c40c0d80411641d070f0581290b10b2141900740c603035040c260400d05442c242d40710341e00c610011070b6040503400300310791344121065009003040056940603290030756125902d1944440c080c3c0801d0300443d541d074000c54496000240c0152085801402d03203414003e0f192000c8001c0c090411081c1c003007014601c555030119510156122000c03900411071054a4504100c03044072076084035004001e000b09009006034a5000515140c90b400129201551940e890388460000c01008070b00a0681c03052420320052000005140d10580f07000b1411 = true := by decide +kernel

theorem cover : BRFrame.Cov 952877697 953057553 := by
  have h0 := BRFrame.cov_init 952877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 952877697 ≤ n) (h2 : n < 953057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
