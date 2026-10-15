-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:11.721185+00:00
-- url     : https://prove2.me/submissions/0589701c-2681-4fc0-9a34-3f5830eb71dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800719424 ≤ n < 800899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800720674 1250 800719424 800719433
    0x301150b0421080c0a0c05060702060f0c0c0604060504060311030103170d022a0d08070f03020702030307050703060501031b03080403030c030509180a0e010e060103021507120806090703020307020604 87
    0x4482d02c02d000014415100059521080010b8004010440d21a0004c0c21100308210706041100d0003400c05445150420840b900003d086024030306804081c2d038800110401d50b44800d0002091180c0010015a00d50341c80d007000400e5a00306005000c0842c0c506909100c4e000c05280c1a64101c07a40084806e8450b600d00b00924596000190340c0722040c0e07004c1c88002c11925008103003010700c844811108a9003042c0540c55860040d1400660080c0a030080078041800c1d03019141c0e80148840d81800b50784d440325403011034a90f2040501c054464010103c000c0100400da07007010341260301902c0302ca83c10f0076240f50117411420030340c44001d042190030802080045d02412050121a0003400c28501f0140c154001c50046030b41443c941d401041c100080004d460510b101c0c0c00c03101800c5000801c0b20400b400b802d03d079901d5060001a2084525200c51040540d041c01200c10141c0d12029010031143c288501400702d540c1038407004d120310001000940814803a100740e9115103816030080a49803925100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800721924 1250 800720674 800720699
    0xb010c0203030f0f04030c080c0414251206170105070504060e01080c0403050a050c0415060212070c030c0803040f061103070b0a022710080610050d0b1507020301150b04 74
    0x81c4a40369180600c000400b00e01c6225000e4008c000c01006401c0c0d08103524200f01c1185c001ca84524a0204e100061040040b80010044038161aa40380c841031a03150031416038200b8089003010304414180031000c50180150541824454070b104028407c1d519412412b442900490144500185100c905c501a80d8810705a580d0805400c0c440b5a02c0d10340c41c0c2c2c440a0600710f030381074160b800f80e1100140d071016003820701c1380d852408424040d0451041c00e0034402900e80d0102020418990310200e049030500940c4c0c2c243c08000e5900406ea050030658030002d4035101d411500c200b1052010030000003442724012803e207140448071a001e14900100740e541d0f41c22080b005081c0c4c0004a07400d01502c0396075100c10300070812407c003480106a51040380e80812080900000114081011000900c070b0681ca60411800c2403802c0e0342441c580302c00d14030412400604c0100312040d40807003180c40c0441019030b00c00041c904070f4000c3e402845800d0800f800a803601490344908820104200310812a0100095 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800723174 1250 800721924 800721937
    0x161a0403080a0503190c050315090105060d020913090506090609150f090a080408030403200109061407020405040b06180f07030c091a030613050103050a080702030f100c030b010c0203030f 82
    0x84191000c04c0300c404980841d0f5022070344030041f40b00001402443c00f088001082900b9080700c0b12090313907040002003040c40c0140124a241c0c25008616000580c0d103980c44034044010303000c01001551081d00f0302e01d5840006613a04080c0e4050100400c8040d000424280504119210840c01980300d1641e100220700c1d00070150482c0b40941d403030360400030b0060b4005100610740d0304001c680b40d03421070502007082c0041c60510462807140c4c0d0540c2c0202d981005010b81111402d007800e40001c0606140c0718981d01c9000402503000e8904010172080021010b03d440c05039034180c641509240b048078501c092450203903403045500160b080081c0c0043d04c41d8010039001c00181c6044440340b6901c1f030107060310b14604412694180e02c0841046418100100d1140000d2450403051102d5459070721441d4a510111101801c0010002031003815034400b0807100c452801c0500490f0403003c10380e08504000e2080807442000a401c28485524a6108015201219400034061444e14000d140c034074800340e0140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800724424 1250 800723174 800723191
    0x2010807022d0f1b10020f0d1416031d010203031014311125060605030d0c0c062109060b091302040f0c0e0f06040503161a0403080a0503 60
    0x400120030844090041c0e90380492000003c00e00200b000c0c08104400b460803172000c04541c0f16030300c2c0c01d5040000160080d05841c01e401c080841240842c40350180e4030405696621080b89203c2c05010594014295003000a01c1c5003c0000c6e201c1440049841c4e10085e81e101411004040c41408444000525071044203401800045890f141c01001d0604483c80d88044c502c0912440c04c8a10044044c0581004e140300840c200d407400301c0e4624810303454440c4002c018040410785601e141004907552101c2c1c040c0800904644118015640c0107010f000804d00854200882c0040010401e0080030280050343d541c5500c9030003000c043c00d00b000203180e0301405035101c0e81c803000d503400c0e261288500c00b80205442600c40c00d1300740d194018031003a2041d491640c004030341351002d00c8003142c0c0c0c0847d000901d5041110100052011140098403a010340c0d0400c84d45401200a02c2419074110040003003103480c2c0c0b2144402400d4241e40c20300d030b41d004034800500400340400c0303021100ca01c00ca00540d48032410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800725674 1250 800724424 800724433
    0x50c060f271c030e0f0f070b0d020702040608061503010605010f03090609140d03050f0105010f1b05010f09150b0121140705120f16111002070c0302010807022d 70
    0x707403041601102d00020110b00440d944003c4a003d00200307100c00c0c14080e1900700181043d5000c803a00030f68038001813090406034080854651400c0c0c0c1150101e0b20f80c41d400401c01e03c0b4150715007030070603280d0001ba135903039240111100c03407060b050a040c064141213840c16150502c441404030801d40241c100080100d40095640302c013000001e840000b6045a070303071008001c060314038204c40c015003204d0000e01600c80030302a500040185a9010040b400c0c0300000340b4100d001d030584100b25075403120045100501315403d00d6821700700c420141e4403001d00d2034041c030b041c03610742c640356011032040307440006880b40003c0684084848079540070300d4104d010140c04074001140d407a07107800b05000103029230f01080040d4000607a00444410604129007060818504217040e003072541038144000031149586e0b041c0003440420200c08803080c0311013200e601c4007241c1555038418924002286943d640012808903240d080880c00403440050701d0488800e050b42103000403001c40184088a982600001856118 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800726924 1250 800725674 800725693
    0x50f0105070c0807121406100b092409180c16020607060c02060a05070e181806251407081b0d0e09070c08030f07050403080703050c060f27 61
    0x2c10400c4c1c20052401e8100050300788002d00e0079006407924010401c995501280c140700850000407100411a50101803103641c80344003101090984080c40442046807007003000c60070700140244000c10440004545024000080380891000d8110664103a410a0b205200d901c181c03c0502d6000011203000404040c1801030301c1d545e003800d49011a03500001a088013003030003400c031110b01899400000c0e9092808640c0030004c04a02c2d403224031144450400c042c000420030030304a8000e40004d00e6060003c0d0342d060300d40008402985610441c900740880d010481c0e0842c5c2910400a600d090840b0200451800c48152a605110303005104511040b003c1a881500b1260040001001d148032903116241d818440400704408000000e0199080c44101981c6100190340002200d5104400c0c84581c1000d48801c141114140940d0300300514070301001460005141e009809010a5034603070013110762569402900044001069503040c15210b5440c00d00942e0101e4101452a8440281c00f120005c0d031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800728174 1250 800726924 800726939
    0x140904050316030903030e0402041809020f10111b0d060207050106050d0b040605070509100522030803010305101e09061518050105060901081b0903010603080a030f06050f0105070c 79
    0x242c101400300c002c41c107546010020143c1004041a4480c01160114105854000441441d000c00301e03c1e040e6040da00c2d0000401c55882c242c0f2202442c0019054841d48102c55401410042c040307403208501c1d100e01c21008030304640445804100da50050503125009069649500c060f40008000b100d0355501c40601160980b00c0310f4519842c0303030242401450600305801c2c40402c8900190002042090810014103161100c4850010303c0d41240780041d980c0c0350044118008a030b0080d44080c8041d0310303400002c18022844091810f903400b40b001d50380e401c02d04540040c12581c0002e04084902c3c6d950718450380c0315045501241429000d140301103507000300d421120008609a82102c16000c4161101521204441c42341c00d000d800141c41152409500c040041c250081c001c0c24421040031059205100d80905000d5869100010300240401c54803440c016483e5040b000321200002d241000080d20f510300e901801d02100c00141c28000c007141d5800044409a120250035500c64400120004001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800729424 1250 800728174 800728207
    0x90c19050a0c080a0905010318020102030301171c17010e0402131a03010c110c01030525110a03022404030c0b07020f0a0803010f271d010f05010806101409040503 71
    0xa05040c0d17a1051194103080014003143c24980c81075140c409101a020011b1340c00004490544050b22030246240c401502c0c13003890044041480320b004404d42e01c1a0000300d0b000030b10916214080f000d106200ea072038a41d14026200e08807406507001c0c03520455103e00ca070407588004001d14003404000c0751250160042401c2d241c8010060340081c420381d5140300082c07414040300a0b2241c09190038807541c20305000006500d0981281c1e0940340e414000142c1c40280900190492031302130300c040e24000541400c001c0d440321618810148009204410203800c00001134410344183d80c182c407410206041601c608840a0004010340203620031880d80d031206a8081004809240c400c4000994960400611170703404e0640d9481403414100c2d00c41c001551381e030610b0030b80c00803100880d8009015100e5000d00200c515902815250551911a0f81700c400a007542005040e94192011035405460b601d00b80b186d05481071007800d8414140070300c04c940c20b2030a040026081b0f8000c10850341030055848103007601 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800730674 1250 800729424 800729437
    0x4020f0301090c08010f06260313090b090703090305032e0305011e06080a060f0b04020c030d0e0d02030d050912030106020f2811010306080609010605090c19050a0c08 73
    0xd22050f0b040401100340240070f8000c080514040c01c2c09140d203401c2c49110401529070081d010346440494500d18110200295039429082240e540d00f00c3c2c0d501c0c0048001131480c8100c03203002e4500c0b400054500c44c020f00415040c07590684d03e00349140c2d00e0b00100028500b10780105810051549124141154890005005103000700c00000346a0031000c009182e003000200b04e0143c8038103000003049447d40100707c46502c41e40050011a1072030709140d4000c02464070700380d90b0394054408a5a001540e500001030140034550907000c010403a072039180e240d40c4201c0310300000c3c010b0740200b11a000e40a00ca0f0850b07074210004804403000d445003142d055100703401c00d800c18001a03004e000b084004401c02c11400c00703265409154a44683ca101e407041145803c842d4015080103503203410007580d03920940c071620040201e14103aa2450a082e8845400b0304442e216180c410f10505000c1000c051440b011180b61064a15038840304406600c0c0942e02900a0703076441060082c440b81950200b564500203122 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800731924 1250 800730674 800730683
    0x81305060415172505040801020304030f02010b010327170315030622080c190c050307090e07060c1a04060b0909010207030905061c0905010506180f0f04020f030109 72
    0x81c8101d0002004280c08400c08942183c0d280a50600040c510001074440c40b50708101ca0b00600d020800105903038a120b0313035202c02d84540c400020401450752080030303e0000788140d40248421080b11004506448260003801d14110b0301581c5041121a1050708110191281408142400903044c0d03a50345900116428402c030080100301036428078091001c40d91104001d1042d03103001600d205040a24021020010400d00d00040e2081c0b202d2401c001d0701000006d525941241000c0915010f02c002c81d40d4410b1034028865010007003140a05800380b40f100200040040402c1490040300716200c20300403400341c50340e0084507040f00d01100b140782400d00c150b02030b020221300d01900340248415050001e0029030541d205205400000350b1011020044030400ca03215600d600b1003180d01c5045180b400c2c06c41110f1890400304404018064002903c60001240c61414107901c2c804440d0000e081100c4204a550b280c0c00003501a0704000c2042e500280098110010f03844503001190840f607840c0c40036076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800733174 1250 800731924 800731949
    0x70b040801060501090b0307030c1e02010e010608390603041406181518070f15051c0507030615020303090d020309011b0f06060e040312180813050604 66
    0x480d4090107504000c0c01d0a00e040100a890615080424040036011400b00360b2244200c80305144620703004020503511514030b421810300d9042c068000c0588040e40841c65092480014014001040100500389005040c21600968040038a4104525448480d0a1a180600303102a4030b0b41c401451285204018548aa0051200143c5840002000044038085034884124003c00106090201c2118480810b1b02512131001c501d0302c00440310a034200521801600150306500660302000300d40c1190496840c0c1500000708640da486000c44080e207002e0700c1800302581c01c906a1200b40c1c46401c85c5070014200d42c440303920303081c80b0300c00c0c03900035005900100910500620900490181c455580010341c43d0004140010300f542c4440540c1d01c2114000300010350602c02e03800840300c025644034004000540e10798200240c00f10083c5c40503170010300840007112a04030684142c041d0440050740300440056180d40b00e9130182d0040641c4810000c461800050f50345644000e000036101122051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800734424 1250 800733174 800733179
    0x3070b090904062d2417010e030c0d03050105060721090312080103022106220605010306090320071a1207050d0e0a120e010203070b1006081f05130e070b04 68
    0x36025113000f8072404841108210581c6942c6a05101034805c0760025407030703401e01b140d241c45002d0041903402c501150303a010000d250104e601011401a00320b1419880800103640c80c0c20500800303014001d4001e1180783c103003c40c0c101e4078916490100311045540740074030139242c90343d480407100c080c10303400f00c00405c6065005008514001c078a020300070b88034140d60701054404c00c50749a40c0d480080c0981001d503010840f909000c3c54104a40110550401002c5c800381d40c1d645046801490111410745c0054a404200c80480030700c000700d8581003108100070b1401070300304020100345002c4005e106584c20420090207200d40414400d044c8204002d8480a0300c881c0e8030500507003034403802d181e02003941e04a2201c16000a000340c0780c0d510041c0d80c52805000035004100140d1031407091107005005500040d04201d0146d150325400f100351045d95480320392545504040c800d60381c4201c01414000c041c40714051049091813a120462200c41d402c02240544030411032604014260700401c41849000506 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800735674 1250 800734424 800734511
    0x702100c020316091a040b10050a0c140a030f05070803010320090415050702160e0a0204030b15010f030209180402030102040b130512060402010c0b150604060509010e03070b09090406 80
    0x140038885021b6800740030003900b0000240303080b105414560148800410f40e03940403840346010b44100d5a014400844c1d2180110109550b410546002c8001030788070078926007094425415100c0302a032080c1480e056900755905c2030038040460150f841d10950103524000381d690342c03590321405940180d503030115000091940c5016544010409019580020400c022140305c0003511402c031001d20b000786c07480d621050002e41c064071840c0d0018000305002c2090054100c0c01c20055010729109032500000120307050310075000d034012500c500f503000f0346000000034120709030290540d1061004000603c0c180d00c64041d000c441c1c001c40d0040c050340d041342000f40014107244641014800283c1e000300510302d0260f000915030001d400c401840141d110004c0303400266500000c100e80705e802040c05071144c0d01d401000b0305503002030a420f070000700750000400d01410046900c400350355954161a01d010540c50500404800140044507a20707601c0022107a03a2002002e02d0744412a108181da80c4880301150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800736924 1250 800735674 800735711
    0x110307030b100e0d0311010603141f150b1e03070e0909060408030c0a1e030f150e0a0b061201271e090326100b0702100c02031609 57
    0x20b90b0320a200c050740c0340c01001e43d40e2544200c2e025500d440d00300355914502c1400350141c032032540001c00320f80c0503010702d12000700040354000c01c050790460024900c002400801c400d80d0280ba208c0c0d401c00c0c42403c414000041e04900910340200601c21940444d02480c000c030a282d031044a02d500020464165a2414982020025040b2041400410a90520f615400074a2102410204010314006002d80810780103607040892410000d110701c0e41f000600c603020380500324071000c28403014500f124410801c82151048029204034100d0072401d03640d5081c20360000c000c01a00d1381d5000c6418004101c0c116014030050340070301407203084414441c0b07681010881351300100308031184040c05c000060044170760520f41c3c48c08070200b04c9408140c0240710306042e25800100b02004048001c4101c40340d001081524160b03018880f070f420040e07401d9507150700070160303400342481c02036111040c0a030f4030360b840384141205001e86000400359000e101c1e403103511403648556507000480d825165404038950030910803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800738174 1250 800736924 800736949
    0x90a0e090706080606090d0302120c0304211104020307051c0e150f0601050304060e030a0804170a090302040b0319060c1d090403140d150305011104031a0a110307030b 73
    0x1040c100c2c0381130800001e00c4500400e504540249003002c0924141442003140c034400f01b03c0354025558812000401980300e0348030b400345030180c0c3c003026102c0c400c245a11203065002c41d040742c21051010400c4007004081c0d84090705a0b010070500b4000582140088000b003c181c0c030015100003040b1111451084c03c080341505070130a100c00d80020081442c01c4001034541c0301c502481c00554940d13076450007200404408503418020f00c4003003800349500d03070868881c50190b8050b0351450801c0c44480018101445080c0001d030015090010410050425070060000541d0080c2640c00c0f90010179000c400214510506651554030b03200fa01020581213641c00c812681c3c80b0030b4807000c0147c0c0001090701918007810007020884000605401080e100060b80e0601d07002c200d00f80701c80034444000032450502c900042c0c0380b5518000702c1c140c2c00a808001c44d000c80703034407212426242911140590000100811074035020b9100e01e48103c40d072240000640c4a01c2050b00c0004120401c9010b10000c80d0269 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800739424 1250 800738174 800738177
    0x1c0204080a030804030203130815010503011109060c0705032508010506011d04270213051003030c051207210908031803120d05190c05070201080705090a0e090706 71
    0x1048284105040801c00a00d00394141c2041d612070b8a907490300f00d00d5482601080300120080100c007140080340030980b204075a248090b00c01d6242d8869041500700c801140c03211034450010480007980d8248400604806843c000558050030350300c3d00401d08014181c5280b461035028041043d000d2030b40c1040d01d101424a84c40204002e18000740064211602c04c2d46401041e1740c0e04611000301d9455802c116401e1000003800308101042da8042032000d414040100d11581c031a01c44103501d0342e95480f43c0b500c0340c0111803a01d01c110386540c40645041d4607006041c3d80c0b0b405400071940c05954000c0081443c14032610710b6480420070351000041c007402c00704240e0f080003510320082003428370002c107440c10402861424a43d80c64101c002070300d021101120902c510b04045684001003896500c03d520a0555602c40c0a807140101464401c80b0316510035000070a40900c0301601552280c032034654010050306040b850314000344006004101c1d1503000c0c01d140b4000800300300c040b2905220680060801c3e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800740674 1250 800739424 800739427
    0xa06090501050d05180a111305040b040206030723090406151d060d0f0f0617060c2505010c321305101206060f080f0703021e1c02 57
    0x3400002461031159180004205403201d010a00390a182040c2200c0c1303500700e008032461005107290800c25210101a02c5120740780340c6c6401400d46031a0b0040703c1c881c59000003041ca0729030300ca608108003500060520001c000713401c02e2100310075185010600c200200d607854240c81e41d418004100a8803500e4002120001c4d035040305260190300b2500d42c00100c0d082015030707114000140042001c1f03004440c64840218240040c20000005640c00380140c03040c00c0c3c84c00d01100740c0f17459050b15905080c81c225400c070b50103a8009007681480801800011400703482c010343c0c4158190711244a481e0840b401d881c2e80c0d41d50007030203000d19081003010000c2d404070500901104000d41104c0c1e0024408034100340320040004000c003e581407050100e029110003001d00d2000180c15200500074810a5000901c1c2850100c0108503103005480c070720b600707011541d9052100d580f602c0740344040d54005040c800c1415020300c113480303044400000403602c090340e00320300d143c0f1003070100041400f0050803141000c44620 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800741924 1250 800740674 800740679
    0xa060f150e010e0310150513150b07061407020627070314011112041a0f0402010e01090b0c0102070317041707050703170a030b03060603030a03180b0f060a0609 70
    0x100440c041030001c0090030501c414980b40c40100381480340c0740320480c40d04c0d40762000c042a0003584004d2502582c800b9114040b070900040312000c112010794500c4142004c03521410051002d14030010a4020f10401000c0f40304010011209150716040c0c1d403120240c0c00803c200032a00c2194088001e030803140c4000e102000b07045c0d602180c0c0310800c600000d041d20840c550041100182504034a0000b0001203001d03a907216440d08040c00760034180c03012100258060060b007800240c1440050145140a4081100b51140d81c015215004004d00541c103200c03c004c3e001402c1f8003040050040780350503000241c0d64850070318000704448400034003050040002d1083c4400300784556107200450382da41c00136594501d20360400703500e441c0c041d51000f442ca44d20040640303440c1c0301c080082c0040b03140545090020146201c01c243d200d16045542c1a05640f041c4049006284a60015a20300e10030a100e44580c9030b140c3c80c3c45100001c02c40c0c14012000380081481007908100100c2d000170072461515001c03090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800743174 1250 800741924 800741927
    0x103020f0d0b011806150c02010906080c180d0c08010c0e0a080a0624121109130b0c1b0307140f0a0b330f120304180905060a060f15 58
    0x50103000d08803104645030302d00501100d0365030240000d0074101d007111011400e4010014421302030547c04038001154404000b64a178003c10881c0c1c000d004003070300d86051003900011300e00c1c101c0c030b080c010691000b21074141c540440c03088203041e0042c188500022510646140303024015041240c0032a019520344401040030035400f01d05900500c2c2e0181e030218518880c00350030950b81072140c502d8540350b6001e040001c0d000c120301d005801118450203000800310322020400029600485040c41200304a000f004009000d01481507030207076002d51006c4c185150202000e50460380c03512007078101e500000d5071506210010035107070403030181c9000078117505100c201c0458440c41008001455614490041540e1401c440b1944800040561000190741440c14082c1c001404050045010760068804481203081240c001615104801c0046292501d058420780c041c1c10001d00c003c107000d07540c15200300081d406025080c040c1c0d215000c0070829a0500710150314102c07499000403003200a00405c082c20300e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800744424 1250 800743174 800743193
    0x2802010c080c0106032108010609052101060b040b04031518060e0a120201020d0501170d0e0f090c0d0c0f09030b041103032b0b030c100504050301140103020f0d 70
    0x5600051070740d2030321030000791140901410341004001c0e043c0040d000d1145241940c0072140b20035030382c0e02c40d000c50341e0b00c0d4806d071034100d40d42c043c0c2d6421190705490342c00c1d282c01c0c11049003051402900005041650769180fa1040e421a8200070b040c014001803c000340311117204100508105290100940000001a080000c0d9000d100520142d110900951140c0c000d020358200075402034080304141c108403400a000b07500c500d1880d42810b242100205010754244100091820300c00700910900c94000d0f03082c0c90105400074400d500c5110b0031400580d5884002c800c1e8091441c90451580354405803051740c058038420075115041114071806000a1640129142d040f00d4111a08064503140c900306500400c480c0d030041034240c0b000250a600c00f007030303c980c01000792407071a10307080090401e907040d5800e0b600f030040055070503030101a1981c1075151221407441d442100d410011f1506580b24082801d59008405c0b81440e42c3c1144010000e42c100304a180402000456124001041980c0c4600c1d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800745674 1250 800744424 800744447
    0x10c0503010e04060207021c021c02030d1110060312080f1e190c11010c080609040b06010c06090605040c05090f0406020a0212132606070e0a090509280201 68
    0x4007a070035004201413000d1a4101c03640c1d240c010344441d10070a10703d0100c0c200c00a650808a020340c03442c000390000102060300c41154154010007800e021030403600115450408400c0d035812038001c2643c041e90750840d0384101e030002d500c81d80040b241d1204850002c0d109080c001c00c41d90103420203008000d5941d05011a40784806140194998680c888240d03a091010350700ca40385000a141030410501540c0060107040c0c007030081d000900040c0030541080720342040684070036400014a40209001803040100e042d445041898032552400c15a1500c03001e0b03801240c000c0e40c074190349900b8001403003c1850b0040190200b40c61992181c05d0000401c40c448000900250200d135001c03421525240c8240041814403c0303140c0440c0e202c078580030100d901d8807120f00c5620081c0e641041086810b51030b159200c625070405ca4042c0015660701d03c0103460071644102555440402d44001044240841c8134044c001c105120044c40d120009111803031058030b07005c0208004035002c13115000142c0e0710036901810b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800746924 1250 800745674 800745689
    0x180118053106090602070b15010201020a121a090117010c21050403030b0d0510050f10210804060305090706050f2703060726060d030c0219091d010c050301 68
    0x2000307101c50412100074440711000420440c00080c01c0070500002201e41d6000303a12182030003007485841e20041e4202d10801d9140004140b64141080d4424460b5110b1454540105920039100580130001a00c40e04240c0000181a420545001c0e90a500340305182c00d129240c1400c047c102041001215015014050b107400b070f58440b800a01014441d40001c03048240241240d4000c141e54034040f0b441d0f18100201c07548451810780014441c8204000e66800b0b8840b0741d0310f1034059410400c000010b0060500005086059034156800140c3c184009000900c81598001920300700102da15082990302e82c8040108001400748114481c0850115000c004a440145000b8030f40c02083c400b0740c8611500c1d190340b50141e8010404426045004a00381481d02c00d80701740350b89103000c94401c5440040d101190000b54103202030001030f024140c00d1940718001004060030a1304109941e09540342da400000106455001200681061690403904500340c5002804402980362004005010501c078444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800748174 1250 800746924 800747011
    0x160906030b0f041b0909030e18041b0e0f0106030b10120b040f06080a0308130c05010e0112050106090f0902030115181e0f0b0a020c0f18011805 63
    0x4040144c4c4158480c1307603410514111540e95580c03a009401003444039020340105038012070070b0065240c085182e803000694000030100b01c0d02d40341c81d658040000c480842c81d020640c101c020913955450648a44a0000c4580d0b4103910741c10004000d00b54ad40e00341c105401400401c010081454011000e418003206142e00054640c2c01c480c005806072180b210300d641124542100807681c2074011484800090003900e40542e5a107910320348648030507a0300e9028000b960000401d008662090741480c00002052404030f00604a03021848200c031000c5c0e200c00080360840c0070801950001244030301c018001c111086043d5894010b020902825503910882001310240104c4003c0302104540d9003e414090055207130721078041805401c0707095a0007214034000ba10b4400040b2420148202e58803883c1c0c40c0d014000c092005414847c418402148646e449144101581480704000080034000e01e00c000001c1600b07044050848101c5030044c2ca0030509070544940c50b4184400780d4600750942071014800d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800749424 1250 800748174 800748181
    0x6320907031e05010b0102120d0c03090803180c100206040204112205030c060c100b0a091104140a03120c051c08070e0a1805060a0b040305160906030b0f 67
    0x86040c03506503007009090000e07410300c2007480a515411076104500c5207001708030f440002001a41c0e5155642d00044841c0320822440c040c1c8255900f0a4803140202d01780840d00041ca0350320401d190b00221500e4100202c00c0d520303600c803680700b00b00c9a0100ca50075540b05a0381c1a40c1c2800940301c2d079004101a0003181c45203203d209424140044078403401d030920a429100c440145816489411407042c036101c1d01c039086c00c401d984d160400444a25034440c038018040341100c1c030045805801c2150149501c83c4130f2040001c0c08404501400b0800740e07008075425500d6007042e03405080c10381c00f0f00d03000340a2000c4000030700c00500c581c840f0790080700003400c0c0038000108514185107040745100400c1074a50000c500306c40c0e170320b8201100d14003901c659101d00d00703011110400c1c44403520301031080e03a121450121086090491b540c1c040d40c3c00075005040c0c498125101c40f07040700d040d44294030465a540c880045900022150302c0c190015040071304d02801302620719100c43d00004d2010f8078400044d424032010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800750674 1250 800749424 800749441
    0x1006061b0c030503190e0307050d20060a020c0118321e12121e070803090c19050108160203070c08030d1508030a1407050a0f0632 57
    0x2000046900c80f04a9540382d454600b4041311900720100e00000c41c000f03c0c00c03070100717180110700703070301a50006841d980c0340300c0c0e8a413a008072030032829080c079005044550000382d813034596000400501081da001090150b84d00000140104a103039900d10390324508550a026034941c0c00901102128403070002a9041d5281c0c149655010014400c2540320301080c082482138030f000c010150f1440ea0440c0c0c03c44c40300c224038900c0d940350381d500d250140c0d1611041165007104d8800694034680010460a0036042520a030345201c1d03150300c02c1e41c840550ba0302903a40781780780e0b00d048102034005101d07210b185000e080c500000646150009000f0091450410b032060300301d2442002500c66060f08500c032001f009aa40845544960040151a160500342040c180403881d00040103002c50360503100451420b01c5108088486103a06144440010130401201010030401c0002d400894080c40031480c41450501d400c02c122021a05049040c807804604581d20303c402c4150300b04190821501b260310362b500c8105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800751924 1250 800750674 800750693
    0x170309132d0501030c050907200c0423060d0503030103111f120c230c01020c06011401021c051c0e1e0105010e040f14030f0406020309031006061b 64
    0x500101e96400400303000d620005070300010f048a000d003081c16540754542080c0f108103a001c0303403030310003055019070074004001d40800301c84103071114101950082a80d1400090944095500f032800206158044503011940881c50326007022007210a02c45e0710310703e071395a03d84034001403001401c131b01d40d0075003c0d01142d1229010205040c2c0010071031900550100000352100e2128800d41c01041d14208040300100d00070b400e88955888480348403c009503046000c83c04541c480b0341d85a82c1e0755000c0c03020a03940351040012078040d04c2402000b9801000b090002031030600c00614254414282c99403505046811008030390b10a000880003090b000ca586400311f01824425800d00b842e4420b4090080381c0a0761070102d15100c4401c0c1c402841203903641c000d501490081031360050840e0b80f51f140d48900044640404020f22621981a81d040c020032584581c45074110364418005a080021010950f18081c0111040400c0600c400c00c400c4d810301c00c00928041c40d07140c25500500c0c42500701018460500e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800753174 1250 800751924 800751971
    0x30a121d040207120f050405060d0e0a0606171002030118050a0902060d090c0b030c03010501050d060909030807170c0d020a03060b1b12040302010c08030402041b080117030913 77
    0x20825940c0703c4184c60000e00b80c903210710f00e400010705100c4602800c42c2c0b265084900f100d80040c0342505107402040e5003801080755000d0f01125200d520103202c0041d00c41e02640b8010131810015002c1c00c5c1c01c4a200c00d08015200724480400e40c81000140300b0703004254001c0002c000f150100069581c4c4110080e0000d00c0752990103540068049040120aa0380780c00140c4514410a04000324079a00d20760918140002d54008804c5a0305000501065100d180600040800d0500201d0382d1556061040d0880e040c0305403d4000810040c01c002e403050f0800124400001d0301240504146044c951000150207900e0711850055000264500707118401c0c0c0100d0060000d80c01d64036502d1080d03105c80c3c07032403000c0c64240840e5030086503a0844a0100310040e2400c070391f010f86580c43c0d0700c1d011b503481c0c119aa10081049030700c180e883c14455501340b0390444d00c02404403a40c50b10300780d5505160f1400d01280e41c620300062140e000700314403112a115107480c1159410030007804502e80c003140c03002605006420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800754424 1250 800753174 800753179
    0x102062e032103110a050a140c0309090f040f020f12010e060a0b0a06120213091802031c0212130b03190c05042301021c0801080c030a121d 61
    0x109004420301250007a50318581c554406014500b030b11000060341520041100c40c3d107242e400340701440303050340640d00401c000542407030451440d51003050080c0e500c0d00b002509408650001c2045a8582824010f41c3c1d0094141c5038000003030f182c9036586c5401c00c0b0740d0040090141c4980b40c08818183c45440803074a10000e900024001480e02607840c0d070340c030700c0d00710389942c926810098400c1c610b00300258058255400c2e03544078680e44030302c0d481d500040e502085580758143e001c10380c00103203030f17050b4440c8801c4801d00702165020710b101401007500d03001800c002c6001d085860382019600580024907007a0b58810a0401034461003000d110003241c610301d5119189d940000801c10070300d0100944000307402500c42104210300c440310b2100316500d0003240100203450b90441640b105a15217242c1c03200d5140f070b0510450342103840d910715560982c6d82d00f458401c04101c2401c014025000244000020880c003075004280c54015034550511503206000b010007401a0088244d03010428103a403a001150003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800755674 1250 800754424 800754511
    0x309031101020c150606070b011e0506120403090806070c0b1009051305010c02012007110a06110c100e060c0109050604120f02060405030405060c070512030405090a0506010206 77
    0x14100303a6119134000900e2030702e079106140080c807940303010707001e5074045908003144620036803c008110a00124514810040110448000803203581d2a002000c2c54641010780792041d06042c500500b25082c59008007115401007000c1041d02c41d8044003030302171180c105020381d0f640e41710b4014400e14044982c201d1220f0740d0602e42004103103c604044100c60503c60b84c002c1242601d040c0c030482c01ca801c03100b0050003c40d010041c1d6541c1c04d0125001e440c50501581916a422138400c002a80c0e140c0240c0c4a840032940a070340c10541c061092000c8558114240c2d170307a802da6000b20744014a0550710355005403082c6d10200c1c5042c0300c083d00354000440c203648801181c5030f50516060a080c00c0c082d400e03146000542215000101c240b022070041d0090350301400550178542040c080013003039000000460b26a10603d03c0000310359075081d002003419800400a9030b6201c0c184410b0000302c48008141800d42030500e414800e503641e000034141d03403000f4915903090b620030400c444022207100c3c0d2801c0920003c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800756924 1250 800755674 800755687
    0x1080c07060b031e100213261b0f01080c0d020705070e0405100516021203070219060614010c0c120f05160608090d050f0307110307080c010501050604080a03030903110102 75
    0x541851804c2000700e08401c44a1310401760fa088000c3e031141e5010f440400c0c202a804010705504180c07001d202414407414956030305012141d981c500864a000682420050000e40405050a9204001e101400c0c070b000240ba01d00361440d0341013403044800f880c0034164005680300c1400418056100138250005040701c2d9400c007800c046541d50328200503545c50620b031a001c10541c074803c03104c0301a408483e8001d0074404072204001040d54000034800029400341d41205000d031441482d95aa540c0c1c401d042c009a03450400137408200e030401400141401001480d54002c50340410409045680c2451541e4188046141c00b81e81c00e054100020003501c1000c888105003031110a1800c240ca4a175510020103030355003004155291040042900402d6003009040d6070b045c1460300450340070f8150f0409090b6003d031204541d03d144e01c42c0c4001e413990007020500382c0c0401000e00032180184401c03150241068248400e4540380c14441c040101495a182d00702001c05009400e18a207402030540219140c24 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800758174 1250 800756924 800756953
    0x516050a060f1b3306140f041e240807060c1103011b0804060f0203071407060e06040c1a0703050f0c1501080a02030c060f0a0c030c020301090812060a030201080c07060b03 75
    0x20742130300801c5207030b81c1450004a0482054082103032201c00c010461983e030081101408020001c034003102c00c00800000d000080c0c41054002d80b405a0030708610107504005020032040d5488494001400d1078228110400c036440c1e1043c80840f800b504020482c4001101000190042c07450001000004103848a11030849820011180c82940905018000c41c80b2004a68080b0700c4200e0340d00000c15103210310841c11000e068081c050300ca10403140000c0720101210030b14540300b81201c044a0081c5150350a006003250000c2040d10250b00b04200c5040454585d00a4468014801103406681020603004040d42007000078680300c000c400321540c0b955844208241d212490040143d00902c035282c0703505602d0500d0340844940d80c00d0f4181047c200401c1141c100c86819011074268204441400c02c0b2016035000e00ca0050807a01c6030805603a240d5031142e0380401400020050383c494500d44d5010005030b600940d0060303002e2141d84130b55035604203610704400140b484000c219054070030f100c0e9451082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800759424 1250 800758174 800758253
    0x1170a02120a02041e03021c02030a0b04060504031e0906030515040606030b18010f05060702010203041829090106030b03030f04090204082104031502070516050a060f1b 74
    0xa910b00410303185078002d640c6000c1e00c40c0075a1b1100a4110f0311001d204609024408104a24244020706a460200c10340e1034000d01044203480035580d850341d40d0144010036800c070600201110100000b90380c42e0303c03002c801800e40042131095005050300c440c0012400446040b007102036000003401048050b4864100030014135207011034501170003968409100c140d0510b03041904944101040b00d034054203150a00c00b0fa604810070403419480140408110844030a0078050729054401c0c0016080c0b10580840b03403e0391100100b011407031501c00c00809681c58024556065508504010444c4404400402d00d948140019010100760118000c03810b00802c1d001401110345000c2110f0081040044104116103003600008140038108400c00000e80206001c0ca07003038103190b42c014200040c03900c502d414007044540b682c41c5440d415030241b14a10380380440901500b8240780014030021100c20107440089004003500a003c402100340d410440901404e4075406d13040c00c4200e041000c561000c4004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800760674 1250 800759424 800759429
    0xc0f020d0b04060f020903100906020403050d051206010c0b0a0c0908030c060a0605040e0d0c03020a20011d030709090f1208070207150503040f060b032a04050601170a02120a0204 78
    0x2044c1025807110303494000c0d000356410a48010007500c40c042c03007d4078400013041000801c85a0940030701c03001010400c14021160569800c0e15110703541c1e149040710281040b802803200c5d042c440e0006900c0049a0a001c1c855400038248400007804400c04109669030713143c69002d82d92902c0002030031030900c0d01c0400c685004055600050000c82e84500c1000147c6080d184c0c0c000403940440c200c040218451101b140c40180a4010f4808403445502d450700c071170b648222151601c00300c2d00c2c68240d66503444184540c2d01c403222002010707103120000000344c542c03034035204090714a51550146000d100ca035210200c512513100c102e07014880c5111002400c081c404031784600260041010010380502e543c646c0000d154195500c051641d901e5a55810b11020040d1040c0c03030059441c44080764685082001c20712014203088109251403042510384d540d10810118107024500781014401544d0b00901c050746507403030310011180140c1d117100b500700007805000468041c42e000d030303003d026880d00b00b58001d205 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800761924 1250 800760674 800760683
    0x1020a020a0b1510080a060b07060605031c050f1b0d0e15210718091b050f0702060717070326190c0201060b120604060503060114010c0f020d0b04 64
    0x19030f968580306107010403000084950015040700042c10814424000164090f2484000007255519140e0f8080c1d1600301e104201d80321540ca110911080c07804002410509034842c1010240c0d51418100411502422400140c040301c0420400444d070315030030040a43d412090203c13822940d044900425200c40f064410380141d501e41407110040303401e4011181c5e0000c0d0341c4054044040e0385001d40325440001044241000702802c80c102d61111106c22440003044500c1022901d018940250403100155500307100902108102c407800718281c110079a032546404541841c0c652006041400151500101094080d5000076074001010382050f80e07016074411301e694100300401c3c507050401d48040180c4010b2581c04d07a0329030140980e0500c1e000915407070f003540f0000c213601d03507a07002407900c0342c200b142c0307594540c03d000042018a04244c4681001044100e00600307480d45001200d120f1804500e40043c10031410b80d911506101c01416032051851307024001e180180b00341d0074002c00081040e181242d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800763174 1250 800761924 800761943
    0x607080409061a16020a0e0916140d290f01060e09070507020d02150c100c02190b07170406050f07020304051c061d03070501060501090311091801020a020a 68
    0x7601207035824083c403405520402041c54407000ca242803407080304600040384e124100f580089080d04560b5060347c013484554008061801600c901b0002ca443c81b500803004008e0040c0c8580500d0360b550f0b580030f06558000d4100c10208182c0351245410401c010042100d0420007820721004820301c0d04843c1c100c50781942c1e800c0b0384004040030444000c134151110130016405000400142c42c1c50712880840034401410303214080000d4176108500c0e04540259183d03900003004400038031000340240c107408110340c0b001c2c02d04c00c3c0210034a1000c8152810002d0013458854000405c3e070350240c00400003509406064003018505498040050706c003c84468140d10b00400204079200e000005a400b51a40203022810030000a41c00a4600803c0c02c004e40342903807108454406003030000101500c91003000003960340c2d84150f080c00c9081d20b0307440c1d1002c0d042111100c01000428040341042a20748011503001d0800d0300c80e02440e90000e040c400b0781c04855440080d882e03840d603400040c44841d0760310803c20300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800764424 1250 800763174 800763179
    0xd0b090c07081305130c031112010614040521190c060f0c06020c011d06160c051c02010b0a1a030a090c030f120801170d1d060708040906 60
    0x112404405456450a001040c016100024400c9003c1d02150340c01000003042c0076a64000540e03012000c8401c904c6150b903c030f0125020b140d050261420401c0c2c0d440240d49064880308480d520080144608001c00003502c940f0410031018004840081c50001c0c42044180305820181400c0380c030f05800480c0900c152809040780b00810306915050a130017440c591107840c9032031019140c20306058044000c000f01caa800d400003c00c28406840d07032240a90000481500d0b103907406d00080c0003000840400d5101c0e008000300201d443d6980c042100780d5180c11040c100ea1032a0292910504a15440c001c04440c3c3c1c81c441c01c0b40d03056000040385041110201183c27039599080e06a140007910350000c4902041000422400080d040b980009201d40c61503402245e580d183c0012002860508407801140054898191070380001074501500d000004210f0302c550f880115a82c42c59201c10050034007200391814442948044941d40100301c020b400355917618121326101040754800d0291049080c5040c001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800765674 1250 800764424 800764429
    0x30c240a0816110d050d021c0207050f0f1b0a12051c090810090f05060a02190e090f1906120c0e010605180f13090c15050a030504060204080a03050d0b 66
    0x10240c03d0080d8002900480070344c07030400c44842d8442c4142c201300a4080140180d0084141d41100441c1c101382001038580c4a14035009007131844043c6008480e034001050603440c58004140d080d03060600e61202e207200340d803c1010400c2071006c0e901464950b00c1002442d03080c080007244a00039414001091a1400c0c40071005903000000e9000ba05031541c03226012008184040d48100360140c010342c0821902c8035555200c514140080301c000c1e008075008134100090807070110076540c1450490030070200e6103003c2e90104102d49801014a600900c90702c01040b50500e2980b43c0341d42e4028589414800680c5542c0b0b540e40c03101447c40c1c22a500c00030b0030740001d029041c80d03d03490705030383d2296111817070042e62401e62a01100c45031074141e48584501d00510075556850412654410100c0b404541300041c0c1c02d142e00a0181d0368043da001c00d0540b082061070720342c85821600074a046050000f456142d80c10103030700a00540d0004141803180007000740516400c80081c4c1140310200505000040c80d0006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800766924 1250 800765674 800765687
    0x519030f020f0d0c03030f0207020a030c0e07050f0904050a0b06030709030b0619150201020f04060c060e0a030503011a130e01051017060114130b030a0c030b030c240a0816 75
    0x70f200d07000802c0480d84800080c440d4010314181010b001e805428021907130002028900c182d070049403034850500081120002000b074180c0c0c0003050f4107100c1d080c03121341e0800c418036100e0611540d02c12599180050f000d003e045c1e000f140318400c06007070140c9920f007a00d0050805001d6020544941004000060051610301042003003007036168072124a00b85060822f0100704016000407080d95000d101c401c036082d41e150050401061240e03201c012006860600104464001c4040807544d000407110342e02013604482141d04542e03280001d0654401104045485070254450300e600307103110313030313000040070180000d200b41a548102ca44800603034400350240c0d5101d491440701e00c00c0c0d0803032000203100e0b0344c00354840c10119030202010300d140009840d401010507110381c000d000d030420b01209004210440d0700c0380040c00c86990800704004980003000942c0d852801c08450301c07070341038202c04071030076055205102031180400003103e4445400d12005401c000c2d044070b40700c0000b40d1321020424860322644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800768174 1250 800766924 800766943
    0x708010209130504051504030e0405011401140307090e01120201110d020c150d020a200a020105070b06061c090302010f0b100f0318051b010e010512040519030f020f 72
    0x2450721000c441e104030b40a0280c00300a04c01c0d501800340c0307044641040c442070920b6108511a50312400c41c658400c2c00c102c01c03520103800c00d0f00390388800350301201141d0f003007409003120010051005481748d4505100b15090710b0380b504a03580382c5000d50000940500314102110301d07240b007621051440200314503080e5544200303d00c0b04006030301c0590503020754200b01802d1840511640440c41c50246006075060603039102d030260400082402c1d100500c8049500f9040e40d10140f003030007902810ba8580c000810750b00818101038412520100031a4980d81c0d403d00f00c46110045060b1003010080800300040104001002035001d54200022240104428400c01d200041e0003030802c242248124011101201108007940500d60344078266031001c44060341003501244104002e1004003050aa520140280061240c1c10700900301c0000b1310680c1c106081c4c4901c0001801c406140382ea40d800c09501c1d1000e1082951003068003400258189540440500403c0d07105400b00d9101c0b07842c1d40c83c129074404165 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800769424 1250 800768174 800768179
    0x110c0a03140c01050328020d140f06100f030f14040c14090403090e13060e0304030203151b0d0906050a140f04021507020109150f0801080304080703120c060905030c0708010209 77
    0x40c6e0a05104003510042c100c110038143e0005040c071902c01503480888807562035810070602510304029050200183c810741c00403003a5110310740c00c20b105001414041e103031040c000c20b0640327030079010740005038951100103852462a10340340c49040605100300d01c4801c44c01180c80210302c0c941007012604040081d00d000b9170340755980780d81c02403404028400d442e03c0505080c0040030400d007d240403030700e58003600044c0031084014580e1903185104051a03c0c9a00d88850103003000441044228040040000f0b0380b1201100150703034903a40c0852600c020066a00300910b01803901080c000d075407006522000c02918003800e11104c2c1d40b903c0300c640c1010300040f24001d40c04500c003941800b440400340c0103482040d106041c0382e001c003511007039091404421800301800103001c02c00d824007610340c01100d944c0100030b6100558602400c054900c2e450742410300024090416600e800c01215202e1005400c0d190741041c010000000c2c0c52038869100e92001819109500c074007a0045803c0006100715104400d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800770674 1250 800769424 800769451
    0x4050109090218030d020d020c0906100e1f05032e050118050909010b1008010e010b2a070807090b090a1116050c180c0703110c0a03140c010503 63
    0x1440e0700c00000c3d41c00458180c1c400501000c200d201503e080118054850058016001c80c640b1a0350092902150171660340c4241445414000700740c0310301c000081d00c0001403402c2c0c1d01415480d40402c0c401e015504010341402c50108003001c10700c3c2e00001640c050701ca07038009160340601a450880c00d94050b80603426807128014410045503004442c00c5481c4400300070341c0240e113540c070400210646001c60700350205945880c2408403d1520083c5020780c43c10504050042c0e50410b40085142e0405003c5c119030380d04001408400c0401c031805c0c2d00e048d408082441700440c030386070141503114040c51290394000d109150010807403c00c180580c0c29201c90180c41c3d03034001e40d070740c1c01103101030b00d00c80c081d110074290100302d00341031409002017603400d01d13002d0002000204ca00c00d05010717001d0340c101c51810704c2e00e204106008104010100b2141c1e15030301072901c9005021001001c9081034980d611071903020100f02400410804032a10b2040c042001d0b8044d148901d140b2030055400d4441100c000f5041c00c1d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800771924 1250 800770674 800770679
    0x103030804150204350304080a140102030f070311120106020d030609020f0a0c020a0b0f031b03040803070c050f0715090503010b0604060c0f02040f0e3705032703060106030204050109 80
    0x64101c004101501c1702d403042e44481525818241190311a4000100c687c1011441c1c0050000096480ca1050a1032000714074615021008850411018100d81d080540310b4025120900c0628180c4111402606a1510950b0b4549000e5070355132224140302e012a040c00c000056986007071003910318030201d800080345001151b202c101c40010640008a9100300443c0780450003500000141c02004004c020b00c1e07a990500c0c41a8a00240382c505205030003000c20410000001c45e00030940b074000c40f590600346c0f0302550b00d1030154141445041e20031002e21034440005140e0742c0c482c0500c04422815102d801e80d50785c850040c1030036289240d070b416400c010108400c20500f8400c0500e5035085000c1e80109003003241560000f17013600e03044044c0300141c60b1661444100c9050912142450030400000341c24041e86082c3c00b028000c1030030f100c0020440c561f95200f82441014401c840c8048035030100d8a2051241082c0c1008407102d400c00a030113803040704000b06c3ca9501134801c503020f0307450503168005a1403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800773174 1250 800771924 800771969
    0x711031b06090721021207082b0e0f06070f06020d0c030b060a051c180b1317090102010908120907061112090109050415060f0c1a06030a0b0103030804150204 69
    0x281010106d820400401520106090030b02914001d8136084000c1c200002030080c400304181c6c3c1d007001e0400ea0825142d0642005038100551050b16001510104144111040050440d008006010740509000001d400401c1040e6008003da094007003410804907803040d804030120340b60f040f422a0011003c00000c0071040c028006003044800d0018000010500e0100650540e0000e51003011050072210b400300030007600350000d0fa4080380300188441803a01366220207100b9400c1c00441049004001000c03001c0d41d10030342202c00c540790070103038042e40e0b0b41c01c0350015203a403001220301d0000e5010b1500b020030580d01c100c0c0e010750a118490028000700d0740f100d0f08590305c0d03845540c03800d042c084502e45c00911a11240580d984288a04010400051900d42d0182145101c61a002c0810101d004400000b072800991000b03030000008590132541d855402013882c02c218104003030203001801000004055100016a200c0c5100fa040008641c080305000c4050380118012400204042e444200c01107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800774424 1250 800773174 800773229
    0x13030315030804210f051617190c0f140f01050f0d0b18071106010e01060f0503060f04060b0d0e06040308010e1902040815010b04120206030711031b060907 68
    0x9490b80f0300c900301001c480c5e502c000054980050031506a0044141c00f01c0c3d021241c414a0b004006040b030100d003c04814002586801010601a01c41c070700d605010002d004035030382d00b000a4224010102c2820341c035941001e031a070941600d594851294012501c5042d48030300d05841d4050a58950300d400d01000d0032900b0007820302e1088054103d04074040040060001034512401000e0341e4944070100501d152004c1c2c10000160070900c0e003481c1c1500100300c0c1036404408148001283e1601a45a44401c1c0015918140c4508615800341c02c2040214880004c08000d010b10b0f100408100315004c4e0800881d0344030703242120040c000ca92460010015050342c40700d4a41d000d0000e80c07005044c03000c195200b8049030465009088168403507003140b8842142e080885014005100350079007004d140c1038501e440700000d03042c024014000400030440a901884281002d17561a100341c0391240100e100c5a0103448103007007503c00c0c6103d82c0021a910040105410003070340d0a80921103a20314071808503103940b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800775674 1250 800774424 800774459
    0x230a0315170c0d110d080a02010c0c0b13110d141006180903200c0f010c02090c2505060714031005210601090515190501080606090913030315030804 65
    0x8441e13501c0b0b00240e44a8100e981e10314410700c495a120006454001e086030416003040d8140b180b90a10800854172200351254402c00080c1103180b201941c0c90001c600010400307105400c800550403200c10805041d0048080f11487c40481f542004510054000d44685100d8130024030350b00304180d240c04116400c03011000b4080d0a103444040020764910f400b0003040c00340b01600b500021494906072410941c202c510704130928110100690940000d00d003028040e1003102905030010f182542c021082d000940b000004400110780c0b00800d051042c0c4604080310031000048022200d00c0102c2010400c1e0b90150010414100d040f070f080c5410b00001d4142418005030fa030b10b61080b905029001001198046c040040b0081102d01340215420045074034240c84521610400c2da10b5001c22500540400440d102482c011409840703803404100c0d2481054145034101c6103660400c440d050008400800162095500700a08800c0e6044519201c2942c00020a0300303800300000c004da903414001d080740c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800776924 1250 800775674 800775683
    0xf0307030209010516060b0f0307140f0d1209140d120e0307210c0605071a0619060305190c140d02090901121b06080106230a0315170c0d 60
    0x6032511114a030b8409181d4104100c4a003500c0d001e08030f466003045c512920414034203500502d52203090005005c0402c00b404c4585001e490383c40074040031903843705242103020342c001e80448402c4150302401000180f5601416808540726500c10300c060400c0700311807061032340020b41281c81050501c0d00702d5034181d56420403545132140030070109584040ba240829104d1182d10810245d07036651801401c107045944c0305106110301484520041961803e403841c030007a1000381034843ea50303000000780c5004420700c090710804d2200342e4041806034240d400540a103061182841c03c1c403004000c01c400f0744801c80400d40000d0b001034070051300e582e07121005d0075001d84444005824050b04c0000724a409400b64041e03480c0c2108804400140000005150b00054514006014a5003071403006414414103200e40000c020000c3d031100c03014031941807004018405000d9243c1d079000500d200038003802d100301080c80745182d400d00015081804225012196145201074444040020104485101e25950a89 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800778174 1250 800776924 800776927
    0x10f0303030906060503160e010e130f03090b0f0c06101a0c071707030309061704140c041a0f0d051c0207090603050706080606130302040f020c0a0f03140f03070302090105 75
    0x5c2e90f641c0c24030103104c06035920303040d4500c00f40c03514602e800190740c103a0003940c40107040c00c140401a0a000d22081d21517410120078403800682d8a82125410460790141d9101000440e20544414441c001001c40015100440c1c20503291450002d040894612030300c800100c03080c000030410511000501012640d20003900e052540d119070901d03160050001c0c040c03981e000f041c0140f04140d080f0100c03c01426080c50007202451100d02025003601001d0400f9005007021510010b0202c0c04015203648144d0150080c8585201000000300b02d001d0030320b02900c244041e00c0510031a0074041c0740303c403103190440000e10900c44040e03e601550081952800b085005040001c58184403d004e9440154455002001d0803454403030018045c0c80040c2115200f040100b0008202c25076078a06007041d00e07012600080d1080341244280006d2080d40c5560505000314842c58003071242000c0c074003601d2800b03030303c1c0c01703081c10305040340c2c09007504c50754a4101c05e0034010720101c1c1c0d00b43e2107a409007600e020181401ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800779424 1250 800778174 800778179
    0x150b0f01121d0a0b0106080c04150c290411010e0a0905040c0e010312090603060302090a110c0a0803040b06030d170604020d1a0f10020d1110020f031608010f030303090606 75
    0xc90603c6085071041c1d4039542440010440349500500041c0d10901d2100c00504007401c0002c0403440e00c1c0500c48440c10040540c401070284841000c0300d0080ca10141107028071215564003221b2080c404031403c1d90f43c00c0154400c140d00e94001c80d04407900c0701008052410183c10300105800600c0091300c15036065000e002c01051050380765140718069800341280d40d006d400f460100070a140d034540c121908060a043d0100010b0310f07038010b1150411007004000c511001c3d0b502c8030390500d010f101d83c030304c07020710418a00b4001d002e1b8002c01103010b00d00458090220365108001c1c16660394000810100065241c0a291003002c0034051164002c240103001500d0050034581c0d0409a89600702e5522400a20b581900050700c0c0004c81107401400c241d80c6a01851450381d03000c0c1d182c50621000303000b804500c0c04c581c810040203104915525404400454503107851a0941e401904100e41000c00790b080b000c403042000380100c1c4001e048450f40c5010604250840e58201c0c0901010081180c8007919040f01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800780674 1250 800779424 800779481
    0xb04051905061b0403020d0b090a12090305120f0f070516030605060306071d0409020f100504170309090a1107173001050d03020f030403150b0f0112 65
    0x1103812038016002019103041000c000c4803255500c840840d428a4100801c00050301c91a00c0c208049401c141600c05981d00c0640d07840c00c0c4a000a4000c019842a0802c80c0340d003508081d405081d03a00600480703191803620407600e020b51140c510200c1c0a04028001ca941045840c401440b259104009454a02c40c032907081121020b065001143c0b016110702c100030250800700141d07030303000c0ea55103410071402500110032403c03500000034640c06941c441d2000c030250749580440303507120303e030203084030609149010000340f41d504a03000740d508a07529420041e41c0c0100c00001d69003210002084520316485141c290380040c50303655000c1d81022410300440010508002980d0040c0784614445541e4080404611500c20000018035180c000e103500d50120404d401f07d050b0341502c0059501c000341041600301646041d14210400c0482d100001d00032042104540400c04c980d1013000c1c2c00d02c52554000d007089100020f001c0a10f00003036140300c01082120070368003c24000c400b68061243d06d000d0a545 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800781924 1250 800780674 800780713
    0x61403160b0906250b0915060f01020a0b0c030604050105030f0309130b060a0207091b0c150608100c1b320d03020c0d0c03020d1110020a11120405010c0b0405 69
    0x1107a5010030010705400c05002100200986c0701e40c100380944071000c0214450301001801502d91409a1311424000101341d000300712910480380c00c0300e0000c400c1d26011042c042240c0c000ca03022805282020000595410f00090b04c0481c904098007a506250849042c0300b4560301a070102000ea0340c4403401206691a400d0081142c110260301900c142400d1144180944d5607032403160b100410001c0110020987c050100b200f4941c0c4003441034840024101d549000d8606508044014011000b40c24004940c9608c03a54200358070303448007400c0805020310003502070b00c5070b800034285110954048801d104c10207001448070ba440484681556030080ca010326141c1011060070100e580010701e6014214200558040b240311454420503000a6a40c02900c030f40c1d032214000144149880701c500165070a00001c50306042d1400c046468055044004240c9560f2100c00e110074040c0e02c100481144601c0100d409840c0180c4235080b060000b03075503061482c0c0300180250303454095042000300c04109a034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800783174 1250 800781924 800781967
    0x10201091a06030615060f09060912061806010b04060f030f181103010203100509040f02191e062c0405070e1008090a02120f10061403160b0906 63
    0x484001e51032601da400d0520b400d03809071540440d0204151080941c0c0d55600c111880c0701b090020494a42c1031401c040350b03080c010400b1056100c64190b46200c03d8120000f80b95100700517101d50040390516040416455807001e003d5003903091410001882a80e000d00c0d00390010400b0b42c03030001200072441d0f8501d070454800026000410000c1c035070300018000d00c52100f149d8254101c1c000c519605060f811000c1e0484207204440c003a851040028003444101c20354040307556000b40032030007004400b44108650b220b030750050180da41e124291300c4840902e00c050201c141c40b0151141480c030b800001140b0847d40500700c0b100c400b504400c1010a95807960300500340205501d407104069940e00d0420400c3d03d8040c04400320411441004108054000003030392255030b034050305d180da04404c244013280e0801041c010b01e03100a10074080982604941584903104449540d100c145000074220304040d00c925250304d54442d0064000ca050194440400c000c011101c00103044c0352610385108440021710b003a00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800784424 1250 800783174 800783213
    0xa0f1511090f0a050a090b0111010207050d17060904080d060f09200307021510090c2c0105073e0103050115050d0c05041701150e06010909020901020109 67
    0x101c0c040406040040080540c81411920302c0781c09410f01d00480d00303941c628413540504549a07403841040383d0040700342c0150080100002d40d5141507034100190b5545000172040001041c54180c002c1d110050380c0b80e02d0054500901c05802030304e41752110400d030b40240c40c080c00360740d503115400240d80c80f4481031200100041500801e6680845100000034120b400c100019400100304111500758080b0b40140700b00c84414441c20b05441c0c0c0c00082d4507500c619008207841d070f443c143c0708421032a007111440140d109082d03035412500b402032401d403c2c8141510901d0340800c0d000e00c86040043c4203035030381c1079031044080103200c15420043e006c0d01003004620002d2106d0100c3e4000b511803560b0601a4a0152102c03511301c0c00744a2100000402c180f00d61070742c4411460b60781c41d4011a10b813082084500070406040c176818009d003001040f90003440c4031a058480125aa1800555505605840351250030140c480b200035030704c0c05014101035031141d1583c3c6e0440d56148050400100e4006048008000382c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800785674 1250 800784424 800784427
    0x504081b07050a0b040b040b070302100f02070b09030c030a110109050a0b0a1a090a0e0c090c2205030d1b050304060f023705072c07050c0a0f1511 64
    0x1002d09012424045420030f80e400141003005200c030a00341e00443e806ca80c62030b40580d42c1d40d0160f00707040303050078100001144a42c4c14000900c9188110b03401038403120340940701e000c80c40c5e1142c951295807031007049503103c0300384c00074040444100e02a0550118202c8804004984a0384a0b03031081c0c00d104404200f00c4115400509001c80d1b60001d10641e0400e0954a01d28661064a40f0003d03800040081c2050f0b8966201c260a00c0000c60a102003000088080d100000c40d04100f01c10711580d80141d040042d8030300e00b00c482585051b81c7d00555030210740c1c1c0600607084030108203c089078110390000415903407038100ca5543d80010b070200000c000401183c0d40f842c0c0c1c07283c2d0714a0020304180c00c203807940344001410905000040d04c2a04801103d0001282400c5489018a0410306145141c0e00c200c001501915000e4503030182c1c680c0188402c980e012080034141e8030113500707442500840341111996803140704207200140e0144c0c0d400844900a0580460103500741080c1c106481c81c0c00c0c2000c405190 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800786924 1250 800785674 800785679
    0x2b0924020d05330915190b04051005090603010303141c14090105090c120c030304030602090f030a0b010b0304080f03040302010608010b01091d15152203050a02040504081b07 76
    0x10b1110403000820112814105207064000001c404c0200507040d4034904620f800e04503510381e128a4041c20f100801d0700101d00c95540e40380000000c1e040381c401c0c280a11300703c03c1e200421512032001c860203104001e01c0d131070543c1d003151811526014030741e0003500440000c01205200e041c444181a0100038030641c0030411001c13081d540f4030110703400780140203da810b10707003440403981010a1140b180c1c042074172011200c48482025a01d00707440d00a140d0303094000010003206004180d00189411031003502c040ca401034440082c10750b40c1e1387d84a000740102c60750a005211144000c8000c58120b40504145400c12014015805403544107840c1103000d41c0d9140c0301080129170070700a03103011038000d0814400862a190300b00c88144c40b04422a203c10700020005216191b124031101c501da407019007500031100011071604042c0d401001c400c6c09055460200c130301040300f40a141015a50302074040c0c2104c00040d42404003070324001e0021030303900c441840b00c4c01200503c003500520700004980100fa0722031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800788174 1250 800786924 800786971
    0x30f03060406052d1c0804050915011b020102100f090c08010209060a0e190b0c1005040f120c20040e0c18090709022b0924020d05 57
    0x802c940d201ca4013030032a15840c2c1c0361600700641c1071962074413448010003100c1031000c00240444034507900141d001d503081070300206021040d00a0400d80784140d410141c1d6031944c2c008012880310b02130742c060024080007207050060700c00c005810040c41c0306004503500080c02c02c0b407060130f0710904510300004540d00c0803c1003c1c40040101d100051408000844c903002d04000841c80ca4405c8160031028001c0c1c40c0c1031008151141c0500b0804507400c0c0510800c92511950a2022075100e8010340082e07120321128001080c2a503c1858091903000da00f005c601036441e81c4502e02890203003042010301445007424004121100c0002300401e11111580c541c0c4080141000121b4410a062841682c0f040c0410201a103942032111007402403400c51224664864200d145000c0b40754220716035550020030b80c615421002d07900c296002c006030001c4d240e103405805a000484120042c05017020b00c0b525050348003e01d528012485004108802510301010031550a05581c4141c5000c07030840c81d82c8161100a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800789424 1250 800788174 800788181
    0x51203060f040b060a03110405040203010e06010f03060e04060f1e0f060605160b041e0501020403060605030c0d120210021803150f07030c1b2003010c02150c0c030f030604 75
    0x10011141048143d441102103030203406050600310915507248a03020301ea565401c02d80340103010050040d95250b0710348401801110054411501080c1c4640b04100038902a003c0c074029950040441d01039a540d5803101009410041a00c0c0c148a135504240402d05160800c1c0c0810074500c080040b4205888c01141c40848110b40e00843c2000344c20f201d20708008100801c501810758006e844807916855608081200e1102200d01c1c840c400c6080809a04103c01034001c0e000309c0e40078440411802e41d4400a150300c9002e40c10b50f0a03031003440403004100060a8590248104075984100d56030307641503203e0903040340d00140b040d01c3d181c07680d504c0d024082c0c602007240c01c0320101e00000103005c03410540c58400080d00c01410710020b00d07880750302e5074040c28483d680d003480303035010108403a0800f0050304041c0000d66080301e5032888146d8100c103040107401d050140d40d03003140f803580c001c0c800b0485141418410030300180c440454980704000c2e110140504101411070940303103198141d82c034201602044100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800790674 1250 800789424 800789449
    0x90a150b0306310f1a060d0609030e0d050303010906061b08030408070c0314060c16031b02060a1e020a15090f0206031501020c04060f060c0501060305120306 69
    0x1424200030280505807008165030380c110712205107144449031040c003180c5030941c950a040041030004100703842031180c801d0f2a040c1c954004d101103a0f464400101031a046002140e61541116040301c00ca00007810381c0d40500401380c02841d000c914204178200190740d528480c84213803082d50000c00140682461417042000411340c5003088500b026190200c41c4104000190203000c80d54040005018800b0000c1200c2d0250b5200000b88050f82e103d00d8800300d00018600f42d41c195110384070000d80c0d051010342c101c51440300000c440141c203001035074007100c43ca020700080000040758040740b0307401a107403940900300792030485d21802c89100d10846008012150210038400f19881150701c107000c40c288000c1b841c00c00e42c0505e000f10b070b58074250800746181300a402009410020020402034140f410808490079603609a080d80c00c03607403941c030030082901da076401050001c1140c88010000240600b0b10683e1041c4140000f0030304d0380d542c0e280c0380d0038541200d80303907880c815000040000a103481d1151032003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800791924 1250 800790674 800790713
    0x30e100504020312030702101e0b09061315051203040512031e0d020c0706030b1311122d010f09200c030c060109020d0e07060e01030b0a0e090a 63
    0x4928068000a0399007101040e41c03591311a0000120390401e2080c8150310644584210a122041d060660344210407105105000c85a18084241c2c90350314100000f58000da000810010139120a03207202d400a00a000800b120052200303c001019244c070441c0c2c200f2946a44061512145400d09028080d58091098042a003041004528841450002c0c20751611052031107601c640b4090a070304024841d4119582441c481c100c00020007641c0343d04104100c02c000c6d240e00700e41d05450380340320050354940c0801c992601002d0240a00749989000302c941d108141c60072208210301d105907103c250880003114580048070100040c03061000c10110784004000560041214414407a00041801c02c11004445000d000049420f10710402300261174100d14078034103a5145581d84c2c4081c000a40c00611001c11150604100c8100c5550104120045405644594a010780c034200110f0040c889171000940c80059080301250744e1b8441d840503403054441c000100000f0400e42041c030107516651f40c0c1d109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800793174 1250 800791924 800791931
    0x20d0b040f050414031c02130e0405100b010504050f240408070504061a03041223130902160303050a0609020c060414010209310c02070618060f0503060f0907030e10 72
    0x111b40c4607228948240e00c07032840c0300181c076040d8908842c0c01034100c96000c3c5030f2005c120170a0005028010400b41c1c640d912000c0b040001c0f09040c801528107004912595038440c1080c09540014107102e842092420171449003034006e2002c000c9180300e9504641c07c48505580811021700060405100d0308001e00f0300d07140300c5211014210800d039401d1000410081c06000728031038a404882c0551003006141910130b2492104400d03d0303014000541002c01c04011041c1c1c1c01000041d0b04001e84212079080c0c543c074030203805025070764905801a0801230000409960780e030600050b94429440500002c81600d005040181000d04000711000300107070800810303074410068208680d0314826115003140064502402880c6104100827003603200615124045090402443c4000e901003024030079550552120710400b42c10b0001201164901e00440c0007240d0f1881070150140d001b04051035101e0802405031204840c41f0340852041c07801902e07400c000c42d40300c4901c00715801c42030000c0d4108010411080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800794424 1250 800793174 800793187
    0x12040515090316150b060a0302070605011a0406080c07050a2906030706030b041509061503060608060d06090f110406091103180a0506090c10110a06020d0b040f05041403 74
    0xa5007050445a002403a003c4d040c0c8007120207039003d030013406002070300815803510707014075402c054040d52080310708907a854600000400c181b084070103154046890207550034185070400206652004000e007201d200d1200034020708002850400401003a0351051138561030034036034080403c2c4810111502c100c000c3c1025800c1010b82e8800044540459104d4503020030203000c0c10300420000d0801007070840e190498140040380004140d0030040c111161030482c0014a100081e0440888150f80241e000281e0f40c400420142d181000105811741d00843e000590003080e591071a165452400e002c030358144180780e0301031076854244140801031810900602c00360703080080b161030b103100080c00d043d814400c4070364004880d43d04111f50484564488100c0d00c150402c49585580c4030302c0084003d100e41001c000c041260341c454510b84407501e460340c1c002c090076801560780b803010f03405c2034020018442c1d49940981080c0c0c0c59010700c1c07059900c2500000744c2403e06007000b500781d00c01148003440c16030040051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800795674 1250 800794424 800794447
    0x11060a021b040605120c18040b0127090605011701060303051c0e0f0a120f200115121e0305040e0405100e06061810030201080408120405150903 63
    0x5a1104905005209240c07101c1d000150081c1080d8200c2a0000c3c0c1004400c00d074541700280102d180c0204540c0d02a0106070380b4000d028441084074000d1100001d0b00c01004120682005150903050b41e40e180c40390b030306007003c25000712030424400761240c030b440340010000d811400502c043c84c91005002400b01c241141c6002d03103e8829229a10021300144039983c203c3c6405902ca04070110105c81034815200321100615901d50140b04143c0d160300b15200d40494041c098a840800b0304c1590b21b0740003942d20031040d510041e8074002a00310695484244220303604115020360805000c0c2c601c1c09502640d0181004481141006a1140002054014113012a80000586040701c0184034190840e0b903039407401e03c0c14200403400500740c2130300b0402050204840806c0b02886501c0c2910030407084c0e0480c0003405181081650b002c8102c142c020000e1015500c54078540ba4000d00401ca0145000320801070842100b0313040314240d4098004002010046c1e44010549030041d10020085081c400003a55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800796924 1250 800795674 800795683
    0x1c11030607050f0906070c03050303040c1409010510021203090f0c040501142202040b03040b0f071e02010e0708030a021006050102060a0b01020c09070302030a06050a080d2a0f11060a02 81
    0xd030300700f5440208814125954400072102e11607489094400c106980e850040d0b82d940041c1e40071228083e100402189030b00003001054503440c4000d042c00002d901c0c0105011148141d05050011406000015001402040e001318004d01d5031000620700c0305903101043e41040d01c143c01700d0340704030300703110042004201c452030b8601d540e2412180049203400c40d041941d01c002e01d5151608660340003141c00182e4134240c0d0003031481140144120201a90748041036014514111402d5010540b1140301c09800020800e001e480e1503180e0000259680340b1740c0c001840c05040740e018040c43e0740005040103860354144224070585004c003000b842150304100c0086d460b003400925441245554a084100e01e81c82005542420b0030080c1130101d8908000000501a510848001c0e06041c03c04900180c1414000603400c116000350000e0101007402d04021562802c610b40c210701d030402907002010300742a00000d0b00071414866a89400181020303d001e0000d51900c0c01140e104540c113005901d0426004107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800798174 1250 800796924 800796937
    0xc0b0d0b0d08121f0609091a0901140409080d0e010b100212031b12071b0302030f030c09060a1106061c02040c052b050a05071706030c1c1103060705 65
    0x440324086688005035502e00700c1c00c00c0c6903803800803040480045c4c03c0744c00c0b00756503003a65642c203014813220741941c4402c420600c0303101c5860380115190004020941120080c0440c2d1139004201081c2501c1325151040c0ca50865070050030903a98644503803800080912401c0007078007050320f40090300505030402035155685020000031082d0000002802106003881341022000102102c80e26100c40c00c07140c20210304215404800f1a5410451445148407941d1414400354076900542ca080c0c0c00c00b0f40124240c1001c2c01c0866910010320020f03415960720000b901c105119980c03404d80040c040146180b801c000a8035580c0240348a080010f80d070404400c1c110280c540664000c14422034020b001c480f81d216451003c413140203a10b42c01e00c00440f42000541000340d1160080c803098554140f000c084500503903600001c10346a0b0b82c036a000b0420f074200c40e544040010144c60284d030032000400e60019441441c540581c01400c01c4200300002c00b00c0555074070505900a044d180742003603016142d8450789 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800799424 1250 800798174 800798197
    0x60105011e08190f0b2812020d050601030b071b02011e020a120c060e070b1b0705040c050405090f0603060c16050a1209230103050901090c0b0d0b0d08 66
    0x410303501c03a90700500c3c2507601e50b07241003003c4c05510201a000740039000071588504412400d001c01c01c8480c0140c01d40e0030551800c022031070762904881845011106408036004040c50510380c010810030b000c1c00e40203600842009042d40740c60740c3c0c014003034000340042980704400a014100540d80c01003c1044040c50250881403003205400c00380e24010b03070404007c2c11900c00c400045050b0780d12001c4060468420071050005022a070100c545440507030080c006144411f10800404a024808602e20700a008081d1200d29807503101040c15240440354104c08103400103410021410b014454961080b403030088072259080c0700340081c1d10380074064011423840a01055801d8124051107010065a0f03201d41101c1c0350010900d09040311400b440344000204103403000010300c7c80c507060791003038001c90f1161302e4840150301c20005500038440901010801c1d0740e5140900005400906041d0290495080e0b15480b458100d03410300568660316821742c0981d0301c00d041c040001e207440c6e06403080c200d841e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800800674 1250 800799424 800799437
    0x180f0f030a120b0d03230324060d050c0310060c03020c04390809060906040f032a060b0f15070201050f0a03050109050c0403050d0e030304050409060b03060105011e 72
    0x1d251a040c0940f40c0d40701103e50241280e9051002c058200070f003000c002c9004408404551705402c1d160b0f10751b010444100040100421140c0040e80c61525081c0b0130020041001d800c0004003002c58007110021103010301c18075000000d0281d50b80c01200400000c02c11403511210031400350f030340251030741c000102c0e42d8082c42e02c07158035074603551003846c1c1c41c203100d880713685071480d003041c034420b208080764603420003001141045000c100140004184544107814100041102e5110707642c8190101072900070680170015011586d4520000c2c2443c0340340c00000c8001c0c0d038120039019082603022a50481ca2480c4210000c4c481c040756610b81e40241c2100c141250344e01c6c0d484000900068a0303501c10306040d40c2c90700d0360004106040a4046d070049060300c1c01008208000c0d65081082d103100e00c41c90001509a40c025a0851031061156200c0200c0031400307001c1e0383c203096541c400326042d914031400440b10180ca59201c600c81d800c003044039a006000c00d02e0480070018400da1441c11034841d041341038040026 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800801924 1250 800800674 800800697
    0x17280201020f0c0a211b0510060b070b0903190e0f09040b0f090d0e06280c050609010902010c1502090a030b150d05060a090f050105180f0f030a 63
    0xe5042c2e450700e020094240740c0c0c500f000d51180d42c603034201c400200ca504442c000403062903002c0801d40e24051115403102c3e01c0c850717802c072001d0010191034501140c4c1c5204018940d07140f61300b1400f40c180185822040386454890700e10f8400e0411000a00d03d507005e0303000380241c0341c850000d20014008500d01c3d051026180c0007900c08a41160048004a03400480480031f1008002d403044038544a40040829507130070b615080601d0f51102c41040310072000035605aa00c3c3c5403031400400038001c1c20b8040ca41130a1010b249240c0c01241189450110080f4100b541443d00340003007880030070ba000480c0802005103c82d9036001a101080d03100014008190814541403102d03016030444072214002480c560455640c0d10b001182c10070708940320800d6603800741c98552903040c40c2d40c003041c0942d80075010303000c80d640301040440108268a001d545001409103001e02140e03003840350034041e600c140d0b0361f8014001d102410500d0001c64403490005588031070005800706d1000710544040e5102490f008030140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800803174 1250 800801924 800801927
    0x4150c030f082e030b16020f03090609041e05090d110c0a060f0207080a0507150c022211130306050c0a09030b0601030b061303060b0a0807030209091c09031728 70
    0x103c0d40c100414250701c00b41031210750a5640c0400000e01182c1d42155003840120701d203281c032802a000708617005441481100c0721868590407604101414125143e02c030710880c00c00e001034500c240c03414a4039800082e142149568807030b0050030380c005450000d00903046e03803101182c10404984148400c0180440600f0509482402401c006101e403904503242e0303620a051068807084c0c64418900780c03060340c03050000c8180c000d10450182c0c035001808030113401c4038a00403402c980f1000345504521507550340f20300180c02103180640600400301203035491707450451030800c044500180c0404400c010500400d81c1e019440308039201507079448030001c0c3e01600ea1380c1c01a0301a0841c0c1400c0c43d440100425501c050b04034070030700981204c1c0034240074000035010f5024000005200e0003208045e80205405001500f003019080e0b801038100380840b00081c00b500d142c4010040c01c001070342d00054400c20108140700c0c03414004550604040a010320704454a40106000300ca07110303c8800c404000141000340c10b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800804424 1250 800803174 800803261
    0x90702070f03050f0d031a21011e060605120c091c080a09090507090608100306060803070302010509060c090d03091a0a030623060f04150c030f08 64
    0x8007510203440c20392035200d240039900c80d00d01081c150124070500c0310403041d1602c203003d101500707d260340c40c0b0180c00500c6001e01004620f02e0381a02c695080c2503507000c5140b0003d20078100c0d04141e070a00d425004080c980050f05403202c6501080400c0f10501401c00149581c96049400000300000c1a90341c2c5100d101060034009007000040d005415400103100b84180e180c000c0804541542d070f10340700707942c0305c030324500c11208140d628600240400c0001d1045c8c5004124941d00a80c5c08844900c0726562580d9043c180c034940c2c1c229a805400c003140c1070341010b03024004c1503042522100505180d15240c070b5031750424004c0358201c03031103100c03201d0004040c103004042c1d502c09400121045045100c02054440c1264050b020150000e45024400559155450768100b1210210707090300902c2d0340d9050030400f840d00044980d4402c2c100412000406052814504141075159144d00e19040080e0802900320701a00030013900b0701960004000b41c203103405c40c03081400c03420280b5480c5001d07010204052007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800805674 1250 800804424 800804429
    0xe0c3a120806032b050714030f250f080f0904050a1a01080115080907090c18060c0b040204021c0212010302030d1706010518040c0c0b06040b0f09070207 67
    0x5000804001050380d004000707600c50001902160610700b15080e40451665203c00107a100d0807036100e000e10900c2c03140004142c61801540d2841c401406802c3d59070456201080714102103400080c100e440380304c07d142040340106840c000407608500c40d20380c500f400445220040c805400082ea4114148040c41a1540791001400402c6503203000c10749480141580c4490440c00300352001c00036090340c03040034000d044c2c41c044880600c0c0c80172021010740d000c000141401046000d40f52022991004500c00c5c10b401c1ea14565461049040c401022201c0b00080c0d0070040c03c001944001c075010900c0e442c90282c00990540e00142e94020400c003840214029a0314882c000317000092200f03450710540681c5050700d000300c0641311140c3c01e10300190340caa22511080c6407544c0469000a603158000c0e00a01280500208005540700c0c0280008080303d490b04264400b0071070b009888e2060004400307000e68045400d9908203c066401400100b5003c0390a40b4035214610480000d07891a1003030091000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800806924 1250 800805674 800805683
    0x15060f0103140a050a1104050f090403020106170102180901031e02030705120f010606030507021b010c150f0c0f2102090306010e07030c0c0c0b03040320010e0c3a 71
    0x86504280010744003030001982c051224030700b04241404035006c02c008440441e0b000400d041240300c1044140145400010415019550303514400580c000c1e880b041100070740342107030005940d076889071003c081c1c029030345181c0b50045240500510020b54105400400200c00e82c035440007405c01440082d1411900750030080d00070f22168603014074071310002045584051100020311035142c45d4501182143d03000c4605400503844000940110802090969206107040c544207070b0780d401c96103d038400c01c0c48450400025607640ca1010802480a2189955031212890541c0c64091030440c0100315558201044100c88060740081c800700641c2e60448014500c0a419603900790ba44000549076420101d442c040400d05042c1d4100c0700901c1100c0c050a211b5120100d0103d450803c0050280707500018805c80c2440300d00059502038900440603001843c0d40700002140143c1d80c18005801c0c20b64464000b4007403040d20600d0710703014403004e140403d2601464000707803503488d428901540c20342c00088040d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800808174 1250 800806924 800806961
    0x50d02041a10030605030709051e0a0902100e01021606081f031203051b090a151b0b01060f05030f01121703010e012301021005061219021215060f0103 66
    0x30480d0781c064000d1011108224260358882c8d40c1d421080081e950106da0b048100c603900d005280c8001c07030090103160099081840020344501560114140708144e40541010900c001c2c915040c56074104a804030140310004071104c680d10b0070101402200004c0c1010038409450164262415595072185004540001480c900c0d40c078035940203030080c01c0a44590648080c05110b003800801050100c0329a0390014040c00e41561078028035103924420000414100018854125044410402403050090043c08100f145500d0002c0280c019000484040c040c8902842013002c103090410072141100d14203102030011413900d00c0d0446181c9015510003d411401000218140345181c0c06681652804103c50700961081c030203400090386003400c5280183c1c40b40d40c015140c00d206810240e001074018180300303c0005c0c41181c0320b0a001c0e035444c588942d000c0c195081800e6141019009840d0300480c2d0141c0b04c000080c1c1010108150300a02882c02600e9042e01c1c2c1c001640b103070f4000e0f40c034400e0404000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800809424 1250 800808174 800808199
    0xe0a031a0106020303010609290304060605041a010806040e070305030705030408060612030d11130909210903080304150e0307050d030e0a0209060d05070602030c1501050d02041a 78
    0x2002034a4810881036a03004000d000402e50398000402c41c1e05a5681d61501004e01c1e01d0400001c2e1020451082c010384006090381c00c1400480c181c0103507014620a85010851505080c10b22003143d1241809000d01254040d0400306070343c01ca080c01d03421084c26140445c02c001d0184805180410603070005007540320010750351081c440084041d00c01c4e039420205880b81a00c1e07502c1000312802c1e20b0320301d20307440e900100a1590114103641c004c01c24a216207a41e03078100f11610844a01c81000e540c404101251260700c402c017001008400003114640811051203502e030038070300007441c9000c2404002c4c00703003800102240910031041c1581940c0346084000707001d04415240b0f11512600300500c00c94840c4240c50421004500900a045610420b1001000da5038055000c008100d04e0140405800c80211038118002c603e087c4030f500041c10341500155580c50120140300d1402c004440c12121084100c2d00611082d40c441e4003071544141c04940100c0e6446c2d030182d0412801c141c6806561740800c010701d00c1d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800810674 1250 800809424 800809433
    0x8130f050a1a1f0b0d18080d06030b01050402180d051002070309030219030506160908060a0923030a03050a0219020606210a0219031a060f0409050c010f0e0a03 70
    0x140e03118444031071040d4400c50860b0f1115440d41064000c603070340044144507484c50680c0c04d5000038407112085414410180442d181c1d0859035002e901001c0110ba00e501003401480584840c850051801f40d4003146000c2ca0210b070581882c8480c40782d20b205040b102c51040c00d00c030080004503002380c03044908641c1d8a5040c0740103442941d0900c0124041c0207180c0c03400086441d62040d00d0200c941003000f4000951300c0352040040c82e10050f40260074050480000306000c80100151840f0300e10603030000500b0b20780d5041103285240000520308a00d858040c058102680200a940b6100e4032818041003584515500d003010b8052100103617400341c0c0301c0c581000e060382c0c000ba03d1802040140c4000048418115600e043e90641041000c3e05920001d14100103003004500400078820480d8a41902601d91351501032107182c207031010001d0b02c12001072050f0352a09000d9401c070030360100c1b0204280d81c0544d440700e88034041c4440190501030025410711000303000703489140704c9080090084008640301e281 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800811924 1250 800810674 800810723
    0x40b030c04031104090302060711030d050901060905010f0807061809050f0a111615060e0a09020114160b0c040909050a1104060302060f2101030f110108130f050a 71
    0x200307032900280f00840112a0425100ba8207000e0381540c098911580c070b460007564440c1d1900e070408550b100411a14035614038510134240100010310021800030710380303260380c0c0c1030703c40c1a080511a2020241704004045c00011480c0403503c1c0750a1444545250080140ea98042c035404485558180400c02c509100000b520030f20800c40e2080400ca480c0078102251514000c82e203103c1d844017101c02d508404a98211001030001258480c081000ca0320741c030b1003c605400903034040c046280c503411003030119030700814103089142c803003032602d800c001780042e1424501d0041d4201901003141207003c01c90b4111040102c4001c0d1002d81c1c400e00580c0b0061a0040e41c0310040702e03082c4c990900d8060101d0051410740107000840c1e400404032801e01144210120381075010019400c448042100c1d0600d854503400c13007480c02180160001c0400c482d940c20035100e1040b803400c1050400c52402c08100c0340f00300610310f11710140c2e0407440e007000c90034951514918241002c10302070b012a0b040041201040031041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800813174 1250 800811924 800811929
    0x80402010f0302030108070e060411070b0117030711120a060c0207090b090f01031b1a040503011d12160b040827060d0e0118080316020708070605090105040b030c04 72
    0xd031900c05809281600b1400c81c0820300505405400011041100259901c2c4c40303904160010000601810740f0134440d622a4032450b000c80d0b002d0b480ca80100800c40e500720102c050711151001071454020207a48403020f4a035050143e900c207650404000c00c4600c0c3c100401101e0300c0e8040010801140090000ba549030400c0c400c0b0190f039810080a240641094018036005144410500303030240d007541c0d6640140c03841e000390921800d0f01d0540018024440c0381d044056205256040e6a60798245002e00d0b09440d980e000078482c06401400340021414001a20300300030703940b0284c69440b4030a030300ca06d501d08000e440c0c1c00b0b09807181e62001d000030301c499800244140c2580c0000181e4209100040d540300442d0240501e034090f01c1400a107040c284650460032004130041300024060307200314005940d9140c174000a660796400482013060325201c00810400d04481400101606403410300e25aa030751001e400750404020010840b106e05901401c203035070107090000d10072500c0b468a222000c40b03d80062 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800814424 1250 800813174 800813177
    0x924060108060405041e14011a0f0f0d0803040609060c051207050f0f030c04080c010801180f0e0303070e030709090809060711091306050109020a0507120e030a1b0b03070c120e0402040608040201 85
    0x9c0c008969095510b40500c3e0098000d815400006c3c0c44034204000300c41013403440f070b070002600d80090300014590001944658402e940001e844c040c1c40c1800400c8503a1240b280050045c01c005000448038400c280c15407000c82071820550380c151042e1446801d0040020803002002e006c010300c05400303106005001590280707000c407001c10b41c10700011590180c0c01e200c0c10706640241180c0340704aa84035001482040c0c50014049040d10310410766a145a1044034154000b480c20303c2180c10924041c0402070081c200d641091101d2001901c401e92144590b1001c948103a20004c0c0ea6804c01000385184880d08400803c61221b601e010302d8045168190007604641d06890f010001c141402c05100365240c141c071556a607410032210780d5030f100e003580c507402910040c045503200c019800d0307504102c101042031046c440c0040346201c1c010596108401500004079201090081011051740034100f1b102e050b400c4088070186000024041e02c44502e42102d15170414000540800c2c010b800c2800280254801e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800815674 1250 800814424 800814431
    0x20c42060f030a0c0b0c071502060420010504050d020406050d21050a050414040605040204090b0307090e060601050a03200309100b0109050d02060d050924060108060405041e1401 78
    0x508101030320350f8001d140081c0701c250b0540007170002da00e051000c0c2044503065022642e0345a102d1740319103002602c00091900586c800d0f4104070410100803695003418002d07828a0b0350b0901a40006011400b403401241c2c000e00241416106558032504080001d200c080d140c94400b90f401e040c000d14080354918420307418080c28a46810440c801c0301202d410380710b030742c1c0e64030704090400e98a04c4107450301c4005030794055143c074000316072940c4906c0100001c100500300014581601c2040c942040ca00d9803103070804603d0000c00081030b90000c244c85074000424a00341d95580080b82c000e030003d00106000c0c1058a0a56000c100c1c0c2c014980c3c001c5005607480c100322807070f0000e0100c03c1426201c559080900040400c1030401441c02c11a42a2072180e100808203400c280c40d110b031880444008448031200ca074044001100401480a06408084c1c003d10381d4031158a81003002a20700c0d0f0004c1c204601403640c427000039041c000307040d16070112084180404984500302e402c00c58614004101d0503074480d480c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800816924 1250 800815674 800815699
    0xa0c050424020613021005031e160f020714191a09010314150405071403040804030204050105030727091407060905061c15120c140103020c4206 63
    0x1501c0018200c44c2c3e8010902c02c5807420350041100c203074201070200c0500c2010f440000d038540d00310305280c0744152801c0f038000c07412a00c11070000f007248603050452810741d040600d05222400d0700035440505108161803040c0c46042e0b2814044440c5010b40c0544100c13080180030500740c0e40400b0040c940d0072003d982c18001c410880ea01e81c414103c090741c00130304040004030a5056820b0980040d0b41c0214681030035061b540303106607203010541c0112000c9402120001e0300f4002c501e40fa200d8107000d81000c0e8000d00d511418401e02c042c2406d560451103240f40d95110b104504090290844881c442e446900074408249250b243c690700d00d101c0c0914000303e501c4500205943c01e044080e1455140c0084855035004105003850b0010904550008480d18a5403404180361003030300f99542e01c080c031968a10702e4107880e251183c002c01c011000000d0405004001d140c0e640080001c404403a02c1c881100f0034507070420039481e1a02400342c28190030102c6102c6c80341d151003440f6030b00340703902c581c00555900400f8072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800818174 1250 800816924 800816941
    0x801091110022104080703030804051203010b0714070906230f0f120a14030d0605010f050a0e0102151e0f04050a03111002040f080c0a08060a0c0504240206 68
    0x1240c000a00603840078070f150142d400301c06110a02e41c610054020b180a464000c0c06060030041d410680104002200384410814104103052007221402011801e650612903440e81611075000054008903030320400d844070801c14081b500082c81e8008041080c90350715280030141c02484100030307000c201d540100c03415601b00b500300032100020007412080c611901e0410003040260309040d80c0154824070190000013040c012401d901548a80003d540710050406418151100c40d0000d904000700701040c10100741e044416103400e99554107144446910f03400040385030078400009020361800e60428014170401c608056410350301c1882c80b84030f1a98134030600703130002072040e5001441d81d03105500c40c0300402d2140f05102e68106076041540c2e08890300d800d50030181c0e0003942040c80104e20f00703281000082c2c010000200c480c6010b40c2c2e03178510180b40c258002e403100310003091403140c035895800c102d204030b1041d42140e02a015411240094220030b0f40540c004140000e404009886218042a030b1072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800819424 1250 800818174 800818189
    0x50109050603010c110d230703110d09060e061c050a06080d020a0b0610170a1a09040b0a0209030a02120102030702061807120f020301090614060a080709111308010911 73
    0xd01c124001851013030700b00c0004035500014602084100001f80380507646441084000340581802955010801c040c84200d290800c9040d19040c07041c414004000c10102d50040341415040b00204c1e044c980342d1160034020380c1015000050701414074601000c100f050900c590141c000d591800040b206038061300d0310305070fa9400700140701405641c1d05e980000c940b884d142c004140c00348607078602039103082c00c1001194140e450907555034049070307141c0c01000da2001481c00c840c09002c0d400c4a40e080a42400c2d1a02c00c054000509502e2005800003004141a18104501305a10740d0152241c0e20038410030b80c21a000390000c1c0e40650050003080c0125820105615080c0c0504c0040000ba200c3d031403420b01601440c4000140817501071100a4210008d07a40a10a0721030031070241320b02080030800000c4184118000400c030790701c5500003040c20710401e0400104582910544400040c0200182c410000386006080b40c80c0052400340d0808295018103402140003248240c10003e0007209020400029 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 800820674 1250 800819424 800819447
    0x90a0c09020f071b0308270f1e041104030b09010f0b031b0118030803060103050c0a0914130c1728150902040b071403070b28050109050603010c 63
    0xb1010140b02610208451006808404418104001240d50340c1c0da030b00ca859410559440418120140703116409001d0784c81070504484040354810b81d140c50340340000f00003140700144c083d034400003544c5400c1e4503240d503800301c00d001c240700f80d0141c0c43e03e90b40e2030004542c000880f018070385035080c600d001ca40c0960900550301d42000c020060180c80c01e500919000d00c2000140303950400c040080c0d4030140c90302d000d4500024601600300030b656417514400150583e20041c160742d40700042040807007003240c4d101417002e0549481030020300301824030b280003e07501c0000002c45400a03180600440a540e0080442d0b8944012030030802c90030f903120340103030011800b95005601800380e03814400520480b07943c05040001440c01c8855003560702c8440c0302089070001d42150141040008101061110400902140807070030402589400c2d201d544055980c00d02500101c00ea070270400840d481407580c0b17248411850301001c401c22031580d40740581c00252005480d064000d5181000c0304104030310410304480c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 800821924 1250 800820674 800820697
    0x6160213090519060b060a030903020c010906200a0215040e01060c050a111201060e10090207150e1c0309030e0904050d0f050403080d0203040b10030c120602070b090a0c0902 76
    0x4001c0300100c080f0710300110444013100c03015500d10440340d540c1c1e00e074005415000742e681d8002555940910b0080d15160071658040e042c44404103007041990b0340030714003616030002a0081e80e1858410b465003032601c20802c100a502c2078035488050091b8100300c014104503a03901410baa21a40c0e10780051301d6205c1818009031040e0016123410000c07c0100c0c02040f040710010700025030485800401900711040794010356007141040050003115801c4881c044054195210704601c0d010a40c0d40d1414800d4000d1075201401d41c94200009004109100c03034200703007902c0c8140d034600007504000200100310400c0c0840c040741d000200030401c0d051110110303100c2e0360b01500800c11104111019600b18604481070010810300b000040005101071016241800f48844056224102850030048000b00100031001c3c0109680d0700700085880090482c040303401d91854802e0480305414018003a125000d406004d8860348000c1c014400030011300490882d01646043d03000c20b40f10108042030340b04d041039080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 800823174 1250 800821924 800821933
    0x6051b03060405041a0901061505210c130815070f050d1d010903031512020303070b1b03011d070e0117090a06051f09020306210705061602130905 64
    0xc4a60926612403a001401341841075101c0341c83c00003001c0416401c40d440b21b4940d46848040000821078446c0ba6100502400c002e410000c0c0c1015500000200282d0210401e504002042c0c01a02c90320464013003280e99101c9131001600c0d034841c240d0320b8450200143c60001120300044005206101d500d600e00c4696840382d15003d0043c424101510340c1e203441007550b2151690803403401c8001d124400101e031003910007045115119180d03070104121940104400d1055411020050f6004800c9a00940d440549040d09464250421111f060b4002000c07100420000002c20a6607088650b000b000d43c03a003081500d81c0d42c48980840e50414030074545800f18404406142000c450070b03c15640c0039001c8001c840000e42c00391583e105a4900b90740354400c1e1300050003003070a09042c0350315200260501c810250710303604091022030f034803403806080f1003090707140081c80310018071060180000a1400405040e02d03080308455a000c08220017800701c0c0b007071040d4a56422004810301400c0c260980080240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 800824424 1250 800823174 800823181
    0x103021f030e160302010306140105040b0318071d150901360b01021504030512060f09240d0b010b0a1e0c151401060e010e0d080706051b03 61
    0x403802400005030210906498510311194080d00704407960219110300042c44030b0500c2c5000140884080d038214104800030300c075400e003031039800c01c0481d0b04441d40342024aa40b030780c444141511901c0a991240c1d802c0c0114030000a58800700b42007031002d44c000760f0440250b500e9030800c19031030084012083ea00011090f00410105c490800c502502c0201d11840f240d0364140c2e05072050400055500c54040ca0780d40700c68000c0156410804040390056642d400c00681c18035440281c031901800d551449260500300004502c0c4d100c08400c203807046800f40c020000ca00b414142290320040c1036143d100620b661008418480c505086019006a0080c2c421b2000c3d13400e0041d0700d503460344001d40407020700c2448140300c07203c031032140360140001c510350b0b071123001c000c010f03207081c80014803080c01d038100c458100300195800600c42004281100c80030706140403d4002c07000141c1c0c14107800d480191b402400702010303130140030b8400011f000da18825501000325940300002c00d4025104034004203078a507030a0000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 800825674 1250 800824424 800824459
    0xe0708040f03051e030103140c18041e060911040e03071515030b0411010e0901061b02032404060e0a080a03020c01060e0c0a0f020f0d0305041103120406021203010302 73
    0x34840b40566680303440c104e03088843c0e4460070390300a9000302c810002091042c9544102801a030f01200002c0754400745405681c0005000580080c00c00380110410f41e52400c80090030141ca003070003a6004d10280301d0100b0070b0030421003400c881ca0006008030300380310440000f2240030040300e010544c41115680d0200301071351106c009040074250035403100c04201e00031000c10701a10b801c6100d58843c2030501181d4401100041620818140142c00f0764414401031140340e40013600b251b89000d4102d407504038017402d400082c1c5486100015003c8120b08500f05580000450b641e56100d039001c1c840c1031021201200c2c0c0b50350780c2da04804015037011800d00481101c07501c13903001080400b502c0d8002080c02c540fa0300c20300b103003914195500003075000005501440c160300320f01801c9020f5402d0020b003e490521100385c5403125543d030f008004050b51180000c0800066410131804101d01404031550455903a0405529600074000c2e000940b052504025400410404803030690f58064030040543c03072002d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 800826924 1250 800825674 800825677
    0x9010b131a04090612030207090504080a030c120608010c02060903040305060c0c030405060a032f030a23090303040311070b04060311090306070801050f04050c122e0e0708040f0305 79
    0x22500d2440002c000002d0904120301525001c2c107058500c0000003811494080d02d444015803041d80420b00708000c00003c100500142c074120344440c1404100300c106140c084404400f01080f403c0294075140d801b0032500310550080300c11200a808550503030300e4035200c16589004030b2000504590003000056249a040c9001c1c2002c100d0410881c0d003000d40fa10001041a00040810390000760b60743e0405054074202d0300c221489140484000640e43c0740700b03502450512000f40320035982625040d41b2001e41c25441000e00c20540d0920392240c1070704040c18140d07280c1c4d00a80f800c0e000a4655107182100d103e000c00e604080380c048540c5903140c40c1c5042c0b1b01f60f01070a4103e40c3c1c81454001800040043d0b102440090301c1000d007561440c06c150306043c1008000c020a04005000e80e01e044200580140c860b82110016540003210710b10a54802500d086100580e01c02d2000f0109910b0300f4210300000c9034090003d859800ca1100302a40d610502210740001c00c0f50003410b41d1081c00402c0000c00d00950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 800828174 1250 800826924 800826959
    0x30e0a02041d1203060f0103090c06080622020c0606120d14070803100f08010e0304050f03070803040e100e0c0a030504140d0c06050108060402130c0302071e0209010b13 74
    0x1080b60b110300c014455102d0a0000400400d000000c0002c00c2000c41c0c42d2189141c840f0b50000d08041141d02c20584605105e0290f6008040500000f900807800580d01e1285902c3c2030041c403c880c031140040801080080e40103001c00d5200c1d40b09043c042001450005c403010403003064203004141c03041401d54125603482c50b501c0e00161307003d0704101c0ca42c0030508140007144a540c40100f0300380c0480c54900303498000c1e00507030300c9454140d150410450f07207001e0102c221821100c0c12031b07500c9184030381080000e040c80e16641c0302844610001800166445487e080544541440d005010616035101c1c0c0c6440020011500044068401c006111003140240d1044e90040d000307442244c0207002069285290030045011301d000320300b210b001e82e004c00001c2e0203154090003407003000c0e0040d800c0643c04034035410300500d100300c030803921011042480e40c031a6040d42c1a054006e1055441e050b0600b04142c0e883c24104410ba000701401400032801034888412030f960401d04036564a5036910303000d82800c0c6205180c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 800829424 1250 800828174 800828201
    0x90f0314070803041b0b04360504050607180f050402071b260c0a0b070f1b05040e01060506030a0e0a050604060507080703060302010e0d062004060f030e0a0204 70
    0x500c0418040703400b50020310310070f038420002d0364000300102171300c1d90003084c4a40c0114092a005c00080c84540301940e0000550001c0010f00e8403090783c1980c2c0344e12076034921180c41300e10514203000c000030700c0030001340d20740203101c5a01e4203407140c0311034018400e403005540503034180500e81080070415802c5c03941c01004000c1c01070052041c401c1400240c10030001042d0720001d03580381c0080c0110b0341d02140d00c82904015400d07a0041203d40c6504010a42000041c4111466114080385200a1241c03440410007480d6100e0317803090342554000c8004600c0031842c0500303030049141a00140c14840148900d07000d40308014500d80c00c550b244101711000e02018000200386025210007000003580c01c01075031b400b880c401e807000f185c0c0b4600000d00074080300006098404050900b20300f000942d8002c101920001c0c426648440aa100c80c200140904612074085880300749010100f54602c500d1400303802900d805951b2040c852042d481701318181d450f18155844590060340e01c0c00c0052505c1c1c4c0c803800c51f0040304e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 800830674 1250 800829424 800829427
    0x181b0c2612090a030c15090b1005010e060301050f01110f010623061c0b0f1302030406141303140f1b0c061e1b0303070201020a02160e0403120b100c0203070504090f0314 74
    0x540c8d901080c0007000d42c0d00550201c182c0300c1c24030186da040505024099010342d0802d04542c90180028a8440d8900119062001d5080741c00f03042203091224045102070203000b840305ca940d031080300c1480030071604c5040038036078001094002843e141048a00c0034081c0c14480303070346681c800c102c44024049050b0702540b01d08440c0501c01d49440c2d201640d800d800301240011389906e010b040000554180801811070720801c8002c1040c0041c2003500d03002e0807034041c039010981e8543d8440c0c03160710740b240341c104040c12070b808501003130707103140400c182200305d18102e09450b070700083c40c014025240210001041d00d003443c2c0107030554035507181c4007910704280280c40c1c00b104451007012a0341035134000c1d89c540700180d400103035004485404108a9001170740b60f90280030840c1c907104100d10b03e000003034001402c00c0b03030210140b4031076103036071300164007481c0014440e034150300344640090802c50303038103008034000c2c0240400000c003031070503108032140d5941115451011005554040710b19850413030004000d50320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 800831924 1250 800830674 800830691
    0x32410030b071421040c090504020d030c030219050c01030e0102041202120c0d0305040f060212030a02030709031211010e0d0915031806020301181b0c2612090a030c15 73
    0xa031303860200841e48042c1411200e9003418100f14003a030403a42c20151055003490705100045c1c0302c45083d24075450709403520807041c42d11071400703e003806510451072903001c00111401c03052040c082203410103400240c80c200000320b41220355600342c1c01588031300c545008a040d00d100c05406c041520455800d0b200003682c00d145146000924200c03180203040c0c00107007001c1000c0c04850005098a80600100d000404c266039611000005606c00100a6070101d900400410245800f403070402d800341d5070149484003080c00801340200f007200c0440b818401c40d820240c08061050021070304580001c80d90f5a00c03440b190410f00c001000c0108a003107a400c050303031400302c2c071a8041c15950349020315105400160383ca51400204c1c44030b81800082c00040700d441c0911403c10511003034003a01034400780e801d190b11201c416051210040f20710301900c044203a41d1070000e0040b900310078000c203092140d160240042d40c88003101c42d5074801c111074004010410324040140800d040c0781100842000180c0b01281030346 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 800833174 1250 800831924 800831947
    0x12030c07090b031e0c0f03030c0708031312050c09071106010b1b0c01090905061c06050601090605040303050a140706021308010b01030b0916020309032410030b0714 72
    0x3185540101107903582c81003501018030703083c0402c0168003061403070b502e02c4495220085450b600c402d105584204440400801680c40c01c5c810384415041c4801585c400315990312015840381d2125008100541c0d000801040401d2410300241803203401800400d9042c10440c107006244002074510400c1c0058458a804403540c00c02120340a004c261501d1619a080008085c41025000340690700d541c11144a030b40e05642d01044000451701404030215441d204ca50102d200d003401c00c0c052201c1683c052842d03409200701600501d00405081e1b80c1d1440480d95040111440d0083d400b0050010700d040222403842c5204101c008001d07451740c004203282030044da8481e0201c4e4480c0c07005170380383e0080c02410480d4076009c0c403500140721005c0c02c2c180b1010804c140000d050311401008081312340c11a0030900e403154403c0040d03c079a08000780803203441140c2c41541d115504880106081c3c1c42201600240204003084c003201c0450ba030180c0681510303203030070a0503180001d00c01c40502080d40300b4481420101d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 800834424 1250 800833174 800833183
    0x11040e06011509140f0d110d03051209030304020d08030709170d08060a4b09050603010902010c02010e15040618050a0605030723280f020c12030c 64
    0xd19000400c10b030304041041d80505000441d6008042002080c4940001c58903410a1404c4e207120840c3e03846481072552031b0001e8001c04d003541e00707034020902201000070503400800500100d0350550850b07001d035a510b01030a0344c92000311030003500508001101e0000a24900203107400170362505001e4034107620b41c0c1110150f10f04161030212554009c00c2181c5817540c1140d84141c10900a58882c01050300346901c090b804817140482c401407200c4200b00040d41c070100d605841c40c1048181c0240c0d007070040d0001e09842000c05000e9110b0151074203000c50030034035051007101c40113541a19001c29007015038005403529031802d000b02d45c1141c4144001002c852000c0000d0015150a480b00c440300728071512007856250140d00500e010344040a414000030703030002c040d03960001d0f81c5c2c42c00e0303070000450f0b100400f110b842c002e0b00444580c00104040001ca0082514548560300d4206003030414a040c980449018006010b01d001603002142c1d401c0d0700342040e2481e07140c01e0112a04503407505c1c0302030f6030440c41c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 800835674 1250 800834424 800834429
    0x70f061406090a140601050f0f04090e061e01121406070206090115030209150a091a040b180109020306043905070b130c2301080604021611040e0601 65
    0x20400d080003005081c1c50715242d580d800240148041040d10800c40c0d86100200d006480386060000c0440e03c1c00a45506400300c809009003203074119100c0b65030f9070901014103600e07a601c11283c080e440015100c7d020103441851a051400700310046a445c014484148000100095818505c51004a000e0007400c00a4501404d0390740c1c001c21051800c81d45180c2122420801400d61300c1d685030040000d642d0300040c80d030700600c144078807101e50107485002480c151140d42c41131169504043c030129031102e079104046681c002c00e40701400b04118400400ca8100c1e0310759500c0160203500070061003607602c254040e6a0005029000045903842c10f80760000d03c00030381510130707250f10950300d80c401d1269565034001055049070070010304100301c1e90b81d5a200600000d140707003c0900e20402ca6014049a400c6000c008c102e039954902218a00e0600c113506010301c2c1701001c0c0800c03030502c08111030341054821a00c800580341005400101d241c0d8420340d5803201108080d90068440303440015200051016a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 800836924 1250 800835674 800835701
    0x3080f210f01080d080a05070e090112060605060a1704030339050a052b050906060102010615091a0403080408060912070201540803090312070f06 64
    0x11480c103603042010514050704501d5440c0c01807100d410f02103400010360b90300b000440a0120b166234504d5401c40f5046030030a0b8031a0f02c007041c100005019150b40300d04601103402880e090041d40d0300d030418009584a210301301c1c1e00103000903644071010000c0d2080f81d0341040c441c1c0703404035084c0a021481e0003d0303c1101061401507400100c5002000c0e410608450f900341039003011410b100b1410005070640c0a1100498883c1c5110418100c610701104016420000034110402c00ca040494010741c1d1520115102d501540c646400882c3c000300086040014415688d41c0064031030030a110001355500203081c40c2e4090340c09000c0480003614070300180000c0c0c60700740010003141c81c1030700040707203050581c0c2a0005265410441c03000980d0380203150b28190301c0c9242c00701d60f12800e4048040181c010707031075101c094a0300d00c1d5104001c40807001c402c21000368103840750700241902c498410351030f4804c5120480d80b5501002c0703000a040e04480c06403030f03524001e1042d0310b500e009030340340c1805440d64042640e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 800838174 1250 800836924 800836987
    0x60216050907180b0405130515090702030f070f12210e1c0305060a0f0e0a050702030702040f06152a051c0936020f04120f0209070f0903080f 62
    0x2056042c51f000a140d02c000d100000d0081e82450039140f8a002c1c03440358000d0080303641c02d0000741058020801c9030f41e0881a00c030350360f517a80303440e00388000081c080d0542141d614080c85a80d22500d4814120402c40c040e5040ca00707134042d1640032519005104540440c0c5003030141030000321400e183c2c40b00d451069680c0d900d01050514000041000350009600001d52644850303509014040b00c4440c0039a01221003040084e02d078880031010f916501a80703500075405414a0f803e1380f07028219402810440c0c100e0241c000c3c08420115043d42c1d20401d101d0b14080d801002c40015030804484480c0c1c000303141c090f10031b9410810302c06820092060b001c0740c0783d03c0030500814040084d102001980c0706012010303a1754075418032610182040e030b030160900c050041500410104914411300084400a200038601c01d50710f040c0b641307008091040807503000c0c0c0c86044c0c9030001807446405110f03100c00c817a0032907555100b21400d65071151a1a0041176031141807c03070501203d1000702801d2842000d181d46130304840b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 800839424 1250 800838174 800838179
    0x7050d030c020a030e040906090b0907051c020d060c050f1b0c01090302010807030504060605181902131503020433030612080c010207050a0f0c060216050907180b04 72
    0x340940300300c040160110351112440c50046580700a014000c00d03803c6401141c0480c09040090180000761006482410200306014485500288400031124107403900d510b4010b40c200920311032011214081d400140e9121590700159550788148150f007130504155080c5104051030303248940002005119004444200d54029035040180b103001c904246007885081d0f00b107500082c110a400703840c200a042e1110042020040c10707402c0035000d0440500080d0501c20903080c1240d40300c0302901c0101c0e82d80c1c0203c200c401002624001c442c2007003002000500850303d4203043c1240b00341c80450803801c01d0303428040881d42080a000143d100400701001e18850003640d00404142c103440780c0034005140c0340c06c2080204015850354107507041c0d004007455032191038528202d40680b2640100070601d00540b00b5240c00c120403c4500da425900440410381900c0e00e072542a40e07600e220109009002e0949032080041d0718014403a55800080c07032502404040c0f2182007510040a2601f00ea9600a000b290a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 800840674 1250 800839424 800839427
    0x1210207210c0302122a0f0f030405010e09060d03080a090c03031e030501082a15270a120303140f06040c020606060f0708070f030822030f030c021207050d 68
    0x2500d5600402812161034182042c1c07034401e00b044480c03c5040d05500205409000c820140007040d65640811f083c0c3d00700124441d4515100c0d8071500805000c14008006911241852200b8a10500c4080c140ca070307020703a180c2c5040d2000040201100c449503141c0a6020000c2d0311300502c000114881c1d07c80070454401c00f007608210400c081601e60806240078010071108078000b9800390002c0c003500301c161210b2940d0500380001c54075640b01a41042c8094414034044070440000c0c40b03401194403d0b00c082c4070003030001c0405220b081c106158011007241051010001a080355641d0724801e08002074003608006c0c86200381ea1084032403005250070401042800d00f094014000030044600c068403d034600400068440d005046400f502c110780810f40108000296084030511500018004200403561030018070f940400c403003c0300903401e800c00308480102d028042c200b50b0303030341612180081c005165080340100b15204405c002c52255210704c0c1e00041694008000d0140501c003c6e24003c00303034000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 800841924 1250 800840674 800840683
    0x5030f0c0706091d0402091b040f0e06103005040309031103150414010e060c2203120e1912020f0a030b180c040c02030a0201050601210207210c0302 65
    0x125020b0401303100e2800c1c07419044900c0350710a03411074250801c1d4481007004501201030700454194141c0015000c10101058a040d4003211808055400b141d5904418426510b940140041c04110720458400c0c0284c0031030f813030050400038200501180c580c06a810020381300c2c180d0b42500403030400c00c0b051003031205180d02090701c08429002032100603134154030302402d03060090026200c1040700b800d4500c1d4443c04e41001071800340c040c0858840d410130001c100e281d42c1c0400d0341881030110400b201c501d00711a2040201c100c4e60000400b400d8038400c003d09907244a40c40e400c01e980410040100010f40d0450142c40001d002201803d0042c1d611510502011b404c10320380181c81110040700420003e00180030761540220030181c940d101107400c1703030183e1420f028480910b034050b091604100c48158000301034a41003100354001c2c48a03840b0100151000401d04c1c011000b0102c0101c150f40300480f280d0020039000c0e1003103200c20450130101164070f0508103008041c5001445107030143c41810360402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 800843174 1250 800841924 800841929
    0x6020424091505030a110c16060906080a02071115090103060801050f06120a0512210601050a18050402030a021b2b0e03070b1b010e03070f05030f0c070609 68
    0x10070300340303007420801070300d100e8400700c6003002c104000040060300c50043d076003000f5207610b5203410554032120300c802a41c1d03c03159108070700c510524a003240043c0d0507100f00400b40442d842c03600c608506444040f11440654080c203410b444294007201048000c0e01d814583c0360050f140e550752207448460b03e1000500740c0ba141d61007401140e06210078007109140c5080000c0e00084e08850074000380c0c4855040500340a00c10101900902070744000710300c2440640000d01e21492001c5280104161030605a00c610b18107641d10340c00141c040c030241d07040c0303405061030881d1103040c003014042a079514000207059a01c21600540d210342c020480801000300400380b0301e4072400c00409051480c490b603200002e210b40c0d5078650201c007e0141a40c0504602039001c42c00725210150940710510b440781008081ca034406200151214110311100140307200610407a180c40c4043c0c0043c61401103640c42c0e01c28030780c034100001e0304e490008005101545400a008041c01e01f21800070b00a03491a2510140c84440c481c1e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 800844424 1250 800843174 800843177
    0x10e180702250308161b030809090c0a081b04030c08010c09080601270b030102030f0f10050901150905030a1b090603020622080102120405010b0607020604030605060d06020424 77
    0x340401e03c002101c4c01c0c181c45411071141205000019181002215140c0040c400390b096491001c0100501c0010001020310103015240118152101c9c0d2403a100c600c00d0102400005203144040341d0204180480c00d0305002905103080d04050b145e40728008140c240341e0010703040c2e070f41d6100c8004825402c109649d00900009024184a40c54007002c103460300340e141c0450010400b51010341030040540d500c0306142600c054021502e900e81b0b0300c0381c80c1800409480e514005100b010006407680708000d07612064540140210390340ea441c28081999404400c0d0000d000d0214594020506440402001000034000c000503d002c0d0218130f100e080aa00035080790804504051051001d41c64030803c4801d00c880303400203c41200107100c0007039010340d50760300000c20395400084d0305494052030405450281d0301940080024100702c4007040858400c400000390492014403040001c40e81d2980b0040d804140a084520401203a64618040381d0007078000300040040303040f1440c918040b142d260703000210a0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 800845674 1250 800844424 800844493
    0x1090b0105090c120402031204030b04030905041808250b0a2a0e13021b010b0a0302030d1209170d0b100915020703082a1b010e180702 59
    0x3c0000010248680741c2401000410200440c007151420020005e28500c1076000a4450381c4078a4045c98170711041c0c40c1540003c01c0e91401160600e458461091038603009101d1000e0b0304420303600c4004540062640490186045242c01c1d58002c03206000080c05100d07903264007051034540d02c0c80f070480d540503100010308200380884620700d000302c0b012003920f02d84900f00300c60070001540024240d804800003000400c2d00106080180440341c0b40c540d18040801e000034482c1100650031b01c5404003580c4030180d0b240d407040d80b015200d140034900c41e510010808001065a044a8858400c210f880c00388440c00024005915076402d10240301e915039402c2d003201d40a4020704480001416030030709026140748003001613001e141050082140300001e40c0d00064117a01c0301d00104110404007500503004075510181400c56030300490108000000c241c1c403088000c0f07160054001150807100b0b400c0040e0700610103200071100300c82040040d070b1144446500405c80c8044c8801d40c0a102407a80c074078041210031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 800846924 1250 800845674 800845681
    0x3031103011203121406092a03090d05130504150f03050303060a08010506010f1404050405041208130c03060f0902090f010927060c0201061a04050114071e05030f04060201090b010509 80
    0x21340900780c2c1242084910280544031400811906234035070241a51000300e404400182c60088005180706150181c06d5490b0116113500540f074500c20000c013240c0c80c1103403420600c2a4509a40b02d1010b00395400d2640d00055103809400c00b10030180c1c1c00940d455030001c0200800c510b401c02c058800791409000a0042e0308000c4006402140c40a032403a00f4428444007000300c808030401035800410b4010310901a84c2020b0610450764000760300401c7c0055239110009441c0c65400704004200c980c04118050340350700d90f4a0712130051011a2001a00b15140d029070300144c1d0b14220014003540d40026039903550b500d04113101d021900540040c4150303a202c1072000d030f45408a1905403210302e4005d5404180e840c03240ca0101c1c010100c64000b50150068280d62041024074500508240c550a072110031507800460034805c0107000e41e000041c02400340640c00190700003503010079141d061007841124104180d40c841652a508983c21440050303640704001c10500044000060050500b034508130070905 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 800848174 1250 800846924 800846951
    0x506130b07060e12091507031d01051e0417011b030b0303090d0b0604060501390c08060405190c12050709050a020c06010504020702010c021c06020406120c11190303110301120312 78
    0x4240311a41c07813001c401c64149e20301c6034000c40c11034214445004c00b03408003045142d41c4a500f038206000b400e103480821050340031508014400c0000b43c0d90308882c2500001341c3c2c4041100980a00c40070950180014000d514440c1c440c0385900711301c1c9204d000c0103201403805000f8801115001e40c44141004007484011105802d0041600303031005801d11500c040e084940c0005c0201d081c0888010140305094000058040010035003a029500c00e10a0f2a2007440380f00740100c2d01e0408541c041c200c0700300003c08000158071410303443d400034400c1d0300340c403801603640c4901801c46d5411503482902680016000058000900440b8050f0404807805c50900e1f1031500000c1030a095004024010710b443c1c524000d00d00b00000307000c3d05c0c0c03562200e001c3d586c554681c81c00900700032410b210048410f09002e1260724807170180d180c0d0f4482c0064500280060b060000955a070040160001c0c2c3c180b55640e500d90300f401300c3c1c6000071400b13040912982e1022104901e40100001072402c00d070300f00503242403508803510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 800849424 1250 800848174 800848187
    0x6050c042108040b090f0a0605091003050c0406051b0609010b040b090c0304111f09060f0203090117061c06090c0e010f05010c02040b04020307180506130b07060e1209150703 76
    0x220052086642c07a4451140446c001940c4940c089601c150401c1002072080e601100030442100c0c1a145688540d40850041d415104c083d02c4410007000240402d00081d882100942070300d1030381448130814202c505566030304003a000e50341c2041c01c0e51604007100d080c1c00c140c0280c0701141c07070607284a10719140002000301240000b4100030301c403a02d40d981340301095540027280c440200948146480485200c00e000d840342400d8402c60004c00c41003092000742c82d0011003990103402041c2c40310310440300e0700045040c0c9407500901803a4020208a034148500c410341144505007482040c0014150503036003401d06008005512011460400070014041030300481000c00c00c890080c00e1103c200c05552001a0207400c9a1520035009031020040140566210354044114026a2070181c1100d441d181401017030710907810390302d690b0718041400b001001c00e504020900c4501603000050281c4200341ca081c02c0a484100c0d010b181c4202180c24880c0385014040800c100200200342d500e080070b240ea0280c080e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 800850674 1250 800849424 800849429
    0x602030a1b060905070617060d05031c0e0a0305070c150504121109040f0b070305090a140f03071203060603060e010501050702040603050d0302071109130f0f06050c04210804 76
    0x400390718010102001500d03086003c045504c40300b61508a900d13010020070040c0d00c010081800042e00012405070b090030503284034203540000c00b4600c3c110400035040d40000c000d4420b200b0b0181c0d0380c0c82e01003203c142803108030b044920039680c29560b00c01908140600c0603d6030010944c0980e0311040f55007954001041301d089601e02140059440c0180c1031050f400c07046c1900490f00300301c0510800040110f0000b501c0d102510848070711100c1e440300c0808500721501150784100b280d00c50845000070426803621115041f10050032100c0c912005d001042c21340d004640100c1d4003014816481352702c1505801800050050703460108801454007004148040b0188102ea05000001440c01d0a644a94220002454121040b901249080785005009511007101a245800c8502c07060311140b07403c400070790040c0d002e104820750942e556100d95026888480d002c41e00c550100c001d200010f179043c0504d40c414140340a1181d1552719107516040002e040703103640c000314550003d0060004148a054506 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 800851924 1250 800850674 800850707
    0x9090b09040b221a100b041202130f0506090906040308191503050304050f061e091c120f031e0e010e010501080307110d150c0302041203020d090602030a 67
    0x40c2e0380340d10a1420069070b009804005400e00340f9180424044001e001c10610480e209044046640c0c48428880c1990180074410b21000c08000800040c001c034207804441a00080603007000c1c000085a001c1201d0341202c0549015465008001c054509600440d6010b843c1d44040c100c02e141665001340618001414420350b0008444a44040c48460344460052030010801818558071703402c0260f41c0741c000b03106652103128a00d002039205e040040986034002041e0344165290080e41d40d1110181c3c00c43e4500641140710f440381d07603a242262848000310180501c0c100098a4a4403400510007140e01400d9024541008102401d07003148980d410241d80c1003010010b203d8912030740c0325024001c08814030032298240000130501e0b11010004204062007101d480d0f140c011141c4c18803903075407108180a0005400025018a002000c0e0403224810300345180c0146056151410b00720b804800800640c0180d2103402c0102c1c69542003200c14024220780d0005505104803d0b000406440341e2148151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 800853174 1250 800851924 800851943
    0x90c080d02030d0c11030313051b0a0326070c0303030b0111100c210e01061a0a050a09030f0b0405060f060a03020f12060906040c212a1509090b0904 65
    0x2c0107030303120b985d4110200304000c003034030b03540c0c10308007603092104984c080141c2c3e081c0109018542e4002400c40b044001c0e00001e4481d050345480d6865000c805c00700c0003004080803090074010024131030301d41d0013400c48901c11000000d8260840c24000c08031030a1200d0b02d0b0504c103041078000980c120010b401e8130300c00304000010881d881c0019044071001001031400040c108420043d401910164220390024400351000300a000e5807a031001501c000401d08003c0c0b086400c101200d009480740340140514070031401d20891720b59880d079504403950343d042402c0e1220180c8000f88410402e05100c83c5030071043c5080c180b2118284100000e600b18420b1000034841ca41446810700b154940d18111001e181c40001954480d00d0408034003611400d00f19012100c2c0401c908020800c05400e117075060490b00302419030504400169500402c80000100c14403012540c400400e10340700312828001c0c040d00c2d4610a9000d05032452030040d0a00c800c2c0d8003e00021400c2480b64011900d44058141c0d00c542c010300141e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 800854424 1250 800853174 800853191
    0x12060d031205060a1802090324071209150207030e0922060b0d060606090e010e0601111005090c040b0f100305040837031b0509060418090c080d02030d 66
    0x102161129442401d80f40c962120b83c03480405c1c1030f03001d0204504141d09030b40c0c00720366440c04507103042400c0c3d60f180351210504000c20200383c460355546182d45004e8030001400c0d0040e032074203020007081c0592040d0041c1c00180060425501614400c1442c3c41078401c505103092800d01d05424000400202041008040c8000c1c28001241c001d000c12110241c60719400014508105026040902808001c20241d0200041195400c40841d040b150205000f0036903451740b800444106e5840440c60100d4800c00ca20422080740520880b03004014030380090080d43c0034030051000b5290b0340c0e50074510951010650200640320702d03060183d95001e51800142c5070b40d07149441086e80c080e107100194901c0900e40440d03c0228100380611180c5025412582c001500146c12401e4400b00d102003100b2045040304240301031b0181c0c000e0110342100902035400d050303c88034040d009400c0d12900b0034005403071311094414801c00c0700400c0b0241038050054034200740313241c0000e541c034828403031070209417030362231307240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 800855674 1250 800854424 800854429
    0x40507090e0c1302030103052a010f090503030c010605040c0f0e06220f090f0e0a0f061e1a030f03030c03190504110108010501020601121709100512060d03120506 71
    0x1110b0400e000280110885540c44402c8002500240003c8555222360348001e82d2809100802c0e8023074500070b449200d216106d041c01120090440c07035039807042c003c954801040a076410720180101400362800020414505020001a9800c0c1c03d10305003070000303d010102031a54005a428040c0c9000c1c2c80322aa503100595a0305400c1c0058030031000300c941c4203040401c2c41e08040c00c543c0c00b151720b80c81c428070460004000c0f808c1103594a01d10761496902003000c6100240c145030050000e41d004000c002010818548042041403900899400c9956580c14800b211401d680c2031505048064004000d41e00400000607a0307407101400850403d0004400203c010f10400c034040314004078040b040c0850300b094540300780766075815903115000c511514000f00e034035403001502504849104060a003101e54035111081040e04000e40010040030801c10042d15403500007180442007816642c0590b6982c8241540714003e40160030903110f145801701e00404039030b10201003a40c1901c405c40002e907a4648000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 800856924 1250 800855674 800855683
    0x50c27030f011d01061a0921060711100636020f09180705030c13081509060a18060c0203090a030311010f0501150f02070f0b03010914040507090e 64
    0x10300001c0d50b0904803050340340308001c5a02014500c80c07000a2000343e440c4e2030000508100f100703008001e00801d2018aa4034a0403141c03402d82e05503842c64140450f20000b06c0c0350f08200c01290100701141d20078219510345a0304100036114800d141100300004c40c00d006903003910b02c4450f142c1d01202c50300007020444a011940001c0c600300c4892400b15610b15503041404120380018002c0341c0314078407030121421507624080ca40d500c901d0995442e00d244d85e890581d03e0780350f07410484000b80352001c0c503200440c2d8024104401d80da1540c50b10f6418500745844048545000030013440c203a8401d044c5942c8440c0341040341a004102603100c0c00c0881d061000c070358124914022503041640c0703c0317102c0c2400800c2c19082581c03c1c03035451414000f40404110400f070001a28801c0c42101c0c04003c29102008516116150550703d840c524419551981e0347c54141048007216030b0040803061100000400c802000f0f4803e42c0c1d40446201c1d60b054003441c2903240d20f501c5220038031424010310303100d24403100c08190a00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 800858174 1250 800856924 800856943
    0x105090307030e121614060a0801030308130f080c06090a0b06010c1a071110290f06040602060a0b04090308060114090a06110606062a0106030204140a050c2703 70
    0x2c00f01d4401d10103800004011701c01d0b620030340c0d4210b801001e02e94131900b000403c484422015803500c1d20b5592035568202c0d0703800d4000304000b13012a0744000b4180060013100d11240c410f0301407a2030f140c03130b503000216040c01c1c02805840140790b40d201e0140000001c0051000703590203042400d104842c8180c90400509180c0349004107294140c01000300715009411000881c5040e8811046a9511180d030040e102120403c02102408800800c01014400d1083c42041e089940280203d0f4468000707002148441d0856088a80913800c0701c41003145110b4241315610381000300f100c05000010b0b882d200500040c001510980c1001200c503055500d44141c00c08640e18080043c040f43c80c241d44e5081d0003006c22489043d44801401240c000ca1180d182034401d80719460031000c0d02980340100800026140a00414000b80c0d6540341d0304000003690b11842081e904195443c28410700d80340403244c50040b10700003094203003212414402000d004204041c0d100305600581501580c072450303500002e06d003807042c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 800859424 1250 800858174 800858209
    0xd140309040216110102030a020c090a09050316031214040308060d020312070309090608070b1c050708040b0601080c0901030f142e03030e09060d061d0f0105090307030e 74
    0x2075600e49030f0304041540d421042c090841400300801d01801244c8031320420803030500513030113060000801d03e801c1200300d821100d21480019420410754a9a0942d0014803c15040c10855003124003803641100020f5020b155030740c4108050403240202009007007014001504005100e000540b950302d5400d202140c0a800030200c80034104003400760001503000307000803000a5540b42c000104040980503201c00d81d0104809050068100401c101440c1c205540325800c00b032001c000d41d218401c2c10721030300c0d0142159a880444a182906111392480f00c007405850401a504040260440d03110041d95045070092130042075a40307c82d645040500240442014058241018003a035080031644264040040ca66824000c144882e10162440c41511010b4040b610086031800c607450500340d9142c2c0194000e003040c00f280e80640b201c4048481c01036004551401e10321442c00c01d45001c00940502400c0c4100a03c4289040c680d80f540344e0081d13400044c20b0155540a0717101c00d59a00304162031010f4074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 800860674 1250 800859424 800859427
    0xf12020903070b0405131404111305070305220b0a0b0d061a01030606081510110102070606050a0504061d0603010912080a0c080c2d161104020403020d1403090402 71
    0x110a040340072603026100702c42c42003886c3d44850341214403d01030800b100d80a001c4100c0507540300d4607060341c00034414247c036603c90751518a982213041c1e944581c038042c884a40d00020949018840400fa844440c0044c03a0640e80a40d51a0006008455400d5103c0400200418468644030124207250891203000300032909001c01c1c42402612107010410403d4240d90910010350360380e405407a410020b1700e80c40b494094070070580c0841d0904403e2001d40700811f20740305908030340c0300300711508a0f0403c4108940c0b503501c031501080305180251400025001c1101e00704195460310306640c0b2500c00c81740708140801741c01400210103a40079031040c3e00b0303a90010041d815800408000400c00003080b40d444800c1c034600641180d8603441450824410f80303070b252405203003044548000c008200b0380220310813005580211311605401c0000500900708481042803a50f0b0098a06454003880c00c2c035000340550310602c800c00c0540c0d00d440110f801f00303411009051f01c0000710b2422a0441c8282d19990350030600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 800861924 1250 800860674 800860679
    0xb07030c0320090a090e1203102d210204150902072303070803060607050a021002031e0a140a0512130302100c020303011502030c0d0f090602030a0f1202090307 70
    0x35104018031000b0004c54910308a561600300751000c07500741700d0700304c00160b20865021904950320401140c124420b40c00c48030810769116140e206142d0691038a5030b0385500d28400e06648111110090084c0c0000d1588050104888400c540514201c000180c4188d444580d00c00b031582141c1c2c960005000500015940d032255414810218000c904070304110151142442c1c0103184040141c4070810352291216186403502000c03c04030741c011301401d0700d00740036400d110f01c010707520030040c86038a036604e4000c2d42e20780510b405004c81d21011403085489440b000c010301854503500c95082034840750076524079502c03181ca610040b075181c001d420050901d010303094144402110440b038200704031880383d4211007070400c030011040142c40c0c2c043c8074100583d0060005001296900b008981a401d07181304a900b44100c85030301c10700c0d1120014144000c0b843c05041326507080e506c0240d100240c543d40c00114607000354544000d10249030316910718200141c44d0b0078071712400525011520400002011a02d9898 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 800863174 1250 800861924 800861981
    0x1b090d1704061704050a020103020f09040603060c03060f0815190e010b040b030a020904060b010c0204021602030706090e0103172b1a030a0b04020f06040e15040204030b07030c03 78
    0x20710078020300001ca001c2110b18011014601c403054407841c2d002000e0301040140e64019006500b0800610b10101000c0c0842001601c0b1807090b40010341c02450003054207039015002130101c070003a4200c180e02c9903c0080c1404100340006940f06100d50704005208265034803601e04403d00c000314020281c4a0601c410a51466070540000300d800070116010403050340034a0070990b8450707401d036009410640b0480000c0108106610071000444181804031017600294006130032030380104d1240b03402020b6000040c0540c00d003049000098403503410700c101480e08000c100380c1681030520008000384001400a4002180042500d1944902c0341410b0a1810840742081c8413240e0300740b08203807547c40c00130103c1da00040d00300c180304900009006402000720940711030b43c0c0c4000003402640c0080410802c4c8030540c842c58020801082c0b00c0f14481044d0410740ca048425400714040740e4800d0780140000c2c80495004d040d9203170420303120f0500140d01600481c0540c050320b41082c00703102c0b0011441050b0f2610 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 800864424 1250 800863174 800863177
    0x5090d0f0b0f04060c0306050f01030b12120301030605090a0b15031c050307020105090102090f04050901060506072117270303070f11011407230712080f1b090d17 71
    0x107902c0703400c4c01d2048944400d402c804813201482440d6008051078a0590035500a034010b0b084000007401a9090315002054030b8a40301d50b100380d20100b00000801002400078034801d06400208413405030610810300d4564801d0800003610b4101a41418400c3e43d403143e0341048804000030740a03461902c0044900310160003500704649040c09035013400001074046030f06200302d48000c43c0007000300684044150905c002050000c2940c84c1c5591382d04000b0642e07664100290030217a225000419480044c103804645000103115014240305440303d044a04071412810300364821034540c034012200720800c8110041c0001a1003459881c00004280444198001035413024001242c035254854166002c1c42400c80340c4940481c0001107a0002080c445441000b6406600301540543d0480c00c0e02e11600c1e00b91a40125000c441401c072081c1c0b070b92119500400450760001c111442c0c2c00d02c514002014030000000141303200a03203000040c544400340d403205c51024525810903041032000c080e19032003007400e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 800865674 1250 800864424 800864431
    0x20c061608160b1510030908030c0d02130909030f03060e011a0706090501021801050403080703110a0515071704020915030a1e1b060e10050c010507030b13020a05090d0f0b0f 76
    0x3482d005c030710003501c18004d00078158041c2d0b1085082c1d14507940d1000850840d04000199410590200000e1000421034001e00c2e019103203034000000e41130410f1134041c241d040014270082c00c0c941040d400b00300401d0601796a50450f03070480e160980ca81413107901c0b1070480c80b9280300144614540180101030040540c00380c0056003041981c2d0030400030450054030180100c5c0310007041000b08220200019201d07104580502c64120112048504d066940314140042c050b00300003071002d54410051095409920034008002c40303074a841403820581c010909000008042e0f08041007010901126910104a00c100c1c094003e80d0401034991015840500c00205640c2955003c0b842214848440140903415045a5454407006000c00c000010312808030710020a1200f030107000d0000c641905428042c203071054800e0340d0001000710016007081499030717102c141400d41070b1040c8a1440707a06c1d0024110354500d041101c240074a80014584250100e030100c40040c45901c9100034000e00424003000e4500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 800866924 1250 800865674 800865679
    0x70f090519080708031206061b07030f1a070f0e060f040305010e1c120b060d0c020c0a0f051c02040b04061214010207120f0c0b0115020c061608160b15 66
    0x10420b07640c5032036175030781d018501e1002494100c82c000320f0002e140010041140c0300c400d2801d00c10f042e4030b0742030031401e0034001e50054428020f0301d80d03420300304000501458001c20b0041d51b0f10029080c10710004054a07003110310007050002a0965070364560300c1e0015650120b0b81005142c2e61503440b4a030803400380c030303102c4c0c010300c2c10b07104072902c0b490300c09032449841031a0b003104e590720094078442131036440190800b6075615070461810024400c440364240070705110000310740c00400340b007042582840f41d405055400a80206d09010701808107540b0186868446480121044103100540c0000f13401410402130860340549804000101e004204a10451583c020b421ba80303021403500c00329134281c1c891000000c100302c100400700e140050042481e14541c040503d0180350018259480040d404c60a070000a800e84600302403414041e410898000b00314400d0f51a82d080c0030207c0865030340044000c01c0200003c2e400300d245d940d1035280d00d040d0a1110341020700d8011a0400701c44e204c82d25581560380a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 800868174 1250 800866924 800866933
    0x30609051602160b2d0f04080609070312030b03010b04180c350a061d190b01171c09091415011b020405010b0c070e010608070f09051908 60
    0x158200709907200f4021134000a00d860b00d4412060b6801220009a08509800c4401d900d000200400614003810146110180c1140e445060000c0180361042c02401c001030382c8d2201c6001e1001a1202c001488800780303c3c100032401030302120010380076000030f14103190800d02d00302100002001c00c140006c0124000c4105202440c3c40c0e500044d01010300c14140010b91520f20106192503815180e00122042060280c0703e0000c0380c0e542e448160341070008060381e104001c1c4948002c082e01408001200c440c55032445c4030b2074106a0b19880b007600148142681ca4103840c20519244009000700854101104058480c0200b031000251240300c4034000d10700803901c4c11002000021643c2045800b03111004c20165000909a00456500d800a845021030428401e000360050b00c07070703005481c0684466040c50f900c0d80c200e066114904515a8410612039840f03900401545030461141a0000d456141000410180400980d0304107034550045802c44800c11000ca6840700d120740701403c4e00e41d0441502c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 800869424 1250 800868174 800868193
    0x405010905070e040c09171b090c1204020f130509071e2d0e07080a0605010c0f17070b0108010b0906280e180d0f0e010c05071224060b0f0a030609051602 67
    0x1c9e43c02d200300c2d02855003170001c00c140307551362101c0b000b0940d001c1e01c0181460408080103001c0b0700c00003001007008441503115001c0c803110000c00e020010143c42c44450740b8000d0706821851405100040c880c91612503c030800005000034021242214260b01b40e11170300d4015902c071503080001d001214410005580394001c100d104540b8011241180c2050703483e546002102d40318944904002c52003100c0e1410038041907006182c8900103814081e00030078880b0307003030740c940b282185c25039408141c024800c0c0742800400c9810754401160f4840e8003540f925426100c040406901800c8020f50414404010348800300011651407101821602d01441d040e20091040b000068512080d441070312408030f040e40700440d00d5944607840d447e0f8074a000f1421202c1040e61001083c1003820503800c19a040b20142031a020300311420412040250350f0f02d41e0030004c0a00c0d0100244130750052105140725010005a6211402d10981201c3d008d04416071707040205083c4501804460106070013564054021341850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 800870674 1250 800869424 800869429
    0x1806030b071728021612110601090e07060c17280810050d0503132909030705010302030903091504080708031c09151a0405010905070e040c09171b 64
    0x4140b00c1d45000788078501100204020390020303400401580000c40500c00d40f00d00410b02110200140781031603155960010b00403c5448d090910503003103000110308240c1c0502d040d840c00a40d040407503000b894030403000080d40ca048052452a5003103010040000709544c0400309804400304000480b55801c07905505442d10250740c00c481c12903500320036504010080155013414884078030014461001c0c2d0340b80011180c10070000c9440354005813026100180c1107061130824403030040c11f4841c443c400c01c1c1001144400030f6910039007401140e040540200c08106003150400c180c0d0312011006050a2000d030520030f060800b83c001d481080c110788030b0907000240c20f00000c821218014030074900d03940c0d01000100c01c070024040240003101d0700390040039040381022452042081c42c84110300b0f044c1a50040e08204010f961041c0c020541c00d902d000244890715070400500002200180c1e40031402c10300b500070a84084d40c19a0155110000c4003981041ca1007002c0340d8490b01555005540c1e0240311100d00f03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 800871924 1250 800870674 800870701
    0x1823090c100c02030a080904060803120a1a0402070f110a03200a08030d050105010f050c03270301020d050a050106020a020904170d0906020a030e03090a1806030b0717 73
    0x18120015044088080d15505103004001081445814140c2d103065003a800300c4d01d4000c18074400d80702c00c000804d501141346040d0080400410181c0004d50820300b00b1004d106011030003500b0015030310740d81e1001114883c0440d20210220340028421903e0380c4550404803440d00c01d40500300c5005000056007200d901d841700c49441a250400c0d6a15a12020a00c808044e00c5000a07280c0d4403000d20300c000620140c0820003000c00a0b6000008211945804009000c1c0107150303103203070180401030110b110149000410307103081d40c043d10541d22203d40021b5603180e0742c0324003031001c41c0c055000044604025140e41c000340c3c01009030000400440c0c0c0c0c0c40404a0711002d500e84025441013052001c2030100c0c0381c2d0111503030350055122099290603805111002101c00d26a4219001ca03004141900402d416100c1c61a04420b1540510b10f810009000901c0351900c0780155902c01c51f0003001c00010b9045035200a029581c0512161003038101684e01500300b4005c0300c00f5000e01242540000c0c14051800e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 800873174 1250 800871924 800871931
    0xb03090307030e060d051006080a0908030c0d06150314090a0c0b13260d021b011805060a030501050a090c05090d02180f161d0603060a1823 61
    0x200914107111640c1c0d42141d24420342c12202d03610180510400385481c03c80e104050085114199121801d850310b003014001d02c100030000100e4a1402400782c0109901e0002c8a5121002c040b0041d0743d00c955400c5000100940d40010780d0b0010704525100d586500f5034032240c2160b0707c103000344c8090341c0c52500596941841203002000c07a421507004003d80070428000e00960310005450000032a103d041401c1d480440074407100b900032a00030b581d203084000340446138a1380030910213030a10301c554141001c007520224240c01c0c10030030281007a882c0402c940700c0d048060032004049a42d00c00031040010090b010a000356031050b040e08000141d621034a04c1810801c420310744807a41040d0a0100f0801c91407440b9100b0383e000700b40885070203455807042c81058401e101c03500300816607047c2001745005d480018a071040621094a1482000211114000454140449000741e413950b80340041150181903501190001080032001c07200c0501e140c0000001082c0400d90041405124489010202054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 800874424 1250 800873174 800873191
    0x1b010527070504020928030213020a0206011a1c0c0e10020706180e070f0207120c0504050a1517010b010f170c0f0d0e06011d070807031b020f070b03 65
    0x7824100020f06058020b49124031004150001c0c02206410707244c200c1d0642551500540e0001d00140114a07104a000c104000c408804500b030a00c15034010307544080602500f094031a1403c4441c9548160408803401a0850541e0000e00700503903000002410400000d2804581c0c1c01c1c0c507000950a02403040c40c2d50880365402000094a04030cc00c1c1c4003001d002c00d4004050346401d9001c030302840450a1107000f0500c0f940c40040005041000a080050b40d0300b051441d981540214008503003462640781c10354200b1640010340c0c0d01d0b000a0640108112410b01d0454480c00400048074001070f01408980ea400d44020301c1030350300300001184c070440f0205901e004102040440901c850582c01d499500146240d04e19107041003203258000ea42d000880c070104460344070b401d4440302002c140a00b5005004043d00c98910100400c070001c66284010200c1d8100a030440c002160944070b40c00c41100c1d04d0403040310b02c40c0d011000700000e4035801450000c5c0803034482c1c5200041c03103c1000c4126407142054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 800875674 1250 800874424 800874433
    0x70503040c0b03071209120909022d0c07030b0106030c020c090106271701060b090303190e060d02121506040504090201051b0f19020a03060902061b010527 68
    0x400c40b03500301c25080500742808108961600c11090034040c0f01d9180c04601882601c16410b920200042242d0502e4005465031801404032040d0000f01c082d28403100020a1443c0c046846042918600c0d805414051849440742c1740002090000c48181e03507059a420759010310403050110f0041c3c1c3c0d20021982043d8000300d000004112180c0703d22a0101d500c04904401c58441c0981c0c803036407207034410720b4100003110023100401280880e803d114030b0006200e4260514140030b0070600117901c03030080c1c2c2085408941c19912084030307280700d0b0705402c07003440d00142141d8640340c0e556039010094020603180b51806070000c0100d440c191b002119003188410003071040d49428240010f02018007409541203051180900c100e5203000200718114070016a520004d042000f0411411441d01d0800219815445112200440540c80e0400540d0a40f42c011902041c6541d4502c04110144220082040c1c0f251810f8030045a1600c1900650300a205080d180d1244080d241032450140070241034281c000d600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 800876924 1250 800875674 800875679
    0x1060f082211060d0e0304060e0901260f010e0616020619020d140412081b121008011506020c03070806150301060302150306040f05060f040b150d0b0306070503040c 72
    0xd0070641982581d40c040d03c41c0381060f0700102c0c940c1c161642050f2807503840c0c0011500707108a6901120010044008550400c6030f94508080040c91018400d0101c0c180312402c10f054640400030854030540900c080020000001d00560381030301e84100b034801c04624059a0310720034100d0701c0020f469014000c0746002c0342003400d8940c0400700035802140c640d21070940740c020050030140c032658070360b1180b0f0250707640301710011003a90003c01101c001401000d0400743e000a691403d2507035400d4800e400c1d0311b10b51040c2540c6510092501d030102c940e2090f41c040d82032450001d06206e0820204045400130340803241c2e480f811000300350300e5804038003550905a1103200014210b810510350740c001010050000640c1c0c1c0d480742c010030000d80140b10544d100c07007400414009103040a101d80206030a18050400441c00d00300002a14511072101c0c2c2841103440740c0c0301c800c01d0b03582c850030300c810380a450041315541d4aa82004074040c0c00c90f030320300b107210340074200c0011100b5024004491003903030b000314100f00060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 800878174 1250 800876924 800876933
    0xf0204030201051605011b0801150302030c0d0c05071e060509010501080316021f080907090921020c06030a06050306131e140604060515100212090409050601060f0822 73
    0x2240303000f43e03010341d225041c5240d01914400341c4c00c3c1c04140380d640c81d0423540c14800501c000e58041009a0100351042023001a00d090520949071081e003100d601151751090807030126400c1c003d4030000390141c0c031a80580610000028041c00d6918031803001030080790744036036880d803c0324002d1043c01c8990304104942107a403039040c644403880d00c1c40241324490140351801d00b01c1040050078422400f00e54400c043c400070800c20801100205040d00d01070183d00005c0c1e4468446040c0c1003601d001c1441881d03061404180207000742400d104015101a0b146d15215038110003621a5128650281c003464022aa20640200c1c05285030381e0048910a254005c000c2c0f41c407a0120900c0040c1c400316400c0e031140d070112109020107401280100300200e40d0b03080c09107924688500682c01c082c46507000c1105001e0081d0003040c8200e42c2840082c00e140c81d4403040010030040e02d01c46034010142e0203020000f03d8810f804c1001a0148000c0360b035910074640d02e0100000007002c8003950800086026840e400010b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 800879424 1250 800878174 800878207
    0x140303010e010311220b03010e030301060302120a150e041a0411120601030b160c061e0e031309020a030b031c030501050d240902090406060512070e0a0b03010902060307030c030f020403020105 84
    0x46d0b806000042d1400c0a0040035055404c09e801100c00a43c00007411100c03140501142600101c107100c1c1000208400f03c00c2da1000801403142d10081051040028148084a00000d016000301c0103090502e2605250112801d8a50304050344100328641c0d08802002c00010f1250503250f1108100b04551a40041c000e00700040421980821403052183e10000d101801041c00609190304141489005020008117845041e19402003035441445401d840b40c0800604100b143c0e01400d0050b69410301d14402c8002e80011080d460700352180020440d904103804407031040788401650104a10798840c0e0800104520b0790700c010f8089000403000a120301c0303411002403c1c40760340c0d1900051951480e40800d10500c4100c5040ea44240d82e210200858200f4480d280c0c0100c07840406414040c0c01d2140e481c0d1501700c0644580c424a982c2d8194030b04c0c9031400d6011402490300103082585903d03140c18001c0c007400c4016018000070341080040c8503058440d000f650140e03a030585466082201032240c0340caa2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 800880674 1250 800879424 800879441
    0x241d0f040f020f1804062c06032401080705150a080c0d11030402010e010e012703170301060f02070e1522060e06121504140303010e01031122 62
    0x4a80c2c02c0100501485485000384048940515402d09410100b030420044800540c400c0581d6000003e50403200c22401c0e81c0c00e6402404900d44140c3c40e00c0d000086843d1002c44224001044207040019104080503590141203d60510449400c2503c2d0300a022076400c0350800800d01c5042441034034049405548850340c48030091004608280041c43d0041c00e6852103050340d05049400010f03c4107550b40b00c1500600c511003820f14042007041c4a00081031038152200d42d140640c0524501d46c1003800c01c00501c4025074003d120380084032074503448070000354003e2181c1030214000d04c081e08402070011590740120b9079402c003812080e68451403028005c0d50101c5800358803c8139a02d864032a074500000d14001a0503040c000039160341001804000311102524851103100c021030540181c00000a513003860360740340380c203884039504d07203143c013001a40c542c81d0880018000480003040d04001107800c541268003c44403020750403003000c280029241511aa655649000150f10402520079000b01e01c0c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 800881924 1250 800880674 800880701
    0x51008070f021510090b0f21070509070203091c0b1b091302040602070b16080f07050304061d091902030910051e0903030c180a241d0f04 60
    0xb118089251a40801d5000c440381159140020340a214440142c4203040010605591109008002c0c0c000a25009550202c0d80c19100718540008c031440303001d1060000810000d06201c0c4141000700000c1d4481d00180082401502e192041d071411607099500b6481258000900d106107454600340e18040150b450038022100c141004031007820b071030742d03070b841480381d01e8490740141c9940c2003100003401c0020960000d41e250805002c0140c600403610464101160f00c610040c0c1e64040905001c01207010b480b901a29501000c100003482c1d0350048400075800c8103100b0300e22011242d60042004440040e20008010b02c1068840c0401100640c011500000e44004541e0048903914000d40dd6600450b448a890035000780455151008628240d820040400203982145403c1071824003e001305131010312001109401da8826458822003130001d000d0400352403641c07801c02c00046d1040c405a140c800c0018151040c1c03218804420016000311100080500d19907640b400c0c04c21018001402c4c007030b003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 800883174 1250 800881924 800881933
    0x10306030b09010905070603020c150a200c0105130317100807061806140f0304020a0b040b07110303090a0513060f06020a0c050406030b13060e010e16051008070f02 72
    0xc1500075000600c1080c10340e0001c180041d5a1404a0a16800358010000e041c01404044807900000c40c292088540c00c1101c0c400302e03603440441e20060040c15200400003000d1080030130414407080e00404465900c00000e00581d2115184903500d8191030718050002184031110008001d02c0800e8290005c280080030a0f007141c840c00024240380080d40510701003071040d000c204000c103400000d01c0042105040603000d6001c240040800d07403041ea0300035486907000000040855031041c00b14009030a41d5440d443c1c5580d11142d00b005241c0c042c0d14103440c00228003281c0b00039450004212000303050058850b8465518010138443c1c440d80d91800c14000741d866201c046082100300c1480002440d256000700300c030807020305095051b102c0c0f0350440d43c0100c0c1082c0e01840400d800603603054100307440604e10740307009070076017820002008180e0b031801c46942045028a43c5040c0061100c0d450380d261104000c00301e507241d00300440504150217100100f003d00c000580130310301031198030b89441c81031b00548 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 800884424 1250 800883174 800883179
    0x2703121b011d0705041503020102071a2803200409090f0218072006010608061c0305091509090c0705070e0c0307320f0c030706050114090411040b010306 67
    0xc0b11501403000c00e215501c02c6500b08550b02c0c05000b4100c03c0444000b1100980c3d0558000030f444503114010241900d215a060303a00100e1300ca011200354284003a403080c441c910130b60414503403040740c4101600180c20204240c0c21040e111541c085400808141d0600d001e141006860251410504c1992000000c20f1280c0c05070b124001c1050320b14241080080081c68020806000f1204140140070502d06000c10300d10107403c0002c2031740c199406400d080b8059aa0503002601041c1020006812908003500500400da04403001c1c1c0000c030f1013155001007000c03240184820300e00840e100294000c0314500414402085076000b400400e00841c151a002600d843e40a0140380f0300b80c41c1c0350b010640020030401d00035400b00d000321840350313882d440d144c20804450481d10a01840d00240c44c020300c001a00210300c01002085582214542054039251001424a0390044c1341c24496041034031091031281803e45014441c02c0e20441d80000021021000c8a081c07100516514481070b061540d50741d8003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 800885674 1250 800884424 800884451
    0x30e040b09011202090f070e01140715060e060415120204090215030916080c1027080f031e0903070513051005090601050409020705122703121b01 64
    0x16907001e00101e8030340e19544840c0f84107004000c0401400006025020300900044c5513012110468238082480c28150101240f80980e003203105408004080c1854141e06845103280c03a0005422600c00e151642d40b1555490113000588000c141541c014154207403050201c4004000c03041e02842c0003820002d50700c1c28650108061203450083c250082001004201e604441045a80079400d00440541c80c0245080c80c00f82d0f41e0b13200c212070300f803040d005001c490220500c0740f01c501014810b080c00400e244000d69907a00b281141070302903209280100c000d41ca600d0301001045441c10021000c04514454000840d200250002c03142c160f41401103038800034117596044444180b900004a00003030509107120007610708002d0742d100d28020800780d4200a00f50ba00070040d07170102e0b80c2d00039026a9070440d92034402d040501010241600c800b000c20410240302c0f1100c810f1100e1251305c000d039405820305008142c1e840016034146c00d0b0140d81041406000f012109518100800280000c58620b070160710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 800886924 1250 800885674 800885689
    0x507060e0f15040b131101030504141b0a0902070c0501211506111203010501050c0a060c020c03060714040909060b0301050c0316090b0f03100308030705070c08030313030e040b 77
    0x9000100b184007424002402404241e50b6080310f4809604030040b086a03481c201004e03031a802d00d134180b560321000681031143e14103412070701e01881c2080c0c0d80400e0b401c174007000411411105003401001d01100205221a103031003241c02c00343d04096140341c900c0c9403000445200d04000810340c02c1180b41d406c41590042c4038024030030341d400b01e03545d481112401c0007001082d4401c02800062a50300614945d00100700d184104c905490080c0f80031561503000f1401180b400600050082600f0f10300400c210b00c40c4d6002c02c18000702203046041d1501078a6101040398039071000000c00c8890b61007004204454000356000001241c400c9501141d545207420019007115000c5880b0f41c0c41d0b01000080000682c0c940c1914503e20f03015042c08240f540c107100b4400b07140c0c05180103a42c00b60000001003048a2041504170000350b80c000c4007181c0da4038008400030182d41010b8402c0b2500000c0c0d41c004500c0c880c021003a2840350f22040f0461084045030f4400712810a007041006821640c0c0e10241c0d41d460301da110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 800888174 1250 800886924 800886943
    0xc050d05092b0221030d0515060a08221a040c050406030b0a020306030703120c0c05100c121b060605030c1804080f0f0a0201050a110405010507060e0f 66
    0x888403911103038880103104242c807071999091202c011074903000140714070754035420845940682d03025010780900654590701c130380e42d0080c0e4030091002007207482c4d0307a450355080302d0301ca101010700540032842c10001f8400321340541c0c0c050001007031350080040d0640000740095100700000b044940304290542d141d200c44001c00e001c071400c02500800030401402000d5075908018101600c0400000d46192a240c084190281c40504080d40000100343c43c1d0307804014080245820045400c1c85600c80c0b00058101c0f15003104c1290208846140013400b860419480c071803580082e00c4142021881d9590000d00b84000f01c402820310850341c00c07a0001410301880002124860100043c569040c00b04051410110303056080c407a01d44081e81090842210300e00c2d42d0001e90220329943c4a4048640709905406800c06110003410081051054aa4150032490181c41008001c0000c45680880385440784224015107003c80c3c4204215070004455901c03140e06c0400c0340d000d0b14105184101c03110304214010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 800889424 1250 800888174 800888177
    0x1401080d21051f0509240321040f2301030c02101b0206091902010c030201060e131a0405060c09010201060b03010f03031106011503020c0c130f0c030506031b010c050d 73
    0x2210140341641000d81070030003802c4100c074510310501d8000305915001c000c03035814a9810444101c000c404c7d0314201300003060318405c1040da921b415003500c04070600d43c000b13100f01c40003120314101c00204403540103100c2c902c05014004492403084141d0041d0301410041d0045000c520400008802e05882e920440d2054010042e1000d82c203203000d18003d240400261440802e90042d668580403201400c119204059082c20800506565070400380d00411680e840384c48010480345c00c11051300e20545049500d248600400c0061030b00d020085c107013050b02240c00a00d01d81c42800418003071850040503048060051001182c40d545950340249075805c2a4800014001c420009108058020005d150069408002001950315141200e07510068825007a0189540002c9447c031458090044007003030700000c0c0c4401c60b0802c001d100310b002041c54a404100c028500311009103580d10900410303015810040c0201945206850b0f0180010010404941444810b41445002803070501108440c1c00c03c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 800890674 1250 800889424 800889451
    0x30312131202030309010c0203120711030408030301080c010908210c03092d0d0b010509041502190305010f03020901031b0302030a0602030a05060f1806060c030d020d1401080d2105 79
    0xa41700303d90954920001080c259002032001403113141035041015480103281c47c101620a850141c003d04610464121400390b0000100128403401d0000e060001c0240a90390450310755901c1c2002a10341c9550b40305080c040404610801013590740c00054490b01c20b800c1d094030710381030603a400280c1d554044041e40d403010760141c60000c046030701a1524615440709071480700210340716a0b65072040e907005005003807082018502050034031294413440003005030000021503482082000142c00c2951802c3d6074000641000004901c80c040414a5011a130303026046001d20b900703590f180028480380c2e10040c01b003010340ca280000540d031304028080c0070500032580140c0c0d9040045002d420790f04001c103014002e806014203039401e5143d00400c010303629201d0341d4094481d200d08001400342e200300c02c1d0080e924880465445941c1989600038070020b02c24030020400e5000b90780310130032441d03070034410001c080d00640c0141e030b1414028016600440300004801405074202580c050444006031002c2c00c000c0b54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 800891924 1250 800890674 800890681
    0x5091204080c0909030a0c0b0a140c070203010615230f0403030c0501050121060b1809100509010506013002070b04062004060309050708072405090303121312020303 72
    0x800900d4590411501302c06903280080390702000d0b182095442008100406c1240002c05090190f0300c001d60f18000c070100446d0038104955008455040180c00381e22139440e10a001801d41c1d64942050b00011194455841c03403941c0c50030300245000c01c0c007803603900d103481040006c00e0130f60703501e00401c00b96109482d02c80b201c0e2a503082140c02c40d81c050300003c2007080b0040030311384000070000310001d81c2580084081034001c00311001c1901001200307914041d80030140c0610000c1140800c8128841c040c0e400704121554070b01100f80d080c0d410644841b8041612039424983c00310021400304064011380e010b0160250152850900700d81c0305c540260303081d40040b814402000824003490b1407030301c0302410800320819004040340d8588200d1180700140b503503e91a03101000418000b0300c006003060f4040c3c90216540e84030f0b42c0b0703201090b80c0e00340c1d01481c4003d5585804074000e0f0151400c41c5405070003582415a4090040401403000d800c6e030800e0b90b035609070790340040c4104003001072502455001c3d586030308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 800893174 1250 800891924 800891929
    0xe0c070f06240e04080913231f0302060d05040302031303050706090e0f0114040605040e060a0c0f020d0305060d050a060b2407060207031707020a020f060307080a05091204080c 77
    0x4046822100b03086019209004c00710307a03031105031100203e04450422031404042250001010400c0e41854008444010b844200009840c402d00c039019808500560f0055441b02184a17105e5000007907003c002840403811080300c0e0b07401180c1c060b100740100c0746421480040c0480c4160f055100711a282e2040c03d09000c80e41e84840094024007a911190045060154513002030001c140034840744850043e840c80c41d10b07500d1340c004000500f8040c01c01c01461651340ea0b4641c80c0c41c4203c2c2c1c018401c60034030003010812441481c22202c101348907030260244500d0300c001100503013005400300c0d40c0825a00080d00214a0600030b03916628400d820004034014804203112000b040d000e194401c000c0c0007007266401041190884080a81c07159006036204020f140a8855900c584528142805480c040200303080d00029001d01050003200c401000982c0b410070440144030448400313001480e1800441d0a042c0c0d1500701a42141045064503103a410380c0c01030340e407543c00ca5032240b126540000d10400550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 800894424 1250 800893174 800893241
    0x1003030f050406020c041509060b04081e06220c060507030f09060e0409061103040b01090501090908070201110a06020a02250b0306010807032c010c02070e0c070f06 72
    0x4800d1401c1140c2000d150001c013945406005518034000c9440d016800ba001540c40c101d1405840400000c00016407926a134811030781117406120000d2107441c00700340d40d80c051520740124408028005100c40ea9401103007d00d00003103923990304070710840c15040030005501c03e0214805010349584040e15030382c140c20020301c0c2504030b040e05018420200c80501c41780c2d078840042041e01c0c9094501284230003861070f03c2c0e00241182481000e100da00071080c40304001c25040050304982d00303480f040c032003a6210303041d540440e0741410006218000800c4a2070040d4004c840e000a400387c00300546034198080d40341d480c00c0e03901c81c1042600580005022520f04510490421030701c4800c0d08074842501c0c10301181344500d10000d01082c1c10720080b9400075240d58801d170440483c4212002048980d10030b4043c50382c00e100c5802c0784e00509542000b44200712107100080705002c85001c0807007d10607888440302170384660300c000c03001e0b1805141d40908201152580c000c080454620001c6039040303428050034000340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 800895674 1250 800894424 800894447
    0x50c152b0b040b060d020703050c0303010306091502090f0d02041407030203010f170706200a050106030215180105090105090303070b01031412030a050a0914060613180602160506100303 81
    0x1480c43c0c10041a0b06442e618180c0d068003095000042c1d442c0c10505003a0781900650001142c3e03480004008010414242c111041c00c1d88103c0400c5e05154034506144140c0c042c4000c00341e0011038506543c4288c0c98060617600285001070000a40f083c0c00c2111000180c804407080004282c001004005c02d80c48038807250003d2079060b40d000340c9403034142032150321180d00303124100402088444c1014820036080414409280c10800c56003909050b1400501801403444181d104809510404100058090840d00010900f8512801c1c400c0c07800015611500b10201c0c0390b0410000f40304517811520200f00400d005409a1900c1c041c5601d1460080c1035404030840c4910700303400003d440460b582c1580192078106181401c0460240e03144841103004001e46103000e0007070340179080c4000402001159242c007902c0c0c290b48400035850345240400c295016601d5051140b5041c5d20100d0109610381c0c050200e0440d260790040b4007110716100c00d8a809819140450031814412003041090b4000000442 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 800896924 1250 800895674 800895679
    0x60b0a051c061805240607060203180d092103020c010c0c0506040f090606020c0d0f111305100f21080705060106260103020a12030201060305011a0f0607050c152b0b 72
    0x1103001170200d0010300540c7c0e0001c048a4000c40403407a00c0f103108400d9825280810119421168041c80081601d4030602c6007419400e5610340c801c050b2118525018182501074005001c0811140c00448941c80714010071b803805508500081426502c000042c4010301400440b445454204002c4800b224803030340c00782d0305541c0002c1d2000300c42d0700d60f00e00001c4826003100641200c4100c0b428000140c19a4a20705a4454074101d1002070350f076419480507024104040e440d400c003644408043c99050014003030300c206441ca0800400a0161103540c80b40c4040c490050301c0d0401c2440d0b65090320f0002c0a8104101217041d408031205810742c0c2c1800211000c80d8500b280c4400c0d49150040341264886004504500d00d0b0030300c2e02c02c1494003d401180065900a000b00940b40d1521903180b18210740d01d4a0700c2c442c2070741c8110320402d40b40c10f01c107880d20319400c0400381031034104010401124080101c0e030300501c680288181032031100b402c510140d070502000b112070300c400f004285c042c086030001d031007092 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 800898174 1250 800896924 800896981
    0x61113090b03070608010510170709290d0f02041824050d03030b12101a030a11090702070f030308060f06031003020f040e07031401060b0a051c061805 66
    0x529030b10031415411510141c480c460762420101040766810309109c9844c0f440526442488151036002000d6811503c1c1504240d8601c0f03480a43e200e12844088440456400207200e12028040790f40d100540d020340e814001450300340d541007008410040b003881084085d0380e40510801c1005624015049031070042036540c0039a080070700141580c203031607902504160780c400313190001c3e0b1103075401d140d0314090080032500d50740c1c040300d01c480c05050350303040c017081c142e28038000050035040025803680c200d0fa10584180380c8040440030b004030207200402803000c500c600d850016400c0b07a01c03a880000f07540030307a840c2c002c28a01407051101300c0d140c0c45156030103107004000b0081c0440c00309080c4410340c0c2c2c0c11101c0b0920701ea14140041c000d04106000c008407401141000020030200c8102003580584400013801100da80f05c0c00005227001d0fa00121002c503104000303040700c0810485455010845180300014440c0c0c8070000007103180101103c007070807503644409200c60600c800b440005602104103501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800899280 1106 800898174 800898179
    0x615071212181403090306010e0618010305010e0615090403030b060d0f1b0c1a0a060f060c06140717041e1a060f06070b04061113090b0307 61
    0x31a00e20001d071280480111020054617041c403002400b8001a0786403440442110030001d040c542e01050b4103c0d021002d186036801c00b0b0103107005500014080f20b480c1c1c4901c7ca0041c0c041c000c04003007160715652005681d10420015402581172074040354482c1d000022842c68061420202c00140c1030000940c2c1401442d40892105c601e145200f00b403d6070304e07140a03a010040400064268060000100510301d0080c400b107810043c454000103641d03a803164221401400d0303401500004000c27400c0e01d01448001c0c05402c001000a2401d03140e603051800014001540c4200c0220020344010f000600348034007401c29101d121071000d9460b000e440d0f1841c00011204180e020703410000c01e4180031400d030b4100404c41180c40320000d030800d4903108c441c3c1c50740540c503040180121900341c0c179004040038180400c2d0141c82c40400f0b50b0840c1d8880f600345410030f0107580d0300f0800e030b074000d50041c00b08 = true := by decide +kernel

theorem cover : BRFrame.Cov 800719424 800899280 := by
  have h0 := BRFrame.cov_init 800719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800719424 ≤ n) (h2 : n < 800899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
