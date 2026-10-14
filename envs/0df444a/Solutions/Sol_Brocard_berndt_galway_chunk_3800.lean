-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3800
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:51.964144+00:00
-- url     : https://prove2.me/submissions/74e0f9fd-9db3-4912-a40e-6cdb8f7d3bef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683273381 ≤ n < 683453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683274631 1250 683273381 683273411
    0x2c032a1606020d2703030e011209060c0306050409020a06030e0c04061e052e031806050103061107021804260415030606050306010818010906021b120f2a0109060609 72
    0x1005e40780d00d130429220201070840102e070b0741c03080c003960110700a00380b0590405201440d800451030521581d014007100e40c44005000640300510f000940040c1b0442c2c0c1004800e1003940400451740211703081d1681059000001b50658586410611810814130340204042151482a2004040c282c61100d40a0300301d140c01501c40403401040e04c540340301d8504840e5910300c40e6000044014401c9101d22250580e070070510020402404101c490510703000300485281d440000352030489030b00920710303484c403034254650040f00580600708507000303400e24000322110039418210fa50600c0404101c540c840d4074010008400450101c6110305252808000780100c035408000ca0f6402902030820910f55202c03031050003142c0704000408481946440341e4002008032a40040c110122542503110b10008800030b41607c0d40c00030201c01c030b0364440800c4007803040c00402005c3c2c902805280c17a0000c640d02050301c0a8003504040c0c56448660755209402000c10540340305040240041e240200030105c0005200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683275881 1250 683274631 683274707
    0x218030c0d02011e12090b06031204120f08090402040e0f0c040303200f061f080c1807111603300509132c032a1606020d 53
    0x200b00c004c19049041844903018400e400000210088200040700c51400c050b040a60f050f12014807078090b81405d5440c1c1180902680e0076682580d4030200b5000342c0365911060311140401c2140c4407e024408802180d41d0380c03003d800104501541e10182d0319248001d80c8a01d000200065003103c1c0502060022940c002e040325003224564600c0203203101c0c913682907032400d40c84d0500c0048070311560082003e001c00441c168040860704055002e0401e49484001782c541d2a10b250068011201200008a0801080c0d0007608650b90342401942404503081c214201504552903551102e8003a03400c208115580d0070481a0000c5003000c01e258404c42802040300f0104500310008103c0081003294582d551201e010303100540c0240300300284513a2a041b90310780c2c00e030420f0f07945592011003909014840044100c5014105c400c03a80d1141001e0304503581c0b0843c129a40d802c0040c030406048803e20f0301030040d030394040c00c1550020010100f1140e0024500942d500e11890b58040d0030b02c0c01203c24640c4444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683277131 1250 683275881 683275907
    0x605011b050c040b0f0a0906060e040b030a0b07050c030310030b06030c010c0b0a15080f0d0809150a0f0f05060a09060b0f07260c01050c07081206130218030c0d0201 72
    0x104540342100c0024010300f034201d80d1710790701c45c0d11020005820b00b0070364019002c860341d58136051511408801007000302d41440c2c110030b1b01350300000190700006403010342955100815040043c00c01413041541d41c9507400072140a092580301c10713801c1c018820109402940300c94100c00416806011000007010007242403c0200114200000b140d00c0b131001d5041510101e01d200008a003035a5a050341d10390710709062810b8200c600500c0700c0701b400540300720010751146030715000800300d182483c94160b40e078890081544603119950001c801038100d040c040ca000f4080314840129075030400c0c004005064445a0040c5107040c03801c0c00c20060942404156000c0b450544401c81d16040c107070810551200700c2c03003d80c007140512a45803c50000c0058054070101120f100200074950311880b07050317564882c400e00501140c4060000301d04071b03c0704158440d40140d01401c80740001c044100706a003030743c01c1070f00f075240c0b42c01c4000700704201410f080111405c5180c08a641e10303a01309498001070000c180b5505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683278381 1250 683277131 683277139
    0x30d0309050319020601030c05060a0801150509040606050315100909150509040305030403110c090c0903010b04050c091c0b062b0b18010606050406051c0509010605011b050c 76
    0x20a08060010a005480115500c4a04003c814962200003034882000f400708660b040303501040400d1605004055034800710064450540d140d082c41000c090116040c07a0b4402004420402108a900d40d0b00400009084a44a0303d03124201441d01c801040600e800e101d000316204050140d0480d03101122604441c81c8200004904110103c25403003840d40340c104941151141051000309640000110300c598000e5440000c07402c859034440742c48245100040d170f403001d9017801103000200c41c580180a001001000080c0244161001c10240c84040358800c11001002c1400022820400301c007010b0016804a407032521006640c900c041c2c3e81002d045e4501400c90140041c610401085100000064010302c422155545290614007284110340d103854001e03c054040c00d080b60140180401c1d0b485503264203081c50b007000e50880312074111407412203081481c0f01a5207038070138907403003094041e2040c00004501c40d4100ac0001d00918040c803d0000c51505058081c4007144012944c62103045040f5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683279631 1250 683278381 683278391
    0x803071505070c150c0c0203010603080c120310061b0506070807030c0305092805010203131101080f07050c15010803190f0905040902010908030a090503011d15060d1b06030b0f030d03 80
    0x105c070444400c0c0c03500c00007c2d055860300c2404400c0c031650b40050524280003800b1a07603100b202007501041c81c041a1a0804690409030b014041c40d802100c0145132095400010750b0034113240d8884621700002600e0540c0454144400d000046915000b0082100783c030b4142480181081c0c7d22a581c0c030442401d070aa80c40c18880561601c20084451207106541c124009545900700150317040205548000704a03400b002c420144c04107540208196403140c5c240b086d035001555210101902e1302d0340004201800c5001300c0040c41d100e50301140d003040c043c10051006584031918440010316040c290310585007849402e442c00c08040f580484a403080e503000351808100600684010380d840039282d00840b0050001180c185007050340808400d040f00c4040f402030000a90644000b98695915140c0001541000603580d02c154004003859801500150070200d040c5490740728407a40c10740503001c4280c04c1c0c4210300d080000d545d0501610b1003951003241c29040a4045c107001a95985410001d601450340320 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 683280881 1250 683279631 683279651
    0xa030b0a0e0a020d060c1e050306130b0d0305040503070602010213060f02010f060e0f01050a0605180f0607030801081011041e0e0c0d05090109050a1b0803071505070c15 74
    0x1031220b490a02d41c040c205100800c060f02e480c8004c1c024442c0041c1c0040c4070208a20040c15201601c2c800b10780b82074544030b1031a124002070201d020415011280e4103030316858003601d83d84030048170000c2c03240030765600c1d5111401c0c003003014206031180e442041107a005004100001d400d018041c0b00322001d600788207400040c02034082e40504000040418814502400000e40354101c0d41110300c04c1144102002d0030340c0e00c4808010510301c0c01d0240394006031092001c2000014046840341c42c8500042c48490010031031000564194000b00b0120001140356004110710f074001c1004e44616020840f0602c40136002d0000f4400d14003580c8a5141d181802400c3c20400c0c011846140e400380c10580d000c8141d615000c0c4280b160365110030700350342000349040d001030103048041c80b424003182c1e400030180c560390031161140c0c07482001001140300f584400c1140062203400c100014801d09114901e2050410403c030300b080d04840b0002c1040061100051441c40018000b0307041c00307181421402e00007803030061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 683282131 1250 683280881 683280883
    0x9010933020d0f1d030a05160503160b010909030c240f0209011103180f2d0901150f08090a0c0b030105091b0405060702060f0a090e060a030b0a0e 64
    0x103401801100305100080040500d04650050a030b0090885014451120000c013141c07407004103003040c4502034109000d8580614400c3d8000e100e01810700c0c1c01d08510450075190a1f045030300110b96804458220509041080b0400c148140140b02c1040100107403031041c2c40c05000304294210041c42030020000c85410303111141001c8101941c4040204201110b80c01e40d14025440082100c0c0407464080403420381c0300c000001ca61083c10b0400b010b100c0d0a11aa0500c04903040211046071300a9001c90613142203403401d2604842c040800170000107035900c40c010b20521540607084516102a08640c05076850340048450940f1540d9141c45001175503a00c9910b400c0c1811759400a05a1040c5000090045040d8002d94141c41040301c7c000700e55101d0f840b81403096040806100ca400740b00348020801450100e01503c0240d0008e006035281c0070000800e0700b029031100400601190f40340d0700620003124007a1040f41d00102c15241400010f045464012040780014940c50f051078440c01c1c90095044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 683283381 1250 683282131 683282213
    0x105010f0915080d121b0206040203070803090d08131e1a070305121b220f030f0b1f030602130602010507020a0609080f030c250308040b060d02130b0108090109 70
    0x50030001b040d440c01008100a44800050b182a8402d100e5020003040522010048407106200185030b0725544642d5501c018081e00541d44400b041e008a4a0025440700c40fa004500500320b048180001c2604000c044084c04100c2601070000a40a10007280065003210440300f03501010041c820703a555800b00745010440e010040b030b8100e268041803001d2100c0011144a6200110450046403c0d40300c09000a14a11610018002c2058000404e000c282e8851806800001c10f1031440302d1291044088400035401c1d0307004544403940001c60130480010b074101c49001d48001c2c03009108030308100000a5403200180800380c00603a480d8002400c020101e002c480c40c0c01c009600280d01d0b445c0403484c8403040c0e0020800b0034010012600320034109481c0c103c440c0501945500c80131101e84030758440b5810704a005007d00e0f00200c4901008000d60f07100e0590250123510010003040346c0d440c00000500040b00a001c0d4842030f0f0602542100150094007045801d41c90039001c00300d20b03a80b2102a000c428 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 683284631 1250 683283381 683283401
    0x20a2604062304090b040b04140c0708120112120309020f0f0d0b0c04030b090a05061503030d1113051c06051b03130b060d030e060d0b030105010f0915080d12 69
    0x70b180001c0000380c1c1072641e0001e10380400112402c00a16840d40107100950390402e9030094001ca2800010300d900d400c12010300543c0d030003213101c2401c0400700000d00c290420280c121020141d4260046810810040740209000415103028070250160307901145070a02200c101c10303c02c07038140000c40342644406464000098100741c03011498180213080c0c10465202d40010760704000c41d640020141503002518809003940301d030003000ca903654902200031000700e504040d503040c0420080180a403803140610030f01031000c115415500c09400301104082c000b2540400c0c001c44400c13810201c0d041c01c8a200c02001d0390080310220700303aa6481158800882c82c4030085098802c04401d00202100f601c46209801e8401d0a900384140c8500080241e00c200d110707802800100c011401280300e003010b40281011103038000d8003299441c00c810000e0b081d41d109801c0200c001104120800040c10a405603085c0e90042c0c0e040c025440d820f0083c5661589607102c1002c00b4046034101d2102e100c04c00e50f0000380c540c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 683285881 1250 683284631 683284697
    0xc10050c0a060212010f030b060d0f02030f0d0e10120510050d1407060e0913140102040603050907060908030d0b0a1203030902010e0a060c0201110a12020a260406 71
    0x41c45007494040c000b03400910440c0c0040c0f90300000842d00703450311011441542d4015420303000c03e03540e080c2002410a500d2500b180c10b12400d00d040340050b2410007040c03912000c0030b00034200d5a00e50a0b4024240000c0d0b80c066032055034090050303100e1070307007040841e000145255804101c941d20803c0a00000c40d180d030044c0e402100f4800740c5014400cad54102c2c01c060040759816202c44555407603080b80d08000c0c0240c065803020282e40400e88c0401000c550400c1c1e54800d44c07480c80141c103110310090880c0c02642c00350700800d807200204501106c040c480c2d08090121400c20f0b01c49242031480043c5d82e4006c42c510a541b03240c0e07070fa0445074182d0700c0684c240300600a2030b01c2a075001420340340c004d01030301039244228045055100b1228036441c00c1c02c4000245e078099510151501819001124020600e4405115502034080d04a0103d0000c0c540c003440c4a0305038000742074403d50381c07500000c00c2480c642c00098580041c40c1c15000d202e07490084508994683c070303008126158942c80000c048991920304212 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 683287131 1250 683285881 683285893
    0xe1e0904050d0315030209010e0601020a48150c150c021605030c06160204090b040314190e010203091e0406080a110d050708010507080f180c10050c 65
    0xc00c1800100c0000703109150f03405000303000c9507031a44a03c41800f408001d41c00041c0750014005e9121005649501c0101441115180d022540380d40c1c00d0309060344440220f5400c040d01c1e0303051034090448420b01442000401c50140c9e1903902a0700404071440c0240420303242c001261102081c4a0058041c105810440c81d45180190100e54402030225515403c0940150b111211825003422648012600f0103400b400529250400b0001c1c0760740181026004041400e0b41d8601680392441026540c0303100329542d455904050a004e000b2030031002c3c0320101100d04005d080c010a410b0000d8802403c03460034081d0303080b80503800603811030140000700c130307089205114005c40503200070200b0100030009840420107261610701e41c64640ca4020f0024203100310b0228041183d0419014955045000c5c4003951211900d42d0501425100c080c0c8510000139611340a0009007000c0610f0640c04c803003413941502c1784e0300f90b411000e6160142d4100180c03262030b420303448805260040b000c98140d8000300c000d440c1c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 683288381 1250 683287131 683287133
    0x40e0f0708060403030515180712090501050103030305060306070e1c1505010e07020d0905090c19020a05061006080415111b0d090302030a0f06060f0306020702100905010e1e0904 78
    0x60b4031401120158006400c08010800c4e00810203003904103800d01800241c1c1200f44d030f80c00c4500040c006400c0e0720801000d2540c110b512601c0e442401c80700781c030800000c200d95142d1706004003900c0000d41060300c250000004e00c481242c1011004107401c0054807170303000001070000e0408580020150103840030940c25000c011b5542c0340d50110b4142c0b20340014444050310b03002404c0703941d281e2940c1540040b95130580c040c13125140003a03256a00107104a0030614010000480144541c01e00c015400980e11501c1041c1c10441d00344a40c07540040301200c2402c0303d9240c400c1c01807004d00040d1001e03141e207502450051820443e9085020f2800c0c0500081d95180740c0707005007000b201d50440e20920796005060310007480d05d101c1d81d007010449800400800030070b026600c174000d40268007001100c0441d40c4030b20000e0a4000180407000442c000c020058440c5803034011310102c040a01c85980c10041c1194050000e60b8220307444044241c002c0d105405c0d10305d010300c01a0010304103950700d0781d8402c05036006c02c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 683289631 1250 683288381 683288383
    0x62d0306110d050c130608150414160309021309150c0e0a150203041e1211180c0339091005040501050f071b090203060307060504080a02040e0f0708 65
    0x42d4200314600c04120940c1d0b85208040c0034003c29000b12901c241d0340c0303000c0000d1445070034540c0d0015070b0441c800b8000740f00f00001404440308000140b0b05c1d81d603079000700160884400d403032000281550600380304401407a0700040c40000f500201701c8074a550341c800c80080c0616900404200400c5540c100803180a62101030a40c0c0094011988201d005440102e80240c80308096101e000d9542c00550400d420040d012441e203554541e401003806803038400068800c0080c1d5103261550184500d00d83e2040b00c43c1c00e01c50741102d0444c030405008003020034080454003c0044a9001a9280a046d000e20554588200105004c2c40310060008052000003c5000c50340017481400340450f2500c03082410003106aa450040b4465503003c12018024098149180001444664407c20b007901000118981ea201f20200c2a0481c1d0315450740402040000c0c1400c00035003001d4041070401c581050b181c45030240d6500e24000c00240195210540d0441c0f1400410200160541a50580c1c080325143ca40c19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 683290881 1250 683289631 683289637
    0x7020114010f081b03060109050417041509170d0e040b150306030d02060108061b0408100605040612080301051504080307080a030b090402010c0b040305041a0d050109062d030611 78
    0x410b0b00341c024400c0c02d01c8036080803082c900310048003401a0205070310301913552380200b20003007040e074804207240d107070002d1307040550002c1c40500740310860852001e004000080c0060200d07000343d900071400c100103240341e0301c001403c00c00c6000103180c01440142c404004c94040c00207019010b40040040318a010150b85901c043c51040409608591066540d0f500c202e03030340c900038890700416800c00400700304146080c0146040c0400c081c1d100d14a840c0c1e54040c181e141008003840020080d644500c140428035150040ca001820b242c10390040702885926172941510041c424a4030480c290b925845811640e003060fa40104004000c3e26124029801c150b4000d03070105940340c000170300c3c000c148091481c05d0302c1d40324003698044c0c1d64505013142303594501100c0c03070014205038103010003880002001c95040501d84000c40180720000c2c1c41e026000700140586006030030000768a03041010512042c0b81d03001d07121001c0e414604516668032100c1d00148000c00494001918850424841c20b000c00009030007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 683292131 1250 683290881 683290889
    0xc060a02060108060708011505210a05040b011a040905130204020408060a140103122618210306240301061e0201060b0306101430010b040e07020114010f 67
    0x191410303035417845003c48400c1024002c800691414018425030303148184060070b00c551203a0b4107950300502841072680340c540101d401c640403030344441c1000201b1031807403100742c014019000b403420704080d40c41c214202c500550080f0040d003995080000c200d00c4180303118032000d6802400031540d5031b80714201c00c1d84409044400c0d1090900b03150001c040140c1d41082c49048079000400074481c4018280121260585403910700700f007110121a101d68030811450007801400c40c02000075251032200c0d981410424454664044886115001d400c207141c3c07041160740c0000d04880500d03215002060f1100f01e054030060090490001200100e2400d03004207d5030700c040703c4040584013000c08040100d09842a078040c0d24148942480422290b003004003442482c032105041981240d03070303691161030043e003218070962410b9694058001d8503040c4900c107400e000360f602c14040700c150b04090b40e0002512581c07260b1800e1030040b000240d0310324803c1d0310000d12103510280e26030265a4802c01c091000f0741d2405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 683293381 1250 683292131 683292133
    0x10c080720100c020d020616050d050a0e0d020901140d06020f0d060b03041101030f02090409121e09062615030c010e0901050607050a1e05010605300c060a02060108 72
    0xc0744401d46009902c0f142105500800c032a000744000c2d420300203983c210481c1192107140450310600092810b008080b00c1c079496a440c07585610040d04010560640404254010b9241c0b24003200542c5803004460b041d903c102e10141e4018910402003070480ba048030b0058800d0f071000c0781c1c1c6001044218000c0c0700c41c480703009041c041705880d22404a590310082d50024038486134411540700c07550094201c00b10402c6096401402c1920060110302550900e03002182e9150a0189000c0400e4220301071780b9501c0000e2000742d11239501c00c1c6c0040c00b032000070300880050100c00c0d512001e00105981c6409011420065440f8260030301a002c1c0125011101c100c2d031003401500c0815040c0d500c940412014484d0040a4065903442c0c9011710803517620080301690580240c01d14070000c60a4031100e012031050508072071003441014100030782124810341200b0300c145080300400d00c40281c00c5136a40b41424040f8640b41c00310b81c8001c1c101d86080000350b40b03030f078201d8030100b081e4080320f4020941c54100d83d0360320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 683294631 1250 683293381 683293399
    0x25060c0807171906090c0c06110a020607210606051e13030206090a09110315030109210918060f08030c120f091c020f0d0b06010c080720 60
    0xd9042d03448120301d08403501e201009800140b101c3c00074070240c07040019118030002d002501c80e060385094030b41c030190420201d07914400c0482003100340c2c07160010800034801c1070350034080c00043c000c0d01e07488003821941c10440d020b000c0c0c2400d05850704031110b41e000d014408104481d59600040d00c01d0b041340c0c0c079049140c07504004461025926000b1906c0350b860903003041100d207045a08007c1180c20500c030490700100d5120000c510350a19104038003001104084c019100d03d8803510b0529000e01911900b07002e82d0400e145100020300d03080c0418441401d2103100c81400150020464141d0180d6218079100f00c02400e001c0341200c0540c4c070080030b0302d014008a0b200d0a8491807419968811440d8100c00c41d07001012a0401107000c2c4090f003460781104d079001d481c00100500080a02000f80c0c21860400c00000c1306c0c41c04c6291009000c90122010380d86171407500c4a03511125200d450003804181031182800c8000100714035113040316801c561000014131509110306121003800203039050b15005030261 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 683295881 1250 683294631 683294641
    0x30f0603010c030e0d0f0203040f060816090503070320030a1209050a050619120e030a030f1820091815040803010303030b04090f12030501061106040825060c08 70
    0x2901801040c00c01c82d90090401e24405503040386c050801203c4d01c011408280404100000c029003160000c00080e034502c000d500300b0a10001407d00c070b4071740c408140410810b00700016200450001c0841c2e81080000f0784084502c8801c545894911202c2c5d94035000f00e05e401000c00403210603a48807400f07203540c0c00c031200380c0728030038450201308c0741c09001d600500030700c10a00d15164601c0d907403032034812170b192075030303107103003282c1002059402d1805c040a1681000c9038903207507250326201f02140303804e108500b404102d200c6003001c5c02c00050900c1c05402c08042030802d2001c50039965051440c1c00d00640030010601c0c2007800128582d0341c00b003000740350340100e0554102001d528154640940d0700260000c2c90360f403139540d080c0c0050a03050b034043c0e0029200d2590a0100712214008000ca90140d4404501904135420040131640160801c10a004400c0d0764943c85000c0041c101e81c3c001d030302c040080d5071068200210690400013004980f080c00b4000080c0081142580119181210685810004d900d807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 683297131 1250 683295881 683295887
    0xe070207170a020609040902030c03190201120c05031503031903060906060f080f0406140708041115040614040911040603050a0c0c0303230709060801080f19080906030f0603010c 78
    0x800d01c2d02a51090041c4024802407a0991052041510007811560721110440103c1e0600f400803034030343c500300c80c0f13031040005650f080204910210301c502d00810149030001000f03441c500000c2c00c031200c10032040841d0105514200304a40c0d0b440088030b5448081c02032200300070041c05540c020076900c58140344000070068020862f841a01c0c1c0baa480b00140b41e079a0100c06083c00d0700007031007969002d440b40c007044895240c50a00c2e9000d21010303070307464002d0318050170f08420480c00c146c410741c050200c1640703200d40070b81aa0199002d4855500d41070003040c02030300f80000d250181c2d40080c0381b03652904c1c07000d00c84124a88014000ca40458509000383c0c0d849400040490f80700d0521100030a0740e401c00e840000c0e10a600c490400c80304150069403445400c000e100e003814080b05ca88005c285a4541408955008001a40144130040042400040c01c10b42c503a1140c41c0d9443c10701c2040710302c034000740810000c6415509000005000c00740c403841d206500c200c60385c03001d694950084d460488542040c0e44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 683298381 1250 683297131 683297143
    0xd0902130b060406080c1911060907080c0105070c0b0414150a05030c07150504060b0111061b0903070812070309050d0b0105060d1508061f18050406060e07020717 71
    0x10020505403e0625244080d14140c0009000c2c001d00f85042040c40d000580a59125641c1e44481d9a2069600c801e86411454880050903155107640b0900c400c0109580001c4c2a0940040a1034090703150507041c6000d40c031641d20394000030740e20140460041250403404401c044844001c41e841003445030922004240761140b00c0c05000046c104000144203500d0580042a03414031944a2206000c0b854100c081241e03401d480441d41c80d61aa2100c0d80305680c00a83c0405d4010560702400c034a00701411003441949001d050036420b00000300719444640c0c0c060012400500012040c0c40742c5030201040a41e0703e03801901d048010404024020500c0e040010107164004d82c044203100490342004100101034121180c4949030300d0700c40200310b80451358003040b10000d150080c014a01420b2080107040c2c61250030300001c83c0c02d100501d040104e1120001d02540300301205000280c42d85850a00c0005020a81c00041d6401d0324002444446a0b0020314582101d50744c04400e00142685240603032505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 683299631 1250 683298381 683298401
    0x28080718060302090d1208010806010b28090e0c0301060215070f210905060603150c030a050403091a09040609060602073c15020102070c0608090a06020d090213 70
    0xc400d003981401550300a81c01050b44403801452400240e040b40d44030605401000d02c048001801c01c0010044500100141c501401c0304500880c02c1c0032032944180d0022000d91101a00c083c01146400d150500034900c40028111213070301c80c42940741c040c66120240d807080c440c8e2801032044c5458055055144a1080e0007640c0b10b0f510074000f8180780c602151035243c4e200840d1501e40b80303030b180710b03503241d501c0d1045440d40362045c0c0203408540f800340c04150500d04400b42141c44401c094040204c018480b8007165030158101c080041c07561070f2410f04071166146608240304040306000da81516903c44c0024050418046400b481410b07112403416050311010b110700310243c0c0c8036600c00e001d407440701e14210480d50408100c01c0a074283c0301d00c40d85003202ca501d195684030300b0031000a0060005401c40802e102944e0f000943c0381500c2c0f555550a0720034a4407500042003020303070100c0c03d904010311034001c109400c01001c0d0340750307078091480d480107103d1030754100d2084060700500001200580101140d036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 683300881 1250 683299631 683299667
    0x1609060e0f070e0303160308090d14070302011e020d1503020306190b04020d0516080603030315010203070f0c140108010e060114120106030204050406080102090d110402280807 77
    0xe44800d03081c03141040d0094141c0007400401076008003551001c00141030101941221800c00210604001d811040064207801c0340f40c012045002c803040e002100b544241c0d400c0000c40e9694141c50900b280108915422240c50610b18210200520383d02d4000c0d2038824624501003000000542c8004490409171200941640040001546184104c2800701c050f81e007500000c0341d42601d520002d02281c0c811300c007036407009603510140400c0b03240310070918800c58080d081c074090b68100303440025600d00000f06000900e58402030580c1b040d074424010354081ca0381c02100503070107a04619100800782c51b1030040c882004944c40c901c5419600c1001154100d6050101c0ca0700f0700d898801c0111804104030300942540c0c0010011481d1600e00b40181e07030f008182e80d81d001a1501d041c801080280c803403660102c072403030f8010300c0050b44640d10502c0e101c0143d640003145403d50b20a9601150181c00365101241508031150310305801440400c580e10a5900a960388002c180e480c518140c1d0b015070040044080303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 683302131 1250 683300881 683300909
    0x9110702090a0e0d0509190807030c150c02040c030204090509010e19020a03060c0203090603011403010506040204060512190c02031c0501030b01120f0b0a0912020106120b060a030203010e160906 85
    0x4c80b81c001c80050404400c098005404e0800c00080e2603440a1642c3c0402a20341c444842003007401080d0322900c020341a03a41c1040c10ba2411030308020051421010007a101e280d442c10020040b5000b42e0445000b010035040c14415031a0800160b4001c05003102d0001c603030b01a500c290300700c95100b400e801440036401440d00c134138141940c44074401010202c55090035403100300a076009550300c15005c0d43c004c2250700420a01a0125809d040c00c1d91005041d880c0502c0c01030109210068204041d1003480080c0c06400c24507503124520000d8100c641088411134a140101e1030b280c09038040300904480104540717403590810110300c40400c441c02440048c3c80c0d082000c0c0184420310b072102074089054080c0041c8015080f0f19122000c1011040c4c07422550a80e07203001e04800c0080340100a0015a10341c0002c000c110b16194000000440007400105020031040020707030103564042400000d580c0141c02009080010050f042c1e5544040c0811208160300040008078040d20303004101c1541c1402c03c103510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 683303381 1250 683302131 683302153
    0x601050108240319050607170c0f0c072102010917070314010e070e0403111b061e0f090a230603090a020301090c0512011808070c09110702090a0e 64
    0x1659241c400c5080e64580544020303a0802c10040c0135030030f03000d40203401902d0181040380014100507110240401191280020000e0356003101c002d42d8640c040d00e00c2c080b651200030b86d420314105000703078001d4641507482c100424502e044688500540038806c2e00d41011127603e0700406200310b030702d8440096480d4001c0e001400002c065600d0280d003817041030008162000c03004613050814070300760455015140d420080006065012441458001e078034800381844281d51404240708400b1100306c98000e6400117460071504491040c01000034004503c41e5884502440029446500080019204040081010805804001803007a030000c0640340d40e200458080e0034414580c00040109509004020819015850a014416030144200c40d8a42c241741014104581d0800a40490b04c2c5603140c4104040c0003600d8036010000035400020098850f01c4505c2d110b1014a9240c01080032981480107204801394850090070440303108a404000e40e81e204034050342152044035000d025035100c0e0461517 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 683304631 1250 683303381 683303431
    0x51e040807080a05041809170702030616020f03040b0a0f090e06010804060204030803090105040b0c040806010314010207080c0303090706050c1509190308060907020111030a3b0601050108 82
    0xb08a50660802c00d05082c0e950701ba50b103081c0700703029483e882c81d9210001d01d03040151200c05410305890a003181810080c840e0003103a51044014442580e451200c6d00d880c000c94000c10403521400030382c0080302e070340c2d0f0340f91f00c0001c0c40d6410a0031108007150740644060a001c0c0138514135015106114402c100c980c3c0c2e9a001107508000103442520495803c00020000c200721000451103000110004111810a494000001040103150584034082407005004088000c51000e04590308404c2c00b1500d00c0402c405640203118205c001812a100041d5403000c1c003401202651044140c9020340d14000d946070301c00d135070301d00c100d00811080ba004820310341905c0990410164100d04034604445034103900401c80c60035103070944d070300341c0110b0005410401a17180004025602001c039100901c50700400307a00c14403250001074641c2d01e100340c40c0c1014001d801000400d140901240b56a089482e20300389903540d00120003007040b000c0c14051040007140d2035000f20407c40c0151446035030411407044081c00302c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 683305881 1250 683304631 683304637
    0x51206040308060d1211160f0501050903010212180d0f0e10090f080c120712150e010507110d030605030304061b061a0a08150f07021906051e04080708 66
    0x503030701484c80800d071000300c0c40c282c0c40b07102e40e000540c641c00c40208051054a140210181d40d4202c0601880414420000071115010480e002030801035202c840b0440001c0c00780c018a0300a050026070a410001580000d45461603040340800a54108271055441180c000780c2981e5600040744100c074450043c2d040c14200207515860515240c04c0c1c0a86079071790610101c07250781c0401201da0050008201e00c0c07911150700300000704804000e0500320b00d01902d8805207001101f001e0684212100200e040c07140d02d40120b00300c03140301d0000700100d03d03121030060441c42e182845c0c0311240c410030002e114100e0092080c0001c0d954010002c500f0f0508e401000c0760880d1b0244c0640d0300040280303600b28000b606038000c5440304524400f4412001c20702e0400c0c042e15041c560721003642a40b012104050650b5800c8000b40c103c060156850a184d03505c01c0c090340341004100304c41d20810980314040c3c09100381035000034020703050400d028207007103106c0000000808056a01814010007001010000b410120017 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 683307131 1250 683305881 683305891
    0x81b0c0f090702101a040c0504050904030503100b03100317070302070b0f0f1c0c09180207170a0806030106051801090c170705070c0b040b0d2a03090c051206040308 72
    0x444105244240c1608150343c00a8804010320000500c00617651a1500500d424010710b0300e0101e082c1458000021000b50740a0000b0f82400070000209502007044821180a030905c064141d5807410054000002c0b0303220392100750782240030116030520070b00d4024101e40450350580d00400059003807001180903940026009580c5490420610000f0300ca1f203c05880541c20000c06546882054078601c8181c036403e03160700c3d08000c2075100030300c06400c1c2390280c1e0b043e180007810016124880d918005601840411104540315804243c140100703a011110600c44d80303040e0000e000247d0344805004884481609401080c1420070041c002040a5804003161892602c4c08131b0400e40c1203c14901d8000e006e64621000400001d450320a00980c1c11402009180031140303d803078a85011a100341c0750180c802a004403a80b107000c2501403440c4220103072100b014501d004030580c2e1003400042d000300084002103408440d07418000540b4689031b20f030600c1c07921200000e4010351b50346070740403940500010a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 683308381 1250 683307131 683307133
    0x30f140304020f1e040e0f070909240207021c0c1e0e09160b130b09010e0f0f0a140909030304032f100515030a0201020714031009081b0c0f090702 64
    0x139180805036030f64044c65044480e03003030240c2005c00340408561309001c15504a001000d080030f4500c000a04c494003038107120074555075281c2c245428003181c040607104443c0060751012004ca12648400000c0c1c611a01d041d01c103800b2514803a070ba81e400300c0302c070b9660000119500600704208020700005802c1e416403242c614403d40c0d481c0f8002d507510b500080c117150000030400714003042c800c00f080c02c00741c10107000d0403210307551070308000e0300c10002001d841883d03072005d00515070071590351000c5d19503012040c1d410400030f101070205500c84a154120103140188203104400c5030000c9020304601104a81c0602d8055540700101c4055622110041c251504001c00c11400340385036100c622018400c812040d03048040110b0541080005282c2d80d211450ba258800d4025104000041c0c6c0c0015504088901c0e55280306104c445400020707040010024600000e43c1c284010701080000c082d005000300091060100260039440d04050f0380c0d044200c51264200640601514040c82d1407509541d010703400d44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 683309631 1250 683308381 683308429
    0x31509080403051005040b0c1201060f0c0b070807020c0105041a0715050106050a0809010b090117210403020907020604081204020d050115140121050a020405030307030f140304020f 79
    0x83c1d20720385410b280a40000b0b07042e5451007400b00f00030030b40b5040c030b400c950404ca100781000d8031000c0c1c1c069041818411402400303210300c0c5221011b4011400c10006c260440320f080c0d9070b460300241c05840118121000001400360b1030b4107021540c000c0099405461000c0000107000c50850440225948610425a8076580800b5000c3e0b190b5080c7c041d450180006a507155211490020041c1280300c01a00e0400c051b4141500000c031138075075094240c112452000012000c000c1c04d4419401e0000500c2c2ca0111200c401d5503003031144442400410841f4820f070384940e80c0d030b50344100c00c9881c2c60061360010400f00c020490074244181c40480d00d600700740001d1901009174560343d15182128a20f078804201309036684001c0080210070101e0700c8481c1001c0c02c0910001c0c0540c070a000e1070303901c00e0000d28019903a40001c607101152950598000c7d010160440b540c41a850801401030a030174142d010010b00301540109141d0110402e5900507580030b061088408802020001280e8011100c00c0300c2c0c078090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 683310881 1250 683309631 683309633
    0x180c121d0f0d08010e090a021018080309090117070315140103030e030f030f07081806070f1401090807080703120f02040302040b0906010e210312070315031509080403 73
    0x1840201c1003640c44000a1035882c0303032524041d00300801603110903c1c24005500b00410410003040400030380380c0c11116a007011110400c16217804400c9212340d40c103402c0881011680c480000010b00d0320b80b030f045940c05076985e82c1340305506241403581d00203400750308890810000039501000c41c4100e001e120344040340c88404448040030324602680181c00241c0104500c020b035040503c40c20018016802c0550f00c1c04010402104991080c00c000a0a0600016448021b034804001902da0840d000300159602c0c0601d06150f04c1d11496400140c0b6140c45019604c0400c0c503052054407000d0354000034890800d20b00c0d4480e408a904001070940600286020000500e8002e100d020f2074441400001610b450640c01400203d590000034907006520120a11120f81c2c0c00140048043c001140c90004c42862120000c000c0310762039528000610010072030a8060356001101842002560707030812201283d0400003101040fa8400030f001c680750b2803580349010041d50404c5040c0c501409045d86000e5403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 683312131 1250 683310881 683310883
    0x30115060e1c12030231180e0105040f0519030905060307030e0115091404170f0c0102031014030c1f09120803150111120a110d09180c121d 61
    0x8411a80000341d001800c140c45d90a0462103129010b086803618035030030030440d450210581e05014090400c00c0c043c1c1001c1c2c1d80c0c0e89235089003d042d03007040001d1042c0d041500e072090b185030403414210f505019840c00240101a120003822180d50580e80e805071aa203040140080360740058600c1c03081584580000e06c840d01c0034062000380034080c0b544221001c0c50301803103608a55803142480480c1c207004d02803001282c0301d01c546840c02d8880d00004d99813a48154010142ca1080c11076030b07041c550000c020811502c02e01a03420086851840030740c24060310940401d6200c4540000e1281d00c8001144800103450140404030f940650600f071841072551900c0641c8101c11004100b21080c103000402c00510200001048101403001c2c02d1048501e0907642038103481c0c0d61042c89051403800b012403510055407280d0241107180c0100300c01c4d100040781072040285540000c0c0601125039951402402c142103e600c0303000802840c50382d4000c80001d80242e0480904404070501c002c811442440358a0031034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 683313381 1250 683312131 683312153
    0x13020d140f012912070b0403051e0a061d0a0521040b0d0e01020717070b1f0501180806090f070816050d151802030115060e1c 55
    0x801880440032403400001814680062a02400031903414020511500d851400d107050707580710401201c84000c1203003808a55002458881c65131640700711800010140310500c0104140c03030140381035400034000f88404da03010500f4050403005940c4807102c110701085107503000e00908036011507612081100034039207070320b4030b00c3c01301050720250055240d407250b4615550540c104480ca080340d46040c10718010322103850707008042014200c00e482c0c208143e9412400e50480303501651020f05c0450903841c80c104540240c00210b02150040460b5002c12951a103070310b01042c1441c075102c0200401400d0000440d040d101d811060f24400e240036002096011042c81980c1c8180141030007021880c00a00b140342c900f15055210154a410800c404000c0400c07044901040d10420740d03060050503024a804c81c42c80002000e555005441d00d2451014440c0e12070880307000e64001c0700248a2400305003400b68142402d84141d0340410b40d0818040300d03d081a40c691905118882c948100c01a01c90711004a452 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 683314631 1250 683313381 683313383
    0x2040e011b09082d10110c0f010902010c231f0e0c1c021206070c200102120f0c07031b21020f06070501090b25020c0405060a0b0712080c180913020d 65
    0x6c0c83c0440c07001c8002908003c3c6910003001c0800902c20b94109030000b070401781b0b0102c0c3c05030444030194050301d813400c80901c1425452880404492010f6003614a42d008132601424005400e810090300007a4000006100107004030014002c48140500350014008060090b0007241c014200000d484c00180b41446034038407036145903c0e80021802146003c1203550310400411340e590181400424003640e0000c0c0c0d5041c1620b503c0403841d036800700780300802114080d2003107800e450300c14000080b04001115032125400c4400c1d8800c12641030310740214900c0014440d81d003a500c030b0364104500340940f030301c14002c10350700201500c1c5a20305040d589416094030398580d4181c513550303060000d110400030400c04480710188401d00907a548030480304000d459500041a071481540c131030f0080344041e91a103001100804041c0d002c1d0f507694003c0d15100100d500d011040c42e001c1001c0c3c0b0b0008500b40b030300d44202c60403c1c652522440c0700c10803440030400c1c0034502034030f07500100005210030401600c848480340e441c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 683315881 1250 683314631 683314661
    0x30c090c040503011503110f011403072c150d18080307020c0904051902120d0206010801060602010c09150912080306090c0c0a02090402040e011b09082d10 68
    0x15909010503d42520560b03064000c0c856000741007080403030510303000c000c030030001118151208100000101c4a082c80c0308164a0400c40c00001e10120540040ea1410141d1040b007000030200305103c05814860070420740650020b0724030704243c003038212640c014201c1c1040710f00300181818000c107015600d10400c0f0401c07103c00e20008203100c0910b1b010003c070340c1c1d4503608441c103804925003540d40c16281c10a040300455481c074a11800310840d56030b01d139a032060b0032502c003c98034224070a0704020f61f11642807046030529403900c1c1010560318418080c1021245413502c652002a10709646154441308611210742000261413010424024403840030304c185000b180388546908100003040981c104c0641075a000800c1000240584500406c50400c0300e43c0441c0c19008581d246d001150241c002c21592210359440c2000310205030003940030241231102940d8440c4102925172042d10759490601428021071019078100d00c541107000b211003600170403990280e40301000c00e80600016101a11215040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 683317131 1250 683315881 683315887
    0x919050a050c0306060a03060f14090106030201110607201c0c030e040509120f0705100501080f160e0a0b090f18010612060b0307030f08043809030c090c 67
    0x1070203001c22080350908411006800b017414200f0000d01015154840240a02c0e25494260300420560b40322000e0700c18125840d51851400d003846034000e20a41c0412070209007041d004641c0349030002903052040c0141c0c0c071500300c3c00c40503498145c42560703202f039180e501d03118401d0058803a0003401034200c0740400e662130b0010144a9464017030403262031000414080d07403a0100301721071004000b0700d80f41c0382d4400e40446666001c0100f5440c0b454821080c01810300e04c92a160700020480030780c403107030480320100e050384d43c00250340300d4407515003081c00f40360782c0941c090b1201406004040500c040d00840041e00c005003030401c00d404100b201e802190203131880101802001000c80f400c92000c00074010f00c40003040501d00b051511310300302d64800340c00f400560b80d590ba00051600c04001c0107024541181c02c030000f06e40305142000e541d1313101d40551203c450b0312480c0b00c0c103070301000311178852031130711407642c030601c444e940c484071265600580d000c0b580c18410000c1c00380c0a9152048074038001d030600140140c2d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 683318381 1250 683317131 683317133
    0x2030414030f2a100b0307030204140919080706110d09031701050612040615180606021605010c110a0b0c0106080106050609030618010b040f0b040b01090b0405010302030919050a 78
    0x1d0b00038014140841d0064806080a0010300810130104101000000089864040340400d20301040d90308020740241c54020b01c020100d0090041d284106112821541210b80c2090040e80d46009088000c004440c1800f0440c001010342d00300810b54401044100e08051046c1440303c00e4400d50b44040c1c4c0401d0102c00032104805030741130308a000d800d0070340d001c030320704682039421030201c0e00002d00261500c1e50303c112405580003510411801401050b90881111411404c441d008180c01c6c802c4502521a10021607900c240d11103148086171016180d00d144036545490312411308220070700a6030312a0401c43c01041800c03454000c0d00120169000008610381041036880c2124036603046244602001c1c803681141c0d03540041e503035502440c036419400007500c0206a0b1030150551000c615402030070511500a0801d1640c001808440c0c00c0720203218284a0a0040d50109003901034084031550800c42484035502940085402400c0301040b2200340d0b00001581484c54641303d022101030301b05403101c074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 683319631 1250 683318381 683318407
    0x3011b0f1701060f030b0604030f03020303151c0204020a140c010632130e0312070e0901050a090c090915030201020d020606011b050f01151703041802030414030f 71
    0x207106032250002040080d41403800107400030b00303607400550406440d48001c080ca501c99105a400071580000d02c580d112940d0b14000e9125081269856112120401504c170716140140c42c1900e060400480c03000088055000e00c0080e500c4100003105026022061009641040f8014503104d446030000140140c105001030921503c501684240c10910303081f082c01e1200030910010303482ca000c50384244a07a0100a00f5806861480000c4401b8000410b0800488070b515074503c0c820400399450700e2420f4488020451160428094280c01c051042410310803100f003030b4412703c484103042c00d02403012035980700701d074045d204011244403400290000c10411960100018441c0808a0014000502e00100000c0ca040302890002109a92808003042401401d1141c031a111419a00030302103051100380c5100d07000342d94841c00c5010b00c207004183c942035402005440903500042d06040030400401c41c082d0203500007920035a90116a41c41c200d40040c800c100400d1002414020103484400d09007440e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 683320881 1250 683319631 683319647
    0x6080706030e0c0f01120e011a01180510030b09130311031206010f090314060601021e0606091005100201140610080403120605040e0a020319030c06020903011b0f 71
    0x325051500b44810b00c03042c101c0c00714200007142001d65214120303444c01c40040b42c4180e04840c2101e03000b4039103506000c45800c10341002c4200030703011203205e807440c074860300458000c031803d07109440d1000710701c0c820711661408004c55808000c1601c2d01040030645507000998844060700c0e82c85108607940c401100f0180c0043e020041581c01101540c2440d59162008801c4c10006140c41c0c10880400c035a9001f480c0140600005540c0090130780900082e0701071030b5590f80500f40c4134103000d441211001c404880001040840a10210000e0485e90316690f050240716500a00b802c85030480c40d0501058a8a84035922203255880350300114581c08043c1641002c10005450140076440e000c1084880039084440c031500541c0c14645207030807100700a03c2a00409040e0003c0740d002e41070045d05644502c00080d800855030084080e80c0079100e03800907403413050b81410002004680c7c800d00d6500411020340c00761101c43e038040d00114106a1850341c6001d0f003030300a40305a002c00c038041c02101c00c0343d40c04049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 683322131 1250 683320881 683320889
    0x3030727060e15120c07080f180906030127140d09030b0f06090115111e1b210a020934140d0905030a0807080f1b0306180a060807 57
    0x7030b07031804c815941c290161802c010000c41750214001441401c1010800855044205154903151030b08000b1041c02d01341300c00c06074014400c428400100300f00c1d1074184100700e030806818040391248142001024140c070780044056646525505582c3c0701e100301882031411140403990340d03180881c00c62500d810440000b400c04114003411008011083e1250407445040d240300c001d41d8640303041205000c071480c61031440400135034040e6904440030442003c1c691202c103900d24043d03806511040034514825050303014016800030402100340c8600c0c144140d102420005101901e1440300650046080c034001a41c44600ca04104070640c1d28804084801810341c80c0d4481d41040030783c00010b00100b2a41e00e03641040101140000c0703401030200b481e40600f007003652140c250b945400d003d1602a0400c1001c0f03581c00042040c0c400010750000343d402a02d4401c501444001500d210140340142e0140c000600300e0b600726042001059110010416051180307413000340100326242801c00d0182003034010341c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 683323381 1250 683322131 683322169
    0x305010e070f0f12091209171605010c1a0f0615120408090612250c0503030f19021b010c05070314070309150c05010b060403020303030727060e 63
    0xba5a5245030700c0104040c40308079a2030070000828a14000c1801800381100040c182c604240c0c0e81e120480e04016407100b1542d881100a0710312070f90b8035103541c841c6c0d41041903030f040c0e41d410b0401340304d99030082c0b43c0301c070303140b4014481e8203081e0b001600c1001400e00165030600c00728116404100c0c880c0780024012001c125010481400c0428100340701b4600280a40f0080c61000003107202c1c2d40a440f101c0560380c0d00501c941080b12720341081d201016910b04a041015040b00c03000703020304482802400d04c0c0c24416071203001189903a413440000b14030004c000d8417420040011000400351202c0e140041d00d800c031b074140c42840d89640d4a050081c00c40d0400c0d69400c05004003030220310f0109420029900b9151804c1c6400303680c500c018581140c088501d81c0082d01d1a51010070383d5a20107a100841501c090300c210000c2000c000702d41c041100a000f6444020740c99401080010305451007122005041542c68040071104180c030303ca2034020b80307056003000000516400c48a08685017a101580002c1c01c084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 683324631 1250 683323381 683323397
    0x1050417070b0f15060f1206090103150b06280315080c041808040f380a09050a231507031b02130507121103011e030204020a0305010e07 60
    0x3590360b100c848002000742c0742d03110040001500781d2440801d044c800c0708004100e1a80d46042001201ca10f4002e88072404814042c0300003e2034a042203800541030781d420082581002e04604041e401808012281d240c004606000035a8041840c2001d6080741400d4120358044045044000f0112421000d00c12070102e1080e004009148001c11400c1c00080d054901054802c40f0a00301d03c0c5480c500303940201542d000140008902c190659588c0a5402a2281d2002c01000305000561812004026180c01d10380e40144d0000041c554000c00071011141809145290340d5400150b001d00c1542c040a10200303c0409074114048140e0301c0309000380300303c0e40c0780c22203144a1540e59071406010b4000f4180729147c010304c1c0202c00b8801c00240d01503801840d6860105507465820701512065560b08045545484024201d4040e402964500400400344604582c40c0000a01c00c1c4851124100040c1e40e1903000030015803101d00007004500f00383c0d14080348551500c044820000340041151007000246 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 683325881 1250 683324631 683324633
    0x10e0409110d03051209070819051005040221031b120306151315090b030f270a0b01030201020d081320030d0c060515031009050a140105041707 63
    0x20142514981d1098410445100d06858103540c10701c5070303052100525006008020044000041507010390b030b00c03541942c3c0c028030b00f140700031030850740590010900d03009440e10214030910341d80a0b031340c868001095040f1a035003d41c5030002e078840348504040e807501b00085814160403d2b00402c82c0340040740004085920000010001c00e00014221510030090402080790201030401920f07000311801c0503044200d0303951000012920060b03610f00c0003190070750703030000354a4442c6401d0341c0c4100e40d2036089940305c3e96124901010a0b6112126002000a0144060400c0c10402034581c800b841801d081c00c281d4110700002e403809039004010010801c0e085c04200782076103403010707000310150700010300b0ba240d20100c18001a91040d420009030948140105049000d40c0400d042545501800c001c201d5900c43c2c02c1510040720070419000e806034004540d01c2d002035040d5020100e00e81c09601a40e0445c0e805a80c1c1500c0d240002804030520b82d155024082800f00d107080300034840316031460107843d280c21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 683327131 1250 683325881 683325893
    0x70e1207030b1e13151406131112180105091207051c030f0c0e01090315020f120a140f040f1113020a0915020a080d061203030506010e0409 61
    0x41c00010000519100400c0703801c0161110000c5003041c2c024051801e00d40311001c0c1081290000068440502070249554514411310412143c01a0303250300d54031030b54800e424007180400019002c90202d03610340d058a50b280c2a000640a2458074409091310341c00c001e044070000350442150001503900d4401405403000d000500400c0c40400341d40c0c6142c4940c00303420080c0c00d290300f81d908028400211030000400715415802207810b840c403500108405180607100b298400902a903050214004040c18004102d040804c11602080c801c1c0242c42e03e0100012648207400003030407541415000000d02480304030500603400319a0243e80048014075044000c25507a540141010744501103c810000511080d410804c07165000039204241002c2c1000100d002503022032220400200c0c401c00225101c50b90303850544c0116055402450440c0c510344800006911541d000621560fa0b1a8002556a00112103c01c01802130f20000b44518040001400b00c0380f02c1c2425074481c506d85040b807000540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 683328381 1250 683327131 683327143
    0xc0a0c14090f1807090f0c02010903020c0d0c0f03030e130c09030b04021206041104110405030d0305070c060e100b061603030e0309030102070f140a05070509060d1208070e12 76
    0xc2c800501c2040d52900078181100714040c0403406100c1c0144000481c04c815941c20451307030002e503000e041017802030300311b0100d00322001c490000b001a04010540c11403403804035090581140600c90700181c0035521107400b441d0b0b01c4070364404c0780400c9020b01010a02d103030455400700310701c00b150007c2c0310040035020014103902c2079020041643c001b00000c02c056449003110381840d480c00900325100b600709410015030400410f99810300c1581400803031100324440781c00b520112400a0018032111048500c1900604002030502040180040ca10800300d03289000d50400e14910340c1c0079001c00c00b10034406e03000781c0c0c0101040314003c0744100000d803001041c0ca9240d500680d054600052440c90501005003181714000410354150300100e40e890520507402e010600310b61045095405200b6440303d01d81e110255440d002c0d0260704041d00402c990306140d0380c102e9006400400d45248400596a4052150400008100000c1d00402080685038104452060103402214078050310146200e04982d266 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 683329631 1250 683328381 683328391
    0xa080312130303140a0501080d020f120a2d030b061801080603070b040e10150f260115080612070302210307051f051b030403020a080c0a0c1409 63
    0xc0e03400080310180b51099025440c000c0b046441000d003401c014900002801007030003140703690300600010444103070000812100300b60004010300180c1c200d00d080010250421402d0606102144207809161201440c240d03c110845440e0041e41084030403008081b25800b01a00d070252030b0030422903059207448900030358103600074078040b20319640b801c0c0480c4c2071030502c0e400049041004900810394003401079225200c1e15076600d005068a45c0c9031003564001032035135107800c041140e00c008142d041d07101e2828082100066a030036015510861070440074614264440004150b000d0a1415800d91001c44150003036403c5860a852011720000340d603c804407032000074030400906010704041002c08070000b2400001609032a11000d044c281a901d40710030b001c2c080c54070002c842e0480740e070001910515000300c948481e141c01154140a0004642d400a802903042d0b20840d55070b50001100b11000f85000851303080a0000741100b403905078255803284e041094694811422601d01e91a0070240c1c0e83d00c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 683330881 1250 683329631 683329651
    0x702040e0f010515190b12040503040510090918050615010306030c0f03020a0e010b03070305060d1b0f0909050c0f21010b011409030606091906080a020a080312 70
    0x25005121000d1a10764610280c900550078842048a08191a9104001d0020a0b82d43c10704c0844005940a1914018022074400325810b000700906400600c859950083c403070002c0702c2c0b401e5241c2c1c0009803240321281041000502c824010300011981e40550554000d07007604449024020f580c40946a17003004001c03481221114580030300b40da00c603801c840c00840cdc05c01414004d140e01c0302c92a814144580c04203a0007071006040000383d9407000742030541203030000c15069095487e0000100c2c0500809000c4940c0641069840d130701007140c011669400901003002140101c1c60071030303008001c80750360b07010361141da14020000012620100d1f0f080b0300c11100320ba811210480c0c1c140094a510910305d80c10214111100c060790740f00e80154400f1820b100240c99001030203140c0000c0d501e43d44210a10310350582c0003003010902e10b00b0107000141c1c000a034800c2c10040000d00800c048110764542c3c1c46995554040b2103c007041d420086900c1c2c1c050300d0301101851400b210040d000641b035501608000d04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 683332131 1250 683330881 683330891
    0xe060708150a0801090501060b041a03070c1506051005070c030b130506010f0e0a091101082a0d0e070501020607080613050a02090a051c20040e15070c0305070204 71
    0x1c1021a030440900c0e0610003400b049030070b0349801d5040d008004800c0b0896656182501c089655102c00084e20100c0341e1103000680204c0c0301e210064030035040174240c802444960220300c1c0004030140018030781d54802003800161103140c4001c10440c503102c005910706001b01000424003207000c80c600182503a4020341d03d20196146c0040c9100281141034002d4180c1c00344200103c1e44c0380c142039080049894035050145a030319104c8080040390069040284942c2d05071840307211a5008103080c0c0e81c015009024280c002c088803802000594014002e840c01c0c150001d8090b40190041c415440f1001c1c81200070a9240d09060010b5540c100c084c0c20b12080c8088080002c0003503561000c101e8070403009c64000d0016003441d580d154003075042001428802c1e5010300010503075050068500c6020302448042d42d55580741c0c0c0e1a1221484140c0e8006c404a1a82c0c8441000c941c441e809560020100c04000f805a41d0611400a070b2112024041c0020081f4924510300841d40c89402d403124641c0440380010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 683333381 1250 683332131 683332141
    0x1525120f09050144070f09121b080d020c031902060906030a0207020616150c05030a0e0102090915011418120312010f06030c090f15020a080d020304110102010e060708 73
    0x822048038586131080c100c940c00e200e07241120707481c08060045000b070310b4160220b00c5421099888074554010040721007209202c100c0400c8201c010200c0803c071803018050b1f8143c45101d5542842d040000c940050381c0a109140250306003000310003410300442c060b142074010290b000406920070801ca9610854012001c01c3e2044025812200850741c01000036a80d40400b254602c00307504005810749220b00a20700c170004031081e030301590401c490569101841c4da07075508005070050110141c44100c0359424826085240c5840003030300d0041c000c05540e40100918600010701c0c3c0040020106241c4200703210825504244071404d071502e600844080d004420354002d9039186010b071503220202210b1840000586140c5044807070103441e0299018411001d0002082c0c401884a1140f014150160081000007105201b180802071070284155040c9030300c0340d04c03650007541016040025059000041c801000b10030b50240c0c0d00070300c0c2030000b800f840c010860081e40324400200350070180450301c2c00103030b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 683334631 1250 683333381 683333447
    0x3020f0603041b08060601090902070309060311270415210f06050406090302010b040903020606131d0115062604170d0506130b1525120f090501 63
    0x24000c2101883c1403a4901d99607111303160342e00401d841060101e15511030216024905000f100e015035055107403c80014a4410110003c02800c030033a030410074140304484007484003803104c0000076602c4800c1404044154200021a03204144000d00070369000d07401c000d00b14006e19024840c2d66500c1901c10260003505140e08ca5001c80c2d00c000304103078a01401c0204001c0c2651048150a000b64001c0000102d40000d104c100d030180c0307201501507445000040d146280281040000601400000c15903400c200b6145503a04100d1041c4600759440d401082204c01c10849400c1c01000c0d17030700d400e1344020b2034088520303040141460000d0302c0c540c845e000503052041c400d4043c41b4001184403080e41d41d0404000480050105642e114401c1050041d1201d104006000343c03107186000070074503185550303c03003842c41c0250300041c00d00c003a0000c0a9000b1800881500300c044c29503000c0c0c0c03502e074080750f5203403402080e00c0340d55100d9800380480b454003403045903808041994000c144c0c01c0c416401c09070217428070f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 683335881 1250 683334631 683334653
    0x606100f0e060d0e101d070308030c0c030a02071401051201060c05070b0c0115080c06030f0a090f0c05010201140c0f07030912060207020a12021c061409030c0f01020403020f060304 79
    0x5103c1d09420161903101d441400500300700c0ba001c460300104030a030480c10910703900c00b8a40c4000348095004101c140082036509004542214a401c4071038135060b80400d40300e08540010002d0005a080f214007003048100c0c0881c011002c0381d0902e4850b00d80b52005940c0961100180280010040405030314020044100b003440b01038840b01840c161512100a40c59010b44116010046030b0300341c45400107100680003c01c144071150050a6600b160703154000ba40e51483c0007024442107584800c1c1010208a040022002c500e01600421040c1c5013444000390075038144080902c80340a0040401420070b102d1000c4e9101c2d40d1500c00300c607030303903402c81d0604a070b402e04075030030005c6088011000c62003000902c0e4000c008451099406402071a40d6848111080001c40000f9401a0a01c081204a03007641c10422640341d01c2003200103890300200150b0322030f074102124082540d904c0041e003060b01700002c201d1039141c1024203009501d03150a55010031840d6200c60341c82400b641c00880800c0401092003c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 683337131 1250 683335881 683335897
    0x120506010c060f0b0a0f0b12040c03060501090f050601020c0a0317070c090203010f12030e0d0f120c02030c0f030a060e1219030501050f0d171e0c0606100f0e06 70
    0x41409031242c800b00400040100c3d204c2244501d00c05200096011b035000140300890307034041081824070100e10580400403800400031110106404000b0000641c180b02e014041e0503900c00005441006071036000031104044d0072181075511201e501c010310b5451516020079a54001c0c6002e01100c0030501c4d18240340a1090003e040103084280440c206005038003840c100d0b403c020143d9030712540e8151401f02040c1d820b01c0a030000720240d40da000281043c000e01300c103940c42041c0341d1050b843c1319200c0342d480a11000c025000203d010000d04150b00c1c0410420b0900941111160080d0700442c0000c1d035140e41ca80c0004041d1030701c03180000450760050100c505d01460300303d0300680d07404d20742d9466510042c001400c6000b0a01c0e02c1d0001ca01400c0880342c996280e21301904903c625001d541b5400440050500ca42030810380402c2080c3d5500340d4040f040e02400d44900303089441d103c4400c2d003c0c0c00d060000346042e000e41160000c8084480d0b000030304009040241c28828000103020000c140039100b0111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 683338381 1250 683337131 683337143
    0x203100e010b030106090e150106270302150d0e0105071b08090414190203060604050d0f02100c050f0c0114130b03010b03011e2402030d0509060402090a0c120506010c 73
    0xd00041680b450b420006187c0d0b008400e4460066050080c00301d8a078080c010400003418554413a0f41202d84d14010750041200b2a01400381203960b07a00080d01e240300300c0e11545007000040303035a1800c1d14650148584070001000280070f18940080010000b5446100346150540c1d100c185205011604044600e0020050424071800c4407400c202c2242c080e0a4811034825094040d0410f0f0032901c0384252800703104000c02049ca003600c0d0204008804103200f6099400d00e2090806400603540d000710041eaa1100ea1101c1580402e00c0c1029424803c26500c03180c6c06d07820040c1050600e03a0f00800207400c0c118454001629005000d60440d8002e0240c0c0020305002d100200120712400f00300080d50407107030400902d400880840c2400d5150b19201d1080786808080c1692451984204070310001d002d800d01e00c100e0f41459005080c0c101611000d0701c00b024603400920a12003941040080c003a80010031040034021903880074001088a0380c01011180419600e60114007681e00c101e00e02c0d007a02e0340200d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 683339631 1250 683338381 683338391
    0x2102061c021c05011707050109030f051e010c0314090303040618050604060f0606020f12032809030801321302030403170106090602070b0309010e0304080304061403040203100e010b0301 81
    0xa1030000180002c0c005c2c0480302031451081d01100340c002805200707440c01039482c01c5500745150342c0e0900001c800001100c0500071441c4110758007408034162070801c0c0095001052400d140300001d01150500808891618804010018900c1d00001203d40141c0e0008000410303601d020003071014041ca440f00104036008100c2840b00307004080d0801040402002c10400c8041d90320142660360b0011070010b02904c1e00800801c0400b00c1d100c0000c1c6078401850129021016040c504003c500c00c8007041920f410750f91140300030140b551006d900d5004d42040181580000da030100020700d414115a0603420358800c8400740642a11111065080110310030750542d103905081c5030103480200d46c1d48020903000d4030b8100005441e441541c840c070071a0580d4010f040001d00704109940c0765400100504059900c9030740b0989456000c00040c0014103504000d50740780d40c00c08000800d0902c0700360101f0070009060082c800540c1d008105909210041c5100240b4000600503c0e8003404075500c01c0d9a040d4601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 683340881 1250 683339631 683339677
    0xd050102041d16080a1503051e010e120a03150e090f12070b040c0b0f0a090e220303060f0f06030501240c03090801060b042102061c02 59
    0x150050000d8900c0d4542c0194102c0d2030700071070000c8080c01c039080d141c40c0341c1400110f5440f6006000c81d5410010712031003c6030804400d00f10f5018008139900403160342d4859210b0558050b0b00140103070b03080030040024041000288407103035a86a46544522040c403000865581c01d60007580304103c0c5266603c04241402c0d621a0780500300041140c6181e00c6000b01c103100a014200443c00304c20841400c00010b0500c0215101d02c00c00010003030045544424501c00032507000201e4014080e803202d01300a49a964990007002080c140d02a40300042039107548040c040029001340540014494200801a1000640c1400c0f070203003040358411404c400c0c0100380070071511041840c0000f503e8103501c040c4202e036038480344d501a103a81c00300c200b0030303580c010100c2204041c802c814004c00c2c1c42c0203141001080d51108070b042d00f1600d09038092120041d0028007008402d8005042400341105c2c481105407a1aa540101301c1521401c0c440c034080034407804450703404409540c180d400304400c0d4040c0da0124159 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 683342131 1250 683340881 683340883
    0x31b1b0d03020c1b03191b03050c120123190f060f080316120c0b0901050105011b17030606160b0609101212050f07231605091003020d05 60
    0x407800b0000c025000d00810641003ca444c43c10f01c6002001030010329040c100111102200c0704003c50485944003101c40782503006801c40d00071005540030710050b0111601c03080c200550030070050a00c2d1003903410a0000003000350000c625080c540c09803546006a60f48180702100540710309401c2d1034000e0700d4042035288800d4294030920a507604445480d909a480307184040d541c0c040d0f8850510b400380c4184800c00000d401007005601d4000d203040580345490646d9852810240444514045a41d40c800411481d03070b01100d10900d50078203210340800c1d001c064580000ca44405406006016000170210703945071136020072164101c66140a541c00c0d070915181a850083d0207482e094030507070040000c1a501408000004222002841c8244080d1866a07401d000d2410358038a01c1e081c01014000300e080c580c440002030500c20312881c0c03400341c5060180c20b4108071820503002c4031841ea00c0a00884070b10300225103030380141c440407a243c0a1542c0c42840c803150b41c0c442c1d60030080d00101d0581a640803c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 683343381 1250 683342131 683342137
    0xf010303030606110709020f041805090705040b090a09020f0607030c050d18030605062d041d212110090c0c060c140a0f020c0402031b1b0d0302 63
    0x4440e68081c442143d4590f011100c0c12100034030112140c1000c0800c0149091641c0240718840d83c0f95003940c2001e55481418411080c01e0f81e400001c1034454007080401d0302c09001c80005014102ca040042c00ca00c0e8010a4604000038000b15035580d5a02c4c0c04010356550540202c0100401403049650b440d80c1d1070002d00a041c41c5800721958414410004411800b4140c5000301000030b0140c40c143c49c1c507503119400a000043d024a402054005092005d1060f4400b0a0344001aa0840b5448031071502c00344000c68500304200a80b65a62001103000158040f56841c19080d040410000c0b1150740040364519100e034800d02e0b20441b504030790354680001c811380001d201f03104502c07940010f1a07807041c0702c50550f0f2131104000006696484654009441d41e4000e0000c4030162500c1412050b280800d2801644181283c0010903100000507444503810040080c01c40741c140d50950039400d041d800105010f02c4080f040c50784000c041020a4000015040d000d52140104100c4a80b0700d0039180180084d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 683344631 1250 683343381 683343383
    0x6120b06040f0611152e08030a0c0305090901091b0c0803011a0405121608072610060305031804090c030b18010204060804020f0d030905060f090301060810140c0304020114120f0103 79
    0x500c03860200044c9044d400883c000ca1f818100035510745000020203ca10041c5948200e00b48001400b94404035154005201e0180441010002d60003c090071040102c88101c4000010090504900000207081b50300342c0c0d04444242062110080c08418085114016a0003007a004180c0f23030f603641905c03070000a603a54101e821448003c101511056020b40f9041c8602400c48131112690354210400140c5c010311140d0b0142000341e0b1810001c110384001519000d81c41071314698000300e509074061030251100c48000404840070031552031255038103420000a0b05c40502100382c0c0c500081c020440e01400c12141340b03158802151746545440014040c1d143c16641a0300030901c141c820f8070582040390b091000b090709038944462180c80c2504000907a40305c0c80d000c040303100040c490800f45803000d0180c130002c2d04001c1c0103080c145864003400c1044500890580d5501d280c2c44040c400c185103444101e90704143c081c6040b145810010b24a980a88142d00d5040ca02250100c100049581030030003140c142c2e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 683345881 1250 683344631 683344681
    0x10020d0b0906030f1902010e18180a02030c0603040f020607061a0f01052b0c03020913020403170306011e0201020a020d0e0a0506070507090606120b06040f061115 71
    0xd40b503600525a95941541d40e202456000c0c5464a60103c007009445503528814503100d5013141000c004175801c50401c40702c425a004200084c40040b40c42001044141211240100954003154001950321104016828002c0d0780000c007250a010401d82c10712126074001d0140c0390303a54154a080c4000301316480303c80b80e04c1280d002400c00a0f00d0041d0b440554003005a40380c905003103000300e0b07944154147d00159010b19121070148121806580907541161020391001611400c2070024000c080400801d01c1e05951320421040c40003480e0540c40c0310800821001b501c1e260782e01c1100585254a2030030514a84849406820140d541d054009112807d2aa0f0980392942c8564070141c0b00c5d0340915081ca9404400c1000c24001d508114001d0041280208125849203950b10301d800b049071400c2e0000000200e07038a10140d100c000c140101e032010700094425518082c80c1902040000c0043c1c0207181c10016203528542c4080c0c2c0c20419061519806111080746003444100b20500c60001c201010f10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 683347131 1250 683345881 683345899
    0x512130305150f06060a02010b04050a2304020306040834030f09051f0e0409030807080f09070905040201020f10061406045001080f06100f0210020d0b 66
    0x30348442c440c103030188010180c0d04045840742c8082007116042070b040c0d20115980c8995403074041c0d60f94054140941d01050300020248a11004554019810030b07207042101210001d01c801030300c000a02a601039001304129845143e6074240c19506181908540c2c0b14100100c88190301d01408860b11018a110340c0391040760304076038002511a4002c52290550280c00442d00440040640700c107400580030314504003000f05840030000c0c044a004d4030b02500055419010043c500d80c004181540002e451140640030f0f1900c02c5102e59204440e004140c843c544a0000c241164001c00c401d04000d2880010f03101540b500c0350301c2c070009001c9481004148000d01ea0042c0036070a00d503040300d058947d030300d001e42d0844003845141c601004a6951070038142c502c03100e02241c40040030100c42056610300050080c03540018000400c08200580f9001e501803004050085543d0f801c1f1b48100c882850b428000500362600c5401d900301100c82c01c4200190740001104c0007101e0300b96206030a8039400b00ca103041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 683348381 1250 683347131 683347153
    0x209091f0f06060201091205090102030d0501090e0c22090816051f0c050f130807090609050c03060d110a0819021212030a05041502040303110106080d020304120512130305 75
    0x5c00d0b24400e0314054424a407516650341d1040c4100010109104180112071802c440e660140088071800d901c03c00c102c582e14148844458014040c6121504003160105c600e4444030030b00c504940b41401070390b203a090742d40380b80300100144001612074100001e0782007802c00c46507040080e100c0f0f40c04080c0c2000d00500343d280301146074292144a201d4039003681e9030b5092141e00c008015166100e5102440402402c0301c3c0080c82107003c202a9003d0b00300110702040c200d1600c01c000b0180c9a000c0c2100501d64002d01c10810591646d000f880e0480b6007002c080a400e09004011842804454200c650316008202030000502c0e04c00404161a9109564a0720700c9240c0400c1e25883d0481c007500c00b12100000c1022503d0341040341c0009800c82e00542e004444418240c0b1440300300d81c8580d00440104a082c003498a180c00280b0800300100006405416665000c80c0003e480740700714014500f4a5030140341520604c401003144040c0000d0920307500c0c0d980c2c000c04000d0440ba10042c40b0071035892043c82c069030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 683349631 1250 683348381 683348383
    0xf0708030309030a030e0102040f120308060619050306210f060f04030801121118070e090705030a0f0b040e030403050607140307030b1207180f02040806040209091f0f060602 76
    0xc0d2149402d01e010303500b041c00c0700d0002c13005021843c00c044e82d5503400b071101058100c0b50415010052020280241c16128545400b0786450401840f1a00c9590700303100358640c2e8181c100160078804440c1c90410342ea555040000395401c041c00c040a40241203120716403544942c001400b081d0710250ba01100e2040c0d54510201400c944100c07002000140724500401440c5070b0781c05520b6500f486412000c0c010514140403403c0c0c00701e08100d0903003104651051055550b08082503c035110741c183c41062a500d00800050141c3c80050510542160384014160121f4090b601401d940c141c0108240006101d0002c0c16070b0704d8009002c01d85640c0148004200d400303002d888072080300e2801200150a503600c0990560080404042090f004000c4454000e1030400c140701c41030140481400401205401e11848011a28482c0403440544d104010a111749500015601c0d03005034107e8480300e01da41c41040440c20700c19032040051800380200100c0d5001445074220300c0c002030724900e0801000d540c9150807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 683350881 1250 683349631 683349637
    0x250f05030c10021903051003170d0b0402161502130807060e030703030c020609060d0203071133060a030f0302062d060409050106120305040e09150a0b210f070803 71
    0x5042c0e1005400309150b90315000e5004658003054540e00b1030941903480c0c03644100360140e103001210355840020200e2000c1c00901c1a403800710000d550450501d041080505100ee040791006040c000c80e125204003070840d550101e540c00c1c1080c00d100210203a6a020513603640540e8020310001c55121180c215950500007024021680c04d952501d0080481d50240802070f0705c00041150020740070003009421050a00056014040c0c0350f48514032a10010b107464280801201d07a50904030540c98017aa813200000c11503824200850208115503e41d00300143c1d15040c20387c00200f40880d030b00c000101781500031446920581c5080038011640030000342e500d40c6507501c801305410203456030740410903506240d0b01240303615224600004000b034540c5c180100340080001c0450000d1740c006020311a0790007044c4410740081150000b020080e00d42034410a000300024505d4200c2ca41d540300540c41c99882c4801d0031503002015a0304c00181c0318001c007040e00c850f0580c1c21500c0c244910600001c1c804000011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 683352131 1250 683350881 683350897
    0x2a0c19060b0f100e0d080406021c1409010e0303040909030206010e0a05071202030a060f27020408031e2101081605060901110c130c0f03020f250f05030c1002 69
    0x4908080c0364900c041c0c07501004e0010194120201861880000e41d69200a00c0503041030303001400781d44d40f02c038800c1c404c0040c84804c500402600142c0c480303e8107141000e5641403502402e1440103210120f02003403840c02150320018041e0b091445407002c0c50303008203500341a10078442a07000d03165512010003041c1c0c0c0055848000289a2030002c0008034801e0340919042040850007041c0b80c0d070740b02080300d0000c034190404001c1080c0c0b03500e01050300d00004800c0b0007201441900794102441d02020945a0050a540b90703007032910b1130030304048104000205d486081406070001c8582c14131414182014909014032606072180050b109024120008400c08030741303005080500c6d0000010045903565060b280341780d2180321308441c280c03541e0307108802c4400d0400310980000e1601c1196600519000e581507120b0149481082000850507041084412012031441e00c602500c1c02c201d504600f00c075a8500180c10305c203a0040c20303010810040000c09e061200d0008844c94030b021080340604922902c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 683353381 1250 683352131 683352139
    0x3040c050907022b1b060506131b0c030507082b050405070315020c03040909031e0207060305041103060702010b090c0405093108030603152a0c19060b0f 67
    0xf0138594001480ca00c40b002c0c03d2044c5403180940312599920000d041d01402c04844207a1608204a102d040203003040c1158800710200380800180040300c8089103161400100820420f441c03580305040c0900111803045038000c00f0603a480e840c8009003c1c6d5408440744500392070100c515002e01813101030103900c1c080d64000f400b4140c11840c41d607402e000d00595608120b00107809200c1c4241090080c000341c40200042d120102d41003019142c01800750140741c010304400b811580000c0482940062030f031081e561642400125a05c542c1000c0b00b100782ca06074100c0d071500c947c804100b044c55043d00090715200301a42c0000040c0c032203441142280c0a24021250403140c680000b809003044412550400000c2c00c40503420070302131001505029447c001c0507280c03400c0001c02d01c416800c04004a150781203002d0284110780c00c2218100c40507901798202107070000c01c13003240d42000c1d45100003150403c542c01030440381e210f105d1004140306070f181824240c4140e450900756010505082c240044220b400034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 683354631 1250 683353381 683353423
    0x20d0905120c0904110310020d0608010c140304060f0513050f19030e06160b01140418030e010e03030409061706040f02010f0509060f04080118080415020a0803040c05090702 76
    0xba05006281200034400d0303c074030703040111059543c1ca09015081000700c0103000980e5500b8407412840c150f495a6004d1215603140064203070b0099071114a844240c803090b000c01b0303540d4456081140107405810142c180280c9014180131411518000c0e15180138880c0045e1100c180189400d9520b403840c44034400300403041d40200c200080d114900d524510500200f1480c00d00e980b8001c40c030f4000b0075a10044600900c03000c01400428400c2d0901402410210707404d015800b01e05010b8124034a20740360003400d2160340000100182c0c00b03040d50b0080000c000e0212034403165140b0f5404003804e114418036140c42c500000c3e40c3c0c850307180412403910030390304014251a0418580e0044902428002d81c0004011050102c480039961309801820b038214481d55a90f2101c0c2082c0d241030850780d01c2252000542065510807000401440996084541080388111030405036842030342030a0782c50100510343d482c0001040100540c001132072042d10703402d5800b00d61036620140184c2e603440300d14201281500f200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 683355881 1250 683354631 683354653
    0x50d02120f0702011b0f020f0709050108120f040603020f1603030b01030b040902030a0210021603060c11060f0c0d0b1201090c06090803121306090b091009080315011806020d090512 79
    0xa811b01d0600800284125841e602081d000c584c01c0c04210f403c08904180c1f1080104502041000000d030f20200700030800e4900345030b00100c81c0305441248103017024940c002c11000341120043e01915011305c0c2400103400304245500d0014020316008200d44c4c0031915140104d00c45044c580704901d03406034080c0040010310300b29000c100f1902e5545000c6011481801c0d80da410b00058078011000451003140c0104200c40d5403d030240c49020021071151403031780000d04001c1c01d100d0900c00e142d00485109a140e581c0c6403028a00000780525003125130300000f2070005001d61100551000400600078901008015103e0307104480413031341c902c24125254024403071f411000304a00c0e8000e4002c0309954070036510040940c0ca40003aa0b40301c05080c0d40c025080380401543c824103016854244c61070640801103411540e0750840325000290420003200c8595104500c181d005225030784d684006008038441c015910715000313586008034020b0340700095121000044a08064030b03000340a211000282c0058138070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 683357131 1250 683355881 683355887
    0xe0f041511041e08070f0f060e010813020a210b060931020a180e120d050a020f040308041406210402030a150c0908120307080403050d02120f0702011b 66
    0x20382c43c40e00003091000003442c0c03c000c100e200010b080401740c20300054a001d08036000c81100c3d42c040300c10300c40340c46140b146036a0b101c0d0000e40e02c45211108403100f0540e40c0081030b40903503150014602482c2d082d689022050340849480b594a00c501e00d055065603076a41070004840082d80e0312150b08001414090645022001260304210340300008086456640c002440540b21780d07018402209000000c50b000610034010000354070105030080080c00700c100245002d03441078014610700140d031031010580d040d00a030101c8410000041e2499101c035201c0c14500da0707951051041280440100c11280080c2c03e000064a0141b000250700780815900a11040304003039009204a9240c068008500c00007201400d000302ca500c4c000310009002074013002d01420800ba00e40020764964007602c0340e80c05048000303003280d0b440b01d008d14100407252500d1405469500929001d01055400031910000b17071904bd54285200342c45224620b865034407850300507822650350310300c071054400504d145c460003540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 683358381 1250 683357131 683357159
    0x801060f030b010b0c010905030304031205070806091609051f1b1112150f07030b010c1709120f010b04050106031e0209061315080c040f09150e0f04151104 68
    0x550300002103000c894030388c0c0d914119802160220003065194064104030000ca201e02ca40c40496810840300608207000000c0d0751000041c03036440c0440032454000d42c0644a250080000c000c06440821800310601002c24415070b40110b480c0044c24581d00580e210440a03980000150082c6091002030700d414148401c440c0066052989840345401c540701000342c100740580700e03000c94403140a20342030100b0b0042c1a10040c205041c1004042114078003c101881c4054a800d4664134106941d1203000e00415140c41c51300d801d148080c010b0500340031444a040d0865080c0520407201046141e894000640849851000e48291011820b003c0013070320100703600600f003288004224900303013040d0300159166652180c0040351040840c07008021000d811270b08850b00034048107c06130800741425140400f1038802e20440003182d8441c10f4000d20620000c0c8080040c0c80305184200e0302c2d01c2c204d24400e07203182040d90122840707200d005407802024141c0c0706210f006240440000c1c03070940352004d1102100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 683359631 1250 683358381 683358397
    0x1b031b0f09021312060e0606010203071709010c0c03050d020d0c080d0504050c2e0201110a08100306051f0f0501051c020c0a0f0605070504030c051c17040801060f030b010b 75
    0x210400c0201e07112080c0301c980403c0380d11501020400b06c81542d0380c90305018000d08001d0640d80240801d10008024101105118108015140e103034200324004a400c2603804e0005040b00401007008018003502058085141015800b22045000d60307060443d040314a845020340403401c03d005140440009400040d001070040c011503083c1c100030b4000503074008050341c038086001c5144050451903030320010b0583e82800b00340020020781e03800030024050740c46040c0e0390314100800b0f14001812009540806005140c0001c1d08000d6442c150104000c3d185070049411014a01d0907000107006212202400a40c0c6042e0f40b16810202d84650f185a0024090b8081c45d0244e024030034400001e0042005031803550080003000001e4850341414012038034050500ca0170084104414008a8003100b03442d0112081038401c0013280d80743c02c0900b030701e8440e522002407003021000702d100040c050100290040ea510301340200000790740c46c0c441415603d101d20000b0a15500070004208104081d00581410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683360881 1250 683359631 683359657
    0x2190b0405010608160905012102090a0f1a0414061f0306150c15020f040506030403030e061501111c050307090b030c030a1d060411010201091b031b0f0902 68
    0x62602d44d10024208004500341c000c400005100070050300d42d082c001d0300c0c018818032658028030000552a100e03848000c031000f0740108444004540b030040d2070342c0503018540d4190410402e400082001109011104504a1142d410035400c00d002e5818015414011903004160b01d9040600180041c4461000c41035002415950380b00061100c00000f4841001c0a16aa034550000003514001d0565040300001d401101d2040c01400d841c0c000d00c004440643d18102c0c0c00503101c1c0c0d600e103011409400d0500501c0c1d5a8041c01c0c06100d00610454114024038609880f01c5610f00780000b0243d41c0c44150300c100c2d84220200380d0600c25841d00590003036800840c24900340c55510744500070440300d03a005840320116000004100200d00146c4c2c4900086000c1c0e0480d1880360407010703000259170340006000074000c1da09140300c40c02c07281e0003503000d801c0c01584030341d0303003175100000b09600ba1071514184000c3e290080c3c1e200b2a040181c0190b4003940540351034849410469040c000064000c2d0425a80e441e01c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683362131 1250 683360881 683360891
    0x141608150d05030304122714040b0612040308010602030a020a0b15030a1407120b070f0e0a2301020304150c0f061a1008060a03170405040221010602190b040501 70
    0x300b141400190f204078000c40b1801c6000040c0203005105440c41180030300060520000303040e0800c1041c00d5201103680c940350000c6c3c40e000e03180000d00102908901558040000500041c00d0b18007011000d2260b4002e0301d40c01c08036030780c409050381c0380d00c2403061010042c1c00c40c4018100142c5a462410341203414100c00134010a507101c080b92401480e4503003030b194401060505403401008008000c0903008200701010041055960074403004805041d50701031003a51031810300710502c03404851441075002070850b142c903696012a0110301070030849080200d0160740f103210305940000200c40441d584518010140c0880300c03021960042400011100c46201100081c082266400340e0340408105507003100301c1140b08410046445106141403080c032541c142081450360f0703440d404000300e82e00f008010042e4200031500c642d44d88200c2c0c210300e6200748041400f1142c2c144800c82d0104141d50404038099503602c501007aa03640c01548803000d00700540c0300c60800000c5d40400ea46410a100c2c00001c00c07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683363381 1250 683362131 683362133
    0x80702060a09030c051c030302180301020d060911120606071110090e0f1006050906070f0b071101090f080a02031b0d121415030718141608150d 63
    0x34961000c0e4481c80001d102082c148144500c0c4915640204011911b0300849801e09040780954440c01401809040d030208401c03003096086200c2030000fa40c014021581c8021140d001c000400c0035000e800078152500000a900955540c11140701c0f008440000703a0f141c1e1202d040281d43e80c043c04044a03c04540c002c491340c107484201d9140c3e80b40f800b60b250360410906203c20802804002080800321b00e0218080c030815200500d561800c0e5110761401e0382c0d075083d041d404a80c461007158401000120100440403d03c410890304a002d8034403541c80f080000d42c2c40ca00705003038400c00d00300a00702c49510490b11000a4682c0003d0500c180a0b005503400e19070080f510001c1c00c5417a41052881e44c1002044603841760344002c9000c9000485e0008000548079840311504501c0024803040ca4242400074914540e075042010500404000300b17140c114000035001000030b0141061b9900d80d8080004c041000c0748400c80e0b502c0f0110b032139669038503459035900182894001c7e2212a50ba009000110940 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683364631 1250 683363381 683363389
    0x1180902010216090c0e0607020a03120219060b0108070908030d0b01120c0c0510061d040302030f0d0903030b04050f040f020402040f1e0501020c0a0608150603010303020c040c0509150304080702 85
    0x10020804c040c0d00142c900d59400c0040d24101d2141c65252250208002410041e903841d5610710a0b01d800c0700013030340d5003101180c0c240d160414207141d000300e14400054a5040001680040d42c044600703a8810059488100c0c0a590f8a00607028100d065042448200310406455111545594051400005030038811051208035800020010b00140c0703c0a4400c0510208008288100c0c100e042c1c204109880e0502c01c0c0c640c88606024645805814404541803500c01c0065895039074914086c2642c6040e8420307504000c214984048001c24203195540000d0f107001d02c6258400e482056141c1c10f030f40c1c0c0d0350b0b48501500f04c0c041c4049910541c02c0c840498000c040419580c0607100b0502407001481d910f01410380180300e1a840141107510285084e0403507100c90041c41c0c00c54549040c06c0105885414400d0300c80d05c1e5404c44250401030210001003450350000f80ba5030364140541c0d0421030780050f9002110075100f982050303070304400d0030080c0c0c8a04241001c011030340a4011604103050508590001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683365881 1250 683364631 683364673
    0xf08160603020904061d06150c12033606070203031005010c26070201031104050a15030b1e040c02010c0e15040f0311030d020a030c0816050703051c0206011809020102 73
    0x44086e81c00c070f40f010003d00b4103200c21010803800208410700e0601c4031301c581142e0380340d00c904a1a802c02c2d80c04000320b0000130070101c0c00c002e91128034142c1043c50310070f042492000b000150b28512184640d4000c10b0b0354500200c00c4a01401c003070132402d4015800c0500642e01000c0c1c0c40002c031610051082d09030000cdc6148c6540b9100364495100d1280e0b034600900004040d50010a11041c001d074042104000d20380c0c4d1000120110b400c810100b807541c111301441a00240105a8003a0304105004040c8013610305040440312084401c42d0100081d203000d100c22401c0b0740b42d0b03d29038408605000030003041490503001100c3c5600031026080c0c506602d4001d000792085240e40101d80524072150f80c001e60703150903c500540c10301e5510060055442d41e4400901805a441001c3c0c641c332000103401d07400406c80190940d400e43c000c0c0c101c034501a9a441c0050b680c400b4a9880108500e90604101c1c50380d10224070a4100d8400d00d032204e44488415030a4001400e42900c202c1c11340c8034060110b012083d08041d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683367131 1250 683365881 683365919
    0x608071715040c05040f0501030b2101020904050a180b1308042309040506060f0d02030a03020607080a0b22150902070c0b2706041706010f0816060302090406 69
    0x100c107801c0395007810300c41034803010b00360705081c840140020b00c01c4072040e910f40d004031602403070b02060100488001c02c500b15259900e442444a14000320032250005400070305010400384c6d070400031a55803055010031941110350710041ea007080701084001c20107807d81250487c0030036001000c22525584d030002d1036402980541d80003a89055180081c800c02681510401410b58070b404007403a142e40c40b661079650091005101c2c500280700c0318080e86400554000e05a4060b0481e007542000342400b0399100005c5803000c000400d440e00060450000c0d010310b0b00d0401d00900000040343c403c0f40c14140d0003403107070b110040d2642da0300301404d0101041400900140000380d00169503039154141326902e48959000f0001010007040310f0703120701014072102c107c200c0c41e8202135000740b01a040024003d100f5075101c4401c01c1903a01c1f8401c44e414010444074100d80301d109069a01669a4005589801005081c00580c003c04e1038100602c5020740c00030301001d90010000201c42e0745510800c50901d1035844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683368381 1250 683367131 683367151
    0x20103240815010605030115030f020706390c02010806060909040c06020601060815060706060806190f3608130312140904020a093b07050406080717 65
    0x242002da4070540420103409005145495442e5604000085242158007080f01003050b54504040e40c0d003030540d03410380c5c40c3c180d40084140010413103145e449074484090400d000018500c0703042d000341c0d07091088441042c900c0d20b407515541221103800544504800411040d0010010010f87c04542c2c0d134009180d214500c43c804c04c541d43c4d4107041c0020f02d4500305070000070602c21200140705071080540c5c180c1b40c1c403013411207206907030341c01ca850454041c0109a01548840c8500307420722400d1080050b0240c3d044100240030029028444200400d40d10044400c0e54115031005a000e01001c0d000b00e04405882c164006036058045076031180881d0740060444501ea100824051040005003040c56410b50320303610b0280121084940a000c95100340c1500c0740c410b5500207070700100e5500440311a40144801c040c00d065407400b480800607038208407000d021004400c030204c42040d87c11804030746e000300031503542c0c40c2c00c1c54101070040c0d070030031809800041401003000c2d0310810009001003075442010640 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683369631 1250 683368381 683368393
    0x90b10091806091d0d0f1707051c021e1317150906072c1017130203150c03010e04020f1c060b33070f21030204030209040201032408 58
    0x16113a00d0400c1c0740040c150003004212008a6001c60381b0440c0458440000c0100d58055110100d0a446a03c190f504c40c28000c0e40203061000a03a0031076003d414680010003100c000710000810310701c81440b40c10400481c80701c0500c4140070b03428480e040e0b0541200d4800441c0d0310b810007004200030700c840485a200580d84910200107440c0e901425032815000300c4c010b440d1012170100d00c180b0602d260044a14040e41000b02c4400d2014420281c01402c0c80c00390a090001e42044d1818241001210f04103030300902c500308015062000f00030130703648214000300b0201c0c01c507428100300380e50707603c0040c0060b0713404000414110059607480c0d001c1c03504006072050b24030326980c00740392400548500c0f01806208054000710340061045d4640b400d5a403006903c06142c0c031001620103140030380108603016001000c408104820064486181c00750f0300010f0407c20002c0507034040c114180e1055020003900210003030301050040d402600200b00c4000940740721001c66000604007075103d00154040c24184d8404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683370881 1250 683369631 683369681
    0x90111130617010302010e040905240604111321080f0c07050901050f1c0519150203010b0a08040201020a0b0c04051309080324090709090b1009180609 66
    0x81040c54141c03080850b9556265130000380110f603150307400034000c544850080041150500103a03203103401b080020034440d0743c60701606003003003803ca420138012031a0111a0281c15140000c0d40d100c8940100840f007558240007907840d50f0340140c02c2e220300280d07450010100040103140a01980700b000c008054803024507070005481c0500340e502241c02078440000500083d160f1008080ca04881591402040d0340314101c1c0002408520700042c02d20302400316582a0815407038103100030507005448203c402c60024440008074803081c402d00c01174007800c1012401643c01100c410350b0090050050703412050751500e8409101c9000c03541c0300d032400030005c3c0501407440c0100d424591240d203004d04000105040c0d03501010740c4809000f841d8800420a502c0510b03011171144ca07016101c0103480381156040810b070240c00703008503010304050703e070500b0600301450924501004100741d16070f0701c00c100e162901b2901c40c100c072a00300c41c007500729495a20200e010700e020b008103091b0b03041014a4400c85101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683372131 1250 683370881 683370887
    0x1303060501060521070503130c1a09192103020c220c051305090c1603030501060305091501060815040e0f060106080132032517060a02030901111306 65
    0x1810800e0040a80780c4d005100d450743d405402d40c1e5016617000e080c3c0c42c9140d22410480400c05050f405004c010070fa58043e45401d540000150211000c1038031421021a02c143c00010211032501912240e035140d4124040034481a141c1e03286070b01c1c002e0050b00c000d0750101010841496000520440c0058440e400c10354404041c416138181c1e401915010f4140080f08800400d400310a00c5654440c0c8440004140e44d920300c1e40071660034402004103015401d41c1413070080c000d40030900c10080801e10706800507a09403008904034003415540d08440040d607081c0700d01900d00080141409903902044104100b6980f158410351012840e810024820704118420907442c00740160091410824100c00400a0080c0e681364a04046800400c6100c1e481c1036034152403c10000361942075161207084540124041182015281c81412012482d105038403540640601e41c4446850400d80d0310010004140002d168007031074000e0000400840c24880e540049085070f0001c1c030442d14140c103100020000990 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683373381 1250 683372131 683372167
    0xc0501020624040b1c030c0b0703090b0a1518021c090804090203040515010b0904060801021303020108180f1b01090f09020721031d0105010806070513030605010605 72
    0xd0b1100c0320340c100c8440c041001d0010810600c0e03083c001d03511160010320a60310504459424190014065504061414000c00f0205883c41c10340c1c00311240360210309454444e0080b070310195007120803002c01e5140d0150507001401e450282516008c081d0704042351120100042c80f10440144802503100c070a0a42102180010701e004004c0e02407400140c3c00000e10000d0944d422601800b81c0162a995a03041440c00e207040310703805100c410041d100120f200700f00c15001d051805800c0c3c0d400c03c035554985060908034401c4e0040305484c83d000c2c0d0400c0005603c10314130b940d8400c1020043c15040c1a4000c0301320f141110b4482000c15680056201c2c20500c800348902c11080c43c805d10303003460315074540800421401a0f90145c0f00b4156000280f003c28861140c9000769440000e81e0b05210309841c1c0c84000700104404910503149003540d40c00c01064010501840703040e1055900a01140d03140d0311001e640c141d0142005035001081408000003141c80c40c401c080c001c0409807280d40e40c030f030051440300503102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683374631 1250 683373381 683373391
    0x41503060905060906060a090f0902311205010204080a0606050907021501090e0313090b011205041e030210020a03051005100f030c0909090c06170705070605060d020d0c05010206 78
    0x2078604010083e069031000401074100300c064400b83d0740e80100f400c0c2100c0c449010f401c9412148040080080e00300c0c0ca6900402182061203041031399540380d481c2e10903c4a50300d82c89604014894442403003040440c90480c861144984001440e10b40e8a0500604001d4543c40990b0401d98511041095080100f26560f0100d52403016152032011003114010080d018024545400d603941110a000c0e9002c01c00c07103c1c6888103600307048903540c2d10000348018100a072130141c0054401c103180312001020303003d00c90013258483c1c40110a600c084021802101c1948825802c510482c50403443e240000d01c000d0200351a07641e404070ba6417401800038142a42190700c07072802090b451031305003c0c465100081840c0c2c0304a510300418900302d110400c84401140390011070368549020060b00402094841c03001c1118202d854410708041d00415803a4100390441712800810380800582000988980c000390348a10020201c061081c900d80100340070440030041111507410001050000390f03010040d255000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683375881 1250 683374631 683374649
    0x7020927062e081f06050a0303050d051f030c03031706013608011b2a0213020703110c040203090d20010c020307110604060921050304150306 62
    0x10b0500d1004912909080182d4000010500d18800311610301440b51000400c0103034102e4100100045008410700c013042c01c810103251070200c0000d52030411110210803a905510741c0c0e801c222101340b0b41d40c080e04006003801c400300002b500313022212402d200d101010b5806083c0e6070707500d1800c501d006005c100040c0b0a200300702640700c04110032070781c0c01000c4200c18000c00031203480c040d15001180b10700411814104954034840c0d030000c10248015403003640380300f800b02820101518a4581a601c1c0060180c04c1c0c140c40b035004840c56001c110b182c15090b0707914805040b62922402003801d0800326009041c0441c005294426168023080040000070240c0e60103c1d021482e50804001d155680d60b906900f040c01d010451803048001400844000c05040c803c00090081821f242002502d980c03043c881203e80461251039408682071072403c0c1d400759a002d4481d44041401e160b444c0d003940064003081c08407910300c0c480d00c0c40010010f1000e0002000002d0f004203804691040180a40e107558001d4800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683377131 1250 683375881 683375893
    0x806010509090402040905070e09030702190302030601030320011104060e040506030718020f161502040b31030302060a0e120901082a0d06080d1e0507020927 69
    0x340360b07100e140c041d4001e94100c030300140d840350526107107007880c40039404090940d081101300030340c1c440088020b0061074803c43d00034107200e40903100e00c103d0024500001e5090b41c442e00c01400064069a446254221101c00010040020080312420740710781c0240803961050200d81080140d40080c1d604c1c68078001242c00f80064582800880d640c1c0489200c0c600380e04600806520050b101641210586032074856860b551700080300c0105c0c04001c0302941182d25101c20004040c17a860039109860994050030510343ca03007080c502502482000031415400c510510040d6050f0b0450307c1e510f0300c4021403198000c0c003420720b00741c9800811078800000c1103599820441107140340500701c00840d04488401d0034540c943c6d4490306003074030b00e4510629100c4d0080c0312011200b52050012006000c0840c000d41041c03003c65210001d10b40c0f1502145003400200b40e0000c1c08800005803f44045450032040ca0002d0070301c081600020120403080d80c0725220386a0354454814101d01034848070a00c581c4140040034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683378381 1250 683377131 683377147
    0x60f13081c050903090d0b060f1914010807090303031a030a0b0612010b030709150f080709181e150f1d030f07150605060414010906091a03100e01080d08060105 70
    0x6c001e03030203010091441c100c0100080071996103e444c0b0203081400f40122051202414803502d03001c10a0082820a441e841306000981d84900a411b202d4082d03541d8610f847c034910303034080c1e01a080c42c511000b0410019410300d00c4a450401501d0701072401800340e0b0b04e080c1880420f000300781081406664869050a003001115140010010121041c0c1d07840060f150402048100340482d142e0032200e0400c1c00e1000010b50080001071074801e46205039002c000144001c4650041707000f8103200107200d0303114041950003c1070a101c420061a000d80342c00180c14540c40040c0782120308a030f0440e00410b980f44809000045224001e10146100740300440c5441d18901c8a03461030b0017202030052844454088401480c08203800c02001840040c0ca082c3e1580d84036040c0c800e840250300d1855000820385c2c200000c400e841303000180d088900c40d1641c08144403801464130010b87c03009124085000c60b0300e07400540c1e00803107031240e4004d10848010781402004800000d003000b4003c9c01a504001c020b101e050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683379631 1250 683378381 683378389
    0xc0d081b0c06120a0603120c0302011104050a1205120406090f150203030609040c08100902130c0509060a0e101707030b010509010c0204091a100b040305060f13081c05090309 76
    0x50031442824005550f1a0786507210701001c0c2c403094000a03c50b10150480310020790304001c3c90a00203100341c0090100804042062400d4010340c440c442e40148844410020075401000924015025030250b8580781c6900c014250b4560007944074400040c8006d00030031280008140441c047c1c10055070403c0d0724021003500135039a0001621451141c820200424100028045801c0060080c2000da442c01928080880c0003400501e40a0303004550541e90b0f80e005540901c1076070990400c40e221107041030301c00c90501c035854100c15101c00030300088016903007141d0349100403100201d910b036681000c500c107041038a0740401800340c2a04180750420b03020361040e81e00b01c1c042d00c60702c0d1420310785000c940a680c00054003429821902610300d402c0c1510041042d00341c014854403504004000c540c07240d0b0b86849480e0b082c499444013901d00d400001c007040b440002d8112154105090924007040c4408a032a040c042d0781c09103c0200a10320401c001121401050107030503070011122000e18103080e0700c2c00c046 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683380881 1250 683379631 683379637
    0x10507110414011701020c0d0e0a0e0915060d03020a1e15050106031803080105010f090312020105100f0506030f0a021209150f010509131b180509010606051603020c0d081b0c06 77
    0x11230705000c540085074a072501c40700d000b50000c180058a454680c103010f00660f4449007143c0100b81d450040744c00140d11800d0a02c038010406070306600800b04180c01d0b4450180703c800d00c1c0c2c82807a00e007410700700103c0420070780443e01c041c603101000000783c69494113001a04550701410f00399031400d4413010349400f0039000084181103440030700f070810030050100d008680800c925000140702e5141004034084155055000702c0c851002c203500c9580107030b00c0b10928400e4444510600b50b200b00200000f0b96600150b0301d61796001b99407448051b00b40203a503140464002c0e03040300d551565a00c020101803034a91603c1c035244d00002d8072000301c0040c0d41040040340945400405080100c40000f190504201ea910381c1d400e90b10304090240d0141c10b89030964019403001b941d034900c004908105c00300f04002810b02c10755040b540191222071030007020301c0411501114a400c25070642c002c40c0c210220300e8840340c819030380301c0c1e11480445d65200e41a0040d04080305c0402d80c8440039600c01c002c0448c1e561214022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683382131 1250 683380881 683380903
    0x30c0d051902030312090c09010f082d15070915080c0a09030501110904050c0c0d0f0201020c061e241c020312131202010509010507110414011701020c 66
    0x192041c0045070011910b14441d0440a0280c01c4468080150310000811500c030140f40880b00c041469984440544217031006000360903058120f600000c140c1c24409010034401032000c2a1929203070720300301c44a0300301495002004038800007041042912a40b1036076071009090a184540d0000402c14401801510002d015042101001898040e400e00901000006543c080000e01001c0309940050390141c02c913100e014019814680403526002041d400e8541080c5480c004014000814600b242c11204031f411000555508110440f103003c000d0051034480c100078241d028101d1001c000842032100010070592102c64840c41ca940300c3c005000395458604800c0341e141d05143c101d15800a03201d112801f00940c184550290034804a02c00707400b4180c0d0301e403550014041c01e559480c01030b4618803219402400100c0800c0219025030041b80680542800350201c203480e0b414020100d42150005944465013003075020041081e42c0c5206102440d80e40450001c0d4184116101e1140e55981000f02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683383381 1250 683382131 683382163
    0x106050304020409020a090218010c0f080318070602030a1103090f04152112080c0d0c030f15090e03042105011b030c02010516021b12030f0405030c0d05 67
    0x4040740941d59181c104010103a0004e00f00c594980c0d4400300030303000b50b020b254601581e0303040e04c00e00074096000d00f44000e001030304881460003a5103566284002d0340c5c001040320b03d5003808220310400c03404003044540007400d900e8004680d11040600050101058804450721070785c81042501980c2c2c41c0e9605924014a05a034041581c5800500f00090400e107900b1060789848414501d600c4900e82d80c49042c8028060303003265189414000381120081421150f0340c0c200f460422800d440103600c5e038805001108545800940114100d0117401070311000f40a85244643d206d505003c0090b01c0c1c030030382c41001c1070300d00118900f03442e01400b0b0b901d40650f610160f01e09076030009141c05102d42904410405841080782c1c0310758900c12000640180000b940c86001507203040c0018070b4004c944503000002d480302e90000c01074240c1700c441e0060110b40320100d0a8201c1d0440d9140d0010140405c0984055041111060b071154100408e041c89d001e01c88104500c00c503c1c02da140808514003048109541066413 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683384631 1250 683383381 683383387
    0x40507050904180b01090e120307090f0602060901050a0e0c0d020301060e07080907080a020d0b0604110406390209071814030c04050c0910110106090c02160e010605 72
    0x414192824040d00c031507550800d0801142d0711050042090610003180b251402c0350a50340c903401c5000480e05d00d04003a24281d841005c1c2c0d10000d82c408006075500804600d401c5150320340302c2c401800b14501aa011030050307400380b014440100c60030b0080b1544030345900d804000420740402c00039920050402114055148411100c080d0344003908a00054a440e2506110702d081541c80180360100881ba40440f0f809070540126800e80d0106200803100c2d0001c0650042d40c400d615448601413001d80219441540c4021b081c2540e00014082d00080c400c54031400245921114100400034401060341c035004001030307070340e1054449690000c95058044d00da0308626654900c058861004ca042e0200b0009110f14001429400d030390000d03910b1000640035640301035254000d02080d60400c0e00d00000c081002c0c080a030103403c01500c003142850603894882e01e107400100c1d90b1801c44041d50000c9818540f95907840d290684c04101c401c69141d03000641c0f00c1c21070725044d0000741c1c081c018003528040000c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683385881 1250 683384631 683384641
    0x703033801140c0d090605130b031503100b03070602070f03030809190c1523030a0204091109010f230d020919030b13050a0b0c310b0301140405 63
    0x8401540c2440b88103900c0503582e83e066410300d9551440d080960b4001441d155001c21401e204406560882900e0110709140d50300748424a503142d0001000708170014140518041c6598040104540e0040c0080c00060400e90400915082c106d050b007020b0b00359030082108201d9403101e000c004003241d80514140d5440d45900c850681010b01703851756400103611500d5000d0601c40e507013030410111402c0e607a2610704608038510568007040c04003540c2c00c0c00550752a2140d0003100b048015540001d10b150011704c4c142d01c5001c43c4045403121100c3c1c410b428004100c190540d40c10110011021019040141e42c0109103102c0e406030710807221088417890404074400601d254a90161162000003e00c3c0000b07c10680c0d60310180040d06100c00d480703100400b00400c000d95003030081e0380800390300074004d091030b075040d0707281d81d883c03488043e00c4140c00302e40c20041d1103500d0f20548418102056500c2c0e004c0700828a400340001403c0300da801000400a041004010030b10604034848070380101502c01190607510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683387131 1250 683385881 683385887
    0x70503090d052d0c190b0a1805010e0603220f080319050606091c060e0d0f0f0c020d1106210108030712051318020703033801 55
    0x240160094000701c1c4044210700b08600400c4510343d54944840040c0141400d807400c42d03845905400c203d0903600110200413082c10108110128421034115108003141d85254041c901c1d8003052030000050f03111040507404015518481c0000c000c05d00e09030034144680301c0002c0c21480701811481c8a40d010f80030541d0400d44008443c8442da0704200d10b03943c5101c560402c0300e120340c401c54021079080030401b600341d40c20715180304590190130040c10007404e02404105000d046900d8103086646030956004503000101c0c3c2d800360030582080364000d070094540f9200c001d00003140406405090040c02595142e20550240142c00071580444880f00f00d940c05040a640304c89042c0d0031217401410004448204441d407244001c4c1c110402d0a842e02a603aa03990429100c4c0035201f4000d03d44a84103107001c02c0240301d00b0107030040e0360000c503285008075039030300f090001040c401c0d400900c1d0350f801080e1134003810b8251056401d60080d5a41d0060304a400d07106001007050005030740c60985602003454903480e48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683388381 1250 683387131 683387137
    0x7060e012007090218040510260f030910020105010608041716050705010f1e08090709060905060f040b03070b0c0f0f0601030b062403041103190c0b0a090b070503 71
    0x34441d426188101c0d1641d2030040a94032095003100d02e0701010310100c44d51b04191103040e115085120254500c00d00b0040950b03e40d40070040001c3c0c0301e04100032000d85101060110030441c0200350000c41d070728a079003000d00451b1442d0701030150559260000402c5000e401c400701c00e0340700e540f0900030580c101555441d010039000c2c02c40c0700126500072211a03801c001000440206031082601c59000045100300b040b02c00201840c0d0342401800f0076101000d00501a00c10340b034005611609490400741c403000000200c03002d40c1e200e0303e074054454003880420b0030140c0c045800303694191010310042e500000803903a83c0b1030500c11300c403a24200040760340030404140407881d8002511340560700c0c000401824543e44540c2070005450001d0110702195491070000302005d4011307075480c0b01901c101030b0300407012502d0b000200140c80e414102c80e100c17440ba56080c03000841c1c01e030802c1030360082c080c15420610111901794000a036891000c04c50010415000716045c7e049509041960307603a00c0c22494010b0a40c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683389631 1250 683388381 683388437
    0x6020d020d0c09300f050705030f03070b010f080c0d0305040f090213080d1e020a02131505040c1403040f06020304080c0c0405060a060e19140f0307060e01 68
    0x500e05032681540d03d0b40202ea0340c2c1200c484808050090081c2e9001c02c11403090a600c4180c081800070894000035034407a881c05265004200340e44407180e6540c04a0b04101d4035842285098000048070b100700140d91440038054580c650790100902d0030700854036034400c04180d5091081c1d24030004641010f1054003214054145645191045955405074070003075041115402410007200f40301040101c1d0004000c10030300070b0769441041404d80d0340d401880b07084142414004600070401d1110150b20364401c50a00c0414080c000619095071090b4408c0680c07154215500c114141001c05815075400041da00303005c1026a0155520b89441c54003110b4100c05900007007405002008001c14082c0100103003103d841c1d844181c5060050101c00c01c001c60360111002ca501803500c0009000d400c1c801c1141440d4a0f4010f85510103c42980b01e121300c00c50039a0340034040c0d11181068410440c1003c806042100c5020b900920089003000e1000d007800c019246001e040000d0007110f106040036120301c1c83d01c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683390881 1250 683389631 683389657
    0xc051c0801031b15020c1302030f01050d06020708030705030f0907032d02030109060c080f040203070e0604020c0105040b0601120203040c060503040c030804060e041107020d1401150b03010524040306020d02 90
    0x6969018005e9100c030b41c01000740e4441c900c000d41400501d4000d0085a1295010300c615001071383c00c100c200b04a2040c000816103905909100b03100002e00703000003c6015030b01035290544c41e40f5146c8280604500014920300d4170790003c80c01007000441c1d001551740a2940044041c4043c00002c10520f841100a04041d5056007091102010300800d58404880c1c44480c0d030351020b1581e20311101c600d1000c0107580003505684001000c001e00c0c00402803880e000980140007600d40300c0d4082042d0b095070703820f6a06a0700d10f2040c2040c00740d1980c00c0544440b050001c4201541545882e8990a02852080c8680303c20701100200160800035075891007800b442d4054400fa4803140c0b41c81c00109100c0d05d403112180100d2920020000c04804403055440b02d6078010300e1400c4000d05590340c664440c2e080c44100980d5034940c000c4460340c444110f1a40044e02c0303204042c503100d6241c134003001000d048213a0551254110708141054281a40302103038145c07038019401580d140c004c80d40030740c0284243e619038884 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683392131 1250 683390881 683390909
    0xc010e011107090e010507080103050a0204091502070b0a0f090807020f1f03060f0b070503093f010506040204060f080402060417060411120d081905070c051c0801031b 73
    0xa4500c3d54481c0c000b04403054000c0000d6900d40900f5200000280000340c1958072240740e2100501d890340012500070301c06c40070158001071113140e68041c1e030040141101d000306202c04004403003007184110b80e1000c89400c01400602d030b540e01d80c1d4206100d03965010f4001c088440d1250300f0b64549c242c039502c494000d40029400400301d481c2c01030040041e4000c080000054113000a0141026819281d050f034100010b0740c60084001c0400c01d450078004130465021044100c00005003950300c4580f07051010040014440b1600030f901c45003110740043c51079104520600003801165030204c0d421042e60601c0c2855640c41e00e0314000501035004a03400407100200c0c40d5903003100b034600070601071b005501c5140901000d04c550000c01424070101d02c501c22150340720f004c8020142e403160803410303003041c14000b0052010041e40b0704e40080d0b9400b180d101001c40c80c8045507008112040000002c0c0240b00c0c00c58041044500900034000101884090060702180d1030391502883d2150b0703410b00030300a605001030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683393381 1250 683392131 683392139
    0xc0105150d0b060307120f170a140901030e120a02010f2f09030604110306060a03050d05180d05010207020a0902090603010932010f0603050c040308071703040c09050108010e0c010e011107 82
    0x3121940e9104120364450362341502201d0340c9644000e4400d070b41141c2c1c4480b401000e580e1207018550300050790060405450788820740c8850000d1005110003010344000300d54818003101e0207401c0d1080d00301e0f0108030905d045003c02100c0c04100000248030340382124030015003203940070020107000700040c1c0341d418001c000c20301c400c0045c28140d40f6030b540c00990503604180c2d01d050400021800d2480050500c0d08840806035100e0300c10b500600b004030200810211044020000c00c091003807003d02120346070342c0001c162083d45022104140181051202945401d0001e0b01003102c900062183c210307042c0c0c542600c4495121120800c000f02284602c4681c4d650b01d001c00d034560107020a00c20b034112480151000b01d01e180c440c2c021a40704481c09040d452501d0714580d15505190711840054a1148102050302d45040110008500940c0207644651070541012002402c890040e0b1049405031f140403031141a814006c100122407010909102410544010040e6a10f051000c0400294041d03004086 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683394631 1250 683393381 683393393
    0xf1803030d360309030b06061b010b0a290f07020315011509120f050f10020a140c0606040b12010e0109110301110316030b12030c0105150d0b06030712 66
    0x148010307156503104441d22528041d00e07440b0031010780090300013000b0358018808504c0e04800150840d1002d08180d1070640c0504000c007124081c035004560594445082c00030900c1e0807070b5040c2c090a000405481407030341c020000740e480c001c0740c0c80e5052032020119400703200134410000e030388485401070107a460a425100c1480c0030540309008407000441c0752071011404030310928251043e100440140c8501030402d4540180700b02003080215041c3c811089890035649040c408407000c039404120142c4c43d031108420180c101e8000c0203242c1240c2109004032049400d00181e241d8100078141c43c0014001e001c6008038040744040090007140d0740c00c02092115180c015030008404600484d8030314020445e54040500780c1d198180c0b4006410b006102060710041544a2070726000c900e800e0018980d580d810110b02c010104040f01d10480e00045214a20194207004031b030b40c0145e00c001e2916100c01d128001400302c00103040d01a003111900c0b400a40f031038030300308562809040e02e1040d04c211a00189030070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683395881 1250 683394631 683394671
    0x12090b0d0c091a0702060c010b04020705060121030e01030b0102120c0c1e0904150b040c120516020d05090105070c0b0405030d090e0402060706180c15050f1803030d 72
    0x10100141d440d05000600380020083c40040d4407014009510b04550750b002c002280d0881044002955601d5101c00c24540d43c0c1d10043c44414032070809010150301d422121808142c031015030050f41c11640c4095800a5030200d6280d0074094242000101200d521004030310305140e5448081003c030b00024991036056001507481018101200c80c3c03555560007071441d08482d00315141441d001101e403030120b0300041ca044841c00b21a519402c0000b1b008416a001a059400d07488640021868155500f075103c03960340a100c1d13002038941031006030792144880096940300d80d0215107080110225041c1241c0e0300c6070045400301504441b40c60880d036211096407003a984588942d511912480303000d1a525402142640126030180726030801c159555028440507903c501022908580d643c00511074040010b41c0c160000e81c0156403509105041c102442035043e80c0500b408141301e4203000d0400103094410480e001c00c01d450340c0b542c4420114101003840d60044460010680342003032110b038041d00180b80c41c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683397131 1250 683395881 683395901
    0x111306120b0406051003091419302007090204171207060b1206090606090603070305060a150e0c0901020c04052203020309100c0b060f090412090b0d 65
    0x1004010801e000300403c6415600c5042d4000c4081800300a1040c013a50040c80514061000d21a01d242c840103070f582000e5148080584c84600c0e40024014080b5910034411101c045240d44005400310b54000000d5403c1241c0010401610100704407a084012049003a01c40c810000c0342e13042030316980b00402a400c180100b4015650a108100c2405000a022030003400311701600c600e084d0340d40c3c49080250040c00051900b2014585071b81850210421240c0d21858500c0054240e50816070100040d890340038120620950184505001103500031a0300354005001590014040c50340d00840c042e4400c69034004002403401204010701c20744040001d10031140c00740c0c01e45107844107420400040751400e8603042207801e2103624881c0010402403014500c54020b0048900704a0f03120300151010105140c1e290018103010303010810804200c0403190014400c40d00c42081c4030700103000c1070240c81c0092000e0200140007030b601100301d000e00f4026000e04007801c401907480c00344500b00344c098650050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683398381 1250 683397131 683397167
    0x14010e0901090b0703020a090b041d01090b062b1401081006060e0607060b09100e0f04050a0209040c03020a06081f0803090f04060902030a060f1d0604111306 69
    0x10008515100600c1105032850703001003156140c2e1134a41c41103000790448107c800c140074403a00f000c100e14200001400041030010064525660040101c218580c0180d000c030312000e04055810f085552003000f0f40b00703003075910380c20b58000c20214102ca00d1103040d01054092000e28150032403407111917408006042c0c900d203c08850459400e0040b6400b151414884c0d41d00041200c66041c4803072400100400e015070103000045403140b074080008141342d0099035208821845888200309052010f104a940301405141c1c8010500d0b068944039102c0200300e100038861144030002900f0840d03405452009190041e000c0e0310300580764a07000d880807805413a0000312a4406101030030010344008200d00782e03424507000d1400d140c142000e20550340744180000d81e0141e15550085100030080c400b844c85000010340200c0c0c81441c1c1110040320090581000c05c00180f2042402d0b80003440c60200d13600b00384246d400140364480701c2c0b43d40d103050140c0c90305d062002d04080740000d045648140700d55071b00c5035104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683399631 1250 683398381 683398409
    0x61407090302120f150c0705071403120c0703060e0f010501090f06170d081503010f0f0e030a08130c031a160f09090c0507140f12030f060f060d1401 65
    0xc01e10f80e554840c3c1c3c02c00b4500e503403012035000c940280700003940b90021000f40740c2d1801d2401d1503540d50b0415542d03030011081c01c143c1e4044c000c031920b030810070501c0800110403902d20300f001c6041200c0e190b65403400040c2c0007035241d049445256030100002d2440d181c0c8100200815611f03403184101a21040710440701e098103081c0f000c2440414582140d40f00002200141620508404183d940c0300c0010010456100c556080b02c0c000e17117080c0555a4440020440026115a000ba60404440142c4c9085800368403e0007a411882d41000006030042d5242240b050011000d16003080c141c3d029030401446d0800740f080840080c01c4c143c0203503009000100700c2501c80d00981c642142c0d03510100c1f420780002140140100004080c0d98455070305d80c1c107103161641c9000801d8940b1002003610806141c042d9004001800d035040301808200380081040c0005845c40c01c0c100580404010080c10040c80382c401c10842000720f41c0c07440200c4500440005083c01030b85070903200c440040c402446500c00c081002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683400881 1250 683399631 683399659
    0xb0a12092406261504061503051011030105011b050102070204090602030a0608061302040e07030b19060e04020d0b060f090903070201080108010504120804030512180d020f0613061407090302 83
    0x3800d0421040d1214a004101e010304c0d100d403ca451450141c020364999070741d00c001112030300b100041d0b2800703940503900030402914142408000c5420241d0300031b01410b018070050100e0b0307031301040b030300d1004544d1400112080c0c0c15060190085c031500718025401403504603032000f0441c140c2c01440c8981c650000c10002c15a4625400e40c95100407241c1800300d0490032008001450310b0382c0301c4132280b007070001240c05240c0c0300d980f01940a001076682c20300382648a1110482c400050183c9406030816001842d0103013000d0340410350b4081801001821022100006469a1076540c04410752950090140d402402c11142c06a1290303c400800e9000848003000811204014014503028a5000d500304040003030500301100c10034030141c01203081040c02c0011074100d60107014207502442030302084080c84a04418031034500000d9107244801d54200002c181c0103598007080c42a84040c805c0340109000d001803601500802800c41050340102c00c8900380070207186d12800510580b4401d442e02c02d042072078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683402131 1250 683400881 683400929
    0x71e0c0201051e04053114010302040221010308210c07020d02061611100c0314030a20090103060b120c092d01090b0a12092406 56
    0x45520041d0200380100031044980035030707000e403618840306490102e0400351103800041c2c40110324602d08801461610010b007400441640904840070900c00c2048080c5107050210700201d81444064800c55010840399035422030400340c80f05d8500000c5c00488150703100d10f844529034000220361181d13090401c0070b00040c00505021310703000b000040320303140c107100140d030800c41c003000600400c82e000042032100150b50294201031000d0944110b005038110038089044c0007c1c0310049451100b00300030141c611021980184030100751011504040396290b40302c00320740c0c005c2e00c1c00940702111402031a03008102c80742c1e0341010b800b00301c00985e0103100541d601c00c45001c0601034440301d510068109004034110515850081c40d169401a0a006c0900c8804014089092200528031000440d50340004003541e0300041e400082c014203c4007500300410614024001206008040140b659400070703c1c041c07060f8202c0b62002000811000400c4c03220000c1098060079040c82080c0c45510f181c0322034101008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683403381 1250 683402131 683402147
    0x81c051210080f0304080a0602090117040c03060c0c110f03010608120711040606140d0609020d0b2110110f07030f02071a030a0515040e010e0c0406080d1115071e 71
    0x8030520051101347c43c5601c60800a40c0320000306414004a080b003605121440c0416a2041340503a20541d1198510f00703280c07003960010b101c01010040c01c450142e0004040e20003444a40b0402d07503013921540b00e020040303401805e644d0071441840c850120b0450308492030380000c24030284200c03948000040e04105000544005000314008130b1070009608942e074114401501050b0640c00c0d020940ca07a9a9000b102244d021401070b00000c0e8448040015609009196035100181c0c03078142c14000c01c80030003035901d4034071002600140c1c60b120260134041c000300c401914054954810107654846041c600039003100703103805503c0e0142c0200580060322100c0004220102050408124035550781c400582000340740041400b00c15401424045d5120340310740c400d0100009108000107041581c41c1e40c036a24013540d01d81070303502c100d0511400340000f24000c81c0c09040c140650500c0905241e036510403505101044858510800ca83c10402ca00b1030740c0031031165004029660a001160840c03003048038041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683404631 1250 683403381 683403389
    0x30901090f0f0e07031113150903020109170705100c0b0f0402030a03200f0607090f080a02010f02100509060714120105010f090909061410081c051210080f0304 70
    0x14500c02401c100080c06158030f2a40020685400101424803142c0010f15030001040305004c540c1d0158140a496480b4040e29903140c002e090000000e0715690008040c7c4401c2d008114204400a01840540300b0030000d1a0280000a06e141031040080b08010080c0c0c2c07290005030340d00d00520001c25040b22801d0200c5000e19000f5014103420022502c0c146c5019288000c08035080883c04010019000305120464404104030080d000600b850030008099507041e4001c0440586402c40401c542203000035240401542800e01c540f040c40d82e00400d9040c41345070310402542034101420010041e0021520340d1241403241c0307400030156000c0c200a5128050110502141031600d00140442c0d8000d82c0c114035611018505040d01c182c503500540242d0342c062a0480b5425219811640c3c0030200c3c41d41c4583c071090062864108516100310b0070743d580204104000c00419070048040210300c55000c84405031000c480399803103401d050140c020444244d210741407c60180c0c440f001e095910110480d0104c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683405881 1250 683404631 683404649
    0x5030a08030604051819021c03020715022a04290411120f060a08010204030c180b03060a021c1e1401060e01110a120504170109020907080402120708030901090f 70
    0xf507084010340d482800d0101c030069038002018604585230000803049080b81340c0c801c0e4003030940d080c0303082660000d0075419200d20055410800d00c0460080341003141c803281050b450a0f48609005403c0072a00a04000074001400014035500c41c0c5a02460600310000d03041c241d404108450782000318586900400d038003684031103400c4020a440e050207421300340d0080c100a0a9600b600d95603584a802ca9000d41c1c400c60311103140680401c091801c2100b50b800c0300a201100303008591440b1f002a0700c41e03170010841c0c1715a0b039001c210f03a10740c940d14200014151401c0d01c02040500a17843c12111800d04070b00d6100000c40c18102d141100e188001e01041c121815511100e403403100d0340d001946c0504030781f0760120440c4151021003010071001a0242d052500c0d030b0f1a016500ca040507541a48140704440c4131403d6070500c0300c0900103072a510301850340010a460040b903e5107580c400190764011b840514050340c40740c600b001c501003801200800035500240c82e039010050381d0303481c00038240c0541d05c07468101d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683407131 1250 683405881 683405893
    0x30f01030f0606080d02070303091e030818060d090b0612030d0b030109230709050403021207030203160312060522050c1204030c03080c03061e01050405030a080306040518 75
    0x1505403038000c1d030031610540d40440c0e0182c031040010320300601c81aa07140140d105003010401d054002441002400c0400f0342c5450884580380c80c0191042144402000c036480082c0000c014200060000348810700141400d985211001002c009000440001c9d01c0b9a084c48001c200a843c0c0b005030101c0c00282c0102550908003079260f4000109800b0b035109426540381c0c001100011000e490301d007180c54503099401c4180c010404201c1c81d160340c9401c141130061402080c080843d0300090040e500c09003492816075200460b280c12815405618881d000b510340e4244d6000030581c0261460480c529200c1e01044500da03200104112010ba10b1905000880302e9101e842004885400255000c00b02c14402803400d080d9140320301440d4001c65080c8d0019003592104820960302110f2182c120408212260640c140303400000e00040c80303540003154440c8a01d0540c25164010340135035005040044c00d840e5001c4081c103003040c2990017140c12901c2a0715000020304840480207880000c400c0300402488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683408381 1250 683407131 683407133
    0x60618071b0f050c03150103020906010e0910080d0c021c0614010608060102060f0103050d0f0908030d02031006030c020706030209030715030f0506040e030d360b060105030f0103 78
    0x41254014129000300510425401410710481041c125000c0c461080309500300400d08100d4104800d424043c0e100b6003004140c88114030f244010725040d02e40448130085107448800040c0c50030846c040b412608203000c442040036610000801c8030440d04c0e441c00395094040c0240c01101c3c421080380c0025881038007510704030072200703c5031005c080e0f45115040000321030002c0480301d00304e01803d07403102001544070390800c1845e5030705105103a0006003c664003583e41d415591030710388070030f2455030110400c61001c6880005512800e10340c001451003605484c2d480c0100044940a54401c030381c14501403086110019000c0c2c820f2041124400700c0e13602a1050a0400034120043d6206076201c540c03603c5075902c0030811011020020f9410001509c0c00124401d01c0941d42c0d0a40c0e4006003164411740ca04402c1601c6064013104403601d480c8407000c0055680d40161030f1289032229410b80d5907040a412078440d005141d03c0f6a42c1d546107000b01d008072141e45d502c4004440a12003115244003400740a80100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683409631 1250 683408381 683408419
    0x424030602031005031903260601050306030c1e010e12060c0c0a0c12020909010b060301092a0504030311070b04030809040207051002130f0506070209130f03050a110606 74
    0x10b0f04035010400c02114280d981e40000e1034450520501034042080110090426820426211070f100a03d003d40c045840c03007031444400590700901103810b00c4000800074149680611200d0000d1800501609070710500c40c0007035507004e030b01d43e6185021800000d00e201d61450000c0034100a91f00c1c00c00100381e241d4904401000301d0308001c88ac038000344140c5045800043c00300c85520003802e41c2801c458a24145401004030b800f501070a0f43c2e120fa4905000c40116444407403c40f0f05623a4150340200d148401d440c0c6100e08500c1941009401042081d040e4a805a0200c002e204584c0666200300301d000309030805544400441c810742c2c540c100100010400210080040c0192201c0140010704000311619610306100c040d61001985503800140840c2510b805140c281c007401201313056903c0241084007150141c801ca07103000c1c2c4a00d110030002820349000101111401c1c0e4400b00b40350512a4524014105070090070303080020500c0c0d100032928403200000c68a00c5504010306048441e10700314014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683410881 1250 683409631 683409637
    0x30c0a030315031217011202090412090b07050a0209070207061e0908030a080106030c020d0206060909030c07060c050c04110a0c1704060903020f030705090a020a0201020d050408090424030602 84
    0x10719820b01d0030350000000c120b4141d00c0d651030004545901c2104410300c801080a100160000040840c90f40d21000158807000e0030b25501c40d610142849052400841c00d58030082994002000c42400007034410801c00702246803041c0520a80307100015489125044e6160a0203001e414001001403106400c4a440520b800e031489400d81030910000d03403940750007801c41d44480c80d6500881c01c0000100103080e031600c00c06142e00c5030361000c0d00c0384019081000b5182c00000c2c005504c04c040b400302183c600e2a061080f1041081910216070040d40d9440010f022003118900c240c4545c000c01003c014281002d0003003480c01d07100c00426501e8951800300541e1000d40c410700580d8402580800d0074060020340c8014030107030610f074680c698800c0c80e510401040c0d060072149a4083d80215408100c1c0e51981c00e0030603040b01d0b09420158850b44241c004900a00804412a0b00381b41400c0503c400e0180b810002c1059910a0f6070030303c001020004c3c01400034626600401140016450810103d20b82d5806 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683412131 1250 683410881 683410901
    0x90903030a0b180f0f0a051512010f09050a03030e010c3513051209030309060a12021b0d0309080f0d060e010815101203030c0c0b0a02031503030c0a0303 67
    0x200544210030b640150024840c12140030240b10300e40000d010b005039152032171580c02800030350180014030305404036030413001c7d602c0001c40c0101c101e01d03031105e182c0c174013034010040d030036205041006440d0003820041c0d55400036250980c04286004000c52051106000d020000e5074603888040b402120710442250310560070201d240f48034510784c0c40c0111700031a80315480c01401340d4515001c000c08a8140035013491003841071540c405a080040c4c1c001c90710701200750780c2008c0e82140e10648498110100382c0340d0048105588880d82e10000e00c00c081000410440e49100b1308100c00c40e4107030405001c00740c0440c0d02840c1c1c0030b040c55034140810445001504000c04103d00003410120f21507a6402004140090a0b04902c905400654801041c1202104a660301642203142d0f84a001c1c80d29031041c80c01c10000f20050b04154640f43c2518106001d8070000c1c1c02e059100f03142007094541000c03408000e4100303652841c1c100250b000070190a241c00415a034038001e4001c0036106904290b0340c10b400400005407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683413381 1250 683412131 683412139
    0x20a11010c050601270902090606030702030c01062603130306020c1603050105160f050412080405061b0705030a021f02011b030204030201090501111e03160503040e06090903030a0b 79
    0x10300340003031000e0080364000c0842e50b11492404040951543c80c55100170580741125241c0007480c2d026030740b0649041c1c0c03c0a02038542c00c0e0303031781c4a0020490840c45401c4811010350308061002910340815880515081c3c2110001303102c900c01d1240c1c1644034800e440d501c800641310b0340342c2800400c406031f00034000865600f0071504803a016103000380d090039841d401030f80c06964620420004030300c503202e600010202031820204039140d640021303000d4000e5018000c01da0b540f80b8200010004030008a901508004000d1074035881c035100042c04040c00100740440f80d0107244800280b0b4180011180c4050b68003c09108c9802501c9000e084181c1418450408541d201c21040104404c2d8100400c036400c4c1c1d83c1e4026a176541140000b45c980078440c0c0c050b6040080d0204000c4200c48080380400710300d003032120580ba03100c011416070ba00d0340c044d5040340300c1c0e00da2540c142e40d4104000000200f0441f00c12000801c141d940356003c000400a00721801d801e81d4208000040b848040c82d480015840c1000b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683414631 1250 683413381 683413397
    0x161707120f270c0f0302090a09050703200a080120090307030204150f0506190f020708030a021b06071211010f02070b040521090d020109080312010e010b0a020a1101 72
    0x80031044000c00c060906048400e500040c02c4180280007101101a00c00f400203220b445103941c0c04148203030310080c55204929643c42128041101c00d00440c00210b07044030382c5400d0402e03a41c082084000c0c80809031440740080d46000220180c040c040c1e4455101920410a19590030745020100f96002008040d454051140d010006985920958150310f000b4034501c2c1c1d48a041c15584156200b03160849442020144088849440d0750284040000611328041541c0750090100380d203400c0a60b003003441a8003004c01c00c03003d41540080d41148a00d030012405040001000c103000841c410144003400140c0852070400200313008401c2901440201000043da00c0448402002280c10403c4225040301c20300c0148010320104016844132209594a081d0b6508228500d82d8407510818204601501041080b01d003035a0191142c600208980c80c256507941c1503544003180c588109010701e069181c07201e000894010114015240000800d4005002084164440030840803d501b0f981d41000024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683415881 1250 683414631 683414651
    0x90320040207060c0c0c060306030c060c02040f0c080907060801032112020a030b040e0105150405070c0b0405030c0f06040302060705031801021605010b04020906121e161707120f 78
    0x6104440c52a0341c151789070340000e41a071816000c001c0b1349a012104150521030180f0100b0740901241d0111074007828803108160301c0c0e1006c5800f42174a12500c0c08400d01d422841401107400252041c401d02490040d15400c90301e440054a1104080c040946030007480c0441d84209092102d18142e896030342c1c2001030241903035400d900140c0e84001c84540009840d2185411035003014060181c048140d14024031081c0f4114044100325150711444a2150b0703114004544500d02864a0300030302a00102409003620303250802c03607a00e5202940c0c41a007485140c101c02c11382d45000c540503000b80c3e4903038003410854a41e048101c946402c0501285010180c8801044c81c0700d070f09100030181055800310000158440e41410303421900d28034981c07400b039801001100707845d58650040300d2150361018083c1900c0c1d16001890390b440c40c012001c1030482c0325900d00b0b01c0f10b02e44465a501903020066900c1007172428040c030407980c0c000000e40d41c0c00045102c1d2000c4e20303c00d015603044090b5400140000092020107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683417131 1250 683415881 683415893
    0x3041a04031e091202010f051306030e0f070b0a030207170403140706180905041b0b07121407020904050c10050a030506030a0206251208060f01090320040207 69
    0x1054504a001c1000c103040b01e0302c41e1654155040400c00b0710304100f8601441e0912004444c038440000074108400105010307441405007007562405400500e80040c1d003034075410007a006254216820360644140d403e0300703420710b8000640c80c0a403000300306814140b0002d810b0a17006034000d000100c40c03901038011240104001e08003d000114040d004c08036401a00c4416203080200c25040b86080080d261881d0700c1a11140362102c040b41c0180d00c0005203540c2c2e5017408400125404901d00c0780e1445000000349000880028110a40c0102028007541c40c209900b034600060030420030440010500c00000589020300106a100380600309491200e5a11800640e0100d090300420000c80d0340450390311620740e030521071036500076404d400804d10b4210a0300012800d00070b80a0000f0100301400c40010045d00c20b000d0240841d60014200700400c80c8540003038071107003040710032501804220404618540c40b5000c800c040741c0d080904060f02c0070f0b6040d840d2860701880011250450707000c01a103030024107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683418381 1250 683417131 683417183
    0x90d08090303070b07030c0201090506010501050a110106090c0f031e0e0307050d03021803070302091b041703041a1608160803162c13060b130e09010911060304 70
    0x8130a804400c61440c1084000c1c00312100303001440d003160314108204001610016146064030f0090921a4468410503000c4960349000c040e45103a950800c480040e04601c20b40110ba50451952101d8003000f13503182084048030044064540c040640c04003030f03940f0a0443d0700200e01680b80c0b0701a02e1418909440c0e040c42c00800c0003141000903400208821318200443d10340d400b1400840242510500d5138000402c0c2640c05400c02005540d28170f1005000b0414038201c0c0d00403d0480001d9503144188041c00c0e440e50031074403842c07120f10002c82400305001009011521601d044448401e0382c2145611501d031030381c001c08050760aa8080700c5440011502e140051440f4080090820001c4041c903034005189038812518901d201c0f41078000c0c01152040c40e845450001303001c0d03c01408040e4100749450141101d80d028640d9640001000b00d4050b503074400441c00d40f0064450f00070242c417609089402c8800b050409096148030015504840c9010030085401500404009040c01d00014074017841207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683419631 1250 683418381 683418383
    0x31d0303041502040b030411030712051509071e08151324020c10061a0a0c020109090603121e090e04060906020c030406120501060f051b1606090f0b090d0809030307 72
    0x2441200c4000d025240401c252b50140203864846454a0070303d03990a544d81c40c500b00c008a014250a00040c0103076403c0040500610011540d81d1780300041c42126122820180545c1d00180115041c02d40c0340d810707107084a03004030b0190402100d604100c2e158003911400c4c080d0410003032031000e130038913469828a00103044064840346c003030103035254941103070400c543c8144d01000642e84150b12106500d0203680a8581c801c80070b00309a80040510f20040b14a80d090790001d03246140b52180110600001e03500300d044039210341d21200069540b403011003c49140d95164000010708820060007109140925030360028492040802c05101d1540d4510590704000c0c28a00b840d40f0100b030400070640e00241882d01d03494040010071065062002c000c022544000205050200000355148100501a170698150f003050303003130b03803212400010181013a00303443c451007002a641d60303400b08100c201c000742d9101311200749603503503d00083e04050010710081c4117000d07950f03420280070038141e5880c1400241281703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683420881 1250 683419631 683419643
    0x1b06030406021e0a030c0e04060b2b0203070906030e0601260f0d0807090f1d041e0516050103020c1507170a050609090d02100b0607020409080703031d0303041502040b0304 75
    0x11b070580303500080174004075510051042d41041000c1000390700310070440b28501d03c40c944003460465540100c0c03200401d03092295000602c00404c01c48890f07400700d1100c09980d41c5030f07000c0c0240900080700399980c000c00e010341103451062014208802014110a80150925801351070340390024004031070414000031405804100320f1010000101d40c0b000c00c01c0042e180b903d0001c209542440380c0850500440c00001c1e51500c03205000c5000c0c00180c50541d00f40c1e151070042d10482a05600d8110f4a40860b01c1e41c00921140d1034178041140c0d030090094075428007806005180c0020407150340000c0f208081c00701421311a0907924518030b1800007500d6440b0307046500c0b01103040d04010041c003014003c01805076619800020b4900001c44c1c0c040b4a03011409545030b404605001050b00189041c400d0400081d4400d01d0041d5507010461904064884240a924100000442d0000200d032500030340304038403565002080090001030745c0c25502c0302428001c0c9001411300780c031103070710f070b0443d40c002c0d503054a039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683422131 1250 683420881 683420891
    0x306150c01150b0c0d02030f16020105120405010f0b0312091509060406030c020c0105120609061c03020a02090705120c0304060f0614031c09060c0f020a030f03021b06030406021e0a03 80
    0x100102c10804210b024103d4070003145071080e00b05c89014127008585409000000424054055a104005444056412000c50806ca00f011b180c040e00800505400c11400c0b424041840250716001ca131001d00c0c241d131107815a103070404042c200540000d103040d040041170001d00c6170a50544480b0054409417030207480001704448803140291400303000c402d80030f04000e01000740680010b801c140c62a0000820759900c03207242c49600000d640701c0081408900d83d120706000000c141940004c5091045001703a4980c08640c031600307030817141c80c030425507803070f00841c48400400c0211100300020741c0e1207400b4000008455991030a0002516110b130b10100d405562211100f03100e140900c804211091035101d0900d50341d0341da190140034a0312510918047c0f1410019500030301000c001841d42f101e6008007400110780c0c0380e2a01460801c880c00082c0c00601c9540228003c00003641c00305091008010a01415a900e44d82c4070806948030351300140f01c2e00c0d1445110105506248040d14114007251400b04e6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683423381 1250 683422131 683422147
    0xb040507060e0d02011713080a050a091d070807020309030604210807090504020706142a120103080a0201231605090904080f0c030d0f0b060306150c01150b 68
    0x86011401c4010500c82d004a43d58000184e0304045070048144035210146c02c00c0d07540001c0b412000e000c2c2c0101800e14030340001e40118150780400100700802607911140040344c0c94004803031082603110b007001d039000c061f440030a403610f004140281d884a9148100d07860701400d000468241038090f0750860b020310198028140c20084042c3c10a00c11845140c188100e10f000080140056140c2c442d85004641c001044000e0080c1c075008140355103404130f0b10080c2810149000e03200507001e040103882488890311211340c004a000e04650807288040807100070369003540c42c0c0201c96840700c10b581c41559624110f100405901c4115480c0140c2240441e00d880e141250f2054034682c03502c41040c0c20000104980001c070fa071680b491316001380d00b150350300c0d07184c0945002c410f110f4480c0950407100b42c072001c5441c801c550269005402c4201c001c44051101041070010320a1601090340d019134031040e49030b85071030354508140140034524007540010441c4030207407040504400403500403c55206000422074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683424631 1250 683423381 683423387
    0x60a0e090313152006180f010911011404030314180910150e0a0b0a020109080c010e0c0405061003052205100b090708010e0c12070c140102090604030204020904090b04050706 76
    0x4d19019295140f072040d090808107042c1e02c6420090140c03942c85105200c50144450130800040209440300007040545001e06000031515201d080f19800511001c20300400099541d098030b0440794113442e0403550b0310005011421540252001100840e0154451442d0b80d4030840d0042c0241c0b0503601502140d401c0c1502da00c1d0100b0550480001d00640d0801e0408540f0341921a50486085003006030302c80002c0b51040780500801403001e440c1078000b2803421401101980a001004c601d141180d28400d07025050106441040301c10325031000500d9441a8518000d401295005003a0002904008031102040030091200401501c0340da000307000f00c0c4281d17000d070b21802070716501c00c44a0264615003408014500c1c001401595580c090315808912404226401c3e41d0342d05d00b01c21021082c40c90311180081030203000f12415118008400c020314514038042c400c0340d1818a01400b400d02d0300f42503400b4072007c3d50081c096180c00c656241c28050100e8441c0030100c0c000c0f44140046c187c0079291034002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683425881 1250 683424631 683424647
    0x906250c0911040b07080c06010e07020c01080c030708071206090207230c060a032d0f0b03030904150305010f021c02091c020d151b08060a0e09031315 66
    0x11035030403854a060006020248001c2c3e400700c402e515141540c1d4456407608813498054a80000311a2041100125101c0b0303100c203109200d81c100358222a000f4105d80d004403466032003510b113038002802c108007044100c1d11550440e41d00170f4590400c0190050284013103030803154150310029105034080b8820080003e81c1c01140c3c4900200ca24800700c207580d0014058641602d814080d1041305c00048490f5400d0103500018044524184d240c01e00b0b01100d0031500020301020340480245141801d00c02c42000c4034490400480741c0a0025030030154041e0130f01c802002ca24621003040014403c0000015109001d44072804110200140e158074a1808501d500c01041c00d035056114010701c449901d544500350b039400c0d0030482c4900d803040502c982c004541c65005607080a03160660072007503110050207940007420682050702402e800715590501c102c601580030340d44c1603030200e0401810050301207030040440e0801d64131816603180c03004444e010b0010034a81c2c0d101c04c00034114099081c2000340c00c1194 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683427131 1250 683425881 683425889
    0x50307030e070302130510150801090f020c060415060b03090c03070609031109041727040e150a180501060501140918090c060711040510060c06020906250c 68
    0x402c265821540005e00d5650450182c1d100700c1c0d170b181c0001e2003001c03407400f118009009443c6000c0c040d8848440003040800309000340242d250410901281c1c00300076200b20741600c1c4d41d010180405450725500e1401202c420b03400b641000740c4480000c240d80d00030f04015801069034030024054a581d80080c1030425035154065803d00c442000e0400215031254100d465028040310802e44907643c52802c030903100c4520101090b4058041071601c00003540701c0710350058400c812034010344058a201040b007a90725030007011001d50403501402c200c080d1819081c64204204107004100303021694a120b1240e11100030590f06a910b0302e104018950700f2a8050710700b40d2119120615003c1050040b03900c4000c0502810307002e00700e16000942d035500511907903408101c0145100c2d90348440d401c1000c4440241c0750014480c42c900303000310307580d40c0c2d1039807a00089075000e8840b81a920f00e00c8e150380000f50410030484d07030003031000c000017540000c007010038174090b54200d9500d25000260b401c1c144403000c15600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683428381 1250 683427131 683427133
    0xc03160b06031c0302071a010806041a060d0201120209091e011a19020c27010506120f090a0803070917012a020106051e0306091501091812050307030e 66
    0x10b00410036450801043c02c10b03520300b40540d45124a150820918520b114a40f00e1107148000106401e6400710b650350040f4007403003900100104202d2250f041e407005460b0780340e121441864280041d405102005c8029418400060801240001043c0084021141c016000d6540c40002d211030191803009409030441d48402d408500c41d030221140d482c032640c2810070005810010341c5c012548200544156203101405030035082418080c46c918401401070040d943d0b4040e03000101d141d0900c0300590702d541c000c55520344040d032280c12000310181e502800c0000300303000d0061190049034400c2c4c000c50040346195611081d0900e0110718442590241f0240e0519905014900b2045803e051200ba950000c4004840001d040303c4400e900400150740002c2d04154222404410050102d00940441d242036094600c25995100e0301900c1d02100e07000b240300b000c101c0c00140041045584003d201034841c0c0b07101c07406188281c651a1442d0200d1035803a000910000801011707030340c07601490014110544c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683429631 1250 683428381 683428393
    0xc0506150d080d022809230d141506040e0a110915030a0f110303070c031101030b060309010912170f0c09060d0902090106090e040b09030c03160b0603 66
    0xd0004030156901080078100e2100802c1c0c201c51002c1e503504648100c408104505e00704000e908850a21aa05400c100c0c040358661000054551681e040d5203c1c440d100901461102d0103001006009601e001c000c0c3d490400203007122406103400c001c4400c600071344400000951070900e00f00000c1d40c4a10200030b21580200107035400003244903241060784101240c00e00c030b40f03654484001c1540040114081c0c0c0c144150306c0c00704180903d0f90f401d008983d0240c10b00168010b000e00503d90b4900c14403800614183c00f0007404c02c041403007056007445c0d03007030145000704044c000b900c0001c02c2a003041e00d034403d0340d9642c4e102c11000c109804019059150342c500340300c500480b00c41103d20004030000c200d844034240540024004200500c11a00c0d8040f005146036102d040c1803180354010400d16508902a04206002145042c05810340030100c50300c1120b002c10342c0d55980c0c0c0d0022141c00203485281d0300d00c41800245aa45005e2014141c0b1a4a452080c86030b00c2c41c07818501c401d420040c0146010760828 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683430881 1250 683429631 683429671
    0xc07060305042f043305040f020901020a0f1b0b03150f010e060903011523010e13090302121c0516020a030c0503070b1e1f05010c03090b0a0c0506 64
    0x40f2030b40f560810494000550721086440c14031051203590000302014031602d0700d1443e450f441100c18050300d01c01c0c1e4081020020780040710f41203210318910280942c0c490114100001c90f01c0c40d0715000c66205501c991383ca041c480390b1110319440683c010508819021080080404e0340ca00504007200048820002000b41e00c0000707840c00e43e2607001a40984170005640303580c0c1c1c80c00d41180b4114070b40000030500b4555180301ca03000c0c4020902c82901007080000d80d8243d41d40c41101d0804200000030049080d1840d0b182e01000200a40d4030f00300c0550044c0c0014042c1c0d003035460080c00840701c209224500051615041c50100c400042c86039014546c840a1150b00710303400544c1d00c01c0e06a160601d05201e211604249140d0f01034064024100241e0008211b50340c0015030090b001c0481c000304081e102d841d9041700d0718010084a900e80440107101c00100002d40c032641d40306905501a0802c00b04440e2075841c040419802040440b02184001b4150800c0090401110380d00011034001040b0000e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683432131 1250 683430881 683430953
    0x70f0e0f0603060111030c100b10020106053a0302070609060206130803091f02042402100f15090b0f2b060b0d030c05161d0a020c0706030504 62
    0x3e03200d43d0412901e20400801060104102c1310140a150101d88030301030b0140f10343d0050302500c00000c0c002c02e034880c1d5042c0124014010350090780d8004254603500c030184001c4007401061004102c2c1c552503004100c0507094017405c0851050745c003c2d40500b500c02c0c10050041c0054885034004800c661004040210210301c031300d48580c40540c4615903903aa0348030f85103194600f03140700325000c0c0c105034450100d042c02c43d0031f40c2c0240100c5100f003052059030b240c4140d074024020a000b2407080940c00605a41d451a1040d900c0030020560354200040c541004900340d0418a10f99040000c00d17540d1000919410300d0030f13101d00c401504045070001e1280c00d00240d51103040c9811424100e11440080601040194030740180040c0e2001820310f0500c000c0506005004140300c0c08107581074010014095000c980e214040010ba420340500307000005440000e00d20401401004880440d5080c0324060b6094401e10800004150070b903804111814941400c2a09280117012034403903600107002c01c040405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683433381 1250 683432131 683432137
    0x70e07050a0c1b0302031b09010f05090f07110d0203031f06120e0102070b2503020901320324041a2e0203120603030403050a1b03050303070f0e0f06 65
    0x1a10004040f8140d030b40404809000c0e205400003980750288209429107035122080700c00300c0e850101c0f041d28199a8501c1181142c0200d801031681000070040043c0741c03013180518054001d1503504c0d00881410000083c0e9080110a07071200300181c0000090058040301c072180018044103016804080624000018000f840c104076140c01e16a11031742c0e141800c0304298103079030b40603800895407042494021035648440300e40c401444984815006480c401032310034402d0b21b00940060b150b00340410036a20069880800f40303d000d14404c02403014a0f00e810910310040c40c0101040da80d6561040c0c6195900c0318403154443c4050300039482c01c0c10f40c40c1000140c0c4490384400354183c4001c0310890340c01e8034014200070010a50030303001700880e030400244c81d4000010245200802d117004101d071295001c1648070710a5200c050025407208143c0f0003c0341d4112011001c0400d131501c8012002e90f265280703411600104d4401010032454840d4855a035040420100310704003c4500040c0c50041c00e00180443c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683434631 1250 683433381 683433383
    0x1020d150b0a0c051615110d050405040b030c1003051e04030c061107020d0309080c0a0e2806080601050916021c020c04150f0e0c040605030c040e0702070e07050a0c 72
    0x1c0512440d480500c030090003581000c154030117181c40655102c0011030307454102d500b1400005101054540151000800d507004088081e9684c10b2510b03240c0350400014000e59040203034140158071107444250345511464400b41c1f15a2004a59881d04074105110000341e07400c24017401c942c01c0b0401c000a50700040018055500c0a00041d81c130004104031a01c5000d6058000c0d0450901090740060541007902c60b000c5a041404803200700c10048107000c00145c49114140e0741a81c41404a48405a881c9031400a010382c43c102c2a000c0020031840d80c1502c5155128904030b4004c80014000c5040c5180c85503031007010880088034071a500080203503500200350000d20a1403142c08148030844c402c1c082640800c4008206002666000c50221250300d102e02c10f0300403010020100054129110342c5543c031542a41c158241040d24101c1c080d54503500080c81e0507104201007001044800c912601c180c0036540f83d600501440c1e00302001c2044a00d4043c1255050000512003408802ea224a90003401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683435881 1250 683434631 683434637
    0x601060f0816200f0105070201020f07110607020d1506090e1005070e19051c0201021902010c0c0b0703020d0e0d03051e12100f06080711150901020d150b0a 68
    0x1d41e182c120100c4007011101d4003010807448107405000307422000101184130100700c034020030241e103680b503041c0c1c200d04c6403005c1401508002d10201c0b02003002070010a0000321301521052500c102a400a0314506d4460811241410f2014504058201511840028204c1c2103810020009900b440582d02c1d130070000c6220b0100d0b212400110400d128000900710070304003800e0410a03091800840810040c0703401001d001e440c01404441c000c0200e008500c07076258068002c2d04030702c0741040c2444410300c5650401da06101a41d4401000207440440d180000c007818002162200c03100d240080c1058881c542da1000c0003803200c0500b0301075850103003020216030b05040007030f41c1d007420f44140c0401420340004243d080501040c0410200c2c201c2294602c42c00003841d501003181c7e10703144811b01229545c060304002030581c80000c0d1a15002d4800300d400951440200c503001020f031305200b03000240031951008140d4001c142403508211501030440c159410321451105181008071a8946000d00a188410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683437131 1250 683435881 683435911
    0x312020703090305010e0c01081f3f0b0a0501270f05010f06020d03021801110a0c140109080c2b0b0903070c0815010b090a050604170601060f08 63
    0x1c0501500c8614011907125000f0b22425001000351a1a800344c0c2245078040340c0c1c071900042c00143c0307002e10a00034080420080021b00d04144041c04440760b000c3e5524140703d02d81d40824181c10b00c440090304481100301d180298400c0300d1a1000742c0c40c0c070280110540f40d06020041c000e456814000c1d10300c0c004046010842c1c0309681199102810b4601c1c80111194070b0b20b000807a000d00f0a421400569541d902140d4169036001d00c114101d110b9092400010340703000d024050307158400e04010359915051000c80700c1c52041e41e00c07003008030038207503004500440d01840e80f1512960001c400600411240002e0181c0100042c00b085a00d030f06540740307142005002d001d0a4086480c9180c051916411880d120450f01d0408010382c0da0303500c111019903801ca074ad54800503141d07600284000d84028691604105e0303900c0c000134850706800c14803000b5444101c2000c007003070f5070f2100409040101984440550415292000541020010381000c020000580342c0b488445801c28442030300304c581d400711810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683438381 1250 683437131 683437133
    0x605090411120118060609050f0f1f091a09010803040303090312170405060a1407020a1137120515060a170307140613060905010f2901050703120207 65
    0x4018841e40b0044c0000c40c003054010340910407a54401402d07500804c40030019074a8a181045241c4800c039100b01d007403400351000a020007006130320008011400c005804009448102c02c00650700700d0300e0250106140202040414644000098010503004014515203421030300d0080c40c00c9190f001c040c088580c072180c620340082c811001348046180c44603460705141009c0c0b40250b12742406480080c225800e02114894515607220018010049500103148841103607441c520035441040d0841d510000400710092010940c8172461140e80680e21040070445032080080d041360350700d401c513107004a0700000c0000020400941e1460071a00001311319025550800055030f640d4468000c080b409011620603040300400001a04c0340307620661103004c843c100e2030492a500d42c1d0441e561403040d0b100e8901c0c01c0118050b5802042d4403406000085150740c000748449068071203036a03000c1e80c2d4044450070b02c10300903900303428030b196075100b442d14038501030443d103000300824100802070b801590b001840178 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683439631 1250 683438381 683438383
    0x60a1a09120706080405010507030209060406030c0c1e050609010212010e13020a0f1d19020901022401030507150203030402010509040b0301050708100b03160e0102071208030406060509041112 84
    0x10071200309107002c8591035522503c0003061408107841c200c0f0b41e0b600344400b25441c0c90280c020350791041005005a03042524041d400c6000e804812140014840a4a1580042882e180e81c0c0c80030394400041800901c061403400031710b8030400038000240c691040c029400c41030100c0c031410b0304607940b02101e070500c2d4407501c4080b1607105640d60000c2d0700c52001100000e22164100200c02101c0300c040301700007610800300c510560100c0072144c000b289205108a0742000c48958050544110184115850507100396032003103d2010700c4001034440d8102c0401041004010001c590207000c110300326001281c814980a5030724040507000a06008011640015940343d5500c002d4441d80014000c2c403013030602280181070f10b0000e0b80d25900d84030700c1b00790214440d0f86200440c0d0040076543c03242c2180c0880c86008603503070441d044c01c4504600850000181040c0301c10b000e0380125010b01c66495803070601d40381031030460b542c59018034083c1507140100000301d500008441401602980c003901d0840c952031001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683440881 1250 683439631 683439649
    0xc090203160e1c080f0304031d0409020a05090a060b070602091504060e10031407030c0906020c06031f1d0a06240c210c060f11030c0f0f0c0a0b060a1a09 67
    0xd4160140041b0800c000c0c554044494010103d4818417401c24501a40a100035604401d10203504a8040300042201b4103000030491350043e650580003c0c41a26220644151f80c00940107542280d00450b20500ea8503294100c420028580c074403481c03600e441d060000d4440c8034503043e40b500c600142c0b03400148040c007903044042e00815828101280e4549005c026006041119185001444515010552074000241c0450b400401400c41d4111341d240790303035900700c110b211b20410509000d1040c0010074441805c08441010440300722040145084180581220f003242c1c0542d840400030240340040c41c1c050075013035080301058644059207a1f0103040240d40340c1c1302c138a85841c00d2f0b5028800440c05c182e220340e0b580c2c0d4291041c0c1d018000c40d84008084c5081e0307558408036076031050007080856240034280009040c0da0700341e0100c0905140c1007421036100e6810141030014180c200d01040310800045903485a844441103610001450800c800c82d500402085000e1100010005030b105050b83c803d0f41ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683442131 1250 683440881 683440897
    0x504080d031a0a06170c04081b0d0203071217030402060301060e011e020d0207080d2c030115030b0f0106021b030a02131d031c050c070c090203160e1c08 67
    0xb900b428541d13540c000510b0341400c2500c0d00030f80d003030710804560b012142400b110115641e1900609042e01480000c054041410880e5a40107246000315001600e090181000600ca5208600000d500908204c11f0615220f445000f841c41d0030010840182e60744401c0c1d9065030914036001e5841a072034030040e2500d500c264131401c1e148800342c10407003480b5800074140c403404145a0a442d00070380d42e0035002d030f034480c580f1120700041041000f02200e4400060401a0f107a560031a440d4001c054210101c1c2c2101c4010b107103200d40c030151400034000d0100461100d60008100c0d51074224070361421a00948505800c445d40b41c01240390a4080d600b980c0800c00c050b40c243c1c000b003001190380c0703916141e003006100c0352081501d51411980c104080c048040181c5880d404044200c40310442e00070300c60001804002d20004001c001030040001003034111a81030040d041488005030f6074280f040e603d1700d1810b081410a4100030b0340c03001d85440b07500c4044240030f601400d410089601252441c04000900070313045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683443381 1250 683442131 683442139
    0x70e0618120f01200313080703090b030703290a05012319030c090b160c0b03040f0302060a2313121e0806060318070810020c0d0504080d031a 62
    0x10500c6503040660042d00f1000c0644941103980480a2044001740021505896114680d20095000c68030031001401c2c040d20074504403c101d6120000d91101e60800c0d80c0200c002507485800c01c0211411010b130000341103075192100410841440000d9000d5001d004050401c01002045d044071150700d0140d80c0f5003040b4140c20364486103a100c07100f20f4141c210912a00090a00080200c0326000301c580b901980e117a4284286801a140c0c44503003c0c0000c1481204d034241079800015808105002450040f1300c40c1c6042105490541070092030044090003075006280b40c00001b03000340d13804100c4c0c0007051555840500c09680d508211021861780c00201074624122410301c2d5210719449402e02a14401c10003140344080340c080000c448d4200101c81342600b107081000840c800000c1c4405042844c030030302c4211a84103031101040c03428503018440c004c81c0550003140e580e00504d400d106c242041031041ca0700e1400d00b407415042f5135407440703595045000d00d80d4a04031801172912580c2a0b40500c54058 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683444631 1250 683443381 683443393
    0x7081b07152105090303010e04051005150a060302090a06032417010c0c0f030e0d0210030207050114070212180d080307020c030a05210c0106031a070e061812 69
    0x46024010100212411408030b24400c525124007109101e641d01480c140001181540c0c20424564006180035000307480c54030407a48038001d50340c00360090f03900c80c000e0084520102d100540070305ca00c0c5180c40d0040d50500d4010f012a0006440c3c2e03c1010741201c08500e80410788003980c8140450a032014584120703250858400480c009000001141810a10900030410042d01c1603080345c100c1e00003e03000345916084200440424403480342000c164100a0004c400c049041d07000810b010010500000840e4010900e001440020312880141c0304408030010603d140920001751070311100b00003080700c0800406c0003000501009510800c1c02c0010f05003030306080c801d0800a0517900110f45041c0148178100301a90103040104640c0c128641c042e0040000c1c440d48401d808400300c60102d01d8007015400e1000d010095424011000154081c10015103111540803400c81080b500501540c03e0281c1091000c0040d2614411138040303c0340140c0360b43c028144900000c0319820005807012a80c4219 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683445881 1250 683444631 683444669
    0xf0c0f07200127060c06020903150907080c0913081603050d3e160c0905180d0f090512011b09030c05040b06070f11010e040207081b07 59
    0x4409514070582003600c0c0c900300100c03642c881042504040d0b8440038812034601d003c101180c05a0002c42046100d01d001509109441011074644040c02030500c441e88051070900c07841070f13024003900001c1c042d040b014001e004800c1010601c001405002000d0340c0c0c80b11040c2c0030078043c4681c1503030305202c80303004821000030715802c0c001c10130b40100202c11b0b8054501401c04690765426a41804010201600c1c0b1040220701d60055075448207100c040044100100f050880b0b15960061552407180301309885000d50382070613004011550b001f080c43e00b4507002c18040c0d4603044000500e80d40c01c00c00c2403404448110404804071030905040d40065000110380c0300d0741d1120401234100d03001d103022900c111651030305100c50840d0b0b150510b00c0041e01120800c0c200b4061420150000841403078050501442e1280f82e503540014a00d40a1040d5118030600550100301d6a02850004044004171015424402030307441d43d111620424041d5100c9131004400d01c0301035541400108001c01040303004160000175 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683447131 1250 683445881 683445923
    0x140d0b1207030c0b1207030c030e03040f030c0806070203070f020d1205031506040b1602040621060501080604110405040c05060a11011b08010315140114010305060301050f0c0f07 78
    0x1107000c03c072102c050302c803800b0410440e180e00b524030512002911000541711203c0c16001012406d010b00f01309911407800e20382088082006100a011043c003820501d0700c0c504007213510090340e41120119820282c24040e1095000058402042e00a6204482c0308894400a0340a202a49004180056466540d40425007180c061272281c80601c85e040150101c190030801144100d01485c0c040540a00000000141405846883d01c0c8050302c005601511544034a4030003560880e44080300041141e48420003e81d405224010300001000780014105640d03425034841000708102e015590303c07000141403112036401100107150203030806540340010070004040d48541c0c401d6030419805c0c94240d904c1884208007120400204c2d0b602c88950f80d0841d40c808c2d03030038606413011070b541c161a8080c0c05d256159000c6203a0080104202e4101031440410014ac00c0e03c800600d1140300c0d91412040000c0078241800c050744c007c3c100f802e040d9503400c180d2060741a5000d0031502601c1120f40c05610080c03444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683448381 1250 683447131 683447143
    0x31707060612030f0f0f140c1c020d08062407060c080108070f08030730081603050f04020f04140f100b0414040b1302030f01210201140d0b12 62
    0x10090755070711019000074000745d8404100c00240000610361034450203036540b0503222201e00c83c1c680400765141c81c00380b210161404400c440300c100c1d9410340c801900c00054040101082c41d44d00703414000014076080c00000c031046031404034007501d81444a5040b240354101c5007207618941d440041040b48103081e0300000c19001003400b0b5500326204c1ea80010810400c9500040116004400194988500c1e9a992410032480868003020f8410201952410302c130b60140134078512255582e14000b521b0143c4c0e03410b8105485910742c2e02458500024000c0d52090a54031941c02501030310300722401c2c10b070040400c0c018408014220030302c080b50000e0000051098100c640985001006100519202c40c4044420b1080c0d00c14050101e04025403080c00b42410380020344010b00080045001e030b030ba85904c0c002a40d0046600354903142110300180440c0c04001420b4000d8646d041d455001207d05600107030010400f584403c95240c0c0218100c5907404550f0050001c3c1c0c40041d002c030089020861100742d4603c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683449631 1250 683448381 683448383
    0x118020c1905011d0606061602090c251505061c050a060e0c030d03181a0703051605091e03011407141908100906080a0201020c03010b0a031707060612 66
    0x250070000890100203d1a41c113005003603661000d4003540d1204c500704051540b2400414600b000b0340c0c821440560741e142035152140c441c9540140d41c41c050004e480706074031110404201c203503c0142c4207a0100c0e05000d4104178003403400750f0014054441800081030101c8900f48021111880e0741c1040401102044550421740306080038081c0014801c140f584600c600c00c0b02e140c142c2d000d00f08034a25684250000c45808008030010030307100d41c0648940c1c2c80f000180c0009488034000c0403e0002540c0e25218003584000440720080c2d07035604000b8020058407030f500105225050494000e00d030f11245a803901c94103040103008008008810601c03083e440350464000c4c0120792003401c030a55001e822011594551002c20701150507015131901502c180c14041d01d01e404080450030007058280c0382d0b100e0500504540c070018002640148002861700c405034450354003a034100850701103283c0380d54062a055a611280c903e54100351040d0a2016018482c0082e010508050f000103401c1c02c003000194000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683450881 1250 683449631 683449633
    0x1009090b0901050f10090b1303121e11010e0f071802040803030a090f050f0105160504082d03120411030109050703030f09030b15270118020c1905 64
    0x2840c0d50003008281c100902c0b80d1504040441c0700c00da001d260000114884e44a28201003a29a0305c0d10701c40031194200109801840848190900502108184200d88808075142071840c0402c051002c0000a2191700034800303101b9640070342e20680a00b134115403802c1e1048400c48500b4050310036407070380d9070105114500c14290705042e49040c2140c1d60007100c0580748684010f510f55141e07040c42e10300030f1504a0054070303060b0b4a5011080051028000315001e001c4070000442d85061522000049640110b050b0040c040300300004c01054001058103040d10300c5c40e0340c034241d50302c000004040020f8140508080913020002c0c0d1482005140355101e4080c600606084000c56207034024142240c10000001d0040d0780700315001c2000a200d001000021586132030301c2400c8035601e6071102c601038020f54000714000342400c80c1c0c1e1054100340801c0c1c038441c40c01003005a03a14601c142000002c60060107408165211003000054001d4903804480050b2900401c0316994075580091022114580b1021141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683452131 1250 683450881 683450891
    0x31305060a052a070807170d0902030105090c0102060f130b0c0c07050411070219080a0506010302090f060a06080603120c0c030d030213061b02061c060608040c030204050a0605100909 80
    0x43e00944800f642e407440b0000843d841d01c4d0140c1c80c4e60403540c00c1194115120458401442003000c07421004d4081040b03046c0f0041401c0311144105801d41e5001000403032264410944519640c0c0d00244054200401d02800c0c01661205100c5040806034600301130106a055000d01a02c00040002050b07000c03040010380b25031648460400c016a0543c00c0c10701540d2100344409405407504d400c50b080c0c40b07450b0040e80c220f4250344000450030170f607250000350385603000a8010415410800d050b581d014060b007018100b185402c00004080b04102c0c010002049107010004259413020005510078800c02c3d4042d03601c603006001d4203540c0b600000320103402402140da024070054001d00948004000740d0b5007810526081440442d0030b075010013041c40401a68150a07030240e10f85000500c2c18100d8140c10300d032005440142c0809035685075001d0030410580c04200300101da11311207804166039045502154a442d8094410042d100320303040103500c007452452a080c0141c20030444e4080700d001942c2031003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683453237 1106 683452131 683452171
    0x50a0207081b041d1906151226090103110d0e0105010614072f10050903070b030c0d0c020a05070b07060b0d0314031305060a05 56
    0x2001403842c003240c450409002d52540080b042c50310b07044506001540a85d00d45010440ca41d440303c04c90201e504000440d00b2084c1c50350401c81c20802d0080e01e813041e40c43c510503c00c0007164801903107255400750400c050034010281e500d0100b41401c0a0091005401078500328001580910041044001d003848038421000d40c060048000900c660500c40f001d4200198424a03030300c83c44c3c05100720340005000803009845414550245040c4201040040a0540517078241903440702d000e03240ca00743c10b81d1140103051141011401c0700d1006907924401d8291b8441502e8000c40640300300b000884203601604105c400d54010b00c100e5040002e6031f12501c2c10500c154100100b007000004507282400158000c4032182c4808807039406500e0400d50700034080304a90072080c01205400700005491004105103c1191a0070170700765019403600c0c4038520014003044592283c0407454400f151 = true := by decide +kernel

theorem cover : BRFrame.Cov 683273381 683453237 := by
  have h0 := BRFrame.cov_init 683273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683273381 ≤ n) (h2 : n < 683453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
