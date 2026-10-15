-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:48.984309+00:00
-- url     : https://prove2.me/submissions/b8443567-252a-411b-ad48-6c987d1c5428

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 788309352 ≤ n < 788489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 788310602 1250 788309352 788309387
    0xd020a3810080709020f0301090f0914060703060515030601260405010920090a0b13020d0e0c0d080711040608010c0c15091109070203090d1109010f03030f121803 71
    0x40a1351003100c03606034001d90b00c50243c1c503041800107000f0500568007510450007034000120b250402e035100c605521800c095900c20541001d01040b800c10f425000300340085c8002e44108140380c42d940392180e01d900018021604016a900f0b02001c03404140c02d03145440c80c80d403114045541001c4c60f0142c0244164038080f141c0c16210350441c80302d5800904040210000600244a56a900030f04000100440f49826078844104000741000e00041e101600d10b0300400c0c1c400181070062201a5454110b607100024880d0b480e0820010004010300196440c103540050741040602103280000d01610494201c84d803650710b803200c0c000c1c040c0e40c03103c89a440c1c40d0007510490a28941100b824003a034104034009480c9005280003a02e0b5420040d110319031016261050b213081001c3c1e50000b0303e80010000c3c05130b44000150310003420502d402c0c02c03001c0c010407488006018142c55590041e1000000c80021000d21103107968014420109070002d08800901c2c0b50584d81d580120f19024126420320031480b1034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 788311852 1250 788310602 788310613
    0x11205040b01091d0a0219051810091a011812030518041e410108010605011706030a0819020c040b0a03061503120513090b0619050903030d050601020d020a381008 71
    0x152040bc9101c0ca840e0445554154400001104010f6440e402d034981c8841a850410784e0015000c0740d01e00c07144008911950f50195901e2007110600220860000083d1040c0e140048248540040304450031614a00c0c4c07001245800031086040c1d424480b003a07011450840700c0e50510756810981e5412145003a0a1046081e1039032204006401ca9919000f89804526808071b41c078404052500c0b59a07211000a04861052100e40c0d144180791300260356441032400c01c0075030385144070b40500c21412485d200351400c00c42520010001a00c4000a00c40a00707411307a111041450030a00f840d2100285822640e140d000c00c0d203064006006510001650040e07064160012443e049240900400341c07100170010307030800350366442c814407000c208842e8406000e002c03c0066a192410300c0589840804541c0c00031385450501d0019040113200c254240440d005900008009400c070518007420540d102c128180c20007403540d00b103a07008044003042281d03080c00000c200d8a40e000d88210b40548a101e401d455 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 788313102 1250 788311852 788311859
    0x2041809050105070f0f050c030912030a1b030c12020f1b0f03031c050c07060e0106050f041509050a0e01021306020d02120d020702011205040b01091d0a0219051810 72
    0x100c401c2117910342c2c03030002080750b6600710345280b103040941b045e04990b07002d59180020340c01c0000d200e40c0c001810741c0190303000404c10310380194021800c40310590343c1d070b441042511415074005100070b69404004140320310000981054a10801c006040a15000304464016444054060345508000c001e01e204015030140c0382001d00740813095550410407140b580300c1401003c807410300039242c0244072040c840d40074005013001c903500e0b016103280840303000b00010f4024104010b01886280200f1203034012410701d16150303540d020254900084034081140099281c407504c840b50042c6c20420800002c560001c5044a5520100c80c0300400321003441d000c6404d02d405071034042c3d840b5000c1c000c1c00309000c00144070403690702c400c035002410070074414905544100c0324180c000049800030b4074191a0755134000010301003c4820b1180c0347c0c0280c00c5002c013844241c445856555180100d11000f070141101681800303041100304284005001c00414058241d00295410240c101086410201e81c1c0e03103000000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 788314352 1250 788313102 788313107
    0xd11120f070c051005150306010303080912041805070504121a01060f0f031a130f0e1c0e06070611180415031b24120b0d0f060204180905010507 63
    0x103102d4580d222001d0404a5003c8103a00c0c01000020300b0800d06c0c4402c1034800f1a41e64013403105c82d003e984251954181802e00f8042180b4102002c1c180d440c090400b04010700580c242e001e0350181d1409044404222a070740d1100854060049a014031207996400030034000b000038000b90005002100c0030b440034180c1c1d03514030446000000248420200318511203281c0f201d40310344c20049c1540005070715114040728450210700f031419600b02001800d940e81c1e0501e182d516180c05540a20101000180180c0c038951403001c00c5022600000340a200780028030f800d0f5500c9040568043c103421000401200c481d00c90030305156446030200307510a103861601141c0e207142c20310880349140314a985004109003103a84800721650030a03c2903c2d1003499280010380a0101840c00100c40396000301c0d529145020172010349401011000c00404908009001d00981c40303901c81c1c19566904445c08079907503082410513400038451900004003c04141c4038800201c090354021983c4684658000c01003540c0e681001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 788315602 1250 788314352 788314367
    0xf0901062307050d0f030c020d080a0b010905041103060109210f02120a060b180c0f0f0415020a140604020d03031109190305060c041202060d11120f07 66
    0x40c40085801c0650145666040794030341810032408400c402c0c50702c4229152030786002014810301002640c510716a0b503040b41d160080c864030f20010b00050804c181e102c14040d1601c10000e010310800b59407545d83c1e040680c41030987d00c1c0200b001030420081541c0101e60b280e01507000311003043c0030490b9180c0004640740c0410b03c0a021000072906c501241d40b0a0b940c80f0b440c40625041640c2c0444415201c1e0a402c0003170000002c0284a8240090942904000d0082908000840e80350284045003001500e0320408112030003074054140140ea502d070b0300502c480142c043c5400c5540400e0034a1000c103016500081c4d6611094001c24000c00c201d5002c8060690314041128002d40080c0843d00380e900080c0260440c4501c03404690f211814010781401040394a09800d00340403490030700c0441081404014040300d0b0b08a00068106882d10381019060720460401c0c49000f4091b060018100001000d00e9100000c41c0341014089561a81e0301000c83c10003000555509141e214107801241c0d406001d00784 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 788316852 1250 788315602 788315609
    0x705070e01290d050901060e01050f03030403060e12071101030f1b0e0f0429010513030b07090b0a020a02030c0108100905040533071d06030a0f051003020f0901 70
    0x410321070303480c954440c44484000c0918501c0341c0606003e1542e400c0d000307000e6036105960381c8000003500c42c0303800480220200103074421400744031107406800840c0c80c003104440581750091004203146151a418501e000481401074135410700114691041001905030301c0d890304800d03602230040c010040503007000ca50303034414800e88882c4600d420343da28a006844003412800c0c020200280060000c01103819600c1c42000d0841400b803000f001d515110300002c1c403555142081c0782590500400290922125203180406811080c1041c0000c5210740314030700180103020308203411911440c050201035651075a801d0102c3c441c0c00741401055942d481000e40b20b01c100781d03102d120702050346819146001000040d1040d900b9004072900e40d1604400720301860030840c880c41d41d517011710746280031203800c144002d07003076004014000ca003100100f91143c031212103a40003107400d2541c9440d08140040144009132105800b5402e1608125080c0007011001c8100c074001d40710708a0039030001c402c2240001c000d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 788318102 1250 788316852 788316869
    0x60405010c030315080304060c0b0f0603060103080c1c03090b0a1104050f0102031b07050910060c20031c0f020705031b13110403121d09060114030a020705070e01 71
    0x3007007001192103508400303511140d892010840300c0c1c64a41035411a80b0603005540440c18003608101080004403805511800b003c101d8441804c01c100000e44920041c0700182c460a800b1400340d0030325606100d441c00031040d00019000b901ca003c8400750240101d0700007a990119041c0c009140c661407802600d20143c05002186c0c905411700081084080106600343d04610083c04180c44070342500300c001c104c803401e4130000c1c410301c3d2500d0200454084000d080c840110034607502000341c150402055002c0c3e030780c489030402800201d005020019248001603075071511401a42101d400201c1d1202c440d00c0f00190785c0c90100794401117007a6a1001c0500c01d82d03805030b00a00c2d0031504080b5084030400e101500814407041c1440b01b001c0c03d015540b43c0500d49150a000140800030041c800761642c10b038107e02d080101a000c10710003807101c10713181148424029119070000a000341c0c440c0d02c4540c08001e01c00ca03e0f1791030382000d0b0340e020025040124119403a00c105200403822000068505d0f0403641440d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 788319352 1250 788318102 788318117
    0x51f080c0109152012030109060e090d0909022107081914011a041e06090504050c03040b1005030d050c0601140a0b0a0216120510021305150909040305030906010506040501 75
    0x3440e0100d014910360300071009400742c17500c01c410310410303000250b0080031601fa0204002e401e2603090700d0091405854030503150f004940784012150402034900c2100c001c59401a111a00c5082c420004041240c101d0100d1241c0c4080050042c2c102d000399004000c80115050030800d401c042100b02c0d41682c81d50f140286001004000c203103085c14000d5400043e030f442040c1040c0c5d9624402c102c0d80c03c030305038100e41c8500b8070300d040c001c0560003810640200b200311014006403c060f40d80311078601c00039001070700c4020b80c3d0002428582d404684400104000b80031a2a5000d1303a02c0010030a80000c44101281c0c0280000003a800b5000c107910144144020480140d09140200f4080b0541c0720000150a5019815450311200e0f460030029004003c509001d0442d481346283c03ca051080c004442e100076032040c01544206c21000c00008151401640c0d003079040c907040b44018003e030045a08036903012a09004101c00c03d1383c00809140101c145804580e030036620341c400c1107030901031070240b00c4c0046c80c032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 788320602 1250 788319352 788319377
    0x3080f09060714071e050f0d0605010806041a16120603020901081b19050607030c05070311040e0d08070e030f1e060a09030e040221042307030510051f080c010915 71
    0x40c45c050000851f0041800c14001420380d202000e4841c260302144031034111108100900c80144204100c52207a041c03c210240303021510303144040c00d012000d104000e1100d2040e0342128030f40d8010000795030020802c40d095a034a099903030355075000344064058a0384e4902c000f0b00b181454500c0581c04101d94a092903000c0c10f200a020752034000910540802a0400f0150081001030080c1c6000d503008094010078078407070406100c01c1d10340d07403003072a00603074800d50f1030307449155100401039004041d0340b4203401f000d500140001d1900c19104100c0381140a540c2c0394508400b641904800c203452100107581090740d0700d24540c42280c0b000e09000c0e020400a042e90037840c642030380101103071088900030661440e0000c4119000c201c0485040380d82c05280c0805510380755050000d0a501400e080081021034215500c9903280c40090017110b080980b06d10103d00e12440394122003142007078080328015100d0350303404641d559103e00c4040c0c0d07002c0f400100e0045410001074400d01d040c8855521100b10300b094 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 788321852 1250 788320602 788320609
    0x70f020f060f07030512150a06080a14010b1902060712020f07141b03010902061603020c03030a020c09101d0403050d090302070911040e0103080f09060714071e05 71
    0xe51040d0a60720840c100145115401240701034150342c0e019646143d00c412030041c4001c440700f40500030000d158070300d0030604641d5031000221401e550080c40e28002944941d0600c9001c0c2408110341079211050600215402c012070014010010b003110701c1c00145154810260303101d000503078283d400601d001c00c030075065028503001000008141c5c52a985000c20a440d03001e030030f6880400c8120f03590001c0300e60811511500902d0242d4801c02c070300800c50711000340e00007107152040141c00d440e040c40b00f20b60181031500078130100c0c41403c03018041d203644000d01500203440c0e10018038914071504002001c140354241452114096800c640603042410714100d442d101e080308020030403820000c04201c1411250031901443c465a407090b001801c0b0b1505015000066a020541d24800c40700107020400179a0f00c0590510b0441f40c0017207903650b44042e4424084464410b0004064010000051010170441000009000f80b132840f82615607854071170700c5406841c040d003040e420038000045d17400d000030b01c3c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 788323102 1250 788321852 788321869
    0x5090d03142d01030b06041104080307061d060903030f091b04020912102703050307120b06070b0906060a03050705130902040608011508030f0406080603150a0606110102070f02 77
    0x785882c020304030380090009500d424100340c204031110508981404072506042c02954402e082050045040900b460705c060350b0b9014642002c1c026944032240d85881c0c02a104010403846152400d4852600c1c125000399520350065400080a02c0018001100c0490200e03054141070300c41108105141942400c20002e50001070a541c1e011001c480b0380800d85c0010042109079905000700801d960302015504c0703001e001c401c032021010b110729401d890002540902160b9003c1104e08001d02c013003180014a5004059051703619402000014524041c00f0700052514801c44100301180c4c015500c10f02070007035400307088c4001082c0d82d204074014001740c902070017145480c1000680004404030182c00080c16079105a10104840e50744034a5020007100000b18800505144c3c4010361500f0510034405265210301e20519003000b004101003145a501444606400e01c410781c1d848641c0d0400c41d034014000e010f5842507601241103000b13680d0501c1818001e070351081d0b0f0008100241340c541a000d02c041034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 788324352 1250 788323102 788323141
    0x308070204020d0e061006050403020907030e1603030e0f18071211070f1704180b06070b040b060102013b010605060d023a0b011202040905090d0314 65
    0x1d03400780141500144a8841d850301050580c00074400e0742001034028510b4003140d001041081410003051001d6111a651541c10036454a00000c00310041c2066a081c80d4020b4010071810404400c00030038168055603003e000201225104002d2000b4004c212481c211015010403010424000a2045000d6040540c9001a40d0004103283d09106c0c071040e1181e016550441e04003c86002003014004000103103102c080411240c0f0349002d05100f0003141c10740c10f03558080d11542d00d07452a401c0c1c6840e401c064403d1180e003c02d0030750440c207041c981400e428004840850040d03180c1010400715000f1041c02c07004c460040e49045981505200987c50401c1b80c01c242d100c103075901c0d540d0014607030322414010440c40c2a5450010703145d24026000f070f0f010043d0045004850500c8022074203101c410010100c0028089190000318106000300582e084080041000422880840c0004000d03007950408c621078004101a81c0300a184070030180e084403d1419080281800880003038600308510318401c072079 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 788325602 1250 788324352 788324359
    0xb03010b046002101a2b0b04030c1101030519020309012a030b0d0215030405010b30150103031103040f06050d0b01030e1b0609120d020d020d0903080702 67
    0x2030070b641070054002045468000140d10a083e1035810f00068850145613010703001501780034101e0100090502045207803900c0c900700300000303550074054540c14074599050b07100c0e0189900346400d003030103040c035114a5010368a004040c8210615580319101e40c51081e52a65502d680c0009030390040002500001d081c0019036598884402202250014405140d210506800c0c512803d5545c000e00342c44000740804d01803215520a64010313a510b0055804030300f4000030543d00da585504029001d003101404054102541031342c0c450710081d17001c0e00c86030701c813240e0942c6251100b0343c420420b580d13540380016110140c54850041c00068411405025904044411a800d182c0c4035403c500507243c1641c414004101c2c002850f8074070304454001c0001010003428208601400351080940f504180380514180000f03000140089a503810306460410782d000e07207002d0900e504030812079912640d1610380000340c819144002c0d0030f10700c0003441d0075407001259501064180b45580d68201a00501405c80c0e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 788326852 1250 788325602 788325749
    0x1021009061104120c0801090b1924090c05030c250602030c03010f06320705190308010b13060c020105071218050109081504020a0b03010b04 62
    0x14030300a01c03000c1c0c00548400c120a441c100c0441c45c2c00b03281901103a1080310281d040012140119052002c0c1303c1d40000700c800858241102c0700e403101c0040c00c0300940215180410000a4114420441c0d00300565808010411127442d0307001081e6018081141c00801d420300070024526442d40c1101a0005055040406101417101b9038501c0b042ea0011520418045404001081008401040c0c540104604c0c2400c01008404203400705140016050142041c03c594003c5446040141c0071212200d4110301560030311000640180141d10b1088000c1d03000500c084004038651a044044446820b141100003403c9454507809647d1042c5104040e814400c0c1808043d021900e244003840300b503201c680c3e600440c54145050310344070701ea15420050403c181c3c00340904c898130740085c00070440100780ea210100380d0f80e03510000710080d040b908003541c10f43c008400000d01e561044060015545c502a0780d00a4074100c039200c40481a040140d526904580b040001441082c0494042035003d4002c6100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 788328102 1250 788326852 788326871
    0x3040f0206130b0c0d0311032a0a05041e0f031205071a180f070918080a08010e13030f05031003020a1401080a09020d120c05150403030b04050103020102100906 70
    0x108158199000e14410380f000144520303501e106100020324400542400c105000d086a001596400f00034a503080032003c145002e0140300380c0080c1e1140e00c51400489650f18040214001c105810034401c05400c600c441040c0e00344541c080030b41c1d4040e1019000c00461503843c0d510341c04000400c404128051010401c02070000c82c10b8600c0014503c11044058691030400e444600030000100b0855038698004070040d0a002801247d09000c0b2654000701080c007002d03444441c2861280303c00010702d40040043c42ea85256080320b003a07412100242581a05660f418100700208403080da80180013602c900405400c0f03074025001b45401c11401c401e21501d468490b800700b111a80b07150040d1307103031000e942030040b01982d014003411b070301c18030085080c08540b041e640840e02e040180301000f0a18a2255008030100d44241c0300c100c143e6820508407000403090030b0484800718810744040e00024140040103015003814020740b812a981079004042d81c01000020340000c01c00c100d02100d0940d290b840c00d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 788329352 1250 788328102 788328127
    0x1a040e0a021e060f0702122a031f050106080108211804060306060f0504061d040203030f21090f1203190e1005091203011401091203270b03040f0206 65
    0x4044070358101c138041c1c0c0d031040c1c540100f14400200310190000c507880f0b13003040320850745140c0720080b00b03082c82841c0d040116011000603040100d244512001c0f040c0c0c94480502d40c2c900d540101e41240c85544031496140d8a03103612603102c00c002944060084400840003504000c40380c000c0c100c1d0b5034070b200c000f4419680540054180c1b001a0700035160f10303880c0c0e4002d10402090140980040c5021201041074038500a00021590f00003025154004d4441c0001019034801380112180e42113102000c50340d540d800d40002940c2d8084049001100c06140300081c405400056624081411800244051a40f070854604154801046120845200054040303c01240d002d00315480b0751140151a141c2d105540c3e40e011510b00601c0340049500400e15000b4502e0343c40c0840f410758030b41d400c08450f00c4600c24016520b02880b82c2c0f003d881c90400281c28014161f204d2071548a2640c40000c4980f403170b8180700e00510241a03800384081341c0504101080004005440881c00b403440034040500f0820b882008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 788330602 1250 788329352 788329357
    0x180904060504060513030905040b0d1703070915021c090503070e0f0615030c0f040f0e071e0207050f0406090c0f020705040c0806040e150a1a040e0a021e06 68
    0x403541240c6940a000c00c00165009075a0301800d0754103481000f041c0c40d1402000c1408502c038981c0240e544078a185002e131030740c40074a10312580050300ca0000c525032071106001c96000302c0d01003000580608010032010110000e4044110052b230080c81940d1f141c0522402c0b017650007142e0b0041c0601d01400140703d0f241800b1180042845912000e4103140c003011006003410020b06241c80b40d08501d1140b140001050142d0b90051804240d0549030003400e1002210783c883c54111031281440e0b0b02d4006004010b0b64a15845604166100385010f040583c441703a01c003142d0940400540c0100405100e00d0900310030405415100800104096a8403000740c001c40c0c1d480745400c000160004200400660104000001080240c90030007203600144401000c0d442c1c0640f100d4404c0792100c820100058041041500003265601501000d04144d0070b40c2000340200008030009038114000c00d130880c0ba081c4611a400301c054006400304160b542c1c03c00c959442519614415006081c3d030380c203255110f0304003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 788331852 1250 788330602 788330611
    0x2205210c03010f02070b0c070f1410180201020d1404140f040c030e0d020304080d03180501060e06120604080d0c020f070e0406050a020c120d060812040f060f050306061809 75
    0x500694509540c2468601510b0047c80c11610140c200001c0d000a0b20740c1002011207a00800c001407000d50003d0440e042202d44070205403d0342c2444170300201c240d0060b48403502c15200340c08451440c94504410303150211214441400e00406000800441ca101c000310303180034500426600c1c0c841c1808000038210749190121000103562861040340b80f4000f01302d0200d5104043c00118180703803a100c4403c0d0b03180d01d5074210300b041640700c19601c0d2402c0580600fa001807503220000348600c60701c68501485401d01150303564070429a408940088100124455001e1900700071681e14000419018501800c03c41074510114403c98450030140d10040c4203002c0688102001c04207503040a051200a4600191485020794030411402c0910b490004454002c0500c3c04002070312070420100c1030005204503841542d490241c80c4188003140c600b00e00501c01d0f01c01c0c6060380710030302d500c545013160f205072101c1070300c80461000c01c0800d54a01d000000391002203000303941c054112620802003455140c0586 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 788333102 1250 788331852 788331881
    0x405040f02090319050a12051902010e0c012a1e0c0320032104151e0c02130e030415020307140c1003050a0e0d052205210c0301 56
    0xc00c00030510b018051040c00840e00035a806881036107491719612007948080003000d07044003410000216004105442071138000ca00359030031007072030200040d020303240384400501d050007011411010b0b50300800580c0c0034003203210080b003584d40c803600600a800900d001d05070394140b200110391488c1c040404505105038803501801175690301c1d40c40c1580600d030150714180801100b0b10409042502c0008261881e08015814034030307075040f02d0402111506ca590843d030040d9100c9180b40c010700d50408800c100080e1040e50305200c240320b03201d040311100c21900c2c000754800d44001468403142c0e403d4010000110310001a40d10b020354501007601605541080b440143c0c0021440c10103010505414108102d11000a003201041c40b10014030440b0405404905159541001c2113000040e43e10204800c2c44143c11220152040038000d003060700411203820b41191108180c00882e841e54120504640c0302a1407001c04401008039165807021410140e0294811014000040e54007406544407840150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 788334352 1250 788333102 788333107
    0x50303040b12010609151d030d030e0c100504180f090f11032e0f050405210901080a24031b0801020408120c15010e0712051018020405040f02 62
    0x101010560b81d405a01020078081c1c405810407845c3c002c480c4070603858a0600e13107034068040c40304c0c140c0440d0504052054040c4a4134400800f195011f6000c01c10f00c60b11071044414044c100170070000c25511580b0508000380c0c0501082205024118040b10001000e40f0081485241001a0b1007100c14032a001d40d803031040ea080000501c0030311701c01080a020f064000d020740c0b06ca142848180e100f03c890038251003001e22003508049002541c80035200d0038541e8010b01c4103040030304295035601d1020348101002d0f00d19090b50130b403141506088540021060b16900394640c1c400454200502c0c00308514502c11980e802c800029890b442c04400207513100d04680794007801e01071030440039039500c1e40208009030302c100001d0040040010784924801c0c401c18910b5a00e4014020940c20250340110102d8160305280010441b84440382c245407150050b40c0da00e100c0d11801a04540130760b003064405807040e8042d400300f8045482440c06d800d250001c81800540b03001c0d070701d074041402c41300d22104010307076560702 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 788335602 1250 788334352 788334367
    0x1103030c040e13110f0d050f0312060d0f0b0c0d050f07030c09030209012c070f032901030f0e030706020909011a1204020112020a080610050a02030403030503060a050303040b 76
    0xc241e03043d0030086038544024101031a6072030107510391000302124402c1801c501000095599003400031085a408002d8a0b1040c000c661010341da900a90000c0828100030000030b840d6003404000e003003610b82c1200d008000c44501d92075052203003070041c0c00c1c80042c83e000c028020b00122640035040c09046151509070051400301d80080865414407500030800900a0301000035a170388410f040d041d602103042504d144045074580c1c00c0c06d1102400806c0040c03100c003041203440c3c0c0e00104402c64106840d1405e0222040c0400100355900806000c11803241110900c1c0c00c095210754801464103000740e10000340510810900e03883c54020718070482c1c105030001070a103003d0400001e01340c010452010b00840780c0c010101120160b02590344101801900480018156071154074403025000c0082000c554880c071020000701480011070303005000d02c1c0b06c0003081a20781d100b5412520001090350146041504542c1d007168181e04c0a01079903446900c128002ca590380c3d003031009000a01c00303000820342e00d410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 788336852 1250 788335602 788335619
    0x509151318081207020f01020c030a08090705040e100f02090a06180302091006031401061e02010605090403090e1506092e0302040617070c06020c011d0615090402031005071103030c04 80
    0x300031b40341d41c984e40184641031200f000002078980c07001007801c22524a5882e08503051906650307070f001d681d0141c280400030f0500c40000ca400084002d50500034000c0016058003041a40700d4115040c0c0c00c0182e404003042050302c94102d2440c8a003484013212480b5a40341c0000b0b07458182a59aa04601c00300318080203160741601c100c40c0203240e03000c0061041e40c5844009002540254030040800b1400e0205941c050b10030760248001d800c0040480016003000c0c09c008003000380c0c1d030181e9584009640c002c6415251508003484864034001d00b00e0703151148000c20700c034480d1481c0d004201061244122520000b841161040981d070072503a005842c0d615048000303000034440d10040040c01c403104240211140e100401c00841034000c2c001590340d81400041500415100603103080e00e500c2b112401c4628140411203500809880408140140340c0004004201c28141c400075810b620103803e580d1030500c6a004a81d00250504141c2c4c4403c1c4002c0741c182c1036601c112000c1a52400014061040d0032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 788338102 1250 788336852 788336863
    0x30b090a0b0f0d200105070b01090204060f020604053004080a0303061532031006030b06040f09051b1803151608100b0d0501050915131808120702 64
    0x10000c42e42e00d600883d540d10fa28404070403560100144115468003403034181d006a04503031001c0e62008001082c0d6940c4c1008200a40250090100046600032541d90080c8001140b9000e29040b101529011565075070040c0302c0d26030041f090030f100d10300f082914001b00400000d0401040d07000e020f050421030925000301103a011b6004800800c001d60402d100d455440034508101414402049081d5040e0241c41d818031800c1c5040701307004800000c100840440b00c414a6030468940b602c060001c64408c1c402c010040c0513600520001001c80c001c10804052650082600329035405c2c07240c0014841071121455036031081100001443c20198a00b14a04041040e03140442008204c82903504014120401102d18000c1c404100090540441c01014003114103100500d820992242d0303505100750200003074102445141d00c591161000500b10f41e035869600621040300a000c1949403807884260b20007480a134044a18058601c1c440d4000100614005c1c0303c6480c072541082038504d0310480091621 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 788339352 1250 788338102 788338129
    0x3010e010506070302060c0c03070b0423030a0c080f0c161805040b070f1806020706030e012f0f03040b040b070216150203161a250c03030b090a0b 64
    0x20b241c00c021000c0425030128106401420844281c2c1d503c207007207100d072881c5014410b400b5018050207000e000410148080341d500b031030399200100f4054a41c00030401d889020304401d010100b8414024a00040e030410000c209904151804070709115403c0301d4103140003003844103031000c01d043e80420303c518601103020202c0c112003000701380070918007071f60313808403500000c3d100e8400d2010072200454041e005002e4007200c09464041041d07095502d48000b550368609110706001b0900c1c0594048074050306019154010340700301404000301c030380c03540d088031408500210f40c91105801d0240d40e0034441d02d000194069802010040381c0c070708080c100b2036035214015000c8020740d40a00810700c44940b4102034401202d01d407840096008400a609a04510848082003040078010500108200084109844840d0140350890180c2d0352655621400c161110f0800c0c0d04602e49000720400900c00d1035903c600303d200c5c0c034020a00c42086e001040c0400344c29501140071989400d00c22090f03080407002420103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 788340602 1250 788339352 788339359
    0x30708062e030c03170c011e0b01021516021e0304210f02090601030b280602071a0a030603020d03090513090206180103150609080c09011d07031e0203010e0105 70
    0x60303840d583d0b07001c000c400c0900c402401001d4000301c0d0f41c200c204d0001a0b40204908034020711507540c0b18000034001340f03c0c010300900d45500c0e00b03c400e00075520000700244130b03c21103042002d041e1502c00d500b15100d44081e04074811403040c50b10071150242d144031601e0303024030380f0002583c842d42404004403140d20b030300614844130759400b07008001143c644410300c9695501500d0340ba02d0ba880d240012005010303429141038100303201441c540c1c8460701e10444441d0b0b07030741d01240003a020f82d252102244c031507010b0f10604400505103c69820072402c1070000b8010954a403c000a40b2580ea0707010070304c00c451a03c0160041400990104902d081c508204c10405000600230040b400c0a036002440b240108620b00c888640b0361101039155034020751100c10313200d11596118844982e41c55000700948040e00403140036024103400310b4401d04010f00c20314180d4400c0e5602a0120400c20100440300d04001e0068040541310342160012144600c03d0990288900705c002d6620740c10700c0c13a0442c2421041c0c0c4290300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 788341852 1250 788340602 788340691
    0x307150b100c020301022b05100302030318011704080a0906050f0406120b0612091014040f0201121a040e0a11130207020411090102010506121b03070806 67
    0x8207952507401c462040c014605006000341c5550000c280203018450345984400e41c03192207050041c1700c00c85107400e001c0100505102607905e10500d290520081d200094055006111400540c0100007049207150301c10314214480303e11010b0139240d100810b40701960303e450300107441c1070b58540c0940580040d00d101d00b005032800c0c0d40000001c01c01d205a20501d42048070032100b507086040750390050640382c04010402515400980f1142101c49400d903a1082d0b20300c9014490140c403149400380805020008042510340e95403915141880720855108a040108d13a42901c00b0160712403141c5960248280c515010074426a001c0c0011100c014440e0120f5500809401000500c8000400e010000a03500030031060350700081080a030080d0070b0000d501c00d0611501089045581014100d6400300b40d00a00007910307404117021640b20448207150b55034000500340480b5a001811103800200080c040720001a640c068007801d04070207480c1d1780e8a5a6040c0c45968090810081e40c44130525004006d01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 788343102 1250 788341852 788341871
    0x1b1e0102030f1c020403060e06010e0103020a0504091e1b0806060607062703030b0a06110d0302091318021009060909051509070309030908070b09040b03030c0d02030715 74
    0x39035900903042e02c140301540c0011034403401c003010f00d072442000746040d90a42d1559100d01d480070290032141221000c40c80ba002c00014a8050300c54034604076500600b07407020850400040c000500700c2e54a040d902507105010007144080000c0078410302a0003000c403110900079000e405014000641e0101c1100d82c001c41c1030100950710131080b250b50543c0500c0014131070507000b000c10b81824030880c00c0102a05900314080038160584c000a20b07407801183d4070201c007078403160140c95850080e04186000e902803d038044689000798001c4c0130f09a001480b00c10070769184044101079a40302c040c4141d0003030042c0c26100c21414141042c1a00956034205600e000c1e040107001000510741344607185155888201041030502032401490041801a01c529075500d44140c01401500070404200c2c0050b604410001d20000c02090503404d488008284034680000c54080001408051011681c90b000400c42804200d50070051030744d050320769401451302c6403418184182c0100c45403112400c201c0c14140b402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 788344352 1250 788343102 788343107
    0x330a1b150f1109040e0a140a03080609070203180102121b0706080618040c0e0408090109060e0d0b060a120f05010b0418140124180902101b051b1e01 65
    0x41d503140000307480010f5059017000e419403500c94104006002404001d607030b05004a404600c10b20414026160448551140014030908500c21110140103030030030701c1316079003202045280f0604010144100d40c038044028010600341d9210030042101124280109040c02a082c88000b004001c1d03424104101c0c17a002d07002c10484142e442d6804152100d04000404100e800f0385c1113009407a84126041c284d20b0700e490f2200345580010301035401b054078050001043d611610195803429405804190003135525503610061180180055600000c0c0c2d110102d01c0041a500707801d440ca009600000403184241401402c45980304a80d90060f410084e01c012501e01c00481c0180455010035001c0c2c00300b45000c40c1d80c5c018849242c026214003405004080c140315002c943c602a100c080c021911007050707881002046841c040e10082d00040c81c0c10030901e865001315685080071f001d04030b03000aa041203640d03c0d4100301e03400044030140218142184141e080c4104190001988038648580c08155240007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 788345602 1250 788344352 788344357
    0xc0609090121051c08060d0c1e051009051512011202040e0d020d0f0207031a04050703080301031514040f02100c021c02330a1b150f11 59
    0x2c0b2420120901c0d500c403080c9000c49062040c040d007000544000e0a03046801800c040f40e8103a5400000b083d12020071601e1519840703d842d655440320b1407485152411049410035200e107039460450700c0c40c007000050305488070802d59010788242d40c3d400303405904000c200050380c120301542110141013130124a44520100040e141580c5081c2d406a800c0781c40c61000a018080e90004a009400f40c030101d4100c00b600000d800d0707140c000d20b450300318600b201d5101c05c07662030359144005052120640c0540300b0b17601050345010740040c010016101e4942d1251605403d9906c00e9000300c0d813601202980702400c1c00c55128a51000c464801d030600141040e480d05041c0c1c84800e0406445429203d0364030180d2070003825a00070265020300280d407480088003035030018088480c42079001c0c40a1005050080a206109041448248800c1c01410002192034615504030801113424004555110324802c102c2e10b10184000344200c1515a4081c01c0d0300d007205c15103c81d82d0000324140d042c0400e000142456206 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 788346852 1250 788345602 788345609
    0x60e0d0504141c0f0215071e0206040b030c03060a230114130e010801050a090c06080901090c09200301140108090a02120607180501080703150f170c06090901 69
    0x30184812450310001a105001c00f032001018290204614081007108542c8008003030084074490300c180d2012a56480c14800c0c440010070781c0c420b140d0000e1000858082440d142800a000b00b03040079168103031070005600a540f504055003002c4200420f51403e41c0c40807000c7e080d207000c411030440c40c00880d0540311321013912941c180001c07041038030b00a482e81d01c1a996000515a0f0010300700e40d80c1c044080100b0400c1c00b900e54103500b4400080c41c030040d18058500c0c06580f00c901500d0562529100301c58007400907044032219500d40e01c0a50104500402000c0a4a0308080025407615401d81c01d42c0c0780f070701d80c0580c050102420b0004001000480d110a118844282004421980c17110745180c280303241140e0096014401d000640000b000c0000e0440c4242040d48402c5824035172407a19400540b0980308050004181c61700142c01140300703800440340c1d0701c40801141c40b0262219000c3d9040c032800d0b0844041c000e01000c2d42581910108030301d040400c0180e50360b07444c0044480101c1c0d00040c0501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 788348102 1250 788346852 788346869
    0x712020a21022a0109091407081e040c0e06040501030c051908190b0a020f0301090902040b280b13060c03120203010902040509160215070c1e060e0d0504 67
    0x54801106000b400f94102e0b090714080040301241009003207040b403400003280140003c1d00c5810110b1400c000d880b500c02d000480206038001ca544102e000c464090300148110580c540344072160016160707100c0080c1c0214440da0f0380401107403c000030344080140c0141524403e5080c4401000421034020549041e1401070700e90080320080244075044420041d0300144a80c0304a40b008400040090308401d485441107442c2c958548900d02d41805034041c02c0212f4280c1c02082004000132590340d481200c04500c054004101d8a1a2a000a07040101d84540010240d4680e1000e039003a09209100b8016190b440410743c2800c441007071841c03181030035009440600c29883c007010103040c081c410900802c420458107654945c2c6030000e41c9d0281d0842e21030070b80078030010707404074541c041e1008605441841503402890300301e14604110b8955407019202d4014000d2252910000c14600b100211803e0002101c20a42000c030b80b810030b0444041c105409201c6d044240c007800d0a41d441030032a000c0b01c1104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 788349352 1250 788348102 788348153
    0x315010504200711010807170a020d110c07050f030a050c060a020a0b090f0706030203070516080c07140306010f320a03050a020102010507050a0c0b0406110a050712020a 74
    0x500004000c0d080e164082d1009980108403a020000401c4030385802c044284e95135055925021000d1f154240f042d88865446842480012003501c01c6502811000300804030114041000440601d131a5200e071401d00c03200e41228405101c10f0908103040f801107041038008000a2041c4e440305c90312100b850004c1c030f02c40c44001480a01c001d10030003104500035080b01d0804030508249125039926071f1ba00c501f45149018651002500c1c8d030003032090f80e20800550300d40501c0d000f00c09590801008050380215140e038001e001e000380904c81002110041d20380071064695065081081504e441d00c140e0246c0c0300c522092030140075155400f45403003200080314622044c409040d980000c01c06403000043ea801030103000d00081480000990340031140d000b80c000f04200d48074110b04640e035204445c3c008021071384641d00f02000031301d08480d0680c018014000054640c0c3d8604003034000341e200301e82c1c3d00c3c0042c001091000620400c0c4c03104a0641569000611050700166989854564070404c0c090010114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 788350602 1250 788349352 788349371
    0xe0c07030302031e1312181712130501030506030a080405090705040911070b0708011a0702010311130305070e01150309060b0310021b120915070b0103120e0315010504 73
    0x80892984c1c80d600030980b028074a1a06101c2d060304014650000c1d1803100d200d0003042e81c0c080c09038804c01c4110904210076076115003081610051008810120b000380e100381000b2010349540440038001c00c40c11742505054080c68100014240c40380681024480d4000c00740480005001c8021607049510584400c174150340c40310401c1e9118003440d401080d5080c01c01c990303c181421448001c1c000303d4425000301050b5207030f00030129007064090051070803030300c03902408501c00701c27054001d004000d00c149000301c1d4004601d0b203901100d030805502c0c43c02ca40b00c1c00c0300a0040100c02e0185201034140100380640c2e80d0f1525025615001e076a0250105046c2d48100c41400d100260701300410518011b01100d03212048202e402c40258450001c1040c0900180700003010640007041307860004503004a07450811079180c007004088000302900c040c0c0c072041000882e0020b034070102181e00039405402021010b22004401070002c00c02c00d68410710941100d00b08a602e0014409800d056440c1034034000b40301e004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 788351852 1250 788350602 788350621
    0xa03020409030918020702040f0b0102060c1b070f1517130204020f2206020a0b040624090c081506070b0702071701020306120601030203030403080a0504050a060309030206010e0c0703030203 83
    0x40343c1d0000700c200e07404004400450504c5070020060188241c0f0204200d40c20307600d00742d040352680042140180c00c2600804d4000c10050040e104031031089441c0c403960f119000000e0300d010200d40c844440001402c0d010005081c854001c0c400d180704070300300714a000e2380c180141c0c0d1828100600000b040b02d4002010019074441d6415500c2c4e22002c0c90000f5529000800c820140d035610450320341c0308030408200440c99900c04200c101d1501e80c040380c080c44540f11907403080058140303080d0704d10300b080701810b160811225200c4400d004110780320b40006d02a22244005240c04c000525841b04003014550411a507200e000449603607903040030680103d070b12082d80c01c0341081e5542d481100903841d01e80b00340b10740c0c0d5810350045008107030843e40b4050000c045e005598844009100180d419001807000700081446e100c02015651814a08180b800c1d88410000c0c1c18014942c1010700025611010072042540400080d809130025280d50142840c00c100300d280c20348a000e20042c2016000700100c1c070101e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 788353102 1250 788351852 788351867
    0x60a020c100e06150a051e030109121106011d0402010e03011b031406100e010813240b0a0f0b0a03140a0e060112082a0703030810050a050a0302040903 66
    0x928000038440206a0090b881d6a030341c098840310324800c0c03040f141541030b1030035445260460b0340207440844915603040300300c0c1c4e814500080c41901552a40c80800000300c02c0b1140c001601d106845240001d03c0d54003950b0300d4500141c200210501c401400510004013642007a94001d034246401d02c118818a000700c0e000d465a040da06042070302c004107001286816420114070040c5202d00c0c050503541d15020452013660711603030300f0045035802d081030619510440d0031039403140c803286c40c2c40301138103055440c07144250508100080007624021103003141c00d494002c1121800b001c403101079110b801d151025400e001c4c00d1151404201001951341c040034000c1e0054941c041603100d0050080c58a0404c031009050ba5015100c03a6025200000c200c074884202c1d101d91700d07a042081d42c0d051003002d9010100c1c034001e8034980c2c070f001c40324020790750041e01040020130080c5200b540c1e492210b01344020070702d04d801c005810941c80740c00a644240159250801580c0842ea01201e01042e40d00d05400c0942c0c03442d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 788354352 1250 788353102 788353123
    0x6060a1808010e010f061a1308070806060f1e091803070f1b0b0403020904111905010e060403200114070803060a09021c050a0b120604051905060a020c 66
    0xc08a05002444500c1036100c0385003610418003c0c02007000c101503440032910280242400515040554050502c007000a4071980d000001d8184040307485d60030032494400c09a111612541c0b09208201d0079003050f00d11385204213000e550640c02007811030065000d4452140c00180103a0482000582000310a41d440c482c0c58256010b40380d6030300c61400e0281c00c0c412411382c00c1d684410101d03100c800100d46841c600080318039440c0c815040605682c20014041d170098800e5804951006501d0500c2c0d40c0c0050409080c00d1700c29280c944e0038038100000d0500840d43c400c1c030b03200c0e560611040010402080182c40070f4150b040c0c40c105622800301c016620100d01c175508108035600400e00d403080000441c011030081c0340454104005941e1050950103902ca031060019080e081020521202c510b9500312a4000300401c5000c04c1008400011411607071f101c41c08155240e00c0362003848244403090020345088038440d01009250301c02a05c4050759104080c002c000b029900044601c0c1d21a010320010200707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 788355602 1250 788354352 788354387
    0x204150605030a06061704121e05031008010b0117100f0e01060201050c07120c0f150606090504020f03010623040603022505071a0702030604030c0b0703020c0606060a 73
    0x11503110349005003203400446060400f180b6090010a00b41d0040c03003120518502d10125030903503502c1d03949080b5200d40640341c1e1b6044c0404034010b1055080801e00805401c1c00d26a105a164600707907518901802041c0d00400590745480341c042c4203030340c2c8458045609400030381d804d8281d40f0346800031041511240d020344000c0c0e5a0343d1000c0364211840540c0c6048030010344c002e02460b1148041004544607900005007401d4072180c010030b81c1401126080c502601450300341c0310202498440e40117201c0d85107000048142d44110500c1182d4100c0c11203000b5040981c1c04509007030540c0d15420041c801030042600707104070170030a120150782d908611000000003d480e81d45455985401501032b4201c4018440c5c00c2c880d0540c4c0030342050342501d240b58002d400c0401855034600e001800503100e01c42030401400342d10f0802c0390101607181008807501480c460381d60203030000700c10b00b801d80d410200540f0603401c15004000e9a031780300c08c1c0081c085070440741c22507501c1d90b180043d00c002e0b0369289800540414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 788356852 1250 788355602 788355641
    0xb03190b130c230a060201060609060c0302030c0106090e0d0c08040506030606041d15060909070324030b04030f1d04050c0705010507091422180b0903040617060d0f0204 74
    0x502d803c1c0b040700c444481c1c400b6502c410f0102d40f602003c0c0e084c2c620038014680003070440b19080011300d114148985149000c1d0040c0c91409101c041000d09440302030b0040e4808548a5110348144101000f801e000038250f0301d400504458690785110310791245124081c4641e101001144460340d94008680040880c001c0c50303a03e40c100d01a60341070b40340f4219900c17000e0054541103103949080c03201c229880d12070021715010050382c4a4005070010183c611006c281c41c5004000940e41c515007008100c06140545103079000b500d050300c0c00a00183c5942d034000c0c10402c0030313074240201c030507541c1814503580e400303c034046203a49d908001100540901c0708003800c0756007420144034041d50030a42020544003542130503a00c28076100c043c030215500d4504031703845012006802410246059108108428010703c200410740c51503118100018400e5555a106400000f010000250000b422048550880c002c180b41450644d0000e41e0f108280e120160900d032004071a5021940c45500c11850354052801c8800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 788358102 1250 788356852 788356889
    0x3011b120f0605130f061701090c080106050d06020702060909040614060f0d170c0d0513060216030221030c10050603030c120d09060f0b03190b130c 65
    0x14060394500500084035440c04800041c850640c2c0245020350b600a08884000b5a8a01d01c0d0002082099a600481684e07810042042075172186040092400e0100100e80d15100c0c2c208265038140c2c903030008240361315000382000300c0d440303598150704900c0d0440e1005882d01e005001082e8a44100907050fa4014540c004002c1048459440b0a0310000c90901d01d02c603d0355203405100d40c00010020099000c4114a11100010785c0f42040102440079016620b051038a1420000c0c074201c0303400b140501042020074003070109130001c032070040201024030003481000c004208040041c1c049000c040d01940075024541001403014035001c0b521107580c0c0850356030340c030b92210083c0c0742e88a580041c00c0c003034100f0012030202e1500000351892000c08074094501c24071a41804903440d40a100088481521030300040081803940c0b040d407030040791280c00840c885012400b01400d0035044420850801c86520095011440c00c1e024240e01601e01c580c05003d205460400d4602c940c1d0503405000c08400b4040500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 788359352 1250 788358102 788358107
    0x304060906030f0605011b0c12060902180403050409052d0a060f030206030604240807050f040507120216080301140414040512090f040e07030302063303011b 69
    0x590454546075003c020a150342120700b42500c0040c03054a0018001500c555164840e06c101101001d01c80c07112210300719500c1103008101140d031942600c2c51513580c0d115000f50300307001c8283d010700c021082c40a26a450720f940d000d85640120300032400f2072642c840001d442010000101710890051007070840e1030110200d071103034481104445415005007040000074000350504a402d0a0b00e138010702081c15070390b0781c2c41030100a104400300605d4100d403000f19214003080690040014109c2e40c00a840c0550811051000140100c06107a016031710304000c1100e010f51090b5040b1200b00100009a81c462211440288a0a84c0c050280418070700000000e07281c0560f881106401c10169000e024404803070502489440302205d0140c0580c000d40c10680c42e0320443d030001c0103210002401d00c150700950502107000c5602030901e0070000c1c1d02804e414401c0c0b41d010028290b1226281c10055131142440340000d14040c0031080910303100b1004808580140c0d02034010812090503a1091050300003500e100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788360602 1250 788359352 788359367
    0x609140a05070504020403110f04060f15020c0d030507240608010e010e03041505030606070b010b0705011a0f1314090a12090b03010b030613050108240103031b0305040503030406 78
    0x22501c5100e00500028641018002c2d101220340180742c502d1040350510034020f0007068580041d600ca603a800c800300714541180d840c00040c100120038083c1041d45000c01174903048000400d2882240003032081000254480119042c0f554003004001151400ca80c441a02003100600b6095aa081c06008a03c2520551018203401404002444441401c2e18130ba82c980c0b04034014100070403007c1c04031414043c0118001c0d178011a0141c03e881c60b000d040e0b100c00f86006403e811218004100103580c3c0140002401007046800e0004105030408408100046e841c100d0350b0f40c070f140503007160411072451500540c000c0540080001d503820b5546444843c8c0c5803923484620080300e802218100d41b01e4503a101d0840d006c02c0d1160382651500d07590800d4110080e641006040d40e900820b01c41e040a0304110b41d002e5140207185003001880004511440910400e0350808540005c540082c010400f00ea44001d4003c042c65404a0303091029842d810110781c0e501c00e980005400d40300014000443c1c5502205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788361852 1250 788360602 788360623
    0x10e060702240c07031d030a11042004182901140c07060c050a0203100506011403090d1b2001110c150a0e04050a0510052704060914 58
    0x6221204280c011100e4103040c0e00740c0f5110041c841c24030074040001e0050a80c01c505400285000350404c1c51040081d11308030081000303d810700510003812940d0308084c0242c0901000c866201c240700303c40c0700c0307a001581c0114410158030702c41524901c0d1821103541c1c852039940c4100402c8246500b40140b09049181c50702502a00046a15004d41c04100d4407406071481600850050240e041c5080c204403000a1082d4003542c250146600c01001030f541080244130340d1081c0e0f9400305946c60b0071000035241a168640c0c18400c8581001000088207000c10303001780280240c1031803a1b0542c100306440401d5045108010110290000740f211007a154000b81d41c3d00100907038500e510602c0c2003044540358000a006030750440080da80259040d8600005800200890320f0900248072581c030002d0207861003654100902d545e1401808022940158200f024003400e50340d0014481c07480300b4014154030245012400c441a24001c0f504200e5a901301403000394000b0440ba80e81d08889103c243c44882000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788363102 1250 788361852 788361883
    0x16060204030b10120c06080429060109090204030206070f0c05090c0d050c1204240c030207140109080a08040510050f0708060312123d0b0301050a140102010e060702 72
    0x80d0b000904060701221841130030780c09001c4441051801100b03641c840d40207041140e260201085c059900c1072041c0818600180780908030007642014400908101800d422001005004004c1400580c60710012928165407161f40d05000382c0149c00c01d4541d504190304002d610800134410700031481c8500e030160800103086401008180c503840d01c03130b420a04c1550235444901c800c00c40000d001c9020070812401041c907034013034014400c0003800c861084031410090840400d5003c6100c0040c0300d65100d403031035107902d060f0007009098844d0300d410205010318100b410800c82e50310000b07402c01000344683c1038080e03010803060081d418820207030001d1040c2200c1a00004c0c504000103a03a600c2c0009a41070070000940c1d002707282c40f8400d03035030b07802d000401040300c40c403126960a040c0341485000c240043d00d090240c28a459070101c0030007654124410303809026003120500040c400c6586031b6055608981064050241c0c9000b02d000503400b41030481b4200b00c40e40280c05c2000040c0d0780228841c42d2466490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788364352 1250 788363102 788363131
    0xa0c0602010b180a050718120309290708090d0303061415030c07030c0f03050309120306030706030228050d06080106030b0406052205150a09110616060204030b 70
    0x40081c02080501c0030104180c00c449035000c0345000b2569801176804c03207207919103a50381c504070707a0a04401e061903070300c0f46034210302c40c01608040c50341c480c010358050b040070280111003140707504070118800803080ca55501180300044c1c4034100000c1c10200e404130760010b00b0303900034807a01e810050020308080c410805c0b01d0001781c20180041c41d144011f00480c000092040e41192103080c50b00305580c00901c411014426070b5400d80001c43c010200380c1201511039941c856403131030408419401e08402d01c1d2001c5080d9400d1040c80003c0d41e005c0740c92000d45200c2c1c0380058035a0301c1840d460951225140a64002d051030034200c1c005550300900030a200b10300081c050101c15500d41c06c940c222070785880301810569800340890000b0782d075030300401e40100c4028150030400032202e11202e606841030034111282c4c1d2241044041c441401010f031503010001e80c0f0200600070264403510500828000b405108120001c2c1c002800c0040c10008103045030094001c545868692070074030740c82c0d50191090326282051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788365602 1250 788364352 788364371
    0x1c1817011b02010e0d0f140c0d1b030f08270604020a060215040602070c0b1603031a090703150b040303120e01020a2012030c03040b07090510200a0c060201 68
    0x140108542001040c2c010900c02c2403c1d0000c8414500e0001054104100a118144801c1c0c0c00340103030010701614809409c00c1d03070340f802c0040c190b541100b242000c802e018619040202341c00c0460841c1c102c1c0142001001d80e690300560341d141c00100e0f44518440a918503c44071081c000250b00c5129a20940301a0b00c66500d0703c0d01070760703a1048072a20040e444c2d909000100040c0540c1c001d043c5543c4240307039907414035440f902040c0703080e0403808910740d80c110038400d14000d241d070501405c160800c5414501c1840c800c4e240c0400c42110004080300d0506488101d4045075410310303203280d001410001065506c45d42c03a440c00900ca28003014101310242e06000c4440c94504040c803c58082003140d44600c0e10011006480c05041e0183e0501440c050050402a90400c1c15020056201d05600006241c1c1d9103401d2400c64002400504810100b2030001e0050103951140d002421404ca06030034484003103240710716100002001035149690700c1c083d030740c0d44030200000d0041c2e00e400d5a000750020f100340c1c2507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788366852 1250 788365602 788365607
    0x2316020307051e300303040606140a0e1306060602030409200405010f020c13050f0a0902151303050a03180608070504090929060f031c1817011b 63
    0x1d9107218a2008510070030854110301e880501c8840ea03113407100342103860408900300302d01041d159801031055078200004110802c801ca1240c6005000c44665081c210308150002c1543c410880c000c1003014840308010800d180000c0720386110300e9a002e24144241601e03520000e490341c005124526000d030401c42040c04503881040c06c0311006100313a044a040c80d14100044807070b4104031800d031045d40651000b1500750384614080c485641404403000c0381a09101d04100450b1000070907658109140c41d050b8030040c3c1d20000404810380c409000703151a05c503a2140e1040c0403415500c010801d00c1000b44203410076810500c0d00c01100d40c2d5400308007a83c1d40e100000d48820504441ca0000200b040009004040359603012000c01409031600041c0e104c402c0c0c0300710b265200c0300e1402511603040d0704104040340c03500046d0702c005000e0540240802c01c40d42000e056107000102c01c0001030000d0031080c1d0809100780140d043c010000002842005000005081c2c005c14900485506031104103140200a50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788368102 1250 788366852 788366869
    0xd1d0c01081618080f072301090e1b070f1e08040504021e13090609021e280e190509070e220b04061205030703231602030705 55
    0x80d0110725180d00c25030400e004480708000e9556070b0205203200f1101150b440c2c8100f03e10030030002108018138189042280e6034420050f40140188000050480c1041e243d034010703072000481d25400344c40002038803a4484100102101c1188804820011039402e06020203041d400b4142030103140c284240410104c2100517002d4100d0016001c02c104001c1000241400c0c2e002384540f12a81c008108aa20701501c4418280e201881c00703500006c50301d600b80000131803440b0f20313801442103683c218074207030603400c80c003482d0300c504800b6140b1540040381800c0301c103d0705e18150740822060b94680380107070380700e5401030b04201d2b4546c0064007030715030602008400580d4200300c005445004190120544d10742d2001c450540c0f0f902c45264001111107c101811004400b44902003a103a200c0412411409030500040301d100d07512016184d0184800900402c401100300c40c60540c140c901085030906038908420705808190544501c0000000c5a8134120681041207d401b482103080e42c41090b943c2003044000b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788369352 1250 788368102 788368111
    0x10506060304080d090b04080703090b04080712080d051f0503010c050304151b031406030a08071b05060403080c0f4909050102190506011503020d1d0c0108 68
    0xd810070104000c030301c003640a805406400354000c6180560f980d552410140156070445010801240403c20143c100b0321210240840e104240d041174034018041c1c0d03443c032039803203140303114501ea00c003502c00d110320581112a0300011b84400e00003402c0c2140034442000550010100220460201041501c0c040c0580050900e1a96540d4103603291621106443c81101901c0d0303506a030340d0446036003003056804440440b09080c1d100081c1900c40e94601d228113910003001c0c6c40c4a90408030284c0002a040c0c001da9100d685c03c25250a4030280c2186810403521050f0441544244080307400403c21116030700400101c080281903030b0210001c600d10350ba840424141ca56039101540b4a048501440150704031020300c4403100311210072240c0180c0029814a40740311600113000f441040c086943c0400c19045d11000f42c0c0d41010345a4803070344485032101d2060003403180c0c1c10b45200d4001e052601ca03406031042d205503002d00b00068000784501c2d0900400c554016071540c084c0007461002ca6008280c8548507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788370602 1250 788369352 788369359
    0xf061b020105070b2203052104080f03190f151514090409020405160206010b03010608070e0109030602190801090614060912060411010e220917070b18010506 69
    0x41c22800d40d01d00041c203074005c044407500f8440ea44080200404601d440390464040d40760b866996100000b000d182e407015082d07010301c4d45481030030b01001810100071205074980011940c0d849456805030540f0404126280708001030070400b8041110032541d00581a600c82105011002a500d084240b440120b0180c001d0124510005501c41c90002000038002140000c00001e4101034990014084900c20b0320500192255154507080703c5804002c12805020350111042c01c0d0340c9001d00007850008018400c1c8100a01c02913407a2840c2d0044232244040d5a00c180305545a018407080d40580644014030100040d10000001440103814417406e02929400b0715040740c00c04170f20040c00995809601c90325040055288254400e070000c0c0000c50103184504080b0246410107000188900c0209840c00d02c544104420381d40e505450090840180c1040280814508905d003403001c3c0d03002c0d081e01c0d18004100d00060703007420002d501c0401441622080580501d4110300c601d007a0072590700310749142c0c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788371852 1250 788370602 788370607
    0x4090b2d0c090d0302010e031b1e0a030f0320180f1309081b073002040b0d1203060e0c0703170c04120303020418050411011115010f061b020105 63
    0x29041500741031540f0ba010340000318400d0881d6091501c0c1d80e00107003a0b1038000c0400701f40090400030501192028603d1611002c403810b1151101039110741d10440000d0a01500100043e817950090b044881040703410052003000d9401445210300310b900200c2011402d01040c1510b1119180104034043c9030000900000440c041c0c03040c06500600c1600e10581c3c04c50010b010a82803c0440450307844503007140c0000d000390a181000d0610b050b00044940d40905c280da01d0094608001c141520f00f182e501180d0108201004d000450700b960704080c005403a803503010780ea002081d5010f03001034048603401c0e0444607a650310101c032030403103008428004002840142c10b80d640040740701c103085c0c2c004c20051265032030959101803400079401c81c807004401190700401e003080114009020240c8007034078503806020a203801e981c5c002d14003000c00901e50501c0310385264480304080802881244007e0003090503295616600c0d42900840700c0d10650740050101583c1c2088c090185501029456068403100d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788373102 1250 788371852 788371867
    0x32e0b0d142203020102190207080d020615040f09020d0c050a0b03101401050f0a080a0c03091a0a0207020d1a060109030b15060d0c120b0a06020304120204090b2d0c 72
    0x28100d5400030030f808564080c0002c140d46041004003441c1d4240b01d800800c04c031858200c08034104490304900706c080d50408802c1160b114036003d030000b84607030200d8001600068910f46a00200280301d070103134001400380400c20802402c2d5812806540084410142540d59417080c1c003030030302c4200c400c0300550700c82c0e4808102e4020450b10700c01d000c400c14103100341400a03640045155400c06010030703002a101409111030104544918030400210303240600203440c03a6224424466506929204010070b9840050301503846541500e4000790f009109000041140c10041c1392651514183c03401c18191034041007056002e1f40031041201c0c1d0005c00b401107561030199103a03400102c0c1c429190020010016042002210320800c3c00c1740000780c0f00d414800d0407101d602422602243d10300da018601e00003040c040c203a00081a181105c1e1443d00c804030351030051001c14094030044000034282550301081c01440341c1b071071070f2a60382c2149110003030609071a401d600c09a072007020764001550b50700410281 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788374352 1250 788373102 788373151
    0x513030e090912030a090309090b0618030709090501020c06060f2b0807050610050a0f0902031e0c21070c0308041a010b070213050408032e0b0d14 64
    0x1544100018140c40620f0840034001d2001c1e4011a070b4a01d0282d5101e544104054001c0110005000d0140301001b80d0f59110001c903805108400000103c1c500600c43c12601c0c0e902000f40707030060300440c2c600307102104842c42c0c424040c0d042425550103901a4000181d9681090581c4104407400103259000780103615a2520300050361540d02e01b40c061218000c0c90100d01040c0040041510500060003640340440c028020981c46410680c032074020680c3c1003103026150300c007500603a003080320300681d41e0b1122840d02d890345d00e20414a00b802004081084809440c0038043c01e200c00400081001500c554031402100d024221003510100e00c44072f00810220380300c0c040003988540b05418403601d50b0558100700844041c06d80c401c1c0d100003070000f909011070800c1c091030030f01d9005c64402441942400c0e0360312070141c00000c0c18a446400307640c05a2050b5002049801c104001e04079000c0c0c209520f60003e2103e5074400c42c190307840a405d000b01215030340b20107080144512101180503e4034010756089 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788375602 1250 788374352 788374369
    0xc05100c0204241a0c03070c0602060603060601081801020d090b07021b0a0314010b040f0614060705060a020a050d0216030809031206011202041703040906080d0210110d0914010513030e 81
    0x1030b507991351400e0040c00100c4108000400c0c4040c020030341110014035102e002454054000d000c1400b9402c144140816a45c00501554101d00d40203d550032000070140c880b07009002d1391990140322410306200c00180034000c03c1c3c080c0558026800c1c1c0d0511000300c003c82c20741d4151022040c0e00890311500c2040071a0300b165030311680c03600000000c50002d00c1040003400783c071130001c1165483c9a994008010302681c00f0724035952400103446503800c1c42150307190300352501c00040c803041c0c00a4000a218019500c00c208075940c0307600c0050215112003000461800b800d80c00c400c11004244d510b004961120000010741e4034030450340016a0095543c480110f440310b80c3e00c11078080c016001c2c000804c5c00140c220803000807402d108011901c4900d040741000540344035622122807a0044101044401d6000c940c2d002c01d42c01c100700c003080d1180c0016034098588150706569003c5860b081c090810840701e0102d00f24800319440003400075442c0c2d0f1003c44810306407101e0003070205409031861a80fa041ca03080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788376852 1250 788375602 788375639
    0x7050d090303232b0c0f09150c0803100504200d1a04060801270b0103032304091a030606060403030809010b100f180e040f0c05100c020424 61
    0x207845041040c0d0350341302520308140440b140402d844211010031021064450601908040d241a1054150f010310240c100314080c054000c28520084117440c80c940182c0d542d4070043d074084069a92441c144103081d10111042c0541441542014408102ca401161681c8034410350314034881d1500300088507580c020322002c440d44040307403051907480c1130f2a91107110b110010000780b800402c0c022903400140d0742c4420480101c5881c135400071040d8001c1680400b8040c1941c0d49030820791020343c070140403451103090740c0c0e9018250300030020b40822000301d00d40007001407260300310804003803044200c109626541308880c02900610103000c2000032070b01c1480f5180d00b01c400d69000045101c0c0003000f085440e4145a0080081811005203d41e40341d8881d040c0d0b4140c1e40c0e160a40703118a41000401c40e50850f004c0c20141c4010648030143c424003040004c3e0070001c007801450003141d408843e0000d071030354182020607441540341440340a00f8a00c00508501125034581101c3c030b509080500d1500d04000400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788378102 1250 788376852 788376917
    0xb040b03071d0a14090a060f0b0706021204060606231e04080d0302120a0b100f0509040c0216060306080705040c170403050405120a12050d0e060a0207050d090303 71
    0x180031040320344990448002501e00c1005008442c07098000740301d00d401e8041c100ba103a040c60501f0411410380c10f80e1401080e1428a4100e40d13440c581818031078040d000310784c600a0840101401d00c810012903521100481c0c04035160080084c09030702c5003420f00c0004e00801850845c013001500c82005010540000e402c07000d06103181083d448002083c0761400440e01400880da00060360820944011030056026509110a1007113035560b00120307011840c1003044009003c21003004101c84e50040b0117403560310401074810010614408802543c80c000922025003681c2d0301070003c11568840d0107132500782c1d40d40c08014411140b810341448000c1141485040c2001490708040c040407011011a0b0f002d640299552a1180c0c02d01042209024a50303941c45250750006542d08001900c10010510031f51302400d140351900d42038030f408130142c24040203c4802d8000d1008000707a0419550181c5180b074060740403541eaa0803003d4042c5d50700d0a05000182c0071a207002600e0114220811007165a2840b91 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788379352 1250 788378102 788378147
    0x12020906190803071101080c0c19020103090503130608070e15070302030721031b2007080304090905011a090a1109220f0b010e0d0609050f060406060b040b0307 70
    0x2c20301142140c016020856001d00000c046425541c0e00040b82074101e9038003a2aa80b0b4164180d0030307242d80c0c4880500921111021a61788001d6a003c1c0d030102c0529a00b090a0300c2d9121032950088400710101d0141d0300104219402040d10726110700f908a0b5a00d0001d031a80050030b030003014503038003600b00500032411440100310b4000050003100e543c0178102205242090244d424120250680f05c0f100400403081c50948080c00b046680122102c0b4004400718842e56000c540c03819450070205250051480c030f110016000842000c19403004410303030302620082000c1d1010219408608480c0700e242c9a1000c94800410a01400b550001030b2a04007070300382610340224440032a02014580403222440410040038016020b030500616101d075045020070442c25010b880041c103103041403a4100d020b20005a141da0401049511180d1b6007500f10045842154104603c1542da5404036400c0b2001c5003484400503410003c00c00360740c15941841c03c55821907036440d0b01205d04041e000c00698409080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788380602 1250 788379352 788379359
    0x320090f030a0f0c06030504030504150c061811090601270f03030c060510150311070501020f070213110a0c03030b090a020a0306050603010b040303080c12100608011202090619 77
    0xb006100c0c0d980340728009014000300d40b070410b2100d500260744110207160078038041000081d405001c50f4145c4803c01600542180444005c03a468120704030018003803482c010b080d080c03a4880040d09039841d0301c250341c401154129502070180c00c040c156510f41c0400c07002c51039510050070140d203a01e4014480e800400900b6a2401c00c10b500407241e60094020501c0142c0ca1818421503002d03641d8015002d400305034140340f07007011100d510a10b9407044820035a441000000e07030030542c3c00303d41b00950031a0080d0345480990501142c4c0b58001c40d802ca10400b5485a00c03603107060603006071840b00c0580360307905082020303900080c3c0341800003010850400d980c45035002c42a5644021042c024a1041401a26a48030b502c010317085400580000c3c9c450401880100a0003407100c08880640e98075103071080d44c40d1600b650702601c0d401a450004034a0854008002d0079090002d036440c11500259281d2140c0c3e603072441c548200001010700a9000041400010b0450400e4030708010310150f00700600000390740c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788381852 1250 788380602 788380609
    0x1e0609060915120411030d0f08130b0a060501020c010c0b04020d060f020a0f0e0a08030d15080a03020309100903150504020a1a07021e01200703080408060709060320090f 74
    0x80c0252944100701039050000348410401500d98030101039000b407100030104880600840c07c848e40110070010150002580100b042c2d440041c3c0700e5210124801905040d11030f44081c00ca5801102c5c0188118481062290722540205440a410480c1104561129020b1209180328594166145030322000010b40060700f920003886402d94036a24074182d0760b0025801001401e001d004240f045030451401d1145200100441d80c0c441e1051b40006501c078520003079035481040135071003204540100d01410051507004001041580000c0f00c1c0301091010140c42500d0f20030f52800041d040c1c075203441011486d4074196100c2900103000801814043d982c410600346000c4804507009900f070004501402181022286208200b203100d009034501c0304940d00082c10203403568804910801641a4501c0d0392509000e08000b461300a241c20390b6660312820380f550f449005407a00c0c00090310f6501c0002e4614031910507442e0417001d04003010f1028200380c1070090380d81c01c400600c66001c0110a00040d0594 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788383102 1250 788381852 788381857
    0x102040e0703151a2703061914221704090b12010504030f201207030210051b070809040501151d031903020f07141e0609060915 56
    0x19281da001c210aa4201804480c86620390f0183c11140310000c228041c0c100540e003601c02c0c070004000503912041d01400c24005250b017120b2803d415000d6007040c03103d401804217400b0012811110140010703606c4100c00e01803200c04490101c0052a0b4940d04809001088410a0894040d010041400c040d94040b2002c1d58800e502c40122640c0d10b81224056003170a41801da00c4280000080001349041d840250490000101c51410401002200701041058003243c52807405d82e170085031452198207200039010fa2103000180c025129941886919100074051544960b1000800ca0000f940781000c90907036410509049407920030a2180c00b07030306d440d130380308030fa008218034414810003a00742031000c8c10248012a0b031100e5007030200b101c0308441d140018600c0080034000d1180404600ca424103e0411441514401c6180603503072001031741e4070182a02c103980f14000c40340c000c00442c503e05400721a0b00c8100c0082e41101e0706112042075454404042d00345500701034840c1802e0102e42a0004459 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788384352 1250 788383102 788383111
    0xc0d020607020d03020403020a0621020703030507090524030a06120501060f0602070b091905040203100e10060c060f230f0f0c0315030c0301020a02150705040e070309050102040e 78
    0x60388000d041111403036042290f640d030038025080131440c2900310b0700480c04141c880e014407420300004508000e41c103000700084004590380d0600c2103440348414600200a00b1090300c0c107800041141c0000b1400340b400c6a1502108004810380c2c1411030b2104600703801503000141094107007a500c4c80006060500715040c419140d00c50400080d001c1c6c00d285005a00c0c0000b03030030500456008200511440b15900215445403408940040c0760b1500106041840710003500030603001800802489070b01001c901001d4141d40c1f050001c4602c5517a18545100501860321810300018003800358800030a1596011070303444a961203001c51001110f440c06000307040e03c400814210341c1000204289401c500c2d85143d003148401180c81c04a0410b20702d030703160502020301030712005801080300d540c080e07904002c83d07418030402400a40d00e802607130034060349800e012410328460703012546c0007840d5144118103d40a03944008110541c07925421401c500510701c40e481251190750810000c5508050381c0143ca115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788385602 1250 788384352 788384357
    0x1704121416061205100e0117010b0402040306140f09101d0a0c080d03090c0905100f180605040b1f05040308030a05341409060705010b091602120307050c0d 68
    0xc3d002010004c6400040500d1100f011a00c2c080c44200303100f103149411240955622890009811601c0340100070382404590701610001e0000204805500040c0003105c50144012490362400e200d9081c28104941403140d580104d01058409580c542c458800f66074850b00101d04164924191031070034224950070744005804080400017880204010310440c1801e241c207100780034581c3d88961500d240c0d40230742032840703403604c0005000c0c200b4100e0950040c00c04068444100f03075140005d1034440d0b121080911203d04001000c201400c041c09260300c1560050305203014246485070602c41403ca6040c1c42003000020040000483c44e10301c051800782c003da080001e085d04005000e040703448a0100c0401c03402e6194010450804884900d2454921490034445003100f84100802c2c101d00c80c40e04065444070010800105018055016140e200000c0e140e00d08661500e644015440f03000d00200e00041c1d1000d01c000700d0400c080d101960f00706406003406030403c142c0d05940d500b00300d03011404100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788386852 1250 788385602 788385617
    0xb1b0d050c0708070e0402010f050c0607051308150604051806072d020607030b0301090c12121d0f06070203060a090519030e0f01050c030406030504170412141606 71
    0x4400c4400d0004000903e004001068201e142ca29266003406000f44044d0621007060080845d1a014a04a85594900d1800d40b201440c0c4924040c099030051030a209444420150200b000740d40084c10800440d0401c905411542d45c0c1400c0001401004181c42c0345c8280c10899090500070410400c0d024902c59210000880c103c0307100000e90200203000d00700003550b0707421003507038298020a03501c0d0450b07461316012902045c80c0c00840d02400d211700000301040e08091300082e2030100c0303a0044408501c5686901e80c10a142041120507902d04060141c802c5070060075203003130f494914001c9215810183c9003c3c10681c064002030301b030000440c0d203180142d03102c29501d0208841808009040d0000402000c582c0fa81d0b5200103201004444006009c1d40307548001c000709a00403c2543c0e5555040030480f41c0e100e80b100c00080141030240c3d8102c400c45440024918012089400d440a40b128010b94281c0f00ca420344407641c040d4030f10396011009000f001d07920403c004501c0e4000e001741810391a07040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788388102 1250 788386852 788386867
    0x60b06030c0315060306060702010f091502060a0e0c010203040b070c2409050114180604170d031802220603080a020d02060c0313080a03390c0209010b1b0d05 69
    0xe10a203600701d143c5214140803c1005040d61300c0c001a07408554084ca0000b09a00d40e10800340c5031160b0755040b0b403103100080f41c4e0710104160300064180c496204c0c960305102c90f43c0520305075583c0e00003d12081d4050303003080c40180400705005014109643c010300c5544130340b603500d0108100f010b81c0c20a99501440030208802c0e41c46410000003c0100404e21b00000206ea402d10088030714010741580081a041c80d0403031608075910352056030040e011a40e080c1c3c00b0302146040c0b4a544100c540b0b5000042814041c54180142c101e000c082c0d015900030b040c555400c608280c25040580000b042c00350200c1c0d0301c4101002160b070800140660541c190014000f4818246000e480e09000030540d00c1419410000c100030301a1604021081c43e41c000d6101c0c0d00e0b03200180c42036028001c1040010a1459a0712151030b004090030846252100c0d0440c9402e4441140c140881d8158030501c2c01030b410034101001040000e001500802113a45413a18020300d003880041401e003040740c401c1483d0001000456901c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788389352 1250 788388102 788388121
    0x110604061d0306070801050607170d06031e0f08090d140f0c040504150b060d05070f080708090601051224151c02060a270602060a0e0a0f060b06030c03 66
    0xc05101c0044008081514103071500402c0c0200c140a514000d8402144117000c00075030310240390110400d81142c903200d038078001c8070000500e058401543d15401d0030780200c02c0030745042c042e000825008801c032944841c00d80c845244580c418880517070041f5103030035510302083c9148815031f084011500680400078108014500c0c240800403c036115528002c00e0200050b41c801002c00ca40c03c1070b200100c0c860102c40c0024585000d100c4030009018140010401c44c0d1342c0c0b1610b880c80c440e0f581e0b12740740f4054852510499018404644403210365000310010701540ca8924064068100b11000301c80400c03410220b80c204841d02d03200c803000074000c02000d00c081604001c0001035015029203903c030701400044008001451001c0c00640254800a210340c50300344103201410b5a40032100c152102a6460608070114020b81d215040040c0111000b040050055000704c002088400000b400408842d0715400c0015404100031039006a40340082d150315100c010146110f0340307c814910303440f460200443c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788390602 1250 788389352 788389397
    0x40506010317180d0305070c0806100e1303030b0a0801091103190804450f050615091f0c11010c03050d020c0f0106090207021206010b040e0411060406 66
    0x3002c203108414000101401c07a4a01c1055031004110b032031580603104e506068441e4400c1c4d14001d803480107140c0010400d018000b4209000d000760007c0d40703200c155291110342c0c1281c0251440e082010300c6803001004280709422101a104000b4a09403841d40c0d611500c60031a058820304881c1101c0c810400c2d80640340620074190706405203804c00c42010650381d102c0d01648194014000c00280c80741f440031f41441c42d0070f03800001d40b614000090a10481c0c40010380481503035040d20398203904001044417440824010903000d1880603000d595612000076100c01c454201910340c54000400d004864800c0da000001115243c001d0b40310300117100600c0c1045050010408201d0f41444140400040003c1d0f0213000c0301d41e120702000300107031a60030340c1d0100340c144120014400e82030b60030031030081000c0042e5801407000da44200e074401003030030300300c1c8850303484003024441c49038560700601041004c480400c824a0348184030708080500c01d46500005031064200e9000740c400185030380418030700d0481c01c2a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788391852 1250 788390602 788390633
    0x10050a0509010b0f030a060810020909060a05150903010207080403031e03090503091002012a1808070b090a2102011d03060711031317160602250e0405060103 69
    0x4254035650f040c1908036243d8450041d20f046911800400a0f840400da90700030b01c05080c00105032140e01d0b034200651000f94000c030503038034401c2c221600443e0b45850b124010781708440b0003820300702d141e6800c00c40021803a0081001d1a4065400b000140d0009000000400c05548262640c0c2540c074401d03c03445007034043c9055a4014140b905003000003055000056403c0c0880441d515180655001000c90240c40280ca01307101c1412038070104040324988a44440b501c22484c0d4a918910703140388075414042c0118030540825420048007070080840c203600034a05c89402a02c04100e10b40d540510f58015881140328400c10711000750014215039020120a1201c600920190010900340c0300094030f8280142028082c80b40000c000c0d20106000d0098400500280720440002961140020300a0b031040852440038003610720300c4400350042850b10400c0e00c100d42e008017440005000000100c08688412003c140700c8400001451002d03945410301c246e20a901504083d45145080503104200b01c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788393102 1250 788391852 788391859
    0x16090509070602160909111801050405060f012a020d0c080115272004080106050a0b0d180b181501050105091905090403050a09080c0f0906011710050a05 67
    0x511042c046040741d0201071750502c2c01c0c0007071000510f2400400b8440900c21440d084201541d00c0300340d590002c44c82c1e50407100c042d5403d00440e91380108104642c0700400400780402d140c1512080280069030840b82d881c1090801040111126000200e041140b0f000c211072150001d44240304040d820f0040303c1440702c4000034120030790f06201c00240d8800071080c4001503100c3c09400c4117040c08183e089081764004e5074440500d55041c6c0321000d5040c0d03106005c0c0010f00c2d82441d07800030702030510680703002c1114850b000c041d041401d101000c40281c140c1821805204090304081c230f01044111000c140a076070000c0c8211a0407800409260130f0541514210002490000042040340d07000801c6030030b00d2008072064030581c040800c103000c0460307450b00201c1d00514250f041004040e001030040101042e030f500d9130400c8969032121141d440407900c00003a00248481080341c16428006081600301c0c40505201c00103e6130420002c40f0110100c0320b20394648039240040200d4189100e44002812094 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788394352 1250 788393102 788393113
    0x120a110306181b03150f060703050405060d020d0513110a05060319020409050f1b030105030705010e031507050409060803090d1e0f1b0503010e12030916090509070602 73
    0xa40094221444250481c07060703a00038001030488040319441c10520903180398455281c5c10b008010f10b48400e64000010f000304190700d03039140c461070110244c0d04407641c580da4840c541030500c0d00b40715198019241c0c9102150302407280003071402c00c60058078801c0e0004d0480c0040800c5074100712100603189068140a41c1d10780100b4041034550b141100d6100d40c1080c98441203e01c2417500f40c0c0207120742c0d803000d0410391511007030240c44006255014010490b20a1580304138440040660f880c1c40b080c807826607d40d0000000300b0040d4054034021840940c000c043d00c0f00c8040240c540d103420382044401000013400082d050180104034030a04015103013800c01141048e04980100d10007c1c890580500b03454040d107240900f050241c600030310b580b6403084040c0e2044056103003480e129002d20809005542c0d4101d0080f650742814415a15030b214020001d11220030030034034a82c2d44e640b01611803140c501034903c0e802440300036529841c0040680140c00111440c11325286824003200f5000300045402c80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788395602 1250 788394352 788394361
    0x3051c0b01020d0315030803090d0e10020a02130f1401090c090807030b090109020a0b0904051e040f11151e070309031b050907020a1406101a0c0102120a1103 69
    0x1880c1c03111034500e00700020700062039075030050b192a07168802050b1f00c00000800007007500205100c0d0b100c1d5101e444000c202b00d404000c029100194825503401a1b010581e628050b1801e51200003480e200c0030701c0043c45c403800f82e07595010f45034502504000c0d00c012100400c10002588100c1018005629003c81c1d5203003024013150b2250040d02c0050800500300c0b0100d121490203503c6801020341c014404505940d492030072680641000c0c1e03249104520b0400020300881c0d003a01102c036070300340012001695654036502e20021840440054810b030030441c00751103043d140d10859104142c484007001da02e5a0310755007a01c4c03210409608183c0050b500b4000980020f1f0800420801e90b5400340d218044103a0000754004038480c142c3c045544900e982c000c2c0103405801089200e9401d010f10001303241a180e41c200b084d59100c0075a407a1500283c064420844034404150341c2d082c80510000103450044180c80c45400d98100a03401001c4140d904140a42a983c900c039440000c0182c401d0107085240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788396852 1250 788395602 788395607
    0xb120f2502011b23130914150306130803040303060e01081005150f010f11010c031e05010308160f0503040b0c0706090308070809010e04061403010e061302010c0c090903051c0b01 78
    0x9004800f03084d0300001082c07000340350075491600c401402c04004204001e0011503e004030407441614240d81a2001464503405810007190003445605809150918000c140d44c5180c01c5034001001601010f50b10319000c20b4a1501d104007500a01495004208082200a03110201da0002c3c03c04444000c4007a8108030f01c0e107600c5461038081d0424240f820900b566a10283e481c4020b41c02824950351030300e484108165056800306600207044900c030908070305082c0681084607400c0c00301a1a80c4410702c04407c42503200c003284100f8a1040c83e09200d030b0002599400d2950704541c21045000c0c602142c90b07010088c04120442c000c020a10f0002c2034030b07281d522040000d10940401078a82140012140100d9018807400000440c000e0400c000b0360395203041d1142c40c2012b4200c0c03180300b5400c20643c08446000094010b0003508443c4049c0031042c0694015520700c2c141d850102d84400e0390b5400015101c0c440d10512100c68000e45401d60380b503c884801408104008a9010846240400b03681241c2d0303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788398102 1250 788396852 788396897
    0x306040f140c0705030408300a080f0a02070203010203090a021c080313061103070c0302060105040b0a14030a0209040302010507030b12101d0a0f05070b120f2502011b 73
    0x600c2c0c05916520030407401d2290562046420403242c501c9001c0380200e03515800e00070f4880040544403920106034981541d40e115125a8024000050f6500007244110220103021038201c0d10701c83c001894039005a0101e82a608112080146904011900c0c810341c20103101d6081108203031b07003442c010300b602650b0340082d5002c05403000390300f108001101d10410165600c19201001041d0340f0540324505070000800506000100f20010b004040000846003010302403d558282c000308600c100d5800d000e80700035042000d048017a4035201c1c0011441c056291900254003a0b800703a40081124a480203000e400c2c0e420140c9401c1c0034a42200380f000b5000750100e111165070100e42d4000c00c0ea4101d80c880c40c0f840319005c0000f890103000750751112040000e401d0400d40118400d109a402e566640d070807086490140c43c90036085009500d000825218450f04115440300f1403481035140d800c04c5440070b108590300b01001d000543e41d0341842d08001c017565905140480c60070714040a0a1342140300e0110b800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788399352 1250 788398102 788398111
    0x4050303010909050c0a0311040e0106080706032f030f06102f060106030f051b070212250611010b0a060c0201090509090d1d030312070c050708030306040f14 69
    0x4030381d50f600e068100003080c4003007000b841c8001c110302c01c1c00b40c40c1d0038160300b40c50342c442c1c00510039854030040030550389040c0210300c1150098805405518500345090f4090808107180010707203036084e110410203030100c011520483e005100070589038501609174160004010f0040361007454920100044030754001d05090180c802c442d00d5440301141064583c028008500c441c54036801000c3c004180660b01d0b40c449000726030000340500c4180c032642038000c59030035100080f05009000708180300143c1402c2c0b0000703980c0030240f41142e4410944121946200743c6c80590040b400c06c1740d44007005860b62012455141200741d100820192f00003000003000103956104140074050310b6040a4156030042c2590300042801600b01800c40c6070825105850307248030307103140d400704a105401260602e0321242d491080c0c440a4011850321895130b15103426020001c000c0d104008124412500080040c4a07800040040e07600440d00c030b003450420403050f20348101120344028942814070580300340c400c00302a0030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788400602 1250 788399352 788399369
    0x2010e0601140f120c13050412050309030f2d0315040b01110105040501091a10030803181501050a0b0921120a02071401030501150305190905060105090f0405030301 72
    0x10b01021010940a0000b2050558020580080500240008a082100c1200491701d8110800602c8000e0040700e20940e0050b00ca40e1005141c0414103003d1001181c002408104803410510109920107041d40610b0b003611008a0f0404810b01350b5000c006210666041a85105d095141024851809a121900c078038030a54071740e617000305c071350340541520270301002104003d00c82c070f03d03044c2801406800220000c4a600203034412840d109011140782e00d01801592200c02010b9145845055982d00301400c0015203524401711801800d07030411547d0402a80b4648100303056140004001c80342c4281d9100e201701401c10000322103165501144c1901c0142c0c050060001415004241c1d4034109500300e116840000001d4400394503500014104100e4408200030600300400306c0c011425102b00707100310302d05010521691022103010b504001e511602000d407044d03010b0003c445800540e10400780c292403036000310005102c0c03420007401195001c4c00c03805010032103060968a40c0d50342d200504c18480b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788401852 1250 788400602 788400629
    0x903071208010e160320030114040209090f09011506110105060901060c02040f09020a0305071703072d05100621050a02151c140a05040b2805100503070602010e0601 72
    0x1321a0282c2e10980c0c0744000c1c01c0605040c800451030042c45d540c001e0141d9582600011241d001d586054001c444071a900a0030008164a40c852600b01694010381440119502c40c05024542060741903217500800c100d0b0f0350660040055100da900711800600307881d000e041d103000180810340e04105a890541d038190750024060144a481c000205a9444000d6008250316000030a000d000100ca40507182480f140c841500c140b120603d81d84d00c12f500000305a8140c45099401380c51203007100801d10b14000c0383c604900c2c942a528581404400100b000d229948e5100921004064142c900045910b80c0720801010b07810b6100d65984140800b070091003010702c0c8600c00c2c5200b40030350640304924200002403020799130701454100a4001d0b4140c0f04260306c43c000000e402c81da0540a1070740a5a00310440102584500c404100b150703401e040c0e0045a941075803141611701c44544580c1c0c1c40b400400200c442400d041c0380825060003c40e92002d01168105002210381c2070002c1403050454541040e1f02c00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788403102 1250 788401852 788401891
    0xe100801062007080604030c120206010302090c160f060213050a05030307170f0a050702010e04140103120c0b040c152318041b031d0c09040c05090903071208010e 71
    0x246002c3d0107401a4465004940a04c01015000850b419440c0c1c0709149503506035807801000c80c1d0b80c503401d11000e944040d400002c50702050810000300f000b10941c8074001e0b106c105070785892030320764001e407001c8401355400030300d12000f107042d003d0301805058100c0b81d1521292401e03001a9a900540c20003600c083d01540c4a0b2281c824840110b03413005484030266a142c1c042c0c614094010b4204402c10b901040c1c01078a608420b2510f449200c0510a180034491056400c5482c1c46001003a620520f80038000000000d001090703508041503c614821100034150328180a07194118050031600c80c814010008499128038401d5812540d1540225045d0f070b45803e000d01900d4608081550f840d07400502d0901e40c0c01c1c021102c0d10015282d0200c544040c042c4a101c1d04255580c1d801e01001c10140d82c00c44800c1d1002c070710b08411581d800a01401f4464202c49c0ca0381c1c00070300310300c3d025131701c002c0d255000260020802507004080d1010750541d09104140c0d40c5044084120644000c10a43c913041c001c440b40d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788404352 1250 788403102 788403167
    0x504150b0f0309190c14040b010c0308060103270c080a03020703030c051204030308070e060903150402130212092a0f031501170708160b0c01110a0e10080106 69
    0x4511a0b403088040d083c4c088018201034100b4400341c0200480300e80003c0d6280c00c1030906014034034081e00180d4501c18142c0c50f584080760001e40c0942164101926100e0700d00e682249107194004400a600240540401c14505800783c8143c6030700200268000744000d00121f50041070350710480741c1600380720b07800180d04d10705a42491144035880300748810204001c41415400201a8441c450300e44aa007500307aa5081004002c1c014454050340c15072000c3d5006610b01c0c2d0215010360803510140980c5552481c0c2150303002a40c000342e0041c0154580c0c84100701d5003034010080110030310800c84d900340c40d09034114910100030111050150044105956940d81510204038010b642e0243c0910000c0e156118455002102c070b00801d07016880c82112408155000c0114034001040070500061100e00d25000511500703412400281000d5541d420030300c440100c1e6070004107049401e0fa640c40611701a4013003000b4841d603000c10500c0410501800500c4850f402100c0607800d00002003c0042d01d26908065 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788405602 1250 788404352 788404363
    0xe13021003020a02010e06010b2a010f0c1b080909070e0901030521190e0307031a0105121b1c0611030a0c0f0e130908070c0504150b0f0309 61
    0x250061400c8048012155041c1d0250100d4500c3e98020301030340c0d400d081001c0e5651828000c0802004042003029915070200d05184900e601c0d1a0a00355480420409142150b101003108000749885142d2110030176880b4180c0d4961001940c1c0410075540680c446040034004c90108500807000340c404940b03800e028010500403c0303801400d070800b543e16072409984071000340d60080c82d03a5600446c40d501c0107400c01c00751052585044040035a5040d032a500b20341070102c01c2815601402910404800f0560203903203030300e5559044015040f107516100510800e240040000d52481d001803195041c18100b1401000560b0000c8603002d180c241030a03415846001050801031000d40341444003201c16a290780a18401c002c0c0301001c1190040814040e2805950304040500160404040750050f11b0a60302080e03a00e14080000075403104203a544210310340c08002e0a0b01d0035502d01004000c1403030107001e40c400e000645240310310018603000c200c0c10240600d04a60080326000310002e8520a010481c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788406852 1250 788405602 788405641
    0xc040e07091707050108062b0c0e090102120a090b0f060402040b0c01060806070906021c03140a05090706020d09050418050105010e04120906051b2a01020709090206040e 74
    0x82d42c80300003410400359603640071284201d90204510714006400b51514030400f0150b1001c5045a546241940020100c040f000c010120346a0240181c04100000c80d0018548904868000140c0e1006222241540c075107004104020319400d000d10840002c6025520b81d8021035020a100c07507503100e0600040281c0220b402080c4040c0c07010070801c1c03000c101500400c0499038008155085a00c40400440c0c1010341c902901c0051392107400c41300b440d2101c409400705030b00c40354a0005440c4503611105070f83c2c0300c000d0b03c902c00718035251000c0c07001903941441745200a0440e0f0001346908107500070080c04071120b501c40e941c030490307569601255512030302210944241c0e100c00200050b603102c100c41450341b070b03040d03c090354000159440340076581c1c001c84000302560355907210740d81407040884036108040d02c0040c4400c0d090158020380c50145820b4aa400c00381351004c16507040350582100024544040c030340c002c080580c1132080d60713000360b11000d0890382901c0382003a1a408903a203400310710101842c07503407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788408102 1250 788406852 788406869
    0x1c030506040e1f1821020c13091a010f15140c061e07050d0914060c09040c020714210d080105090903120c0904090209040606030501050f0c040e0709 65
    0x4246550008080c032682c56400824810042200600340381007000703071000380c001c0609003030340c00300b400c034440d00c5a105c0d600035103910480da0410130110100340d082c980302d000c244241d44c58880210821072400c0320000e042400c3c5d02810f50f290715020b0f2207005040c50b40700f001003482103400a440d8940c803902d680101b01041c2d0040c41d54410078800b035a41e0304d110854100003a0002282e900700b5806407050110b00545003230ba1668100380b1a00750f007500420280b0300456220b9100c0c284075484034400d06c1124401c0c50070130041070722920050180010348071003000000464029407400d1141000d0611008148107040d100a0101040102e1400d9840300c00312005216102c0c0013a04180305034440146c80c141d407070035034041105840b404000c0d6581d01a01c440d40700c0706850500081d000d0360a14010b003007010401400415000d010f50040380d03100d24141c40a135005502d501c418424440309000f00c0d608442d10400101d00c2d80b900c06541c00440c003550041c1404414840013040060b07221b03100307040c0a409180d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788409352 1250 788408102 788408113
    0x90f090c09041b1a03010e10081f050702071a0f13150201290114130b0702180405060f07170114100806061c0603210305091c030506040e 60
    0x42c141224102d4091041e4800f229031000c01082100d048041c1c0504c50250381c07425801c60742811112041008020440284e00842140000343c0050070403601a075074134030f03002d008036452212090b5020340b07031700901c0c40080d503119440811104002a00e6600c040c1c01c201d011a40710100d180414085204118032482e944104400100b0b01d50941c006101c601c0007180c000300481140e024420030401004402e00519441c02d8900040a500030035003a1950390501c41060305d001c50841d2411100301094104154030071000c610305003142441c0390108045041e0030803003017a903d06a0f82e03042d5140001440043c15008442c04210064000c002c5100703441c4402c200344030113607111030810b8980a01040d100c0d00c549070391100c44403032501a000490280c0f0006e00030ba4540000d5a1407000c0d021080009801600d90702ea40010100e8207240001d90200c400b282000c5001011160080c03d40e1809004d4a4040d089101d030710300080f142403402c8540e00300d18140418142d4601d8000740c01800505010a154010b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788410602 1250 788409352 788409361
    0x5030c0d170c0622122007060f12090b0c070f051b011d0a140607020a0e1603020f0307032d02031006080408090402090a170102042102090f090c09 64
    0x100d00fa07481128201001450301244a2091100e0289188003a120300843d42c1500c4c0e0141c890600344034001c0c1010000152550116055450b21b903030384c2e0184000581801102d184c00340d00071040018444482c1d402e115845072912040d45007000940307804503001000800c0740030020400c10858806810000783e6440c1d842a11100e80e0810f69181600d0008080c0391804900c00d25404000701041c10142c4090709442c185010000b0302542e6542c90b691005040c80001d006070760307818042000e0318041c481022a421b200001c24220ba04d09003c24091500500040d10451003002c16030368420280c4c6008960b03603020040e00c26248a00081003100141988506114401c0c19001140184400800c80c004169919811070b81194140d8000b00103000401c030f9034680c0d00d001e802410410000900c81d81c08140c1e64032404903a25140100328019075008a01000072501c07560f00d0590390ba840c1d002c03030070b420810b50780010a030400c01409040d00200907004664040c904000040e12076078054400e0505052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788411852 1250 788410602 788410627
    0x2070503071e1e1703031e0a11030c040501031409060a0f0905030c0a0b07020111031902090d030210050f130204111611040509030a020a06020c03160b09011505030c0d17 74
    0x45500070f0b05103a10103c04030013080700000044034402c0f420b0921191810b0203158800004c4440544041c4070240c0744d09607008001403990043d0b00030006c2c03846141e9203d10f0880050169030b2221020502d110416042290002000c120198040c05884001402102c0322100400400542101030581c0c0b001052803070224100048401006004451080d12582c44800481c00c2c0c0f0408002420803450070302c08100003c0d4a60000032400320b1a1202605050070b1401154018485010a8005a000300000c1d44840800d1248a41000c1e0800000310a4540f0040c490304024640100134040d82c1d440c0f0307607050000703036800541e2202040060f0f004154495810010041905013850910179403420000c150711400c000100c0741c0584d03564014100c49581070b120038000b500070758902c81042c00300b0403600c90301501c05043c02011a00ca652400754500b0020341da20f085a01e1610441080c9400070821b11441c1e40025810a0504044481d040c0391255841d141504070950b0007134800c000d0010822007120b55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788413102 1250 788411852 788411909
    0xf0c03060207150e03120903120f01060305090c10051309060611010b030303250e0307061e030e0705040c0c0206072108071b02010203090909060a0b0102070503071e 72
    0x20302440e083c4031001810b88021084480c110b24598082e40100300c5a109035202807021035020b035481c0b0944c0d082004038414040c001800716016441845044014851070303803d4401d16401c410ba10340181440d402c440c0c08101501e2003500070405104020428600802100e00020041c0c282c06a052004507940c0c1800340c0030307640402d42e0103a15401c00805c030900d401d000050300d210f1908040381c141100b001e0754504880155055001d0104860f00c1108000c035201040b0b0b9070700a100700d541d1030010039000f14040d48541c0c92000b00608040c14050381c403050701c800080d44410744000710b40000b40c1411000c4107560180c80b800f0020b401042c0410100c0a100300609904030300c00078080c01021400911b00d0072030300000210b500d8000702d201c200c040c210b0806c00034030b0030308101d106004407840e0418200004031190400c43d28040154401001c1007004405400740b90785401c003c2c0000c0642c181443d00290322060309000e134600d00c030074070f0320a11080348440c4034841c020043d100345880c2400d089104080c820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788414352 1250 788413102 788413117
    0x903080d0f11090a060c11061c0911010905100e19080a060f15120b040c05040e1c020d02030d0216080d1a010c05031218010f0b09010801050103051002070f0c030602 72
    0x3210503080005d0014000c0441d041110380c8203000c642404800d0b410001d45400c28040d0348807107040300ba10198810300d04c0c414120302e24014800000070b14402d10004115000c5900958050451403880c1d045480c0c2240451520030011200c2850400d5484010340c47c200640d442a6654400c40c4001014420154800d8801e444042d0048c810720301c942116406040d03c500c512541040f038441c94501042e45003403500e820503c1f0f00344c0d825420383d9450000d0f0a0780d410103844150b9400c0540a446584032590301c090100c4442d00261001c00b000040294490060000301550107030006001040c00043e40840007003298440b0980e615550102402d40081c040300d20040c0e803101d060051010b556000700030b441011035115005625001032061b01c01e88400300a0114040c4104044810400700801c4c0a40c003c0000b0f40300e00080e64400d4801002007600060348035a007682d141c100140003050300411600103500103004003503924146850510700b00c1c0960807002d00f0f840441a00801040007540051490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788415602 1250 788414352 788414359
    0x609020a08460c030b130f060e0c180906300f0303090f01092f090a0e07090c02030a0f2609011a0906040902041b111902010903080d0f1109 61
    0x1402c243c54001c0d411101181d076481d030b02c81204001c1a24808190f009409010390000c0080340856481b810703407010701425104103401040208980404504038940b00301982011240d1202134103154000c110403805000b211504901e40000b4400c000c8030103554031800c032100d5000c48488100304402c2d95244e800549010100b401b50844038200800140500103003250401402c0e60501c4414140c2c2800000c8442101702c0c40204500d980b041c0e64072402d0300c62188011060102d0240101c07006142800b426402032021189450201e2105590000c10340300d800d165401c0450016103100b05c2660048107210241c107010003050b06080503d107106010078002c0c2e40403802802149170119005840100c0340100c150010b00c0d15000400c030b0f11700307500889442c90001d00300052002c4845405a282203108501e480070554a00095000180030054202c45034040a8200100d818a60000742192400e01c07001d0450300d03011034600207990035a8072500414580714020418551a09120203c50b041824058131 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788416852 1250 788415602 788415611
    0x18120302070c090e0606040915060303030209040c03060b09092716081c050a030e030415180e0c030a141003030e0102070303170702030403021c060609020a0846 70
    0x1098003c500440401d440c00c3c0001e40010742d9000240401005881003d56001c400c031003040c520140c2c1c51240f040030f58000d40d03025170f5400040090200381d4201c201c0c06000c0605d490400c0201c0c0c55410305541c0d0040e81101d0300e10f40c0340c0324002c856405400001c0a504100b03000ca01c102802c00000811b039405210b010000030401d9503071800300e85c80725100300c00d04202031240700c104070b100d1f4494002414104114100003590f1011000b600303203550030541201020746501d905217001c2d44d070428900300c000000c5c0b2014621207814110341000340704005d40602e00500c00400420308404c0707590040761140305001e50800151a0003810030115030400d10054020032031402803111a94404500c0805803074268845802c4d0b40319101000340f00c2200107026004500040c031021006945111032140d05079911701c0352060791465420060200e900d25844400c0c3c0c503204210042c00341390400d1710160b00c206074840714030036150000d00d20b60706480d0205002c0000c900e03010030040c0c61410040400014203482e60100f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788418102 1250 788416852 788416859
    0x702060301180f0c0e0d030918140108071802180d08031801180f080405030715030b01021c03051302030f0106030614070903020d170409090213140a18120302070c 71
    0x400c07268040d40604c001040d130089100e141c2440031020340e60520a2400301c2c03410b0703544c244c00c407000c0c084200004030554556a0700d1501c4040c800015014100c540c02410107141b0b040c4001140e225070808898443e600400d0440d030a071508001600c0c61403000d0074482c00400d0503d4141d4041e4021a900c500b0303a50413580e0542e15600c14800d4a801d40c00f040c100a4580446032a040e408240e959411600d14030300b040080b4860320180303d01d00c005e200e00030111070910301444000d826500c0d04e1421904641c018a80d0b06040481400b969035850300508000609450311208180304184107403001e905842011780d2251040015840030080303a010b014200300c0458803941c4c802c240c1d00d0a80d22240051381d002410f03c00742c44c004080c81d004030300c682d1030b40440d41e001c1100d0000781d4229a20500c07034240d950404500f581821044e802d000040040104056403c1d00c1500b641d81038081c1168800c1540c1e47d601d415040c0c5000e04586c80c5a4000d28019010308103118014041d40c064201142d24004a01001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788419352 1250 788418102 788418131
    0x8010c0905010e060d020f0c0c09070c0203061501053f010e07030b12060a0506010813150b01050d0501090605010306050907081603020424090803120105060a0203070206030118 77
    0xa105984050b943e181d003255600c002c10039160000011840325980c02c020507240c021010b0000c00c01e0a400c80040c00040400c9000c001039540000c1c600424850010f01d01401a500840c0f61640b015a220f50400a800d8190040340e440c011404036940c80e40345044054195250224001880c1148200340c1981007040d05100321189401e10610008042500100b0141da0180d044194101400340400d0120900301d03400e03914240c420b81301e80c500a40c3d25814030003996444030903958048000d0761102d090918036690103d80404800101118507580d8001031382984c0f094084550341c14011800384070558442e0840320003003040d442101d0100e031034041300260a0a0001c2ca4910524481d1515046c668400090072105c2560380e600004240e030820011800c0b0940b0f07220200c0740024407204c0e1b03104202013130020704010b49a42114000d548107100131140c2442e07844002d81503402c250389954441041540991640c081c0d084000c0d0302207030120001c00da007840041004803901e09000144054070103021031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788420602 1250 788419352 788419367
    0x5040b09030a050714190803010f060f1e0e03030a020601081603030507030302070c090c030c02060f01050a03080c070b1207030b010503070c020d021503090109021f0807120f110408010c 81
    0x301c041181448a6404600310560740e05a00020505441d1404c1d4220800e40f07030504686d800b01c4059a0102c0140440c10b07201500341c0160045003011034218044000207002503c001c96507400c14082450700780e00c01403040c483c044034210003404403a103945072401c01a44070407007400740140d075100f40304050340095010400c04045941640710b0300d207003040c41e483c11406580715441c19039050074010700c0040e925405214541c99150140c0e030001d00d86410890080c00d041014041c0042d80107680018042a500c1c140c862080340d0740850441d07900c031482000076050807000d9008201031000410800360410941545034460100c030398040240809150064540d40800c0d10320b2000900b0900c089001414043c561149190008008404860200c0d204840d254400c03588100140d4440d0711100c00c50400900b0071407520401c10700a10b2019152000800c8100020000010070201d0006110110400d03440301c3c4013001602d000303020315064081110002d0f8014442c601351986850189020240b040071b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788421852 1250 788420602 788420617
    0xb030f07210e0f0c061e091008042003190516030f0c170607080606070b0a061a041404180c060e0a173409050f0609010803091e1305040b0903 62
    0x80f903820300c08502d180e031902a08042d03001b02c42c4081041007200a580d076880d002c0700e070070b40d41d602d5096528181c98800b01040c52940796003d00d071304c04003041000d91703804501c1c1fa000305690302c10b02003284002d09080d4900854081d090030030145025010080c030405803070b4100c40741d006042c01000142d9800e06002c01d00200c3d00e400450350407079001304524a10070000030383c10040c010056070402400f07888004100c5d40944030180003e03a590070070007640390148041000302190302c84c3d0908007403070580040c117a120080c1c0300b0751085a5600c05108095031070b84510b0800f0390004d00c00501c80c0c0d166000500380e084d0222080344202d030f54042c00030b094803001209201019400014041d1460b01d090602e580c510349126002490203c55405001182d080206070b005100c01207000c1801e0820910910240c00042d007414040e842260041c0145000041180c41c6d010080d22900c504265084060305084200c00d07040344d00c03060b06014102402000e810580c00380340180c075201c80d603859840320304e80d59109202d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788423102 1250 788421852 788421859
    0x170c070b0307270306051806060303040503060f041410050f0c03150f010504090c020714030f0706080c07020612330105030a0608011514010201060b030f07210e0f0c 72
    0x2140924001c0850f021107603055003504021841c1c94690303651105031401111458030000da03003145d10401e4031082081607000300058000d545000c0c2840c022949511000301501d40d07040c200d00c040707010410840001103401c20b030541983c11a00c50042c001000c2d2405a8014101101c45008a00384806002c11207000d800c04c80c1c0500e6001e0541828400180f868201c42811701070107001c001408852402081101040343c0c1c0540310040c00c4c00401e20842501c03a80c0640030354044010481c1c02c40000500406440c42030902e841e1b0395482c81410400343c410382740c0003500b19030302107460504051130b010703450300586140350805092401e84000303000b113a6031500c00c0c0d00381c40d00ba100300780307070a50299004580100445402080c226101d00e080e42c29100c90203000709007611f04c2c0c14104005005055460003a010901c001d018091800c2207030881c9000181145541452a02c04108d85602400e0301d0210301c214480f182580750b07894002100207084c000a000703854003501f004549102d501040041c003040004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788424352 1250 788423102 788423117
    0x3032b0c14090111010b120705010219170d020d0204061d0906130c0e0307030c0f090b0a231305091b1018080a080d0b01030903020c040c0507170c070b0307 68
    0x68011036020001c2203881c1c4c41d655807044401421340341d603200100610b44080041a10600c0e08000924200e03100c548035003880c030b03450301d8000043c1c4000b05888440c40081412901d0345000f180980c000d00c00c3c1f001c9190424400100010072541051301d0382402c444400e000440080b002d003e101462104a520681c0000e04500c0f61064481c6d5074050b26195500c3d150040c9a1608000071038501011030b0019101e50407001e4042100d068007401c504007910030420306000c05059a00800c0c0504550300510610407684503032403103001020050720102440040c5000084a015602c1500a000c1501d070a6460700440a42c28911000002070200805025029211080103914101c400d41c0582c140c1074480f030011300001940a00c1000102c0d2064040c02655595001001070003040761040c2c1d5100f4103047c10315030a580405e801080d80b0810a409580214440e140d9000c01c03039691144da040100510348103a941c041e80b80060000d030611030404030488802d1601c4d000e1158a40c08116030300c0b400110718 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788425602 1250 788424352 788424367
    0xf0301021c110403051e06060d12120219030c090f0506120a140c0a1d031515031002070b281812170c0a0903030e03032b0c14 55
    0x700c1e400345950315040e054840c1040d850765181da0814400c540a41010081340840001c030308010300c00c1030b401c00b1080b00c2e0b26980c1b10040d035600c8000c002e000b0481041c0244541c4541c501070082e01100d5000c50071000c200708028090300040c3c020a613001c0090001160140c000c40c8001c1c2c1903070002d0903641c0042c1a1414072115031038607442850024403030038400c1d48880c003040740c0c2d130080503525018650360f0840549400900c0030040040c440c0c000b06050300d09503402ca04c440d50b14007249040c031011006080c010141d4409241481d0050100b10320354241c40b4141c5a13801850040d4080d000492042018880d00d1300c0b441e038001c5083c4005650b000000c0c0d000d2515040b03480043e8007191000303846500e5090500159150300b60f00072907081c07086001c901400c0c2000d50100f4102c102950042d1052801814450200303001801c01317451380002402c0c0004240008000c0d90100300313070b403402027404101d004001c0c1e5003601130030610007000c42960900d0608651200490281600b56803030000d00780c149080110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788426852 1250 788425602 788425657
    0xe0a06230f04260304030c05131d160e06010e3703020910060f05130503030c010c1409031005041e080a0e0f060706051906140f030102 59
    0x50011480e2220804201c158581d100351000741c4010b01001c40080d185016103400403070000c64120880e0016041004103000103001402e010003542d4041d500c030b80725509a4040c010041c54000035030034a840b03080d5048181c001d400505082e401203d00c42480c60b2955403864000e00002c2039454901140c21051000e41504151802040c031400d50114000301250620300114200640040e03400300d0381003c8400e00550800c0703000310307400500604074185958980302000f003070402c07420b15000802c20001000362080c618030f03010034060003005003500d586505c1703503400794000c00c1540d40000205484940522214210300151810100090701610340d00d4143c4040c000140340082048540f84158080320b08a0110f1b4220440054070603413919640d00d50085d0301420700144101c409114106c8002d20304a59200c860a41d00741036402130001c01c15448040c255541903503002102841c052070032100113006152a001e56144000581d0070703041c0c0120000905003031740300700c113007191303400c1713408003a0ba5074450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788428102 1250 788426852 788426897
    0xb010215010512031306030203271b04091e02041d0a06020a030f1d0610030c0e09011b090e1503301809010e01030b0c0d09021f0e0a06 59
    0x1c042105891910380c17041d90719001855581c00510000740d0100c10414007400c10103200d604841c42c03814250b140c085540200b6514503c0c10005c1d000620682031346100354442d500300c0c0000503484030881c078002d220b07071000b00103002d0740c00c1c0d090384604d01b040001240d400f440032000540ca40c0082c05000c5503511a104c00010358040a42042095510321301089610000c0c801c139024080d070104c40b004100d0706459080c0c5070103c00703841104a4030002608000060301051804100d0348038030b0940d0b0300c0f0359408103038500405041d519020201400246004059848541d2005a604a030820105506d46000e00b01c186408151b0141d00f650010b0548905500c0b8901138840f01d00c411001d8000071240c032140010181c0100008040031165524410f1142c03074207249007409000071254580c07181d80340d5212404000000341426451820000e480744000302250400c4804039006000b41d0f01840c000030040f19034030041c880240004440c0c5206c0d1a20780380c28200d82e0111520381d521503e081c040c00c4105e01e0030340e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788429352 1250 788428102 788428129
    0x30819020c0907120518031605190b0109060e131103070305030f07060e0a02010203160812010b040806091c0e0f0901060503010e0a09080d1a041409010b0102150105 72
    0x5115030703901000d503a902c0c54051072041c0c9040d9100040a240c40c0480c1082d5200505402d03103a400a00c1e0a14040c0e200105072030898500074501c1001d1006820310604007001003140140c2c1d86000004041070110046025041701d40c00c4a04100711a07840a80c000f40b814142c0b840b541c0e105048243c03c0101c0c3c44041101d8980c1d1009040e918480d81d20703030700e8510f140e000d03100b5a003030400f0114064003400524400c480e08102d4400c0600020820b96000175100d1240c0c0410203401107000c0c030998240302400c8160390900550314094503103561a01c0440200f6040340c800c002681c030600001620452021550311903078440c0c034001080301942d008054030010a5507010b190050001e825050481c0c0e6589800c2c1d00900d20b540314607640354105504160780d42c0c0c00801d00038440c4c0c1444d01550009040b08112503a8200801000615030310426a18503101c00c3d03401d51980c89421b01101c041b0f003100c2410300c5800758514100030880d0030141360040e40c50b90b564810702c80c3c41e44c00d140010003190401d0a00d03014039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788430602 1250 788429352 788429357
    0x621020a03140c03060702062a0f030c0f0315151809220803041e15020d0204080109050606090703061a0a0201020f030f070e060c03030601230c031c06030819 69
    0x603e052401192601e01c0884103103006906c0381040c000c4004c41c0c840700180c10055403401e1103d0742d6400542a4192042c02400342d106c0c0c40020001c3c1842100c0c1068626440c5062085a40ca060502d4103694810f82d0f10280352060b100802c012184010b85030440340c003655100360701c0140280307920400100941c024202041904010f03000c1d1080030071b00401c2c44045200e03503040c03030300c1341464107090b00701565118249124001c90803054001c40c1c00b110b02d03020a490440005070340c2d00319400302d5601078021944110035035800c107141c0000f01302020800c0351140100b80d40d0040240e8035907804900792440e0384642d0220603084088000c2c1100c02c00010815081c05000162030540c2007002c450096204a0f525040301081e1014840501e0740441011040c400c01c82d15203041070503558006441e4480540030605002c6600c00d00c00c0d90320220807112207111010181d040d01c480038102030355101d40c01070f1125a110706032007191080704031441c812038007501d40000040342868a03255103000804606a1500117 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788431852 1250 788430602 788430613
    0x1151101021905030a0b15180f130f050a020427021608042409150c060e0304140301090c060810030b0709051305090d050a110d030621020a0314 63
    0x1000c00e603544602032454040d0782c40f00e94a01e07011025100725419403004500c030312180c8040c07608807003650003555a16800440c1c0502c00400078000100e1001038501416000085540d100d400102541c1c09026280c1e4016420b010f107a80794003a0f14101e10880c011112061004020440f61840d16142c40c80a001185401840c00b500c00c403d60407a400c1c000c60480b096400080c007440501050a08501840700030103079090301c0c01c1161400340501c6401e00540c540011010498040c80d0302c9549551080394004004000082ca040b110503120f510034010f5510110310701c540300881f03003414071808400356044007000d4217150401004646a840141c03008004481859020010607507241066004050b2908d8040c200e910b04000c2c081c4a206041c0e81c420f0041c82c080421881c5403002c030b00d001e0b81c880c5902e082c40c1d86108070071050340e105011951104c2e4a02c11130340312140180e015484032060f030300407910401062aa10007030fa5200208072000a4011a510a0420004207005c0c20741d265407002805458 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788433102 1250 788431852 788431867
    0x7031a030a060b0307060302031e151005090109060827031b100c0813030f1704060501031b0303021005061201020a2a0b060906190b0c01050f0115110102 67
    0x910300314003200141c65480d40d4080e542c3c0d403460108000402800b80707003019821131602103060703042d510020300000300c1c6440c04000a040e84880250003510b0010007040c002d0782c010306940041151700074111850100c0c4084101051907800b0303003409840b52080c940000c411103c06100c0c40362130300700c13408003001910040c03010380700712454000f21090300c03c0c0303401c02000d102c842d0980900580f400910403c1c01d20100c0300501c035400c2200c0840d900340c150981004000b000c0886000c0b00c0c0030030b01d005151314800880d0280070802500e90030190490f40070300e5195004c1001d10070070054600040c440100580e201d82d04814500446c0e41049030311000042c0403d1040b4400207036030303003a030384110720440000d44402440d002c0341c0ea5080c680b005100f203c84150b00704424a5032194100480988440c0c45550003400113030250340e43c0002501800c44c0d8160003581669141d10f80702d029040720090340610350a000006608440d4402c00a048400c0d401d01c1418808100030305035004000031046075110354003000b494 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788434352 1250 788433102 788433109
    0xb04060e041505010b0c0d0c0302190f02210721060603030824101b08040e0717070c0206070c030b2415030106260a021207090e07031a 59
    0x4510032070080b9007140714030600340c15a008440058001c110808024481c480d920711001132500b0186456060100b10611103003010b134a010b0141041000c5078404a400c2c0081100100c840d069880c401e41d65003113110103001644c1d8500200c10b5503004d00c1c1d40800c00401502c201000d1101152098881d51101c1c0c2005464a40613501c0c1600207601050840050000c0310100c8581d010b80484580c961a046120813400190300800d00700d25036040207458150400c4110f415030500c00c0e4141d00283c003503034980d0303500391003110044100c81c91400f08100d0204150040030340c00310640700380c4480d030b10014016965402c0100b80c7c0c101c0b22003030303902040c1020301000050212035803d00601e0b01c2c0c0800410300c0f11865040610191702030109000d4424007920f0303502101d482042e641514058244141d5820030030350044c030b1401e0b0f01d111404503990b0842c1809201c14040d4001c10001038050540340f2169502002036500710b916200c0c102c84045030800142500e4840d9104120f00781d1020440141601c240000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788435602 1250 788434352 788434379
    0x904030e03151e1017070f15080f0c03060d030507062904061a0c190b060f03240c16120809060c030a090611070b0a060b09030a060b0406 60
    0x2012074140208040c09510300c40210a0307249a15150301045a80c81c0c000d628400c130205074822a045a400b05207030503034411040c420380e005081e41c6018001c0969562a011090310020b040f454085031041c0081540440307680d4509202d0410081d009146456001c284401c84858940030b404100c420302c04030000404a014801c01080301c2c85d1240c1c034480265411210a45c54441e10601c50743c900340f000c100d02440071407900307440503140040c82d486d0180c01180c281010744a207000ca0f425020500143c00304001481c505029041c2920001c19100b82001403540e9000446d0303200d840071300000c070190752050074040359a901c41a0743c5c000c5410506400a100201d1104610882c0d84016a0f1a200c410700e90010495034000c40302e000402680c100b05103180302034400580003140c0c1c00e07264513901d400e00856405c400355100b980203425559440342d01309031150b001c007591040740c06800c0200000e500282d01080e5100400018094070302a10a1741d5158000c00c12480d8a582003522031100007503841c200c085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788436852 1250 788435602 788435623
    0x40503071506052805040b011e05041206050702100207050615012a020310150303080702070b040801050426040605130e04030804050105010602061b03040303110a0c03021b010e0904030e03 82
    0x2644031300c400301080b14284515075604168000d070b15000c2600030742e0707a01c04545141c040485803d1801300d00c005104036400c1c07280741c111129002c42080a1000c0002d144d00281c858503003542070341e1603200c44148907010b9101f148070140c41a40220080383c080b17036500400001201c81410b158600240643c0e0045441d9030034a079128180103010f4030307030b0300b9802e0500c050030088850325420021043d400c1d4407010720700111300002d4100306400700006c40c624001c1000b08060200e1110b41c5032130301c0e41c40d9a461702038542218101d82c4c419008841c03140e049501e80711000d00c2540800d00c607003494184030086800b90031904105100341c5c0700980009103050080001c030702990282d80c80380c0c079138a85400c0290035103070182c0c082d20865019404200300304103447c1024488041c1d8144680c4c1d2925241001c4010300f001044001980c103000030f62406558003c952658603612940907613002210b41c150010108140c0340c00c1501158240c0d000f0440d81c84c20303412540e4001d01c241010006d0800540119140464001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788438102 1250 788436852 788436889
    0xa081c2409150509070f030213090e250b0a02010b1302030609010e0105060904092307090c020714010c030525021e0d12090302090a14060904050307150605 68
    0x86080c81244418001c2c1e40c408280900d10032105464003001ca543e89500400f10810405010742d80e603041c500c243c040340c06040d0392840d11803041da1a9075101c4000c000005c00007072036104072112160a0060b02e8402d50341c4460762510760041d42d2809410405542c0703c14001c1045542c1c50030082a90307a01c500001011020b1b1140042e1280381c102c051011524040e04210451189200100324903910f02c003c80c1d00e680c10640e07012420f01c1d0117242400c03004000c01c0780c4c9408500f000d0130000301402c00107244811182c00c28410300036022440710580c3c4030910750090711500f5240e0761001c140e0394011315084101c14487d1070258504100341014107c0da002d80c0b041d584107016003802d0302080d40b502481045c2022003105004000c5010900002c003401100d45009118000c16441192000c0c01000e254009680150003010340f40b910b0180d110080140c8038802e0300303052403040803035010f0800c4540c01c0d00c0b035a40310009515200070b5456105200c0c05998100b0405a1540d6000c0751989401c4079000a141550 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788439352 1250 788438102 788438171
    0x21070e09070f0f030519140319020c06090a21051209031618153b070903060f060b0711010305070203090105070b100b0a0504060807020a081c 62
    0x54500907040201c0c1d8081050712129020620102c3e4012904113600b55126800e01d001c00c0c00d61800c54980303a6000c2d8000c03100d0102150b00c0c0b0030007650000c06227904c10a40e00b524081d104480400840b80242d02d1119001030841c030050040c43e1031030141c0400054266a0150041256030b2454546000c48101c4034683c40080345024450400f0070509004689031210042000d0401001210800c268183c01300b2541d2a514081507210318003440e1806000d500311750102c0c414190b5880d03c043c103c0b402410b0310754804104800160f0829200b114091501603603284031551954450070040c111074407105940c15038900000540b50000801040c580d80f0070b000c0c1911261540c000581221300003880306065403c204084911070ba808821110703d01e901c80b40d200465141c1c02401c03c80007401c0e1300700409000c13001031562907103504035016000b01c0b9034542d43d80350180d40d2598102d0b114528007200411030b0600303120109020600305104c5044d8014050001030201592002c2101d8a000d5070700e140e40c91069 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788440602 1250 788439352 788439359
    0x3040204021b0a110d0b0705072d0b1602031c060518010305100e0618030702030604060204150219030806190609060f03020c0d0c0203100f0204210221070e0907 70
    0x40003406030220100d9143da003585032030b04c42d40b486e480010700c8882002030000d540001c00030304c041d0404503844080304940203002d000600301c400c076001c4d800c280c800c0c0c005000050850104a0b81005403400940c3c040c609040200d64541c14640d007008010116076241d80000c03900380c4030003445008800540e50030060551450a010742020140152810160305000d83c101403540005203c54000d04059034030320180b4000f02c10681903010f03d03c4000e50500a20303081c0411b111154001c2c0054800d0b03000c0030700802c9a0000b050369a0ba40e0401c68140403007aa040b1203010078044c3c1480f9601610203066098202541034510004030a07941060021850307101007407040661142d0320513038065103410114548450101443e07565680302c81c10303000300301103480030303408641f014441e82807942e20921050001c403900c1c1100c80040d410500404615000c420101c01c1803102d01e40401c0921600030f49600301a043c811040c207031000046040038002c0c450403000280c020884076420380b01d03640450207800c05508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788441852 1250 788440602 788440613
    0x21b0f0309011209020d0b07030f1103040c050105041208090a03052401140109050d140601060201021804052505190801081615111606020604110103061a03040204021b0a 74
    0x4030f00002c9281c0c07500b41d070440140c541d44211003200b50041d06642e0b0990300d81c8400c03406800000e0414100c0c50500450f0019004298081d600442c0310300240800321382c9032001106c65010320b1003102000d94290f202c0b8030210318aa8018032110401600c8000e135582c40751035003482c207002c3c07030603441601d007403481900d2024110076165805099800f040f0340210000c44002484003e050041c03c2c801c40ba1244010300b0400124000c040c606520005d0b200d2541c0e403500064001c4d040fa0013400c583c503800c401e001c0d006182c2845424403540034011100184880c00c00510240900d51145805100d4204800d404184805420410104c10365803410003940c10f2603032050901103001c000c05100e17400c0040c02e001c203003250320070b40001861616001000103000030240785041c083d4510b0406980d1000d401054143c0d01085c2c0741d01c41e40c0505003600403d03190340300440c00c591084c440d00c031511641c001c0400e407905d08a0021504180014009410013002b0000e212010403c1c0007421072980c0142030301c0e000c000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788443102 1250 788441852 788441867
    0x902030601090f140a0503010213090b03100507050a140a1209021212090406051f0c0c21050f0610060c030903021801080f0c0603010e0c160501060603060503160504021b0f030901 78
    0x21b0164000c0d410000c120705c01c00c91640c61801240b065580300c02d01080582c0b0100100400311424810900c4141010580540396900c5446c1c7e000024541854000c0302007e000120b5090720794580d911544a000c0c13507804402400b2003901260310070020504021400c100f0802104030440105105580f2100b2008000c100e0b201030340042d01a480401c40c0400041207a01400c04000183c00d140203031100310718005205107890f4111606c3ca0881d418079002969141e1455159a81724104407800c5d11110950316664000c100d42c248003403c0710000a200075440765801b00100d80c03003410f00422023138072540069503041c80c8035481c400050144004015540342000030411414007800506185103007100440c4072032105008000c0b4010410001c280b0070414030007210020752520080d035090114928060303029240511580000900f04403001c01c0f14940400c440100c042041c6056004030314120903c000780d0843c1f84281204003c040200700703000781c00d004540e4281003942c065683e6000b060000341c40c03072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788444352 1250 788443102 788443109
    0x90c02010e0c0f03070305010501180b1206011a12010920070804030209151e04110f030a0c020f0307111302031627120b16090902030601090f140a 64
    0x580c100485250311074004503061402d01010f0302e04000b0710036900b011034641056640010010362a00000086d00181091001c01e4091100010300c05400d0300400c02c01c19007a00e8101000c140c0000c0010000c103603682d924000c9000262541606222080032007041c4807609078400d1083d60349545036080c1d83e07103450114520030f0710300068081c20f010b001c2e02d820030039005500009008140c401d020039108481c00c8501c06505000812204030f9070110707240c2d281c20f8900c0184040c00703282031044901e00313403e15009464800c180c12130b8860460355224080b00140c09081242410340c0a814440708600c00c060004080c034a020345001c4544442000521009502490441050f41c2c4180184482c14a240c050440088018a007034031140c0903480c80e400502850721040103407080f0402002883d401a00112203809002c1d14031502c45566000840d14844034403c0c10340001402031000780f00c5680182d014640000061415005094541000c0d102620154012000c000340442d03030220319141052105019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788445602 1250 788444352 788444357
    0x2307030b0c0a0c0809030118060e060a0608030d091407030f1b0501090513060b031017010207020904030f0c15021207030c140a12020307050418050f010b0d0e070b04090c 74
    0x81c8016044014048941c031000100842400100a07045d594250030007035034920b0201400c01d80c0001807600800404103d102d54115000d00c50000c1c1110340c041c1b0a86044175215400786103061000002e400003400b009108603400d11000c4622170450030308100c0300c1c1c09103102d80034407000c03c0000d01f014403246240811404c109900c10500b40f0490368045020b42c2100c03411350b06e031072603000e16290400240c074864000043e803000100c10082c00c0034200b0f031440b08480072500b5864900035154642402d038402c40001030b4200800b400440d00203440b030710945140c1e14444c80c5c0094290345582e1760021000290003404401a000b0403113081c241c1e035500c035050308401141010016258100006000485441c560024201000c02d100f200707140901c40007094640c140300215680c1ca48a5400750030341d001402000d00070710140010b40f66001082c802d143c0604803a10916405038a40720811201d035108044c030301540b5465070302c41b915009041218134003404031407403201d031114140002c42007202e02032120b035804c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788446852 1250 788445602 788445607
    0xd0b0319030903120215040809011202040308040302060f0d050709060906020a050d080622020c01060e1003080f0903010e0601060e01090609120804051507030e1e010c2307030b0c 78
    0x9030800c000208403130f400702c038203400003106940070307800c00451017000c5100100000c200010440068002c000b40e81c0d0980f5080c03803440301303c8040c0c0124000c50100a028042c00c00042c005490448094040b1030404c1ba126898420b00341c003000140d650555400b004240101c400b44585508270100c1c01c0030740418401010441060349400359540702d502c000d601484912004118030ba02c4500d60003910040d944e03616000300c04181391450080d0300540502540e540790200106242d102440d580d80070342c10342103504021509548030324407242d0000d0300ba24550007003000b0038a0a52001e008008802c01c1d00030103012550324140c0e01900d20361804007032a041180c66007050017469088500340c0c00b61844408408002509841e001c003c6214a40005034050b00181080c0d011200841c010066584a0303a41c0000b5180381c601801443e0401d00000340300003144000850303543d4071418108600d01c1c010364000300d80c41c001130300420781d01149070000841a0003c1d4414000c0c0b03d4000750898101d02d0247d101407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788448102 1250 788446852 788446903
    0xc11010e0315041721060109060c030315030f06020316030e0d0309020a030206121f051f090e0c0d0b090f180111040612140702070b0702150d0b03 64
    0x280c8a00d040980b4010648802d4082010300411801130460300c180040c241d9030300d130756040303003011500b000c050780038800f042500000d0780551007424013504a40d81c54841342e00700070707050703806401900b210b10280710001c101d01d000201140e140101d6031509401124016603d0a14444024618003800b1041c0241030500d6500804140c0c005050444500b507440c00003021102840020880360303003a44040e41c0020003180114440076012045802000d1140d550944107000700000030010519208540e440242003590034003403c41c02a00c00040c80c104d10740351080c2d87c0c8500b40720004903015900710207002c0001c101603903600014031983e260307604115151000f0f40b0b0849140001076000500004109c14980c4944020410075004402c2000391001100d48883d01c1d41c1c4000c0c10342c920a03401d510b4941c205004003851261145032907016110744c5d40900205c60500540c2c2d1090390140743d080360080749640c011401c401303200d8041c00700c00302450300119503484400300301340c50110f4006003414400000c88400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788449352 1250 788448102 788448109
    0x90303091b0f121a0c030609090a02010206010b0d18060204080d08060306160507052a0d150e03041d01060305160e01211805010e01181704050604060c11010e 69
    0x580841c1c9850100e0200c52599140400c013501036040802c801140d40c0051240e202d1070f035405980b05600544000708641d0703d00c0490b981d203e0707028401030b0260b00070070014020351030924024800441c1c03602020540c1c569200c10b59504c03000200c8151000303503012406000102003882284907c0c040d0b40340082190a25000194036205d024080d8081c0f0307140040388140030340c0101c040d51801ca07085000d841010109607102c044014008610342015924000060301d07038501811801d0320241c0000040240381120640341000380704150500c00d09110610002416104440c0000141000707040841a15490004060300740c40021300700c404042800711f040784800ea840005451642d6091a01e2088520300700800f54100d15503549991500d81440d488119603d441d00301c2c1d205181c410002084000c11010115088030103071691511415003452034040820780c403240d001105543c0382640c91500b9600d6000a03000c2c2e005500003004500028101c5051203e00c121110b00d120342170801502103100500003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788450602 1250 788449352 788449379
    0xc0e120d0e0301020406210612050606030105070c0f0f020f0a090e0105090f030a0503070e130209100203131206020d051612060302012c03070602011406040606021e030d090303091b 79
    0x4002c204a06814907c00c0c8611500448010302d000e0000e04165845403d19a07101d22040b04c1240c025070808c4003003004144074500c4001c0d039981261140b80181083d5480d010040078120b03050360320041710b4900b64142c1d5034808405004280465000800a20700d0341420f0035650001c0c001d41a54001c00c56172041e40d60084204c0344440c0261404035625524804107070360246060507003e81101c0f0070000300e40320384955801450b940a084070b40d01c200100d46c001c02c80c4d6a01ca480018400300070843e804001511503c0c1c0042d11052160030094148401152420100c0d041119602404007040d0700c3d5594007a004001c003015001844004d002c035508640018042d50b8040031031714a0b00c42c40c880c1600003100101072a0445c1e2038014252400350b540c4040090203440c1c03040000f80d4010507030020501c1450584a020111030b40c0350094070750f140c03d0003114801c2141d90f43c40c18041d80410440c080c00c0f004144201c040b070074400e0310300080c06c031014106041c4107164184a480032041c006002d000480b0034001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788451852 1250 788450602 788450627
    0x5010c020a260f0d11070c081e0709021c090308100b030c0315040906063203070311060c07150809031c0e0a20040c020303190c0e120d0e0301020406 65
    0x190f1590341c0e0b26102d00c003c024404200890000d03400070841801704825903102c602112907170001c56810b004591000301034034010441002041e400040704004005480d00541901542e00304940d485c1030041911000340c03101c14100f00c001a96241c10850260300c4041400b0242400c07804d0b0f1360079840c000c5811889844050702d14075003c6201c02c80b200440c1e68542240100031750103e0b0612070184d48000f00a00481260610f8041200c521140d00114802450800d43d010380107004242c1c2d645076403103032040180c01e208500d40240c003c000740300c1411410041d10000307044541034a1016408020000d24100010300880300380d0b0400c114101034a82c11440801d981440f2401c0060401c810014140c40c020203803070020301c444c0410030342a1702000310402141e0905400d54051199645010040703850744021102ca161104003544000e40901059110605006030781c203080092004070400940a0079202c4080c003e06e5201d0704016a00940c4031060080600b001d50080d800d02d81072102c090319a00e610704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788453102 1250 788451852 788451877
    0x30f020609030d18120909050703110304020f1f0c02090709061d033406092d0b030a150501111e03040906030309150203070c030803040c0305010c020a26 67
    0x804c01800140e80f0a012140e283d004e4040c000726503049001814804092058280c141d190400184685010f170103028840301d040002d540ca55513076a8200a210800c1035140343d00310450b561070075000382040000085004541d200e610603410f1030b1040002c506402440c0c00c0030032258030700030132215410402c1200c402101052800c440c0c8039a201180ca040740a80c890b0004020804030180131100d800507060034a40f00c60915503084d034450505407482c2000344600e40300c00c420f12000c50785030603603600c400843e00b14110210343d0340c9586a01c02c01c00c0780c01c2591050f06903551402c421080c0c40d8000028801000c3c20b0078036141025803403602545840030f821400c03403203018402c0d41c1d40f0102c4060003100e003d0000040100a442d81764140103010b4119400307810341082c00c6142c5a501d16000005031502c440e48000c0a5454a003156500348075500068401c4a540a6421010000030000c0c00b900c030008410354000c02c4080440d00300441c100c1c150703245252858884030118485c000c1d0050031202c3e03140064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788454352 1250 788453102 788453111
    0x180b0705070c091e230a0c09060c0f05060103060c030b030c01080a09140601030803241c050316081e0405092a0412171903050a0b0406080307030f020609030d 69
    0x100c00c1e48501102c0a81515115117032012000f2070048035401d200400007614148176590790b890419031700701c0d100c180909011078062402000201c0c0306280d6020b034107120340f6a91254060a03078680b41340040a030001ca4a00da103401c1508543c80d4148220315003038008034002d103400703400300700003914601000d084041440d840344891014412080414a000c1c0c90040c00c488156943c2e04002a06410035034a000c582c01215140300151420b040060054001c01442c0c1043c00c1c2c000303080c85200d1304d6583d40498660209112aa2103609000041000c0c0d6000d00121503440c04201010100300c3c59900002c81d488105000500031070b1564915158800c0000c00c540c11000c09214101324000c0a210022920300030014003c190840407003920550f4a100d0031680d0000140001c8120150180200f0120030382d0940c4110f0540a02c40d801c03141d0465403580300001d000d500d0b0300119059800d02d420111040c1c1c0b00041c420209a40415815a43d2049102512042c140315000584a00c1004072006215480303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788455602 1250 788454352 788454371
    0x31b150106121e021905041a030a110a080105010306080a0b13081b031804140a0906020c1b0a06020a080d0b01050d140a1401080d120609180b0705070c09 67
    0x7980c00042d912061607004004070f210340401c80041d41c02816000303448483d0b0000c088559010304240e500f503c903c1c2d00900801c1201c0d0a1320a6250801410ba015003615514040245188200105040b20083d5a079100540c18800050190b071402d6000320907075030217840c0c00c0c1c0106e150b41e007100d90889a400304004482c0e030b550030000c681d8000c25002040004036125051030f880400001400e11305042c540120504007544100000c843c640e48602000c4109080020000d080c6a84000e40842c4500c40c01400c02100c100820302c1c0007082002c012450058886030307642c61a158002900030032261000f071801d078920390f9640006025006851990701e841d181d046400342e00441c25616030805100d01005140d40000c0710003a84002500e0f103007585840d01c4180b0800000b4008541e060728181d0004220040000600f154041c2110070035030304056a51101090b0381045004640c440d614045150040100c2400d000c49040e03000780210042c420b041110400041410301804200d8103a440d00203004241d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788456852 1250 788455602 788455637
    0x603020f09040219030506031c0309051c020f0609060907050121021201090b1e01121d0a0b090106060207030807081b06012607150212040602031b150106 67
    0x5408207060307000b0300110b442000d10380740a6800101c85500d66050000e5240d00c400e2545a0100e0704420203602c03900982d50403070314000e803c0203100520980c100d031521200305d40129100f0300b1501b24900103820034103450189400400c512600020850040d02d041d040a4030b40d01c1d60b803109407140b00e05112440541d0303801640d0b00d01222410021401d819075130303818501e1910325156000d028071804945040a1305816090030929242080e141403c4002c00f0400000103540c4401082e03141c00c861500c4000e03402072004642ca5182c0c41c0c10210b03004154004007460700c4159401c00412a49040c2c0c90b18808109045c0cac0010020200c98018119070340d16409420520704070700c1105c030302c4504e0300c1c44500c8100b800100020083e049a514402d6401c159450041c04195201c120301c0c46c10041d4014141407014201480a507824070303005004071a40720190ba05040141c0c4c01070307800035001d07030400f05030003954101200030240b00420039806041650340764000d40402c0c403818003489081145100082a0002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788458102 1250 788456852 788456857
    0x6010509100902030c30011e0807030f050c03060709260a03023f09030a0f0f0507060c23010b04020c061b040f0303080a0b060d0b09090303100603020f 66
    0x9569a0190340d2031414030310f110b982d90300038175006c1d40010250b109401030400307140940298041c801c107800100d9103401d404c50594411110580c0f034110b02d1010015460300c1c10030401d0000e500c1111222030000145c14454104100d1303048581c0250003000c208081c42c0d502c089034400355a90740c85807035029070441401b0003074000b06084000051055113110300078150001420152904c1c60244140f2145a000d801c101020300d5000044286100216000b00310540c14040d290b10301003c0d00b29809100651034250982a4460003907607210914001c00080c80810712200300604020b090071595500c155480040103100742018901d0705011601c01d4081480c01c3d0410610220b005200355202d02c000d06941c0d4880c0c90a0329007104001140c1c503014207196040040d50b00700da465400c0350048034030b1601c2c00c0d104058010a030000131559420400a642e03a04000381c4000d0700115000901d640c030000900c500d03510b0150a040c0981d10600420604a0a940c21202038034842e10300036071a031085034070703234106030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788459352 1250 788458102 788458109
    0x6080a02070507121a0a0c09050d02030a052a0906010c021003150605040f091b11100603150506030c0609040b061201090510090903090918050f060916080601050910 72
    0x31810002c80b4070900072400a602c00c5c400040f6250011501c482c804042222a00325241c4c1c041808040100013070b1604000100280b07001500b41e800800041d5134250511004000010846c0d1046824466540e240280c0751a032910540301e82c149410020300182c140045001d000384105031041c1c0c422132051084d0407a02c2280c0b8001d0301d502c06903448080250554105000d6840c0070a00780900094004082c051030726000707441c0001048401c0340140c100c820000071452004c1d1032140c4000720003281d150b0b200303040040d03000d40139040e00c40141845410035204042c116900c00e030f1295191065556400d000c841180c08100e4000505c070f20301c2c80c0071070140e0003040c2d12580540c46c408000503590702542c00040c41411203441a1000c00d03100c8121008981050b07070080c00080c1c04400c18050503c071179000750300007018940e0421400040d581c880745420003804038862a90445024092307000420454030700a811b040301c42180050402e03840a64a81c41403088900c91010200400c000010010303205014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 788460602 1250 788459352 788459369
    0x206070c08091c110112140408072105040510020d0e0f010210090b06150f040b0306060412030f02120c032a06011202010906030515130e030c060109050a0606080a02070507 75
    0x441101c0d013042402c0603000640680410200c0700b090020806504c10700f00c1e01e080310b1060204036140c0c4c0c2c850404680040708100d85c420300c210009a07100e810101030000e08a240da41d01650b8a05103420b0040c100d44030302c06030b0299032155241744c0a442d0404c1c494500f00718144c0c0d40306100c0c1080f8004074502a003007090345986510b03000b081000d102c0044178203481540c056803141503054421303071440200d01c5024030040d01c00401707010521010b48000021030300208010003050034280c648490000d0075018140840c00304000c00481c1007081d03010b10404002c0c000383c03203125040900c0241804d4503440713160078860310411440750141600c40d807892601c0c0e038a0790800844007550703114507840302c07000081002030b030108031401d0740092490310a000d414030400c05082d44001034031100c1c0c248000125000030301100d03903407194109030b1140010000b0b042031000b51401404070703501d400c28000c04ca0f607001d00031000039800d1200c01d0100e0f503080300c4006c1c2c00c40c42c111001695402281031250414025400c000b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 788461852 1250 788460602 788460649
    0x9010605181605120a1a130e01060b030c030a09032d0e0604080a03080c040f03050a110418140f0d0909050a0b030303160c050307080406030c081005010c0c08031201080d0206070c0809 80
    0x25101c82c7e41d4081c081d40300c0c03554020800b0686505004038a800111750303040b14000100002080030705c190b0041d44600d842400d0003040c480070324004000104020038505082071603452700300700140d8880b03058503980c1826244140f0341070030700d0341d0a51540e481d5030340a010700c00f14002080a8100200880b0000d041c950010307030303180391a860800d13101c6014550540f0010a01030107480701d03192500c68000c501d184004400c403c602c0c03a51b40d0100681c1c51807400e1007a401000d08030701e07100d8030510400b038060400e5074030f40038060700380080b400442d10054201d420003454002d8540403618000216a0001019080d82801000c2c0c24400c07680789d00540c81c0240355000204030312040007505070251094800d1601d0038030140c0303030390a01142da006044450a80300302c0101ca08110a5014018065285004040405900380c4a50500349594002d5000441c0111390030b00400c080321040c081200c050441d03101801890600b0325009003010200c0c440640b44242c0007481182580d03a010307158041141c0c1601030403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 788463102 1250 788461852 788461879
    0x4080304081c080f0604050702032701090803040503060103140a1a0a060b07110f150c0604050f0f03041505040503060f0f09032109010605181605120a1a 67
    0x544400469500c05590030711100700c0c14605000e01c64461040c1000181c1e0b01132a507882e400c0002908000d444801540000c010102003007001c441100e81001004517900030a01c400400140345c0520340d0b00c00342c0545c0050005100b540c0d00402c00c10f044a801002e0b004032540b800c480d49003041075001d8010440e0580d00c20261004140c0c0050310720690390420100900740e0b0710001d5083d18811440010714004a4581f13080452400701f000420a201c080c101c40509111f075140d0143c150b126803400038090344010b04100402c541001441e16991f100c03070140c22640f00401906969004501944049061002085003164400d40030398004203001000c844450030030b4600401060b8040d94010a015181000900c101100204840400c1641c0c0a06e410903801c1c0e0502c80c18516014140d9100b0395200e050024003a42c5000590607800c2c3c0b2030103080319a081543c0d20541004121601e0001e0207030500c0320f01c1800e08201a815404441f018010540010414502c180242d010365160390000c204000711 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 788464352 1250 788463102 788463119
    0x1b04140703050114090421270504051e070e1302040b1902031809060f0406151e08060108040c0b0d0941030f04140102251a04080304 58
    0xa5040b0b44c5607580030602d03860041c05100ca0554202c6014000820b420000160700e03214800c10003099000d480c10401a440b41400c07100d129040c1c000d0100c06000c1484180618034040c85019009400c1c3d00c0c20ba0002042030301c0c0c18550070310080c00c000c01c2c0a07115800711060b441e40240e213518080c064004540c3c458450300180748981100c02585060607a038103800d803c8900000440d04071000449030b00705850711142c01c1003400c200050802d600011692800603598496016510280401d0b114101d2080a01540100390700240c2410300700000020400c2241d0b660030660341904040203180c00401c03940c03942400c8001920b41d0748078a03082240002c040b100002a03a0150f4011032013010004162441002143c80d944404410382c00110045042907140300014025143c40303039203030300039241800501140106550010307440242d41100f1644044141d43e4180a40d0300806441180600140f034500490301c8180c40c00c1c021240d1007155880c2c0444030340309031401e4400401c05c090440360703203a48a0950 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 788465602 1250 788464352 788464361
    0x605010311120304140d060c02071a041206050402041404030f09081506040e12040902042d170304030b01120c1502030a051c1802090a0e1b04140703 65
    0x96030400701c5403924000c28646144441c03140c1d10180015818503090250021011280711300c604c4d40048045403010002d0004e00404100f01d6068000d05200c0c0d00c0c20b2640072880100d1040114414810401400b07101f85151070076200c0384c2c02441c0060280d40b1840441d0091485001443d2140100070801041650000140c88150080e42d0340c0d0001951702e42140d944c4080d04500030805444600001e41c00307040951080c42510890b4089484060060a903e0616409034001e10f10494001a0900005501c05a4900f81c0b140c244c0400b01d112224000003050a039150090b03121111030244032130b069001c01c2003610051500400109507650303413600c410098001d182e5085440c0f440c04240003034840c564001020011840350041e40c45c042c020308040710903a20504c40b9900c10a014290030010200a100c0c040800c0d01e004030010b40500700e80100328000c14010b009607045070030320905000c030300400b2a0045e03820700f07006417040080021400140c0030300f85c40300300034550015141c1008000f6515812 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 788466852 1250 788465602 788465609
    0x120504060504050c040b1e0d0209040311190803041b0b0a02060f0a05100e0406090b0106050d0e030a0507080d0902030f03130504060b091e040c0f02060c070b0c070609060504060501 79
    0x813140d08040c407a0901044e115440b01683e4800c0600140011801c5020907081000070004c0580c0d449120550000303240540c00c0c0c40550003d4111800560302c0d9008000030f16408c07010035100113180489036684c100034800240018101c00c02c2c81c0050040d000c900240c8409820301c0d01450361602d50165009684520440e44083c2891100307003ca81d011220744541c42c000c0c2d0501c50680b00c0f19080081d04514480081c7c01101c01940d14081c103404100f140c220345000e4501079848541d43c1c180b9201c03100c2551034240e227400558004101010130365800400710340001e88d00000194456101c4840d42004001c1444040e4040c0a401800020194044028042020200c20f06498181c40e00140421600140200d000740c100c1042070034803038601045034581031412601486ca08048a034080340644110340d02c48004a040c00880303109080c1c050042980c0100c1c0d90703e0003410a02c240d2910104000050305100c002c2600107030000c213002c0c19400505a150b0042c4040c0400c1c1400d142545c007c0c9801d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 788468102 1250 788466852 788466863
    0x30b031c17010506090108041104020a0f020d080f15011107091d0102190c11040e060108240403030e0a0c0b0405090f0402010c140c0d0506070e010903030c030807120504060504 77
    0x401459801201e007121416107101510312400c10102000648600c900540241c44010b000c034007118803540c9500040001d15003a554400b645408444040d183c4031104414400b48100f50040050422811150075400020001701c0001e140d0307003030010703211015075640e5100c4600640d4004281841e06403c51401c000080c86e282020f4000081c80f6400c034080d00c0c007440c120300d04808007640036500c103000e000f1900780180810601740b60b041c00010216000d0072008162500000700420405009001c1150b2090740c0001981115081c2000e0484c4400300130801414540d40e100c54980e150810020032030016401000e20741d401da22580b0489081c3c22506c00c491051000c0c0c4002003004c84800300c054003407581a19022a40c03a140d540700001c1d824030303a102c800300340708410742030310140c0d5440940001c1d02c1c01440508906d043c059001031242d0103595100e8144007031607008200113030740701041d010941c4d010300c3c0c201e906407200345003204d454181d40091750050703080006000501072160b104a0045100e0b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 788469352 1250 788468102 788468117
    0xd18050a23030d0507151805070303030c09120f080c031b010605040207050a0212100c030b040b01020606100c0303060f0810051b120a182319060c030b031c 68
    0x11030401d55103c0c940740c1c0c1500024030601081d00000e00803c0b1012003010006000300da0203614802000c40020070700360545041d0311251040003810f07018450909102c18502d4102c0c0014100950020811402c0200402200780401e40e6020700c0758541c1951030080300c0c2c006a175500e2110240c03030f00340d100d90b42604140a5203010000941d5103410710880e480d855101016100d885816001c006007038078982e03e0100d190051501d21b48444406109001844c1e0154400150920f48030b4180000c4440004440d415580b0840c2400308a0380c4952181c1000078461401910519652a0032000780c003440e40101c0800400250202e000680402c1400c054039403504100003035500e602c449140c50601c003181d00107850041102182500ca9000390301c0d80318084400110350305480b040a1040c1005000b401d558244420a0030180c0d0b46120f0803e400d9103a105d0018400210f00d641c160301c0b82d0399075074002401d940d0350703031070400c03555009812581c0110780041c190b6050b5030700645280c846071005a140000078028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 788470602 1250 788469352 788469419
    0xa1703130608220b0c0d1e02070c12030903080a050c0d0e040f0606050d0209010e181603090203030307051612031a010203030c0d0b150d020a0f030507020d18050a 71
    0x540e0041d071111038200d400020141c45c1c10b08800c50700d510031a00564a20f413100c08508810010030348200a00503158001130b40c0f04141d04210500849a40212100500d101031550202c1e920281d01020b0300c2c0c00a2107903507500e016070b6050f01c03140b080140800880c0076800c080c0320901e4018950341075280095030140f0000c825001c40c001141c15501410010540c24440509280b0160380a03001d200c1d018100069090401c0c00040e07400c19000d0ba000b81102140c0c001c201d100442800702c1c51042605082c1030103041400da00280e2a408010181410004042940768122010205a1a086411a048030042e0080c00401000340180b000800800900003101240702d502c00401c8a00c0f0302e00011070241070403aa01d0042000e032218003001640000c0300150300e403882401200400c0036080e1030800690b0380340c61079800380c281074441c26900c0605240008100d80141c002c00c100c10345a445140c9030040d0344040c803150400720140d4000680151501c80c001c92944681d128004120300400d081509c40d412 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 788471852 1250 788470602 788470651
    0x603050714070302060c2b020903010e0d020c1e060a1106060d0201020a0f03020115080a0c0f18050a0204121b080706170c071a0604050708060a1703130608 68
    0x180b8030700140182c1c40500001c010440c8034025040c0c200101108110b1410043c1d13020780b05506405107407080d82c0d400500401c0e01d1809205002402825501400f080ca122481c06500d4051401c21039001e26002c044c00c088003190444610300e022070040611751074010401006289003810610100b407031103880040f074400e181040b00b170035a042d4160300800c00310300c0715a02c805a40e914a0002c90941d929041034840c0b000d11142c03084042c0c100f95004003040711260038031069081e0b4661184944003191300087c04108200c0c3c10740840110081c10104054544544010007171107030340d10010092092090702010800c00d412285a55003031304000100c603940b00e4901c0d940b20001d034800d080105041c0c417010f0498404204615901501e00303540c05007030822546940203001c0880c420a2000c00750281048080d260510946401013024a40441546402000726140309000e002d841d0014001c0c6414802840e000c1003280c08000090403002011640c811016101c41c0080da40303640c01d015060400203030703d031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 788473102 1250 788471852 788471857
    0x21c02030912070503041d160509090403050702030a0602130504060e01080616020a02060a050301081005090316020f060f070b13080a0e0f040507090828030f05130603050714 76
    0x2080740060042e0a404031210003980c0e00540044900c0c0c0010700000500a0400d88004d440e07503c181400a01443e0908100a1008001ca2024180a824060b101841d03c4401d48264400d42c142840c542d0b9049500000380380c400300c41c0c00241030500000340100d81001a540880458809440034002079807110103011040d0001d008a1000350320a80019003090300101300b0400c260700500545411400d01c2e000314590341d000080b00780c081000040104100c10741040300f04080705079a4404c00a604040c03c083e520781c03040c3e001408189415004007425980d40c17807944403d28000500140e038400f514465200c298021400688020106000190b800991030581c072083c1584502c00f180b901460071420782c0c0e0101c1c940f04098114900c001114015103030351240c2d500a80f03603a00c46c80241890254400c1c0f50020344a60055180c0c454151002e203d1402000c441d1080d0341402c0204242c421004e0458503401102406803160780c2040e80000c00e25016400130740036a00c19580c0c130081c102c03400696403462 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 788474352 1250 788473102 788473111
    0x6120a2304080f090a150206070924261f120b0c03070e1822020109030b0a1b0302030702100b18090c100e0a080609070e042103021c0203 60
    0x61404101d4010f100061000900c0c002e64000d000e0300d0b001d07403101811889826200307032180140c1c0c428002d000e8069040742c0f40e4030081941c1a030300040c0000206001c603244440304104014818924660342481110b00f12246500004c00200142c41c41e243c185c40001c003400e40c84404010365001c1010480e03544035244450b2254000b96441e21503140c600c40710856074001840d1030204201d0862018265485074101d444580601e465042c05003040d01c0314641d46840d41744071210240c1c14000a5006076001600d43e81141d801020141d12640c90160301c1014011440c0111020103081c003402c5091a0541d010714018070143d805c95440b5607104001008503440103401d00d60081c40b0f070100c001201c2c154144c1c140d0143d1804203441e241215240468000c0d840300d0171540124502c400c00c4c0c480350030812038050003000c842d030041c903c074109050080d48680650181b00c02c1043c10000181c103101980c14000650700000500d00300e0402400390050003900441c071610b81c0341180c00481041c1102c50f000f902c2c001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 788475602 1250 788474352 788474363
    0x303052409040302012904060f0e04200d0b09060106050a0c29010e0a060608010b121b040b180d2102030702030a0c05091b04140f1c0b2a0906120a2304 66
    0x2f07486903200c0890080104d410f50b04400c82c00c8100007000d84440034184250341c030a902c12179083c14858901410b02c03030141c0240080020070700404995035801803c821060ba0000c9a98100341036a6081c001042c50410010a40c040b02200004900e140402c1c1e0310b200e00c401b80800c100290716514200c480000a206105a541062007032910008070b21000c0c0350043c40c1c40f0300e001c04222807001c0c040b900d0f402c13650081009a03c04120482f99902038000c204c2d00b400111800002c1c0e000e81d0340c031b104d2016003800d50320319210414240c1602090003002100d5005070014100c81010459140411110700326020313150091001d0004600c0000d00441030840150a8520660506003072428048c1da4170301d2103090640c00040d030303401d4407042d44445800d004180e0f107907034000240b41c1036800d00000e0b40750003402429220a841410fa24a0524080641ca00b450002c0c12070796035105100c00980c05000301454084800600002c0c8801406941d0068440304042007014003a20101e00d0b0044c2403020845000c0c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 788476852 1250 788475602 788475629
    0x50316020a11090a020c0d03060f08010b061603090306090f020f030d080c091c0f02182404110a080f0702010c052505030d090303052409040302012904060f 68
    0x5a20308a840c1c25030003c4c51180050404010350601e0b440c0401d00801c0b500030075520f050900401c0d600c2e8601c01c01420110703000780700c0072041d036000c6500307442104c2000203150744440130b0a04051040d0203050055410a5083c0a19150340c20040d500741d8110004034455071100c50850154100442c401200208a44072010507030344070501208242d002c0c00c6100c0d03002c000c41600406080d20040914502d85c0140704d03a0401d214a881031180d251040b101c07070400d010390001040200004415040c004030b074608181c407004840c840c0418007825581198106040f800708040309640d50081c542ea12620030009011544e40340e42e0011380c02c0398800d40c48000062002c0007403441c4440d90705140c903141c1088034182025480142c9445085d03400082000c00e401d61186800d5003810f5040c022075400002040001c3e03500c0e00189100b00107204c086140c035020300098000542414000e50112640c84ad45040144258054100c07400458036034004240c82030f480d103000071030081085001c2005403103d41c101c000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 788478102 1250 788476852 788476883
    0x5100305070c0f330c09081e0102070f06021c021309110c010c080106020f0c0604090f09050d0201020d0f060302030d080408070c06030209180f01062607050316020a 72
    0x241c541001c000507200740b00c214140e24a955240c500c8140f10451000101e110703504400946415140c030041c51401b0803000b40c0c0140104540450480110b21407e00039581a60180c9842e40c0079008012000c0c1620146010320000d024040d0003c01050031842d020501c2c4600f0140c0d8403080b8010001c061414403004c0300c041c01070180c1c540c000303c00302000008180c20000840b0110f0b00396546412600f000580d041e004001d41501005140802c052000241c105610341401088a0340600c2c070495210f241c0320500c0710005031856000940150700b080545101c0000c45034041d02039885106550080c62034051000810b60700c912a0a09982d80240506610048040c040300c4010003d0010354212a08114000005400c0b6900d5802000540c6001da202c1070a402000001145071448051300c808030b1301000403480000f43c02c20b0649800b41003003d0300c0c050780704c10507088a62030702140c141200703000c0070b0020386500040594424645c0a8601131081c40100342240c6030360a04400401c4640b0485100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 788479352 1250 788478102 788478113
    0xe041410062103110604120f050c1f0902030a0302010c0f0c020306010e1905010905011401020102032e08060c040e0c0a0206070525030e011e0e0d0f020604030c05100305070c 76
    0x5600c032902a00d058004c429450b0340250030071000303607000c50f81c0340041d1402e0300145420500c01240c808150030140d0070b109804c0c40706c03031316480e91000180a000e1001d210307100b848003e6002d07102c01a0081e0032104550380503c0d0103402801d00085a0000c940380c16a10380145205520100c8910741c094050030f07031079107400ca00254184015000003120001501900e46c0c0c3d41d901d100c0c00d0f0003440100c002042c507526040103001c80055206400b03045900400c1042000152486a0120004554004c89111089032000e803001c104030741100296010f05d000b403040d0005030740040d0094582e11512102146c8500000b00403900c181c20304400940c0002c000252020b000b48050b002d90f00329801d00c80b4403405a0a144101103443c0b840840c0402c6200400da02c903545e000d100c9090446e00420740d1100c03601c170703142e0107009490300d824507030f00c1071a0f0400040100212418400400c40e405817026031902c0d00da2a01030100848d0340503681c0503c3d038021032480000d209024190180c41d558440704017116003901d41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 788480602 1250 788479352 788479409
    0xc08030604091e11090403080f18011e1b02100c0309020a2403020301050d020d151b110706050a0c140706050703020f0111160c0e04141006 61
    0x10036a2081e500c40006010440ca01142103202c444010b04000c159228544a90080a80300e40385000705100810000065000448150003a200b40041d05072590b0741e100b03480d0000c2c0703c02140d1800d5403c0c103c440b06080449854921100030a00d0b00380704500040c540100904550407040300141d10a241c0c200400d01c1607800040142418030700800d01440e6030f008155090b000c2c2d03114a018100e400012100703a00191404803006146140940c40c6500d80720014030003040c0000040d1280ea1403000001c1040000110313011031402d42c107000c3c4811156880a440c00e140d8488003c0041071000b404466800408110282a601c03d41c07507442c20115a1281114580209641121f0b02070366200c17100c2441d0400c12560340200042e5a419950309558a0002e04210100c051034202c0da0410780286800300c007503030560340d030080c45548429940c14507040c0603d40005507404910b40c0c60024041c0710078000c00d0403038180614820800c0320807441480050740125030042c0306070400790751540310b25100350000300718 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 788481852 1250 788480602 788480611
    0x6030a080a1d041406040b010309081e0c0607080403110105010f0902030c0702041b14090307031101120908040312110606060a02070f17121c330806090d0c0803 70
    0xa4618000e42c0301040c01c4903403064034a50300505000c100001c40c80c0a00030303221035003000c0c60103000e00b44032070f40da900035401280600c0b41c550a8074641c0d0707920391b00c085081d501208803120440c1c0007400d00072006041c0900503902a40000c02c3c00d858581098414005c440c12981c1c03040380c034500c0d24030b064607100007900f0203018801c0000e41000110701690f90b1b4066810501c2400316005c8182141450180c84444c052880242d42c040c1405050701e1503501041401c00c8030340204401c50700b82000700c0101c2d00148910501d1403a1403601090400340711b5998081c006884c4503132096440c4280032002a00c59034655040c40800d98800c80c0003034080c0c14014003408440d0310b680103c81d90561101400b01040340c1503000208810080e06c0640d10000c0c00b0008000e1040321403800382d02d0999480c07000c41c00043d01c0312046058940354604841d540e4054099110808264490440c2034481402e00000c0c0c4069403003020054400d40c07010640e02c1da8080340c082e0604110391614104800d0341d642d842441d4000a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 788483102 1250 788481852 788481887
    0x30204150302040c0e03160f0b0a0c1712060405090613080c150a0b06031b1c020316080a0c050d15080607050a0305010b0301030c091e020f0a030506030a080a 69
    0x28800001070303e0354001c0303039181102510303000c50050781d407028145080780d00540303120385e800700c6001000b9070352245141e0300c10b59106100c229a105000c0d40140d69500c1c00d0f4200030603c514040300300c07050350580e001034582d0465a5505d80d03440d0700c407a802c00080c0c0e981512001825000000800c0e00c410000d2403c1441a210361051402c240d54900d9035402c1418050152a40c19040420810303800e2a03803080c03c0791144121030642c214241528a00c00d850003400e0001d141007400526600c1131610440707070141119046105540e03905e0402118856010058191380102d40c1060210300c1080b01401540c9400c40039988040c107020102001101604c094900300e000f0003072800300810a8141888140c3c4509015101c40e81d8034100018004c017102c40503440348003020700502c0140300080040c111007088a80c02040491901d0300100b1482580c480302c00500e0109100240310840e8010300c80c06841400100e4a0421140c0c0c1c0303050074181c460f140c00c00c0c01084000304001ea01c010b0b03402100007281c0c288080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 788484352 1250 788483102 788483141
    0xc0506090111030a0e09010905091c0e03010603150b100519030f090503040614031501050d150311040c0e0d03110708031225090306202d030c04030204 66
    0x30050a44e405189000300145014040460600301442c03044d004054192013000185030000080d9180e02207035480c100f25424145103410103500c0303401d5410142000a000b04296562490040280c41401e8031820405013014003c10642c0b80298903103813074110303540700c603407928001100ca15001c103a010325031014959549803203131001071688600c0210900c2440115501c0b030500c000500400c480b6002408030240c20010041c0c3c030001807551b9000300d8028200b69840d50070b1001903001a00791450782e0804c43c01c4040c03002060103a0300f40801d01090f81035404009040f8003010868124080d2002960400d220305e01d030000280c40b41140c1c07100e5020300010380e01c01c943c4510102e070661303020710f0907684201500014404107503890300360001011000c0103045401080d600000e0070759142e074400078080c1d6540d94014117800000860908034107903128041e5a691081d60b412804c421248010041c180100740c01d0303400016070410899015040a020380c070f08081c6160f0070030018002d0342e0140410400310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 788485602 1250 788484352 788484377
    0x10f1101112722090503030a023718080f0a06150609140d02090a05060103050604061202090405011b0c0b06031204090e031213210f12020906070f060b0a030c05060901 73
    0x1d10180d80075601702300b070140c0c0e211946804180c03400145280039004003940006600700d01100041045a0042c40c20210317411038140d585601e080f0026404070314540110703110010380f014086035031822207110f514100040340c080412600784c0100b50060402281800906101e0082e4103001906c0c0342000512603001015694045517030703000c0c00d581c01080103441e007060101035a00f40c0502c540c0048155010410301d032800001101c040310180e40a402025058041001d100c002c0d084010741140366009060551481c2e10000c092411030041911a03983c0380020903420b02e03000ca00b082d0300c5286003546504050601c0c403550010116603540b4286403004224040f00075040b924018445c02c01c6140300d01100242d405d04d11401020302191818070205101c1c1809111f4001c591100d08076800d14081c0003044108040400900c5a5840342d40e1010b004140d140c00c011508418001031480782200303009030300160b0244002c400301c5010050106001a000740180d003810005071080280501d01489214071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 788486852 1250 788485602 788485613
    0x10f030218011d0612070806190303110a050d02161d041709100509090f1603020a0e0306010807230a060309030c0209040b180a0809010f110111272209 66
    0x600c445c140c5849082003010442d0891007007a40300c50159408204520500700c01c803252030181c040181400f840c0200d542c020101041303102a00c60703010040324040800c110b00a036407441058800c04c90301281c04000b1510b80e0810202c000100240e124004e11512142d0f03e007100e500c003102418a106e9004e10003842240d032110f91180640040b62219a80d801e820014404c0b128001040c02e52900d90030340c140315212040c004002007801807450300680f20190050100c81300c1c140150400d516220304d034004034840314085004411101034001c80b00c852507001005203103c51070a000e02d076001112440400031580030f84c000e8804984030f494007090400e210b9000400b84034042d10142d5100c005001002414034240800308210080c5c0340080c40000742c29500c03221144a2510303420304011640e03500003003160140d01251b00211000001784828100d6021030240b42c1c00c030341c3d01c1e0908000062074542c0c020010042070071000501912078241c024200b0041750041e810003844803002d0b5507854410000c1030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 788488102 1250 788486852 788486857
    0xa06080903071e060c0305190510120614070804050a0b10090c110d02211803030f09030d05090310050702071710060b04300f060b010f030218011d06 65
    0x101e860f1251140095401d10000b201c101141c054145481d010030f001e55803c001c0600d10081e4a90389010405580d10880c000f009480b03648511001016040004201b010756080580f0300c22410b0740c4500c499442400460b0300010075103010b4410342241c0151008201c110892a900c000b90141541c80b4a545d40c15480071200c070380d00714a00155641035000c00c40c801c24040c00103001c102d480108840c0361000d0200c0ca0b16080003c030003895542c00145200c41034244140c0400340180203040d203481d4001c1c1c8011400d280d00c02030349244240101d2189007140d600610640300640300180051031107404a994a600a0202400c90003e500c01c0140c0024080039050a1903082e0010001825414400001b004103a9031103801210700d46006110034800282405100d1307080112140c4070030b104880403d0a540c0380002d000014126034001d500d8501444005e404c01401c5240c04c0c2d880c91101003c0c110210228041c25201065960b441410001c0035031150110b00e55110410310100c41080c04031000443c1075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 788489208 1106 788488102 788488133
    0xc030603100b1203030123150904020c12040f0801060e2e0e0f010302031c020c220504050d0216030506011a0c0703030207080c0109050a0608090307 65
    0xe075030b07064000311a01c03000e2003541d0fa20b50b101c242e1750250240380e0003680c0160200e451b941f83c0504054880c02c00158000144900b80742c802800c210282d4041002034020f0311444054007e41d22450f4014801050100d41501d452494414810300f50f840b943d202400d030007040c40030002c050400b4040c058a150390030800c0546048250f01c0d00340d000c6410b03007188480c0c10300e54007008804d00e09001c4c481e040c0c074000c404507070658584010641d80030050100240050704403825544103400d00c003c220101d5454440da403800c2c4109a91040d084030000c5800365900d60000c214003890781c4c0c061001c11442d08240c02651201c905640302c0781c0e0798500620a800c0010500b0310888c0c204e40158042d034444036100400c1e281c80341c0e5a810000d503502002c0c0104c0a0a0083d100082c80e075600070402102202e40140000100c01e14109055940102c02090020103010812940340021680844c2e0782a2 = true := by decide +kernel

theorem cover : BRFrame.Cov 788309352 788489208 := by
  have h0 := BRFrame.cov_init 788309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 788309352 ≤ n) (h2 : n < 788489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
