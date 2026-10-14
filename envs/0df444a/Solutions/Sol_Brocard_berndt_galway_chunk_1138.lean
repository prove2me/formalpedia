-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:24:35.237818+00:00
-- url     : https://prove2.me/submissions/a1c474a1-e174-429f-8986-c6327d541994

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 204496402 ≤ n < 204676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 204497652 1250 204496402 204496459
    0xf15090d06060806070306030c0b0a0c0501060905060111010507080a02030c12010b13050d0b0402062a0a030f1b020f2214070801240509120d030f060e0402 68
    0x410104003940d1400c40c0003407505020b41e0003240308420016040345d00912611040e81c0e0044401c0000c240341ca1b441e01c0c42039004e0076401c000c009078043c01c8800100c09000d01b44c050716a4007000309051034803000050070074003d83d9160354103a04100500c164550000800da80000e24080056503030740d030b2511034800c2449115155200c0110020002541204002c0036040704000e580380130a440d035032101006080e4410807070140c861100e0902050040c83c1c0360004240441c400c800001090309000c094070312030340307204012180d10703000013560720105130740204690940d4410b41811100b804045203070b02c0610801c058001d01651031499000c0d4582e40380d150303001100b4a6503030081d0005a07440c00f944060042407007802c48035541c040204140c107018015450581d4010521030b01c0e581e58401140840041c8844a44103100c3d0800500b40301e51144c1091000c040321003801043c60010080009044031000c15041409900d40f92084c0010340119040a4000381c04950000e004009140c0114035140d007901b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 204498902 1250 204497652 204497659
    0xe010807091203020c1201060506030a09050a051b010f1704140705060409060302090603060c0f07021507030c140127020402220306060b03100302040507120608031e04050f1509 77
    0x440c20503600045103000b201d41506c07009220b003001c0e403010f4281e0701c150041e580e0140701800014000307105c2c3d40c800b091481c010310031650400015100c0b20f051a40000031031020700c03200306042c0e05558020300220780a50403440c017040045140d854074545803c0150000b852150016404a940c40d0104204005844001e2005030703915130b1040580018091440100d01411150b400644540740100381d0a1040540e1910f6030300d020b002801c0307054140c0c40440c0403a8000c1001e903540e80801040c0000d824500d100c3e440740c01c03900000d41080c0d01d00c81007003a400c1a0580c102010894242c454003070612440c0315039203001c0c01c107880720310008000c0e00600c605100b94080510280c4100354030841c1c1c800c00c9a009845c02c0050580340d40da041494071003140d511604020611040005003401d83c0602c0d0f02001d58988400400d0900d103950b425038502c0d0b803004d2603a234404500312507031103450040c50b2202007901c18220715040c600000300d0768000c03240c4030f414450002e0f081c0c1070100e00e0415003103d0b0071030b1005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 204500152 1250 204498902 204498929
    0x507091b0210060e060d0507211b03020102120d060b03070917060606090607050f01050403050315010207030213050712060e070f051206040b13020c010e060c04060e01080709 76
    0xc0c0544240e161100005100621950507000c09605052051030140e0700d82c14500b654a9888800f40800160440000c5895116a100006980d071003842c3d5642000d03800c02001503101c1311414000b101d5a001071043d454824142e4080005070f0300018010301200d10301302d019481d1100316080740c4c028030144e44400700e102400001c00c01e01c250b2050005042c5c48242c1034841880c01c94042c1702d50f58410841d031241d08098104160403292511001502c1110b01c01c804443c0404561429642900d0f400e85003103011030004014490700304d40c2941d00e000c03142d10a00c000c0665a02e15000103d94480c4900c40490b6240e07a00c0c0802c00140c8034492100c01d40141a500384002c0340c0c0c071803020030319803011181d01c4002000c0001070354000d4072840480d010040c1c00c0a01d11116120441080024a010803519a10070301605041c0e1805040d4000741a00c018903400000b04e203181c25000c40d052950040c000d10904504020a002e01d940040e0000751403282842c1c04052075071000826915800103400004601095 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 204501402 1250 204500152 204500171
    0x9031b040f090b06010809030f0406030b0a030510060f090c02190f0506100312030605010e010e0303091302180103140a11070b04081b010e12090406031b090b100e010c050709 76
    0x24030341c0e468000d50702070b0b860b001241e40301f50744151240126400200c00702d07030030132003001074a100390000c0a261000401003010113540e5a240f074503008440048950306615607800b0040902c00180100c0186041b0100b44800361140341c00035100c80e1000004c031109010102c3c6078091001c0800000c0541c0c0d07108007142c140e42420041002005202c0c44100d40c201d05048090210324400d000d403d08451040e141d407440031a6031b10041d107035040001101c41c2c0501c000d002c1d580d81030346d134806e418440121012005a941e0340645000005940396030030a8107041c141000c03d0600040d02c0c0a896200c0c0c4480710004190b0074152045e0490f104940001d02078a445006100602c80000c00400c11995590b1801150050f0058a98281d840c0c9004078292038010700d241d100152030300001003000c0f420003031000071000c1d103039911f0415602000d1080a48031003204424404410103108203c03c4180486440c0c540b0030090500074800d40c0e8030055a03040210400d80d8900700b020802115001c2e06890340107104698030f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 204502652 1250 204501402 204501413
    0xa080606030a08070f02150309010e0c0d0b042402070506010803160803090a060903030e01200f0a05040b0c0106180504020a0b0a0e03100b03070b1e07080d050c0a0305010b09031b040f09 81
    0xe270303010324040d440d01103225040400080c0709000300002524030030000c40c403501c0311041044014015241c4c0304a040c5030f01c803600c114091900340701a143c4001a114122400e100f40b030040140c0204185030720410030f0804942e840320351222020780c44403005549650b1071504a080c0307450010014191030812a0210805400d5042525480c000400810600100c07414080b40000411341c047c811650402492680160b0a402484480d200d03003010351a095444814100a600940da0401036941d9400240888007490110020541900806210714206a00080c01a03400d5100d40002d0050001d180358055014042d4800c00b183e00509a0710080845011003000d00021600540300303001c3c82c403003c0380703810400301030b1042403105e0348a180403440300c0a080407143e40a01010750b400d0209020180d980b03292402006d100740d01e1845055160000d1810150580d041a0048080c26205010003017054500051a0041c07002d5160040c66843c40038021070014502c400b10b04125130f003402130444c103121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 204503902 1250 204502652 204502657
    0x1401050c071d0a18080d140906071b1e0201030b0612040b090d0203120c0c0a06020406030b040c080f042105030105030c090106080f041505090604020a080606030a08070f0215 76
    0x800502d0740581559030780d4024003100e0400750f49084014242c00d841000c142208050401c00e501d8200004609003940381c5120404c90481d0003070843c1c3d0020040011403540081c0881071896044002c0700140740c60794a51801c0324410b01e2128648002c405402c00303580c4a508901a41d013000340009594907420b8401c002e55490441d41510740355040f80111b2610313280001e04140c0c4000c2036000d1030414607900c200f203550200140c42070410b41000c0c0b045501c40380d41403100819403445a0801a540e07803a180c03000d02a40c840c401075500c11494001340fa0401ca400403c016888040c1ea5100b091540d0340e803401703960300a41d20791405001c0f07480c00010a07215030460002c40c142d0f03804504888100000300d0030444001000d00a0500144d00c080c041401c0000d02d0440503003161040d03c1c02c0e032541050f91101d100b03c0300c1c2290001da00303034484414030056060080000b8081c1c4003090140ca09481d00b840800e980d524030b603038000c02c10300c0000b802c0030134030860710b2000980c16401010040c9040e61071032021901d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 204505152 1250 204503902 204503939
    0x405130201020d0509010c02040203041a0c0403060501080309060301181d1005010918022b0b0402182802040b0d09021f020a12120606050429041401050c07 68
    0x10301c1441c0a2416044c09101a03e80d0450143d40395602c001317080d420b00c406904081c10855400c410640b01c1d24a0703400c0000010703c100c0810790002d0b03c452540c2401d500b42c0d441030340810071581080000c203005071100d1007164159032403190b80101c0030444288002c018000b00c0b8500840600d00744002c505000045213904400006800038011642c0742c03010041152180a000404038008d80d52003001800c00503030b030758515425171480c2140c42d400b020702c3c0c0020f024400710481c1e0003110b400801c402c615000088001071040714019940520f401c8102004001c40891582c0c2c810720f0101d40784928084580458001e00006e40140351201318400c5c0300c0c005403a10000c100d1007000d120390103920520700a00c0c2c02e0309007041d560003059550040d0322584014a05248101c0c20002c4c0c2602c00d0f0503070030103401170b01c004040700d940355552145481c65010401012212184115400a40c0f1025a601002c161001e44820f12512148002c0c0380006842903c11003c40c9003444c0508100003680150034441039150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 204506402 1250 204505152 204505157
    0x203160306060f0902030105130b03070906081006120201020a02040e0c04020c0105010e0711061501030b0301020703120c0f210207050f060a0606050712080604020d092306040309150e0405130201 85
    0xf02c13900d502104e0180d0009010346600302010100d00c5000b412944c200007015800603055416560b101d42c1c0580660b4401d403c00607090b40325240c61401040c60b88580340040c00f00030401891a007640e40000d40f1131101460182c0300c4c0e0b42301e8a41c071031440f6090054403d400c0c0010320455031034800d00c0c5000d0180001b440b03402141d00446d800114a00e001d90320790919442e00c0c801070308681c0e0ba0090803c0c40b0a160008050400d607990318803058a0f10240b0041c20060301079140c5500c020740c1b05103940c09032818007049108001007a45056641c6802508001c0072112130070a070245900c48900440080c055036030301610034840c0c2a03d10102507070103d001c5000d02c0d0910020302503191200d4040d03405205810000f015a07060300241440c49200e039110070f401c003100400c09454070050380e1080d815100752140a440c0c60301135650610410f4507004c620442c502d08240505020325143d1800350071031000d84104041c801c4214024000e49208042e01c04151000400806c103500307000035490118544010101d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 204507652 1250 204506402 204506429
    0xa020a05060603191203090c0b0c210f030402120102040e070f1812050c120c01031a03060f130f03090315050108060109020703030e0d0e13090b0402010309020316030606 74
    0x290f820042440b040c80c440c2c10b4200c50001d80c00307998074800616050195402c02d5501c0420100007900500c0c00801403400c95102a00d880700c45c4400ea042400c8035032022900b491181141e5043c182100c00e0710308104000e42c40a8503961240041021141d00240c1e0340e200e03501c0002c01140720700031001442d02401d80c07559801540b040d40d20003900ca518004041035009200d0003820070070041c1918403058000d00c610191500494144046034461540f264003002640016140540d25603041c0700c0e0b10740341c420141400351a4090711010a40707445003c0c000d06c24462040300059042203080d0b41d030704102035101d242144070481900340140104e026002c01c480c4000000c400b800100360034003c5c03505a900840c05844d02da460804003e0095105180c100c00780347c1c4401d4003203200541846024084042911a030207001515010401c0704100084005c0d030710f80c5010302c1200865010014240c0c080d6080c00c00040000640c000685040580c3c1500c40329021001e00120810280c0d80045040341c1d4441c140c0300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 204508902 1250 204507652 204507661
    0xf0e030111040f08061609030b1f060503060f03031309020307140d090308090a02090f06030115240f020a06051e070c0605061e0618060d09020a050409080d11040b0a020a0506 76
    0x211101c4103e1b442d20004050507401d01c0854050480e4071742014080d0101030300e05071240b0620300508400e51013880881c4c8003000700116410501c014408414013200998038058001d600b0790b504954500030a500710750b012000604440c05104000b151070340441c1e080c0c0d103584120071140f02400703c02d002200060209400728035407040026543c901a6801010526950b0b00c81c42c10040d4500014100307903143d0349580d0b040404002c0c2d1244d4502400c0c07040d8450a0040e5195001003412184003841000c02c045002c12a5400b40e01040b41f148542e84600c0100d42900d98603080800c94580d4941c1d5102955035205000f00c06811024002480d03100700b20600a59944400300008940c94044000d00303580c00d5075428245280540c0240402c108000001c41c8084800700468200d4020001e0312140640e0b42050400394580400c1000040900300c3e420302c02d01c0c41a0391040860f0041d42c141816007900c4070881c54150700c500044e540940041000c42e0340b6140d81c900001d68485132000203480c82e0144c0381c0881e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 204510152 1250 204508902 204508921
    0x151416052a0904050c121603051507020f0d05070807140a0303050a0501060906121808040603050901061512141e0105090714030a0608030310140d02010f0e030111040f0806 75
    0x2a11881c3c01101078045c8800f00b1040c8000e41c02a0905101c06018a0320144408070380105608041c45c003c00080100401c02c068020035254080d041000b55884000b12074070f00e0f400006c10700a40212850519140d101d9450032014a000303ca600414181491003644080c9000064002c0c946000355000c2c4a140c0f62002100103d0b40c0c2809200009400790f102446200e025108840d0205400c0c0300004a002110a5506443c0708860048030146000501081400d40c58012103070813268280082000e00d24102d595400c00e81d40004c11014410a401740d10440c0308a544252032070520186803880c10318100f00440103200d04440120940d104e1140003180c43d080102107076104003c1500d40340003400503540010401d4100400c2c2c035285603155400402c220328240003440c040c01001c48c60a004034140040a000c0080d403100036030040c0c0e06880c0c44e10260b81c0c00540c4203107804035424958001c1c0c1704a40400d0150140150758585c20310005000201c1d010100054070480f0302d141d041e290240c6174003202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 204511402 1250 204510152 204510169
    0xc06131502030c0a1d0f01030b0a0f0806160905010e10110607050d0c0804122a0b0708150a0b0a020f010e030901031401030b06040b010905030d1107151416052a 70
    0x16901b00c034481c510040355500940c06a0b60110700203081d0480309070348143c04003600c91070340c1100c02541c005c04107211a040200e0311780b080c3c00310642090b00801d410100001c040294000e0103611420710f00948251341c030300940ca10446c070400f003400c1e0740302c07407418600c0a850340d40450750b82c83d21a882c3c01c010002991041c60400d0186da4032264805d602d420382c00085500c0e0240a031070243c0304140a403488011200340303506141c180d1003100c1d0700890380380801000c2d00b50b200003484910034039000c017111206955040542003d0343c0c1092001c0d0348502e800b62080b072a207074052400074034942c170f012604152418000007804488400f40d90074480c1e000604032861038031000f0b210080c0742c2c540803004600c0902d440d400181030414107140072400176907a000004d00d400e2580e000440030410600111074880010f1144802a1041c1c4088100a84680310014551011700c8180c115001300440c1160000c01e0303410422020a4102d41124500510300c4c0020210500844030a0000c4840b4a611a11801e19408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 204512652 1250 204511402 204511457
    0x170d0902010e040c0e061b0d12060f030f022e0503090d0f08130f02270109110a0806030f030406020610060305070f030c0c020a140301050604020c06131502030c0a 71
    0x84d140c100c81c41d02d809010b410b03000301c50f9050500182203c0c0101c1f02c1410440950700101d15900d200c80c0f88174900965040b101d0300e80100040c000c0c10902440030400c65589040071945c1500e4030242500d070883e901c9030b0301c600030a050400241d60350503610910340c808040c601600690080c0c500741d880102c3c0946468513040902c8000c1401e80001506000355118803d0f00c0900452004e001ca1031640c0c0018074100940300080d031101e000c541d500f1031b0720090048190250007900d00c10401041c1d08541e0f030300e05000c0c48401100300715034100020600d0300c06000c1042c440006400300da440743e454030f9020f5112102100c1c640301c04c00104c1e00c0080d03401d2290240502540035a1901c001c40d1342ea0100c21006448580a640f0900140745030007001a00c680040c04002c00d041c010f100840350840d810582581d80c05003d076445640103004004542201141c8641c10081e44d150114020080d480c10360321103c44100d618507524404401c004e09007058000800792100e07540e486d001001441c004842d07017001e4600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 204513902 1250 204512652 204512657
    0xd0f02090a0506130306051914090c060d021201030605190911060705010209120d1101050c1204020a081603030e1221041206020a02060c030f070c170d0902010e040c 72
    0x7004104a0910400500c400c40b642e840703549507661a44c40b4001078810648410892141480803903103c26850300c2018002250241c0c010300c00c1c1445030103a0341d999a1010300c24401c000010701002d03036480d1035044800906101444032295a0340b0b040440c000c0404568084501e40d06c10541300490310300384285950b05600552001c2040c2c0384105211180c0c0141104684d591b50801c0101116a10010000c9400d850b03000100001d03030501c80300411051042c0120b0b1001d078100b006101c040e01c403039410703074044452181c2003883c10b66490001960f5804261b01c084203a01503000d02131041000d1824a400b980d002c0d40700c0e0b4014901c000c00f48103810a20700010b141a81004100e8401c40d107050b604e2010013581480720604040e1506401075080d151000c04460f420303030028800c420b65805000d400d52011640c114a4218a8100e2401c2400c800c010088000c110b032030307034160b0200580491003d094961500a0580710603a4030920b030020401420300382e02142541b4014005840c040c090140d4801d05135 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 204515152 1250 204513902 204513919
    0x5150f09100b03060a051206011a0f040308130f141c0f060c02070503070905100902070302070306020307020304030b0a0b0112020a05070b040c08060910060b12040f110907050d0f0209 80
    0x2650b40c40740340d000a416a0b610000710800065507036101c20341406490755460117401d56514000f844034001010003070040c2600020b0003041d0849201805a90440c2e1300440110794a04420001c0400d51641e07412452092903210808503a1010610090941034000c0d10110502061280d440000010b04d080040403003403000c600100044030b94000f03000300d420a0046602d600e448000003030030100e1319000302c07820907540c0c01080305098840c40e4a00040c1142c02007140380ca880d1303480007902e0300d001d800b02a01c1c00760000007080b0b03501c0c07082049400440e00900d1076130039818821b8084000e05004140300d070014807096520000400c16200320b402000d0b1380d4540034a400c2c8981d442250300c541c0240140c4440c0c6d40c02200044021045c0a40e610482d000d03000341008044170f01942c0102c80d003580008290b80c1050004850441c032003604c585c1c01c2500b28400c2600101c1030f1928054550072629800d400800c12002d02082c80d1304200540f039101180304082c0b02c00d6001f184d0031004c9018840e040d95014000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 204516402 1250 204515152 204515159
    0x405120307091a030f04060b0f0616030e0f060313030219080408010c0f0e10050418020309070602030301030314160f0b1506070210030504050a0f050d0e100f11070905150f0910 77
    0x203e601403490f0039005481c0c0a09c507100e1000088554001d003040c040783c20802c0040e801019480b200c2401c0c0b05404070b41240c2c2a99081c2c021403a1070100800900342100701c0d400d1442893700803c00e04581220302140024101400d1038200f22a4110344250101c0c4d41c02c00d440001a9070040b540c080d4401d056a8030451005086405c014008040500310750034050200404588a10064040890005120005a40d07807c020700ca113440c1c1905584110304641040c0018000203900031100078010760f45012090b01c2d1070100b03d10300034141d0700307840081640e00040900d4003001a80c1031824801c514000304100400b4075401030110070711440000a6006c8840c450158034a030183c1d1000303800070f00030380c11900421240e6480e50462000040e007030b2001d034030052071b044403558401184100d40708261840e0b240c9031441800a4801001c8074501000e020764420401a04242044584001c2500d0941031169051440000b080780c00001041030099480300525103203410030784030032400707040124a4420501d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 204517652 1250 204516402 204516413
    0x61406010e131122060906170a06170d11120712020c151806190e03030c0706110706020706090905060d0f03201902090405120307091a030f04 62
    0xb1140d441c8205641d07a0442042c40781e88050190541c500c51982c0f50721a0304403241c481c201038503541d0041080140c1c08005121700c1e9408030003c01d8a160714221075803d520360076401400740c0007076089000340c07041c0d030720f003c1403102d9000803040302407801c0e91516040c540b843c654140d200c01001014800b6080700300100c9001900081d0b070140e020f44144181d0366611100c00000e680401031301804c3c2c0c484040440d82226100c03803007180d6241200125919854600f03522440040c8032041d4450754103001c000203582030152000d000303c035005000f01d019900f402c2d850300310141c100094100309402c1c0307102c1e902002c2549800043c60000b40d4075603072100c03803103180b50622010151100401c0607802041c02103100c2c0019138980142d80f00d0910035126025031014404940c403000000c185940200d510128164424510503a00c1c00b06075501508c4c5d186299586080c07003440c000701d0540110100c2000410420041e41c0414800150780c80b4800d0480d11a00b003a40f0083d0703601040d102060310b140f90070007080000d00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 204518902 1250 204517652 204517669
    0xc09150809100905030a140a0909090203010b190801060f080601031401230412090509011505090d0309030c090e03090103020a110d021f0504050604030804020d0b04050a061406010e 79
    0x40c2000e00b00c901c40040300161a080e0340c20b0f00011500b590010503100742c0b603500190320550503004d4185207410030030700c40700007041003c40f48038000f8143d50b034801d0502951820740042181020181251900c0b180e0100c40301702d00308082c82081101c0d440d020b00855002c5040d1034140868252100504840e4250313200d84803194110b0054034540e65075084814107849034400ea08044031000f44003c1d1140c13500d8206400c2d00c010345480b410800121000c2400255070f40350f641419215075800740c00c0d4401d0b40b00426130f01ba00c241801e50f030384010241400401c1580c000740b010180c9100700800340c1000c0d0b9801c101000e030340041b002c29440e5001800f0201e403c1d4820b90142c000310340d181c43c1210020940004050038040c0840c44a00140c00450442c0016a0030405100070041061000c07c120301e01521200e40321440600002d04011f0000085001e44d80c5210340c4036034494004a024480303041600c0c0941e595149210205d850314280a00703109152030300080f4600c52501a15000d6100006408019906 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 204520152 1250 204518902 204518911
    0xc120f06030206300703020712051e030705130f0302030d020615040507050708030709050f0307060c0204050c09060c06250215071103041211060a05070602160f0f02040c091508 77
    0x20003010180840003404d20000c180140a580c400580d100e000c0d040c000342c0d0108a05240003442410040c002c201c400c1c0310b01a02d544545891400d40302c1d15114000c95903445000c0d01707241c548103640004620301c40080902c0701102d02c202c0443c1d80d05020b5010030f0380c41d42411204116500140401c144580c2002c1e08050761102252401510f03048041e91013001320703001a40d2003400908805014402c81c205401c110001a50407401001c0ca00c0c90018010f200350500c40c1d00a0040c0c0d21a0007003802c040721201030300d44000000f084d03140c071031140c1030038599200403c03180201c0715081079940380030070310410076000201a0158040d01015005801c4240c407030074060407a40401480d040000244581440540080c000151096034136100a003407070700c1c070324040010540c851602000048ac5103500b0004407002c8030741c44000541c9681e100803c00c4030a461420b4042d25002103036030107000f0000e00c1550280e005208603010008080c0042c411908583c0d0740c0244010003c0d0701c2881200c1d103000c1e002c8103900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204521402 1250 204520152 204520207
    0xc030601030f0c050304060c02070b1e09030d0c0c0605030f01060c0512040611070518063106030311010e030406181518090b0d030e060903010c120f06030206 69
    0xa06945502c98000c4454a4001d0b100182c8040180000c10103075001d590a078464600c0200042c5051900441d4148511004200ea800c107101d881c9141440003820784005110040a8411034000c20602401005a8802c101e800740301401000c207059005000b640d0007140b095124590aa0a03c902030381c002c0001082a507003442103180300340c0c440303000100038805040300b95140c205040d07030b028820307252403000c2d04080d00c120403c844a4440d002c2d40703440103a002104603004011452184c4140005c0026500000140002c1c1c0040040340c044541004003101c0c03103aa00c0e151000c0312481040d08a03914011080c051341c0080004005091140c400031040d200e040d202c00348507030740c2c6400c2c01452011083d1a01c010960703d00360b000d02c1c1d40c60100860010b0000c0c48040c0000ca00f00400030300441d4828200801b80188000b011015460380c40607a80d6003000034000f004900700c004006000c40454036040d00c0b50078100342400306107440034010282102e602600050402203003000101c0364404e40301c41a880c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 204522652 1250 204521402 204521411
    0x307050f0711150910020a42140903070507060302030c09091008010b0d0b07051c1503120f090e04020409020907031527090302070f0801020d0609090b0c03060103 71
    0x98503520803225280700e030003c0700d0060750b03070760b2000911202c40030040d4000e0030340d040555000041500c260118044041c881c0d10600380d2508441c0d42c3d105400e081103a8841202040364441e0711207041d5003d0328030810720140498180ea1400410b80c0d4070310527844002c189070810035040140c14080c2e00a136800c29071042c0705900f40340c4c0c29808608481e1040314204a0010b425908001400003846422071611058070f2150040384140c44076a420b501c0601441d04001c00082e04440010380300c0001c1a0b45102c50b4001d2080c9440c1c1d00b28000801c042780001d54a2081040450150a0080440f50a1110030780c42d040780d51441c8c01c1c128111070000801c00d0340c20a484420600041e07403002d007410720481254170001040b140002c40d01c03025080e6038000078620007900001400c0c40d07814182506400224480201c5d5050301e034a81241083c069074081c007880c0080c08400300e60340c0700640250400e110401d00070012603588460250585900c1c280280071a2803540215a0081100d802568012070605000c503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 204523902 1250 204522652 204522683
    0xa08090c1008040204050f01080a110105090d050c011106070f140403020303031e010803090f1e040513020111070b220513060503010c0806030607200f07060809030307050f07 76
    0x100782580104940c0c00082d8010100011407815101c3c8540050310003012542c25030610558076502c0c01d00241c098409c0c03181d81d001c49009d0b07104104607024014003402d5000700004500c1e105a64099001105022178221002d1008005000403280d02c6800a40e881c1c1880302c10516040d1135242d1080340c10585182c04120100150302c0402c001c500a46c12900840d001d0307101c040518800c884103070051805500100700b01203244d681e06461404043c4115007603c000e901005a24000343c41d11080940c00c10b08040410009052961140001034002e80700c5a40c1c428805400c0d540b110100d0240140c1340e40140304400316000d0141c01e004402a000000200f01a125000a01209a1401d90503250f948a06080c45241801c0c001d0020940701400d0032644e5081ca600006d403030b02001852030040216a103142c444108414507a10300c81c4010307000352180207401010b5188c9440c03260080c0400700d860000420503100000044a00c1407070555146402c040300c0a650f0f4a482e840410107940e06400401c002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 204525152 1250 204523902 204523909
    0x702030106080c03071a04050906040e0706030e0c040b030613020d05010e010207150902010e04020c03091807030b0108010b0a03110c100f0b1e061e120103051e030a08090c 75
    0x5401602d001401802c0d442d40b140b0070076203480c1103504102c4000310419102c4541d0402c0c2000d4030143c500031508120580c0c2d9075800f00d0b008000c010369800a920030768200140702034040d88001918104401030714440d25000080c001910880492203405038098000191400314860104040c00d00c020503c040314803060700d8090a4072810300d0303011120395001465404100140d40021002580380c1c2c0180300c111420b0b0006002c0002021b0b50b20300842c0c002510008135002402152241c003402050341c01a061011042c103030042c0c0803142400424548504144158007500c1028101c3d6a02e6500510389080d01c0fa044015040340112058240024000c0c0d07581e01c0401d0013600c00c04124420300080d80161444c4017010303500004007190091b2400254038451812500a80c000315009840c0143e480304651307451147c81d011030140240241c0c021500c264801c401c8078000341203d008004803220002c0d0038a070214a1030458001d01681d40c4100405686507002d418405c0e0300206010940c0c05136116200407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 204526402 1250 204525152 204525161
    0x3040203011b0819050c19021011030f09030f07080c10090f0510020915090d06090807060509010b060d0e0f060a060303021006050105040611070f030b0f0717150607020301 75
    0x2c080115001c039041000c030700003003a0414050341c9203401c2800981401c0c1c8180219201c2c1a06e5003401458064110f0b54440c000c220504d044141708108120380144184061619002074410090480c1d4140128011340c6000060314000540310038041d10b0a1400c0d51001707e42d90002031003080ca030044045007454919180b041d6442d00d40034500b0110340c2003e0349005410108050642c010071841403182c2c0055881e4a100d00b80c000e184852030365a105070590008281c00840c0c14010700e103d042810f00e90070030a40f00050210366216410900c0307941c4820700302c00d007038803803400082e07401a07418020210a0b844c00d801c80b600840c00c0d1016150aa991010a10701b480b100f00c0e4003070700d95030312003108208150707040001da0300c0310030211b10070000e803820800000c01ca0720561298008000740c0f10958411400c040c010b0000500f054401003003074940d60f150519910310103c815142200108000401c4c050081080c6003a0800351807201c0c00c50303600c9440e0420003962101301e054201c102403010b100161800d07c41d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 204527652 1250 204526402 204526451
    0x6050426072304091e0204060b0307030c0207060c020d020f12010606020d0e0906090c0a0927140f0606030c04080a080d050709030c0311120a030305070306050f03120304020301 77
    0x1c0c0721011055060315104082c6001201401189441c00318000301c1c840d08844100b00d11014100c22019180d07000140143c0025080008180f0300082031100c019010390102c0d501b010b060702902ca426075507050a4074001ca14120103504070a90801303c0c0010700e0402c3c400c20a244009103052114001410610300715040c0b41c00a4001da0711a124041007150000c910f01060340c02250b07010101d02d00640402e2049401801c0d400b00400c012545180b180d00134804403014000e40782e200842000021880781807800818115103c0d141f614400340098450f4080701c500c241e034040ea0360601038035201d06108041d44010006003041000f40030121b200b0300700b0301c40440c4650140e4440c0751140003c0100324106c89020305a41e0601c0107144003007001a110214420440f60008850801c111405001ca401520714082e030b114503020310340150040503056813101e40030302e10607541044000c2e165018090303000025040140c9c1988402c851210728910600290f0b8018400780c00450050301e41118143c1c081c10051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 204528902 1250 204527652 204527669
    0x18060e1003021e210109120215160c0318051c06050705070b0f1f090f14060f06070503091f0f02011a09040f0503030a15050a0605042607 60
    0x8404000750714040140180140f079015842c2c8201950000141c40e42c4800d40c9100c424104001d1000800c21081d84000307074081d08070404481011503d40020b40340d06080e806502c1116812000c1081e207251600810342808072078030350710908100e03034070191000c00c1c41d400800d0115111410109040d1130f81d00c003060070200003141d001100ca00502d0030000380c3d00300410282c10080c045c030002021070580140e841e00b21440820600c05510350041840643c003607405601d01c090036100e00000d10340c1503a444810840380c8030000b080400103000f1072800600e81942d40c10303070100e8013548028003032030008001d000162081c002c0b6450721111030045040035082d254881c00f000b03004240c80f01d080d070b003054012201008500c001c1103185140c8003100c0b600103a0111440c01114010009810810101e2211161581013400c172900e905c2c1c44c651900280a90325028986190305182c0010241400049001902e0300d076165141000d04094442c2003038044500300c64000d201c0c2c083c9200301c0002c1480010003914858 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 204530152 1250 204528902 204528931
    0x1202010306050906102303070f1205060a091116050703021003020a0c06230f0604180b01090b03071502010207171e03060d06060e0907080d080118060e 66
    0x5000160072074034240d000e6030242c43d03560200070303203a6600100c510620102d402c1201c0c0103180e84030100181840c140001e1540c2c04000103005806412911501c1025055038079403144020714880f0405452007a40c840e80c024402007028068203165420503042141c400340d400d4184460401070104010071440e0a0740c2580041a041c415410300031800c0d00707410280e080a51800301c11030b100400001c1a0280503004994074001000841c12000f245060400380d401007030110b0500b00c44e03a00c01038409440ba035200710303e410501d010751081e440c0d030078601c00d42020003401c82d6271a0600303c0e4043c114440100307603d8024281c4c0411203001e1040017500006095000507210b0100f890412001074075102007500d400c0091050081001c1c0084980e003c12580010301516a1100f50100321100120900104407500f404804200203001d1810140b0411049040b00d071800d80e14084603131036240d05443c101c002503108006005840301c81802900f8241b42c041d000881c01c0d903e54850701c5000e811b698041c00d52120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 204531402 1250 204530152 204530189
    0x180b010905010b12060411040e1029190201140a14010e1303030e1608030903070504020319110f07050c010f030e0c0d020409020603071205070306030f0803061207 71
    0x38401c0d6030242002420301444c024800c2104252018010542840303192126907443c81c0044071f40640d4000c0414070a00041402d11205421105006000e41080b58040c56910054100e000c18508040c400040040e443c001220150850392100307240d281040d1741d00c0e00910700c1203561500c05684204121000012409400760000303c1d1114103a21a0001603160000d01401c0e5046a49194845070b041c00c0011310a10344602007130800b02d803a020f001c50748800002c0012507600220041c80341450403002e03620401d4552040004a001c15500400c511402c80004401040781da404005401850001d050034409101078400040c3d11500d01102d06801c0a009004d2650704041900343e40f1340329083c03d000e5000d140760f01c00c1d542c0264158240c412001c09005c07000355201c640c01074000300c1d000f8111681e070f4070705440081c0c4944c05154003422142d18190002d10342c180309204200c2034981c0014141d5100582d41c9422019410162903940d116420313a0341e2000c1200c08200d688014411902c10340441c001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 204532652 1250 204531402 204531419
    0xd151107050312010f050a0e0702120a020a05070b0f040e090c040f0b040e0601030302031801140705060f100806010e04020f030d0e120609030406031d030a02060f061804080a03180b01 80
    0x40c0c0c010700c1d035055030201c01d00c86c660362901f04000b13440300c200c1c95183c1c50b501d03040200d1030405428070329040d401c0005044041d044c2d010609550442c000c10403551019074410840c00f99224454a10f0500310090001b40b28139013651803003075008040c0d40111107030652540f0004080715584101d100c0c0e01584c64004a25038100303405480e003040c1c01180036008541c03542d200039449101d84150854001041c0e4441004c50b0f01821a210072031004d655481e0f01c0311020314000d5030350300d816940c0f0005408110b0024210490b2035035000b040d81d01000c080c1246910300941c0d13108011000d8400c80c2d202c24032f0b0f0810061501e00b001000c48070f403c1961803082919000c0184103141038050350910035a000b034002c20200d80b200008680c03c48a6174a800a00491802d80e00f00580520011080441c007001500c550120f0780020424010003091103074601d16158070041001c40030400c1c03c00e08141d09070500041c045a44040541982c80c0a420003060b181c86e940c2c2078041111035198110b940d10201001840181ca = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 204533902 1250 204532652 204532687
    0x9020112020a03090b06060c1518030301090c020105010b0a020a0605060105070605090c04060b2809050a030515060a03121d04151401020a0b0c0f0d0c0e0415050d1511070503 76
    0xc150b49262034405501c442585540b458127a00100b120b1040128189190342c42200b810381012070709898489d61141c0c009000381118241da03400560800002003817000210086a2a2459075001840b10f1180d540d01c2c140074000c0201020706101080c05008003040c21030145a22a030500c002500d1402e100004110803038005400010140c4824031010030100c9564140c403452811050702c521003da4000011101010150041134028610b03600000401100281c0d49410020307031a074214a0f5940c502c14031001c3c5810b0720029005101e5101c14490490007180c07030b40c02c800340d911090742e10f14440c0380105040d2400101d9104181c43c02c83c40411600010700d65103040c807602440900505100d9444204143e05d0283c40803940b01d00006641e010005080e080b1258011200410b210007004000054000207170402da05010340d003002040540400c80000040684030028020a0030303421507282c1038540603182c02802036141c4c2e25150401001c43c040c1c050550345210300025039079600a008140c0c03450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 204535152 1250 204533902 204533911
    0x1506050702040e0606010c0204050a060515071110080406020a18080f0606090c0405092e0e090105010e130203030d0516090e06030a060506010c1a0703060b03061309020112020a03090b 80
    0x4c0e0009401d010341680c2c00082e046100d501200d0120361a01e44403991401402164401580003100d90043c4510280d100c024000141c06194044061401042445404003041e03010000140c1c440300090700007051795000c2e04000d041072030854003a1604003120025003070305411140842d40014424003615208001403644102d00b034580b10071a050009208500d4003d07405014410031403840050781c00d0381150502c000580c050041014011207000c03980341d07400c034940107100d009442c2c5400242605414010381d4100c9a49000c0025a545c901030f84400751544120101d0340340c0030030050242010154000c280c0141c40c880000004a8501c18024044600039401410785141c510100142c40d50042180c0d0b0485400c13804c007040556840e030048480f802c0d1901e005181074462144210b45810900502d4031468054504101040d101d1400300c00b10700040754200c4e4008038480c0185500d042541020102c2481810007840c42c035410305100b82030b604003000c2c0c1000203031348405001c1404183c4003441e030007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 204536402 1250 204535152 204535181
    0x1090b0a1b0c0503070206210109090209090a03021b0a09020301080705031c0804020114070203010c09150912020609010903052b030204052d030a0506150108011d0703150605070204 79
    0x4101c0c8641d50992070b4000d114000e446980b0102d03d03032546d500c2300290803a011510306040d011a6841317084c014001d00303081000b80e000d03680c403800040c0311840001d10703030f000306400d41c00502d0f540d0340c20207002003441d010707410341d030b030081e040e05400141303004603001a5002e09410030180a184d41401e06040c5020b070710056141c40c6074060341c000130119400003c0150002d80a00e4809810300d004001c0c2c00e414412071074001c0d0950b00e8440c0711481d065003c00200207650814200c140c00050a91040710031000070301400046801c0204444010b16211300241600d240606100e103d6507500d031111030070b01902040404800800795043c1081c0c10a0402062040906003011410a0300701800326120070410580a000c2a5480f800f00c100c00301010101075105000804a03500103102e443c01a0b01c030310055402d400c0800c4c02c0c11401754158000d02c0303258169180702009011140e0149862028001c0c080c00100c1495034801d4a42081031001030720b0f002505241d2540347d650420f074810310084070306040350f0042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 204537652 1250 204536402 204536417
    0x307290c040303030b06041d0601030b060408030909190606180503070608060603040212062a0313021302070606060507120201051522150e07080f0601050c01090b0a1b 73
    0x1805503445098070280da0b0585400074940701c107100031030140c1c4100c1e0002c003101d25003050f00400111b0f8004030944640402c0c0e0703050002c440d40200b40641d40c000c0e40609809900207001c6e82d0700340c3c1040c01e1f102d580111076a4071260705544202811040b51500e801220000c0d40441d00c2d4480c40d61840303000001042e040d00100785c80341c90403200405040b0f001e02410305c90000000482d0656a5103100c003400b10b4aa00103a50060510502a40c0c072803014196040c21024a82c074105d00000302201945e02c180d41c070791481d0f030b1700c2604c43e804c01c20500c0d010000e41c000f0799030034003103200454014130608001e0300407512890703603079105801e288015105900062045a04240c1041140e12070040305064908003980d07403600d15005600b103000c200caa4000070907185407422403603e18407400121507034101c03004c0401d2002c1d262a2108100e56810085800103503000000d00418815489480107050701c014440000403070308060350756101c2c00384040c2d0750060201c0d11640783c0034215011501e4001940c506091188 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 204538902 1250 204537652 204537661
    0xa02070c0e06030309040e0a05010501060809010b01030b06190909150504050a0e0c01050f0c12040314030703050301030f150c03050403121a0d05160303020703030212090d0609080c030729 82
    0x80d928070841000c1c80c0526110079034441146002c0200411603527002e0002e02840d0f84030880140600801c517543d100960820301580340e01d50084c801c180072070002415161078502c2e40301c0b0741109000e159808800300721a1000004000000b8800e0252240740809000d505c50314080402c0203840c4094440340030b852a1000d0142c0680740010307010880d82003803c0c45174642411081d0fa890300d0282002000c414010010204007412031400200306a81c42000c13076884289010703411a175030b4040e0348070080c0850b2040005002082068050b00c402c5d520604401983c84207503c100d0054417048400c200129483c0c4050004146d000580c40301c1c41a0307214010045103480b550001c1e6074458848115004824980c3c8200c20302600b40406411201004040c6d048aa13481c41c0080d56500c841c40150014003402d104035106a0113441141c0c40168020000e0400718130780e454140040c891030f8407c4400c0c0b642006108501c04050014200c0607000b25403490003c41100d21260220ba0b20600f07442d4008403420400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204540152 1250 204538902 204538909
    0xf030307062a0206180706231e0315100e011107080109031e05040e06040b040b090a0e0f150c130e0408030a0b090c16060b090a02070c0e06 61
    0x10348566421010201e4411100256180003141030607058188400e0455241e01c1181c001650364003078507100b002e240d40c203102c201007240c880d5450f0051000140c8100b500c4503820808449083e004915000c0e42031806c2198400c0e141c3c040382c680c5c2800c0c0100004404c01100b45051000f640c43c2001c10390f000584051502070040c1101e0f0045080c60501003080c903030244901c000c200c114082c0544100030030034141c80b41800f9028031103042c4c004025014500c6c1e80143c06110700b00ba64120b58031100450010b0b03c5d11010030024200c555107d50301305590b140d00807041e03035450f5403140c0100d030006400107100002004180c103020b414a400740071903002c451013402e041d030704000e000e0340070500300e000a46442d80f940f0031103405c0101d07501411140d90b001050005000ca2480214084c81101d04200000c682c1001880118101115600400e04017441590070325041c0301c4100707105900c03440c00003841c0e40a4100040d50b1000c1618142c00281e40840d22804019103103440707101408520070b6000c0d0301d14000000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204541402 1250 204540152 204540157
    0x306070f140a03090c0821070c050904033c050301050303090f030304080d0e0a0501170a0509010b030f03040611120f0a0e0d05010b01090b0705060a05091e03040608060f0303 76
    0xc8002441c0d0004000d48094400c1d44403e60440d03005080000c030a6036103034203da030b80e042c52443c1d15001e103000a105050b01d003180f0485030040e0b4844020322620b40340c10f040000711a8014810740902100e65548003c0c000d6411a4410080d00c84104c11141d042088103105880114020765051040800041c0450b03500002a10705001080702c0341c0056042c190007182c11409241d0140b141e51003002001c00c40760703401c10302e2080650320a0f03410361095680c0e0700044442c081901104009501c0000c04110311100c5070b00b1155004400500100d045016000424540010742080c044190800b04040c0b14195000380d0341426121400000d14040c1812014003040b03200d0f1610880160400081c1c1402c031a001d0813030142a282d004000042c02901030820780c2c003038118041e19600040b5448404100b0808000075a0503043d000401030455030b490b540308200400f00940422090301c1600880b8040e030584031420300382c60029034050350700d440c6403c1c0040c0a2400141403148119403041441c520b40d1000803e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204542652 1250 204541402 204541427
    0x11030f04060603050304034707030b0a03110306090105010b0a05130306050a02092d010c0501270506010e0c09010813080f1b060907060807050c010504060b0306070f 72
    0x81089458600c0c12000910855000600900000c60b00005010141142101c072950283c0c2554001d41e40d00c0c2c9211180000503040312680c0035240030842000e80f01c1030560343c00300c50350400142189007800011045e503055402215130a101110301035041c1401e01c00c0580050001c00240160750610401d2035140c0218200340c002c100c1d010400030858844c0071480301c015500400b0400031410120725420282d03000c03d91842c001c10881c418100c8a288441c141140c111444001401084080004403400004400281c50030764a4138032400c180c04015409020100510440341100300291400600303210050f448160b24800b80c03c03c01a4080380304045802c010802d05c0c02d584940d55807020b80c034080d80c00301000f1784005408039a1605010040009150301c80308411105a5044107001c8250340e004100c40c100204d8104542c1000352900076001c094200245040460600e11248013130b40c02c4810444040e502c0c0b94403200e0310391050405100c02078005009141c1194042038a0380044c05a003007540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204543902 1250 204542652 204542671
    0x60310060c0c1a03011d010b0d0b0646050d0e0f0601090e0c09040818060c0d020106030c140901030311010914010f150e060f01110307030c0c0501031103 67
    0xd0031500b048040d00001020b454003084080c5855640350710103960790024011501d032081840c21342d101820108080a040b03400661840c2e00d070802d0041e0041c01741841307100301030b0442c0301840f001e40c4200da207501880c60b900e15000f0501e40e9001c002520b803030443c0c3d150910f01c112104e00c0c0000910a44c400300b1200e0020b0702d011b01007000a0103002144c6031001c41d08403400b0710700074000080f0b0403282941204a00700310020807226140241020400d00000584008003104000c02c001400e036894030354920034682c002450f40f81000058241642000b03081010a00182d40d100002d100700304404000d000600610280082c60104540c042105444180400384c00c1c0f14807200500650300c401d40120134503a612030900040407400d0a0003501070801320141440b01424903031149503244880c000c40c0704a401c011004205034503000300344807400c0001c1c5c0c1d09604004031246000aa54800c01c01411035603c03035079490110300c066041000d20941e00d5004241050b0038844e030012002400e40c20b59030014242d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204545152 1250 204543902 204543917
    0x15210d080f16050f0421020910230612040615060302070b04030e12030f19030e070b07050c0a0e1837050d020f060603010b0d030516020604090204060e06031006 70
    0x14030f101c4c518002c07035000302c2500b5003195200e40c00042c4034141500c803e100741d90084054503622003440030b603980c1e0301446a82070400c4c42c2038450710203450151111050f0240416240125040000405100403681641c000e07484454000c4c0c0009110284070041459250450400210b03a4951004e064040c202900b000b80c2da40c4a2155695044403902e200090b50303044076601c14418400c0c500d540c118051654407110016200c2048d14000d000d103901c01e40400c0d018040f42410711541141d0f5400469054440748200c001c004048c0e12611410005822010000c400514110080c1b80c4401c05500c2000010b4004251840340309260350340d008155480800c0b46008481482491600075a803560060414400d0b0a040642c4940104050054100100580712103940342d100341400ea441c58144250055960b51035140070901c200b01414405000240203e107a014030703000245503170019001803280c40d90000e400c200403a008150300c64a681d00780c54007800c6241203408500d81540c01c0c8981d20034001c12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204546402 1250 204545152 204545167
    0xf13060203130b0310051e18010509040b070519050c10090201120e01021e0c060906071d061b060703060e0105030601050f010507060f1b05070b15210d080f1605 70
    0x982c85c5400c054103024007401001c4c0d0b60406d89104152040c00b94134001c0000810500f10074411861247c16500054240c0c00b181d00c503a80c0315160880f0040090003049814010034200340e01030b4610511800c0241e96058880a085d4602820800c4005002104078034003403845006076007200401c882e20590807000149001c210300700030302a10800c40303a0003120140c00640c14a41541c04043c0c010070000004640461307a401d02d25a6481005a5480e0f000c28009510380b1407103104000709680c01d00340a40003e040c035200c00c01010005400310221070003600000200002d09030316104150007000740c10105d02040d458800883d480c2d0b5410301038607000d030401400c00107440c1d000703508940c1603a500840411400000e01546002015123900100307001420303141444a40c0d12400030340302c079690404030480c3c0c10340b900450b8140d880501405207402ca0241704261420112403050194400c0702d002c00b8000114188000421058005042040541c0017a0607c036601d011052005c0b241c0c031450504035552a10f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204547652 1250 204546402 204546421
    0x51015331805060d0e010506061608091c0f030206060303070206070204230f01080c010512071107080a0614060406060f03110d02030c0d0b090108121b030f13060203130b03 75
    0x5032904116000a400031301508628030581c4130200002901300204030740d403250003c000451181c40046901c0503905811607001c40c15040027055000d000400d643c1000924540403529a036421000ba034100c004661040d00341038041c03011603444070080380a10b140c41d4481d40092070310b015400001c0c0c0a19a540c40e0340c4502e4224034540481960b041c1d1a4448510f000c0c080010000001d008001c0c031f03802194015003044d4000c03400d85008149405401101e983d50110072a40d10403000300851b141e11038880f0004400c20f040c0681c11341a03015047c0132036a16503090b42c0212140024108a000d2407402000b00681d5030311004c0400f004006290204e100403100480711011f005191084020307502c000309000d00310158800818116940210900607405040200141c0b00004d2040060680000800100b500f4801e4010141d030004400b906c64810320241100b481c41c1c111406002d46c20000040341c4021540758080709000700300d58070081d03262074244810203200310480d215001c034030240803010503801503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204548902 1250 204547652 204547697
    0x2061306110d021c0f0b09040204051519090608030406050f0c030705100903030f0e0303070e06070b01060f18031a07020c040e0303070905030304031101080405101533 73
    0x901000c10f54a500c1d9803002e499090020042a6220314a0800b4040009845029600d0210380062020104e07613569000d000c041c2100511400070802d40350815140c540d81e85162502040100c3c0910034000e00340341c6054100d4803260014055a40240b2081002d03a900c80110390180c814002d0349902d4112030035481d45140181c41e0b00405c64010100020a148004e601051503903011340c0e0140320b5820000c00303e900701c80d00300300590010703041040050045402014000003110014000324130f0b00d00b141c4c90b1070400110a03005880016142c6c500414401e600410b050340080d0400e41c52450345195a0318040d007208a40300e844c8000462800040340d076070003401700ca007000001420a00c40b12260107109510b95104440f884003040345c034040440e05050010030f46003a264001201a28107801100544820310010000c0f00c03580b14a0a003000740308014041c25400181c031500705041c02e400c10099038401d6940079549001c000040d4200c00046c5600524035011441d5424100b0510441400b08410070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204550152 1250 204548902 204548917
    0x3030703021b070e19020304050c101404121110090504090201050702090702010c030c020c0609130b03030c03040501020d0507111002160b0306040b03010b0108010603020c011e090b070206130611 85
    0x18003c3c2d03100020f00c0e840e1032000707078400c074120000a1040b40c02010024124001540c016103603038842c03a10001d480c140300301c2c245081e50b11428030f0000c810180c0f12044e110f074003941114134041c412000004c100064464200319031070b4100c030a8480c07950310343c0000f0142411881391511503034544482c0b0055900070030441740f03c40d1f0094500d9032145003034100a8060b0144001902c0004e103080d84048042d031010176250140d000c000c1440340740c40040400c103c101c05152421843e050b03510780c2c95a10741d5a08000404554071200c000e1902c4074900f0307001905101d035243e00f510910804000d030780c00051703100d40000000c501c01c8070030800f6440c0c1400100d24000103c0c41c902c4401130311410208600c030f9460080c603c00c0d801180c09000c040c082c2005e04d42603500c4c2c903c0140c013003242200140001802a00030b00000102c0a00015142c01c0c81c0303030400058000030401403691079440818406000290580701e600032141d0006040a041254011000880900002c1e2446030f95504e100d01e041c00410456105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204551402 1250 204550152 204550207
    0x2011409060d09080c06091606030e0705031c030f020310030308090c1201090b0c21040f06060609050913030504090c0507063801142206050315090105030303070302 72
    0x11103034035291107504c0e41d000524030782083c401c51001410b15040041c00d0b20152881a00311541c035450803130305501134104407400f5403181c00307280c0b00031510fa01c04000011041542c009004111050110040c04071802c1034950710609004200304002403042c3c0034802c04890b858a08182d0a5031400c0c0885c0c10014a00c0e00190301c407400d0954950719480c15000004801c5c012881207205498803800510107224001003d0700f001c0994002080e40342154140c070b1703800350007403441000c3d2510729038900044450941081c0c0104200590503c800d003090017181c2d901554580c1000b40400003074030050f090f07024512403410303c00d46403034020b5046032190003512501d562042d014040941a0701c0c0001c2001800003101820144108254211340b21820420440002c180c45d40d003100c01c140340904a03294170065402064194a451912100300d86403580710003000c42e80c1c3c0d840d4072400d008503900100550720b01e40600c00d1282100510541e40c0c0401100d8102032141401a83c5a68400000009070b01d041c014406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204552652 1250 204551402 204551411
    0x23040201051912060b0a1b051005040c080604030201021801051e09010908060907080f06070c030f05070b1f080a03090e09010e0307030c05010609060b0a0f051b0a02100203040302011409060d 83
    0x101808804e000e04010081501e641107d40c0340c0210190310924404009043c51340003902e40a03103010680e014942041c01180f0035110551603079a014a40340c2c00f52011001070390f00240c0145000340c40300940c0c02c48802403800d40c0c40c040c484a0160344e86c8026400700400d0042c0001d0f41c14417a03024142550003803242c1c2058545619080c50f090ba118030013881094840d0050364038250556001050f0184541e44a84600b1019106900c0071100d1a402450f5082440002c01c0a503000c1411019250310846d901035400707803901205851072680003444d51100600da0300000282000907008040681541d49072041c081c0c0c1a0b8503804214054800010300b04880d001c00240d8030700f419800f41c00b0411290045009001e0b8658801003c011510035126082da1440c5c18400c00c0205031149a00707408886c100d2900c1420301228010008682200403c074140303682c802c0300500c046003000b21100b03d10000d2800a50f080038038503000a07164086024004284083c00035500600303036503140c02d5440b40c1c001802c0c00c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204553902 1250 204552652 204552659
    0x2b06030602040305070b090303040e0402010323070f0305010807140a031406040b060a0518070306150507050106080d0807050708070507030b01080c0306150d05070308030a2304020105191206 83
    0x798043c0c0400e503001d0103124004030318600781c14101c2c2e6118801500135403525191100c2c2c1d040d15000a0004ca04141d02e905217846204400b000002c0e100c802c03840b01c81070a082c1003401a259241210b551014141000e00400c8500e07004901e500071207028100341c0d50108200000030b50300c19102c2e0030042c90740034607800c1d0010b040400500d00740b00394490b0280b0109601e408080100071641c902c100c540c003070410103a070104412182055500102603043c0441c919032070303506140c0d407102c9050070500000d00118401040c42802d0217400b005017240800b90802c28140174004151010040103c000c1c803000054170001c01c000e0108036003246401900b0390b00495102d2908940e405003e1041082500c6481c1000c4010714000c0b45140c0100c440c000100c42c200040014420644175140064a16004607000080460b01796401144600051000014101c4941c072019050104084400071410703502d104000050360044201d0342203540900e5004100007210302e089031802e030304440c10f00f0218181003000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204555152 1250 204553902 204553913
    0x30201050108160e060d060b18070210020301050901030b04020d05030c0304031109090604020f0d0c140916020c190b0703030c030e030703081501090b0a0815090402062b0603 76
    0xa058a240e4000c0e9908861040c45151405209005102c0d0804c18100440c240e80340895946000c40d02c525004a1317908040303000690203d0342a01000f160350206010031007226814048110749069030542181154100703c00308202d0141400028915100da2011609550f0f4044d18009416440421079546804003010700b80c43c0c0e0000d1004491521000c580c06070765142c09440c0610400e06080280150703030f155020460b981038440201a0440c1080140402260580c00840050800c00100c1c0564800361800c6c4100814000d00d050040300306000c0303001c40f0550205800351800c00441c0c010b805803800e00500c181030328050f40110303003040000032508200f40d015042158100c195031070410420303140d120350740d03101e03c00d111005000908080006500341e10450369481d46004c18503050b80b54907154100b041c12036000761242c0380462001010420307401d0010302d08154900081e6465109400c00340e000c0350f102d021303d0004000d0b0403100307545880101c0104160009500000700c060149690701d00780f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204556402 1250 204555152 204555161
    0xf03070515010e0108030d2a020703152307021504050d020709052206090f081306020d050a0509030c0a060f030e0307030905120a08040b030a0c0f0905040b0102070f03030201 76
    0x1d450600c420030000098009040b01854100e03025403015600e400000c000071070040450030221011701003004d100a091409140207100a200d0b140c000385146415818081010001c0d401c40c140d00504040315085000b40420309900d080401108407407060b150401c0076820050542a001d01501d501400c1200380300e000100707400c040410f40c094810640d10340030403c003a503030109c5e800b0403190300c06420141d103160318040d0051040c0c060740e000214007103556100440141d4161081d1190000401d1000d082420622030400601240c001820340a00040d40a0494041d90f01e0300b106000e4007244101c42a2428082e200421000904424136a030700d0f0071025041c1c0285d620350381c0000c1c2c980314550520b40300000450300342682540307804144078a4081006030010441e04455214000c00c41501d00140c003000250001e06248a805910b0b840d01620b05802c40d140c003002c1d08200318140703c40c607200070382004180c02039030402d40e80852050302210061340782000c50f92110a0180c02a1400424103a040d0701 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204557652 1250 204556402 204556423
    0x306050a090b0f0615090307092d060302150f0c0a03050a260408131a18100c06150305060a0902030c01020303040c06030c0c08220f0305030d0e0f030705 67
    0x1452003480c1c840343d803440840482220f101d908200341c100b41c01201e0000a003d072404000c001d0482c2e942035112046801510712004c0d140720001820148501c0340340848554840107011942c00f0080d05c4d245400180e0001401000d1700722003880001c03264418940d560449240501c8041143c007081d11502e03000f051980310400000003d085840021910b160310f00840800708258072035050182c0b1030751070300c910942c4a000100c3c140600e80000180d04103000ca13300300da14483c044020b031102640d0001003c0048044205441404109804040c20781c20041c3c00908a07003194002070450911900f0307156600303c90300040d1042c45401c0c10480441480d07080004550310079000d07039400c02c15201c0166a01d00040da0020181462442c09000040c401d41c01010f4406403850301010440c5c8a4451082d0342d44000010681c0024020303114455109880d030381001402c490200707800e42c504e503848181c0c503805861071580307001d81c5a03481e40701c0300c90080104040e0340b0110015283d0b21107a40c0b80041e610000940c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204558902 1250 204557652 204557663
    0x130201081501050d0c050c060103030905030615011b030201150e060a0503060f070810051f0305060303040f061d30060403050307111f06090b03010e03040315060306050a09 75
    0x1e0905107080565282200043c0c484504181c4030008601c044c020052802042102c00c0c0f04406e5501000c0050700c1c025800303030b101ca1101c10f00300070130301d8202040108852000e54041d5034042c41c0e0b9a0044909000010300d40340c9054004107032404a0140200b05942007410114600100f859120044128001c0360200d0317500e08030703940c3c1f4004d00d03803544c80485102078200c01700c40000d00c100e80a642c031030754021740803c00b00061a480303a0008209424400080c0890070f007980e040c102080e0580719140c1c2140c0c0481c0114249840c3c0710090310002c4480c01071504000701002d101c00b030540c802511864441c40105843c815030264aa4440c0b4080714107087d204c008106071160707400b101c020640c0c5001780d4250752040d2555483c40c2c0261245008c2040440c1d09104280b07a5813192801920782c1102600e4440000c00c1c041c0c6000b100f08143c50b00c541450b4402e0b4034044642d6003000b00001110700b12a480400c440c0581046201c0d10020301145d0300c0174000300c0c00c16080000c010000c0d0f10034000d10b44600c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204560152 1250 204558902 204558917
    0x50a020f01060605160507031a0f0703060b040512010b04052818110111010c020d180b0a030b0109031202101a0904110607020d05070f06020609030913090803130201 72
    0x340600e4240c500c40d12441c2c0115408200416060301d40d8104402180d02407000c950000d6920360b03503605000315015182e40001084400d112081d920362500d43c0e0081150300c1d0a0042500300f00201d04c4501c03c0b8464288241c0e1840d0480d0b500c0039003900b050000300c0c0010820495440c08000e50305144070101705903103a01603a020b050f120317500355208940ba506080310b00d581c120b500968542c0c0d41315003884449030610002d8507000034003d00034051440d81352282d1380070b403814a8103100302910b500304241c00e00d030000d40c22405c14070591071f108003501c488214605c5c011a480345020010383c2c80c03010315000600311094140046501c20740004800990b201281c2d400c0240b03215610190000c031403c4400340d03522038103020100e008901342c0200684501c10081100703251060590009050004060017218107070001c14082000900e0464414010b040340d0000d4103051030003030740c1181c40f032017044e106071301c074100d2202100ba521007141c0c40312608a5021110a54a0502511428614551000483c0020250b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204561402 1250 204560152 204560173
    0xd0f1a0306070f021f0207051e06060a120f060e0d0c0b06040c05090d1e05010e0d02010b010203030708150402040b13051c06180b040b0714091809010e0d050a02 70
    0x18680180c285800ca50140181500c8520f0000c0e00e410034041820401d1b8080c0010404a001880290003040d9042c02c0008850304a503412401c0100c01023409208001c040c8040207141240444402444e9101c00c1d45228840d181c0340007001001890182e4005205000103240140d41184c00b4109950103285507100780c0d03560034100810380d07481c200040005001401100058105288071a41680c480c1d440511030750b0041142c0b449140c50f91704140e1325130713445081d042d0b15070005110601d02004684001d1252825000020f0340d41e2201611200803c10158009503180a000b0b103440c8a2140042040d5604d9a94080c00c3c3e07045d40100301482c2172003039528000903071b41c07901035901520141142d4103d103145455490380c1d03004100305101d07120f4002c0d0302000900064071032446c6920451291a0f980030f039044c0b51707000034060603003c0c40e4510150020022445581e42d48000b2600c1c243c800254038032542d881400d800c1c050311801c01802803078440c24662558180d0003c0280c51600e845a0031030721002e50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204562652 1250 204561402 204561407
    0x8070f03110a08040521032b02040f0b070305040506070602030a05070807020706050a120e0a0515060a0b070203010b030706031a010203071203091e0305030105011103120105060d0f1a030607 83
    0x281c1100007400300f0403c0000300500c2c2000d0074849030882c82c44007510ba494032055107081c00c6500a0500d80030701d082c3c11405400c104401c5038441c10512078070304d0850405041a2600303000c1400c81c01030b150b110a02103407040815204904650240c100581a103444000300e01c3c0c043d01135001525442015400c00001400c1d46100700e14445c41002d0542c020020149402015503203640440070f1f0b14200812801d606018000c10f014000c2c50f0404d480003004000c000e0f003445d07070800c0c030b01075803180c102c0d0400810b100155442840485c20307070701031540c0030341e1321565480003030700402e0450802905070150700310002c4c009405900990020000c01c40c205110500c11004984038421070000824804001e004000750303900c84d600000e5020712130008120007503424420280e14000f110011000a48008014812540c0c04404031008400c034500071801c1250710b216845005805000e82d501545002c61341041c443d42580061100b600304000070802c843d070b40d108640c003c41c0e5161000c0e0083c812180440d12862 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204563902 1250 204562652 204562663
    0x151c020f130e270109020d0c08060c0a0f08101d010e0703180f050312010f08010b010c080901080406020d020f03090d0912150609020a050d0c0e031504020d08070f0311 73
    0x107081201c0c031054201041180c980a05141910750f40c503641c0c8124130030040c0c9901541c50251800b03180c000400910300a002458034000500383c1011322014032800301e5294001042c104100614109403032140d940030349008402046500c8464101000070400042d50040c001c0170b4103a03a0702140d44030722640d541500f0f500307403071500d409040b1032040c04030390300003140d980032020349a0341c80740c4252880c00c5a846e013070038100d1000380c0204580301c20f0a80d0801c0203440c248910f1100d401c080c284980c10b5155a21222030f24002c4003420b505020700d0340005020424140d04403030380d07402100011501c42c0e1408891000580080b10941079900c0745c42001600c0c1d41c090f100704030480e10340d500380080301d5070565201c11000b92105401c2e0240c540b03404000c2403d400900250200c940c00e07554468480c0401d020390400d5070174140505060140b25280c100d030548000c02d00704240c420202a8181d29181c0d03102041000e03181180140803458082210b4081007141c26108000c1806a520100740310f480e04880307034861 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204565152 1250 204563902 204563911
    0x40f06050603030406120213030803090304060806030d09030618120e0102070e04020901031202010902130b18040503040b070c080a0503040f0801111204061b0206060103060e06151c020f130e 83
    0x46c4130400d102003101180c1c008021148908103100c41c403503a2661103200e160000d82d1600c02540011805101c169440808a540240c08070700800308000912009455800c0b103000141500c1e48070f5440c1800e0040303000c048184107074860350071204071100035001000142182000c80c018080c64800042c0712150400844c00360750001d100780309a9182d42d0f15007101400940241c03040d5502c03803489102599440e0100f08101c00183c10200e44110070100f04100081c61181010b03212400300144000304100009490984500d1072685540b4400b5090481d06c90010f903102086510a24441d03004204003c00940201c2e41c8440f00000d04546500ba42800d842c0c00e02110038600d0b01c20701008169440c1c100e403481d040f5000d00d60010f0300c407800391026141501408401d00c050f90148007800050b50b40361064800038403646800068600f0402d001500c12202600700302c20088002c24524880d11200200d0300c40c0010b001c004654038020a600a09203410603400c0c1c80580ca4001c01c00508500d214400e207228 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204566402 1250 204565152 204565157
    0x905120c0c03061e060102121809060607030807030c0207051e010206100b070201050702060903030c0d02190201080f06060c100605031902090403120e0f010b040b010f05041a12040f06050603030406 86
    0x4189122104c02c202c0f10703006000354114440d02c1c00716016121080010500b91032025009200f0000540038001d6404001e001c00d0700900f020026100444d03400911503400092916001c1522003e03280b04130b140c44155002994441200c0181401c05010b04204c1001402d003038003590703416518801e000c07103a687d4612614554030000c00040d80198843c00040105c2880102a1814122650086031464002d10341115440c1d11040b0520800782c0c0401c20f45c4c03145100f0161018042883d5070000300741d0840030b03100300e8445a100001c035045550381001d0314060880c9004981005187c03a245d0805001c240c8a4039010303002c3e4070600c80f02c12100c0e10b0755102058005e0011032250322039a504568400f040007a00c18803d1b0745000011050605014a18901d4415000811518190f000300003c072949032081d01d0622000c000001c5203542c05c401941c08481e003114400f100d40d6644085441c0030b10a0100030840c0c0280322003004100110448020b113403a0040d40100041e5a403041815070340d22590040d0000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204567652 1250 204566402 204566431
    0x5090102070b160c080a02032e021c09030c12020a11060901020c040e1609021602060d0902180f0f060a14040609092108041a07030905120c0c0306 64
    0x41000d01c40020a40d41202e02112943d45803691500180c483c4c564108400f81c1d00081d0804080d480d0400100d0011440006406c0150000c41034121b01d150045e40b500d0561500403c02407006096554140311030f00ac0500c007400141c5051900070b0804000710402c403a440c0e21407400810491002824102d06980f00748a00c3c4605c24120400c601070f08035001c0c8174110b1040300100401602c1394014219241c03101c03001405210390521a01080c1c20003a0080320110740306103c0d0140d0381c01385031407070722059070140c44441d5503120701b80c4104090301e101c0b003010f90840c2141c88440075400c00c903008184911040c06801426468114080c105850103846c604d600003846103003407002890400c8200e80700300c4001d2000414039030782c2c0002e2081e1a01c1c81d409448240ca40d03842088003842040c508900105685003051462400b0340d100006040607460044915011754005200c0c03900036801185096001022100103030340715400b0701070982c03081030a14402c2c0035040d0f400c195400c0005003940581c641013007220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204568902 1250 204567652 204567659
    0x30105040b030a1b06030f020c0709051306060807060806300102040f09020403050d02060c0f0d110c16050d111002010209060d0606090b12131103030a0c050105070509010207 76
    0x107001500a0590b043c00303000f82201c0010181144101e40e4492001c1c03281c8070350310b449400b80842d05401b40004401d4010032208a000f01c011030118261503115000041d2504c5040941c1500e50850200410f0301d031030a0070100700100700085420480e00780755207400880e40c44006101700703a034a0310b20740f541e4004403c0d8180705807400012102002188007000509051ba03851009840201b0740d449088840c2d4005400e00c2400414844000030050760300003010942002c2002c48200c0c860301d14403e90701c1e05d000c1081c40c90b0143d59041420080d400c40c0e011078a4506c0401c2c401c0d1100222040701c060208440d40008aa081c0704d200005425000280719014002c0d450038020302c840c6e04502d0700d0840d5400c00011400f40e4826000e0204613200340000140242014000303408c000c09900b000d1041d0f4024000da034801c842290000350f01484030004800146464030b404030a1801c0d612504d513141c000441c44103d4aa8000f4203030548a0140009005d16100d010040e2241e01c9103800e246e005810903034062 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204570152 1250 204568902 204568909
    0x120c0a0303091410061404022a030f0403060b040b040b0a030f060b04050f0a0609050c07030c11280f0614030717010603050906060f010e01030b03070506121009050c030105 75
    0x24091800382e22040740e00460341d1200d50414540c84c400310f910b40d5440d6070034810710314605424004000c09641c118504104903901a002d15041988004840351800d48450041000d0080d15842c01d103101c2d0030343c1c46d2501e0b441e2840c042d08109241c3c0b40140d151059040c99445c2c02d000d08004102c0180054407024190740325401c0402021605a440c2a152103000c83c0b1a2106d02c9a207201c2d4003010704a42d0181448694a0f0a03141c00c3d03072212a015040c0010f20040c0040c9200b1520b40e0355150600342c00300d81451522540741e808070207140b6071000c0041c405894501303d040590084101c0300840b124015141d20420103100340e240a0040000d00c0601c20b0f220104041e030085401207400d042c00c4c0f0901c03165459800310030740240c0150b00040d48602c140b0400344001c10419802000884910700b0300044280002c00f6822013003403040c10103855032a2908180c4040c0140e101074540501000e5603544402200000680180e584080302c002002002807000d216105240c040c3c406008904d00d180d10342400c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204571402 1250 204570152 204570161
    0x21b09060609010903050a030c0b2a0714010c0914010207140103020304150c1805010f0c0201120608061509010609060e0d081b0d080117071505070f06020903120c0a0303 74
    0x3080c2c14405004d202001140c003c120a4084038482d03543c06507604414a42040c01c28800b07841e13040302da030a0111406004031304e01c00c00361405141410043d00c4240ca400d010058401c03001d440d001c07651900706603446035a40103100c0000d886103161326405003502c0c07100480e0b40c2d8045101c3e149011049614862040d84203070019034000c0d016510a070040d28502e620602100d21171468032011641c425002c50b820440801058014002400d02d000c1042d442d2401800003000184001d0400c10708001c0d0ba0680c160300d521500c0075004040841d86586440f940402d503040240101a1050b401031000003030303481c03103610010141c0d985036490420908058040c0250f078100d8201c221040c420a00502c40560b0940c2d21482011b02054005c00b8480d5413581c019101e400c043c0c00009600d4010346510640c1c12000400308211600541c1c2c1c07805224107012300b02c6460081c40401401c41416140400500560340c000c0c015a10044042d03c0c0c15078050419010548a540490b181c140c22140e40240401d000384d20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204572652 1250 204571402 204571417
    0xe010506210402031f05010603060e0c0306100207150e1207180f02040e0a2f070803060321070b0a060f050108040f02040e150a0b1807020a0206040303080106021b090606 74
    0x12989200c056100704014188500a80303070482d99101c6c010440355074140102d50081c41400a1ba6103541458511610303a03103c02000d5502503144880c2a9a13800d1007080307060002d002c0c007000c44c1d45e90342c40c409009088001c440c8407507229040c00c0e2515004a00081140340449000c04544041200c410880c0303005408021481c04c04bd40e42400f000400e600805070092240400380800a1440381500540010102a00303048410f21004000c402d94030300410200c0729195084409591070341e0b64103000a1404024030701c26001c80d00030541404107080454003134100b41c5d228210b03d010b9035840c4d44e030f01c10440c0c100d4170801004080e0f010080050f07501034130a80360440e00940030341041e101c0760f4000c28103403120b041a0000981c011108408950840d0407007581203140c0b01c1c4140801c10044e000600000d100721103030900440590702042c1464000c0018040c40c40e805001c5e661503640c3c030b083c0a0107440c824850480907008140c20855030300501050085200c00c028a100e0b401c1d02c0701030502c540d5410001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204573902 1250 204572652 204572659
    0x11101060b0a08180a020a0b0d020403050703050d08011a0a050c160f05100203090a05150705120a0905012f010b0a030609050c090f190f0c02070e010506210402 70
    0xc0c04a24541e124005040d03103002600c80308801c0c18000b1284019002d0410490355541080c815900147c0da4030700404100c1e203000e940140c50701403040e0003100070720841d0320050180c0720301003002082000c0450f0800e1504016152a001aa070b00c103442c801c40030b55203000300901c403020420100c1c128003900141501d12101c00480f054411141508550100c1c4e5400000498004d01820484d40c586182d8540074205644051810850700c140410b00340c040034003507284035001c041840c0e01c2c00c1003107106480e10290401c0441c0c80384510394250760459030001c10a00300040d0005004034841d406541c03840980d07000b50480c41e90012144170084005c600700c0f100840a03540300d903a2540c55581d0741503c10060b41c0210800a8a0b13030051a00601e80f00b0300c680c3d2a801207030b41c803042080105241901e10ba011610310312003c3e1580d10000b0010040c01f2034110303410b00074504602e00305850f0b400145070013074542c07001c0f16080a036200c2080201d90300645241e9800b81c443c4000640b9072a070440e03105a002172024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204575152 1250 204573902 204573911
    0xf0b04180e1501081c0206010b0901020c1309110d0206030a0b040e0a03080a0b010801320409051b0306060d110a051f090f150e12100c0305090d080402011101 69
    0x40000e0b800c00c0d04256490000381c2051005006100081c080e0901e014111000441c01da1202c4c00043d4441905102e00a041078001c9404c2005034020301c03116a2506004040d10a081401c403801c178010000140207842c4800440383c0140c01c1d08002011160305138000700b1150640d900e62240c0b0015203e820203180e00640c13070750409908440100b140d01000e0f0b1094690004603d06940241c080301c1c44580d61038100060480100b110030090780282c4a040c00103c6c1c0d004c50300d010212100d40c881039000e07805030050300d0600550240b1402203009030344802e08684200d4001e038880708040c0e07249010b0300d41c80e13440101c000740f09002984007000b584101c6006019903551a0303452000840391414200c42035442d0300d40800450364194001d81210203491301c511028102803c180faa004d21136540c11080c0e01f4800c169032801541c0d5100c1403200e50b4114020200c80f103005c41c0c80720200160401481c00e03c0401d0624002c61420718010401e000c0d508a00c0c0c2e07800c078950f50385400440d09103160104000103551b03035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204576402 1250 204575152 204575171
    0x40b091204060e040b04140103030f2a02011b030e040c020709051e0906160813060c02010204080c01031a0603130804080105060108090a0c1e05280f0b0418 68
    0x1650041c0c0020059511000584009801804103480041c0100c070321075483e03c058400400d40d102510f0341980d0b007608d040803882a00800c280c0709610315244900e02e2403005042e698010318001d203100d070800c2c400e0342e42540e61443c03051b210b130440e0f004540050201c3c1c4000002c2c049800c0607400646580814412500354594418a0004480c4281c07003021004d03076415022194150000c20b1607402a44102c0100414030f80048005a451114550391082105020101e19601c11100342007804c00d030400710030441c1c03080b000e4004c0d000b503000e882861001d0040d80300b80d12140d8000d11540314098503031000c0700d10110030039040200b59440245010780003841160700c000442c6d029030107070014003481800000c103420000000f41a80308000c21410590340103440d4200002c1a07031415500311160a180b4034012403039000451200c0350150061504188000b018845014000c46031065401c0d10a84022905c0d8032040c0d564000f0546019452607560100410402c0f266500d150400c550300742500082c50140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204577652 1250 204576402 204576433
    0x2010b0f1023041a0309150a140f090c0301020403050712020d0b24040c050a1d060a031d0a02102109080d050a0209030c130e0303010f0f1d040b09 64
    0x603400e2400105a00801d050104440401078403040c00150b44c0b40d20304620348140e0242e82d40466600805aa01c441d0000c180c0810464102c002000600d80d815a00d514020403401c048103c1151492558805c203d800d24845c10180b08903030680c1c1c0c105014101c91410107282c1c0300200c0803800100d03000141c060001002c11442d544840c081c1000288110f08000e41e2442c0c4c0c8282c0322400e03006c1303124031314000c0c1522040e60003001315101060b1608003444100e03c08a10081e0f030100c088020740d045540003035422419513040d403012082c621408130b070444090032031800996500b03030100001d4109900303040804005004415102c030001f00c50b003410f1001c41c1210803a50540711016000c0f518400b0204251200300b0080c004c2550207042143d046081140000009988440c00e40f09180039402c1c3c1420304401d009071360420221691408226a940d50303449481c11354400341d0340700700980040c0010021844110780c424000003074440d80c50800705529030341c031000c03800d0b200500182901d2140d08902c103803450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204578902 1250 204577652 204577697
    0x1a062107090305060109060b180102100509030417030304050a1410060e060102240105040911030303013b0c0a020c04050403020d120e190c09151502010b0f10 69
    0x21800c0d5180850715207540303411480c112040e0001c0e0069400c1000600040d51828180c5104203244030015180444500060741010301e80c280d544001c50420f0100081000b00100410440300d2140c11784002050542c08144c881c0419140105250404168040410141100940500c10398401e807400341c001c03540c00e882100e529510885192544208102503503070180150710700050041c1c41941d00d4a20842c6d4448007043c1400b429102ea584c89011100348076516501d81240c1201508480c0d07a540c40310003002d080d02100300c0990010440c0c451481d501203c8030b00566141504044030f00068585003900401d5401491100c0c04601c14504841425950313401001d000e18081c2c4c02034041e003d020035001b042040300c5200000250b06000140d0198200082c0c004805090100c4c001241d038024900050455525448190468281603200880201c1c0c0c849050031654005201180d1113107120003a42610500b07100c040e44010302c031b482c0c540c0604140d90400b080b2815460915030b064002c161581040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204580152 1250 204578902 204578911
    0xd1d0601090912020c030a14010207020d0b0103050106150e210d0801080705040c2309210c010804110d062c010b0a0302100e0406030c030302030304151a0621 69
    0x1682c550b0b010350280141800a1107004400e0720103050b41d6126070700401d566031a941401000d40b0780032006542400406c0d4180d400c9254000d220028081e41410403060015080c0419070743c95103882c0c0002050a21420301114010240d100c040009440070100012001c03482d410b500701070b5200c9201c603c01c0c00140411600d154440d15000d4442d41800c01700741c500380d200c0e00010300851800c4042c283c0d007a00f0070403840002c800600c000e0055203801e03400541300d009075010650028500d074000000800300c0c506011100707080901f150711000601d00119a0a1001d440c081c0c40c1802c04000240c0a040c808035196926028000c0400c004000d825240071304030119101007400c040844819180c04402e0180c01c206000840340f0885150031a000a003800c00c11102c20424401d0316851000b140e00c480d04200021900840f00e200c5547c0c0d0ba04000c2d480b6031007101e044403c1d00700c2c1109800541380074418090003071410800c40740b52168400621445070711010002520014800e55441011030b60b201344c9206 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204581402 1250 204580152 204580169
    0x21060d060e01092021070503010e1b010c0803040237180e0c13090f03050405040509011b0c02030f061e09030901020a020103180c0605041503110d1d0601 67
    0x655a190402440038106018440d0f000130708240000c2903550703401c403400000c0e60805110745144200c0c0035441d10b020559405940c140d401c01c1e0340da048511001c200e0302098100c0030f880098000070034004654034000c0c0300e0000c20b100340c1400420003504000014040d141d080440c4007401206200000100d160544c5184140d90303080c00052007030401d2400c01110038003140c5005d120044c2140c0c0b0654841c646541414001e168000c00c1c40e00c40142038002c0aa4a600640030300341c401c0550800078070703c0d8014042c250180d81407401003410014148944e01454400f2803040d40200581d450441d41c007011044141e83c507101c2c2c1c00c0721001c07a0f0000e015035800380e21428841c050758498003598040451008140e02140d4005104000c002c2c3d8020900d0684142d092a00150207801c4411020140d00400005803d00d03100000104100e500170000308159034180006c01042110b01d14201c1c1500c241c00c01c5117000c0a0103109002001126401c501640700c0c0460491105102c3c84190030300e0444264000d600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204582652 1250 204581402 204581411
    0x606031202070905060616050307080705060115050c0a23030f0903011119051605010509060a0f020a0c0f0204060b0a120f14070c060e0f0a140321060d060e01 69
    0x100c2501044520014010141c09208034039190001880d50b0140b40c1324083e00e21040c059840400c401803040f0740c411a807103a407207a1500c2c1d81d410010f40e0350509004040c00300441041340c118640c0101c00f91005070386400d008289403c8281d450015821045080600d201e00640c21a155400244050600811000c0b900c2d41c0b074884800400d429601c007400ca41c1110301041081e410100600c0e00049254030711401e04070380e5421020a00184100b140c4009001075203030406000b2668800b090f4580507401c2200240056031b0305c9a5014100d114200b240408100b524801c0d5000503141c40c0c02c05002400100002865503030f4034880c80741c42c0d001c42061800199004020081b20840c2c1c4103941000c801c0d6203041000d01c0b03659074400360004001e40103205026030b095483c0c08001d400d80044a80c09990019039420400821a1641e240d103540801c4600c2543c01002d1201d040c0000251740d070500001c0000d666480c2100c0044001c1134014001d00e41040d43c2c0c407840004503449009040c04955520000107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204583902 1250 204582652 204582683
    0x303050316140406050304020f060d05060f0a080c0f04020903060f04140d050f130f0f08012403020114091009320105130e0702010203090d0513090203060d060603 71
    0x424481c50315034880140502200b1245240080c81e0584007590400d06040b5030b262900d0001810700306000f0b440503484040050a5800d041154102602444069410b050000554000c101c0051103a000c4c0c000309610010241044d441c014100700c00c2d844000d8001454500a40d000c81d042c01422512024000c10300701c240001c1107000c4c211550164000809001c10340c15407400244103201d03d179101400e0210100d01c3c0701414018039200c600411000d607040949a6a42e07000080c2d0b011a40704145065184c1810f540401031045503441c01c080c410340c0c580d00340c54215401034441008500100a401209201ea0086901c40c1103144400c0056030700d6001410b40741800b06400c84003041203d680340740303620302c1015514000103c0780081ca07609003040c0d525100209100c2d1180c0000f68030800d8084842c5081c013601513019070081d40201080d400340c4284032403030201a42e41d4461561401d00640c0b8058007000481800d501958000400034110700c0742c11040d03128142619155017042e0b0321302a42c044000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204585152 1250 204583902 204583921
    0x90f050d02061008070308070201050a12050108010506130b090402061614030403060b0d0210230f030f0f391b071d0c0702010306170f0705181b0405060403030503 71
    0x80f0003009580001c1c0721260441d580d00c1c609005182000b814048041065902d050080d2941901424415000c011039a501c286007400307400b065450901800703542c007000303020640c18020301100210144c601001a00c9175030a101d41ea0384820800b10900982008000001d00c03402c45450980c0c0010005546030360031828814125841d140300b240c45455210060740050321121100398122100d810290504501d00d69045c140076521500180590307000240d560503040000c011707502400001d241d054855a601d02d285074611019035600c044940700c0c0d9411104408000040903004040046034554080d40f01e0300803c80b60040c405600c031801c01c502c45d000c2014010840c200051607240d08107195400001440d10420401078640c101e083c00018404c415640030740c0148005083c409214004140072085071a201ca02c9251420094007511100058070319128441001900b03150078006466252000c00d25100740303c1d00a01c000481e000d010024590341d8410182008600030340f699640ca103090000c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204586402 1250 204585152 204585181
    0x703022b03180510020c0103051f0e100905040803010909050c0a29090105090d0204060b031f060302030420010c0803010b0d060905011a180616020102100c12090f050d0206 75
    0x2806646441444000c04d680022001948003080c03e000400e503c40c400c1d20b8030071141b144070380c903a01910f00070b00080e002201d03d1501d101e80d10359210f904ca01c9803241c52070301c19100142c40143c400366040c00103002c81d41543c1d001c1c80c400c6100d8070407500f841e9480c0000c18a42c45050348500d0511a4503945a5028900c01c0c0c4d50700c0100c500c10400c240740a1035400060b00c103000d0010098003a103c00c016402c1151941e038400307405006085405034992404d100c2c0d1148403000d448144000c03c04116000031034a00034001d0701d02440d8480e540a541714071155401c0c600180203150b150401c95100c00e1040840c100d40010340c040d10b104104650f4401c13400e500038080e00c2d09030303216030011440d1900400015039100090170000ba000c50074150f8a03544820700844c0c02a4018443c1d40c8400300152040b8400d02d600c2c00003c089100381c00b44c1e140308500d000050225035422441e50041040380c8050180701400b40d20600c55648101141403008000e42c035035031b281c803e01d6046032016a0022050120f100040300c1d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204587652 1250 204586402 204586409
    0xa0305160b0f24030d141c0b011d100e0303120103050d02190c12031e030903030b04140402040e01060801090503090103061a2212051f09050703022b0318 67
    0x450f4030200c1d82d81c10109076284903004142040180d15040385c0005401d10301250f8040d20026102d0850080c5001c0310303001000400c0304c0c0c6011441200c42c00158149400180f8480301004041800d40c52200405468072080031035419458002041131906000754048840d010f14090001415806401d03140640b410503818030170b80d030b003003200743c2164000f8140c42441c0e001d4400c46085000035460a160540b04105003001100341090300325a8805015416031000750014041c2e901808160440760500040750600c42007001440e280c1c000080141c102600401004102000001400c4d660785541c41d0031902c40c2901220960030000e01c40119681c10300070600070742040c8028000300d03c000d14841d4070910510000c100c140140b00e001805003828440a44001c20010f88a202c4a404e60700e000c0d5201ca110031072545000b141545100101c240c00c1c0f08070110198407400400819055800300802c0880ea03250344081c0c08540c401720001c00100c1006e440740030317200352248034140c01610182d180c5042d0727031340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204588902 1250 204587652 204587701
    0x50c0a050301060b040b1b0703030f090e07120b060d061805090d050d0e2b230706050438010509041e02151c0509010e0a0305160b0f 58
    0xf8060064a40d080100e40c1180c01d031440c1256506035550580e803a6100644031101c0380d0287c041c0000c189500000c070350034400c11307542d00d624030240c45070000d00d5084010b80750000018081c4404100c428000c2d4041081d10300000c180e2420104c0030f800300701c141c0d90150010460310201c01815450b02031180502c90304503081501602a080500750010507501a841143c0d66042e12a01c084100100030320440e02452184002c0c100410300a060b0620341d8000440250000f455441c941442064038691f6002c0c03000340485140d2900d01261182409480098400e941041d04c200b1449002c02d03508108005400728401e003035110070300c0138560440c0302d201640710a0042a240b0208400603d100e1840307519600d6020840481031501d002091460034038842c0400b2901000518118040500c5e00b200410820840300f4005903540160075420381d40c2003603040009a012001200c0081d0085019062060300380802d010394070019210380c88941030996403500c441140905100e2540c4104100100200816 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204590152 1250 204588902 204588911
    0xc0f05072109061d01050a0813080d3c02130e0403020d090816090525030203060325171002040b042c060609010314040524010e011a090904050c0a050301 67
    0x90001ba02c03501c207825a80040280c610700050b200714555401e092a43e4000403220307283c040d01c44010009018000703140b401480c1c03170911610300013034160703401d059000c050900d08103690051a222010350008000602c1c04400b00d1004100815601d45013032240e8002e81c000c001010005070043c204442c9a0001546908111016494250703441d000d001195407000c000591a510308250840d0700a116078030b0f207170010844411003086541500650b009041c2141500c0007652102c0e121069410b003031520f4040405415010005038030000c1a40440b0a100700a446860042030014400c0780c0c06030f003256024503408141071205034540c0348210407651650304045040208440186c5500d0700045ca4140f04d04000202c00075240d00c03130707005160902c1080c1000d81680c1814507009442d00004032154021103041c91400340640d022000c400c0c1250400e82590390189d0a0401c4512490941c8604082141042145014503107400d03000300e2280e40104064540c8060201c1040a00d0065074041403113a0b051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204591402 1250 204590152 204590207
    0x31403010e150f030a030c060605060715051506040902030412140d050702010b06180315042001020a0807030503061905010e091005040204270c0f0507210906 69
    0x7144a0303030b030030100c00b12140850302c006600103596001c1001c00c01d60180034540c41c02c0101900201c1a6450038410312040c0021915601880000e0003480d1000c0e1000814480680d140101d03540415001044224000b40b080d070b841000c5601a4065408030040c194004100002e1105400c0c0e10782d03414a8916102d4071071081c0142540310380c061900b00111082d684c802150a45000b50701842e070064000c3c21351900d8016680900c202502030300c00003802030140221a560140103c4555841590710052060343c86003969020031510449420300390642c480d807003100001c14266005404040d1103940d5496803407420f48180301c40011400b41b032030740400b013002090003560381100c062894468103548524a503030300c10003416241191a801541c00c12720014000c1550142c0e440310342d696040c000b03401070740f039407006407024212203189103010005070031040100c1030644039100402c201030054001b4452500c6550109010409060541001c260740440030811300743c21131401c0200d11b10345d0011030411b642 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204592652 1250 204591402 204591419
    0x1a0f0309010b031c11060c0d050a0b0a0b09120703020a0b03040303020702150301060e0a051003020904020f0415090e0c030c0a0c020909010501080f0609031801090801020a0e040e030315040c0e04090f03140301 91
    0x88823003d154a81e19000090109103503644410b0070014000d000c159425a24014641f1a512040205004114001e071080c03030203400041c400121f81e8003410b05901c00340f03000503004003500040c1003241090303002c000a90269507a088652400d14240c11403ea8951401c0809010000b0521009018a90b14070302000165034481d0b110400071210b003000f5940301e5001c00003800a20446034802428680484c011506100c06111036011030720300d4941036215a01e41000001c2c600c1c080b54a841d1454003080015840c0a03514007400500d03489040c09000a5815130001d954803204444081e45a9901d100401c202101040207110440900001c0c0829040c204c0d02c1c07a4607482200790084a04807880c200f41d0b0140d1207984001c0c001c00a100085450344c08050000341294181401300340318038240840c0071081080802104e00070a548100d106249010005002c007400d41e414546081c010000824502a00c0381c0c014118158820011940e08407031519001e0140c0700d02c80c01c0c01244c09010702c0140700d68003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204593902 1250 204592652 204592657
    0x8210906040615050a0f060807020a110f0a0e09010506040513020303180117010e0123060d0504080d060603090614040c0b070f06020415091a0f0309010b031c11060c 72
    0x1608080c0c0072078000e003140c0030f00c1c4041a42e9441250001e480d01c0e0700240700f152201203107050350211b56400600d42c450b247d040ba44c40c030010b400036100e0701c100ca00b0303510303145041c01d6800000b460140075400c1203983c8910505c541d40d8212a0243c0c07503510342040280350b01d854403070143d1047c907a00130180b541c4c0850700426904c0c0208000e00510020b80307405560035a00500d01c00106104035149180c4568584030b21080201c070a00c9184200684a000d818000039189007004c0701c2a406000507080100a03020100648001340043e00c00690130400782180d40c15134002c10000e08803c0e100820b50148500d822811030f0440c1d00034050805e0003005020019075044d40903801c0b0359071b0a600036201c01a0307080602421044100c02003030700e403000400050420415100c1101c00b01c403a203c56121075925110f00203103840080c50070305008410040c40001c02143c001840c0c000c40440000180c01c9810303004a1f242400c04600582001418a64181c0381035210149502c1d000d4110007625541c1843c060060b810b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204595152 1250 204593902 204593911
    0x50a0f090e0106030203120c12030c07081305100c0308060d020d08030c0f0301170f0706020c120f01021206270604020901020a020d12030e032d1608210906 68
    0xa501c1e2039075115020030075000071000d5a0020203072100c111101001e184558090b10240c3e034140035903040751200c2c80340c40d41640d1146042e41016803400d02d85d03945000722a0f20240c1c0212042080c060041195101e00001c1001c040c1035448a40300b0440c81e080280c810311000340030030b02c00d510b2203940000586030004888030302c6034003181040d2a43c440750700c46551400350b441c41e080c0c03020000c0000140450f000144081c6010aa070507030b81c40d16002e000203070700e90503107004d24405030b4085e2001080703030b042c820000314500071701005840baa01310602a40782a0380c8482d043c2a01c24ad10310b000d00525151510045410000c070f40f03c521840c143d200c070840c980000041110344603d902180450141e4000d210203074540782d00030415020441c1d107161040f02d0205905800c0c0000345401d0003490302c02c000004a0382c2901c41c40c0c00003000e070456091075032a0302040000240d8410801c1c01504070307c140705520151583d214680d11500ea010106584001c68540c1030b8515100030044144403001e81e0204230682c22 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204596402 1250 204595152 204595169
    0x14070c03030f021509100b0d022b020415090e0714040207171606050c160803100f0b0403060b09010b0702010e06090a08061f050a0909110424050a0f 65
    0x301c0305964416402c04d002035929010514a5800304140c003840800c800d002c09a52241c200311080382c2d10705024101c184c1c103d009420013040a03001c044206000444400001080c900c40d2001543e54041010f551000070b9441d80d100d00030b0070074032840d04240901c030540074040c802080c2d4240791408820080c28000b410703a0140d54001032600034006261402d428006465071a141e90f201a941c8400d140c00c141038003a02c241d0b00d08004140c42d081c1000031030f0891541182030080801441d00c4003052035002400020344030044420000d40394101c0c40d06d0400900c4036050550302e4601d14141601a208040100362150058200610030310740620150761100e502032916210310120b0b640803540c01c1c81ba03c1e495640c4071100703050000754103100050546c031030468101e44040c154141420361048040c280035456004100800a000b1411194000708145015240c5560801074001c0030504603a07601140900c20341315103140100c1400c0f1a01480010101a1141d0540a00d8018020000802c0d400345030b01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204597652 1250 204596402 204596417
    0x70308010e0a02040b070b0601021006080a140c0301050907080d020a0803010b090307050916110a11091909030816110303150f04020a170a02040501080621070803030714070c0303 78
    0x1141d01c903d40c151000351119110700c1d60b80d042c15003003460f904ca200f103902074010320441d440525025224010401100c03821001480b0345103003030740d60b0a03000390074903880072152182c1900030180381d4003402580d0060410320090303d01a4207060410382000400c41c46a415135000100d040c00090741441103d0445100d10700071071300c0c1d0b09443d0020f824440d860340300f540c0c4520310300103005c000d003260f0498850220340b80d140d41e00f21748403035180a615011000b5020b8040441208240224184038a0096002000140300d44541c0745402c080011500050010360010303c2c00000c000945d50560140d0000b8203485c18408010750822000300e940748002800040708020340d20003c102510383c540721824134040200207540300e20403040000c00455405201c03400e440c01c004041941091548200c3d0203561044c1e440c0415030ba1210140005070301c06940c0b501c8861101d400600900401703105000281082001445d5203007054500140051b1030b00850390325000b010061840081e07414138158084940c1802c2402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204598902 1250 204597652 204597661
    0x207050d02010e040c050d0c030b031506121615020c090417041805061f080103020f06040503100905071a1b0c0a0303050a020111090d330f0e03070308010e 68
    0x710f0390802c000c24a504541860622040030381c0040c050720354100e61400421605240701012800d40f4156540c103900764020103e6503e054103601c0c00d8980c85000a003d00c07010781c0344420034510300080d601503001c0140a402c01488140112101118452041e2004240c58280000014610341014100400c00e1018a0204585a20240540c0d0041c41d610014200168a81503240003500048581a02c50b01d1300d44e04400c0c500c0f0310900100d13003800b4182c0d1400d52503030a40d401d000340420160070039584138005000008060b50200603103590101104000b0038142101c2c075159241203200c3d04001c41d41545046902840d030410000d487c994940e001003424480b2010051904082402c50140d400050f800c40200915800000030700c5291074541c001c0101e1800c45074035210320300480b041d9581c40800b05028a0118a42c40b002c084642018680c820810040e40039611040e010740302c52281d01a00e40300084c01c0700050b072044aa00c50602c0300074610b8990969401043d6041c14001d81c2d030340307803050300205 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204600152 1250 204598902 204598907
    0x6010f0e0a0906050310060e0f0702010b090405030714030408121606050103050616020102040b0912011104061115460501090c0903020f0409051002040e16020d0207050d0201 76
    0xa11040501400140c40c1c6a207880c0b221014100c01d005841c000d02c64004800041c003800c2c07080c40308482400640301c07401d0b140c94170000307244003002d420141199200c01400442d95102d5400307501452041e002541d0300e00482c33400a409000604229000790401c1c441080070741d60101d00d0222103a83c102c812903460625810844081781180f0015044600d483c001104000b00058824000e143c80300038030621a003410b00032401d07403142d405030b600311210a001885c1c1c0e90038880c4d20348000c41e054800100d05400000c6050603ea04194890800200c1c0c2218040203107100344414408010b441104202c81c7c5440318101d800403204080700d1f182e48900c4841131005180c40b5840412914101c2c030240465030807600101c0117002e00703001e046483c0b4680110056880d020744003920460750f01529205034507400310b04020040c40300000c06e4a80740222007603110242c0307040c03004201810480150388461700f44000d0840302e03040440411015984a07c443e11460341d00080e061049440c125080010960240b004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204601402 1250 204600152 204600167
    0x50709051e0d0f2d02010e010507030201021b1b0103140417070501060e15090402102f0d0e0a0e040b130f0f020f010207050901031716030201090213021206010f 70
    0x280100c0800983d400400401c030218020000114007060f00c0000c42d4440071001d0400084000e01007504106040495400360b4003918842d4000c0c000103040810140c074240109203140900089508410744404895004416400004000f841c04000c06d8410200030301c610303000030340050000d488504011031280c1603402200c68160f0b1000007801081c2c3e0b10b0711200c3d405003080e510f100e402551215699268100441c0d864400d0b60020076016195001c07500942c0d010542070080098410b102c0304114040342c54810b5949074541c00402070029858100c4020201c004560039240718418003842000020340b40740c8419041131b001340045000e40c8076016403044540c881100100a26115000c1e24180400941c83d02e40390340c002c0c1c4c0c1d601c544c0b070b40140c0120384410150084950101e0020018130118028507404184c080b2081c5e80300d460700c0c0c00d40b0704d207822850ba00308085006030745500c003900c1181450582082d51580e408019801d20519050160002400514560402c205a114241c1d401d10858a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204602652 1250 204601402 204601429
    0x1407020411040e071704020f1011010c05130803040e040611042105010605030706050a030509070b040f03050c03030304020f0103020c1002030a02040503010605120307120905090c030901050709051e 86
    0x20940d03039540c0d50000040c0001c4115440c0010424018226948016117203d80303105d15802458444008145801c100c15a44061207050400081c010300b4400e500c000d01c0340c0c0d000c044071501c4841d122000c1e284401c0c0c0a0000e0340004074550000d04c000c00580313400c0500c403908540d000c0c00104480004503885056800380f60320080d400061a40100141074004802c00d030400e0040e00284892500c0b0014503503904000d201d440000740c01000b04001c0c1520a070f20040d0020030389002d54030001d507070f0703603914405400a1300a4150a19017900c20400c004081000c0e00305910b065000d503080d0711f441e800003000e4201ca070544505054001400751610755090040c12000041010115101e080500c50400250064081c1c00d00030340ca0324201203002e11308103002000ca5031a4000841c90504950713039107000403141a5209050161242c00410a5942d40304414170403100316003426100d03d428407404d429604082c06c69010301500711018082511003070035406c40d00040c142990071f00c2c035418020584540c0b6a15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204603902 1250 204602652 204602681
    0x1202030c03090115030c0501051608070b061f020705060309010e0616030b040515040b0a03080c010203070e01111c1413050114030903090409020f13060f1514070204 72
    0x810000c0000400029501814401008200811100d90303408090811360001a0102200040c20486507200700f0080040740d0000380348981542a42ea1104203a4010a4046a00d040d8410401440e0700b0200c0c8106240031110a030107103c040d409102a4840384640101401030000000140d0000700942002d40707000c80302c104580710791829075a11600d10144401420000c1c0c1030146031140b502e420701496000380d240005000030080c200b030400000300000528640c2014400c040080030a5821002c0c145140b44000003682c0d0746098500240900518540c40e41400318510b1340c01020b81c00040c401c043d141c20ba071050000310100c2e00c0192070548400c0041d00c0040d20016080035170803040300034a01291400e072100b040480b1000701d042c100c1d02045400b01c0d2280e10a008002c500d2405803c641e14190024142c0c408032000355000c1b03098500700034010078030f090301c400c02082802940d1180034001d0454001094403486500340003442070342c00c0400010340020124841c400c2d0f569030760180754800d4442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204605152 1250 204603902 204603907
    0x7080409151d160e0a09020a020a08030103030503190908090f0f130f15080307030305060612091b010345140f03040509010b030a0f06080304030b160c0201050a1202 72
    0x6001d192205400f200e11408552408030b03083c030254015210340059800041c5110102c50501840400940264102c08114482c01d482d04001c21100c40045000c0c41c001e580e01030b80d81c51300c0813400f0130100401400044051600c1e401c18082103440c0160350040b4011251040104007110015449140f0380716550f0340920440300128a00440e5401403a540e02501411720402d03960311130300c001240c2e071303403117910401d80003000100000384c400e502c85680301c1e400805450034850300c82c0c40c00e008000103d900d40c0c09a400301e003010030503211001080d01809001d00e0280000f01c00451009110b82d6107aa04e59000102c243c1138071700d40042002009841018902600f50f03528040c100240d105c0c42040302403100d4002e0291000d0304031030200864098600180400c8d0880e46040c1ca850b9160b030004104000b200d03075808140080c4c1c0c5c0140079000c0100008401107072101d0071800c105501c0783c000341450000b21411762034400700741d0700316001c900c0c01343d02420300c2500d5145601c415a490f80400c2030716488103200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204606402 1250 204605152 204605189
    0x110d02040e0d080f0103030207051201020d02041701150506040909081c02040e011e0b0a05090a0b0c07061b0305090d0b0412080109050f0a0c12020d05070806060708040915 75
    0x34000da10400e00f40d0b01c0180c02c1d2035001050a20410a010140068105280034482410204c01e100080034038200018600140009010101e801c10341010344208400480e4003131000090191028034185451828842d07031804e000555644543d103c1c6049140c2c0702c50782c3c8014450b0540c20b0307941c00c070441d0750400034648504189078020b6002d4021158042a480008940002d010b11020200c83c40c1c0c1d900b945070f05040000004050300900900303c10003a040085035074540f2036564503c01840c00d18a03403030b1201c1984c0c00b40e0341040c0c01b40d0031400405c00c00285502c0e142d03590000780c0c03540c250141052a522041d030300200e41c0b21140080301400e205541824081007107100e14540812500b55030b5014100c0c1d8076107494000b0b03514241c1c0c0308903520b1406c102150308403455074001145100d06061502040801d8010340050707030802c1e08031102256861040001850300b2200b800d034000000c46d405072400c00c4a0303031441d105011b1f60003414842d82d40c0301d402d031140804030707403400c000f62041c801e081420551 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204607652 1250 204606402 204606431
    0x210604030f17130203280308060409020607050114060f0303040e07030204120c0f060c020607020108181506120102040b03040b060d02060705010c02120c120d0921090b07020d110d0204 80
    0x610f104a02030b01ca00030482101081d1111101444070301c18054045005c0c003514216019000034110a03403041d80c8600007801603490728010480e840c450000414103132103400021942c480300074015405103004880607c01d9a4010040764140e420103a48072843c0c2d11440c504500034000c03604003011903044a40b0300805d200d0303101d9014048800310140040b07195110b0808445d40004008000d40100c403d01007040198060304030254041c0381103540d0b00503103841644961074045403440890b01040840244400781c1028000c00d01c104203054000c0d441c1c145407202d000442d12000300054548205c0030041050390342c071110100781c03864008104640750346050a04500810710f5800d603401503c1243c2c031080c80e80300c00a05403410015090b000d850b1050b0003421401d07056010303080341440c0c1c0380e4601d070090009010003410020603091000924490710000c9020704194a01c1d044a030342e00c1c3c0d0502000006a48000a09071420b43c031100a43e611003512003c18100344528030001e6000c0c0c103000c0e03030340304046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204608902 1250 204607652 204607681
    0x120c0806010501020705060904050414190b1302010207172505040b040515040c02010207080c0105042a051e0a0608061903150b0d06150302210604030f17 67
    0x185040180c95060b680c1e003006980c0c401107441419003024041c0300d5a003403854035500950b0b00c64011004520000d8880f03240c10701388030700d0000c1060b01750312004108040c4050f40c190303a03500c4000440070850045590700080c0d030f102c401340301c0c404402c010b100781054010014822450981e880101d90701c94060307a901c0e011420101402401d0240d840c0070020203040c030300f80c0030340c0e0b0094410180b1201c24100b101d0500018045008000341550340030460400041ca202c401400c422004d82c00014040c00d042c941500c0b11084410401400b402460b101d041d103c1200102038122602101e91049003000040c94801c91540d0740a030710b512500742800000e60541003005540b0030b800c12251807031100401d10200d000741c2c115000140c205101900340c4040d46655500082400000a25120b01c108490341d5680580d800690850441508080c0800c11400d000744408a00a2407401074519001541c142961703905000703001408001c001800807003010b000b403204001c00c5104804680c0c03035283c060440711021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204610152 1250 204608902 204608909
    0x111e071a0415030c120e070b04080601050f060c190212011b120212041b05060706020a0807080105091f0b0c01020415030b01171518070201050603011a041104120c 71
    0x140000140e40382c140340b1a21a86007413107142d848500e011148070411400401344940300c40b246100d06a000b162034600100070f407008000380b1008158541c140030038018007074484041103014000901c0030740b203030321404100240c40309001e545808401c0b05900000744040c86040c00a011940380202e80e412079417900008180c11143c070340710707407840300b40304480c10007240300d0304036081407900c8a0300200e4000b65055690040a8502000c0c101d030740e507203c100042c25035101200440f112980050080030164010784459440042030030900040e41c03410020032400203004001c4811100c4410149040c4502c50101c01e002d040c2500d0031030744407101400c1d0346000354020b0060000c40030000e10069082c0b44640102d800a4106030742d10b0b51a05a00d01851010003400b50418000c4180a00b07449013544680503030048000c098074421880b4142513001a08444005e8416802641480c942d07804401c1d00c6001031140d81c0003503400061001e031403525464680641c0d04030242c1040a0700c08102800890903150041d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204611402 1250 204610152 204610169
    0x2060d09030206070e06070b130c060507030e09011203080901090506010f03110402040617040302010f020a03051f0803090f04060f060e011103090904020d0f060f0f0c111e071a04 78
    0x1d0361100030040d01c25001d0081c02e1743d4040020403140780061920f4000d07d400508092201014400a507644041e00320150011030001380e003c40e548040c154003040030300d03d68800f985c2d081d2065040105180f000529084003506200c404004102024000d50040c8081a08901030342d110756190b1980c00c0721503030700740700070b50310000400d024446a11f054803c9070201c44040d00c620500e040090896800e54900030400e83c00d5550300c5003a072244515600060089a540707a40002d0213107042c0800c1046a01101c009900f0749109031002d00c03c1840000840b004040d084903000c1c0105c03844000a8040d007115009010f42c010300240014805070046922a6189030907200c40c42d400d40250f220701ea4078059030344225409054100410003608001c41c010b42214000c6502c5404054641c4a840603038107059249410b403a0b6420f0f04e407001d40c00780c0c0301d170780181009460304080d0f50600c4900c00f9034500b8142c0140303154502d896002c1e003000310100082c0c002052008207000e04100c030712401c00c20603085171148000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204612652 1250 204611402 204611413
    0x60f020303091506060d020a0f081609180b0a140f061306140d0c0804020111010c080a02090402090a080a02010f0903510b01020601181802060d090302 66
    0x100a00200540748601c02c0a801000d40200b5000c0e40c400d1200c0103000e154100314200104200c10301c1d00d00040a03030342d8040d03c50a5222114500062050750000c10890203081c40c6a0896a82da5020410604403003031072614075401103a21011400a00f22103c8440d801040000c0000d014461100c911800c10781c2190f01fa621031422405001e1180b00d030302481d400d442c001d400281321035809038060f2290050045989810000100c003000c088075100348411011817a203104000031981d120199000840c1108003c0c40580b01c2044060714980c0080c181c1030025401040485450301c465040d913060b004e0082840480565900110743c554040900a0303001941c0b411040c18480c1c05003203200100c9034001010302e0140302012039540c0d010800442c0c4002c020f48050001500110a002003410a04070400030003064600000001240d4031001c5490654105000401c00c082c2080944a2171403160391020955150f50409442ca48001040080d0b11043c0440d100100100a61064800b98440d80803583d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204613902 1250 204612652 204612677
    0xc0213110c011d1002360a06020c0a0b0a1205040807050304120c080102030103030504030206090d0203070f08013c0e01090b06042003070f0903080415020d0906050a1409091006 77
    0x3a0b2140301003120220303540c96515844d000381c00c2400006c6500300c16a00800c10041c1001801c5178000381d01c9140141c7c0042c0310b500d4180b4150102d100100b994000d0f5618002440e14081c0007100200c4407101d003503681d80d0000303040c4440d5008440c000ba030300406690707903192031300105d0075004140402610060103048012480d4032051080b00c0c162071305500c509040c01c0c659400c0004640c000e00c00290080055000000183c40030800c1300080c201c600c2100c4403041c2802966821034001d00410043ca01c00780c2080d601c0012080d041c0d60709261032800400441c0c428031550390141170b001d038010a031580303840002014020b40609550061008035010f00c40050318480c88030310191014100c501e45002003004c80d090b00e0040d400d4900d45c200f64104a01e10f80c0d0f40c1d489030440345d0440d41c0042503402110701d0a01e5000c1d814040c0141e20034030350038880c40150600d0741c02891400703540902c2007801036241a4050300d42070101aa507100c1d40c0140030003650b00e802d580d01c1800400500c06e200c00f24105803201c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204615152 1250 204613902 204613933
    0x3020d080c04180527030c0f01180b0624030601120b090a021308010915061a070b0a0e1c0f0201180206070c03050d0c03020601060c0213110c011d 64
    0x3a0700b01c8040c030b8030f500041110381861030020b06000e003002d505d6003800c0303803410104101c0039142912115003c0c044c41c1c550461110036814101c0842410310640d2500e0410009a0710456400315150f030001c203e50040d035110404a0b05420303804208200c80c07481c1d02802c451000b5600011403041c002070741e4290b840b0800d41c040c2c1d02681d80c4046440d5004140c5c3c000038045004940c09803502846e0140058541d40c0c0d141d43c001d0850310700600c01ea80c85c10800c05c654101c11040d010300002498041d4000d10000e01e290340310852801001d0000780500e448101248084266400c8080b181071003134195444001e004405010112740074503440c0100f07600800c2c4800c0d0900610800c03820b01c005200c034260200c5503a080040607401300e03504540341c4c0c151050200200c0d100b080be607064540e01b529042501c01c0325046c080d1402c3c0050344032008000b04400307000016180c401d0390141c0050303036000c041903071914440d0710f01c4280a920300806440d8a048078008a18185200c0b0420380d880240a54a607590080102e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204616402 1250 204615152 204615157
    0x603010801150b310b070302010501260703080a021c0e030f1b060c011b0536010e03010b030d050d1b170709030f0b040203010c022b09050a0303020d080c 67
    0x1481c1c5130f49608000c41011079a00c0d44295441c5030004a041d01c0751500980041600801c1c02a001070f952800140018041c10380320404034903005401001e032000d01c024055171281c0d2404020001a404222800c40380d000300f065000c01000c013802e6410448901c1c00c01007002140c3d840c8a4840d00c00c52180309903804001c918090344440c454040c44030f441110041c080594800715a00318a0743d0b880d00d0614000f8080c580e000103813201030f5074059480070744010050300410183c5002882c035620f86000c0c002c519000304010460f031800e007021891900340340d000030f004003c420f4207590940260024028595030080081c660320b0300700002006070170202c011288106211005100110340301040300c21051190030744482e03000580b440c000e0640d640702c0d9119005500c1c10001111103048503000e100851074280079003004420684003c000c680280c04400700d10400c4030094001d810300046568564070f03c15100e0310080c1901504081900382e0302d14000390b407159031000c0759000481507000314803071010310401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204617652 1250 204616402 204616417
    0xb01080708130c080304060c03021b03100f0e010504080306041d3c030703080a051b09010903080c0d23030103060b04061707030c1a0d05150603010801150b 68
    0x11001116519002081c180b44181002500d00401c030140006120008000510103020710b644c60441ca0f04e143d280c06440d0a0007408080e0801410001c180d805440004440004103100040455280c210b02c2c40c00d4002c040151100880e54284000c200c01e11440200031401001c05941c1000908154410745402240010100150b5009501640d900c8c01044a04160008035510881720310310061401800d900d003c0e075280307405a000130851209154200b401154441c042403001d10181c80c19944074049030307d800c030200246150114440b0b80c04d0748201803407006540d01130340c001e5907412101401e580c1e0b81440b0403600005401490240c0e01c260001d0740c041d40c00003d0310f03003060a607403e60b0f80d81c3c806401c01041d05500240c0e5182d000a0054240d894480e03854200c00103041c5050031800c00400110140d000300000140c0704148a0340c1e4a4190125402d800350389400003100d031181c0e000000d41d00244095550b200c08080000310704500306601c100d1465000c0c0e00c84120ba0b0303644a41d40e5191303004400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204618902 1250 204617652 204617657
    0x109081504020f030712030f030f05010506160c12110a0503210a0216061e0e0307121104051e0a0506130903020a080307050901020717300304060b040b010807 69
    0x1001c2401420318012003069000300400b515112a01c1c0d90180b208040c0b0300c3d00590000b0f0007560b010491540500c030700308881400c09002e012071742c10a40030a00d03900c41d40300c2590f002c80c415000c1c8001c0c081c010009001501103960117580c071007174a00f020281000c612145278400c41c210000000c0624000442c00c00c4056807119042441c242c4a040003501e400c0405540194060040d046000c000c0c0703500414042e011a403144040c01c085c0c4c04400c4203800100c0c050409104c460744442d010b540e80019030b402141e00700305500029880f80d00c0c144004000400c0015042030074101440302d400c0b410740700356010040020701050390765202c0d42c5040c159241a07a5168000f02c95003500400c3c0c210f5034020720304281c000d00450b1403080e4955948000c0c0d9008407070f100c00154001c90b20b00c4440d0303414001d00000f04200c1b026800c00842c40e6054a4a41088030000b0202d0b22407084000c400021030b1a1740c3c105414440744036601c4c1e15160030f100c409000d424003480c3c440d038500004441c00d5801516400d01900007503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204620152 1250 204618902 204618943
    0xb0a030506040305030406060e0a0e1005221a01090603021203030f0f0405012d0c050702030d05090a08070303030501050411030405060604020f070c031a0c030c030708070e03030711010908 82
    0x50f101510075600280060f14040e40f10b403c040352800005505a006101113500000c1105154010504007141ca4045070f011604000510004a0308e42d0f80c100d00b07981c51045050700d1850285001035002401c1041030031109034110001403000c60325031045046034000c3e03485480c060f018049503070b22444207c030380a507002d21810125403080c4e061041143d20034420400000d0000385100100d500104002201c80801002041c07040d00000500690050740410f00784582010b400e940080e4907941d0900080080100100d8405003554901c50724100600340c02d0300362440161642402000340109004d0346000f1030500510101003c90340d4222440780340c003c0045c0480d52901e0040202039800300428040c0d910040c0030700004110701500441c0103522604040e00740121201e20100c01000090482103030358400d108020010341003800301c0e6401640c80c07400380c400b55a001402d42e42408052040c50705440007080090400003100c100d441241c10907292003104c0e0b0340e28900340d41c0c0c4020201c000c98008074107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204621402 1250 204620152 204620161
    0x80c0a0c0201031103040b1009090201021c03140705030916050105190201020d0e031c020f0a030e07090e0c0a050307050307090902060d0e06011401030603020a0332010f0b0a030506 79
    0x510603000c0051051401141020980f540d100542d04190b40545041c4210818400d0305904078048000801d415039061010f40d01a80020b92501601c2c038658240459580a500c1c1451090348988180200d81c4a605140d00348442c00030080d80048a109205106481d407142d00418000c902700101d8105940c1c0c585422500240491a8528203c0c0b03442959003d20590f02045624002d5142d880c1e800001903485115501690b001100004001d2468510420508640d222058100c034141c0030103040108987e81c0d0b95900310314110055001c4480c0a140614240400740c0201c0d202c054070343c0440d5414020b50700e5600b0180c5401452042d41c0e415840b08500308500380007900b20b10001740c0014400b905216607100c11b2802d8500e49001d448460700040f005005540c24009820703c4ea5800b071074100708490031640801e6440c0c0d42800040c080c4030440d041c4021030300340703045100070074104088a0004d04516126450180400f07078581d80c0c40a0802c0300c92100b504200300c04a0449400100a0090341c88 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204622652 1250 204621402 204621407
    0x10120206070c0f12060501050402040b0f07030909110d2421020607030c12030b0a03030509030a0c0e060319110f01090806010f030c05090709050f01090e040c060906080c0a 75
    0x2070981110100b407502000120004514a400c0007403a440250000c01d40161030400d0481d101604003d01ca02c0c8184428400c264040051b030300f40103070305030f8081c0c0d030b81100d418190f41c1da00c02e591160060741c1c1010341c504c40c0c0f5035194016100e203003556070080c0b00500808151031441d242803901c11443c0001718a08200f8034040c0c00340c050180c440c1c2c50b1100c840d1616900440d006601802095002c6050800690204242c2e0500245191400e1a003001984010303000103a0404242c4805020044049152032881c1c4d0309000d01140c4a90281e014a0410364810000120040444140d486400744120400e4141c801801550728a40e00000c0344001104480412000400210300c16040044030100851010010040a4040c010110116038003510390b2406c0d110084554011a0040d41c03071005100b400e9401402c03141c01d40c3c10440d054103001d0508030048401c20750320b51242c5045401e1406000a00100c1000c15087c0e4030b0560707400361590f4507903406071041c000a45407000c0700030b8200b140c00802c61 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204623902 1250 204622652 204622657
    0x1716021b180c0307020c030a080403030e0f0603180f030c0304170f0a11041d03030610050c0109060f0c0c02010c080c01020f0301090e07060206010807051c050303090a060510120206 79
    0x40c4014424036038224201072103448060126100c800742040001440030302c2c0d40401500300002070890081ca41d600c903a0b50340000c9401240310040c14043c000080106503070710100075401c04038000d020952685440d404007509040030709054000d0340140030300381c49803400c04012520040b04000046203072034501180f00702c0c5026003032a051030601a03581c142c0b000780c5084c0206400507009003415a6040c01d9103080004590581d8603514040300f0309080112052801700980e980110300b02d908a641c250b42c07803400d0b0303600e200c2d0f032001807042e51800004c00c1c1040b0080d4094140c020548100304540800004103690405001d0030183c00305a00c40c0c0c450000480e0100107141c424820302c005810500c45049400d0180c000380c06c00429503444040c0c7d18003002e010484140202064401000d242d4035040c2115221040ca01031207004840f144000b580ea1180c01c03140140300c42c0d00608a0b542c903c0e00b000400c1e02d039100744408403141d900701000300e0380c490840c131610b40507150800e0310040801540d0b400c209250303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204625152 1250 204623902 204623953
    0x406140903150f0f0f070c0b07031e020a0212032211060d0b01020c09040b1b1b0d08010f05060d180c0b13080601081c1707171602 57
    0x140329510740d01c580c05012400d5140283c05a030103d00b09801c2200009075011130080c11148440319039810010907503400103d0071002e940203640c0b401e55407500c0c502100900301004008810b1070303229980c3c0c100c80006070300078004943d01e6404e503200c2c00f029000000d2544000e40e043c0c00b031220b0a950700144410ba440b0300d807004c5407042c5000100c10414101140f05030b04816800020182e031422313100d2a03941c041c0403403018403c080307460041b42e2425540d9100d180d4800350601b01c20f0002c0112455107608084215401c0100e10b61058905000507144681c1e10f0080500c000009290310000150aa080300c0c01141529001420f4500740006000d04c10020030036504070f00c2c0442c0814038490042140b41d0b000c40c0141c0401158503a40756440004c11040181e130b41c0c04010503501c081e004004050000c00c1d81480b00c811004500158107880500325540c3e0090504640f00604240178030001c9504814601c0320050752012450302a030303a14211900e800307100c290010140e0024840032024424420034200c0d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204626402 1250 204625152 204625159
    0x30c090e1908030105090105100807031806060308090f1212030c041e05010810030b181c090807050103290604080a0b0603060f090307060515150d0f0204061409 70
    0x280c240001414070088940350003903900b20700c0000107020300e051a40e032031800740600b60b580c5079018268490050814400418080415650744150701614100302610441150081d106003c002c3d02d81c20013019503401041035501ca1004c10300c0b2201d050800e56820000b02c1c00b540c004c1c000c1440302000311080c544c4010501c0041100410022802c81071505c6441b5400c032100d1400ea2109041000262080c40c0240070780400b807001e040200b0000b01042c48159010054900c10080304940f0040140782c000d10200d10008070120286600d540c0358070042031030480b401c5400321107000f50354000540498864001c03010420100c000a10790b030030301e01ca4040822050142115251694ac0c401050900d101d00400f1556030b034104c000d0041e9450104627494115009150415903030400b819003940d03910507864014082c680f200c000900805040480e100308600142a02d00380d05604840c1204550203014101e42861400c0c500c0c0c40140c0d050b109076020b4038000e482d00c1c0c0c0e0151121404600325000900360607803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204627652 1250 204626402 204626413
    0xc14040b1608040e04150b03102307020a0308060d08160f0206030a14010503030f0a08070e0a030b0103140d1409030708010207060e060a0b0f01030903200706020d050301030c090e 78
    0xb090100144010192404011a1410245401c50000c00c0107401c81500a040050f03083c490b0f41c002c10701c900c46104c040c00c0010541039003000414404801901d1801c0041c2290420005a40119109030014840d64504a080d13403140104220080c0f40100580b40c10401c0c001d42008101201a8046203401518807000426860b80041c181d0346c0308a842c00183e030b85032080c02030b212003640c1000d0b0251404038051410110503400f0303031003203006001c446410880c5800100b1443c07406200c54000320035028110f40074181d1607080120781c008080c441120000f201e078200001d9454085141c2d59a202c00781d03180d40da141000750141c0b400790441d60803158980030b4900c1c0061142400d00c000c25200b4401e900c08204001c0858502d400c1c04401007003990081d08022645045581c1d4040005071070340b003420300103032a00d000c5c142211680300400804845400301d5464407180000010800300300e81d41903003160805110305000711a180028400180350000303185061040920640100300103004003c00c854 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204628902 1250 204627652 204627697
    0x903061805161a0c0604082203060b01140c0606010f0311030a0506040605010f020c041109060a020a050c01020705030601050907110601141e01122f030a0c14040b 71
    0x80c1845540b09100340704414510040120740b0b5044440200004a909043e040091803015151034050041000300080400203130350310340d055002c0c03a20805141414003800c440e5106d2400d40001c100c10780501c2d010030044110555030981080494070340b000d580001d0415a21090015601028500c450300705240c2c407403002d090350420403005035101c1c980e074070300200300c3e0300b022800e100860b1580d030401d50401c500c125003c03070665000900341504580699001034140600c0c4a280312501030050000c1d8005000582400420313030015120b42003502507420758481c0c00741c900040e40d03030f00e20718842d80f5016040380340100183c2c40e0403018240e10000508141081c10440154a0708000007600041030042c4800e0307241640381403a43d07132094081040040030103200e60020000e408521403101c0b02824503144c3c2d129200c10801d81074a42040d003100104091130282e00c1d2544529604111582c60045240220894080d80301c4c5089000b250b01c1d03000f409117010f007440010030b461752104007000f14650500600c00d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204630152 1250 204628902 204628913
    0x20d020f1309031d06070c2306030405010f0608010501060e040207050f01090b04050d0f05091918061a030112030c1106040e04051902150c0a0c0b0a020d030c09030618 73
    0x10044a8880d0313490080b40311003458084c0c1c0301050300310b44e24010725081c0044000204041d00c00010795600c0140042e8541e001c4084500e03048c0703580c07800b581244001c8144010454150410034203100001400d003d5070fa1600300302805c80b4824400d0100003005070507498450b0501d0b42c002c0031171070b0144c01510101da64083d841c5080d2080170104076098038801c3c0420041c4041442541000c44140c908100d0602c00146c00900a00800032031510900e00344c5070003114510041000070040003c00c0c10600040300b140c40c80c03001000c65100c1d0150154156400380e0800b6030490499041e15120800090540081c0d1011540c0c1920745030115402440200807050079543e0001501c0105420b03041500309250900d002410403c4070300402c10103018400503080160f40b00741d12980c2142c0350342d484584401084006038540b0119945c0030b04094903003c80410002c40e00c10052004641c2a022514026000081141140e01c805007002c005040f9070b00a02c0020070540250306945003051001040c2c0c400d94841 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204631402 1250 204630152 204630161
    0x5070219180207020108070f0309060e010e0c09130308190f0507110606030a02012f01060906062307170a0206090c0f030a06021612030204050a09050103020d020f13 72
    0x200a0129101030100824460019864128000d4074810750500c04140c3c0042d04d0b100028028000f407155014003182c2852107903000261654011606003c00700c3d0040c0460700134501c00078104603a015008400c0301c541010100d0500414014524000926698800b25804800900020080640140c80b01580203e07405a041090100080040c0074141840007405007400c0c3d000c510b645400800c10440c20f580c1c0410740000310b90702800c00c64100c80800104c0408042d9029504003100341b6800400e910100550022050b170b044182c04010340e6841700801d40f00b15805401c4654080c02c5210b031840003818000c0601961031064400006003010b403400000d940d0030009190380141c1c010001c010112200b005030b901c1459044e90400014404c110200303480e0040c4107406844107400107030040c0d60803111403000c0c100c0c581000010005040d0000001c02a500901c22540705d0515010b002c5a40700040c481e46d41200c0c0d004020303682c0b00d41d2581c00d11040050041d1481d41c02030034030113652610442c3d4050b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204632652 1250 204631402 204631429
    0x6020c0f0604120c26060f0601021e060103290a020c0c090f09120c0a141c1806020601051305070309061109030f0102030405030417070306060b03150f0102030a030b01050702 76
    0x761a600e181050071180517542948100d05a030707118041c402102c140c0200d10b803600000420001e14503035450900507854107541541c540d07403c0c40c404c01c191402000101e5050b040c0c0348100c0701d8070000c1c2143d8200d0398081d08100b28655048849001107900483e07581d0050042c400741a095a9210300030b80000345d03d50808640108d03007524007030304120302c4a00900c9140d10403e080c00c491801c1c4004a00825901c242d2107500030545169002e02d0708001808014290f4010b9070080c0e003400070905000001c281c940d000e080317188803906145012134181c0c004911541070302e02c0a0040041c00703d1048243c000b5000c050403000505580d4002240880c015006440200f01c5816207240ea6038005018513181590032a85481ca80e4414020b110001c0d0000c42210f044580307203d14140c10900300f409041c1030401682c001880e00e4070b0320f4000100128040d02071751045a20b02111840307a018070b000d120700c141c000019640140c000b0482c2d0044240290300c1130b403030f906041c5461030030716080342e001c41c040c02c1c0400d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204633902 1250 204632652 204632663
    0x1080112050709060b0a121b050c0309030106090902010f0806090406020304060b04060305071703090d0b06131506090506190503090705030a05010212131203090204110a030504050705040606020c0f060412 89
    0x1400d90711058200c03d6a160f080d00f45801040b103408c05988070710f201c0f80700401510420100040387d004c1903404006865028200800800c02e207a6280c041c3c9006000c0c03003208a020840707002404645030b009513002c51140c18041d2049002d03984130303520140250700c0180300301d40c100c0c3d030740c40703c00400d0b1594400c0c100070318850340007807070614107000480c00c460f80c0103489000c1c40e81c0100001c1209881d03d034581940154000300c85c5c809902d0300700c00100411142d00c500b00a452074501410f00c50003000301c65804940791900c44040c1c954462007401420320803801000003030308480144506451150004581c40328114007910101600c51001070b041404541082e50560b4011907034680070001d0300c103410707041003490701f541500340303002d980310600e460b6540c40000c1850703900d02c104425529030741c100c400c010030324a6080740c1d81c0ca541e8101074010304064401351418424060b003ca41400c01e407040d002a1880758000b40b840704011420040b41958283d54035820000502c800965080c542c02c8070b14a240c401c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204635152 1250 204633902 204633907
    0x17090d08042d05060912070602210c0403020a0e0106050315042c0d0305061305060d140a05070503010209060403140c06040305030406030b01050909041e0c18050a020901080112050709060b 82
    0x40c1030039880c1502c017400315003080d0484000d500301101c5d900700b00d0740c0955200b078004d41c0fa6803221644210612618441859650b41c20041091089140c40100203481c809c5841941c03081e00d0301c080c03030342c402c0090043e400842d00401c08213007401c0c42c0360044110b4000c0140701164100c18400e000c90501c5015107454060b40000150915500050061014810b4075240401c414a86180001c00f08136440c010b03141c0143c0e85d400031170303010344560303d001311071540000c1004454080c040306ea99548110f05400d582c54028601e002c0f070180ba044c000c40d1420380380100003c0c1454107584442c152111107103c820000d01c00d407607061120740c541c14003800046024501a507101c51404c0e2014064480051001341000010040765105991b00c002c541e8010b41c0084004150800c2c49400a420300c03078610002d020b11038000301c005155218002c03c9040b00d0412001844161503104008040e40200c1600c107010842c0400180031a60f80c0484002149011301c0854625a0341d480442003141c0b216040744003450b800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204636402 1250 204635152 204635243
    0x80a0e040501080c01021c2a02030c1816090504140919050a171303210503040503040308030714031f05010f0909050a0f0f06030317090d0804 62
    0x152240782d00608485000c3c2c0540141040000d481d04000704900740c084d018001c108000700c0c840c0204201f400c075084149450724000300540340c075070090f89904030300ca40314102340d045c4d2070304018801500b01c0341d20010124031030316a498030408280380344140c00e04010302004001143ea5840c051944203190159418290303003020417115003051003c484c540e2152a80200c91000103000046080807650001306c4441c24070a2400188039a20980403c605800352809022050100040700021110f040317500c441e140701080d6805071028001110050000d0704280420001b0135845801541c1c081030a10300440700c08040c4244221a03007041e201c001401c41e00c1c507104c0c02e0580034041d0b0741010380002d090945802030072074001004108180507603114252201c0200302c40109580000034000740c3c4031000c2c4102403500d00d03000001d0100344405d500050036124a05902c01643e41c419000f006000007914001264142c00d0310301b910060b00c100d8940f02c02c0000e40300c245105000d40d00100c03282a0303041313001004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204637652 1250 204636402 204636409
    0x310270b060405010605030c12040c030b07120e0a030903080901030605130203091e06060120100b1504050d0602030c1902010b0f03010626100c021f06030804030609050a080a0e 77
    0x3e0581003c0103108040040c070801c00c480c02c084e40c04000c0440d0100d04182c0c0c552810000c00320407544000c044001c40c0c028403072269040039080680341c2e902c440030890007a010014a6079000202c2000c0c000c00d480c52070078804074100348010807100c1010304000c9505a0b603035000c0f45101e00300607030358000c2640c0842803080c80c14082c130a1400760660801c800808041411015032140c002601c2a414414172904410f001c0702203080044071301148005698005180c3e00514014203081005c0323a00c0f841d401d8148020100320ba03401c1d2001d0754009002d51005072056034400009500c0a401c040c5519014030030042d240d140c081c0e074920300d00029400803c1c80955241801603403240004100c0c0700380d040c054140011a0804401132038100105926480100110115801c0c0f4189215181240f0304203c02c0802c02600014209071111082c000c0129558002010804132152404001d02d0381104001c01c20120351190000b04882c2c0c022000d841c03820900f030340e403d40540e1041003c5d102144152821000078134 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204638902 1250 204637652 204637661
    0xc17070f0b040608130302010b0301020c0a0b01120803041209030c141017130f060f15090e0c04050405010e060a0b040b040b210a1704051302090310270b0604 69
    0x30115828900b82401d124000c1c181c64030080085004031031440309102403502c00d4010f03074003400b001785c02150b40300d0390002903540b910711032601a2011070030440001222192910343c0401c5580001c2481d007151159510081304100f0b000e43c4104010125101102190101c0b01090043c40c0c0c0d0a42c03ca41e04101c1c2c8148225110100c1c58001480407007032460700c1c0100f160107000d501c0030030546d40e000d042d0102d2070550b100e01d84c12035014000518240c029000d00b81e00382e000f03e55090803418110000c070703aa41e5441081c0c0308a090050660340102d90f010342981461b402c03068009100790008074660102c036680d01e24200e0101e8440700350940b03514041c030311070809209052080105a80a0115444507004203042c0e00320810040003140140012100042c0c0138000c0160841d0301030402c1c0540c00e40c01003039041d190400d00549109407140681e46229132a1482165210031000c1d0242c100b500010380d040d0014030840c0051154a0711441064440741c41c1c203105a21802e200303c00d402d2040c2000c109100458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204640152 1250 204638902 204638909
    0x90703060506040504172b05040302011b0e09280b09100819030e03060103110907030b031c050408100e0f0a03200a080c03120907140405040c17070f 65
    0x1d6140c401844040b03800301c0103500010f4106c0ca516655800f070740c490b40c141c000c4061448582000310f03607610f110b03120b40368200e07502132400f0b6402400f4000c4810883da2920300709041c1300010070550820b0341120300f08002c03a05d90017a40c10010542144804808034000340039041d11344c1c12156210740600c0305180002c18503400843d640906c035985420a46565a6802d40300c030070703215040c01d22115208047c8074416254205401030b0659046581d41d10b810b01030a400c03000307143d200d4504000081c402c140300f032140c60341c001d04c024024003450301050100c44181c0c50f4182118204401004042001c400070840281d400e204803200141410310100d4441c10129500f000740c095803c6038409101003030303015030002030703480c0d0004514a240d0905101c60746068140c800080040101180e1035150030000310207081e40c00040c0c14500076965980c210705072101c0b098040d002020384150020072490516912443c0c0c40340c8143c00c03500059454001000d0f070000d0460484141c3e9020a00c1030111081c45072a00000b0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 204641402 1250 204640152 204640159
    0x50702010219050406050a03020f0403050a050d0210150e0a0e1903080a1a01050d20030103020f030601050109140f1c0309150c0609081e0d0b0a0806041e0b090703060506 74
    0x402e030410200a03c40d11070000007c0c01c040e00400d040e40d1810043c42228020340d0300c0011103410818901d842911642141c81c0440036001c0c00c0c204001d400d9441c0542c0082e0410320b22400e05480c208543c01f224040c018180c080043d544513500da0016008008040414001d490f5407401800d49186c01405100001e240c40c01490038010703c01d95405103e03441259039442401d019807961041c0780200c00410b00b000e50300c00c1c035007004c445a8030400070080080d8140c9009592185080d05031005140c3d641038280302d180c0c00281e100c08100000450318545401c01100241071070700035294440001d15514001501e0a40703c4a14821102059000b001250013044070b03040414940c0c112840c080c10580722580080d2050b030722126a80704014910b002c07241d03129804603004e640b400241d54071071300c1074012940d065003051400440d81c5c2c280c03500a103180100d404440007800b00b503840b80da4460b00501110b20800d4000c01441210b00001c0c0c6466035036119414100080410300e1842c02d0510642d4005007640b400b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 204642652 1250 204641402 204641407
    0x50a120e16140603010302090c0c0601061e0507030905090c0c0708030c0105130506070f05210a110c190f080301090c0201140408030604200c0106051002060f040b061305070201021905 80
    0x4968550783d0a40e411070343c0485441c2031940d03c044441480d031007850390030036190040b070002050580c0c2001c13041d1480e80607900b04040e0001c11400c1910070b440380050107004030381406410801e0b450210314103644040e0381031185081c00e149004070391406001c1d400c5040c07240c10200340000c12080c00d1281e582e0288a583c0e14101d540003603110f054a40070068002c0c42040021165080b981e4020b904403095508150b0740c1d0b203000c4485224a0b2003a01042d20f140c2c0c81141400903602da5658450203850900d803007100540004d68002107840446401c03807070b0031600d28909180322004504803601843c0201600c12000c1000040400001c0c00c5a0915501884480c420300600021400107002e03a84e106009076000030301403000190292a40e2030544c0103600340c40e00080c441010300c1d0103403c00e074101c8505a07900c078500342c81e010083e0b0301c0c0d050403984070301c03800d0300203001034003040b040c81500c1e40218010b800612000740802013030302038403011500781780943c0d00043c00610001c0840b183c2468020740745403a60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 204643902 1250 204642652 204642689
    0xe010f050a050c0d020703020a0f03021c080106140304021c030507170f0a0e010306091d10050106050304170415030204031e11130605030604030f120204080a03050a120e16 75
    0x14014013418642c40220f40d4003017000c5c02094000c10501510503080000404080400d140c001d50b0307424030f4042002c01c0c01c910103005010b03900401e12181030b0780540c3c640c030003004010160000380f60030007017084c0d07842500d440e40101007844011b041d280b5140241e981c2c9948510a0170302c011064012848902800010844000902c00000139100070b00700620303000e0107604c0c180c0012409030a042c0c1003102d400d1b107802289055181c040d0813440868191006584008038403904080859a092041e800815002c20004000604001c4040c84070340c120540e042c05e058440c500301075920b041c420b8001c080b980c00901030083c00800b4031501e0300da10a84c0c141d076104200c0c40e603524880c81e601340d0b0f0480c0142004e45401c402c9152540100e000f500c000f80440d6054605820024403a64000000d400800c481c04541d03100c1e04c13014022101651081c80080040c6102035808403500d42c881d02e14401000280c0c2a8180c0b02100e5004141e00c1c080e065008000e5940d121701c68204240c01036001a0a801c14440030a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 204645152 1250 204643902 204643921
    0xc0f060c020f090a0b222a05161505060a0803090109030b310b100f0e1503010203090724090b0f09031608120304081812010e010f050a05 60
    0xc003141c0c1403c0d500a02941c130b402c0900e0018015101c88241e11102040014141c1050121100403202c2c004c02c003441010740c03142c0b2141c5001c060000c84a2401d2a171600030b501c0394000e0300200b4207040715104604910840d0344480c034181e19520300c4491402c0d00c9105004c1b06103022230805d0003410004e405140750400f40b070b0003c6c0c0b002c1001d20000301811040000601c03450b50300c1051003a105074035803184e1107240c60403403500181e50700f480040b1340300180400401c2c42e942401d44c0010513110075090001c04141800d224075426a401000d00d6488008003803c240c1545080c000385020310381d080000d020030790505942d09028421400721400610030010100d070700948c0f001d1900210b40300f80000d25942d40790b50132004501d10980d14425014410042c1d005141c1d080710607184200d40c150010740b20303544540c16000002d403005940150501c007042c004104581000f41c0c1e8800404c1c0d00428444c18200360380c02090942c3c09614280751565500c0600503640c0c0441d000c0c203031303011030303a011b0411580c5082c0904 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 204646402 1250 204645152 204645169
    0x160f0503060a05091b01140703081902090102060406050a02130b0a02100b03070b130302030d080a060905010303080c1b062809020105070f03050f030c190c0b0a1808070c0f060c02 78
    0x2e2081c0c2c040aa54117107a6902843d942c0101c014000d4480c0c0e0341310040d0034007400d501c40690b841c21100005080e640d10400942c4269004d03408140d0284c4402d80303440d2980d8000d4500507107807100300c82d4200016041c14201389008002030580c0f03400e13aa101d4a01c008064204460f000310b00748041d043c041100d034582e50108112054420b000e090503155000b0702d03103880f208001c9410080d058480c40c1040360280c4d0308203503a00e10410301510280300054452070f201c81a22420301c030050104040001240d48600e90340090044001c5403041c000400c00d00d2514546051420703666100100d1003c44158000303510000711901d400240309082c0404000c940c0004c010784074600011706140703564140c1200300341c81003045842c050b003a20347c000c9d141d04180413000c1090344803076088a4481a8580000c0b0340703030301412032542050b801c1481c80c20039a482c1060f03180640b06c0c200000b00900c0c0001c409600068200019040003401030481e484a1400c220000604941c0303074000380280245103904000503a2230814 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 204647652 1250 204646402 204646423
    0x227011401080604141b1b060108192d05060114100315030602030903040b04060216060f0e0f0307120804031112280f0b0901050105042c160f0503060a0509 68
    0x1884410520410586d800a01852080c12042880341110080c90f0030000307800c0d41a215420107858420141018511740400c1e1751030300806214030b0703449412540e180642054540c94a0f0280f40d500c181007541c03100d04200098000068540740c00030495807074102451110500251800c041108800221441c1660440f034130004003416000000140c0c0c450080c07003910020010300091503140c0340c035030345c020303407122030000040c42582403e5100280c05440f0354081c0046811540300c81c108141c41c9024840b000a02645c0f071601807003001400100c0d4888131a005601702d0183c40380e161124150b00d00507485099056803584031302a0503507481c0c0c980001249910340c11450781c04200c0301e4007400c2c078071000a00303031188040c00381d2200410103024030a80542262040c10050000c00c80d83c2c0c0c03200100811a110402642d0828005940800050840750b0126034808036032400c6030100a40411012041f6803035802c0b55140007445001001181001c110581d000340c90108207201034a0900e03003c44d900c018010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 204648902 1250 204647652 204647671
    0x509070b1602030312040c0302090f010e070c050304050d0303060905010501020304060807030f141609061d06130324050906150103091406070e030601080a02010804022701140108060414 81
    0x1c401150b404004643c461340396035501c0c101c145403e041c2003081c101184800d900900400300001c0d200d90904814505036802c45204c2d45003034807643c000f11144000c5043c115403c0c80204400f14203030340c450140400d09403180c2e4001c26460f0800f0f54040c03c0d11702c103900a506660089c0301c180100e580101145901410340d107800240f11070300d003a8000180c0400d0080003000c0c0038240601028031507014240a0043c2c058442003110390f070310481168080c0e0684420702c0640b051042a040914154000b000004100400303d0f185070740341d80394041403940581c10041e00b43c0910002460110982c0249a403003000d41c0f0151031140381102000c0e016205401b211410503036940546d1080202076808445880d25040840f10380c1d240949010381040f441d40c503001d20034442c403000040c10f400700140c1aa4001d40c181d6515460b80c40b50b909010814180c2046151580c0c403078071000368802c0400b24150300a062080d40840403501c8540007403e8540058041c600540c185030740081011180581d05400c6514503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 204650152 1250 204648902 204648937
    0x5130b0d0b090a0c090f0c02060108030f180a120c08070b070204022a010b281e031b1802070b070e0103020f0711010f0f020607030b0103020424030509070b 68
    0x4622103030600d441d0f094000c1c25046595000300e00c20660785c6c0700e0140e41c20102001c01070030f002140280c2e6520800d02c55240194810130044200001e8140540030209130f18140951140c1c6030000285401c850b030300302028440c1c400c0d6150b424030918230008401071550b07001801c0410b040c0610055140b1840c14003070300494001600c0014044090102c408012405551560350500210360034060045400281e2213141c031000d18a0080c056a000b680341d0750403021800320010b01c0e00346d0b0440b004032080300300402c0d203000c80400000b1441c8120502d0105e014a94a102801c3c286120b2a91081081c6010301c1c80c3d510502241000a25a07210143c01c20803038105202d0056600b13004802038450500c01c0541c8290104881c1d04002c115924001c109009881c1e25440025400b0100d400000446900307005a0100d40800c0102e8000d074171010f0705050601d80035181c0fa8594280341c90b1009001202c0c1c1c030301300d0108907281c2a00d40c5840380301c0d0043c0528018100651802c4a1407581b0b00800209851900f5207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 204651402 1250 204650152 204650161
    0xc02010509010c0204050f1911030f07110a0302100507110318030717030301031202030a02060103030e0f0411030702061b07081b070605040e060907090e0711011505130b0d0b 76
    0x3d04229001d159008006002c4ca25000164040c400c7d42580c80c1c101c2080c0189010030814500d00a004c0c1070003131911501d06550f2200024803002901410280502800705200a90904144920412039002c2d400414034114071003031440480300e00074100c80c204001c030781d80001e605502004950940c0603080c0b01d51521900350380060704110f0a940304460714000070700880d51140340480594101d0f80120341e5a071030a981c60001340d8681c40b4207030b159001071b0030007801800001d008071058403070004094402c440d48803040d00030404940808040a880601c040204000960704001566021b40b107001c0e5140f03a140e0003030310703d5090b005914005003c1c1c0c4010406042110600c070010260003581720880320400d6444a02400d9680300b80910300c00c40b0851400211a810150416806424281d4946e142c0c2450b02c08a05400c10000d49600e0400407084281200500c00b40100d404a030100500c10145514003020803903101d40e0b4060b0384010714240101484103603074441020b1040354000020042d281d03607 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 204652652 1250 204651402 204651407
    0x4030201031508011b0201060504270f080708180a0f060f020a02030a080712030204050603010303050307030912031b0323060105040e010902070b0f04120e0102010f050c1e0301060c0201050901 84
    0x143d81282c4029881e15051900b80001d410001e2848101600200102c0c0e8940b01400180c40108282c0d41700c001400f080c20350305025810034070712118041c1d460100a9441035407030380c2003544004000c0c2c078072490100e00302d16201400020b01c003000100301d64200a070383c5016000c0815900c18442c4105200410155807a45c40c02884200341c3c0c3c560040580380745106600d4100c803146c00110056464040b504003019015020344210b400790b410042800c0d0039a0319554084a5544c001443c10040580701d01016000580030360562031003440075140401e0480070311100009440300000382d0800c15041083c2240040105a40d00302c0d00b2002c03c10404081d501c80f0010384d291708c41c0b68064030748200580c0c000203862030940e0140101910440d00e40e0f4281d101c1c5810030789050030542d0060224038126001180182c01f48001030900e03e018000412500c030b480d0146c604641e000c481c42e0380c2c0c5820014064050045480f0185107a689176180603096505040004008495103d0001d050000000d02d03002075a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 204653902 1250 204652652 204652691
    0x1e0507020a0803090303100b03070504051005040b0705070608090c18130503180406060f080a09170408060613060f061101020d18021206071205060f0303070503250201050403020103 79
    0x54010b006940c0d242000c0c000c881d07413540121010b40404403003102c00705080d581d44c011070b40100342030780d036013401c00782410108103c901c500340400307050000401000070b000c02c4a2000d0322505002d040035065151a01801a000042c02400302c2e0b003076006011031450581d10021081c0d000030b1042e2103904a0b03500d410340d03900c6141d04100040c10601c008904846110324030803090203122400d4605214281c1c0c2d8240c281c0e030889100340e01c140031038070b414002003a0650951140d0b41003030040c0700320040340002c20741c001400d600c15000308449401032001c010342410051006d14001c1c800c1310f01003060b146800248004644107005103802c108003c07007014901142501902c5103440e030301c41c0401000c100c25a1319003480c1b40c0c4c48404c07401a81c90b50b841880f4490003040c0b040c81385903a501c444d8000d84030100040001d110003041c07942d22000c07040d8044050f84040020740740382ea10071802141e80d4500302141402d0120802582034180803669a0000145d9210007031754110380d42030902040d4046061508541344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 204655152 1250 204653902 204653923
    0x3060b1218030304140f0304060c030509030109020a0902040609050910050d0302250e0f040302061803131215150509041e0b01170c090610020f030310050f041e050702 73
    0x5102c00700600042c000e580318501c85800c851400c58455501030444692203015031f105201c0800d0b40c1070b803040003190040c401410440402000000c4480065002a080c6a00354010810103039021400b402505d402132700c10000360100f1200c00305c4514003104040008400740c054203018448869081c0c041600801002c00314400b21001030711544c0d03907840c000b80c9001442c8514001c06d10000081600e07070103011086800360341c169028102c60b6840a9507600b00c19080cac0c225820320b110801011603141a60501030000d40050000d54520040c98241108040122100f5903121450a00360210244820644c44122881075a4035005517481d03041009a0f10300e01c803400c1000002c04d00b81070040206990992b410707204244203451880c4800c501c0c25a841d072003616030b180c000080502065040c644520700d009244194811241030316a5800c1c03503810368100b0f070b0300e40c002e110700090103025a00c0c060f41ca40340c1e51403042e102000452082043c4000401000c804d000c0c50b165070341c020a206910078005100304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 204656402 1250 204655152 204655201
    0x6061b17130801050601030f0203060d02100e060c151e01030b04020d02030607080a05090109050613080f0c010603020f090906040f052e05010608190213150f020c0103060b12 76
    0x41c96950109601812080320f0303c2d030020b450a2007043d0010410310075030380240e401600c12250070300b06900f070148040c0205c806c64184445140442800c2d03507000c00070a035803040000a00341c0032400d50300030341d0030640160900301303105210044100c817410300d0310b080344c11250420340030205901d0300d00102d0415524090302a405010707110821450b00e401c0000c1c203019001040382005669035201000d0300303c41151394020002e800007070103d501482c449030740e008031a002e5030314680f0303006406030340e038200b070340640d82c2e1040d5031751280400c009610341000983c125010503613594049180c1594600c1c0c03075a01c0200000c0920881030380b9075092040802c40d40e07650b41c0e81c03c0b00140600f4104401600480c01801e2005901801c040000c1410351041120710f00800c48904254142001404010083d41110b0040f0300d00103c0ea440018244084505070300010400341c640d4030000e0b9180c80001e003450419840541030600b0507400700301a501c48411140000308030064100203484103a00b08006001c5400751001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 204657652 1250 204656402 204656437
    0x30f05040f091a1c240501120b0112082205062d0702010e011b060615030c030b0603130c0e01030318060f02060705180a06050d06061b17 60
    0x40201c0c2c1c2c0d50200300515a1010f902c1c850303c109504000c070804074448000d002c020220b20710800610103000b1601c0744480302148013031103201c43e107420044032000d07070041da0b001c60030800a40c184120b540203180509080da2224507000c91549450341144a18060580290340d05001c00390281308110102d0701605005000d95034801138070b0841d40248055610248000c2c81c0c10000c111640e02001c22654410350686424103152004001518011a0f03000b01ea0202c90000c51507000091103489040c01500514000104130500014018111246172040805051401e19900d5565030b410090f41d50000c038020504032490810725161081141c503278052441801e07044004400c045d0080340c0d81081e10888000c407101940d503904109d43c0048103903904409a0803c0300807611882c400c000800501c8000c0c5500d41e100d2002c01c0100f1b03c1c04800b5030100700028008940d583d071b52a8a170143c1d82c014035030392425480c54142d0b443c2210036101344c99001400d0000c0740504d15501c2281a0035100b00005e486981b10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 204658902 1250 204657652 204657659
    0x8160c0b190e012c04061403121e030f1617011a07050f06060312031005130902060a02010507020601120c0b0307020f0d050a030b09071d240903060105031207030f05040f 74
    0x411030004c0d50140c030550070075a001c80c1c4d498240c480220b000900034000c00d64021394000c0d090544d4070880340031f43c100c00300200a8140001c0344000f14050911420345104504c0c0c18202c480a40300d000307a00300100000c00c0c48000e5103c210410150548251401e02031625100d02d84001c1d042c40346680c020700034016800200010a0b0200c0d6480c4698001d0f400c1c5d40c0d80c0c1c0880030080090b80f0080360700001c03094250100740440e003441d40d21407580003043c03200002c0740b001580000780a034110062220060b9110401c020250b079041c007086005009040c2090412410b540d035882c0045072600414092200110000d031955108220b1510094543c000f543d0001585e0100200310f035100c40785402c0840d0030081061502c0c249a41502d101c4c8d0003e50b104103920210301c1c42d1480110800020590100c0300d580c40b1000d4810060084500e0b99201e08040c3c0c1d9076244100341401d0030300581c0b10f41c1c8a03030003c640c00c80300e680d545400c82e51000c0e4503191030101c044201000303440c6405190408081c01140381c0010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 204660152 1250 204658902 204658967
    0xe01090321110a03091701060b0d05040309091107020a05090c0d0b030a14070602011410170f010f0b04140603120a020a0819080604051006031808160c0b190e01 70
    0x1030302c840000c0d00c0090344461b5603841c00c0c0c40c4d89102ea880d040300d0410211f402c40e00c640d40880c0e0800d10030b1601403200c9a03103121240582c4c3c200881120000c800184090031807925890240040a068030041c1c40d0340b03032211301850340707001da0541400c10307a40390549042c1035642840301c18441a441114482103a0103222001c0d81c4412078020303000550301c0c003941d01540f40403480e030f124446d1107441200120242031080c0346c0c1c4100c81091840000d48a201000c071114bc40071b0280e1030140c0c14541c00003030352840c0c81e4104002e640704e40c041c1281050400c0d00703000198901041004aa03207025101c1c507a00d131036120040707240080c008009041f03500b002c92901204400c07681c240081481c1c56440306419180d94040204076074040e0742c03c188400159004020721402074001c0c0030ba01858454456010145485003411948001e42c5861400e0580e1040d034208469210b5090240880e860144d0070400051480d9002c1403c21444a0a2081401c12542560b00c0703800d004d07962a4a400c40f00c840d00c2800d4002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 204661402 1250 204660152 204660167
    0x30304050402090f09040303020702121c0f12050901050601020c0a050f0d0507090603052a09011a0c0105150111060705120a09060c0c02090702030703020a200a060f0e01090321110a03 80
    0x303c0c0700b0b0703928005044407040c000035548810300340dd1641d20850100503005450000d607c0035180705001c9500380d110840300c114440c003840703860054004162860700500090403e818040381da03104190781c10003441283c4403a4151843da50042e1000340301111281405071425049174010807030541454404410400b0100d2a0010f003149080000700c45018821803990721800710301002e4200e40d0520041143c44501e1034030325125003000510703d1a00c0b9202e2459425200c00301e48a510050f2070340210049075030301c2501d40c030000350100050103040c100100e0040081c0700e426000041060054040345540b005907200a00301c95100004001e148611080545002255042030340314903020400114160b0007c400c503a045603169001e484091441e580d03070141e845082c001c80070311038003410034801c507501c8444c812005444561103010051400c071310024002801d41c0c07206810041103410802c0065110f08400c10b242b40500c454900901c9424022500302148071103030100f03485101c0c442d806042d0030409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 204662652 1250 204661402 204661417
    0xa021e0a170604020c03070f02132a080702071413091a150102100e0c030a0f0501050105100c06090215210c0c0303011a0405180a0507030b030304050402090f0904030302 74
    0x100c05081c0c2e0342da481004100d0190074a40145a0020841300b40062906100c0e030349582e10040841c040b90742ca84180c14102c950312996003542c01c040b920b0840c81042035010703051150540b4680244a40383c8003600035200c007040e100d8841e10000c0011403581c02e940318000700041400f60441005006c12608019013980740d00141d080e5241c105c0d5011900300241803201c0500190107800401e88c030100d44070510010545c07414064002d01981d11102210360b42030081200e03e83c00b40c01143d0501d041c6040240c21140306a008610030310344001e00b140107030340110500005607080000042c0110071400810b001c1040c8030307000300c0e0300000010613070b1203000d400da44802c49200c0c01044903965601c090746440103100c0e11000c0880c80d80184010000344107401d18003020496603007078250400b075842000c102413030700d40230303526440d0385800d003c20020030610f02c1a17030741c840601c0c9024051078000f040401d07182e11071400740b01d00035900000ca00c8a00c0d03d440c80000c111980250a907034040ca46810000d0094000e540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 204663902 1250 204662652 204662687
    0x90c050307030c020a0201050a18030209070c0c0f06141804090c0914040c03060c021e0a060e190312111303060501051e090a140901061a0a080a021e0a 66
    0x2030f09004042c80015442011a410f071242450500e007244161034200d180c490036107424050680110040e126021024000da15a89480919401d54a050003000f91550403980c12225441810042c50760b0000205221070594400c0c280e42e610a203050a00c1c000364005c1c100d80260600301900100080c00d1100021129009020800c0340031201c1d11075207000b815503000d4072203131101e40e051000c241658061710080d0381c1c1e40120340703110242c1480011843c03401400c10a464200e89412404d00145002c0c009514807800090222400c5c4807002002c408442da0004d002c0002008411000c0c513240d074040480c140300d1241d901e440c2c00c640d901e540c0f041c1c80c0301d000455031279041c0340000400e800d16032401612203601d501d84504500300c40003801000c2900618400080f41c8580002840c49204082c49005070001c6002080e480e080440f056040a401c41c0300c6d10345084104030b1101e003243e0042c00c0b40d80040c01c0c3c482c056611608122a0519040703001da040745a0140000c07003010701c0c7d4102684a0f0b2094024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 204665152 1250 204663902 204663911
    0x411010503061216030201020f031815070b010b030907060e0618010219050a15090f080d060504050c070b0c180108041b150f09030b010b0325020c030c0a030519060204090c05030703 79
    0x27041900c901880c10a0070580d016113002407070038034212503c0d02544015011071428000c0316110501101003ea000142004000003401460f901c01e102c5503002d001c0a04002c0656a044000324105201d1000101c0420b0b50000c01c0c4400c41c1c1c801d00a1112a41c48242035a400d802d250805c540c031401103550844040c4403419038064840c1c958040e82c0080360b08035040c88800c094580322007c030f40d405030103540c520340e6894501150941c1c0c1d5204060051020441c21a10781c4510310701f1148245e8094060030500c20300740910500f410302480d142e4000b25083c41d042e08551a40c0c5040e0300d9045c4643c1c0d0660a0104029001c1201c50349030380369107110b5401d81c5e07404c42c444c0c4850b401910b03211300758000135122101200061040b81040b41c011500265140da6000d0881e410b604030b20800148076403080f0040e00080310300c0301c0d180b9003045011a00e81003219a50070861850741c81a41d203500300c41003101e071280042d90340c40501c2101d605540040a050304244680700c4950301c010101c0d80211080b030082840c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 204666402 1250 204665152 204665173
    0x607060f140118150503060103141912080a053105011407080708060105070308180709020d0b09090c01031d07090b0a120c1e05060c010c080906041101050306121603020102 75
    0x15483d490017180c1020340030b007040da4250b03150144003040c0040c00010300d10035510140c020001c2c040e540101c0c140558803c02442003244401442200c1c041d002e04442400e01c0c007030002c5500da50a0329001c035620605100b48584108500305900c8040600c050300039440d000403402411001800a03220300c819035504d0105a4031044e0550320a401078645500040d42405403600180c044e2403950b070420035040080d5040c46110303540620300411500502c6989401150b40c44440d03480d0701481404490880c0d256200e460500e40d12665061010440307410140c42e034400000b06012658806403c0307000c41d060707032407554a0301310000c00307042282034090280c8045a00020b0845038250301140c0c507580706111a84440c9044002881c80400103c003000d03141e0340d4400040c035030352044028804403214800120711908806c10182054000805440003600440b04000010700060650b81c41d8003024207180340c43c0e4840d00c011440030680320303140e40d800303101d002c80d01c14112541c21b9006045074800d900b19042e00d082f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 204667652 1250 204666402 204666431
    0x1512070206010e0c090409081317070b0d0f09020604080c01020c01050a05090d050c0d1b08070503030724020a02030c0c03071d0603010f020a051c09020607060f140118 73
    0x1c0920928800d000340101149030002c000c3c0c001c110f40c180040000c544140c1646a2912a5022403403101c03c1c0300c00c035102000000c201c60440410320b0308a40242c4003051900c20101010301c01c00780c0c6c2c1ea5640da0717581144810b00c00143d201d0030100ea0040d01c020389071500c850004d83c0c5c5120301c56505015114000d045611307503120b107003241c0b0348000703540e5020704024140d4184540070062030000c8419000301c00c1408400c1e100d60a00010309030060508410714507200d00c480c1e0144040e504480002d13044090306000c00d450010445071b41d00e50005081500707800881002c0c440c0003e687c088602903000292010700c0c1940000500b010341e03140c0301521b07448420941010350711f110303034440c1005021140c0c040c006a1a44100c1d603a03401403002e400490300c061043c14203001c90f8410350074513020a502103018200105000c2d00951110044a000c2080035030a400207440760080140007002280c131140707252024170664201d500740b9043c0b80440e41c242d507110304806580f4101030040e154144e16200c0303210003004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 204668902 1250 204667652 204667663
    0xb0d0e0601030809060901020703060e07030215030408030708090309040f0f18050606010e0607080307090e07080108060112050f0703080d150b0901080c1209070e15010f0e010c0215120702 82
    0x2a44250f5043ca03200320041403040d10703080704440c2810350044010002c08640035002e40011905004060084541548104904040000f0408250314801e208020009818404403034001c40e59040440044d92250305d890700e54800d40944c0e80c2c0040c100002d291654100f600450f2103400c030200c05004051503481c114201076200e5901034130381e13402000460040c1d40500d1607000b4144002d0000ca01e4605c0507204d03031109600c26948100050300080b010000e03068210070032500310809142a041c00d526200f811540c60406000d001422402000b505040060030040303050701c0c509410603545040c0e503a040200840c3c0101300c0004c0038900b042a110600d0341c00c141da450590340740300c0d07400d410108800300442d000c000081c02904140c0c030410034031811b01242c152151103021880d00a20704a0300b41080301c082c03004050005031901d60030710511141aa044a03101c807a84015291080071190070500480349542c2c140030103508680d000c0380690480c1300140040c49020703940d03007100c2c0f01500c4604c0100e907100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 204670152 1250 204668902 204668909
    0xa0f06050f0a020304170f13031b1a0409180f12021b0d0807030905130501031a1e060103060b040b0705120a020d1b0602040e04020109080c010f030519060b0d0e0601 72
    0x40700a9441c0e80390101c1c0e62800307003403410a84040755003042300c0140343e81003990268009079120f500940150084044d40130003200580102c0750038540e01c0c81c00018030314072030065028001ca610703200c48903091994181c00a4041c51504601c01e510401e6a60409099800c403840f50071006001d0b820401400134155040c000380c5540c0034020541c00b02d00742c0c652040f17941201c1c1741142085184100013400c1da40d01c040c501c9614400c0780001a01d075241d03103066105c000346084243c1c000c440c4041001180010f07101890556154800d00001c0c0307075601e10048004000341c0c0c010004012002c900400c0003ca101e001e007034403c1c0b05e08120360081c0002440c81580380a001e00c0f21006078007908100406911510350006141000703c0c24a44542c000d954400991b0401d42000052448001c2000207660f48020744c0c10041060101800c404d100387d00000303100d00081c0d0040c4091585038408914100307034101c0300600e1840404810815680c035881c00725070b1a40300048a001d86c038203051400084401c00b00d18175040303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 204671402 1250 204670152 204670163
    0x30604050c04270617061501030b090105060d0902090a06030c05120705060c010f0908032d0c0a0207050d081201171902060d0c08180106050d0605090a0f06050f0a020304 74
    0x700032040080c01610030003026120030340313883c0c4000041080040c100c10700080051009842c003450a94060303111484042004c504042c00d100b5003000d82d031100c61146054510903a800380d80d8030419001c2401414034590300a420080000802c103806240343c0c8401c060380c1c42003070b0b8a400030350b4031410032040c04201112407070250082e4800f00301034501030006058a002180020a80000355446802241c01441c41641c044900004200d41703028203494951a03d80b441021040038219180c80850820b801858100500c100041d40078209000308000c1e4001d04006050000e00c0d075403458040c5468000881460401021300000704d08020f1184c446460703141300d40014101c544001c0710b0040e01462150060782c00c103030100b2007030a00c07113100c0c010702c90247c40726282e450301e80c244100300c100c8a40380002124001d0b49880800c2c00180d0340d240c2100303a030f907810403400314050316242400e81c14011264801001c030000d404004080001c00c0d04981d1241140d21403111060340c0352081e060aa01c07041710000c21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 204672652 1250 204671402 204671429
    0x21c0c0e0d0b01170708010e070501120c090303030b120115140612041b0e090a0507060203120103110a08030408011406010305071b05100606050c0c04111204020609090c030604050c04 80
    0xc1070280c41480304000c81c410741203841385c0c2c0d942c409090031101480055130090704400c60500040d41c200000607503021612100304414001e022005002c1c1c1c0032030000900b055101d070101003a65458001142490b03140c8402046482c140d601100070407900d5202d807130404800241814403526209050781c180707080c1142d030f116490303660740e5403480e034101044560745185040da8400301d40d014404c1000c80c4a250084002c1500b2115806c02615188242c1d200f441190b200300074002c980d402c00c110490441707511610542070111414001401400c41e900840118403010400207248107054200c0101c03071034107880740b01e800e0302d40b48011000d44a048420201040602020201c2d0340390022101d2410785c021b0f03046d00c00768400403c080f81a80c2c40765002c000081d81c0481c5003460000113000034100c40700121401c021440c02c0700c0c0300d21010301403070030b400d410130783d0384000101503486c0c6104031989641e00070080221840c0041c540146504280c844902a502e80000224602000400ca5080d154154100a07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 204673902 1250 204672652 204672659
    0x5070905040c03030e0d080a020606091b09130e01020307050a12200a110f240603070627030c090c02120d02070606050d0501022701090b030901021c0c0e0d0b01 70
    0x295580b8240c0d01164201d58001b06a001040f8000044c0c074032030b90309601410490401100f0401c1c03405000d4501c050804403c08030341030032a540350481d4075030030054820147c49011942d0410042c904d114000c2141e500000c1000401c603848401000800c680d91580350785809c03807146901c00c60748180311030a03403500e1501108448007956001340009450520f0300125480361241d9680c02d0000c03078219a14154080703400380d00c0110800b8451454110040d0408140c5e2a0103c0000d0f80c40f0514031a420501144080e4502410300001d005103022110f80c0c068584150350340f4201403040da841c07240710905481c28112180d07440c0b0205a44400c20202c024050610703c820a40c00700a60060f00100c03040c60fa200000074040d03d8039000101003600610005840d0f0140481c031601c0100c1800c00f0030403220603c2c0e05000da507a001509101034924920300d036500d035952400001d0083c41030140c4040a80c0c0340485225a901590708008107059603a603c1d5920030300700c10280300346007000c0d90008101c600c00a0050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 204675152 1250 204673902 204673907
    0x20604030c020f150a030e030c060403081b0307020c040c1106010b031302040e01151a030f04080c0105090708010605180414011d01060518010303081b0c0709050405070905040c0303 79
    0x80707140c640024030081641c1801d400041112071000e0b40c200c0305201c003060002c00e15030144a900482d41134200994034002021155907104d0078010001010701403000301281400c2a200035000e495191201016928180b4401c040e40d9548802c0c5800e1240b4200900031018074890b4502c10481c004200081c200c236403c00304012403603040200b14442c080410315000e000759a55000d000e00309580a8000034981244840305440041107400075002044401840e4506032104c0b07003125801040c04c00e00860a48030340c80c00000e24400c0421610740c41d0b082100f441003824000c1110070468109100030400036550b00309019408440d404864451307207407100060302140c65071801c1030700d20711140c000040d0b514568a00825145113282441c00310381d5180b05c1800907003401984081d002503401c501c0802989156001400e42000130301030040402605000b044038400c2400350341b98124010107031400e041e01d0304500d0f002483c003240c091340c540c425064009481c050398402d59008a4003c60101c01f01400c0d07450a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 204676258 1106 204675152 204675167
    0x7030c02100c0e180f0c0c0102042402060a05010b0406110f01110301030b06030a080306010c020301420635010308120601020d1d0d020415081002040602060403 70
    0x10f006036585c1030701c14281c0c400b02101c0c840f0340c3d0b80c84900045029000720b520014803614503107400d014501d0402d0140c91101040c0d42118400d548000d500030542d0001e02c01c04124410402c001c0c414940304c0d1000002e007502d00412190041070601c141e608464980081010076900031005004002042429a80014086004054100d031039204c0701c001c1d10026280a050010201d03201045460a400480911000d14070000e49d4a6440c0c0d01e4848a41504c5400c4120070400b010b060388a030705055a00055420136a90200300071081c2000070b0000301540d0b400710200040b046021440c884048135180a10300c01c18030f160720b8001543e1040f4034071101911060554214039111955594006c0c1200003500c101061446114041c00100750300c3c48841da40a50005e00300100850041d00101134802252200e030110f030456a2502034103801c038011401820f00503002040401c000c030f48103225 = true := by decide +kernel

theorem cover : BRFrame.Cov 204496402 204676258 := by
  have h0 := BRFrame.cov_init 204496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 204496402 ≤ n) (h2 : n < 204676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
