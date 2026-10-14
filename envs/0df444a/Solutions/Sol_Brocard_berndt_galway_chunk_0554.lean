-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:25:00.719998+00:00
-- url     : https://prove2.me/submissions/e94939c4-9fd7-45d9-b8fd-4176f60393de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 99460431 ≤ n < 99640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 99461681 1250 99460431 99460469
    0x3090d081e09011b05150703021e0306030c041e0207080a03051501080103120c060603060b030d0c0c0e100509090109061d0606060c01090b07050a09050a030f020909010e07 75
    0x66820464030449195540b4204004030340064007161107108900c400c10484500c3c0820402c04014003283c3e0a00000d0140e00390810840c003170301a4001c4503160000c40d00b4042001c2c143d62030b46003501c0c401c0e40c0060003443c50850203000e120040c4407540d007a0081e400710042c5800149454002001040c1c400d0b4139403a42c03032000c88002022114007411018104001c402a04456a071049155040d80c0c1c00154250981714100d1094070059020706000741820b080031400010f200095221401c00141034040d6a145040540102c40d40030710303454002d00b40e142c80c500512503400640c03070032a40140c0d400724035117010341c841e0001610600121448240380c0c2d11070088108011460003010b40a908137140f400c2400e800130000350700d5000042526014800210740706060340001d42101c0c0b0a25001a5201098102148020700560003102d1010104569020006150a06d02034500072a600051804800880e5908100c004e800250132400c142d0b4032010113025205050210000a14400d000c10801e0008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 99462931 1250 99461681 99461707
    0x19030507080103110906030f012901090806070e01050702040e0a050705010311121510090807050108040804060c0302100218040609050c04120807050a0b0702011b0f0507020303090d08 80
    0x2864141001208001080001c801300c444405152081740d856000f903440201081c5044000441c2421660900e207108010803d0195412641005900810b0001c100791005640343d11340b13440362234501d611035000915030368460180242e0005e8145486c07480d18800b900050203070307141041031840c40d1708507952800401c00c0c10486c41c0d0051000b801c080c0700014805214541034000d08040300d03a54140c1c0c20000f51041c88204800030301c1840142100014000940020440d09507030140300c100307100b82d003800b162940c01044c1e0f8520071030380700504514080c1000300803a042c1503035503000c07015880340b5200c034041d0b00600d0001c0e04118603180c01000c14800e41c00200425151503601c1402814030748800e2210b4110b07104112000e444411007000704490b12443c01040c81c4c4034011014056000f020b01080030010b01040070b81c02014181d0083c064006020341d01100c0350b1714827840001180360000002e0300700c3c2c010300c05018014001829a42000c00810200341c05802c805011510110000740110500c11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 99464181 1250 99462931 99462941
    0x90206130e1005030309040c020307060501080a0210030e03041502030702100806030c0f130504030c0c0b090907020d170a0914030d0c020d1416020409031218051218061903 75
    0x110b40c05041d1842d442c0c000403035228071a0404c43c50085440d000300c2a11240204103e42d8920ba008004101d95a911074080b9203c5062070000c920074650a155a22028800d001e1640c8010500b8042d62070316140c90380e0840a80c04502c4d404065000a00c9080301607501c0c03c6035a5140b02d9070340c9480c1450b1038441c08040c00c01c0c1caa6204240701b041d00ba00c0613a400d8a0342c80060385007200818000600d0b484031705069521300c085001c014030054030704401003413101c030150180000c1e010035507000096860711081641c65121038040e44000034000240d4481c0c002a01190903081524100300044170486600e0382c1c694036804d00c2c45001a5440042c2040b081040e0f84a004500510340c4003414041e602210003c040d01c51380300c1020a030303c0c2c0100304c450420440c03040c0e100384075a000700300300316117082450b004d000c0700c1445001e030f01c115107840092030004000410085000f07070b0003c003038140b1400c4101d24444940007020b86d10030b00e10a117411400035855000003406032400b4201d50201c4082c0c0f011000301518 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 99465431 1250 99464181 99464191
    0xb0a0513060e09032a01021e04030b01050913171303050a02030607020a1509050114010905071d130f0e2d0d080408072a03020f06031612090206130e 65
    0xa4001c01c80c1c2604010210081c03c039100c02d13085256858248411410b0290040c0c0c100e44061108401a07032123915818801481201c0c842c0204224903a629420084068411250310014074003d1b000c8500007a0780304210300c00000301407000781c14a41e01036400c4401c10307020380085409034030500c000801d5180c10851503a00030a41e100034150034503140d55280c14888801c051400280e114405942005400c0d082081c108840c004001c3d05983e480341d0a1010348402d032001230201d0311170811401d241c0c0c4111108400003d016104000e40b058050021004101800f5040c02082e81d42030110600d16040c0030902c0d5042c6803030407a400c048207d28580d0380300001e01890540d641d00035050410030307a802603c50350b4000d4200807202c0c0c68003070504200b500c0e0b0805000c0706c07207900e25030380100b50300c2101c028592003543d009482c004240c0d40c000d42400500e100513561001084400b45084c400700d4455640740c040d05502c007002194100140c4d01240e140d03001b5220040790b000408006200b020301d85051160b01c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 99466681 1250 99465431 99465433
    0x90b0603040c051c08070c090f0605010f0c020d050102030405010b011b0c050f0d0605010b0d0c0201020909040f150e0c09060108060d060c181806050105040e0a0b0a0513060e09 77
    0x541081d954148890403140320b20344c09280420714038180000c810416544803900a03074020351b0b681e42440c2201030812103000b1001218548420280c942c80144074070030a6582c10b07103448000c119a0042603600321100f10040307a100481644810006c1e40038000343d03000702d20900010030380000c50307000503160400c03145d0b040c03c154020424540100340c41200d100c0481d0429030741c0c1001c008441c3c01284c0e6060342d120f030107407280341403100000d82240d4040040c9219905588100070a45441c1e604a00740e1140a403030740d90140034000450049a01c49440703250481c480c0541c04280b1210f20b00540560b40b0300c070b8a4150303503007002c1a1543d05003820070000d41d0181007440c0401036407900d00d0009600f01c90454016001c250384545440e05240a4508040d892030699041c19080380c0d00d501c0c44405e4203030000c000754450b082c40c00c00200d950160b0300382d80545030f0f8180185025034402e010407004004d0030302c055a10001c16040001c003034035000c1c020400d01d0038100000c505241044507500006002030300450325 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 99467931 1250 99466681 99466687
    0x9030a050604111507080f0f0a08010302030f0a051b010c0b010b040e0a060308031303121e1103070504060e040209060a171510051305120d02010c0206010308070b040c0b0f04090b06 79
    0x703072481d00d000316030021b90310082d05a00c1e03089a20902c0700700e0007801a0b60100071000508250881e0b0002c212030304a0707108030203d8441c40c0880e80d200382c49a400c50002002c5500c2401718940182d11040300710301002c0b06151903c0340c17041f075032208511160b0a034084a0000400101800194100415103901004428091161900d541e460910501c0b0040011988122841000e410103104261840e410414020240094044012408118014840d51a620364544400c4110307140207001a81d11491054071440c1c2494a000350640f46006e400d0740f1f80b6401a804c05c440c0009654000c042c00d41420180da852000c40d10a00c070345800070902609002090501120104246d51800411914821285805521b804820f8001001100c440c0c10059105003503141c08080c081e000102c03040384001c0d50b4000d00c0b0746544254103030380b41c0c1e1007800040c203241c800300100c0012031741c5020760310381083c464103441100582c0c640280398182c005c140840d0040000003003c0019000c940505400c3c11801c9600c145 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 99469181 1250 99467931 99467959
    0x50105030c01090b0d0b060316080f040b160504031a07020d02010902100e0301020903010606030b0910030b07081909030203090a05091003020405042609010306060816031109030a05060411 82
    0x3807100f40c0c42060107071100011810f500c0c0449030400c002c07180018141e40e0712030500178100c0800007003000000b80010039400c0022566500d105c003050080390854420310320340d11a100c03070702a50000308180d20240a0104400800900c80d076024100010104010324901d09212a000781403400004500d001c5a0400c2c0030403000d45d44032134030654209214100610420b1141d00070a0184c0104a4601d5040d460800002441a0950440c1040e00300c00c0303d0381c490b16a00c080440030f91040c0c600001d0440004900091a16130003150314a800a80c03e000400340b2244600202c0147c9104074070840041c3c00103d1000800d0811015010207400b080b00c2542107850581481c80b104451480080d11076601c0740003190510440d84c08007100c862000c11654107141140450030003e13072102ca841c0380040e1810400040c06403040e034040d40106038a45200315140d100030030403400f07442030000b03210740072030200700c0c2448541e81084010341841c07285015011519041c28550807000b00058414005c2e5540100e01b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 99470431 1250 99469181 99469187
    0x1101110d09050f04060302030f0d030b060309060c0a05040e04031206061409040207020607050709060e0106050711010f02010b031603050f0109050307030810051503060f0613051e031c0201050105030c01 88
    0x71055403020b841c0d000700c0143c0c1e0b000260240c42c8983c0080d42600502d12080d41075030b00800d0410111180da1010700524800340f051003500e1104440e481e40035048075000c52494001540140381d500d0340303440c000781071948178002c0410b4030300107680880100b0f0350300304094071200c0e65015640c010301d001d08002041c200400b60078076503403041a4245119540c005440411503a0310020baa5040d600101203400007078071210400c0050a10b4020f1101d003160300c4c2c000103000c501c100100c46846074001000c07250120702c00019503200c1d500b4040f0030305654032082e5401281d102005a40f4001700c0760b100c030008047c40c5003030542c101a4424214925a41054039440105200004840300c003039062411030a41c1e5070742c0100c020750a09a80005a0004a6562400030805034901640c01010100e400383c1000c0c0d03000341040560b00c12117040100305281160108074500d0050700c0300c0da044c0d0300c84c07401c009400d41c00c04c0001d0a040c841c0e000d08000819126900d00801c0c0d0911034180034103010f034020401803000100107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 99471681 1250 99470431 99470447
    0xe070f030201110304030b0f01031505010506090405060d02060316081003030203030403080a020408060a06051008250903020d05010e1209010804080a0e03100e15040c0b0a18031101110d 81
    0x10b4148035840c140c40c042c442e42041210011a0410383d81e0750642031490954085010070310041d40c0615844890303003801c400300d219150403500000c2180d03207011814004d02014100040c0810b0303100300051000d41c00743e222034000b5803040118006442103400a900c001d404031102030329503aaa207101d1542400043d400000716904150507041c03080c00ca984200c02c910203841036800c442440c2c003a0000b40402c00034944c0281c4240d80b8220380708000c20700340680469069501701c40d003280e0a48001d2060340100381c02100000b500c01e0034901200311584075000b0421603652000120340300d070b64404034030b50a02c00510030a031a075503106107840d140c0300c9100c00003400031101a00140a12200062212869008002e50b258030b02e0040c0a540c803880701840000d00520085205000b10301038580c1d02c050100501c02200d124540c081d00801d0f13100d00b070a44036402600100c41a009104480c09802c0d880e90071034a210004501c84d6100348190002100010706248100c0803c03251a402190444240340e044004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 99472931 1250 99471681 99471683
    0x306040e0a02030a0b040516080c0103050106020d0207090b030109050618060f07050d020a090806070801030c060f0507060b0402040509100303020c1c060903050d290a0f0b030c070c06020a0302010e070f03 89
    0x1045250b845a0900c03d00700100f00030781203101b448c0b9004c0040c941070049a4881d400200b40c8041180345c1c2d81702e0051343c4500b4504010001a0000c54003840062204e9000049006003e800041c14090990300c17203140c54016a5449a140d01c0100b80c0154000200724595011800f0500304200b8100031201400f54000d07980d500909507000b14032060400e204040d01c20017032400000701c918038206120090109a030a00040d58170341c1090001040c620702510b115655000d032580c85030300d005540d856210003040340c2c90172580d215408000018080e60f40c0c80209015800303031030401801e18954600640381145800740786000340c8805e1114403001c080f12417416045900700402190a6419240485140c80f401600030385451a2030003610141143c407400e6420000d1080358403078030210100400455070158811600407800b450000d000c1050b0301c0014680095a1610450a058540c4e580c80b18002d003d400a01c01a4000e41d003110906a09000b10215200e16501800741030f42081d445081c01c80003804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 99474181 1250 99472931 99472943
    0x61a090a0308031b030f04020f010f0c0206070c0b0714010b0f01200f010c05091203030405060c0a090b0403060207030314010f0b0702030f060a0903081b160201030b03120306040e0a02030a 82
    0x1800c002c044181c4010300d4240c41c81d500c5d40c2c91404030f00c40e0540c1001510140c0c05070b29007008001155001c0d902c1141d0540391502c50b100b002c02a07070300f048401c0d48014030441b11420700c0100014801060301c00b90620707502c0354900c1015034181020450071078040d81400ac4c03088110706e20f00300c0143d800102802c0d0149250180341d40101101d240e03c1e01c0e240c44a00d1425413076107000b8a000101e40d100018141c07018088840c420080c000b0851a9a2800181e40107800d030340141c8049072007804042c0091405d1401401e206030b401c0c1d901c14581c611074016030700c2038410b41d4000074807004040d03061003000c8075000d55241a000b154100089007030344942d00e00440341d41507030000d601010b42d5010440c21600c03000120848031986403c004c0440500801001180492121004652110b0f441d5203030b640c03208039450056041ca180305186403841c00c1c0c403810582c103040d0b88601c26107540d101400384816440301d044400c0c0d580d04008040c8000c0340c0007100414250b40054002c800140d4011a264100b00e410103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 99475431 1250 99474181 99474187
    0x4140f090f0d0c0206090d0c090b0307050301050906150a03050f03120a150b03280e010c020f030d18080a0807020c030706051804020f030109050910050915042301061a090a0308 77
    0x11b0041404100118800382c120030326020300180466850704030396107841040d030a440310b00342d58105040c03d86005403281942600454002110b1403d00c1d0703810aa01100140610460b0b80e481c0c84080c20150b07107040311605034000180046400d4001c11405070818080d507005c001c41401507101340c01e003005074001c2075600d2600002140e0541e5192251b401410344010001d4411a0350181000080160b40d10700f41d150350034a00340c088076500102d0310301141d540c11009140341214501d210001400c6003034111900045210340040032035201e4020740003015003605e5458845c10010310183c42e00c440070144a20070b61100c101409108c0e404801c1d03030250001031041c14107600103100000e010740164020504035180100001130140e80c55008180501000c1d019101a088090751302c1c1c0036140102d41140066000c0c001800d00038018104282c2d1080c050184400300c0c6c1c10a480e918280c6920b4603140710315a456032002c4c0b10520540c21a48881c80740054070270300e0020803002040c1e031004070f480090048032001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 99476681 1250 99475431 99475447
    0xf01060c050c1519020f010b01090506030408030601170a0e0c060a05040e060a0b0c070906060c080a0e0111010f06050901050d0c1203021903030614030703050601120204140f090f0d0c0206 82
    0x35224004c0700c206001814900f0500002d44c3c4950b0000542001e44c2081011040381d40241e0b01003003500d6000c0c00701883e507502d9443d00c080e203610240c207042c1007000d000500c0c2c1050f800c0300c00142c000c58070b814000c10010700c00b030f141c18584408000c40c240315640430451101091382060454044370868243d1445964420000610300381444d8010880204c0010700201034207070204018083e80c14203442000180e45901f811144001d0480e402040310344101b02045544c0c0c00341c07003615040d01051424070712003050708084c90b0070b40d0306040721584c016840c0e82040c4850300d45001024050442640c0c00003100c507590300c0e1203070160141d100b8241070103400c09400d8180740c803e01c680140e0a02080700d4106600ca2440e004000304218407030351b80314200340d0b0140c40c00e51401043c03100440390060000c0005909007000c1e05485070307817464101c0e0300c65900c0c4c0616000c41c3c0141d4140d0f03c50a04007584035210b1600c0019141810350345e8402c0c04203a003220324200c5032241c0003410149001d4041d503201d5122075403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 99477931 1250 99476681 99476719
    0x3100b0307030c0312080a06050a0314160311030d050702030307060510080304030b07300f020412120f0503070c0308040f0b0a0f1505031b06210f01060c050c 69
    0x190000390455480311000f00c01d00900f2081042d59491a0341e486c0100c0d42d03000c01c03450481d000760081c40c0e4000f280c4c070010408a14a0003840c0e054510741401d4504040030755004042e02005d80d031048444458912014400f031400303000e801401c001508110707140ca00c1ca0350009450348100d9200402e444d558402161420307240d1003c01014107100d1044980d51030712400d086030340c2141110400e0009240c41c000c8560708034900030f03c11460701407052101c1c0c062081001c50000d0f1601500382541c0075801d20000480409480e40c00042c14007410044440380c00408004100410b4030790088240705c410018000d0103507002011190f8580c02d80f0f401c459544480c07400f040d0034240e100d00902001c4416051081c0c640300c0f9480f6010f007580c0303101d0030401e60001410800040043c1c1c490258140c00480b02c2d102d500254200514000320f004100b94640034500c09241c0b2a980480c1c1d1040d261580002041700c7c5070559028103001d800e25044c4101200601e54030a9903400c0104d1500703000c0d003083c0314582c1460403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 99479181 1250 99477931 99477943
    0xf0e09070c0f0303020301090501140d03030f1107030804060b0a0806070c0f140d0f0212120405030f030906040c080c060901030f09050105150118050a03140307080304150507080603100b03 82
    0x5880650800b0510660a009019400078015150064a041c000050702510f04c01010b118050107446080280d03020b40f0250014520380c00c91013012519078182e0504401031400406555100e07403a03c0000742050b080c070000300c842c99103a040c020417001c2d4043c4269900003a0380c40e40a401d03494244030803140b034075250200043e440c800a240c0000c03101110340b90400803601c28903004040ea2403c0d250003c600b001c90f5184000800c0814290f010003e00410000c07101034641d02074012821249002e130310031000003480e402100c3c4906070350014400d000c200900d0041400c010440e03100100361003004000050410710a03900c0c05414143e441c0012155510190440700d603141d08407008010038a00b11595101c0d00314401005800a00c03201362901210000100c004191100035124070034240c1541c4d69028810b0031461102611f00c014440c0c00d00062140c802544103e209103e8941c2c49884d07c1ca486003600c0c4007810b59824442e654040000646002074010503034064000f01080b0b15008901090800c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 99480431 1250 99479181 99479183
    0x8041509050604090c0f020a03050d09020f03060c090102060901020c030301051e10020706030b0105030907170a080d0f380a030b010b030f010e0c070303050417030a0b040c0f0e09070c 80
    0x5040802d00007103130b460300d0303101c40d01a40c0d40b130303c0f034074401030f0507440072a2035201114004010a01c184520706030b00e215948800a2140701a04c807038004203146d00081d2030100c08480b40c01e030f80c040004000e0b01c99603043c40070540022880000f5414604003540c1607880380414006c41d4044e11801d807105404d407449102040c0740b24005011001c0130300015100070740354580d60103074502007420190f00307484a51181044a115101707031b10281440c2801d15081030420800305a400c8194440c000303170031010500b141c0c01480702c2c9400c0b150016100180864403419580141004912100341c200701c0a140c1c0c000440d9507554518241908100e1000071001400c030319030980028004e6544200041035a2401e031000314021003190fa0415407581e600e084400110320200d403203c01a032000d10580b00080c0c080c0c0c1155400038494042c80b68424600c14503031a80ea0411601100c415403100d4900c80c8509042c0305000d0b448800380b91803506080400c8002d0980b90341440c606001c1c00c0000300041d201403041203034032041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 99481681 1250 99480431 99480439
    0xc0a1514042105010b0105120a0b060c161d0103051903091502031308060714090103060e09030d0c03020301080304050112020c07030c09051005091f1701140f040804150905 75
    0x45004121240c200e52182d00007240c156180030800c1070700d9805942030381e050b070318408151009542d51510100c01341480d01e036003c0e08000140180c81d0082c40911030100d20640780081d820405140c034120f18403180048240300705030b4040c000184085003000c12a264105020f081e000000c044a01d0202c4007031102d0ba01008000030b5000384403204039408401010f0311000da4407980b08248c1c6880840741c9403801510050081800034590054040c4003001426480700f0504002400540c0d6090000311000c1c01c450700c2c03a071604006000d115107669072088821521040ca01107003107605214502d40c3c0d902c070324014075041c800304400844e0307420802e404861104489205803034480b5580d00c0d10114900c0303c2d000b401542d07810300c000200e101c003c0d1041c05044490007060f003081e546035007c0c020a111429003100e030b0510207450002c0391200301c94545160407408440001108c204003071202c0c0240c1030241124109502080500c0041000e44003a0303000d44805900d0700c1c0902e20f09003001e44100302203901039604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 99482931 1250 99481681 99481709
    0x90b04090c030b030c0901051003020c01090c08060f04020a0b0903010e010c050901020708120f0304050a0218062403010504020c160612050105030307020a09020c0f1e0c0a151404 78
    0x28281e00702500d0846030742c07800d0084201d000101601e400600d8120b907004480e501c01001070b4a4402a2180040e41c42d040040c13074611400091406c2d01c442800a480d0041d4001d800c11405204101c100e5108412085550860a144d40041c1600c02d0921030140440c00c04658140b16580039407000d040344038158000c01105540120240052b040000514090300408000013410040428110703ea280d100320854600091b002a0041c29080900152001e10880540c1001a2280d04a48801403030104042107289415810040068401d441c1e80e4803107003031400201c504070686016a03040d501d00b21005a22480880042d030304d06280070038510149100e10b01c0004900da00007008001c82c024aa505101d640e0300c40d01410f0b6648503c1a0082d04805800002c014401d842e901510710000820103403120a1441510a80340600010a0001901032050403d03e101401c00000484c07440079100030710524034040b4100c4908420b016140d00b40b002c1496100146a0900d0455001d4061003808541d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 99484181 1250 99482931 99482939
    0x1b0d06031109010b040303050d0c030e030a091404090305031603090b04110306070302090603040201120f060b0919050622050907030903020c041503080c010212010b12010915030210090b04 82
    0x2007200c0c0e6070000c0c074020805000045403443c1920200c4041d00c4d0103803170312072801204165103c003c2503494611410103a48000d005140402400201117041603076450704110f504180c0521100c074843e00b01c5500c11071800d0f4043c070000b5002416660b00450458085058001c0c0100030740c003038018043e0050000c05210104410890a5081880480001c1d800ca071050303551070000760224030a50030055440322050002900640c880e0f05e08030f000040b030150228080d0b00844a5070161001c5c0d4008009070413001c01c1240080c2003401d50f4158400c85602c80c000c9251400011603120312828010740f048a031070800c000c003100b404100344001410003809042040c41e21000050082140c580220300501441e60f00c0030a82c6024000c5410151303564008030f241038611707601c100440d4420941291995000d00848100d24500c9000383c0c006c20b00304c14210756a903d5440401ea0144058001ca00300c2850040358000740d0442c103010000703aa070305a651a4135180030101c103440402d40d039404801100c50008001ca = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 99485431 1250 99484181 99484193
    0xf210804030818091014040f0509031c0b060a1d03030a080601080702060411121002030903121e0a05060d060c050a1b2a0305010e0c180402091b0d0603 66
    0x5180e1003401200038405064a0401807001020740300c0c135805800b0170000b80100628003e507802c9900000b00002540d4081114000940e80102d601040300d800c08140300310551127459280721110002c0c50304100a0b280140000c945004000c00041084449000c1920342c81c0d542c0803070b60017841c0003001c40b5100d2800d003000600555044800d280001c145d00003181c01ca500000751103014603404005030b03c1c1f00c031041e0103001c41e242d2613007580b010500c40c1d44c0c4410b0f04280c01d132000b540646503d02c0030b141d54000d20750301c1c0b050480024010f5a00e008099141c140c050400002041c0c00c0f0b0b112403000b084c2c6449032000500d844480a41c042c0c1000d00c0c041102d034466400030010842400381d601d0311000b000001040c01e414990b00c0300040c280c407007000c00c2c0c03007500424110340103c0058003421105c0d42a4403520f41c42d0840f9600f00d07040000c2d0388412071245440c41d01c488100c0c0300f032500d40c120600034a820b5001c01c0b01c0c800c0151001081e40d9440c05441001d4041009031004010901010458a5541e007405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 99486681 1250 99485431 99485437
    0x4080406090803190807020114040c030314030907140409020402030703050901050a09030c080726031005040501060210111c020414040203040209040b1b0301060e010e0303040f2108040308 82
    0x45004a4001d0100184008010003131320440e0009200700c1404030301a04c0f042d102034070018010000c6540e20700101070180300c0501c0d02405203001d4000b20240d40d05524010f011010184100701c21071000344100308010758002451300a407920051071042504c5104081000750484041c001e52050012041000b495810f5001da445800c1080080c00700e034840c404194100e81d1004800340004402807248004200a40020300e1500d110b05c586a07000c00e00c54030005051018030000b60b01b140d40c0001401101880c248500010b0308046808105a501d0000c02075a00c0300e0303007500003801c05d84580d80122030900380310641d000901c8000c098050606a9080c040013540b240c0200715661028140c03031310303503820035100b901c7c421a4003800c0c04070f01e51180c0c0c5510805c1d60703004110f040e165000c500b01500381084500954002e00303140c2c640d41c110700551400585042d100310074032230181e0310920041000309081c00356003080b08c19141d541b80980c41000145824403a0008020306807000c001000000c04c001d01c801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 99487931 1250 99486681 99486689
    0x1b06051f05040e0d03090f021c15110706200406030e0609060105010c0f080f0d02030105030123070e030a02120c03121309020c0a02030a0b0114090903180303040905040804 75
    0x242030858a91040208642d01184034a8080e800041007440c560f000364014481203005c0d242100807081c0c0da500040d440d444c0e0f050084686581d0305250820051642091410045021001e101041d102e50000440b8041c1500c0030781a40c0d00c59040040c140f40340714410210969251051340c0d035035101c6001a0140110300c83c61441c1c1d00c0303200c000075114074010600c0c4c0d0503184141d541d041000c2403a12032000780110b80d24103492500040100c5130320454100000c0c25024181a07015899601d000101402c4440f211556015200980e803001c0900c0940d403006070b0b01c111141000c01941841d140803d14107825594002d4004100301c6104081000015500d64500341c110200c504a05003501e41d00104d005001c020a562810980700b4040e0710300c1500909118807202c0d0498400e01101c2d00028680210580107a408402c00340040c4007420055403887c40301c560540d85690a414134007111941c031f1007030140d02d0709803100c142c031180240e036424001c940c010000c590b414422810913080802c550743c002e00c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 99489181 1250 99487931 99487981
    0xb040602070b0f0706020901050c0607030912081e0a06120804032a0506090d0209041419030801030f1109070e030c010c030813150c0207050f030a121b0605 68
    0x60010b00800c0d42e80840c1d02e90005480c11900f03000c1390307030b4504000e5000301032554184003060140061180382041820f1190300590342c045007401c12410100d0140400744a074008028020301080180305618140b1140b5154410807451540d403507004140042c041c42e003040c1291000c1284810034008013001420076a402400ca15141110524101d0389407550403440d4034600b0810442045036142503000361071071450160441d401f09009600080541e002110700325080040b1055001c4043c3c01002059071911054002c03607038180c00f5803405000400c0510000340003011f1000c0707000411400c84010341c1c2c401000340082c1103c2c1040c4602800d00007079032012034041d1084912000c05503106484c904211605a1039004071030301c405c0780100b110b0154a07070944444080840340e60105056100701c0c80d08070082d41c0a0f004241c1443c0801200030014601180702e83d000d50715040105040750b000380c3c00d419150030085e00d148080b481074940c0c100c10300400380005250030304000426002550000b0301e4100d60b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 99490431 1250 99489181 99489193
    0x20f040806090f010e100507031103070f0906093501050c04080118020a090509010e0f03091c0b0f0405010f1d0d03060609120c050a08010902011101020a1b080d060b040602 75
    0xa40190300b05d03141c0d070040301c0090f07000409400000449a2185802c48034620f000f003001c034108400d643c0503500c01e4031210002000300e100384805551004100300907100c01e1070080c034928030b0800a05c0202c501005581154000f40720400b02d91041da04020110010a1000744840d00e4000071148568110b8499002954203004130700c051204a14014010568000d000c00c0d2000d0800050740d00a0000501316020b0350360325000214218400c204440c005110900150390355024102880301201c1c046540c140c0250503c5007034400140c50001450b0301a0000482c0a81540c4da800c0081c050814000901301d43c0d85010040303501c00c1c404494030740c0d42d070b0700c1e40c0300301c4200814002084049801c035200701800901c04d09818481c612101110381070391801780f0304010301280c070f81c00066a403443d00e030710140c0c1580d99111175408558000340c2040c0e669030110000c50501941c100046c100d8403082c00c4000240c40b038202810108206901a0340c18103081640402c010368460310014091340c040c0c02980d015100708 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 99491681 1250 99490431 99490453
    0x720030d0e2223070e04060b07060207020112050a0203010302090121021002330112030c02150f0c0109030e06090f0d0c03140709060501080601050304030c0204020f04080609 76
    0x240c11079628100029140b55500d4515402034503030422014028002d407a1100300300c1c140320030ba040301c020b00d40e18009040c22007401c2415014009140415440780107038200340741081540c18200640700e032607410450269580f40c540c40120341048041d0058100540340c003061051009040d0b0145059901c02e80d0000c106988904000c641e8001c11011050101e602400c03880041c2050340d500c429001103801150569010207402a0840410000094051354040300102054440e00100ea0040c624540d04190340956514014450200e0080103401181c01004500c40c0041c96011030b030b00c120320110442e4598041d406010b0103012400700c160b0010380002e03401c154074503151040318400040107007055038840400d03050040c3c0d00184c46041d50340e03104c14140040424072a01100030090b003102c0c0602011402d15040d41c0c02c8440580140e07040021080c10498940d801c04100c4e6045a014100088554154800600688220849520418004580000e03004800030f1800d02030701004040d90004410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 99492931 1250 99491681 99491687
    0x6090c15090303030510120f0c05061215010e1825030213051905040902030c0a03030c0b1f050405040c030c0602030915070b04020909240a0509070b040504020d020720030d 75
    0x16010b01c002100c000c0302c100f0002202358800c0c00103d80304411440c8019940c400080700364001c80c003918800046001003160a81c58000c2c031400e110400d086c802c04000b03000c1c0c00300f4542e900329281c04400c0001140450f021154429004110f10050581e04980c039881150041c0039400c040d022030724000300030b800814503160080c280c00d080f070284d500c440c0440d80b400d01084040d00321441c040c0d801d80600040c00c242500d4002c202000f85d4042d841c0e641c2407410520f00043e800000038084003200b040703040c0200300d0720903032003900044481c2110040b445803114282903c03014110345c001400c12003020f03000202a600400582004442120482c00d80019808040384e03d10440e10020031600c00c21000400510709240e41c2c3c0e4002c003401c41140c03e00054504455042c010b44a10302c03854510803403c02208035410701030181d105d01000c0151544a19004203480e060046020b1a03100302e802080d80311050142d07505a540360f0390001e50700e11424170650710114201812040f900e0281c081c400c5080e40042c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 99494181 1250 99492931 99492961
    0xc03060a09150e19031404080a050d020102030c09040903051603090906050f03070509100905070e150703020d110f070b09030c0d030e010e130e010c090603150306090c150903030305 79
    0x140d4044c08540480800d12884400d55a20840920500202900c048143c0d00042c1014080c06001480340742600c2c01d01c80d00e8403185454000440e8010000c000c5a6991082522075103001942c0204290030b162074141e555000d400809110303840c1e01e0500009140c0d101000340f00b114800301040040c40e40366400e00c9540ca5403165000d030140c2c8006402c00a030300340f08400a0707020303400402c070904c2c0c142c94150140a45005440c1d2070000707031401c04410b0451900c1e0160407511482402060701d13248040c0d80183d296a80982c0550a010000b1007000030301c1e00c02c4c403482501030095016288800e440d00380e04001600031101c060700912819003000d01c241050340d4140301c00c0c1d4160300c4080784030154500441e40280c02100795030b0000580340c0c6042c8000d01d01e00610700041d131404004140103608800080c443d2038103501100401d8180514588110000c024100c152500300001080050003800c044214508686c0400301a1841c410102c054503800034180c020340384241d0b000c0c0000d071948a80e07012021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 99495431 1250 99494181 99494201
    0xa02010c0b07030b0a0902030603070902390706020a0c080109170d02210703050f16200d0507030305010b0a08060d03170a06030c050a0e0403110c03060a0915 69
    0xd01580340c100118011101e41e540c4030310140340c0411149400c0010910840706a40110000da1300841403003640d01d001d10a5002900000a0450034500f041100050340a800460b10200800d144c0000015080c00c10051010f074010f0000c42d9013a60707450342c0c02551011030f4a000c1d1180c0b142c600d00800c0c0904180500002c690b04404c2c0f01c401c40e0b00e03400c5080c0c6240c2c410b03845258859801c010310f4030740a4210702c58a4898018038404805483c007071310302505a580042040707059840030010132071300880d018982c107805013551a15041e0b02072100c1d140f510300b41c45154841d98900c034038440c190840390700c48001d0400368460740c3c0900080c0d030f039031110061a0042800800208405000146c403e080142c05081050302074038100340d800200c203290010308041968428501515244144184803004a411004140075106102100c0c504040c440e444ad901600050030030110740404500d10000b0403241408203002004c0d69039a05180d04084010032200e00d0071039054a616090351110384951050f00e00c00c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 99496681 1250 99495431 99495437
    0x801020c0616231801030c140706090c030c03031202040e01030b0903190518030c06040905180303071701060f0206070818101d03031003020f040f020315010f020a0201 73
    0xe511814a68504804111072910800c2184081c2d00e2061051049060050f4490340c0003582d103100342c0807601c1c0500001c842c6141418241070000c0846075221000d0309001c904a1519902c94007a40303401405800c0c0064054848070707400b20040b0038069400c5000382100c0c03080d160060031030040c0c44230105a002c0c521400074103203042c01c01000450380c8441003d40c03011840c025285010145032400c035a0b04110040c100000d5000700d101c0d034807003013001074038200c621048000381440303e14040060701d54419401070101998541c0c004c01c0001020952050540041e501944d450f46084080188520303001d0a071400310b0300ca01000040c105009591600c00080254050603d554410000761035400001d0f242082060309803603410404d0700203100405000c03010500c080303103030403003c40040076040b419100c020441d0010800c2c41f00400000c0403982c1101e0b07059403c1421184a02c1c002001030040e1304550b0b20080c00001088070031140580380e035016850988803440c20608205d41245c0d50b004501d002408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 99497931 1250 99496681 99496693
    0x10218040c0c110906210f0601270b06250201030f020901021005090f070b090406092705030405100e040c0203030702340b0705010f0b0f040504020409020a080d03060801020c 76
    0x12410441c000c190f00c01c078050040003d840c00485544030640b00c401c40400b454101800f20001d80c0c00234000280180810040c80342300c40000c044420742c0c8075512885480722540c0b803020365000d89034002600c3d04220046420441d402300b50348540128100303140300300e00180c074146080b450642c0601c06d450032a20185d0040001d0100f19007141d00601010f8801b400c41c0c030400304c0c48060740108000c414046c2c071001003055143c0d6454410302c425078049400600c0160300b40740246000c50040c10041c7c0c0208042c006100c080b06070741c01d0550540c0301d83e03000190000d1307048039102d0803560411002030100106460800c1880e1260307008a8480c04161034000041c2c008441071107590200d034020740d4002405601c0f005000300182844005164180e2004550180104054081c054280704103070600f45422010b010161301c20000a0603105841d2449214566490110f81551900d80c8040d44540e806800700e610309440e094826581c45005c041440040e04001c03000c1586407041c020385014425030401080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 99499181 1250 99497931 99497963
    0x30305030c030a14011814090a0b0a02040e01060309030f030b030304050d050102090603130507060905032d0604061505040209130902010c120c03080c090102150c0408010218040c0c 79
    0x7119400030740340c2e2092644920040c154109018030040c006c0c900a4640714140441d080148140c40d031056607040c101c070714007081000c03043c40800d6505c0c0a076031040e03900c0d4035907403030310044002801583c020080081800c0004100319815034010b8580303134007039110604802d18004049041d41c0448501c19003580003408104020700346010342c4d040e00d910aa00140c01d002d410380119501d41c01c101d5040760507a0130307450000c041c40418464540609040d1401040d5503085c480801da459502d17001110040310000003095220194140c54081c440c03441064595504060401001420301460b10b081100d20010000400740307094822a118007101408006040c516544d000c402491040b00580c10b203c140581003001403010f40039000da611240d141c07000c200c0500d0030001c21018000784020040801044080f903a82e070002540341490400c0b80700781800750b6031104259880e004660140b0138030b60020400b042c0403820214200d403520001d07182000820340c2101d040340d92000d0000042d0203c000312840103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 99500431 1250 99499181 99499201
    0xc091a0f0102010b03010e0303070806060a051204020d0605090c151204060f0902090406090c0b040305030304060f0e0a030c051b060a08040512040b0c010b100525060c091a0403030503 80
    0x8000c201400006401d50300080070a0a580080c1d1040000f03070000000c010019030483d094a8000e141950003030b0810010080251052003140c10111050a04200003401c642d80e02c076828800d00d9010100740214141003540c10344ea0110340580510810940c0c504050003c94035041d100d09400340020841903868984403800100219041c10304141d44407604034026865400380980514810980024010014105226414525004100c01d42e40401c010000f2980000c1030703030307007140d080b05000403c041c8248000c8000c040d400755800f214042d9038441c1007895004010004c0a1b4051000e81c3c4c0f000344014190043c2c481c208804030340c0014180300c8040d40782d20407074600b68400d00c50b500301c5000144410960074641c0040c0e00444a0480000321041018020f000c0c1c1c1000c9902903030300d401e0313611a020024020b0b0203003420315035440300d42c002869484248280b41c11120342d000300e8104050841040d00030135504c1c8500880d1404241c04070b0403000020140201c6040f250186c0da182c0c1903485100d4a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 99501681 1250 99500431 99500449
    0x1d031602011407170a0207050405060a03031808060a0b090a05010b0a050f281b020a0510050f070c0f080a08040303080a0e070e16050702090a020702060d09030c0c091a 73
    0xc581d4006000d003000044030220820740300682044c045407103100000000346048840c2d0000c900860a0105002a035100d00c2d000c2002c0d01e03071600700f1103500c10080c5100c105100955010315140d01c00d1000780003801000e0340c0000d003a40313801e40e20590290340d2902000141c030002e20070018802c40400030b010b4100e2140c0082c142c080001c4011614080f508036541080c4804c10b04041440c00c420151201015042031072030400350444c98031040450bc40350000390780e242c00c0b445807030f00600c1c0012030107101030b11134070444a403e08812100c940361360301030070214800f82c810700445000904030400804c9601000580071001070784190f0042c6450309643c1c0803100184040d000c10386c02611001c42c520100e8042c00484050100700d00c09401d28070300802c2d000e0000d00903824440a000003040701c480980c440d01c0220f03034000005000036075182d03014804205603104a01d140300c00107241040e0f140030103501070300c1c00c613809025400e00e6040c5519248003a003161008901c0032201442d2000c3d00405081c50012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 99502931 1250 99501681 99501707
    0x305032203140d1215060e010903050712110307080a020409020409080304150614060904020a2607030501061b03080603070801060e010f08070b1608040306060602011d03160201 77
    0xc4480c0c666030b90764007511841120000704250032151840300c41c1070f444200c44034038408045081c0642d1201c2d08864010340c030503004070b900f044500b07820030701e41c0c0c1d016060394401142d105084500e00e560b5a0b646004006210804890810034840100302601d00012401e06440c003a8000c0c1000000e1a400c00004200d5040101c0e041519180000c0201f10350074003561040340100104120150406045d03400c4492a0b00108181c02e42d54051a40507203070740080d180981810744005903111b80d840800d80b0315000c0c0024081107180d480d00442140540e079205c890040c0d0041d2000d012f9a40c17900b600396240720107891014070300d889070708030320002c40d01c26202280c025101505030742160780c40e90f008600703640e295000422044000401040a5640300017000001e0008030064505d19080c00740c0728400d803290136910480d000c80041540207100c1031034122801141e0210080100907511900a406850405c00c881c10344400c2c0d404120038004080300320340c0444042d180d2025640c0c032541c0199188203030414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 99504181 1250 99502931 99502987
    0x8010302011d0f0d0f05010e0619050c0c0f030403120203030705091903120201230402210102040906060305010527060103110f03091509010603050303010513090c0902180a030503 78
    0x58203d807503d54a0501d041103002e82e0000c8002d000368241642580c2140e0900700340355000c1000c0200c0c941d044443c004d191a103200340401d09484031550707982103024070307181c0140b00c1c0260701403800f20940020082c01103078030030806100c925070390520a9890b4001100d4a9020490800005070b1500c0c1001c94410f021011401801d005030b01c9031192008181c1241101c40940c0d1750303840b0301008003130305070070884400ca8068402140346072903404510030745900004c5110010803071403070034602078080d0151000b6000c4d07220f041025980d221001405400284526401054180021481c08002000980480d116264160310540f2101d0044006200c0e5141e11a910f40041c0900b0b8042c0c0c2070900198001e500310001440040804002414918005005007500d0b130b1500030200001030300442503334110342c02120741104501c1409041005071020707040080001e08280001f2460250350360180c00940300b0903c43c54042c0c0012030500582200b03600014049034010303c0700c4010310303031144c0d41c0941b029801c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 99505431 1250 99504181 99504199
    0xb0703030b03100f0f0b1c030c02220501030b06010c20010909021803010c050c0a0b1b070b07030507020d0905040b0103060e04030f030c05090f0d03140a031a0108010302011d 76
    0x545803c115204000503000c00c60f21410301044400c414082c0305644442186c0c110b01000406440020407481100001c06201810000b50195520010084442440b451041400b075070701c0710950b001005c090008907045159880820f0741540310340d1000d1081039000080210054241c425280c19050050320541040306405002c00d01012900181c590308510f00000345201243c40109070035608041544010082e0900240400c1c44000035481000d5412071400c00d0b4a45a9801c42c10f80d54034030804480082000041e00c0e402c0124428203244980c00f0b96504116644503003000301c5e114035071200380d6800681c10349024891883c0503440403448000504002402503a1000000c1444000700c07815000302e0004040c00b98099014060008240d1003458043c0c134000380c1c803000a800141e10090301e4007907580c1e140d0040030140196680042c003081d40c08043e44450500d680103000e0a402091445580c02d61050030318254014180e07107040e254140c6030407402d0340002c014002c1d00a00d4040c059404a060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 99506681 1250 99505431 99505453
    0x4050409060204030519210309170901021203060a030818040e1c0503061c14160609121a0406020403080f2203120c030203130b030f01060305010b0703030b03 69
    0x3031180c0c000340380c411080035803541e1850038580d051660001d003c000884200c6007000010340603034400c602105001040781042d06a058044005042070346004002c900d2441001d1411010740e8050403560809a00f160381d030807914510780085000580b40340b600482a100280009040e8101410301c1c00105000c41a41d4640040000c3c26034030a0512042290030404076800c0b00502015251424201401d0280c81d50074103801140450011030103001080761188040010400107a070102c00342c58450044840b0300b91964902c4200e483d0901c40d1101142c03089400240c1119809130346103519401191601001050f90580004e504c0c0c02002124019070810010000032a00c0c2c025015900ca8481c085898100314100107030f0b20003440c00c0303100e040c11344000200001200b02c071101060030030a140410703c1190030719081c1d20754003984035802070b140c0d44c07008081042241c50000e148184070501d02c0120716642c4402c00d50403240300b8042c0200c0c00300b0070006200840e000303400c00348420300d0250440f88103c0c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 99507931 1250 99506681 99506689
    0x19060b06120106090f080a060c0c0b24030a0f06090201121119031406010e24030402030d09060e06070f061410050301060803180315010905090610050121020405 70
    0xc107103600703040000184014800c03641c0c800078a00203003031002c00c4921190f003800300060f41c5400982c00282110f413100c410b442d00c64850700400e00c100da17100f01607a0b001e0400810144a404511a26503000b001e0507407a001c0f9494000b8401812541040e10849410020f8494038090440803105a0505c142c0c0c4074443c04952141c880d00c503650299040e555101e0342904107042e5403c0481800c1c0e41058103043e62003400202c0d1840a5402c000c090828400060b2080049a40e02e504e4141c040248506809580e100b10400c900951051784200c054030404154042c0a450340403003401441c000410a1a465400341040c100800303845004243e10844d405441d510072096852254282058805003400c1c0a202581c0f02018805404110000d2101500b806012a0380e4012503400346038600001c10b942d0803c0d00c09002c207094080380881c1c806060342e110954200640303801d0ba100c2c8603611039200000d407195800e079800d03810b54005a5502c040c4100303410805207031340b041d64100000603070300304000582a62 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 99509181 1250 99507931 99507937
    0x1421040605010e01120b071d15030907090504120e030109020418050f030c0c04021b12120c040f030b06040b1c03020f06092d010c0c021e010219060b06 66
    0x100c50400070072250305204200c032004006034400d8103125031100203100098100424942c1c4241d10b07140c4040c11400324142c804640341000e0020ba0040c0c404441e420382901203078000d604c11000001100d482580d0b030030058003250f00c201c401070300301000d0031800a21188640e5456280c110000c0c00451000c14030740028003110303940d403032800e90103402c4901e074402c00c4400d104d281034004082c00034506002880080075141c0e14181c2ca02840f60754000f940d220300307031405054896580322a400300c035020480b4020340d04042c1d024030310800c074040680c0000340400485c4011201500c503100c80c17451f02c1c03d1850b66007020b0510080c100b60351140d1600742c2c1d2003075074071100a001c03034001c50100c44841140003810040c0c00c204121001250b96004041004548200085d8259115110b14610003080201100e070720788020440541609a508204208101a030300600c2e04180e24000c03a140b41070042e100c0c0c0c01d04c02e0810030010b6503016800000305194181034003000d4410b00c6001e8a80859642c292500280301c9034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 99510431 1250 99509181 99509183
    0x201090b0a1d1501060e010207090c11060a180b040204020c0f030901030e07050d080a020f0f06070e040b03070506030a0207080706050901060806010f0b1b0a050a020f0f01142104 78
    0x95842032030b401901504203441c0c00075031104000d01840c07800b80401c442c260105010b50740521401181041c9544d1080142c0c1c0c00070060300c001000950b00c200350050200001e40581c0e95540700c0c520100d5040f102e170b07100d0b44a41240329103001d03080000740d0b540e50040c0f41000700309980c4030341c4c02e00080341c1c090f80c1071208405071407412014581d21904113002400300c03080f6110000c1641e1100506000340e40310b001d42007411a400454250b1200c80940c0c00301d141c100c6203031908040d4058649020201a40040c0303250082c00c0307644501d80d200c901041440101c61079048007582c0f540c0924000c12442c01c103880156044074500002620f08920f035141d0311381c2c80d4844101141d46a5542c0200f006401c020f10071361015005038405006554945140711500001c180110300100711700265003000141aa03031146900200c0000395108200740c0c0c00c0003038842c980c415040c0c0c0501c80101001c0164540401c440007050016101c000e15084400c2c8400f071543c1240001d90a40c1454816052600489240040c412 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 99511681 1250 99510431 99510451
    0x3030711090a111b0f0d110c09040308072a0308060f0301090c03110303040302040e031209010216140a020307030b09010b090103030804020603060409171201080a11100201090b 77
    0x8054500074405084001005450701525060103100248900ba0881c0c04118012901c20600440e80c0d5402d8108034410001d103070284544001245040d070016080c01c004044282905e141942130004d20030509001c4400800255000c1c0020304114002d070180841e0312408015152206c1102035260036040c040d107800d90120341a40304002c0c039454040f200d542c450b02c00350001d00c00800c0d2583c07041c20100c0035000007411064018007595482d14100199402185c00070014446012600c103660303280d500c00340c1146e02c150035050000d80c0380c85050003210041148030220900c0c2d540a80c403031001041040c52006850b02850114001603038040140700b006d10300031980d2b4911802c2c0140c03614211007010360241d0069400d0300042001c240c20540c0f540e405601501d500c1d680b60b80715000580148882c040c01072011221002030b00320b206255006d0301070344001304c072850319590321001c8031561003100d040024000d441d01840040c41d402d08040144402c00203000124400c1c1e0660395511124408589100c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 99512931 1250 99511681 99511703
    0xf01030513020a08100516080712090b0408030a050601020d02190302070f0e090d03110304110402120403031b09030203060c1308060403050703080105040203061e0d0f0510050108030f0a120209030307 87
    0x491103051003055004949132001f0b0161980c00000648411001015242400103800e144104003400d81c111441c015801940f61038245014900740909800603a900c40d506441c1c032002071102c3d40001070850051400c0d4004100704050981c0ba400c050810039001c400714026403000062800b032004003c4003030400e0500c420b100e4a880d002c45031500c0c880c8c84400d000c060504084440c0142580c08a9412542141204906001c1c50001c2030180c420b5101c0f10b0116202d00080105041d8107501290040b02031075111541c0e141201421201d039820b07800060740c15080304011890801148005012023a01904409141ca0b44c1d41e080c582014406c403800c1c0c3c003086001411008041c3c3c0144158007501080b2811420741c10000b000c00c0d0341c400012031048500321b114106181c2c990700c106006560343c5d44050981d02d0f0756081e18102d51290b00240021050505020001c0780c4e510010054800c20f02d07180f0341e01d605108140c0421a20743d040d003090141145d030300f00414800c9071000e100608559008a00c4802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 99514181 1250 99512931 99512953
    0xa0206190e0604141903142b080f04110a0803041a032703040b04091418030703081b030108010e060a06050102100b04061e0807060e0f01030513020a08 66
    0x480381c181100001e2040c10100401c1c052400692540c0302e44001c00c0c0c07581502c101d01c040c101c072500c810039040a000e106000324400c025503400142c0f0100d4001c0041003c01100307440c008100406c00184041010a80c5000000c010390040005240d00902886440496200c0240468519000c0381c011711026013001509110b02801d110024050044441e4803d28619044071241d200012000c4401d090301002c07950b607160b248c002c106a80151242541c51640d03166526841002080c0815078200c601e02584001440c142003100c1107514000c0c41005103140000700e5608460b0048010041001426201d480c82c05000800015501800410000240d100c1940440e80d1520800a004a00160400800f80160399000c00c406c9064824074202003001015000014094131103500301c482500c0c81400194024020128910119403100095400312a1120703000c0340e9240e985666960400641030722031405501c00d40c801d03640103941d8615001503040d9079000401d4244c0e2580505010f511501c01c1003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 99515431 1250 99514181 99514187
    0x80a03030b010f0f05032512150305150a020d110c0f0615120114090a0b0903072f030d18060810090b01050c070b03070f110604140a020619 61
    0x541a0070703090030898503a102c000c000074414060686003408010010000c44c1d00d0703501c1c1d4500b44e820000103000501480c01c001c800240b8101d407000d0355102082c1440c84411a10740040540d8050703d030000080c01c50200c29040c1c40c110000060808514913500b00041d0b114420703280700c1c90314000458030200380c0c3c61404480291500d4000364034110690001e2092164010b0000b01e9280500020703902100c20744000603070940101040004819800e01c000c080105e81e00c07003c0b4080204038400c3c5512481d41e19446407081d5607009a040c001d110820b2030545422100700983c0d00c5848441c1540709010f2806200046404d00b00e02405181c04244596940e40c800c0204040001c00344c01c0c81d26195019123011100d0842540c107030301c00c1512040d942c4440c001680d110740210380a420036113007107856843d52140185038503842142d046001400c070b0030403403088602c900f14103181050a4001403010740c4494560310361a107080c3c0c5100240d449018480c03070050312900041c01c114a0020401c25100030050b41c00703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 99516681 1250 99515431 99515441
    0x5160f02010e040c0807080a18050a0201170115140706240b0c1213080f0708070603050106020c12011d030301090b030a0c060311070b0103050d02070501020c0a0902030406090b01080a0303 82
    0xba40f16504080d81324203100d03031040030035078012850703d04136009848030703c6d440000304905811100c2a400401c0c1da442032003000a00079401c54400e0760f94641c1d45e1280303003200e124003200703025001d02106180f16542c0214413030404040d49000c0d004400740b0f071810960f940b00444d0701c103d0441400758208001286254400e121500080580040480c80c0200d628062a1180c000c0341085a4945002c604100e601b91001d0f02d050180c007804d4111000800c00c801210b650794014490040d45106018011600074402d00034241201c01c503400520000114030108a030016040881156941d07991070810441059144980c40f0500003102455581d410b082410041d02c0010105601070350100c4030030b800043c0358213420012520f640c40d00180d11000b03032801c04103512805030090070a404032400481480f130089000e00345c10349103408540302d1603039940c01a61249040c0e00010752014455108000c610400c1e0019544144075100002d400d4506907510122000c080e08140740541c0000003520400d81c0503c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 99517931 1250 99516681 99516707
    0x11205070224010803070b0a0b06120a0e01060311040c020f0d090807090501032607020402030a0e0610050102120c031b01020316030b030601230306150a06090b03010506030705160f0201 81
    0x2d501d07103560600d000c2c01d9482c03150540091a013100e0400007181010320340c1c8062806d1500400b00341d69043c00786c20824090000303030b6a44041500d050b58180d4403120500c15442142e0740007088054140b0704d0010032004020b001d008070154001c0d6030902008c2c1c141802288940f541035282c07640c010b8200441640380203c5504130355040d51400300144003207000882c100702d00102042c00c0d4401421140015040e038020381d1b00c02900240040140910440e5a07006000070070913440c1121019a0f4010819070f52400a12036140503030480e121103005200c2c0320b00100f510040710011649000c02c0148540c0420140c0c0e591300802e65404014840700c24101b10740990004410b00c0d080c421001c0a5002179242c0d60f040c45810348046609210035a42020901c11803079603203008050b200c0910b003450060a4104d651035500344a02411800490503c1c000e49841040c1c03802c0c4a25241141e00b01020b2044907800034001070b09005c1c080c00480b807502d41107248440c4461241608131401011440050500b80c51300755 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 99519181 1250 99517931 99517993
    0x109061b12050f010308090a0e0703051819060203090c21011803090501080a0b060c0615060705070909170f04090b04022502130905010e06060108160804020112050702 73
    0x307200b00070390f2612209064030b03007240d54680c0e900c2a050001e074801c05076500250300c08150204004183d0781560200b40f060845006003c1e06820400d555915002000c13020161442254010b40c049065540030f0350384014881c041340c172a0b60b651400207640e06a40e41025030b06078010702c0705000010081c0601a01d07064005000c0d00d044c4101e41d0040c058002c103000c0c0b68100055440050000c03185034101480040300580000e40d1072003898515511028210386524544440140301601800c0290450700f1080e0400003414480d13051103202406400a0182600c100c2d0001c010b00504d0b01d40c1c000109850140045c00c40d948615142c04130060f2554411400e02c61441408031a000c50890700c01000c24003030880541179005042d200080b0041280d80011600c903203090505020418154005400700c50414103c410a0355044011161180304458002c00095214410042680902c038200d0300280305041144080c021412039404540c0110b0700d080c016802600d04020003003102c405030328140000380c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 99520431 1250 99519181 99519191
    0xa05010915090504020309010b01231e0c0613110102030406120b0d05030f07020f090c250213050412110c01260c0301030317010302030a030c050109061b12 68
    0x103800d0090034441c070000c8001c14804001e8140c8100a010007404004204640300c0c100040654000c0080b0a2035a0103d40c84154040003c2103660040b400206581d0050b89440b02c11030b48d400c01210030750100f0300c24907010311074058119820302c030310341c4620241045041ca400107818901760485040e10400d0564004100500c22658085c0d601c642002c80c042d80800e2903c10007011681003138140c0000751403400302260000303000b130321000101406030080f80c61050703507509442007081c10b0301d003525840312400c010484440d011040c00030a440103045440d001c03900c01e50a4001c02e1416042000304100199160100820840c0e4140f03103400040d45480e200082c004110700302640c17a500382e000c480c103004c0c090130303080540c3d6100c0d103401000517969a0383d40c80a04296010310b08941081c0001ca01080c0b450300100d0b4034080301071074035040f20740040060411a141d9202691b001840d076406803042e54851300e102d030116100703015500b9120f03001c00751012008010880181040610074010441500300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 99521681 1250 99520431 99520439
    0x7060c120507020d0c03150b01020319030905031303050d120b030c010e1201061e0512070b070821010e0a02070321061710060f061b020a080703060203040c050a 70
    0x10303152280c80a20103080c07041d075600721800050340340008814000c0c10004801e2000c420030080000d441d04a4880300003e0000c100c20740300681c0c8170b019211490140310520003a01030340b2403103600a4203640c1d00820a803460520480c444d021803d10b107400941d901d03805803040480180d030041000c0c8074480c0702d00301000f1000d80341000944a4404020090404c42554000c03102695401021520081140006c200480d542c59542e98001c6007080d2019040e0303402e15002441c0d04007080e107006444014005040c040707007446841145604804000d0b07442c04002c1c0060000408440e44411841081041e00c2c42c181d85441d040e8802940003c025000030b90047c8142ccc00029000b076064104151003480c41060202e0a202c0e0340d000305125440a00d11b0101b1441e0811001408641961000742c064800e03c02070b41c4031304054001c2c10240c17090300c0c0000c0c40070010704e41e25aa5425038105a51000b882282c503550b03107804040c5000f100750400d0320542d5002081c4020000701d00504030040c4070503240030b0703035141c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 99522931 1250 99521681 99521693
    0x604020f090f0102030d022d12010b0a0c020a0306051014030709090512070b160906090902090103060801021305040b0f0102150a020c0a03050c1519020706020c071707060c 75
    0x1e0000d455005400040000507140c1c001d00a0340c0c3c0f816200d8104546131801c0f14a41480701c120702480c1e849070078180350700c607280c4d8a4500465989880365180c40c40c0b2646040139a1440b0303808000c114080040b128070f040c0059694503541c60040d80641d03004505414026025090045168030a01030000d80715200705013610040384810499261080c0010160301508040d42030454107825803000b03040010783c0200f00003040c103420b405010804024200d000401130b0580f50b4444a025403008600780780d40802c0300000a400401c0d2040c018900403c00035910004036003039030031603418158294601c860134425400c1600c98207443c410200d80d0004030709040f9001035141d02050b1008454052400001820020182c040b2035000d400b01045442003001401e0041460708460300790a22401544c448001c45602c40e01c2041c041c5c9200c1003600001360f10030004c03100945c800d0b48226441602840203040c121020b0106100178802001c0b040d0110314403e00c158206011a00f041e030030701400740780110200d41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 99524181 1250 99522931 99522937
    0xf142106010b031f4502070b090c01050d09020f0306040510150b1207050c0d0807031a090c090406030816020a06080403020a030c060204150c0b0702010e0604020d030302190e090604020f 81
    0x40310a40341e0340c01000b0800300444170444071440301008015620300da906580340d580117080290150b45103500985410300c2d0305880740f40344030f201800981c00b4440c0c20703c078540f168410100c0600c010404042076000382e0101e030604c882100d00b135801c0c3e04107210700007003000d03a40544c0f01c100c001145100d140d41d0a0202640b01c5029111111180e48184000130341d00900900454a402c4980021180503d8848000600c480130884a55001a00300420300100c64046040340c24191070003403010010b641e928964610581002d5809503220789c0b10704001000c1000e0b000208810003549104184284070341c014445032128a070320440820200f10100b00109501040641c10f040e41458000102c81c110f003010406802240c110b80b180210710720b1500c0f000d0f500110001101032144010014607600e120007a401c03110901c443c001c0a07042580010018a4801651642e00744681001410140303010001c0d102113980403250008500003245026651070402c54440d031000080b1000d41c504a041d41021070640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 99525431 1250 99524181 99524219
    0x6030b01080703261c020702031011030412020c04090302010e0d020a12030b0409060c030b0901151205060a08010509030307021605011b020d05010f02130f142106010b031f 75
    0x28250005140c040c000c41c0304170f0317203030030503150711035182d200044800d07802135201e241c00301e00c02e00c6a00a107140301c9000d80180c03183c0001e6403c00358155a1240c95070b00b43d480054585030114068030640c0d00c1255202d00c20b03490810302035800010003240d030111980c038004000103e6002d5502030148000000c107485407100d0700403091316010826080510118002d0406900001c02d01d82c10101c503425010780c154840308085504446443c55039a0310b000c202c9504103c4031402c000074042c0321806605000e1600440d03044240a0007185280b5901c001007401c41d50700352103034082c903000042032008441e410091060010302c14544110710707615000018007450b203d65204a07424050503401d40540d0f0300c00e66161451900100280700c48482c10003c04020350155622000c4500310b4040850341d040040041015180101221f0f0560000302c802c00411001d1070103000807003000b010b07400d00c80038020701c80a4001c0088140c2181c803420541850458810b1a144040071000f28000070401c00b031030399080d00140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 99526681 1250 99525431 99525473
    0x9090a0201110307060203040305180f0604090209010905060403080702180f04030f02011b180b0903030301090e070801060e2e150e0303070804050301060b0304030926060a06030b01080703 82
    0x203141c900a0b00c2e8154020a03501034040c0d403021081000345a0040001d1a0155500c031841d000060000704204003a0b02030a07030160040c4042c4414000b85065a00901c00c41030141081d2142d5552a00000c00c0c80e800b03a002218680303804030301072085083c1312031031030b00f1102615540001c62401d0342c4d02903511400180003804008014030100c80c1c1c20300039482210200e9520300102844280e2840261444e03500300d071012480358030b00700001242005c040c29900182c00c0100031b18910713460300c21140040c1c480f00070783d040207000d421000680707144240705d400010900c8014140051600e00226252449080d0180e062818030102411040310360310349450a658031089000d16030012114101c0301d407640c0b020314907058800010858140b11502020704202c0d071040f0002d00c01c107a00d802480c40303580000d40b0700802080e0b40c0003050154800045007030703005000c01c5031218603000103807005a1801506903a0742600ca95650024003d2090782e0032a2405404000f00418032b461855076251006d0951010100d08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 99527931 1250 99526681 99526697
    0x411180f01052107030e060a0605090702070e18010608030703080a1a0919020405220608070501121e02040303170601030c1d190803030a05091902040b13020415020c09090a0201 77
    0xb40242e0092150425072800c1f64130f140380044810700100000c0c0a298071604c0c03054001011144001155000d513051407031801100e4a55150084a04103d4268a1001d54039100d01003064031081025045850023640c0c0c444083c20080ca45508032003400d10480c460550303160b1500d080f9102d105100350414000300301c0b540104c02c0403078520000d004c0ca070030183e48159400f50145455004082c080040f41003154100600c03a600d10b042c0342e445845100791400b084d08240c00160050045c0d21111800c00c0c841e40c4555445000102c0c02c04a0340071750005c0300480c1e000e548088000f05000465584048282010003401d281d07000c001d00310000100f840c0c080040010040300980d200c5096040907042002d100382d0340705440300109601c1c0d42007100d003c4421840c00c4009901894000f0b0144204460300001c40303051100c64003030101134100042c0d00c84c0c00c000d00d0a0f112a0401131031004000800c2c50840c1049400290b000080c10f1400c0c40c00141d10903040c0b03409106609002280e4101c40d19070900700214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 99529181 1250 99527931 99527941
    0x140106030e0c100f0e090108010204060e10080c03040303060b0a080910061404090f02041107050609011a062206050a0207060315050f01020a0f030f0801270203060411180f010521 78
    0x502440305d0700d8001d0300709401c800001070003101500904241c1c1c2082c1c46061034103501600f807180340020b04218400060342540480c2050310080d0042d50098000d02e030101c0d41035207442c00400c580d80a0100c2e4400a001e2008001d10f4003005d02440c3e0baa0f004d04c4805120703180c82c1c8403a400c08051103d00803845a0741d40d950b0b510400c21510300c090152540070344240040c040d000001900d42d000740718140c0d01c0f4012100080d1850b4418424044c4040011700018102c619106c04d100064020241e05c1c21511a0405920480c01d8a0440b100081502e07684a954485482c3e8009051008503880b2805241c200345840c581ea95012100c181510020340e20b092000b100f010040f4641810400094032110160401c0d406141d401603003004985820385580e000e1366030311100e0108018201e102d07a15000e01000002810720003e0300159008a0300074408174203411440e001a03090717030142c01681d03c40303840e010b5149003d0408540d0101d40c58002d007841d6060413200e06100d03800000d00026083d4103100e64002074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 99530431 1250 99529181 99529187
    0x81b03040c0f0e09072c0906100e07120f06080609070302041112010b0d0908030c041a030f13020103060510030e0d0819022203150b090603150c0409140106030e0c100f 73
    0x11802c00c1c0c3c8914403550030001d8045e230300d4100584ea100d01d1046010004030700301c24420700c00d0f0301a14683d80c8a06100210300b1741e120051003006081c502d000d440704000036034200c0c00c00004d4003801040004d0405a4030710300c100030880301140403803103664000748040441c2120000c189411245d5458540380d5031080850210002c1c0304130100100500300c0030051017a0841c48501401c01c2d9003000030640b02041010860900324081161032086550000340003c0c5022041411500030a106050101e001c50320707140011200c428540c0b554000a960314182e010000080000e07141c1000c15050105040c2449016600d541c0075a51403c05656000120707450102c880c4c0e50460708244c82e014800500e01d84928201c00998204e050b0042c5132402c083c50700c000c0b8500b0310072031809160000c0c01800c1100b0040d403d050850001070405031064020701c00010700140d0340c007401c8100d9401502e054415818114068116510780c0041308950707000160403521030b164851070b0228111a03060406038902e40110413 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 99531681 1250 99530431 99530489
    0x10903031112031003050c1c020d060605030102040801140a090803040308070e0901060c0b0601021203060d0c09050702011508060403050409052d0a140405060403081b03040c0f0e0907 80
    0xd000c4150000400c50380c0e030034421304c0301d042d01c5c45901a2104000c0b1170080003900a00d50b20b1225172840d20702c00c0000140b400c00b500202c218841c00010480584d200002803c9030416840f00c62a40d448002c80c1200c1400048500d600c030007200310401c80d048160700c500100d0300009000406011120004c10040c9025149000c84140014038116540d81c43d21700041103995500c400b2110b100000010551941c0081124030b07100130120106825079880c201000342240000304180c03003607420300b072000c81c0113510b9020b260301c118000d4001051000046015081682481d031080e46103030461000e100000b83e00208076000c4409148005c030300c6480302200241c07004129045091310001d841c01403141c0840e194110707803190401d0036007008410200c1c07140c035030b5a0a0444008210390421800a000203006d010501c3e0070940c42c007071001a0b8400118072652940c02a1403e031032600000c40c0801252807136402d500041d00302c944001c0102c3c01d00004480c0d5441160080d400030301051202440c1c0c2e00c1c442060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 99532931 1250 99531681 99531703
    0x21c0c051209031216080714070f060501030b090d080609060a080a051507020a0807140309090a0b0306071d0915040f0e0f0a080d0b0d2019050109030311 67
    0x1440c0018201403442c1c0740e03a540000d011a100405040002d0088030582c8107000070406503032240055170751241c2d8111040140d104d207001006805001c070b540425149a00b8403a02c41c42203500040c2941542008080041d0043c03681142c0d50058500241042e4082c41454000500366640300c055180c050004100c07007010b030406001c2d44180c41c403010034010002041003146601d402021103d440f10401241c0710068203801500c003010800c00f8000040c10074030440001c2c960b401c19203040084c01000034400840a0380c1081d602602c40c001c0041d1841d0510103035400c0310f01818945d00d4000b0220540c0c1d24040b945014920505c0d00380c00240d11181b02d600c071107560341c0780204108074036000c540d032220041070340465036031107803043c54011104a0340000b541d04c945038011800a05102c81d1402d4031025103e004507854000c0354480703500b0300044800c090140100403071040740440c0c030341520138040345d0b10700c54810036904452a0710400407a40c00120490603280c2601c0c040441101c61107401c1e14002c180c00d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 99534181 1250 99532931 99532957
    0xd081012060b041a0102030f0708040806071805010206130f02010207150f030b1804140a020303041202010e0108060616021210091a0408030601030f0e1203100801021c0c05 75
    0x40034410449298020804070701c04440030440c3e002500112014034a0b4281c205002d61f0003085007100c031003100c0f009806c0c1a4840d04031580b402d9111000e1a0404605540b24000300301c82e01d4610380d0003a0a0400d144c0604420300c01080b6925098500341650904141c018010341000500355065900c240401c501802c2d1101c00d84840d1040341d400240401c1d201004080000c1c81c2000719103440c6400702e820791006420409000c40c5440f1600d4010400d0008034280b01d031071241d0608140107880c148080e1005011840740710000c5140c45c0000b6180024010419040100721400c0000581c0e422080c0d0361904010310010612000e1440495030050750401038404910030840802c14001c4180c020000d16481420040c00c1142d60030303000c03510380b041602d004000e40010300014800754400d40c08862044885000850000003171400c00c5e051915500403c032004a0000c00c02040304944c042c03080050010382c00071440c0054170710a1b02c0504850922024026031030700407a1211030b00c1a0117070381c6855001c0c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 99535431 1250 99534181 99534209
    0x503070b090a0311061e040807050a080d050c1608010204032a18090f06021308030703021525080a05060604030f06020307090305030a0f0e060a08061306090c02030304051006080d0810 80
    0x101d0003180c00234400e030312561107441404034241c1443c49600c003c850119000b42980c0d41c0d0542c09495941000040304020711409144403810000381e851f00e00103280310000107030f440c1e0441c2003c0744080d144510b011201c2c0940d44610310070401480f02401211400601085901e011800710000340c207810030080c0005030310788100c906000d01507008051040022130f040c0400c5130b6400d550343c0c490103003160140141e0010900b0b0902000c074690030725880703014185100308905411182001c400107200203000010558404c201d0703000c81510030035801c03101c21540c1a09144c519942c00000d14144400207106a8020002c2500d09005055000c09035910100b900c1d2501c0c030a0380014008410200510009840c2064544203800c0001c203e40704d840390b9030345020041e940e2005008040c0402c40045201070f9551600050301083ea10039581001069805907035641414103200d8501940e030b21080344050301c0d00c5010000c8810005400c0042c036241c0c02c0000842e5503684004003400301d260302c1407880c4c420078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 99536681 1250 99535431 99535477
    0x30c0307060b0405072a060204091e050903130b0f1b06040b0606040b0301060e1315180c020c10020309030a080d1a0303090d050a1b0503070b090a031106 67
    0x150018042c0b03400594040001d0380e100d07a4111822546131203124032070048402180180502c1707104440b41680205000761a040d940ca5036401103840c80c10407000039079564103031810440c41ca8000c0a8201e001c19001314104500120002c5820f4181c1c448d440e42c2050025000003407049180070740c0c860320300c1388039040c008084e501c066a40340c007400c840881d00403000c0c80024005143c0b00080e6020b40760f520702001c0c1142e08100342511401c03c000001a0300c402554071000e5005068000c62400080e603030f2489240900d0072800104030302d80401c0101032281040d40c212040380c3d00040e40040d09c00122a85c07010b200d00c50b201031f4114410f1251051300b500912406000341302c4500d0081c0100f2000407800c01c1007240880080c3c05096032181d200d6456082044800c80038513100303820511103070080007502c80e841c500b5a29010b00387d1081740d88480c1410760074020005840d040c0240c00041c0007191501c2d29000c100c07000500e0031402404002d240c049128120b8849480c0c040c10795210603003000c0280c4000a803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 99537931 1250 99536681 99536693
    0x80301080304030512030702030f0c0c0a090606030e010b0306060d020604030503130f06030b1f12140a0506120703170c19020307090c020304091d15070306170a021002030c0307 77
    0x5000c02d071050702c1380055840c4881700050880344694800e6015600b481c7ca040d141c0c00f103607480f10808280512482001c1c031310503541e41c4201c000600f48280c00040203031800d10085c00742d400500d00e070280d03a45000b89044803520701107109030b03100201321140d00c64000e191000517628041c0340c0000c1c01e03074030011942e000380c6000c0c0303203143d001e5542060380100515513503181102034902001d1480e40001100055141440c00c444c00080e0100b102e04001c0307000c1c243d9072004021118401c142280075101c034030621515403403e104140d040303041591006021840142043e5440b807080c1700040c00b8241140707285000401c00d40603607800341804015120221403907a2000c05500c0100c5060344680150340000401403083c0c4143c42503404180c0286082610f4192028003c0c80720300d003503117031a85091125542e100d4080c0300083c003203081e0407140c3c855818076110041c00c840c42a003004454070f01d600034180f06000c0028600c0035580d0f04484603032400c654402c00300d0644c060314080b011107201c04618031040000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 99539181 1250 99537931 99537937
    0x80a0504050f100c030e010201110c03091801030c1415030403110c01091401031109030d05040e0f0c07021c060c020f10020a0519030b1504050f04090b0c0d090803010803 74
    0x1000c8401d0519105400c0412200414010102000c540041c40c040f00003400340c5c88200c01406c0500001540685808220b2402d81c400c0e502801e881c1c0002583d04070a1500070034403000354100301840400d543c1580c0d41d00f03007440e80742d014403c0804c2d50f02e07140008550754400903181d450849441580c0342d0605140180c80000402002c0303005019410304400a544602c0d140b00807203840012002c41c0008400c010740040040260b00d44034500d0800101400e0f89082001003405c600e640e03192607480c0c1c68600f031501540302c040d101100743c090041c203006030f8510300401d4074001601107410b0560564642c4002850300f000c400c1c010038090400306142805500403483c02201003c1c80107a41e008401d4010f82001c03440313a45c800fa404903605000d07200643d82c5e680c04103600d08490f410000344001d60000062000c211140100b04594000502404282848a5410039807141070340c043c0011940d44d0f03248c14030050b0052810100084c04114000e071810700360407040b01580c0200f15566603503107a40320141c50b030f8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99540431 1250 99539181 99539189
    0x12051f050703050603010b100e0a0806010e010512010903090303080c0d060b0405011d1008090f030c010203011701020304030e090a090f0501050406140c030109020a110d030605010206132004020403080a0504 90
    0xb03441c25000644608060007544030603840104120010705801d1000d58165949074543c40c0c001071401c001082c01c0c0d0080243c07501804015040c030400f980b414080180c40c02c2217805001c040d03414409010002900070108005603641400c2070000c96540c0d603d248074174050315403100342060400c100000d00392420700060080e180203030b030b0391902c018001d05150380d4440d84420003a040b14201c8100c0007424400c580c91034001e4011020341c0c40b040d800001891a540000d040d0f001607950000c010089441e58a85004003041000000c0d821031410b03890103070154800484480c01140103100250380e200a55014030000c5034017a02e4910020000e0030243d0007040200d40440b107003440c11690218031030b03040036594030030300903003070b1846c0f550b0f0a0071070200180d0046031100043c0b208180160076840418403035243d6a10055400042103807401000900d083c00183c04000701750341d5160800f0103e000b0380b41c0040748032090043c1d03141010b801c40109001b0f211340c0d400604003003000710380b43d0001035200004004031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99541681 1250 99540431 99540437
    0x2100b040e0a200d020a150e06071410060b0a080c0c010213031401050108030a03111213032309150d0c0c17040506071b030b180f03090a12051f0507 65
    0x280031500140301c50a00b8004c000b9501400c440b40410680c404003442041010140ca0300380d520364551000705180d904940c1044940094401c40a20520f10401861112100b109004c2c0f042914050003180c4910071101807c08110381c410016440041140845821130500c5000710341d50600c18151070004000c078001111065142e1544a0051405000e074506031108280618500300c5d081c0c6041d001031410007000f00140c1818458417818800c081c04c0d09100d1440c3d11400140b2000b286401000c80d221896603c000501e0140500d0304003035801c081e1400302005580c41e40c04100b10500c0d00d5154010580c480d030204c4d0a0590044030554400c0344480303994403ea0800f03625524403016102e33180124001d264202034140300c5007020490081051036052030003000d69025503180c0d03c600c0c2c0c4201d022106040103449000c141c84040504200981c03a00010502440c1802c000c20005600c911182c4599030342409408484c405001d0300303110750840f21060580d214141401e051410018080441304d84000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99542931 1250 99541681 99541733
    0x1c050f0714040207020609060d1b0c020102010b03070f05130905010e03190f0f08150d03030b030c0a0506070615090203040620181306080307080304060b060a02100b040e0a 75
    0x81c40c1054000d8686190340100380d0341c20983c01c9020310003250010244190713a1030300d03075541107100180d00034204801a04c1d81e0300c005402e03280d400003900351a010403504c0d000758010001000035003540d01420041c0c0b102184c01c800455900c880c00310160500313080240c40e5520f8001c11481c0604000000c4c1000c00140d224101d418440f0302080e10701903026100304e00410b086ca14480318036441100c40d603500c050b00204807010000611b01189641081100031000700c1c0da0b58400815615080040b00201c00080345d83c0060070f410403010034224000d07220000c0c4800d440c1c200c0c0c0c0003400d01e8288100302501a0500c02c544a03d42824103c000d031107071500c1120210b1811603180791400d10302d4122015000403140c003111010013081881100c101015010003080d50703d2101040c0c001c000e02c0100b0181c0d0017480c00c1500c070709160500004403654401e029100f400108206a14241c01003826643e4120780040041c440050002050103000d8a03c031a41041c000c44841130b00300320400d080b81780e01a000e0f441c8506 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99544181 1250 99542931 99542969
    0x30106080c190b18060f0d0f11070c12021206070e0a09020a020d11010b0d0b0603060c0301030f0b06040b0916020105090606010c0605090109061104080d0318021c050f07 74
    0x582c068007401444040f00301040b1804040e641030ba01010060341c0986881e1824031504030071405034011080b06080683c0b039014811344078100d4000c405401c4040d4221a14048403940c4800321142103200f10125604a48a01e8095699030100040070054280a50700c00d40b90800c4000e010800301003a8502c03c941110300440c610910b8400c0d02d040c2015a0028103025aa014003901d407014600000c0c0003664030f800e600c45079074079044007070b01d1100e10030101861a801d0407010541001700c01480d200b030a4009000420109003443c00c19003425401030030b82c05683e00c60b14003050142a074440c986070440087c0c401d02c12240341a595500c164102c0e64003c004644076614529101c860680e4460b0000f0842d070400c00219105a000c5a084003240300001a00000c0b03540e24801d951000e09003d0220001040070455500e007440600c00402c490b103410040401600c1c0c1c220300150300325a01900034055001b03010300944050700085015a009011101100d0814038481c0e82c0c0c14603030181c0c05e207400e40914464 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99545431 1250 99544181 99544219
    0xa03110310030f020a0801110705070503031801050705010b220f09050c15090306010305030703090905040819050705060f0115020a021e060d09060b01030605010e0a0509090a02030106080c 82
    0xe4000c4280d0840e420240303255480b0f500e03050785201c0041e42d21a4181d140081c0001091280264268407240301d130343c1b1020142400b82c24214281d100324040d4101b00080421001c0040d840381c003c036024288243c9807402800c1c81401805851481500000381140612100c0425144d50345d026004d03003824031004894521501c1a10710940000302981e020302c82c0d03020941f07000c08030305030089414944176080c0650040041e02d416001e900c155110380002801c201490f0b4859460405000320007800c0c0b109003013541d142c0003548500d61200009541042000c80110700c12030440f2001d0f50003000b01c0b0114100302740441c03070402e020720840401c101d10002c00050b150000c80c0ba8070f6400d800510461000d00c265040c0c68112100b0604142c0c0f002c0c0030060712145032024810500c60a01400d000106404014009411038039540c001506100e088074290746c8995907032480b1800d80b001600d80c24450b403a00030401d1319100841000950650a221010801e1400020264040c002c00c0320b8001e813a2002661031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99546681 1250 99545431 99545437
    0x405060303181012110a110607020d0c15050a0e010c2d021f14070e030a060929060406170613020a03020402191e0e010c0606090603080a0311 62
    0x700005000302000b1241034600410403071101c8000c0c1c2040d00104c031030100c812003140c464440d207644031a004107030b143d070060b40031000e1b80c83e00b2050030003040182090f41c8083d60f194028002c101c1000540e2030060100022403185d02901e6100102c00e00c000e00708107000034060710300356204044640c03801e031494054500c0340011503060100300c0140d0050a10880010341d00030100220403080d8401c2d06210701118407104000040c800407031400007200006151000403c203009003c0c841003000c0100f55880943c0c0c04200300002c280d21607400111204a0b103000c03040c0c40b10300c040340d403242d2a0f0000d50001070b44a03045081e01c100b00441d07042211a0b150b07441603103144284510005a9402000024190274203840c0300300000340024485c807a10f603a07c0c4d000070140e0380126031910107900c01004513007805405c6100d43c096403591101040e00c103807200d44001c0241c1c15960714281041408101c071010f04c0602c0e8046c130040c03c0d6121042c010107880c1c6c1400300c215030081d01000c0c0001d03d00354000444c56403038016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99547931 1250 99546681 99546697
    0x30102041401111501240206250327020429060f040315020702040b03060103021509011404060509010f09030507030201080910060f18110a050c0f031303020405060303 73
    0x1040e0071444450045907070103034181841c54284218901d0015440d00315040c28020702400d00018901c241c100319882007080040080010f541c0f0a60900500c114403601e800400075440a0740302072aa183c1300220007600c0b100c880c0308490088003002d07008014a164121940d01c0c0299014007800a15803105c01007500b00b407025041e01b80c03445103643c15602d8044001c0200100d0141d85030b040948039180c61190301e0b50260320708255540011884110b0802d03001d1210500c80480240c50150b03d16008600c0741e481190079640c0c84c280001c0c9220160303010303c0316007107008000d085503501c6544829021701281c2c000c100e6140070035403046140b40c00c07a200f510001c059030f07800b00180012624640c010f440d0a02d024100710214000c0000058009140344941001440b9224100d80404d00e80300b6001c0700000d0b8800c0c90b080c2681015a08405480400125400071206280803995000442402414414180010012404005a0030400200d2074543e0421740c4d00032a030410158649404041c0d030f038030075201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99549181 1250 99547931 99547949
    0xf0510150b030103020607021201060b07020906060a02060402042403050304090e060411010c0305040e130204060603020f18010504051203031918061a0a08010509160503150907091107050c03010204 86
    0x20043c4014180700028240e5184040c0c0750f10000300a60000c1c9c0d00355901600003005882001c100c04055140010400340c000c181070f07440c60325048401e0f20003911101c0c0288041d001d192214141a00c0400b8104158614600a0045c50900e600c0340382064599100b403090081403420280488c1c02c02c00045001c5d07000e07035400b69200344244007407001980d0a4544c0c440c150203110341413100080a10001c242c051080c1030300c04c01c0036110003091041000325000f0741c10503810540706000d0b511000c0555012070340c004040d000c1c268070066007007004a504e03210344d401c201c0c0c01c09900c080754261708a0000295004164040351030210482c8020304408440d9030354600703242c0c04408140b207000324045900800c80c3c0c03100c40100a0008120501280b001039855018000caa07540e5010822100414030a20400301050031089510703520f00000207545104d0031030145500c001c40030104007019820041c0900624a01206214444004030141c541d600100c0c001d90780c5024844071203c0628042c821101a031b20302c00c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99550431 1250 99549181 99549187
    0xb0901051807120e0c1206010605090405180f1c05070c03081c02040b0405010815090402060307030e07090b030609010c0210020c0a050601030605040c120201021002090d0f0510150b 79
    0x501e4041c034041000d018541071007400c0c820015100c1c128012120300101a00040c0351054801050007112900c0703484e1101941c101d28018482140d0103012241e81020898012030661248480184034400c4c84154001520400c9024400c0340408507502d0184134007501f80880140d140c1c0c0c811b5405101d11100101b420071b02c00702c2400001c004c803010b800d00c49090300c0e60090f80809044e404049038410307041440315810206040000b580e01044059010070a000c10540c00410007003c1070041c5000382009225440210005103540d11039402540d041549004880131555612001c900402d04211441d0280c0a19400200901c2c01406603540c0580240e0041941081000c0e100340250098101c58146015184204000c070f241041964060750065000140e1800c0c14917280e9100501d640c005401c03100c2caa010040582e070041a58010310304983d6000d42d0b034900b0100000c0c43c0030b00b000d000403d03040717031520040f090240000fa54050450300036410419451800061401e519503880b420399082d10030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99551681 1250 99550431 99550459
    0x3061509102001060e0633030a0c05070507030201030b22020d2304121b121b051203070311070c0306050c070507051002120415020d090302010c030c050f100509010b090105 75
    0x800511413010490020307818065203440c7e07001008500c0d411a10300010000c0184091002e203803141c00e51013142410301a2a0245c659211a11960309100c0a814143d840368440700607143c502c01301400000309410301c2c0e400003039104460f000f50040c4804101e45860078240003895200d04003003144008109080c1ea4840e03071031741c0c0d95003444d041011020f410881d220001c00601801c3e0808805007500c613540182c148c030307070440008007110f1240c0b18191000c42ca1028244c0031031404a10400c04458110400341c0c0d940e180740c02a409041c601c0d9424440c414001030100074041d1401c069001ea83c4580c0040c0500d4a13203a00c1081180035a000c00352164001d61b0f82003040740303048034610344000400d005035030240c184102d03031000c1c0d5007095210720410b03616904003174600340d814030100000c030070603003401d030500c03421900000d2a1036044007000b0b0a0082e945d1010003401402c01c141510300e18400210f801e48402042c8000c090035096900890640c03d142202525152800145060340c001600920030400c0ca = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99552931 1250 99551681 99551689
    0x702090402010e040c080108150106050304140111070803040201021b06040b03061816120c17100509070f1803020303070807110a0f1502010c0503061509102001060e06 73
    0x342040303043c0034034003412541d281c5403402034146404007170700c880401d0361501c0c03c0d40382401440286130100030540e100500519030488203907500700e0303040040411001031201032280100403070f04d510811010b012a0820410840b80000d500c114400e80c00e403032032045812101c1d0f90200b14940720a41c412800e102c24048124040c02865000d000188881e07441e00d00c50100901e003100039540c428902d610341d0801c5444039000340e22541041a01c603030401a41000990080c0605030103d000384106140c800031410444507102500e003e132200a02d9414941000c980c0a41010740b24841038011600c08180d0403200849101107600b1170340c024000d103240200035039070154a980b2516040790400c44c00742c0f5680d400d4992921a10152040ea10411441c5042001c0c101080701500c45003070841e814024450300701d0381d200e000d40e83c010500340d51000204001880000761801010f10258101045c4001c0001080d80003411031040c0700e0075040001c1165482c4861400e81f4202d0180e91700c00540c0301c000c00e5041c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99554181 1250 99552931 99552949
    0xa080c010c03020a080d0603020319020a03030c080c0d090f0911040302091009090302060609090109020a0303080a06090f02180105040806071b0506040b04020916081b161401050106080402060702 85
    0x486441540d040c981599503500c05c54001c6400d02060943d280b00a001314281044400002d210b0700c6503464981c0710581c0000c00e1b02400b40001001c1208107180e1404004c0d0300c1041d02c51800032981a40d00076804080c0061848955201790072841828110000700546544075100ca20030014280600e85825234090200c102c1014150000402480400003030888040c8105219903102e030b805001c0c5800e095003089078a007409048600340ba454540000c0040e41e541100c5400c0740c4e803500f04405190384201165008006d1584100040c604048008612540a5004102c509039121210341c08280d2139004448901039802401016808900411081c0340a0714a1181d0014104100a81c0c100d00d65201070030820142e03030460321400c404e0706110442c07420420007580403900400031003401031300900040c8500000380c500c2c0f0440b41c5000c1b042c400c070404001120b0f61030b620481091b210b8203d84c80c0001c1d00005145042c0000e510382170000c10780510034041c05025580090010f42440225000c10032810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99555431 1250 99554181 99554183
    0xb1e060d0c0e21060708190507030209060d0501051003050f010b0c1603030314061207030308090a020a0609060305150d03030c09030b0c070b09030301061718100203070e0a080c010c 79
    0x34041881406542e8440201140043e40510b9aa90b0303210032030084c0c50104081c08041c140201e5404004003600c488040e00b14020848001007200d4884a10a800078410351204c0b40c4c00000000d072000d54030900340c014604a89080c2c17403c494000c140f243c1182226403d5a114040c0d0b620a00100406105200509031151706082900e03042d1150358400104110140d204802080d04c440a00c00c005840c901c00035400300b411380383d1021415105000c9a29000c2600004007446401d80c04030348085810481101419400760420241a4481802402c40c1d1140d02c204000a818680010b00348842410710342d26482020300300e10302821096800350007038030b5540683d40401c41110800004602c030100e4413402503040310541e07030391001c403801c4c9040c0640340107007640070f80c1d4000c10040124660044040800d9803110344080d00c01c2d00c600c0e403000c10b07941c0c2c2904842d00310300c215880104240c40f25801580620042d4a8000740d07900a4428881010b145104084440c1c22030350f4089050750182c01840c64032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99556681 1250 99555431 99555437
    0x161103040b070b0a0c030603030e010c0816030305160302130b03060d05071e09060305060a09080d02030109020a03060e040b0115030f0207120807021209041503050a05010b1e060d0c 79
    0xd900d441c0c0c48519a0806007081d00c14070780707181c1400b140c00c40300d00c110202000340d89024010343e421030324080c000481c100c8165040000780280001840925003c0d40d03c0d010050442c82c440c24207074100100901401e030f03000c40070b4003200003801d10468003901c00c94003100700b142030700403070b070b5141c0840c0e66442d80008164941118006150800040d4240f0840015100343d400b04420341c1c501101d00c0400700e02c0780d009005501e01d0080c043c0b01080380040c00e07551000c400d071008074202c045860860000d004080030b0f040c0c4940084008200c4001c5500940740c50002c560f000c20015544000401040c80140c4024159105020050003108030f044650305c0c21101c0c604002c0342075281d070340c0c004040b40c5c4100350546c2d078034030400002c244040e0300c880d01a40000540c401040e0450b1846506083e074419800e81a20481c1d0b602100303c0c03529410809000155041003d981001300c090030098080c040e041d20075071041c406c0000c0d082c905c0c69400400d0301000360180c401400d00031a0a010001080101095028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99557931 1250 99556681 99556687
    0xa080d060e100b09060c010e0a1704030b0114010201091202100f0507080402010e01050c0d0509130c020d05090a09060311040b040204080c040f11041d15010f080604142805161103 78
    0x11b190240500755000701c00200400707646541e07080007401c01901d07050784a1581360821082003c1421405000d05517402c110350b00803020360420050f40108038400d0010003104100d05080c000700d801041c1d1050301002d00109101405801c61000120b4004640c0e60010038820008240503504c100e00105061006040c61458415452241d91400039060002b40000c0c0002806d10221700300038108140700664013800348148a001c802c080c0d120321011100c1820070001240c03a603000da807a6410741008168a4808100050b12402e00b0a00311910086031030065040000a0500d42032600c00c5034115100b550143c01c2c40c03d0207104000250030380001c2144542d440d075100e550224007807070017400140358062509030051a1441c3d02211042d000702218048000602180900c0e600003144d10000b000600c3d1440b00740da03403100006e0083c445480c7e0a220034507241c0411040e42740040c43d1001007a51008822204448141407809850b4119030382d41c041c003c814082e4100a01505e89114182c0d031160541c1c1c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99559181 1250 99557931 99557947
    0xa0b0112150501030e0d0f05070512120a0e0a050304050f03010603080c060702060702060c0a0c031704050d1103160f080408060f0103021e03120a020705030a080d060e100b0906 77
    0x42900d201440030340044801c22020030075503030184103a0303880c043e000002e40303c00000c0d02d0b4007802404a02c00550305101300081c0b0341040150500413030201e00300400e03206403101100c0e210003000e003000310b0b4400d0100745481c0f42428030100020310320a02c41e9000d001149007500740010b0100303803080504160f425640f03540e03021000a9080009d0712005268100800003480c140400900d41a000350280c01550090710500c80321140c0f080445000074403500300452038419a25081710b006440482c07440f9040183c0003480204040480d401c0c24071503060362455000c01036004265100d12a843d046001d1882500c1d5807000103400f029422a41d0307016181c4c2c2401c1a6441d2401801c0400c111030424203600a10014021450504444010341c2c0c0c1c00c1d05c00c07520884045000c2981e4402c415171584d050390020840c80c140d280b00b0410030300600de028007034038200f4100d4680761b0500e4000e0801d00c0d503403a0800d00f000c03030700c0b684003d41f040c4905151402e0780d0f2003501d0280c0b11403017588140d56081c1c01001c20400c903070b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99560431 1250 99559181 99559217
    0x8130c1809060f15050a030308010902030c0904050930160204020405090106120501060905060a0804050c13021201090b060f0f071703060a170d03180606060f02010c02070501080a0b01 80
    0x1a1034007482d0380082070502c890a65000c013800c503a00154890145001d0a00c00709a01c060884d06580c10081c005a4a89608410300c1c1031740070f07030700e03100b51f005040c0410009826408034240109950030f1842c0c0d01c40c08441e8028010107012a0240d0300342003414807202c83e0004045109102180c0080c0c001460b007601d83d0301040c010710f4260081d80200d10421603a400c000c07060b00ca8140104090b00c0c068510034100000200303148100d0681100700030582c40031070240030f41401861441c080052034510707030348502c080d0710002e500504982c41d020604403000103030480550081c030080c92001011545080d4000f1103800032034110b0403203a200804144120000628080e400c041245030040c18243c483c03600b442003013000c40c21500030310314400e10f0781000b01075034000046818202c00300d410302058a031501305041b100d41c010288041d10480c02c1040008450350030181c02c608445082e07000340007040c160798060b80d031007410340300d07080c0007480f820005400561310307030f108156000051402d5096118040450 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99561681 1250 99560431 99560441
    0xf06090804150e0105090a0b09040e1902030601150206010605030403020c1509030f0d050f0903011b05090a060c0c0e130c0303050d15050603010605160b010306090308130c180906 78
    0x20651035407005450020b540d0841c0000b10030b00303001d01c2c03c00e1402440e100410a0004648100ba40300030740400c401e045540c5079000080b411541c7d8040300c45202c46550208085c002802c0700385c3c040c1c01248004179810020050041909100303800401040c3d1900d0707012101d90740b0003401601140200c0d010f9072855a6483c51b02c080310350742e200c00300340c84015800415040101c8207203d090030794032050f00c0303402c0950404182d50901030764041a940300c400c218082409800f0748052001c20343c042013800e06950307030007101900403000e0a8901114a43e1100810396038041c00c8000900303403c403202d81c1006803000010240e54070030081e12038032820000551b1420000d00d6543c101720045480130400210a05c010b200b038448000554648143c4589400d0103e1b10f1440706010f00c40c1013040019134103003180c158009610b085648002d40d4002517940e814841e008003c01801103001030340802c04511185134400240d00c40c507400c60565050103103403183d52030010114040d03504015485000102c0480c0c594410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99562931 1250 99561681 99561689
    0x108130b010605090405070503060d03030b060f03100e091504062a03090308060d020f0d0201020a020904140106090e030904051803070303140610080103170f0a20190f06090804 77
    0x16007520344c0c07400c500304010307104024500803c21800744200280c0b651800c8016004135010f05000400c1c501d51404a81148a0032851030440035000007400544680c103030b650700c120fa401903044403168842d11441078a0790f14500c689000c402a81c80824041445644a5a8481441d607241d0394003062040220b020004046a04408650340d5100542416013242c2d42d2a40a03004443d00d4044940f554002600307840500039850090000c811000c0c11039000b00092414160002c000b0b4040d403074030b4902410103c54900e058900740d424590300150000d120b000760495529000081c50616018106000040500418044640c2c980355049401c0b1a8144001c0920030f01031b42e00401d542d00c001a8507140c41001900300340c00381e000e181000700b0440c0c0c003022480c10340b940145541210101a08a0280ca02652080c13403688040020b030aa60307035400221181d00c440c4c40144007000340d1048030710144c0350b820301c0d412944c2d42d0111100f0500003c090900c50740005100c0d2400003120130168030341080982050f04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99564181 1250 99562931 99562937
    0x4030c031112010b031f0608030403140f01050402060904090302011b091d0403080711070f0608011814060d150e0604020102150c09090c12040803070314090c0108130b0106 75
    0x20092600b040304140d071141c81420000c0c460303000035001090366000c00c543e00e480000e6400c012581c08204e00e070005c0005105010449441d01d07140c4c00c140d81041c6881420b1090361047e6007c1000070034041c01110f125680041065040c1904801800040c0c00301480480031550303503003a01d24500c4004041d012400d00070703035151101c80d41004242c10302400c030304000c102c14017426010000000d900c00080f83e80b00711035150030210941110b00b602d00d0b041c82900301d202d540303580b100c000c1031561707204240724101c0d4010705060860b40c14080645007110804503405008040c000d00048003030603c200e482440506c6a80d24103031004079404140c08449a51003000c241b034020506200941d80d04100303080c410300c04030300300305800d0402d507091420910071072280a001351001c200244e8448441410345100c2c4000390461141031410346802407003540101c9040780803c1c0f0f0140254403640c4003240d000d2240b407000d402440011b20314001500d200030020701d440e44440c84011617400003000207207480c0c02000c480c1c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99565431 1250 99564181 99564203
    0x30b030c0d061d1507030b03071503051005060c070b1c050a020406020c030d02062d0403080714122a0d05010312030218012d0518010e1806040204030c03 67
    0x350f8042c000100b00042c0c165210740100c000c001051402150800c402d8100068015100d20109040450700d51040500c00e9070360f03101e20846a01900140d12560b000301d54084d029848008128060003040300e001e160340d201000c01e20488904400500d2440030000683c1020544000c041007940d80454072401ca098000c40c040111a80400c50b103e22000120060640001410f4000f55103e030010b012040117405150f004105046d0016814810118440740385c802e890141409490214180c45d10f0b00060074044820302c4c09402d6a00380d501000c94442c1099094888240454141001030003800c0c41c80a5180d46141403100318005000314051103401044641c590700b4048140d50010f2000d205140c010001c84542800d0750148084940090800400000d4022a40030718410712203050a02c3e0960b10044544817908000a03240009a001f01c00d01074400c80401165030040b501002a00100d040c006544114001001942c1c0024007801c014282030382d03a11080303081c40196005070740c0040c0e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99566681 1250 99565431 99565451
    0x411150405030a0f11040501180f060b1902070b0f07030e1201020c060a06091506110c0603130c09090309120303090803040c18060806061c0c06050a0801061806030b030c0d06 76
    0x1710701050084001190200031075807603c1d0303100303008030308001e410009203030359084903444250b155104078041d00d1020036450b280c2100307400520380ea0750040c402d20090701c210140000e0410340a01212414540503c46506015496074240c40d030302d1500c402c941e031054041650f40a158002d10180c1030301d40c42d220040c038080c102843c10204880e456003000c0712080c20201c2012050300d010244104549203458030381c40c00d0001501d030780d061001840301158000b000000307010000456848008030346008045608069590f100380a04985602100034041091442d0402c1040c0c0c2b00c6240100e0a030290030301084e03100941d6a10121503100302c40840780065081e805000511036500c0c130200d881c50f138142c00c02c031403410003911070746c0c07000018041e07032184582010081f40c040403480b00d4400d99600c8681d003e0415154040034200f508021a200000b032018000082c45500c00c46800140340103c280142501d070030400100c000e4954506541d0b0036114008013022942c03070710104100e00b1030207103000046411030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99567931 1250 99566681 99566693
    0x606030311010902030d082a04150c020a03030f02070f030605010e061806041a040e0604110108011203080c0708030a0c0906020a17090f03060403050c070504050411150405030a0f 78
    0x40781c0100c500c81c1c0c504410000140c130300081ca42d000031854201007281c0c1e42e80c540d105942d05810031084907080001034000c85281c2d040d0024005440e0b03c014842c513901d0341d07100d0441d41d038240303440003940c840241c07070041001c0381c020740010513841c1d4148155031041d81ca56440d110604441d0340200c0d0320301d580d440100b00c40b65140c0700d041d4008208481070044101e80079040d0990034805040f56101e582d4501030f40c0c20100303c034102d161940001420070320242044091113a11200121029910307180d40d144280c2c1c040d886003181905a80d03100546405800094404030360750440200000031001080100314086418000618412040d00f07102240300d21740c004004140b000c00f0fa001d00e05541c000220603000629883c0794010442103a202240c4800100002580d040c00c441c1d03246405002d800d0a200600d60310030300138000b94031001c00300e415180c4d0380c000307100440b0b038221009000c17411081d0016050b0310300300d100540d8032035040b4141428681ca0341b001a0800c807e202d421210001381070325000070440c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99569181 1250 99567931 99567947
    0x60105070b0406020a0c02120a06050f070503160306051002060f01120b130807020409060902100201110904050402030c0402160b0c070b06060307030b120f0f060601053406060e0612030a1803020d06060303 89
    0x10a03800330040314105050007400c02d000c0500703510000d0b07080c070b10f25480035407295000c4401018002c000b06038080c2e040201075160306003511502030844038840040307410306800140c521740c144c0c08006204607a9078041d8405d40d41c40d00801c00c95105504101c010301598941c05124441401040002110b0400d03104001c02c1201c00c842e40410343e4180102800480f0700103065a42045080c0e902251554641c030029060909210a1a6002d440400d0703a44400420050146d2414031643c014012901e540d1241c2006000d65a402001c640c1510f0001d103250034040041d6410564604000c64520324a6001802c04c000038203446160b6401b0b08011900b08c1010005000c111040b00050310fa41e00f41040001c4c024807805081074210558500d210420f40f131011422030301009a00041500c44900c0d180078405001c0c5842003082c090403e40100e101454282c3c1c4a003140341842c0000d41c90b00c2001c1e001502c0150712041180c030018900300d00000545c072242c40200c101803255000144417411403601500c120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99570431 1250 99569181 99569191
    0x5060312030a09140f030301051002010219050d09060c02061906050907050901050d1103041101030c020705040b03030403060e0f0d020601030c18020d1a01020105060105070b0406020a0c02120a0605 86
    0xa40280000c410540c09801100d030802d40608000c00e40c1012810b00b50921041074042d201c00340306410307040e000d444020024506958040f01d03c00d0042855040c200d00f030307018004102c1c000c1810b8001d03041c0b40034014001840c10225468020840d4040c1d61100e034101d61100003900b015030441c00c104099101c2d65800710321104203d0404004641c2054041596040010710000034480001281c801903070140d0b0980f44514084c0e041840300400c1c00192403548d8000355001c0350030f420741c003c0c40c80702507000307000380c1c403600403907038010070035030340b81108100c040d000b038280d900d826010401001c00402e55600030b481c4900184002031882102c1220902d2130810f1a40f209001c542040340140001400d071410141100e20400c42c0d035000d071042c0041c250087c850300c0d10b11030001c0e11740124034401030a007912000c0909801d8000b048a55070715001910302d4401c80324000c18480c00e00002038001002e650140000d0419483c040091440700c0d408100a0940500080f8055002e4100c20007045254055a6405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99571681 1250 99570431 99570433
    0x201080a0e0a060504050a0b01090b191815052d04090203030a111005011202100f0c02060c0a05060403080a060501030204050105090907030b0916080c03010605070b0a0b0d15050603 79
    0x1140c480c220760b440700d0300a40d005001d42d4603000032400b44001007054601007504100c4800301540d4a14040005010050709603000c0d5440c1030320a0381c100115041c080440d0381080340034032030506094011008000c9141d031088150249640411140c40702040f800c80a80d500181c074000f010140703041031017444000d0704c06115034140741c0f055006031001700940701541498149100302108500440c0d0504200e079a02801e00e5280c41d000144a00e160355521000301e0083c0c41e4842c03001001c010440b1f01d1407031060710b517003ca0b0b04070500c000142030010003072803040e011a085e5402d86005a54150030840c041e18280d0015929000b88401c9006074032330800100001d0a00310b2402e46000d001900d18055040c2003441848110001950302d400ba40000400c190020401c050626084c1c1c00c0d284981003c440034800140e00c000020615580d0f80100d81c185d9003913882d03a03420031201d640c0d00340310b0140c0203011601c2c44d80c890042c401141c03207814200c00b000b407280e854080c03500341d02500b810440d44010152882 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99572931 1250 99571681 99571691
    0x20f1e12090d150902040c05091306230d080408010b120f06190207121d01090315020715020c011406030c010e090a092003011808030a0507031d0a0201080a 68
    0x90380c0d02c0b0000c0b441000d900c400c001207640c503100d480c1002440c414802035009410014034480442e4000010b142040003152204108810008407030b0480c2d4244c0951207c4286095008844a9480a0010f100c41d0700421010850002e039440c0c18141e00940d02050090b0b441c0c401e41c1400b841d116054940811000c0c00a00320000301914141d43e0b0b00003d08000380c132054142000310242c001c1e070110340090340c2054441640c940100402401c0020400d07803521007004510f8440034540c45511030004a0f501b1588041d0700c081e0399081c01d0000c1d40401310443e400c2d0340f41000380720f811103e800903043c00519000001121a2195595602c603040100218400d404c00e10743d01005a82100c4500945103007601c034000c1171382d105d0070104000d06004402030002d1400e0251603502032008002194503c0040c0d000744a4054011540c08203410780d00700040a0300014400500c102000c2d07800164080340b5486c3c00700b50504100e8071005401c000c001450311036040314007040250350b00320700784a030050801841000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99574181 1250 99572931 99572947
    0xb0a061403130c03140a020103060b040303050f0322030807090b031909140102040b030105040c0f0f0302070606031a07080903030709171e03070311010908030610020f1e12 75
    0x140c80e10004260605048030951100c2c140300300350f2500c001650f44902c3d80180030107001e500980d40d40301c0c00d208a0029060400104900f6045015141120f0b07164079a1820000302e05500000364100a002c0324800400c3c84181028034140e00c9044140c90003030316441424180303100700038002d004036006241340700403c2007804a44c2c40040081c00e950890107000050701c8505242896040c49440a00880c0d90b00104002c47c1016043e80154100c40d811102008600d00003041614007050001c14100414414540102c1c1d01d8001c0d0014000c040c0f11713405c006890744e283c0e43d501b841c0040c0c1c203001141d124007040030454983d401c82815034120000320000c5045192018004146110502915a42480071005060025000c10800079860040d014040c03009800544080c0daa810502069000521140d00715542441c18480d40700c0042d0010702c0c071480c6580e82400c0c000904281c0324414110321945003c804c190405010100700c082407402c05d0084411038901007442c2c06003030040507d45000c1085042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99575431 1250 99574181 99574217
    0x905060d11060a0306090e01150f03080304030518130c080a0501210809060c01150f03020d0b0c0c061005010e0a0e070806030f100501030b0705160b0c0c0f010b0a06 72
    0x80764001c03040700c1142d6507030710710101100038060b03c1e801000c0e6142802c500840c6c0300010340000c0e0244101d0510447e2156407180c084d044207900d84005032980c4820000b190110380f0070801018880b886000310202448a000441c4801286440c800400c07542e075201c1c0500654031000070341d002600c070603080c03040d9410411252061020a40c0911041c458841d03e88108400784c0d06544042d18000c0c4855143d16031405000d010f01507410688540000140c00030504400c5e50041d0720503207030091702c81e0174181095941d0742c0321201301402a0000d4502488260825041003103440e201380003007140f142c100d515110014254040341154244542561042402400c01211444d41e00083c541791001031512248082030821202d0300c07441c9414021494401045580e540200d41200c1c401e03986030165030b0b03c0040456050007402c400d03031540c07545180c1102c041010002c0d19604140075444803841c007480070040f9450250306588440150751543c00c2280c5901e0980035080c010119414504c6150030080e44039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99576681 1250 99575431 99575453
    0x90a020307050f010201180b010e0912040b07021f0c06060503011118120a050703050c01030504050309040504080904020d09020f04020304350301080309090117070e1b030c040905060d 80
    0x2406000c0d00c3d80c01c110240c1c0300350400c1c421040180048868190f0b00d0801003605c110034011400c94001403400302c0d81e00c031800a0701c0380700240200051410310f410211100c980c0d034446076060742e200c3d10740c0b071840034124022071250030605140c0e2503144410380240b4004064038280d80c0315902c40e916105d10210460300d8482120048590b0080c1d030b007031101c1e1a80026400940b0298854103900c40c8800030301c1003050000d2400143d0303000b10210b580d9002c009004406417542120b00820300e40050294022a0800d41c2040381c01034814040642808584004034080341c1100280e1000d250711001e4840950504064112407002c00b83c5007585185083d4482c90315040c031070243c104243c40400c40007114030050b40002121080340c1440f51385c0d02d50b0740d0701c03406540380c000766000c03441750010000016401c0d058a8001084150f06006012041d1801d100040c0c410790060070342100c0c04160b801e5407600e40c1850001d6200f1028503a0403a10b80c0e0400c40400c080b070f01d00a14440c0221018480f42012840041d81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99577931 1250 99576681 99576689
    0xa0e030717120d02120702030c0106080a02010c0b07030609020f0901030e03070b06090a060302040207062309060718091b08010e0105130e010e161a1206100504030b13030305090a020307 81
    0x74aa83c078481440000004d2180c0000680d00280482c18464001c2d800300041400f080081d00902a480c0c0300e030380d0740d40c44a01c1403030001c1c04600c0604002c030000b4210f420b0f04d40c2c0039a803404d0000d039003607a484c0c0800599110020328540044c00160154440d80c041c4580384d07003040343e0b8000358100505540c0b00c03401404c001d80444d00c00c22003180082e04400b810b4220001943d4050420340d25610706140c01c030040c145c070442140c0b82529981c070115500b004050014480c0405c540100116180c98034240e5000d000c1e5205007214101d4a05c0110342d001450050039500d204084401082681e02000189520010381006800c4840c440040115650700c0f4840d12303041c81e40c414002000400140e1444c0108041610091180180010f091044075101e41030803c030340c44182c001884050100e40c02400d4440d02c40c1c03090126848801241060a002003142c102c4189410200e181036125101c0e8984103c0403030340b000c3c2039000c1e14003000404d6454042d0356041242c2170000d144100d465400a915034815000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99579181 1250 99577931 99577963
    0x603060e1302042a0c0606080d0c0b060d050304030803011712120c0702040504061415130e03040509040b0106031505010c1104150906080f06010501021b01090b0a0e030717 75
    0xc004001c83c0c0c1c131420b500b050b05000402e42d82100701419006000014846000c1d01d0b080e10b00440002c80030300c041040702c204d0707185596070906200da50b5683c030719442c40940074a420458042c500400107030b0070002000510302a0390441e86075803503d98821040c91048911320641c2e0040d1039440b045880340b0040d9107006141c44078201182d60f03907400943d403a00803044065881420007081c0024410194040c80e01301c841c1680d4003080d0307912280700c54000d03400507000c3c68111240c0501010302040c1540050b541010072000d692038650365000144040c0800d441c00d0307070541c2d41c54004000301e54040c800d40500b501900d01414600340303441c0001e88a0043c032140500040c02c40c1204c00341d9507890740c0c0300c580c084c0e2060984103000385d112502100208003d00840025100e06104800c45500016040e412148142d0003816440442c11101780104a8000614140f010508000c510303942c0d114058240800665034000000a0500c10517160001503440b1801c0725140041d052404540451511002d0000e09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99580431 1250 99579181 99579191
    0x20306010b071a01060c030305070306050d0f020303040504020f130608010f06030f0605040c0f090f150c061503060912030c020c060a020a05070f06090e010f0e0402010e12070603060e130204 83
    0x10a0503484601200182a04443c984001003421504544941d01c640d0180c0e2317041245942d03022050342215454051960701181e400d916100080c0d40205130452140f000e425241443d035182d02041c1a43c200b090001c6103040301007120400707850200c1c1d40000404e006c2c0f40410855150180600c3d0a035814000c0804150302e50f400048024030301e4000000904020780100300e81c04c0c00341001804200b03c2d002c8500064507410f4006030003400c000250082c2d8410023035004914500d617005540898030103800b1220980c031968400d90b180034444101c0000d501400700403030903071514a0034900920300c288000d800d040c40d120407001190350000d4075402081c019a80e40c1ea803508810005c1c0e01d03251501c0e2000b0401d01c21a9004165111395811190031906541c5a10700629107581d51001c4003c0c09005114088814100420042e00c2d80f0403001d4026006060401c82040d03240003144070903501500e40704d40c1d80e1103080100200ea50500c2050020881481e48201c50b040c41c14418900200580000c1d1140b41c460f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99581681 1250 99580431 99580433
    0x22d09040f020a060815010309020a050d050a08030a050106080a020c06010e13060203041a090a110d02060405100816020c30030c06190b01080403111009060b0a060309020306010b07 79
    0x35900c6420309400503d0601d0841c0d81d040001c2400c1d8044880542c15005682d010f41e4550007800350b01c41c01640208420109405d140511605100000d410b81c1c0d0b91161501c4240400e005000560094102190100303a1398100f0710007400001000d02030300703c600c0c0f04102c2019284d001081c12819103222810031991600e820310310801c22040e0716400303040b0a200000340010000000c40400e90305116180840165031480322040e1640308040000d0807040d6130103816001d41c5000484142d110b4801418141081d0b290030100e140c285120415001080c04070003403206152285040882c580541d06c000d008105502e00490350741b00c14100821440000020100d0b01d040e003806050402980c20801c4980b51103141c1c0005540c0e100964001c25469540c000040201669000b0440041c0040e19241850f4440d994119410f410030b29500155001d4034034040341d143d510740245880d841c0500c6001c900d40d100c0104015500d4240d60040c814103162074003040040e280400e1660444000a0030580c4810079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99582931 1250 99581681 99581693
    0xd0804081509010b03061303110a06060602060601021b0f01030e010209180106090e1501050c15010f0501030e070515070c1d1614030117030705150103022d0904 70
    0x1650300480c540380621078405800e41d0901000500c00c00c00c4000912981c4194001d140d10b80c4000e48018100b4440c04010001090203000c015807542500c000300c070711002c02919000120f0303c85800285c0107030050004c0c0034503036034100510446103520710201d800b03510310354001481c41016003030b016045c1902c40c3c840c0c021200081d41030303c1080001401081545410340c004450041c0c0034010039002c55980000401c82c81c045899103489009000c4120030081306010042d80c1c00d03001110034464622500c0201480e10144510450080c030000b45151466801c250003d4150b0300c0c141c02032841c0e035201410800c450743d02c0b522801d9508080c420110382c0e4107140d0406e203260124503000b1003061111100740c038049501c1200340e00e1040d040340510a244c0e1040c080100c48480022000c242002d602344018411110500c11244540e0001c0701203070302c0c2005580c0c40ca420f040034003c0d1b40d85020340b8000100b080d801e10341302e03076510303c40081a0014040300130380c24040703400c0e104060580524401c03c0000c04200c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99584181 1250 99582931 99582937
    0x70e150904020f07140604050d2709021333050706020a05180d02030705060c07180f0e060c030103170c061302010f030911190e07050c010507050f090d08 67
    0x140065648a030303c5540180b8650200c0c10844841c14a080d90f602501c0c0302060643c040c95208000d45004d4900e88001c607406e0015006103403407482c0d9204109001d84100e43c407000100100c40c8054ac589030350206000101d416580304041220201c00007480119825040d0024102480d03050f080c10721050070129418010200c000704450710020300c00300b0207504030f006045158000b086c216100800380d0b0500c01d10b111a484000d41580c42414140414500103001c0c1c100c60400038100c3d01070301c0d603840200e0f10340c80148290380301c02692680c10f04075004550249100b00d9508a00409940c20800c000003000c0c4414400603003040b04d20b0481c019102219030490307109542d000103d90090800704911a012001d207442240802c4004030078140c000d0190041040040d0000c0c00001292135200070300400103a47d614002c014441c1d041d000c521400d42c1111540501c4107030760307000e031030316000f018907421168041c01220070312100740000c0882d00f80880485013842d809030783c2c50700540c0c2107241841c40d44c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99585431 1250 99584181 99584197
    0x90c030a0207080406110d0c020303030711030c07060810090c020d0c021309050606121c0c0204060504050405030a121107150609050c0903071a34030f030e06070e15 72
    0x43e6001400013889544020b1400c4d402001000707a8041001990007650107443e6040007d4042e0828000600c805010300c141b55010942c103802e503460404a40b000d14213000c06a0000404542c03c45e0a00105c44e0403461440080d00e2041010016070b102c0c84d0b406990340030355040240403c11781450308000c640742c101c11000d0346505820144203404162408271f4480c0e00c1152110f0044000c0480120b110000140c480400d0030701d040014100114040d045441c69081581a40c06c45d403140d4000805464074410346100303a000708080c6442d10182c1034010400510441004400b40c09c1c01c00780d840d1000c011007140d1388250300850564882200d415080041e0045502607100c1d5403134902000807080150008094405088040e650b00f81d4940e90900c0e01522114000d00d5840810701c00c440c00c1c540e01c8885004541c1d204008880505031804216a070304543d49401c4000407a0703c03092160581c1c05000c1e10382c1c2c0614010151406151441c00103092203219034900740300c0c0740300900c90f01a40303124804440d904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99586681 1250 99585431 99585443
    0xe07050705010204090e0d0c020604050103020f13060305010611030405010e06300601030b0a1503051003120201020d060e042a08060108280305070b100b0c06180a02090c030a0207 78
    0x89664000940050100c01281482030081145100d5040d108d40e180041482d07006200f07a040034200b000460080d001080d040c0011b850401002102c548041a408000c0490b5074003c02d00d50304084005088a5000b140950150720030b11042c0051380e00240d070541185001c3e210141c450010310054180f8000c003440520040c001c507072448410f00003213000c0c0c40c880c400030788050003038207021014400710b919a48204802440300703464800105100303801590b041070100f514900004e490351106200c0e09130a805101c050b0391300041c04075215105020b41401401e0a60b158101c910381620b40142001541048500091a00c3d010384031030b0801d4481c40c0040c020460071100b0a41c0c445820380ea03541c0c244000650f4003290580e20b1420b40100e5151807019640c5540c0303a5003003c8031070b40c0303c001d11000030308208401c0700052408603030044000c000e1320003003101000070550b900740307561000c030b000b1584054440180c100b2000f150160315081e4003c2e40100070703001c600d6a83d0303403800f0703d150083c02174100007405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99587931 1250 99586681 99586687
    0x13060c06020d05041b0f06021c020114190b10050901140c12030a06080708071a0717070b01080f1504020d020603040507060306050301060f0e060a17071809020a0e070507050102 77
    0x17408030800f424800300507090701a44010380c8800440030900707224410940143d024a01225100394040b080c41200c61003800040381c841494031003031910943c01c55a0940c1848605080c07002c40045000b4866811404d944d13000d1111000c80c030051540c4510024981840640d500e003100612710202100c940783c1001c416102c00d070004440d00052540242d420800075030900c10085240382c0046141001c0b504468014400c0d5844c02d00010301100d12781c1c10a040415082c0401c0c80821004070001c51503051240c0c5459588001d440c00c8412480c068020b02e455038000140541c041c2000191805c43c0c1c0071020b520b01103942c941c40020440010008000c0d00800701005010401000041003001d4034611f4a05020032078441091500300d13a0300d132052001600d10a1401c11098821844254014102030029404143c640c00c030f484299000110038282944140e84c100000c4a01140841480000c600184011900b40d0005001e0041070701072a016080200086074941c0e00410490b403919034080001d6407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99589181 1250 99587931 99587933
    0x15020406020c010e10090512120d0e0d0c02010f05090f0409212a03050915090109080321060d0b09010b01031a01091a09031e0d0513060c06020d0504 65
    0x1403204110451103000c5901e104d2594503e14001d0a16200c42002e65551440b003490034082000b0808034490341001c40c02a503010000c0140d4040040c0440b00b4140404100100d50100b030030f10749444421148100445041c02100507070b400501502a1030711490405c0d1141c0700309000581e2240d0b0340891503841403034071880c441008044075032022503101040060102e150081415103080c84205850340a010303c00001120072000c00726508205800707840c01078205580c070300110300182181c040081d000c00d80882c0035612580e0021180000c2c14221000c1c504000158000d1040d640c1d2401016401511180014540761180010883d860350424a50051801e10350081d45c000c0c01d540d501640040d0030300250581b440798402c041c85c0c40e0003040e5505466030b454112111030141d290700988238103020803c04d61070269002c11a4030304d02e036803591144000d011b0004207030b4038103503006400505101c0180b00c4541c1e0360b410440f10804950803800d0110468140340780c000b0080c415125a404071900d4601400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99590431 1250 99589181 99589183
    0x10801060914150618100c05010e03040f0512010b060714011b020a02040e120f030a0513031b0204021303060b030105090105131b0305060c0a120204030308131502040602 74
    0x260031145400002c0101c91050ba4155100741000c40304401d03544a04410012107041100c020404140d040b407010b60030075400b00000303038105500405c0030000760702c2030b0408040c0301081c821030303040254103030045251900d0500030305840f1225107d070340c4c8512411031349141c0340da03401e42004100d4040201042e0780c070002403800410311054440c2e9040c1c40d6207071030811201030302074508402d106121b80e0000c0c01044240c2d07003040040c04c150304000d110380c000e100c02c0800603451741c0081c10ba100303070180090b5201d152928540d400c60b40e004000245460b450300b02c000109402260181840e07032641101c5e04080122300202e006807085810b0300840b24001e000c00010300c0341a9101c0103035a00210700038045511144610b900340c030070030344601041e07580014020000072462144a43c3d00d13841030013140342180c1d480d2201400e000c400c403034000a2190024403040d0940c2e021030100c0400c42d02c240110305180c1580c600910100300182411070b0f019a0306880ca091200f80001921401c5840d541559039a03107401c402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99591681 1250 99590431 99590441
    0x30406020a06060501020610170f0f0f0f0c1f0905090c040302100305010608060d2103060e18060103110d050a03020705030705010309020f0906060c0a06091520030901060b03010801 79
    0x81d5089443c191000c00c00d58800b054460043c41e0014802c0c0006050850300307002581d40f40d1140c2030274450180c20f10300e03100d028482140c4280007a4050141001400d140c3d0381000310815811410360040341240003a60350f903002e18001c0281c086209103540c0000c000030340d240d4a0f60b0f00300a07400040c64041044405120009209580c0b0030380340e8040c800000385083d000d40d03e081c06003402086030b042c006506801c0070504440c0c0203029401e2050341251000c0352a14031501c44c210000040e031148030070311840300240d18030354100c00c540c0300035102000500412611024103020080c25060300e4002c4515a82d280541484420382000503a18400054500030b90f0340c181c140301d058041c3c00361200001e15980281700d1040c86070b402815060246403c0c204004250400034641076100d03806010100f4031000821184918a02c9028001b4000b800f0b41400321118100358400b509607428043d10600c504070301112003c21a42c4011142c1e00c03034450084082c0981200e0300702844080c4044000151b00c0b4054000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99592931 1250 99591681 99591683
    0x50c01050903071406130201210603110301150303080c0a09081c090611150601020a0c080309090105090408070f02010210020703050301050a120b010b03041e150c020316020d02040e030406020a 84
    0x680001151030084d9241c40d03e02c00c035800b02140380040c8000b005940620102405a000b200c0c5040b01004251781d401c089655030f0704203441c104002480010107060034414501c9504404d4203a0302207620b903a5000740780c072034010a0900340d450302060310442c00340240c40700300c05041200251000802d81c000443c805840b41401800020034a80000460340c0c01905025021088503014151035101c40024200d203da01401950451050100201c08a00540594001740c480400078542d51030207201040917402043c4c1019125902440a0000180301071007181d000b0f96000031210051181170005034140800442600d000b94000a144030405500c50015410f0366812501c400325103860300180b00d00610007040c000c112174400c90044c00580415005550300c588105e0402c40001a1a08000040216071204848030a65006031042a00c02400340d2003c0c60b841c0d100035414128802d413404008000d40b18081d02501d04c13101a1015925a908603c95407807000c070880b60346036503801c802555400c007044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99594181 1250 99592931 99592943
    0x207050705011b0f05070e040f060501090c09030b040201020106030516050301050c0a021e0124091d0c0402090103150e011706010e070302030c07020d0308070e03072103050c0105090307 81
    0x30114096026036000845916a40240d54081c1160364900701541000001a0b500f84101c000c0010304004504001d8496803144410b000d5040b054501542501c00c103030022950381d41400d0304244520703401003800c0200c1e500b0000100c0c40f51220300050f80100f145410107070540c0030b061980321007900008415001c0b1402500200165610429170101c640109072000340103030400c4503001d08444010b2050140e90300884000903414800f01d206a42148604407200038050402804110743e0310240705003881f10115081d102c00c00c42401c1221900c0d10100f4004a129940c0030680b0f101c5a44641d1001050050717101111542a071a2511100181c10034400c1c1e418039440c4e401c0c0c0b50480d05003c28458120b8032120145810741e00d0380107050340690002440c841d002c01043c0946000b5944600d140c0c44054000d803a420b00b60308080341c004000c50881c030055400b83c0d1001a08100011465081c00d580741000303c2c104651040c0b038a000c48061040003a120381079801e2034148800300c0404401051a00c1c400d00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99595431 1250 99594181 99594193
    0x12030615030606070b0601140a030501060f031a1e040203010b19050c0d0f14120a060f050a090209040b030706020105160c0f03140c010c051b070506030703020c030708070501020705 79
    0x1010510321880100c40d0990814000e100c035100180c01c1c08144c982102050600200f4180c0300039050344a500700980b050002074550004010b4035800002e156607000c00c5203001e01200030341307001c1c0b801101064603007140640078842c0e46040642c0c8840081c00b80080051040d075403943d442d00d0600c4542c1281030f9400f04450106c1103681c07030901440480f80c3c1501c0140203090846800d4030145c0701d012070303110301c2c3c000d201c104008062603056007002081074103150000320550741040d41441d01251707042c1d0495041104121403d115aa440e81c13074a5013219050301000d40e4442c041000304001d030208800d580d8161248880c04100c1daa010b400007403041d40c2d0012142c40c03180324100215400307002e0000103481a491821880c002c03e10804007a04481550400d840c5410402c1851900712406c01102400240000c113410389485048c08182d40300c5140c03403004000d031031309141c0016001d11000d0f020350249940001c0c0107448050910549620541202440e41c450402c1e05042e0f020303510a040498041c00f40e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99596681 1250 99595431 99595459
    0x7140102040e0c0304080405090a0f111e0313020409050303070806040605060a080a09140c0a090603030f051606061419140f03010b0301050108030909090607050a0f11120306 76
    0x14800c0e00d007260142c415005654a4401100d80a41c1c00900281d0b100036080001284c0c644540c5a02030150003110000201000301110140484091850a41c00300808208001e4144894003c503a5030f24140d0070001e540340c41d0400403401443c81518001d41150500107905c05002011014611800c5540c030b036500960703030700c0c001c22088075200d0003000c0d440340c0240003811400e4030504103d5400000c0c2e034400958040d990322110184400d14214000c47e42c407264859000342032241c051001442c1d014821310820f810b41da070140c03024200c200c8510802501240e84010640c15441400150b078100d0300411196403294540c0307000780510800c0e1805500411a0a185c1200e00c02c0e1210440e11459420a8042c06c0841000601201c014072150304d592140341407251903070280b282034020b04403880155540e140c46400d001030540000c05001440e00102c040154490700613046071003650302440c18603981040c0d05001c0d210711940c0b0000481e9440b03107070050642800da28000394000d01080310b074078440000d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99597931 1250 99596681 99596683
    0x40e0a02040f030f03030914030c0c01030e06041202120a020114150a0303030f0e06180f0607020715050f1303021203130308070215030a0203070e09070c0b040c17030714 74
    0x518800c84100c0c42c180c203400c0021401910541e1090751007854046441c10b9252100c0c0c200324103c20312214a44c100040c0090005010095851800002c0c01d0a00040602201040c1c8440300100040c145024108402c00030034400d100030040c5034000d40c8c03201e0b207643d00d4031002402828200500001c20385240702080c2d000404203103854407540000c01c00300302c1e00e00390364089006d0003301640a904030f0300c076420a6804001801002d101d00000300c528080000f20b28030341841c2c8810200380d41e0700b58118400f0310101c03030780c0070803141e06468140344c0f0b404500b07100307001c00c4905105910307900d04100c00120b00c2c80c80b014400050803044034003c0302c10082400d11003031a29181e01c101400080313400045802040010740740d40142c00c5442c0002c00201103803800203103401e00d42e80111040100941d002040102407034000c00945a000d0707040c0c444017030a14200d4009050f0700600000646600100d0700041c0c200074005441c070003c0c210400000ca60101c07410401eaa603508040c804903031454595400f03500c0f01d40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99599181 1250 99597931 99597937
    0x10f080103020603150102010f060611060c07170708070807050a051204060909051b1309050a110304020105131e0306110307020c060d0e03120114030705010f0e01090503060c040e0a02 80
    0x20700103120904d1340e15141c0080c1890014076250368155502d80c80d026458807124841c040c0100f1980e1034104900c0200c15030941003070402810a0404d4906002d030f040810300048445012641440d0344a41d1031445060a044501994900800024001451100704880490003540c0079108104950000c8943c0004500a00a90180c140010328416040003100810f400140c1c12805505078851620032021846038164001c0f00440d4003050354180403c941d80c070620823130b9402105034070204803905c400c030080c08242c030016102a04014000c01c1e022010003000812800521491119001c980440d921108000156220507914030385011110275000754030a044034803503503269020301201c5981404000568000702d409269143d0388007175071400d8600800c0105181200c0101e1040e071507140049402e007141043ca20580203130041c1800304410f9070440c1c2003032580340c7c2a01f0603400207140708004950014059104036814440c440501220100b85801441500c03101068080a59030ba4049071040e44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99600431 1250 99599181 99599183
    0xc0c03011407030c050702150a08010b0a140f1603020d0f0503040209010b030405210d0605040b10080c0c010f0207110a030f02090a0b130f1808030406020a020309030303090c010f080103 81
    0x8400500007520382c901c203a01040120b42e450030090708051642d000324050004061680c4410200041d140344104c0e0815442d50041c203442c10441e140040c500344c000c080508100d5801041000800d002c0800c0820200f50f507403a8181c5521084402520300b4000d42d1141c03081d2200001c41e16551049080910480480341f00e960041e141040702d921340580c3c00d402c0d0348000c0003540c090284e001034600844410b60000c281c2018050466150081c3c00501403c0b02c00940c8858400c0c1d00d030031280949030700d0310740308200503001b42d0802203425611511074802c0791190300d040244c01e528101000710040c0c920f502a02da0030b030040c00c8280601c01b00c0c07014043e62004a000150840e0600c2c0c0160005181209403a94400a0749001081c5440f07118041584281c024840504840d01e94661461440d07551280c10806045480d18102a000c6911a074800380b1010f0f002402c00c68000400700c2549000b0800c45408000107000c982d41d9142c0103007c25107608240d280d81d0300080f602c9420950f09485003503074038166 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99601681 1250 99600431 99600461
    0xf0b04030b040503091801050108011205100b0a09020a12050a0b01050706020901020a020a06020c030f03032e0503030703051c0515060304030905060c07031e030c14030f07080c0c0301 80
    0xa040d92501003801e07034000d00485880c4003c000f181e91940390181c2c4803071001100c0c9103000c0f255042500152418105030000481007421a0003034001c2240000c10303071903071000c212001403003540c464042000c2040d42e0304a6400540001003000f034003544000464024121600c02300902d071108051403064442012500340001c1082c401940442e1169004164041c8c05004840d90408254003048804040d075201e2409600040b885007400c1c141840b031448400002009180782d031600d010a420b00100078084210311040c44000384000c0680c0440b00405000c0090480b503d412841c03800400c590f0245807051501d40c540c04400340d442015000301809034924150503907403060800f0034023810b504000c00c15070800c05044000102030321040d009061106030700c0301030b103403050860602440c901603402101070103010000b0064046030340b100943d41019030080070f14800c141020500791542c0505819030060034000183d4008005030b0f64000c04144281805569400d010a0101400c0302d951064140403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99602931 1250 99601681 99601687
    0x9051207050a0b0f0306130902090c19090312050a03150e0402030d0e010801030809040207020a15020c0f0306070c0510050c1b0613080a020a0803090102121602100209040608030c06040c0f0b 83
    0x3900d4801e5101f4a011040c0400041301c0c2c1142d00003076880d03081078480b02030121000402041c2d0200715880c202c43d032300300c40c1805251315180d0381c0e0710700c202f1035030b4407c4600b00900030a1000c0c94a1103600140104e07d50310441c2044980c46003030001c900203060300c00720302c248282071407074440314064024140649016124000a60310b143c456480e203512505406a00a50801c00040103070745d019900340103451004032041600c8000384010b1302d81918401203070300c25051404003031265035000600350361040d2940760880d03041c0e019292144c03503c107446144075401414501000408254180501142294004c481702443c0764441031075100c0300305856800148520134210b0002c140e0580091030902500c2c4100e860400c450f4803058816003003522040402d0f500010380380d0480c461a1612a08050281c911408407070a05001035510a100c0340402201d42d00403c107040b007540d9952040300106100e105417a50380303010000a07501d07035000326400c4030011700200000c141840c1210900054138041561a40303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99604181 1250 99602931 99602941
    0x60f03070e0703020a0c140a151e0b0a0302031912080705070609051006030f0204050f0702060a1503020a0b030f0109060506040302061e1201030b010911160309051207050a0b0f03 78
    0x81c0d48070000445c144a20503000c080090320340011a000b55082030058102ca6401c0d00e0310401c0c1002d00c3e01182105401c20702c21000e600080240700a040d4006400012841100c0740481c0c00b000b0250710295040c0110025405200710b00e00079103444a1180b81c665482058505040d02c50010550342c9400080081c00036000283c120b41c0070781d0045028108660f030706202209130b80b0a981094000302c0d004004950000b0850429000703241c1c000f02c00c00b0340c6010a00c1d000c64020750720b490003014404035640f2484220184502c0e4001000a1074001d03040f20007841e103410030004291320a94000c854030031500300000d1184024403841060300c00080907503180034615000c102d4181c00c80248241000da10039800350211820340000d00d9a0308500000254640c5181042030740442c2c140e02007030006017000008041d80e9070150484001c041248440c010301c10303617414100d80000c007070740009401010b96008c00c070b040c0c0f0b0002904821504102c861500b81a214032459416000daa1900d90240d0014800701d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99605431 1250 99604181 99604187
    0xb03150c070302010e01051006030b0603040816080f030a020a230318010209040f0603120f0c121b0b0105040c0203090604060302031308040b0304030e06070203102403050105060f03070e07 82
    0xd4403400783c8004680d490a2400850844200707440c0300403e24030885040103403035054012201c503140202c40d2642545420340383d1034000d00c20100900102c0417020241001c111107641075031107011400d81c815849142c003402c04c800a51000c20a100815285000c2402d896825944c180c6005814144076045840303100e820302001c0c400d0003080e05955001d0015032089c0e00d4522450941c11045800480d40b0392071400c00d20701d002207a0f00c0030410405400c03200e6a019800c000495402a4031003401d04800a40010440c0d81e10f250350390030020ba00c41ea10f4610300b8099200c0705035050310b40c1202c00b000f0000c007029050340d5034400d141c0d1072508882d0038003080251714004d5025550000b804201004101c0c415501c1158031303405034200782000c1034040140410302d60300503681e2001d1141a500c2901d081503d0300040d66407401200e582c0c5a4036292004160300444c7c01030101580001c00c0715241109403a481c0c824080c0c541144e4280c0100300b8600410354510b0005100400c440c1121070001c1c041e15502011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99606681 1250 99605431 99605437
    0x201020c0f06040801090b010306050c180f010c050a14071403120904090b07050a020c090112060b0a120c050301112d0f0703020313060504050310051f15030b03150c 72
    0x1c99000900b4480041c42100a000710040d052095074524141e41c114545281110000742882128075014001c000000b04074448407c12040216100071030043d103c0012a10420034001c001c119028034180750042040c0070b140280f2303540b11503083c7c90070141c80740c0c1858010302954140700d03412f9000080340d520401d01003004049003000944081410300c140d85411102c40d50641d90100090000a030b1040c5451381880a1441001c04541c00034165240c52401c2d542070851100142c142036841084054a6a840078641d00501c0690b402d000052110700340b40000071030700d2050600a50070076805090301c642410072502c80050f084000d044410024030290700700d90740c00044e07048424042204920350700910000c0d20030340d842a0300071641d90301d003541c00480713520907540284103001c0c051000f40000d603008180381c0324000300501c0002e082c0da1010140c50100c0313504e11612071844060340000c074084260500c440d0742c5080f551028412003540ea81415034604c0d02c86806002c503400c81e40440e100310062001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99607931 1250 99606681 99606709
    0x180402070602040f0303020a03110c010806010f0e100302120c07030503010b03180a080d140f01090e101b081005030a02040b031c080106020c042c0708030703170a090201020c 76
    0x100500340f54882d0380600301681c1c0340d0016805039010304900e80400d0341c0251003140001d10000a41043c4440070f00280c03240c40d0281c200c0c5d05000c0d008203e00d0300184640c559880110008005001c1054481000390081d1301403114950040b10300000114001038140423a2800e0f94145e9410b807950f0f00c1c00140001982004c0c108840144500c0d03803500c0307440e10170050221038a0095500c40c1d95803080702000006c507081030309403040b0760380418100002658108030042c1116100c0310041200e014846400381003803040400c980d4801d1a08110005400a10f15003103d2a15251540c00b070340d0b101c40c0e0401034248500d03c6002c0c0c0c50303805615000c00505054010241c040c80140840f5001ea405200301d003000c11107040c10341c00065854004008081c0c0c104000a4082e4095601b084405c0c2e08052601c540d1040b9100c0384c400c44c60f41d1384925003442040109000820f680c4084d070f42c5a003400d1800520881c9001003c01c05c5141d6400480e040c3c404521502e600a81d058009001001601040c00701c0c0400e0400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99609181 1250 99607931 99607943
    0xf02070305060c04050a05030604051f060506120103060b0603040c0312030603020409050a020405070c02030a11010c02090a02090301060501030605060d050c1b011b05030f01031403040306060e1602010218040207 92
    0x4001000031000c0200724050302016400c1c40c4c582d41844c003401341ca8035441c3d0140f882980300fa418040850000709105015524980382448010301d1a0605070103000c00345e2215801034000660305281c40f100316006ca040e644a28814400080b1039410000c017400152009800c1607810141080040c2c8e883d541c501d40c10140c0e09010504031b80d41d0f00003400f111381c1c0300804e5956400000425045103400d116161f8446560700700420306085c0b94012959a039402c00c0000d14011206040c041c00c3c1e8055107014042e00c0e40148010300350301c2c0c00c07004070020750131030b1503954003a600380080468198009d01400341030ba1006401c0c1c904041c80c0141c01406084c0c044c4c41e94140700783c2046514004051018141500c241030000031500c1d112648040e810745210804240400c0400e2040c48000180b092910381100e402c400345261002460400c2d606502c51980300500452404c03100180480c40d0050582c85070512000380d012140f40c01605a00740e104028035070035003088000b61608646440d0b40074118050040ca = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99610431 1250 99609181 99609193
    0x60a03020c011b020f0f16090509010209060703020a061103010e2403011d070f0e0c03041424070801030302031c0b040903051324030207031106010303050406030f06080d0f02 76
    0x1a5490301c8212501c43e103000141c00c010b001c5254400100300c0b85e02c2c5170700c900c00140b1034000704001920501c10784e400b0381206c0c4c980342e10105c2c00c2070b403094054481001c4001c20702070303335000245000f0b90341e0301c402d100442e41e0a04200070b101c0c0c3e07441200140c0303040303c005001d040f01d11399038080004200007210031400a02e2240500400c80d0303032403d1044880c0c0705240d41d0010032403003a01e0720702480c011299015000c10356001c0c40500c400392500d603425400c144020f01d80c0ea12900d4920303241803c100000a110464070075441e076405100300b403001900303030013803514085581a1070310728007240d4290b401d000c0900981e00c104a0f050b40e9151004a0b0103100300e8446000441013020000501555415481500001c03c08a81c80340e54003e00c03130040c0000c10715000849052a140107400441d040304240d20018940d02107010001e240c06007501b2411410300c0026070304550303161b01d000703851a001400b5074000a45000754a41051b803043c0704040070b07905071030020701028030710b004110341039510303002c528085000c0e039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99611681 1250 99610431 99610451
    0xa110f07030b0a0b0a0503033907140102191101050702040e25060f080a02040302040212040b090102070302060417040e0106030203040203150103020120160801050405011a060a03020c01 81
    0xd00011010310710440c142c6415061031000c100c02c2d600200d00c09071050400c4407040103d41d07400012144103124403600b01444681c85030082c030b078080580e40403150b130b07003061220810402030104d03642e4203076400300691402c1400300100490391040c100020b40400400480e00b60003040c00826545548541450b1561401c0d1042d4045802e450362101c0030300507948028021540130166488091030382c1c41750043c503d0803900c1c10400a01e541c0e89100f5000501c4903400100e44500180e030112005560060001e5580f2000503010303c44109040700d050381d5405441d0f0218070449818000c89110781d405078000c15480c1c40702e840b050900280c9089001e444402008006010751041c15282d0003040a62401030300d070710703050040c13500b0158405288607041c1411401880140e801114003008014562020804014151080b80c039001408484221081e041c44001402e070205402041c8120b1151001b1b000c00d618030003c80c014a204015180d41c0038206000c2c045c0858460303406000301a00c03100000c11100d40e2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99612931 1250 99611681 99611683
    0x50306040f060b12040b0106050306100305130602070b0604060f14040b1315140105070308070c060b03060c070201090504050f01060804030e15040312092108040f0f0f0b0307050a110f 80
    0x24400354500c0e804c2c10200700038030180c118038600506c0c5131b0500500e1450200006070340551600564014075540b64080b5038080d09005044004aa102c4001c6681d80c400381003104c00d401040703c0c000d21550a00d40c0200b6103164015000e01222100b54045401050700c00c2000040c104100d65070f6003040380040c0d421844421800b80d548903c0c401d8904d00c091904010809141415224110b030601004101c0ca0b00081d0740104c0d03942c0d112003286404500395082d8070f030071000350150780d0b2813980c1361117480c06005190f00d410006100e268400d0329507080c0141d8403014801a148101d5240000a001038010000c80d802994041e0f4050701c240b510030120411140090448008400c40380803088020505000b00b1141c44081c0c2035000d01418929000e030301d84400082c0580b02c3c0007241405c803401c41c5031402042a542d0582c0d0151480019003440c0d0f80d115a100e41c24107225210f0158004e402c4040011541220000c990088401d0b540e124030b0012a07030070540c0c0c09821103202e12003900c20211202078201c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99614181 1250 99612931 99612937
    0xd02040f0902012a030e0d050105040503030601230708070c0803120f070302070b01140301022703010c1d1c080703030c02010509010b0303191106040305131203050306040f060b 77
    0x100302100103246580d0b03000040a0850101101d0102e5501ca01e96040043c2800340034980b055151900340c886002c02d0340803640540c2d100c0c500034010340c00c1c00d0520040100c08400703581700301d900ba40e48004c6060303088940008080d070741d00ba00c240d01c0010804038000c9030707140c402030001e00e0054140c52010b03507556200e90302e15480384042c101c2c0a560388040c400c0448800c004184c00c00300c203107000d50800c001502d401429400610882c52260a4401d44a003161829010344000e0308000300c52001c0415504403130344c0240011000035102c5c0d440c24000a030118007842a05403461040d1066406041d00d080501c0904900303640c0020103110103004040001d45018001e1000a1007a680802c1c661107a09000e42903e070041c18111541e41050716205c00341d01d00100b80c1d003101c40240800a0041b038020000d13248030b0070240d4038402c6406400c0400c002c1c907070080700802d03041c1003e401d00915140d80341e2040050000700c10004000950803c089070b828075068000f004495084a4002042681e9041e1900b1940c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99615431 1250 99614181 99614201
    0xc0705030a0e0114071505090c03032205010201270201030b041113051e09150909060414010218060c010b1905040e030304050d050a0c0c0e04061d07140d0204 69
    0x42c000c6036188810350f0301214640004030a01c902c9400d01e25680e4407000c5450b07001a030010450354440010703401e100200001e0180d4000602680c2c0c0e640340c6105080420341100303400a0020030f50f03c0f80002c107544144980c03483e00c142e00d5900c139032142003021a10011018000103074105505d0300c40c060f4443d6254810400c11004041000d55540c8a070030b180f01141d0101e900075446442d214a00101100c0d1211407260858422100a0b16a540780c10000f190509030005045e08650361008018030408002401030045001e0b141c060000d850516200742030380706074501d201950704030381c50610450401c48081c00d4003900002c008a0300b005a1408144114408030a80c0c22000c2441000c00580c102441801d9441110401440c03035407619480d0303280d50394000b090000801600040c000c09861140b5410a40140c0c00040300d1800d9556142112448030300303030340680702d182c0f42296100d00d039000310079807850140c2210054000540342c080e124000d560701c1480d1030b070007040307590140f40180e50703034030464840b8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99616681 1250 99615431 99615437
    0x5120c09100f030f090c06030216050304120219140609060705010e010203150103051506090d0501020a020102070b0711060708090f061f0b030f010302040902010c1202011b02070614030c0705030a 85
    0x2c5420640001c054660410801d030510703160210b4803021814007001181590301a08016035540a544403c1c1c00c04008004c0c050aa800042004a100346251000c114081d00840350380038200e00c00c40d04004141894440c125291150b81001036890404101500d8510340040c0605d0a11586895140c25a018412404e980b82d5000041000700301d8800303000001294280303030800c2039241c6000c0851940d141408240c0c822740c408074008199503500840e050826611900947d143c1c180010003901071340009504903007880d200c2001516862050903050100b88150b00140895140c42c40e00f44c4000c980035205005e24002c481c198212003e0401c8154000d40c04039500b12008420074040d20a03046480d00190200306040040c0302d2a11806074840741074a40481d400940c132000341c801a10070f400210340080c480102c0702e001c3c40c14650198410600c100b15201b14105020300340504070307141d00c0b1500401c00890340b800382030b40240c42c0b03500185612411690105142003840c0d11000e145800c042188000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99617931 1250 99616681 99616697
    0x10090b0403020915031c0219030e0f060f040303020304030303050604110d0e031308060906010f050d031116120510020306010507030305090a0804030b011e06091413021602010305010b090105120c0910 87
    0x20f00f40e410400804230f8503000c0c00340c400d003044980d80109040e1225a5640c41040109540d04003a501c1008903250b8071f2041030b01c00d03652680c902d4040d440c0e4100d444141e0101c0e24210000350142014014500401059804107280261f1044a00001c00c07400d0200750551105110554043d40f0390181d2101408c001b030010422032408981c2c66203007040503003080083c89840c0604011503100c45404062065040c104600e50340e0300e001e0468039141c03104010540e03242882a002444411581000301c1c024011010f0b1a0551742d220300c1c480030303480151800c60008108128201c0070902c00d0340000c2d0071a81d1300050340ca0320040e644035000e241d0080e0f0000e6a5a07040702004102000c006c0142d60b00d015102103103d9400f030700e4104e0180c00411140300f1100224400b107540c1d2081d94404410a80040c05800115190080c118940f0801c0c034010760100d0100c0c1c50000081a01e880b0b0380b050f68070b10007050f9621440c0510b12500c0d0500c901d806020412030045c148401e92960340c80303400041041c0e2240c0d4407900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99619181 1250 99617931 99617983
    0xf0902041811030d020a080c03120a06050f0103050907060e040603080301090b12010c020d03020315040509010e0c0102060415020a020a050a03030203040b01150c03030203150303040b0910090b040302091503 90
    0x880c0c6840a140715210780d112621900ea105c2e00410884942c5800203000ca803200c1c21003407202e003584120244520718081c0d600801280c01c0140d480710083d1442078518560340d0919500641c1100c20550b000d001075805040c0c100320fa20300c03e002c00d0882001c0644049903165076940c4400381c580080c0c20450074107417140c1c0011040c0c24600d11000060a0003402808612142500030b5116070640d90603c003059000400220580c0b00010752800854010300100f06515148001500a0414030040d10b014000c00b0040080d13988006138050156400c400004c11485201c4442802503000604140560154401e0710f03010a00601c01c101405020307440141c0d07240b505150868201c00b05810421562901a50280c8241c0e0b100c00030f5040365506050040e50b030303190343c0401310000c01000000d642c140700000e4081200f0700d5a070042e0044503019510060085440f220680f5104528015242d000000717100400141c5011304140740c0024114005100f40a44440424104240b00d4000c4c0e060001d800c8400c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99620431 1250 99619181 99619193
    0xc0c090b090c1c0203040c050d050d18050901051009030b0106080103050c0901080d08060f0d060915090201021902010c08160b0109050601090603110c06070801080c030102040b0702040f09020418 85
    0x50740a1540068249410500f0003c050801c0c01083d03068101a8003200250802000000400181c40024282e03412030006280040e505c50000404200042100c1170707524029007480d030704000b600e0b0018110230b19682403030240001070103818030000810a80400000c0400d00901d00c4038041c10f40c075520103141e07604605009240c403440841242c000c5903100010000c0e80341c04140c848044096141c1501191103060014420107007944041f076101d20000070b160201b040661007448903511400380484030141c90554681194640d400180c0941c00c050601e0404107180340c441e100c4a0310504004454400503141c0748215008a400c050f0020050603140050025880c1c065004020600d024406880d284000030249549442403205241c1c6800c90115900c658605a0305000c03100012240c0b10310f00385000410041081c0310301d52007400740302000c001606060003158159610220301c02d20301412542400300502441c1481d400c0d855580d8990300041c0d6441c000e10401260449410792144c01c141003035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99621681 1250 99620431 99620449
    0x1905040611030f04121401060b0903010b04090c0303111f0b0319020a0b0903030403170304031107050603070f03020903010c1101060b070b010b0717040906170f0c100c0c090b 76
    0x5407055a1042c8031801d00020340200f02c4054440481d1000c41c18546032070140c0b002900f21006407010b500f01100482c101102c40e0140400f440110000d101d140ca07000d080c00100c0d100c0344805001e5009408080c00440d003d40303107040e450444003040380c0100340111050031200e00c1220706501d20f070307403035440303038101480d08000d85205880e080342825035000c00c2d640010010b0a8910074071707070398079800b080380e0305581d5003881070f20000e503080b41101d1603840c4071403212003169004960807008240c03600d48a4090203000111841a00d4000e42b4143c40d640f65110b041e00c03030070610300c046020150200030340d10b41c6407000c0c0103c072400501920740066118046580a00355207007a00611a240303000c4c80900701142100b1125411103c005048a960356058200003d0000720300241c41005440000c00044d05d2000364011412a0707022100e10308160120b00e056034449041c0408046d46601c1540c00311480d10784513014600c0c41c1d0036410a415003a40c166240080200c0e030703a100c0110143d0720417002042c2d04002250f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99622931 1250 99621681 99621707
    0x90c03020411120103030f0201090507090e120c0a0b0a181505060f0f040e070b03010f030614070c03080702030415050d0c0e01091404090b0c0a12060f060c050319050406 74
    0x81414400f21000d420f010350350500c405401c110041c121002c0d0030b0700030340c040c015554000742035410040e20b032040140076251001140340d8a1044420ba81c40d403c01d0801628044100b94014050b040f030310303440e030f030f201c480010b001c10061654940200109080494892482074860a41ca1103404000440c0004684008003154000c24102520000c243d541010140c1ca840781260009110000805010f1800301d071500520007881e000000807462a80d88500c50f011070748140c00502424000c20302d504c0101c1010f603584001b01d201e00c602c9000090043e40003540c4011584100d0f41030940c0ca42151007043c2040c1c0303100c0007144000884034100c000320300805421039400e04015041c01e0111000800b03103d810301c18a402d002140428020300d55907900012a0f00790080c0d44038005003000c0c42e2051440c0c1c80f4400d54004684400700081c01c41940d40603500440d014045103014a074a02001a540109500021a554002000100104190f03071481b541c03640c0c0f41c2d507945601c4500b4260080c1c961044070031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99624181 1250 99622931 99622961
    0x702060a15060c0803090c0d0f110d0c0b090d1205070507050a0509190b03010903050d0506010905030606100e030a0f0b010605120604020a050c1002030709090e100e030d090c030204 79
    0x7810310149030041c95080c01564411820342e6603980d01c402490610482c2824558854107032034100c818460f0907400800981c3c02030030001d00b107034000420020044140070000b4032081d2084410000e8000320005800c200e0000b42402161003860355a0303121101c11201c90101240c070110761a400d01c070f0100031400c00b908c03081d1445003925040c40000381c98104010910404c501e6000c9a03070044200c95000342d540031074090001d02c003503820f0f072a01418503004025a00d02c168034020000d5115803064034240101c80d00640909281d4840e40c041c01000c2d82240145010b1201f81c01e48004e403610200300c214503150041d8041844844e141c42c25450f484c00c1079108204000c41407001c0b043c552000d60503203410240480e401a52011003000a55403400765002041e4107000b01880d1504240094005500c20b4106a9800d00b034140c840704101c08480f0004284103299004900c103003901301d072550106078840070f20300071a03040404851098094501417801241c2e080027103081001142401d001b8a200702d00300c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99625431 1250 99624181 99624221
    0xa0f0803190612060203220303020d0c08100303050a021f0b04050906090322050402030901050105030c0312030f07050705030301060302040302010f080f06010f0513140310020910080406020d050702060a 88
    0x5071072142015a01405013400d640040410b21006040140240f0a10b82e4a5a07294004035810060000d412400c81800b8890401d10444406031041208500c62081c9120b401c0d02142503440c00c642c280c05c0b00011380e065100d04200a046461410240d203450141040d01060a40c10f41060200342c42003d000403030241e12600a002c0d5131000482070b80c004840410769000c0c3c000400110b02c0810b0103a81c812500180b0000511003070a4041d044581030b00c1c03090341107504000880c0149035a0b81c1c0c24120365455141c0500c0030074041841d0308803068000006c2c2c5480e9060040a450b19402c3d07074030aa01c0350b400309030300107410421543c2200f107004a10140381040361302460264021005a40010441c50400c52120201c600d00c170f00450640f082030030202c400d62500d54445000b03044403958a0200b520910a8001d59881c4c00c290b40211740310b100001d48414108042610140c505080c058402c0f100300d60240882081e00c5000c2c854144281c140c2c2c3c0c01011641401c540d6002240e81825864003403003490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99626681 1250 99625431 99625439
    0x60f0603020304210201020433050405031e12040602100c2a051606111507020d0c030c0503030f04060b19050f03010f0504030f09080705130209030a0f08031906 70
    0x490904c1d411150744060144050301c41aa0032070083c80303507070454809151020450405d04820291004030080000350191420f042e20105131a640500d226295040d48138200c0080000c040901510890b0030002c103d03103107400c640500540903003054001c000140d00c861f02c3c0b007010004501868114003ea41404425103040800c008402240340780441a4010b000b005507040100c1003100d2803003428806040352500f51154001011450203018200c410710400da80c98201040c0d554080d4007988098005103541c4950301e0701507505452500d410307011303c80043d1605005c9407040c80190f105401c0b811780d1000034036203490441d0031107460500d003d0061007141826199000031101000641342d089406462444403000000e016140e013900042100342024144020103802009203c03000c1c1c2141c072900c010680b20b10300e450f611922403140c036074010030801d481445040280d0090008801c09815202888541d494002010200d950100c846590010030001800560000c40b0390711803402500384034003450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99627931 1250 99626681 99626693
    0x81c0b03060a2009060720190501020f06060913170403050c090a0e0a06021b0304080f0f0a05060105130615020f0c040905030d050901180b06010915020a170418060f0603020304 77
    0x307410002002c224440703400d21f4800c1c2c0c1c8a402240d8080c03004000c03440100601c1c82c20b18400280e03100e50781c05403060852001c0c4c0a803020400521405000d8040b03045540c42c81516145504c07810000d503000710031070700311240e88446a0f00070400780d8003540040c50008540010702101010042c40003181914285036000165000701d0442e20306030b0080c030050303221a070000030000c6d010780e1070b69401c840d07100c00640002c0c0700c00b020400d01c00035491401a2480c3d20240f05206031034140c8000010b03c00d410150062000d4600f07802116a03160030428002026038540d00341049502d070741c841c000c015a00c06034048401c01c8003080300b44c03c8003130142d07003c0c001081581c0d9083d0341c9004002c8048512611840001c01c802805d500c11b0f2101150300381c121072150110b00300b240b03a0100a4400c54001035030703454003107400b001480c61100001171303c1c7c2c0100103202840d190001c0c2190030901002569000304400a10000055003050038040c0c09500003411618200c4107855401d40c5a2004003454010f00800000c075030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99629181 1250 99627931 99627937
    0x501020a030e01050c030d09050709020f0f0d02090604080a020a05030d0509330706050f0c0703030b0d02040e07091b0e10110105010603051e04081c0b03060a200906 72
    0x29050078022880e411101c01138450307000750490881248404144c40d02828099005007602c64010380950711038540741c100c1d080591041c520804640c010800840028811200040410b078017035003030050811011b180002c3c5a07600584c00101c1551100382c43c038042d45000c010400003081c00320300811040314681001b801e28003464010500c039200010001b0041c0d450200d0a0301c01c0003101c21140044440c512282c01d0070b8019580030f4400c0b515020000f4002021004120b0141d036000e0682d07802d020156500700d0282500c015203a03007240c0e00004440060700c81d0300030b0010b80e01ca5000a8111141400c010740201d03100b000c1c0706c0300c444100080146015070014101000308034151030300038407107400380c005545d400140c0c80038040d036628050000504982c55403205016450080302c00c00ca0700905040549680f0090307070301170590361003080082c110019401c20b80381040c510300d2000c86c940c2d0441000070f0900c00204c94590742244c84880050010003103469103502070590800150500078031401240c4180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99630431 1250 99629181 99629183
    0x10507020d0309080409050f0106021b090a0c1b080301060e06030f040326070302090406091b082211010206060d05101109031c02060601050a140703090e0f0405060c040501020a 77
    0x543c1c4061030410b001d51039003103c02030203c214051042d404c10001140c5101c030248120b40041c0140765070a4a013482541081c8041d0f2030080442c2c503e0340f00c01100038010b044444030700c01448a1005006a500d9164181c446560b0007100c070f107901c2e580740c8240075080c40340d0340d50307028418a810010000b8510101c101560425094581161024445c08815048602d0543c2501800704103000b008061a41600102051142510140715250303441c48100140c4a45040d0207048a4400498216a51054410b268044200e4880016a024900482d40100d04801c03055030648060000701d4140d580420140343c00c6a1305942d5110003004686a440d12202400e144070003031034480200315010300c4900c1c01e9034110040102071b030391006200200d840381100c2090b40301c0d026010701c20000e155980104155495400c4d56295480440d40740c1741c9040032548150740440a01a0050000c514030910258031440380c4a8642480181d0030282800c1e403504c6001442f0410218081100b44001d90340890014400d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99631681 1250 99630431 99630437
    0x504290102010905060109091104020f0a0c0c170105011706160809150903220825090203010308180d03051603020c2d030105091c050403080301090f050603010507020d 73
    0x641100004034050541890301400c544207500012590843c55881000d4403407288664003c10340301c40707042c0002c0c0d005e00c40d80300340810801d0005041450091488005d524401c0c80c802109a0310740d14550400e9042000e5090169900da0062041042281425180074600d030010907013132606610492400288a41a408002a01002c612002c00400807101d840549107405a04d510b42240044d640c3c0e0817102141f2801c0014000105135450b540402000f1740320820094603091401c1d0309407445861004100d440c801d040a1000180c241d668400303103000e144140c104603501e140d80040c4810301344042d0b10a9114944d00b01c10702000a030080115094003c600e80810002021820260304294030040403641042c100c209010192101e17040100a10079240d4840000480031004e141c00c80e03d00b21740711213040d0300003110080500c0f100d81070b211050406240440c501034595035074100781c4d0001c1e8826071402d40c5429040c1c0d04000030740246584000c041c0c000b0803c1b46043d0400030f60310030704290b281e414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99632931 1250 99631681 99631751
    0x712030c03090e0c03042003061b0c011401050102120405060901030504050f1f06060c050303060d0c080d050d24030204230f0609070912170403050109050a0506010504 73
    0x4041c0544030050042c10f1040c0c50403942d250070183c4203810b5104032811a04110b840c0540010f0504c00e03801d4950180c8041d0080140d81d480c2040e942c0010a03600342c007596211300780050540100c0074021785c82882c036502030443c01545003800280c585003000205c00950641400103000360b45540c0b054a0003507d00740781c0450035407160705246060500d500c030141300700c0c0115015000022881c140c0c4604814584604016180c5d60341411140c80d000014000c200360030802c0801c440c4e00e850109040094060210008140e0f592005940703810a050b0701000860303001f240c002c2c8908000d01c09e5804110703003190b08611944215283c18039101c0c0900001707104030f5071010001050b60010714080072030501520340d00040c1c01d0900e074101071141b00302c5840384200250400a4007030391151025404846202180f00c15a85560b074542410214418840500c1c010510000002c41c00074000c000b81180102c001d0102550303603007030660034440c05030003050003a070812002c00c000524001c07060544408030011250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99634181 1250 99632931 99632933
    0x3080f07140102130f090209060904020d06081c080a0c0503071224081b0d08090d080f0c1b01090b070f080304210e010c110f0307060306090506030712030c 68
    0x1070411012030006540c404a00031a882850b07405103020364900c049070300b036103943e90400c1030160b1003030124498002c8000d1120901e207003003d030042c01e80b00e00460720120f400c0d529064441e103402e9540406100368100da48500b4845034000605581000c1030000c1030210300d030030303010280841c40040c2201c0e0400100c6048a41c0181c2164010a0040754003910b08180f1048091820584078190048a0450007558100314501c4003220707528040e808040c020927240c1c0c5c00d0b0740b10005660022244176804c196041d295000182e801c400424a410011020a031100d51500b010f074a81511440c010802d0300b48140c0005c002c2c1c1e000b151a0b13080703401d40740c165582c40203079251090481040b1a0020480400841800304004078048120907c03690000c40c0741940c00c00c0901280d060301040f0540740402e0300c2e0031200010844400160301404405081651640b51440c00301c4d00e4040035920140c00a03039114000d00c030503d040d006980d00110100d0040900c0c604042e001ca1048641610003010b00c42c458504030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99635431 1250 99634181 99634193
    0xa0c05120a0803090a14010e070522060b1206040b01050d0c0504090c0504060f0203121302030a0b0a15140307090b0d0609050705040c1112160b010f0e09030403080f07 73
    0x1010785600851098403800c2000d8919030301c00c101c80c0200c41806e1010b540c0390001c80d0503c158015961074100410549107004d050000c8400028284901201007042050b80c10515004500040100151195035140b500d180d1010717000003d440300744101d0030a4440402a83d004081e5204041010380000c1c0440340d20b501540c1a100340c0c0c3c02013038000d040c1208020003036003100c00343c000c81c0c0007600d40c2d01c400c2c00d07922400c903100c0c0306118220403074180c04000315001d03142003490306688138400b408440d41d00d1040e0f00c400c0480d03103080b04c6036a109603c0340044480c6031508454030005100c01010410100c141400007a2552b070b55011b0380c0c11403565401001495562060130300b01d501c1d0404401c111030141401c1564492500d4018039000d1070500304079406c010311843c804229407400c500540040002d02600c203805d54801040c146480c001450b58070301107801e41d0001802404480c230080401c07840c00e540d044240381c006004c02199041480104089030211044444410107400400e5441d0900e01c1c001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99636681 1250 99635431 99635443
    0x4021312080405040608030c1209040b1804050c0d02010e060c1608251206050a020f0409020405090a020c15190e010209040509010e1906021216080601020a0c0512 71
    0x29042160081600303100c541d50081c001e444050341c003881100d4403030b0403441e524800c452240f01d00317070f2050b9407511040141c040501b104040091000c5044401d100000c0c2c82842d0394001000d6401969042c4401c02c1010845a8250b40c01650035814a20721a000648a6018081e20348c1c002d86001072080403120083c015485210451101301503400d440c0d0030020b5440750007114500070124400420207000c0c29100054080703841000e41c2105001251f40c1d04070180c4000340101010640170311030600110341e10405480648800c200058841c2d00d8002004500c013400b80040a1f564410072510f40100744c007280d420480302003051002e0054403080f80194540240c000c21002481c500b03d1040b5070708d0010340080688010480b8144a00d443c0d0718441c80c03c03201d800001c00040e6002c039000040c0d05880407014040075000740030050038000c080818402c070440480311a00c040490304190030440d0b8011030322039000351003807000704103210f1555641d14018601d8060b0703030310030424942d204034200001c10078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99637931 1250 99636681 99636689
    0x30c012a1a040606050f0603131b08030d140103020a0b0705030403020301020f0a02010b0f01020d03110405030d03140f0f0a020906090a030c0f080303190b061b060f01050d0c0302040213 81
    0xd6540100580392500d214100c1901c044500c3e0381000400182c620701101011110745005141b545075444203145100c10b0b92050a045540720881d141c40003c0c100000c0c41700e001001e40402850b03907803803000415801c071070350300c91586ca09030400320040c00540c0b50209200117590403090000c0c1d4801443c2416481c41c00303030741d100035403540c0001403140c00001c10b28054042c010f090780007406840c0022003040011640da200325070060344480c5041004600c0f903040384007030080c03100485182c10b8681e0007013030030054038070078420200e0307150000f0328007998809007182e0303114100429490842c18420b84c4450321080c0a40240301d100d0300414100d26a40d103200840e00c807544000c1441d5a03203a0340385002020030380a440b405e0090244c0343d44c0020301030b4000c4100e910541c2c41d050b0f26040e04800c01100001800d0b12103000b42c01072030a000c01020b188010b08880001c03800e040041ca060701d4080244030303440d20140c01181c040d00030406c00100103013040c2050010f9030b40c1103502580350415000c000700030f001c01da40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99639181 1250 99637931 99637943
    0x611030706051f05030d020c060915040f0e010e0103050d050703120f1406060a09030230010f0f0216030807120903080f060d050601030b070c08030a020307020c030c012a 74
    0x800d0201810703003c0c1c50944074818a5481c2090250f40c0e01c101a00d4900344a410310240e00321269000c418a40080140031040006180c000c185040080052503070b0041d81000c000124104810312105203503103045401000c0280814550790304540d40c09880e648814050801d210021568404043c0540c0020b000b210a039801080340441c1c0001c1d00024005080c07546150400100101c0d04c50700b002c0d011a370348441c12740c0f1346071003030362856007808103541100600f2642d205c0040a030302500c42d80b246501500306560f9001141009a000851045404001400104910401c010259181a1030700303500d1140e09401c11800d00da5541500740c480c04401e5450460307079860174050804051b0401d11160084d038078099652401c6d078554040c0001071024a80141582d4080c0c0010000144c0401b455507000c202c9162032400900c0c99680d001903900103403200030042c1d401104004000e6030410101c0b420390300803401812929484c20028000642c07458004806036101c28460854042020071000c860364800b13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 99640287 1106 99639181 99639191
    0x110c0105090d050c041b030e0304051f020f01060618050901080c06030a020c070323070608070e0d0f0501060e0115021507020f15010501021e06010611030706 69
    0x40300c1110303d0312403d0b10420f095204c1e030089064880c064605d000080481e42c0c80a03051302d104460764103a40e84140820001a035440c980e0054119002c01c0690700c46204460407400d0811981c0311501c1d80d0b0a007500001e8081d4000300e07460300440c01c41150704071780b502e03181040000c0400784140325489d400448500e080b0701e81000190b41220703401d080140340c280039420042c14090a0383c401d6903040310001442c80281c04228208007000c40e6900940042d50500302c020f064001c01902210411001a19510f002e0303c40341801e40d07804e0740141958aa0342070301c0c506580640054068424121004000052000d2401c2d510035260501c5401400078074030301c4141ca140002005000360218400c04100384203040080c0502c03102410420302030b0300550b0401001900d032107800920307160381c2d80b42d16400c08161000884c3d0b482c1980c3d00780c541a5052180f913541d0603d07601400900ac0d0819182c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 99460431 99640287 := by
  have h0 := BRFrame.cov_init 99460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 99460431 ≤ n) (h2 : n < 99640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
