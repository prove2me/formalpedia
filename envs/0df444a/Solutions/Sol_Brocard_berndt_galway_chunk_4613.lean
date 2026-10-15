-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4613
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:10:53.182975+00:00
-- url     : https://prove2.me/submissions/98e58ecd-0941-4231-b5d7-6dbf41e84789

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 829496402 ≤ n < 829676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 829497652 1250 829496402 829496429
    0x1c12180c060e150708070528140604170a05040915080d05030c0a120f1821021b0a0e070203030105190501021e100e07030b070f090b0c0a081c06 63
    0xd03094481019282505c0d000244259078811600d070040c1404107196020001188510b0341c0001c018004030b184448500ca500c02880040700061095540c2e4030448000b02001c8244030f00d487c0d07505400000d044d0704c581c01e0a105043c542c80b00b40304030545e500490030600444101108115001040103104d40c0416941003903072840c1080f0203c00a544205d0b504e00c4240075140c0b58031141c941c025417050404030240e03002003000090701c100d0345850380e48659040d5964410f00d600240c5c038005400407449070f03803600c3d0000c1280c2410803c005d0381c0f0925a090b410b81c022004000003c5210340181040e11404007580035556035030400c2c08011020300110300c20200f008140e2014005079800043c4100c2203030850403400107042000030f155144ca41c0e24041403490318108803185031003110005183c0140c0c2d1103045a0111641d40340800c8562940d110110800940504030401c5800e001ca002001c501402c2d2064485084290f2a860240d071b02070070301912001620038100c7c51390041c43c0f00e00009080d20415030761 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 829498902 1250 829497652 829497679
    0xe07091e18080c060f0f06030c0f0d0b040507060305070f0504030f1b0807171605060d063303050c0f0f090916020f1c12180c060e 57
    0x4140840003055905a0303100ea206080d10540c61040684561006840e5611122030820f1903c5901c150744c060300d56502c50003c07803180c04028851920405000d00103000d48100c8408101c0701c45400342032150000348440400c40451000b4910034400c9018400070030300d0518100d001011620300809503420408034562005542d40c1c040100c40859401101c900c103050294207108010b982c0c100002580403405000008041c000819100c0840344030040380048414011066515a4514003038403000d940025003d014504d0000c0240480c40c01c8202c00107540c644910390988003803a00a40074001307051140e4840b0701c02c49034000040c0c010000d482c080c0480c0c280b101d100b480318090072281841002d4041040034880381035078107580450a005089101da0b040600c6919528101640d00c08018002c070301524008400c00500007411250301540d5110101c0404411245400f05045a030301300c079214200d20300880d0031078254840583c0240e030181812445c10002800d481c220950090040e00340c40c0c801c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 829500152 1250 829498902 829498931
    0x5090102120309010f0c0e011202090d26042303010905100c05120a0213080a15020d090b150909010c08042315040209010b040e18010b0a08010e0709 65
    0x51424080702403410384980712071151602500c00740c0c100c41c915910740124201455808140d0078202c800a8941c4400221520110401e921882c007501da00110b4020201000036001076010301c818903a080c07112503017080200d01c105103a2059200030440018a04580141d00c0d1310900b02c4d0000d50b00300c0c000c001d0600256900760300c4000c01204000110764034980c603d1894010404c071031710041742e08011506440c6c0a59420025081074030a0580c4030840b5501082d0f0030b0001442c90440c5070130691203032008400e000314030080d40c454020791002030384401030000042c0c5000481070107401404505541c14200e1000e0080d903001c000c0c5407512750703070400c0b000c4061725801c01e18883d00203401ca1520030700481070403015103803c0b0000a01e10f40c140f00309103611145a032004051400b5500c02c40d01804547d9031400c03090303030901850107500b241c0700c0c140700440d84406007440a00704100b160b03400440c0c40c1600780c0c001060001b0f0307540815000d035110300710304800030404e201010181030100e40800042d800e90890 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 829501402 1250 829500152 829500163
    0x61505160336080c030c180406090609031101050718030308130506190b0a0b0307180e070203090f0d0b0c1c051302010e0a03080d020906090301150e010605090102 71
    0x981400106004216001015070405402c181d215a205000007889024510304440c0c0344a00f110034011101c0c804014607002c80c8095000304020704801c00403100811400962202900440d05660764040d210001407541c003800d107590b03000c2e803117800c1b403174084035046403d50368010a00c000700400c0c0f03200346140c03480800311041541c2c0c151808010700d6950502c80c90440391103900140082c46a20100826541c40c10029024a52100d00501011003200d050003070329030403801aa00300020500001e04490f1082c6410362600c150782e40c255041c1950f03044006003102d810f41312500140c01c006010801e41c24a24510f40d200c04040e94855400b8880c0c1d150415050300180c080c1407040c900003542101c072410140034094900030101c04000da0300305a4052100d401f40d10340c04a001c142d03140c41c0742e192071503c4080e660071603070803002061400c0714007841e100003075028840310b562124017401400c0041e1000d20071a607425000281c0441080d04004645c54800c0d01640480c081100801c1500d5159901280c3c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 829502652 1250 829501402 829501447
    0x402281a03011e0b041205101b02123a1b03140105130e0304080d0504091a030a0611210402033a0903080a031e150b0901051b01061505 59
    0x11b45a0403c6d81700d242182c1170074050f2481003042400c04040300c6018850340d68070b404c1c4003a59000c50720800580e10074a559400761389881000e0001c01e0300041954000303101c02942c101c44003040b048901008140010440b2480a04807011804d9651440c108035018420742200d1260b5a40c412003940c94000010012586440150725541d1174407a840e001050410a031009808080d0035241244094074000300590024450300101078280b00c0380180e20b80340d0038104d11808502601500644040b901c4136000f420314190750b03aa40c03072000c10070010428442602d80d1b4445012112841e400d0516004040c5000c0040078020103e10402d94000000c01403481804440a80311503280c0313104881d542e040d01c24003580e500252106000103401c69400394188d00c008041155500c890a16400c1c10b901d000464000745c00c41c440300100c50109000340c03540140540301e201d00c149040e0b450940050b441c501c4107030b0203c0008007603a44804040c0503440781c01c8050707041c3c0006072802a080140551021000f40382180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 829503902 1250 829502652 829502669
    0xc11030d05150414151f030218041a010c0212151008030a08041104060512060402031c0912080d060f0f081522051c080f0402281a03011e0b04 62
    0x18a480c0b500c1d025014000d0008100c09181c0048074400047c000e584100c0c2e01c162007070030950070043c4d0783c0b03000d01c40d400d003010440d035481da500d26407100152a00350b40820280c5e880302d50038000c03088917501000b003104555528044c0411320b0a015111403c0c25015401030310442e0000e101100000e54051501ca80c02030f0010341070100c148070003020400074070050300b0407604210200303218103140e00c1c0068107d006030300c00d9040f20041407000d030412a603100240f01d610005040d4400400285003031201e10300006000320123082c603200000f50300c0c2045503ca54001034003100d40e81c0082101c64000742c8000700615803c0054103040116080394400d410000f0105a90300582c81248100a0305c010304410f1140e43c0002101c1c200c02202b02c146581d00c220708031400c00102800001080c0c0b00007070702560b0003546d0148c011a01c8001c0e0302c80405444101c001141e5060501d50340c0010754030001e82e9445103502c90101055900d505011031001c3c1a0365203542401c00301c009400820078681850119007c4a0480c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 829505152 1250 829503902 829503931
    0x3090309010f09050904080421051c170709030203070b031009020711030d0810060504030803130203151003030e0423060418051623040c11030d05150414 67
    0x490050f01c108555820140d0816640c204010800c04564002c205980621040c801306a800c520700c0100340303540000080c800d400c9a0341061021800d603140d01d00b8890f403402c0889840b80c000300e100b541243c2c201c4400002408050040040d401c00f440144003138a12010402c1c95858894480c201c1410a031040c3c0c0745440d4002000411700146122500c0c0c1c000300102602c0030366044e40c0c0010442c0000343c507401c1c40001e010382e0000d01c03d40504201c500312503100e2205c0781180d43c0d4080c01440800642000c3c0d03054040c608412419009031401103104003a22080e106c141401c504004000400c9030704502c0c00303030f8902001040c040351151101304900605141d280c3c1e29a45600c040b5015120410081d040c010003200500108103010860300d8a90041c400c0c6096810b5490030601c800720742098165035204900c00071071280b41480d030014510481d241c18081d0301e220814001a00d9503100e0409080800d03503072810710000506400c090341c003c20088030203100d910407402c21003056880285c400c64031907210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 829506402 1250 829505152 829505177
    0x7120e0108070c02010c0213050f070e03011e110708030a0f0b09090c10090504020a050705060a1107060504020d02060a0c0506094303030207030c0b3405010501090902030606060309030901 82
    0x1e08c419101c00352032201c81844581480156900304590a0761103401050f00e214030340780381d82014450350590248103400c02500e5a40f502500d0010084100b0701504040c1c10050000030070402c800a5014081580c80001c2540c503080c0003c0840301181010f920843c45c0f03400303100f100c4030300050408a00c54101d0760007514100e5200140d500400d42e030700c101d41103400420b130004100c0c2c000000c1c01c05507004000741d9029035200e140c2c80b4111014207450413941502481110301007626a8007559103c0e2018064002240c0e07a600060074a41224801c100001e04010000003049424071030560480d0400300141400b0610500c0ba41c0c00340c000748a1602c110202420704a41c210101d2040341c0070307070b640b805d440004588909000f929600726004c160b401c42d04c4c8240c001071102560b012540e03201001e000c0180604a101c11b089103c01204402180c45801d0a07807040c00b24401f803181e24002d10f0b140000007456007080c41850300304403006103506c0c8513202c03c2c000c100841e4404002c6543c0e9800910f40034002c01d91 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 829507652 1250 829506402 829506409
    0x406090801090c090f1b020f1b060a12020403080318010c0c05060c21010b032a0909070c02041a01030b01020109020603150a090f022a070e0c0f07120e0108070c02010c02 74
    0x21b9040110b011440101c0e0140e0810380108071002400c8000d025241c61084c24a40c003400851004c4c0499040b070420494a401c1034851000051030440c00c401c054a0180d490302c030240e80e42c10680d158000381203c1100c4c070340044024410404e1490341410302101c4000140c551a84401000f012480200c00020f02c000305007001444020102c003090002d60000e5864100c1031750a41c004540b58911461a04111035140e04128410035045102e0b01c00c0c0303807600e60321000388002e40b840a8003640034081d980810000690b21400f035024143c050010b103280c020040e00005040d6801056800e05691401101e0405a12618200d0782e00041d41c061040411000c1c0000c42c9507140307150b00c030100319898800011710758180f80d002015a15001061658054001c52001c0307181141801250780c15841460100894104800c003142d10080d44403034036080041501d402c4051703900c08502203520602035802c190145400c80c4818041c40c42c00e01e03040105140030b140103400411046400781c14001100d2102d800c541c2c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 829508902 1250 829507652 829507661
    0x8090301020f280206132012010e07050a0614031305060903040503010b060406080406110412030e18040c06030b2b0201230d1812050406090801090c090f 67
    0x804490381d1980d5203a6180260303410307158589400f400402e010700700000b407a2000880c44d0041150000b201d4142e000c1d13549002502d00701c0400704801800f00b80307194007180d03600c0200b0101d5075410b80c00032034100d50700c6440c1c506041680c4c011900c510550704092003600c2d40407006148260f1a0524550340e43c5440b4900c10081e180c110004160b0f02c40c100030000440d0740403001e0002c49006030b00900c0070b90310060400940d0700960166600060340c9100045c081740c295006400c9003032141900d0351074191a01c0180140260b81101903012a5000d0940c20369410240398a544012140078507e00c10b0600303944180440c000c0e4802c6804140c0c6500c064103480ea200c40d4119090100310054800c100d010746500b00c007203c028201139020505500c40400c104c9582c266126085996101044c81c15054642943c01042042210140c0c0034200d80000c001400301c5009966140642e10ba0548039450440d0081c085091500030740c034607034103210109000620076940f0304240c42d501f40c00403031840d000805940040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 829510152 1250 829508902 829508917
    0x110c130209101205060f060703031a06030a020a08060306041112240414011406010f0908010e030301150e1f0c0501060f1409010518060114270117040809030102 70
    0x90800c404480095400c10406181040f40c1d4005200d103a54900c104000e40303c01c1400d80d9040003080001d807000a00c01d51082301c0918506110000b40e40c04040418440d800c00c0f01c0145040381d0000e9540301082d00003a0141d030040302240240320900c4e266490b00d807503180040c4054040c6c1c0012082c1c0180e10000d104000c041000014060040ca8406041500010042ea8203032440010441c8880300c0d83c4060103a88807101c0e40031240081c030f440d0a0011660a00030b18080010800300e040003154002c03080c01464100c4480100860300c2c0d50400500448802d5400101c0302440203000c1851b009450725001155113400d0003c01009400910030709488540b07010030024250351038668081458190b0101c608103844041044545040c255420301c11554001e000301c0b64408180d140a0750002c002c081d003075500071018581550005180300140c46aa04001103e5001c681204501c42c00e580b900d2083d0089e1440c00d2070500000c0000025100c00720102500103084018001286140c83c0c400b5011541c21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 829511402 1250 829510152 829510159
    0x90c0d091e0309030b010b13052101020c0313120302060115030209030d03050f010f0f0b03180303010314100203071b021c061505040e1005060d06050408030a0c110c130209 75
    0x100308070b40b03001010100c0a0104803003d040003000401c40c40c54107400e440700d00a0801d00000744604002c1044802d1088030030880b034542588802400004080c0003074584850b040000f580c81c1d0322016001040420282c00202c0c0e5034000010140c0070a03400070f0450304640310305049507405078503103404074082c0c4581c1c1c1c45903802d4890200007141c1e6560542c001c6104518080c141d41d2981d884c2e03800c81c00440040c3c81110600c1c40c142a052004070110030041d83c00002022413a0b05091042d43d03014110381090f8016207814040e090075025000041c0260525203c0c0d0803021491450540006840804500605903041e8021400704086465060070809101d00c0036078007003105020362070402c2c0035140c042e40490000c0d91074140065a030620740514900813500c4009412054681c040030300c000d00c0001c0003583c0c441c0c45801e4010219105201e070302c0c003690007080000d55a2500710164810340c2d0b8580c1a5008018041c6400f00c525840440d480810800480d0400c0c01600301c07100c901c0c080c1c0103403083c0650 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 829512652 1250 829511402 829511453
    0x70503101508070e0f0102100b03070f030b0103030305150d11240912030c2a09010f03031e0f0c0309080726070311060903030c0f030a0e090c0d09 64
    0x21101c1c0c006180c24801c1d0242c0d40c4051029908801740220800401d00b0b81c0d025a0000c001c081c03001c0d240d40c1200d080b40c140901115000c139994488040424010750003a202215490014024154107000b510b80c0141c4c22007600c440700840d800030a018241010000d417030071801008902d02e59892081d0265101681c02c40b66001c0d1217030080503200ca80c860444c00b0b105088407008074169400c080207590f070006047c0c004c0e200e610080c0707144440030385d840b000c0c0d10300c500c4484d801104150b41c1c0c0303c0098043c14015508226982c1140342c081c0c01d4240d03040c0b04041102949850000c050340c40181645000c1661501000000d110724003622005c1070f50b0804070542c00b402e00003058054801a006840c400c041c21849004400d006829860301024000608600340c0b280900095003005001411fa40c540a003c07285001250b1080a0920f14400f481400c117401c0016120302d4903610044800100400700ca0940d21801c02032060411849210805c1626903202c40c641010702000c000d600e1500b4040305400c88 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 829513902 1250 829512652 829512689
    0x706090203120306030c0108011d09250f06080928060504051b0a03120f170709090e030c06010e04060204030212060f1506162105071103010c050307050310 68
    0x2da45070011035416003c0d10480988050ba9882052018101d50b084007040290320301c1055184d102e078034014400740c500d10074001c403011030468a001240841107010550f048803802c0c0030502240581a0788400d08001000b4240542d4800101e2012043c090300413908070044a041c00b8628481102040508a1450300c0704200c1408004140c0000141e580301e502c0d03440764035105c1080303c1d44e8942d000140c00d8a84240c030300c400b11405200c0740300003044a03051002c0200148040c04605480883c6c8880004e00e20070380c100480f00081c0540050107000101850600d81040e908136690501403007605066403001002c02d090040030f5045401658014010241c0d280c42540b186588135000c0c3c0c0c0b809030002c541c00009402e005410403044950000410403850103220700003100d4503d0303140c841a02d210071641c4c81031284000200d1000300300c9446803220b40c0ca621443c248401e4140c10069400c0c00381e4102011200340e947c2c030200b00c0b54006464200652a612400c00c000c041c548140c00c1014800d2244d800710 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 829515152 1250 829513902 829513933
    0x606051801201b030a030f0309050705040501030813060915050d060b280813080702030f0d090503070b0f031305010207050709020d0c02010603080a0518030a0f0b13020904080706090203 81
    0x7440000000c1d80046543d04420038140d99103103103440900084c0003803591860a500ca5088038140c140144101e9514645a07800502181c000382c0c0111542c00e400650242d0301d085104000d00280900e0070821110b07851324020b40e81c81042c0898100801c41c000584980000740c585c4030001500003801580e8031940c2c881d9144a003a02201d10703900c03c00c1d40c1c0d0518000c07030310b10560f0424440e002c40000c1f03c0c0304070242d6070b0304001ca80004004a03854003511251032101e007820403558404030b056940702c50b40d040c40c1030281030400881e6000349080141c1000f88030000c04128007140d0b080700183e1440d0490369604d041581c020b0048402c014403901400000081140701c42e0007800020040410400c0300b415250000da00701e4282e480f00038030300c80c010f211401142d800b500180000c58000b0095582c140c40460009081c00704681c411201c808603410084144281c8141650780b0010b1310001e4840e440054000540740800100300034503020000030400c00300800b0750080c15041d0350160444e00f02540200c01c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 829516402 1250 829515152 829515163
    0x1e0332070b070b0121140c0310060f09020712110f060403050318160b090f040603300e1003110307030f0f020708030a0c090f1205060703060605180120 66
    0xfa0b038032542d10400440c0607040b290030034203081c080c6155040309150558405a00607140c40c900340b15070140500c0c4c0b0303400c0d23101880740502d80102c0c00000550a0b08241c00f6800c8910940c102040c002e10502042c00001c9100da4464046100c6040882e000f140386c0e0445403402508100c0610240101002c1c00100750700803000e10301034010380252100ca9418452056641c0d00d03c1003a14041101040c000c01094195400a1181d0356018060061f56245034022030240e1f000c560044035561070743c10507480e0310040c40d00c1c1d00000e2500b40b0004031841001450085c0000c9000148500c5a80300c100300c1d10340e0a000b5801940c0165281c800b190710b030b240200000c1c0003800c400d010769140d1802d00651000d0417600d4400c5840c07840d40030441070308545a03034102c5801030141030740030800c0c0801000f0100d403401c000008040140300c15014a0700b60b07005840c0007401c3c40310180c02c41c024581080c1d01404100d4101041c1d44046c021038218004075680340303004a840c0c4510010f14400900c4206c600c002e00a0040348 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 829517652 1250 829516402 829516417
    0x7030f0b0f0a09030e0d0618030e040c0201060602070612020403120c0203010b030102250809030105041b0602060609190f05091b150712090306020f041e0332070b 71
    0x101c1c1d10710380d5990100141924000d035401800200b800145507464a040c1c401d035a0715a004103400070380c1d01003491441c030640100340401c1e008602c2503407898565290500458110060f40d200900009240c41c00195403103002c2d005200c1030000000c121031216003150b050302c00441d0042440c2c1803088510030054917041c01c2c11410383c0203500f8010150602e0070140201c0c2c2c101c0400183c800500009040b40603c01208034608440c00c010030400c0e9400c1c1d40c0c003405250300460044100410f400da03503c1c04000100c050740d0056055400140800c102c4d0364503c4000d503800a035440d0039540c040c070a80400c01c000d1481c0c601d500100c5140a0602c04400d00010701d00345800c601d104c2910500943e8400c1248030000200c240c4903c01c820004917000914010040b15550b28134240740c1a00d80c0c499903010180c1e00500040440b065000c1420001a103041c40360720868041c00b01514115811a04c41d000b401000c40302c0d03185c40181c130b1499401c00390464051240d62401c1401502e4515481d01c1c913145540d0f10502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 829518902 1250 829517652 829517671
    0xb0712271103151b0d06060201021b07030f03360620070302040e120706090c0603051b1608031311060424030605061c051b03040f0507030f0b 62
    0x1852403150300300000e142c0e22141e801200848070b0b544003803003154040d0300d4003000c0b110013000344000d009a80c25402681c0152050342c0000d43c64502e041c5901c909948220f00b2a00c0039070069004001044901c00e4204080fa01480e220301c0c003008100344a4000404484d0b01e42d0a1b505101c3e242240554204840e0207986ea01d5462242c1f0b080949a41c1d0b5444c108540c00340d9103038000314410001071a15500c0b280220781c0c10016510340c200106805501d0ba0000d01c0c040c0c81a81d1500a51020090709426400103031080382002c02071414000d0300380c654056500360044507250000b440300c0c2800d49a030f10078000303983c2c8031410f142c1d0b0b40350100d108003021240c0482128450f4091499900d2450044140c400743c80000c020b007100003114012000c558820321007120245541c4460220b05521114001c180001541a0980320742d58461441d4084803802000100094000401013070303042810022a504030f41c1250b000040c2c06280d04025040c840503078001002c0340c0d43c040342c0c44100414150050310400d00b01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 829520152 1250 829518902 829518923
    0x180915130b12030403051504170a110c0603011d041103030d1d0105060310020d020d09060e070e0705070807080f070f060c0c02090103030f020f030d060f09090b071227 73
    0x10840702d56680100c0c04000c00503084111110007010211186d168414050803062900701d10084a41c8040e50106086900007040301e040c04a400c20100156150b50b141540c0d040d203907600d4013400c42c0c48650070300400c0a2006054002ca418000401c5000500d51001810740382e40e131b0500c1401c140100b1402e0701940d81100508038203108480103118051041e00060041e214807a0280c0700c88000394000100e003900c6603424040740240a170544515905944240b000007180c0010440359450407110b42d01100c40c1480300780070440015408003e4540c0c0702d900c140d0041d00c80e1343d185801c914a00441c12050f0f0207110104040042c030480120f2040c603140a103108006081840300c2c1103075004001c50020350018000c0d001000000d208802c14000313540c00780705a427844999492150f0443e40200038016040d07860f490b00b80000e0003000900e40090000701000c0043c10030a6450210111009008005212840f840900d601309541c00800c0882c00e41040c3e114050f50303110b100c40c0e030004240c1c810740b02c04610 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 829521402 1250 829520152 829520179
    0xe15041e060801020f0a111501060c06050916120609021c170712050c011d101109100f0c150f060603050603070311060705120a080c180915130b 63
    0x184200c8207400004400705d460012103520a0301c2e2909078054214842c4074524080d10780107403684013030b4041c040720b0f543c140b048400390811005885024140718450740050595400714159490364004a030301d0244803d007580014104400148400ba1010b5003080450f00310181d0f0050000c01d00703580380e1003001080b00f850030720329003002540a11903004188000b00d55411107154061005070040345900030004c21000c9501441094030b501900080210b94400c07842a041924980600303a81111003c0c0114149a403920000f949904060340c20814040b000c40112421840740104d985e809402101d02c1e07503a89400268030004000c2c01c00c401c80070514100c00403802600c2405840e0040ca0024010054181540c45000f00045c2c404d0003d07900541c1001070000042c014000c030840406000500c0c0d4031000c810001500740304000300840c59440d0104091450a15000c200714a109800c7e141d0100b16503400a601c10010b10390444154042103005a1701d038684d1712504040030f030880c2540c8207a1a41203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 829522652 1250 829521402 829521419
    0x190e1e04030c0204020d0f0c0c02041b0215090c0913020415050607380603060106020a0807060209030a170304031713030c0213091a06090c040e15041e06 67
    0x340c9000340041d001c40c00c418094609030700a0404e004010400050304101c1003c403004680c04c2c0d00e10034021a201e104030000f503150a2044002107048940100c031a0284a14002d480700343c01440303204008018004546d401404026512180601400d03035542418640800e40401c60015012440f441c14850425588500046940b08859014094a0a1114994441c0c5407103007800398102c040b0304481d40800c0c2c80b81034102500d400c6254208480c0590504d00207050515805800c0101590302c41361120000848020460700c0c01c40d004880141c82d0141000081d003010b52281c40a040c0401103801d03c00140302241c0203501586c8640c0707822202c500304c1001c41c07140c1c560484001607580c0850f040003003c41d00030340c080043c03203200a045e00708910080002c441116000c5170242c800038001c0c03911f11140000d00e5255600800704546a00c0c00340381505521500d40b05d2070251707624295400000c290411000302d075030030110800500501800c001c9076514008042442e5a1050050600100086141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 829523902 1250 829522652 829522711
    0x5060106091211011116030209010801090b180f0a060c0f020c010518060f16120809060103030e01050c060f1506091f1e05031605031014190e 62
    0x982c1440c0e9004042c0241d11524194290f0b043c1690600c220100100000703c014484142040c07955004070706641d0442c014821040c0050300000091703894654000e004c00c103d002800d0b07101c4044d200c16a1b030800660101c500b014081c81400c00184140c80c41901000482d0700458222039155440515000c9021780c00c0743d40c0d90700c0340344290210340c0c02c10030001d140026445400d03c2c0384004d0015441c181100311010395640c084507003408405101c00500d810040b080180c2400581e8a291801c3d0a003419502c031501d401043c44000c3c1403040341c2c20f085006074000c070255440a10242d09440592070410041c61301103404076600c1c40320710103000d820b100c0c82c903084090700d43d4160b000c0c1c0345945080c0001403070801085840c1c810070a100c0101450a01d0107a20700da04003415409594580d200c0c2050211024136500c6401003106000042c0208000e40d004031801c030040303d840c40102040d0424490105410503140400214004000c08005c100703000d82c001c01c0f6020b0705002080800064110b0f94210006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 829525152 1250 829523902 829523909
    0x20603100b03070c1a0f06060d0209210f150c070f05010c020a020a0f0e04060b2407050c010903150f0e07080a0b0702030a080a240305011a09070f1107051009030506010609 75
    0x61b0b103c540403a09a08050018114990105400514100391040050174231a00041c2106141c03400c000e103100d4407030f4144231800003002d0b520001c15400255007450100d0407001030120346c0c4082d01240342001e114801145001068110b4020032003003e80c06402074031402044426400b492000f400003035410108004070007110181404a112500c940d59010f0203411140304040d0310100c0c01501c0244030b4028400c07109000680d005917a958079039450700741d040c8901d07144258103006000408002150b1485044c04200340300034400070781d103d2149808001402c0c54004200b4510035503101203000c10303000a100d00f443e40a0b021181c81039542c132004076680e200e070201e00380024130740d4404201c8104944e08281e400c2c0b610031855040b100307001d1002c445800300d280d2007568141c2d103561304683d40d0900c0703074005042c060055645882603d41844050000680c11000f00c080104000000b070b007800003809160b000d000010120340d50b031035a03001c2c000d20408003030106507040d02a807000000c02d42e01651641048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 829526402 1250 829525152 829525171
    0x207060b1e010c0614100918020604031515090c08090109121805090705041809020102030f0d02040906090506011101090308040206030a14070810080c0d020603100b03070c1a 76
    0x4822100440f018403005604903080c90b207401480c3c2404001c62501d511880c005040980700e1031503c250304060714034403081411a082c1e0340d0b48070400340e1528030813039003601d4100b0b9110300d00c50100c41811000300714880c040c0708420801180818610318907000321007441202d07a5003880640f40e0302002400c980f040b04c1c1c002d001203010281c6941d214000c8000f409611b120032502d040c090303901c42c00300705200e004545500001c0c100103024480e402050802040e4417041c3e01d0b040088150703070b50000c2d5a07032007942001c50050001142c4a44e0507100b9804a034040c0c840c0740c40621101c0c0e92060141d002d081300b40c44550115100d1025680c07010414400e000203241c05903900451034a650702440107a920181c0400403207501c91030762501554032502c0b00742c01540d56a445000c0380c580b1050045285201c3d410084c1e0581001110b02e201e9a12209400d41ca603030125040b41d608c0d00ca074402c0380f40d440d24a512060b180c800c04030810184942008440c10107a010700c5c0400e01104543d0301982c1c0014040b205102c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 829527652 1250 829526402 829526449
    0x110909010308460915020303070306080a031215090f050412080408090d3207060201060e0f06010306081c080c09091501050c01060f03140313060c08090a0303030207060b 74
    0x40103082520f9880040314200410700d5500e42c3c0b11a001410f0030100080564400024000802d9061042000034000c080141c200349959660060489543c41800003446880d20004480103018090071001000d100100704000501c20401401501c021a802d6419484000c150050180504050740c030541d07000200c03d142048a80c2013100044840c1d80554680701003000c5544030755171034176400c00e445040c9030100184034a000945403803c54039801c00b604590400c4010089202c04d400f096803c0700f1083e002090760340c0c4900040b402404c0c02c2e40104450310030100e4105580c00083c91200c0c2004450341c0f075504940c0c840d6400011842112060b640250b580d0340021107500030486600004001498014904403840c0f040c00d080d2a40c1d500580041c108049040003040240c4c4a41881ca4481401131404e00010f580800c0012201d40314060a10128420302010080068219801800000e04903c3d2035501ca0900500035004110200c645615040e1010316500d171907503005d002c5040783c031040711 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 829528902 1250 829527652 829527757
    0x8160e0f06130c0210020412120509030a0b090c030102030709080706050a1b02010903080a021b0405090a0b0703020706020d0507120603020a09020705150c0a1b080d110909010308 78
    0x8100000e038031011170260a0340380b080580113000800060034864104d040070740c1c8030b0400300c90a0910714201000d000d070400c042c5049440c04518400c1d15a040b080d040155039840e54428102021301c00c0722681940f000003005070240e080710400c410f4900345011142466160300050700c1d14031800c460384002c100343c1c540c150503403103401c0083c0248901c10307d02047c2c0540d51740c0d84c0500d0b5030030480e05000560015806240c48c030b5a0200c841c03400d0a0b040300c041c00a401c1007040540c6815454001500f03030906000000c6e141e50007074044480c600d0b4005070465a07408090705d41030040c94245c1e42500040c880c00400c3c15442c04d2070240c54183c9400829204845103413003515002540410007c803101e0103158101d13113606031382d099440d208181340d81c12191b036140109001440420040429101d04142c50381203c04a48007000b030b1074251018945c0000c8003a54114960124000c081141ea170010300000007200300508440617049428190202040c030300e2816410946101d88040b040320f0381610701c3c4101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 829530152 1250 829528902 829528939
    0x90614070503430e18131e0503160b0105032a041508030a09230f0d14070905070f0c11060f030a06051003021602120708160e0f06 57
    0x50403102c0d4030300e08142004040410030f800c0400031200c0c0c040810010724491640d42410350040c00c180121559803541c602d0b219020030b11604104001034143c604401d030181403100e018400d8103000740c0203821240c5402100402c02c0b2203040c41d610172602c45409100002d240e0131b001a22a44440c254255255800c403125000c0400d030b480840190340c002c1d1a9207101e48051151a81000030703054810195a5900e075902e005800805240c1c0085001c05520302c2194000b2988400400c4c50f500880e8190104054100003030395500c40d00102034000150044400e40f0403e00007549030031034110362070900c03140d91a101c068411130b01001c6540041a0302c0e003c820001501c00c250790b1000700000300124181007128080d081d05800440381c9580c0c15540d09000e0215207010807110110300c1e401d14003035103082d58103049240c114103c0c50000f4001c0280c509540010782c410301240300645407010485507035410302c50f0b004213200f169101e1022999038a10208480c00305954543e403041c17001400510310302d82c000300d50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 829531402 1250 829530152 829530211
    0xa0b0c1005060d0609230c15161e0213050f090735011d0c0603010b0403020f0a031205090f0a06050304080f121e0717011202060904090614070503 64
    0x71a400c005c2c60010801031170301c412a1146108150004000142e5011b0a024004a00000310001140d0502c01500b810040030400000c0b641d100041d03070881010164081c81c00d0f00e8012000f33500000a1403080f0900e159a40200d1152046000c15a1107488081500f600e030f040d54007a00700d500d00000e03800e00d00003100c289550421070105e4580381c64401c41c1e040243c00c4698583c031442005246070324001100c90300708a000b40340b410031100a40743d0351500c0460f0127984030300e1100074001c00f8080140341c2980d440e1165079000f5604036044505034034408500401980c130500d59648a00c024405c0100c02c0d06000c0d0320700d4251070050300c41c00d180d5162078680e100d464010901c9410f2040003009900c205035989100103000d00c4000b200c03150003405070f501a890256005140c0c80400000030320448180460481060450300c1c1240e200458556030b0001c11028400d006065812905100c20f0300c040150b0303a801002e03501d03402c0a07210440c0d21090800c585910060b103030700c01c101909051321188010b03542c2c40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 829532652 1250 829531402 829531421
    0x301060302160609110a06090e0a090201110727090c03061e0614102309030f030313051e0303040b070e030a060915020901140c0304050a0b0c1005060d06 67
    0x700b0481201160355500f0950350409011900080c040c0d500ca1150300b0180b2542028010f1401d04da0170803400d141c44680b410303500600a405d0161038816405c15640525400079009500e402521807142e111102c90100c010000c0b0b581c6030b00d209820398030151030700758407400929982c4084410b404c28a55100c1202500d240180082c03048507613080046003003c00c0c0701e5400100031180d92854008107620401c050410084005405c2c4450201e904c0381810084c40c000400c10900c40c440c6499000d0807020074034100f8240201003241c0301c004140701d11200d580200c188603600c240112902c50282d0600f030b60510011005006240e40180081000103120224103540300050f842c01c83c85070403007500024a09040c1100646580380d840b420302003881805003480011403190711040d40f4000810000814061144005048010020464007600c207000c1c41140c000701030040140c0c10090325400c919010b60301c54000c50721103200b40307030302070466100c54000e8520840b001801514001c04640780c0c034010340f000c80d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 829533902 1250 829532652 829532677
    0xb041a0a02280e0604140f0915010c061d010e0124031e061404060b1e060c01060f060207090b0406030b222301050c09030a171e07050c01140301060302 66
    0x482003e180e860b414090b20043c41c1151000802e60241c80c24071240d00010454240204070b000d081020750b541255165220303290a00e4105101040b41c01c280c4010840c140c01c0c00440b81d03020f0203000c1340038815003000d0282c5803040020800008414549203000e20900b41c00d05852886a00410108903902c19400740c590b003003402980d040205607607900c11110310800d20100c0913103004c144401c1c050184a4a18020000d951082034410610100c0400111041c2c0b9a44036040000350f49440700350030340203400204004a00020043c0d12100081d40340e900307130b020302c000407498411500c0051602d030090700104c1e80c211503101926200c001048010852128802e000c81100000b40170004042407490441100c400000018003542d0419241c25904041c24014603100c040c011603010346c0c1c000c07905001d031075070204801e2220000404041014007032000e2038890444142e1800d80320003062001040114800d00640c3c0c0c00316210310042d00d0046900c81c001154a4042c401885124040d40c001e244040d1b569 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 829535152 1250 829533902 829533917
    0x70905011805030601031a1302090606090105093105011401030b030a0209100f0503030309031617071a0108031903050c092706100804030804030c0b041a0a0228 70
    0x2c001103894160280c1c021941d00c00040b4040c0e882a0f041d00c0c41580000f10b50803904100d0381030b40c001403214900076180178424080041d8904580e07005208444101030050310b154803d503184903810090240ca010024014801684801200060780c424507069840310303000000b51500d6000110018142440c4585d0144101804213000d82d561a03103461255103415246a00399007022046214140c017a44582d01a9105106002d04580044140d54019640c5180d40c00c0303400c62410000c540010380042d20f4103503403002407481c040c41981e020800d6031100d40a10107405903600e4020076a00d03c04c95030100c00e080c0d42270565041480c42600f00e190000a001092402e105802c130000b500c80f003070940c014400d80c04601550094010000c91281c0c8490112400680807170395a6006e0b0098100410080030007204500040816024000d48801e0355001154400e083c5418070b0700780100030350b00081d0343c40d42d00c1e100c00041d8003000c0b034000c0390aaa15250381c1d100103003400041c0d984282c05460349400900100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 829536402 1250 829535152 829535159
    0x21090f0b16081c0b060a23070f1a150f1005040503030a0306090b01030603020a300b09010e0708070b1305060c061e0c04121505100314060709050118 65
    0x260040d155110664070840d45403140c43c040102102c039030700e0034a13004403070901541da8030642000000382d070600c00e1130307a5180700c5001504e0ba00092107528802096a01c40900700c0050100d4940f0072030100001e0510001c607622842c0c03050850030001c01165920103807109a60300b21f03040800301c3c501955900d0514904094543e00004d00b542c0107400300b5000a5603c0100300b059840314025020507034020700f010449141543c010640f0f800d290701425490404400080206044500b02a442d22101404e1850180d4051401d81c0c0100c400f99840c0c1100d60904910554072000422041d044501071300041c1506460a00f020f19560400c080c81d00c0c4240e0201000921070315110000d00886003603d019203158a0b0220051071400111503807007111480020400044040d04012030b81610303041d9080007000d01041c81d100d41700404100000448908010500a0035010480d8542c03d40344106690703850441c040044076a500380c110f4006000a000c61010021940580d4010701d085124503120307400e5984 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 829537652 1250 829536402 829536413
    0x140705060a0f171306050c030f010b0703020c1309050c120c040e0708070608040b150d0311210a09120c090903020709020a0f140c0a080a0c0f21090f0b16 67
    0x8100c4490340088104e500350820800d10b031081c5980f01c944e0b2a003560a60420038003525803040140110400f5580000c1c0000a060007080300e10f40407000249001a4000d160b800200a418240b600b291030703200310741c6113110740c0c43c01104060780812108024061090240104806094407000010385402400c0001c90111814010800035100503150311480b4180b9140040c405040281419060a24004e40c00000d0ba035105001e0481e54240c5031801d07000d8070310728007142403004c2a40b075206912031403040400d24442c0000588104165612079007005aa1912a0786040d0700f12403005003844500242446866001d80c44075032940e00030320440d05100c0e165140d5100300e07030160103140c0100303100c58140c11510380d10984100740702c0318140d1014240003603070441503515450058001d151303440108603803486910a801403264140c001d1f400b064401680e00303056203c100f001201c544004521100340c120395016881a90494600c280e081c1881480c01070841d40da50000b184001c60488640d009801140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 829538902 1250 829537652 829537697
    0x1b0105011e08070303050a0309080c0d0c02011101020f030604090f0503030c070605060a0806073218090c0301090906090b0718091116050109020603090703140705060a0f 74
    0x100907034000c98074100c540c050701c5101d5690201d81503a105400c28800298004c0c107981144170141804601003220740303060000740c00344118010036842000b40031120a54000c41508140d8001c0c2c13078044c0d0741400c0c45151030903032240f6048010910703000c00228000f41015404100554024450501c0d8580390741c4e502403c0d0b50003074403040307085440803650070180909840f549030040c40849040714258500405d0f10f80350040200100c007400005060a0302103241030301c40000c00d860181d0803590001a103081c180b119040449035640d0310740001212380035414040816405460400921030450b860301c1d8000c0060105603038115a0b86444051843c005403044072a41d010f00b0041d1140d4951600250340c104007031415500040116050401c0303059800a803030300b151519a06009050125506410b003140235110706100203402003400420014000c101048020036203204502c2810903215100880e50303210f070705001d4180d0040c002c20802102c1d070f000e00300d010411040bd081035103040140a85012400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829540152 1250 829538902 829538909
    0x504290702041401090f061d04260a03050c090328060609050402120a0b06040b03070b0a020c10051e16020a09050118140106081905091c051e1b010501 66
    0x10300443e0041c003484800e402204400c102c16074080024030700d00840d100e90a01e00d94600b480e2040900040b0302404000102903401d200c9a00c07040e19103508a0705a00141e0f8071094203d0006881e00000c5210710026200722078048500400403c5445021141d4283d0b8280040b00022450f49446040b000541d640c029a0010510070f00009007910305801030040c121514070800381c40d0b40283c010040090b4100d01a0f0b078104030155800504c0d4040c28011924055068024402c424070108000001c05d60004182c41541400e5034a00c00d1500451003c1e28580290070001c40c281130303e80741d660b14201410000c0c0c202c900010030440301c0f6040c1c5801280080f40c40da000b003078003547ca8000601c0b400b48401c48070060541011810000300402d1000c064aa40041c00348004010390040468109074403541250182072f4100420402d42c01d000580c20768a16900000e040aa8007032500f80d4000d6008134291005409101c50010344280c03201501c01083d40308a290a0048800071043c0404100c02d12800d07028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829541402 1250 829540152 829540181
    0xf03050c160902280c0602090d2315100e1302040f050f01050d08090907030b06031626060108061507080310050609130e010204150f0807050429070204 66
    0x3100a01665042d0481c20881c1140c18184032102c4d40c1132440d40580164203641d00003000580754502c520018024420201026040d85400b400e04440f0304502d20383c3c200342c070b0a02001c8030a1030540032098140758404407010354003003000c0081045809181e040440c0e0010740c5c824070801c02c1d21141d0000d402c403581c0d0b82000281c1540c1d11300300a0900310b0303980d405015007400c40303200c04200e01951300c00185115000e840d07405a100d50000c036030003034025080301d0301c2a0340040105440c0e01c1c190011400503603038804d0b036a00080d00041d01600c51240b0350014490550304400b07660880c4d50f04001560080000340c1031542000c0f0a903042014140e4400143c4400d9200f0320f000c640d05c2c00e00c00d0029070f040380d80390401441600c0070403011300c081d61501040200d2035140c1101064004242c8111402809140d100120300100c01525003811540300c0d50411541101d61262185521065800c03140e41c0180c0c020964000c0490b0044110041c408005004010701e032030502d0329000c0703150b01050070789640300d003c1c80b00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829542652 1250 829541402 829541407
    0x32a031401081b011107050f06070209040f030f18061b080316120614011d0307090207020910230a1503230f0721052706040f03050c160902 61
    0x107003c000c0002a611030001d00c4c1028a007040d0710461a112106c5115242c440d0301d80006060841d04c4100645442a070002c4c03001c20f803442c26081c034641c48410a80120b000038410b04400c0328a50040385940c00752940f070345040c4202350134140207940141984840394040c40c500180038001580c810015480340c0400d072007030803070100709800240002b031940e149400b10600b0301c0e4003401801c50f00030351085070f04000d1034124070440041c046100d402080740f52054150061040100d0444659002440d00e50320a48480010b82d41d0928402d004558600906190b81c1a11554030040078188550405d5424024410303100150f840081180d1a5555403074003010a4582d102e08180414100303021030108948040300b00c0c1031422070210118200010541028000907020010925010f18840f02e0030b50b011174401c02031420840340d85c20000c50201e90803a070340d040d604080128010302084071401240d10114200240845503015989600040398203456441140100407800882400c0d1700001c00c1100700060303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829543902 1250 829542652 829542673
    0x30c2506050301031a06061b060402090c0c0d050d020d020310030c170601090203130f3c02040b010216030b01050301061d060d03020712150606032a03140108 69
    0x100040968030030300510909000410200e14034150940c200140c0d8500324480340c0e92440055140d0083c2803c007805007a0016900415420004001b40594004c4564140300c1d5140068881c540c030541c041d00d20b40e600140038003020343e4000c1c0058030b0504003400d400340c1081883e42902080703800813601a142607101450400a1045220b106005020b0380c0c100c0440051701d04413903590340c2070b06119a40c07155500100180c4481c0412141c0030311940d0090310100302c12821305105004100340004401c007491a65040c0c00c00d0101403030340e10001415440c8040b0448215003c010090140e08161415801100f6031340d100820242c0c2890b0255118540c0c1084c254103140506085482c65004400101000421a07038034071812030320143c0c044003c40350040388404034070f0202d09012042d0710603100503090300c0c941410495103003081d0301c00555030700c401c0000c1a6507140840607034451440310904901801d0800d00c2c807600041c4442d19900302c600b4045a603a040050003005001c099002c2c0e001500031080300d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829545152 1250 829543902 829543963
    0x40e060415020c03070f1e0302030c0705192c01120302010b03060f0103110d0605070302041409010f0605131d1806040b01090f0f110405011806090512030c 68
    0x114078049a03042103090011207103103595244500c6101418031100c82d030803501009583c40001600e002c0388501080495180d2030040c4d07894100e810040042c0c0903002000c90707542461035841c0ca8407030140e2003049411385807074143d41c14a000145008101d10040900c065108103001c078540c024007010680032841041c5040c002d0850745003e40c8980b19800101c10700804240c10090307241544c0e001024040d8610403800010880400104010030150400b410480070b1901039010b01700700c030901d28a2411511481d0104103c00c44240200d500599105400f030024512400250003070200e0b004052503190746444184142c1448051000e0b07c21040ba030811548007007403680f592030711940d80003c022a017002e5442c001d405005019040256950306001e19003040190856096100540010080801e00d09607001d11648507000e058042064401800c8542030310b030dd00e0004403034003690b540e183d00d8280b404000200c8600c1c80c1c001c1503440300b44644d40170840305010440441d02c4407440d201c0c0100032031004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829546402 1250 829545152 829545173
    0x4030c1401090b09100e0f03010e0d090e010b030a050c040806130213090b010510122415050a03090204091b050a0b0708031807080706050309060604060312030b01050405040e0604 78
    0x1507440781080c0f1a10085846018400e0312000383d0b1b0030401e8409803120045044240121072166066081800c1d4888142e008210550148451303501c01c0b20080e1100c00200340ba0100b84104c140210742000007801c40e018561096400082d40026585056604c04c00c1601c0c00000341c40c40c05108000000c3c0108500d00611080c5070808843c5042c0b08800303068854000d1506e051003014064031060b032440c02107a105111110040d060207104002c40c1058052548030400c070421045a2418010000f0959104022031001601c45503500d080c03a08088000032000b4050302c0380304907001030700c43c0b00c1c201c00103000ba07500701e0001c0d801c2c14200c2010340c6840d04215406206900080303c0c0e250801c1400041401d2004a83d8403119000412522210040c1618589461640301041038081d44001144140c2d00000441c0502945400c84040e900d5601c01c01046501521004048078964822442140c0c02600822426081414046e0031300740d4034404102501e460152038045608060304000400180001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829547652 1250 829546402 829546409
    0x30c1009090501240320160605130f0327080d1d0d02040504111c030305070906080106120f0c051c0903200109170316140315040204030c140109 63
    0x44400b4104000c907840a0b80a200864460400d61101c06c00d00c209583e164500000c05c200b444050b43e03841000409502a42441380100c0c2d82c103060102050b800760b1303c90881d005050f08840e036800e01d05240e07a03041d581241000d40080350415104111074580c0c4d2a043d008000f042844041c2150013854000103002c42c8008210310f80071716805548000c6c2d5180ca03400050071a40c141c8002459441d14184403156040380d05805501490701c180705800701ca80d2a101074601c910030745062001c0c6c0c54581c0117a030800c01790b000e400c00062541d0b00400015204041d600c401e410303200c80004440341101d0200c0c050b81c4804240d90302040300040d107240b1102440412003074030850303040304004040180d90010141894800740b00c0e070091381c01040064000082d03025001265104846002e20a100303410102c06402c11104104255040d408905445001b4031080101903176810042e40303942c0d51407031804102462101c5480c2c11a41c24803020000076000c4103440c0240180009416201c41000f000500b007144d50380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829548902 1250 829547652 829547669
    0x10f11161e0f2603030403020706110102040e160e03010e0c130209030307060e1504030801150206060108041506080a1518050c04050402041112091b090a0b030c1009090501 75
    0x241081006661080d081c140c0703009040c64a040d0260701a0b00416045000d083c004602000092001b0103400042ca00708484070b13515079401e00c041503000d40303080780100e1007408582c03403034500001c030303440c5030740386031803002d0000d0b040120455140e0004a403c54030600320031106948040d6044031039160506c07841d544c003001d0744010352600d0307406030100c2d442e0300600310028029500c8031100b900025042c00304100405100e40c0d02070301d503e814180100020307001c0c426003c01d1450440d0141d00c1c00d1001c10000e10403041038541007041d0f2240d50340c201b410324550a81c401241d0382d4100104000f20309004103042140942035121100061016100031515030034074002c0740900344c1e07441d03400140340400c854090392012200020190f80328004100036001205801c214503400194094607003010700c8040e8060000c40040b81c0e2481c0000c4524602035032216403c0d036016104200007001058607820881a00380050180c1c0c040284140115010600c0f8400300e401040c0c2c240070500c00e01c1010b10031a401494100f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829550152 1250 829548902 829548959
    0x3020a02150901022104081b04060902030408070233070c0e130b04060b040603150b0103051e0901020f070305180d24090827060711010f1116 62
    0x503001079641d01c0039420048400085c406540c00c10348985083c0ca00521401040d2100c0d1440703160314580319410915000d102d1441c2c00d00100e69041a0300c2500d00ca00c4e40f02c82c5891070010b6540804c00050003030000160a8149040364100d030894140c06c45035586036401c1407940340c21591520342441ca2058100c1c0c041c0031104804c0000d1841a00d10320940150808a00c0d40c143d19281000009440040006604a402e00c50008204140a05441c1022000b80f40410042c0b90240c011002e83d04c06440031210540700c2c0c4124500650030000300b82d0405510b4000516000340504c1e00c01d9075800c0300070140d0224401203468a1400e050107000301c0500411501009071090301c1d038400800501c00a10041810210b00d20190180752960004000c250011040740d00d41400c049405921400e1000d00116200c91a052020301c0c2880e1003988d90555106900c840681000001120305010342c0c1030040800800c01c2d10340c003509005100c05c520200e040d02c0601c0c501406c0c00f0019402c8410480e40d2a40180503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829551402 1250 829550152 829550167
    0xb0916230f0319111e090c0d06060e03010e011517010b040924060e16180306050a0b0f1005130b030f0417070b01030303150e1005030610060903030e060c060403020a0215 74
    0x2445d0040000c0d01040f18120129180d1008440c46401101c4420346428a080c4001c1241501300050b0740034503904500a103c80346000b103009003603e03d280c48035500106100d2052000082c14810302c1030103010740c000010741e40038050000b401c0d201c0d603107401c1e144901130350340310120b0462401d5903100058411b402404003510701825440c0c0040300600031031094070541c600070401e034032481c001d5008c107107041e81c40300607030f512400c128000305002e075100c09105e442d018080d00f1a0a10076800d41c205c0b50014034138840318001070000e42c0c55504c40e5488e0310180c900207d010403030500003030245000f50703940c2c2d00b481480c0c03400313150a40a12004480280452800340000b00000f00d0007c01c49042d294180307404141444400207101c20003819400600700c22850320100001c500080c11501e00301c501c00c6080361710baa126109280100c2406009240000354800001d101082c0508203034003050302c2c0034000b1450503800c0405241404010344048005820640b050001c4d8580103000e0a19200602c4041e89001d04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829552652 1250 829551402 829551439
    0x1409090304050d0606050306180601300804210308070804021f1b0812070e0d1707020d03081e191e0203040b0916230f031911 55
    0x1070381c402d41d403042c400c0c0302c60001040010b40080e030044c00007404540d4242047c080481401c00e07541c0d2202e1040c80b403c0000a10590b01800c0f68400340500d0f2000403070b40300710313601c02c244100d103024050740c4102040000080401c41e0710594141d010010b54040d4042d48e651030001e160320802740604003040450020320026036110318051305600900711409040c006802819078092840c0100d00300000c8005011301d061006d500001d00c030761060010703003084540d20301c0b009030341d80c4980d111015000108034944e0350000d5000c4402401c1810b01040240c100f84440c1c0c0044d10402d00c21000314002281d040c107101301c48600c2a10300c070502c200e101c0d1901c0945403454811148500359051424540e0300c1c0e8019986032008a50b480352100d05a0740d081d55a4a041d05001113282000e83e2040e0b458425a40380215030750141301d201c0f06441170b40d044c4101d100c8000790406810034400309210303441101c0c030000103070ba9a005c20590303100d00851130f00320200c8541d90500140300520322141c02d00451001c2e20b00c40081d038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829553902 1250 829552652 829552657
    0x4031514013803010506071b0f0e010e070c0f0606150512071d0f01030f05010e09070603020c1c120f0e011514010323190e0307170a11060109020414090903 68
    0x2a801c0da50a030700d07180381d0704080d046521950030907004234036586000b00341008c880380d031901600c500b07048550569a0f9075201e0039950702c049074080d0004140003070f458001185408070001c1071303001f90004100103031600000b0b02c644240315008000300d0800070300c01d00f506480001059002e0031038181459103001e481600c040708107107190703100d04c140c000c0325003080300d03a01a902c240c1e062140d0050801c0950703100c03810300b501260162024030a03885120000200c082c800e008072540d850760b60001d41445074480c00c510b52010303000344603c070a2083c402c0b02000e414580d0312071015001c41f402004103038121688040741c00c40d0109811003100411502c001c0c0044000c1802c1d4030030a031000c0c40c001820303c2d030342004145000d5100807881104042e40042c031a10f07004555410344c144480100801030b02d500c81610999901c9040380003444410000012004050303201d028001950103410035004524000c4955410701e14260848890154045814040e5102c03c56030140e006d0010703113106200e410148a1070b036890 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829555152 1250 829553902 829553909
    0x80c0a06080711030409140903040612020f0c0f01090318051509040b031b03190f031d0406032108070206010e06041515080901020f0403151401380301 66
    0x714901198407684568031918095a041c0140d945442d244d8036103401500d070007134590b140c10020001050703042c03c0201c1203504540b2680c03030361a203040703110303444801a40221044d403111130790034030010500550900c1440e4102d03030b10400018144540d481d01601d525080f4001d5041c50000700d009001d562601e441031038003c2c5000c000701e9220003440b000100900f1404103680c0d014015041001500c01816980c41480c00040341a2910080e03a40c06404507113501c03003800381840c1c1d4510703020f0000c00e0050500c5402c00000e900d620143c82040d2002c6400e64035950310031209800b1055010a241c0ba80030700442d00c0421500d400d07d06030030a00f400075610070041c01242d07800101540814019a52503201b6000020703900440c444883d0344001090b2071500c4042d4003404074201000041d500c00041c800c03602100211142141042d0940e01c4084010750f503014414080c0b66120310089003071070481e038183e00801510350301104100041c035002280808922011910040709482000e00c41541c8042da41074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829556402 1250 829555152 829555157
    0xb0f0702060c0703140d0e1009030602070302010902061902010f02090102071707230f01020c0303190c0219032306191d06060120030703030902060f16020109080c0a06 73
    0x195418881d003a4104403d41c1d000030508050600300680080001c81c0c0c040d510400751b02c540204203038140510524800b00d03220030380001d851031028000075940e9400740040c1406440000b03118482c0d503010604a84c0072190b20341081004154940710541c1c240940c41c00c10404280030350030301015034000303541c07110300d8040d040c4500c0c4900302a40c0c920b142040400010000d0030110342030380215041040c00c184002c5c040502030540f0a00789401135000046010b240c08001d0011880c1c0b21520840740804202d81c0450402c0001451042016a865641d05d0811002c810710310f0b0042072940c60310b243c3c907600b002d02000c0a4840d09501c2103125001154a507480364501c81d44401010108480c3c0c0d00030040344424800c00d00100450319142c0380c001661911941c800c2e00d03550400c1c2d5409403040302000032500000000d500030024400003a110350043d00815101403c41030030907040d1050b503100d03a08114469200026011015029580d0000d4024011f19802010b0b0040510100100d8150710141c01084207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829557652 1250 829556402 829556407
    0x1b0703111c0b0406022808160e280e0412030b0103090807030908161a070201021906050a0b0907050d1e06140a0e01050a121505070503100b0f070206 65
    0x8401c00705034041d000c980c4548410002d26040c030304503000b0741081501258210741040702000e058440980440b41800545807928281c0c1c803c101010755101050710309041003c8a10b41382140d0303c1c2c00c04829840710ba540d1414051007589940c842842080d64408508070b113140043c0030201e410b00c1c490440000040c0f4010411819141c0160b01514a001700103104540004590051541c0a0091002d03240f40720103403101030f8106454883c5c41a0f80e0b01a2228030f123500d1401100c9034002e400100407071881801a00c2d0110105069164803004880307083d00c0d40c5865400300700e92110382d4481d612814404441c403100e0740c1800103004056000b4030103010405581c46e1800c0c0d180e441000c8000c10003d4a4400600131181c4030240c8060b03403114600c00c54001d030000031011407100107040303806068813000381018910524110031441810070825064403802403896407540c0c48551400307158499516915040c1e66410418644940744510b0303800b40491000a03c6a241d58400d607900b00c070601e40d01100c0c0c007038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829558902 1250 829557652 829557679
    0x1b08090106050915030708030f0a081504110406090803040303080601032003130201020f190213110406081603090302030f07050f0d03051f08072d08031b070311 70
    0x14014903241d0407469000c000681004907500f0900804c6022207829804c0e42e0482d50780303803045507a034060b46144590807d010f10148060354070550043c1d610001e40118107441c41c403800e01250480701c00c807034042c12040000034103101d601d80185591000b8012200114509481e40e10000c0c120200900454100740d203414121349801401c41e101000040880c581c2e035920304252690506a10108604074094040e40045c0310702104045403001440905051080c8513100301c0c5d003041614121810941c0300c2c1603450411400744054071001d80090040303610b624602d03040c5016100c2452000039042c0040500301510880000c1e408015241402c598102454684100f481d0890500294095804240c0304952404007601e600d50003507800f80031812a4418141d004840450095a0b6405101501e0384880010000d00c0c106541c43c000000d001c2d002e919400c0f40401c10010f0307034881580101001c4e400420b0740408401144d0868041034486030050458030319507a260868031007001c850740d110301c1c80e33040c099 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829560152 1250 829558902 829558921
    0x3170a110c01170a0902040c09080d030912030504020d15060303121509020901141218060405060141030601060516120306030b0a020d050c0a1710080a0f151b08 70
    0x4107146030300a07c244015481d0302d4005100368120f10958620384115038529410030300900c60dc2101a400c080c91202c441d00041d0103401501001c0c00483c0c010108040c180045410030444c01c2c10321400100124034145076040050940c07a034410000e10440c0781c01940f075400c20410f0076503404c40f84002009038490801d000141c4c1c42c5004241c80300160140040d51011540000340e041d48a0350440d03441101300354015003c14ae4900085800a08070fa001e0001889191030615403650328420040105984000f010f042000b910040c2d070409a900140d01c0440c40e080c030b810700105024011a28080f400c0007100e0045181c003000c852000741251424078405101c16100e500044040d5810007440403450402c455010025800303401c84a1481d4508404030701a1070001c000c44400354100d81e07642120026110b212400910090f080803050800510000350088080c40300000413806007400b603c0c40b102c80d04000440a00250b1001c0c0c16070301d000301c442c0a2840401c858014086540341250496a500880 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829561402 1250 829560152 829560161
    0x12040f11040f0f0509010c2304030f0f0209060102010b0f060c030708300f0f091c021e0106151110020f0a020c09041e060603170a110c01170a 62
    0x8158000341000728800001c0700503049184030740e0b4080c801308180d81d101c3c0e40043c00c0700c6016405100280c030394200701d4101080314a1080380c080700c80361102d1a1583d40d96916080d00000d00080320b148a030740400700150f2500ca2140c1d80d001c2001c4c0028040e40c1403980009010140c16001c0d184034007c00700e0036404101007041500d1025501080745544c9895500c520354149045076a12089025004e00714041d2103842c49046008a01c0fa070300002c059191000d10b8458480000c120800c1072044841919103020038000104100503550050510100c401c0201c0c1070007000080301c0b200076810f10804004d003a0060201d00e4441c03c3c81d190070b05082c03d191460300d050040f070384425910b480c00402d00310501d0a400c2d000348600185902240d00000c000018810f03040300444000d08075920790036800c0b100c51694050107150b184a079500241c40760f203c0c0d0381c00a882c0705884544060b2407001c14058071094000703001940030320b40100207005000d10200020015800c504419044c14105070110700200c2d0706420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829562652 1250 829561402 829561433
    0x7020909010b0306090a0b0a23040606090b040e190213050103030e010306150221070f06020304050105060604031104200a0f0f0f0c0210200f0d0512040f 67
    0x2040415051414509020300040c5400d54424020342020a440700c000081e81e001c440d500001c0c070025969094413800042c0b00c103000f42d8200b0416440b41303010741300c1c03007901da1442a4410000010070701d0402c0b540c0301c1104d0004203514062403030111845440100024000743c0741300481c802c00c8041d60a80302044c045041c40c0070101c001420440040201500210000c03c514800c0e64200419036841c0c0302d412481a0700341400001d600912003c841002d44000e8480c1d00740040c1950918001e0307203540d2500071414035070041e228954080207000400a003802803c1d04510304803161420700c0d05540790110070054880c030041c4a641e803031210401c1d0074105090512100d40440c0d859844010075600034005030010741c3c80d00c00207141041e1140c0d6182c094925004c940300f0503511912032a000e9400d20204c450100300c408140410000c2082c0b8480d07a0850101241281c240900111440c0c1148946000e240e01a0401800b81c1401000b84244113040502c0d40181c01070b00301c0c00f0101c8681003d540d1549401c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829563902 1250 829562652 829562659
    0x30c17040f0b040b07021506011b081b03030a0e030415030207020a050a0b0d060501031a041112011724041211010f09030908070b03010b180a03120e0f1c0302030702 72
    0x1403c000620a590709441d05c41d000d9030302036522114806041c51203681c1e048680901266007000070b0f21403a2382e00452110554400c0c030003039140803004608140c0505230740c007240105a0000041001c000018068511101c100d0b81c0110304040c2003101001c00184072024a2081550108403003040d50b407044400030051401a021059041c0c9400e000e00c0d055100030303501c91100d402d1070400178407548070303100302e2510482d040c64604001c083c4104203c041c1c21180f41c65921a0014410220b4040c28078849500911260f1801c0c00008200680c4034200504000050400e40c440303200030b1401020a40d005034083d50016005826655081066506040b5524007100c59803a21a5100020980340e02641042e80070b074682c64a05070b036510810782e81d440c82d0302500c0c507580030a10042205100900c05094400b0300005030394008604100030494800c8954425500f10300081d4507200d0140d084011803407004010754030407107100e80e110302191440e800b1a80140c16410b4412400e814188280140c40e021035005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829565152 1250 829563902 829563923
    0x13060515010e0307060e041a0a120b070212040312050d0606050405030c1c082b0527120d180c0504051e0f1009020706150501030c17040f 60
    0x2040c10601032648490460118041000c03000305403a0000700078046a94654030039841081d030b08140009010620510100540f40b00c4c2ca198140c0e59800c2c22030050300200c015905100001d0903c1e5800550140600c0195001000c1300c0300c24907092001c40e82682e400080b90007203020902d404540c284961740c1451003403440c2040c08180030754010010f104590303003142201c5400c164071042080103c03098030202c030004030030000c610001c0d00c0c030704c0506014540032280c0e410341c4440105210700d10b15160f003d5038a465070b8100300209503401c0040c842e102400c1c00b4104259092031201290f88140c0110b01d030480b144089001106c0c1229500a2401d2200d031401c200e40c15145c1c0d00c0c0c20351903040140a850720a42c280340c000345038621088490301c0c4100c91080380c44565220fa240e031941c5441d0251184001341e210f0000800c61000300d000a280e071903c00c2500040c042080c2c2c042030100c40e22a04400e0405041071124441c003903101e041e00c0680210220b180794181c9036860a0009100d80010041508840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829566402 1250 829565152 829565161
    0xc120c2416030905010302120f0a18050d0801091103070c171605070819080d1407020d020601060e01140f13031a0105040612150b3303100608130605 65
    0x400080325125100c1e4943c3c0b00440e40310f40c0103406138003480000000310950703500012100c4100e0b10019070868000707280010f00300c11041100500c411146021355941d031051640206481c0c4c81422140180b201c1c4808010642160111180c5880007410400c00c02c0b0305c4001e218103000d8000d028004002d02d0580351541c90ba0002088245141010b0050b51b241c028064005035050011501c50700030071303030016010402e454503030720100c031034110404075030100365203641040d00c50040016407801001190024844660740b41030003031511405800070410001170b0201d11035a039820446440c1d40c0210780a00584914080082d12070500400202d0b032000c0b04452800424440e048070701c0c5854510041c41002e00da0780b598248801d031002481400b000701d44040d244400301c0c160230140032100705400004500c0301c0e04600010001c0c01c844542d009410601078001c02c0c01351034207001c82036200c0d4038002241949000f005a00d00040c803440f8072014021550005a003040100d685803110f190f000c803040015091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829567652 1250 829566402 829566427
    0x40f2c06030c10022505091303030b060d02030a0c0c021309030e0907080910020403030e06070f0c0b2d09120f071805070309020a03061a030319020c120c24 68
    0x58402c60164003031003d41d60b001707401c40104040803c0d59405880a40907444444042011005440781542019130790000341c486661100001e192074808014003503124102100c10000300d8940001520a000a0302c03000c0c00182c48880c050342c2425403200c4005000000746c203060b9814010762008643c4421281c08208a481d00140c0c541d0059801204032011000200d80c408101c0c440d0b400003034081488500c00b078125150900080504611400c0b58082d030813a5640d80350740d91021500a4080d124020030041b04800043d0101210040108034143e940c184035081c044046c81039010301c902a4445e00300800120391304100b90b1744144009000c40c2e19081e511200454012441c5214079902414070010500213807082c0038074161a90020305000d4030b5469552004010080c0201d00e640b26041c45040112542c9c051004d41011040d005604d80b40520403040241000d442c410010b05c2544080b014206c000d200080c241c1a2031800c0d102708000312560707100e114110003043c2d0094242040083c01c0d100024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829568902 1250 829567652 829567663
    0x160501090519050312180604030f02010c050f1639060f210e070e060a0501080c07080901030b0a032108150603040f0c0b040f2c06030c1002 61
    0x14050802c0d00d11001a40001026640220101030004d500520103c3d10340888049074580001051701c0d422800680310120500704030b0112420340100d2420740002400b980c082c001d5a0042040d40b800c41d141c00f8a0307084200b5070b8001d042a0307180004008100d1410450503503000d00c3c80d10000403008189040072000044206500040c2013081d031880f0300e00181407806603d2402d90070506450711008000c050101c8500c0841640075581c405440382014a6070007424094400540009655a500751500509010304406268000c030304201109042110316010749084d2402e01d41d12051541d501c90700c04004801504007000e06d03071b41c403005c480b500004000d00908840d251641ca540501111450b42c1b1080e25003844c200c4440308046201e2440d10902d2500500071030348144104050780300f103031007070301c50b800c400c081500842d070709100000b000c0c00604e50140b505d100621a80c0e1401c900502d4600c003c807401032031800b01c00382d50b008000102d00b042d5020311110906402c0507101a80001e81c5000c0207540c1c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829570152 1250 829568902 829568921
    0x1090c1401020c061b120c01020c070e1605030c0909150301050a0509030924030a0204061b050703030f030b04050709050418020d1707051506040b0603060f04050606160501 75
    0x4144034080e4504079400414002034a4030001c0401e810414603800c81c0c12184c400e452100280d00817401100c0c0242c040300050440203600100040e110840001c9461a044598015800d101c54140410140d4041c0d035001e024414880c0c81d05075100c1d01e44041e482010b000c0c85682c2035001e00c02d03c08020200d24250120010181d04400078061900c071a0f901204680040c0c40102003030300100190740300b90602041da402581c00c1d03109800c003035942d0308003403181d03170741040e560102c55130340000c3e040000650285d1340400c04200c00e1120400c1040507617074940e44241c030f84401818420300116040d0b403103020780d021040140000d04140a42d240c6220010144102801030364421440c0c00c0903e982444451400010942e01405007010000a038594007843d4050310b10044000c40c041001c2c200080092003140c82c0d80c003d110580159007000c404000c00c6d9610b00030b0050045d0428000c20070165200e1150000c82213094030001116120800482c005218010760010780341c00300f105040401c0015032060810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829571402 1250 829570152 829570169
    0x501051b070914010e040f110a090504060203041208011217250c06091d1f1d0f0c0a1202090402160b010806060a03140705040c02030a0f0315090e0f01090c 68
    0x2160389030021310400c100701b81c801400303082e8050117101c001140910715040310b81c0001c3c11680d00ca03544104220540e00111011a012038000c81440200400d66901e50201a0f85007002c4c0003070b40c10303c101050a00c1580c00701038600c040100700c0b0015010840225841d45a980c41e401c05800e0040400c1c160783d0a01c12011103400e013502c0400190580700b102c0003001e90310030754420081d203034042c211481c0c001e82c0038003984482250859481d14184031030f03c3c0701c0000c00071603030301e4500c91110041e50b0f411108010078040c004002ca6003040b050000110448060b171aa50070110000c0030f01010810003406442d04040d002440042c41002e901034841440d8001441134406c107043d07070389410400e81c03584000c0d20000d41040110100340005100f48502c11821008002140c42d4940d9980c0043c042d81c12b05840d81e409600001038145c19140d2010040348a60f516007014008203604041c0f109a0140310312600588680d142c120101e0200c00b8000d400990080c040240540c4905040081030903005116941c40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829572652 1250 829571402 829571441
    0x70f0c120302070e010f0b0706060b070b04061121040c0320090903070503040509130204060b25110f030a05100e0d09120b041a1923010501051b0709 65
    0x8a1340c80d07210b140b034107844181d61018030080c5003010800050300000001c8030200d0301c0d1000401c292152401030300320a401a401088035080508206088070012070b00b1107501401040302e40c0f0000a45000101080a03404041046a50390b0910810000668100505400104181e41d900d01d51010640b1526103044809030034940391494420354074070520308006c0464005000c00c0286140c1f180300c0c181d10034016040a04c1c0d50025500040464540b0740046000c040040740711070039800c03074a28928462000301034035000340704641c440150b411114010700e486442c0e5507100a080f42c034140221444070364840c08541249500b0f409500203015440c401803c184120225240300900c034640e00c03000c0741e92620720700b095021281c8405c00d03080340050082e180070340614030070387c0d01640240c070013031048861038000b400c1e11030000394660542d42501c44040c80404800d40304156404d02505a6044402c03d080aa40c1e603003180c510202d460040448100481c003c001c0000b0f5194199007140c0b1250030503414600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829573902 1250 829572652 829572659
    0x1204350c0d0507020a031211030a120c260a02120421052503090b180901051905190806010e0403020607050f0a0e03010e01020d140601081b070f0c12030207 68
    0x448078000d0107000b130345c44541070000b08042400061a02c24404892400849034519541810316561000701c2d11000211260a106c0c50003225115011446881e0b1410000540003241c140402c408001c01000c400b046040c04542c40c0001c3d40e0488400e08800c0000030424981400c0158031480e11002c8090103001c84060ba00940d8495401c0310301001d6100c40c44501262740c45e13007400c00096982412001e1107491103000c01d10070411400341803400d9110700191000540d140c180203011106a0140740076118110401d500000c05081820a0300c1c000d441c40b020420b80c03800d494002907031660040941d80114000850103410544090f4442e90194084800d02d03210102c0840d1588591f15190001400500c04200c09900c01c800070740d181d400040010500b0103610340c006003264020140700c56102d17504c003005041d11980f01d4440d90700440900300b40f841e0745000108a4500d408501b103405103594006503100810810044000e20036800c50003660500c3d488051448500401c4074055015101d81103000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829575152 1250 829573902 829573907
    0x180c030213050c03070305040804090608030c01150617040609140d080708010302011d040e010f0c090b04030b0c03040f080307120e012703120e010617031204350c0d 72
    0x740500d0100f840320386943d40e2000700b10002c0c00c000c0c00841f9042000c0200060601850140d8009000450041c40d9181e080150b0203023100e1805c0134000400300404000c024075600a0b6004818021301d40c0950560380d55407920000130000040c00400c2c0484513151740071100c40c00507003512000300680b200c40c1c0ea0340315028180c032044000d00c0001e00180668001e8440b1042400d40e0700040180603102040400c5608401c500792594070740010383d40c81d901d0985a54955010b4686402012880101072902d425a11088000f4800406140b903040000000c01d04000c0307a5514016025002414203842e0f00302420028081292001c61220182c02c195013070300307208010722640120702180100b01381d6806084686122902c4104001d070284815101c01c00e00d04002c0d401040d14500c164030001884504101d0111104611510002115402817268007105581100c0d941d0f0000c0d04045403000d440e0f2080b2a100c52451440342c8100902c21400c605083c400c01c84000c1c1c9001c40200b810344815071801d4404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829576402 1250 829575152 829575161
    0x1b030504020a0605161e050d080615030c0405060702010c0501060303050306090105061201150c020d080d2003222003010609090206030c1b16030b06090415050a180c030213 75
    0x302171241c0c0390360048000901c64191409814160031940304016a081d10361504004440c045003001c140f1a80401100d86800c1c00d07403028021003e030301c2a0840c1800c1d40080d031680210300405000e41070029084044d07a00407001c000009501c8402400070b26100e150090480d0401e50b4850700804c1d2402c00400c0c0fa2910345c0a5a41032100004406a10380ca4400d03000803000480302c2034018800c1c01a01e01000d03854070784440e080f5500070301099a541c0001c010490803101c00742040200324600c601555110010a01126088458074050914400030f03140c41c0071030304a110740f005002d6040c03ca041000c1031040c4071701542d8458100c000f0800c050f07030348105000b42c403001d01e0025400701040002424607512007018000360503500c000c809401c41c522071a281303404030318004000a2604131608104010983c41c0c0f1130b0740f080c0242e4086059041c59078901d50111441c031541c9450760b8541000489600042c4c1c0106414180c010042181c0700036800c1c008001748190000380d00440400300390140007080d40c00b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829577652 1250 829576402 829576417
    0xe0f0f16050a24050f0d361101021c02010509070506030114040e0a080403141b0616030e0a060f0e09040b04080d1806020405040e0c011d0102011b030504020a0605 71
    0x14a281c1c500104140f000669000481c601c051040c18030100c02c3e82000d120280903c0040140d00048420112141410841240c6211240200b01c1f50030203042c550400000b025195124120003000d02119006034103011350744408502d0007410f180c64011031541500128000c02014041e10240da44034400e000e0184024010b41c440d9040c884812804c030b0600350300800c0080c075504c0540b1403280c55030b90b9504596119603c10342d00c488a08801c80080703030007804000c400c0c622004c003480c8040d40b0500850381d41e014100311506014442c2950205050042c841307aa55003200414005085407688405040401a105040b0001c1c4110460102c6814404212030203950030101001850f030b15a5510400c681c0724a94105842d61a40740305481a600d07031b01c102c100e16106081c056212818030b424001101c8019001c1c4641d80d006180c0b200580e44c0007100b074a0009100140ea030100400280142d015008100e810b142c50141420a00145685503018901031407085131003035166076585a0407140b82c040c0d2314 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829578902 1250 829577652 829577669
    0x328020f07230409030c1a0609130201030209030d210506030601050f360a05071e0e060f030103031121071a0f0601080106031e0e0f0f16050a 62
    0x10500541e440410b920401e52400c040440d1168001c2c000b15003599408001200820303280759061040200101251180d0442d1040c0ca855078035000001844000c0040c0c0000503400495200b0000c0d6446a0101c4512040c042c0445030b130000d007100010081d0040c1c86814031074001604440c100a801c7d40209030084000400500d49a402e080420145411441d0a580d00c11600c3c0e03072602000d801d160110983c5031074101000d03a45044640c0c4281c00c543c0003818018254540410032443d25082071100c04071080e442c81c54035071a0164902034400d8800c4005440e0302c201c02003188a070044030a00254103aa00c039a07903042d002c2080c141c000d981c2e000b0f1001c43c0b5034400c00103031414041014074005000c1150190400c0c400c102c038807801444070750070b00343d4420000700a00d104024032941c004d155280100540d00d820018205001000c00c0941c9803603800503070060304c8682d6090384a40030040d11031041500d0081c2d0360310940300102c444c1c0c0e4110960450300164584000050f20313161100f142000c80300c128 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829580152 1250 829578902 829578913
    0x80610090f05060c070f14180103031d060c030403061e09020a0b071b0611010b030d091a0d0518060609060a0902090d060e031309020412030f110328020f 67
    0x40100490f90f082500c00280f036204004000850250411900b001070500c02e4281145111150600040c0813541d140d4120100741200104006948034030300d0700e00100503403407004001c0c80c40c00001d0301038070a030340003041d440c0b0021401000b805403951294003040d01d1881d032040241c00f00f141d06000d68803608800f95011520038000c0121800d800e00070701440c0c2c4034813201142e881d90031001202000841d0070030800910034079000d0b40780b40c0c030921660061190440c02000e440f1044100209000c40f240182a000071030144100c480005400a5603102d00000c8020f1003103180c201d0b0391009101c418569402c0c81d00c0360802042c1141800d00031a8000d4001802c04e03040c140c14002d040010b13621003115a5080385550816a001c01c07810b00c14141d070b042031480603554581c2034108030859041550019542c442c4100410030411403007400781c0c018a645410708040c00d80050300140c0710103904161042c0640000034110350400705901c440f10000e0320f0051045101a8440c030100d07a5010464000138259209 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829581402 1250 829580152 829580159
    0x6090512031e070f08040323072d0e09060a020f0d0e2b032403030c02030a0819110c0907081005060c06060114070309062102030403080610090f 63
    0x208045500d0710a00c07040305181c6509556182c402c4003010f0b13800e0752100d1010406204002045400c0d03a15014800c80f9101e003045a40d40340d0307454000903c651080b030030005060388000340d4080c41114841a0550421408a07542d940020101c4000c80e500d01481c010701e0001024040d0500c213030b62141c03040c3c1d1070369414a000a09001b0082911103a140c200d0f20500da4000121480000c2070f140070111401c41c03841c0701c016000d010741074030642c2ca03140746844c2141b00d609a40100d42501c1004503038152030105400c00a50010a0038102102d401404003040090503001c481540c00c0908510229555000034500140949a8540c0c003c0b801c1503078810294004203407000d108211540d04100020b1401900c42e42ea800000c0e1503a01958440340940c00c01000c2082a43c3c0024807d0700a111801849140c51074a07a002081f44e171142c05004184a40441451a0a024001031100d00c2a820104540d80e0400b803c4c00781c50b4a0742201c4c035610460550080d850454801d211240440701c7d52003401410504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829582652 1250 829581402 829581427
    0x1113061202040803272b140d02010204050a050607081c0e010e070e070c05070b0c071a030a0b121902042a170705091311130609051203 59
    0x28a1580c80818035000c1c407021407103030000c0c40101000c8403058040a035600d5146906002059566244d6200e0b4103006524070510115440400b030001140c4a1603940d94100e141c0703820611105a464800c0d4850310800480c1c0d560150f0090095400495030110810741d82c03810000a0302ca49a801443c2c0300c0306000d54140c185125501c8000c210340c0360008174195150180c45821602000f48801046c0c1c01424108003221140ba01c2580011a6103400d13001c800b4540c441c2542c40300244240011001c00207012803510005101920142031084c81d0340c601c801074008810f042e50804c2c2c0310a1400da15041d0074850340d1808511540d401d201d03030400303003642c02903080c0b15080644800310140d820035200c04030b481319000115100746030303c200c002a1703042211005000515841c40402c1c0d65108982d000140b1210a811005440030010202d83c0211001c1280d41e000e40a802c00c840700d01e81c2140081030700008205001c6004c030a03078056a40740004140d54404000c0c00d131040d03032880d502c00d810070054940e43c0c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829583902 1250 829582652 829582667
    0x8061302120c06161704120305070309050a0906061b02010e04020c0c0402040f0e01080604200f03010c02010e10021809040321020a08060301020a0e0f030a0b0109050a111306 76
    0x102103420b940d80b00d5554004120113612148030141d24001c0c4261080c1001159140d04a01e82d440180b602c0c05c2508026030050310460b0084007405202000c10302c80c082512131510748016180141402035059518184030025103484e009070400304841e000030810030b000c0c20011400950f016524007100000e5001444000d6001e122200e005000f40315a04210b9200ea0008100401c4612000c00303030f240c508142822480e6043e0420300030394011605100100c0c0601da401c0f0940c0e140500b021801204c802c001030456016030f81c80d99010750030102482001c68041d4050401c040070078040e03603929000d5011400484c461408807030740345c81d440c010030000760404041c0194842d1290510292000c542507114076074218007020a004140c000840103901c6520409658000505030000d500740444080050102086040c0340d60183c0c00e2480c01c0c3d1040d40e01048410301090b00440060b43d6561500f11a40292208942003502c1ea801d010b41c21180d030742c1001c00c880014102008a030380c1c1e07905103101101c140d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829585152 1250 829583902 829583929
    0x10141011010b06160203010b010504120206030c0d0e10061403031905040b0f210f04021e0409030c0b0f191509110d0b0907051c0204031a09060108061302 67
    0x41d9030319441985580c482d10020b10490345032109640515100744101800d44126800d42c50420009000030020710340c0c1c01038105030190781102d00e161640d5400c10180c1d8280140ca5000c412503042000c2d51001003004528403409d61100742c800d00c2055215a49042e0b000c0014a0f0a41c2580c8200a042d00000c1903071580c00c0c0150443c5411440c0c00c2d504c134107800c100e0704009803d2440c21000036a0b12103140210f103450240107910082c00607140b900350404007028400403c06800f94500f0b500c12080343c54032007800f209a80009004100040041c1001094814020301c100c071040c000310f021442c0ba40008880a11071403020140e400d14810028520300501440780000403036061003440843d103080075001d0880c148504034590f64a6602001c902d0056035459442980200c003600180309500c3c0e40f080407519840e5880d001c7e41c8076040c100500c01c00900c03030b951000c1c18110f100303180d1040700881e41d10050301501581c411298240d072107540140d2181415258100024411100e02005080220404420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829586402 1250 829585152 829585187
    0x60507080c0a080a020f0105010603060f05100309080d090c12020a03170c0706080a0b01090302060406200607090e180c0d240e150108121b0a0506101410 67
    0xb9400c1d0395014182e8200480410150300001079540e4203007002d11402d40144890f181c10b002c80b520b0000b204815807900c2c003079240150350514905a09a001e0742103507407195030100d00141d1fa1000301040380020000c5050840310304900f50702c0043c0a0700762884240300d1b250002d0410180510b1034be40d603c1054000008266414010b13c00070794a0300d01131000000803c010707107a22040303180c0b490420301110011206d03181442406402800035071940303401d44080c0c4040f402d00c05035058015442808180380c19400c0c1219110b07840070000041c0d841400c0f04100c0d00101081c0b1603c0e1a400e03041111440b0743d42c0890650703884032a00716054600301d0400840c080c040c2a03210241030709950789001208010036200e0b420780d1180c0180c81c0c090410003030700d0340d07000241031448103a504000c44071381c4074491340c140300e8003a440102c1c01c02030f810710404c1d418405902a008032003032505c00345441d90315050101d8211980d21896500010341e81c85a04042c022103a0052595000c84840c05041c0c0e072903104207545000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829587652 1250 829586402 829586413
    0xf11150a0b15070c060305010e070804060209040209270609090a02060f120a0501030c080d080f04060e0a0c06080a1b08040302030c0a05030d0c170a09030e1c1506060507080c 76
    0x411500b51005001d03a0740a8080c0000d120300b0041c0c05070560b04182d220503500e0700c90a08010256522860036500305920002c090b9440c040480043c000c0d0003407900d002d0340901c015240c0c04488654500c1c1350174206d00da1004842a90741ea1b0304210200c142210341000f00e40240d26a40300519100c0000d01c0c01c0c50b10030303028500f8803828102d0313500c2d02c2134200c4956200550780c0340140b003442a065041002095400d00500300002e90320001058180c010b00720201221011001c0340410030180c0048030781e1994102101c0380744000781400d0321501881d106e210081564800403034042c245c83d004412258201988105042d54a8002112080e500a01c242c045020500103808202c60034401d02103040d000383d00460300d0340c1b6402b9038003086801c0c260444007030218140c440c0980c544256070039035110400600c002802592404d040c0e580b5030300c03e03000d142c1c461016a8401c0d03001c296110b07400391580c055110444001c0900001d4400c0301c00b0b600643c03001c65810f105407800a03005000405800b040b1006807907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829588902 1250 829587652 829587679
    0xc060706090c0f2c07020c0420070813050a05010c0206030730110a020c1009080303010e07110a080301050d060207080f030618040f0303090318060f11150a0b 69
    0x180400c1113900000d851291400540541c070f8144021088803000c0c0319041912420f04101c0603680c0c076900101380d800340e52120341c50100d403448031184529900b018084c0c5a55802c1a14040500d80e10089000d06408500800481c541c1007480c1458180d680684405030302403015020000d0316000240403d0400520305e00d030032a20032218000c0d1301c1c0f400040d5a000604185031940c1e4050300c0c0c807484901240c100503c601080582e0001d5028550b00082e64207040000c0005e0040310f800086400840051000100010704070180000c00e9200302060b680c0e842e00ca01c00901c08030744a103000300d0b000d80480b2062006002c00e250a06030b03002901c0c841c0d04010302e41140c642e1040c8aa4004048840195101208002c418100121083e24880005030100300a1034141d4503e0102040d1003406003c15079100389950400d8014001901d00d00103130342e4456207003a56890010032103040190302e1000502e8040908034042c00005804010b54080400760000d0b5a078103140c5002071103002d01c3d11b40d110490f00840f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829590152 1250 829588902 829588919
    0x130b0f07060e0c0a030b270706050309190c210b190207060f14160f080a02090d0b04020301060902040e180c0a0308090a0e011401111c1707020c060706090c 68
    0x80029841442c001c0e03c91f142c0001d2404c191583c01240b05050782c0d10307120990443d4804511031054440d00d0130100c2d26500c50036402031400081880303a00c8a610140742110601920100007800c8408507560100001104c03c00c1c40d0300c2005000d00103110000742c0c0081030002c03400c640100701c010700c440401800d0081a44075402645c0d031001501d5085a40c911103c50700b4417100117800d60200c0c0048510007214030009004000c000000441010070841c0c0e00481c213509640d4048640000c0010902d000056860502c00d500e103900b554100c1c840c0d03107008000034801c100f0380240c0e0200d03000700155240307658540e99985038140e0580120700e0070307005d804a5500e103071b51003d0031703140a10700034000a91215108002d000050940e80c2121030810458001000444000014041001c800381703010b40001011401040c40d14152513190f00d0300d80415843e0654481d07204054200d60200d403400b110481e151004181d0b00c0780980307510603170440020098000030031083c0d044020748a2042c550111030580c2c84102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829591402 1250 829590152 829590169
    0x603120c0c0d140d0e120102090a03080d1b020c040e16060e0604030519030e031b010507050f0708032101031101050717030c040e0a05010b1602030c0d08130b0f07060e0c 74
    0x150000c5050200c0c2d4a0380c84c02c1c0540c080186c100c0350b000847c0380c40301d00000074101e600d19110040c010140010b40c003100c0380c010f0708100c1d2183d158082c01d000e00700044d20040d48803c4003441c00c80c0100e24000009000c000005000c0c03000340e44d00343c075402c16036003824821141840041c486a070011010007000000502c00c124614011040800300c1d4030341c0c03007540340080081504a000c617109500c10480300e00d89105864400c0744110007420072070f40d140c0d8546001810540300300036100e02805404e01c000303514000800101319a046c201c8813110070f1040d18170601c0c0c0441080c0030103002c480b240302800c00c85500400052480b03902880482e0b03000340484d000c448440e801203038040044038010404100e000750074203026801c00f01546d801d00541d8102440c000240c0190b0389010144901c003480101592428070074000c0c09200902500d00d4030a190400445984c03040711030385000c030500c080001d05075017a0426160113440c0d4400c0c1c3ca14087c46522814068180740058070194000d2103065191603075001003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829592652 1250 829591402 829591423
    0xe0712090c080a1b1d1512060613050108060f040c09090507031202030315040c030608030708090906010504060206150a0503060f01061101060605040e0403051606050603120c0c0d14 79
    0x2858011958034010030401040d00103801541d1401e20144061240c00c150404031100301402ca005c1c1d6601c0900003418007500c3c0e4103440d08042008085444081c1c0071402512a01c070079a1718040400d809401a03040720005d1144c80700d0340d001003002c6448000f4203c05603801601030f81c0c050200b19100c034511011101d81480442c0c09602000c8200100000c4c20b581c0444c8260301d00156081d032030403a50019181d090615042d110f181c3e94a0b020700454007070750101000d88280302c201c80d182c00305882c100d400d81d0300c1072030703061300c14480f100000c0d400e58803031011902030724016070150005444d0310243c2409056500c9100358009110a00414a030301d00704183c40c85003003180307561582545084006840710360301410b00341d00c69041c02828007041d0341007405c907000c0391450360350142596124202140e40e030181c5c90b2072000d840d01015400342445082d41000740503ca044054541d40d50769400a19800d2190815040d0540c00444a800781440c0803410354810a0050300d5441c401da540c000c1183c101400b502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829593902 1250 829592652 829592669
    0x31b0712020a030806010507050616020f100b1306050d030c0f020411030609071d01120608160f120312020307020f0609010e19080403152c01150e0712090c 68
    0x1980b40905a10a4901d41c00620030300340a8070b00a0541c40c0c5d0b5440744401000c0c000340da02c1800c46891018401c2001d820120076800940755a940d842c502000900b84c40480d161194002034100042c2680510910003114402040078443c140c240e0b1b4180c5020044650940e1401450b00d000300150b21180244450000c030500b030280e40340392090421030428800780c8504100110011941e90b0590143c0c00b045042400342003007503c450190300003001070a61500000194080c1600c1c92296824460f54a8251800308118030165034683c00e480700c1007002c0e00805000540c40d04009880341d5a1030f070044d5002440c42c41600c4000a003400b0712464414150391a03581603655905032002c069080c841c00300381001e02c42c1d0f044449103454880ba0010701403030002901d0004945c1041c541c10741aa40041918503040700354501e586690107280c06014042d1202d0004d55003040c1d03000141314007080a800945002180c0d04081d83c1301c50300c0c204e905070106a078503c2e420b555104160003007455130841800900070380 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829595152 1250 829593902 829593913
    0xf010303080a050f130206040305120c0609160603020a051204030e15031e060a0f030f030f0203031b0d0f050a0f0c1704030e060708130f080d05031b071202 68
    0x1898024000310000301294405454003081c401c0c5140c003c10581c0d0003080585d002c00b60340401d4000100309125076403000f84180314000e01c40800c4000c000c054001504080c00380d410555901600e107803980345030030821000040220381845818001d40c06428104a24584141031140d030400200c0c10351003d0714180c000c19883c0c18048204d03d0138643e1140d0318071a1030026400c5081000131003041c180343c210429141444d070000214251602c00c1c41100a040d04001c02640f25580c0c01c00082c4038000240560001e0915000c0408aa000101712030041049450f915000300001c0304808194100340c5490798955203814400014448600940340501d03528070700010076051003000d00003101c0b40e4070082018004008031000800100f901e40c2d90744903405061021180e415440000c080e40300350070703000b0800c0308007152040d10501450598400c3ea64400d0882c12019110099191b4510f440d04c411400204104000f60302840440d0b4400c2c0c500040144803424030195170303118100c00501101110040c0d010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829596402 1250 829595152 829595159
    0xa0c06020c0c031e070b0904140c0909010e0910090c0506042426090a060c0507060b011e1b02120d0909050c03040303020a1e020a0c0b0a170a0e060f01 66
    0x14000400810003000f040786100000450840c5c94400303522488074040e07800308807100030780c41d150801c490314002c248840c00c1e0b038a000303528001c59810807541c9034012200440013183c40c07030000d400140202080c02c010310401d04548004c1c0003034605404220f9850301030200c0040ea584a66003d4000b500100b1030340850032303084074020074850f8605980b407010051740d0341901300a0340894450012a1071201944007840d035500b08501d01c0d00303445500042003145419003543e00a98044085e00c1454800c64040c411120715400441e080c0c20503022404540c100e220b0883d0515000349118419040343c9603c5148851071034000510703421241020342d00580000d5101c4910030f90001d02400600011482000241401d01022203540801400101403660026581400e1344c00303a44411a002010390401842001000001b0340b903402200d8101c4400d03890301008504080b45a0545005c00c10300d0b0f48140045109040c0710002c0540980303140c08881c1c0e0b424a80303080d144144083c520420340504041c0c901c0d450f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829597652 1250 829596402 829596409
    0x418060509011109190b0a03090210081b070201020c131b0f0c111c140d02120d150803030c03010e090f0705060904060e040b01031211060105060a0c06020c0c 69
    0x10040c48040540d1403c1d55040c100d800d0344040d100d69031001c0e02e0444085900310f040912002841d000081492404130381e078000c6640c1500b00c401400d00c00d440808441d076051006641e400d0f4161006055200c1820305440e942e441c41001e02a541c2c01441103858044403030011510210028481c1015580c41e01042d200b1010079079422a5004d03050b1400c0710f185210307600c0c000c022640715040207140041c04100d40c00182c0d50003055108911408010300034810f16441e0032031000c1142d40c1c40380018010821500e4032035001051504031820b0004c002885c02040c818080000d042c039081d140209140e284000c03400c0d00040001e51b00c82e043c00c00b291a62541040078010500b1001403070618580d20250b580300710058046502e2045a03401d6075010385031031041e40000e015003140d40107022032010690801c42803000e40c030366150403a80100b014422000034203200301e680d800b68125000840d48002c0040280d428184018450080c00c0d00d8142048212542d408080c0c0e802030309885481d61040c41350741080d26 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829598902 1250 829597652 829597661
    0xf0e0f010b030a0506010e07030615020109060b03120301290a03291305091c03060f09020f0417030f04140a061d091b0a0203040603060503031e1602041806 68
    0x1c0c01100100301030240e5540c0c0c5a99a44140561a03507080350b0000324540c00e001c0d0f007150001e07140d50f612425281c030310010000e00a00720114261040b505003041340b1900d0070081000f0300303020800e01440b4510381c2401c4480d108402a186440e00700d105801400c509031042c1c80150031b00303002503580071851101c21041488440c40c00009004c881000598002950740c41c4c0030014400107041d503001c0b03020f54800e41c080d41014203a10241d000020744003804035606a26501102c1921401040c0043c01130305c44003103408078091080301c0f0f5401542003109200e012080c90a03200d02403c518122071510510142d55196504603520800310f034a44800000221710301140c8101c050051807030881003080c900120030101c0e280c0c004005006030a07003408104124000c1d00c1c613403642400030294a03500d000d0201c000752340c2e41c4140300d2200020f00e40348000c2164500401260070125140840100c200d0008502500640c0f203e2107425060007865001c000584a9019080e121428004546180201c50406c04282d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829600152 1250 829598902 829598921
    0xb010603020307080f06031f0e01140402030a0311010f06090b040c020d0207091509050103080c1204030b0c0a110a03020f0c1816050708030a06060909140a0e010f0e0f01 74
    0x141c01802040450341e4040e2480740d04c0103800d21065080e4507403a01180c108004c500c503030b070400c42d045e1400071303100c00c072540103400090070000003001a5074020015000c0d4000a031b900943c50340017505160f008c03d03c10071160b49001c10880002503c0c1180100c680c00f03c406550010b0b110707580b6000c10048a18080c492180400507030b0020b0800c0c0d01100ca03009480b2069401400c078159950a201c440004c0c0c2011140c010b00120390003005156140d0404183ea40c002d5242c6c50a548a004243c80d0701d031076254103407000c4070780c040d501464540750000008080d401102c2c10004022502c0c40400f18000b0420105800c903020b81c016206190001201c2410611030780f1117a4043c00d09a05405040c4010a9010b07510142d46075034090f4800b10024129075610908002400a08011041c4005032a459024001b10f43d850703211002c080e940c5038203000a030b5000405076a0180414000a2038030b06045e004403040300c11100c00000c2c5602c602d1448000c80d1040302d000d00190380031001000c8012000d00c1080383c90b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829601402 1250 829600152 829600157
    0x703060e06100513020c150108070b0a0f0e121b01201507020c1201140f0906181f02031f12080c0a0605042f060f160c030f0b0106 57
    0xa6290003182c03400b02148902c151070003240c4818451590782c181d42d060350900e1000f202652881c050200701641c03624028020500240103400000031801c0a800c100c1d070702c080c4d80b611080082e0072040740075652030b080d450740b4a0f0002370346692405c40410030300c10b00c41111490103555041d0031001000401828180000488004606180400e01e5200003855024a513038564032480070f640c0c5540403802d08141090546d080741c4400946a98860103401c0310300c43d40c0c1d4415034071069545001d581902002c0a450340d40c1e05030002800b02c0d02821244904118240710070048510306084808241c1c0c904900183c041c070100d901100340030b007095203510031048880e6011800c008084c20507a04a81d00b00007814005d051150000e06d02d2040070003800002c48054116404110614150034018504101c0d085482810700d10350010072242c039001d1500e4000404098500e90400c10002480900c035408080b03c2c0300408006200c040c00101740c09201c50207580310302d50074141585189002c00c00240c0c1a0084803d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829602652 1250 829601402 829601413
    0x200c09040f0b150a050f040f020c3702010c14030a020705040b0a050901050d0f050105010f0302101707050703020703300206060303071e0507090507120504050c04021c0203010303020703060e 83
    0x80f40d030f50300650541910400c94428001e071985800280007805c3d070190000f949400030503005a401c83c0440e0200084121002c041c41e42c1041200c00ca04030200c800c00d141c0c042002c0d5070800c0155100d0030992101ca40305400310160400f08502c0c84d403440c0c0203000b1980041c0d00180007400310307080ca4061402c9103402500da019446003404002812040140035141c0101ca200030080b040c0800f4501e030110090b0050000c000d156110000409242e010740002d0340695000740c0383c40c515511030018058071810f00002c005c05521464030440c0c641c1c0c0580300690461141c00340c00700200709420b0104403240c0e07150311000000705110b032021908814804040085d5003012082004035240401283d10707250f07014142104500485102441500c4807240c0500f41d8411141c000c030303200001d80d0209008030b9040d1074880303007000866444010754000300d800800340d4201c07114040807411316401902580742509411f13588507000d41104003c90300300341e00a800583c4010400c0003031054a00c60000790f40c008001508 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829603902 1250 829602652 829602691
    0xf050307030c03170d020a050403230a0b06030a0b0f0105090f01060e2b060f0b04020901020c060310120b011e05010f121116110402040501200c09040f0b 67
    0x241c11070784510001c2c4c9010076000c2900d502e025084120f0b07003841d82d0220110b40350540f00000030120f8001d800101c88138450010546030b440e400c80400412981c0b014004c1001c480550703101c0d604a000600410340511844a0381c00000b10560728640c030880b420807841c0310b207615040c104503400001402c2d81000680000040c041c8541c00004401c00040503560400d0080807203031100c42d640800c44082c5d03c0512a540300703204100c21500f202c458120750240900400f03800500300000ca00c660402c181c0964040004000e03d0300b004000f456025040c0c043c00540541d4400c0f11891082c400d0340c0880d500c504240040c483c2d03804544072008066201da0140308540d08200c00030780701c41d0300e62a0380b100b807003c4111000000f007680d4012007015000c08a0594031510328040b0110020800802124070880ca200102c00b035080500c00d543c11288160340b4845d4000314010301400d0800070b019552968004c118080700a510b9000da00303405148540410411002141400061810b000d422403800c0510136a810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829605152 1250 829603902 829603913
    0xb07081306030e0a032d032a020705011407051c1106040c061809020c0102090117150120120c010c0e03031b070906060e0a0807050a0311030a050f070f05030703 70
    0x41c5e0600300741d42c4944508111401c600c420007820403194401003140400303076515800100c0d101e0340a00b14507041500000c050181400c08441031401640181000c0086610031800c40302e030510f000803135a14058064885034140980803404031600b00c8000722a60350740c1d034010300341a100766400001d403419003016940e079112141c5c070788610002c1000010000d1a81200801004000e1080003000c540c0c4401d403d4409010750001440140811203400d885100444202c11051050412000a400328074130040103542544605c8048614032028042021480e902040f007104004501c811f2151602604143c840c20f407810441d0720810007240310b14150341c58400006071031541e040100380003901d000c0102450314140040c1d009984007400c10702e00103040c98101c510601100004d903900d00c98952140c5600f590780e1418030460341c100c0d403101c03000c1001c01d0040c003201f0741c000402019144d28070304ca40c0710700c0d20b4140446245d140c5034101c0c004c200050b03082880d44100815044e0045c10b203051131900d98 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829606402 1250 829605152 829605163
    0x100504150e13091a01030606140301110301051005070501020c0a0b0108010e1e03121008120310050d030e03010518010501080106050d0b130209010305010c1b2103060b07081306030e 79
    0x140070402d40f11220041042a070921101010b4498003508100750b0352818240f000d4240b80c46008428000f000042030342d0704041c001c941c203454001604d245564a45014022003640c08882c400801c8401d00005000603820700052004000500003080c0c0c0b00c0342070500411005060348240c445a2406d4490b4000c0741000c00c0c145900181c6003014615040541040e5080d0304c1041d040c00309031000941000300c030314022032945094540100c11a4900d540c1c403960425607100540e0b015207500402c107001c12603881d042d0880424648031703207000310380000142d0200e0b00b51042542d5a1050300900f000c55864442c2c248610350040528000074015686000c5c0411080400d40d00007070101c168481c0040c0305224450f2048064990183c460076286da0350307080c02c0d8003e08242c9164400500032100415546032303131441519000ea0031180401c00c1500748110000454000b200c8002455102d880004102c41d40e60003600e400c0703005802e40380e5559030201300200c9661207500706a081c10718003c580004e0780c000040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829607652 1250 829606402 829606429
    0x60c0408061605040b040f03050c04090f1101021509010e103305030f150106141b0705090c070204050105060f0f03070507051b031902090a1802100504150e 68
    0x415142e420b00c4010121882c0c811a042042244000500019200d45d8400c1e0542205e00680075106034001150800c41501c2e908040503207100003060000c4089880c40d002440d20910500440b03003108004205c440c182c04080310f5180c4070b40d40d9034000c8226100240030022882a00600803c4594001684250121907031403800c0e520411480781c00c03010f140c100070700c00d0151900500310b0759052000c103a4aa62241c503601100c1d800314801c1c000055180c060328050310302184000210341481d10303034140043c0e0030980d0301c0008a1485030590005071034561501580c0151513041c405c0d50394100e0341c018481500d4041e480365014030001c01200003821508401d8502d080d004c0c80c525a500d85030f06400300c809020742d81001d03061b40182c0c2004460043d03003d15100280f07800b40d09903070102c0b00d034408403140c1c032050b0b040103500b24004400007420300e0000e40c0101c40d162120194401020300c2c980200e0079200300488034201082c4000303002d1102141100c075000a002d15803070b01400725844072001c120000810f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829608902 1250 829607652 829607671
    0x1b0308070f140a0e061608041a030705160201031812030e0c09070e130c05090a150c0201051e0403050f120406020a0803060d1a220f17160c08060c040806 67
    0x241d130800c1681c6407002c072030810381103903001c8042000904140c11154050311a12003007000765400200b00318000000d40384950100d8172050306207100308800c042054940d840c00c90401d039440c440b08540da6141311000000900545c20441206800b0001170100c5841d84484032465200703a103c1c01003540c403656060b901003c180b40540030580801c010480a6442c05c0410380718500f4040000181a0320602500101c4000c482110000742e5944164242200f00b0200c003001400002826015501031002480d0700c001505546000e03038191004640e00303800c180c100b21260b42062910318a040d030100004414800c0c242ca02c107203054030f0580065910140300e080200b0300c0d43c0101c0042c0c03107541c0f0310586c0c040780d9400007940340c1d80e0003c0c40c041808043e0200c0e12884401111103000c151081040311940c8145c3e40010720307a8560880c0c3d10751008002c41d0701c02c0303070320705003020002c0180c0d449104101d410b801d480344250541c41420f000310350f03060100007001c407440c054040c00f08000282c00000c030b140c0c1118140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829610152 1250 829608902 829608917
    0x120f0b09220804120c06030b030303040605090f0a060b0a080f1915020c0f0f06062817030403060b03030f040b13090e0a02180c0a08071b0308070f140a 66
    0x800e14280360312941000b401500c0003143c002060fa5880541c00320359445082a81a04c60311018107404030f8010366546a0554401e10000303000600303990000303070444900002c48011154003600d4500d0400b043d881250341d1526051f0200141c2040c00300c0601802e0b41c00094405881c401c420f9030f42d0380300300b00c080810035010071501505000a5400880030000381910a568401840c40101d130303140d4440d002148135100790407101c1344445022030a580035480050845003821844084104100b44030f00154a00d00517103480020307480b09110300c0040c001c44141c01745440310315500f020406c95966014181c001c3e0010012928191100700480781943c81480c442911580c812080c055041c4c460381140202901d0484802104640000c260030590b1080720b001c0c6411403003c0011800b000c0696401d000107a06011106a15020307102c3e40e5444902840c00e210008042d20410340e5800041c00d0a60104100400f40080d03241e0029011000201a00300b40205101182d2030450a100d49640c1508110342c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829611402 1250 829610152 829610191
    0x6081303050703180f170d030c02030a0509040f1a03070f0b03071b0b011e0603150e04052a040501060e0f01081503030d050609060a080303190902090403120f0b09 71
    0x60490006041c0712040c49044589942d1900c800380351316806c0302402c1c40b0351020028040e01c00d0244286408050380030f10f040070100300047e1019005050441e5105d500e074404994400d8130380c030034001e41c640410016001311030391070103142c20600c1340e8014024005d416a01071000002042c220380e042400c5191400c1c0340c601e1003140100320701000302c005000d14aa2400043ca04020ba20f144007110000401410255503580e01501140c4c1d41100789015a403091a00b001100301d1020702c13540c0b01d4020016030307080381c0c0340803c00541d8072259031452125800700c1056560b5130031b05104481c0945940d08042c0815001c00b40010b0f084c94081110b5030401c00342000082d1100d5580540c1d0304031400280482c2e448400c0c00c01c40130040e000031100c0c14042e00440c80000c1003854030300b9138002214040c201540c039546a42500b05913208400342c241010585500c484001a01c5564039644102e01a644042507904c200f4904e0041d69125103080750940d0900300e0700503141d038072562102c1c0c205170100f18055001d0311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829612652 1250 829611402 829611437
    0x1b0a120308130b13111002060606030703180311152401020709021b0f03090d060203090118050c01090915140f03010615120501030b01060c02180a020406081303050703 73
    0x61508000d00183c8004180481c04c0340c09150030134042d214884d84950101c10703205100d0358040c9141c4040c010ba1096000c0340c55414280c1c000d6030800f500c0d03c2c01140e02003a0407082e1441c542004400c50003d00080c0340194000024081640c0b161425043c0b42c105040c484111181180101e0320f0380401035018100407036607802004a00c0c010020800d0640d1101040507102d041141c1c4114500300b10302614100911280c1d000c4219195103074020851a95101507860743c40c001c0d0001003885404c0d659602000301805069007107205400e00c104000c001c200d0001000400810007688200c244908210408200c503c1d80c001820580b80c2d0500081280c010101c00076024112111003650194a000b03000304400200019511104601d9102da061030510b2440d10b07421140c09110180c05e1319510401407004501c103900c00780326540020b0030089004554003803002602401d584031082c1e69400a41044050741200010350701c4020385d40501e11000c05030324007a12030b21070100e00408212040d260034000305c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829613902 1250 829612652 829612681
    0x60801050106053106030204030c12051e1203010e04050d0819090510020309060105010816050307301d030403200114070b060103140610050c100e1b0a120308 69
    0x130028000104013175988130003500070350143c04165004485500f0100740f152000b0170b00d404059200d4000e04441281c952852403800c2900041c8403a03000f140c0442c0e804107003e00185010f00021361208049080a2034101c0c5440c19402140044c0840c0c60100700705215800b85040303e121501101180458847c581a400c1640100c007005105e0301c04400c0c040c81c1c4d04009862410303508207880b042c00d2130301c502020900c080500210500001d50400002e40e000748070301c40c0e14410840120007100081164550640f03030861484104400300d5907a80602c2074070075010039480200c903007580034500e424115100d07c401064074204c0c04132081101c0e010301c0c00d245d1003403692000ca030121a01c0a91100c49510b801c0c0300c024401e450007030005c2c0c141007100d03201a50031a21f00d40900001001900780c400444801e480c5074000408036055030148440b050762201e00c5026034146000300c4000740028841c00001c0044803500158414011004500144001101101031305802c43d0175040c152601e6a1b210808e4030400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829615152 1250 829613902 829613977
    0xa23041b05030f0d111501270207050a26030a0b06041a07021e06070f06020d06090e07290306040209060705030a030614062505070b070606080105010605 67
    0x5210b80c3d10310b480c0040c8081846429280075903a04010302c03000c12081030380c6039001d28000604c40d0740c490040200080341c406440714542140c84841da2801e20b24070440c126005501c003900d040d041b0901510400822042000d10110382c02041180405c035650000d03010702000300048043c554a4044624507555038080c0e4008040b4600651006006001038808d15041860304a00070040010100324004c412088590500000740100e0705003002500c4d004240c286600f070955046508026403103a5040b10f010781c5001d8110203e01280407070350380304601d1500300c0541c44080712900760380c501100d02c0c03000c09000041c0e2840942e640c0d203a0302d420000400901c01e00349426485000010902c040101c04800f810101c2c403a40c03410040075944080b010055642c00d841c0540c008400c1014141c2203000405900d02c0404d4030914125000b01591194505403294100048083c40810510100105802040c018040c40c5000340840c7d45050720145c00c60282d8003000401d0b0005410751480f691003000048443d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829616402 1250 829615152 829615159
    0xd0510080307030c061a010f0e01270608060f06040e07020c04060e0601030c18180f020703030905120909011413050a050a0e0102070c0618080d0302030a23041b05 71
    0x202c02203483c004e0542840c039041103846a0038040c0d0100366600a0643d000420780c103840e8011003a500c0c1030b0456030f582c0c010441c00d0600001032030b500c61158004000e81c403108403050700c1903002c1c0c0c01c00c080600440d10040c0254400e07105824045c141fa240d22054400311501c80d0025446601d92500990508480d161801c0d0000c1c940840040c07030b840d04120b150f01030320080e01d08204003403006c0003c41c4c4580488030244911352100408000348411003400c280001b40f07030100041c140d030f004015403003607038031810f42540003903291803030034013844000e0120301c41c461011100d20f8940b954080206240d46414440c0b40340460100b9500143c3d40c8130310101d44011075030b035403007080189040c03440306c0010071064808400003863f122080816590502c03c0b1545550410030a2041503d17011040700c00401906003000109a9041c0c00103d641c01005444441d8541c0d0b10050303100d14241c85400c0c01c94078086400c558450402c2030384803004522046058006402c450101030422404d07010700141d0900e41d022540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829617652 1250 829616402 829616407
    0x80604021c0c241d1f0329030c0d1212020c06040c080d0309031227050a0326130516060c140304051309030903061a030c03030c030d05100803 62
    0x100050310704480b0100381500c0300b0013813105010251403d000381d040c0c076a070000d05800300c50404911034010384000200d640b41c04141544000c01c610302c0300d2050b8440c81c20f03010b078111000d9042d00d030038000811180c000f07560310f24544090340c9410b520344100070021814040501803030420f50310304e40c04440340c0200304411140a8203051800303110701034440c07084aa45005501da1200c1c45031280c014219020f40603550000c605800343c4000c402445004090360002d1504c042c0c08020307483ca0300843c40c0c0315010350050b00f05241242006020000c810048031904030011846a581840203610dc0d604416641002c1060280619000e403034440104040c0704c5500c4c040a0001390f080c2c2c0240440c48071481651064072003941ca6949d140c0da4000c1303000301a404041e080101ea140c0284d41d0020003018000d00d042c00000795251286405c450704107005540303425282e040c0524600342001410300e00c0c03206400031807420814110281c0c07280150041500c1d03094685002ca0034070b000190854002d000c2c418280ca5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829618902 1250 829617652 829617689
    0xc160308030a1d1513060603050f010e07060c0305090f06130512160e091609060618030503030703090501151e0f0b120901020c07080705010207080604021c0c 69
    0x45650012a8207080c00c1e41000040740d032400c5800d0b07072060f001c92828010b08440c1d0b0303408121004260024401ca0030050108625800309126005100003180160060907581305190815400d403103115019981c0c80d031103003404102d81e980c800030300741403103800d860016100e19002c40010040c0100002c260761001010850180760802c608605048450488119412007202c08031151545841c18a2542e4510100401c10950a80d0381d0348503803107a0300c0804d8680141050b030756010000803a4000c003207815900d00003480420340000c800340f4500c0d004206020004d10b140c5d51143d880c40010200010107131280c03500303c100030702500400c0ca0b0102c10f0000e0f01000d6110320051a59100a05610907020302d90200024000c0f005000b110942d440c4c1e0f00040e203044d091351854030400d0005000c801181d03500300900944030078188444d1028200041c0030705481c038641000245810450707041006590003035810b210069955280c16403240100320f003000ca50b00d031141071204907600316900843c24a031041c000f50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829620152 1250 829618902 829618913
    0x207050f030408150103020303040302101206030c0609090528020913050402040605150a03090f021011060c0901410c0d110c010804060b19240c080c1603 67
    0x9000b0756441c0f500326000341c1e0400c80310414200c804c0c0f00c06501a0801c000030310150521220b00701c2000020f051171450000c4800c02581120b603641d00582c0c40894020040c010380e644940210000d1941c0c45040c40542800e2401c8806d0f1402c0301e8030504180c0310384443c000c00441f9501511040ca4004140825050f08288820040c010072a422846285444004116460400a80c086050104050b0740c01d14080380c1342039000b002600404d55004071126031840069a910421400a40c0036a4440580c0ca000c00480d911340703000a001c8031419401400b034035880f41d0384809410148405405208980c801c1c01002a4490b00c01140c0c41c44a201c1c400c1c0c041039000d140ca4000c00c44280103508a030000e654101080715243c180c0070340c181e03030380e004010851000d40c40f4003502504a0f00400740000c0c200740540004d0340c1051003403142c8948180c5450108030f50515280034180e00103103440204407400070f801e40100203842011004180e043c0c045409100c0c0f6004024041c08502501d00c021106078072411308 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829621402 1250 829620152 829620157
    0x3020c011d040c17180a0b100b04060c11010201021608030c040e0f1603050f0c13080d0210050f070c03110316060207140d1e110d05031e070206010603050a0207050f03 73
    0xc0c91580e07000304003050030b0240784e8060480c40b550040161220706c90a40d60b034001e000c0301600c010a00240410007203280c81e06940100014170302500c5660041c40d151411060701d443d4013150300c0c19a4030510901e17201d02c100e141c1c028501580111403d60365506e40307032001154002c42e00040f841000107010001d816803010101405101d8041e07036554020700300001141580e004440401e40340c042c1c0e101040c0480a180b000d0b1580d9220fa02111500b20f4075429558504500807200300c0050703001071103d00d8401050f02c40caa40110426031051564500000046d00c064060300004003001501c0d20360001004051040d9240e44400c80070324075051442c0d0501c200690048031060307401442041c0d0b10f5099000018800040301602e80380c0c035407680362104001403007240c00140c040c00e000200450030ae242605114600aa0038151103054982c207240648203900194146c000b03002c500d9084c18015515000200241154611f25000c501d50741e4142c4400d0113805041401000ea00c1240028114890301001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829622652 1250 829621402 829621427
    0x90c170108150c1e0a020f0d1805060f0f0903212a0607110c060708070b162708030d0507020d1d09040501110d0203060f01030903020c011d040c 63
    0x20110150746405824544038490191010003c8103080301d08103000c50070740007170488003042e0b00640d18001c003010001414403801041c0280004d4080405170116010100d61801411056410070f007800640601c0d0f00c1c85c3e02c80c46140c2c001030800030518403500e580810603c04000030f100709030b601750002042108070640100800c4a54049142c504840c20400580286020b05102703004044945502200381c8198035221520b06440c0034460990100f511088010400c40c7d200701d41d59551340c146420900c00402c805070140012071220002c2c4041d00354440c3c1c0868142c52990601c40300c417500c8507021a50403041e82e20580c2079000100d9103201c40f47e0030382c0c03003a4460012a000d41c1d51000e00105c00300c0d00030264007620700c03d4804103031190441d82000910142e00504c02c400025280c441c00c40a00e88540002010540607a000000c0040d94140b904103000741c2d00003800e084c800840d8035a4040e49409003800402d040008a005d40140c2c050240750103a0090b5020708108000c850515000b44540e0721403d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829623902 1250 829622652 829622683
    0xa06090e07030c0f0c140d0509030f0105040b01062607030c0815030d0c050705030609070906050609060702091b0a0f1e090b0f13090e06060d020901090c170108 70
    0x100029200c074024010110100030702e40d0341c000311044200c4c05499040c50704406039000d42420303c8100411108111500b55104207444040c0c0310011038081501d032103002e941580c80c4d079041001340000909006910760540310141011030024003600c405401b00d0400d00070341102d41340007800380210303141c059102944861181e41e94140700d951700400c130000d144d4008080f640580c080580321682921864000c004144514152f80c3c00c541e540d40040d2070300784180c80074002900100c4007004001c44503c903030340040005035159420700c008800021280e010f4408041e0041690800003454590448548581c05107a2024144c0701d2030340400050101d4044a60704010410440269403000c0381c00d114103401001d42d035a40c0c04907504081881c941a04844044046c8690500401311000320040070f040c0500095400004c441c00d140c0102890840301038400c0340241c4200000c0740142e102c4a6031507065507402ca02c04503035080c4200d400c81c0c00b1107840c0385810118408000101e4081404160a61502c0501d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829625152 1250 829623902 829623929
    0xb0a02010e061504150b1b07080a05150708010b04051c0204061e0e13020402090d080d0203042a05190512070905010e07020604030c1a041110090303020303060411090a0609 75
    0x3003115145c000c91314002c800c0005024840603800356401418210310380c012006032405155107042142c504030784090125a0b6401404c0b480c21951890040680c1c46405454012403a524245450410f81301d1030007918007503218016a0f0504081c0300504400043d409030003003020580c1e130741c81200740c41203001c1c2c2500019101e900004084502410345d138020800140c4620304c162003942080001c0d8000014550015400315510002ca480f0b00b0107815410340b010300141e0b03245000c0c07400341000c0000f807506d28007040f41e010f084100740900d140322205655090750247d04180005203945504612a4400c56201201e070707600e80c050580225049007166601501486240d89400800042010444614005070302c03d40000700401e208a24001174603002d00c041c014640c5030081881c9210500710b405030f9030202001c1c904000760602c456050f11902c1145001110b00e81140c2d4025100c1c400600700c00d1082d40c03940b80150725100400c0403500316240c020f105a1340c29594801c080d0402580d407240714408100d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829626402 1250 829625152 829625171
    0x6090a020a06111207060b03060702150a05150114091201020403060507050301120602210f070e060408100509070b16030e0409020904080a03090b01120b01080a0c0b0a02010e061504 79
    0xe481c40303c0c0e000081001910b44035070902c460441c260031041094904a44071300841445440620050b40620780301d42c003a00240483c145401d1031228081d18600007140b5000402c8500303088140c26600e051000d1800e1040020020038500c070a01462002550018130340025900701c05055004004403441008188059070321148103442c540000d108403100380140205034000039642d68000c000100143ca0311564900d040c149401d0340100442e1510041c05104040c88007650300550510380510f01180c90704c1c135082c24210696143d00041c29244036440d00e40021440c2020113125400c050440142400e07200e08003082c04001851040f80243c3c0410703c3d680d942c0420b41000c0c0141030751030fa00503006031002d8507175990b505000e910403a181410150340c1c040401c0020a248480b500800d115043d41105448900340b0701c04d103100c1a4402020355009001c4c036030000d550780d450030382114060300c1641d4a03039009800581c0035200c0d5150030201800b6200c104680142c414414444080b019103007080100342 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829627652 1250 829626402 829626407
    0xd060f06030c121b05010c0323040b0309010b0a05060a0e01140c1e030708070f060f09141e1b03160305060106030b06180609010302041a1e07030e0906040e06090a020a06 74
    0xc1d00842e40022041008000070070b000b103108002038640c0610b0809900752500b440031852b0000d400c00645c1160001c140300180e442401190300c0048100c41c980841464030001034240d200e001c1c452002c0c4079844004810582c01509080c0360203424a06495540c84600d405907280e00d21358544400d4036903441980800840008243e60790784d94004d00302d80c500109a101c000d0750404070001110001e40312901040c3e650081e0107400c5030344d48034030b079500b03052010351190314106036644040890000d00701c241411001e80000d28014680c510100840140d81c40c40082404c1044c032008401d810300104000000b044070014450b8103d4a02c0e0781c0c02c111901160040010605c1441d05140d00c41d4038105070075019142800042c01c40010504005107401d5079101f041d035140d0321000c81000c0148020940300c0e420381c0020007241903029204110380c503000b81c980e80501180031462170540224200d000140040c3c4480e8080e8013085000000c490340c5151850203555205000c0604178040c0da00d0703000c00200c890 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829628902 1250 829627652 829627703
    0x140a0606080a120c050703020402071502162906040b1503190606110a030806040f1404021c02030303010b03060d08040e1906140d081626090d060f06030c12 68
    0x161700001a083e128650307005c11019404c100f00030365075042050108000700c2010f2008001540900b80d0741b540860070341c180180c280140346c0c1d441c4c1e41c46905083c0c4c04040c29035442c0442d4040822180024001c4180c404034135000051100e8600c1003030000180004041307045802c20260f541410306010403902e07420300322031043e45003032003520540c0110850300010340100e1045a00c1000034000081d80342c0090704040c151a01c070424007070418969001c1c4070035400e00100c6070011058070708030b606110360a51f002c00e60701e00c4144103001c540302001c000b260303d59032007996400280780c11501807070700c0315110b07021039a040005403003d44112420b1507403084045018001c000840344505d25003d15080c2403410700491115914080703610107010806d468240178801880c148060051402031001c046058071400510042001e0240417202803081c1d00c5260348462200da0390680c0f00b10040742d282228000d910140030b1680004009458202010410781c00030f50300d403002e140c0516515100e09110060f4a8001e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829630152 1250 829628902 829628927
    0x50f190b070f0c021017100914040c0b03280515030624010e1207060908010e030d2a0203221a1e1303111c140a0606080a12 54
    0x15252907105009850889406050320017a03080045034445c0310b608044d0001c104450b184110a8501028131481d84184211035512a90882c0e51410382020b464413900314045105100308980300100098036611a8090000f8840013452900c0d906a000c4010002921045511010903a4040c8418210b4600012843d020740043c440004017030264241d1941c0c074035400a0720300e05204441218140356100c40d0340c07000711600c601024010050806400a0060b007080d03200362884e0b814a01a40281c40740403081784c4000e10030100c00a01c05204c0c200102001d80c80c020900c0110800344107402e02550048014800c0008a03040040c2002d5060303800402c280f4103004400000c59400c00b00c2d400c0600b403000601344071100107072030300d19120580c0c180d403404d0744109034621050340000c400700104034604013000300c3d0820895071312100c112110f42d82c0c120142d011030041e0202d40c51014100520209112082c05680c00540c2231000b143c0300c290495070303001c0c80702c0c08580c20b04614001e18021407007141d181325103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829631402 1250 829630152 829630157
    0x607080a0b0a05030a080a030e0a0b191b03090b010b1312021c0501090c05180601080703060f06021b030d09120503390309030703030309050f190b070f 66
    0x219169166040000e0001c846156089074103142c0100c3c403a0780400504035024440c6500613603600000b48010f00b035503614469618950b20040b46000000d0348402c9155200c0f40303050425201c00c90341c5000ca005450306003081d8003946200c220319020554103821001c0e1340303402100c0301407841c0da840300e07207003414032440c41180215803008106100c00700355230f83c1e013032000c500080100c2c0004101c80d000d0b541d08521040b0444060395100401070401030f140c0c05040040104503600034010102c845508058074006042d1030400804000050303030b960180c5d1005010f4650002c01042c1a500d5000180da81da1103103590030a02203460309156006e00c2c0c00260088035013044c4c0d0f540841e403483c00112003801b6020041c01c0f41c0900090005404412503000680701c5403040400b201d0700343c0d00c204c00300c1032080c88456103842d09800410501d5015200010300d44200c85d414540040c00b0a000c2c103081e820080500960b103114040d04c0e0009800c01003079044041d50307500a420740b07240342c2c40c1c2030010340300c0200d0003050401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829632652 1250 829631402 829631417
    0x90b180106080d1710031a01081b0a05010c0f3507080702090703020c2407020c213d0b01021902060903151603090206160c091109010305090607 63
    0x102c01504ea40030941000c0228000c140d100e482c0e5882c001074012803880d05e140304d02e1540040140b0401004048541ca4104c40070141c41ca101101003141e0034240e0007914107203c3d05044140400c48201c00d075040c21500101624130440844c0c021841141650502c0141e4140c4180c14500e40545c92085404603580b141d542860002d444d4240b2000b403100815401c14560f00340a4120804028000b03c440340c0d45200400716900c0c0c21900c204a5140c1c00b404d660b003190300c9108294820388400596013001405031040751408100c0307201882c500b234825400700410044180800f06c0004403c0318001c00c014403c4130005130207040c001a40115088040c02e00c0c016403007144a034203000100c40c203e0503070a0015014a1030720420324082481e03c001144454088400b80c8108403600352101e54400da8919a03180900c220705564000521701d000f078844011a0000c440c1d6060100280d000c4004000d0040d400b0920159007030410351700240e0080580035002c40d0414000a018460110781c5520030000b603103c404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829633902 1250 829632652 829632677
    0xf0a06050909060a110c0a0309090c0815040e030d231305100209060f07150b0312070b180f06040203010507111b03030412061b02010b06030a020d090b180106080d 71
    0x203818101108511600200701b1800001024055966090300030f45503070294910707110000080300c0300000240c081026003000c2c0092030744400520071030440111000300c4d0121100c00300034210b210301380d00465080e10305001e40d460203c04064046541d407a05030145003039542e1040800b00d600c2c5101c4010310f280c100c0314941c105150580d003c0c4c02d88240140480c0d040001c001003421144e400403401740c40c20444041e101d407001005028030803100d4026000740403c0044401d5190007401803a40c01019001501d0028070502c2900e2040044007a00383d04540780c1c0407071007d1441c0c90b1030040d0b4090f80a9402d00380020981c0340200e14075900c803118080141004000320380600002c104081410303915020400000501075480301a00155602580b80014035040001c4044101850003c0050075a41486c40300000e07a516102030b80d81c0b002004070b01596a018020024000300380c5090018000802c10f800e00070b403440903001501c0062040d800820100707444040741395840d15400003840c00241d400340e800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829635152 1250 829633902 829633921
    0x50703050717250b030f09061b0d0203040f02060f0304031b0201080c21090d1803260c0109030e28050103110c0712021302040617041a0f0a0605090906 66
    0x156403035200d0241040326030340f00c0001c0d0380e50341c3c07042e61b2141c1d20b2900c43c002d22107100780a0061030b4102d12079520040110002c607903401c9481c000c4610300954268048002030900c0485032611110a0b4000d204c0780d80e031103400000c90341310782080d0b80581c0018940301d45070707001d4501c040400404c5c2e50140c4400303000d951350103c9030000d40e00101c110030598081100700085890703840f5406015034450009015008000c0c01c0041070082c46020622080312110303400c101003110120100d40b0b0280d1910700d08d401c6e03450308980315410300c00caa9110380298030b03000c0b1170b0040c55130000703100a21030800c131010151400254107440c0c02010504045d2201300070080c1c108080e44c0298000404200c010a00700d0400d604100041d09051044d844000a801402c034494214a4100c0520020710200d0204500f09810203000070610701740e002602c00005500c1010400303000c1c4c0c004000c5040e0f1009030344212035241901c0320a1039000c05503410940203041c20030220b860f1909402d12481038005c90024001d5541d4114003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829636402 1250 829635152 829635193
    0x1060608011d0c0414040b040c02010b010e1e010809030c0613140120090d14030306270c0703030605090a06080d05040302091512030f03071d010c061512050703050717 73
    0x85e140c0c001c1da500075020300c50725075000e884480c20680d0000141a50180c00141c07018030300c941c02c90b01c038100c2c1c9154460895025810b04240400070301e80211a6501d1070005403941c400c941c1d50b42c0c0f0702d00c100010401207203800e100786110f032413141100c01c0207030a051148500342c40d4180307003078220081546104840326a454001d8035100e00000c00c002d4800c40541c840d907601051403802620300350000400c00104e4100120304c0c404103c40309401d00c3c3d58010403400e1040c7c000c8060403d951040000032060306043c440c7e00104080d01c00201112600c1c24a804424002d00309485410828081e10764078444842c094019901100d80161a5a0882e0799400441c00740542c00c0b081e5580c480300702c0820780a071140410240081c0404052126030740e040c521409406c02d20800d01866448604030181d42e0240d038804096084564891303802700c1e0700750700405030b0120407109811026100c507034030081d0818810000b4034282101e0145058408564564101c03190858019113404202c9c1c0c000f15403140c240e510000c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829637652 1250 829636402 829636439
    0xf03070305150a0e0f070e092d0f090f03030114090a060b0a0518030c0d150b0303030717060901050a030b0a0209060a050301090b01020a2307050301060608011d0c04 72
    0x510039800d02404001004101584c0101684560000410200380c40d01a15250031425500342044041481000281c0b506001480988201d84496102c0c80005085c81420420b076406502841280303003005032040d0031042240c00040d184038903000d020095502000b128107a954001a0305441041c0d14140000c000010344110401d6694500000f40c0100407800b502003245185c6d00d190b650440c20120605000c0c0410f003180c8650400400484265075903504002e6242d0300400c101441c0480580030002803048040194060000000700710310075501981ca14002d6180350030303d107100d4840700d09200401000340540354025038024014004100c0c0b4500241c0c0c402c200304405440c194101d000b14001d80c01018400001c910088014458a4918051600c100b4130a03c014550802d594448850350407501d00c0b04c0900304180442c480360034000340020303005400050000d1142941c0c9880082c0100c401344200140000f00b81d03880031820003551400740c040c40c83c00c0035850400e41480d0000c2c824040404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829638902 1250 829637652 829637671
    0x110715170c0f070f0f110a0902040e010608040510051f0e01050d11030a05070f030b06061c0209031e100c0c0302030d05060105090d1b090e0712030905092a0f03070305 73
    0xc84400050050005c1000703070780c8516650040f0115110601c206503000e0703005180f0300e6005002c18408003903c2c6405504440303513032030100c0c45501c841c1030140c00c0151449900b1481803c0004106040f48035501000314041000300c240d4289948201030140c4140c2030088660004030042d21201140c1912454607900a004003602c0b152003299441c1032500410f64030000464040200400510011500c4a0361145d020f07502145000d1a240303040350341d86c01c2d103904090100e0740131138107000382c0e1800c112264812a058034100181000040110340e01c0c0200199428501d06042e4201880c4c0d1103090041403441c0d15400035810600308a00d03d2002d000021302107810001c00703100f01c86980d9a0784600040e0140100080040b0001321100c0d842c66140c0c54100022542c00d124505c10304072800a41501110291280703c4040303280d07480c048400001560081c6d47c80003c030010300206041c01c4118040d46044000d02402034842c0740010303e0b1138002e0b88402841d41c20180b0005504502913081140d0165900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829640152 1250 829638902 829638923
    0x15030911090612150a0b0a081515060403030305090f070807060302250f0318120b09030c0d2601062f0f070602010501090e1c110715170c0f07 62
    0x2500b09880c081d000a005480d501c02041400080e1100741b11398a4199000c3d20a140e560b810310000ca41d40742000d5050700b01404000c00003886002d4442250031450348014001c503500c41d42c0c0c2c01c2c0180540300030340d800201c80c06050a410210705000400c0b1017111305100241044500d44141500203401c0b40110345040c81c060b82c502041c901054075800082485100143c00b050f02c9800c00610b07134109541000e050f040310322004c3c001004211980d41c201070b40182802502d6558620140c114058008240014402e00d14072041d000d410480401000444844800d14190362804c4c90195040038030500c0b0120344c070601d400d05c90301282c4500d42a124108441144108884405207261080030200190550031a120600c0f09560a006e1240102480c032010f000c00303020410110745413100c1c00845100600c00a84080555014510009080421500f541e180c80d030341398000441c0c0202e910302d038130004060400f0fa402a40a5510316030180d170140c1d410034244001070600f290150305c401c100f070303c220040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 829641402 1250 829640152 829640179
    0x4051b030405151006030f0e1f090210080610020a021f020a020901061e0302030610051c02040b07062405040b0d1b05040605150906070c0306090c150309110906 70
    0x4503038540e40a11449030300044c446140c000d000b8215030000401c01d0703146003805814107110a0010b503102002004250131404054503140040050144640003908012002d42c1c2c00710705038108401c18840c1400392444010580316803070480c2c540c951002c0095010f5a0306034008040c480f400e88810300303141c403801207454408098000406465090303001c100015580340720543c0111150010047c0405035003405d50960428800054a010124060070304200000c01d840350303120300c02810f0340ba0b04241180c2c1151348903220410313841503a0101a054940a0506608405d215804041100c4494900d040c8800780780c10482008040c0c03140c0d07443c2e150300014456909000c910640b44000110701080701c40d1f00bc0610f00410300c02643e410b175100c40c0c03003404131020480500740d20b401158803041d0b0403a103d0faa120f10620300b143e55400f03144c0000d44080e01d000201c1c1d0802100c00c0c0c002d015182d40c8004c100214507400d038100c1c00e175400490010050343c1560001815403d00c2985203801c103c0003490304481048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 829642652 1250 829641402 829641433
    0x60902040f05060a060f080c07060b060a090317040e060d1110020c030c06120f0a11072603060a0909050a0b0702070e06010305010e0721020a02030702010e04051b030405 74
    0x303030607010406480d0745006110440c035081503010000c2610342094140011940d030b0103040d2100003403441216400000e002c00401c10341f64840300070404010300340c5485203c2188002c001d4102800219488207081c0182001c901401c010f890468402171034026859943d14148102070311401021508004044405090395a901810801840c0d269004007003e0320410205132804010b4200940030300001c1103903e04030b07000c3c0c065190b4003000108a0a03016100e081990b80100218520358014042c08a844410401c803440c9821211040d403d0800c544162000741c6112440103441e0668024003103d010840f44260360848601e6600070001d035410204103846801140b1000c841d0380c3d0068101c0300d4288076920b02c0d114516003014080c6810041c960400b043c00308030b10b00140c080c109220040102d1410446a5107610252400281c0c055444882c2c0000107581c03608001c000701e012590003e050300480c07c2a12505124485248000800009075182500c945d40302810545503405007840700d444050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 829643902 1250 829642652 829642661
    0x9010311040b041d10020412020603040507050d121205060109090e030409050f070210020a0f140c0a060c09050312120415090503031e0f060906180117120f0f0706090204 74
    0x8110f13500c410311545802c51817414004480002c10400380705200a004542041c842d140e035a960540722503540c3c1e03c81e8140240b50020320b0b40210780c801e0f42d07094107078200210582c079103d000c0d066441d15840c15180d860b800d81514021202c2600141010400704564481d58010303442042000c0c0036070340340a403920707104425030b0307012030701401d40d0314140e018010203d03130400c05400c09007058002142022038030900280305138400000d1004018000c9510405042d554048408a00ba0001210865500d5141c030101403c4d4424181c0045000008000b03054140810552100040e05801c28034004100e01010031a481c0500161000c1c000c01d526075415401c14070840c40e00703e009000454a92810000300061005441c20210104000d24240050290040003240e08070030100c4181c4882e40d0340b10041520000144964000f028483e000022910444040c42800e10700d10307016141e40d600b0119215025105040800380e00700000c103d440e000c01c40c0b101c0a048694031882d0040b03000c0045400003029503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 829645152 1250 829643902 829643921
    0xc030e01080c0d0908121b0405041109030a030201290901031202070f03140132040303111b210a0518061c1401081f18140f03030609010311040b04 64
    0x10008900d0b030072540503081c0680c03007d9014100c000066501e02030b41c4440c05540724003400741d6142c044010241918405491003107101404a41c454034282c00c000340600b0400c8580f88801035050f201e4081a103500c0c40035544048041e01c1070b6113030b91a681c0c07140c2c12407040208160860003403a85c00f0a507540b506100000444c020700c1001100b4046440040c211540e1360321a008002e28029030f0042131039900c00305545100034a1200c50705070b5450034190060302d640000c404504200040c0c6141004411820b03400e05c626041c00c58880c002801c0c03030004c40822400c00a000c4410902103284124803880017028a10020700b42c400300084a080440c845400c81448801c800c0301c00e2004407401c110b103108640c2070013612070040c0a0755150175081516241c00b0385c402c8041403000c40b10f00c05401583d40005401c08080d0824003c401c1140c2414103000d100454a01001d00507441454071a16002080c2c901507d401420540c440c0d282d503032160442d10310744030381c241c211f910b54440c4405540c85204100f401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 829646402 1250 829645152 829645163
    0xf0f070c23030a08190b0a0b0c07090e0f1b090103020d0f0b01030b06010315050105090103090602070b010e0412081608040318090f0b090103201306060f0305070c030e01080c0d09 78
    0x80741480035801c0e55824010340204e4006182400c800d0b00c60f070f21f001c8418219032a103080d01da503524240130440e080c00801d402c540302103400c0036030b4900d00942c006040200013111a040e504000e2044405a0481d2000c240715030b84543c52000500141c5404103c02e80814410041442d03c21030365512030740c01150980c02035036030b84400801c00a443d60140034402c40c41c001004031403013140c1040300280c020b014058505040503644c40c4028204584c540c12580d03003c0c0c01c00580c01e45580d40d4100013841d52030464044402508042200c180359000381d0343d1303a016440d1140410001800304500320740344580144107404202074414089603440c20b11580001500700c0603800720b006164036103560309441052581c3c60250f06840010004201031100401002d4618403409060b03000c160005960140c80380241c0610a190040011f9419000a03079090030104c5078509005503922141c1c150b81000710200701070049040c800451405604c10184140d2258451003100c1c140302c1040800d00441d40030710400c842 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 829647652 1250 829646402 829646417
    0x406050402013005060307090204030f030221030402150d05070201060e18060c030408070804060528051905160b0603100605062b050a050f0f070c23030a 67
    0xd5580c45800c061914003080d4040d405401000c07071081446000360588044940d5510214420359001e102002c02048c80c9a400d54580e9240e0900764024030740d0313510440161182c0c003041014802c108131448031240b0310103001800d55580380c0070f0141c200324003211858035001c100310710a030ee58142e00c1154010740940c0e000140b102d0600a020820240c080e1280d101d0028103104006064000a001c60340030300c60f0078480c1d441c0d4690f40707081074650081c00c1e4002c1044501041c08124564400c0103031180704130501c0048000c0403d5180d01521101c841041d400160b020451000c14000e5106044409041441d00b945070044c0481c42c2560318241c2c0e00110344442a090030f00c10a45801c011000903142c281804000707080c5440006034581c070070221a40e10751526841c48102c60501d0314000b003003a0580e140107100500d401e01403440204801c8811070149404c81000c9200c015011841a10915440e203480300a001c060729485ca01110380c05013103640f4031a4440c2036507440390a02c003038903001440d5109e001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 829648902 1250 829647652 829647661
    0x108010509010b041e0e07030b07110601060905060d09140304080708011a090106181d1e090d20030a050a1215030609080c0703080a0f0c0c0302060a17040605 69
    0x900391443c074600c040c400ca05100303401d08491101c00c07814601c0d0006000001e0720040040321141030050756800603000365120000c00180d907030881c2c01000448007030010380c0c4050fa01c840d000e450743c0c031140c0201c60b0440800e1129030301340505c640c414401315004650b00d00e09113035610041481e42e4015048020250800c3d1001c024005090080c0101c441c00c1400c2144010359101c003150060405101d000b013004400c2d01440740c401142c0c4543e2010f84940400d12140c86400080c2400e0340308103482007840d41e4a401d440540d42054070045a01844524001d4081d09810700380443e103ca403006924440d584a504443c107034003e080000b00740d040e107291103154440d80300386005000304042d503240903c3c082c1418846c0076800e42d0030700b4500c00c1d42da03c50300c00580ca01303140c00c009906000c0e800c048103062148000200a220502d0003411142c0d00a07692918035518104003100d506508200060410b0303041c4d0710a00052500401800319009070340307015562401c0994000040d410244c4066900b82c2e40c41c410711 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 829650152 1250 829648902 829648921
    0x32410030209040f060305060f04140708161e0e10050a0806040303180f02090c0d0507090503100b090a020d110a050306040f02040e040f05210d0b011e0e01030b040501080105 76
    0x10a000094584c01c104240c516159182c82c1c1c44020207290160300183c0c0010104600701c0205484030040100b1103a245440c4c0c60382642d10510480d1113441721407084030010701c011261100e25103068440b8800c0103441d00d0103031402d021880103003000c0340c0c0d8900150040b880307803106c1040ea4003e020f213000514080c00c1078100038048406500844683c51105103100001ca480303215048603065040d03c1d680c4c074a1b0b46240340ca002901840c1d0700000032906000502c00f06652241105042e80d404405543d08010b4808502049640150307819401507540c03000151001c00f258050000300013100e1000c034400007050101007503035002c0324034203001c200301105206a9040910850307443d4800c4d20011440c00e42400207180c00b581c0000d00003011100c03150701c81401c2000031f00405002d0300c4040311000e94400f011030103668540101710004c820600e4040c000c03e02c1c2d03100d2140310314500c8141c246445407801002d4111015003101c04828145502c500c21030000313445603c502d5008040c0200002420300388070140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 829651402 1250 829650152 829650161
    0x5040f080a020a060f14070305092805280b0301090e0106140415030b0112050c0f21070510030f0e16140315090a030206091203241003020904 62
    0x140c5403a50002540d030005032518420601a03030090300f0400c41128505008a03160004c41c06ca29020400204011040640080140903000c0d4200e540c00c0043c0c01c480c86424401803d0041c220a005220404001d81c1c1442a00454242c21030300000604584c03035500c800c0075100a500030790044034004010020704003144a40d400c4000344100074460a4138042c203d40080000c000c03070720700c960768602602400a80501c076943c010356000000b40040c1da03440042c4110a1342019007594280201d5848622070310302079049140c5840000c100161010802c004c0540c8007a040c0040c1826100300100850241c0d50740075000c1e6860700740ea4012506111f022071440689540520b080d015500060044910070210703c81501a0350a181006204880c5c140009181503904180c52400b1064903090000780e40d008a402281b19000360221840c540300c1c0c0351080d80cbc0f20001c60700d050301c0080038030110302400000c0298030461001c840c1c80e450303115421030014414544030f20344d140100b6400900409039003000c0c0039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 829652652 1250 829651402 829651409
    0x50c0f2b031e0206060f030f011509060e240d05011b091403100b0406231908030f0a030902032d0a21052701140702100315050d0305040f 60
    0x70703502c95050400348040d41e18a009003400e8803541d041c030700856081d20100322100c0c040003204004d005580c0d0180d803003101080b00f0b01800540500f030020202c0d514035030420f128000c07180000086d01c08403020f00b0f40060756070030048856020613a446d080e4003040d401d02550039074030103071403a5680844043c3c4000e40442c0003035001c9503c110510544070401e603008500c5040c511004980481e081d00000009002017040ba0031402e00c144c0cac20075414100b07561461006070120b1013900c5000c1e1600044108810343c3e51584119180341d40100048162100d41c00c000e005008000d05003c90303c82d6869001a082851002d41c0c8810480034405c1d0441a0b15400000b2502c80d12480c05030044075529140d1014201c4c0c1d012210b03020400d00c43e11007020a1042045070500d0325840240100324401e860b2440c8001e00f041040d03400102c850700410422864541101c220581c028803c03821030f03407180400c1e4064041c40071075003203403078800000107195200d038500c1c140f40d02c1c0b0035030f03840c1d68941c1844224480d542c07041c3c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 829653902 1250 829652652 829652687
    0x106090509060d020f01120608030f0d060e010e070c0602040f060e0405180a2406120308010f0e010510090b03091e06010b0a08180304031101030f09050c0f2b03 70
    0x80c400c801588400a41c0311443d40280f90003140005001f5800001e010300c0d03846441c0381d01c00040c10703060741c0c012840a4020380f09040301c2400415910b5440c500c42c0ca0081c000c400301154107c02165510740100003015000780720b144050300381036a64a011501c034085900500210f04104405401440d1030311903594003c0d0140c0050145000b814412039440420750b030000e04000c64142418030b080010700440702141104c40e42440740d0b6446010003041200464021008650480004111076001010440c01e8032043d400400f00340c0c0c60002084104400c0b6825201806416003020803007001032001548120004801030140040072982440c6001d6200d40d810b0088e002000140404900b000448154411320320707010025854400c2002480580742015800521000800004209580e00c2e003544040c0240c81c10130140d2140f8992030252240d80000a003240c104103507800c5c0c580345c041c6100d83d0021380508018001c0c00461801c403c0101c0c08011030803118202000d10040640c400d450b00d40c4040f111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 829655152 1250 829653902 829653919
    0x70906080612100c0306090507020f06091b040218150405030f010209090a09210f090506070f03110a20031c020606090c1603030c02010509070f0315090506010609050906 74
    0x6240d10364a030503c640341c261a99440d8030043e841d5a20940194000e8030303541d0002c00083c24443e802a6450100c0005164030340101d10000c2c031018408510010b20307182200480114401c84c5003003100075809200c2100c2c00d0115442a0b560381e03190b040c1c0c00d0304940c801c00c1080d66140c0c24030040509d082e403102c2c1072010030ba004000700002503c9003080076030422412440860180f40c5c0d4a0000030f0314001c64040d180a03030031001280034050f41300c1c10300407a15403a6207a056616032500107004440c815001d018040c08035003400640007078030506044052003d01e00542e0340b40d07011a80c0b03078104001c2a003018990004090380300103092400b03210191884040d550b00c11041d00c4041c0000c1d4035101e000f01300d540706c0c0d0000f2000a00c001980c004840d02110880e4100d40051420b2401134000e02070045410010740c030b07020006154000c00128441660b0741521258100c51540da80c0c45a600c0c11000c480e05165110030480e400981c0c2040402e0103000141c803000b4250b4101000d028000100500e0310b445501d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 829656402 1250 829655152 829655179
    0xc081201050a170a080714060c0304060606080103261306180816031707171908130602180a0f140f060a0807020a050d02010606020f15010b0d0f02030709060806 70
    0x132600c05003a413040d94103440358a1420240c04251034401d8641c0d20f4000c0c0e904022251185000461055115000c20807000d516403200b210000c0003400010003682800d08026800c100b0004807070315100040201d035180010203c5108507070030440e400100841c142d600b140032000c5c0543c81c024068002a001440280500d0b0301d201000050392001418080072071096880600e0107408443ca01d42e0081c0c185004081c0fa212824029440007244120904492001100c024800c10200c0c3c02059074000c4903103a4201c80d10344200030342c030240d203028000c203c0e071120000907113407058070030300806140d24000026452700102c0841e800069090302c1c03050240b20311001080c3da441003658902c030060b2528035016075401106074a0400700726005400380c4078044442a00c04d0b0305420400503a00d0b1a42507030201d44650307880300c1d61011a50a8940000000030060213800168006092041d480002c00304503030b6907010510b03049907c00e803180c50005a030132900380005900003501c540c018a06031000c403040ea90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 829657652 1250 829656402 829656449
    0x50901080f0a1b0b030705210403080a020d1d0105011815060e030a02090c1e030402030c0f011214070f1d061c05090303090c0603090c100c081201050a 66
    0x224200040205140c00c0f44041204007102c0741c14003528500080d90390b2414090785c050420b402848041a02c0d8643e01b40d134404032180e1501650245030706449412007a191101c2c8440170f50040480813044503500e80c61007414a205181540001c1c00c540000a810f5041541e440c401e1404078413452003040c00c141c440b502c61400f81d80440215117603460121128512100028100300d04803001070360149070041800780710841c00c8014030304004580c540e40401301c101c04030510b0600044034003950581001e02594158109044000302c1d01d40145081101d140d0480d080004403481310050351601c0071507a04000280303411600c880c4031581d071404c14600c0304403c4c00d80c014419a82c000194080e03a00420365001000d80061140385060880c00140b181c2d00d850900700303640350411110807203e032040580350381e018103184049034002e41110001d40348840144085c803800d2106220003034100612204800d000c9282040a00950510700403140034952401e8100000c0e103680d0f410121000350320521071006070300c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 829658902 1250 829657652 829657663
    0x603250c0b0106120608011d070609050f040e0c0d0f0302010c090302211207060e10060506030a050c132402120d0b030309090103030c1401050610080a091b050901080f 73
    0x1a40f500d0300031014190116590f01030700150b032000c0c3c510b6080c200b44200300340c0c403402c000c403d61000000301c2d51440d076030700011a901c08040c8920b40c1c000c0c101c1c0c1800c100b18100b0f50002010410303134400b00d624420602c1c02081050314070510990308032181d01500c200f0542d082c050031992070380e0340c5848400c1c142181c000840088140070000342901c80c502c0d50f00c0001405204070501101d620015a4840205060000203844e41034080e0501c0e002d664172000311040c852054030141c60020b0900ca055654542880300182000384c8228840da4090200c141203000b07080c111005048400e0b0100c2d900c169030303103601c451410250072000c20f5400401c1c2100480030318005480130003140c00d41c045030041c440c0300440e00314480e03d00d810740c01c0014040040b09140d00040001583d922a01c01c08000e0844160f0080c200d400940b00c26600c000745120305500e803407040160a420043d00c4c0000150028642d442b09001c0b00081120420941c0340c00f0204446c1c90103110361030042c0f16850142c840c0c0d284401d101c3e904c03503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 829660152 1250 829658902 829658909
    0xc090b09011d09250806060406031e060902061c0e01090506060f060403060507090806130515040206210114030102041401050c12031510031e0203150603250c0b01 71
    0x410b02e10002480c0100f0402200c9005440c08100d004100d9120211381c036003091034001e004440c4242e90110b042c2d4100384c46200100e0303400200f001c8401c0702004181c405803407030090645030f440d110000b0202695545d40100403c00d155901103841ca0140c1105e1015101001e103804000c0c5d01d8150044082a00880e01c1d641c000011558940c2051007100040d0490150360000f8140c203203070100300031810780c11031400b105507085401101d91540d0754151000b0014142140109550000d40199011307058103070502d40c001e071000f007807603061a402d40300c81d114034414680003010f04400000100302600741501509031541050b4001d6180c00d0800c106860017580401400d81045030000e000d01003058103201c50300c0c641c054104003a0362800d14540d51080a00180c1300c40348562494114891180e000380b10f18a20b0b880c01000040000d141020244000d420051010035411141c20700d08145a865500541c410b148500308420001c1484a22181c4442440c03412001c4c010107452140c0841c40c07284400f0b044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 829661402 1250 829660152 829660199
    0x5070c020906040b2b020f030307030203040e1009181b120b1e0106170f0906270d020304170f1c030906050c0a0f020105150d1e0c090b0901 61
    0x6182200c000700b54180c1000074801e88802d0380c200d41e4403a940c44551780340007007802118110b1302d10541508040e00c92040300c40c0203000d40e008000130007103059600c90065000307501c038044d00d00c030942d250640419140d03110620080038040c040000d04024022500040b4000f8091000c0c1d1032500304444208400e02c8104094240b44050000030031801000d224480d01c46821140c080d42540c0d100c0e005440d100303041440f0b042d86184100081c442985115002c0d1003a42240010526030701c8207050b142010205a000b01a100c5990f017500c1c81e8001e08000d04a0140303a16802195543d02d001c184550b14101c1c0510f0148580042d0074124010000145400140411100c80044800c0b103403025001081c180c0b1b00100002d080c40200540d841101000e0a004451a12809001c66490307034124200c400443e1000c90b842001031145915040c82c01c921000d807880303859031040c0b90400c00100305110314207141c1101c807601d07507034410f2107a44028050712b00700d450140c40c0341c0c1d11941860401c00030f40901d0315140c0301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 829662652 1250 829661402 829661411
    0x30406050a03150f270c050a0305190501171605010c1502040e041a0609010f060f1101020d060515030103030e1509130515030708030a0810170a020405070c02090604 72
    0x40c041514010701e402400c1c0b41c0c0c9800c030010740d160340d03110801c2c00c17481d44800e003840310b0303825404000401d001d40003640c6101d9440e1440c14003200000d07001030030054151092a0f00da012451859101849000e011304020101381002ba8003c1388014642103640310303900400f003405a010000c0c3c1e60000e46542c6105e50060645800800c58140e40000740281d07441582c8840303000e020b000070b100784a401c10103000400348060340c0a51340d603420300c419a0000c1c0b1907503205103940502000072500c11143d0075280030440c500305c032001000031052400d90f04800320340f080f103503035035081049079242201800c0361060007180406e00315855a2000ba0494100a480c14029000300c01000301b41481e000803126002001080a20181104000302000b440700300c0b024024000036030000003151400040440480e9561402140717040c6e6404812202c406001e0606561560321075030208103c0600c3c0492840b140d07940340201401d0b5014010002680d001510035002d020a505c02c00000d41c403010300740381e40314206980105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 829663902 1250 829662652 829662671
    0x130812030a1d1f060509090705042417070807030b150d14010b01080a09150902010302040806011e33091e05030d0801180902010309150c020708030406050a03 69
    0x112810100c1405a42d80c081d1030404080d510f0241c00c80c0840ca40142010045540c0782d80600001100607112201c00d40d11112003040107103040d401c40c6a101540e110301228583e20749203082a2030b01e040c0c0003a245e402403c03c180801d04406c03c02d1740c00404081c8000c0122a00e161910403a040001d00758030340201c12000c02c0806901c1e84401510029403260050030400315260100e0300808420094900103404030700850300d1212240501c1d11541e4010850700188081c00103200700902c42400300f2030605400740000104180c0a126039402440d00d000e402804955900c9540600321181d003180c2c2039615480a5007a01c81848070704e204925091003e8910204811081507030601001e91284d42c03001c08070540c11280321502030074402103410a60880302445d16200301078444e904240120040801800f40c1964041d1a680003106545d006040c006a40c1306142c40303404111a05150322070680d80c44140390035681c0d90420494000b4020040a1810039051540042040c40382001040c101a03c421104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 829665152 1250 829663902 829663931
    0x30f13021c0317060103020a090603020d090602120a0c03020712050309160b07030e03060f040f0618060e1e071806051009180605150a170408130812030a 67
    0x42442007000d101d80038003103031a01c1c0c002e00ca48504800d03200e40d840103001007078895001c0e0081d600184203e840d40c0d07521509140741200207404c440e4180e85c070303540c60741c0031800403c40b54801040004c01038190303441c891404560f500705440c0c0142d424402c162040000401194200c501c40086000e1460326070760b251110010b09181c04000c00d40300c0b16461442c0c400248019810f0001d1240305e01c2a11100d0102032a50704058a84508aa00c10102e0034118000380018841480c0c10810750b114200010702c83d003031f051440b031110a0411003243d2080d40c440c89810860740810060601d88481c0d640326001040d0798040c03a46994813449034071403c0103030707044d10b4000720502d0f049403001d040060701d00200b60915200080142059214004480c00f60a000d440c500c0d0b50380c007841c03050b10f4020308000d91030340e010b01c0c0c0154550710440209c8104101c002403800e00b00d00788400140241c0c010020340f03441e2016200f0209100d01960b2050015a0044440c8100001424241d9600000381200001c0081c5802c419 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 829666402 1250 829665152 829665169
    0xb0a0905010c2006400302011413020109150c05011410080615011d10031d0a020f10020c100804031205060d0f03090902040905150303030f1302 63
    0x50141d4240303030200c0b21a55000259031400640d00d40b8404481c0721014a6544510060f60106489a5122004499103030315002074071107600c004030303c0030079142c50403685c00c0c2d20114408100c0041c0d4442d8412100d146c01080015000ba5180e4891501d0705866400070300081e1140c81090007070401e040440070705901543e0009052a0410000c1c000300504886d4076a4601007160401081140440007050300e440019026128030703041e010040350030080a0040d140911108820541154000b074420580e80320003146070043c0080f91804070318001810801c00c84001c00c6011418107500c070788440e2015035560001100014816110b032603500011280481c1000d114180e810741007441094000d4665601c040c286200d24013075641c815011074803c40c1c200950b5016106107600402400030b84002c40d07a155080038074680310703040c5103102695030f09585099800940c031041103955952300b044001207078030b140001200012000341d0719514040030b064152244c041c0a091aa4856031401130854842200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 829667652 1250 829666402 829666421
    0x20d05370b0406180509061e042f1e22140403020a0c080d050904050a0e0f150112172d0712020d050d0c0912060b03190c030b0a 56
    0xf400041e031500944400030702203030304010050340b4010000310380d020080341c07440c081c44a0b504540e10b12120302d0811407407000301034403d030751540c0f05c01c1464447e0003801416895196a103d0008540151201004150260030003851103080d500d0350300e001e407a07441c586401c00480143d44217003506c003a03252584008210900c01c04581082c8041400285a00000c903030614070301c01c11b04001440d44034210192214422400e482c041582032016003000d20300313a04410ba0281003084002201c07403d07002c0d007515201c0030111258070b642100c0005006260700c01046400b404002d0325090140c0025921143d143d2588415150703581800b041c0c000150250481000c2101d05004040507040c52031004030400c0d6000105c211440342c400803598541c00d0000c41c0e040300031921a110380d41495141c8c5403200180c9110348034002040110038000c2009001b2440341090301d4042c0c1400103041c1284001c4c546069460460581194100490400003902001c10306007500e603c031114105945840e40d8820141c0740201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 829668902 1250 829667652 829667659
    0x204090903031e020c1002030601050d060b0406140906090105130e193206030a1406090601060912080a12092609060301090903050c10020d05370b 64
    0x410306024103505400c4903882c50400c00201000710400e810090803407294080c0d8800b02d811101740000304240ca540515403151040c10054605080c014030101125420781150b1000c1d08080360610070907901c510f0075401d60760444c4803585080c1c0c030304000805902074908124108000000d03183e4060030082085002401c24032542002800c1c02c80344800f06010610003140058540003003107590082001d070030108044c1c18408000c500c6200b607100f5901c0c0702d00900b0180c041c0b164006850002c1c2903d9504000c201088000e41140c2c148004294101941079119a0070416503480c20b000082c032000200c0c14865101c105169500810441514106449030704c0e400c140340741a4006c014419660010740c111325050b000700ca40d1925004e52042503009a6840b00d070411802e10044c40f20070815403100c48550300030f082c4242410440c0c1282442c0954901c00c850403175802017510364102005000d02c0b038018202481050190b0940300b000542c580107800c2e03d0010810021407103422480d90741c020168024041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 829670152 1250 829668902 829668911
    0x810050a0e1b03162a1709030f01091101030b090c030a060f183e090316060806030a3906030c020c0603330904030e030c0904080a03020d020409 63
    0x213240b198407604540d8150390200d406118000c1000b213440200584001c0c07a943c00d0480440c00d519182c2244aa41001b603c1c4100100440b294564082014500b1480302c1c000104a480d601d25101c4800114010303464181800c20701c030b140b002d03a0b48510341b81e441000740b13449030313200c5d510701c0300d420040c02d12a0b00101107075088100108950002e1810f60b850340d81420000d101c10110030035494055000744070800f826001d100000e652540d408800e40c0610140d0100c09420015054006810105a913030a00d000034480d82040100541150419034401401c4025007071a240a44400386000c610702c03807101d4078941100f04607070980110801007c045d4035044041c0d082030340310b140c003500800300c00d0340150152082208590703080c0350020480c1e00c191500511040310900d101d5a14a8144841402d00800e00411001031043c4d00c0f8070f42028400e50003581c4800d08a08681d0605092400d86142903000ea640c00742040046081c0d0b400711048a8558580140d031034061600e450000e0049400040714681031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 829671402 1250 829670152 829670161
    0x8070b0c070f0c08010e1b011116090504140a080f160b101706041502071703040b06100e030606093d06051c150302041b0810050a0e1b03 60
    0x4045500c10344130f501c0000c0158459490190780d446a02002403880c0d210300b5a005d1845522503d84651510229000c03079150078200b030000500a0782c20340090040550714020081846405450322554440540c007822114045c1d80740d00881e4403034071844c69456440000e91106404402490101d40c0e90046d070950101d0907c0403030307800f80300307821311540001d20394106c0501781c81a404218180203a9001c1e0321451b02800300031082d40a03421a40099580440400c1c084c9520b65a035801180701da4828843d21036103190407820401c103100c0881074042001101c802100d00c03a140000c076507812100840e43c041c2241e070707140706d078003044101d001001b007001c1c1c03080d910fa2540340d500d40c03c0c00c2d010302401d80901501c56150101203c081c00350001211b09000d95a000112110aa81c0626a124000380030046c00940b01d40208040d180d11003c845802807009503101c429a80c0612525040290a40012440c03490500066030300c1c03000d4045e00700c00f6000040401d074045280c00c0080942c08a070540286ca0303203403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 829672652 1250 829671402 829671413
    0x18050a060c02010608070b0d0507030e03040b0d06152f010914011103060112020906160803040c0b04120822031a0603010510150207180f0b06040308070b0c070f 70
    0x8004202201540c00e04c44080b40106010400e00c0030750714038922850405841c0310b0700c40083c02d0054442c0d42031503594a010040c0c0340084c0001d01c046c104c3c0e9101655640c000d420700e91304458450344070305450342446074032018182d0300500c02c1b0b1a10a101c0419103240d1940d0380c220810081030f0310289030f00c3d807030840d6241c108018400d00400c11291760000f08804c81c0b94881c174140710b2204803011270000e1101a01c5011500944d40500000200070b0400d03414018001e04891000c4402082602c0c11440802000204201e1414000140c0360701c03030a83d82000d1601030001c00001444400514800703002c100240211045000601c49450700030343d00c050142d41e07082c5100c1c0440d2aa24080501f01d4213000143c250030705000d0240901d06086205610307500c1c0a00090560b2010040c68003140101140050f01e410401d40c1c030500000010130029100b1401e0b03518404a072200068036008410038481000403c2500c000d694840307411480075201e0ba56812018207c0d40700d8003400a02040340a591074081c8003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 829673902 1250 829672652 829672661
    0x7090501030e152a07050c0904210306080c040b0a050f0f0916021b0d060506281418070c02010c060507081501020115060509120105090a021008090a0618050a06 70
    0x244001d820140c01807001c144d0301c0c1d9118038080600305501402c200004c90074142e140b030b81e12501031081d03144444080c0b481004400d04420100002a460300814085c540040c0289492800110780412103c47c004000c80c0001d58a8490b0701e08c69450602814041c0e10b41001075441090001c1884646142c44102c900950140c8500c1c0c00042c45040e078019280070041c80802400d8034001c00b01c00f0f690b502640d9982c0a032900070040c031f801030545812000d0304102c003a4103001d0f0782c0c200c21880c06200d041c402d4005010b010519064031800e500031003500f00400c101d00c8a03030065203034139003190002080c0c001606d4090740060020081032806c1d003000891980b008056000b114211002c002d00c41d54580124244da6032400204540021047d08000c900d0003103008101da2038005d00a4904d00a032011460300b140e0080703500c9075880d003010b40950114a000c00702e1004a821ba41880107407418903103403036940c1c0d00090800801407541c4100e580103114116108582e62170380441118070307501c19858040c0191 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 829675152 1250 829673902 829673941
    0xa03050a290112020a120308010602010e0d171315020702030c01110606090402120a0b040212121605070b032403010204050f060d020c01090f0b0f07090501030e15 71
    0x3000c2060040c1c0440d010000c00546240c900c020304100780e420248000003442c0e031802c089030311644840d40061408600c0c40700c801400d02907120014598900340002e4252100b500c0c1c051603039008200c55030b0099030000c035040c00ca180b01c410104a40d41e40c0704c0300e91103001a4404060901907442400509803c1d0a40003003035240c0c0700741c080d11250800c800054803000c1c0e004071043ca284e0020030000f091400c10701a00d6502c980000d0040003255202c01a85050400301c0200b0740c1ca09511900304015820801081141d100e5003030010002c07911091680c5440340103017010311601d0140900078909000c410020a005004101c00d05540e9040054242c81d020005440c5058440c0003002d805900f85018402c5e1811034201810140400760503004004980d403100c950103254aa0070b01214482140034860034403110300c43c405902c00300480341020341d0b0410004203062102c80042c010400100c1d400408070003210021308010600c40c8140303044c18200b0190b00404c008031403c82003080591783c6801e00c1c00050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 829676258 1106 829675152 829675163
    0x703120201290409032a0b060f0616050708150106080a06061b0c030c08010e060a05010f0b0325090f080c151605030a08060f0306040f0210020c0a03050a 67
    0x100c102506446e0180400c840e180c04000b158945160045c1c0200c1e040051135901000040c1e26200d40d58071042807a04c03503664803041200812454014050316400e41e0b180d88038000380502c200e0b609218600003c1c00319004503284d41114403d4a0135a10507540e0703d5002c088040c03040390720098980782100e20300c2903d50000041650710005101418000d4000f1400388940490700c1e00d072a0001e405d880101c0d2130480108507c17400d821f0740100719010050916100e0751507114107a85510b01c81c0d051a81c2c05a050000340005a0100034402038640e0941c1c60381700c207a1074014256990791405132098100002d4201401e12038050000b40401175031480d2a450301204030340e141410364201c1241e83d03005c42c4e80a02406124603210480000040d015401040c443c035180d21407418030b10007107501030301a2400403c0d1006841c030a021442e00d08401915000c0c5003aa20704c0c10715a50524003100340c44 = true := by decide +kernel

theorem cover : BRFrame.Cov 829496402 829676258 := by
  have h0 := BRFrame.cov_init 829496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 829496402 ≤ n) (h2 : n < 829676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
