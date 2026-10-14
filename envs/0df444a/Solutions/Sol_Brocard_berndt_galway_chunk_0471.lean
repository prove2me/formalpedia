-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:58:54.282975+00:00
-- url     : https://prove2.me/submissions/ffd91423-37c1-47e7-a91b-1363b8939479

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 84532375 ≤ n < 84712231 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 84533625 1250 84532375 84532379
    0x409050c01080105010c0b0402100e0303030408041a04150327030e090a0204050306070806010203040b1917070c0213020d060b030403090e040305070b040317090a0c08011109190b13 79
    0x2608003501644685e05021607121590002242c80b90515409641150b0f079001820907000c080325080f0300d80364041c3e00b42c40004144020b2004080103841121186202c4c42e04103001c0c440040500e00803481a040b2221805079004040c5000341c10400454451315002e004811041c1c410000000441005502142003030444070600d00341103001650103c9846010344c83c151516000c00e070f8501c8000e003a0b001700301848001c280140e20901c210b0340101b00c2641d5483e10344500590300e00385101c1100324a0702003004200060640c42e4001a0b00344210b100f5200c4410f00c10140d0240040800940480c80703e855013080160400040b80c401e1390b024058040c3c2c4d040d1a0301d00b41c54058402000c540240b440c880e8080208800264008210364129038822065800c0d501c46240031b86141d1135121001507900310840400814001c0019500c038a0390103010050700300e940c0c80c5105404c840c4841d8020740402400c000d100c00f181809179040c554510750042728541603503030340d40920940c2c1040c40c503440101388440301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 84534875 1250 84533625 84533627
    0x20406030c080109060b0415020f0a060b030c0301050c0d18060f0c08100803070303110705070b0c100b100309020102030720040b0f0904060f09020307030804170f03091c020409050c01 80
    0x49409061401307410003005040c00200f004900407803150301041242c1c4611a4901031003801483c0740342c0c040408481c07000e82980740c500058030210088a00920502c8220341061405018040c02070502c3c100c62454100130601c960050992070840030184861000004000b42c0c140c4034110b1040040000090100050303c4002c0602c4000b400206c0e5075030300705138103015003030000c821031b15016418280010841014420020740d409a0754018005004401000450060b40f00081144114507010b40d0544480c1d050381504503040814040e401183c3d4100940c8203a011b40e00210020380140110303030502580d503540040d20400c2c0040c01e81c003103a0541060340c0b98142402810528071007140d40c0b030720014502010584d00303d00104043c000b541c9414403480c0e1002e841d0f100c0c1203140c2e006001c0c1c1c1d1203e41c503420409944e500c43d100d907121200c0c0215101101d0800816580500540c250185103007240f24070400c032500a0202e002d03094a0000341c17520b80141d94610036000d031130780b01320f028010301c80381080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 84536125 1250 84534875 84534887
    0x2010e21030a091e09050a0b03061003051c090b03040201090b0a0903050d08090a0b100807030f02030606010206130b091006090e07140f1507060c050304172119020406030c 75
    0x40200e00c1040c51181d144c1e90500c0b0800080166940b0810015a994a4005030f00162000340d8034a07406004c0c8500780a0703800c24080c440001d50b07000f1012100e020583c518041015040d903a207c10028030400c5051101410000003507400a0051401701d40d95512404094001d51140b104000403030300f8040704100b00441030028008401440c11b2040542c07070440c0085403600d004103002000c1e144d02200150480c502d02010b14050808401102c90040c0c07689040422091080001e0344a40b0903400081c1c1c0e10743c400a81c00d0700c181c0da014400031104071a039a030038000110291840c030090082e00b102d07032036090442c8507940082c0851200882c1d801c0141c1860b500b00071b110b42080052201c0103070340944940b142170207003001540948081000d0700410f09810003d015000004180c2d0741484640310304aa4483e014500590250800d10743c80d89441020b6400ba100320541500305404078200820052289138130305034045005800d448146051890035000caa109030003400119a45281c45030100f0350000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 84537375 1250 84536125 84536129
    0x10e0703060e010509090a051f1103090c13090512042621040909140f0706020d080703090b0c18030105100b090622060318020108010302010e21030a09 66
    0x42420020a414020804110b000c140946402400008003040310b1070010040740c40810740000c255052400420491b05503c050103030261111414894105401506102124010040358001f0455001e20000340803110b4254680d8881c26652100001c0c040366051003a0a0707046030f000131b09a074441c00d10b04d401030300c900c0c0c00f0442034410440200003100820005003d0f110342c1c0d14090381c820300b00400c1400880c01d100f0317a000783c8c030110f041a07810f074104006800c0442c19821100700341c0b4100000020702c0e607522151441001c0040e40002c02c840080740c02031682b243c10071480e1402044481c41a120000115400d4484194820002400c000a140c50301e000003002c8204030300902c15414050b0344003003500c1d0a80680b0ba03c1c0340300081c088030281d6445c400c4a6000301640b40018111141c01e50042c00c43d0158800c010209052080080c0581d21049a05c00382e02d90503142c0301010b9085400456900d13034016140ca030490750042642418011080988265180010066550340b2801100030b000c02019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 84538625 1250 84537375 84537377
    0x10f111f05090a030e090a02040810051602150103020105071109090607030e0a02030c04050916090209041104030305071101120f020304140a03021203060a090603031205100b04050d050f0f06010e07 86
    0x103d100c50300080d440100c80512407030841d011113117a12090007840c001e114a600c140c071180305154511002440c00e41105115180000a0a030780e006001c01c140d03142e00c00f0400c0c010103000048010f10040d80a0030190860138051420800e206515001042c0c6400040c2c5043c60942d00c00310402a0159140c05024850b9400c030b805009038060644c04a41e9801010300c800e44147e4445000800340001040703482c072030910000c1165030300ca135180c2c8610025480341e5070380d030b0180c0d080548407041d220300c5e071003281c085039032650764a80b6000c09502c8000c000d09104200b64100030b0150b098200c0c08680303016108415824440040c0e49092078580514030109900327000c07106420071000000482c0d00415075188000c02d100015a580e6641c40014502a1643d005080102c0c0341c0361010041c503602040100d15800ca080d0300f0800c60701d132215205000907440c07042161a180420081c0300300c0c102076500040711407003030f0110742c5800424505d642c03c06204c0c1421001960111004114041850300c050340c1004007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84539875 1250 84538625 84538633
    0x150e191a010f0309020328150b09011205120a0504080105061008040813030206210601030b0f060901050405040204030609030f03020a0c1202030d05100f05180402010f111f0509 77
    0x140d4006841c40210380005410315070381c1c106900554805008412950300006406002d540d0400070315944417902a105540324a00c0500201c0b0f80e80e444d01c140103180700024099506a0710301010b26900b5045650b04a5560185500a80c41009010040c12205826403210346c1c6503400d0800d0b0300d00311f0304014581d900c603070007241c26490002d80022480381c0083e003280c0441d5440086c0d007190a404003e6031300080d00003400013615403450030340c0c000028144410046210554484400460a44075601c070f000c0d40c80403801445402e24940500144807004040c1401410320380e8400015040340c009520645d02140c40743e81940416a011096800b840c50701e050440c01d00d103a408008203d415009002007840c200c2150900d50113000b0000d40310f085510007402e100d149460810f200b0300712040e104681e030b10a4440780206071444c000540032015030f0866400f40c1d1075601e42c1c0044070390b80300f0710a2880078040310714418803402006012404800300c0c0b881c2c000e1039021610060404440000b4814002030704 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84541125 1250 84539875 84539921
    0x41802090607031b05030a030c0906020105072106121202011407051e0903030c0f0c01111c03020405030d170a0e0309010c060b06070501091a0f0703150e19 68
    0x41d0745025120314a802d403502001019000c07618035001003621a0241451001103135840901d9410b80015441c80800e81e07400c00803942e03980e01682614020f89032000480c000159034441c40f014840002e025401400e00400c4056443d50241c500040d100f00c1903035200d500c2418801901d809009564020452807202505071030074880007040d6010701000050b090301001b0b2010601e13980c0b001518030741c0e0070060959682d883d4104800e952030040100a402e0390261f502d0050407903020f17034480700c0162a9070028000040208039002c2d00c0c000200c40640c1071603401d0201103055207003000003079900b205c0d42d01e074031014181074400c0c085000001002d4800082c00e001d4030384005600842900d504800a00340711406481c0d41c83d040d80501078408105400c40c030301207015402d20005400402980303000712114666500300e8940c13010240400c0f43d8110b02803504001085040c1e01c40d40c48080310080350042010040c0c0c940801d01d01200d415596800b03c0d04040700100d0880c0030703a204d050007014400c036582c04d0401b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84542375 1250 84541125 84541129
    0x3050c0607020304080d05160b131103010204150e04060305190318150f02070315060311030a0f03111204060e03060702010e1b04110d1d011401030b0901090c080304180209 75
    0x190340a0031007030070000c7c0424140e46403428440c800703801c641d100d0702450b00b929154107000104402042c06032041103030500c3c000e126040c188201c50030743d420345241c0a0114581281600d001c101d07170101319003080d500c56001011410501c500c003a5460b18811803200d03520305040c010442c0212084003124540a540c040100d15124a00d0010f030f20494103007242001d41c0e0701c2c0c05034108140c0da400502100c0c059110b0404030351541e8004801d491007a11f9118003c0c0592041c55559440c001c0700034000940c21069001290080032580c820402031001c41e42001081203281207160803070752144002c40c645055080d10380c5424459680c1c80035940c4000c0014819000c03a0341d9403074079402c0e100b02d80c080407078481d0350581d141d58001403445c15071115000e5079180d00e59000d0000b051502007441030350050302d080c0317a2004418042c040380b1010104800b0070710b90071a107505500700c40c00790803076010703642e610b2500c0002050f8440240041c8901e0000e5500d0b140350606640c0840b11004284984520400845d1856 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84543625 1250 84542375 84542383
    0x105041a060d0201030906152408040b010e0606221406030603061b090613140a080607031d06130203070506070507091104240306050f0102030a0e0402090a0303050c060702030408 78
    0x142e60246008039060501d81004401800710396401d103868400c915000c12002e5818160402ca200300e044107502440c1182401c448802e0282ca00030b081c40a40c100410140c00346114464102c01c2c001d20080ca050b40a8030403441d14003480c00031054446105104014100725038010518103003094400916514081c80080c3d12844000c1907503000c064015040315400600d64140c491600b40600419a00c18841d8403500c2d408120703104030300d840600d00001a1190402e01c000e00200c0b5000b030010401502c0d42e0000f0350140880700300085400c58040c00d051590001045a20300442d2480000f04074454640181400c1c81000c0c0c03c02802144204802c030700203640001d00008845071004006007103c5149001341141c030a55004800c0022061b08180120716255040541c150a41e1010804d10356914248a2607042c04214580540c00901202c9041409105111951500100014546007044002810a882d00d410a0b0002031000c5603010700001d040048582103240c6000450403d460031a02e60341ea = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84544875 1250 84543625 84543649
    0x6190305100e0915070e0d050604050c010309031e02010b09010b190203090609091f080f0d0201060608060f0a08030c0d02151519090c0c060c030507120b1305090105041a06 75
    0x4c0400041c0000701c0e035a2041c2c1c801d01ca0490020b06500c803d201c20305001c0e607203c8003030701c1c03c0d22180034802e00180d5940c0203104036140d8031360640700d900f0210f03040c034614200007501e88001410340d520f4800b80e56443d0f4031a0380d098040c05c070420141d07031215030000710500103449c64450007082d507104000780341150303503284c0583d2803010303084400c0c02c6c0380d55600201c1c00d0940000511880300c050140404182c4080100d0410945418003040780d030302c0354480208909a8030b0502c10f440106800300049541c505121500c91640c41300a0043e51405a039200140d10b1980082c0300101150480c0521481300d960501040390b000700003a414175040d0408544d00c8003140c4441c54001e110740580341c00340d09240e00c0e8010202c024031101c442040003079020000079241215252080710801d10b04410007800c2802842828003e160903501c254070101010010700041c0074100c80580d1100800e01c0c6105e201e0b42034000c680c13190f01543c001090604080c501720030b41542e0491210480710300070301000403603100c03040b002030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84546125 1250 84544875 84544903
    0x60f062403040818031617030d0c020f0607020a1205030a090507030302030406020c041a0609031905070311061c0b03030702120a02041409060a152c010801020408030d020906190305100e09 82
    0x2031f9400c0700343c0740e2074554030408140840460511018015950300422070016103078680054503c980c0d00d151040762980c503010002400301e64044a03c01026124101440d4401c141c0c6e0030003e82c0b0051515a24a448450b50084005070b00009052000c69414441702401d401b09440034882c46040b0700e00c5a104001c0f4064403030052001058005080c0d40402c112286192154020f42e24141036080917030301c070a00b900042d145000b140d220040e85003085422207000f1031680062141183c80701c00940007910843c505070354544000d0003444056510303070680020350700440004104485052042c802a107a2404080504080d682c041100020011412552000480c1800a00080308002e10100704603240c2007a000c00f50f14500c0c0382d0f4140d040601e4500b0243e402503610303225070380c0d0b0141e083c280d01c00e50003140038540003480045001d6450390003410031580000c01c521304001240301543c5496141142c04400a40c42c0d1082c01246000e40e907508014202105e007450b0903181c44100e1986e29079100007001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84547375 1250 84546125 84546149
    0x81f0c030902181b040806070314070c0201030c02070503030f0d05060303040b03040f02150d0b011403010f0501050d06091107030e01080c220302030601080f0f060f0624030408180316 80
    0x1001e0310250420070b41d001c1ca00c07049440c0c03136039103034080b43d0f40d1f5401c1101e103400071900e001c151580e4003488250351031017088a9902c404260225a00450103042e04000c00001e500c10102c01084c203940500160141118081c005516400c0049070842628009000c0c14002d800c1004241b003000c403140100c0341d0140c1c00680001862540f440410400c02d01002c400d00c51100200c0d00000b44441394100f030034618002d03a284298100c031401412240d01c02031080c0200e08403c00c0c41000345500403000f0340700320b00620300001042139584054505641c072810300b00b8141000000c0310800c0541003400c01c000001d007842c00c5009840c1109c1e901038148174844d80440c80f6000b0b1028050900c3e070711300920740175503400b40a49900f9650340034102d0307407020100040e441a018520300120188400640ba038452005608804815115070b418801c4a18417074402c00c04030603040907040681640d00d4001d600440c0310b5580a561842014007910b40d60800100b120300c05e402c060f0300700c03542c99044070031070381540c1d6584200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84548625 1250 84547375 84547381
    0x50105151909180501140901050a140d0506090601051503071d03010b030a0615120203070b09030a170706062120040504060204140d031e09081f0c03090218 68
    0x2500c19aa080d4000e201c0201985403c1148400d1a0000c0d030480d00d458814814982c503d00c100b10f0400000d014442e00b04200c80000c01c03841c034120887d694030a4000e001842c8c4080a078454505010085030000c485901c0a40104147d040c110084c007220441c80d092a811420241c40061400784005c500e105440c80025512070785a50a40c0025682100102100c800c404c07203242090142840c00d040c003502244010f0005022001d4070400c041c0385a004014002d118141800c0c8105130b003111800765010b10035603102e000007542c1c407500199580e81c80c3d000079880b081c01c1c1c54000d007615035640141c4401e1500f564008600144800c0c00d0895a5100383d980032041d0560502c4000551185569580241080288014401254000c0080ea1603062500d0001c0c0c0015050107010283e403000240003c1e00e049188140e00d009668074004a81c0902d010307400140c1d64030440d40790100e04103181e4168042201c0c5151141418818001a4201400c1c11b0007142c2c1c0940004028002080201c80900045800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84549875 1250 84548625 84548627
    0xf03050a0b550b030d0c17031f0308090907110c010c0302030c0d03150503010507090308031f0306020903010e01060b0706390201050a0b0609060d0f0507120501051519 73
    0x191610203070403603541c2d41c2c2c80020907001c1d25010781400e00078090801c0000440b032103807060b103000c01e40110f4410140d00200000e0341150307100400001d00d50041d01500001038940181c16401103020385000c9442c2c3d800c0f01c081213061140a803c290a201142034a0342034040d012038443c04012003400c0412010080c2c1c20f041c2e0551007806000d00c418068203900014443d00341c0e001112124020450a0040e0346030b0050600b215400e41d44e100c08500000f400700000b0320068020355100c0d103490b45d040104540c5c1d0341204904800d0703410454a4035008219400c06040c2403003004030842ca008001c0c401c8901e0300300544404c0c841c440c00a03040586809098006465861041e1908619000b0007107031000045501c1c6e9000c209950b5800055003844045600314020b130185e6402910014103062400741002c04002055020360400030baa2031700c43c0c602d142e00b4180f904c106449181c40340c5541d150355661001503c00c03580140c100911075001c041c040081005003000342c420051001c1d030303841150390306410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84551125 1250 84549875 84549991
    0x16030209180703090b010609291215030105010b0301050910030c05040c0201060e0106050c060a0b0a090b010e150310080601030b0c0a090f081506030321060103060f03050a0b 76
    0x80d01420348007010717000007000da501a10a030211406412902010710040302c00d81c034100861882d00c0340c51002403001581202c44030700c0403500b15a0040d00900c4030000d4201182c00e6079426032101d54412800300c0100002e0030070404a5034008010015020b03d1400d6950707820b041e6401e4025140210f81e51001159058000d40c0540c0180110752003d026942e5a428018801c0d4840d8103030b0801401640040b41c0024400c0c0512908804024400084d0301c0c00c20070036a0060002d10301c02410401c440c01c07000c000742c0360f0300c98143c0200a1007108a030741c1d241201c081d0003d1074480d40300208551050004001203001c11110740d403c01800c0b40c1c0107070f0760180c00f13000f2182d1102d00c4e0440b4425060700e07a00040d001000044800e11501900b00303500c0317243d444400b05901c0b8011618120082c68240001078507121003040d900e64040d005050000340309840c0c640413a140e407a142c00407602540074200c08010b00860f8030320158018500c1c0e101e44c21140c4076400004201c1c260707041900c481941e50700da1060b1984c8a030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84552375 1250 84551125 84551141
    0xa09020604030606061404060206010605030c040308161b14090a02040503030325030c02030304030c0309090e010e0106090513082d27010207180209060a0816030209180703 75
    0x2400241c596403203060280060200703205000c081000d00710f0f9020048181c4056408940720394002c0c0440b41c2c40d0480984003644001d1982e850f12104010100c00600100060183c1c041c12914540e95241c0520b405400c1b03080c150300550344100200010007496001e000602c48011065800040780c1e00c90f10b14000180c000d50700840d42c140404000c004a1085103e44940207e409a503482088892440e0507402c862198010320b00603001000003c1c0400d000e000c268070014841d24000c0c201300e540c3d40601e001c0b0303040e0170341c50750090351211003424001c0c2c424025440030341b00e201c0c020400c0342407520210303494251150000300302d0840491512400e90601840011a00c40700c000500c1160400240102d070380d11190003251801c40e0964000002030a055000710710460680007850b6460901a2000b490030b107140d00107015a8007000a4a06a111840500300d0a4000e0702e5030b41d01810804c5030340110300d8100074044201441072002c08410350316031910700041d00460780440c000d0380711940c040b00688422 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84553625 1250 84552375 84552379
    0x2240d0f0935090906040e161203030e010501080304120c0b03100510020c091515120f0f0c0d0b030c0d0b06010e010c080a0807091d0610020a03020a06050a0902 70
    0x424807604240d018040d8444140b000c4980c0d081e000c0c0300c40742507800140034161085030403030140400245d4500b0a03900031514650340904460080d0207031000c601c420880f503040b451050012000020406070903001350741594401c0c200a03c125030502454580c1ca000c0c070b100301d6829172142000c8000340301400c40391801030903603103c0007941da08d000d01010030f00e01c40078030500c0e01405010b0946e0b1344042c40400d41600407040100346244030b03101d22540c03050b850031140644c0c2c2e11044503e13041400030510340082402c50b0040780300900614000d5011000c00c840180340580c14004101002100d180000840311411101000007a2890701400464a0b160305454220741100300110b42030b0511a41103a0144075181c2640d400707000d402c83c0e0004550321031500030000c0005100b800303552580c0307000b021040c6d4481a21b240108040d41e03036605d500c00003141020269891134600042c8816420100c0c0d0613000c0b45240e000410108283d60b0b070080d030301d80700400c0140c00c041d41d50004c02c20002c03494008041040d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84554875 1250 84553625 84553643
    0x2060d050f04030e04020306010206071404050603160e0306130314270a06030209060d09020301240816030317090c0d050c03070905060d060e0a060507030902240d0f09 73
    0x30801001d1107807501500e080d8082101c0807070107a65850180200c91043d40107074081c1400b600d0301c203800d0b120790000b005141040309080c00046110340360480a14890040107200c40c0103151040d0001c4d081c01c42c2071800341d020750405d82c104210580700c1c02607004000c0e070614100920311030242c0c0ba020b1a000d0240c1c10106004048000d4458110003101a21041d00c101d074411078080e0b944005804030700c11030b030b0002c1c1c010005204603803154030b003035100001260014002007104180d03603040303200404210360595003c0340007100610001100308003000345150b00c600090b80203420b582b0003401c2c0d818520314407908010320200189039014140020300c01d181010701001e004680611f4a0354480c101103540601901c03e80d1300000381d0100c1400703140d00404000d40441c0080700b080e21420040c28841d20b07a02c02c2c510032401d8072400900f440c0700e02d074419100d0340d500042d2051144100300c1076558100000003410702d000b16644d4800f50b89412210000150440003d42c1440150302c0f00142031000030103400004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84556125 1250 84554875 84554881
    0x307050310030c0b0307021b030a0f0609080a050309010b0117040227130b22120203270301050f060f0d02031c020d020d020114040b180d120e03040302030604080702060d05 75
    0x4c00000d14020401e83d020f9885951005d210038490300003840601d40c0c035a001c50307810f030b010440305200b1120719130241c90086400d0707019442d544619481a040c040000e0300000421009440a200360800d050007440c0c03003c002d21017001070181d1700601a10103440707404400801c103c01210003400d0318000003c080b60f8000b900d0441c8400741d00408081e400c5d140030748642c0000300c403405c4d00c0702229070300340392030407102d80085160b00d0300c0302c4218103105400c080d88000c01c20180c40200d1047d00008800107103540c5403460014030145400d458002d006c00e070000c01030500780710265940c0da10200316018181c031182070440250000034035100d4909003143d0300e03e4581c17001418607540820740c04606042ea03000c640c441c9254074012800c8440c000c40f441800c0d054a004500002c14444860390003031030500070420404084020181000c100300d0740c00e0003140f60190520b05035203050007441c00c94140751000e1800c103417558020a0702d031f07040203000800303a810004c6c4820842d9039140503140c400a003964200214a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84557375 1250 84556125 84556139
    0x3050c070c0b2106090109151e0312020a11040e07030204020d021801211a060a03050f01050105040f050909010e0f060105090a0204150f0509060706051f06050307050310030c 76
    0x1d40f20402c00814a045004114404071041c03e4250080901034000c855503807030944014010011880503541e0424546400158050310a850381203585980c00407144c01465407070400480d40c0d0750030840040d5084090700c00003240c40c0c2e0800c80612101603a0110b4648841c0540500700b90039508004d500c98070105054404102c15800381829950703018014102c6080d4a00541d01500c00d8105454102d60307861500ba56140f45d5000a00c8000812644000180c1840f00241c1580c1200d201c40c0e000a99650800480030714910308540104002c1c20554507113820042c040c10803c100e0300032a4040e40d03400001c0780801301d09501504001c1c0d6110306480c5560404116981c89100a00c162482042e42002043d4a0342851003150110303400790300212031806400c034040d11030400066405051000c10300c603000d0310b500d03510b0060012a104400024513440c0580090031100145540140d0034840ca801c00d05c082600481180d41280701c60401c0c2e51260399001c20315400c0d60301504004d00741d40c901c00b400640c007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84558625 1250 84557375 84557377
    0x801021206040605010215131703010303020a0303061703040b031506120702010b060a05030708040201020703061125020904020112320a090b060f0619050a090b0f0a03050c070c0b 78
    0x6020112003d20000ba0340707400482c0c2c1c0e162920359111504009502250500301042c6017007114034820115a40002c0c4001011581034209a1083d40984c22140c104030406a16110744006014284040b88619007107113180703541c0e40a68051401d1b41e54001001c00c0b206600031410494003200180070a9a0704c1c00070b615000d9400040d01c01cbc002643c20039807104001c0c54028280c4000d01105c0d55400d0440d070356400b04551800d03014001340d0540c0198040400411210700800b000ca040400b01c0d29a41c07c4810f001d2070810300c044582a031505059001c1d80b0040e17a45120058110b80c0928ac1403982090403100d490050103000000384805520804909902098004030741c00000e0f51881c0e02c0c45a600d01345174030180c2d20358140082c02c1c55210340009400b172038114070201e8240006441e103400c00420981d55501024800c408030b0200703801140381c2400550000c2d46502611141d01c0e854100f40001c1421096405000d900d1010703d61180700240c4900c02c02d03000d64801d030340c100034451980c56681c10401c0d25 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84559875 1250 84558625 84558631
    0x21b0a03020a03110d0e0402091f050307020d0905090a0b13060305060109050c120109020a0c06150f060c03091a0c0102070303050109061703120402030304050a08071e080c0f0a08010212 81
    0x401d50585000b0744c100c40108081c3d59402c0c03a902c03004045100d10701004002e40c2711461107603000c510040d000241c00303c5051421341d140c0302519110b40e00e06010001038500301500d51880c0410515800a000c0c80d200ea062060b0800840c1601142007542c440014031058190010001610314040d000400e0250003c1e02030b049a4685000300050313241d002844196101d6000d0004800d14050010440391409074001c0060b0845c915010000d071005030b039560156072101c18009035a1100c10002d02c007114440101c0801816079060200c1c0501c6580d0b8040e00040d624031400034071401c0300d110040f40700380702c004840c0c45004410085650b200c20345400b40007004c080c02a840003d01e008000300b0140644107441512034114401103042c07035802d043c030310701001e00100f0803070b0517020034040016130b615580a960092300703004c00a4208182000300303900300c80d181c08001c0504294210300400560202180c094442c19054070200b0080c0c9110004c00d0b88011580d018400c90b41c400500d00b17071000300482c80790740 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84561125 1250 84559875 84559877
    0x607020102030f01051c0b0c04050a081b04050702060a050402030c0d05010c02010605010302211506030408030103060b0a060c030e031f06060e0a0303080c0c01090b0f37021b0a03020a03 81
    0x101c517622801400245609401304a00c00000e120866020404204840ba070100300a041c0b1803030152120085a4000e685078401c3c01e565100504060758203060211303408040c407054400b00841c1c89e217007c000356242d0000c0d01e1003909941e0341010070290348043c45103221050000e001e8040030b480a1502e94003c1030050380c004015445e025010442c3d612034000c807181c030010050f0044404080d0300740c010300e041001d40072800f107091041a54900361104009140f10b940604100e6850b5851400c1607010744a5840c0560711509040b03109100880d045200c6111158040c90b104040c8028400801c0c5042c042c90581d41402c1518070385400505400c0d0030281c1078803880e90306c1188420004007441080c81c141c3c0001130100c0e0304a0700007800880766070003030030440c0107800012807094082d8841c010043c4080e5100c1c0940b5103000c0c1040500804070315403420a03000c03002d1103101090422804101e805030f03490b146049030340001d20442c13030702c0300c018140c000d03450f001e0251003070020f50380f401075030720341e8110340840c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84562375 1250 84561125 84561151
    0xc06040b160e0102120c0c030a061401060504030206042c0103061a06030c040b07080f0a020a1103030c0a060e01022b0c091203030906020d0f14130201020c04050a090203060702010203 80
    0x300550b200d80e00541e8501c1040c1c00811001c161503080b00c1107500722a4001d012440381a5003a41c03203940800c44100654055640090b000c8205440c034070086005070081c5050003005c020400058858204035000c03200fa031414003078282801e00781c01d045600010042c0a5a004100012062141e5907201e00e00300c8440092100f495516842030100e64041285e0050450400744020018a180d444c028221580b140100d54a0729400303a01c460300d0740d001590a03000681c008403450040003002041c000c85040b003200258141074101c8805c0350b03940b0700044002d11047e00c880b000c1c4035948003501075903490f000c500c403950081c0721304600c2c2c48900d41c24050300420712402c4c00d6000c1d0442d80141c80c54002d4441e999205500701d80140c609a016015180341110341e1b075400c00485204280d248119075000319541008102c0c0c0e00719000905e4041c0380940200559a0030f0701d00e82c00140e80006d1407155504040c2d40c08910340d9548401d2381c00134600c10a010f0f4140c09800108410701da8194002c0d0701c00d00021b0688 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84563625 1250 84562375 84562411
    0x90f050c090114131508070303050d050109020c0604110f1e03060609010602120325030203071d0a060806030703050307120206010f0f0b070507050316050a2310050c06040b 75
    0x310341040050f00300c1c0e00710100c800782c0300c2c640b1400d4000407101c088030303180603044a42e101031491808040f94815400924042441c007580300060140f24014420340006609212540060307584480010b0801040643c505140d940c1e103489003081c050588400600006007a985090103c80b2036111042c03551090181c040010b54a01e808a100c605030ac0c0319600426030700090300350808080c2e2024152002c645001c041070010b120b010044440340a1301170340c002d0703200d0500a030080c1000c00e0706074a20146402031041107500fa00c80340d0b0008204e9009281c0003c954483c1c801103803c000311034101400e140400903080c41440f00502c103040c813140e050342c00c40345e0aa984102d004200c81503401500c1c03548003445410440e600345c0030094501140100e0649444075504e40007c1d1503c44102d144c00d0f01550103640c02c01452600a004a005201b080114100c084800e6024100003180204040c42440c0c00c2c114012603078810015100f5108459084400b0fa00302070030030f03920320340701150400a01e020316002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84564875 1250 84563625 84563639
    0x313060201050a180f0f020409110f04060b030606070204061203051b01050106090603020f090d051c020c0f010309030203070b010f0f080c030a0206091203070c08160f0303080604090f050c0901 84
    0x91100e0441d0014813805441e00c0c02ea452424079503400100b500c0d9040d00d031142002694070341c8500030000740f286119644000d011006d00c26100c1c40000054440c0707142c241c0402c4145e04c0c1d201183d80c0301030100c0c0e80716030700d580e07a02c00140105410b030491052800c2e030081c18810960032000034025000369100320003010760810180c41c03d0311424060070740041c48501080145500070340180000f0740002c0540d60501d800d034070104101501c2841c090340c10394041000c03030b00f02504000040340c1e440104d2024007120702640d80455092030082400d18101951420326a09151003841665601c9600582e86180b95130f407504074101100c0c0900a04034a5200804002219480040c0004100c10058081d1459507455020801144c102070082900715070002400708541c00213000a281c410700c81c903100c2120f01d040c03400d180c1ca800307007003a080b0000d1342e841030081c012500002c1d032210842e030345481c000185a607242c002c80c014011a54004001400c40311119042000204145003030400c1521601c4403070f030303907048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84566125 1250 84564875 84564881
    0xc0316030c09020d0608010507030506010f020304050f100207080613120e0d02041d01060602010e0705120709091e08070b060a061b0c0305030c060708070503060604060518030313060201050a 83
    0x48010050054441c0c100402040d81d0058000440d88550004040b070b5141201400d50360121001b20009544004000d130940c1c01c01105806000148002c50030181040702255462030034408551107100725a6000030414801c00a0102820480050b605c15040920195074204a1040120369180d000f0410642c5980b040c03c820540ca20b00400c1014440c0c415006e00c0b00400c0210000070002412f1441003007200c000b40980c01c01082181e00000d2910b400b66103040c1000c07110703000740c1c0c0f0441d5041090120344500140090546140300f400123400111490500360741004156580c1c0c0c0c1b403560316025424440440042c0c80402e0044104601943e190402c105001d4030303d024890101d14100c10180d0803a01d004c0300d800c0b10a100b4114030a0b01c9403207444644c03841d08440c0a002c210f511030801c20040740d50200405801c8601410894210300308100016200c1c080d9014600c10814089404c1403800e1640c102e400036014040d0989580e56029103c079401031000b8000da0000d5070070320b80403401c1012144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84567375 1250 84566125 84566129
    0x6080603030307142a030901030509010204030f0803070c02030706050c102007020f0307030c170604020303030a0207022e0e01110a0b130b13020901120b04020108070203070c080c0316 80
    0x10341c581c00c2c80c0c40b0050309105030b50451a5500c1c01c0c901d4240780e01d2418036090042c5d9140200340401191034400850005082d200003c0010080364018002040084c000c020107040c1e656102555940f07030f65a04000315002c00c601d2502035032601c10710a00154040e000402860340d07442c14816100d60898a05101054a88144020341c0c030044140314824110400c1c0040c02c0b1282c40240884800055680002d00e442c005810640384400100c0302000b1800c0d002c18040b102035000302c09005a45010380001e0740b0390200810002d03040741c001072240304540d02c0c210021600160003114940004001a800c481ca0503c15640404030346115544062907000f280801841e4030b40e44000d04813001542d86510107401c010704114400e065011041c0002004510407074840d12041071006403840c800d004000b060007040e882405e0b080ca41008100120b22303001c240d1544030b0340a003404603454a482c241203146129204019011030105880411101c03004103040425210441c01c54641c2c82c08810080403007071041c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84568625 1250 84567375 84567377
    0x80a020a080118020f0d0608010e0d12050a0603050102160b0601020f2505030a200f06070b0601020c1c020301060b030709090507090b0a031e1107060209130e0706080603030307 77
    0xa0710040001e40f44011041071250b124442c050306191000d640044107810035607850000c1c43c1c0310b070410f1000007000d00c41d2a0a038005c00b402009462803072040945261f81c01080801010b842d800051482c54250308640d0080d64040000c5603100c07074900c03401310389212000c801c83c0c151582070f01103a40b541c4005038000000c6189400f51590043d10300d00f1001d07800c0c001e400030040e4600710800040540d024848826001e02405004070109a2503804d500e1741c190181e21184110541e08440300103840704000d5410b55503000352000c40503100d00d00141e14010212a0740755000901002403050004044d03000030201e0701c290000c0c440d2685561030001103000c00c60300d05d00000c011075410054110035400407a041802c03421f110900350348807081c0b01c88541c0300780520404a5140c040c102c101d103408462045008040701c02c1040074050100c100c120038860100040c2115801080041569507901c04040500c0c0000c501002400d400448640d182ca00521800f000300c0c2c041800182141004401c91b0310401503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84569875 1250 84568625 84568637
    0x31f1404020d060509011d07030203010e0a0207020d1211060a140f13020901091406030a11040f020f070f1a040804090e0f12220311010f1704060606080a020a 69
    0xa15400d00c8029044203402901c0140c45610005094580d0f22141740070307040524920402000390041004041005000003081601c100b004000d5100c40c85a1503412607166035026a03500c58a0002a2f03014404d6070000d401885403051110b2015004103021f40c00c85400800c0d0340040d41c400340c0c00800c0340d1b110000c2d0b07603a0100300000601c1001c8000040c5038081c01c440b2010340c1c01342030740e00459000e000c00d030080b003051170703581242034510400e1000150340100c04500605203108141e81c0d0701d028100c6c40d95400d020303036200c03203121a4900442c2c060741c0600070001040d5448900c00d0170100d0a00200180540c0d28800040d4200703042032144e080d062266810143c09450145050701d03078401490941403000103130148064103900c4c00e03000d01c0002100f110702480f45850f280810059a40721022010003030108403400c80410019400c0b801d550341c1038a007403c1020b0100b603c0c1c20701307070fa00e28284d00c04e02e0304050445080000b0010aa402107050303820613556191035030f85c1c1383c501d1000c03071080d0b461440100304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84571125 1250 84569875 84569909
    0x17160f0515040801020304061a100207032306041b050319020f120a030305010509070c0c03060b210102030702010c0302040b091201020d060e0117160b0a020a0c03050102031f 76
    0x1070100800ca55150307244500351038503030303940da92a0880e0015507084a0302a283e445c0e92600410b8480400ea400d1000c8489890801000304083c1d554095440000c084550120848140d0f152241d42158603058080c20b81c0c2a61400b07140c011800550b0f40703c00507881c1c0c0440c5000c2401e080000b03107203217403c2076000070300100741c055000c10100d49003001c1c10940c015000000000121024045059082e100e07850100e090750511302000110840248204100000b84540c000410814803494007100d80080000804d445203c01040312107203214508201030071003200a2280100541c0150b224241550007049a0b03c8034800840a1b4855445921003540c1d09000c40000e61070000d444404004100e0001840d005600c0381d20001e64801d035010080201d485801084422030120b15400c0d0a40400c01402c10640300d1854410340340d006000e121400c480c04110902d04a000b002620496900030001003a0720384d40b440d015020b9881100e150000f8060031030300031041e0480c0200e03602510001e1801d006490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84572375 1250 84571125 84571129
    0x1061b08090301271101020309221b0203071109010609050f0a03150207020307050f0a03030c05070504020f04060e040c050a030207020a0b0a0c03020f0f060114061317160f05 76
    0x28020700305960b0301d9540c0d012408190500c940406007030080903a2599010345050400480308102070360041d0554004000c4418140d4541600b03c55140d266043c00d452520382c2d9104c4001062070712081e50310220a20400280b013a0004084e00300300344105038801c0c90110074800c0c4040c030103080c81241c0101d07001d864207001d14508001c142c07074181d40c081c00100407246d4a84880c810038184400d0061503550014008084d800c042c410400500000e44410321f448282c00007091742511503101c0030781007043c14a080402c1080c20b0240344001c1900600a54640a000115480a41c014420400030550031011042c1d24280f80c00340300718240403134452038144410003070250302070b40c000e4404030b034882410074020422107203c201402c0803400340d03070311500e50425914000c1e00c0e20741c0301b03140e8070300d40d511a900390030a0000c002072881c19542c40c00300010b88101410080b40d07250060b00d50101d20000000b40c0880c03030060040314082c00810740710890300300f040d01034202000300106001e6880300c90002c0390180301c54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84573625 1250 84572375 84572377
    0x6030612100606030e070e0408121e04061a010c05060703050c090a03140105010f080607050a1202030702011a0a060210150308030403030209210d0f030b040e07030b01061b08 76
    0x4002a50141d03840c0304001049001115900e40258001c66600e0380c409568450400151016240040070380d00309007040d4803498080d005030545c3d2441c90b454a000115051a00e800c06109242c001d100d000040c1010300d090700103044844510599544400b24400c0c0d10b42c81030402405250f08040580002e450b0094110040c14004092030008001080030708803503280c2c050340c40d00840c0070f151403560011540f02003500303540040c0e0180070366107181c81c020b104900c00859401d0300301c0040c2c00c01c1c680d00c503048041920300712201050741401d148080208540c26806402c119010071024440c3d1508a90100400400700a20b006003801030b8442d0390315151404040d40614405904034800d1610341e5501e40e1203140b0b5500454040303001079000b04e501400f60421206507040c0c00410704000c4d0402c5000c929491342e0301040c5002004000d00c0c8582c4d5490540660b1019040035000b9006001400304002e0050365111184022070340c20700701c24000111544a61040100742c11080c101800110b050740b10b0001c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84574875 1250 84573625 84573649
    0x702130504050f1f0608060103020a0b1c0207080702010906021609091b0b0a0201050c070f021e060c030c0c030304080705060a0504091811040c080c130308030a020909010f0302060306 80
    0x6107110300b00d800c3c8884002040018401800c2c40552503000f0700401c0706a059850b582c1c04280107601c041c0c010b200698446031000182c0e1a07100748192545040120009142e0003002011101032000030428103011540c802016082c0c000e80324009a1552484201c3c1c3d110060102c2c0c000c1c0d00310811050010403003603040070003424040e9000c40c4600042c3c45010301d091303c2a61084151a40c0014264049038081c0a0310382e03c16038411109042c41410f40321940e8108050354000d1150000700c80340640c0104285a11200c188050203090701c40c205100100e59a40c00490300c13015611400303002b041c2901d00082183e0541d90f10201070125145810144161a00202c0198041c00000d2001080840c10b1388140301d8806003940c0c2802661402317041020300260011040c038013980c200f2741080b681380e400c1508035400501882d1015510f110802d1614400c00f030bd078000424601c3c0000a01070309011940260181c0c00085400406a9a0301c403001c02c050981440025000b850034800512146800740100d1a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84576125 1250 84574875 84574883
    0x1b0804180e01021204120203030103030c080a1112040906050901050604030f050a0803090a0c0b0307020615030f060f18060103051209010c050a05100c050405011b02030703020d030e090a020702130504 87
    0xda01d03011040c015099822240761402000e420104102c1408100d145e41a000d080c3d0780055031642d411610f004012102000300a004074500207403010070180300e280c00141042e40802518174074010031814958551141c4203a09105080010124139072501c5d14880d4121079000b802246040e19603541e0f8a00d811500e0419a4030380070702041e090200d86030100562080ca0b603480688044102e5181126500800d50003000b50342005100300140181c00145094000d20b004200d0656103c4010000b864002c200004c0c85860007074070148824403084020700c034001d805681c036400c135400c20000c0302070303464200b4440603105a02c040e80e400020544000103005145040c5820040d0100390303250f071894820300b002c044507107503c80524107441c840d0310310948440150798607180c0d18261801d000200702c04c080c0a040ea40900c08507005034115a0100005002150b001e48100c1c400c03034407410082c02400f44950b0f603901074000f800008010001c2d40c800c550700580c0c01400001d111041402c06001044004d208903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84577375 1250 84576125 84576131
    0xb0a0e04080714150a0c020607141c06050f04092004090c0b070209060901060f050c0717100606050a08012702180414060609060a1b0f02011b080418 65
    0x207804a00400c0c0110380ca855604003c0c8520380c0050078654000600078003c0f0a0305d031078140440601940403502c0d6400c41c40c0ea20340403088000a81c950b4445208030155904a16440401004040200c0d0402d2045440840d814841c542c0e050050200340d4002c000c006011540041c0800e591444140303c1c0f440015010b00300103401c591541c0d445480d1039164101d00850580400c0d01004c42c54100d080d00e50001041d5100001075140100240803021400c441c40c0034010040f4190710460002c00c1184001c3c1680340f141c1211460028a607900d901401d09039108031800d00304040303403081c010300c03c9034245e41c41641c5e0078980341c0ca80200304011844038006000000030120803111110700d075001811490103940c1c43d00c581c480b4880c0400c8100d420f0703104040901c840307100420049a80700002e0714050305040c1d40080d540d18a0400403901043e2001400c00585d406058450500079000e00544005100303032500090b03440c2c0d10550300984260b03c0340040221800308418041c50001414402c03698a07001741c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84578625 1250 84577375 84577387
    0x403051305060d1a12030a1b0b010303030b0108011e060c06140c0306190f05010e12060103050a0303111303061d0a060911011b0204090c0305060a06080f010b0a0e0408 73
    0x403540e9012540d5041e41c0754440203052284c126058a650103900111000e2410300c102000d1725849005042004081c000010b1102e1038261000c003004100315481070a100103581c42c1d10703000e80200201044580003810100000c42c50711142c0700000000c58503c40507042e441c0c136020b0100d8500e400c0640c11640c09840310343c07030140da4031410000c034002c3d444410356685a140003020f0006280b101101d2104040d0b083e4020881d41600e030928100742c850030f180c110014243c000200784004050440045c80d032044800010901001140300e218480c40390350240710b140044c0c2c1c2101040d005804c0b802071041c0f044c00003000090704036448400d2488158a80300c84080d408032540341030181041c01620704a4854400c030003000307110141c1e00800002402c10b00c0792000041c00d1100013102c1103100902560b03a40200c1c01c01e01c01d0040b440401941d2140441e0700c90b04e0030340c1c1064090032042c803500e1402c0c400d8100d2540c0942041c001c40651075800350900e0446850a0140c05130004040c1007914104c000f000a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84579875 1250 84578625 84578629
    0x19150503030a02011e0b01080c07030c0f030903030810140f03010e070f0915030305040b07080706060602011d1c03091110051c060e0a0c020f03131e05090403051305 72
    0x34068022454000180782c1032003182006003410040c82144401c1d06e080007070526681c00182103900100441581600d9001d6403070203450042d400c0102030302c000c00440043e410550b00620303450581c1d1199403405a15194003124096403c0a800394000007100c0b240b80456034104040c40c0302840e0710040000ca0f510103141451401d0403c540c000c02e002540a8100380104242d501600646121201c014400c83c0d1542d00c00902074025030081e49130300000064103505019174001592410390f00a607040103525503844001c6d00030708401c5071403854541da03a0300e0000c1e441d801190700c1c0104404506442030708455040304038010a05418203c50f440300c0000c3c1d006046e1503103e0441481803041d142c2c0c0c2c1c1e803440e06040031050284445503804001d41020402e005441c4214407043d00032a10000100b07604140c00001d81c100321640800b0f0324a4440443c0704a0686011000c2c00210740340011171080f1104a040041c115424600030190000090800700b000203221b80c0090211485a1441065241e11100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84581125 1250 84579875 84579877
    0x2d03030c032706080f0c030f04050106031b06110a0308060114120727060f05070201030902100504051e0315071e02010606080c070c2903010e0411091915050303 70
    0x840b400c00c01407034014021181c00c4800c01e81c00c420309402c030305602d00e000b902c46149440020051075601c401d07580442d042100c2500007a001e141d01980102c9503c2075408000ca03444200d1184030000707040310b24011041080070840707400c41501584d1b66101c9580d03071700054840c03294455001030340c86010081802941c0302440d0050040c500c5a48000410a01001444240d0102c1c0384400e1110082e500422543d038200341d403408103a0290420a4030b620480c00140e0042c000e82070007941012405410402d0540d12000500583e5000c8600d06c00c00481580559000904100801d8155122030a4001294021a807a551180b500e103400074411545c00c90024000e18100340a40c0583c1d1981c20034441d4580040d07140703600804105401e0300b40b000c40e45a1022a1001c2d218440810003100c003051000250040803905484648940c141d5030350f503d039920883e000048400f0340700003a0070780340c6050901d070082600e03000e0211810980161080004481c1c010400b140d0440d0158141010008032500d00740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84582375 1250 84581125 84581177
    0x2030609030a080708070801031e05060906040302100209010e150c12030907051e040911040c0c11030d080f060f0405090c010e0901051318050102070c2d03030c03 71
    0xc040c54032016406009407030795101820000c24411610308029449500c40b0340c041c116900b05480d500c11000464a2a00200d080c0703401a04a014030310400001c5680003a4290156100f070742200d102500842c05c0800300e00420119500255800d11102c0c0c480c0342030a5944039103441c42302d115103007004900c101882d0081c22440380740b1141022040110310103080c003204006290a440c0d010314041c5481514040c8800400900d104655071061b00b418001c1d03000c2c200024030340190080012904000016005c4d00141c0c01c00c03940307401d6440001c425804e000c286440b220301207444d1019aa00c41d0400483c503000d00074096034000648402100e0950740d24042c00b8000c403540c9001e8090f600c903400c001801d9000c0d6085040c0640c6c0d9500c0100714a03201d114686007403a407440c20014040c021351450400c1d460300c0e02d001900c507600100315035040c480e03144c102c1d000701c03080312030700300038001401e55200d89544991a0501c24414858001c0010034010300080000305e229180420480c218426000044c1c0700750 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84583625 1250 84582375 84582391
    0x70b1219090f0c0f050d15140c091203040501140c0307020307060e0301050f04170a020c1302040611010b0604090908070c08010c090e061e060c010c030b100302071a060d020306 77
    0xb5003140000d001c5050303034020140002e100d08800c840c0c00c0c00c005c5042400a42d100030b08500c2805c0740c0c072803982c80961204c0030421582d02645101e017814100c02c1d109400141005101d405a44140019907034000b0481c0c003240c0d41a11140c2e06ea440c03405030807010f900084071502c400c0c0000c1142000594042c40254090110341d00d41440c0d100c030502c00d240c01c540c0018800310062800e8801d10000c0740e10418420b0302c03000d00d0103182d680d5800c5108100d041c0b070000441c894200c002110540704400ca141c02034001d98805540e0901d0158120740c0ca0350980d810300c4035260300319004000030311290519400020382c40b030240c0e034481d1078845550348680121220783d0100d58665918140c03c000c4661080d4050b00400600310b400b521410300030f0000320210014060050388107490710780195280c541c08141c4502c0d5180000821082c592980003401601040d07812510070000c881e55180154024401c2d80c0046810410300001e080410354207007600703903010701a564421309001903c00180d40800c00c4511071864 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84584875 1250 84583625 84583643
    0x6030a080a120f05090a020f030a0c03122304030b0a110a0306030c092c070305030309011a10020a031116090207061a0310050a021603020d0f02070b121909 68
    0x4070340220b4115284450700840042c113007010b025101000043c9080d501d901121941c60301380103100007915250074107800504051880e1400402d2101301c41c014008000282c40340c22511019a9144103840d80080c90710402e11810300c41400031540442025030701011090000415501c140340014254008a030103a0019031107400c00e00402c0003880b10f0030010210034505100710080d100308298403403e00e4003030740d03a01036642c09080400e80d030411114008507006000d6035501d0801115050281c0030b1400c00315840309062448650034206040d00041e0501107901410401007903035022100020300c41032810b01841140181d45441c1d40190340f4400800041c2001070b41d0306010300e4000281c03299007154582031007504061044645000c51b0039101a204400b000405035507180c8910000d0040300603040d19680898201000c1540004030340485030328589030404078520111080385d41390850b0245600c5036100344550b00c500044100c880d03400c088640152001b251505503070700125442e1030425120001d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84586125 1250 84584875 84584897
    0x1903020702180a06062a02030a1e0b011505030c07021801080a150c020d05160b0114010219033504060507090f06090e0a1407050a12050f06010806030a080a 68
    0x100d4801d1350700400c4e850403c2014400c0410080a201c0f0300e54591419150400700420115502032082c203e0311030b417194400400c1c120030741d05400031080303034481110750104840011400c8110600060412201e50b41c0302891903481034a5900290048082280c002c66940e410400c2d0a9450a0352806070418030001c040341c4999051044030b02e0505401410660701c0c20080c02c0350181d0101d42c509201110f070400c140e035181480318807854251064400380600e012880003043d000c821402a40d19210243d00302c1e0b8001d284021420340c00860400b0050104081c60084420f004102520449080f40c5944010f0810811003a4494a0784203c80c2141c0c1c4503070756010014401d802107400806080380c00e001e03400c80e90a280014000ba0320758003c09181d01940000075003040c1c0103800910f00300c001d035011580c103400c1001000d0907940007030f450380011030000720100103503410a101c0c59100302c0c40d40b0802e00071030f00d07000c6c010355a042028100a405014403c22500492030001c014406048156500d9030034403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84587375 1250 84586125 84586141
    0x305061f0b040e07090801020429120a0f0603050102030a0c020708160b03100504140105040b040207210509060705070e060904050c010e010905030d080a110304020303190302070218 79
    0xc00080c00c0c85044001660301884080072040c01e40b030a41c0c91402c550040d54a442200303070b6000a060780840d00c0343d800050b0100b04050805500d402e905003000c800142c481203034226820900aa113000304260344038400040a151407600301251120895900042c2c16850ba250075003640d204440c5000740c99201c000000100350f0400c0031000400000c000f9040700520b4684034140015a8800c5141c14400480070580001c0ca4100c90303401483c008004000440c400040e4064108003440340b00d03c240d1a11078004400e0410f802200c01155000b05c03100918150300c0381926032241d26a00181c01c1050a01480e20240c5070a0f0041450a01030401402010f250240416200070000d1141e800b418805080c0300c001000003070340903901602424410b0304040c1460040b505c0000b0f40e885158180b14440180b24080d4204080310b00600b0011000d0110b14401c942c5c040103480180e03402501a44100a0030b1b6015041240001d1300381114074015103094a1500010300c1080d00c0c008100304180c070041840902 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84588625 1250 84587375 84587401
    0x103020a08280303060506070317180d050c0a0606031a06040207031205130c0b0c1b030d080a0e0115060f0305090606010f090806070c1704030b180115030506 69
    0x8051420080000c150300c101d4408010b80040400304550141c00b000c0000c15000c1c1e000320021702005070402e0340b90089410001d040016001c012031940c2d0440000c2801c500700e0350004806906547c00415840d00b900c102104e5950160300404070a0051081ca040000e0190052000460140c2c510070f42000904210301d0304030030003070182d5104a01c100490000603400401811405031180e000141c17598518070a440d10309a030010003410540000d6002c10b6245495003d8007908801e2000c694030002aa0a003800c803e034121080c1e0b6142c1e210046900740c00303200e03006c3c15078004202d4001140d101d09200415080d01c2844100d5080e00b00e08002c184080c0354401d0a01124040c145814403550400420150705c460001e000f40341008526400d05007098007d8400d0310082c03013200c0481d01103286c1240700400199865100300c802c03500120510060034400802c3d10b065a40140240d8455110803012480407804a1044102c0c6d54940706100190000081d1a40c021030140c000380c01c00c4d181c244151038013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84589875 1250 84588625 84588629
    0x20a05060a0203040b01092f130608011a030c0c0a03020705040b090f010e060d080301141212041206060308070605010509090f0c090a0204150e0103060608010821090d08030103020a 79
    0x16591040c8100070100b030071801780b541101c00d802400100145ca1125080301c076020180382905240046403401080c201e81d10040c040c1038140014850300540724078049507440c00a100d645030080c0c0116950003043c031000000c6411a14100c91103180046d00c0d895642440c01030401600035801c1180300700120709080c005d880c01080704840b07081e014a03040c407089050300018001d1090001c070541c002905c540340c1903000110680c002d020103407a980d640d0740306800c1404a803a494025004824410034508002501000c800d00c42c165040c10700c0c0c14020081c120005840007038078120f0310740c00000007280d200070082c101e46003c0c035404599581003400380110300d440903196045644c041c0350f40c621100004510040101d004036000040c0fa2a00103214001c0c0c01503070050000f020342c070302810841c5900108005086842a2020b1050a17038502c8184e40365a424414040c0540220425180c100c2d070040d29580008205500e0070300b00344941c0d010501364001031804a8040c0400001031042d85040300d44400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84591125 1250 84589875 84589891
    0xd08010f0608070c06090204020f071b0e04030801140a0b0301060f0206010f12020d0206040b03010e24090c0706110c0a0303060803091809070306050a090b130302030f0703020c0a06020a0506 83
    0x820b41c1403842004058404d05507000e8051541c070003202046586a030110b4075030000d407032501c64465425080000138030187d0008069111704031800090006080000f2030700c19501611200c100740e01e011001d4049009079000355502507903040d004035010398810051406000c00b81c1e1400794880030f0041c041e2810780b061b00311126060080100308082080200900e01c000d905851b030b4110001c080c400b15019014542115003010408000407030312000c80075186114404417034420059074000d4000030380d060303030780450690403000c08400500c2c646180741c0100b14051080b100001c0d010016917443c070050700942950b054070380003501c246040c15458000c485c0a42451005146040c00080000b0508180034100d581c084030301e240041c1c424101800603100030b5070012800e001b80c1c50444200c40c020421a02c08460b1311302000042600e81d041040b07000e4036154507400442c90700e024206481c45542201d078080381140300b200741420941e03d99915442c01040c82e5002040c51161520f0b01e02d00308500209904 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84592375 1250 84591125 84591137
    0x506030613020a06120b061803060f0f0a050622060812030f01060309080c01050405030a030f0513080c011d0a060522170c150910060b1b0106080d08010f06 68
    0x2809650b40129a03012138000e401c045800324145055507000d045c480b22144c0d401440030603012085610200e80110140c01141a5410740da17454420f0400c01174140d4221100c0002e143c002101031219601c810f80000004210310748104000700310410740031800340340207111a1250400c10900700e0801200354041903840030a811031030a0b20800c211100c0500c05c0345d00b0952a50a0081400b6000c400c5410710b90000000740014a000d0400c01e60365030007010490700013450440304060a107241e104150103101c0d0031010210b0f040c03098641441c103030403c0d2020f1009550307560100c503c65104c2072070750601c12268400382c1160300107401d010b4115000123140320121005030455404900c4203500060304241d1007030b0316100300b50142d404281b860140e1801c5d442c3c9441860850241146552012407145000780200d4442e04c00b051302d04015141035120750005000b003800b0585030b480c0c0400000305000400c2e000019016640c0703000ca45001d10281c40c1e03402040600c001031000509081400c405070005080c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84593625 1250 84592375 84592411
    0x20114040918021e010522051201020a1206030302061b0c01021218060f010312090e0114031b100503040215030123041103040308040501060f06050405011101060f0b0304030306080a0605060306 84
    0x1c0d00500c00c24105080300c1041d104942c0f02201181f41041c064030000e407081010803540c0040358002d61000e0a0840861908400000341c00d460b4000c00040d41d0707059020302141d4944202080d41d400807400d080c0380c498014407010701501d0091010b0111030202c240d003800e0508201d1001001810103000c0f000c1d954010508001200c548012820b044903840b030104240c0c015090022a03010850341c10009404038040c3c00000d030a00b01c104420304100c001c5098810711100e5019500c0788400150070b10b6040310450032a00c10b078600807009190301030300242078040540001a080301550307009800c0100100c002d44880c00030302000c00c110400c0c2120a440410000c58522183c6840b800000d00040c00c000310030f800901002802e410010081040000c4d602c20700d501ea0002030300360740003270044174001102250600c40c1036405004034001c03180d100303030b00101450800c0c807499280c0d070000304142e09054441a0020340d48108002c1024068040e100018450502c0010141000c50180c280038840c02002d9035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84594875 1250 84593625 84593627
    0x30e1c090504050f07050f0f0d060e060d03020d03020906120901060608010b0c06220f05030a030f150b0f0c0a0f0204110c0c040f06080609030a020606100507020114040918021e01 78
    0x441c41d017103035031818a20f807030f0580180700340700c5c6124880c1224081d96010507680305030803464000d04140c44070f054001419a403414144182029a4400900141d008410b42504140603038018030b00d542c0040e02d1103141c11603180c4808d441003415601c092242e99509000c00c0b09550041d02103014200080b100d0b480c2a10450545594400c0500b202a45001d0043d1090704002601e016411b0b15502015800500ca0141860342c0c49400410924010034100b050f41811148940310754100041d0304c00060091600f04a90440141c110441c03100c0d801104102c800c00912040007290800c038411a83d0100216083c4180000c2d92056081800c10744420f2004100108002c5280007128009883c0054190300e00c00e18480076088541c40840306004040c103000c0c0c0c060012000381409402c903021981c5035204d48040c0b03ea400c082103541030020342c3c140000e4005602c0340741c40c6010322420802c041d05141d1540d2940003182c0c1c00803086040c07104c01800b00b50460400805040c05107458015039509a642440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84596125 1250 84594875 84594901
    0x1510051c0203070e03150a0e0a02030a1106070c09061406090f040906110c0a0506061002060406091a1509070f0909020c01060323070f030c0303050307030e1c09050405 73
    0x940254001c4002100c941c03040c080242d132400020116420b902c1c058015003030000086c0e1703443ca0100d05007210f00502d00000501021040e0f07000e4000d0040c45400d071a0326101c454030000c0c466001c4010803005000c13511103448400034260400b00002c0742442c0405049400700c40700da91034040c1009100340c1225a449150880041505580c0131500004514140c4010904400d08882e0f800d0045042052070b540000e02444c01449201164842d0b2201c100f0480914030f06d5034600c0040e80a1000a40060b5154211003d42440703014000481c80c2302e0340300b0320401c05003202e262254040c0143d84d06900d10300019059003100c0c907410044852290820001d0407490b03640541d400103500029804c051300400d5100302c0c01907030015400b5007100300c42d030006c003d000c41d07540f60702815104081d07000c0f540111022403401102e9010003451000b600d1a0b074240d41e580c100030711807814141e4401842c400040300388090074403800f0707c0a000d00c14224815025005411f0703500018003542c070781010001c003914281 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84597375 1250 84596125 84596167
    0x206090109080a0c0303090203030f040e0a02090603070c03031b0507200f10120510080d1403070804022e0201110408030a05030c070c030b160c02030d0e0a0905151005 73
    0x45420740310f501907400d0546c00b43c06c01080c0250184400600301c040c4280040191060b582007200070041d47e2594115841a805a6101d1542c000c1d0f0800c0868180c6000f04003c030300c0d13507200b410f010070180c4800ba040c10079030302240d0485010400000b180001c0040303124030503c04a0101000041d0890400003203809481340400c2540929400b80f07400e0001c2d4020000034035880e40030803050059150800c6141828801480307641002d106800500170351500039807103120320f100c0d000301103030856450b803004898100c03001d441070760002e12500100d88929071030fa2501d40407603010781d07007505c2442132040001c0c01c440070041c400542003420300080c40341030008400c0305e00000c807a00c0c09603225224241000700501c03440c0700041085542e0680081000401c24a0603c64081c09910b1004d00c03424500544800425490080d41500f04071035804159000e240b05a54000340544406a211f8460a40700708440741910340b00903520700d1106504152500101001c0b0000440c0b8003036050140e40441521090b40b10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84598625 1250 84597375 84597377
    0x30405010e040c091401170a06050307080a0807030c0c080109030206060a15050708031b04170d050403320109050c0a06090b03010308030c070f0f0c0e090c090c070501050907060206090109080a 84
    0x4800425844e885090035402604d1f41584d0707a020350501071400d00c0100a5489030034001e024101000940e441c0110314480c1c1190044425480c00c495070340c0854034030714030000441d11200f1500010900d03c0c805d01c1500c15051194004100600f48402045507803d85640300b82c1d6081303d00032109031010303409001d882e030666001841640700d4803181e2000e000d036130102c0b545a2075440c0200303001a042e40041c52404401e1029029550850b0000380c00f11541d20890001800001d8800c0c03400710b9002500303801c052842c20746001d1001b580605600300d800c7d80d0744070f00d003901ca50b03008120044461070030140f0030300106003a04107034825900c1d024081c466800140700243c6030320f00100014144560310030407180c4596200318075840000b0b07107142c01088014210300927100180c0c840c1000c52440035580001d0b00a903030840c000e044c54030344d480401c5804040200080001c203000c0c030100700051000d024040c050042000078212441c00c2c604000e282c80b0700200030300303010303070424140c2c0010030345040c100c8007a1221 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84599875 1250 84598625 84598649
    0xa090303050f0405031603120e01050906070c0503011d010501050904050631031d04060317090105072001020d030c0e0f030f060a050613060503070b090a1502030405010e040c09 77
    0x10301c161056a802a13500180d05030282142e180c1c4180c03c10148001524414000500302c031403065070440c0c4140312481c1031408140108086959403800b1005400182d00ca007240755001ca0f26240031034250349085100c1c4d08010041c000340c980b040e40a0250a01400080d18605964035007911150f598074400340c030803a540421003160035842e01814403100b440004060304141c00021f1460010000201c0d010f0900c0c100c4c081c40390081c400d1070b0a010303090031a50850802c8201d6071072034621b030140d43c3c00714001320305001081011031f00288081041c41100c518a46945003014601c0001a00306490780000c40c04141c03910018811035500245140041802900c0c14046043c4071400709241c4000060050483d02c24402044142c40c507541010b0b12030759080d41c940b108519142c403020242c1d131244c0a4180c2c103800c03044041c0510f409a1018120300c0100030114030f08242e807500110341c1c4c0c0b07410007880c0c001608009024045035810081d10035140b40151350801151a29600040520165020708401d05039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84601125 1250 84599875 84599887
    0x504050304080d0c03120504230c030609010c180b190c1b0303020708030a02070314011d030301050405060901031505060f04020a0215060910090504030903080c01090b010b0a09030305 80
    0x44100260340181020342c085a5440540081c0a03124a4040300e0460001c0c0702e02e070310304038281200c0c05003a024643c0b0006055030801a4030601c0042c601c0d400c0000060311a03034032510016a402c000d218000c0f8000c80c000154850003034001422204000440c2015010805040010046403802c66800c5000a0740c00c0c2c005400540b0100c48051540070013402814648100c80b011040113541c800c2100d20035001c54211950701d43d90705482e80620011a800342e0001c6000b007010500d07040804104403011000000d420b1000041480072000e40e40080e02e03554400700040c012030406206aa4201c0002ca0b52065103624503031780c56554000da007542010151b151700101d180c42d260790b00410a146030081007552244210100250b1b51804028403101c03036003808000c42d109043c0039031028010195001c030089801c1c1000300c82d201400d0068011010409980c8000002c91112405030074002101c01c008902c40003a402c001c0045001a000b401031100100f100700704160f00414030000b00c9a25041a40c2c80b90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84602375 1250 84601125 84601133
    0x80402040e01022d040504050117010501090606020d030203060a03050a0803040b070e0a050103090c0e1e0604090803040f1a0406020301080f0c0102060112110603040302010207120203160f0f0c0b03010609050111060a0504 96
    0x201407641b16641082c00d08001190480142428005c1742e03a54070000c0000b40e07aa03010560a8440030310801e80503800012000d011984250011a8030080182248080d1b0396241c2c0e031580b0340101c8010940342e024021060000300f003102034030382c1d40140340c2d0301d0006290381500d000075110030820311a080c140f43d40c400c6160b0400c40c00d03100802c010400a08100140d14104011030f10f11101c40c1d001002d1054680005191460948255420960000c450506545c0d071955110412445000b080e103800307001006407069006050406032082d40b00300c801684952500046c20f20700f003080720319403086401000c1101e43d60390b40040d440381103801a4044002040d03640c10403a01761805840c032590091000400c21040c550150001e014842c404d00d80c030254038034000308c12616400b44422050700f400e0720020440210b81805150001e4a01580e04075103007007903e50340c1d4905809aa808040c5882020004020250f003015030400201800e007131070310424044c1c41710769490702d600800c003800a564660120b420301c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84603625 1250 84602375 84602377
    0xb030618070e22141e100216060908040308071203050606090d06050c0d020705060601090f150302070204021207030501050a09200a050403021c020406120b04060903020f010c080402040e01022d 84
    0x1000048085d184241500001d4015207824150b0350751131441090030741a00800d41d0710031203005207401000c034a00c00c0e100395110fa0207030440e80000c0e03030040000e22011000c01d14035001015094441c101400b01c064405002405581d00108010710400040c41408015102c458074031102c3ca6000c01e0008031565155410b84484c00f0f40001e0850242c400300300384040160015030b543c0100c8098a9a03144150340720480d0a0700101402140700d0b00350b003400004407050003500070b012858801840582172140244600c40c12950450340342000984801c0100054202114000c0280c241e207a002c0c400b00d600d4400c140b0700e2215801405051850000f41c0e2100c00740301e14144c4015580c0200102051202c098206800c4100608141e2180e80381c4003000030182044449512513540c8103603840b00664a50300c44e00b000b070030009015400e50003030041948100a00384111200b030a0300341c40d025800e00f014011700040302c0c2044941201d588c0704102415415086000c0055458084120200b150841304440d01e05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84604875 1250 84603625 84603653
    0x326040b07051506030c130608190c08070501020d0804030306170307021f02030a0c08070b0408041a0a0c020618040c091a0a0801051002030f030a060303020c15040603020c010b030618070e22 83
    0x30314041ca114ad034483c080d451002a0b00769000e19600e43e041d94a940c4280e4841c03003e07104d03450151b44410b409151890003941c800b9805802800c0024141d9620101c9a01e80c1c03480c1c00001c0c1c415000000c2c03d004610700208014a110342e0081a1a011400e025002c0d540384120b44a03370003400368030200c070010000d040d000c075030400360f00c08171004031400c00c2e14101d0b20b550014010350866400b4103041c0da0440708135006540a0707a5030b59460206c2800f03140c003840310076840b00d282c0f00c030000b0007407103014004d4845004000b5500707015600c00418902d030940180500d602100741c110552400c010b0101c20651010885055842c12074440040c0c2020b00c034203a256101e45504401c03401030100c00c20101c1c403d15404403045034025025100e0203482401000030066505080d01c01070a403d00080c440d152003a400741101240c00c100001d18803442e03500007850300c14225100040250580f44070707100c02078103012580c014000c420305101141000601c00340c810000141c441000c5e58001c032800c080c016201c087e018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84606125 1250 84604875 84604889
    0x51b030a020c0c0d061d460b061903080a03020a020a05100603111f14070503040f030c051c02010f05121005010f05040608010326040b07051506030c1306 67
    0x350010b401d00e01745c4003174101d000d5580440c283c86015504000408149200e003008070f20000901481040880d462201d80501640c41d910009001c2c0d80142c10301e2000903081a0141000005525240341003000ea40000d02031055850300d962070800004804000751292141035060141c0c4a03041d040c030880c0307444601c1c3d00c06800c52240601f41c20380300d9074581c455000c0d03d015180d0710f25046856418411000711030380d51042d00303c1e10441c0c9080100c0c49543c0540342d2004c0d440c1b005161080c41d403202480c5da00190410000d6000e02c140c1001005800302403030000b0201a59415513481c100d22458111215030580a0306000c200c1c01540f0289105104443c50b90303d03681c15200c0300b1700b0540c0b1080342c12130fa10f000740c5020030604100c6105050042c9d0a40d01124070725038034203009a0070b596460000400c2c20902c0c2040c207002124801201d890301002d8000380c2051801e25896003581d0a00a142c80038810b010101c000e0030b68180005904c0104070b42d51a00802c1d110f20940203200e030561001094950b000c18 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84607375 1250 84606125 84606139
    0x30708070c06020c0450010f14030d0806040b04060905040201140c1b06040e01080f12031521030307020307060608161818080702010201051b030a020c0c 67
    0x80100441150080c0039120b482e822915150650000d100440301d50b05489500c0865400c0c1002025030307105608404442c01881039510680e4500b441a184130405650640815005005010469072420100e0050401d01c190407125189000440c3c0c41f140001c601c0001c02020200050140d02e1700d03000628503400283c410040c0703e82d11028800240802e641c200c0c00200c0b00e00c99810b9084204050380c054a13080000b805884030240301000100011024143e0040f0080c000007076104000d6040710700900c0194003802d154417207261042d042c0301d01c000200000003424818040c021811b058070456008082d2000f40400c1096956003062000e82a0310151b14440081040200d40c0e02001074211688252024001680c0300d0140e191505c40744101c850f01c3c24549002044258800b0480803d84404ac501c0010322590900c0408046100c80c03d05554039640020b01600b1540e09104e07031035000f03060100b445001698810149110310001e40426402a00401e07102c0000406006034030690070014105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84608625 1250 84607375 84607387
    0xa0605100305060907090b03010b090d020301020a110712241410090b06040509040605062806081e0412050d061e0b0a02150403030905030307020615010e03070b03040203030708 77
    0x1d000c0c0c401243d001e8019046a0040b80d92240519520303416503c10083c540e0450b800e080b940c80440e003211003140d5120444042c00000b50318207200800c840c00450f65009488110300310503d10303281d400d5000e17024483c2e0700700307d12003c1260641812a01c0086241c0c8030400300c19090700f04081c26034111420503070070b50201030082c415581c5460b2421030b03c2050060080076110f0b0304124407402248203680c3c00c1507101d40000d0001e10544d001ca94001001000c100700561848425603d48801d00d202c11a000c220300d030140030043c6c222110941c03114040068030100a00804d904030302440c0648014000d8804000a2030100e000c2d60035034070748594a480420005995400c080c01c0d1860254180000b4440700c800480d0f0a11120111506100b1a0b00104500800011148100603000700241e007010b90707c1e03010b075000400900042d406031406500410305400c00c215100c83c03c80c2c2684030035041c0503d0340191400c544021640400302c41003044910f4580c2d5031400802d04502c0b0b500c00007000b1200c0041c2e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84609875 1250 84608625 84608627
    0x6210606010e0a0e010509060111070306020901080c030601211e0f0e0111031803070b0f04150b01020703022704050a06061202060708070c0e09010b01031515080a060510 74
    0x4203032055000340d07030320140c000c0c030b00c0e0900403100002c0c01001c07220213000c0018015410314036103040e0032880c10301d8030807400040300050504040c2e4980080b05c2c915000103143d040b9607800000c080c2c01141d0680c010349142040300010b4800c0d002941029102c203900c80d0098504142d650100380c480e01d00c0c1041c0e880b924002c4d8030400c010034a4101a02031075240c20b1841c0000b0034144100c01040030207105a61070360b180c680c0102c03825410380c82180810300c030070072100380001d003110700242c003e040042c950030361402c282c6001d80d4a0405040714020079850001c5803011b5a0780000c0c4102182d4065880c00c0c8140290805240faa03014104401c8140302c005c0300380410060f00007420041a0f000300000c0060a899080c0c0c17001c180140003000c1d500003001d201b410301103809a002001118072520400e0082d0742d48201b00e0004000449600105940d1010210141d507003500034a56045031000c450014981069180110f840050340040100803810000940030b080d568094400f80200400300302c1114a0458 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84611125 1250 84609875 84609883
    0x20c03010c09180608061f08010c09090506090c160c0e01030308010e0906060109060e060909100f05010507050a0308041407080102030a0c0203160303020f1303060207021c03050901080621 82
    0x300300c0020802011030307001c019480344201811750b0002c0340a4041d64071036000510000c041c1908501c1c00000c12403001030380080901c16010026001d44a8150551401d00d005007100c0009101c0780c000c03240e9104201c41d85030102c046404110001801000135000e41c01c14600a006039009805002201300003c0285504151440d049520341ca10842440d6101c0c65800e0b150201900d40602040c10f511007400200d010f08d035200c900e94802b600960422044c400000d2101c8000e032035405050040c1e0906119a507940502d503000b030070085c24080e242041c030366561750343c03902d02d450080d080082400c0480d04008816220b00c80e000800000c68085079140e0f00a507000354420340d48140e139189404424089240044141c1c2d4085242c1e01602c041d04c2401c2d00e051700030b9442400f6144103a5030400c031080800ea1348001000145004200040e2540290310602060122590920400c00b4100c0d014400003540700c1e00300c4400c5d02c030078605142c2036216000450101c040c44102c180c0719480341450000b030400c0010b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84612375 1250 84611125 84611129
    0x60f07140f011b0c0201050307261b0408150a060509010306050723030609071b050304080d05030124031e0c09051023040801020c0a0512090d020907020c03010c09 71
    0x4020016050450843c40c1011440c580b02030200340118030b100055809a030156a0080c0d09007400340407840501410042c20441800e00100c02110006200418560305802003c410010f031055203050f0600c0860f41e580d91400900d0340717014103160300051100c900c50b00b112004040241c13007085e0b40d503113030b00e4400041d107011502c00f400191400c80211b00b80d2002c00444682c0d01104070303a18690b03200e00040c8190607000409003800d12010f4440c0f00c68401141502c40a51743c0242e02641c0c540d4104000f060401d0950142501044010310060003120100103d0382d000714901040d00c41b210781145815006440703021300c1500c2e02c0a103111000c44510240d0480c034400303d403641d1010301032615072003000800504142a0000500501c00700001d041d200440d8081e009040c1d02a2410b09558607a840d00703a074807141e8805025040141d0840810100704000d1003c000c492540c00d0400a551020480e10401204060b11559854000c904014000d00c81d000f651080500280f200300c022140141074044a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84613625 1250 84612375 84612403
    0x60905070b1210051005070c08120703110f0330010303080402090603060108031c060b030106180f03170f1b030a02101109040c090b03010e060a050d03080402060f0714 73
    0x400103180f68050f4403606094443c024181c0c040f02c15150000c5400d03400c110002c4665065508000c5007a420410907803000040600b8204e507189100c1c60003c010350302e8204640c40c83d078000240c07003030082404819903205c514900401149020f012010105030f00d151241100155803000000c01031643c011071940c800c600a44060109441d40c50506a890200348104020340d001405080e05400c00c80510590380700300010082441070f02d82000d003640764001e074080c602140f00f4000300c01c00b0031502441403009000c10721043e0303071203461915440c8000754026180c4406507000250a40e4808400041d0b40c05611410880d100360803180c00e034183d490707214408140261241480d0080c51090b41d02424110004c5945414201004002803201a0003040c800c0f1080c411940790100350100c0300c90103176008007400b00010025040c400305011081400d070300041d001d20803004030100420380042c44203402c00c2c0e06903405a07603010310101d4103006006e4a8401050120f10440d40311041a000076114014810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84614875 1250 84613625 84613657
    0x6020f13081f0e07030501020c0309120609250b0a0e041b090e040309080a0c030605130305181302070b0f0105010306180b01120501121b140409060905070b 68
    0x12484859601d0909980d00300e07440a150394410002105a0031050701d181d605400c407003c06861b961a1070a80e04241e40c2c070641e42c0d00c0403031000702a1070100880040700c3c010101816890800242141e16400744440b00d0101d0314100c102141d4203015084128000e1a00443c074580791401044001c020b186251001446103050540b4034841c4080e048985c0c1a4003a942c580942282c0fa00100e81e0004000404c2a0140036040f00300103403c3e0020301074682e007103219080c0141c056096141140403190050901ca0220012031043c03800079400c401101d1003072041c0f000341035400d0f00c04800500c000340c04a01c000c04d007500100d0407408001803610106e014a51504800c1c0441e03803140c004404440c0c052241c101cac0780c042c40c180d50313100280c25401004002010f15010b039040c00b00380c00400540c1d000f81c0c400e2140c40d903024401c03400d120000d1900d01701010750606409a141c50905044200c0c00e400280c00c1c41942d41c1e000040400000364451195140d008040e9010140e8802e0081c005411a1000b0005524 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84616125 1250 84614875 84614879
    0x1e0b18060c1602010c02030c0406031412030105061c0603120c061103090718140c04090f09120f0c0501050709060207090b0d08070201180f14040209030706050901090306020f13 77
    0x8018000d0b9407220441c8503a150310182d203034004490075002210280d8160003514044102d60b2142d003e040003440c05007090340740780f06440030014948540e0310021415141e051005008179543d6404403644030421030340b0031380c1e00d54040b003007a00100201d900c02880301d07280d000002d42840d00300c16040318542c000d40c401c011000560503900c906100464001a15070841d54050054040914107a44210301d0408001000302ca030280010b0008001c1d140520f0a44001c94100074403c0c01e8055980d0000c80c644051001031100c1e0340c0c0d0500072020178981014030080520117030415105401003801c0f160444000d00c41c0b414614005000e030f158900078080140204000403800308030740e0040b00000c03800a4031142c488010303500c40c0d80b29504140000c0741005920b803003082c0141071000911014203001c6406907205890100c0d40802200b030240000d0040c5e0040c010b030031027640e003c21400101c070310b03509190381d41d0140400125901c03641a00024915840482d0002c01010400b000d0428a48441d003600406a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84617375 1250 84616125 84616141
    0x903100501092712140f03040305040f0b16060c02010e100903081806010902090d050f070509100e0a110f04060207031506030803060f1201060e1504090309031e0b1806 73
    0x2400d41c1011300210391021008004601c44d00002c0108480028564113195031500401a5584151400e0f40064404074080c03003400c0c04000d410f4000e00164034050b04d070a11070140d540c8400b440c05070240a591307964041d138070058001c1d046a016039410388180c40c035805c042181c40d401000d00000590001c2c22100010741010352101c0404442c034000710050466030f1810084402035403041528903042047c0c00d00c41d20016404100f0030b05207618101c041d10401e8100414440c4031711000342501051069038400304142c1c5440f001968104100c8803010800140c0c84501140621a11004e40340036100010000b503803682c00700341e0350b05403841403006001081888080c1d405446042c04007078120401007010892510700340149100340c801c00b0b003000800c41c9810140030f00b10786c815448080128140401c103c2c40c640000807105080fa007c440810201e10742d61401000150705000051006012408d01d89003148803030088002558488031011240c503084444007200448111072a01921600c80800d0501e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84618625 1250 84617375 84617441
    0xb04061103070819140c0a02150c041e03020d0c0f090b0a0905190213050901090c08071202040806070f030e0105070e0d08120a020918010609050105090310050109 71
    0x261129a19442181c60713650031107805101606062039210341c2c03403007140030300d046280c40380740700b403600c10f00d815250f892118000c0d081c1581802d00e0b841d4000c4036801c21007100400000d8409440d42505a0034041440c41e000507070400154001039440400300b4400300410a03a01004c0083d1440b0b02500c0c0c198540d144190010381d80782a20b4244d101c03c04807410b000c985155171145511540c10680841e141444081c3c001c00c0741e20088914110400402041c031890620342c803594010103451204000100c64400001d000c818040d02c04010414552460640c014440c2c0680b0301401c0d000c0141e1703070701c1d00380144094203c445000e85c010104e03040c240619080c0c601031041511405450312650103007e01ca208002e031001c05180100c03044207040c40004444070342c0d0f044080c0314030305426006a440c060308c1e04101e5010014030010629510b070b10300512107241c1c0008407004690003800e1050b203c2c00c021000904060a010303044080c20318010000030071140c5908440c24030407900d891402c0c1c7c1900c2454440b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84619875 1250 84618625 84618631
    0x2208010615090b190509040504060f0c2606010c0510060509071106071209321b0d080904020a09060306120b010e130203060f0403170601081b13030b04061103 69
    0x400f80d0a0065000d640e5034200300c888140001d1500502d8040c8140004003121303010782d41590150340c0d803503501d410444984154032100c0b800b41000300c4064031050651140850407100b0b0442c000b00000402c115900483e01800c2181d48003041d6140e800600e010b0000808442c418148074443d00c00116801a002c1c019212002c0e2440010301400d65481c481030303507290b0b4040169000701d1b40c0c911111010441090524034110082040b0b803584400d040f52070419001e1603d00000c807600800516a0541c04040e8071400001d0265a1140a8662070400302c0490140b8020140c0050002420b00d031410760000103001902e0aa4a0400240b40c80c2c46075030100c803909040080c00410104c006102a0001e00700e0300c0e601101d01000955484055130201c0e0410f60180c441e17a1007100d0070001e00003050b4100d8404500100901c40d00d121a15142000030281140600060461034590f0781a4500d001c0ca441121228082c2103003020030750390b903483c3c1440d0000007100c0039100540340200c1c1c403110450207011a40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84621125 1250 84619875 84619889
    0x109020405060a18120f060e16030308090c0a08010c021b010c0602030402061e030a0c1706010f0903120525050312150904030e1e090c220801061509 65
    0x10410300c180d24203403000705000604c060400d02c8071000103180f40c6070002c0d188801d8403c0081091802181c5402c0081c2d60800b40341c0101900859125401188410410411030b501032602c40820385803039524a0034122142da6054110680c0c00c0049410b45054102c5203461030390b98211460814044c10080821034031000040c00144505000d40108a098003e5034201d4001041c440c034100040030742e6045004803001545252101104004449150b1300c0390000c50120380c10035030030746102d009140104080c004c1250f8140041c01c00c2d01e220381131151005001555012080b0784103420060340c0030345103402000c004104100300d0404820301c030305901c030643c401ea40d004004508015881004e100d040600030201f211041d01d503410b0110540d19010510b0059020352140f018119001007880300e400c0f580c4e1140c0100c203da14105c5e0041e070f1034601240b41e000040c2c91131740d900c0703180d010080359440c41c150302c0c0d60750849030b0114041001003040d400501244e032941c6944d00d1200d5117007819a950815446100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84622375 1250 84621125 84621127
    0x20d0e030615011b06090c0902130512030702091014031203010e061f030506040605030109020d06020a0203041205031b0718090602070b0703150503010902031e150f0a05010902040506 80
    0xe400c840400c0d8800044601410120705104d0a804245060010002c050300c02d59241c0440100340308562040c0740241c18529415460200420414203200100348034440c0904c0c4250709074451000e05100341e4070196402050300c611420400c0c000103400362540903000001a006401200924000440c841240349490035581543e1a1032a9182a48001000150050f02d1602402e829802c601e803898807132516600c0000e19410a9411701c0200d60054001c94007030303850705e8801c10250340c50401124107245d0000001d44d03207030700e034105c02c90440c0520340c40a007a1802c0000603404101c404000741102c05c4283c0c1d150465480174400d000c0d6122010700c50300c04c0c035202c090352605c40c800094014020b56809031001524165080e600c03a15510030450b50340c0c001965402441d846850341040440060100320000c0c0114446900001c2e22040d03118400c54450225040d88a10700c00c1c144030244110400c0406140f4910b01566a008109422903000c0d4544e031402e03002040d4818180b090300c0a4a501901d030f6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84623625 1250 84622375 84622381
    0x6090228030b060102070314070f2111120f030c1002031311010915020c041406030706120b0406150206070906050d0903090801020301090207060f050121150507080106020d0e0306 78
    0xc080c15140501014110b000300040800819210a2107003c4400c44000a001c1c0900e80103420642d040144c109a050307a06030f9244c142c007444a40d00340c501282e00242c50581d0302034cd860000341c0190106140241c64002c0303d52480c40c115001c405420401d402c0015110b0880f21a02400c0892104032012599801500b42600105d20350510703421802c03006040190640e5100ca010202300b95000c02080c00582c4014803681003814640103002c00d07082c501a0400341070601000103521212940100000c106007004882c2210416410a1407040c0300170304100011600ca0606a98034608803107040090320070380002c41e84940c400c444480884e54240d89642c10603d40140620241500c00015801c00540340008500e80d0021f01c01140280400c0320010b9841c0002d19002003070b40d03083c1290444036450b240040200e12240c95806860449855031140340203a2440c10b118200351400065004601d0081080f81882c1c01c881c155040c0c4415400b1901982a000e0b403c5440303520301104a90190849408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84624875 1250 84623625 84623633
    0xb0309030a1202071a070f09060e010507020f0402040806010e100609050d030203090910170102090f12070801141b03160815030604050703260403030c0204060b070609022803 76
    0x126180d00c00b0380350094a000d000da150151014407406254034410008030074000d6040c1c00c40c1c0c40c05807810950600c074420300d10700302001c0c083c1da1001110b24103100f00010b40344210342d81e001c40450411340080c01151a280c80d040f0540d07481009000303da20710074807200801da15408408a180495566a4a00703192904040601c004101858022400d502c001c1c0a645160390b2807000c5a4410713508007074001181c03032800c0440b1000842d401110240359204010b891601d488070300340803840d41c0c0306480c0c0002a6200861302032901d08142c0c0144031075442c1004c5074281034840410300f401031490005600303428002c0c0405401c00d200586e42c01c01094884043c91119600401c020790340b0924007110300c2524284d41001c641045002c03201100c054011480034020451040422802c0d070f1810b1070601795400c030142c050302c2c4502c01d07800090140460480340004540d26900300d540034042e50a6001c2d166032241c0750800140c2012074089105002201c03200c845e01c1054442d001c1a00340210000714407900d5912 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84626125 1250 84624875 84624887
    0x1409060a03060b1603020c010e0102060f270c01031512020d0203030d0606050c0f010e190602090d050c04060806060d060506030c0301020c0a03030c05030610030e070f08010903090b0309030a 83
    0x1411001c1c55140c4000044000452000e02916410b0074051040c404103850024105403600390414140200142500c1c0785036400a2410b40c00601c41c810b003189030711410304c010000003802444c0b00758a21203415003000014042168500c80100f0788082c0b01080b10798022010102560082d00502e00c10881076a0146c5070130300940880500280580385029810606003055038441d0700118041040000c000e840044200640500344003000700804c01040e40342020b9441d1030252004002802400c0700c42700500035540d045440705080140303a484000c0c15454078546400d82e0030700c41c1344a00e14004000450f2440440d04130320980005250f403800e030101d55142c000812015101c0b641510522002580c2a1024401000810401c41c010480000c0e81e180040c05d403100301c43c070807003000030600520081c0c3d01c90a00e1000302076000d05004c80e00c0011007200078600442640310990303505200c500080c0b015411b501100c45c20340669034441c0c2481d00d83c4440c20342d510050b942c040032170f4030410944074040c2c8035003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84627375 1250 84626125 84626137
    0xc1504050f0c18131a01060c260301050613120309080f01140a0f0e0a060204030b1308030c070f0b040b0901180c030206071e0809040507020d080a0b0105040306021810140906 76
    0x114200c0c0b0481700510000c80e41000903040034002c1179200c0aa4400d00001000c00007519400381441002640c1c1805070000c6408107109090003100040b9015007680c12000001010344000b12030700c0c4125507541030080900000b03124900d2a801105102940d0120600500034400f1000a80104544424044000526908a83c059003d503207140442040070140455540d0750b0042c9405a240c80c00d50421695151000c0e0448892a40405603000050322210650b1b501001040e5a40e4495906041540c01c58060a100821210505081004200700303409a24081c2c90502c000b004000001b41505c2061801c41002130042ca07401c41e402c000508e0034000400301c09201c5c1004118540d856000c00f90301c048200800c50711380c01c02181001c8103061a208035940302007903100401d0070301100e00001d8906840682040c5420f51551513182141c4d002e1f40480c3c00641d13100710119030710146d41010311206407010751762034031450600030340c2c500582c41079020042e012120300c0250b20b40070300f0a0400900360300c58 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84628625 1250 84627375 84627383
    0xb100e070f1e2601050f060a020a08030406020c0105041a01050f03070510111c020606060412060b060c0f070906120c180906020f0d0606050316050c1504050f0c1813 72
    0x3240c00400b00807020030116000d501d07802403e0555050104005030581c001d0038181c0208000d210b81c4030040d43c000b07655000341d81c1101242c5e81d291140d00340320b0b02034443c0101000d803030b60815041c4000c220411803001c41a0f003915500b0000350762101d040103000c05140040b5075040c0d004540600003890940c8002c00c095402c1c2c10310f40440031910070100e0400d407001c100c03403603520000c0d460440d25a4049c041d150380100b0132104c15141905040303118826402410019002594030018041140c032850308445605200c1022070341c144121000b030325510060360260314880e07414940000340340c8505044818015a00c041d8401d03403242888880801d1007040301c1106820758541e00540d01092a0780300a19528000070841030360386602c00c6c052404d4034615800501003100c1041040000080b40c1c10a903e020070740d29207282c1c0d030f85481c041031740b400481c2c4040941c0d0708480e0040c442000000606d040d546840c560544e413190b4500d10401c079502240c03205009a800796030000603603042c00344c023880c1c681d203100e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84629875 1250 84628625 84628637
    0x151d01021b1305071107090606050406110f0102041e0f030506040305210c0d15180b03010209060f030f010902031905071b0605010614040b07031b0b100e070f1e 70
    0x20100b0b400d07504240c610a003c61540302d41900c0064080c800c0c0720190000e50002e22003285040c4004105204500c1607004008a408410301c3e034076020301c410783c4440c0b05c0c000203640b1940c58405900155a4100c00030124641c0000c00044501070002e8040480ea081380150401d952140c40c240e450ba40a62261445101c41e0140c402c0e54417180342c41180640c0c0c1d2502c2c2d094031640c040100004031440f030103141586c024000c1040111710481c160390f4802040c140c001149904416000c640a402021a51580842c01040d10540300680c440a140b04031440c1c83c410704c103642d0315200361080b4403080d0341180240c110300c4a600c2880340035030072158104c00c40f490100307001800c89010007600004294101e0b00c01e40c40e01c00401480364040c0140c101842d40103500c51030030b0702d4481d5651542c4546280102405a841c5d0300a515400c19102040f100350402110556480c00101c0340c4070311501070184582c140725901c04140e1081c03140f05050803408807030711010402c0f0518400701c0224081c00a10108001e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84631125 1250 84629875 84629899
    0x6031003121205070c12140f07140d090e15060c030a020604030206010f06080103060e120406050706050109020315130f09030905150c150405010f0204151d01021b 71
    0x120500091400402941e40c102d041001500038420358802406203030400c0002d00f4140085094602c00c00f840140508111003001c1011368450000d006010503461003800100c2e50301d050111142d5284c80b0428400203550341050510410389071507080703014401030000e840c0c00280b07004d00c0911045a80d920010052404e050030940c100d440c6a01150080d40141c000c82c050104040e010880d0a02600590480340c9506003401c500424a4038144000380c0140c1e11780901d841e25140600200c142e50808800240d59a52559809010340d4001c01d0210740032841c2c1000042c0c000d400e442907a004400d0600d500181a005004200d84001c085040e04100d55841407000e0403d2151720070f09140c54400d88500e048540381c03108210120546107240718413a0001c0004500b2040302044d90030055080c05045045901e56003840750060560007840007040703200090201d40d804c1c905114001e1900c643d070310034513005501e501c000c589988c96100d80d40564050040030b04142c0c1300c0d05003000c1054001d052520220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84632375 1250 84631125 84631133
    0xe1b0706020d02070c080601050114031803070b04030e040c05070807030201060e18120712200d030209030c0a05090c09010e0d0303050105013506030a0c0b0306010e0904080906031003 80
    0x190245980b190120f40c000350b20720402185404c0c0740000d1420401414041d850280081c255840300c82402007032150002c00503a071461a860800c0b5010183e404032500c40c40d141c50b00e41684502036400784c0208180c104c0200f03042c5800e0140c44200c3c1455500c2c241000000d03030310304015400c003180032001c0d5500e44501003591440001d00d6031003210111000351b81c03440d80700080d60801d06036184003440c15008004c3c0380041180c105904031101b05918110905100a04480b011000c030400200307245d0081c080c4101c810395040d00900340300c0b40e088082e01d03880100c02c0b04201c511221441200c0c0c2111200f030004c1e069150341809403030001c106040500c00c0e01a030304d0003d083c01c41031280803001b1956420040c042d0b540e002050347c2c4044000d0750306203503416181c604048410f0300781d04000c2000c0500d400107001c0762420711140210961040403100405d4030b55001100719081190168005401542c0141d024605001018004da07013000348549010007040034003a4035880103149000300400000000005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84633625 1250 84632375 84632377
    0x9030210020f010504051b010306030816080403060c03090c0b0c0718090609080d0501050901030f0206071103060a06050f04020708041203021204060507030e040b01020303340206010806100e1b070602 87
    0x40c131710406c040d12000c441d500280518600a1041504145ca0190140005100c80c400c4410501c220440182d8207501842c10034401d10a42e00f0007400d080c142413952200c250150841c1009510800d2078684403600c03116801824006c1c070104210540c480e0070708101c410780030220a000c130f0001d811302007070610040e240d203030540e9a189012074090800143d0410b4480c0c03280f10341409400704603024201940b450315188e18515000001078441c05001030004100b0082001c0c4012400020301a104d59281243d0702e00000e00702881070328054090354500c50134605d007a100b02e81c05c0701d601140d11402d0504001e000604560140421070940c4114002c411180d041400904000d0440341d4030030340e45040900d40101480c41450409002d14246400281c2c541c1c1c000c81600d902c054400d1004c409040c0100c00c044420505440c8110a6400f0042c80700583e40c1c0414454140c034641400c4403119110300b20f241e144104c142c40b07003c558480001c003041406524202869071800800449802c00c82d5a454070822 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84634875 1250 84633625 84633631
    0x4030b01090f05070f030209010c02040609020703030e0313060c050c09041b0501030c0801090c030f06120203150601020c060d0e12090f0a061d030708010c0503220309030210020f0105 80
    0x48608060040180307402a0080c40448001030780c2c00d1081c0c0c00c0c00301000e0300400c11000c182083c181c002c00d111080d80d01c84c4a9500709140c00800600030150385c1c2d100a03000394024130060340000d0801e0042039645000000b02e440007005001c58074540303403815074110307460807501008885901416000b80340300d03a524015980554011360038500700c50600c0d000100301d2600e41c0d03c4241807608015903861280e070002c2c580743c116907100c0c41c081048000e43c4401c9004088510b0160207040c034104010070a2010200d202080610030b4084842d640714803520801c03040f40448143d0f006074407403404c4186a04060010708071b19040f82c00f001c9041250014a035060140e0f00d1200a5200d2003c280b1000d60328096441c2044800107450740034566061a02c000e11500380b011100100300c5031402602c2c50752700c040000030000e00e5200020043c0c24100b42c00104154400d807130702c2e018201a40700b10041e98600480c00c01c45154540c903058000c0d4690f0342806020108400c0c190154001d05684a0650b0000c2c042d0500c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84636125 1250 84634875 84634883
    0x6070f1e020102070503030907080d0206090d08060d12021c050f04030f020102120c0a121d040203061203120703110307050702040b131401080115050a0513090512040e1e04060e120403 80
    0x82c4542010082c81c902130111072f01108640c4002e0502540010108000e42c00704041d203061441950b4250100720b90920a210042855031950518a061507000c1100032900000c006101b2032601e40b094121018010358400742110f00c0c0422082000549040c004020305206005840290007100380080a0307030056100740490340c00c0115140d0401c1a0010b1090311543c950415480344005040d8242050030500c240303c0c0515400004034060350b4603c0030340c0d507881c031006c41100c3d030302d01c10010301d5602e600059803080d010a0821300503107002c0c26128140c2e8496441e60303132020b007007510640030072011386060040190800740c103044032646001c50340284000b40e00d010f40a4001075140030034290864501a5000d10000420802440715550b44005041191011500d0407070700700c0e260020400030001071000a046200b50204a024142414041c204440350205c021202e42c3d0f1303c0a00450302d281040e21100b0942800d4001000119a5804803146c081a88121848204001c44840640c1d100f600151 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84637375 1250 84636125 84636133
    0x4050c030601060302070506070e15040303031505010f050d27081c02031b0f040902041e0504050c0d050411040608030d200301060f030b04050106050c06070f1e0201020705030309 78
    0x8591820200040c5004140502c3c08600d80403498035016100c101c00b4041d8000c00050f12041144c42e0785540e440317600e40784282102c80c0e42c1d582da0300d0050024059010940042d004411000401358094085001c03810380644800c1d242c2101920f44400801c0141d11450190034400c0301c1040300c440b8026401340e01032283e805075944143c00050704031181010005024154010420400c1061881d0500301586450500c0203840c3c2450010188560066420a1240900c0414001503403041d00c180c000055a0884200746003d8a560510098403001c0b00d010000c12410007075400c0302d100c0c079400f282d0b2250117699803404a502e400c0004040d124030f544070040650011541078500750051141100814941ca8007034207000c4c1c0210140441c1c0014852101482200f03501400726030b000382c100302c02c0680000c0080000d0768554502074141d0b049007032020a83e1040d88001081240034607800095494180c0710034910058020202c52080400b0610a086540030300c0800002581000030b5402050031201030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84638625 1250 84637375 84637393
    0x91c03060305160b0d020703050d090f12020a03081506130e0a14010e060402071a040b0714090102121309060b071209120204020a09080d090315061a160206030405 71
    0x4285891201c1c1d99624a043c1d62039010004415403504a46a12011400c0562510710702d0609032582c2c080e07260440d0045090071380001c10801c0008440458a100302401104520685422070b6190b01d021001004510300301c2c04101c118580b482e2805140100a041310b240000e0460741e08800b200704d600809000e40c40c4400d002c5440a58050103003002101c0b450b8040641c54000b1070424240c010340b0441c011540000c0c402c0900a2039158044c4204080c0324503030302070409103824400030204640c0240051803043c100001621860300310703805280164000d1001d0400340c0310000281d030160381200024a040c00300050000c00c0d5001d00401400f400d24044c1e2036a18504040d039049130805807410402031052002d20084001c0c0d00c54800240d01981c0040e1205e180705425103107242c0d5500040c1c002d10540b000004001d07440a504829a4032882c0c2a82c59203460308210340c00d8582c20302882c003e00c00c034600024402441d1201030481170707200c00c00388001c0b8405500800c1d5194000e460581316500300d5125 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84639875 1250 84638625 84638633
    0xc010e0d020f030304060c0306081203090c010509090610031e06050f09010f0303050c0102042621090d05030904020a0908010b033c0d0309020102010e03160308091c030603 75
    0xe200c60118260016000c142c00000340701d62a488001d00050040d66200d1516181d0751103a400390f005800314004441850100c0304241c00c4913002141e000303581d440f95818185155105c0ca0a6410780b1130017401010700d503112a030400208a0300342190750201a0740b0701c0088580c20b001e8046170b40f0a4504100020030a0600c41480104441140c1ca54041c00c407020040050301c014070144001c45c0d4040c50965203a040303860505019114a40c841c04842d1040310310100000400284000c1286c0780200700c0c0c400c0340c1c1d0000c1140244810102e1980300c0700040c85142c6040c2440880d9120b601d2241c01034030701d0b2500c0d41001508a800c0140c4c51800120841c10501c00e0141c03d21802c4001d070000c40040070450700400685a00010b8485d101500d13800520081c504102c03500e600d40f2200020030240c480d9105c08020003001442030880c142c3c019030a101070f03040665001f10444000c0c1d180611029034100603510b00360350402028121012600c41c00c859240d5448160a06400944071540d01003015851814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 84641125 1250 84639875 84639883
    0x1208040e0a1e0b15070c05011206050904080d0e011401120311010e15010602060f060d020105090d080904060b180909070e070503100b09010c02010e010909060e27031e0408030c010e 79
    0x48660700c0d6590411508001c103509a0440742240d4013460040c04034000802750030060803070744d4000d0b90409116014001008480c00107003480b0b841400003040015003040700c9600340c46911031220340d1100c40e40018441155a00410b400890080c2000548403e40003220750031100500c9101150703070840201c88d145260103604d52401444103100801d04c0e801e0400081c05050005804280b0951003285d141c0216409901541d10344500100703000140c8120341055003855000a10702c907c22454010045400640700c03056460380d04c0c0b100e0710307122001144418481d281a028001c4803591080c404001200748400c55898800d0b45666036480c0c03030381030003150b090588070ac41d0041d503502e81d0103000100c6641d84c09108071620a40903e0000082048400141d40c4406035400c10a802420700a0101d01c654011440380c1c01031110140b0501c4000e4103030404818135040c91112001500200280003406c10348564400ca1a548080d0052501d907035a6880c80c030b140c1c410b0049014a945844024940c0c8400780 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 84642375 1250 84641125 84641149
    0xf100b0105070b150112140103150c17090307050307051b010c1101030c05040f08011b02010902060403110402040b07051506010908030409110705011805071208040e0a1e0b 75
    0xc20070506240003941d41d600e6000e4018482e101400522002c0300b00c40c1e1107040301546200100c44104245441c0c540c0181083d402400300f0344040080700d40b60010300307500703108504031001355aa03480341c2015454680da88078440a88035452034031040c8031210101d40e040c0020310304d01c2c0c45178006221004882907580c04005140003001e050140034401c800200d140c2d40001034545a0918002a103052091010fa455000d039030411011100a01000700740b4041c1540a52035820820400302e002d800260822030903150303da50003c2d0090801d000400005a0840d003103182000000c0025042c81d48840c0e100d101904001d40c10385056200350740b840307800603050042541080c801c2c68448006410180155543c0c4202d00c42c40d01c40c50740c0c45400c2020000107109507200c20b5485402401001c0000d008059540b02c2e88109844600454000217000c4a05000c803030152a800119942001d01e4000410f00c07064005000c9941c03142c0341c0d8280a44000443c0030102005110540001e0030b482c024103012440b5030ac0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 84643625 1250 84642375 84642377
    0xb1c05010e01060c05070911040305151012030210050f060f0301141303020a1719020102031303050702010203090a0e010918021c030207030506190e010209010e060a09080f100b01 78
    0x48010702215041c444400d05446641c00c24450035031aa00e030941c07400034140c1c0400382c540e00c0d00907120b1280356044020412207004074115180c07007080b118001a0184117a03403021012030484810400c444a00b806214068040c3c010349515007407154540040d1f8200300c8000d8180c2c4c00f041c040004a02d40f0452107142410250020005280003c0c60307123114840181020700c410304010f03654420184200403c44403140c0c0810301d00d898445108081d02541c12004580b00540c2d12000e003440028414800e172880b035034541d5500d207680d8103251002d407081d501506099045000c1046a105540c0b91000000b0081c50900c1060613a5803401c0070b04e40c1102d813c80d0740751002c601e11141100c05030b85c2e950161003070000200004100c50b40f880c641a440e2090326400140345006110400c01e020021003200400c3c401094414446a2540210b05080340316407800035011036800c4030307440350600b40000942210512404c00b080314548841ca543d240803140400f060265004c074070709881c82000c2e0b002d6076144d4282 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 84644875 1250 84643625 84643631
    0x7030908011803050903010905011112010512030d02130b0a090821070b100e0702030306030606062b0e07080105060310020c101a04020304031701080f0c0d020a050306010b1c 76
    0x1129000603610800703902c010b01009400305034004541d401303502c81809154060000c01150b8684c001c1000c1981020904202400150000140d81c0c02c003c85400107000b0700d2406113150004d0304040313130025040002c8402c44185940700c003241c1809030300028010361001d61a111226803070010381d1840c0041d80c003850341c90588c407101c3c0c40840340205015115025072180141100340d0b9400030300c00e80c08406501124401050b0350038054a19000b20003140124000d406444060760b981007400030702e22400900c820f007580c4c0c4032800c1441800032520786480c40e8400b0400b1401c008460318417450b009140d0840280359648134280600f9180400600700da40c0c58441c415802d00d0f0b01560059102c0e80d0b1266540c000310f03102c10840180d440d4180800c00c0c0f10400901c11502ca0400b0709009014030042003a0344000427042c1d0022402100004900b584c1c0207021004000d510041e0060140b841f80000040360085c16248020846580034424a80600a075207038031611425410b29100982203080f04446003185 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 84646125 1250 84644875 84644891
    0x6060507050601150c060207020f0316090c0c0b060d02040b09090d0e09010b070f03020a1b030312110a0e18071707170a1107150209040b0109050a06320703090801 71
    0xc0c004d001851180d81006c001601d5900c1400410403084880c1301444c0e0500071405084c3e01c076900010700070151200385504100202c1104e80941e02c1c084041009400f034005000026041c2ca0554410703c5107910107400464640061000b2032074864003915190200d80011000c0e009480e48a040340f50142e0044400340d00ca94901460141c25124131000506442004024101450300802190401c240d002e4082d40c014807a04518000e002c4090000310000741c0030312941d039030303c14180c01040056040b130320507940b402244410070380d88801850031080d00308545240000650811601c640d02c10242501d034190000019402c450291038001e000c0c40c09d024003811140074248040500e598094101e8200003088030450741285414050080001c1c50b424405412440403041c64000d0550301d03009403014080150f4440c0150344605d11402055040b0039410401c001c6240304000031030040c061210a685250309060040246242030800c0c4603414000150200070940c3c40207400c1c006103401402046411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 84647375 1250 84646125 84646127
    0x901050904062004030804050a080a02151602190e090a030c11010306051e04230a021806130617010605030703150f030501050f0a05060901060c080702040606050705060115 75
    0xa1030161028181a0f81c03080d4003401e180142041040b107001d03000d84075803141e549241103862603106010300740c055481c4480c000b1b00c07040d0010b00c488820b43e0080841c4c605d40250010010240c03c20755400000c0e103d00c06201c005a102c000c020801d100311140d08030643ca042c68840500a90050b104903040d038044071100c40420791041c100c0c1c101c84c0d070100c210341e10224280c0040300908a40d8120311740c0500108180c03d01d01010030b1a060301580709036014020141d04c8503010b00c18225074900011104d00c140000b0f01c03a0742040e40141940c400c0540b990816520740c101081041d0005a150b850204100b1010700a460300300030990f104500341400b8a1066050a40041041c00043e05140500da20344500c0f41d026006d0b8400305000e8400c400c40ba0302050b0792400c1035406880140d9024203210300c840086040e9810901405116100c06440c1001e41d03464210111440d108100b400e4444100030721903240165140d00401c401002907584180d22281e43c1d007011400c00030181e006540c544001d03070b0110302d03031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 84648625 1250 84647375 84647389
    0x1020c030d050c0120070b1b090609030a0c030b0108010513020f0f030a050607030b090a060303050f0a090308031305160321030f020408060910060b030109020d180b07030b090105 78
    0x1180c10301d0043d855800200c4901e014061000f1200302c19058440788541c07102441001d842c0c42d501804d00c0e81d44d941c0301e800105201701d40d4000f8005448800300803280c2641000300c000d01c4200320203811601c1500701500d032281d0340d01050300201d4503410b4000c0104540e032800d02601d500401050001c0c0c2d010b40039a800110b0031a01030007003e025403401100049565000d01c10404680d0700302050710001c1c50500c0004004184009031b03030348108195004a60020781c188211400d1301d90548413940703400c00c41c481c0c80c061074000b203103d0300400011a5003c80004d01ca80b001c2d501502400007815207540b181d00c2c0807400c000c00f20b01e80454620f02940200003040c21010410411240c400c07082c0c1001003020403c40c050b10b8101c0410010900000f40021040b4000070503074410020542aa0003121802843c0f0050700d0544c4120107201c4001c2c0014040405950b000300914070a1800014600109a40c00701070f0710038510096840e8083c06082050035905400f403901000c034201c1c0c400c10300c0e6042a00050380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 84649875 1250 84648625 84648643
    0x60801141e040e0a030503061203071203020c030c030a0507020a0b070c06050306040b030105130201020c4e072402070902071b030506040213050c1e040902040f0305060601020c03 78
    0x200c0c00e1104a5010642c50703c0c0d00140c90140031100b40d03022480b6605014146500c107941280c010003102c04c001d0b441c0325000c8250354941d54000ca04d5082182c5002c42200a50070445040000e070004001c030030000c0d40c08100808010707070141c55942c0c68010070300410074071700034507404000c44140400000c000200d814035440151031030360405c0c944a484001c00315005040c22050580c040d0700e040140010aa07108620911443c400d0742120441060041441000c500c00c1030303088204000e6024410049001ca000c0c0310307505041c100070011030b045c18400b1080c0c5c030040500440e52900314000500c104400d410240c047c51640445014205940c980d000355104814400c840311980c1c0428450704200840181d07041007054081c3c1000955100e0403c170342c58180c00c2d40d0482c8646010700b0040348101c0c1c1401411302c41d43c2000c0105040200c2882c51004a09895504a02c1c040e0b00700404500a2a20310103000940f0561000c2010386085140042c6041000b6102605642c00044625a176550000c1c003505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 84651125 1250 84649875 84649909
    0x30203010617041b170106080a0209070f0513030b1603020a0c1b0902030f1806060f0d0203010e010c0309030210020c060714090402040605070302101506050f160c06080114 75
    0x100b165038030b04104c1480d40c951407283c0481420f0140002c2d030241078004078410140c0f0389000300f04081d900d495441da03c1407800d800a410110050000e080c403030280900c0110140c0302d0801624020220086070381c10b054541041b10354410f41030601c003183c0c100c1032034020511040d040451a00c901020b001c0d04003500b1000052590301510b1315000304848107190a4000c1c5039601007551070f408c12200050805000300e503501615180c030711020030100e1000602a0155101401402c0400305210900c09032944034401030341c0664840905400c00300e400d01c10000c4003403050340c00040f00300742850028105030851000700c0c10785005108405440d00049240c1e034100415081011250040c000590050301956050561081c404a000104260810014844070344a9403c0d52000402403034850704889450b055510006c01d8590103000480c054402014001483d480301c5092100250300141c02c624440011242c1e0a1004000c2200c20340021141d405003ca14100101c09003a01c40822021000401c0d040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 84652375 1250 84651125 84651167
    0xf061b0f04050a03030c051921031401060f020f070f1502150901021809101509170f01060e01060206070c02041b03091205040806040803041b03030903050705010302030106 75
    0xaa0030038103a2045500425000d0081e800240c0d40b0306014100714a5030303609460741e0191510f00e824401169841d880110362040309890742d10b003100c0c40c2d441c035948100d480d8003e165032030100030200e10b10400454001c05450b580c00480e110041c5009041500150f00300c1031030f5101c061b05001c1a400805450300f5142d103429008001350513900100c0c41c0140c000185450300031000c05000701c806064004210007200b44c0031243c0b00208103014800c88140071030742d8102040e00e2007c24480d0f41c40c162801e00c5003801c41d161800d095500c0d01085d0324a002603208070f58140e40255844003e40800b030040d040105607105958200758540000a925841d000b0308071010132180e071903410119135950380b0503020002100c80c4079591004102c405401000441000d99100710141956408a481a400c440564030a14060032031501c540d59600c43d65080a002140e070b9185403c0e400d281a6048480140218081da0340c0d00400f92640c1449400c000c00358003d941010300410060100325008000000c16a8103e582e003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 84653625 1250 84652375 84652387
    0xb06070f080906040303020c0f221d010f0207050f0c180405010f0c020a0c050907020c041d1203070801090b060301061d03030a05090102070806070e0913020d030c050f061b 75
    0x150410702c5050400c0d580200e010030301000385a80026030fa0380c107074070940e11502c044000004001900742000c4280755154110f400301100c400c980d4003d4041b03035003c5481101d000c080b220305107003900c1c000b040701000746034003241c41000e11408201900000c0d06c00c80c0a048000c142801181070403044040c40c1c080e5011070008241000300941c40b94104151a40e410800031b901da103402074941030584c07030548213100c80c40d102061916004202a00414054000b002500c1c640c009110203072190100068080303031858000c0820040910820940e075010000b040d66901d400c0b90081c0c05201c06030001180c00d403620711501e107a6101d01084034192103440c100050380b011081c028070f0f9118100d21005416001c0400e9403c642900300000d4801070f21300340c0a5a4840352501e0010381c2d113031004c0703440c00001041d03052500701e1400c15200349a04445660700a81000c1d410b41c020540b49003c0840032800244200400f200303000c02400648030605185011b4222818610002d01214010f80c0c0180301c420000556 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 84654875 1250 84653625 84653633
    0x10909260906030a0516030e062a0a0e090a0209010f0e040f0608060109060803030903030703180623091903030b0102070314030406022b030504110d0f060c030b06070f 73
    0x19501e403000001c20043c0e607071500100c0e600c05400155510301c4100490141038007018000d000d4118826040d00007000150b07240324400100c41d41d20385020080014118440400721a1440205100041030300d404601009460522425032401441d03600010b105200c5140b4617a4405041d00c441410740c608503c0c0c80d6141c00028005080041e00001094909000020750110202d0114100c2c1c8007034004000441e0703120720045e141d00c81103030688034070342007040010b2119009600649482e00707098081e1130000000e540e441c0880390341020181448a4429004a0301da80103802a94008450000303841a15030000c0702e01c5400c52030345c50003400d05495112402050b40700b00803100007150440f40366402e66102e0b4071002c1c2c60707610500407080107006210720418400e142d04051682820031500d41107040311034070300444c020a400740c400c442190401906429580c1c0d081e1400710094025142c3c6c0e9407484540c5440c0d400c4510718568042032500f8641141216903d002c00d41d00e481e0f80255640c00c181c011458 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 84656125 1250 84654875 84654877
    0x7021b100e0306090a021c0b0105060d06331d01030b04020f0d0e0c01020705010906210507020c0307140607020409050f0d020610060903022101090c0803090901090926 73
    0x1c0656054810a81000f01148000440d10b0480c1e000f520179070707902100005030048040300e64a0161001411070010041030070107100030710054880384400540c580e2192081c564124801509100070b40300c90015100300710508041110300700c01740c141f0945801030251603031980c800f1101601d040c160354000403517840c0c445404540f02034002c02c1c18240d6aa11100d18080100076000b03162203248284026519035500010303004050f03640507101c2d00910b03450050100c9860003803180c40c0b034140e11000300303603203041d0301034015180100303801c2c3c01074000c0f43c01460505250100301d9003d81c4e03000c1d240342020b0180c0d840d240202d40f100c540544001ca02d410319030400a00c1c0c403a120440502502c61109214501e03540860920301554540040f07d12182d5901c0702114000e425000103944440100d8110b204a4984061000780401180002c1550205a1140d4078000200d9110001c641c10002d0422410f00d4009002805800e15600401090b00a62500d4080c03040344005107400c20034240c3c0c1e103044511100c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 84657375 1250 84656125 84656147
    0x1e0504050c0a0f030b010b0c1509010921080a0b06090d030c0f0b010503060a060302061b0c0306070503100f03050a020409080d0509011406060a080417160606050907021b10 75
    0x140001200903030f42c4149143c90a99884151540c0d0030100022410469010880300390120000007040c1c3d4111610001c01020b9000d80b440c4030540d030781d48414000135801400d010341d030703604d002c2c1c010b103128150300019000c1c01d001881c0c52580f514200c040e82480d80c40b4810b40d00c16402c16250700c42045540c1c07070300750f50414900001034460010040038108001301c100c00c1c54165403042d02a520a507c41782000f90640d011804000d51156040c04900c440d28502c0b03000c0c03511181c8040454010340c6d103500c082428084d0270f5641d200050f60010411500d100c500540300c00411176142e0030301d4a6032541c0c40b40c507242c2e002c180000b80b20380e0322040b0700018081d04100352150340e15000b40800c520300f0070243c00c0740242080c15460000c0800744000415a1805005a80c0e42a006490703150701d0744c0c0e89950302c1d0070140e56003861104c082402c0c0043c8541014986000006502c1000001599170400c0108109201d008162404650204c914081c2d00305450180681205054803004801004503a054400b40c07026 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 84658625 1250 84657375 84657379
    0x31518060c031b07030207120c050603090f01061d1314060c0409050f040803130201030608030c0102040f05030a02031209010c060c08070305010f0f060e04110a08090c041e0504050c 79
    0x30350521032000c440400a60155085814070780340c5003031501901520b07019030000540960003e00c4204101c4000c812074070b50a9208400c038061a1307442e400011055001650304501c81c1d0b009501402d2400000d00c01c09010b410b0300060502400742000c4020b01f1340c00c0041c655581c03412140010300c03c0156a5901100c9800840261070b0346207046a044486500580305030000c181c02c0c600400d400c0400c4a60403801290030200d11481d5030340d014800780a41c80780c01c1d0708038109542e03020002100001800030b003490880781400560380c0c42c548415590310200720b400092003138000d103c0e0000160b40c009018854000300208180e207a40d0144016590701720900000307030172a0300784600c01c5000b40d40804664031441d0903407020080c590f03e903046d020020340107002e010300050002205210441c010010080d04413401407011948103940790035004182c0003c20703080085000101072000c1404203026808900000340c0d02000551501101d45134440c03000c42d51084c03016901d201013028040f05104400b442580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 84659875 1250 84658625 84658633
    0x120c08010603080a08070906050412020a0503010606110c0f012106030b0f160e03030405060919030b04020901121e0503070507060806040609020c0a1106120406021b030306031518 78
    0x242e400c04440580c07040f035014001403003d40018038014040c05096003a07601039510035080505001a1a941e50f45d0013109076440000700740b0004090703600340207170400790449688141440c007059a989150803615101da510410f202098003d460740e00000364001c121181c86440b02d0b601084804400400c2140c00240014555034208041c583c8040f00b414003070702c001c21003102c074440740101c1155410310b2031418581c56042000100f0982c6014400380004010050401d4110f51a0405000704810a40d0080b42e14000c07a0041100303526004012500406100c002030101c2030469461030000a80008003180501d82000341c0420b202c0c0810644074050350060840c3e4040340c072483c019100c542d086414601c07542c201040819420719034003d40303084a07451001405008402d680e0620100308544403550020b9060080000e0207401074241809640a004016078510300f0440c02e0010480c9140b02404541c010001c0c0442ca0b14002000d405100309200340e4092a00d655802240301e00c01c003d48205c440c81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 84661125 1250 84659875 84659879
    0x30b0f0c12090303060117040506040206030a0e0a0f03020d18090213051201052208030c0f160b01090b0103020403110904030509040207050106150807090e0c0f04120201080c03060a120c080106 84
    0x1c0003c0218060303203098a82c1500c001113050071791940c02003140c0040181e08804085401030401300042c40c0c100500545c0480e100b0740781c100c0107103080d02d903140656140e0103110340343c400e068050010316080542450040402c0000b4485248989c01a01c00d461444d6400298058020960030341ca00c080c00e4003c04422408141006541c0030304030a40c2d4005000c80b40e6840c41c41c13035251481c0d800542e25400000a41559100480c0011940012984580c1c101c0b00b080444858a188075140c1d402504c20001440c0c03950611100c001112452610281894410881400030070440c1c0400c41c900700c2e04036001185a80c4031b1800300c5041c02030700c10703003500140086030354010007406402003000e860208120001000c00c1480813160300c9d0007501d9036000f042111070244180030700882681c2d03000c2420066145002c001085046d0350368001d50040c0d151251016001c070866a00c000f8281e084600c1c08582c2d415400d0400000f10345c400b10b8810200c100384012158010070080f619030100610b2410000c005460f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 84662375 1250 84661125 84661141
    0x20319050c010e011b0507020406080303040b1603060b0403023c120c180c070506070806040b0d11130b0603010308190c121202070501060602030a030c030501030b0f0c12 74
    0x34109201d86852942031042d03007030300c0d00014401d00d403101c41d10b110f411151000007002074409a0000906903000b54032180c1c08600c3d09404c03c01140940d03c45c0040c2c074441c2c0f50410b41c0074050303c82c0c00203510405003084000c01c0800c8480c0c0644043d260119018042041381c440145404110705903181e4041080d001c0c110b4000181c01c420300b5464106541c00914038001040b91368a039003540e03035a96402840401c044140007004a12160701412400d411450020b15843d25072074500c08407032100008000208204ca242040e0040201d01c1400b0788070304405040c2e0341d0f6401140001204c075540101c008007214030981815422051582002804042c0c0d039584905000b1096806040440c0080301400007030600140b25001003078210f03400c81e2039900e1105c1012021210060101d6110304019001d000b000013080d0203100d804001c0003590011a90382849001c00b40681d0241c980700024103250100400206840c40c40295106d40e528164a0b980d55622030001d103540681d40703080d40d50141c0407040100d88 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 84663625 1250 84662375 84662377
    0x906020c0a0314012901030e010531050f06040c12030c0b19060806063c0f040f0605030c040c14030c130906050f0f13052a04090f05060303031602031905 67
    0x800c0087e42c0a003d090102c0700d10701d003601d0055500c0d040d41d5102c028400c040da8103d24844403000c0c1007620503030500071280c46003031400502c0d80903200c0c590000300030311007004420b490010092001366925481080b45440150101c00301c0f02000d442200c0900024015100310400c100e07244c02008010440c2e251180d9000c0e503215002c8507081d01410091204006071006040322120504a2015200999075500003250f6031a842a801c1604120350041410b2a1799a50103528000785a604000809074074103030803d840c0c10848032841d80580c0c40e12420840150f4040d4241c48030103260b00841e0760b40d45071310341d180da103900c0784481c821a1000c2401001c0740207055a00100102c640803107151010345210b1041044044908031059480741c12088280070704c190350f0700515803100b07442001d0103400e40803406001021417150b4004804400c0000c1c184050b080c1440b80100301010060200140c1c41c1283c04651307a41320140494410000411761101524420011110380300c41d0070200c03840131040c200f405441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 84664875 1250 84663625 84663701
    0x30307150b1c1506050d060e0c0909060601020601050f100305040c05090c1804060e070e010c0c090f0e03030615030c0409021201090f1509020d021303120906020c0a031401 75
    0x1d02110340c0c0501c200505001d5030065440003081400c40b206d1503582c000c01420040d900e404113015950351910340c4d03600c4c000141c2c0724072013607000307403800d454884002818100140c02c103d10030039230081c030095562221107444a00e20f566050000d201d4441e41030031001d2504a0748001da000c0c0d01c01c8200039410000c2c0000d006154403003000c080344101e2900c100800e86d8118003070b221030080c860340000c8080344147c0051152090605080010511981f1410a0301c1002d40045c01c20988820300305840c12400c0c0b00700204460020051400c501f002000540b1000c029404440801404004038000c07920301002c0381d00401e040101150f4416440b2a5411625001d1290032001803410719400c006240c280203c0706114151f00c25047c105041c003804a0082d000b03020142c00c201d50034004039201c2d036410b210350b1000d9800350341c0e007200450205100070000203040e044602107402003403003102103860724075200c02a41e83c0036914050421180e1005030041c402c40f8488d0090080174205044008004004004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 84666125 1250 84664875 84664883
    0x1150503160308120612010617250608040201181d0c131e120c030c0b040303092303010504140d03021c090203010212010b04050a060e030307150b1c 65
    0x4004241c40200303040994030362202030070140041041556251894409036805540105510303100b41074040c515003106d903660400d038103d150821b0703002e4100c001080700c04d91040038550f41c1051103181d1203207034500941a01c595130600c40e642020178110780c00b400d40307108281e034007983c2c01075003942d00c0c0c00360b0210030500c003013110311000c804001c1010300545d80f0454461403869070b01c042c4454503081031794a4500c1e088170742010008a226010a441d040c08640c0d1048034020141c2303124450039818006603620042c1d1240c980381070304000400029811680d18001c4496114501c41011000c1550b6106c6214800f030311549075103058200000c00c182c8150780001502d42c80c00300c03640d015031004250100e00c0348601c0e00c81006901c20004001956a0704001c2510303201a00250822600c1400e1801000d000c0e080204e21081c08542803155040481e44500142001c0c1f80409030800d001c40403984a2050604c040d148050358644040102c100d034110f18004d590107440c005a0400b032035240100880001c004031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 84667375 1250 84666125 84666133
    0x9050910051c0b0f06030f031201090b0406120b0406020d09030302030a050c03010f03080f0705161505070b0408090a03120e030705030a020916111002120603010c050d0b011101150503 80
    0x95081e16020184070007107911014004070707512021a44c018600d001021554503204e11660040742e200d0500281044c482c0d40e503520001c4d9414016103800755004100a00d010314a000030410010710f51204807454590090303030806603510340e0300b4280041d114010001c540f007400d04040c1e0b004c01da07241d80114410100d20604100d66143e090580316144004c0c410b4400508100070280701107215400207100c50752400f00094035001560ba5280e00703181c13441c2091030940f4246c4804201c5e4000c0ba03610101d00001ea45400c51504210b0364030090203000291024016040114505c011034492000309030141d50424802404022040c800410907260450040d0107401000000903803410009021289683d00900b8411165168021455500d204521103006c02080c6490140380c0001889401008080300001595485452a46801385000901201d021380c3c540940d034080d49130700a054409001d450000030400441d08001281e565806015603603095184c405030541241e2300d441c0f10011100260161 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 84668625 1250 84667375 84667399
    0x90601030e1c0c02100c05060901020f1213021201051812040311010c0c080d0305180a0611040803031305010617061f0315050a24050409030905091005 66
    0x440c1526400206265203600c482d110105100c0c10500003001c0c0c0c601c41c60a1211a090f40e00044d407940c00624002e808680c80b81103607800c1c0481440400d03403100c0840001d61520001003000030062007600640d2401400c500003142003038014002c28072101c0e4005003111600031b41c48040b60300030708003030714192114407403100e60906040740416104408010a000281040c1ca0b50705c0703900041c03880d04d0f4418104500d1403a0040000c1c002c0d4041c0f03005e000c205c4003d110071030300c06d04003a003102c0020304500081070482c80c0c440041e450000300540025070007180420784d10480d120b9a040c4d8080d41d00980c405000100800c000211941e00e4070101c00d02800c002c0c0310b5a550380c01c41c1c003a20340b030310051a029504014001030309403002000d00b0061a80459040400d550b59032210000c403150145100089500c500621080d0340c034a0040c1104100c503003407826542c01c0300030f400300c00c41d044a03c200ea00480d10b8503044070a040c005d145903401880082d0004910f880c1000003101400d803030740070707003417040b0314030044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 84669875 1250 84668625 84668627
    0x50901060c02010801050f061605010504050d0302040e0714040b0f03060a0f03030c08030405070306020309010c0807140702040f02090d0503071a040309050915030d050901170c071202030c070f0302090601 89
    0x1040c1ca005406031030b0407040784d0a110030b01c00b040000b0011a0382000c002c004c0c41419444c410b9029510301c0c0268000074203030030300d072820b42d051411442c481c034100740c01480284407102c41c11541640103481420500c8046d603840c902c0a559008580c001e00d0200404a903401c400e1001c07400a51260f030301116184211522801c1c01c5880c000c1074007001d80059056481c200019404100440e0454050011166010b95a540d91000c1ea40304071040345490351240805e01e00075810502040d048031050038158101c0403105000340007401034140203031155464960710904030004d80d0442c1e5130141d024003149031305032482c101607590f40d00c000780803a80c006c0c54190401900c1c070030260361030003198543d40740080603280c2405c00507400c2c0086c100d102c090301a903c000d10241d604012080b40d030402a1900c40d01d5816210000d080300511500140d5840342c4401003019101d401c40c11640c00640c2709004070010060120102c0c5180101c1d10080030b540314189010488003d91b001c0c1c80112031080790b00808503500c82d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 84671125 1250 84669875 84669887
    0x51006080109050c090922081809060306060d0f050105010b0a02070911040303030207030e0301150515040b0304030c051e0102030118090c0506180409060f0e0a12030c050d140105090106 81
    0x16240b401d400180171030f0500b45070070210b480e08401c1c0f81c0c102c0e20515002104001829a103020100e0703048a000482541401030307000341003071421003110003a00924041c8080f07500e0301c070010803061080c010303902c001c400c1002061405200d42d402c00000c0000d50707110346000c4125802040d42d80c0241c840d0184c0010004007034050444800c61003115242002c0c074543c0c0a402940207003804034213104621248840c1030720b092095142032140001070502c59490841407202c210030751050780c0500a0104014414803018404598001e07a0514201c5940c41c03903420400c3c20540200d14000e44141002c44213800b071034054016505840c41e901c41600902c0350000000e0407240309840050202d0701c44079040120f89131030b4004d040581155401725509164141c00a0122240130000301c1d03440e540c1c0c10b070590000085200e03041801380c040340104004204c0303440340f1180d443d060014004254552542095041c4030b40c0540c1c240d01c00c11032040c0003c0401c2032101011075001d010b07060194080000014209118070303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 84672375 1250 84671125 84671131
    0x4030f110618010e0604030602120406150602030f09030313060c03020610080a06110d020a11060609060603010308070c0510020109121e110f0a030801080c04050f151305100608010905 80
    0x440301c402c1414000155020703001e003072040d54014000d01000010038254001400c04021581882402e45000d207030000856445858008284480c040148540342d0000704841c2c9a000500c90662101b1484d23002900c0e40c41108003c0364030400030180080c0d520b410200390b00c0c80174402c0d000c1e110030765140c98a1102102040c49804415071016080d0300204015510003801e000603005040e15058041c240721003130340e0003a130070900001c0500e1151182c0c24810312071035811a0307044490702d4250400c44001000c5000600001c1d010700350005038002009480030301e03080180030142400d000c1d90000000a13009010100083d64405145094151918070440388012041400103802071aa2091001110018403403040d03902035218107000c140140d50108080d4806a1080d66604c450350b040110031070411180e00c0c20980190b040000f0f0240c01666106580e0340074894000c000309142c0d46500184002c0a0300d003050500c036140c28184002000b901000da01079840d00c0e00d0310800ca913a12805042103540072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 84673625 1250 84672375 84672397
    0xa09080403030f021e0f06090f06010b0d0603061503120c0201050a0f030b030a06060f060203030403200a0f050606010306050f030303130201050c010e06060a05120606101404030f1106 80
    0x411007840001d0080c2000e0401042a10459604500100c085a02e00d00700f1141004550310202617290307060020448160300c44103800140198448211310300f0b0b500c00042c0580300c20004081060303c1092402d81c40280115000038042c011400301e484440b0801006000580d6400311000c0304040d0790340100c00c810352180e4182c0d103042c40c244402500f00c410950b5400d40c6010140c880e41d440c1e40594003000702028050040500042192a003140b180c1d404a1076881601550418010040400e80003628500c01d650104d19004203000a00a0141401c4200e04c000b00701e08148804a000d0140c0003030854800c0e5420788040140301d0f00e83c4c0c1000364203844400c019034176a20030000601c9c894081c0c100001c4051060502d10b0034000d409903094252440c5218001c2c46500c039104001803468000a402c2c02000c0958902c091918100c00e6140c441c0c100900540c001c054207a201713419540314085034080c032a4202d06071a04c880d200d150411191900c0d500c262607a8405c101e6600540c50f107003044640800f01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 84674875 1250 84673625 84673627
    0x20109031106040e0c09010206060306100905041703070e041104050a090b04020c03030f0702150c07110a050a060c0b0a0501080a11030a0f1a160f03050901090c0b120a0908 75
    0x515614042108071010300300382c021806100c0080d104038901070700c034050055440d041e03465003803d400081c82c1c180002c0c0900c2c0300c0e40c082014040c902013612a410182d40d00b00801280f580e0b50741c00c207843c00d8640c0560300000c95000008203d0300c0c3d035010342003c4034000215828058100c0020060b1114000d0b40a4280d000604000420821486038068034001030007500c05802d000703100c1946421a08211081395141c0751710810408001d42c180416441c10103010000c00c414204000c0c12141800b84500060850401d040e5a00b21541d54204903001400028070b1441803903120b6200070100020184100c405104110106007104c20700e00655050341c1c848070081c481541d20351254034a1038040001281c042c06000c40c5c4a005ca07141550485d0040e000d0a420719032100310215003555484020003600c41c0c007810344070030034075650310100e0204c81d011149008900c68481115046c018450090010302814040000250502d0003c020b0303c902c15101103078603216945d201440b01a2170bc003413001001524 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 84676125 1250 84674875 84674879
    0x7020d0522060804050d0306030803041131050609160c0f0c090207030215070801060f090e070e090717040f03030f111b2a150a0915020307020109 64
    0x12155001d00300e12100c030a040501d80c040c1c1419550745044607000140014004401c002c00c1c0301003002510305031116890f0400000345151200503603070001400c014840009800390300984e075034058040001c8480002c10030b042c0e884c408010000e410001c15184800781c01e000000390b081c6440050603102d415800c8509040d405c403101c0460710800b05a100721342c3e442510201001007480304060030041d0000520041c3c0e0760401e420041d10f8800160018090841e5510401a205501804503411500700b400c003010400300001c01030311144000c0e08407000c40b40454040040700c9070b002d003002c1c81c002410b455511240d2510682250100d04041c2d00b40507220300d42d400305002030038420032844a02e00a03e00001c0c40780d40520800e0950391218001c044105e00401e05a4a038510500441c80ca01307001801030020031110072500307038501003980401000c0c0c407858580e525652540e261001850803900d1009640b010100009440410140a050000750100c0c0d85042d45500003c11200d0b8650140c5030040024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 84677375 1250 84676125 84676127
    0x10031d0105010b030601260106030f0501080c0109090b03030c010e010204030318120b0709030f030c1101090302030601030f03030b0a060801060207120302061305120d02091306030f08090402120c091807020d 90
    0x3261480c2072642440300c81c1f040e18000800101d41d50103000135a9000c03403a41e04004140c1c040e944180c01481e400c2e04502854800d980e007184000084034034045020900c045400700003811801082480700903542095049110100198000c0054a110346c0f208010020080c4551070020214040c1200c0c00881c0d001c108003080922a10907070040c4685450315000d512070303403000b89191030710340110302103005d0003500d4081102ea005030301d5500c0c2007841c02810f681d14640000365140010b20000d001c800100c103040d824180b0071342040c444103401a00c0004600d07500c51005060301400d100b17110050042e0440403c580c03030700c1c9013041035a507007507402001c5503269054100507240d00440200c40c0ba100d221030400043c2c0c440405091155105280140c480c400d29080c03080e0550030001301c1084624206060001a000540c40d018140d00704100036240e22070040420020300c6105050560a1402030030807018503c10382c01080c0f1742e941603904580c11041e440542201c85029142c0740050f80006007000102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 84678625 1250 84677375 84677387
    0x403030c022508070f30020d2003030906040611010204050402160b070c080a08060a050a0b0d050907050924030a08070303180201090605090109090c080717130b041110031d0105010b030601 82
    0x1c1b09841175000b6203658650300140700048040c8048400c080c00c5400381050852a01c00038050b010154099803401311224006005807045005800034460503000d9112400c3d800d5041d50060302010300119034814000d45c10160911924908442401514000070400780c800c040c600010741e0b12484050409190f040e094940010092030542c1250b540000000c1564883c241c40000b850541e0ba410385da0b03845200b00741c003074031070044c070000c8030b41d003e00740400c0380d81c5504000d1030703100c5130785190004980c0c41c0303e0318184140c0c1204c1005d41c2c14810403030800280300d40310005110840c441d80b010402a5080c0103140d95240301844081d01003480145c00300700c5140103800816140790149020100d03192030358410001c41c2c40004800001846400400600c2504101c81d0b2414110703e00e07521300b803817800100d20700604560320402014081c808000c42c0030000c11090203078001c02d0007400403ca01060520040003040f02180031001c03003043d8041d0074070018041c405c0314181e84085800f01e26540e6020019140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 84679875 1250 84678625 84678689
    0x6090706080604052e060f0503040210140f070813091b0f17041101090b0c10020a050d050f0a0b0a03081902070302030f0706030617060403030c022508070f 68
    0x400c0917042c40110080b00c04581000d040c100411905845604060005101604040e101710602c8410030501025a40b00f01804c04200c280c0d18040f60a040349041006943c0103004501c8903081d400b00c2c2500c00c0150030400703081c3e8200c8a00c030900c1502d0350390203054180d0300a10f94a600200e01da2103001300030751164007940442d0489041c052200860324001d0100d04000703c81c06d8031368428a03140d1800740d41e4484021002130404480403400d244c420301d413480d1103501c01c0c080c0309846503001581100307a50042d000c1c1c07015094200d80811441c506200c03070b8000c0c498200c44050742c0078a0044010031038501081d441e400c0e2074010081c1424081c00c892040b600c442d0720140306055101c1c59000000503a81040030f490f81c040c803a006003034028582007001e400c3d103030325400060034506070f8002c1e040740e00030000d4080d60240d010f24020858244d1100243e00303100000e001e0150303100da013580c00c50100d0100d116200840e100e5000b15041aa034640500803815003500500340486000a01c0c410816020040014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 84681125 1250 84679875 84679891
    0x70801061802042105160f031101050307020618150109050709090e0304180207060213030b060102060103030c1113020307020123040506070804140304092414060c01060f080c030609070608060405 85
    0x38100e0f010104501b040169511a02004901f04c07810710820101902903000403d0a0902900350f081150010b5151350004080410310400071050383d180c0002000740705503108081c0300c4140700f542c640002c5006090125001070215040180002e04800d06120b829500303801070000d1800c00e800c0c100611505003012800d540b03200c0e02846035002084141c8010840b41d42c4810500904915600d0f2508601600500040c155041140100042500809031a400b10380c0074600004604c044000200d038075094900c0f80c01c05500c048104141030707805520030803100040030180704079003d4808010418205c00c980c020265008080452003035070041180d942c20521a0320508040304014118506c1c64010f0f500c0b100280b5112804051007420740c50312503100c03000740194904070a0400c041044a07a0683c1c074a90300601000801048400c000c0d0700580103000365441240c1d040e0344d0f84901590360002c10f13407481c1c4680a22004200400740024107039080303608030785642d0007903a13842c0c042000030100189240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 84682375 1250 84681125 84681133
    0x1b01050408030a23120703050c07050607031d030705071a07150203010303080924220506090129040903050f070f05070911090904060905070801061802042105 69
    0x11800322810b20242c0b01500441c1d545000c1041644c0d08004410071000300d469010b0810810b905210150f103d001d0ba04c0401c41c2000b00302c0d0f0b01c40e61030850240c400d560b400341c21401100e06001c0c00503803540003450004d5051060800303100d40c82603403076207a12900100400d0390f40422000c04c51300f00010000c20f602402030030700d03a080105940300e440c00d006c11140000925a03001005004140d0860b004607000043e080041c913008903030b102c11a45031020303102e40b401c000c074046001806400c005418805078800211424182c401b091406550741e603030a440c0035807103500301080b01d40301c01c4135070085925140e15226508141d0640c0000e010041c18900703c2030b020081e0070040003000703107007210003040d580e481100c1c04c04114545003080c5003040115001141c6160518401212001c01c3d00140c4500300c60880b69204d8603216441d042d0014861080c0007882c6001d914030000d0404410341c040030481d4100344481d00c00c2d11040303d40500320300c294014103460040208900f5400c81220010342100ca10500c112 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 84683625 1250 84682375 84682379
    0x1020c0d030509031002160b0a0b1c0203120c151317090a050406060509040f0617033103080d060f12060f0204060503040b190507050307021506031b010504 68
    0x42032090003400025000b08100240703803400c03824100110a2210070050b000c41c1068180c00030001c2080603190040e005e5441140840d886003642d03804000040d00062032030505c0c01c05000c540180c6180c51000b82d2290080c5c10107510075131411030448440040d42c202401181000b405911884040074001c1c0b80512014100c80c0c00003014400f04444404298034003507100da000c6000c1003803d00c1d054211a00840c01c01004120f807503000416500c100400715000320300748072600c0d0381d40000c010325880445210307110b5081a4141c3c030003100900000392003400e004098101a000240d2280e40c030044400c40c9440c1800810100d407908028102c0440300c14400f18140d0f940c0c2459040081103600040c0c18040021892020050203118074ac0d18114200303400d50601e880d10b400034155010080c0702a11a000560008102c400300003455102c1c2c10b00002c0400bd20700f0800e200801c84d4000f11009009446420080990144034070b0185100d0200103005140200c4054003001d00740c180701900c039043c01414440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 84684875 1250 84683625 84683629
    0x90f04030c050307020d230703080316020c13060315060e0c070510110c0d3204080601030b010f061d0103020a0903020604032001080408070605040c0302041506020d18050f01020c 78
    0x8900f40203001c2e1101888100da1b047c54003072141c2801250b90385c0c0c1e03403200404000080702c0509580e0301c80f5144141c0c0c04e080d12694416801c005607482415030101c0000c03112182d6035030b42d50102007583e015640820125005d0b1340c08100715030890160110240b050380024121072003210040903410b01c18000e4404c0071021008403000e440126042100c060317004100c44180d01e800300314109408605203400840030850303402d22500c0700c80300c8005c100c100c464886148030b0040340204440c010085a400c0303d902c1e41c0d580c101002c034601c081c091030700154100000090ba440c81400c07080d410b038089007111800e204601006400a600503443e20381030110503180040580c0d10040508002e50240160f003840e80b40900e0030f11104001c01141034103022042c0144004114110151b441856125000140319144d50a000031030a0481d48025031080c180003503000030006006820342110890703002c4504040440000341d0318591000512201007810f240c2c104590305d494040c1005003001030043d500d07240b0300000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 84686125 1250 84684875 84684889
    0x305220e0406090b09030405180406090c0909060b01030b01052217010b030f010c0f08090304050406061107090204120b060406080303070908070b03100303030b040b03010e0c0f090f04030c05030702 86
    0x502030b00c44555582c403590500903040b03070450348000483c001c0d51a141c2004000307000003011000802e950909580081c04114982e400b0000c082d030800280c801556903501c4100103070864000c00c58501c1e00b0148400a030b54004e0143c0411220161542410f00392a15894010402c80540c404240454100001070138160403a214903480c01d24400420286000d00500d494000c000080200340d03031408c1e610064980d03000060100840c034515294003151100740185245008136008641c4c01440c004000a80e03a8004141c90b106183c87e40c01e0f10807040e41c80500744128042c03840790244030550500d00d01d00198901e01c00e10380c0041c1c01000007813142d031201612031641d00201d80e0700001c070300c22a005004100080001c0d00c010521a1020392551030720301e1405e0700c4481301d44402428103483ea140e83c429542e603070700600c4010b100a0020411071090340466992030003d510039a00944401c4810324036401c00313042951080c01044089109a01e8540d412244600c00c5881651180014003103080140e6030a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 84687375 1250 84686125 84686131
    0x4050705040509011a030609042607030807020111030a0b04090f03091706090c040c020f0a0b0717160503040c0e090705040f0902010c1b05030f011a0d0305220e 70
    0x1948481d100ca042c40148148124107820141d40400c2c0300801c05e07001944041101d038850b00558408000303446500d4001b20860f0303000c00c000010045004101848103825010700085030280d03440c0a000c0d210a0000c0e0308070f407030158039405060070400008408000a40120141e000050030005040015032a00c861403036030b0a40031000203c0342001000381d500b103008103010304030701c500c05415941440446030340d562420360308140c091a11280c188010394000d1100940c0104d1000955425007480c0c136080180c1c0a04440344804111039031340d040e1040442d2240f1901c6860302112104042100388429980c580008008072191608072001198214041c2c0083d8081c4039041c0091000314141010002a1100404807039402751900d410000580c0e07002507c058081d40200e0088000c894010140d03c0c8070b507054102503010301c50700e04084064038055000c500140c100000c001d10780ea048130200002210802c00207000142e080c072608445110214890f580490740303084a18500d5600c441d1001c07000c80072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 84688625 1250 84687375 84687377
    0x1b0b0109020405180c18040f02070615120305030c030903040807090e0c01080727150c02031e030403060e031303030503040308100b040b070f02060c0a050705041a10020c040507 77
    0x802c1c20859400c0182d68200c02503104001c014a61a12619194a5000b0101d05140c09031400d542c4501c103071240d500070790040c402e503d02555180402c0c00d00c4005000c0401c1081ca914113002c10000782c0c83e1101000081b032036071568400b440c6481e140b084904640025000c41d0060200f00800180d48404020740c1e402018a0780000ca40c5444d42107a840c24441c00501e264140700d0f424081010041d8000b0491007403400048010141d045140407900203260150440640c0c448503840341b2240303a0300301d054041224400c508031840d91042009080e81c500c00e1a410306915030007400305000103800c07500008510050401140d0910098601021170046980e006801040c030020611040c942d025120b540d004d01c00d280040241031134002c554402d4441c500c82c0b007142140125a40e0304101c0311180d000b0510f80c00070301d026183c101ea40c0700705896140c100002c5505110f40c8600080710b081a000b0300380030340000d548124544101006112452601c0c0505034118005c91384c0003c826904c61045501443c3e003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 84689875 1250 84688625 84688627
    0x31006080601060206070f0e12010e010c230415120902190303080f010b0d090615140108090f0d0c02030c030a0c05040b01031503030c03051207030207060b090f071b0b010902 76
    0x94004080c2c02c28901400300c0041000040a4070002034006000c1c0714035800940c0c6032105400400005130051000cbe40b502e000381e5080c9608602c40355804090300c80103400521615010b401403444000052041c0e2180003603800035540c01c91100c0c6e004405504004403414000300f038100a9a0000f980c02402d40c01c1e84000082900051060560000e0305aa0025100312002c58650401e515400d05026600c0007403102e03900c0f940340008000094102c8c60b540f404207d101c0b80390f240ca03001980c0310a01490b09050009004000080515600141524038004800c0141803c010841c008944110ba1203500382c0e0948203401703060500d901d040000100160288c1201201182094200010354100100c228101800e103811410703015802d4048104603540b608050580040c0c518040e0f0301c41c0581c046103900c1d040740074204507070705805400903e42c072231040304208000300034403040001442c000e8840d4018481032400081e0b03424002c810b0b08091441e000041c0321134034000d0f0381c0c2c880452401d0f048141d00c290 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 84691125 1250 84689875 84689879
    0xc0c01140a0605120a06020a090801020f0c0f07061b1a0f040507060207060504091a18040218161218030e0307080d0f0302030c13090902090a0501080a030e031006080601 74
    0x5103440b44002810045400440c2d001d1002c1084d65168518a0090121540000d801030120700071030440e4010000b02c0000c1d9240c00d0040c894000940105408140500600c1c0710329407120f0300807411800350340c03243d02c80602c10700101da09014152110001248d0718004901c8a030080750241c45490304c030701c5428440c10002d04e02442c0072030030300c2019400102076601045052091036009020355050344c2d51500001450309c4844150808142c0325030219802c986c040d04a8220303000340343c80161189000780c40d0420750550022106140c0380007110b030b080f0f1000d1400c40c21040548680d4140800450030b04010581d007440e400030240224291404070f002c290100205c00c2241014042d0200600c5610090903031038000f282c01800170030001030100c040550000000c0c000100034000e442d40c0020b482400c2c02d8242d11401d07400018101c0610076481464240b001444101450003042c1c10794400c20081c10040c0c0d85543c0c240c0d200c151194400d5403501030207000313480858041c403c83d001002544000c0000b94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 84692375 1250 84691125 84691141
    0x130b030a09020406050319020d1704061205130218090a0c08010c081f15090f03032007050f0d08190503070f050406200f0d0305070207090605030a0305030c0c0114 71
    0x5004c1d54402402500258602c0d03014901c0385079009121501913440c1034260390640342c2510300c0c0101c21095480c0c044040760108050364040200354020360401d1082140d86c6480c07214010981d08141d000f54026041a620350203c8510f10242c1d41000814044804110f00346d9a0442c0c1d441c600e8110607000d031341d52001021650b60001700960010504d451000d80c01007808000c189002107405850880e668202d0701d05241889080001c00605564803107a5801d03849207001851042c007441c828802c1384d2008412543c800000c08c191040310001841c541031030070803030306001c01d03011100002c0d5203103242031003920500504640b404e21903100070b41d156035492800180c05082c200500c80702e40b08010080c002800140c0e0040c4213010b21350016072801e1010110a02000d00d481c2c0200600d0007075010303c40f0019802070701030300301a014180c1c1c0d4007034400140e2180090b60480304588607941c0d2560100142d03d0209009600440e0800d210040d000d01d004d112074150f0382520749100c10700c0c4102441d801002110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 84693625 1250 84692375 84692381
    0x9030e151e040e010b0901140a1d0603130303110405060d09020102060f0c03061c12030c08010602010e12030403020705030f0c01030506040902030a060515100c020a060905010c08130b030a090204 85
    0x7505041ea8200d0400781010940d81603120140200c91000100048460440e03007d406580d644441c1c68926965070f100d0980010300b07004214400b40100a002080c20b403031441c0c40310540c0d03c160801c9070702c150700003840e1b00c0440c081d001000c1007a0480303404200200d20b50300c1c0c000081c0303e0316100c507001040704070300c0340300080c41c1c024028201b003519029070741440000b024590442e80c12000072030340c07000304101d1480d50030070131144c200008003000d03640b200551110380c045c2c0003160074206586581e06540c1c2d940d10264282c1300c0341100b020068221035446902010342e1000317541c01c64042d104030381404d0b4540d40404d10f0315100ea508280a540300708001d0178950f0b03040c0200d41d808031090300e09002030b5889034042640d4080300c03240208a05d48800c000b403602c4007085500d214584004100034130508030742030007030607491042006a004080c242c0002c0389050046144a04481c4103964a0600880c65100e0881c0b0f5004940031016112106000245010303450010f1802145403240c000303a2040340c1d204005c22 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 84694875 1250 84693625 84693667
    0x408011a0a050a0909061404060b040c0806060d110705031c0e0a0209040f1103010507030c0332040317010f0618030203060601051309090b040312060b090409030e15 72
    0xc240c5540c0d40911443d2990348550b0100e82603000c0c04145c40c00d003840c0c210b0180101c407071002d02d540004000c0100b4000c054202c100303505030550301048000c444520072610400219032454220304100000017901c58181c2c088259240050f13000e60520105aa0380c0741142d014030980f10120600da4211040c40c01c0a1007a0904499818000c00c43e20080e0750101e0030302c06000b08068484500340c54000140304211a8441c455000200200b00515003120050000d044d40d86803080001d29040d4459101450300e900701d5000d0700c240107502c143c4044248a6102c1c0e0000904c101d082260340862074455020300e00cac0b024060045a40300300d81c500c0c01d2250050001c558404540b41d00c1401420820140c0c80100d045034001000f03103080c41c1e03515440f503025042507400b03501000e9201e2421103010300b405049041240500e1281c1d6400c3c29005d10120034409031030300c078042c2c00c6020604100b21142c514107640000c04040c403905100c20382d1844840018003d0f450f17003005821041c0000380030800c2600302580005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 84696125 1250 84694875 84694879
    0x31703061e0a150318050f1501030b06041113090501141e01080c070203070b0d060b0301081b010c0506070c02010f09140409050322030c05010512040204050a060b0408011a 75
    0x101200030480001e44030b44a0b0f20403488400022038001507464442d401004104d18003408a40e9000d050740b5116584111448200506018000000a0341c40070b84401c07070304a075005446821a511171004000041001c8560310a508004000c40c0845042da14200c0e0014854000002090340c9004032101d004011200b40912642c40e9850ac1005400c4402002c10340950038038084200341c0e035001080e81c05106100f400303036140c45405000036000c180917005140c2c88507042414400d1a03a20761003192580420b00416220741c0140d02614405000c403204c4a00c60300c0c0524040403c148292a0311f803d1910a540f40070001e099500c256083d544c100d8016010b403401817038100d10482c0761070618404444510f040d035104689543e220002c2c4034003002524161450080c14040c2d82c1c1003590403400340c41d000d02c0120303070800c1c040714009001e40c042c0040d00d110140e91402d02c03403a99180c0d0308000c0280401065941069682c0c500415030100c20700240c4040c10b100000000e040e140c4001c440f843e49007100e0424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 84697375 1250 84696125 84696169
    0x321020d0806010c060e030405042a020a0203060a110702040501090911010509030d080a060b0307050c0708061009050a09061113080d0f08040501020909100314011505120703170306 79
    0x2080e41d1344540e51200741c3da003000001072025069201281544184d0713002030350003410b0a4002440314100e01410204c0c140909540c482101301407000e036102c0038000c101a505400010000c0d452406a4000541c2c2c1b501034840b191030300010f0750005044860030707005201c41940d540e5004003040b142b11618405038009080c41802c01050b10000fa80d41c000f031102c507100b0000311401082241c1d016401107401380c10b00f45041d5449140440009000f0381001c44103007201d200741c80002400706004030308580210b441c40d0f620315200341000c51940107020301802001040e84d684101501081c890303c04d000380d6034529869165100491000003500c00700e00d8200b80704d039070072800aa804054101c030a1002c5410305041001a42c1d840f4144140203016002c491504040c000301007001e440b5451840400345c81c030640d01e1041090030072010301c0c01ca60480321442500c2c0e890000a000c41c3c81c001242c070642c0740d0380000312045641c49994280c145410312540080b0344070044240403042c98030701d03224140000d0741d040700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 84698625 1250 84697375 84697381
    0x306060303030c090305070918050f060415050906181011090a140609090423060f090f0a02060c0a05100203180d12020304021f11010c0c03050d050705040321020d08 72
    0x21b50f102d0710280308049125903140b00740103503600c944044010990b003100540344d90202450000da210b0b40f0131501203a08aa050700c00455414051180f01d02a05080b00140b48030307034402500300d09039145003800c0c1d5400d124526003c4080070aa010780d01d80d41e12549021602e0310051814004025110341042492445440c181c5449031a18800e6030b410f501d089801d541c80340c8850811080c0c0003110000450300a0048070075410030705000071611b00035550121254803a540d0000780780c0c1c403500707449090f0400360006054200585440c00250000310803407015210f55800c00d94800303150108120351414000c0d008010003145144814407202d02c00c00c0a07018191004421200030501402180800307030003903010022800355240c44c5000100d0310140000a40a9440284043e14540801d681c9a60560820b103100c1d042d144a14a03102c441541900c8a6081a403040e0781d12001d400000c1410302000006c3c072000002c01d40307000609000350b22400001400701e680700002400c00c18a505000e05102c021014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 84699875 1250 84698625 84698633
    0x5030d060503120702060d0903030b030d0f0e010f020d08060402041508011a04050102060403051c0f020306130c090e0405030c030403030906020106050109060e0405090a060e1005060a03020102120309030906040306060303030c0903 100
    0xc47d10350240030000050014100d24083d4000d12000341001c0d00b5204450050b400c0d40d8001c0c003030586085031900c0e580ca09412140c011200c03204003008401c0160004010310303c0103806004555003000300100050f0405454000c20245010b400750010000b5408500401030301000030b0314a0480225495203034078103810000040c1da142c1c0094002010008002032104101e6048241c3c0e0a80503400c440c03d0191306c507800d03401c030040e400a44404e4800c00f13a141042040c0942c0307214000f0b20265544800b041d85107043c2c1200020040148140c6590008008189984600344000e10145110351541c010701c5040420003401c6918a40082d030510142c00414000030390841c80c052100070007101c011a85544044000b0305042182200030800c0f07040074003e0040600c08076000d04902c02d0110208001c0d6600340070002108494400a07000d6006013101d002c614480100a50b8404d40040840f450f1581300e0006c5001a0b11a51054441c955628014001c16030305018840c0080070510b040b20246081d611 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 84701125 1250 84699875 84699877
    0x1f060303081603021207050307080604060e071409030a1209090209030705100c0203010c03020c010e06040f02040c020a08120a0e031e09041107080403020f03030310031205040305030d06050312070206 87
    0x1241140181c030804090050b244241c04451303180c449692550942d00b041d44010b04940c10580d1424003080071100040d00c24100303480b4000c100c0d040e44403036443c5900c5080040d1001c000c65910030304020300c01c000000d496202017141d138950354420340d10343c1c20110300100010040c0d51160482044140104070940c1c1030750380040c81400b600c1c01107078402500c41400b00306650900c0c8110000b5055420489840d240e543c02d640a0070600e00850024080901301c00c441ea601e801e4111002441c250003482880302604060f40b1001c1034030202d0040b100a11179a1710b5465190b000702e5450803805526000b00300f40d1040f94080c403540c204c040001541040b000303143ca0003008010140c000d10b40d8070041400c2c0c8144e519078003e090720044106203265141ea86007004103031644036010230b030300400f20a2507400c003500340002140e01c144001c1c5142c001ca01e08581d1803480892a04500d1810403805100102c00b003501400107000c6030384449400151146060700b03145c14001d0780707a030b8010b407100103019400c00340e22200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 84702375 1250 84701125 84701131
    0x1501060c0206090a090e16060c17032701020304120801060f0f140d020d110f040b0702030106050909030901020706021207080c1603030c0b0c0702151b0d021f06030308 73
    0x70b070059200c2d00d0420204d00700b00e0301d50b40420a114280890107189102c08551030401c00c0300588103d0b016031b06c0b20819600c540e040c50008040b0010421b5041d10040f07544007442e040018500410441d08a03110001201e0403c4078902603142d60000600042000c81d40c0e41542d0301c00103040000085d0b2610102500c3c29421513071107014064041521a442481118021905481022119106c501c000c40d00d4009402141003607000300d24128030b04100c00384441c00d0b21402450030104a01d01418089200f21a0304110012601036481e01404a203503942c02481d0b03846140c0260046445014440009281c504664042020354005101d201c0701c51601d07204845100c2c1c2c004054603560262070301500d2501c03420541d555003000c0003140200c10141d0182011001d640103250780945034586240c425050301c0f410304002d60044650041140b028000c4000d0082c0c100709040d4410390000c000038041c242511011001c0c01a00706461202084103495041d01c44040048801c1000e07a0031a41d0141240c1c600dd = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 84703625 1250 84702375 84702379
    0x10f0e011505070f0c0e16120b030c011b0204020f0309010b04110a030c11070806040302060c160f0501020915040501091d0601111204030803010906080a050a0611120c0301030201021501060c02 84
    0x13541c00b20510003c540784400406000c0c900320b00301d01d0900b0b0100d160380c0c1c106260800294405291644d404540d002e44141d01000401500444055000644805d801003645d0f2110340c03454210030025035280e10240184500c2d03044025602e18001d40740b42d00b1155140c0f51148618a4090600a06081d2100f921102039a509000410255040c41940c50801807200310040d071182d4580802e1000d008a0754a0195100f5001c64802d130b1640c01c1e00c42c1c2079000b1581c100f40307482d070148010008162080a10342c1d020340248001403a040003e40440c042600710b2424104082e0300090810465a210400c0c000804014818411140703c0044010454402034949810040c60401c2100c3c004000d1003030030300d19800452203594590b0b40e0310f41941c1d541c00911441091078603140f40020609400b0401030a0341c0d50090107401c112009030b0380e8500802e8158151803401030203005a0b00c40c43c02e4101054094039910251584944c95440020700d4080695100111000c903031004000168010520301006641 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 84704875 1250 84703625 84703643
    0x717040c1e0302030a060c020c0d1110030605030d0e090702010603020f060903070b0706050a050610200f0709020301090501050411042115090b0a06140f03070b03010f0e01150507 78
    0x101d454a80d4070032180c002035810700580003844c042024a603c03072001600544c017031384d101c0380e4088100f141d105000a03029269034030f208000c41c0790340351a0740c82e07281156180c1030000e0a1303a252804246024804900400481c01e0480c981069241c5a240302e5440056440244801421a804191900190400b0354090780707001c51504026a000d21840000e00800e000e01a15403055013050b002814042d50710443c05880e10003c5025814600340c1078041104603203480b0310784070030804143d42e807010314583c1050038010490421000740060103003d0003010600c00242c0c4950600340804119481a84850302c21840c0c81e10207914000390409032000c5602601d010810020184200c80d0410001140108207014900c0700881600c0b25034421202d29005080c17160550340c440c443c1c00c040380c00e2802086103200c0c01618800072131804500c1e0300482d40000d015140902da40301c00040040d0401c3c0c0280b40d0004e2440c4007400f010b00d0f6000c46500401d02010090000840584040e00612034054040c00001e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 84706125 1250 84704875 84704909
    0x60608330d11090408030f0f0103020105070206070f0b090109060609020a021c05070c03060e0606040b010905041d060403050405030607090b1c090b10081002030906070806030f060703050717040c 85
    0x18070003240c0382d0400c06070074641c080c605490f0254240d4030482d20b080c134280f406030202e810048900c000a068039810f8444a1905d070054080183c20b400401d8102c8018800101c2c620014420840650007019180008180403007246015002d480c6990065040548144403105801d03500181c2c1c804080346660307058001c10f8459004607020300c03407803102611006a56100104014099001903004000d80c0c040c2d58540d150311003000127a542c65011a40015074091044c00103103059409804401c00344031645001c880304109580c02c0110449090300890400b180402007801c040c440c299014020785401c4580f603003400c2075266180107a0ba2400074102e0300180c000000f070f07000c3c4e102c00e02440c0c00c82c1c24034449142262000340651102e005010f42d46c024600c41d08200003480c003d4034010351100000c1d00555591010841b01c000c402060719030725100d01507803090b0b075427414482a40280c4031b42d503011070b0a240903400074020780301d0003007000c05d4014640204800b2419205421003034030100e8046005141c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 84707375 1250 84706125 84706133
    0x307020103052502030a0f05160b0c070506041203060509070801031101050d0207060e07060c020315090111070609022716050c0d03050609090102030f011413060608330d 74
    0x2000d180500c8050300740c10f2201610f42d40e00000074203107043c40c0e5950103144072107428044809014588250a0301c0400362480380010300300780e2105902400b650a01c0d424a01c00e40c445501e0300d40306940640d152400ca502c1c032071000e9854003450025041c1507480b00220304201c540101a01d105110240c42e480510b400c2d141103a104408645440c00040c40035500c40c280c90908000070000c4d0040c01c4054400c04400040141c000d0314201d110b80c1c1c0007406400e05021014440d00901030080080c07116540e14444a070b07a20030301101034180503005510028814480348148154807950141e045445003020703843c070146100c558001c613400300c544034460300c071810249001d450341d00401a1000050203045451990668582e00c030a10440c0112119000c41d240c0b0303031240d0f08038032050318150800050180140540640d0341c03c0311010410152140001c180b891540c5012541c050b042000001e868500b401b1140f11100046458000d035250b0100c94004000041040003101421003401070802c28a640c040c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 84708625 1250 84707375 84707401
    0x807030c052e0f0506010507080904090609050703110303130524041e050d080a0f0509040f1b0f020c0f030a0803090f1e030901120b040e100b090603030702010305 71
    0x4240780d442c46511000484088442c00c0a50b49800e1a428035110b0b40007100c40c410b0003224011207060710340304d1400700c06803501d810780d60001d2001034105460f085010f000078031500c03400300b0003409040a04142d90440c80c040c9162246e49143c0c1e4480d0b0305c240581030003881c2605032203040742c8046804611500f005040c20b205503900c4048500d6a07980840d0026800703031509115400c000007a10026017040d240d604100f40000440ca01400c83e41c0c0038070549602d40d01591420210b81c482d42491401c0031007500004096400704a1a0010300740c644c10000303a0034240c0f0380320441440207030400d11468112060000c0d038903907100c480c26218404012102a03951010310003001166007021406a032843d10403043e40e40d074010300b21030304024030030520034580740050310090429808026003d0f41c9451a10f0004540350f4025692440300700d503582d11890500c0e92680b280382800c0780034070050b11006455031202c1d81180c0240112500807e40241080b105503008001c4a00c1c90754242400140d58035550a4030300c00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 84709875 1250 84708625 84708643
    0x30030806040906180507050a05060c030d0c12090303020a030506091608060402280212040b0d0b042406120e06010312230304020a090c08130302032703010e0102070807030c05 76
    0x701000ba20741024080041041c506a4905a171080c42c2150741d400ae0001c03511401d2a8401260000e009042105c0c03641d030004200d90035103141c65550715030395a0103a0704076000410200c004c00c0c2d00245141c0f509400d802a02d030310a008640000c07003880d100c00d140886080324500403081202da000000c905580e264180c0d000f9215110100c6480d00115148034101c400e9a07070000d015119080626078146800022202a544c0180c030481c01c19000320780aa028104510000754010f447d442042e0b12043c1e40040d1420f4070301c0e102d40c9251a039107043c0c0c018280c01039010280d1001d504010400b09907010000f81c6a045a074807814400d102601c146080300c01c01003807842c076285040b0451840d8030340390380900910f00840c000c039503500ca4980d980c1100d50856104c40078035008219030f4070005240a08502c00d03218803038028019245415041d00e9582468081705440e40d10501180421510908091041003181d500120085140c64200d448440a9016450004040016030074481041000c10310131404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 84711125 1250 84709875 84709901
    0x1005040203071a030a0b06031e04080720010305060f1c0804050603070f0807020a0b13051f15080105060a0b0705030c0102030703020702010807080f01121103060130030806040906 78
    0x148102c0f811810760b0a039100fa00c11001c000d0801c0700c1c2c2421440c106049038090007003400d08500300c40c41c1000b1214000780c01001036800c0c00f001c1c040d01002c40e04041001002c1001000c00d0880d0141c128005400c45002802450040c0c548845a403226102c00203680340d00c000d500b6516006c2d003c10b15020b60780c0e01c99500856000320004c014050a40c0d000840d10440a0150f00c40c000700b50345070201240d91300e03e1481c000e800c174080c04020232507120a40300317040c0d051800b40003591032001e05e582040e03541030041011480146d03030301c24188420803003240c014005440303603000078801c41c00e2141c0040d1021551340142415108006848001c104003001100c0b502005100295160326111380082c0003508801002c4c4d01180f040b8001410192092499901c640042001003400b83d080262856440c5125070084464904801e030103c100d6808200181c000c00740000d10328955500b651282c0200c5822600d1000c0710007551000200181d00300800940c411f00580c0c000400007440e003011070142420f001049 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 84712231 1106 84711125 84711149
    0x8240c030f07030e062706190b0604080109030807030b120607030203070e1f030608060c030c0a0e090a150b1804021e13030308070e0102100504020307 66
    0x350300000649400222040c01c4130b0028a007100c2510030346c0070802e44603040e01c031001c1c0d08400340c01810405806008141080030f0300c1881c0000ca001c40500d1785455103107150700b50300e0361402d55005040301c0b002440003907418203018014001c10f41f08440001d00f0920005550300707142d081c403400141c907440141025a1040000c90094001511440c10407070a50907031845031369001c1c0c1c0c0c0310301c141c4814082072801500c428043d040b1001640304114640207071040002e8a00c3d402c0030f580d8005500421700d581da900102048414442e0103041c940d100c9046014016503003078503803100310b0341c50003249c25824031901d88900384074600648400c480d100c00600b442a0190420f5000b40c404140c1d080c5401c00c0608052103500101e802640310080d41c00340d4003004105041c0c0c84070850390484141c3c240142000000320000b5150101c032400c05a80940701c2001c5400c5490401c5008018060036443c0c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 84532375 84712231 := by
  have h0 := BRFrame.cov_init 84532375
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84532375 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 84532375 ≤ n) (h2 : n < 84712231) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
