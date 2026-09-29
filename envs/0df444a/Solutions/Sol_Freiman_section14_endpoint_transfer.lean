-- Prove2me | solution 1 for Freiman.section14_endpoint_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T10:00:19.838946+00:00
-- url     : https://prove2.me/submissions/a28a456a-78a3-40d7-882d-647da696d1d6

import Definitions.Def_Freiman_section14Geometry
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

open Freiman

namespace LowerDev

set_option linter.unusedSimpArgs false

/-- The part of `lowerHistorySuffixContext` that the endpoint development actually uses:
the catalogue word and the real word agree on the two terminal-run tests. -/
def sufCtx (w ctx : List ℕ+) : Prop :=
  (lowerEnds w [3] ↔ lowerEnds ctx [3]) ∧ (lowerEnds w [3,1] ↔ lowerEnds ctx [3,1])

/-- Weakened context-fitting predicate (same as `lowerHistoryContextFits` but using `sufCtx`). -/
def ctxFits (base : LowerPair) (C : LowerHistoryContext) : Prop :=
  sufCtx base.1 C.words.1 ∧ sufCtx base.2 C.words.2 ∧
  (decide (base.1.length % 2 = 1)).xor C.parity.1 =
    (decide (base.2.length % 2 = 1)).xor C.parity.2


/-! ### Square roots -/

local notation "s3" => Real.sqrt (3:ℝ)
local notation "s7" => Real.sqrt (7:ℝ)

lemma s3_sq : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma s7_sq : s7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
lemma s21_eq : Real.sqrt 21 = s3 * s7 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]; norm_num
lemma s3_pos : 0 < s3 := Real.sqrt_pos.mpr (by norm_num)
lemma s7_pos : 0 < s7 := Real.sqrt_pos.mpr (by norm_num)

lemma not_isSquare_of (n : ℕ) (h : ∀ r ≤ n, r * r ≠ n) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by nlinarith
  exact h r hle hr.symm

lemma irr3 : Irrational s3 := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 3 (by decide))
  simpa using this
lemma irr7 : Irrational s7 := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 7 (by decide))
  simpa using this
lemma irr21 : Irrational (Real.sqrt 21) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 21 (by decide))
  simpa using this

/-! ### Values of certificate field elements -/

lemma val_eq (z : CertField) :
    certFieldVal z = ((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3) := by
  unfold certFieldVal; rw [s21_eq]; ring

lemma val_add (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]; push_cast; ring
lemma val_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]; push_cast; ring
lemma val_scale (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q:ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]; push_cast; ring
lemma val_neg (x : CertField) : certFieldVal (lowerHistoryNeg x) = - certFieldVal x := by
  unfold lowerHistoryNeg; rw [val_scale]; push_cast; ring
lemma val_rat (q : ℚ) : certFieldVal (lowerHistoryRat q) = q := by
  simp [certFieldVal, lowerHistoryRat]
lemma val_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  simp only [certFieldVal, certFieldMul]; push_cast; rw [s21_eq]
  have h3 := s3_sq
  have h7 := s7_sq
  linear_combination (-(x.b*y.b + x.d*y.d*s7^2 + (x.b*y.d + x.d*y.b)*s7)) * h3
    + (-(x.c*y.c + 3*x.d*y.d + (x.c*y.d + x.d*y.c)*s3)) * h7

/-! ### Linear independence -/

lemma indep3 (a b : ℚ) (h : (a:ℝ) + b * s3 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irr3
    refine ⟨-a/b, ?_⟩
    have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    field_simp
    linarith

lemma sq_eq_three (u v : ℚ) (h : u^2 = 3 * v^2) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp at h
    exact ⟨h, rfl⟩
  · exfalso
    apply irr3
    refine ⟨|u/v|, ?_⟩
    have hv' : (v:ℝ) ≠ 0 := by exact_mod_cast hv
    have h' : ((u:ℝ)/v)^2 = 3 := by
      rw [div_pow]; rw [div_eq_iff (pow_ne_zero 2 hv')]; exact_mod_cast h
    push_cast
    rw [← h', Real.sqrt_sq_eq_abs]

lemma sq_ne_seven (e f : ℚ) (h : ((e:ℝ) + f * s3)^2 = 7) : False := by
  have h3 := s3_sq
  have h1 : ((e^2 + 3*f^2 - 7 : ℚ) : ℝ) + ((2*e*f : ℚ) : ℝ) * s3 = 0 := by
    push_cast; linear_combination h - (f^2) * h3
  obtain ⟨h1a, h1b⟩ := indep3 _ _ h1
  have hef : e * f = 0 := by linarith
  rcases mul_eq_zero.mp hef with he | hf
  · subst he
    have hf' : (3:ℝ)*(f:ℝ)^2 = 7 := by exact_mod_cast (by linarith : (3:ℚ)*f^2 = 7)
    have hf2 : ((3:ℝ)*f)^2 = 21 := by linear_combination 3 * hf'
    apply irr21
    refine ⟨|3*f|, ?_⟩
    push_cast
    rw [show (21:ℝ) = ((3:ℝ)*f)^2 from hf2.symm, Real.sqrt_sq_eq_abs]
  · subst hf
    have he2 : (e:ℝ)^2 = 7 := by exact_mod_cast (by linarith : e^2 = 7)
    apply irr7
    refine ⟨|e|, ?_⟩
    push_cast
    rw [show (7:ℝ) = (e:ℝ)^2 from he2.symm, Real.sqrt_sq_eq_abs]

/-- The rational norm used by `lowerHistoryInv`. -/
def normQ (z : CertField) : ℚ :=
  (z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2)^2 - 3*(2*z.a*z.b - 14*z.c*z.d)^2

lemma conj_identity (z : CertField) :
    (((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3)) *
      (((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3)) =
    ((z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 : ℚ) : ℝ) + ((2*z.a*z.b - 14*z.c*z.d : ℚ) : ℝ) * s3 := by
  push_cast
  have h3 := s3_sq
  have h7 := s7_sq
  linear_combination ((z.b:ℝ)^2 - 7*(z.d:ℝ)^2) * h3 + (-((z.c:ℝ) + z.d*s3)^2) * h7

lemma normQ_ne_zero (z : CertField) (hz : certFieldVal z ≠ 0) : normQ z ≠ 0 := by
  intro hN
  unfold normQ at hN
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  have huv : u = 0 ∧ v = 0 := sq_eq_three u v (by linarith)
  have hc := conj_identity z
  rw [← hu, ← hv, huv.1, huv.2] at hc
  simp only [Rat.cast_zero, zero_mul, add_zero] at hc
  set X : ℝ := (z.a:ℝ) + z.b * s3 with hX
  set Y : ℝ := (z.c:ℝ) + z.d * s3 with hY
  have hXY : X^2 = 7 * Y^2 := by
    have h7 := s7_sq
    linear_combination hc + (Y^2) * h7
  by_cases hY0 : Y = 0
  · have hcd := indep3 z.c z.d hY0
    have hX0 : X = 0 := by
      have : X^2 = 0 := by rw [hXY, hY0]; ring
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hab := indep3 z.a z.b hX0
    apply hz
    rw [val_eq, ← hX, ← hY, hX0, hY0]; ring
  · have hcd : z.c^2 - 3*z.d^2 ≠ 0 := by
      intro h0
      have := sq_eq_three z.c z.d (by linarith)
      apply hY0
      rw [hY, this.1, this.2]; simp
    set e : ℚ := (z.a*z.c - 3*z.b*z.d)/(z.c^2 - 3*z.d^2) with he
    set f : ℚ := (z.b*z.c - z.a*z.d)/(z.c^2 - 3*z.d^2) with hf
    have hcd' : ((z.c:ℝ)^2 - 3*z.d^2) ≠ 0 := by exact_mod_cast hcd
    have key0 : (((z.a*z.c - 3*z.b*z.d : ℚ):ℝ) + ((z.b*z.c - z.a*z.d : ℚ):ℝ) * s3) * Y
        = X * ((z.c:ℝ)^2 - 3*z.d^2) := by
      rw [hX, hY]; push_cast
      have h3 := s3_sq
      linear_combination ((z.b:ℝ)*z.c*z.d - z.a*(z.d:ℝ)^2) * h3
    have hef : ((e:ℝ) + f * s3) = (((z.a*z.c - 3*z.b*z.d : ℚ):ℝ) + ((z.b*z.c - z.a*z.d : ℚ):ℝ) * s3) /
        ((z.c:ℝ)^2 - 3*z.d^2) := by
      rw [he, hf]; push_cast; field_simp
    have key : ((e:ℝ) + f * s3) * Y = X := by
      rw [hef, div_mul_eq_mul_div, key0, mul_div_assoc, div_self hcd', mul_one]
    have h7 : ((e:ℝ) + f * s3)^2 = 7 := by
      have hY2 : Y^2 ≠ 0 := pow_ne_zero 2 hY0
      have : ((e:ℝ) + f * s3)^2 * Y^2 = 7 * Y^2 := by
        rw [← mul_pow, key, hXY]
      exact mul_right_cancel₀ hY2 this
    exact sq_ne_seven e f h7

/-! ### Inverse -/

lemma inv_correct (z : CertField) (hz : certFieldVal z ≠ 0) :
    certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹ := by
  have hN := normQ_ne_zero z hz
  unfold normQ at hN
  apply eq_inv_of_mul_eq_one_right
  unfold lowerHistoryInv
  rw [val_scale, val_mul]
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  have hc := conj_identity z
  rw [← hu, ← hv] at hc
  have h1 : certFieldVal ⟨z.a,z.b,-z.c,-z.d⟩ = ((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3) := by
    rw [val_eq]; push_cast; ring
  have h2 : certFieldVal ⟨u,-v,0,0⟩ = (u:ℝ) - v * s3 := by
    rw [val_eq]; push_cast; ring
  have h3 := s3_sq
  have hN' : ((u^2 - 3*v^2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [h1, h2, val_eq]
  calc (((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3)) *
        (((1 / (u^2 - 3*v^2) : ℚ) : ℝ) *
          ((((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3)) * ((u:ℝ) - v * s3)))
      = ((1 / (u^2 - 3*v^2) : ℚ) : ℝ) * (((u:ℝ) + v * s3) * ((u:ℝ) - v * s3)) := by
        rw [← hc]; ring
    _ = ((1 / (u^2 - 3*v^2) : ℚ) : ℝ) * ((u^2 - 3*v^2 : ℚ) : ℝ) := by
        congr 1; push_cast; linear_combination (-(v:ℝ)^2) * h3
    _ = 1 := by
        rw [Rat.cast_div, Rat.cast_one, one_div, inv_mul_cancel₀ hN']

lemma div_correct (x y : CertField) (hy : certFieldVal y ≠ 0) :
    certFieldVal (lowerHistoryDiv x y) = certFieldVal x / certFieldVal y := by
  unfold lowerHistoryDiv
  rw [val_mul, inv_correct y hy, div_eq_mul_inv]

/-! ### Signs -/

lemma ratSign_spec (q : ℚ) :
    (0 < lowerHistoryRatSign q → 0 < q) ∧ (lowerHistoryRatSign q < 0 → q < 0) ∧
    (lowerHistoryRatSign q = 0 → q = 0) := by
  unfold lowerHistoryRatSign
  split_ifs with h1 h2 <;> norm_num <;> linarith

lemma quadSign_spec (a b : ℚ) :
    (0 < lowerHistoryQuadSign a b 3 → 0 < (a:ℝ) + b * s3) ∧
    (lowerHistoryQuadSign a b 3 < 0 → (a:ℝ) + b * s3 < 0) ∧
    (lowerHistoryQuadSign a b 3 = 0 → (a:ℝ) + b * s3 = 0) := by
  have hs := s3_pos
  have h3 := s3_sq
  have key : ((a:ℝ) + b * s3) * ((a:ℝ) - b * s3) = ((a^2 - 3*b^2 : ℚ) : ℝ) := by
    push_cast; linear_combination (-(b:ℝ)^2) * h3
  unfold lowerHistoryQuadSign
  simp only [Nat.cast_ofNat]
  split_ifs with ha hb ha' hb' hb''
  · -- a = 0
    subst ha
    obtain ⟨p1, p2, p3⟩ := ratSign_spec b
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hb1 : (0:ℝ) < (b:ℝ) := by exact_mod_cast p1 h
      push_cast; nlinarith [mul_pos hb1 hs]
    · have hb1 : (b:ℝ) < 0 := by exact_mod_cast p2 h
      push_cast; nlinarith [mul_pos (neg_pos.mpr hb1) hs]
    · have := p3 h; subst this; simp
  · -- b = 0
    subst hb
    obtain ⟨p1, p2, p3⟩ := ratSign_spec a
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p1 h; push_cast; simpa using this
    · have := p2 h; push_cast; simpa using this
    · have := p3 h; subst this; simp
  · -- 0 < a, 0 < b
    have ha1 : (0:ℝ) < a := by exact_mod_cast ha'
    have hb1 : (0:ℝ) < b := by exact_mod_cast hb'
    refine ⟨fun _ => by positivity, fun h => by norm_num at h, fun h => by norm_num at h⟩
  · -- 0 < a, b < 0
    have ha1 : (0:ℝ) < a := by exact_mod_cast ha'
    have hb1 : (b:ℝ) < 0 := by
      have : b < 0 := lt_of_le_of_ne (not_lt.mp hb') hb
      exact_mod_cast this
    have hpos : 0 < (a:ℝ) - b * s3 := by nlinarith
    obtain ⟨p1, p2, p3⟩ := ratSign_spec (a^2 - 3*b^2)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p1 h
      have h' : (0:ℝ) < ((a^2 - 3*b^2 : ℚ) : ℝ) := by exact_mod_cast this
      rw [← key] at h'
      exact pos_of_mul_pos_left h' hpos.le
    · have := p2 h
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) < 0 := by exact_mod_cast this
      rw [← key] at h'
      exact neg_of_mul_neg_left h' hpos.le
    · have := p3 h
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) = 0 := by exact_mod_cast this
      rw [← key] at h'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hpos.ne'
  · -- a < 0, b < 0
    have ha1 : (a:ℝ) < 0 := by
      have : a < 0 := lt_of_le_of_ne (not_lt.mp ha') ha
      exact_mod_cast this
    have hb1 : (b:ℝ) < 0 := by exact_mod_cast hb''
    refine ⟨fun h => by norm_num at h, fun _ => by nlinarith, fun h => by norm_num at h⟩
  · -- a < 0, 0 < b
    have ha1 : (a:ℝ) < 0 := by
      have : a < 0 := lt_of_le_of_ne (not_lt.mp ha') ha
      exact_mod_cast this
    have hb1 : (0:ℝ) < b := by
      have : 0 < b := lt_of_le_of_ne (not_lt.mp hb'') (Ne.symm hb)
      exact_mod_cast this
    have hneg : (a:ℝ) - b * s3 < 0 := by nlinarith
    obtain ⟨p1, p2, p3⟩ := ratSign_spec (a^2 - 3*b^2)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p2 (by linarith)
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) < 0 := by exact_mod_cast this
      rw [← key] at h'
      exact pos_of_mul_neg_left h' hneg.le
    · have := p1 (by linarith)
      have h' : (0:ℝ) < ((a^2 - 3*b^2 : ℚ) : ℝ) := by exact_mod_cast this
      rw [← key] at h'
      exact neg_of_mul_pos_left h' hneg.le
    · have := p3 (by linarith)
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) = 0 := by exact_mod_cast this
      rw [← key] at h'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hneg.ne

lemma sign_spec (z : CertField) :
    (0 < lowerHistorySign z → 0 < certFieldVal z) ∧
    (lowerHistorySign z < 0 → certFieldVal z < 0) ∧
    (lowerHistorySign z = 0 → certFieldVal z = 0) := by
  have hs7 := s7_pos
  have hc := conj_identity z
  rw [val_eq]
  set X : ℝ := (z.a:ℝ) + z.b * s3 with hX
  set Y : ℝ := (z.c:ℝ) + z.d * s3 with hY
  obtain ⟨x1, x2, x3⟩ := quadSign_spec z.a z.b
  obtain ⟨y1, y2, y3⟩ := quadSign_spec z.c z.d
  rw [← hX] at x1 x2 x3
  rw [← hY] at y1 y2 y3
  unfold lowerHistorySign
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  obtain ⟨w1, w2, w3⟩ := quadSign_spec u v
  dsimp only
  split_ifs with hx0 hy0 hxp hyp hyn
  · -- X = 0
    have hX0 := x3 hx0
    rw [hX0, zero_add]
    refine ⟨fun h => by have := y1 h; positivity, fun h => ?_, fun h => ?_⟩
    · have := y2 h; nlinarith
    · have := y3 h; rw [this]; ring
  · -- Y = 0
    have hY0 := y3 hy0
    rw [hY0, mul_zero, add_zero]
    exact ⟨x1, x2, x3⟩
  · -- X > 0, Y > 0
    have := x1 hxp
    have := y1 hyp
    refine ⟨fun _ => by positivity, fun h => by norm_num at h, fun h => by norm_num at h⟩
  · -- X > 0, Y < 0
    have hXp := x1 hxp
    have hYn : Y < 0 := y2 (lt_of_le_of_ne (not_lt.mp hyp) hy0)
    have hpos : 0 < X - s7 * Y := by nlinarith
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := w1 h; rw [← hc] at this; exact pos_of_mul_pos_left this hpos.le
    · have := w2 h; rw [← hc] at this; exact neg_of_mul_neg_left this hpos.le
    · have := w3 h; rw [← hc] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hpos.ne'
  · -- X < 0, Y < 0
    have hXn : X < 0 := x2 (lt_of_le_of_ne (not_lt.mp hxp) hx0)
    have hYn := y2 hyn
    refine ⟨fun h => by norm_num at h, fun _ => by nlinarith, fun h => by norm_num at h⟩
  · -- X < 0, Y > 0
    have hXn : X < 0 := x2 (lt_of_le_of_ne (not_lt.mp hxp) hx0)
    have hYp : 0 < Y := y1 (lt_of_le_of_ne (not_lt.mp hyn) (Ne.symm hy0))
    have hneg : X - s7 * Y < 0 := by nlinarith
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := w2 (by linarith); rw [← hc] at this; exact pos_of_mul_neg_left this hneg.le
    · have := w1 (by linarith); rw [← hc] at this; exact neg_of_mul_pos_left this hneg.le
    · have := w3 (by linarith); rw [← hc] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hneg.ne

lemma sign_nonneg_of (z : CertField) (h : 0 ≤ lowerHistorySign z) : 0 ≤ certFieldVal z := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt ((sign_spec z).1 h')
  · exact le_of_eq ((sign_spec z).2.2 h'.symm).symm
lemma sign_nonpos_of (z : CertField) (h : lowerHistorySign z ≤ 0) : certFieldVal z ≤ 0 := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt ((sign_spec z).2.1 h')
  · exact le_of_eq ((sign_spec z).2.2 h')

lemma abs_correct (z : CertField) : certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · rw [val_neg, abs_of_neg ((sign_spec z).2.1 h)]
  · rw [abs_of_nonneg (sign_nonneg_of z (not_lt.mp h))]

/-! ### Möbius evaluation -/

lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

lemma pe_single (a : ℕ+) (x : ℝ) : prefixEval [a] x = 1 / (((a:ℕ):ℝ) + x) := rfl

lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

lemma pe_unit (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1/(((a:ℕ):ℝ)+prefixEval w x) ∧ 1/(((a:ℕ):ℝ)+prefixEval w x) ≤ 1
    have hpos : 0 < ((a:ℕ):ℝ)+prefixEval w x := by linarith [ih.1]
    constructor
    · exact le_of_lt (div_pos (by norm_num) hpos)
    · apply (div_le_iff₀ hpos).2
      linarith [ih.1]

def stepM (m : (ℕ × ℕ) × (ℕ × ℕ)) (a : ℕ+) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((m.1.2, m.1.1 + (a:ℕ) * m.1.2), (m.2.2, m.2.1 + (a:ℕ) * m.2.2))

lemma matrix_append (w : List ℕ+) (a : ℕ+) :
    lowerHistoryMatrix (w ++ [a]) = stepM (lowerHistoryMatrix w) a := by
  simp [lowerHistoryMatrix, List.foldl_append, stepM]

lemma matrix_nil : lowerHistoryMatrix [] = ((1,0),(0,1)) := rfl

lemma matrix_pos (w : List ℕ+) : 1 ≤ (lowerHistoryMatrix w).2.2 := by
  induction w using List.reverseRecOn with
  | nil => simp [matrix_nil]
  | append_singleton w a ih =>
    rw [matrix_append]
    simp only [stepM]
    have ha : 1 ≤ (a:ℕ) := a.pos
    nlinarith

lemma mobius (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    prefixEval w x =
      (((lowerHistoryMatrix w).1.1 : ℝ) * x + (lowerHistoryMatrix w).1.2) /
      (((lowerHistoryMatrix w).2.1 : ℝ) * x + (lowerHistoryMatrix w).2.2) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [matrix_nil, prefixEval]
  | append_singleton w a ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hm := matrix_pos w
    have hm' : (1:ℝ) ≤ ((lowerHistoryMatrix w).2.2 : ℝ) := by exact_mod_cast hm
    have hden : 0 < ((lowerHistoryMatrix w).2.1 : ℝ) * (1 / (((a:ℕ):ℝ) + x)) + (lowerHistoryMatrix w).2.2 := by
      positivity
    rw [pe_append, pe_single, ih _ hx', matrix_append]
    simp only [stepM]
    push_cast
    field_simp
    ring

lemma cf_correct (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  have hm := matrix_pos w
  have hm' : (1:ℝ) ≤ ((lowerHistoryMatrix w).2.2 : ℝ) := by exact_mod_cast hm
  have hden : ((lowerHistoryMatrix w).2.1 : ℝ) * certFieldVal z + (lowerHistoryMatrix w).2.2 ≠ 0 := by
    positivity
  unfold lowerHistoryCF
  rw [div_correct, val_add, val_add, val_scale, val_scale, val_rat, val_rat, mobius w _ hz]
  · push_cast; rfl
  · rw [val_add, val_scale, val_rat]; push_cast; exact hden

lemma val_alpha : certFieldVal lowerHistoryAlpha = lowerAlpha := by
  norm_num [certFieldVal, lowerHistoryAlpha, lowerAlpha]; ring
lemma val_beta : certFieldVal lowerHistoryBeta = lowerBeta := by
  norm_num [certFieldVal, lowerHistoryBeta, lowerBeta]; ring
lemma val_tau : certFieldVal lowerHistoryTau = lowerTau := by
  norm_num [certFieldVal, lowerHistoryTau, lowerTau]; ring

lemma ab_unit : lowerAlpha ∈ Set.Icc (0:ℝ) 1 ∧ lowerBeta ∈ Set.Icc (0:ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerAlpha, lowerBeta]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
lemma rho_unit : lowerTau ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerTau]
  exact ⟨by linarith, by linarith⟩

/-! ### Continuants and the signed difference identity -/

/-- real-valued continuants of `lowerCD`. -/
noncomputable def rCD (w : List ℕ+) : ℝ × ℝ := (((lowerCD w).1 : ℝ), ((lowerCD w).2 : ℝ))

lemma lowerCD_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

lemma cd_append (w : List ℕ+) (a : ℕ+) :
    rCD (w ++ [a]) = ((rCD w).2, (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2) := by
  simp only [rCD, lowerCD_append]; push_cast; rfl

lemma cd_nil : rCD [] = (0, 1) := by simp [rCD, lowerCD]

lemma ratio_eq (w : List ℕ+) : lowerRatio w = (rCD w).1 / (rCD w).2 := rfl

lemma cd_pos (w : List ℕ+) : 0 ≤ (rCD w).1 ∧ 0 < (rCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cd_nil]; norm_num
  | append_singleton w a ih =>
    rw [cd_append]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

lemma param_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w :=
  div_nonneg (cd_pos w).1 (cd_pos w).2.le

/-- `(-1)^{|w|}` written with an `if`. -/
noncomputable def sgnOf (w : List ℕ+) : ℝ := if w.length % 2 = 0 then 1 else -1

lemma sgnOf_append (w : List ℕ+) (a : ℕ+) : sgnOf (w ++ [a]) = - sgnOf w := by
  unfold sgnOf
  have hl : (w ++ [a]).length = w.length + 1 := by simp
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · rw [if_neg (by omega : ¬ (w.length + 1) % 2 = 0), if_pos h]; try norm_num
  · rw [if_pos (by omega : (w.length + 1) % 2 = 0), if_neg (by omega : ¬ w.length % 2 = 0)]; try norm_num

lemma sgnOf_sq (w : List ℕ+) : sgnOf w * sgnOf w = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma pe_diff_raw (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) / (((rCD w).2 + (rCD w).1 * x) * ((rCD w).2 + (rCD w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cd_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cd_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hay : 0 < ((a:ℕ):ℝ) + y := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : 0 ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * x := by positivity
    have hdy' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cd_append, sgnOf_append]
    simp only
    field_simp
    try ring

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) /
        ((rCD w).2 ^ 2 * (1 + lowerRatio w * x) * (1 + lowerRatio w * y)) := by
  rw [pe_diff_raw w x y hx hy]
  obtain ⟨hc, hd⟩ := cd_pos w
  congr 1
  rw [ratio_eq]
  field_simp
  try ring

lemma width_eq (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  unfold lowerWidth
  rw [pe_diff w _ _ hb.1 ha.1]
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerBeta) * (1 + lowerRatio w * lowerAlpha) := by
    have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
    have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
    positivity
  rw [abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul, abs_of_pos (sub_pos.mpr hab)]
  ring

lemma width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  rw [width_eq]
  have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
  have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
  apply div_pos (sub_pos.mpr hab)
  positivity

lemma width_append (w v : List ℕ+) : lowerWidth (w ++ v) =
    lowerWidth v / ((rCD w).2 ^ 2 *
      (1 + lowerRatio w * prefixEval v lowerAlpha) *
      (1 + lowerRatio w * prefixEval v lowerBeta)) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have ha := (pe_unit v lowerAlpha hA).1
  have hb := (pe_unit v lowerBeta hB).1
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * prefixEval v lowerBeta) *
      (1 + lowerRatio w * prefixEval v lowerAlpha) := by
    have : 0 ≤ lowerRatio w * prefixEval v lowerAlpha := mul_nonneg hp ha
    have : 0 ≤ lowerRatio w * prefixEval v lowerBeta := mul_nonneg hp hb
    positivity
  unfold lowerWidth
  rw [pe_append, pe_append, pe_diff w _ _ hb ha, abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul]
  ring

/-! ### Threshold values -/

lemma threshold_value (a x y : CertField) (u v : CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold a (x,y) (u,v)) r s =
      certFieldVal a * ((1+s*certFieldVal u)*(1+s*certFieldVal v)) /
        ((1+r*certFieldVal x)*(1+r*certFieldVal y)) := by
  unfold lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

lemma scale_value (t : ℚ) (h : CertThreshold) (r s : ℝ) :
    certThresholdVal (lowerHistoryScaleThreshold t h) r s = (t:ℝ)*certThresholdVal h r s := by
  simp only [lowerHistoryScaleThreshold, certThresholdVal, certThresholdNum, certThresholdDen,
    certFieldScale, certFieldVal]
  push_cast
  ring

lemma complement_holds (b : CertBound) (p s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) p s q ↔ ¬ certBoundHolds b p s q := by
  rcases b with ⟨bl, bs, bt⟩
  cases bl <;> cases bs <;> simp [lowerHistoryComplement, certBoundHolds, not_le, not_lt]

lemma cf_alpha (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryAlpha) = prefixEval w lowerAlpha := by
  rw [cf_correct _ _ (by rw [val_alpha]; exact ab_unit.1.1), val_alpha]
lemma cf_beta (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryBeta) = prefixEval w lowerBeta := by
  rw [cf_correct _ _ (by rw [val_beta]; exact ab_unit.2.1.1), val_beta]
lemma cf_tau (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryTau) = prefixEval w lowerTau := by
  rw [cf_correct _ _ (by rw [val_tau]; exact rho_unit.1), val_tau]

lemma wh_value (w : LowerPair) (r s : ℝ) :
    certThresholdVal (lowerHistoryWH w) r s =
      (lowerWidth w.1 / lowerWidth w.2) *
        ((1+s*prefixEval w.2 lowerAlpha)*(1+s*prefixEval w.2 lowerBeta)) /
        ((1+r*prefixEval w.1 lowerAlpha)*(1+r*prefixEval w.1 lowerBeta)) := by
  have hne : certFieldVal (certFieldSub (lowerHistoryCF w.2 lowerHistoryAlpha)
      (lowerHistoryCF w.2 lowerHistoryBeta)) ≠ 0 := by
    rw [val_sub, cf_alpha, cf_beta]
    have := width_pos w.2
    unfold lowerWidth at this
    intro h
    rw [abs_sub_comm, h, abs_zero] at this
    exact lt_irrefl _ this
  unfold lowerHistoryWH
  rw [threshold_value, abs_correct, div_correct _ _ hne, val_sub, val_sub, abs_div]
  simp only [cf_alpha, cf_beta]
  unfold lowerWidth
  rw [abs_sub_comm (prefixEval w.1 lowerBeta), abs_sub_comm (prefixEval w.2 lowerBeta)]


/-! ### Endpoint-case development (m7struct4) -/

lemma append_singleton_suffix_iff (l x : List ℕ+) (c a : ℕ+) :
    l ++ [c] <:+ x ++ [a] ↔ c = a ∧ l <:+ x := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← List.append_assoc] at ht
    obtain ⟨h1, h2⟩ := List.append_inj' ht (by simp)
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨h2, ⟨t, h1⟩⟩
  · rintro ⟨rfl, t, ht⟩
    exact ⟨t, by rw [← List.append_assoc, ht]⟩

lemma suffix3_transfer (b ctx ws : List ℕ+) (hs : sufCtx b ctx) :
    ([3] : List ℕ+) <:+ b ++ ws ↔ ([3] : List ℕ+) <:+ ctx ++ ws := by
  rcases ws with _ | ⟨a, _ | ⟨a', rest⟩⟩
  · simpa [lowerEnds] using hs.1
  · simp
  · constructor
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append b _) (by simp))
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append ctx _) (by simp))

lemma suffix31_transfer (b ctx ws : List ℕ+) (hs : sufCtx b ctx) :
    ([3,1] : List ℕ+) <:+ b ++ ws ↔ ([3,1] : List ℕ+) <:+ ctx ++ ws := by
  rcases ws with _ | ⟨a, _ | ⟨a', rest⟩⟩
  · simpa [lowerEnds] using hs.2
  · have e : ([3,1] : List ℕ+) = [3] ++ [1] := rfl
    rw [e, append_singleton_suffix_iff, append_singleton_suffix_iff]
    have := hs.1
    simp only [lowerEnds] at this
    rw [this]
  · constructor
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append b _) (by simp))
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append ctx _) (by simp))

lemma odd_append (L M : List ℕ+) :
    decide ((L ++ M).length % 2 = 1) = xor (decide (L.length % 2 = 1)) (decide (M.length % 2 = 1)) := by
  rw [List.length_append]
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one M.length with h' | h' <;>
  simp [h, h', Nat.add_mod]

lemma even_eq (L : List ℕ+) : decide (L.length % 2 = 0) = !decide (L.length % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;> simp [h]

lemma prop_eq_bool (P : Prop) [Decidable P] (b : Bool) : (P = (b = true)) ↔ decide P = b := by
  cases b <;> simp [eq_iff_iff]

/-- per-side matching of the report's natural-shortening data with the history encoding. -/
lemma side_match (b ctx ws : List ℕ+) (hs : sufCtx b ctx) (par upper odd : Bool)
    (hodd : odd = xor (decide (b.length % 2 = 1)) par) :
    (decide ((b ++ ws).length % 2 = 0) = !(upper.xor odd) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true) ∧
    lowerNaturalShort (b ++ ws) (upper.xor odd) =
      decide ((if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then [3,1] else [3] : List ℕ+) <:+ ctx ++ ws) ∧
    (∀ short : Bool, lowerEndpointSuffix (b ++ ws) (upper.xor odd) short =
      (if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then (if short then [2,1,3] else [3])
        else (if short then [1,2,1,3] else [1,3]))) ∧
    (if ((b ++ ws).length % 2 = 0) = (!(upper.xor odd)) then ([3] : List ℕ+) else [1,3]) =
      (if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then [3] else [1,3]) := by
  have hA : decide ((b ++ ws).length % 2 = 0) = !(upper.xor odd) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true := by
    rw [even_eq, odd_append, hodd]
    cases upper <;> cases par <;> cases decide (b.length % 2 = 1) <;> cases decide (ws.length % 2 = 1) <;> decide
  have hcond : (((b ++ ws).length % 2 = 0) = ((!(upper.xor odd)) = true)) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true := by
    rw [prop_eq_bool]; exact hA
  refine ⟨hA, ?_, ?_, ?_⟩
  · unfold lowerNaturalShort
    by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
      exact decide_eq_decide.mpr (suffix31_transfer b ctx ws hs)
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
      exact decide_eq_decide.mpr (suffix3_transfer b ctx ws hs)
  · intro short
    unfold lowerEndpointSuffix
    by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
  · by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]

/-- shape of `lowerEqualWords` when the left side is (weakly) wider. -/
lemma equalWords_left (P : LowerPair) (u : Bool) (hW : lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u ||
         (!lowerNaturalShort P.1 u && !lowerNaturalShort P.2 u &&
           decide (lowerWidth (P.1 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.2 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])))))) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

/-- shape of `lowerEqualWords` when the right side is strictly wider. -/
lemma equalWords_right (P : LowerPair) (u : Bool) (hW : ¬ lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u ||
         (!lowerNaturalShort P.2 u && !lowerNaturalShort P.1 u &&
           decide (lowerWidth (P.2 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.1 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3]))))),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u)) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

/-- the virtual-upper test of the mixed case in history terms. -/
lemma virt_iff (b ws : List ℕ+) (par upper odd : Bool)
    (hodd : odd = xor (decide (b.length % 2 = 1)) par) :
    (upper.xor odd = decide ((b ++ ws).length % 2 = 0)) ↔
      upper = !(xor par (decide (ws.length % 2 = 1))) := by
  rw [even_eq, odd_append, hodd]
  cases upper <;> cases par <;> cases decide (b.length % 2 = 1) <;> cases decide (ws.length % 2 = 1) <;> decide

lemma mod_eq_of_decide (m n : ℕ) (h : decide (m % 2 = 1) = decide (n % 2 = 1)) : m % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [hm, hn] at h ⊢

lemma mod_ne_of_decide (m n : ℕ) (h : decide (m % 2 = 1) ≠ decide (n % 2 = 1)) : m % 2 ≠ n % 2 := by
  intro e; apply h; rw [e]

lemma ratio_pair (u v : List ℕ+) (w : LowerPair) :
    lowerWidth (u ++ w.1) / lowerWidth (v ++ w.2) =
      certThresholdVal (lowerHistoryWH w) (lowerRatio u) (lowerRatio v) /
        ((rCD u).2 ^ 2 / (rCD v).2 ^ 2) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hup := param_nonneg u
  have hvp := param_nonneg v
  have hud := (cd_pos u).2
  have hvd := (cd_pos v).2
  have ha1 := (pe_unit w.1 lowerAlpha hA).1
  have hb1 := (pe_unit w.1 lowerBeta hB).1
  have ha2 := (pe_unit w.2 lowerAlpha hA).1
  have hb2 := (pe_unit w.2 lowerBeta hB).1
  have hw1 := width_pos w.1
  have hw2 := width_pos w.2
  have h1 : 0 < 1 + lowerRatio u * prefixEval w.1 lowerAlpha := by positivity
  have h2 : 0 < 1 + lowerRatio u * prefixEval w.1 lowerBeta := by positivity
  have h3 : 0 < 1 + lowerRatio v * prefixEval w.2 lowerAlpha := by positivity
  have h4 : 0 < 1 + lowerRatio v * prefixEval w.2 lowerBeta := by positivity
  rw [width_append, width_append, wh_value w]
  field_simp
  try ring

/-- the exact value of the normalization threshold at the base parameters. -/
lemma wh_key (base words : LowerPair) :
    certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) =
      lowerScale base * (lowerWidth (base.1++words.1) / lowerWidth (base.2++words.2)) := by
  have hr : lowerWidth (base.1 ++ words.1) / lowerWidth (base.2 ++ words.2) =
      certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) /
        ((rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2) := ratio_pair base.1 base.2 words
  have hs : lowerScale base = (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2 := rfl
  rw [hr, hs]
  have := (cd_pos base.1).2; have := (cd_pos base.2).2
  field_simp

/-- the scaled auxiliary cut of the equal case: `(5/7)·aux ≤ q ↔ W₁ ≤ (7/5) W₂`. -/
lemma cut_lower_iff (base : LowerPair) (v : LowerPair) :
    certBoundHolds ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH v)⟩
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerWidth (base.1 ++ v.1) ≤ (7/5 : ℝ) * lowerWidth (base.2 ++ v.2) := by
  simp only [certBoundHolds, Bool.false_eq_true, ↓reduceIte, scale_value, wh_key]
  have hq : 0 < lowerScale base := by
    show 0 < (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2
    have := (cd_pos base.1).2; have := (cd_pos base.2).2; positivity
  have h2 := width_pos (base.2 ++ v.2)
  push_cast
  rw [show ((5:ℝ)/7) * (lowerScale base * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) =
      lowerScale base * ((5/7) * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) by ring,
    mul_le_iff_le_one_right hq, ← mul_div_assoc, div_le_one h2]
  constructor <;> intro h <;> linarith

/-- the scaled auxiliary cut of the swapped equal case: `q ≤ (7/5)·aux ↔ W₂ ≤ (7/5) W₁`. -/
lemma cut_upper_iff (base : LowerPair) (v : LowerPair) :
    certBoundHolds ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH v)⟩
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerWidth (base.2 ++ v.2) ≤ (7/5 : ℝ) * lowerWidth (base.1 ++ v.1) := by
  simp only [certBoundHolds, Bool.false_eq_true, ↓reduceIte, scale_value, wh_key]
  have hq : 0 < lowerScale base := by
    show 0 < (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2
    have := (cd_pos base.1).2; have := (cd_pos base.2).2; positivity
  have h2 := width_pos (base.2 ++ v.2)
  push_cast
  rw [show ((7:ℝ)/5) * (lowerScale base * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) =
      lowerScale base * ((7/5) * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) by ring,
    le_mul_iff_one_le_right hq, ← mul_div_assoc, one_le_div h2]

lemma bool_aux1 (a b : Bool) (h : (a || b) = true) : (!a && !b) = false := by
  cases a <;> cases b <;> simp_all
lemma bool_aux2 (a b : Bool) (h : ¬ (a || b) = true) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

/-- the equal-parity endpoint case, stated for `lowerEqualWords`. -/
lemma width_law : LowerHistoryWidthLaw := by
  intro base words
  have hx := width_pos (base.2++words.2)
  have hy := width_pos (base.1++words.1)
  have hq : 0 < lowerScale base := by
    show 0 < (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2
    have := (cd_pos base.1).2; have := (cd_pos base.2).2; positivity
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton, forall_eq,
    certBoundHolds, Bool.false_eq_true, if_false, if_true, wh_key]
  constructor
  · rw [le_mul_iff_one_le_right hq, one_le_div hx]
  · rw [lt_mul_iff_one_lt_right hq, one_lt_div hx]

lemma endval_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [cf_tau]
  exact pe_nonneg _ _ rho_unit.1

lemma eq14_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) :
    ∀ p ∈ section14EqualCases C w upper, 0 ≤ certFieldVal p.1.1 ∧ 0 ≤ certFieldVal p.1.2 := by
  intro p hp
  unfold section14EqualCases at hp
  by_cases hn : (lowerHistoryNatural C w upper false || lowerHistoryNatural C w upper true) = true
  · rw [if_pos hn] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · rw [if_neg hn] at hp
    simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hp
    rcases hp with (h | h) | (h | h) <;> subst h <;>
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

theorem equal_main (hwidth : LowerHistoryWidthLaw) (base : LowerPair) (C : LowerHistoryContext)
    (hc : ctxFits base C) (w : LowerPair) (upper : Bool)
    (hpar : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true) :
    ∃ z cs, (z,cs) ∈ section14EqualCases C w upper ∧ lowerHistoryAtBase base cs ∧
      prefixEval (lowerEqualWords (lowerHistoryAppend base w) (upper.xor (lowerHistoryCommonOdd base C))).1 lowerTau
        = prefixEval base.1 (certFieldVal z.1) ∧
      prefixEval (lowerEqualWords (lowerHistoryAppend base w) (upper.xor (lowerHistoryCommonOdd base C))).2 lowerTau
        = prefixEval base.2 (certFieldVal z.2) := by
  obtain ⟨b1, b2⟩ := base
  obtain ⟨⟨c1, c2⟩, p1, p2⟩ := C
  obtain ⟨w1, w2⟩ := w
  obtain ⟨hs1, hs2, hpp⟩ := hc
  simp only at hs1 hs2 hpp
  have hoddC : lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩ = xor (decide (b1.length % 2 = 1)) p1 := rfl
  rw [hoddC]
  have hP : lowerHistoryAppend (b1,b2) (w1,w2) = (b1 ++ w1, b2 ++ w2) := rfl
  rw [hP]
  obtain ⟨A1, N1, S1, E1⟩ := side_match b1 c1 w1 hs1 p1 upper _ rfl
  obtain ⟨A2, N2, S2, E2⟩ := side_match b2 c2 w2 hs2 p2 upper _ hpp
  have hwp1 : lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) false = xor p1 (decide (w1.length % 2 = 1)) := rfl
  have hwp2 : lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) true = xor p2 (decide (w2.length % 2 = 1)) := rfl
  have ht12 : xor (!upper) (xor p2 (decide (w2.length % 2 = 1))) = xor (!upper) (xor p1 (decide (w1.length % 2 = 1))) := by
    rw [← hwp1, ← hwp2, hpar]
  rw [ht12] at N2 S2 E2
  -- the history data in terms of the side data
  have hN1 : lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false =
      lowerNaturalShort (b1 ++ w1) (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) := N1.symm
  have hN2 : lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true =
      lowerNaturalShort (b2 ++ w2) (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) := by
    rw [N2]; unfold lowerHistoryNatural; rw [hwp2, ht12]; rfl
  have hV1 : ∀ short, lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false short =
      lowerHistoryCF (w1 ++ lowerEndpointSuffix (b1 ++ w1) (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) short) lowerHistoryTau := by
    intro short; rw [S1]; rfl
  have hV2 : ∀ short, lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true short =
      lowerHistoryCF (w2 ++ lowerEndpointSuffix (b2 ++ w2) (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) short) lowerHistoryTau := by
    intro short; rw [S2]; unfold lowerHistoryEndVal; rw [hwp2, ht12]; rfl
  have hval : ∀ (b ws ext : List ℕ+), prefixEval (b ++ ws ++ ext) lowerTau =
      prefixEval b (certFieldVal (lowerHistoryCF (ws ++ ext) lowerHistoryTau)) := by
    intro b ws ext; rw [cf_tau, List.append_assoc, pe_append]
  set u' := upper.xor (xor (decide (b1.length % 2 = 1)) p1) with hu'
  set n1 := lowerNaturalShort (b1 ++ w1) u' with hn1
  set n2 := lowerNaturalShort (b2 ++ w2) u' with hn2
  have hE : (if xor (!upper) (lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) false) then ([3] : List ℕ+) else [1,3]) =
      (if ((b1 ++ w1).length % 2 = 0) = (!u') then ([3] : List ℕ+) else [1,3]) := by
    rw [hwp1]; exact E1.symm
  have hE2 : (if ((b2 ++ w2).length % 2 = 0) = (!u') then ([3] : List ℕ+) else [1,3]) =
      (if ((b1 ++ w1).length % 2 = 0) = (!u') then ([3] : List ℕ+) else [1,3]) := by rw [E2, E1]
  set e := (if ((b1 ++ w1).length % 2 = 0) = (!u') then ([3] : List ℕ+) else [1,3]) with he
  -- normalization bound
  have hnorm := hwidth (b1,b2) (w1,w2)
  simp only at hnorm
  unfold section14EqualCases
  simp only [hN1, hN2, hE, ← hn1, ← hn2]
  by_cases hn : (n1 || n2) = true
  · -- natural case
    rw [if_pos hn]
    refine ⟨_, [], List.mem_singleton_self _, by simp [lowerHistoryAtBase, lowerHistoryConditions], ?_⟩
    have hsh : (!n1 && !n2) = false := bool_aux1 n1 n2 hn
    by_cases hW : lowerWidth (b2 ++ w2) ≤ lowerWidth (b1 ++ w1)
    · rw [equalWords_left _ _ hW]
      simp only [← hn1, ← hn2, hsh, Bool.false_and, Bool.or_false, hval, hV1, hV2, and_self]
    · rw [equalWords_right _ _ hW]
      simp only [← hn1, ← hn2, Bool.and_comm (!n2) (!n1), hsh, Bool.false_and, Bool.or_false, hval, hV1, hV2, and_self]
  · rw [if_neg hn]
    have hn1f : n1 = false := (bool_aux2 n1 n2 hn).1
    have hn2f : n2 = false := (bool_aux2 n1 n2 hn).2
    simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    by_cases hW : lowerWidth (b2 ++ w2) ≤ lowerWidth (b1 ++ w1)
    · -- left side wider: wide = false
      set sh := decide (lowerWidth (b1 ++ w1 ++ e) ≤ (7/5 : ℝ) * lowerWidth (b2 ++ w2 ++ e)) with hsh
      have hcut := cut_lower_iff (b1,b2) (w1 ++ e, w2 ++ e)
      simp only [← List.append_assoc] at hcut
      refine ⟨(lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false (sh && false),
               lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true (sh && !false)),
        [⟨false,false,lowerHistoryWH (w1,w2)⟩,
          if sh then ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH (w1 ++ e, w2 ++ e))⟩
          else lowerHistoryComplement ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH (w1 ++ e, w2 ++ e))⟩], ?_, ?_, ?_⟩
      · cases sh <;> simp
      · have h1 := (hnorm.1.1 hW)
        simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton, forall_eq] at h1
        simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨h1, ?_⟩
        by_cases hs : lowerWidth (b1 ++ w1 ++ e) ≤ (7/5 : ℝ) * lowerWidth (b2 ++ w2 ++ e)
        · rw [hsh, if_pos (decide_eq_true hs)]; exact hcut.2 hs
        · rw [hsh, if_neg (by simpa using hs), complement_holds]; exact fun h => hs (hcut.1 h)
      · rw [equalWords_left _ _ hW]
        simp only [← hn1, ← hn2, ← he, hn1f, hn2f, Bool.not_false, Bool.true_and, Bool.false_or, Bool.and_false,
          Bool.and_true, hval, hV1, hV2, ← hsh, and_self]
    · -- right side wider: wide = true
      set sh := decide (lowerWidth (b2 ++ w2 ++ e) ≤ (7/5 : ℝ) * lowerWidth (b1 ++ w1 ++ e)) with hsh
      have hcut := cut_upper_iff (b1,b2) (w1 ++ e, w2 ++ e)
      simp only [← List.append_assoc] at hcut
      refine ⟨(lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false (sh && true),
               lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true (sh && !true)),
        [⟨true,true,lowerHistoryWH (w1,w2)⟩,
          if sh then ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH (w1 ++ e, w2 ++ e))⟩
          else lowerHistoryComplement ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH (w1 ++ e, w2 ++ e))⟩], ?_, ?_, ?_⟩
      · cases sh <;> simp
      · have h1 : certBoundHolds ⟨true,true,lowerHistoryWH (w1,w2)⟩ (lowerRatio b1) (lowerRatio b2) (lowerScale (b1,b2)) := by
          have h0 : ¬ lowerHistoryAtBase (b1,b2) [⟨false,false,lowerHistoryWH (w1,w2)⟩] := fun h => hW (hnorm.1.2 h)
          simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton, forall_eq,
            certBoundHolds, Bool.false_eq_true, ↓reduceIte, not_le] at h0
          show certThresholdVal (lowerHistoryWH (w1,w2)) (lowerRatio b1) (lowerRatio b2) < lowerScale (b1,b2)
          exact h0
        simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨h1, ?_⟩
        by_cases hs : lowerWidth (b2 ++ w2 ++ e) ≤ (7/5 : ℝ) * lowerWidth (b1 ++ w1 ++ e)
        · rw [hsh, if_pos (decide_eq_true hs)]; exact hcut.2 hs
        · rw [hsh, if_neg (by simpa using hs), complement_holds]; exact fun h => hs (hcut.1 h)
      · rw [equalWords_right _ _ hW]
        simp only [← hn1, ← hn2, hE2, ← he, hn1f, hn2f, Bool.not_false, Bool.true_and, Bool.false_or, Bool.and_false,
          Bool.and_true, Bool.not_true, hval, hV1, hV2, ← hsh, and_self]

lemma mixed_natural (b1 b2 c1 c2 w1 w2 : List ℕ+) (p1 p2 upper : Bool)
    (hs1 : sufCtx b1 c1) (hs2 : sufCtx b2 c2)
    (hpp : xor (decide (b1.length % 2 = 1)) p1 = xor (decide (b2.length % 2 = 1)) p2) :
    prefixEval (lowerNaturalWords (b1 ++ w1, b2 ++ w2)
        (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩))).1 lowerTau =
      prefixEval b1 (certFieldVal (lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false
        (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false))) ∧
    prefixEval (lowerNaturalWords (b1 ++ w1, b2 ++ w2)
        (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩))).2 lowerTau =
      prefixEval b2 (certFieldVal (lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true
        (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true))) := by

  rw [show lowerHistoryCommonOdd (b1,b2) (⟨(c1,c2),(p1,p2)⟩ : LowerHistoryContext) =
      xor (decide (b1.length % 2 = 1)) p1 from rfl]
  obtain ⟨A1, N1, S1, E1⟩ := side_match b1 c1 w1 hs1 p1 upper _ rfl
  obtain ⟨A2, N2, S2, E2⟩ := side_match b2 c2 w2 hs2 p2 upper _ hpp
  have hval : ∀ (b ws ext : List ℕ+), prefixEval (b ++ ws ++ ext) lowerTau =
      prefixEval b (certFieldVal (lowerHistoryCF (ws ++ ext) lowerHistoryTau)) := by
    intro b ws ext; rw [cf_tau, List.append_assoc, pe_append]
  have hN1 : lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false =
      lowerNaturalShort (b1 ++ w1)
        (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) := N1.symm
  have hV1 : ∀ short, lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false short =
      lowerHistoryCF (w1 ++ lowerEndpointSuffix (b1 ++ w1)
        (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) short) lowerHistoryTau := by
    intro short; rw [S1]; rfl
  have hN2 : lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true =
      lowerNaturalShort (b2 ++ w2)
        (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) := N2.symm
  have hV2 : ∀ short, lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true short =
      lowerHistoryCF (w2 ++ lowerEndpointSuffix (b2 ++ w2)
        (upper.xor (xor (decide (b1.length % 2 = 1)) p1)) short) lowerHistoryTau := by
    intro short; rw [S2]; rfl
  constructor
  · show prefixEval ((b1 ++ w1) ++ lowerEndpointSuffix (b1 ++ w1) _
      (lowerNaturalShort (b1 ++ w1) _)) lowerTau = _
    rw [hN1, hV1]
    exact hval b1 w1 _
  · show prefixEval ((b2 ++ w2) ++ lowerEndpointSuffix (b2 ++ w2) _
      (lowerNaturalShort (b2 ++ w2) _)) lowerTau = _
    rw [hN2, hV2]
    exact hval b2 w2 _

lemma bool_ne (a b : Bool) (h : a ≠ b) : (!a) = b := by revert h; cases a <;> cases b <;> decide

lemma odd_succ (L : List ℕ+) (a : ℕ+) :
    decide ((L ++ [a]).length % 2 = 1) = !decide (L.length % 2 = 1) := by
  rw [odd_append]
  simp
set_option maxHeartbeats 1000000 in
theorem equal_law (base : LowerPair) (C : LowerHistoryContext)
    (hf : ctxFits base C) (w : LowerPair) (upper : Bool) (he : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true) : ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧ lowerHistoryAtBase base cs ∧
      (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
      lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z := by
  obtain ⟨z, cs, hmem, hat, h1, h2⟩ := LowerDev.equal_main LowerDev.width_law base C hf w upper he
  have hmem' : (z,cs) ∈ section14EndpointCases C w upper := by
    unfold section14EndpointCases
    rw [if_pos he]
    exact hmem
  -- both sides of the appended pair have the same length parity
  have hbool : ∀ A B P Q X Y : Bool, (xor A P = xor B Q) → (xor P X = xor Q Y) →
      (xor A X = xor B Y) := by decide
  have hlen : (lowerHistoryAppend base w).1.length % 2 = (lowerHistoryAppend base w).2.length % 2 := by
    refine mod_eq_of_decide _ _ ?_
    show decide ((base.1 ++ w.1).length % 2 = 1) = decide ((base.2 ++ w.2).length % 2 = 1)
    rw [odd_append, odd_append]
    exact hbool _ _ _ _ _ _ hf.2.2 he
  have hEW : lowerEndpointWords (lowerHistoryAppend base w)
      (upper.xor (lowerHistoryCommonOdd base C)) =
      lowerEqualWords (lowerHistoryAppend base w) (upper.xor (lowerHistoryCommonOdd base C)) := by
    unfold lowerEndpointWords
    rw [if_pos hlen]
  refine ⟨z, cs, hmem', hat, eq14_nonneg C w upper (z,cs) hmem, ?_⟩
  simp only [lowerHistoryEndpointReal, lowerEndpoint, lowerHistoryValue, hEW, h1, h2]
set_option maxHeartbeats 1000000 in
theorem mixed_law (base : LowerPair) (C : LowerHistoryContext)
    (hf : ctxFits base C) (w : LowerPair) (upper : Bool) (he : lowerHistoryWordParity C w false ≠ lowerHistoryWordParity C w true) : ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧ lowerHistoryAtBase base cs ∧
      (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
      lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z := by
  obtain ⟨b1, b2⟩ := base
  obtain ⟨⟨c1, c2⟩, p1, p2⟩ := C
  obtain ⟨w1, w2⟩ := w
  obtain ⟨hs1, hs2, hpp⟩ := hf
  simp only at hs1 hs2 hpp
  have hbool : ∀ A B P Q X Y : Bool, (xor A P = xor B Q) → (xor P X ≠ xor Q Y) →
      (xor A X ≠ xor B Y) := by decide
  have hmix : ¬ ((b1 ++ w1).length % 2 = (b2 ++ w2).length % 2) := by
    refine mod_ne_of_decide _ _ ?_
    rw [odd_append, odd_append]
    exact hbool _ _ _ _ _ _ hpp he
  have hcases : section14EndpointCases ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper =
      (section14NormalCases (w1,w2)).flatMap fun q =>
        (if upper = !(lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) q.1) then
          section14EqualCases ⟨(c1,c2),(p1,p2)⟩
            (lowerHistorySet (w1,w2) q.1 (lowerHistoryPick (w1,w2) q.1 ++ [1])) upper
        else [((lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false
                  (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false),
                lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true
                  (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true)),[])]).map
        fun v => (v.1, q.2::v.2) := by
    unfold section14EndpointCases
    rw [if_neg he]
  have hnat := mixed_natural b1 b2 c1 c2 w1 w2 p1 p2 upper hs1 hs2 hpp
  by_cases hL : lowerWidth (b2 ++ w2) ≤ lowerWidth (b1 ++ w1)
  · have hnorm : lowerHistoryAtBase (b1,b2) [(⟨false,false,lowerHistoryWH (w1,w2)⟩ : CertBound)] :=
      (width_law (b1,b2) (w1,w2)).1.mp hL
    by_cases hv : upper = !(lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) false)
    · have hvirt : upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) =
          decide ((b1 ++ w1).length % 2 = 0) := (virt_iff b1 w1 p1 upper (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) rfl).mpr hv
      have hpar' : lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1 ++ [1], w2) false =
          lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1 ++ [1], w2) true := by
        show xor p1 (decide ((w1 ++ [1]).length % 2 = 1)) = xor p2 (decide (w2.length % 2 = 1))
        rw [odd_succ]
        have h0 : xor p1 (decide (w1.length % 2 = 1)) ≠ xor p2 (decide (w2.length % 2 = 1)) := he
        revert h0
        cases p1 <;> cases p2 <;> cases decide (w1.length % 2 = 1) <;>
          cases decide (w2.length % 2 = 1) <;> decide
      obtain ⟨z, cs, hmem, hat, h1, h2⟩ := equal_main width_law (b1,b2) ⟨(c1,c2),(p1,p2)⟩
        ⟨hs1, hs2, hpp⟩ (w1 ++ [1], w2) upper hpar'
      simp only [lowerHistoryAppend] at h1 h2
      refine ⟨z, (⟨false,false,lowerHistoryWH (w1,w2)⟩ : CertBound) :: cs, ?_, ?_, ?_, ?_⟩
      · rw [hcases]
        simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        left
        rw [if_pos hv]
        exact List.mem_map_of_mem hmem
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hnorm _ (List.mem_singleton_self _)
        · exact hat b hb
      · exact eq14_nonneg ⟨(c1,c2),(p1,p2)⟩ (w1 ++ [1], w2) upper (z,cs) hmem
      · have hEW : lowerEndpointWords (b1 ++ w1, b2 ++ w2)
            (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) =
            lowerEqualWords (lowerHistoryAppend (b1,b2) (w1 ++ [1], w2))
              (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) := by
          unfold lowerEndpointWords
          rw [if_neg hmix]
          simp only [if_pos hL]
          rw [if_pos hvirt]
          show lowerEqualWords ((b1 ++ w1) ++ [1], b2 ++ w2) _ =
            lowerEqualWords (b1 ++ (w1 ++ [1]), b2 ++ w2) _
          rw [List.append_assoc]
        simp only [lowerHistoryEndpointReal, lowerHistoryAppend, lowerEndpoint, lowerHistoryValue,
          hEW, h1, h2]
    · refine ⟨(lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false
          (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false),
        lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true
          (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true)), [(⟨false,false,lowerHistoryWH (w1,w2)⟩ : CertBound)], ?_, hnorm, ?_, ?_⟩
      · rw [hcases]
        simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        left
        rw [if_neg hv]
        simp
      · exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
      · have hEW : lowerEndpointWords (b1 ++ w1, b2 ++ w2)
            (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) =
            lowerNaturalWords (b1 ++ w1, b2 ++ w2)
              (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) := by
          unfold lowerEndpointWords
          rw [if_neg hmix]
          simp only [if_pos hL]
          rw [if_neg (fun hx => hv ((virt_iff b1 w1 p1 upper (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) rfl).mp hx))]
        simp only [lowerHistoryEndpointReal, lowerHistoryAppend, lowerEndpoint, lowerHistoryValue,
          hEW, hnat.1, hnat.2]
  · have hnorm : lowerHistoryAtBase (b1,b2) [(⟨true,true,lowerHistoryWH (w1,w2)⟩ : CertBound)] := by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      have h0 := fun hx => hL ((width_law (b1,b2) (w1,w2)).1.mpr hx)
      show certThresholdVal (lowerHistoryWH (w1,w2)) (lowerRatio (b1,b2).1) (lowerRatio (b1,b2).2) <
        lowerScale (b1,b2)
      by_contra hcon
      exact h0 (fun x hx => by
        simp only [List.mem_singleton] at hx
        subst hx
        exact not_lt.mp hcon)
    by_cases hv : upper = !(lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1,w2) true)
    · have hvirt : upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) =
          decide ((b2 ++ w2).length % 2 = 0) := (virt_iff b2 w2 p2 upper (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) hpp).mpr hv
      have hpar' : lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1, w2 ++ [1]) false =
          lowerHistoryWordParity ⟨(c1,c2),(p1,p2)⟩ (w1, w2 ++ [1]) true := by
        show xor p1 (decide (w1.length % 2 = 1)) = xor p2 (decide ((w2 ++ [1]).length % 2 = 1))
        rw [odd_succ]
        have h0 : xor p1 (decide (w1.length % 2 = 1)) ≠ xor p2 (decide (w2.length % 2 = 1)) := he
        revert h0
        cases p1 <;> cases p2 <;> cases decide (w1.length % 2 = 1) <;>
          cases decide (w2.length % 2 = 1) <;> decide
      obtain ⟨z, cs, hmem, hat, h1, h2⟩ := equal_main width_law (b1,b2) ⟨(c1,c2),(p1,p2)⟩
        ⟨hs1, hs2, hpp⟩ (w1, w2 ++ [1]) upper hpar'
      simp only [lowerHistoryAppend] at h1 h2
      refine ⟨z, (⟨true,true,lowerHistoryWH (w1,w2)⟩ : CertBound) :: cs, ?_, ?_, ?_, ?_⟩
      · rw [hcases]
        simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        right
        rw [if_pos hv]
        exact List.mem_map_of_mem hmem
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hnorm _ (List.mem_singleton_self _)
        · exact hat b hb
      · exact eq14_nonneg ⟨(c1,c2),(p1,p2)⟩ (w1, w2 ++ [1]) upper (z,cs) hmem
      · have hEW : lowerEndpointWords (b1 ++ w1, b2 ++ w2)
            (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) =
            lowerEqualWords (lowerHistoryAppend (b1,b2) (w1, w2 ++ [1]))
              (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) := by
          unfold lowerEndpointWords
          rw [if_neg hmix]
          simp only [if_neg hL]
          rw [if_pos hvirt]
          show lowerEqualWords (b1 ++ w1, (b2 ++ w2) ++ [1]) _ =
            lowerEqualWords (b1 ++ w1, b2 ++ (w2 ++ [1])) _
          rw [List.append_assoc]
        simp only [lowerHistoryEndpointReal, lowerHistoryAppend, lowerEndpoint, lowerHistoryValue,
          hEW, h1, h2]
    · refine ⟨(lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false
          (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper false),
        lowerHistoryEndVal ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true
          (lowerHistoryNatural ⟨(c1,c2),(p1,p2)⟩ (w1,w2) upper true)), [(⟨true,true,lowerHistoryWH (w1,w2)⟩ : CertBound)], ?_, hnorm, ?_, ?_⟩
      · rw [hcases]
        simp only [section14NormalCases, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        right
        rw [if_neg hv]
        simp
      · exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
      · have hEW : lowerEndpointWords (b1 ++ w1, b2 ++ w2)
            (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) =
            lowerNaturalWords (b1 ++ w1, b2 ++ w2)
              (upper.xor (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩)) := by
          unfold lowerEndpointWords
          rw [if_neg hmix]
          simp only [if_neg hL]
          rw [if_neg (fun hx => hv ((virt_iff b2 w2 p2 upper (lowerHistoryCommonOdd (b1,b2) ⟨(c1,c2),(p1,p2)⟩) hpp).mp hx))]
        simp only [lowerHistoryEndpointReal, lowerHistoryAppend, lowerEndpoint, lowerHistoryValue,
          hEW, hnat.1, hnat.2]
/-! ### strict comparison development (m7struct4) -/

lemma scale_eq (p : LowerPair) : lowerScale p = (rCD p.1).2 ^ 2 / (rCD p.2).2 ^ 2 := rfl

lemma sgnOf_eps (L : List ℕ+) (p : Bool) :
    (if ((decide (L.length % 2 = 1)).xor p) = true then (-1:ℝ) else 1) * sgnOf L =
      (if p = true then (-1:ℝ) else 1) := by
  unfold sgnOf
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;> cases p <;> simp [h]

lemma sign_facts (z : CertField) :
    (0 ≤ lowerHistorySign z → 0 ≤ certFieldVal z) ∧
    (lowerHistorySign z ≤ 0 → certFieldVal z ≤ 0) ∧
    (0 < lowerHistorySign z → 0 < certFieldVal z) ∧
    (lowerHistorySign z < 0 → certFieldVal z < 0) := by
  obtain ⟨q1, q2, q3⟩ := sign_spec z
  refine ⟨?_, ?_, q1, q2⟩
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact (q1 h').le
    · exact (q3 h'.symm).ge
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact (q2 h').le
    · exact (q3 h').le

/-- `1, √3, √7, √21` are linearly independent over `ℚ`. -/
lemma val_zero (z : CertField) (h : certFieldVal z = 0) :
    z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 := by
  rw [val_eq] at h
  have hcd : z.c = 0 ∧ z.d = 0 := by
    by_contra hcon
    have hD : z.c ^ 2 - 3 * z.d ^ 2 ≠ 0 := fun h0 => hcon (sq_eq_three z.c z.d (by linarith))
    have hY : ((z.c:ℝ) + z.d * s3) ≠ 0 := fun h0 => hcon (indep3 _ _ h0)
    have h1 : ((z.a*z.c - 3*z.b*z.d)/(z.c^2 - 3*z.d^2)) * z.c
        + 3 * (((z.b*z.c - z.a*z.d)/(z.c^2 - 3*z.d^2)) * z.d) = z.a := by
      field_simp; ring
    have h2 : ((z.a*z.c - 3*z.b*z.d)/(z.c^2 - 3*z.d^2)) * z.d
        + ((z.b*z.c - z.a*z.d)/(z.c^2 - 3*z.d^2)) * z.c = z.b := by
      field_simp; ring
    set e : ℚ := (z.a*z.c - 3*z.b*z.d)/(z.c^2 - 3*z.d^2) with hedef
    set f : ℚ := (z.b*z.c - z.a*z.d)/(z.c^2 - 3*z.d^2) with hfdef
    have e1 : (e:ℝ) * (z.c:ℝ) + 3 * ((f:ℝ) * (z.d:ℝ)) = (z.a:ℝ) := by exact_mod_cast h1
    have e2 : (e:ℝ) * (z.d:ℝ) + (f:ℝ) * (z.c:ℝ) = (z.b:ℝ) := by exact_mod_cast h2
    have h3 := s3_sq
    have hkey : ((e:ℝ) + (f:ℝ) * s3) * ((z.c:ℝ) + z.d * s3) = (z.a:ℝ) + z.b * s3 := by
      linear_combination e1 + s3 * e2 + ((f:ℝ) * (z.d:ℝ)) * h3
    have hz : (((e:ℝ) + (f:ℝ) * s3) + s7) * ((z.c:ℝ) + z.d * s3) = 0 := by
      rw [add_mul, hkey]; exact h
    rcases mul_eq_zero.mp hz with h' | h'
    · refine sq_ne_seven (-e) (-f) ?_
      have hq : ((-e : ℚ):ℝ) + ((-f:ℚ):ℝ) * s3 = s7 := by push_cast; linarith
      rw [hq]; exact s7_sq
    · exact hY h'
  obtain ⟨hc0, hd0⟩ := hcd
  have hY0 : ((z.c:ℝ) + z.d * s3) = 0 := by rw [hc0, hd0]; push_cast; ring
  rw [hY0, mul_zero, add_zero] at h
  obtain ⟨ha, hb⟩ := indep3 _ _ h
  exact ⟨ha, hb, hc0, hd0⟩

lemma certField_eq_of_val (u v : CertField) (hv : certFieldVal u = certFieldVal v) : u = v := by
  have h0 : certFieldVal (certFieldSub u v) = 0 := by rw [val_sub, hv, sub_self]
  obtain ⟨ha, hb, hc, hd⟩ := val_zero _ h0
  simp only [certFieldSub, sub_eq_zero] at ha hb hc hd
  cases u; cases v
  simp_all

/-- difference of two history values at parity `(false,false)`. -/
lemma value_sub (L R : List ℕ+) (cw : LowerPair) (x y : CertField × CertField)
    (hx1 : 0 ≤ certFieldVal x.1) (hx2 : 0 ≤ certFieldVal x.2)
    (hy1 : 0 ≤ certFieldVal y.1) (hy2 : 0 ≤ certFieldVal y.2)
    (hpar : ((decide (L.length % 2 = 1)).xor false) = ((decide (R.length % 2 = 1)).xor false)) :
    lowerHistoryValue (L,R) ⟨cw,(false,false)⟩ x - lowerHistoryValue (L,R) ⟨cw,(false,false)⟩ y =
      (certFieldVal x.1 - certFieldVal y.1) /
        ((rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1))
      + (certFieldVal x.2 - certFieldVal y.2) /
        ((rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2)) := by
  have E1 : (if lowerHistoryCommonOdd (L,R) ⟨cw,(false,false)⟩ = true then (-1:ℝ) else 1) * sgnOf L = 1 := by
    show (if ((decide (L.length % 2 = 1)).xor false) = true then (-1:ℝ) else 1) * sgnOf L = 1
    rw [sgnOf_eps L false]; norm_num
  have E2 : (if lowerHistoryCommonOdd (L,R) ⟨cw,(false,false)⟩ = true then (-1:ℝ) else 1) * sgnOf R = 1 := by
    show (if ((decide (L.length % 2 = 1)).xor false) = true then (-1:ℝ) else 1) * sgnOf R = 1
    rw [hpar, sgnOf_eps R false]; norm_num
  show (if lowerHistoryCommonOdd (L,R) ⟨cw,(false,false)⟩ = true then (-1:ℝ) else 1) *
      (4 + prefixEval L (certFieldVal x.1) + prefixEval R (certFieldVal x.2)) -
    (if lowerHistoryCommonOdd (L,R) ⟨cw,(false,false)⟩ = true then (-1:ℝ) else 1) *
      (4 + prefixEval L (certFieldVal y.1) + prefixEval R (certFieldVal y.2)) = _
  generalize hS : (if lowerHistoryCommonOdd (L,R) ⟨cw,(false,false)⟩ = true then (-1:ℝ) else 1) = S at E1 E2 ⊢
  have e : S * (4 + prefixEval L (certFieldVal x.1) + prefixEval R (certFieldVal x.2)) -
      S * (4 + prefixEval L (certFieldVal y.1) + prefixEval R (certFieldVal y.2)) =
      S * (prefixEval L (certFieldVal x.1) - prefixEval L (certFieldVal y.1)) +
      S * (prefixEval R (certFieldVal x.2) - prefixEval R (certFieldVal y.2)) := by ring
  rw [e, pe_diff L _ _ hx1 hy1, pe_diff R _ _ hx2 hy2]
  linear_combination ((certFieldVal x.1 - certFieldVal y.1) /
        ((rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1))) * E1 +
    ((certFieldVal x.2 - certFieldVal y.2) /
        ((rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2))) * E2

lemma cross_iff (Dx Dy PA PB : ℝ) (hPA : 0 < PA) (hPB : 0 < PB) :
    (0 ≤ Dx / PA + Dy / PB ↔ 0 ≤ Dx * PB + Dy * PA) ∧
    (0 < Dx / PA + Dy / PB ↔ 0 < Dx * PB + Dy * PA) := by
  have h : Dx / PA + Dy / PB = (Dx * PB + Dy * PA) / (PA * PB) := by
    field_simp
    try ring
  rw [h]
  constructor
  · rw [le_div_iff₀ (mul_pos hPA hPB), zero_mul]
  · rw [lt_div_iff₀ (mul_pos hPA hPB), zero_mul]

lemma bound_neg (Dx Dy Px Py CL CR : ℝ) (hPx : 0 < Px) (hPy : 0 < Py) (hCL : 0 < CL)
    (hCR : 0 < CR) (hDx : Dx < 0) (hDy : 0 < Dy) :
    (|Dx / Dy| * Py / Px ≤ CL / CR ↔ 0 ≤ Dx * (CR * Py) + Dy * (CL * Px)) ∧
    (|Dx / Dy| * Py / Px < CL / CR ↔ 0 < Dx * (CR * Py) + Dy * (CL * Px)) := by
  have hform : |Dx / Dy| * Py / Px = ((-Dx) * Py) / (Dy * Px) := by
    rw [abs_div, abs_of_neg hDx, abs_of_pos hDy]
    field_simp
  rw [hform, div_le_div_iff₀ (mul_pos hDy hPx) hCR, div_lt_div_iff₀ (mul_pos hDy hPx) hCR]
  constructor <;> constructor <;> intro h <;> linarith

lemma bound_pos (Dx Dy Px Py CL CR : ℝ) (hPx : 0 < Px) (hPy : 0 < Py) (hCL : 0 < CL)
    (hCR : 0 < CR) (hDx : 0 < Dx) (hDy : Dy < 0) :
    (CL / CR ≤ |Dx / Dy| * Py / Px ↔ 0 ≤ Dx * (CR * Py) + Dy * (CL * Px)) ∧
    (CL / CR < |Dx / Dy| * Py / Px ↔ 0 < Dx * (CR * Py) + Dy * (CL * Px)) := by
  have hform : |Dx / Dy| * Py / Px = (Dx * Py) / ((-Dy) * Px) := by
    rw [abs_div, abs_of_pos hDx, abs_of_neg hDy]
    field_simp
  rw [hform, div_le_div_iff₀ hCR (mul_pos (neg_pos.mpr hDy) hPx),
    div_lt_div_iff₀ hCR (mul_pos (neg_pos.mpr hDy) hPx)]
  constructor <;> constructor <;> intro h <;> linarith


/-! ### Section 14 specialisation (this file) -/

lemma sufCtx_of_matches (w s : List ℕ+) (h : section14SuffixMatches w s) : sufCtx w s := by
  refine ⟨?_, ?_⟩
  · have := h.1 []; simpa using this
  · have := h.2 []; simpa using this

lemma normalize_mixed (p : LowerPair) (hm : lowerMixed p) :
    (decide ((lowerNormalize p).1.length % 2 = 1)).xor false =
      (decide ((lowerNormalize p).2.length % 2 = 1)).xor true := by
  have h : p.1.length % 2 ≠ p.2.length % 2 := hm
  unfold lowerNormalize
  split_ifs with hw <;>
    rcases Nat.mod_two_eq_zero_or_one p.1.length with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one p.2.length with h2 | h2 <;>
    simp_all

/-- Endpoint realization for `section14EndpointCases`, for an arbitrary fitting context. -/
theorem endpoint_law (base : LowerPair) (C : LowerHistoryContext) (hf : ctxFits base C)
    (w : LowerPair) (upper : Bool) :
    ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧ lowerHistoryAtBase base cs ∧
      (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
      lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z := by
  by_cases h : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true
  · exact equal_law base C hf w upper h
  · exact mixed_law base C hf w upper h

/-- `section14LocalEndpoint` is the history endpoint at a context of parity `(false,true)`. -/
lemma localEndpoint_eq (p : LowerPair) (C : LowerHistoryContext) (hCp : C.parity = (false,true))
    (w : LowerPair) (upper : Bool) :
    section14LocalEndpoint p w upper = lowerHistoryEndpointReal (lowerNormalize p) C w upper := by
  have hp1 : C.parity.1 = false := by rw [hCp]
  have hcod : lowerHistoryCommonOdd (lowerNormalize p) C =
      decide ((lowerNormalize p).1.length % 2 = 1) := by
    show (decide ((lowerNormalize p).1.length % 2 = 1)).xor C.parity.1 = _
    rw [hp1]; simp
  simp only [section14LocalEndpoint, lowerHistoryEndpointReal, lowerHistoryAppend, hcod]
  rcases Nat.mod_two_eq_zero_or_one (lowerNormalize p).1.length with h | h
  · rw [if_pos h]
    simp [h]
  · rw [if_neg (by omega : ¬ (lowerNormalize p).1.length % 2 = 0)]
    simp [h]

/-- Difference of two history values at a context of parity `(false,true)`. -/
lemma value_sub_mixed (base : LowerPair) (C : LowerHistoryContext) (hCp : C.parity = (false,true))
    (x y : CertField × CertField)
    (hx1 : 0 ≤ certFieldVal x.1) (hx2 : 0 ≤ certFieldVal x.2)
    (hy1 : 0 ≤ certFieldVal y.1) (hy2 : 0 ≤ certFieldVal y.2)
    (hpar : ((decide (base.1.length % 2 = 1)).xor C.parity.1) =
      ((decide (base.2.length % 2 = 1)).xor C.parity.2)) :
    lowerHistoryValue base C x - lowerHistoryValue base C y =
      (certFieldVal x.1 - certFieldVal y.1) /
        ((rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
          (1 + lowerRatio base.1 * certFieldVal y.1))
      + (-(certFieldVal x.2 - certFieldVal y.2)) /
        ((rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
          (1 + lowerRatio base.2 * certFieldVal y.2)) := by
  have hp1 : C.parity.1 = false := by rw [hCp]
  have hp2 : C.parity.2 = true := by rw [hCp]
  have hcod : lowerHistoryCommonOdd base C =
      (decide (base.1.length % 2 = 1)).xor C.parity.1 := rfl
  have E1 : (if lowerHistoryCommonOdd base C = true then (-1:ℝ) else 1) * sgnOf base.1 = 1 := by
    rw [hcod, hp1, sgnOf_eps base.1 false]; norm_num
  have E2 : (if lowerHistoryCommonOdd base C = true then (-1:ℝ) else 1) * sgnOf base.2 = -1 := by
    rw [hcod, hpar, hp2, sgnOf_eps base.2 true]; norm_num
  show (if lowerHistoryCommonOdd base C = true then (-1:ℝ) else 1) *
      (4 + prefixEval base.1 (certFieldVal x.1) + prefixEval base.2 (certFieldVal x.2)) -
    (if lowerHistoryCommonOdd base C = true then (-1:ℝ) else 1) *
      (4 + prefixEval base.1 (certFieldVal y.1) + prefixEval base.2 (certFieldVal y.2)) = _
  generalize hS : (if lowerHistoryCommonOdd base C = true then (-1:ℝ) else 1) = Sg at E1 E2 ⊢
  have e : Sg * (4 + prefixEval base.1 (certFieldVal x.1) + prefixEval base.2 (certFieldVal x.2)) -
      Sg * (4 + prefixEval base.1 (certFieldVal y.1) + prefixEval base.2 (certFieldVal y.2)) =
      Sg * (prefixEval base.1 (certFieldVal x.1) - prefixEval base.1 (certFieldVal y.1)) +
      Sg * (prefixEval base.2 (certFieldVal x.2) - prefixEval base.2 (certFieldVal y.2)) := by ring
  rw [e, pe_diff base.1 _ _ hx1 hy1, pe_diff base.2 _ _ hx2 hy2]
  linear_combination ((certFieldVal x.1 - certFieldVal y.1) /
      ((rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
        (1 + lowerRatio base.1 * certFieldVal y.1))) * E1 +
    ((certFieldVal x.2 - certFieldVal y.2) /
      ((rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
        (1 + lowerRatio base.2 * certFieldVal y.2))) * E2


/-- **Comparison semantics for `section14Greater`** at a context of parity `(false,true)`.
The symbolic comparison of two realized endpoints implies the real comparison. -/
lemma greater14 (base : LowerPair) (C : LowerHistoryContext) (hCp : C.parity = (false,true))
    (x y : CertField × CertField) (strict : Bool)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (hpar : ((decide (base.1.length % 2 = 1)).xor C.parity.1) =
      ((decide (base.2.length % 2 = 1)).xor C.parity.2))
    (hh : section14ComparisonHolds (section14Greater x y strict)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    (if strict = true then lowerHistoryValue base C y < lowerHistoryValue base C x
      else lowerHistoryValue base C y ≤ lowerHistoryValue base C x) := by
  have hpL := param_nonneg base.1
  have hpR := param_nonneg base.2
  have hDL := (cd_pos base.1).2
  have hDR := (cd_pos base.2).2
  have hPx : 0 < (1 + lowerRatio base.1 * certFieldVal x.1) *
      (1 + lowerRatio base.1 * certFieldVal y.1) := by
    have h1 := mul_nonneg hpL hx.1
    have h2 := mul_nonneg hpL hy.1
    positivity
  have hPy : 0 < (1 + lowerRatio base.2 * certFieldVal x.2) *
      (1 + lowerRatio base.2 * certFieldVal y.2) := by
    have h1 := mul_nonneg hpR hx.2
    have h2 := mul_nonneg hpR hy.2
    positivity
  have hCL : (0:ℝ) < (rCD base.1).2 ^ 2 := by positivity
  have hCR : (0:ℝ) < (rCD base.2).2 ^ 2 := by positivity
  have hPA : (0:ℝ) < (rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
      (1 + lowerRatio base.1 * certFieldVal y.1) := by
    have h1 := mul_nonneg hpL hx.1
    have h2 := mul_nonneg hpL hy.1
    positivity
  have hPB : (0:ℝ) < (rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
      (1 + lowerRatio base.2 * certFieldVal y.2) := by
    have h1 := mul_nonneg hpR hx.2
    have h2 := mul_nonneg hpR hy.2
    positivity
  have hdiff := value_sub_mixed base C hCp x y hx.1 hx.2 hy.1 hy.2 hpar
  obtain ⟨hcr1, hcr2⟩ := cross_iff (certFieldVal x.1 - certFieldVal y.1)
    (-(certFieldVal x.2 - certFieldVal y.2))
    ((rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
      (1 + lowerRatio base.1 * certFieldVal y.1))
    ((rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
      (1 + lowerRatio base.2 * certFieldVal y.2))
    hPA hPB
  have hle : lowerHistoryValue base C y ≤ lowerHistoryValue base C x ↔
      0 ≤ (certFieldVal x.1 - certFieldVal y.1) *
          ((rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
            (1 + lowerRatio base.2 * certFieldVal y.2)) +
        (-(certFieldVal x.2 - certFieldVal y.2)) *
          ((rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
            (1 + lowerRatio base.1 * certFieldVal y.1)) := by
    rw [← sub_nonneg, hdiff]; exact hcr1
  have hlt : lowerHistoryValue base C y < lowerHistoryValue base C x ↔
      0 < (certFieldVal x.1 - certFieldVal y.1) *
          ((rCD base.2).2 ^ 2 * (1 + lowerRatio base.2 * certFieldVal x.2) *
            (1 + lowerRatio base.2 * certFieldVal y.2)) +
        (-(certFieldVal x.2 - certFieldVal y.2)) *
          ((rCD base.1).2 ^ 2 * (1 + lowerRatio base.1 * certFieldVal x.1) *
            (1 + lowerRatio base.1 * certFieldVal y.1)) := by
    rw [← sub_pos, hdiff]; exact hcr2
  set sx : ℤ := lowerHistorySign (certFieldSub x.1 y.1) with hsxd
  set sy : ℤ := lowerHistorySign (certFieldSub x.2 y.2) with hsyd
  obtain ⟨a1, a2, a3, a4⟩ := sign_facts (certFieldSub x.1 y.1)
  obtain ⟨b1, b2, b3, b4⟩ := sign_facts (certFieldSub x.2 y.2)
  rw [val_sub] at a1 a2 a3 a4 b1 b2 b3 b4
  have hG : lowerHistoryGreater ⟨([],[]),(false,true)⟩ x y =
      (if 0 ≤ 1 * sx ∧ 0 ≤ (-1 : ℤ) * sy then LowerHistoryComparison.automatic
       else if 1 * sx ≤ 0 ∧ (-1 : ℤ) * sy ≤ 0 then LowerHistoryComparison.impossible
       else LowerHistoryComparison.bound ⟨decide (1 * sx < 0), false,
         lowerHistoryThreshold (lowerHistoryAbs
           (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2)⟩) := rfl
  simp only [one_mul, neg_mul] at hG
  by_cases h1 : 0 ≤ sx ∧ 0 ≤ -sy
  · have hEG : section14Greater x y strict =
        (if (strict && decide (x = y)) = true then LowerHistoryComparison.impossible
         else LowerHistoryComparison.automatic) := by
      unfold section14Greater
      rw [hG, if_pos h1]
    rw [hEG] at hh
    by_cases hxy : (strict && decide (x = y)) = true
    · rw [if_pos hxy] at hh; exact hh.elim
    · have hDxnn : 0 ≤ certFieldVal x.1 - certFieldVal y.1 := a1 h1.1
      have hEynn : 0 ≤ -(certFieldVal x.2 - certFieldVal y.2) := by
        have := b2 (by omega : sy ≤ 0); linarith
      cases strict with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hle]
        have u1 := mul_nonneg hDxnn hPB.le
        have u2 := mul_nonneg hEynn hPA.le
        linarith
      | true =>
        simp only [if_true]
        have hne : x ≠ y := by
          intro he
          exact hxy (by simp [he])
        rw [hlt]
        have hsome : certFieldVal x.1 - certFieldVal y.1 ≠ 0 ∨
            -(certFieldVal x.2 - certFieldVal y.2) ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          refine hne ?_
          have e1 : x.1 = y.1 := certField_eq_of_val _ _ (by linarith [hcon.1])
          have e2 : x.2 = y.2 := certField_eq_of_val _ _ (by linarith [hcon.2])
          exact Prod.ext e1 e2
        rcases hsome with h | h
        · have hpos : 0 < certFieldVal x.1 - certFieldVal y.1 := lt_of_le_of_ne hDxnn (Ne.symm h)
          have u1 := mul_pos hpos hPB
          have u2 := mul_nonneg hEynn hPA.le
          linarith
        · have hpos : 0 < -(certFieldVal x.2 - certFieldVal y.2) := lt_of_le_of_ne hEynn (Ne.symm h)
          have u1 := mul_nonneg hDxnn hPB.le
          have u2 := mul_pos hpos hPA
          linarith
  · by_cases h2 : sx ≤ 0 ∧ -sy ≤ 0
    · have hEG : section14Greater x y strict = LowerHistoryComparison.impossible := by
        unfold section14Greater
        rw [hG, if_neg h1, if_pos h2]
      rw [hEG] at hh; exact hh.elim
    · have hEG : section14Greater x y strict =
          LowerHistoryComparison.bound ⟨decide (sx < 0), strict,
            lowerHistoryThreshold (lowerHistoryAbs
              (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2)⟩ := by
        unfold section14Greater
        rw [hG, if_neg h1, if_neg h2]
      have hdyne : certFieldVal x.2 - certFieldVal y.2 ≠ 0 := by
        intro h0
        have hz : sy = 0 := by
          rcases lt_trichotomy sy 0 with hs | hs | hs
          · exact absurd (b4 hs) (by rw [h0]; exact lt_irrefl 0)
          · exact hs
          · exact absurd (b3 hs) (by rw [h0]; exact lt_irrefl 0)
        rw [hz] at h1 h2
        omega
      have hdyne' : certFieldVal (certFieldSub x.2 y.2) ≠ 0 := by rw [val_sub]; exact hdyne
      have hthr : certThresholdVal (lowerHistoryThreshold (lowerHistoryAbs
          (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2))
          (lowerRatio base.1) (lowerRatio base.2) =
          |(certFieldVal x.1 - certFieldVal y.1) / (certFieldVal x.2 - certFieldVal y.2)| *
            ((1 + lowerRatio base.2 * certFieldVal x.2) * (1 + lowerRatio base.2 * certFieldVal y.2)) /
            ((1 + lowerRatio base.1 * certFieldVal x.1) * (1 + lowerRatio base.1 * certFieldVal y.1)) := by
        rw [threshold_value, abs_correct, div_correct _ _ hdyne', val_sub, val_sub]
      have habs : |(certFieldVal x.1 - certFieldVal y.1) / (certFieldVal x.2 - certFieldVal y.2)| =
          |(certFieldVal x.1 - certFieldVal y.1) / (-(certFieldVal x.2 - certFieldVal y.2))| := by
        rw [div_neg, abs_neg]
      have hq : lowerScale base = (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2 := rfl
      rw [hEG] at hh
      simp only [section14ComparisonHolds, certBoundHolds] at hh
      by_cases hsx : sx < 0
      · have hDxneg : certFieldVal x.1 - certFieldVal y.1 < 0 := a4 hsx
        have hsy : -sy > 0 := by
          by_contra hcon
          exact h2 ⟨hsx.le, not_lt.mp hcon⟩
        have hEypos : 0 < -(certFieldVal x.2 - certFieldVal y.2) := by
          have := b4 (by omega : sy < 0); linarith
        obtain ⟨hbd1, hbd2⟩ := bound_neg (certFieldVal x.1 - certFieldVal y.1)
          (-(certFieldVal x.2 - certFieldVal y.2))
          ((1 + lowerRatio base.1 * certFieldVal x.1) * (1 + lowerRatio base.1 * certFieldVal y.1))
          ((1 + lowerRatio base.2 * certFieldVal x.2) * (1 + lowerRatio base.2 * certFieldVal y.2))
          ((rCD base.1).2 ^ 2) ((rCD base.2).2 ^ 2) hPx hPy hCL hCR hDxneg hEypos
        rw [if_pos (by simpa using hsx), hthr, habs, hq] at hh
        cases strict with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hh ⊢
          rw [hle]
          have := hbd1.mp hh
          linarith
        | true =>
          simp only [if_true] at hh ⊢
          rw [hlt]
          have := hbd2.mp hh
          linarith
      · have hsx' : 0 < sx := by
          rcases lt_or_eq_of_le (not_lt.mp hsx) with h | h
          · exact h
          · exfalso
            have hsyneg : -sy < 0 := by
              by_contra hcon
              exact h1 ⟨le_of_eq h, not_lt.mp hcon⟩
            exact h2 ⟨le_of_eq h.symm, hsyneg.le⟩
        have hDxpos : 0 < certFieldVal x.1 - certFieldVal y.1 := a3 hsx'
        have hsy : -sy < 0 := by
          by_contra hcon
          exact h1 ⟨hsx'.le, not_lt.mp hcon⟩
        have hEyneg : -(certFieldVal x.2 - certFieldVal y.2) < 0 := by
          have := b3 (by omega : 0 < sy); linarith
        obtain ⟨hbd1, hbd2⟩ := bound_pos (certFieldVal x.1 - certFieldVal y.1)
          (-(certFieldVal x.2 - certFieldVal y.2))
          ((1 + lowerRatio base.1 * certFieldVal x.1) * (1 + lowerRatio base.1 * certFieldVal y.1))
          ((1 + lowerRatio base.2 * certFieldVal x.2) * (1 + lowerRatio base.2 * certFieldVal y.2))
          ((rCD base.1).2 ^ 2) ((rCD base.2).2 ^ 2) hPx hPy hCL hCR hDxpos hEyneg
        rw [if_neg (by simpa using hsx), hthr, habs, hq] at hh
        cases strict with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hh ⊢
          rw [hle]
          have := hbd1.mp hh
          linarith
        | true =>
          simp only [if_true] at hh ⊢
          rw [hlt]
          have := hbd2.mp hh
          linarith


/-- Transport a realized endpoint case across the catalogue's `section14EndSet` equality. -/
lemma endset_transfer (E F : List LowerHistoryEndCase)
    (h : section14EndSet E = section14EndSet F) (z : CertField × CertField) (cs : List CertBound)
    (hmem : (z,cs) ∈ F) : ∃ cs', (z,cs') ∈ E ∧ cs'.toFinset = cs.toFinset := by
  classical
  have h1 : (z, cs.toFinset) ∈ section14EndSet F := by
    simp only [section14EndSet, List.mem_toFinset, List.mem_map]
    exact ⟨(z,cs), hmem, rfl⟩
  rw [← h] at h1
  simp only [section14EndSet, List.mem_toFinset, List.mem_map] at h1
  obtain ⟨⟨z', cs'⟩, hm', heq⟩ := h1
  simp only [Prod.mk.injEq] at heq
  exact ⟨cs', heq.1 ▸ hm', heq.2⟩

lemma holds_of_finset_eq (l m : List CertBound) (h : l.toFinset = m.toFinset) (r s q : ℝ)
    (hm : section14Holds m r s q) : section14Holds l r s q := by
  classical
  intro b hb
  refine hm b ?_
  have : b ∈ l.toFinset := List.mem_toFinset.mpr hb
  rw [h] at this
  exact List.mem_toFinset.mp this

end LowerDev

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem solution (p : LowerPair) (i : Fin 16) (pl : Section14Plan) (gs : ℕ × Section14Spec)
    (hm : lowerMixed p)
    (hmatch : section14Matches p (section14State section14Catalog (i.val+1)))
    (hv : section14StateValid section14Catalog (i.val+1))
    (hpl : pl ∈ (section14State section14Catalog (i.val+1)).plans) (hgs : gs ∈ pl.specs)
    (hc : ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length,
      section14Holds (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).1 (section14R p) (section14S p) (section14Q p) →
      section14ComparisonHolds (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 (section14R p) (section14S p) (section14Q p)) : section14SpecHolds p gs.2 := by
  classical
  obtain ⟨hmw1, hmw2, hparity⟩ := hmatch
  -- the plan and the spec are valid in the catalogue state
  have hplv : section14PlanValid section14Catalog
      (section14State section14Catalog (i.val+1)) pl := hv.2.2.2.2.1 pl hpl
  have hspv : section14SpecValid section14Catalog
      (section14State section14Catalog (i.val+1)) pl.caseId gs := hplv.2.2.2.2.2.2 gs hgs
  have hfirst : 0 < (section14Goal section14Catalog gs.1).first := hspv.2.1
  have hstrict : (section14Goal section14Catalog gs.1).strict = gs.2.strict := hspv.2.2.2.1
  have hexset : (section14Bounds section14Catalog
      (section14Goal section14Catalog gs.1).extra).toFinset = gs.2.extra.toFinset :=
    hspv.2.2.2.2.1
  have hEA : section14EndSet (section14Endpoints section14Catalog
        (section14Goal section14Catalog gs.1).first) =
      section14EndSet (section14EndpointCases
        (section14State section14Catalog (i.val+1)).context gs.2.first gs.2.firstUpper) :=
    hspv.2.2.2.2.2.1
  have hEB : section14EndSet (section14Endpoints section14Catalog
        (section14Goal section14Catalog gs.1).second) =
      section14EndSet (section14EndpointCases
        (section14State section14Catalog (i.val+1)).context gs.2.second gs.2.secondUpper) :=
    hspv.2.2.2.2.2.2
  -- the real pair fits the catalogue context
  have hp1 : (section14State section14Catalog (i.val+1)).context.parity.1 = false := by
    rw [hparity]
  have hp2 : (section14State section14Catalog (i.val+1)).context.parity.2 = true := by
    rw [hparity]
  have hparfit : ((decide ((lowerNormalize p).1.length % 2 = 1)).xor
        (section14State section14Catalog (i.val+1)).context.parity.1) =
      ((decide ((lowerNormalize p).2.length % 2 = 1)).xor
        (section14State section14Catalog (i.val+1)).context.parity.2) := by
    rw [hp1, hp2]; exact LowerDev.normalize_mixed p hm
  have hfits : LowerDev.ctxFits (lowerNormalize p)
      (section14State section14Catalog (i.val+1)).context :=
    ⟨LowerDev.sufCtx_of_matches _ _ hmw1, LowerDev.sufCtx_of_matches _ _ hmw2, hparfit⟩
  intro hextra
  -- realize both endpoints
  obtain ⟨zx, csx, hmx, hatx, hnnx, hexx⟩ :=
    LowerDev.endpoint_law (lowerNormalize p) _ hfits gs.2.first gs.2.firstUpper
  obtain ⟨zy, csy, hmy, haty, hnny, hexy⟩ :=
    LowerDev.endpoint_law (lowerNormalize p) _ hfits gs.2.second gs.2.secondUpper
  obtain ⟨csx', hmx', hsx'⟩ := LowerDev.endset_transfer _ _ hEA zx csx hmx
  obtain ⟨csy', hmy', hsy'⟩ := LowerDev.endset_transfer _ _ hEB zy csy hmy
  -- the corresponding catalogue branch
  have hmemB : (section14Bounds section14Catalog (section14Goal section14Catalog gs.1).extra
        ++ csx' ++ csy',
      section14Greater zx zy (section14Goal section14Catalog gs.1).strict) ∈
      section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1) := by
    unfold section14GoalBranches
    rw [if_neg (by omega : ¬ (section14Goal section14Catalog gs.1).first = 0)]
    exact List.mem_flatMap.mpr ⟨(zx, csx'), hmx',
      List.mem_map.mpr ⟨(zy, csy'), hmy', rfl⟩⟩
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmemB
  have hbranch : section14Branch section14Catalog (section14Goal section14Catalog gs.1) (j : ℤ) =
      (section14Bounds section14Catalog (section14Goal section14Catalog gs.1).extra
        ++ csx' ++ csy',
       section14Greater zx zy (section14Goal section14Catalog gs.1).strict) := by
    unfold section14Branch
    rw [show ((j : ℤ)).toNat = j by simp, List.getElem?_eq_getElem hj, hjeq]
    rfl
  -- its side conditions hold at the real parameters
  have hholds : section14Holds (section14Branch section14Catalog
      (section14Goal section14Catalog gs.1) (j : ℤ)).1
      (section14R p) (section14S p) (section14Q p) := by
    rw [hbranch]
    intro b hb
    rcases List.mem_append.mp hb with hb' | hb'
    · rcases List.mem_append.mp hb' with hb'' | hb''
      · exact LowerDev.holds_of_finset_eq _ _ hexset _ _ _ hextra b hb''
      · exact hatx b (by
          have : b ∈ csx'.toFinset := List.mem_toFinset.mpr hb''
          rw [hsx'] at this
          exact List.mem_toFinset.mp this)
    · exact haty b (by
        have : b ∈ csy'.toFinset := List.mem_toFinset.mpr hb'
        rw [hsy'] at this
        exact List.mem_toFinset.mp this)
  have hcomp := hc j (List.mem_range.mpr hj) hholds
  rw [hbranch] at hcomp
  -- read off the real comparison
  have hgt := LowerDev.greater14 (lowerNormalize p)
    (section14State section14Catalog (i.val+1)).context hparity zx zy
    (section14Goal section14Catalog gs.1).strict hnnx hnny hparfit hcomp
  rw [hstrict] at hgt
  show (if gs.2.strict = true then
      section14LocalEndpoint p gs.2.second gs.2.secondUpper <
        section14LocalEndpoint p gs.2.first gs.2.firstUpper
    else section14LocalEndpoint p gs.2.second gs.2.secondUpper ≤
        section14LocalEndpoint p gs.2.first gs.2.firstUpper)
  rw [LowerDev.localEndpoint_eq p _ hparity gs.2.first gs.2.firstUpper,
    LowerDev.localEndpoint_eq p _ hparity gs.2.second gs.2.secondUpper, hexx, hexy]
  exact hgt


