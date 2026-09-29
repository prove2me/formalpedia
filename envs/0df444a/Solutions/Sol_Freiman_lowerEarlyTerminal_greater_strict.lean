-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_greater_strict
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T09:48:55.295565+00:00
-- url     : https://prove2.me/submissions/ae21b9fd-3b49-4a31-83ee-f84f109e52c4

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
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

end LowerDev

set_option maxHeartbeats 1000000 in
open LowerDev in
theorem solution (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) : section14ComparisonHolds (lowerEarlyTerminalGreater x y true)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        lowerHistoryValue base C y < lowerHistoryValue base C x := by
  obtain ⟨cw, p1, p2⟩ := C
  obtain ⟨L, R⟩ := base
  have hp1 : p1 = false := congrArg Prod.fst hc
  have hp2 : p2 = false := congrArg Prod.snd hc
  subst hp1
  subst hp2
  have hpar : ((decide (L.length % 2 = 1)).xor false) = ((decide (R.length % 2 = 1)).xor false) :=
    hf.2.2
  have hpL := param_nonneg L
  have hpR := param_nonneg R
  have hDL := (cd_pos L).2
  have hDR := (cd_pos R).2
  have hPx : 0 < (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1) := by
    have h1 := mul_nonneg hpL hx.1
    have h2 := mul_nonneg hpL hy.1
    positivity
  have hPy : 0 < (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2) := by
    have h1 := mul_nonneg hpR hx.2
    have h2 := mul_nonneg hpR hy.2
    positivity
  have hCL : (0:ℝ) < (rCD L).2 ^ 2 := by positivity
  have hCR : (0:ℝ) < (rCD R).2 ^ 2 := by positivity
  have hPA : (0:ℝ) < (rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) *
      (1 + lowerRatio L * certFieldVal y.1) := by
    have h1 := mul_nonneg hpL hx.1
    have h2 := mul_nonneg hpL hy.1
    positivity
  have hPB : (0:ℝ) < (rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) *
      (1 + lowerRatio R * certFieldVal y.2) := by
    have h1 := mul_nonneg hpR hx.2
    have h2 := mul_nonneg hpR hy.2
    positivity
  have hdiff := value_sub L R cw x y hx.1 hx.2 hy.1 hy.2 hpar
  obtain ⟨hcr1, hcr2⟩ := cross_iff (certFieldVal x.1 - certFieldVal y.1)
    (certFieldVal x.2 - certFieldVal y.2)
    ((rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1))
    ((rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2))
    hPA hPB
  have hlt : lowerHistoryValue (L,R) ⟨cw,(false,false)⟩ y < lowerHistoryValue (L,R) ⟨cw,(false,false)⟩ x ↔
      0 < (certFieldVal x.1 - certFieldVal y.1) *
          ((rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2)) +
        (certFieldVal x.2 - certFieldVal y.2) *
          ((rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1)) := by
    rw [← sub_pos, hdiff]; exact hcr2
  set sx : ℤ := lowerHistorySign (certFieldSub x.1 y.1) with hsxd
  set sy : ℤ := lowerHistorySign (certFieldSub x.2 y.2) with hsyd
  obtain ⟨a1, a2, a3, a4⟩ := sign_facts (certFieldSub x.1 y.1)
  obtain ⟨b1, b2, b3, b4⟩ := sign_facts (certFieldSub x.2 y.2)
  rw [val_sub] at a1 a2 a3 a4 b1 b2 b3 b4
  have hG : lowerHistoryGreater ⟨([],[]),(false,false)⟩ x y =
      (if 0 ≤ 1 * sx ∧ 0 ≤ 1 * sy then LowerHistoryComparison.automatic
       else if 1 * sx ≤ 0 ∧ 1 * sy ≤ 0 then LowerHistoryComparison.impossible
       else LowerHistoryComparison.bound ⟨decide (1 * sx < 0), false,
         lowerHistoryThreshold (lowerHistoryAbs
           (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2)⟩) := rfl
  simp only [one_mul] at hG
  by_cases h1 : 0 ≤ sx ∧ 0 ≤ sy
  · have hEG : lowerEarlyTerminalGreater x y true =
        (if x = y then LowerHistoryComparison.impossible else LowerHistoryComparison.automatic) := by
      unfold lowerEarlyTerminalGreater
      rw [hG, if_pos h1]
      simp
    rw [hEG]
    by_cases hxy : x = y
    · rw [if_pos hxy, hxy]
      simp only [section14ComparisonHolds]
      exact iff_of_false (fun h => h) (lt_irrefl _)
    · rw [if_neg hxy]
      simp only [section14ComparisonHolds]
      refine iff_of_true trivial ?_
      rw [hlt]
      have hDxnn : 0 ≤ certFieldVal x.1 - certFieldVal y.1 := a1 h1.1
      have hDynn : 0 ≤ certFieldVal x.2 - certFieldVal y.2 := b1 h1.2
      have hne : certFieldVal x.1 - certFieldVal y.1 ≠ 0 ∨
          certFieldVal x.2 - certFieldVal y.2 ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        refine hxy ?_
        have e1 : x.1 = y.1 := certField_eq_of_val _ _ (by linarith [hcon.1])
        have e2 : x.2 = y.2 := certField_eq_of_val _ _ (by linarith [hcon.2])
        exact Prod.ext e1 e2
      rcases hne with h | h
      · have hpos : 0 < certFieldVal x.1 - certFieldVal y.1 := lt_of_le_of_ne hDxnn (Ne.symm h)
        have u1 := mul_pos hpos hPB
        have u2 := mul_nonneg hDynn hPA.le
        linarith
      · have hpos : 0 < certFieldVal x.2 - certFieldVal y.2 := lt_of_le_of_ne hDynn (Ne.symm h)
        have u1 := mul_nonneg hDxnn hPB.le
        have u2 := mul_pos hpos hPA
        linarith
  by_cases h2 : sx ≤ 0 ∧ sy ≤ 0
  · have hEG : lowerEarlyTerminalGreater x y true = LowerHistoryComparison.impossible := by
      unfold lowerEarlyTerminalGreater
      rw [hG, if_neg h1, if_pos h2]
    rw [hEG]
    simp only [section14ComparisonHolds]
    refine iff_of_false (fun h => h) (fun hcon => ?_)
    rw [hlt] at hcon
    have t1 : certFieldVal x.1 - certFieldVal y.1 ≤ 0 := a2 h2.1
    have t2 : certFieldVal x.2 - certFieldVal y.2 ≤ 0 := b2 h2.2
    have u1 : 0 ≤ (-(certFieldVal x.1 - certFieldVal y.1)) *
        ((rCD R).2 ^ 2 * (1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2)) :=
      mul_nonneg (by linarith) hPB.le
    have u2 : 0 ≤ (-(certFieldVal x.2 - certFieldVal y.2)) *
        ((rCD L).2 ^ 2 * (1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1)) :=
      mul_nonneg (by linarith) hPA.le
    linarith
  · have hEG : lowerEarlyTerminalGreater x y true =
        LowerHistoryComparison.bound ⟨decide (sx < 0), true,
          lowerHistoryThreshold (lowerHistoryAbs
            (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2)⟩ := by
      unfold lowerEarlyTerminalGreater
      rw [hG, if_neg h1, if_neg h2]
    -- in this branch the two signs are strictly opposite
    have hdyne : certFieldVal x.2 - certFieldVal y.2 ≠ 0 := by
      intro h0
      have hz : sy = 0 := by
        rcases lt_trichotomy sy 0 with hh | hh | hh
        · exact absurd (b4 hh) (by rw [h0]; exact lt_irrefl 0)
        · exact hh
        · exact absurd (b3 hh) (by rw [h0]; exact lt_irrefl 0)
      rw [hz] at h1 h2
      omega
    have hdyne' : certFieldVal (certFieldSub x.2 y.2) ≠ 0 := by rw [val_sub]; exact hdyne
    have hthr : certThresholdVal (lowerHistoryThreshold (lowerHistoryAbs
        (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2))) (x.1,y.1) (x.2,y.2))
        (lowerRatio L) (lowerRatio R) =
        |(certFieldVal x.1 - certFieldVal y.1) / (certFieldVal x.2 - certFieldVal y.2)| *
          ((1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2)) /
          ((1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1)) := by
      rw [threshold_value, abs_correct, div_correct _ _ hdyne', val_sub, val_sub]
    have hq : lowerScale (L,R) = (rCD L).2 ^ 2 / (rCD R).2 ^ 2 := rfl
    rw [hEG]
    simp only [section14ComparisonHolds, certBoundHolds]
    by_cases hsx : sx < 0
    · have hDxneg : certFieldVal x.1 - certFieldVal y.1 < 0 := a4 hsx
      have hsy : 0 < sy := by
        by_contra hcon
        exact h2 ⟨hsx.le, not_lt.mp hcon⟩
      have hDypos : 0 < certFieldVal x.2 - certFieldVal y.2 := b3 hsy
      obtain ⟨-, hbd⟩ := bound_neg (certFieldVal x.1 - certFieldVal y.1)
        (certFieldVal x.2 - certFieldVal y.2)
        ((1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1))
        ((1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2))
        ((rCD L).2 ^ 2) ((rCD R).2 ^ 2) hPx hPy hCL hCR hDxneg hDypos
      rw [if_pos (by simpa using hsx), if_pos trivial, hthr, hq, hlt]
      rw [hbd]
      constructor <;> intro h <;> linarith
    · have hsx' : 0 < sx := by
        rcases lt_or_eq_of_le (not_lt.mp hsx) with h | h
        · exact h
        · exfalso
          have hsyneg : sy < 0 := by
            by_contra hcon
            exact h1 ⟨le_of_eq h, not_lt.mp hcon⟩
          exact h2 ⟨le_of_eq h.symm, hsyneg.le⟩
      have hDxpos : 0 < certFieldVal x.1 - certFieldVal y.1 := a3 hsx'
      have hsy : sy < 0 := by
        by_contra hcon
        exact h1 ⟨hsx'.le, not_lt.mp hcon⟩
      have hDyneg : certFieldVal x.2 - certFieldVal y.2 < 0 := b4 hsy
      obtain ⟨-, hbd⟩ := bound_pos (certFieldVal x.1 - certFieldVal y.1)
        (certFieldVal x.2 - certFieldVal y.2)
        ((1 + lowerRatio L * certFieldVal x.1) * (1 + lowerRatio L * certFieldVal y.1))
        ((1 + lowerRatio R * certFieldVal x.2) * (1 + lowerRatio R * certFieldVal y.2))
        ((rCD L).2 ^ 2) ((rCD R).2 ^ 2) hPx hPy hCL hCR hDxpos hDyneg
      rw [if_neg (by simpa using hsx), if_pos trivial, hthr, hq, hlt]
      rw [hbd]
      constructor <;> intro h <;> linarith
