-- Prove2me | solution 1 for ConsistentSubmodular.fourThirds_boundary_edge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:41.464029+00:00
-- url     : https://prove2.me/submissions/01be6272-b820-460f-808f-ceda02539e4f

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary

section

noncomputable section

namespace ConsistentSubmodular

private theorem concave_quadratic_nonnegative (c e l u x : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : 0 ≤ -3 * l ^ 2 + c * l + e)
    (hu : 0 ≤ -3 * u ^ 2 + c * u + e) :
    0 ≤ -3 * x ^ 2 + c * x + e := by
  by_cases hs : 0 ≤ c - 3 * (x + l)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlx) hs]
  · have hs' : 0 ≤ 3 * (x + u) - c := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hs']

theorem fourThirdsDiscriminant_lower (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    0 ≤ fourThirdsDiscriminant p (p / 2) := by
  have := mul_nonneg hp (show 0 ≤ 1 - 2 * p by linarith)
  unfold fourThirdsDiscriminant
  nlinarith

theorem fourThirdsDiscriminant_small (p d : ℝ) (hp : 0 ≤ p) (hp3 : p ≤ 1 / 3)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p)) :
    0 ≤ fourThirdsDiscriminant p d := by
  apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
    (p / 2) (p * (1 - p)) d hdlow hcredit
  · have := fourThirdsDiscriminant_lower p hp (by linarith)
    unfold fourThirdsDiscriminant at this
    nlinarith only [this]
  · have hprod : 0 ≤ p * (2 * p - 1) ^ 2 * (1 - 3 * p) :=
      mul_nonneg (mul_nonneg hp (sq_nonneg _)) (by linarith)
    nlinarith only [hprod]

theorem fourThirdsDiscriminant_interior (p d : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p))
    (hleft : 0 < 5 / 4 - 7 * d + p) (hright : 0 < 15 / 8 - 16 * d + 5 * p) :
    0 ≤ fourThirdsDiscriminant p d := by
  by_cases hp3 : p ≤ 1 / 3
  · exact fourThirdsDiscriminant_small p d hp hp3 hdlow hcredit
  · have hp3' : (1 : ℝ) / 3 ≤ p := le_of_not_ge hp3
    by_cases hsplit : p ≤ 55 / 152
    · apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
        (p / 2) (15 / 128 + 5 * p / 16) d hdlow (by linarith)
      · have := fourThirdsDiscriminant_lower p hp hp2
        unfold fourThirdsDiscriminant at this
        nlinarith only [this]
      · have hprod := mul_nonneg (show 0 ≤ p - 7 / 24 by linarith)
          (show 0 ≤ 55 / 152 - p by linarith)
        nlinarith only [hprod]
    · apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
        (p / 2) (5 / 28 + p / 7) d hdlow (by linarith)
      · have := fourThirdsDiscriminant_lower p hp hp2
        unfold fourThirdsDiscriminant at this
        nlinarith only [this]
      · have hprod := mul_nonneg (show 0 ≤ 2 - 4 * p by linarith)
          (show 0 ≤ 152 * p - 55 by linarith)
        nlinarith only [hprod]

private theorem edge_nonnegative_of_discriminant (B e r z : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hdisc : 0 ≤ 4 * B * r - (e + r) ^ 2) :
    0 ≤ B - e * z - r * z * (1 - z) := by
  by_cases hr0 : r = 0
  · subst r
    have he : e = 0 := by nlinarith [sq_nonneg e]
    simp [he, hB]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hid : 4 * r * (B - e * z - r * z * (1 - z)) =
        (2 * r * z - (e + r)) ^ 2 + 4 * B * r - (e + r) ^ 2 := by ring
    nlinarith [sq_nonneg (2 * r * z - (e + r))]

private theorem edge_nonnegative_on_unit (B e r : ℝ)
    (hB : 0 ≤ B) (hend : 0 ≤ B - e)
    (hdisc : 0 < e + r → 0 < r - e → 0 ≤ 4 * B * r - (e + r) ^ 2)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ B - e * z - r * z * (1 - z) := by
  by_cases hr : 0 ≤ r
  · by_cases hleft : 0 < e + r
    · by_cases hright : 0 < r - e
      · exact edge_nonnegative_of_discriminant B e r z hB hr (hdisc hleft hright)
      · have hfactor : 0 ≤ e - r * z := by
          have := mul_nonneg hr (sub_nonneg.mpr hz1)
          linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hz1) hfactor]
    · have hfactor : 0 ≤ -e - r + r * z := by
        have := mul_nonneg hr hz
        linarith
      nlinarith [mul_nonneg hz hfactor]
  · have h1 := mul_nonneg (sub_nonneg.mpr hz1) hB
    have h2 := mul_nonneg hz hend
    have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr)
      (mul_nonneg hz (sub_nonneg.mpr hz1))
    nlinarith

/-- The boundary edge is safe at the threshold parameter four thirds. Its
formal residuals need not themselves form a feasible atomic profile. -/
theorem fourThirds_base_boundary (p d z : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hd4 : d ≤ 1 / 4) (hcredit : d ≤ p * (1 - p))
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 1 / 4 - d - fourThirdsBaseDelta p d * z -
      fourThirdsBaseOverlap p d * z * (1 - z) := by
  apply edge_nonnegative_on_unit (1 / 4 - d) (fourThirdsBaseDelta p d)
    (fourThirdsBaseOverlap p d) (by linarith) ?_ ?_ z hz hz1
  · unfold fourThirdsBaseDelta
    nlinarith [sq_nonneg (p - 7 / 22)]
  · intro hleft hright
    have hm := fourThirdsDiscriminant_interior p d hp hp2 hdlow hcredit
      (by unfold fourThirdsBaseDelta fourThirdsBaseOverlap at hleft; linarith)
      (by unfold fourThirdsBaseDelta fourThirdsBaseOverlap at hright; linarith)
    unfold fourThirdsBaseDelta fourThirdsBaseOverlap fourThirdsDiscriminant at *
    nlinarith only [hm]

theorem fourThirds_negative_discriminant (p d : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p))
    (hnegative : fourThirdsDiscriminant p d < 0) :
    (1 : ℝ) / 3 < p ∧ (8 * p + 1) / 20 < d := by
  have hp3 : (1 : ℝ) / 3 < p := by
    by_contra hn
    have := fourThirdsDiscriminant_small p d hp (le_of_not_gt hn) hdlow hcredit
    linarith
  refine ⟨hp3, ?_⟩
  by_contra hn
  have hdupper : d ≤ (8 * p + 1) / 20 := le_of_not_gt hn
  have hm : 0 ≤ fourThirdsDiscriminant p d := by
    apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
      (p / 2) ((8 * p + 1) / 20) d hdlow hdupper
    · have := fourThirdsDiscriminant_lower p hp hp2
      unfold fourThirdsDiscriminant at this
      nlinarith only [this]
    · have hprod := mul_nonneg (show 0 ≤ 1 - 2 * p by linarith)
        (show 0 ≤ 17 * p - 1 by linarith)
      nlinarith only [hprod]
  linarith

theorem fourThirds_boundary_polynomial (p d q z : ℝ) (hq : q ≠ 0) :
    q ^ 2 * fourThirdsBoundaryMargin p d q z = fourThirdsBoundaryPolynomial p d q z := by
  unfold fourThirdsBoundaryMargin fourThirdsBoundaryOverlap fourThirdsBoundaryDelta
    fourThirdsBoundaryWeight fourThirdsBoundaryPolynomial
  field_simp
  ring

theorem fourThirds_boundary_discriminant_identity (p d q : ℝ) (hq : q ≠ 0) :
    q * ((1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
      (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2) =
      (4 / 3 : ℝ) * fourThirdsDiscriminant p d -
        (q - 4 / 3) * (p ^ 2 + 4 * p * d - 2 * p + d) := by
  unfold fourThirdsBoundaryOverlap fourThirdsBoundaryDelta
    fourThirdsBoundaryWeight fourThirdsDiscriminant
  field_simp
  ring

private theorem polynomial_nonnegative_unit (a b c z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hend : 0 ≤ a + b + c) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ a + b * z + c * z ^ 2 := by
  by_cases hc : 0 ≤ c
  · positivity
  · have h1 := mul_nonneg (sub_nonneg.mpr hz1) ha
    have h2 := mul_nonneg hz hend
    have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc)
      (mul_nonneg hz (sub_nonneg.mpr hz1))
    nlinarith

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution (p d q z : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4) (hcredit : d ≤ p * (1 - p))
    (hq : (4 : ℝ) / 3 ≤ q) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ fourThirdsBoundaryMargin p d q z := by
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have hB : 0 < 1 - 4 * d := by linarith
  have hcoef : p ^ 2 + 4 * p * d - 2 * p + d ≤ 0 := by
    have h1 := mul_nonneg (show 0 ≤ 4 * p + 1 by linarith)
      (sub_nonneg.mpr hcredit)
    have h2 := mul_nonneg hp (sq_nonneg (2 * p - 1))
    nlinarith only [h1, h2]
  by_cases hm : 0 ≤ fourThirdsDiscriminant p d
  · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) hcoef
    have hdisc : 0 ≤ (1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
        (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2 := by
      have hid := fourThirds_boundary_discriminant_identity p d q hq0
      have hqdisc : 0 ≤ q * ((1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
          (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2) := by
        nlinarith only [hid, hm, h1]
      exact nonneg_of_mul_nonneg_right hqdisc hqpos
    have hr : 0 ≤ fourThirdsBoundaryOverlap p d q := by
      have hprod : 0 ≤ (1 - 4 * d) * fourThirdsBoundaryOverlap p d q := by
        nlinarith [sq_nonneg (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q)]
      exact nonneg_of_mul_nonneg_right hprod hB
    apply edge_nonnegative_of_discriminant _ _ _ _ (by linarith) hr
    nlinarith only [hdisc]
  · have hm' : fourThirdsDiscriminant p d < 0 := lt_of_not_ge hm
    obtain ⟨hp3, hd0⟩ := fourThirds_negative_discriminant p d hp hp2 hdlow hcredit hm'
    have hderiv : 0 ≤ (2 - 8 * d) + (20 * d - 8 * p - 1) * z +
        (31 * d + 12 * p - 10) * z ^ 2 := by
      apply polynomial_nonnegative_unit _ _ _ z (by linarith) (by linarith) ?_ hz hz1
      linarith
    have hAL : 0 ≤ 1 - p - 2 * d := by
      have := mul_nonneg (show 0 ≤ 1 - p by linarith) (show 0 ≤ 1 - 2 * p by linarith)
      nlinarith
    have hquadratic : 0 ≤ 1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2 := by
      have h1 := mul_nonneg hAL hz
      have h2 := mul_nonneg (show 0 ≤ 1 - d by linarith) (sq_nonneg z)
      linarith
    have hbase := fourThirds_base_boundary p d z hp hp2 hdlow hd4.le hcredit hz hz1
    have hproduct := mul_nonneg (sub_nonneg.mpr hq)
      (add_nonneg (div_nonneg hderiv (by norm_num : (0 : ℝ) ≤ 3))
        (mul_nonneg hquadratic (sub_nonneg.mpr hq)))
    have hid : fourThirdsBoundaryPolynomial p d q z =
        (16 / 9 : ℝ) * (1 / 4 - d - fourThirdsBaseDelta p d * z -
          fourThirdsBaseOverlap p d * z * (1 - z)) +
        (q - 4 / 3) *
          (((2 - 8 * d) + (20 * d - 8 * p - 1) * z +
              (31 * d + 12 * p - 10) * z ^ 2) / 3 +
            (1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2) * (q - 4 / 3)) := by
      unfold fourThirdsBoundaryPolynomial fourThirdsBaseDelta fourThirdsBaseOverlap
      ring
    have hpoly : 0 ≤ fourThirdsBoundaryPolynomial p d q z := by
      rw [hid]
      exact add_nonneg (mul_nonneg (by norm_num) hbase) hproduct
    rw [← fourThirds_boundary_polynomial p d q z hq0] at hpoly
    exact nonneg_of_mul_nonneg_right hpoly (sq_pos_of_pos hqpos)

end
