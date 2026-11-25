-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.HL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:30.672264+00:00
-- url     : https://prove2.me/submissions/a436e0e9-5969-4eb9-a410-168473643e6d

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution {HL X8 Y HM δ D G PH tableDegreeThreeBase PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw L lrw ΛW Sν DF c cg aδ aG1 : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 1 ≤ L) (hG : 0 ≤ G) (hPP0 : 0 ≤ tableDegreeThreeBase) (hPN : 0 ≤ PN) (hP14 : 0 ≤ tableLineDegreeFive)
    (hP16 : 0 ≤ tableLineDegreeTwo) (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hlrw : 0 ≤ lrw) (hw : lrw + 1 / 2 ≤ Prw * L)
    (hPH : tableDegreeThreeBase + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw ≤ PH) (hc1 : c ≤ 1) (hcg0 : 0 ≤ cg) (hcg : cg ≤ 1 / 2)
    (hSν : Sν ≤ PN * L) (hDF : DF ≤ L) (hΛ : ΛW ≤ G * L) (haδ : aδ ≤ 4 / 3 * δ) (haG : aG1 ≤ 4 / 3 * δ)
    (hHM : HM ≤ (D + 1) * δ * (tableDegreeThreeBase * L + ΛW + 1 / 2 * lrw))
    (hX8 : X8 ≤ HM + δ * (Sν + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * cg * aδ * (lrw + 1 / 2))
    (hY : Y ≤ δ * PI4 * D * L + D * aG1 * (lrw + 1 / 2))
    (hHL : HL ≤ 2 * max X8 0 + Y) :
    HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L := by
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ lrw + 1 / 2 := by linarith
  have b1 : HM ≤ (D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) :=
    hHM.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have b2 : δ * (Sν + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) := by
    have i1 : tableLineDegreeFive * DF ≤ tableLineDegreeFive * L := mul_le_mul_of_nonneg_left hDF hP14
    have i2 : c * tableLineDegreeTwo ≤ 1 * tableLineDegreeTwo := mul_le_mul_of_nonneg_right hc1 hP16
    have i3 : tableLineDegreeTwo ≤ tableLineDegreeTwo * L := le_mul_of_one_le_right hP16 hL
    exact mul_le_mul_of_nonneg_left (by linarith) hδ
  have b3 : D * cg * aδ * (lrw + 1 / 2) ≤ D * (1 / 2 * (4 / 3 * δ) * (Prw * L)) := by
    have i1 : cg * aδ ≤ cg * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haδ hcg0
    have i2 : cg * (4 / 3 * δ) ≤ 1 / 2 * (4 / 3 * δ) := mul_le_mul_of_nonneg_right hcg (by positivity)
    have i3 : cg * aδ * (lrw + 1 / 2) ≤ 1 / 2 * (4 / 3 * δ) * (lrw + 1 / 2) :=
      mul_le_mul_of_nonneg_right (i1.trans i2) hw0
    have i4 : 1 / 2 * (4 / 3 * δ) * (lrw + 1 / 2) ≤ 1 / 2 * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have i5 := mul_le_mul_of_nonneg_left (i3.trans i4) hD
    calc D * cg * aδ * (lrw + 1 / 2) = D * (cg * aδ * (lrw + 1 / 2)) := by ring
      _ ≤ _ := i5
  have b4 : Y ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) := by
    have i1 : aG1 * (lrw + 1 / 2) ≤ 4 / 3 * δ * (lrw + 1 / 2) := mul_le_mul_of_nonneg_right haG hw0
    have i2 : 4 / 3 * δ * (lrw + 1 / 2) ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul_of_nonneg_left hw (by positivity)
    have i3 := mul_le_mul_of_nonneg_left (i1.trans i2) hD
    have e : D * aG1 * (lrw + 1 / 2) = D * (aG1 * (lrw + 1 / 2)) := by ring
    linarith
  have hX8b0 : 0 ≤ ((D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) + δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) + D * (1 / 2 * (4 / 3 * δ) * (Prw * L))) := by positivity
  have hmax : max X8 0 ≤ ((D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) + δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) + D * (1 / 2 * (4 / 3 * δ) * (Prw * L))) := max_le (by linarith) hX8b0
  have q0 : 0 ≤ δ * L * (D + 1) * (PH - (tableDegreeThreeBase + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw)) :=
    mul_nonneg (by positivity) (by linarith)
  have qa0 : 0 ≤ δ * L * tableDegreeThreeBase := by positivity
  have qb0 : 0 ≤ δ * L * tableDegreeThreeBase * D := by positivity
  have qa1 : 0 ≤ δ * L * PN := by positivity
  have qb1 : 0 ≤ δ * L * PN * D := by positivity
  have qa2 : 0 ≤ δ * L * tableLineDegreeFive := by positivity
  have qb2 : 0 ≤ δ * L * tableLineDegreeFive * D := by positivity
  have qa3 : 0 ≤ δ * L * tableLineDegreeTwo := by positivity
  have qb3 : 0 ≤ δ * L * tableLineDegreeTwo * D := by positivity
  have qa4 : 0 ≤ δ * L * PI4 := by positivity
  have qb4 : 0 ≤ δ * L * PI4 * D := by positivity
  have qa5 : 0 ≤ δ * L * Prw := by positivity
  have qb5 : 0 ≤ δ * L * Prw * D := by positivity
  linarith
end Formalism.MainNotions.Gaps.T0
