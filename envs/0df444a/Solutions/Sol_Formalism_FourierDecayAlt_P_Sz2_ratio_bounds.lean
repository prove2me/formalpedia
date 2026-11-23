-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:01.478372+00:00
-- url     : https://prove2.me/submissions/82d1fde3-6f6c-4442-a0aa-7d93e9a0bb2b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution {G2 C0 R du : ℝ} (hG20 : 0 < G2) (hC0 : 1 ≤ C0) (hdu : du ≠ 0)
    (c1 : G2⁻¹ * (R * du) * C0⁻¹ ≤ du) (c2 : du ≤ G2⁻¹ * (R * du) * C0) :
    G2 / C0 ≤ R ∧ R ≤ G2 * C0 := by
  have hC00 : 0 < C0 := by linarith
  have c1' : (R / (G2 * C0)) * du ≤ 1 * du := by
    calc _ = G2⁻¹ * (R * du) * C0⁻¹ := by field_simp
      _ ≤ _ := by rw [one_mul]; exact c1
  have c2' : 1 * du ≤ (R / (G2 / C0)) * du := by
    calc _ = du := one_mul _
      _ ≤ _ := c2
      _ = _ := by field_simp
  have hle : G2 / C0 ≤ G2 * C0 := by
    rw [div_le_iff₀ hC00]
    have h1 : 1 ≤ C0 * C0 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hG20.le
    linarith
  have p1 : 0 < G2 * C0 := by positivity
  have p2 : 0 < G2 / C0 := by positivity
  rcases lt_or_gt_of_ne hdu with hneg | hpos
  · have d1 : 1 ≤ R / (G2 * C0) := by
      by_contra hcon
      have hcon' : R / (G2 * C0) - 1 < 0 := by linarith [not_le.mp hcon]
      have := mul_pos_of_neg_of_neg hneg hcon'
      linarith
    have d2 : R / (G2 / C0) ≤ 1 := by
      by_contra hcon
      have hcon' : 1 - R / (G2 / C0) < 0 := by linarith [not_le.mp hcon]
      have := mul_pos_of_neg_of_neg hneg hcon'
      linarith
    rw [le_div_iff₀ p1] at d1
    rw [div_le_iff₀ p2] at d2
    constructor <;> linarith
  · have d1 : R / (G2 * C0) ≤ 1 := le_of_mul_le_mul_right c1' hpos
    have d2 : 1 ≤ R / (G2 / C0) := le_of_mul_le_mul_right c2' hpos
    rw [div_le_iff₀ p1] at d1
    rw [le_div_iff₀ p2] at d2
    constructor <;> linarith
end Formalism.FourierDecayAlt.P.Sz2
