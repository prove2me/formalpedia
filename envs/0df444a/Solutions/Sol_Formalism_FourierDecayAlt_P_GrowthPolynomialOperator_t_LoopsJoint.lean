-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_LoopsJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.564435+00:00
-- url     : https://prove2.me/submissions/46de0710-f365-4b8b-afd7-4517fc218e24

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : LoopsJoint := by
  intro hND hDS hS0 hGS hB3 C hC
  obtain ⟨K1, h1⟩ := hND C hC
  obtain ⟨K2, h2⟩ := hDS C hC
  obtain ⟨K3, h3⟩ := hS0 C hC
  refine ⟨max K1 (max K2 K3), ?_⟩
  intro τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hP hXi hx hdd hIn
  have mono : ∀ K : ℝ, K ≤ max K1 (max K2 K3) →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K k (2 * r + 2) f b g v NT Gam := by
    intro K hK
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, le_trans ?_ p6, p7⟩
    have hl : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have : 0 ≤ (((2 * r + 2 : ℕ) : ℝ)) ^ 5 * f * Real.log b := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hK this]
  have q1 := h1 k (2 * r + 2) f b g v NT Gam Xi (mono K1 (le_max_left _ _)) hXi
  have q2 := h2 k (2 * r + 2) f b g v NT Gam Xi
    (mono K2 (le_trans (le_max_left _ _) (le_max_right _ _))) hXi
  have q3 := h3 k r f b g v NT Gam (mono K3 (le_trans (le_max_right _ _) (le_max_right _ _)))
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hP
  have hk1 : 1 ≤ k := by omega
  have q1' := le_trans q1 (hGS k f b g hk1 (by linarith) p5)
  have hG : 0 < Gam ^ 2 := by positivity
  have q2' : Gam ^ 2 * ∑ s ∈ Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
    calc _ ≤ Gam ^ 2 * (Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left q2 hG.le
      _ = _ := by field_simp
  have q4 := hB3 A ((k : ℝ) * f * Real.log k) hA hx
  unfold Terms.RowLoops
  refine le_trans hIn ?_
  refine mul_le_mul_of_nonneg_right ?_ hdd
  have e3 : Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k)) =
      Real.exp (-((k : ℝ) * f * Real.log k) / 3) := by congr 1; ring
  rw [e3]
  refine le_trans ?_ q4
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  linarith
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
