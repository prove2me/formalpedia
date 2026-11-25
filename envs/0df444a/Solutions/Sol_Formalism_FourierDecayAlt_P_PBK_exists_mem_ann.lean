-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.exists_mem_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:23.325464+00:00
-- url     : https://prove2.me/submissions/7fe45e10-5df4-4f7c-98f9-04c7dd794181

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {D : ℂ} (hD : D ≠ 0) : ∃ n, D ∈ ann n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  refine ⟨n, ?_, ?_⟩
  · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
      (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    exact inv_le_of_inv_le₀ hpos h1
  · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
end Formalism.FourierDecayAlt.P.PBK
