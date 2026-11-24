-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.Tl_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:22.774365+00:00
-- url     : https://prove2.me/submissions/df1d2439-2b8a-4012-a8cf-c348135a0ebe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_mulVec_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_unitary_levi_det_norm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (g₁ : Mat k r') (hg : g₁ ∈ GV k r') :
    MeasurePreserving (Tl k r' g₁) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by
  have hdet := unitary_levi_det_norm_one g₁ hg
  have hne : g₁.det ≠ 0 := by intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hmv : MeasurePreserving (fun y : Fin (2 * r' + k + 1) → ℂ => g₁ *ᵥ y) volume volume :=
    ⟨(continuous_const.matrix_mulVec continuous_id).measurable, by rw [map_mulVec_volume g₁ hne, hdet]; simp⟩
  exact (MeasurePreserving.id μx).prod (hmv.prod (MeasurePreserving.id (volume : Measure ℝ)))
end Formalism.FourierDecayAlt.P.B2x8
