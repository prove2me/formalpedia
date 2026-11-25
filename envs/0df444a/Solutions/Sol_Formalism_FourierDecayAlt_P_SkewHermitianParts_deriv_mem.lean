-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.deriv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:23.84132+00:00
-- url     : https://prove2.me/submissions/ecd2ca46-fdcf-41d4-93ba-83aad7339cf8

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_closedS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution (S : Submodule ℂ W) {f : ℝ → W} {f' : W} (h : HasDerivAt f f' 0) (hf : ∀ t, f t ∈ S) : f' ∈ S := by
  have h1 := h.tendsto_slope_zero
  refine (closedS S).mem_of_tendsto h1 (Eventually.of_forall fun t => ?_)
  exact (S.restrictScalars ℝ).smul_mem _ (S.sub_mem (hf _) (hf _))
end Formalism.FourierDecayAlt.P.SkewHermitianParts
