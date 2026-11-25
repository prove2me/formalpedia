-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:26.677835+00:00
-- url     : https://prove2.me/submissions/f0b0b4e5-db43-419c-b3f5-2f744c7f55ee

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_closedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_pow_mem

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
theorem _root_.solution (S : Submodule ℂ W) {A : W →L[ℂ] W} (hA : ∀ v ∈ S, A v ∈ S) : ∀ v ∈ S, NormedSpace.exp A v ∈ S := by
  intro v hv
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have h2 := (ContinuousLinearMap.apply ℂ W v).hasSum h
  refine (closedS S).mem_of_tendsto h2 (Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  show ((((n.factorial : ℂ)⁻¹) • A ^ n : W →L[ℂ] W)) v ∈ S
  exact S.smul_mem _ (pow_mem S hA n v hv)
end Formalism.FourierDecayAlt.P.SkewHermitianParts
