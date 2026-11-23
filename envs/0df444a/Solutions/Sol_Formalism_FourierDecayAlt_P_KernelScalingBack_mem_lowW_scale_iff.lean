-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.mem_lowW_scale_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:45.839213+00:00
-- url     : https://prove2.me/submissions/cf1801c7-3cba-48bb-ba47-8b8ebfcae9f3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution {g : GL (Fin S.sum) K} : g ∈ lowW K S (T * c) ↔ g ∈ lowW K S T := by
  refine ⟨fun hg => ?_, mem_lowW_scale S T c⟩
  have := mem_lowW_scale S (T * c) c⁻¹ hg
  rwa [mul_inv_cancel_right] at this
end Formalism.FourierDecayAlt.P.KernelScalingBack
