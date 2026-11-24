-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.parametrisation_base_vector_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:53.382746+00:00
-- url     : https://prove2.me/submissions/009b5ad5-727e-4dd7-8b88-2e563bc807ea

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heisenberg_dual_base_vector_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_long_weyl_sends_base_to_dual

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HA : HeisAct) (p : ℂ × HPar k r') : (Matrix.of (tau k r' p) : Mat k (1 + r')) *ᵥ e0 k r' = xi k r' p := by
  change (heis0 k r' p.2 * w0 k r' p.1) *ᵥ e0 k r' = xi k r' p
  rw [← mulVec_mulVec, long_weyl_sends_base_to_dual, mulVec_smul, heisenberg_dual_base_vector_formula HA]
  rfl
end Formalism.FourierDecayAlt.P.B2x9
