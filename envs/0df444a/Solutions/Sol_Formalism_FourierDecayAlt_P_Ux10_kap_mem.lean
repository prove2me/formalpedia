-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.kap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:27.201794+00:00
-- url     : https://prove2.me/submissions/4df162bb-e655-4d4d-ab56-cb1dfc08320b

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_UpperTheory_Reformulated_B_Qk20_kap_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {Y : Mat k r} (hY : inLie k r Y) (hu : IsUnit (1 - Y).det) : kap Y ∈ GV k r := by
  first | exact UpperTheory.Reformulated.B.Qk20.kap_mem .. | (apply UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y hY hu | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y hY | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k
end Formalism.FourierDecayAlt.P.Ux10
