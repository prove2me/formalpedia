-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.op_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:19.192618+00:00
-- url     : https://prove2.me/submissions/73fd49b3-c965-47a4-b7bc-1cfc42ca7b56

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_rw_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordIntegralScaling_smul_list


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution (Θ : DiffOp k r Wp Wq) (c : ℂ) (f : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    opApply Θ (c • f) x = c • opApply Θ f x := by
  unfold opApply
  rw [WordIntegralScaling.smul_list]
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_smul, Pi.smul_apply]
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
