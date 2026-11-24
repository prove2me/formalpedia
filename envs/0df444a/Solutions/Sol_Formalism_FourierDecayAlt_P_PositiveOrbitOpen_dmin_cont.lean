-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:45:24.7578+00:00
-- url     : https://prove2.me/submissions/e42a1aa7-8a83-4db0-9ef8-c371f3bb8357

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_zhat_cont

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
omit [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  exact ((zhat_cont z z').matrix_submatrix _ _).matrix_det
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
