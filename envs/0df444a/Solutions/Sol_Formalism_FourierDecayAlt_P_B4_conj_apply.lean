-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:58.34407+00:00
-- url     : https://prove2.me/submissions/34823895-c665-42fa-b404-276cce65d027

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (n : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (aDil k r t * n * (aDil k r t)⁻¹) i j = dg k r t i * n i j * dg k r t⁻¹ j := by
  rw [aDil_inv k r t ht, aDil_eq, aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
end Formalism.FourierDecayAlt.P.B4
