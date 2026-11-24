-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.adj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:53.331804+00:00
-- url     : https://prove2.me/submissions/136c3b79-c382-4f3b-8e4a-353262a12f93

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {τ : ℝ} (hτ : τ ≠ 0) (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    ((aDil k r τ)⁻¹ * X * aDil k r τ) i j = dg k r τ⁻¹ i * X i j * dg k r τ j := by
  rw [aDil_inv k r τ hτ, aDil_eq, aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
end Formalism.FourierDecayAlt.P.B4
