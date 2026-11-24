-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.aDil_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:02.603354+00:00
-- url     : https://prove2.me/submissions/9b983bba-dcb7-4906-8302-c199d6188e4a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mul_inv

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
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [aDil_eq, aDil_eq, Matrix.diagonal_mul_diagonal]
  have e : (fun i => dg k r t⁻¹ i * dg k r t i) = fun _ => (1 : ℂ) := by
    funext i
    rw [mul_comm]
    exact dg_mul_inv k r t ht i
  rw [e, Matrix.diagonal_one]
end Formalism.FourierDecayAlt.P.B4
