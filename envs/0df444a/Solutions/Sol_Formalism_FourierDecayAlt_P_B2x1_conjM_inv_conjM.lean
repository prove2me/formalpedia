-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.conjM_inv_conjM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:21.751852+00:00
-- url     : https://prove2.me/submissions/b6d61460-60cd-4cfe-904f-8d24f1f688b0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_conjM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution (a : Mat k r) (ha : IsUnit a.det) (x : Mt k r) : conjM a⁻¹ (conjM a x) = x := by
  rw [conjM_conjM, Matrix.nonsing_inv_mul a ha]
  show (1 : Mat k r) * Matrix.of x * (1 : Mat k r)⁻¹ = x
  rw [inv_one, Matrix.one_mul, Matrix.mul_one]; rfl
end Formalism.FourierDecayAlt.P.B2x1
