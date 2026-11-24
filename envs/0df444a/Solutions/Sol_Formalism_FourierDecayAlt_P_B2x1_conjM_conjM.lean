-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.conjM_conjM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:51.262853+00:00
-- url     : https://prove2.me/submissions/dc8bb133-5e06-45de-b056-190ab99bf97f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible

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
theorem _root_.solution (a b : Mat k r) (x : Mt k r) : conjM a (conjM b x) = conjM (a * b) x := by
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = (a * b) * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.B2x1
