-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.polyClass_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:10.81025+00:00
-- url     : https://prove2.me/submissions/ab7ddf16-ae2f-44eb-9265-4fdf12be0776

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_cT_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
theorem _root_.solution (i : J k r) (X : Mat k r) : PolyClass 2 (cT i X) := by
  have e : cT i X = fun g => ∑ j, coL j g * qL i X j g := funext (cT_eq i X)
  rw [e]
  exact polyClass_sum _ _ _ fun j _ => polyClass_mul (polyClass_lin (coL j)) (polyClass_lin (qL i X j))
end Formalism.FourierDecayAlt.P.LeftToRightConversion
