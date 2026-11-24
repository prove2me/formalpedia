-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.cT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:27:53.648424+00:00
-- url     : https://prove2.me/submissions/1480315e-446e-4086-84ab-5d51bd29c34c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_kc_sum


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
theorem _root_.solution (i : J k r) (X g : Mat k r) : cT i X g = ∑ j, coL j g * qL i X j g := by
  have hs : -(Hpk k r * gᴴ * Hpk k r * X * g) = ∑ j, co g j • (-(Hpk k r * gᴴ * Hpk k r * X * Eb j)) := by
    have h1 : Hpk k r * gᴴ * Hpk k r * X * g = Hpk k r * gᴴ * Hpk k r * X * Mv (co g) := by rw [Mv_co]
    rw [h1, Mv_sum, Matrix.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, smul_neg]
  unfold cT
  rw [hs, kc_sum]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.LeftToRightConversion
