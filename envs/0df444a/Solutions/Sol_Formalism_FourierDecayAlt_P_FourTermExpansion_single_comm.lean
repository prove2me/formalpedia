-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.single_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:06.585134+00:00
-- url     : https://prove2.me/submissions/e94cf7f6-d663-4ee0-a65f-476282f1e3a3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (a b c d : Fin (2 * r + k + 1)) :
    Msg k r a b * Msg k r c d - Msg k r c d * Msg k r a b =
      (if b = c then (1 : ℂ) else 0) • Msg k r a d + (-(if d = a then (1 : ℂ) else 0)) • Msg k r c b := by
  ext i j
  simp only [Msg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply,
    smul_eq_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  split_ifs <;> simp_all
end Formalism.FourierDecayAlt.P.FourTermExpansion
