-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.lower_left_commute_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:59.683801+00:00
-- url     : https://prove2.me/submissions/1001d8e3-fbdc-4658-a2cb-4fd65e56c5c0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_compC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hC : SSComm) (hN : NabSS) (hLN : LevNab) (hLF : LevFns)
    (hR : RhoUp) : T21Commute := by
  intro P hP u v
  show t21 P u * t21 P v = t21 P v * t21 P u
  have hA := compA hLN hLF P u v
  have hB : (ggA P * xA P u * l0A P u) * weightedSumBis P v + weightedSumBis P u * (ggA P * xA P v * l0A P v) =
      (ggA P * xA P v * l0A P v) * weightedSumBis P u + weightedSumBis P v * (ggA P * xA P u * l0A P u) := by
    unfold weightedSumBis
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l hl => compB hSc hSh hN hR P u v l hl)
  have hCC := compC hSh hC hR P hP u v
  unfold t21
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hA, hCC]
  calc _ = (ggA P * xA P v * l0A P v) * (ggA P * xA P u * l0A P u) +
        ((ggA P * xA P u * l0A P u) * weightedSumBis P v + weightedSumBis P u * (ggA P * xA P v * l0A P v)) +
        weightedSumBis P v * weightedSumBis P u := by abel
    _ = _ := by rw [hB]; abel
end Formalism.FourierDecayAlt.P.Mx7
