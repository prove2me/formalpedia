-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:33.86734+00:00
-- url     : https://prove2.me/submissions/9799dc22-5805-433a-8be5-55969be7c611

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGLR_mapCoord
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) (nu : Fin n → ℤ) (x : M.ι → ℚ) {R' : Type} [CommRing R'] [Algebra ℚ R']
    (g : GL (Fin n) R') (i : M.ι) :
    evGLR (R := ℚ) g (qb_ev M ℚ nu x i) =
      Matrix.mulVec ((prMu M nu).map (Int.castRingHom R'))
        (Matrix.mulVec (M.A.map (evGL g)) (fun l => algebraMap ℚ R' (x l))) i := by
  rw [qb_ev_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast, qd_evGLR_mapCoord, qd_ev_algebraMap,
    Matrix.map_apply, Int.coe_castRingHom]
end Formalism.InvariantFactorPaths.ColumnFamilies
