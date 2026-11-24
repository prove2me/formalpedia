-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:01.716802+00:00
-- url     : https://prove2.me/submissions/d2f949d4-aebb-4be8-abff-92af53e36cf0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = ∑ s, star (w s) * Hpk k r s q := by
  unfold herm bvec
  simp only [dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
