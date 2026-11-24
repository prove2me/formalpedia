-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:10:45.654408+00:00
-- url     : https://prove2.me/submissions/74cdaf2e-1955-408a-90e3-c90698c93155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  rw [gb_herm hv, gb_herm hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_mul', star_star, star_neg, star_one] <;> ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
