-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_herm_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:12.337435+00:00
-- url     : https://prove2.me/submissions/ccfbdb7a-acdf-42d8-ba58-ca5ab223836f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_herm_bvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) {p : Fin (2 * r + k + 1)}
    (hp : p.val < r ∨ r + k < p.val) : herm (Hpk k r) (bvec p) w = 0 := by
  rw [sv_herm_bvec]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hw i hi, star_zero, zero_mul]
  · have h0 : Hpk k r i p = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, mul_zero]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
