-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:10:41.347452+00:00
-- url     : https://prove2.me/submissions/9f21d548-2dab-4366-b613-a78f4222a6b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_entry

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
theorem _root_.solution {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    Hpk k r *ᵥ v = fun i => (if i.val = r + k then -1 else 1) * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [gb_entry hi.1 hi.2, if_pos rfl]
    · rw [hv i (by omega)]; ring
  · intro b _ hb
    by_cases hb' : r ≤ b.val ∧ b.val ≤ r + k
    · rw [gb_entry hb'.1 hb'.2, if_neg (Ne.symm hb)]; ring
    · rw [hv b (by omega)]; ring
  · intro h; exact absurd (Finset.mem_univ i) h
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
