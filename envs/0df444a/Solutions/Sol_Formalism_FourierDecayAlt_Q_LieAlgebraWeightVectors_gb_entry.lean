-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:50:40.897801+00:00
-- url     : https://prove2.me/submissions/57d8d44d-cfe6-4c58-8917-24f286a75d2d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector

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
theorem _root_.solution {i j : Fin (2 * r + k + 1)} (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r i j = if i = j then (if j.val = r + k then -1 else 1) else 0 := by
  simp only [Hpk]
  by_cases h : i = j
  · subst h
    have h1 : ¬ (i.val < r ∧ i.val + i.val = 2 * r + k) := by omega
    rw [if_neg h1, if_neg h1, if_pos ⟨hj, hj', rfl⟩, if_pos rfl]
  · have h1 : ¬ (i.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h2 : ¬ (j.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := fun hh => h hh.2.2
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
