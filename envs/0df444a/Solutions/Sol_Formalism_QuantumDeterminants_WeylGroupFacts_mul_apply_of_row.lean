-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mul_apply_of_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:06.900277+00:00
-- url     : https://prove2.me/submissions/8e932c58-5538-4f98-89cd-905f7dd5b3e6

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  · rw [hrow i, if_pos rfl, one_mul]
  · intro p hp
    rw [hrow p, if_neg (Ne.symm hp), zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
