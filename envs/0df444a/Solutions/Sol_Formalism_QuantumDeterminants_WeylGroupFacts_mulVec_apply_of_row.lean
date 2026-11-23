-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:06.259922+00:00
-- url     : https://prove2.me/submissions/a303904f-e48e-4ed6-98ec-2b4c80b7e130

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
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  first
    | simp only [Matrix.mulVec, dotProduct]
    | simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [Fintype.sum_eq_single i]
  · rw [hrow i, if_pos rfl, one_mul]
  · intro p hp
    rw [hrow p, if_neg (Ne.symm hp), zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
