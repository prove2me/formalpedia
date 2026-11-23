-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mul_apply_of_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:06.715164+00:00
-- url     : https://prove2.me/submissions/58920fa4-3dbc-4048-8a17-6eee118da2f5

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
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · rw [hcol j, if_pos rfl, mul_one]
  · intro q hq
    rw [hcol q, if_neg hq, mul_zero]
end Formalism.QuantumDeterminants.WeylGroupFacts
