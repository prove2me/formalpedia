-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.col_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:11.304797+00:00
-- url     : https://prove2.me/submissions/09a103cb-d70f-4d71-8396-2f00a98a2496

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
theorem _root_.solution {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : col k r (g * h) := by
  intro i j hj hij
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · rw [hg i j hj hij, hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one]
  · intro p hp
    by_cases hpj : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hh p j hj hpj, if_neg hp, mul_zero]
    · have hz : g i p = 0 := by
        rw [hg i p (by omega) (by omega), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
