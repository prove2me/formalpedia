-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.block_mul_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:06.131864+00:00
-- url     : https://prove2.me/submissions/599ac38d-3e10-4354-8eaf-24624ff449d1

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
theorem _root_.solution {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q := by
  unfold block at hh
  rw [Matrix.mul_apply, Fintype.sum_eq_single q]
  · rw [hg q q hq (Or.inl le_rfl), if_pos rfl, mul_one]
  · intro p hp
    by_cases h1 : q.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p q hq h1, if_neg hp, mul_zero]
    · have hz : h i p = 0 := by
        rw [hh.1 i p (Or.inl (by omega)), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
