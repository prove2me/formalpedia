-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.mul_apply_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:12.584801+00:00
-- url     : https://prove2.me/submissions/3ff587a7-b741-49ff-84ea-c8cc5f039343

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
    (hg : col k r g) (hh : col k r h) (i j : Fin (2 * r + k + 1)) (hir : i.val < r)
    (hj : j.val ≤ r + k) (hij : i.val < j.val) (hji : j.val ≤ i.val + 1 ∨ r ≤ i.val + 1) :
    (g * h) i j = g i j + h i j := by
  have hij' : j ≠ i := fun e => by subst e; omega
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add j i hij']
  · rw [hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one, hg i i (by omega) (Or.inl le_rfl), if_pos rfl,
      one_mul]
  · rintro p ⟨hpj, hpi⟩
    by_cases h1 : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hh p j hj h1, if_neg hpj, mul_zero]
    · by_cases h2 : p.val ≤ i.val
      · rw [hg i p (by omega) (Or.inl h2), if_neg (Ne.symm hpi), zero_mul]
      · exfalso
        omega
end Formalism.QuantumDeterminants.WeylGroupFacts
