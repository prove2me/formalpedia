-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.col_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:01.701627+00:00
-- url     : https://prove2.me/submissions/471a447d-1fa3-4f79-a3d5-b32c7c27479f

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
theorem _root_.solution {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hm : g' * g = 1) : col k r g' := by
  suffices H : ∀ n : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val = n → j.val ≤ r + k →
      (j.val ≤ i.val ∨ r ≤ i.val) → g' i j = if i = j then 1 else 0 by
    intro i j hj hij
    exact H j.val i j rfl hj hij
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro i j hjn hj hij
  have h1 : (g' * g) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
    rw [hm]
  rw [Matrix.mul_apply, Fintype.sum_eq_single j] at h1
  · rw [hg j j hj (Or.inl le_rfl), if_pos rfl, mul_one, Matrix.one_apply] at h1
    exact h1
  · intro p hp
    by_cases hpj : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p j hj hpj, if_neg hp, mul_zero]
    · have hz : g' i p = 0 := by
        rw [ih p.val (by omega) i p rfl (by omega) (by omega), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
