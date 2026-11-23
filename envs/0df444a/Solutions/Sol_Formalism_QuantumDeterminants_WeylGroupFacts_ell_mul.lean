-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.ell_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:03.759434+00:00
-- url     : https://prove2.me/submissions/4cbd43c2-d54d-4d99-99f7-ad76665d6ab2

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mul_apply_add

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : ell k r z (g * h) = ell k r z g + ell k r z h := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have ha := a.isLt
  by_cases h1 : a.val + 1 < r
  · simp only [dif_pos h1]
    exact mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt)
      (by show a.val + 1 ≤ r + k; omega) (by show a.val < a.val + 1; omega)
      (by show a.val + 1 ≤ a.val + 1 ∨ r ≤ a.val + 1; omega)
  · simp only [dif_neg h1]
    first
      | simp only [Matrix.mulVec, dotProduct]
      | simp only [Matrix.mulVec, Matrix.dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : q.val < r ∨ r + k < q.val
    · rw [hz q hq]
      simp
    · rw [mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt) (by omega)
        (by show a.val < q.val; omega) (Or.inr (by show r ≤ a.val + 1; omega)), add_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
