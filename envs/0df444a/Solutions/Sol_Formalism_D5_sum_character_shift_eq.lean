-- Prove2me | solution 1 for Formalism.D5.sum_character_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:32.818787+00:00
-- url     : https://prove2.me/submissions/e83fc14a-f410-4bc0-bb9d-4103cc2cacc2

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_zmod_two_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5
theorem _root_.solution (ψ : AddChar (E0 × H) ℂ) (s t : H) :
    ∑ u0 : H, ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H))
      = ψ e10 * ∑ h : H, ψ ((0, 0), h) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft (t - s)) _ _ (fun u0 => ?_)
  show ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) = ψ e10 * ψ ((0, 0), t - s - u0)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · first
      | (show -(1 : ZMod 2) = 1 + 0; decide)
      | (simp [e10, zmod_two_neg_one]; done)
  · first
      | (show -(0 : ZMod 2) = 0 + 0; decide)
      | (simp [e10]; done)
  · show -(s + u0 - t) = (0 : H) + (t - s - u0)
    abel
end Formalism.D5
