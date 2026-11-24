-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Good.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:08.650161+00:00
-- url     : https://prove2.me/submissions/a68c71a3-c487-4be8-a81e-4197789f0c37

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace Good
theorem _root_.solution {p : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (D.ML × Fin D.r) K)
    (h : ∀ i ∈ s, D.Good p (f i)) : D.Good p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero D p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Good.add D (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Good
end Formalism.MainNotions.PlaneGram.TwistData
