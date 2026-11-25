-- Prove2me | solution 1 for CompanionTheory.Zuck.uM_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:07.235593+00:00
-- url     : https://prove2.me/submissions/f296ece0-0dd0-4442-8e9d-690d00b67e17

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution (F : FRep k r) (g : Mx k r) : uM F.ι * F.ρ g = ((triv k r).tens F).ρ g * uM F.ι := by
  ext ⟨_, c⟩ d
  simp [Matrix.mul_apply, uM, Fintype.sum_prod_type]
end CompanionTheory.Zuck
