-- Prove2me | solution 1 for CompanionTheory.Zuck.mAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:48.551044+00:00
-- url     : https://prove2.me/submissions/8c38628a-f10a-4d83-9af5-2f0fe17ea815

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
theorem _root_.solution {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]
end CompanionTheory.Zuck
