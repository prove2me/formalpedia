-- Prove2me | solution 1 for Formalism.REAL.mem_symmetricArrays
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:07.046531+00:00
-- url     : https://prove2.me/submissions/77f90ea0-6b0b-4e53-be37-3706f3161a6c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (F : Arr V n j) :
    F ∈ symSub V n j ↔ ∀ σ : Equiv.Perm (Fin j), permArr V n σ F = F := by
  simp [symSub, sub_eq_zero]
end Formalism.REAL
