-- Prove2me | solution 1 for Formalism.REAL.mem_admissibleArrays
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:02.197728+00:00
-- url     : https://prove2.me/submissions/897922a9-a3aa-4cf4-8c3b-607913a87904

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (u : V) (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by
  simp only [arrV0, Submodule.mem_iInf, Submodule.mem_comap]
  rfl
end Formalism.REAL
