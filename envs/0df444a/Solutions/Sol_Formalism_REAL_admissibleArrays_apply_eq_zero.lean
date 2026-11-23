-- Prove2me | solution 1 for Formalism.REAL.admissibleArrays_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:38.8995+00:00
-- url     : https://prove2.me/submissions/74ecb91b-6420-4686-89e1-3337a2ef1e1d

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_mem_admissibleArrays

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
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n j}
    (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) (hα : ¬ ∀ i, ε (α i).1 ≠ ε (α i).2) :
    F α = 0 := by
  have h := (mem_admissibleArrays ε E u F).1 hF α
  rw [if_neg hα, Submodule.mem_bot] at h
  exact h
end Formalism.REAL
