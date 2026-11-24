-- Prove2me | solution 1 for Formalism.REAL.admissibleArrays_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:09.974208+00:00
-- url     : https://prove2.me/submissions/b05b377c-bf98-4199-b25e-d5ccfca3cfe4

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_mem_admissibleArrays
import Theorems.Thm_Formalism_REAL_pointwiseAction_mem_admissibleArrays

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) :
    KStable ε (arrE E j) (arrV0 ε E u j) := by
  intro a b hab F hF
  first
    | simp only [arrE, LinearMap.add_apply, LinearMap.sum_apply]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_fn_sum, Finset.sum_apply]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => factorAction_mem_admissibleArrays hF i hab) (pointwiseAction_mem_admissibleArrays hF hab)
end Formalism.REAL
