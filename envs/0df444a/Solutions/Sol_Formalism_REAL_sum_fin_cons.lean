-- Prove2me | solution 1 for Formalism.REAL.sum_fin_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:30.293103+00:00
-- url     : https://prove2.me/submissions/457373e8-0238-4e7c-8d80-2da67de4f40b

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
theorem _root_.solution {X M : Type*} [Fintype X] [AddCommMonoid M] (f : (Fin (j+1) → X) → M) :
    ∑ α, f α = ∑ α' : Fin j → X, ∑ β : Fin 1 → X, f (Fin.cons (β 0) α') := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (j+1) => X)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun α' _ => ?_
  exact ((Equiv.funUnique (Fin 1) X).sum_comp (fun x => f (Fin.cons x α'))).symm
end Formalism.REAL
