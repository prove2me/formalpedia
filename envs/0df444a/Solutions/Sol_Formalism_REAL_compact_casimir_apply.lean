-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:02.480085+00:00
-- url     : https://prove2.me/submissions/f5645634-686c-495e-a2d0-51c45d8e0e27

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (y : V) :
    CasK ε F y = ∑ a, ∑ b, if ε a = ε b then F a b (F b a y) else 0 := by
  unfold CasK
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> rfl
end Formalism.REAL
