-- Prove2me | solution 1 for Formalism.REAL.compactCasimir_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:09.284591+00:00
-- url     : https://prove2.me/submissions/8273ed09-7932-455a-9e04-8809a5c5c713

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ W) (x : W) :
    CasK ε T x = ∑ a, ∑ b, if ε a = ε b then T a b (T b a x) else 0 := by
  first
    | simp only [CasK, LinearMap.sum_apply]
    | simp only [CasK, LinearMap.coe_sum, Finset.sum_apply]
    | simp only [CasK, LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> rfl
end Formalism.REAL
