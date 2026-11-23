-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.DGam_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:54.645361+00:00
-- url     : https://prove2.me/submissions/36422413-c0ee-4da0-9e32-a570afca13d0

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_wt_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution : 0 < S.DGam := by
  refine Nat.pos_of_ne_zero ?_
  unfold DGam
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨c, -, hc⟩
  exact (S.wt_pos c).ne' hc
end Formalism.L2.DIV.CSD
