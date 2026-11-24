-- Prove2me | solution 1 for Formalism.REAL.arr_module_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:06.675135+00:00
-- url     : https://prove2.me/submissions/2d7cefd1-effa-42ed-9f19-e794bc1f258b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_arr_operators_gl_relation
import Theorems.Thm_Formalism_REAL_arr_operators_compact_unitary
import Theorems.Thm_Formalism_REAL_symmetrization_equivariant

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
namespace Formalism.REAL
theorem _root_.solution : ArrModule := by
  intro V _ _ n ε E j
  exact ⟨fun hE => ⟨arr_operators_gl_relation E hE, fun c d F => symmetrization_equivariant E hE c d F⟩,
    fun hU => arr_operators_compact_unitary ε E hU⟩
end Formalism.REAL
