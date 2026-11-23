-- Prove2me | solution 1 for Formalism.REAL.height_functional_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:41.255802+00:00
-- url     : https://prove2.me/submissions/16d1b597-3e17-46c9-aecb-e35cbd0f9fa4

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
theorem _root_.solution {m : ℕ} (c d : Fin m) :
    heightFunctional (Pi.single c (1 : ℝ) - Pi.single d 1) = (c : ℝ) - d := by
  simp [heightFunctional, Pi.single_apply, mul_sub, sum_sub_distrib]
end Formalism.REAL
