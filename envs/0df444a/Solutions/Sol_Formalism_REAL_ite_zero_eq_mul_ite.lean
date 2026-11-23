-- Prove2me | solution 1 for Formalism.REAL.ite_zero_eq_mul_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:04.847439+00:00
-- url     : https://prove2.me/submissions/9270b448-7b18-46bc-b172-bbd50102f7e9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (P : Prop) [Decidable P] (x : ℂ) :
    (if P then x else 0) = x * (if P then 1 else 0) := by
  split_ifs <;> simp
end Formalism.REAL
