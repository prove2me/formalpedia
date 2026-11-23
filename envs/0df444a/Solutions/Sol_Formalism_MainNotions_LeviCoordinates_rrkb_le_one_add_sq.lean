-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_le_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:59.823395+00:00
-- url     : https://prove2.me/submissions/f9722db5-c4e5-4617-b105-1be82873ebca

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact le_trans h le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ 1 + a ^ 2 := le_add_self
end Formalism.MainNotions.LeviCoordinates
