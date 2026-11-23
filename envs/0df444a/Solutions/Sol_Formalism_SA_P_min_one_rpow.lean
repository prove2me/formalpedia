-- Prove2me | solution 1 for Formalism.SA.P.min_one_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:27.440593+00:00
-- url     : https://prove2.me/submissions/3ee5e628-32ab-48bf-affa-938481473aca

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) : min 1 (a ^ K) = (min 1 a) ^ K := by
  rcases le_or_gt a 1 with h | h
  · rw [min_eq_right h, min_eq_right (Real.rpow_le_one ha.le h hK)]
  · rw [min_eq_left h.le, Real.one_rpow, min_eq_left (Real.one_le_rpow h.le hK)]
end Formalism.SA.P
