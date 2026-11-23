-- Prove2me | solution 1 for Formalism.REAL.sandwich_alternating_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:15.428805+00:00
-- url     : https://prove2.me/submissions/4bfa8bad-8698-4219-8e37-f9d859962046

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
theorem _root_.solution {A : Type*} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R + L * a3 * R - L * a4 * R = L * (a1 - a2 + a3 - a4) * R := by
  simp only [mul_sub, mul_add, sub_mul, add_mul]
end Formalism.REAL
