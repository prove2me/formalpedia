-- Prove2me | solution 1 for Formalism.L2.DIV.quotFrameIsQuot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:00.12871+00:00
-- url     : https://prove2.me/submissions/cbf0e2b3-e4ff-4696-adc8-8c966ea84f01

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_map_surj
import Theorems.Thm_Formalism_L2_DIV_frameOfSpec
import Theorems.Thm_Formalism_L2_DIV_quotRestrPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : QuotFrameIsQuot := by
  intro K _ _ _ n D H h2 P hP v
  exact frameOfSpec D _ ((quotRestrPosDef n D _ (h2 v)).1 _ (map_surj _ P hP))
end Formalism.L2.DIV
