-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.tendsto_inv_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:37:40.374666+00:00
-- url     : https://prove2.me/submissions/2888e489-5618-448f-bbaf-d09208e2b47d

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL

set_option autoImplicit false

open Filter Topology in
theorem solution : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat
