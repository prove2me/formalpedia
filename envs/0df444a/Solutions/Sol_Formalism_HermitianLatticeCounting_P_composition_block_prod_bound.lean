-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.composition_block_prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:13.754599+00:00
-- url     : https://prove2.me/submissions/6066c98a-1002-4884-b89b-42295180eaa0

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_list_prod_le_exp_sum_div_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.CompositionBlockProdBound := by
  intro n c
  have h := list_prod_le_exp_sum_div_e c.blocks
  rwa [c.blocks_sum] at h
end Formalism.HermitianLatticeCounting.P
