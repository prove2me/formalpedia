-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.E3cut_nonneg_of_nonneg_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:15.593278+00:00
-- url     : https://prove2.me/submissions/cb3525ce-02e4-462a-b970-0ab5fe590a2d

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (K L t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) : 0 ≤ TruncationCutoff K L t := by
  unfold TruncationCutoff
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hL ht) K)
end Formalism.HermitianLatticeCounting.P
