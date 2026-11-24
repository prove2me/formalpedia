-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.E3cut_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:15.413367+00:00
-- url     : https://prove2.me/submissions/891a7b1d-ee97-4450-8e5c-e993ac003f0e

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
theorem _root_.solution (K L t : ℝ) : TruncationCutoff K L t ≤ 1 := by
  unfold TruncationCutoff
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
end Formalism.HermitianLatticeCounting.P
