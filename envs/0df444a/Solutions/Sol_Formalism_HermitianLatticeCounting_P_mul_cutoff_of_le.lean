-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mul_cutoff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:09.958648+00:00
-- url     : https://prove2.me/submissions/7c815dcb-411b-4881-9f99-8cc0fff14d81

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
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K L y : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (h : y ≤ L) : y * TruncationCutoff K L y = y := by
  have h1 : (1 : ℝ) ≤ (L / y) ^ K := Real.one_le_rpow ((one_le_div hy).2 h) hK
  rw [TruncationCutoff, if_neg hy.ne', min_eq_left h1, mul_one]
end Formalism.HermitianLatticeCounting.P
