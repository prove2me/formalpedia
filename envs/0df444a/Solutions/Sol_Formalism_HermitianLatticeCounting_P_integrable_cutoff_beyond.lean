-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integrable_cutoff_beyond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.540003+00:00
-- url     : https://prove2.me/submissions/966f96e8-e877-455f-95f2-cd887fb1dab9

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mul_cutoff_of_gt

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
theorem _root_.solution {K L : ℝ} (hK : 2 < K) (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioi L) :=
  (integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_gt (by linarith) hL hy).symm) measurableSet_Ioi).1
    ((integrableOn_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL).const_mul (L ^ K))
end Formalism.HermitianLatticeCounting.P
