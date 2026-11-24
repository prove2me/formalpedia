-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integrable_cutoff_below
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.01557+00:00
-- url     : https://prove2.me/submissions/75a901f1-ec90-43c1-91f7-7685c4a357e7

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mul_cutoff_of_le

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
theorem _root_.solution {K L : ℝ} (hK : 0 ≤ K) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioc 0 L) :=
  (integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_le hK hy.1 hy.2).symm) measurableSet_Ioc).1
    (continuous_id.integrableOn_Ioc)
end Formalism.HermitianLatticeCounting.P
