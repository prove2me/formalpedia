-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.colon_count_weighted_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:23.229891+00:00
-- url     : https://prove2.me/submissions/9f5624c3-d91e-4bc5-89e5-1c99f5f1e7bf

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_cCount_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CCountWAsm := by
  intro hI hT E _ _ f D hf
  have h := DualLatticeIndexBis.cCount_of E f D _ (hT E f hf) (hI E f D hf)
  have e : 2 * (1 + (1 + Real.logb 2 (2 * (f : ℝ)))) = 2 + 2 * (1 + Real.logb 2 (2 * (f : ℝ))) := by ring
  rw [e] at h
  exact h
end Formalism.HermitianLatticeCounting.P
