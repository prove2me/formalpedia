-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:10.750126+00:00
-- url     : https://prove2.me/submissions/8779d338-6fd1-42af-bdb8-e3b54eb4c6bc

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
theorem _root_.solution : IotaDetermined := by
  intro K U _ _ _ g L₀ ι₁ ι₂ l' hg0 hmem
  refine ⟨-(g⁻¹ • (l' - ι₁ l') - g⁻¹ • (l' - ι₂ l')), L₀.neg_mem hmem, ?_⟩
  rw [← smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hg0, one_smul]
  abel
end Formalism.HermitianLatticeCounting.P
