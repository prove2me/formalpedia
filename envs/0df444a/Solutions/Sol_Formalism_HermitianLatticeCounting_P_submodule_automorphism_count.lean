-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:24.982518+00:00
-- url     : https://prove2.me/submissions/f196b414-d9e5-4fa9-a0f5-b06e63687f97

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_SLP_Final_submoduleCountDed
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_Final_autCount


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CardSubmodulesAndLinearEquivBounds := ⟨Formalism.SLP.Final.submoduleCountDed, Formalism.SLP.GlobalBoundRefinements.Final.autCount⟩
end Formalism.HermitianLatticeCounting.P
