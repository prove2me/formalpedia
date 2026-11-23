-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5bSig_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:52.039152+00:00
-- url     : https://prove2.me/submissions/0467fc87-677a-4807-a684-08faaa3a2d33

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace

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
open NumberField
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (a : E) (w : InfinitePlace E) : complexEmbeddingVector a w = w.embedding a := rfl
end Formalism.HermitianLatticeCounting.P
