-- Prove2me | solution 1 for Formalism.F.linearCombinationMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:40.98809+00:00
-- url     : https://prove2.me/submissions/3459a29c-ccc4-49eb-a29e-515f067d244a

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) (c : EuclideanSpace ℝ ι) :
    linearCombinationMap v c = ∑ i, c i • v i := rfl
end Formalism.F
