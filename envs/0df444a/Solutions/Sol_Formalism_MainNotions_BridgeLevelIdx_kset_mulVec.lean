-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.kset_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:45:17.808651+00:00
-- url     : https://prove2.me/submissions/36901c58-c737-4b75-99d3-c86605c85844

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}
namespace Formalism.MainNotions.BridgeLevelIdx
theorem _root_.solution {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf :=
  (hx y).1 hy
end Formalism.MainNotions.BridgeLevelIdx
