-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.lf_csmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:17.665877+00:00
-- url     : https://prove2.me/submissions/26d026d1-503f-4f27-852a-1a35bcf57f87

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
theorem _root_.solution (a : IntAf I.F I.E) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ I.Lf) :
    (a : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf :=
  I.Lf.smul_mem a hz
end Formalism.MainNotions.BridgeLevelIdx
