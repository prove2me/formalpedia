-- Prove2me | solution 1 for Formalism.ZF.laU_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:20.407888+00:00
-- url     : https://prove2.me/submissions/abee4afb-c770-43ec-aa69-a2fcc739351d

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : IsOpen laU :=
  (isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const).inter isOpen_ne
end Formalism.ZF
