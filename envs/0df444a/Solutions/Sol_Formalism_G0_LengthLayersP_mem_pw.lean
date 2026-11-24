-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.mem_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:04.22722+00:00
-- url     : https://prove2.me/submissions/bbd0b9de-bf7e-46b1-910b-7a881a6116bd

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_mem_span_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution {π : O} {X : Type} [AddCommGroup X] [Module O X] {e : ℕ} {x : X} :
    x ∈ pw π X e ↔ ∃ y, π ^ e • y = x := by
  exact mem_span_smul_top (π ^ e) x
end Formalism.G0.LengthLayersP
