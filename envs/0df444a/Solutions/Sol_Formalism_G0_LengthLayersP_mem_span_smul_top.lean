-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.mem_span_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.027799+00:00
-- url     : https://prove2.me/submissions/0e96f020-e3b8-47da-bc72-5d9b3ac9820e

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers

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
theorem _root_.solution {X : Type} [AddCommGroup X] [Module O X] (a : O) (x : X) :
    x ∈ (Ideal.span {a}) • (⊤ : Submodule O X) ↔ ∃ y, a • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp
end Formalism.G0.LengthLayersP
