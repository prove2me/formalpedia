-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_eq_add_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:21.485889+00:00
-- url     : https://prove2.me/submissions/a3aab52d-0424-4a22-81ad-bd6c89fcc41d

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
theorem _root_.solution {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O ↥V = Module.length O ↥U + Module.length O (↥V ⧸ U.comap V.subtype) := by
  rw [Module.length_eq_add_of_exact (U.comap V.subtype).subtype (U.comap V.subtype).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.comapSubtypeEquivOfLe h).length_eq]
end Formalism.G0.LengthLayersP
