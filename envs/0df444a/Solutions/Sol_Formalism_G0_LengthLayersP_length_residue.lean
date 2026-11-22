-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:41.737346+00:00
-- url     : https://prove2.me/submissions/2b0dc9f5-cbd2-4a13-9c25-54fb1ad58547

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
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution (π : O) (hπ : Irreducible π) :
    Module.length O (O ⧸ Ideal.span {π}) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact (PrincipalIdealRing.isMaximal_of_irreducible hπ).out
end Formalism.G0.LengthLayersP
