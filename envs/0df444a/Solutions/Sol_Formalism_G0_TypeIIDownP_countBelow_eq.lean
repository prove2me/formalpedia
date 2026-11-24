-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.countBelow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:25.935808+00:00
-- url     : https://prove2.me/submissions/0d3f3e87-08ad-4b10-8d7a-a80e3f556c01

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
end TypeIIDownP
end Formalism.G0
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
private theorem finrank_map_subtype_eq' {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (A : Submodule F W) (V : Submodule F A) :
    Module.finrank F (V.map A.subtype) = Module.finrank F V :=
  (Submodule.equivMapOfInjective A.subtype (fun _ _ h => Subtype.ext h) V).finrank_eq.symm
end TypeIIDownP
end Formalism.G0
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
end TypeIIDownP
open TypeIIDownP QVandermondeP
end Formalism.G0
namespace Formalism.G0
end Formalism.G0
end

set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (k : ℕ) :
    countBelow A k = countBelow (⊤ : Submodule F A) k := by
  unfold Formalism.G0.countBelow
  exact Nat.card_congr
    { toFun := fun U => ⟨U.1.comap A.subtype, le_top, by
        rw [← finrank_map_subtype_eq' A (U.1.comap A.subtype), Submodule.map_comap_subtype,
          inf_eq_right.mpr U.2.1]
        exact U.2.2⟩
      invFun := fun V => ⟨V.1.map A.subtype, Submodule.map_subtype_le A V.1, by
        rw [finrank_map_subtype_eq']; exact V.2.2⟩
      left_inv := fun U => Subtype.ext (by
        show Submodule.map A.subtype (Submodule.comap A.subtype U.1) = U.1
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr U.2.1])
      right_inv := fun V => Subtype.ext (by
        show Submodule.comap A.subtype (Submodule.map A.subtype V.1) = V.1
        exact Submodule.comap_map_eq_of_injective (fun _ _ h => Subtype.ext h) V.1) }
end Formalism.G0.TypeIIDownP
