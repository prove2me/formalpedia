-- Prove2me | solution 1 for Formalism.G0.typeIIDown_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:58.861086+00:00
-- url     : https://prove2.me/submissions/0a0492a4-a122-4896-a47e-51c5f7fe871c

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_TypeIIDownP_countBelow_eq
import Theorems.Thm_Formalism_G0_TypeIIDownP_countAboveCodim_eq
import Theorems.Thm_Formalism_G0_TypeIIDownP_codimCount
import Theorems.Thm_Formalism_G0_QVandermondeP_form2

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
private theorem mkQ_surjective' {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    (R : Submodule F Q) : Function.Surjective R.mkQ :=
  LinearMap.range_eq_top.mp (Submodule.range_mkQ R)
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
open TypeIIDownP QVandermondeP
namespace Formalism.G0
theorem _root_.solution (hS : SubspaceCount) : TypeIIDown := by
  intro F P Q _ _ _ _ _ _ _ _ f N g j hP hQ
  have : Module.Finite F P := Module.Finite.of_finite
  have : Module.Finite F Q := Module.Finite.of_finite
  have : Finite (Q ⧸ LinearMap.range f) :=
    Finite.of_surjective _ (_root_.Formalism.G0.TypeIIDownP.mkQ_surjective' (LinearMap.range f))
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hqr := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have hdim : Module.finrank F (Q ⧸ LinearMap.range f) =
      Module.finrank F (LinearMap.ker f) + g := by omega
  have h7 := Formalism.G0.TypeIIDownP.countAboveCodim_eq (LinearMap.range f) (N + g) j hQ
  have h8 := Formalism.G0.TypeIIDownP.codimCount hS (F := F) (W := Q ⧸ LinearMap.range f)
    (Module.finrank F (Q ⧸ LinearMap.range f)) j rfl
  have hK : ∀ k, countBelow (LinearMap.ker f) k =
      gaussBinom (Fintype.card F) (Module.finrank F (LinearMap.ker f)) k := fun k =>
    (Formalism.G0.TypeIIDownP.countBelow_eq (LinearMap.ker f) k).trans (hS k)
  rw [h7, h8, hdim, Formalism.G0.QVandermondeP.form2, Nat.cast_sum]
  simp only [hK]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  push_cast
  ring
end Formalism.G0
