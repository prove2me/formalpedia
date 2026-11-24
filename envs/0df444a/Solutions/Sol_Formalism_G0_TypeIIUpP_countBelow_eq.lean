-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.countBelow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:26.771184+00:00
-- url     : https://prove2.me/submissions/1fef6607-9b49-4586-8a20-e59ab9806b4a

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp

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
open Formalism.G0.TypeIIUpP
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
attribute [local instance] finite_quot
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (A : Submodule F W) (d : ℕ) :
    countBelow A d = countBelow (⊤ : Submodule F A) d := by
  unfold countBelow
  have hfr : ∀ U' : Submodule F A, Module.finrank F (U'.map A.subtype) = Module.finrank F U' :=
    fun U' => (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective A.subtype A.injective_subtype U')).symm
  have hmc : ∀ U : Submodule F W, U ≤ A → (U.comap A.subtype).map A.subtype = U := by
    intro U hU; rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hU
  have hcm : ∀ U' : Submodule F A, (U'.map A.subtype).comap A.subtype = U' :=
    fun U' => Submodule.comap_map_eq_of_injective A.injective_subtype U'
  apply Nat.card_congr
  exact
    { toFun := fun U => ⟨U.1.comap A.subtype, le_top, by rw [← hfr, hmc U.1 U.2.1]; exact U.2.2⟩
      invFun := fun U' => ⟨U'.1.map A.subtype, Submodule.map_subtype_le A U'.1, by rw [hfr]; exact U'.2.2⟩
      left_inv := fun U => Subtype.ext (hmc U.1 U.2.1)
      right_inv := fun U' => Subtype.ext (hcm U'.1) }
end Formalism.G0.TypeIIUpP
