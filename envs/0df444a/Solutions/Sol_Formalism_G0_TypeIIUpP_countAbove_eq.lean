-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.countAbove_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:46.540881+00:00
-- url     : https://prove2.me/submissions/00f0a268-1177-4c88-a4c0-82fd7a68091d

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_TypeIIUpP_finrank_comap_mkQ

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
theorem _root_.solution (A : Submodule F W) (j : ℕ) :
    countAbove A j = if Module.finrank F A ≤ j then
      countBelow (⊤ : Submodule F (W ⧸ A)) (j - Module.finrank F A) else 0 := by
  haveI : Module.Finite F W := Module.Finite.of_finite
  unfold countAbove countBelow
  split_ifs with hj
  · apply Nat.card_congr
    exact
      { toFun := fun U => ⟨U.1.map A.mkQ, le_top, by
            have h3 := finrank_comap_mkQ A (U.1.map A.mkQ)
            rw [Submodule.comap_map_mkQ, sup_eq_right.mpr U.2.1, U.2.2] at h3
            omega⟩
        invFun := fun V => ⟨V.1.comap A.mkQ,
          (Submodule.ker_mkQ A).ge.trans (LinearMap.ker_le_comap _),
          by rw [finrank_comap_mkQ, V.2.2]; omega⟩
        left_inv := fun U => Subtype.ext (by
          show (U.1.map A.mkQ).comap A.mkQ = U.1
          rw [Submodule.comap_map_mkQ]; exact sup_eq_right.mpr U.2.1)
        right_inv := fun V => Subtype.ext
          (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective A) V.1) }
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hAU, hU⟩
    have h3 : Module.finrank F A ≤ Module.finrank F U := Submodule.finrank_mono hAU
    omega
end Formalism.G0.TypeIIUpP
