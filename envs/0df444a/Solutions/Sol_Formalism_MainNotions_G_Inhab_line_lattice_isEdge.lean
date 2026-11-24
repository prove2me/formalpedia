-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.line_lattice_isEdge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:58.112926+00:00
-- url     : https://prove2.me/submissions/e8e03cca-9942-4869-ae3f-4fa770035710

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
import Theorems.Thm_Formalism_MainNotions_G_Inhab_line_succ_le
import Theorems.Thm_Formalism_MainNotions_G_Inhab_p_smul_line
import Theorems.Thm_Formalism_MainNotions_G_Inhab_card_line_quot
import Theorems.Thm_Formalism_MainNotions_G_Inhab_line_isLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : IsEdge p n' 1 (edge1 W Qq p a) :=
  ⟨line_isLattice h _, line_isLattice h _, line_succ_le h a, p_smul_line h a, by
    rw [mul_one]; exact card_line_quot h a⟩
end Formalism.MainNotions.G.Inhab
