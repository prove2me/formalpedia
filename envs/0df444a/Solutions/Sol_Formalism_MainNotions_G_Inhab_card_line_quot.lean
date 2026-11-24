-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.card_line_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:42.974211+00:00
-- url     : https://prove2.me/submissions/cba07388-ac2b-49dc-86cd-c4b6e7c97c4f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
import Theorems.Thm_Formalism_MainNotions_G_Inhab_toQuot_surj
import Theorems.Thm_Formalism_MainNotions_G_Inhab_toQuot_ker

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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    Nat.card (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) =
      p ^ n' := by
  rw [← h.res_card, ← toQuot_ker (Qq := Qq) h a]
  exact Nat.card_congr ((toQuot W (Qq := Qq) p a).quotKerEquivOfSurjective (toQuot_surj a)).symm.toEquiv
end Formalism.MainNotions.G.Inhab
