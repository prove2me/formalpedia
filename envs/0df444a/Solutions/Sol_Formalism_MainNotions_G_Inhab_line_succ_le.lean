-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.line_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:50.924331+00:00
-- url     : https://prove2.me/submissions/18659d6e-e137-4c04-a764-eeec19f26a40

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
import Theorems.Thm_Formalism_MainNotions_G_Inhab_p_smul_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen


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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : line W (Qq := Qq) p (a + 1) ≤ line W p a := by
  unfold line
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have := p_smul_gen (W := W) h a
  unfold gen at this
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
end Formalism.MainNotions.G.Inhab
