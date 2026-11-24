-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.map_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:07.712605+00:00
-- url     : https://prove2.me/submissions/0e6d2e66-a072-4900-82d8-06b4c5765f25

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (a n : ℤ) :
    (line W (Qq := Qq) p n).map
      ((Matrix.mulVecLin (Matrix.scalar (Fin 1) ((p : Qq) ^ a))).restrictScalars W) = line W p (a + n) := by
  unfold line
  rw [Submodule.map_span, Set.image_singleton]
  congr 2
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, zpow_add₀ (p_ne h)]
end Formalism.MainNotions.G.Inhab
