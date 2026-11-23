-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.colSpan_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:59.293462+00:00
-- url     : https://prove2.me/submissions/af9a3ca4-2774-4f82-ac64-9bfe0c7bdd4d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc

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
theorem _root_.solution (g : Matrix (Fin 1) (Fin 1) Qq) : colSpan W g = Submodule.span W {fun _ => g 0 0} := by
  unfold colSpan
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    rw [Set.mem_singleton_iff]
    funext i
    rw [Subsingleton.elim i 0, Subsingleton.elim c 0]
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    refine ⟨0, ?_⟩
    rw [hv]
    funext i
    rw [Subsingleton.elim i 0]
end Formalism.MainNotions.G.Inhab
