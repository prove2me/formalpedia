-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.toQuot_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:08.624854+00:00
-- url     : https://prove2.me/submissions/091af90e-41e6-4b97-a716-4d9d4d347935

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb

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
theorem _root_.solution (a : ℤ) : Function.Surjective (toQuot W (Qq := Qq) p a) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨c, rfl⟩
end Formalism.MainNotions.G.Inhab
