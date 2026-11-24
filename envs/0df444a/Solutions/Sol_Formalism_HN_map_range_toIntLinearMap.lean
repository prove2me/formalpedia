-- Prove2me | solution 1 for Formalism.HN.map_range_toIntLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:29.787697+00:00
-- url     : https://prove2.me/submissions/445e729f-b219-40da-8bf0-43b7bc00f570

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN
theorem _root_.solution {G : Type*} [AddCommGroup G] (α : G →+ E) (p : E →L[ℝ] E) :
    (LinearMap.range α.toIntLinearMap).map (p.toLinearMap.restrictScalars ℤ) =
      LinearMap.range ((p.toLinearMap.toAddMonoidHom.comp α).toIntLinearMap) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨α g, ⟨g, rfl⟩, rfl⟩
end Formalism.HN
