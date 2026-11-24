-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.gat_M_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:11.398816+00:00
-- url     : https://prove2.me/submissions/17f1264f-9394-48a3-a6bc-095e582d8a55

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution (G : GAtP p) (h : ∀ c, (G.lev c).M = ⊥) : G.M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext c
  have := hF c (Set.mem_univ c)
  have h1 : F c ∈ (G.lev c).M := this
  rw [h c] at h1
  exact h1
end Formalism.MainNotions.Inhab
