-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.fg_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:34:01.989969+00:00
-- url     : https://prove2.me/submissions/a532bac5-848f-4809-9c47-23159905a705

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
theorem _root_.solution (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM.1
  have h := IsNoetherian.noetherian (N.comap M.subtype)
  have := h.map M.subtype
  rwa [Submodule.map_comap_subtype] at this
end Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
