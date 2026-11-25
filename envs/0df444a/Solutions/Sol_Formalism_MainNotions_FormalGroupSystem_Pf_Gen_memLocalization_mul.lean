-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.memLocalization_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:15:18.512398+00:00
-- url     : https://prove2.me/submissions/f61e11bf-10db-419e-93ad-79b069b3791b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution (v : Pl) (f g : MvPowerSeries (ι v) K) : atP v (f * g) = atP v f * atP v g := by
  unfold atP
  exact map_mul _ f g
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
