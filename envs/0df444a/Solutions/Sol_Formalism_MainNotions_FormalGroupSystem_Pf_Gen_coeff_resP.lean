-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_resP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:06.055608+00:00
-- url     : https://prove2.me/submissions/24a0018d-bd92-4983-ac95-a12bf7fccbc8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand

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
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff m (resP v f) = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f := rfl
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
