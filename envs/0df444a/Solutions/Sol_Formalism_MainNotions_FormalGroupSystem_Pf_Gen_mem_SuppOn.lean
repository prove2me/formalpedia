-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.mem_SuppOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:31.63089+00:00
-- url     : https://prove2.me/submissions/6f535129-a0ae-401b-b380-57edd174a7b3

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
variable {R σ Pl : Type} [CommRing R]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R} :
    f ∈ SuppOn π v ↔ ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v := Iff.rfl
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
