-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:08.973894+00:00
-- url     : https://prove2.me/submissions/c5e8aa66-866d-487e-9f84-81e1be46d72c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_mem_SuppOn

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
theorem _root_.solution {R' : Type} [CommRing R'] (φ : R →+* R') {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R}
    (hf : f ∈ SuppOn π v) : MvPowerSeries.map φ f ∈ SuppOn π v := by
  intro m hm x hx
  rw [MvPowerSeries.coeff_map] at hm
  exact (mem_SuppOn.mp hf) m (fun h0 => hm (by rw [h0, map_zero])) x hx
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
