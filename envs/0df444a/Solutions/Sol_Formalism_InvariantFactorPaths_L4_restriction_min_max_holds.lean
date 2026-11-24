-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restriction_min_max_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:21.702945+00:00
-- url     : https://prove2.me/submissions/59654017-f1ea-45ee-a040-0ed8b5b12eb5

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hypE_eproj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_res
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_Y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_res
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_Y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_res_hw
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_keep_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_into_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : ResMM := by
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hOnto x
  constructor
  · intro hx
    obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
    obtain ⟨h0, hh0, hres⟩ := hOnto x hxX
    obtain ⟨PE, hPE, -, -⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
    refine ⟨PE (wtComp p LL (K + 1) w h0), eproj_Y LL J M ρ w e1 hHP PE hPE _ (wtComp_Y LL J M w h0 hh0)
      (wtComp_mem LL (K + 1) w h0), ?_⟩
    change resL p (Fin.last K, ρ) 0 (PE (wtComp p LL (K + 1) w h0)) = x
    change resL p (Fin.last K, ρ) 0 h0 = x at hres
    rw [← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ (wtComp_mem LL (K + 1) w h0), wtComp_res, hres,
      wtComp_fix LL (K + 1) w x hxW]
    exact eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh1, hhW⟩ := Submodule.mem_inf.mp hh
    obtain ⟨hhY, hhH⟩ := Submodule.mem_inf.mp hh1
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨restriction_into_holds p K r LL J M ρ e1 hr hρ hv hHP h hhY,
      res_hw LL (K + 1) ρ w (Fin.last K) 0 h hhH⟩, resL_keep_supp (Fin.last K, ρ) 0 _ h hhW⟩
end Formalism.InvariantFactorPaths.L4
