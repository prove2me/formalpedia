-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:32.61039+00:00
-- url     : https://prove2.me/submissions/f087ddaf-d0db-40b3-9a19-c7556be29eec

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_props
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
open Lat2
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatDualLattice.{u} := by
  intro O G V V' _ _ _ _ _ _ _ _ _ _ _ _ ε ρ ρ' b T hT hs hb he
  obtain ⟨h1, h2, h3⟩ := dualLat_props hT hb
  exact ⟨h1, h2, dualLat_stable hs he, h3⟩
end Formalism.RepresentationBoundsCohomology.LOC
