-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.isLattice_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:06.91089+00:00
-- url     : https://prove2.me/submissions/093ed0a8-e0b2-45ee-b252-890536051873

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_span_eq_top_of_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVN
theorem _root_.solution : Submodule.IsLattice K (1 : Submodule (𝓞 K) K) :=
  ⟨⟨{1}, by rw [Finset.coe_singleton, ← Submodule.one_eq_span]⟩,
    span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩
end Formalism.MainNotions.BridgeLemVN
