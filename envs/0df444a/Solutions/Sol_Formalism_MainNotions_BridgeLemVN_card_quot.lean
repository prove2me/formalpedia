-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.card_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:58.930805+00:00
-- url     : https://prove2.me/submissions/2f88f0cc-0188-4ad1-8432-33f2e0ef2d17

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
import Theorems.Thm_Formalism_MainNotions_BridgeLemVN_fixF
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_unitsSquareIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_discrTower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isReal_cmF


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
theorem _root_.solution (hK : IsCMUnram K) :
    Nat.card ((𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range) = 2 ^ fDeg K := by
  rw [Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK),
    (discrTower K (cmF K) hK (fixF K)).2.1]
end Formalism.MainNotions.BridgeLemVN
