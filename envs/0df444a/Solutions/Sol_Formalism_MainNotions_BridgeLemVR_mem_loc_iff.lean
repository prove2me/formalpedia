-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.mem_loc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:53.11807+00:00
-- url     : https://prove2.me/submissions/2fcc35d4-e45d-4567-b147-1c266cd81aea

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution (p : Ideal (𝓞 K)) (N : Submodule (𝓞 K) K) (x : K) :
    x ∈ loc (K := K) p N ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ N := Iff.rfl
end Formalism.MainNotions.BridgeLemVR
