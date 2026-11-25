-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.mem_locR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:51.444174+00:00
-- url     : https://prove2.me/submissions/58b90720-ab9d-4a24-a107-5c33f55bc44a

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
theorem _root_.solution (p : Ideal (𝓞 K)) (x : K) :
    x ∈ locR (K := K) p ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ (1 : Submodule (𝓞 K) K) := Iff.rfl
end Formalism.MainNotions.BridgeLemVR
