-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.planeForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:24.851466+00:00
-- url     : https://prove2.me/submissions/db365a2a-1bdf-4f61-bcd4-d88b1f2deb76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) (x y : V) :
    planeForm h z b x y = h x y - b * h x z * h z y := rfl
end Formalism.L2.SG.Pf.LatDictZ.Z2
