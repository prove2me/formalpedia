-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.IdealLike.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:40:49.437881+00:00
-- url     : https://prove2.me/submissions/5cfc2747-7407-4bf2-be11-64d1ab07867d

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
namespace IdealLike
theorem _root_.solution {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {μ a : K}
    (hμ : IsUnitIn S μ) (h : P (μ * a)) : P a := by
  have := hP.2.1 _ hμ.2.2 _ h
  rwa [← mul_assoc, inv_mul_cancel₀ hμ.1, one_mul] at this
end IdealLike
end Formalism.L2.SG.Pf.LatDictZ.Z2
