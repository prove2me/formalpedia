-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:50.067194+00:00
-- url     : https://prove2.me/submissions/df162aad-36ed-4e2f-a3ca-f9d5969aabcb

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    extE h X hX g x = ext h X hX g x := rfl
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
