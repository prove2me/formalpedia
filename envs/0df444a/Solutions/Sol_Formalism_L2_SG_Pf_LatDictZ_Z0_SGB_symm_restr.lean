-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.symm_restr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:40.085804+00:00
-- url     : https://prove2.me/submissions/ec81b7ff-56d2-430c-8763-a3d5db62f7fd

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
variable {S : Subring K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (W : Submodule K V) :
    (restr h W).IsSymm := by
  first
    | exact fun x y => hsy x y
    | exact ⟨fun x y => hsy.eq x y⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
