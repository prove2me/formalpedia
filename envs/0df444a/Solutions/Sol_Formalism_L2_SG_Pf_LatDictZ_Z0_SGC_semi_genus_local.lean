-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.semi_genus_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:51.715701+00:00
-- url     : https://prove2.me/submissions/9ac467a4-b91a-4763-b8ce-87fa15b6ddef

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
theorem _root_.solution : SemiGenusLoc := by
  intro K _ _ _ V _ _ _ h hK hsy hnd p hp M₁ M₂ h1 h2
  obtain ⟨g, hg, hm⟩ := core hK hp _ V rfl h hsy hnd M₁ M₂ h1 h2
  exact ⟨g, hg, hm⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
