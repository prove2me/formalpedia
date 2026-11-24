-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.mem_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:11:42.914163+00:00
-- url     : https://prove2.me/submissions/d5561cab-f5f6-47cb-9f32-d1dd3b92f1cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {x : V} :
    x ∈ orth h P ↔ ∀ q ∈ P, h q x = 0 := Iff.rfl
end Formalism.L2.SG.Pf.LatDictZ.Z3
