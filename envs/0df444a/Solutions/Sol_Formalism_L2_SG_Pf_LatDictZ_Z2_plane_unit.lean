-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.plane_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:34.411011+00:00
-- url     : https://prove2.me/submissions/9d08c828-5967-4b48-a77b-e50d4db27b93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isUnitIn_div_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locR_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing


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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (h1 : ¬ InI p p a) (h2 : ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) : IsUnitIn (locRing p) a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  rw [isUnitIn_div_iff hp r hs, mem_hcompl_iff hp]
  exact ⟨fun hr => h1 ⟨r, s, hs, hr, rfl⟩, fun hr => h2 ⟨r, s, hs, hr, rfl⟩⟩
end Formalism.L2.SG.Pf.LatDictZ.Z2
