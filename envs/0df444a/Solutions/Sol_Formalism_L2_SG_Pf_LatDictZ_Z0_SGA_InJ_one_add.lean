-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.InJ.one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:34.86994+00:00
-- url     : https://prove2.me/submissions/bb06d165-f76e-4710-a74e-5ff5b170f3d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isUnitIn_div_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
namespace InJ
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : InJ p a) :
    IsUnitIn (locRing p) (1 + a) := by
  obtain ⟨r, s, hs, h1, h1', rfl⟩ := ha
  have e1 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hs' := (mem_hcompl_iff hp s).1 hs
  have e : (1 : K) + algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s =
      algebraMap (𝓞 K) K (s + r) / algebraMap (𝓞 K) K s := by
    rw [map_add]; field_simp
  rw [e, isUnitIn_div_iff hp _ hs, mem_hcompl_iff hp]
  exact ⟨fun h => hs'.1 (by simpa using p.sub_mem h h1),
    fun h => hs'.2 (by simpa using Ideal.sub_mem _ h h1')⟩
end InJ
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
