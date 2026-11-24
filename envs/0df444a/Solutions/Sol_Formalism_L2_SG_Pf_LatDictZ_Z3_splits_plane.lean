-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.splits_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:23:17.996393+00:00
-- url     : https://prove2.me/submissions/1c20f766-4d61-407f-9ba3-8919d8f8505b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_orth_pair
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_hyz_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {z y : V} (hz : z ∈ M) (hy : y ∈ M)
    (hzy : h z y = 1) (hD : IsUnitIn S (1 - h z z * h y y)) :
    Splits h (Submodule.span K {z, y}) M := by
  intro w hw
  have hyz := hyz_one hs hzy
  have hAS : h z w ∈ S := hM.int _ hz _ hw
  have hBS : h y w ∈ S := hM.int _ hy _ hw
  have hnz : h z z ∈ S := hM.int _ hz _ hz
  have hb : h y y ∈ S := hM.int _ hy _ hy
  obtain ⟨β, hβ⟩ : ∃ β : K, β = (h z w - h z z * h y w) * (1 - h z z * h y y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : K, α = h y w - β * h y y := ⟨_, rfl⟩
  have hβS : β ∈ S := by
    rw [hβ]
    exact S.mul_mem (S.sub_mem hAS (S.mul_mem hnz hBS)) hD.2.2
  have hαS : α ∈ S := by
    rw [hα]
    exact S.sub_mem hBS (S.mul_mem hβS hb)
  have hβD : β * (1 - h z z * h y y) = h z w - h z z * h y w := by
    rw [hβ, mul_assoc, inv_mul_cancel₀ hD.1, mul_one]
  refine ⟨α • z + β • y, M.add_mem (hM.smul_mem _ hαS _ hz) (hM.smul_mem _ hβS _ hy),
    Submodule.mem_span_pair.mpr ⟨α, β, rfl⟩, orth_pair ?_ ?_⟩
  · have e : h z (w - (α • z + β • y)) = h z w - (α * h z z + β) := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul, hzy, mul_one]
    rw [e, hα]
    linear_combination (-1 : K) * hβD
  · have e : h y (w - (α • z + β • y)) = h y w - (α + β * h y y) := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul, hyz, mul_one]
    rw [e, hα]
    ring
end Formalism.L2.SG.Pf.LatDictZ.Z3
