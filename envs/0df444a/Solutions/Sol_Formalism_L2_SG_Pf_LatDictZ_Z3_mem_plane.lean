-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.mem_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:14.211124+00:00
-- url     : https://prove2.me/submissions/6c72494e-faa8-4cce-8526-c57a0397211f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
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
    (hzy : h z y = 1) (hD : IsUnitIn S (1 - h z z * h y y)) (α β : K) :
    α • z + β • y ∈ M ↔ α ∈ S ∧ β ∈ S := by
  have hyz := hyz_one hs hzy
  constructor
  · intro hw
    have hA := hM.int _ hz _ hw
    have hB := hM.int _ hy _ hw
    have hnz : h z z ∈ S := hM.int _ hz _ hz
    have hb : h y y ∈ S := hM.int _ hy _ hy
    have eA : h z (α • z + β • y) = α * h z z + β := by
      simp only [map_add, map_smul, smul_eq_mul, hzy, mul_one]
    have eB : h y (α • z + β • y) = α + β * h y y := by
      simp only [map_add, map_smul, smul_eq_mul, hyz, mul_one]
    rw [eA] at hA
    rw [eB] at hB
    have hβ : β = ((α * h z z + β) - h z z * (α + β * h y y)) * (1 - h z z * h y y)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hD.1]
      ring
    have hβS : β ∈ S := by
      rw [hβ]
      exact S.mul_mem (S.sub_mem hA (S.mul_mem hnz hB)) hD.2.2
    refine ⟨?_, hβS⟩
    have hα : α = (α + β * h y y) - β * h y y := by ring
    rw [hα]
    exact S.sub_mem hB (S.mul_mem hβS hb)
  · rintro ⟨hα, hβ⟩
    exact M.add_mem (hM.smul_mem _ hα _ hz) (hM.smul_mem _ hβ _ hy)
end Formalism.L2.SG.Pf.LatDictZ.Z3
