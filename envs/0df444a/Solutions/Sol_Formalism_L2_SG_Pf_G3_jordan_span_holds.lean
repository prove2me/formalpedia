-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.jordan_span_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:24.210151+00:00
-- url     : https://prove2.me/submissions/d496e952-b9db-40a5-a2eb-7df36b8dc101

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanSpanHolds
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_le_locF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution : JordSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem
end Formalism.L2.SG.Pf.G3
