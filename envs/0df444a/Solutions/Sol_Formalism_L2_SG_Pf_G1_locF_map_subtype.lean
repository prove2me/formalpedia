-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.locF_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:22.587395+00:00
-- url     : https://prove2.me/submissions/adae1775-419a-4cf0-bc55-a31b01cd8774

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFMapSubtype
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (X : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) X) :
    locF 𝔭 (N.map (X.subtype.restrictScalars (𝓞 K))) =
      (locF 𝔭 N).map (X.subtype.restrictScalars (𝓞 K)) := by
  ext y
  rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF, Submodule.mem_map]
  constructor
  · rintro ⟨t, ht, z, hz, hzy⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
      rw [e, map_ne_zero]
      exact fun h => ht0 (by exact_mod_cast h)
    have hmem : algebraMap (𝓞 F) (𝓞 K) t • y ∈ X := by
      rw [← hzy]; exact z.2
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y] at hmem
    have hyX : y ∈ X := (X.smul_mem_iff hne).mp hmem
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
    refine ⟨t, ht, ?_⟩
    have e2 : algebraMap (𝓞 F) (𝓞 K) t • (⟨y, hyX⟩ : X) = z := by
      apply Subtype.ext
      simpa using hzy.symm
    rw [e2]; exact hz
  · rintro ⟨z, hz, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF] at hz
    obtain ⟨t, ht, hz⟩ := hz
    exact ⟨t, ht, _, hz, by simp⟩
end Formalism.L2.SG.Pf.G1
