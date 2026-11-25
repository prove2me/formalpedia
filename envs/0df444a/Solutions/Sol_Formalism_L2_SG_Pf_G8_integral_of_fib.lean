-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G8.integral_of_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:03.136296+00:00
-- url     : https://prove2.me/submissions/269505cf-e8fd-4d71-bbc7-18819edc0822

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibPNeZeroOfGenus
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPermOfMin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G8
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h T := by
  intro x hx y hy
  rw [← Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF (K := K) (F := F) (1 : Submodule (𝓞 K) K),
    Submodule.mem_iInf]
  rintro ⟨𝔭, h𝔭⟩
  have hne := hfib 𝔭 h𝔭
  unfold fibP at hne
  obtain ⟨⟨Λ, _, hdual, _, hΛT⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have hsub : ∀ z ∈ T, z ∈ Λ := fun z hz =>
    (Submodule.mem_inf.1 (hΛT.symm ▸ Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 T hz :
      z ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K))).1
  have hyd : y ∈ dualF h 𝔭 Λ := by
    rw [hdual]
    exact hsub y hy
  exact hyd x (hsub x hx)
end Formalism.L2.SG.Pf.G8
