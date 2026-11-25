-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.isLattice_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:34.959375+00:00
-- url     : https://prove2.me/submissions/cbd6d20e-3348-4654-a862-f2d269e9d2ca

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_smul_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_cut_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open SplitBAux
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) : Submodule.IsLattice K (S.cut Λ) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    have hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj
      (Submodule.FG.of_le_of_isNoetherian hle)
  · rw [eq_top_iff]
    intro a _
    obtain ⟨r, hr, hra⟩ := exists_smul_mem hΛ (S.ι a)
    have h1 : r • a ∈ S.cut Λ := by
      rw [VecSplit.mem_cut_iff, ← algebraMap_smul K r a, map_smul, algebraMap_smul]
      exact hra
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by
      simpa using hr
    have e : a = (algebraMap (𝓞 K) K r)⁻¹ • (r • a) := by
      rw [← algebraMap_smul K r a, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
