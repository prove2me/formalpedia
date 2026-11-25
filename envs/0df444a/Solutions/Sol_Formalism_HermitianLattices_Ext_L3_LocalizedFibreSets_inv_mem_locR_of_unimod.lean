-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.inv_mem_locR_of_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:56.388044+00:00
-- url     : https://prove2.me/submissions/00ea1dd9-47bb-4e2c-91e1-944ab5b37d3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_comb_mem_dualAt_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_one_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_dualAt_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_loc_adjoin_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L')) :
    (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  have h1 : (h S.x₀ S.x₀)⁻¹ • S.x₀ + S.ι 0 ∈
      Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) := by
    rw [comb_mem_dualAt_iff hs, inv_mul_cancel₀ S.hx₀]
    exact ⟨one_mem_locR p, Submodule.zero_mem _⟩
  rw [hU] at h1
  exact ((S.comb_mem_loc_adjoin_iff p L' _ 0).mp h1).1
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
