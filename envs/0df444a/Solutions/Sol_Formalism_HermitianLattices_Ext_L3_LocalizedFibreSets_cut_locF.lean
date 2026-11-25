-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.cut_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:02.100608+00:00
-- url     : https://prove2.me/submissions/1273b563-4964-4987-9ebd-327ebda6c933

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_cut_iff


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
theorem _root_.solution (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    S.cut (locF 𝔭 Λ) = locF 𝔭 (S.cut Λ) := by
  ext a
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower]
    exact hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower] at hx
    exact hx
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
