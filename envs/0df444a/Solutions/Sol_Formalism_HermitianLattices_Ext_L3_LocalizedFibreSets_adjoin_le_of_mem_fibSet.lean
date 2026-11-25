-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.adjoin_le_of_mem_fibSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:40.485623+00:00
-- url     : https://prove2.me/submissions/9ec4bd07-9ec3-4e9f-9b4a-794bba9d771f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinIntegralOfNonempty
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
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
theorem _root_.solution (S : VecSplit h h') {L Λ : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {𝔭 : Ideal (𝓞 F)} (hΛ : Λ ∈ fibSet S L 𝔭 Λ') : S.adjoin Λ' ≤ Λ := by
  obtain ⟨-, -, hx, hc⟩ := hΛ
  refine sup_le ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  · rw [Submodule.map_le_iff_le_comap]
    exact (LocF.le_locF 𝔭 Λ').trans hc.symm.le
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
