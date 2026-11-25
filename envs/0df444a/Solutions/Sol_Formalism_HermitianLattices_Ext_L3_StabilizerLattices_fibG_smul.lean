-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.fibG_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:21:16.406865+00:00
-- url     : https://prove2.me/submissions/1cbdfa64-c510-417c-a12b-c03dfc0c954d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_gmap_mem_genus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_apply_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_cut_gmap_extOf
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
open SplitBAux
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ')
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∈ fibG S L (Formalism.HermitianLatticesTheory.gmap g' Λ') := by
  refine ⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩
  · have := apply_mem_gmap (extOf S g') hΛ.2.1
    rwa [extOf_x₀] at this
  · rw [cut_gmap_extOf, hΛ.2.2]
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
