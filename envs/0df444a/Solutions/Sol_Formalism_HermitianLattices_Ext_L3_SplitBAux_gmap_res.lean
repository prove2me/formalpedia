-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.gmap_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:10.133701+00:00
-- url     : https://prove2.me/submissions/182fabec-bebb-48cc-8658-9637f24da0b3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_mem_gmap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_symm_spec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_cut_iff


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
open Formalism.HermitianLattices.Ext.L3.SplitBAux
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.SplitBAux
theorem _root_.solution (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) {L₁ L₂ : Submodule (𝓞 K) V} (hL : Formalism.HermitianLatticesTheory.gmap g L₁ = L₂) :
    Formalism.HermitianLatticesTheory.gmap (res S g hg hx) (S.cut L₁) = S.cut L₂ := by
  ext a
  rw [mem_gmap_iff, S.mem_cut_iff, S.mem_cut_iff, res_symm_spec, ← hL, mem_gmap_iff]
end Formalism.HermitianLattices.Ext.L3.SplitBAux
