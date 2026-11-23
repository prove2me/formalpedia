-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.gmap_extOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:38.60777+00:00
-- url     : https://prove2.me/submissions/a28bc2f7-0c06-4de8-8247-76ae37d462dd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_mem_gmap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_mem_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_symm_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff


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
theorem _root_.solution (S : VecSplit h h') (g' : V' ≃ₗ[K] V') {C₁ C₂ : Submodule (𝓞 K) V'}
    (hC : Formalism.HermitianLatticesTheory.gmap g' C₁ = C₂) :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (S.adjoin C₁) = S.adjoin C₂ := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [mem_gmap_iff, extOf_symm_apply, SplitBAux.mem_adjoin_iff, SplitBAux.mem_adjoin_iff, ← hC,
    mem_gmap_iff]
end Formalism.HermitianLattices.Ext.L3.SplitBAux
