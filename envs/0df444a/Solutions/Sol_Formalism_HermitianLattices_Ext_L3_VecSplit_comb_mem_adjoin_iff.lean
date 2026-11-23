-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.comb_mem_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:16.571814+00:00
-- url     : https://prove2.me/submissions/fb27aac4-ab59-4441-bbc4-c28c142a20e3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')
namespace Formalism.HermitianLattices.Ext.L3.VecSplit
theorem _root_.solution (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ c ∈ (1 : Submodule (𝓞 K) K) ∧ a ∈ L' := by
  rw [S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.mp he
    exact ⟨Submodule.mem_one.mpr ⟨r, rfl⟩, hb⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    exact ⟨r, a, ha, rfl⟩
end Formalism.HermitianLattices.Ext.L3.VecSplit
