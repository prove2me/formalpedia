-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_mem_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:44.412514+00:00
-- url     : https://prove2.me/submissions/1b5d1b79-038c-47c0-8add-c751a14fd2e8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_decomp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_apply

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
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') {g' : V' ≃ₗ[K] V'}
    (hg : g' ∈ Formalism.HermitianLatticesTheory.isom h') : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := by
  have hg' : ∀ x y, h' (g' x) (g' y) = h' x y := hg
  show ∀ x y, h (extOf S g' x) (extOf S g' y) = h x y
  intro x y
  obtain ⟨c, a, rfl⟩ := S.cover x
  obtain ⟨d, b, rfl⟩ := S.cover y
  rw [extOf_apply, extOf_apply, h_decomp hs, h_decomp hs, hg']
end Formalism.HermitianLattices.Ext.L3.SplitBAux
