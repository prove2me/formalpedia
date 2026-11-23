-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.res_mem_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:21.751799+00:00
-- url     : https://prove2.me/submissions/eb5260ac-91a5-4e2b-bf6a-d1f2885551e2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_spec

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
    (hx : g S.x₀ = S.x₀) : res S g hg hx ∈ Formalism.HermitianLatticesTheory.isom h' := by
  show ∀ x y, h' (res S g hg hx x) (res S g hg hx y) = h' x y
  intro x y
  rw [← S.isom, res_spec, res_spec, isom_apply hg, S.isom]
end Formalism.HermitianLattices.Ext.L3.SplitBAux
