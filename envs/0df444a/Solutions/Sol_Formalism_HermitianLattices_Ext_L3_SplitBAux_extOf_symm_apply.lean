-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.extOf_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:16.092292+00:00
-- url     : https://prove2.me/submissions/c511f278-b3c9-4850-9ac4-cd651009c3a2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply

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
theorem _root_.solution (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    (extOf S g').symm (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g'.symm a) := extFun_apply S g'.symm.toLinearMap c a
end Formalism.HermitianLattices.Ext.L3.SplitBAux
