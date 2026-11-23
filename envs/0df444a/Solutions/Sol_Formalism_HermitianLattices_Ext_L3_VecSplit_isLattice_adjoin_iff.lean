-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.isLattice_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:37.856456+00:00
-- url     : https://prove2.me/submissions/6e21c894-f856-4619-88d2-1b8a564eceb7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isLattice_adjoin_iff__9a69000cf349

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
namespace Formalism.HermitianLattices.Ext.L3
namespace VecSplit
theorem _root_.solution (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := S.isLattice_adjoin_iff' L'
end VecSplit
end Formalism.HermitianLattices.Ext.L3
