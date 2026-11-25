-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.isIntegralLat_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:25.473835+00:00
-- url     : https://prove2.me/submissions/d8ee19c5-68ee-4217-b7ca-79dc3cc0c8da

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8

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
theorem _root_.solution (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := S.isIntegralLat_adjoin_iff' hs h1 L'
end VecSplit
end Formalism.HermitianLattices.Ext.L3
