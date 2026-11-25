-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.isUnimodularAt_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:19.191925+00:00
-- url     : https://prove2.me/submissions/f8d06aab-31b6-4dc7-a0bf-df197f6a04bc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29

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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) (hp : p.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := S.isUnimodularAt_adjoin_iff' hs h1 L' p
end VecSplit
end Formalism.HermitianLattices.Ext.L3
