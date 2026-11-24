-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.finrank_perpSpace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:41.830265+00:00
-- url     : https://prove2.me/submissions/e11a1d59-1bb8-479a-8fea-7e532ea1d885

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_finrank_add_one

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    finrank K (perpSpace h x₀) + 1 = finrank K V :=
  VecSplit.finrank_add_one (vecSplitPerp h hx)
end Formalism.HermitianLattices.Ext.L3
