-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.isSymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:33.34592+00:00
-- url     : https://prove2.me/submissions/e794a0f6-f133-4b06-bc44-d57eaacb24bc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
private theorem star_sesq_eq_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (a b : V) :
    star (h a b) = h b a := by
  first | exact hs a b | exact hs.eq a b
end Formalism.HermitianLattices.Ext.L3
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace Formalism.HermitianLattices.Ext.L3
namespace VecSplit
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hs : h.IsSymm) : h'.IsSymm := by
  have H : ∀ a b : V', star (h' a b) = h' b a := by
    intro a b
    rw [← S.isom, ← S.isom]
    exact star_sesq_eq_swap_of_isSymm hs _ _
  first | exact H | exact ⟨H⟩
end VecSplit
end Formalism.HermitianLattices.Ext.L3
