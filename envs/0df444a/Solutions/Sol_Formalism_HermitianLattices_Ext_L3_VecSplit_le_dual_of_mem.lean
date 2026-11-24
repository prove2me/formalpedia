-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.le_dual_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:37.841488+00:00
-- url     : https://prove2.me/submissions/be026188-c732-4487-a1d7-698d79cedbbd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



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
    (hs : h.IsSymm) (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ) (hx : S.x₀ ∈ Λ) :
    S.adjoin (S.cut Λ) ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin (S.cut Λ)) := by
  have hle : S.adjoin (S.cut Λ) ≤ Λ :=
    sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (Submodule.map_comap_le _ _)
  refine ⟨hle, fun x hx' => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro y hy
  exact hΛ y (hle hy) x hx'
end VecSplit
end Formalism.HermitianLattices.Ext.L3
