-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.finrank_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:10.668969+00:00
-- url     : https://prove2.me/submissions/6f0a37a4-db89-40ca-8c25-fc70389c20c8

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
    (S : VecSplit h h') : finrank K V' + 1 = finrank K V := by
  let f : K × V' →ₗ[K] V := LinearMap.coprod (LinearMap.toSpanSingleton K V S.x₀) S.ι
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, a⟩ hca
      have h1 : c • S.x₀ + S.ι a = 0 := by simpa [f] using hca
      have h2 : h S.x₀ (c • S.x₀ + S.ι a) = 0 := by rw [h1, map_zero]
      rw [map_add, map_smul, S.orth, add_zero, smul_eq_mul] at h2
      have hc : c = 0 := (mul_eq_zero.mp h2).resolve_right S.hx₀
      subst hc
      have h3 : S.ι a = 0 := by simpa using h1
      have ha : a = 0 := S.inj (by rw [h3, map_zero])
      simp [ha]
    · intro v
      obtain ⟨c, a, hv⟩ := S.cover v
      exact ⟨(c, a), by simp [f, hv]⟩
  have := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega
end VecSplit
end Formalism.HermitianLattices.Ext.L3
