-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.mem_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:10.953014+00:00
-- url     : https://prove2.me/submissions/ca1c7620-9f8c-442f-a2b0-d5d01a995e62

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
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
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')
namespace Formalism.HermitianLattices.Ext.L3.VecSplit
theorem _root_.solution (L' : Submodule (𝓞 K) V') (v : V) :
    v ∈ S.adjoin L' ↔ ∃ (r : 𝓞 K) (a : V'), a ∈ L' ∧ v = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι a := by
  unfold VecSplit.adjoin
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
    exact ⟨r, a, ha, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩
  · rintro ⟨r, a, ha, rfl⟩
    exact ⟨r • S.x₀, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, S.ι a,
      Submodule.mem_map.mpr ⟨a, ha, rfl⟩, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩
end Formalism.HermitianLattices.Ext.L3.VecSplit
