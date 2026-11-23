-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitBAux.mem_gmap_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:42.260018+00:00
-- url     : https://prove2.me/submissions/a47b6678-87d8-470f-86be-e75cdda8e374

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
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
open Formalism.HermitianLattices.Ext.L3.SplitBAux
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.SplitBAux
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (e : W ≃ₗ[K] W) (M : Submodule (𝓞 K) W) (v : W) :
    v ∈ Formalism.HermitianLatticesTheory.gmap e M ↔ e.symm v ∈ M := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hv
    exact ⟨e.symm v, hv, by simp⟩
end Formalism.HermitianLattices.Ext.L3.SplitBAux
