-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.mixed_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:29.249114+00:00
-- url     : https://prove2.me/submissions/9219e5e2-a769-4490-8965-bc958e6b21f9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_discrIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_exists_mixed
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_update_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_of_unram
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {x : Fin (finrank K V) → V} {i : Fin (finrank K V)} (hx : ∀ k, k ≠ i → x k ∈ L) {y y' : V}
    (hy : y ∈ L) (hy' : y' ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det (Function.update x i y)) * gdet h b *
      b.det (Function.update x i y')) : z ∈ discrIdeal h L := by
  have hu := update_mem hx hy
  have hu' := update_mem hx hy'
  obtain ⟨z11, h11⟩ := exists_mixed hLi b hu hu
  obtain ⟨z22, h22⟩ := exists_mixed hLi b hu' hu'
  obtain ⟨z21, h21⟩ := exists_mixed hLi b hu' hu
  have m11 := mem_discrIdeal b hu h11
  have m22 := mem_discrIdeal b hu' h22
  have key : ∀ θ : 𝓞 K, θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
    intro θ
    have hd : b.det (Function.update x i (y + θ • y')) =
        b.det (Function.update x i y) + algebraMap (𝓞 K) K θ * b.det (Function.update x i y') := by
      rw [← algebraMap_smul K θ y', AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        smul_eq_mul]
    have hw : z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
      refine mem_discrIdeal b (update_mem hx (L.add_mem hy (L.smul_mem θ hy'))) ?_
      rw [hd]
      simp only [map_add, map_mul, h11, h22, h21, hz, algebraMap_conjO, star_add, star_mul']
      ring
    have he : θ * z + conjO K θ * z21 =
        (z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21) - z11 - conjO K θ * θ * z22 := by
      ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hw m11) (Ideal.mul_mem_left _ _ m22)
  refine mem_of_unram hK fun θ => ?_
  have h1 := key 1
  rw [map_one, one_mul, one_mul] at h1
  have he : (θ - conjO K θ) * z = (θ * z + conjO K θ * z21) - conjO K θ * (z + z21) := by ring
  rw [he]
  exact Ideal.sub_mem _ (key θ) (Ideal.mul_mem_left _ _ h1)
end Formalism.HermitianLattices.Ext.L3.BallB
