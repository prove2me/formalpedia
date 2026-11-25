-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LandL.gram_det_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:47.339623+00:00
-- url     : https://prove2.me/submissions/f354b304-f078-416e-b2f4-f9ef67951ad9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandLA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LandL_det_mem_subring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LandL
namespace Formalism.HermitianLattices.Ext.L3.LandL
theorem _root_.solution {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (A : Subring K) (hA : ∀ x ∈ A, star x ∈ A) (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
    (g : Basis (Fin n) K V)
    (hdual : ∀ x : V, (∀ y : V, (∀ i, g.repr y i ∈ A) → h y x ∈ A) ↔ ∀ i, g.repr x i ∈ A)
    (h0 : (gram h g).det ≠ 0) : (gram h g).det ∈ A ∧ ((gram h g).det)⁻¹ ∈ A := by
  classical
  have hg : ∀ j i, g.repr (g j) i ∈ A := by
    intro j i
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  refine ⟨det_mem_subring A _ fun i j => (hdual (g j)).2 (hg j) (g i) (hg i), ?_⟩
  set G := gram h g with hG
  have hmul : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.2 h0)
  have key : ∀ y j, h y (∑ i, G⁻¹ i j • g i) = star (g.repr y j) := by
    intro y j
    conv_lhs => rw [← g.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_smul, starRingEnd_apply]
    have h2 : ∀ k, ∑ i, star (g.repr y k) * (G⁻¹ i j * h (g k) (g i))
        = star (g.repr y k) * (1 : Matrix (Fin n) (Fin n) K) k j := by
      intro k
      rw [← hmul, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hG]
      simp only [gram, Matrix.of_apply]
      ring
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ k, ∑ i, G⁻¹ i j * (star (g.repr y k) * h (g k) (g i))
        = star (g.repr y k) * (1 : Matrix (Fin n) (Fin n) K) k j := by
      intro k
      rw [← h2 k]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_congr rfl fun k _ => h3 k]
    simp [Matrix.one_apply]
  have hinv : ∀ i j, G⁻¹ i j ∈ A := by
    intro i j
    have h3 := (hdual (∑ i, G⁻¹ i j • g i)).1 (fun y hy => by rw [key]; exact hA _ (hy j)) i
    rwa [Basis.repr_sum_self] at h3
  have h4 := det_mem_subring A _ hinv
  rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h4
end Formalism.HermitianLattices.Ext.L3.LandL
