-- Prove2me | solution 1 for Eden.hasDerivWithinAt_planarMovingPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:20.799387+00:00
-- url     : https://prove2.me/submissions/4d9aef8a-41d2-46ba-9258-4cd7b74e9d24

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
import Theorems.Thm_Eden_planarMovingPerturbation_eq
import Theorems.Thm_Eden_planarMovingPerturbation_zero_time
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
import Theorems.Thm_Eden_hasDerivAt_planarAmplitude
import Theorems.Thm_Eden_hasDerivAt_radialAmplitude
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_planar_radius_sq
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_tangentialRate_eq_q
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarDiagonal_apply
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.planarMovingPerturbation_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace) :
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t := by
  have hs := add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))
  have hd : HasDerivAt (fun τ => planarDiagonal (planarFactors τ p) v)
      (!₂[radialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (radialAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 0),
        tangentialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (planarAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 1)]) t := by
    apply hasDerivAt_euclidean_of_coord
    intro i
    fin_cases i
    · simpa [planarDiagonal, planarFactors, mul_assoc] using
        (hasDerivAt_radialAmplitude ht hs).mul_const (v 0)
    · simpa [planarDiagonal, planarFactors, tangentialRate_eq_q, mul_assoc] using
        (hasDerivAt_planarAmplitude ht hs).mul_const (v 1)
  have h : HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (radialAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 0),
        tangentialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (planarAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 1)]) (Set.Ici 0) t :=
    hd.hasDerivWithinAt.congr_of_mem
      (fun τ hτ => planarMovingPerturbation_eq Ω hτ p v) ht
  rw [planarMovingPerturbation_eq Ω ht]
  simpa [planarEvolution, planar_radius_sq Ω ht, planarDiagonal, planarFactors] using h
end Eden
