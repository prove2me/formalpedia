-- Prove2me | solution 1 for EquivarianceConvolution.convolution_theorem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:09:27.094872+00:00
-- url     : https://prove2.me/submissions/bdc7cf77-5a54-4caf-937d-ee32b7f7bee8

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators
namespace EquivarianceConvolution


theorem convolution_theorem {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (f g : G → ℂ) :
    groupFourier ρ (groupConv f g) = groupFourier ρ f * groupFourier ρ g := by
  unfold groupFourier groupConv
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulRight v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (f i)]


end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (f g : G → ℂ) :
    groupFourier ρ (groupConv f g) = groupFourier ρ f * groupFourier ρ g := by
  unfold groupFourier groupConv
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulRight v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (f i)]

