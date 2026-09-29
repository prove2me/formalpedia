-- Prove2me | solution 1 for CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a4f567cc-f246-5518-89d3-fbe4e9777f5b

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : GL (Fin 2) K₀) {a b : K} (z z₀ : K)
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hΦ : (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) ≠ 0)
    (hΦ₀ : (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1))) ≠ 0) :
    crossRatio z z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) a) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) b) - 1 =
      (z - z₀) * (a - b) * algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) /
        ((z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) *
          (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1)))) := by
  have hcb := moebius_denom_ne_zero_of_mem K₀ hb g
  have hca := moebius_denom_ne_zero_of_mem K₀ ha g
  rw [pmoebius_mk K₀ g a hca, pmoebius_mk K₀ g b hcb, moebius, moebius, crossRatio, Matrix.det_fin_two,
    map_sub, map_mul, map_mul]
  set α := algebraMap K₀ K (g 0 0)
  set β := algebraMap K₀ K (g 0 1)
  set c := algebraMap K₀ K (g 1 0)
  set d := algebraMap K₀ K (g 1 1)
  have h1 : z - (α * b + β) / (c * b + d) = (z * (c * b + d) - (α * b + β)) / (c * b + d) := by
    rw [eq_div_iff hcb, sub_mul, div_mul_cancel₀ _ hcb]
  have h2 : z₀ - (α * a + β) / (c * a + d) = (z₀ * (c * a + d) - (α * a + β)) / (c * a + d) := by
    rw [eq_div_iff hca, sub_mul, div_mul_cancel₀ _ hca]
  have h3 : z - (α * a + β) / (c * a + d) = (z * (c * a + d) - (α * a + β)) / (c * a + d) := by
    rw [eq_div_iff hca, sub_mul, div_mul_cancel₀ _ hca]
  have h4 : z₀ - (α * b + β) / (c * b + d) = (z₀ * (c * b + d) - (α * b + β)) / (c * b + d) := by
    rw [eq_div_iff hcb, sub_mul, div_mul_cancel₀ _ hcb]
  rw [h1, h2, h3, h4]
  set P := z * (c * b + d) - (α * b + β) with hP
  set Q := z₀ * (c * a + d) - (α * a + β) with hQ
  rw [div_mul_div_comm, div_mul_div_comm, mul_comm (c * b + d) (c * a + d),
    div_div_div_cancel_right₀ (mul_ne_zero hca hcb), div_sub_one (mul_ne_zero hΦ hΦ₀), hP, hQ]
  congr 1
  ring

end S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq (solution)
