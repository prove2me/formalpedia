-- Prove2me | solution 1 for EnergyMomentum.minkowskiInner_boostX
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-22T01:08:02.340814+00:00
-- url     : https://prove2.me/submissions/fec55538-2a94-4a6a-80ed-fcb4480303a9

import Mathlib
import Definitions.Def_EnergyMomentum_basic

open EnergyMomentum

theorem solution (c u : ℝ) (P : FourVec)
    (hc : 0 < c) (hu : |u| < c) :
    minkowskiInner (boostX c u P) (boostX c u P) = minkowskiInner P P := by
  let β : ℝ := u / c
  let s : ℝ := Real.sqrt (1 - β ^ 2)
  have hβabs : |β| < 1 := by
    rw [abs_div, abs_of_pos hc]
    exact (div_lt_one hc).2 hu
  have hβsq : β ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one β).2 hβabs
  have hd : 0 < 1 - β ^ 2 := sub_pos.mpr hβsq
  have hsqrt : s ^ 2 = 1 - β ^ 2 := Real.sq_sqrt hd.le
  have hsqrt0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hfactor : (1 / s) ^ 2 * (1 - β ^ 2) = 1 := by
    rw [← hsqrt]
    field_simp
  simp only [minkowskiInner, boostX]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_id_of_comm, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change
    (1 / s * (P.1 - β * P.2 0)) * (1 / s * (P.1 - β * P.2 0)) -
        ((1 / s * (P.2 0 - β * P.1)) * (1 / s * (P.2 0 - β * P.1)) +
          P.2 1 * P.2 1 + P.2 2 * P.2 2) =
      P.1 * P.1 - (P.2 0 * P.2 0 + P.2 1 * P.2 1 + P.2 2 * P.2 2)
  nlinarith [hfactor]
