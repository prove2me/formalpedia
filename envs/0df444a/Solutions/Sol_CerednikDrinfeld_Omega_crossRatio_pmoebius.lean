-- Prove2me | solution 1 for CerednikDrinfeld.Omega.crossRatio_pmoebius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/62ae3a93-03b7-55bc-9067-ef2042051b14

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CrossRatioInv

theorem moebius_sub {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] (g : GL (Fin 2) K₀) (w w' : K)
    (hw : algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1) ≠ 0)
    (hw' : algebraMap K₀ K (g 1 0) * w' + algebraMap K₀ K (g 1 1) ≠ 0) :
    moebius K₀ K g w - moebius K₀ K g w' =
      (algebraMap K₀ K (g 0 0) * algebraMap K₀ K (g 1 1) - algebraMap K₀ K (g 0 1) * algebraMap K₀ K (g 1 0)) * (w - w') /
        ((algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)) * (algebraMap K₀ K (g 1 0) * w' + algebraMap K₀ K (g 1 1))) := by
  rw [moebius, moebius, div_sub_div _ _ hw hw']
  congr 1
  ring

end CrossRatioInv

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : PGL(2, K₀)) {z z₀ x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (pmoebius K₀ g z) (pmoebius K₀ g z₀) (pmoebius K₀ g x) (pmoebius K₀ g y) = crossRatio z z₀ x y := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    have hDz := moebius_denom_ne_zero_of_mem K₀ hz g
    have hDz₀ := moebius_denom_ne_zero_of_mem K₀ hz₀ g
    have hDx := moebius_denom_ne_zero_of_mem K₀ hx g
    have hDy := moebius_denom_ne_zero_of_mem K₀ hy g
    rw [pmoebius_mk K₀ g z hDz, pmoebius_mk K₀ g z₀ hDz₀, pmoebius_mk K₀ g x hDx, pmoebius_mk K₀ g y hDy]
    set a := algebraMap K₀ K (g 0 0) with ha
    set b := algebraMap K₀ K (g 0 1) with hb
    set c := algebraMap K₀ K (g 1 0) with hc
    set d := algebraMap K₀ K (g 1 1) with hd
    have hdet : a * d - b * c ≠ 0 := by
      have h := g.det_ne_zero
      rw [Matrix.det_fin_two] at h
      intro h0
      apply h
      apply (algebraMap K₀ K).injective
      rw [map_sub, map_mul, map_mul, map_zero]
      linear_combination h0
    set E := (a * d - b * c) ^ 2 / ((c * z + d) * (c * x + d) * (c * z₀ + d) * (c * y + d)) with hE
    have hE0 : E ≠ 0 := by
      rw [hE]
      exact div_ne_zero (pow_ne_zero 2 hdet) (mul_ne_zero (mul_ne_zero (mul_ne_zero hDz hDx) hDz₀) hDy)
    have hN : (moebius K₀ K g z - moebius K₀ K g x) * (moebius K₀ K g z₀ - moebius K₀ K g y) = E * ((z - x) * (z₀ - y)) := by
      rw [CrossRatioInv.moebius_sub g z x hDz hDx, CrossRatioInv.moebius_sub g z₀ y hDz₀ hDy, hE]
      field_simp
      ring
    have hM : (moebius K₀ K g z - moebius K₀ K g y) * (moebius K₀ K g z₀ - moebius K₀ K g x) = E * ((z - y) * (z₀ - x)) := by
      rw [CrossRatioInv.moebius_sub g z y hDz hDy, CrossRatioInv.moebius_sub g z₀ x hDz₀ hDx, hE]
      field_simp
      ring
    rw [crossRatio, crossRatio, hN, hM, mul_div_mul_left _ _ hE0]

end S_CerednikDrinfeld_Omega_crossRatio_pmoebius
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius (solution)
