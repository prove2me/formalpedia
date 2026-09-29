-- Prove2me | solution 1 for Complex.integral_ball_eq_integral_smul_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2756ddeb-ccb7-50d4-9dc5-a2e0cc20ccb4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_ball_eq_integral_smul_circleMap

open MeasureTheory Metric Real Set

namespace PolarDiscAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem circleMap_eq_center_add_polarCoord_symm (c : ℂ) (p : ℝ × ℝ) :
    circleMap c p.1 p.2 = c + Complex.polarCoord.symm p := by
  simp only [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  push_cast
  ring

theorem indicator_ball_comp_polarCoord_symm (f : ℂ → E) (c : ℂ) (R : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    p.1 • (ball (0 : ℂ) R).indicator (fun w ↦ f (c + w)) (Complex.polarCoord.symm p)
      = (Ioo 0 R ×ˢ Ioo (-π) π).indicator (fun q : ℝ × ℝ ↦ q.1 • f (circleMap c q.1 q.2)) p := by
  have hp1 : 0 < p.1 := hp.1
  have hp2 : p.2 ∈ Ioo (-π) π := hp.2
  by_cases hR : p.1 < R
  · have h1 : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp1]; exact hR
    have h2 : p ∈ Ioo 0 R ×ˢ Ioo (-π) π := ⟨⟨hp1, hR⟩, hp2⟩
    rw [indicator_of_mem h1, indicator_of_mem h2, circleMap_eq_center_add_polarCoord_symm]
  · have h1 : Complex.polarCoord.symm p ∉ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp1]; exact hR
    have h2 : p ∉ Ioo 0 R ×ˢ Ioo (-π) π := fun h ↦ hR h.1.2
    rw [indicator_of_notMem h1, indicator_of_notMem h2, smul_zero]

theorem Ioo_prod_Ioo_subset_polarCoord_target (R : ℝ) :
    Ioo 0 R ×ˢ Ioo (-π) π ⊆ polarCoord.target :=
  prod_mono Ioo_subset_Ioi_self Subset.rfl

end PolarDiscAux

open PolarDiscAux in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ∫ z in ball c R, f z = ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, p.1 • f (circleMap c p.1 p.2) := by
  calc ∫ z in ball c R, f z
      = ∫ z, (ball c R).indicator f z := (integral_indicator measurableSet_ball).symm
    _ = ∫ w, (ball c R).indicator f (c + w) := (integral_add_left_eq_self _ c).symm
    _ = ∫ w, (ball (0 : ℂ) R).indicator (fun w ↦ f (c + w)) w := by
        congr 1 with w
        simp only [indicator, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
    _ = ∫ p in polarCoord.target,
          p.1 • (ball (0 : ℂ) R).indicator (fun w ↦ f (c + w)) (Complex.polarCoord.symm p) :=
        (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target,
          (Ioo 0 R ×ˢ Ioo (-π) π).indicator (fun q : ℝ × ℝ ↦ q.1 • f (circleMap c q.1 q.2)) p :=
        setIntegral_congr_fun polarCoord.open_target.measurableSet
          fun p hp ↦ indicator_ball_comp_polarCoord_symm f c R hp
    _ = ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, p.1 • f (circleMap c p.1 p.2) := by
        rw [setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
          inter_eq_right.mpr (Ioo_prod_Ioo_subset_polarCoord_target R)]

end S_Complex_integral_ball_eq_integral_smul_circleMap
end P2MW
export P2MW.S_Complex_integral_ball_eq_integral_smul_circleMap (solution)
