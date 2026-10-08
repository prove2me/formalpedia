-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_deriv_pos_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:27:16.497222+00:00
-- url     : https://prove2.me/submissions/223d35b0-f733-410c-aaaf-f8e2492566eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_product_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (θ a : ℝ) (hθ : 0 < θ) (ha : 0 < a)
    (G : ℝ → ℝ) (hGmon : MonotoneOn G (Set.Ici 0))
    (hGpos : 0 < G a) (hGdiff : DifferentiableAt ℝ G a) :
    0 < deriv (fun x : ℝ => Real.exp (θ * x) * G x) a := by
  let g : ℝ → ℝ := fun z => G (max z 0)
  have hgmon : Monotone g := by
    intro s t hst
    apply hGmon
    · exact le_max_right s 0
    · exact le_max_right t 0
    · exact max_le_max hst le_rfl
  have he : G =ᶠ[𝓝 a] g := by
    filter_upwards [Ioi_mem_nhds ha] with z hz
    simp only [g, max_eq_left (le_of_lt (Set.mem_Ioi.mp hz))]
  have hGderiv : 0 ≤ deriv G a := by
    rw [Filter.EventuallyEq.deriv_eq he]
    exact hgmon.deriv_nonneg
  rw [AvramDividend.Classical.esscher_tilt_product_deriv θ a G hGdiff]
  exact mul_pos (Real.exp_pos _) (add_pos_of_pos_of_nonneg
    (mul_pos hθ hGpos) hGderiv)
