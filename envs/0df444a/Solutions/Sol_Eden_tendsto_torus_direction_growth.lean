-- Prove2me | solution 1 for Eden.tendsto_torus_direction_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:30.6968+00:00
-- url     : https://prove2.me/submissions/4b52679d-0f48-4300-9f00-5ee902e66730

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
import Theorems.Thm_Eden_norm_fderiv_torus_directions

set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t)
      atTop (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_fderiv_torus_directions c ht.le hp i, Real.log_exp,
    mul_div_cancel_right₀ _ ht.ne']
end Eden
