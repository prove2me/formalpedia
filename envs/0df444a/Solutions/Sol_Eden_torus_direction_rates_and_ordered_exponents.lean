-- Prove2me | solution 1 for Eden.torus_direction_rates_and_ordered_exponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:31.716793+00:00
-- url     : https://prove2.me/submissions/eafd8de3-d021-46c6-a4dc-63765d542177

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
import Theorems.Thm_Eden_exponentSum_on_torus


set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ torus) :
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧
      0 < (2 : ℝ) ∧ -c < 0 := by
  exact ⟨exponentSum_on_torus hc hp, by norm_num, by linarith⟩
end Eden
