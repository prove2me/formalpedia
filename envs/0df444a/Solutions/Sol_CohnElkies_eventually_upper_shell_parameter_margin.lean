-- Prove2me | solution 1 for CohnElkies.eventually_upper_shell_parameter_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/b69800b2-46cf-48b3-a903-4a2e27eb47cb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_upperShellMarginRatio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      upperShellShortCoefficient ε *
          Real.exp ((ε / 2) * shortEndpoint ε) ≤
        (1 / 5000 : ℝ) * shellWeight ε *
          Real.exp ((ε / 2) * shellLocation ε) := by
  have hratio := tendsto_upperShellMarginRatio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio] with ε hε
  unfold upperShellMarginRatio at hε
  have hden :
      0 < shellWeight ε *
        Real.exp ((ε / 2) * shellLocation ε) :=
    mul_pos (shellWeight_pos ε) (Real.exp_pos _)
  have hscaled :
      5000 * upperShellShortCoefficient ε *
        Real.exp ((ε / 2) * shortEndpoint ε) <
          shellWeight ε *
            Real.exp ((ε / 2) * shellLocation ε) := by
    exact (div_lt_one hden).mp hε
  nlinarith
end CohnElkies
