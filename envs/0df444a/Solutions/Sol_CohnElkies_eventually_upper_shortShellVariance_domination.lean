-- Prove2me | solution 1 for CohnElkies.eventually_upper_shortShellVariance_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/ae5dbfee-0b1d-4e39-b96b-79447865dd7b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shellLocation_gt_shortEndpoint
import Theorems.Thm_CohnElkies_eventually_upper_shell_parameter_margin
import Theorems.Thm_CohnElkies_upper_shell_parameter_margin_propagate
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_bounds
import Theorems.Thm_CohnElkies_upperShortShellVariance_global_bound
import Theorems.Thm_CohnElkies_upper_shellLocation_one_le

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
      ∀ δ : ℝ, ε / 2 ≤ δ →
        upperShortShellVariance ε δ ≤
          (1 / 100 : ℝ) *
            upperPositiveShellVariance ε δ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (tendsto_id.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [self_mem_nhdsWithin, hsmall,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shellLocation_gt_shortEndpoint,
      eventually_upper_shell_parameter_margin]
    with ε hε hεone horder hseparation hmargin
  change 0 < ε at hε
  intro δ hδ
  have hδnonneg : 0 ≤ δ := by
    nlinarith
  have hB : 1 ≤ shellLocation ε :=
    upper_shellLocation_one_le hε hεone.le
  have hBsq : 1 ≤ (shellLocation ε) ^ 2 := by
    nlinarith [sq_nonneg (shellLocation ε - 1)]
  have hpropagate :=
    upper_shell_parameter_margin_propagate
      hδ (by linarith [hseparation]) hmargin
  have hvariance :=
    upperShortShellVariance_global_bound
      hε hδnonneg horder
  have hpositive :=
    (upperPositiveShellVariance_bounds hε hδnonneg).1
  have hqexp :
      0 ≤ shellWeight ε *
        Real.exp (δ * shellLocation ε) :=
    mul_nonneg (shellWeight_pos ε).le
      (Real.exp_pos _).le
  calc
    upperShortShellVariance ε δ ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) := hvariance
    _ ≤ (1 / 2 : ℝ) *
        ((1 / 5000 : ℝ) * shellWeight ε *
          Real.exp (δ * shellLocation ε)) := by
      convert! mul_le_mul_of_nonneg_left
        hpropagate (by norm_num : (0 : ℝ) ≤ 1 / 2)
        using 1; ring
    _ ≤ (1 / 100 : ℝ) *
        ((1 / 2 : ℝ) * (shellLocation ε) ^ 2 *
          shellWeight ε *
            Real.exp (δ * shellLocation ε)) := by
      have hscaled :=
        mul_le_mul_of_nonneg_right hBsq hqexp
      nlinarith
    _ ≤ (1 / 100 : ℝ) *
        upperPositiveShellVariance ε δ :=
      mul_le_mul_of_nonneg_left hpositive
        (by norm_num)
end CohnElkies
