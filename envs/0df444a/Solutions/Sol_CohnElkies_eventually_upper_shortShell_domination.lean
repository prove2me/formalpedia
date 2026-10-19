-- Prove2me | solution 1 for CohnElkies.eventually_upper_shortShell_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/e5661741-7eb7-463e-a3aa-dc75f79f7c37

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_positiveShellDamping_lower_bound
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_upper_shellLocation_gt_shortEndpoint
import Theorems.Thm_CohnElkies_eventually_upper_shell_parameter_margin
import Theorems.Thm_CohnElkies_upperShortShellDamping_global_bound
import Theorems.Thm_CohnElkies_upper_shell_parameter_margin_propagate

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
      ∀ ℓ : ℝ, 0 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            upperShortShellDamping ε ℓ δ T ≤
              (1 / 100 : ℝ) *
                positiveShellDamping ε ℓ δ T := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shellLocation_gt_shortEndpoint,
      eventually_upper_shell_parameter_margin]
    with ε hε horder hshortmargin hseparation hmargin
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδnonneg : 0 ≤ δ := by
    nlinarith
  have hshort :
      upperShortShellDamping ε ℓ δ T ≤
        ℓ * upperShellShortCoefficient ε *
          Real.exp (δ * shortEndpoint ε) *
            min (T ^ 2) 1 :=
    upperShortShellDamping_global_bound
      hε hℓ hδnonneg horder
      (fun a ha => by
        have h := hshortmargin a ha
        nlinarith)
  have hpropagate :=
    upper_shell_parameter_margin_propagate hδ
      (le_of_lt (by linarith [hseparation])) hmargin
  have hpositive :=
    positiveShellDamping_lower_bound
      (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
      hε hℓ hδnonneg
  have hfreq : 0 ≤ min (T ^ 2) 1 :=
    le_min (sq_nonneg T) (by norm_num)
  calc
    upperShortShellDamping ε ℓ δ T ≤
        ℓ * upperShellShortCoefficient ε *
          Real.exp (δ * shortEndpoint ε) *
            min (T ^ 2) 1 := hshort
    _ ≤ ℓ * ((1 / 5000 : ℝ) * shellWeight ε *
          Real.exp (δ * shellLocation ε)) *
            min (T ^ 2) 1 := by
      convert! mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpropagate hℓ)
          hfreq using 1; ring
    _ = (1 / 100 : ℝ) *
        (ℓ / 50 * shellWeight ε *
          Real.exp (δ * shellLocation ε) *
            min (T ^ 2) 1) := by
      ring
    _ ≤ (1 / 100 : ℝ) *
        positiveShellDamping ε ℓ δ T :=
      mul_le_mul_of_nonneg_left hpositive
        (by norm_num)
end CohnElkies
